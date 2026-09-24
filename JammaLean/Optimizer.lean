import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Order.Monotone.Basic

/-!
# Exact-arithmetic guarantees of the lambda optimizer

Models the lambda search in `src/jamma/lmm/likelihood_numpy.py`
(`golden_section_optimize_lambda_numpy`, `golden_section_optimize_lambda_mle_numpy`,
`_batch_golden_section_bracket_numpy`), `src/jamma/lmm/reml_score.py`
(`_refine_reml_optima`) and the C twin `golden_section_log_lambda` in
`src/jamma/lmm/_lmm_lambda_search.h`. Everything is in log λ and in exact real
arithmetic.

`docs/GEMMA_EQUIVALENCE.md` §5 and `docs/GEMMA_DIVERGENCES.md` §6 already say that
on flat objectives rounding can change which side golden section discards, so
the bracket invariant below can fail in floating point. These theorems are the
exact-arithmetic guarantee; the committed flat-optima and parity tests are the
empirical check of how far the float code stays from it.

Stages, as coded:

1. **Grid.** `n` points `g i = L₀ + i h`, `h > 0` (`np.linspace(log l_min, log l_max, n)`,
   in C `log_l_min + g * step`). `best_idx` is an argmax over the grid, and the
   coarse bracket is `[g (i-1), g (min (i+1) (n-1))]` (ℕ subtraction is the code's
   `max(i-1, 0)`). `grid_bracket_mem`: for a unimodal objective the peak lies in it.
2. **Golden section.** `gsStep` is the NumPy update literally (both probes
   recomputed from the ratio, one objective value reused); `gsStepC_eq` shows the C
   update (`d = c` / `c = d` swaps) is the same map in exact arithmetic, because
   `φ² = 1 - φ` for `φ = (√5 - 1)/2`. Keep-left is the strict test `fc > fd`; a tie
   keeps the right part. `gs_iterate_inv`: the peak stays in the bracket;
   `gs_iterate_width`: width `φᵏ w₀`; `golden_error`: the returned midpoint is within
   `φᵏ w₀ / 2` of the peak. `golden_error_code`: with the code's constants
   (`l_min = 1e-5`, `l_max = 1e5`, `n = 50`, `k = 20`) that is `< 3.12e-5` in log λ.
3. **Newton safeguard.** `newtonLoop` is the three-step loop with the code's
   acceptance rule (`δ > 0`, central-difference curvature `< 0`, candidate in the
   *coarse* bracket, `|score|` strictly smaller) and its stopping rule
   (`|s(candidate) / curvature| > 1e-10` to continue). The finiteness checks are
   vacuous over ℝ. `refine_mem_coarse`: the result never leaves the coarse bracket,
   so `refine_error_code` bounds it by the coarse width `2h < 0.95`. The golden bound
   of stage 2 is **not** preserved: `refine_can_leave_golden_bracket` gives a strictly
   decreasing score (so a strictly concave objective) whose refined result is 0.495
   from the root while the golden bracket had width 0.02. What the rule does give:
   `newton_step_toward_root` (the step points at the root when the score is
   decreasing), `accepted_closer_of_same_side` (an accepted step that does not cross
   the root strictly reduces the error), and `newtonLoop_affine` (for a quadratic
   objective the first step lands exactly on the peak and the loop stops there).
-/

namespace JammaLean

open Real

/-! ## Unimodality -/

/-- `f` rises strictly up to `xs` and falls strictly after it, on `[lo, hi]`. -/
structure Unimodal (f : ℝ → ℝ) (lo hi xs : ℝ) : Prop where
  mem : xs ∈ Set.Icc lo hi
  up : StrictMonoOn f (Set.Icc lo xs)
  down : StrictAntiOn f (Set.Icc xs hi)

/-- Two probes with `f q < f p` put the peak left of `q`. -/
lemma Unimodal.lt_of_lt {f : ℝ → ℝ} {lo hi xs p q : ℝ} (hf : Unimodal f lo hi xs)
    (hp : lo ≤ p) (hpq : p < q) (h : f q < f p) : xs < q := by
  refine lt_of_not_ge fun hc => ?_
  have := hf.up ⟨hp, by linarith⟩ ⟨by linarith, hc⟩ hpq
  linarith

/-- Two probes with `f p ≤ f q` put the peak right of `p`. -/
lemma Unimodal.gt_of_le {f : ℝ → ℝ} {lo hi xs p q : ℝ} (hf : Unimodal f lo hi xs)
    (hq : q ≤ hi) (hpq : p < q) (h : f p ≤ f q) : p < xs := by
  refine lt_of_not_ge fun hc => ?_
  have := hf.down ⟨hc, by linarith⟩ ⟨by linarith, hq⟩ hpq
  linarith

/-! ## Stage 1: the coarse grid bracket -/

/-- Grid point `i`: `L₀ + i h`. -/
def gridPt (L₀ h : ℝ) (i : ℕ) : ℝ := L₀ + i * h

lemma gridPt_le {L₀ h : ℝ} (hh : 0 < h) {i j : ℕ} (hij : i ≤ j) :
    gridPt L₀ h i ≤ gridPt L₀ h j := by
  unfold gridPt
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

lemma gridPt_lt {L₀ h : ℝ} (hh : 0 < h) {i j : ℕ} (hij : i < j) :
    gridPt L₀ h i < gridPt L₀ h j := by
  unfold gridPt
  have : (i : ℝ) < j := by exact_mod_cast hij
  nlinarith

/-- **Grid bracket.** If `f` is unimodal over the grid's span with peak `xs` and `i`
is any argmax of `f` over the grid points, then `xs` lies in the bracket the code
picks, `[g (i-1), g (min (i+1) (n-1))]`. -/
theorem grid_bracket_mem {f : ℝ → ℝ} {L₀ h xs : ℝ} {n i : ℕ} (hh : 0 < h) (hi : i < n)
    (hf : Unimodal f (gridPt L₀ h 0) (gridPt L₀ h (n - 1)) xs)
    (hmax : ∀ j < n, f (gridPt L₀ h j) ≤ f (gridPt L₀ h i)) :
    xs ∈ Set.Icc (gridPt L₀ h (i - 1)) (gridPt L₀ h (min (i + 1) (n - 1))) := by
  constructor
  · refine le_of_not_gt fun hc => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact absurd hf.mem.1 (not_le.mpr hc)
    · have hlt : gridPt L₀ h (i - 1) < gridPt L₀ h i := gridPt_lt hh (by omega)
      have := hf.down ⟨le_of_lt hc, gridPt_le hh (by omega)⟩
        ⟨by linarith, gridPt_le hh (by omega)⟩ hlt
      have := hmax (i - 1) (by omega)
      linarith
  · refine le_of_not_gt fun hc => ?_
    by_cases hin : i + 1 ≤ n - 1
    · rw [min_eq_left hin] at hc
      have hlt : gridPt L₀ h i < gridPt L₀ h (i + 1) := gridPt_lt hh (by omega)
      have := hf.up ⟨gridPt_le hh (by omega), by linarith⟩
        ⟨gridPt_le hh (by omega), le_of_lt hc⟩ hlt
      have := hmax (i + 1) (by omega)
      linarith
    · rw [min_eq_right (by omega)] at hc
      exact absurd hf.mem.2 (not_le.mpr hc)

/-- The coarse bracket is at most two grid cells wide. -/
lemma grid_bracket_width_le {L₀ h : ℝ} {n i : ℕ} (hh : 0 < h) :
    gridPt L₀ h (min (i + 1) (n - 1)) - gridPt L₀ h (i - 1) ≤ 2 * h := by
  unfold gridPt
  have h1 : ((min (i + 1) (n - 1) : ℕ) : ℝ) ≤ (i : ℝ) + 1 := by
    have : min (i + 1) (n - 1) ≤ i + 1 := min_le_left _ _
    exact_mod_cast this
  have h2 : (i : ℝ) - 1 ≤ ((i - 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    · rw [Nat.cast_sub hi0]; simp
  nlinarith

/-- With at least two grid points the coarse bracket is non-degenerate. -/
lemma grid_bracket_lt {L₀ h : ℝ} {n i : ℕ} (hh : 0 < h) (hn : 2 ≤ n) (hi : i < n) :
    gridPt L₀ h (i - 1) < gridPt L₀ h (min (i + 1) (n - 1)) :=
  gridPt_lt hh (by omega)

/-! ## Stage 2: golden section -/

/-- The golden ratio conjugate `(√5 - 1)/2`. The code's literal `0.6180339887498949`
is its nearest double. -/
noncomputable def φ : ℝ := (Real.sqrt 5 - 1) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt5_bounds : 2.236 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.236068 := by
  have h0 := Real.sqrt_nonneg 5
  have h1 := sqrt5_sq
  constructor <;> nlinarith

lemma φ_sq : φ ^ 2 = 1 - φ := by
  unfold φ; nlinarith [sqrt5_sq]

lemma φ_pos : 0 < φ := by unfold φ; linarith [sqrt5_bounds.1]

lemma φ_lt : φ < 0.618034 := by unfold φ; linarith [sqrt5_bounds.2]

lemma half_lt_φ : 1 / 2 < φ := by unfold φ; linarith [sqrt5_bounds.1]

/-- State of `_batch_golden_section_bracket_numpy`: bracket `[a, b]`, probes `c < d`
and their objective values. -/
structure GS where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  fc : ℝ
  fd : ℝ

/-- Initial probes: `c = b - φ(b-a)`, `d = a + φ(b-a)`, both evaluated. -/
noncomputable def gsInit (f : ℝ → ℝ) (a b : ℝ) : GS :=
  ⟨a, b, b - φ * (b - a), a + φ * (b - a), f (b - φ * (b - a)), f (a + φ * (b - a))⟩

/-- One NumPy iteration, literally: `keep_left = fc > fd`; the new bracket is `[a, d]`
or `[c, b]`; both probes are recomputed from the ratio; the kept side reuses its old
objective value (`new_fd = fc` resp. `new_fc = fd`) and only the other probe is
evaluated. -/
noncomputable def gsStep (f : ℝ → ℝ) (s : GS) : GS :=
  if s.fd < s.fc then
    ⟨s.a, s.d, s.d - φ * (s.d - s.a), s.a + φ * (s.d - s.a),
      f (s.d - φ * (s.d - s.a)), s.fc⟩
  else
    ⟨s.c, s.b, s.b - φ * (s.b - s.c), s.c + φ * (s.b - s.c),
      s.fd, f (s.c + φ * (s.b - s.c))⟩

/-- One C iteration (`_lmm_lambda_search.h`): `b = d; d = c; fd = fc; c = b - φ(b-a)`,
or `a = c; c = d; fc = fd; d = a + φ(b-a)`. -/
noncomputable def gsStepC (f : ℝ → ℝ) (s : GS) : GS :=
  if s.fd < s.fc then
    ⟨s.a, s.d, s.d - φ * (s.d - s.a), s.c, f (s.d - φ * (s.d - s.a)), s.fc⟩
  else
    ⟨s.c, s.b, s.d, s.c + φ * (s.b - s.c), s.fd, f (s.c + φ * (s.b - s.c))⟩

/-- Probes sit at the golden positions of the bracket. -/
def GS.Shaped (s : GS) : Prop := s.c = s.b - φ * (s.b - s.a) ∧ s.d = s.a + φ * (s.b - s.a)

/-- In exact arithmetic the C swap and the NumPy recomputation agree. -/
theorem gsStepC_eq (f : ℝ → ℝ) {s : GS} (hs : s.Shaped) : gsStepC f s = gsStep f s := by
  obtain ⟨hc, hd⟩ := hs
  have hsq := φ_sq
  unfold gsStepC gsStep
  split_ifs
  · congr 1; rw [hc, hd]; linear_combination (-(s.b - s.a)) * hsq
  · congr 1; rw [hc, hd]; linear_combination (s.b - s.a) * hsq

/-- Loop invariant: shaped probes, cached values are the objective at the probes,
the bracket is non-degenerate, inside `[lo, hi]`, and contains the peak. -/
structure GS.Inv (f : ℝ → ℝ) (lo hi xs : ℝ) (s : GS) : Prop where
  shaped : s.Shaped
  fc : s.fc = f s.c
  fd : s.fd = f s.d
  lt : s.a < s.b
  lo_le : lo ≤ s.a
  le_hi : s.b ≤ hi
  mem : xs ∈ Set.Icc s.a s.b

lemma gsInit_inv {f : ℝ → ℝ} {lo hi xs a b : ℝ} (hab : a < b) (hlo : lo ≤ a) (hhi : b ≤ hi)
    (hx : xs ∈ Set.Icc a b) : (gsInit f a b).Inv f lo hi xs :=
  ⟨⟨rfl, rfl⟩, rfl, rfl, hab, hlo, hhi, hx⟩

lemma GS.Inv.c_lt_d {f : ℝ → ℝ} {lo hi xs : ℝ} {s : GS} (h : s.Inv f lo hi xs) :
    s.c < s.d := by
  rw [h.shaped.1, h.shaped.2]; nlinarith [half_lt_φ, h.lt]

lemma GS.Inv.a_le_c {f : ℝ → ℝ} {lo hi xs : ℝ} {s : GS} (h : s.Inv f lo hi xs) :
    s.a ≤ s.c := by
  rw [h.shaped.1]; nlinarith [φ_lt, h.lt]

lemma GS.Inv.d_le_b {f : ℝ → ℝ} {lo hi xs : ℝ} {s : GS} (h : s.Inv f lo hi xs) :
    s.d ≤ s.b := by
  rw [h.shaped.2]; nlinarith [φ_lt, h.lt]

/-- **Invariant.** One step preserves it for a unimodal objective. -/
theorem gsStep_inv {f : ℝ → ℝ} {lo hi xs : ℝ} (hf : Unimodal f lo hi xs) {s : GS}
    (h : s.Inv f lo hi xs) : (gsStep f s).Inv f lo hi xs := by
  have hcd := h.c_lt_d
  have hac := h.a_le_c
  have hdb := h.d_le_b
  have hsq := φ_sq
  have hφ := φ_pos
  obtain ⟨hc, hd⟩ := h.shaped
  unfold gsStep
  split_ifs with hk
  · rw [h.fc, h.fd] at hk
    have hx : xs < s.d := hf.lt_of_lt (by linarith [h.lo_le]) hcd hk
    refine ⟨⟨rfl, rfl⟩, rfl, ?_, ?_, h.lo_le, ?_, ⟨h.mem.1, hx.le⟩⟩
    · dsimp only
      rw [h.fc]; congr 1; rw [hc, hd]; linear_combination (-(s.b - s.a)) * hsq
    · change s.a < s.d; linarith
    · change s.d ≤ hi; linarith [h.le_hi]
  · rw [not_lt] at hk
    rw [h.fc, h.fd] at hk
    have hx : s.c < xs := hf.gt_of_le (by linarith [h.le_hi]) hcd hk
    refine ⟨⟨rfl, rfl⟩, ?_, rfl, ?_, ?_, h.le_hi, ⟨hx.le, h.mem.2⟩⟩
    · dsimp only
      rw [h.fd]; congr 1; rw [hc, hd]; linear_combination (s.b - s.a) * hsq
    · change s.c < s.b; linarith
    · change lo ≤ s.c; linarith [h.lo_le]

/-- Each step multiplies the width by exactly `φ`. -/
theorem gsStep_width {f : ℝ → ℝ} {s : GS} (hs : s.Shaped) :
    (gsStep f s).b - (gsStep f s).a = φ * (s.b - s.a) := by
  obtain ⟨hc, hd⟩ := hs
  unfold gsStep
  split_ifs
  · change s.d - s.a = _; rw [hd]; ring
  · change s.b - s.c = _; rw [hc]; ring

theorem gs_iterate_inv {f : ℝ → ℝ} {lo hi xs : ℝ} (hf : Unimodal f lo hi xs) {s : GS}
    (h : s.Inv f lo hi xs) (k : ℕ) : ((gsStep f)^[k] s).Inv f lo hi xs := by
  induction k with
  | zero => exact h
  | succ k ih => rw [Function.iterate_succ_apply']; exact gsStep_inv hf ih

theorem gs_iterate_width {f : ℝ → ℝ} {lo hi xs : ℝ} (hf : Unimodal f lo hi xs) {s : GS}
    (h : s.Inv f lo hi xs) (k : ℕ) :
    ((gsStep f)^[k] s).b - ((gsStep f)^[k] s).a = φ ^ k * (s.b - s.a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', gsStep_width (gs_iterate_inv hf h k).shaped, ih]
    ring

/-- The code returns the midpoint `(a + b) / 2` of the final bracket. -/
noncomputable def gsResult (f : ℝ → ℝ) (a b : ℝ) (k : ℕ) : ℝ :=
  ((gsStep f)^[k] (gsInit f a b)).a / 2 + ((gsStep f)^[k] (gsInit f a b)).b / 2

/-- **Golden-section error.** Starting from a bracket that holds the peak of a
unimodal objective, after `k` steps the midpoint is within `φᵏ (b - a) / 2`. -/
theorem golden_error {f : ℝ → ℝ} {lo hi xs a b : ℝ} (hf : Unimodal f lo hi xs)
    (hab : a < b) (hlo : lo ≤ a) (hhi : b ≤ hi) (hx : xs ∈ Set.Icc a b) (k : ℕ) :
    |gsResult f a b k - xs| ≤ φ ^ k * (b - a) / 2 := by
  have hI := gs_iterate_inv hf (gsInit_inv (f := f) hab hlo hhi hx) k
  have hw : ((gsStep f)^[k] (gsInit f a b)).b - ((gsStep f)^[k] (gsInit f a b)).a
      = φ ^ k * (b - a) := gs_iterate_width hf (gsInit_inv (f := f) hab hlo hhi hx) k
  unfold gsResult
  rw [abs_le]
  constructor <;> nlinarith [hI.mem.1, hI.mem.2]

/-! ## Grid plus golden section, and the code's constants -/

/-- Grid argmax, coarse bracket, then `k` golden steps: the returned log λ is within
`φᵏ h` of the peak (the coarse bracket is at most `2h` wide). -/
theorem grid_golden_error {f : ℝ → ℝ} {L₀ h xs : ℝ} {n i : ℕ} (hh : 0 < h) (hn : 2 ≤ n)
    (hi : i < n) (hf : Unimodal f (gridPt L₀ h 0) (gridPt L₀ h (n - 1)) xs)
    (hmax : ∀ j < n, f (gridPt L₀ h j) ≤ f (gridPt L₀ h i)) (k : ℕ) :
    |gsResult f (gridPt L₀ h (i - 1)) (gridPt L₀ h (min (i + 1) (n - 1))) k - xs|
      ≤ φ ^ k * h := by
  refine (golden_error hf (grid_bracket_lt hh hn hi) (gridPt_le hh (Nat.zero_le _))
    (gridPt_le hh (by omega)) (grid_bracket_mem hh hi hf hmax) k).trans ?_
  have := grid_bracket_width_le (L₀ := L₀) (n := n) (i := i) hh
  have := pow_pos φ_pos k
  nlinarith

/-- The code's grid step in log λ: `(log 1e5 - log 1e-5) / 49 = 10 log 10 / 49`. -/
noncomputable def codeStep : ℝ := (Real.log 1e5 - Real.log 1e-5) / (50 - 1)

lemma codeStep_eq : codeStep = 10 * Real.log 10 / 49 := by
  unfold codeStep
  have h1 : Real.log (1e5 : ℝ) = 5 * Real.log 10 := by
    rw [show (1e5 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log (1e-5 : ℝ) = -(5 * Real.log 10) := by
    rw [show (1e-5 : ℝ) = (10 ^ 5)⁻¹ by norm_num, Real.log_inv, Real.log_pow]; norm_num
  rw [h1, h2]; ring

/-- `log 10 < 2.3105`, from `10³ < 2¹⁰` and `log 2 < 0.6931471808`. -/
lemma log_ten_lt : Real.log 10 < 2.3105 := by
  have h := Real.log_lt_log (by norm_num : (0:ℝ) < 10 ^ 3) (by norm_num : (10:ℝ) ^ 3 < 2 ^ 10)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith [Real.log_two_lt_d9]

lemma log_ten_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)

lemma codeStep_pos : 0 < codeStep := by rw [codeStep_eq]; linarith [log_ten_pos]

/-- The code's constants: `l_min = 1e-5`, `l_max = 1e5`, 50 grid points, 20 golden
steps. The golden-section error bound `φ²⁰ h` is below `3.12e-5` in log λ. -/
theorem golden_error_code : φ ^ 20 * codeStep < 3.12e-5 := by
  rw [codeStep_eq]
  have h1 : φ ^ 20 < 0.618034 ^ 20 := pow_lt_pow_left₀ φ_lt φ_pos.le (by norm_num)
  have h2 : 10 * Real.log 10 / 49 < 10 * 2.3105 / 49 := by linarith [log_ten_lt]
  have h3 : 0 < 10 * Real.log 10 / 49 := by linarith [log_ten_pos]
  have h4 : (0.618034 : ℝ) ^ 20 * (10 * 2.3105 / 49) < 3.12e-5 := by norm_num
  calc φ ^ 20 * (10 * Real.log 10 / 49)
      ≤ 0.618034 ^ 20 * (10 * Real.log 10 / 49) := by nlinarith
    _ ≤ 0.618034 ^ 20 * (10 * 2.3105 / 49) := by
        have : (0 : ℝ) < 0.618034 ^ 20 := by norm_num
        nlinarith
    _ < 3.12e-5 := h4

/-! ## Stage 3: the safeguarded Newton refinement -/

/-- Probe offset `min(1e-3, (hi-lo)/4, (x-lo)/2, (hi-x)/2)` over the coarse
bracket `[lo, hi]`. -/
noncomputable def probeDelta (lo hi x : ℝ) : ℝ :=
  min (min (min (1 / 1000) ((hi - lo) / 4)) ((x - lo) / 2)) ((hi - x) / 2)

/-- Central-difference curvature of the score: `(s(x+δ) - s(x-δ)) / (2δ)`. -/
noncomputable def curv (s : ℝ → ℝ) (x δ : ℝ) : ℝ := (s (x + δ) - s (x - δ)) / (2 * δ)

/-- Newton candidate `x - s(x) / curvature`. -/
noncomputable def cand (s : ℝ → ℝ) (lo hi x : ℝ) : ℝ :=
  x - s x / curv s x (probeDelta lo hi x)

/-- The acceptance rule of `_refine_reml_optima` and of the C loop: positive probe
offset, negative curvature, candidate in the coarse bracket, strictly smaller
`|score|`. (The code's `isfinite` checks hold trivially over ℝ.) -/
def Accepts (s : ℝ → ℝ) (lo hi x : ℝ) : Prop :=
  0 < probeDelta lo hi x ∧ curv s x (probeDelta lo hi x) < 0 ∧
    lo ≤ cand s lo hi x ∧ cand s lo hi x ≤ hi ∧ |s (cand s lo hi x)| < |s x|

open Classical in
/-- Up to `k` safeguarded steps: a rejected step stops at `x`; an accepted step moves
to the candidate and continues only while `|s(candidate) / curvature| > 1e-10`, with
the curvature estimated at the point the step left. -/
noncomputable def newtonLoop (s : ℝ → ℝ) (lo hi : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x =>
    if Accepts s lo hi x then
      if 1e-10 < |s (cand s lo hi x) / curv s x (probeDelta lo hi x)| then
        newtonLoop s lo hi k (cand s lo hi x)
      else cand s lo hi x
    else x

/-- The refinement as called: only when the final golden bracket `[a, b]` left both
coarse endpoints (`interior`), three steps from the midpoint; otherwise the midpoint. -/
noncomputable def refine (s : ℝ → ℝ) (ca cb a b : ℝ) : ℝ :=
  if ca < a ∧ b < cb then newtonLoop s ca cb 3 (a / 2 + b / 2) else a / 2 + b / 2

lemma probeDelta_pos {lo hi x : ℝ} (h1 : lo < x) (h2 : x < hi) : 0 < probeDelta lo hi x := by
  unfold probeDelta
  simp only [lt_min_iff]
  refine ⟨⟨⟨by norm_num, by linarith⟩, by linarith⟩, by linarith⟩

/-- The probes `x ± δ` stay in the coarse bracket. -/
theorem probes_mem {lo hi x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    x - probeDelta lo hi x ∈ Set.Icc lo hi ∧ x + probeDelta lo hi x ∈ Set.Icc lo hi := by
  obtain ⟨h1, h2⟩ := hx
  have hlo : probeDelta lo hi x ≤ (x - lo) / 2 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hhi : probeDelta lo hi x ≤ (hi - x) / 2 := min_le_right _ _
  have h0 : 0 ≤ probeDelta lo hi x := by
    unfold probeDelta
    simp only [le_min_iff]
    refine ⟨⟨⟨by norm_num, by linarith⟩, by linarith⟩, by linarith⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **Safeguard.** Every point the loop returns lies in the coarse bracket. -/
theorem newtonLoop_mem (s : ℝ → ℝ) {lo hi : ℝ} (k : ℕ) {x : ℝ} (hx : x ∈ Set.Icc lo hi) :
    newtonLoop s lo hi k x ∈ Set.Icc lo hi := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih =>
    unfold newtonLoop
    split_ifs with hA
    · exact ih ⟨hA.2.2.1, hA.2.2.2.1⟩
    · exact ⟨hA.2.2.1, hA.2.2.2.1⟩
    · exact hx

theorem refine_mem_coarse (s : ℝ → ℝ) {ca cb a b : ℝ} (ha : ca ≤ a) (hab : a ≤ b)
    (hb : b ≤ cb) : refine s ca cb a b ∈ Set.Icc ca cb := by
  unfold refine
  split_ifs
  · exact newtonLoop_mem s 3 ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

/-- Golden section only shrinks the bracket: the final `[a, b]` sits inside the
initial one. -/
theorem gs_iterate_nested {f : ℝ → ℝ} {lo hi xs : ℝ} (hf : Unimodal f lo hi xs) {s : GS}
    (h : s.Inv f lo hi xs) (k : ℕ) :
    s.a ≤ ((gsStep f)^[k] s).a ∧ ((gsStep f)^[k] s).b ≤ s.b := by
  induction k with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
    have hk := gs_iterate_inv hf h k
    rw [Function.iterate_succ_apply']
    unfold gsStep
    split_ifs
    · exact ⟨ih.1, hk.d_le_b.trans ih.2⟩
    · exact ⟨ih.1.trans hk.a_le_c, ih.2⟩

/-- The whole search as coded: grid argmax `i`, coarse bracket, `k` golden steps on
the objective `f`, then the refinement driven by the score `s`. -/
noncomputable def lambdaSearch (f s : ℝ → ℝ) (L₀ h : ℝ) (n i k : ℕ) : ℝ :=
  refine s (gridPt L₀ h (i - 1)) (gridPt L₀ h (min (i + 1) (n - 1)))
    ((gsStep f)^[k] (gsInit f (gridPt L₀ h (i - 1)) (gridPt L₀ h (min (i + 1) (n - 1))))).a
    ((gsStep f)^[k] (gsInit f (gridPt L₀ h (i - 1)) (gridPt L₀ h (min (i + 1) (n - 1))))).b

/-- **End-to-end bound.** For a unimodal objective and *any* score function, the
returned log λ is within one coarse bracket width, `2h`, of the peak. -/
theorem lambdaSearch_error {f : ℝ → ℝ} (s : ℝ → ℝ) {L₀ h xs : ℝ} {n i : ℕ} (hh : 0 < h)
    (hn : 2 ≤ n) (hi : i < n) (hf : Unimodal f (gridPt L₀ h 0) (gridPt L₀ h (n - 1)) xs)
    (hmax : ∀ j < n, f (gridPt L₀ h j) ≤ f (gridPt L₀ h i)) (k : ℕ) :
    |lambdaSearch f s L₀ h n i k - xs| ≤ 2 * h := by
  have hx := grid_bracket_mem hh hi hf hmax
  have h0 := gsInit_inv (f := f) (lo := gridPt L₀ h 0) (hi := gridPt L₀ h (n - 1))
    (grid_bracket_lt hh hn hi) (gridPt_le hh (Nat.zero_le _))
    (gridPt_le hh (min_le_right _ _)) hx
  have hI := gs_iterate_inv hf h0 k
  have hN := gs_iterate_nested hf h0 k
  have hR : lambdaSearch f s L₀ h n i k ∈
      Set.Icc (gridPt L₀ h (i - 1)) (gridPt L₀ h (min (i + 1) (n - 1))) :=
    refine_mem_coarse s hN.1 hI.lt.le hN.2
  have hw := grid_bracket_width_le (L₀ := L₀) (n := n) (i := i) hh
  rw [abs_le]
  constructor <;> linarith [hR.1, hR.2, hx.1, hx.2]

/-- Without an interior golden bracket the refinement is skipped and the golden
bound `φᵏ h` of `grid_golden_error` holds. -/
theorem lambdaSearch_error_of_not_interior {f : ℝ → ℝ} (s : ℝ → ℝ) {L₀ h xs : ℝ} {n i : ℕ}
    (hh : 0 < h) (hn : 2 ≤ n) (hi : i < n)
    (hf : Unimodal f (gridPt L₀ h 0) (gridPt L₀ h (n - 1)) xs)
    (hmax : ∀ j < n, f (gridPt L₀ h j) ≤ f (gridPt L₀ h i)) (k : ℕ)
    (hni : ¬ (gridPt L₀ h (i - 1) <
        ((gsStep f)^[k] (gsInit f (gridPt L₀ h (i - 1))
          (gridPt L₀ h (min (i + 1) (n - 1))))).a ∧
      ((gsStep f)^[k] (gsInit f (gridPt L₀ h (i - 1))
          (gridPt L₀ h (min (i + 1) (n - 1))))).b < gridPt L₀ h (min (i + 1) (n - 1)))) :
    |lambdaSearch f s L₀ h n i k - xs| ≤ φ ^ k * h := by
  have := grid_golden_error hh hn hi hf hmax k
  unfold lambdaSearch refine
  rw [ite_eq_right_of_eq_false _ _ (eq_false hni)]
  exact this

/-- With the code's step, the post-refinement bound `2h` is below `0.95` in log λ. -/
theorem refine_error_code : 2 * codeStep < 0.95 := by
  rw [codeStep_eq]; linarith [log_ten_lt]

/-- For a decreasing score with root `r`, a negative-curvature Newton step moves
toward `r`. -/
theorem newton_step_toward_root {s : ℝ → ℝ} {I : Set ℝ} (hs : StrictAntiOn s I) {x r κ : ℝ}
    (hx : x ∈ I) (hr : r ∈ I) (hsr : s r = 0) (hκ : κ < 0) :
    (x < r → x < x - s x / κ) ∧ (r < x → x - s x / κ < x) := by
  constructor
  · intro hlt
    have h1 : 0 < s x := hsr ▸ hs hx hr hlt
    have : s x / κ < 0 := div_neg_of_pos_of_neg h1 hκ
    linarith
  · intro hlt
    have h1 : s x < 0 := hsr ▸ hs hr hx hlt
    have : 0 < s x / κ := div_pos_of_neg_of_neg h1 hκ
    linarith

/-- For a non-increasing score with root `r`, a point `c` with smaller `|score|` on the
same side of `r` as `x` is strictly closer to `r`. So an accepted step that does not
cross the root reduces the error. -/
theorem accepted_closer_of_same_side {s : ℝ → ℝ} {I : Set ℝ} (hs : AntitoneOn s I)
    {x c r : ℝ} (hx : x ∈ I) (hc : c ∈ I) (hr : r ∈ I) (hsr : s r = 0)
    (hlt : |s c| < |s x|) (hside : (x ≤ r ∧ c ≤ r) ∨ (r ≤ x ∧ r ≤ c)) :
    |c - r| < |x - r| := by
  rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have sx : 0 ≤ s x := hsr ▸ hs hx hr h1
    have sc : 0 ≤ s c := hsr ▸ hs hc hr h2
    rw [abs_of_nonneg sx, abs_of_nonneg sc] at hlt
    have hxc : x < c := lt_of_not_ge fun h => by linarith [hs hc hx h]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have sx : s x ≤ 0 := hsr ▸ hs hr hx h1
    have sc : s c ≤ 0 := hsr ▸ hs hr hc h2
    rw [abs_of_nonpos sx, abs_of_nonpos sc] at hlt
    have hxc : c < x := lt_of_not_ge fun h => by linarith [hs hx hc h]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- **Quadratic objective.** With an affine score `s t = m (r - t)`, `m > 0`, and `r`
in the coarse bracket, one step from any interior `x ≠ r` lands exactly on `r`, is
accepted, and the loop stops there. -/
theorem newtonLoop_affine {m r lo hi x : ℝ} (hm : 0 < m) (hr : r ∈ Set.Icc lo hi)
    (h1 : lo < x) (h2 : x < hi) (hxr : x ≠ r) (k : ℕ) :
    newtonLoop (fun t => m * (r - t)) lo hi (k + 1) x = r := by
  set s : ℝ → ℝ := fun t => m * (r - t) with hs
  have hδ := probeDelta_pos h1 h2
  have hcurv : curv s x (probeDelta lo hi x) = -m := by
    unfold curv; simp only [hs]; field_simp; ring
  have hcand : cand s lo hi x = r := by
    unfold cand; rw [hcurv]; simp only [hs]; field_simp; ring
  have hA : Accepts s lo hi x := by
    refine ⟨hδ, by rw [hcurv]; linarith, by rw [hcand]; exact hr.1,
      by rw [hcand]; exact hr.2, ?_⟩
    rw [hcand]
    simp only [hs, sub_self, mul_zero, abs_zero]
    exact abs_pos.mpr (mul_ne_zero hm.ne' (sub_ne_zero.mpr (Ne.symm hxr)))
  have hstop : ¬ (1e-10 < |s (cand s lo hi x) / curv s x (probeDelta lo hi x)|) := by
    rw [hcand]; simp [hs]; norm_num
  unfold newtonLoop
  rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_right_of_eq_false _ _ (eq_false hstop), hcand]

/-- Piecewise-linear strictly decreasing score used by the counterexample: slope `-1`
up to `1e-3`, a steep drop to its root at `1/200`, then slope `-1e-12`. -/
noncomputable def ceScore (t : ℝ) : ℝ :=
  if t ≤ 1 / 1000 then 1 / 2 - t
  else if t ≤ 1 / 200 then 499 / 4 * (1 / 200 - t)
  else (1 / 200 - t) * 1e-12

theorem ceScore_strictAnti : StrictAnti ceScore := by
  intro a b hab
  unfold ceScore
  split_ifs <;> linarith

/-- **The golden bound is not preserved.** A strictly decreasing score (the derivative
of a strictly concave objective) with root `1/200`, coarse bracket `[-1, 1]`, and a
final golden bracket `[-1/100, 1/100]` that holds the root and is strictly interior:
the refinement accepts one step to `1/2` and stops, because the stopping rule
divides the new score by the curvature measured at the old point. The result is
`0.495` from the root; the golden midpoint was `0.005` from it. -/
theorem refine_can_leave_golden_bracket :
    StrictAnti ceScore ∧ ceScore (1 / 200) = 0 ∧
      (1 / 200 : ℝ) ∈ Set.Icc (-1 / 100) (1 / 100) ∧
      refine ceScore (-1) 1 (-1 / 100) (1 / 100) = 1 / 2 ∧
      |(1 / 2 : ℝ) - 1 / 200| > (1 / 100 - (-1 / 100)) * 24 := by
  have hδ : probeDelta (-1) 1 0 = 1 / 1000 := by
    unfold probeDelta; norm_num
  have hcurv : curv ceScore 0 (probeDelta (-1) 1 0) = -1 := by
    rw [hδ]; unfold curv ceScore; norm_num
  have hcand : cand ceScore (-1) 1 0 = 1 / 2 := by
    unfold cand; rw [hcurv]; unfold ceScore; norm_num
  have hs_half : ceScore (1 / 2) = -(99 / 200) * 1e-12 := by
    unfold ceScore; norm_num
  have hA : Accepts ceScore (-1) 1 0 := by
    refine ⟨by rw [hδ]; norm_num, by rw [hcurv]; norm_num, by rw [hcand]; norm_num,
      by rw [hcand]; norm_num, ?_⟩
    rw [hcand, hs_half]; unfold ceScore; norm_num
  refine ⟨ceScore_strictAnti, by unfold ceScore; norm_num, by norm_num, ?_, by norm_num⟩
  have hstop : ¬ (1e-10 < |ceScore (cand ceScore (-1) 1 0) /
      curv ceScore 0 (probeDelta (-1) 1 0)|) := by
    rw [hcand, hs_half, hcurv]; norm_num
  have hint : (-1 : ℝ) < -1 / 100 ∧ (1 / 100 : ℝ) < 1 := by norm_num
  unfold refine
  rw [ite_eq_left_of_eq_true _ _ (eq_true hint),
    show (-1 / 100 : ℝ) / 2 + 1 / 100 / 2 = 0 by norm_num]
  unfold newtonLoop
  rw [ite_eq_left_of_eq_true _ _ (eq_true hA), ite_eq_right_of_eq_false _ _ (eq_false hstop), hcand]

end JammaLean
