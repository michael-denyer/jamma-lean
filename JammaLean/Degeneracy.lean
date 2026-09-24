import JammaLean.Pab
import JammaLean.GramDet
import JammaLean.ClosedForm
import JammaLean.Reml
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Degenerate SNPs, pivots and linear independence, and small-pivot amplification

`stats.py` `_beta_se_from_pab` marks a SNP valid by `is_valid = P_XX > 0` and
returns NaN otherwise (`GEMMA_DIVERGENCES.md` §2: "P_xx ≤ 0: Return NaN for all
stats (SNP has no variance)"; Summary table: "P_xx = 0 … Degenerate SNPs").
`calc_pab` (`src/jamma/lmm/pab.py`) divides by the pivots `Pab[p-1, (p,p)]`, and
`GEMMA_EQUIVALENCE.md` §4 says "Recursive divisions amplify this when
`Pab[p-1,(p,p)]` is small". In exact arithmetic this file proves:

* `pab_self_eq_zero_iff`, `pab_self_le_zero_iff`, `pab_self_pos_iff`: `P_xx = 0`
  exactly when the genotype lies in the covariate span, and `P_xx < 0` never
  happens, so the `P_xx <= 0` test fires exactly on span membership.
  `pab_smul_intercept_eq_zero`: a constant genotype with an intercept covariate
  is degenerate; `pab_eq_zero_of_mem_left`: then `P_xy = 0` too.
* `pivots_pos_iff_linearIndependent`, `linearIndependent_iff_not_mem_covSpan`:
  every CalcPab pivot `Pab[i, (i+1,i+1)]` is positive exactly when the
  covariates are linearly independent. The `_of_linearIndependent` corollaries
  restate `GramDet`, `ClosedForm` and `Reml` theorems with that hypothesis.
* `hasDerivAt_calcPabStep_*`: the partial derivatives of one update
  `g = ab − aw·bw/ww`; `calcPabStep_perturb_le` bounds a perturbed update with
  explicit `1/ww` and `1/ww²` terms, and `pab_step_perturb_le` rewrites it
  through Cauchy–Schwarz, `|aw| ≤ √(aa·ww)`, so the amplification is
  `√(aa·bb)/ww`.

Floating-point rounding is not modelled: `calcPabStep_perturb_le` takes input
errors of size `η` from wherever they come (for row 0, `FpSumTree`).
-/

namespace JammaLean

open Matrix

section Degenerate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The residual vanishes exactly on the covariate span. -/
theorem resid_eq_zero_iff (w : ℕ → E) (p : ℕ) (a : E) :
    resid w p a = 0 ↔ a ∈ covSpan w p := by
  constructor
  · intro h
    simpa [h] using sub_resid_mem_span w p a
  · intro ha
    exact (resid_unique w p a 0 (Submodule.zero_mem _) (by simpa using ha)).symm

/-- **Degenerate SNPs.** `Pab[p, aa] = 0` exactly when `a` is in the span of the
first `p` covariates. -/
theorem pab_self_eq_zero_iff (w : ℕ → E) (p : ℕ) (a : E) :
    pab w p a a = 0 ↔ a ∈ covSpan w p := by
  rw [pab, inner_self_eq_zero, resid_eq_zero_iff]

/-- `P_xx ≤ 0`, JAMMA's NaN test, holds exactly on span membership: in exact
arithmetic the `< 0` half never fires (`pab_self_nonneg`). -/
theorem pab_self_le_zero_iff (w : ℕ → E) (p : ℕ) (a : E) :
    pab w p a a ≤ 0 ↔ a ∈ covSpan w p := by
  rw [← pab_self_eq_zero_iff]
  exact ⟨fun h => le_antisymm h (pab_self_nonneg w p a), fun h => h.le⟩

/-- `is_valid = P_XX > 0` holds exactly when the genotype is outside the span. -/
theorem pab_self_pos_iff (w : ℕ → E) (p : ℕ) (a : E) :
    0 < pab w p a a ↔ a ∉ covSpan w p := by
  rw [← pab_self_le_zero_iff, not_le]

/-- A degenerate vector has every cross product zero too: `P_xy = 0`. -/
theorem pab_eq_zero_of_mem_left (w : ℕ → E) (p : ℕ) {a : E} (ha : a ∈ covSpan w p)
    (b : E) : pab w p a b = 0 := by
  rw [pab_eq_inner_resid_left, (resid_eq_zero_iff w p a).mpr ha, inner_zero_left]

/-- A constant genotype `c • 1` is degenerate once the intercept `1` is among
the first `p` covariates. -/
theorem pab_smul_intercept_eq_zero (w : ℕ → E) {i p : ℕ} (hi : i < p) (one : E)
    (hone : w i = one) (c : ℝ) : pab w p (c • one) (c • one) = 0 :=
  (pab_self_eq_zero_iff w p _).mpr
    (Submodule.smul_mem _ c (hone ▸ w_mem_covSpan w hi))

end Degenerate

section Independence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pivot `i` vanishes exactly when covariate `i` is a combination of the earlier ones. -/
theorem pab_pivot_eq_zero_iff (w : ℕ → E) (i : ℕ) :
    pab w i (w i) (w i) = 0 ↔ w i ∈ covSpan w i :=
  pab_self_eq_zero_iff w i (w i)

/-- **Pivots and independence.** Every CalcPab pivot is positive exactly when
the covariates `w 0, …, w (k-1)` are linearly independent. -/
theorem pivots_pos_iff_linearIndependent (w : ℕ → E) (k : ℕ) :
    (∀ i < k, 0 < pab w i (w i) (w i)) ↔ LinearIndependent ℝ (fun i : Fin k => w i) := by
  rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, ← prod_pab_diag_eq_det_gram,
    Finset.prod_ne_zero_iff]
  simp only [Finset.mem_range]
  exact forall₂_congr fun i _ =>
    ⟨fun h => h.ne', fun h => lt_of_le_of_ne (pab_self_nonneg w i (w i)) (Ne.symm h)⟩

/-- The standard characterisation, reached through the pivots: the covariates
are independent exactly when none lies in the span of the earlier ones. -/
theorem linearIndependent_iff_not_mem_covSpan (w : ℕ → E) (k : ℕ) :
    LinearIndependent ℝ (fun i : Fin k => w i) ↔ ∀ i < k, w i ∉ covSpan w i := by
  rw [← pivots_pos_iff_linearIndependent]
  exact forall₂_congr fun i _ => pab_self_pos_iff w i (w i)

/-- The Gram matrix is invertible exactly when every pivot is positive. -/
theorem isUnit_det_covGram_iff_pivots_pos (w : ℕ → E) (k : ℕ) :
    IsUnit (covGram w k).det ↔ ∀ i < k, 0 < pab w i (w i) (w i) := by
  rw [pivots_pos_iff_linearIndependent, isUnit_iff_ne_zero, covGram,
    Matrix.det_gram_ne_zero_iff_linearIndependent]

/-- `GramDet.sum_log_pab_diag_eq_log_det_gram` with linear independence in place
of the pivot hypothesis. -/
theorem sum_log_pab_diag_of_linearIndependent (w : ℕ → E) (k : ℕ)
    (h : LinearIndependent ℝ fun i : Fin k => w i) :
    ∑ i ∈ Finset.range k, Real.log (pab w i (w i) (w i)) =
      Real.log (Matrix.gram ℝ (fun i : Fin k => w i)).det :=
  sum_log_pab_diag_eq_log_det_gram w k ((pivots_pos_iff_linearIndependent w k).mpr h)

/-- `ClosedForm.pab_eq_closedForm` with linear independence in place of `IsUnit`. -/
theorem pab_eq_closedForm_of_linearIndependent (w : ℕ → E) (p : ℕ)
    (h : LinearIndependent ℝ fun i : Fin p => w i) (a b : E) :
    pab w p a b =
      @inner ℝ _ _ a b - covCross w p a ⬝ᵥ ((covGram w p)⁻¹ *ᵥ covCross w p b) :=
  pab_eq_closedForm w p (covGram_isUnit_det w p h) a b

/-- `ClosedForm.resid_eq_closedForm` with linear independence in place of `IsUnit`. -/
theorem resid_eq_closedForm_of_linearIndependent (w : ℕ → E) (p : ℕ)
    (h : LinearIndependent ℝ fun i : Fin p => w i) (a : E) :
    resid w p a = a - ∑ j : Fin p, ((covGram w p)⁻¹ *ᵥ covCross w p a) j • w j :=
  resid_eq_closedForm w p (covGram_isUnit_det w p h) a

/-- `Reml.log_det_gram` with linear independence in place of the pivot hypothesis. -/
theorem log_det_gram_of_linearIndependent (w : ℕ → E) (k : ℕ)
    (h : LinearIndependent ℝ fun i : Fin k => w i) :
    Real.log (JammaLean.gram w k).det = ∑ i ∈ Finset.range k, Real.log (pab w i (w i) (w i)) :=
  log_det_gram w k ((pivots_pos_iff_linearIndependent w k).mpr h)

/-- `Reml.pab_eq_schur` with linear independence in place of `IsUnit`. -/
theorem pab_eq_schur_of_linearIndependent (w : ℕ → E) (k : ℕ)
    (h : LinearIndependent ℝ fun i : Fin k => w i) (a b : E) :
    pab w k a b =
      @inner ℝ _ _ a b - ((JammaLean.gram w k)⁻¹ *ᵥ crossVec w k a) ⬝ᵥ crossVec w k b := by
  have hG : IsUnit (JammaLean.gram w k).det := by
    have : JammaLean.gram w k = covGram w k := by
      ext i j
      rfl
    rw [this]
    exact covGram_isUnit_det w k h
  exact pab_eq_schur w k hG a b

end Independence

section Logdet

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `GramDet.logdet_hiw_eq` with linear independence of the weighted, rotated
covariates in place of the two pivot hypotheses. -/
theorem logdet_hiw_eq_of_linearIndependent (U : Matrix n n ℝ) (hU : Uᵀ * U = 1)
    (ev : n → ℝ) (lam : ℝ) (hpos : ∀ i, 0 < lam * ev i + 1) (k : ℕ) (x : ℕ → n → ℝ)
    (wH wI : ℕ → EuclideanSpace ℝ n)
    (hwH : wH = fun i => weighted (fun s => (lam * ev s + 1)⁻¹) (rot U (x i)))
    (hwI : wI = fun i => weighted (fun s => (0 * ev s + 1)⁻¹) (rot U (x i)))
    (hH : LinearIndependent ℝ fun i : Fin k => wH i)
    (hI : LinearIndependent ℝ fun i : Fin k => wI i) :
    ∑ i ∈ Finset.range k, Real.log (pab wH i (wH i) (wH i)) -
        ∑ i ∈ Finset.range k, Real.log (pab wI i (wI i) (wI i)) =
      Real.log ((Matrix.of fun (s : n) (i : Fin k) => x i s)ᵀ * (hMat U ev lam)⁻¹ *
          Matrix.of fun (s : n) (i : Fin k) => x i s).det -
        Real.log ((Matrix.of fun (s : n) (i : Fin k) => x i s)ᵀ *
          Matrix.of fun (s : n) (i : Fin k) => x i s).det :=
  logdet_hiw_eq U hU ev lam hpos k x wH wI hwH hwI
    ((pivots_pos_iff_linearIndependent wH k).mpr hH)
    ((pivots_pos_iff_linearIndependent wI k).mpr hI)

end Logdet

section Sensitivity

/-- One CalcPab update, `Pab[p, ab] = ab − aw·bw/ww` from level `p - 1`. -/
noncomputable def calcPabStep (ab aw bw ww : ℝ) : ℝ :=
  ab - aw * bw / ww

theorem pab_succ_eq_calcPabStep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ℕ → E) (p : ℕ) (a b : E) :
    pab w (p + 1) a b =
      calcPabStep (pab w p a b) (pab w p a (w p)) (pab w p b (w p)) (pab w p (w p) (w p)) :=
  pab_succ w p a b

/-- `∂g/∂ww = aw·bw/ww²`. -/
theorem hasDerivAt_calcPabStep_ww (ab aw bw ww : ℝ) (h : ww ≠ 0) :
    HasDerivAt (fun t => calcPabStep ab aw bw t) (aw * bw / ww ^ 2) ww := by
  have hf : (fun t => calcPabStep ab aw bw t) = fun t => ab - aw * bw * t⁻¹ := by
    funext t
    simp [calcPabStep, div_eq_mul_inv]
  rw [hf]
  exact HasDerivAt.congr_deriv
    (HasDerivAt.const_sub ab (HasDerivAt.const_mul (aw * bw) (hasDerivAt_inv h)))
    (by field_simp)

/-- `∂g/∂aw = −bw/ww`. -/
theorem hasDerivAt_calcPabStep_aw (ab aw bw ww : ℝ) :
    HasDerivAt (fun t => calcPabStep ab t bw ww) (-bw / ww) aw := by
  have hf : (fun t => calcPabStep ab t bw ww) = fun t => ab - t * (bw / ww) := by
    funext t
    simp only [calcPabStep]
    ring
  rw [hf]
  exact HasDerivAt.congr_deriv
    (HasDerivAt.const_sub ab (hasDerivAt_mul_const (x := aw) (bw / ww))) (by ring)

/-- `∂g/∂bw = −aw/ww`. -/
theorem hasDerivAt_calcPabStep_bw (ab aw bw ww : ℝ) :
    HasDerivAt (fun t => calcPabStep ab aw t ww) (-aw / ww) bw := by
  have hf : (fun t => calcPabStep ab aw t ww) = fun t => ab - t * (aw / ww) := by
    funext t
    simp only [calcPabStep]
    ring
  rw [hf]
  exact HasDerivAt.congr_deriv
    (HasDerivAt.const_sub ab (hasDerivAt_mul_const (x := bw) (aw / ww))) (by ring)

/-- `∂g/∂ab = 1`. -/
theorem hasDerivAt_calcPabStep_ab (ab aw bw ww : ℝ) :
    HasDerivAt (fun t => calcPabStep t aw bw ww) 1 ab :=
  (hasDerivAt_id ab).sub_const _

/-- The exact change of one update under input perturbations `d₁ … d₄`. -/
theorem calcPabStep_perturb (ab aw bw ww d₁ d₂ d₃ d₄ : ℝ) (hww : ww ≠ 0)
    (hww' : ww + d₄ ≠ 0) :
    calcPabStep (ab + d₁) (aw + d₂) (bw + d₃) (ww + d₄) - calcPabStep ab aw bw ww =
      d₁ - (ww * (aw * d₃ + bw * d₂ + d₂ * d₃) - aw * bw * d₄) / (ww * (ww + d₄)) := by
  unfold calcPabStep
  field_simp
  ring

/-- An error in the pivot alone moves the update by exactly `aw·bw·d/(ww(ww+d))`:
the `1/ww²` growth is not an artefact of the bound below. -/
theorem calcPabStep_perturb_ww (ab aw bw ww d : ℝ) (hww : ww ≠ 0) (hww' : ww + d ≠ 0) :
    calcPabStep ab aw bw (ww + d) - calcPabStep ab aw bw ww =
      aw * bw * d / (ww * (ww + d)) := by
  unfold calcPabStep
  field_simp
  ring

/-- **Perturbation bound for one update.** Inputs off by at most `η`, with the
perturbed pivot still at least `ww/2`, move the result by at most
`η (1 + 2(|aw| + |bw| + η)/ww + 2|aw||bw|/ww²)`. -/
theorem calcPabStep_perturb_le (ab aw bw ww d₁ d₂ d₃ d₄ η : ℝ) (hww : 0 < ww)
    (h₁ : |d₁| ≤ η) (h₂ : |d₂| ≤ η) (h₃ : |d₃| ≤ η) (h₄ : |d₄| ≤ η)
    (hpiv : ww / 2 ≤ ww + d₄) :
    |calcPabStep (ab + d₁) (aw + d₂) (bw + d₃) (ww + d₄) - calcPabStep ab aw bw ww| ≤
      η * (1 + 2 * (|aw| + |bw| + η) / ww + 2 * (|aw| * |bw|) / ww ^ 2) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans h₁
  have hD : ww ^ 2 / 2 ≤ ww * (ww + d₄) := by nlinarith
  have hDpos : 0 < ww * (ww + d₄) := by nlinarith
  rw [calcPabStep_perturb _ _ _ _ _ _ _ _ hww.ne' (by linarith)]
  set N := ww * (aw * d₃ + bw * d₂ + d₂ * d₃) - aw * bw * d₄
  set Nb := ww * (|aw| * η + |bw| * η + η * η) + |aw| * |bw| * η
  have e1 : |aw * d₃ + bw * d₂ + d₂ * d₃| ≤ |aw| * η + |bw| * η + η * η := by
    calc |aw * d₃ + bw * d₂ + d₂ * d₃|
        ≤ |aw * d₃| + |bw * d₂| + |d₂ * d₃| := abs_add_three _ _ _
      _ = |aw| * |d₃| + |bw| * |d₂| + |d₂| * |d₃| := by simp only [abs_mul]
      _ ≤ |aw| * η + |bw| * η + η * η := by gcongr
  have hN : |N| ≤ Nb := by
    calc |N| ≤ |ww * (aw * d₃ + bw * d₂ + d₂ * d₃)| + |aw * bw * d₄| := abs_sub _ _
      _ = ww * |aw * d₃ + bw * d₂ + d₂ * d₃| + |aw| * |bw| * |d₄| := by
          rw [abs_mul, abs_of_pos hww, abs_mul, abs_mul]
      _ ≤ Nb := add_le_add (mul_le_mul_of_nonneg_left e1 hww.le)
          (mul_le_mul_of_nonneg_left h₄ (by positivity))
  have hNb : 0 ≤ Nb := (abs_nonneg _).trans hN
  have hq : |N / (ww * (ww + d₄))| ≤ 2 * Nb / ww ^ 2 := by
    rw [abs_div, abs_of_pos hDpos, div_le_div_iff₀ hDpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg ww),
      mul_le_mul_of_nonneg_left hD hNb]
  have hrhs : η * (1 + 2 * (|aw| + |bw| + η) / ww + 2 * (|aw| * |bw|) / ww ^ 2) =
      η + 2 * Nb / ww ^ 2 := by
    simp only [Nb]
    field_simp
    ring
  rw [hrhs]
  calc |d₁ - N / (ww * (ww + d₄))| ≤ |d₁| + |N / (ww * (ww + d₄))| := abs_sub _ _
    _ ≤ η + 2 * Nb / ww ^ 2 := add_le_add h₁ hq

end Sensitivity

section SmallPivot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy–Schwarz for `Pab`: `|Pab[p, ab]| ≤ √Pab[p, aa] · √Pab[p, bb]`. -/
theorem abs_pab_le_sqrt_mul_sqrt (w : ℕ → E) (p : ℕ) (a b : E) :
    |pab w p a b| ≤ √(pab w p a a) * √(pab w p b b) := by
  unfold pab
  rw [← norm_eq_sqrt_real_inner, ← norm_eq_sqrt_real_inner]
  exact abs_real_inner_le_norm _ _

/-- **Small-pivot amplification.** With `aa, bb, ww` the level-`p` entries
`Pab[p, aa]`, `Pab[p, bb]` and the pivot `Pab[p, w_p w_p]`, input errors of size
`η` move the level-`p+1` entry `Pab[p+1, ab]` by at most
`η (1 + 2(√aa + √bb)/√ww + 2η/ww + 2√(aa·bb)/ww)`. Relative to the natural
scale `√(aa·bb)` of the result, the last term is an error `2η/ww`: it grows
without bound as the pivot shrinks. -/
theorem pab_step_perturb_le (w : ℕ → E) (p : ℕ) (a b : E) (d₁ d₂ d₃ d₄ η : ℝ)
    (hww : 0 < pab w p (w p) (w p))
    (h₁ : |d₁| ≤ η) (h₂ : |d₂| ≤ η) (h₃ : |d₃| ≤ η) (h₄ : |d₄| ≤ η)
    (hpiv : pab w p (w p) (w p) / 2 ≤ pab w p (w p) (w p) + d₄) :
    |calcPabStep (pab w p a b + d₁) (pab w p a (w p) + d₂) (pab w p b (w p) + d₃)
        (pab w p (w p) (w p) + d₄) - pab w (p + 1) a b| ≤
      η * (1 + 2 * (√(pab w p a a) + √(pab w p b b)) / √(pab w p (w p) (w p)) +
        2 * η / pab w p (w p) (w p) +
        2 * √(pab w p a a * pab w p b b) / pab w p (w p) (w p)) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans h₁
  rw [pab_succ_eq_calcPabStep]
  refine (calcPabStep_perturb_le _ _ _ _ _ _ _ _ η hww h₁ h₂ h₃ h₄ hpiv).trans ?_
  set ww := pab w p (w p) (w p)
  set aw := pab w p a (w p)
  set bw := pab w p b (w p)
  set sa := √(pab w p a a)
  set sb := √(pab w p b b)
  set s := √ww with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hww
  have hss : s * s = ww := Real.mul_self_sqrt hww.le
  have hsa : 0 ≤ sa := Real.sqrt_nonneg _
  have hsb : 0 ≤ sb := Real.sqrt_nonneg _
  have haw : |aw| ≤ sa * s := abs_pab_le_sqrt_mul_sqrt w p a (w p)
  have hbw : |bw| ≤ sb * s := abs_pab_le_sqrt_mul_sqrt w p b (w p)
  have hmul : √(pab w p a a * pab w p b b) = sa * sb :=
    Real.sqrt_mul (pab_self_nonneg w p a) _
  rw [hmul]
  apply mul_le_mul_of_nonneg_left _ hη
  have t1 : 2 * (|aw| + |bw| + η) / ww = 2 * (|aw| + |bw|) / ww + 2 * η / ww := by ring
  have t2 : 2 * (|aw| + |bw|) / ww ≤ 2 * (sa + sb) / s := by
    rw [div_le_div_iff₀ hww hs, ← hss]
    have := mul_le_mul_of_nonneg_right (add_le_add haw hbw) hs.le
    nlinarith
  have t3 : 2 * (|aw| * |bw|) / ww ^ 2 ≤ 2 * (sa * sb) / ww := by
    rw [div_le_div_iff₀ (by positivity) hww]
    have h := mul_le_mul haw hbw (abs_nonneg _) (by positivity)
    have h' : sa * s * (sb * s) = sa * sb * ww := by rw [← hss]; ring
    rw [h'] at h
    nlinarith [mul_le_mul_of_nonneg_right h hww.le]
  linarith

end SmallPivot

end JammaLean
