import JammaLean.Optimizer
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The safeguarded Newton step on a smooth, well-conditioned peak

Models one step of `_refine_reml_optima` in `src/jamma/lmm/reml_score.py` (and its C
twin) through the definitions of `JammaLean.Optimizer`: the probe offset
`probeDelta`, the central-difference curvature `curv`, the candidate `cand`, the
acceptance rule `Accepts`, and the three-step `newtonLoop`. `docs/GEMMA_DIVERGENCES.md`
§6 describes the refinement; PR #477 is the investigation of where it loses accuracy.

`Optimizer.refine_can_leave_golden_bracket` shows the accept rule can take a step
that lands far from the root. This file shows that cannot happen on a well-conditioned
peak. `WellCond s s' r R m L M` says: on `J = [r - R, r + R]` the score `s` has
derivative `s'`, `-L ≤ s' ≤ -m < 0` (a strictly concave objective with curvature
bounded away from zero), `s'` is `M`-Lipschitz, and `s r = 0`.

* `newton_exact_error`: exact-derivative Newton, `|x - s x / s' x - r| ≤ (M/m)|x - r|²`.
  The constant is `M/m`, not the Taylor constant `M/(2m)`: the proof uses the mean
  value theorem only.
* `curv_error`: `|curv s x δ - s' x| ≤ M δ`. First order in `δ`, because only `s'` is
  assumed Lipschitz; the central difference is second order only under a bound on
  `s'''`, which is not assumed.
* `cand_error`: the code's candidate satisfies
  `|cand - r| ≤ M (δ + |x - r|) / m · |x - r|`, with `δ = probeDelta lo hi x`.
* `accepts_of_wellCond`: if also `[r - e, r + e]` (`e = |x - r| > 0`) lies strictly
  inside the coarse bracket, `e + 1/1000 ≤ R`, and `L M (δ + e) < m²`, the code
  accepts the step and `|cand - r| < e`.
* `newtonLoop_le`, `newtonLoop_contracts`: under the same condition with `1/1000` in
  place of `δ`, no step of the three-step loop moves away from `r`, and the loop's
  result is within `M (δ + e) / m · e` of `r`.
* `ceScore_not_wellCond`: the counterexample's score violates the condition. Its
  secant slope is `-1` on `[0, 1/1000]` and `-1e-12` on `[1/200, 6/1000]`, so `L/m ≥ 1e12`
  inside the probe reach and `L M (δ + e) ≥ m²`.

Everything is exact real arithmetic. The floor that bounds real accuracy on flat
peaks, score rounding divided by `|curvature|`, is outside this model: the theorems say
nothing about peaks with `|s'|` near the rounding level of `s`.
-/

namespace JammaLean

open Set

/-- A smooth, well-conditioned peak at `r`: on `[r - R, r + R]` the score has
derivative `s'` with `-L ≤ s' ≤ -m < 0`, `s'` is `M`-Lipschitz, and `s r = 0`. -/
structure WellCond (s s' : ℝ → ℝ) (r R m L M : ℝ) : Prop where
  deriv : ∀ t, |t - r| ≤ R → HasDerivAt s (s' t) t
  upper : ∀ t, |t - r| ≤ R → s' t ≤ -m
  lower : ∀ t, |t - r| ≤ R → -L ≤ s' t
  lip : ∀ t u, |t - r| ≤ R → |u - r| ≤ R → |s' t - s' u| ≤ M * |t - u|
  root : s r = 0
  m_pos : 0 < m
  M_nonneg : 0 ≤ M

namespace WellCond

variable {s s' : ℝ → ℝ} {r R m L M : ℝ}

lemma abs_deriv_le (h : WellCond s s' r R m L M) {t : ℝ} (ht : |t - r| ≤ R) :
    |s' t| ≤ L := by
  have := h.upper t ht; have := h.lower t ht; have := h.m_pos
  rw [abs_le]; constructor <;> linarith

lemma le_abs_deriv (h : WellCond s s' r R m L M) {t : ℝ} (ht : |t - r| ≤ R) :
    m ≤ |s' t| := by
  have := h.upper t ht
  rw [abs_of_neg (by linarith [h.m_pos])]; linarith

lemma m_le_L (h : WellCond s s' r R m L M) (hR : 0 ≤ R) : m ≤ L := by
  have h0 : |r - r| ≤ R := by simpa using hR
  linarith [h.upper r h0, h.lower r h0]

/-- Mean value theorem on `J`: `s v - s u = s' ξ (v - u)` with `ξ` between `u` and `v`. -/
lemma slope (h : WellCond s s' r R m L M) {u v : ℝ} (hu : |u - r| ≤ R) (hv : |v - r| ≤ R) :
    ∃ ξ, |ξ - r| ≤ R ∧ |ξ - u| ≤ |v - u| ∧ |ξ - v| ≤ |v - u| ∧
      s v - s u = s' ξ * (v - u) := by
  rw [abs_le] at hu hv
  have hmem : ∀ a b, a < b → a ∈ Icc (r - R) (r + R) → b ∈ Icc (r - R) (r + R) →
      ∃ ξ ∈ Ioo a b, s' ξ = (s b - s a) / (b - a) := by
    intro a b hab ha hb
    refine exists_hasDerivAt_eq_slope s s' hab (fun t ht => ?_) (fun t ht => ?_)
    · exact (h.deriv t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ha.1, hb.2]))
        |>.continuousAt.continuousWithinAt
    · exact h.deriv t (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ha.1, hb.2])
  rcases lt_trichotomy u v with huv | rfl | huv
  · obtain ⟨ξ, hξ, hs⟩ := hmem u v huv ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    refine ⟨ξ, by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2], ?_, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hξ.1]), abs_of_pos (by linarith)]; linarith [hξ.2]
    · rw [abs_of_neg (by linarith [hξ.2]), abs_of_pos (by linarith)]; linarith [hξ.1]
    · rw [hs]; field_simp [(sub_pos.mpr huv).ne']
  · exact ⟨u, by rw [abs_le]; constructor <;> linarith, by simp, by simp, by simp⟩
  · obtain ⟨ξ, hξ, hs⟩ := hmem v u huv ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    refine ⟨ξ, by rw [abs_le]; constructor <;> linarith [hξ.1, hξ.2], ?_, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hξ.2]), abs_of_neg (by linarith)]; linarith [hξ.1]
    · rw [abs_of_pos (by linarith [hξ.1]), abs_of_neg (by linarith)]; linarith [hξ.2]
    · rw [hs]; field_simp [(sub_pos.mpr huv).ne']; ring

/-- **Core step bound.** A Newton-type step `x - s x / s' ξ` that uses the slope at
some `ξ ∈ J` lands within `M (|ξ - x| + |x - r|) / m · |x - r|` of the root. -/
theorem step_error (h : WellCond s s' r R m L M) {x ξ : ℝ} (hx : |x - r| ≤ R)
    (hξ : |ξ - r| ≤ R) :
    |x - s x / s' ξ - r| ≤ M * (|ξ - x| + |x - r|) / m * |x - r| := by
  have hr : |r - r| ≤ R := by simpa using (abs_nonneg _).trans hx
  obtain ⟨η, hη, hηx, -, hsη⟩ := h.slope hx hr
  have hsx : s x = s' η * (x - r) := by linear_combination -hsη + h.root
  have hκ := h.upper ξ hξ
  have hm := h.m_pos
  have hκ0 : s' ξ ≠ 0 := by linarith
  have key : x - s x / s' ξ - r = (x - r) * (s' ξ - s' η) / s' ξ := by
    rw [hsx]; field_simp; ring
  have hdist : |ξ - η| ≤ |ξ - x| + |x - r| := by
    calc |ξ - η| ≤ |ξ - x| + |x - η| := abs_sub_le ξ x η
      _ ≤ |ξ - x| + |x - r| := by
        rw [abs_sub_comm x η, abs_sub_comm x r]; linarith
  have hA : |s' ξ - s' η| ≤ M * (|ξ - x| + |x - r|) :=
    (h.lip ξ η hξ hη).trans (mul_le_mul_of_nonneg_left hdist h.M_nonneg)
  rw [key, abs_div, abs_mul]
  calc |x - r| * |s' ξ - s' η| / |s' ξ|
      ≤ |x - r| * (M * (|ξ - x| + |x - r|)) / m :=
        div_le_div₀ (by have := h.M_nonneg; positivity)
          (mul_le_mul_of_nonneg_left hA (abs_nonneg _)) hm (h.le_abs_deriv hξ)
    _ = M * (|ξ - x| + |x - r|) / m * |x - r| := by ring

/-- **Exact-derivative Newton** converges quadratically:
`|x - s x / s' x - r| ≤ (M / m) |x - r|²`. -/
theorem newton_exact_error (h : WellCond s s' r R m L M) {x : ℝ} (hx : |x - r| ≤ R) :
    |x - s x / s' x - r| ≤ M / m * |x - r| ^ 2 := by
  have := h.step_error hx hx
  simp only [sub_self, abs_zero, zero_add] at this
  calc _ ≤ _ := this
    _ = M / m * |x - r| ^ 2 := by ring

/-- The central difference is the derivative at some `ξ` within `δ` of `x`. -/
lemma curv_eq (h : WellCond s s' r R m L M) {x δ : ℝ} (hδ : 0 < δ)
    (h1 : |x - δ - r| ≤ R) (h2 : |x + δ - r| ≤ R) :
    ∃ ξ, |ξ - r| ≤ R ∧ |ξ - x| ≤ δ ∧ curv s x δ = s' ξ := by
  obtain ⟨ξ, hξ, ha, hb, hs⟩ := h.slope h1 h2
  refine ⟨ξ, hξ, ?_, ?_⟩
  · have e : |x + δ - (x - δ)| = 2 * δ := by
      rw [show x + δ - (x - δ) = 2 * δ by ring, abs_of_pos (by linarith)]
    rw [e, abs_le] at ha hb; rw [abs_le]; constructor <;> linarith [ha.1, hb.2]
  · unfold curv; rw [hs]; field_simp; ring

/-- **Finite-difference curvature error** is first order in the probe offset:
`|curv s x δ - s' x| ≤ M δ`. -/
theorem curv_error (h : WellCond s s' r R m L M) {x δ : ℝ} (hδ : 0 < δ)
    (hx : |x - r| ≤ R) (h1 : |x - δ - r| ≤ R) (h2 : |x + δ - r| ≤ R) :
    |curv s x δ - s' x| ≤ M * δ := by
  obtain ⟨ξ, hξ, hξx, hc⟩ := h.curv_eq hδ h1 h2
  rw [hc]
  exact (h.lip ξ x hξ hx).trans (mul_le_mul_of_nonneg_left hξx h.M_nonneg)

lemma probeDelta_le (lo hi x : ℝ) : probeDelta lo hi x ≤ 1 / 1000 :=
  (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))

lemma probes_near {lo hi x : ℝ} (hR : |x - r| + 1 / 1000 ≤ R) (hδ : 0 ≤ probeDelta lo hi x) :
    |x - probeDelta lo hi x - r| ≤ R ∧ |x + probeDelta lo hi x - r| ≤ R := by
  have hd := probeDelta_le lo hi x
  have ha := abs_le.mp (le_refl |x - r|)
  constructor <;> rw [abs_le] <;> constructor <;> linarith [ha.1, ha.2]

/-- **The code's candidate** contracts toward the root:
`|cand - r| ≤ M (δ + |x - r|) / m · |x - r|` with `δ = probeDelta lo hi x`. -/
theorem cand_error (h : WellCond s s' r R m L M) {lo hi x : ℝ} (h1 : lo < x) (h2 : x < hi)
    (hR : |x - r| + 1 / 1000 ≤ R) :
    |cand s lo hi x - r| ≤ M * (probeDelta lo hi x + |x - r|) / m * |x - r| := by
  have hδ := probeDelta_pos h1 h2
  obtain ⟨hp1, hp2⟩ := probes_near (lo := lo) (hi := hi) hR hδ.le
  obtain ⟨ξ, hξ, hξx, hc⟩ := h.curv_eq hδ hp1 hp2
  have hx : |x - r| ≤ R := by linarith
  have := h.step_error hx hξ
  unfold cand; rw [hc]
  have hM := h.M_nonneg; have hm := h.m_pos.le
  refine this.trans ?_
  gcongr

/-- **Acceptance.** On a well-conditioned peak with `L M (δ + e) < m²`, where
`e = |x - r| > 0` and `[r - e, r + e]` lies strictly inside the coarse bracket, the
code accepts the Newton step and the step strictly reduces the error. -/
theorem accepts_of_wellCond (h : WellCond s s' r R m L M) {lo hi x : ℝ}
    (hlo : lo < r - |x - r|) (hhi : r + |x - r| < hi) (hR : |x - r| + 1 / 1000 ≤ R)
    (hxr : x ≠ r) (hcond : L * M * (probeDelta lo hi x + |x - r|) < m ^ 2) :
    Accepts s lo hi x ∧ |cand s lo hi x - r| < |x - r| := by
  have he : 0 < |x - r| := abs_pos.mpr (sub_ne_zero.mpr hxr)
  have hxa := abs_le.mp (le_refl |x - r|)
  have h1 : lo < x := by linarith [hxa.1]
  have h2 : x < hi := by linarith [hxa.2]
  have hδ := probeDelta_pos h1 h2
  have hm := h.m_pos
  have hM := h.M_nonneg
  have hx : |x - r| ≤ R := by linarith
  have hLm := h.m_le_L (by linarith [abs_nonneg (x - r)])
  set e := |x - r| with he_def
  set δ := probeDelta lo hi x with hδ_def
  set c := cand s lo hi x with hc_def
  -- A := M (δ + e) < m
  have hA0 : 0 ≤ M * (δ + e) := by positivity
  have hAm : M * (δ + e) < m := by
    have : M * (δ + e) * m ≤ M * (δ + e) * L := mul_le_mul_of_nonneg_left hLm hA0
    nlinarith
  have hcr := h.cand_error h1 h2 hR
  rw [← hδ_def, ← hc_def] at hcr
  have hcr' : |c - r| * m ≤ M * (δ + e) * e := by
    have := (mul_le_mul_of_nonneg_right hcr hm.le)
    calc |c - r| * m ≤ M * (δ + e) / m * e * m := this
      _ = M * (δ + e) * e := by field_simp
  have hclose : |c - r| < e := by
    by_contra hc; rw [not_lt] at hc
    nlinarith [mul_le_mul_of_nonneg_left hc hm.le]
  refine ⟨⟨hδ, ?_, ?_, ?_, ?_⟩, hclose⟩
  · obtain ⟨hp1, hp2⟩ := probes_near (lo := lo) (hi := hi) hR hδ.le
    obtain ⟨ξ, hξ, -, hcv⟩ := h.curv_eq hδ hp1 hp2
    rw [hcv]; linarith [h.upper ξ hξ]
  · linarith [(abs_lt.mp hclose).1]
  · linarith [(abs_lt.mp hclose).2]
  · have hcJ : |c - r| ≤ R := by linarith
    have hrJ : |r - r| ≤ R := by simpa using (abs_nonneg _).trans hx
    obtain ⟨ζ, hζ, -, -, hsc⟩ := h.slope hrJ hcJ
    obtain ⟨η, hη, -, -, hsx⟩ := h.slope hrJ hx
    rw [h.root, sub_zero] at hsc hsx
    rw [hsc, hsx, abs_mul, abs_mul]
    have hLz := h.abs_deriv_le hζ
    have hmη := h.le_abs_deriv hη
    -- |s c| ≤ L |c - r| and L |c - r| m ≤ L M (δ + e) e < m² e
    have k1 : |s' ζ| * |c - r| ≤ L * |c - r| :=
      mul_le_mul_of_nonneg_right hLz (abs_nonneg _)
    have k2 : L * |c - r| * m < m * e * m := by
      have hL0 : 0 ≤ L := by linarith
      calc L * |c - r| * m = L * (|c - r| * m) := by ring
        _ ≤ L * (M * (δ + e) * e) := mul_le_mul_of_nonneg_left hcr' hL0
        _ = L * M * (δ + e) * e := by ring
        _ < m ^ 2 * e := mul_lt_mul_of_pos_right hcond he
        _ = m * e * m := by ring
    have k3 : L * |c - r| < m * e := lt_of_mul_lt_mul_right k2 hm.le
    have k4 : m * e ≤ |s' η| * e := mul_le_mul_of_nonneg_right hmη he.le
    linarith

/-- **No step of the loop moves away from the root.** With `e₀` fixing a ball
`[r - e₀, r + e₀]` strictly inside the coarse bracket and `L M (1/1000 + e₀) < m²`,
every start within `e₀` of `r` ends at least as close. -/
theorem newtonLoop_le (h : WellCond s s' r R m L M) {lo hi e₀ : ℝ}
    (hlo : lo < r - e₀) (hhi : r + e₀ < hi) (hR : e₀ + 1 / 1000 ≤ R)
    (hcond : L * M * (1 / 1000 + e₀) < m ^ 2) :
    ∀ (k : ℕ) (y : ℝ), |y - r| ≤ e₀ → |newtonLoop s lo hi k y - r| ≤ |y - r| := by
  have step : ∀ y, |y - r| ≤ e₀ → Accepts s lo hi y → |cand s lo hi y - r| < |y - r| := by
    intro y hy hA
    have hLM : 0 ≤ L * M :=
      mul_nonneg (by linarith [h.m_le_L (by linarith [abs_nonneg (y - r)]), h.m_pos])
        h.M_nonneg
    by_cases hyr : y = r
    · have := hA.2.2.2.2
      rw [hyr, h.root, abs_zero] at this
      exact absurd this (not_lt.mpr (abs_nonneg _))
    · refine (h.accepts_of_wellCond (by linarith) (by linarith) (by linarith) hyr ?_).2
      calc L * M * (probeDelta lo hi y + |y - r|) ≤ L * M * (1 / 1000 + e₀) :=
            mul_le_mul_of_nonneg_left (add_le_add (probeDelta_le lo hi y) hy) hLM
        _ < m ^ 2 := hcond
  intro k
  induction k with
  | zero => intro y _; exact le_rfl
  | succ k ih =>
    intro y hy
    unfold newtonLoop
    split_ifs with hA
    · have hc := step y hy hA
      exact (ih _ (by linarith)).trans hc.le
    · exact (step y hy hA).le
    · exact le_rfl

/-- **Three-step loop on a well-conditioned peak.** From `x ≠ r` with
`e = |x - r|`, the first step is accepted, and the loop's result is within
`M (δ + e) / m · e < e` of the root, whatever the stopping rule does afterwards. -/
theorem newtonLoop_contracts (h : WellCond s s' r R m L M) {lo hi x : ℝ}
    (hlo : lo < r - |x - r|) (hhi : r + |x - r| < hi) (hR : |x - r| + 1 / 1000 ≤ R)
    (hxr : x ≠ r) (hcond : L * M * (1 / 1000 + |x - r|) < m ^ 2) (k : ℕ) :
    Accepts s lo hi x ∧
      |newtonLoop s lo hi (k + 1) x - r| ≤
        M * (probeDelta lo hi x + |x - r|) / m * |x - r| ∧
      M * (probeDelta lo hi x + |x - r|) / m * |x - r| < |x - r| := by
  have hLM : 0 ≤ L * M :=
    mul_nonneg (by linarith [h.m_le_L (by linarith [abs_nonneg (x - r)]), h.m_pos])
      h.M_nonneg
  have hcond' : L * M * (probeDelta lo hi x + |x - r|) < m ^ 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (add_le_add_left (probeDelta_le lo hi x) _) hLM) hcond
  obtain ⟨hA, hclose⟩ := h.accepts_of_wellCond hlo hhi hR hxr hcond'
  have hxa := abs_le.mp (le_refl |x - r|)
  have hcr := h.cand_error (lo := lo) (hi := hi) (by linarith [hxa.1]) (by linarith [hxa.2]) hR
  have hloop := h.newtonLoop_le hlo hhi hR hcond k
  refine ⟨hA, ?_, ?_⟩
  · unfold newtonLoop
    rw [ite_eq_left_of_eq_true _ _ (eq_true hA)]
    split_ifs
    · exact (hloop _ hclose.le).trans hcr
    · exact hcr
  · -- M (δ + e) < m follows from the condition, as in `accepts_of_wellCond`
    have hm := h.m_pos
    have he : 0 < |x - r| := abs_pos.mpr (sub_ne_zero.mpr hxr)
    have hLm := h.m_le_L (by linarith [abs_nonneg (x - r)])
    have hlx : lo < x := by linarith [hxa.1]
    have hxh : x < hi := by linarith [hxa.2]
    have hA0 : 0 ≤ M * (probeDelta lo hi x + |x - r|) :=
      mul_nonneg h.M_nonneg (by linarith [probeDelta_pos hlx hxh])
    have hAm : M * (probeDelta lo hi x + |x - r|) < m := by
      have := mul_le_mul_of_nonneg_left hLm hA0
      nlinarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hm]
    nlinarith

end WellCond

/-- **The counterexample is not well-conditioned.** For any `s'`, `m`, `L`, `M` and
any `R ≥ 6/1000` (the reach of the probes from `x = 0` around `r = 1/200`), if
`ceScore` satisfied `WellCond` then `L M (1/1000 + 1/200) ≥ m²`: the condition of
`accepts_of_wellCond` fails at the counterexample's start. The proof reads `ceScore`
only at `0`, `1/1000`, `1/200` and `6/1000`, so it applies equally to any smooth score
through those four values. -/
theorem ceScore_not_wellCond {s' : ℝ → ℝ} {R m L M : ℝ}
    (h : WellCond ceScore s' (1 / 200) R m L M) (hR : 6 / 1000 ≤ R) :
    m ^ 2 ≤ L * M * (1 / 1000 + 1 / 200) := by
  have mem : ∀ t : ℝ, 0 ≤ t → t ≤ 6 / 1000 → |t - 1 / 200| ≤ R := fun t h1 h2 => by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨ξ₁, hξ₁, h1a, h1b, hs₁⟩ :=
    h.slope (mem 0 le_rfl (by norm_num)) (mem (1 / 1000) (by norm_num) (by norm_num))
  obtain ⟨ξ₂, hξ₂, h2a, h2b, hs₂⟩ :=
    h.slope (mem (1 / 200) (by norm_num) (by norm_num)) (mem (6 / 1000) (by norm_num) le_rfl)
  have e₁ : s' ξ₁ = -1 := by
    unfold ceScore at hs₁; norm_num at hs₁; linarith
  have e₂ : s' ξ₂ = -1e-12 := by
    unfold ceScore at hs₂; norm_num at hs₂; linarith
  have hm2 : m ≤ 1e-12 := by linarith [h.upper ξ₂ hξ₂]
  have hL1 : 1 ≤ L := by linarith [h.lower ξ₁ hξ₁]
  have hlip := h.lip ξ₁ ξ₂ hξ₁ hξ₂
  rw [e₁, e₂] at hlip
  norm_num at h1a h1b h2a h2b
  have hd : |ξ₁ - ξ₂| ≤ 6 / 1000 := by
    rw [abs_le] at h1a h1b h2a h2b ⊢; constructor <;> linarith [h1a.1, h1b.2, h2a.1, h2b.2]
  have hM : 1 / 2 ≤ M := by
    norm_num at hlip
    nlinarith [h.M_nonneg]
  have hm := h.m_pos
  nlinarith

end JammaLean
