import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# P-values: the F(1, df) and χ²(1) upper tails

JAMMA turns its test statistics into p-values with two closed forms.

* `_f_to_pvalue` (`src/jamma/lmm/stats.py`), used for the Wald and Score tests, returns
  `betainc_batch(df/2, 1/2, z)` with `z = df / (df + F)` and the exact complement
  `f / (df + f)`, and returns 1 when `F ≤ 0`. `docs/GEMMA_EQUIVALENCE.md` §6 ("F-Distribution
  CDF") claims this is GEMMA's `gsl_cdf_fdist_Q(F, 1, df)`, the F(1, df) upper tail.
* `chi2_sf_batch` (`src/jamma/lmm/special.py`), used for the LRT (§8), returns
  `erfc(sqrt(x / 2))` as `P(χ²₁ > x)`.

`docs/GEMMA_NUMERICAL_EQUIVALENCE_BOUND.md` Assumption 7 ("CDF stability") and its §5 bound
`|Δp| ≤ L_CDF · |ΔF| + δ_CDF` assume both tails are Lipschitz "in the relevant range".

Proved here, for every real `m > 0` (the degrees of freedom):

* `fTail_eq_incBeta`: for `F ≥ 0`, `∫ x in Ioi F, fPDF m x = incBeta (m/2) (1/2) (m/(m+F))`,
  i.e. `betainc(df/2, 1/2, df/(df+F))` is the F(1, df) upper tail (§6). The proof
  substitutes `x = m/t - m`.
* `fTail_zero`: `fPDF m` integrates to 1 over `(0, ∞)`, so it is a probability density and
  the `F ≤ 0 ↦ 1` branch is the correct limit. `incBeta_one` normalises the kernel through
  Mathlib's `beta`.
* `chiSq1_tail_eq_erfc`: for `x ≥ 0` and `Z ~ gaussianReal 0 1`,
  `P(Z² > x) = erfc (√(x/2))` with `erfc y = (2/√π) ∫_y^∞ e^{-t²}`, which is
  `chi2_sf_batch`'s formula (§8). χ²(1) enters as the law of `Z²`, its definition;
  Mathlib has no chi-squared distribution to connect to. `two_gaussian_tail_eq_erfc` is the
  Gaussian-tail step.
* Assumption 7: `fTail_antitoneOn`, `fPDF_antitoneOn` (the density decreases on `(0, ∞)`),
  and `fTail_lipschitzOn`, Lipschitz on `[F₀, ∞)` with constant `fPDF m F₀` for `F₀ > 0`.
  The range qualifier is necessary: `tendsto_fPDF_zero` shows the density tends to `∞` at
  `0⁺`, and `fTail_not_lipschitzOn` shows the tail has no Lipschitz constant on `(0, ∞)`.
  For χ²(1): `chiSq1_tail_antitone`, `erfc_sqrt_half_antitone`, and
  `erfc_sqrt_half_not_lipschitzOn`. The last one contradicts §8's remark that "near LRT ~ 0
  the CDF is linear": the χ²(1) tail has infinite slope at 0.

Out of scope: the numerical accuracy of the Cephes (`betainc_batch`) and GSL incomplete-beta
algorithms and of libm `erfc`, i.e. the `δ_CDF` term. These theorems pin down the exact
functions those routines approximate.
-/

open MeasureTheory Set Real ProbabilityTheory Filter Topology

namespace JammaLean

/-- The F(1, m) density on `x > 0`. Off `(0, ∞)` the value is junk and never used. -/
noncomputable def fPDF (m x : ℝ) : ℝ :=
  x ^ (-(1 / 2 : ℝ)) * (1 + x / m) ^ (-(m + 1) / 2) / (beta (1 / 2) (m / 2) * √m)

lemma beta_comm (a b : ℝ) : beta a b = beta b a := by
  unfold beta; rw [mul_comm, add_comm]

lemma subst_integrand {m t : ℝ} (hm : 0 < m) (ht : 0 < t) (ht1 : t < 1) :
    |-(m / t ^ 2)| * fPDF m (m / t - m) =
      t ^ (m / 2 - 1) * (1 - t) ^ ((1 / 2 : ℝ) - 1) / beta (m / 2) (1 / 2) := by
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  have h1t : 0 < 1 - t := by linarith
  have hx : m / t - m = m * (1 - t) * t⁻¹ := by field_simp
  have hy : 1 + m * (1 - t) * t⁻¹ / m = t⁻¹ := by field_simp; ring
  rw [abs_neg, abs_of_pos (by positivity), fPDF, hx, hy, beta_comm,
    mul_rpow (by positivity) (by positivity), mul_rpow (by positivity) h1t.le,
    inv_rpow ht.le, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_neg ht.le,
    sqrt_eq_rpow, ← rpow_two]
  have hB := beta_pos (show (0:ℝ) < m / 2 by positivity) (show (0:ℝ) < 1 / 2 by norm_num)
  rw [rpow_neg hm.le, rpow_def_of_pos hm, rpow_def_of_pos ht, rpow_def_of_pos ht,
    rpow_def_of_pos ht, rpow_def_of_pos ht]
  have hmm : rexp (log m * (1 / 2)) * rexp (log m * (1 / 2)) = m := by
    rw [← exp_add, ← exp_log hm]; congr 1; rw [exp_log hm]; ring
  have ht2 : rexp (log t * 2) = rexp (log t * - -(1 / 2)) * rexp (log t * -(-(m + 1) / 2)) *
      (rexp (log t * (m / 2 - 1)))⁻¹ := by
    rw [← exp_neg, ← exp_add, ← exp_add]; congr 1; ring
  rw [ht2]
  set A := rexp (log m * (1 / 2))
  set P := rexp (log t * - -(1 / 2))
  set Q := rexp (log t * -(-(m + 1) / 2))
  set R := rexp (log t * (m / 2 - 1))
  set U := (1 - t) ^ (-(1 / 2) : ℝ)
  set B := beta (m / 2) (1 / 2)
  have : 0 < A := exp_pos _
  have : 0 < P := exp_pos _
  have : 0 < Q := exp_pos _
  have : 0 < R := exp_pos _
  field_simp
  linear_combination (-U) * hmm

/-- The regularised incomplete beta `I_z(a, b)`, the function `betainc(a, b, z)` computes. -/
noncomputable def incBeta (a b z : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..z, t ^ (a - 1) * (1 - t) ^ (b - 1)) / beta a b

/-- The F(1, m) upper tail `P(F(1, m) > F)`, the Wald and Score p-value. -/
noncomputable def fTail (m F : ℝ) : ℝ := ∫ x in Ioi F, fPDF m x

lemma image_subst {m F : ℝ} (hm : 0 < m) (hF : 0 ≤ F) :
    (fun t => m / t - m) '' Ioo 0 (m / (m + F)) = Ioi F := by
  ext x
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨t, ⟨ht, htz⟩, rfl⟩
    rw [lt_div_iff₀ (by linarith)] at htz
    rw [lt_sub_iff_add_lt, lt_div_iff₀ ht]
    linarith
  · intro hx
    refine ⟨m / (m + x), ⟨div_pos hm (by linarith), ?_⟩, ?_⟩
    · exact div_lt_div_of_pos_left hm (by linarith) (by linarith)
    · field_simp; ring

lemma hasDerivAt_subst {m t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t => m / t - m) (-(m / t ^ 2)) t := by
  have := ((hasDerivAt_inv ht).const_mul m).sub_const m
  convert this using 1
  · funext s; rw [div_eq_mul_inv]
  · field_simp

lemma injOn_subst {m : ℝ} (hm : 0 < m) (z : ℝ) :
    InjOn (fun t => m / t - m) (Ioo 0 z) := by
  intro a ha b hb h
  simp only at h
  have h' : m / a = m / b := by linarith
  rw [div_eq_div_iff ha.1.ne' hb.1.ne'] at h'
  nlinarith [mul_comm m b]

/-- §6: `betainc(df/2, 1/2, df/(df+F))` is the F(1, df) upper tail at `F`. -/
theorem fTail_eq_incBeta {m F : ℝ} (hm : 0 < m) (hF : 0 ≤ F) :
    fTail m F = incBeta (m / 2) (1 / 2) (m / (m + F)) := by
  have hz : m / (m + F) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  rw [fTail, ← image_subst hm hF, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (hasDerivAt_subst ht.1.ne').hasDerivWithinAt) (injOn_subst hm _),
    incBeta, intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo,
    ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [smul_eq_mul]
  exact subst_integrand hm ht.1 (ht.2.trans_le hz)

lemma kernel_eq_re {a b x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    x ^ (a - 1) * (1 - x) ^ (b - 1) =
      ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)).re := by
  have h0 : 0 ≤ x := hx.1.le
  have h1 : 0 ≤ 1 - x := by linarith [hx.2]
  rw [show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
    show ((b : ℂ) - 1) = ((b - 1 : ℝ) : ℂ) by push_cast; ring,
    show (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow h0, ← Complex.ofReal_cpow h1, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma intervalIntegrable_kernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) volume 0 1 := by
  have hc := (Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hc ⊢
  refine (hc.re).congr_fun (fun x hx => (kernel_eq_re hx).symm) measurableSet_Ioc

/-- The incomplete beta reaches 1 at `z = 1`. -/
theorem incBeta_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : incBeta a b 1 = 1 := by
  have hc := (Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hc
  rw [incBeta, div_eq_one_iff_eq (beta_pos ha hb).ne', beta_eq_betaIntegralReal a b ha hb,
    Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, ← RCLike.re_to_complex, ← integral_re hc]
  exact setIntegral_congr_fun measurableSet_Ioc fun x hx => kernel_eq_re hx

/-- `fPDF m` is a probability density on `(0, ∞)`; this is also `_f_to_pvalue`'s `F ≤ 0` value. -/
theorem fTail_zero {m : ℝ} (hm : 0 < m) : fTail m 0 = 1 := by
  rw [fTail_eq_incBeta hm le_rfl, add_zero, div_self hm.ne']
  exact incBeta_one (by positivity) (by norm_num)

section Monotone

variable {m : ℝ}

lemma fPDF_const_pos (hm : 0 < m) : 0 < beta (1 / 2) (m / 2) * √m :=
  mul_pos (beta_pos (by norm_num) (by positivity)) (sqrt_pos.2 hm)

theorem fPDF_nonneg (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fPDF m x := by
  unfold fPDF
  have := fPDF_const_pos hm
  positivity

theorem fPDF_pos (hm : 0 < m) {x : ℝ} (hx : 0 < x) : 0 < fPDF m x := by
  unfold fPDF
  have := fPDF_const_pos hm
  positivity

/-- The F(1, m) density is decreasing on `(0, ∞)`. -/
theorem fPDF_antitoneOn (hm : 0 < m) : AntitoneOn (fPDF m) (Ioi 0) := by
  intro x hx y hy hxy
  have hx : (0 : ℝ) < x := hx
  have hy : (0 : ℝ) < y := hy
  unfold fPDF
  apply div_le_div_of_nonneg_right _ (fPDF_const_pos hm).le
  exact mul_le_mul (rpow_le_rpow_of_nonpos hx hxy (by norm_num))
    (rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by linarith)) (by positivity)
    (by positivity)

theorem integrableOn_fPDF (hm : 0 < m) {F : ℝ} (hF : 0 ≤ F) :
    IntegrableOn (fPDF m) (Ioi F) := by
  have hz : m / (m + F) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  rw [← image_subst hm hF, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (hasDerivAt_subst ht.1.ne').hasDerivWithinAt) (injOn_subst hm _)]
  have hk : IntegrableOn (fun t : ℝ => t ^ (m / 2 - 1) * (1 - t) ^ ((1 / 2 : ℝ) - 1) /
      beta (m / 2) (1 / 2)) (Ioc 0 1) :=
    (intervalIntegrable_kernel (a := m / 2) (b := 1 / 2) (by positivity)
      (by norm_num)).1.div_const _
  refine ((hk.mono_set Ioo_subset_Ioc_self).mono_set (Ioo_subset_Ioo_right hz)).congr_fun
    (fun t ht => ?_) measurableSet_Ioo
  simp only [smul_eq_mul]
  exact (subst_integrand hm ht.1 (ht.2.trans_le hz)).symm

lemma fTail_sub (hm : 0 < m) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    fTail m a - fTail m b = ∫ x in a..b, fPDF m x := by
  rw [fTail, fTail, ← Ioc_union_Ioi_eq_Ioi hab, setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi ((integrableOn_fPDF hm ha).mono_set Ioc_subset_Ioi_self)
    (integrableOn_fPDF hm (ha.trans hab)), intervalIntegral.integral_of_le hab]
  ring

lemma intervalIntegrable_fPDF (hm : 0 < m) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fPDF m) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    ((integrableOn_fPDF hm ha).mono_set Ioc_subset_Ioi_self)

/-- On `[a, b] ⊆ (0, ∞)` the tail drop lies between `(b - a) fPDF b` and `(b - a) fPDF a`. -/
lemma fTail_sub_bounds (hm : 0 < m) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * fPDF m b ≤ fTail m a - fTail m b ∧ fTail m a - fTail m b ≤ (b - a) * fPDF m a := by
  rw [fTail_sub hm ha.le hab]
  have hmem : ∀ x ∈ Icc a b, x ∈ Ioi (0 : ℝ) := fun x hx => ha.trans_le hx.1
  constructor
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (intervalIntegrable_fPDF hm ha.le hab)
      (fun x hx => fPDF_antitoneOn hm (hmem x hx) (hmem b ⟨hab, le_rfl⟩) hx.2)
    simpa [intervalIntegral.integral_const] using this
  · have := intervalIntegral.integral_mono_on hab (intervalIntegrable_fPDF hm ha.le hab)
      intervalIntegrable_const
      (fun x hx => fPDF_antitoneOn hm (hmem a ⟨le_rfl, hab⟩) (hmem x hx) hx.1)
    simpa [intervalIntegral.integral_const] using this

/-- The p-value `F ↦ P(F(1, m) > F)` is antitone on `[0, ∞)`. -/
theorem fTail_antitoneOn (hm : 0 < m) : AntitoneOn (fTail m) (Ici 0) := by
  intro a ha b _ hab
  have := fTail_sub hm ha hab
  have h0 : 0 ≤ ∫ x in a..b, fPDF m x :=
    intervalIntegral.integral_nonneg hab fun x hx => fPDF_nonneg hm (ha.trans hx.1)
  linarith

/-- Assumption 7 on the relevant range: for `F₀ > 0` the p-value is Lipschitz on `[F₀, ∞)`
with constant `fPDF m F₀`. -/
theorem fTail_lipschitzOn (hm : 0 < m) {F₀ : ℝ} (hF₀ : 0 < F₀) :
    LipschitzOnWith (fPDF m F₀).toNNReal (fTail m) (Ici F₀) := by
  have key : ∀ a ∈ Ici F₀, ∀ b ∈ Ici F₀, a ≤ b →
      dist (fTail m a) (fTail m b) ≤ (fPDF m F₀).toNNReal * dist a b := by
    intro a ha b hb hab
    have ha' : 0 < a := hF₀.trans_le ha
    obtain ⟨hlo, hhi⟩ := fTail_sub_bounds hm ha' hab
    have hpb : 0 ≤ fPDF m b := fPDF_nonneg hm (ha'.le.trans hab)
    have hmono : fPDF m a ≤ fPDF m F₀ := fPDF_antitoneOn hm hF₀ ha' ha
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by nlinarith), abs_of_nonpos (by linarith),
      Real.coe_toNNReal _ (fPDF_nonneg hm hF₀.le)]
    nlinarith
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rcases le_total a b with hab | hba
  · exact key a ha b hb hab
  · rw [dist_comm, dist_comm a]; exact key b hb a ha hba

/-- The F(1, m) density blows up at `0⁺`. -/
theorem tendsto_fPDF_zero (hm : 0 < m) : Tendsto (fPDF m) (𝓝[>] 0) atTop := by
  have hC := fPDF_const_pos hm
  have hg : Tendsto (fun x : ℝ => (1 + x / m) ^ (-(m + 1) / 2) / (beta (1 / 2) (m / 2) * √m))
      (𝓝[>] 0) (𝓝 (1 / (beta (1 / 2) (m / 2) * √m))) := by
    have hc : Continuous fun x : ℝ => 1 + x / m := by fun_prop
    have := ((hc.continuousAt (x := 0)).rpow_const (p := -(m + 1) / 2)
      (Or.inl (by simp))).tendsto.div_const (beta (1 / 2) (m / 2) * √m)
    simpa using this.mono_left nhdsWithin_le_nhds
  have := (tendsto_rpow_neg_nhdsGT_zero (y := -(1 / 2 : ℝ)) (by norm_num)).atTop_mul_pos
    (by positivity) hg
  refine this.congr' (Eventually.of_forall fun x => ?_)
  simp only [fPDF]
  ring

/-- Assumption 7 needs its range qualifier: the p-value is not Lipschitz on `(0, ∞)`. -/
theorem fTail_not_lipschitzOn (hm : 0 < m) :
    ¬ ∃ K, LipschitzOnWith K (fTail m) (Ioi 0) := by
  rintro ⟨K, hK⟩
  obtain ⟨b, hbL, hb⟩ := (((tendsto_fPDF_zero hm).eventually (eventually_gt_atTop (K : ℝ))).and
    self_mem_nhdsWithin).exists
  have hb : (0 : ℝ) < b := hb
  have ha : (0 : ℝ) < b / 2 := by positivity
  have hlip := hK.dist_le_mul (b / 2) ha b hb
  obtain ⟨hlo, -⟩ := fTail_sub_bounds hm ha (b := b) (by linarith)
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (by nlinarith [fPDF_pos hm hb]),
    abs_of_nonpos (by linarith)] at hlip
  nlinarith

end Monotone

section ChiSquared

/-- The complementary error function, defined by its integral. -/
noncomputable def erfc (y : ℝ) : ℝ := 2 / √π * ∫ t in Ioi y, rexp (-t ^ 2)

lemma gaussianPDFReal_std (s : ℝ) :
    gaussianPDFReal 0 1 s = (√(2 * π))⁻¹ * rexp (-s ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- Twice the standard-normal tail beyond `√x` is `erfc (√(x/2))`. -/
theorem two_gaussian_tail_eq_erfc (x : ℝ) :
    2 * ∫ s in Ioi (√x), gaussianPDFReal 0 1 s = erfc (√(x / 2)) := by
  have h2 : (0 : ℝ) < √2 := by positivity
  have hx : √2 * √(x / 2) = √x := by
    rw [← sqrt_mul zero_le_two]; congr 1; ring
  have key := integral_comp_mul_left_Ioi (fun s => gaussianPDFReal 0 1 s) (√(x / 2)) h2
  rw [hx] at key
  have hcongr : ∀ u : ℝ, gaussianPDFReal 0 1 (√2 * u) = (√(2 * π))⁻¹ * rexp (-u ^ 2) := by
    intro u
    rw [gaussianPDFReal_std, mul_pow, sq_sqrt zero_le_two]
    congr 2; ring
  simp only [hcongr, smul_eq_mul, integral_const_mul] at key
  have hpi : √(2 * π) = √2 * √π := sqrt_mul zero_le_two π
  have hpi0 : 0 < √π := sqrt_pos.2 pi_pos
  have hJ : ∫ s in Ioi (√x), gaussianPDFReal 0 1 s =
      √2 * ((√(2 * π))⁻¹ * ∫ u in Ioi (√(x / 2)), rexp (-u ^ 2)) := by
    rw [key]; field_simp
  rw [hJ, erfc, hpi]
  field_simp

lemma sq_gt_set {x : ℝ} (hx : 0 ≤ x) : {z : ℝ | x < z ^ 2} = Iio (-√x) ∪ Ioi (√x) := by
  ext z
  simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi]
  rw [← sqrt_lt_sqrt_iff hx, sqrt_sq_eq_abs, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl h

/-- `P(Z² > x) = 2 P(Z > √x)` for a standard normal `Z`. -/
theorem gaussian_sq_tail {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {z | x < z ^ 2} = 2 * ∫ s in Ioi (√x), gaussianPDFReal 0 1 s := by
  have hint := integrable_gaussianPDFReal 0 1
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero, sq_gt_set hx,
    ENNReal.toReal_ofReal (setIntegral_nonneg (measurableSet_Iio.union measurableSet_Ioi)
      fun s _ => gaussianPDFReal_nonneg 0 1 s),
    setIntegral_union _ measurableSet_Ioi hint.integrableOn hint.integrableOn,
    ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
  · simp only [gaussianPDFReal_std, neg_sq]
    ring
  · rw [Set.disjoint_left]
    intro z h1 h2
    simp only [mem_Iio, mem_Ioi] at h1 h2
    linarith [sqrt_nonneg x]

/-- §8: `chi2_sf_batch`'s `erfc(sqrt(x/2))` is the χ²(1) tail `P(Z² > x)`. -/
theorem chiSq1_tail_eq_erfc {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {z | x < z ^ 2} = erfc (√(x / 2)) := by
  rw [gaussian_sq_tail hx, two_gaussian_tail_eq_erfc]

/-- `erfc` is antitone. -/
theorem erfc_antitone : Antitone erfc := by
  intro y y' hyy
  unfold erfc
  have hint : IntegrableOn (fun t : ℝ => rexp (-t ^ 2)) (Ioi y) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn
  exact mul_le_mul_of_nonneg_left (setIntegral_mono_set hint
    (ae_of_all _ fun t => (exp_pos _).le) (Eventually.of_forall (Ioi_subset_Ioi hyy)))
    (by positivity)

/-- `chi2_sf_batch`'s formula `x ↦ erfc (√(x / 2))` is antitone. -/
theorem erfc_sqrt_half_antitone : Antitone fun x : ℝ => erfc (√(x / 2)) :=
  erfc_antitone.comp_monotone fun _ _ h => sqrt_le_sqrt (by linarith)

/-- The χ²(1) tail `x ↦ P(Z² > x)` is antitone. -/
theorem chiSq1_tail_antitone : Antitone fun x : ℝ => (gaussianReal 0 1).real {z | x < z ^ 2} :=
  fun _ _ h => measureReal_mono (fun _ hz => lt_of_le_of_lt h hz) (measure_ne_top _ _)

lemma gaussian_tail_sub {a b : ℝ} (hab : a ≤ b) :
    (∫ s in Ioi a, gaussianPDFReal 0 1 s) - ∫ s in Ioi b, gaussianPDFReal 0 1 s =
      ∫ s in a..b, gaussianPDFReal 0 1 s := by
  have hint : Integrable (gaussianPDFReal 0 1) volume := integrable_gaussianPDFReal 0 1
  rw [← Ioc_union_Ioi_eq_Ioi hab]
  rw [setIntegral_union (f := gaussianPDFReal 0 1) (μ := volume) Ioc_disjoint_Ioi_same
    measurableSet_Ioi hint.integrableOn hint.integrableOn, intervalIntegral.integral_of_le hab]
  ring

/-- The χ²(1) tail is not Lipschitz on `(0, ∞)`: its slope `φ(√x)/√x` blows up at `0⁺`. -/
theorem erfc_sqrt_half_not_lipschitzOn :
    ¬ ∃ K, LipschitzOnWith K (fun x : ℝ => erfc (√(x / 2))) (Ioi 0) := by
  rintro ⟨K, hK⟩
  set c := gaussianPDFReal 0 1 1
  have hc : 0 < c := gaussianPDFReal_pos 0 1 1 one_ne_zero
  set L : ℝ := (K : ℝ)
  have hL : 0 ≤ L := K.2
  set x := min 1 ((c / (L + 1)) ^ 2)
  have hx : 0 < x := lt_min one_pos (by positivity)
  have hx1 : x ≤ 1 := min_le_left _ _
  have hsx : √x ≤ c / (L + 1) := by
    rw [sqrt_le_left (by positivity)]; exact min_le_right _ _
  have hsx0 : 0 < √x := sqrt_pos.2 hx
  have hsx1 : √x ≤ 1 := sqrt_le_one.2 hx1
  have hq : √(x / 4) = √x / 2 := by
    rw [sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      sqrt_sq zero_le_two]
  -- Lower bound on the drop of the tail between `x / 4` and `x`.
  have hdrop : √x / 2 * c ≤ ∫ s in √x / 2..√x, gaussianPDFReal 0 1 s := by
    have := intervalIntegral.integral_mono_on (a := √x / 2) (b := √x) (by linarith)
      (intervalIntegrable_const (c := c)) (integrable_gaussianPDFReal 0 1).intervalIntegrable
      (fun s hs => by
        simp only [c, gaussianPDFReal_std]
        have h0 : 0 ≤ s := by linarith [hs.1]
        have : s ^ 2 ≤ 1 := by nlinarith [hs.2]
        exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) (by positivity))
    simpa [intervalIntegral.integral_const, show √x - √x / 2 = √x / 2 by ring] using this
  have hlip := hK.dist_le_mul (x / 4) (by simp only [mem_Ioi]; positivity) x hx
  rw [← two_gaussian_tail_eq_erfc, ← two_gaussian_tail_eq_erfc, Real.dist_eq, Real.dist_eq,
    hq, ← mul_sub, gaussian_tail_sub (by linarith), abs_mul, abs_two,
    abs_of_nonneg (le_trans (by positivity) hdrop), abs_of_nonpos (by linarith)] at hlip
  have hxx : x = √x * √x := (mul_self_sqrt hx.le).symm
  have hcL : L * √x < c := by
    calc L * √x ≤ L * (c / (L + 1)) := by gcongr
      _ < c := by rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  nlinarith

end ChiSquared

end JammaLean
