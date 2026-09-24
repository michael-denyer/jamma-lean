import Mathlib.Probability.Distributions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The F(1, df) p-value is a regularised incomplete beta

`_f_to_pvalue` (`src/jamma/lmm/stats.py`) returns `betainc(df/2, 1/2, df/(df+F))`.
This file proves that this is the upper tail of the F(1, df) distribution.
-/

open MeasureTheory Set Real ProbabilityTheory

namespace JammaLean

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

noncomputable def incBeta (a b z : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..z, t ^ (a - 1) * (1 - t) ^ (b - 1)) / beta a b

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

theorem incBeta_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : incBeta a b 1 = 1 := by
  have hc := (Complex.betaIntegral_convergent (u := a) (v := b) (by simpa) (by simpa))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hc
  rw [incBeta, div_eq_one_iff_eq (beta_pos ha hb).ne', beta_eq_betaIntegralReal a b ha hb,
    Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one, ← RCLike.re_to_complex, ← integral_re hc]
  exact setIntegral_congr_fun measurableSet_Ioc fun x hx => kernel_eq_re hx

theorem fTail_zero {m : ℝ} (hm : 0 < m) : fTail m 0 = 1 := by
  rw [fTail_eq_incBeta hm le_rfl, add_zero, div_self hm.ne']
  exact incBeta_one (by positivity) (by norm_num)

end JammaLean
