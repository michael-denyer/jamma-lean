import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The likelihood normalising constant

JAMMA's `_logl_const(m) = 0.5 * m * (log m - log(2π) - 1)`
(`src/jamma/lmm/likelihood_numpy.py`), together with the `- 0.5 * m * log P_yy`
term, is the Gaussian log-likelihood with the residual variance profiled out.
REML passes `m = df` and MLE passes `m = n`.

This file proves that the profiled form is the supremum over the variance `s > 0`,
that it is attained at `s = Q / m`, and that `Q / m` is the only maximiser.
-/

namespace JammaLean

open Real

/-- Gaussian log-likelihood of `m` degrees of freedom whose residual quadratic
form is `Q`, at residual variance `s`. -/
noncomputable def gaussLogL (m Q s : ℝ) : ℝ :=
  -(m / 2) * log (2 * π * s) - Q / (2 * s)

/-- `_logl_const` in `likelihood_numpy.py`. -/
noncomputable def loglConst (m : ℝ) : ℝ :=
  m / 2 * (log m - log (2 * π) - 1)

/-- The profiled log-likelihood JAMMA evaluates: `_logl_const(m) - 0.5 * m * log Q`. -/
noncomputable def profiledLogL (m Q : ℝ) : ℝ :=
  loglConst m - m / 2 * log Q

/-- The gap between the profiled form and the likelihood at `s` is
`m/2 * (t - 1 - log t)` with `t = Q / (m s)`. -/
theorem profiled_sub_gaussLogL {m Q s : ℝ} (hm : 0 < m) (hQ : 0 < Q) (hs : 0 < s) :
    profiledLogL m Q - gaussLogL m Q s =
      m / 2 * (Q / (m * s) - 1 - log (Q / (m * s))) := by
  have h2pi : 0 < 2 * π := by positivity
  unfold gaussLogL profiledLogL loglConst
  rw [log_mul h2pi.ne' hs.ne', log_div hQ.ne' (by positivity), log_mul hm.ne' hs.ne']
  field_simp
  ring

/-- The profiled form bounds the Gaussian log-likelihood at every variance. -/
theorem gaussLogL_le_profiled {m Q s : ℝ} (hm : 0 < m) (hQ : 0 < Q) (hs : 0 < s) :
    gaussLogL m Q s ≤ profiledLogL m Q := by
  have gap := profiled_sub_gaussLogL hm hQ hs
  have key := log_le_sub_one_of_pos (by positivity : 0 < Q / (m * s))
  have : 0 ≤ m / 2 * (Q / (m * s) - 1 - log (Q / (m * s))) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- The bound is attained at `s = Q / m`, so the profiled form is the maximum. -/
theorem gaussLogL_at_argmax {m Q : ℝ} (hm : 0 < m) (hQ : 0 < Q) :
    gaussLogL m Q (Q / m) = profiledLogL m Q := by
  have gap := profiled_sub_gaussLogL hm hQ (by positivity : 0 < Q / m)
  have h1 : Q / (m * (Q / m)) = 1 := by field_simp
  rw [h1, log_one] at gap
  linarith

/-- `Q / m` is the only maximiser. -/
theorem gaussLogL_argmax_unique {m Q s : ℝ} (hm : 0 < m) (hQ : 0 < Q) (hs : 0 < s)
    (h : gaussLogL m Q s = profiledLogL m Q) : s = Q / m := by
  have gap := profiled_sub_gaussLogL hm hQ hs
  have ht : 0 < Q / (m * s) := by positivity
  have hzero : Q / (m * s) - 1 - log (Q / (m * s)) = 0 := by
    have hprod : m / 2 * (Q / (m * s) - 1 - log (Q / (m * s))) = 0 := by linarith
    rcases mul_eq_zero.mp hprod with h0 | h0
    · linarith
    · exact h0
  have ht1 : Q / (m * s) = 1 := by
    by_contra hne
    have := log_lt_sub_one_of_pos ht hne
    linarith
  rw [div_eq_one_iff_eq (by positivity)] at ht1
  field_simp
  linarith

end JammaLean
