import JammaLean.Pab

/-!
# Wald and Score statistics from `Pab`

`stats.py` reads four `Pab` entries per SNP. With covariates `w 0, …, w (c-1)`,
genotype `x = w c` and phenotype `y`:

* `P_XX = Pab[c, xx]`, `P_XY = Pab[c, xy]`, `P_YY = Pab[c, yy]`
* `Px_YY = Pab[c+1, yy]`, the phenotype with the genotype also projected out.

`_beta_se_from_pab` and `batch_calc_wald_stats_from_pab_numpy` then compute

    beta = P_XY / P_XX,  tau = df / Px_YY,  var = 1 / (tau * P_XX),
    F_wald = (P_YY - Px_YY) * tau

and `batch_calc_score_stats_numpy` computes `F_score = n * P_XY² / (P_YY * P_XX)`.

Proved here:

* `px_yy_eq`: `Px_YY = P_YY - P_XY² / P_XX` (one CalcPab step).
* `waldF_eq_beta_sq_div_var`: the Wald F is the squared t statistic `beta² / var`.
* `waldF_eq_r2` and `scoreF_eq_r2`: both statistics are functions of
  `r² = P_XY² / (P_XX P_YY)`, namely `df r² / (1 - r²)` and `n r²`.
* `waldF_nonneg`, `r2_le_one`, `scoreF_le_n`: the ranges the p-value code assumes.
* `complement_z`: `_f_to_pvalue`'s `f / (df + f)` is exactly `1 - df / (df + f)`.
-/

namespace JammaLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Entries

variable (w : ℕ → E) (c : ℕ) (y : E)

noncomputable def pXX : ℝ := pab w c (w c) (w c)
noncomputable def pXY : ℝ := pab w c (w c) y
noncomputable def pYY : ℝ := pab w c y y
noncomputable def pxYY : ℝ := pab w (c + 1) y y

/-- `Px_YY = P_YY - P_XY² / P_XX`. -/
theorem px_yy_eq : pxYY w c y = pYY w c y - pXY w c y ^ 2 / pXX w c := by
  unfold pxYY pYY pXY pXX
  rw [pab_succ, pab_comm w c y (w c)]
  ring

theorem pXX_nonneg : 0 ≤ pXX w c := pab_self_nonneg _ _ _
theorem pYY_nonneg : 0 ≤ pYY w c y := pab_self_nonneg _ _ _
theorem pxYY_nonneg : 0 ≤ pxYY w c y := pab_self_nonneg _ _ _

/-- Cauchy–Schwarz in projected form: `P_XY² ≤ P_XX P_YY`. -/
theorem pXY_sq_le : pXY w c y ^ 2 ≤ pXX w c * pYY w c y := by
  unfold pXY pXX pYY pab
  have := real_inner_mul_inner_self_le (resid w c (w c)) (resid w c y)
  nlinarith [this]

end Entries

section Formulas

/-- `beta = P_XY / P_XX`. -/
noncomputable def beta (Pxx Pxy : ℝ) : ℝ := Pxy / Pxx
/-- `tau = df / Px_YY`. -/
noncomputable def tau (PxYY df : ℝ) : ℝ := df / PxYY
/-- `variance_beta = 1 / (tau * P_XX)`. -/
noncomputable def varBeta (Pxx PxYY df : ℝ) : ℝ := 1 / (tau PxYY df * Pxx)
/-- `f_stat = (P_YY - Px_YY) * tau`. -/
noncomputable def waldF (Pyy PxYY df : ℝ) : ℝ := (Pyy - PxYY) * tau PxYY df
/-- `f_stat = n_samples * (P_xy * P_xy) / (P_yy * P_xx)`. -/
noncomputable def scoreF (Pxx Pxy Pyy n : ℝ) : ℝ := n * (Pxy * Pxy) / (Pyy * Pxx)
/-- The projected squared correlation of genotype and phenotype. -/
noncomputable def r2 (Pxx Pxy Pyy : ℝ) : ℝ := Pxy ^ 2 / (Pxx * Pyy)

variable {Pxx Pxy Pyy PxYY : ℝ} (df n : ℝ)

/-- The Wald F is the squared t statistic, given `Px_YY = P_YY - P_XY² / P_XX`. -/
theorem waldF_eq_beta_sq_div_var (hxx : Pxx ≠ 0) (hpx : PxYY = Pyy - Pxy ^ 2 / Pxx) :
    waldF Pyy PxYY df = beta Pxx Pxy ^ 2 / varBeta Pxx PxYY df := by
  unfold waldF beta varBeta tau
  rw [hpx]
  by_cases hq : Pyy - Pxy ^ 2 / Pxx = 0
  · rw [hq]; simp
  by_cases hdf : df = 0
  · subst hdf; simp
  field_simp
  ring

/-- The Wald F as a function of `r²`: `df r² / (1 - r²)`. -/
theorem waldF_eq_r2 (hxx : Pxx ≠ 0) (hyy : Pyy ≠ 0) (hpx : PxYY = Pyy - Pxy ^ 2 / Pxx) :
    waldF Pyy PxYY df = df * r2 Pxx Pxy Pyy / (1 - r2 Pxx Pxy Pyy) := by
  unfold waldF tau r2
  rw [hpx]
  by_cases hq : Pxx * Pyy - Pxy ^ 2 = 0
  · have h1 : Pyy - Pxy ^ 2 / Pxx = 0 := by
      field_simp; linarith
    have h2 : 1 - Pxy ^ 2 / (Pxx * Pyy) = 0 := by
      field_simp; linarith
    rw [h1, h2]; simp
  field_simp
  ring

/-- The Score F as a function of `r²`: `n r²`. -/
theorem scoreF_eq_r2 : scoreF Pxx Pxy Pyy n = n * r2 Pxx Pxy Pyy := by
  unfold scoreF r2
  rw [mul_comm Pyy Pxx, ← pow_two, mul_div_assoc]

/-- `_f_to_pvalue`'s cancellation-free complement is exact. -/
theorem complement_z (f : ℝ) (h : df + f ≠ 0) : f / (df + f) = 1 - df / (df + f) := by
  field_simp
  ring

end Formulas

section Ranges

variable (w : ℕ → E) (c : ℕ) (y : E)

theorem r2_nonneg : 0 ≤ r2 (pXX w c) (pXY w c y) (pYY w c y) :=
  div_nonneg (sq_nonneg _) (mul_nonneg (pXX_nonneg w c) (pYY_nonneg w c y))

theorem r2_le_one : r2 (pXX w c) (pXY w c y) (pYY w c y) ≤ 1 := by
  unfold r2
  rcases (mul_nonneg (pXX_nonneg w c) (pYY_nonneg w c y)).lt_or_eq with h | h
  · exact (div_le_one h).mpr (pXY_sq_le w c y)
  · rw [← h, div_zero]; exact zero_le_one

/-- The Score F never exceeds `n`. -/
theorem scoreF_le_n {n : ℝ} (hn : 0 ≤ n) :
    scoreF (pXX w c) (pXY w c y) (pYY w c y) n ≤ n := by
  rw [scoreF_eq_r2]
  exact mul_le_of_le_one_right hn (r2_le_one w c y)

/-- The Wald F is non-negative for `df ≥ 0`, so `_f_to_pvalue`'s `f <= 0` branch
only fires at `F = 0`. -/
theorem waldF_nonneg {df : ℝ} (hdf : 0 ≤ df) :
    0 ≤ waldF (pYY w c y) (pxYY w c y) df := by
  unfold waldF tau
  rw [px_yy_eq]
  have hq : 0 ≤ pYY w c y - pXY w c y ^ 2 / pXX w c := by
    rw [← px_yy_eq]; exact pxYY_nonneg w c y
  have hd : 0 ≤ pXY w c y ^ 2 / pXX w c := div_nonneg (sq_nonneg _) (pXX_nonneg w c)
  have : pYY w c y - (pYY w c y - pXY w c y ^ 2 / pXX w c) =
      pXY w c y ^ 2 / pXX w c := by ring
  rw [this]
  exact mul_nonneg hd (div_nonneg hdf hq)

end Ranges

end JammaLean
