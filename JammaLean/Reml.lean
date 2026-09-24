import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import JammaLean.Profile
import JammaLean.Pab
import JammaLean.Rotation

/-!
# `_reml_logl` is the likelihood of the error contrasts

`_reml_logl` (`src/jamma/lmm/likelihood_numpy.py`) evaluates, with `c` covariates `W`
and `df = n - c`,

    _logl_const(df) - 0.5 logdet_h - 0.5 (logdet(Pab) - logdet_iab) - 0.5 df log P_yy

where `logdet_h = log det H`, `_logdet_diag(Pab)` and `logdet_iab = _logdet_diag(Iab)`
sum the logged CalcPab pivots at weights `Hi_eval` and `1`, and `P_yy = Pab[c, yy]`.
The textbook REML is the Gaussian likelihood of `Aᵀy ~ N(0, s AᵀHA)` for any `A` with
orthonormal columns spanning the complement of `W` (`AᵀA = 1`, `AᵀW = 0`,
`df + c = n`). This file proves the two agree exactly, with no constant left over.

Dense matrix form, `P = H⁻¹ - H⁻¹W(WᵀH⁻¹W)⁻¹WᵀH⁻¹` (`projP`):

* `contrast_inv_eq_projP`, `contrast_quad_eq_pyy` (Harville): `A (AᵀHA)⁻¹ Aᵀ = P`, so
  the contrast quadratic form is `P_yy`. Only `det H ≠ 0` and `det (WᵀH⁻¹W) ≠ 0` are
  needed, not symmetry.
* `det_contrast`: `det (AᵀHA) = det H · det (WᵀH⁻¹W) / det (WᵀW)`. This is why
  `logdet_iab` must be subtracted: it turns `logdet_h + logdet(Pab)` into
  `log det (AᵀHA)`.
* `remlLogL_eq_contrast`, `contrastLogL_le_remlLogL`, `contrastLogL_at_argmax`: for
  positive definite `H` and full-rank `W`, `remlLogL` (the formula above) is the
  maximum over `s > 0` of the contrast log-likelihood, attained at `s = P_yy / df`.
* `exists_contrast_basis`: such an `A` always exists (an orthonormal basis of `ker Wᵀ`).

Centring (`-gk` with a centred kinship, `Kc = Pc K Pc`, `Pc = I - 11ᵀ/n`):

* `contrast_centered_kinship`: if `1` is in the column span of `W` (an intercept),
  `Aᵀ Kc A = Aᵀ K A`, so `Aᵀ H_c A = Aᵀ H A` at every `λ`.
* `remlLogL_centering_invariant`: `_reml_logl` from `Kc` equals `_reml_logl` from `K`
  at every `λ ≥ 0`, for positive semidefinite `K`. MLE has no contrast form and is
  not covered.

The code's `Pab` form, on rotated vectors weighted by `√Hi_eval` (`Rotation.lean`):

* `pab_eq_schur`: the `k` sequential CalcPab projections equal the one-shot formula
  `⟪a, b⟫ - (G⁻¹⟪w, a⟫) · ⟪w, b⟫`, `G` the covariate Gram matrix.
* `det_gram_eq_prod`, `log_det_gram`: `det G` is the product of the pivots
  `Pab[i, w_i w_i]`, so `_logdet_diag` is `log det G` when every pivot is positive.
* `pab_eq_projP`, `remlLogLPab_eq`, `remlLogLPab_eq_contrast`: the `Pab`-based
  `_reml_logl` equals the dense `remlLogL`, and hence the profiled contrast
  likelihood, given positive pivots at `λ` and at `λ = 0` (the `Iab` weights).
-/

namespace JammaLean

open Matrix

variable {n d c : Type*} [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
  [Fintype c] [DecidableEq c]

/-- `P = H⁻¹ - H⁻¹ W (Wᵀ H⁻¹ W)⁻¹ Wᵀ H⁻¹`, the matrix behind `Pab` at level `c`. -/
noncomputable def projP (H : Matrix n n ℝ) (W : Matrix n c ℝ) : Matrix n n ℝ :=
  H⁻¹ - H⁻¹ * W * (Wᵀ * H⁻¹ * W)⁻¹ * Wᵀ * H⁻¹

section Harville

variable (H : Matrix n n ℝ) (W : Matrix n c ℝ) (A : Matrix n d ℝ)

theorem transpose_mul_projP (hG : IsUnit (Wᵀ * H⁻¹ * W).det) :
    Wᵀ * projP H W = 0 := by
  have h := mul_nonsing_inv (Wᵀ * H⁻¹ * W) hG
  simp only [projP, Matrix.mul_sub, ← Matrix.mul_assoc]
  rw [h, Matrix.one_mul, sub_self]

theorem projP_mul (hG : IsUnit (Wᵀ * H⁻¹ * W).det) : projP H W * W = 0 := by
  have h := nonsing_inv_mul (Wᵀ * H⁻¹ * W) hG
  simp only [projP, Matrix.sub_mul]
  rw [show H⁻¹ * W * (Wᵀ * H⁻¹ * W)⁻¹ * Wᵀ * H⁻¹ * W
      = H⁻¹ * W * ((Wᵀ * H⁻¹ * W)⁻¹ * (Wᵀ * H⁻¹ * W)) by simp only [Matrix.mul_assoc],
    h, Matrix.mul_one, sub_self]

omit [Fintype d] [DecidableEq d] in
/-- `P H A = A`: `P` inverts `H` on the contrast directions. -/
theorem projP_mul_mul (hH : IsUnit H.det) (hAW : Aᵀ * W = 0) :
    projP H W * H * A = A := by
  have hWA : Wᵀ * A = 0 := by rw [← transpose_transpose (Wᵀ * A), transpose_mul,
    transpose_transpose, hAW, transpose_zero]
  have hHH := nonsing_inv_mul H hH
  simp only [projP, Matrix.sub_mul]
  rw [hHH, Matrix.one_mul,
    show H⁻¹ * W * (Wᵀ * H⁻¹ * W)⁻¹ * Wᵀ * H⁻¹ * H * A
      = H⁻¹ * W * (Wᵀ * H⁻¹ * W)⁻¹ * (Wᵀ * (H⁻¹ * H) * A) by simp only [Matrix.mul_assoc],
    hHH, Matrix.mul_one, hWA, Matrix.mul_zero, sub_zero]

/-- `(AᵀPA)(AᵀHA) = 1`: `AᵀPA`, the Schur complement of `Wᵀ H⁻¹ W` in `[A W]ᵀ H⁻¹ [A W]`,
inverts `AᵀHA`. -/
theorem schur_mul_contrast (hH : IsUnit H.det) (hG : IsUnit (Wᵀ * H⁻¹ * W).det)
    (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcomp : A * Aᵀ + W * ((Wᵀ * W)⁻¹ * Wᵀ) = 1) :
    (Aᵀ * projP H W * A) * (Aᵀ * H * A) = 1 := by
  have hAA : A * Aᵀ = 1 - W * ((Wᵀ * W)⁻¹ * Wᵀ) := eq_sub_of_add_eq hcomp
  have hright : projP H W * (A * Aᵀ) = projP H W := by
    rw [hAA, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, projP_mul H W hG,
      Matrix.zero_mul, sub_zero]
  calc (Aᵀ * projP H W * A) * (Aᵀ * H * A) = Aᵀ * (projP H W * (A * Aᵀ) * H * A) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hright, projP_mul_mul H W A hH hAW, hA]

/-- **Harville's identity.** With `A` an orthonormal basis of the contrasts
(`AᵀA = 1`, `AᵀW = 0`) that together with `W` spans the sample space
(`A Aᵀ + W (WᵀW)⁻¹ Wᵀ = 1`), `A (AᵀHA)⁻¹ Aᵀ = P`. -/
theorem contrast_inv_eq_projP (hH : IsUnit H.det) (hG : IsUnit (Wᵀ * H⁻¹ * W).det)
    (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcomp : A * Aᵀ + W * ((Wᵀ * W)⁻¹ * Wᵀ) = 1) :
    A * (Aᵀ * H * A)⁻¹ * Aᵀ = projP H W := by
  set P := projP H W
  set B := (Wᵀ * W)⁻¹ * Wᵀ
  have hAA : A * Aᵀ = 1 - W * B := eq_sub_of_add_eq hcomp
  have hleft : A * Aᵀ * P = P := by
    rw [hAA, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      transpose_mul_projP H W hG, Matrix.mul_zero, Matrix.mul_zero, sub_zero]
  have hright : P * (A * Aᵀ) = P := by
    rw [hAA, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, projP_mul H W hG,
      Matrix.zero_mul, sub_zero]
  rw [inv_eq_left_inv (schur_mul_contrast H W A hH hG hA hAW hcomp)]
  calc A * (Aᵀ * P * A) * Aᵀ = (A * Aᵀ * P) * (A * Aᵀ) := by simp only [Matrix.mul_assoc]
    _ = P := by rw [hleft, hright]

/-- The REML quadratic form of the contrasts `Aᵀy` is JAMMA's `P_yy`. -/
theorem contrast_quad_eq_pyy (hH : IsUnit H.det) (hG : IsUnit (Wᵀ * H⁻¹ * W).det)
    (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcomp : A * Aᵀ + W * ((Wᵀ * W)⁻¹ * Wᵀ) = 1) (y : n → ℝ) :
    (Aᵀ *ᵥ y) ⬝ᵥ ((Aᵀ * H * A)⁻¹ *ᵥ (Aᵀ *ᵥ y)) = y ⬝ᵥ (projP H W *ᵥ y) := by
  rw [← contrast_inv_eq_projP H W A hH hG hA hAW hcomp, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, ← vecMul_transpose, transpose_transpose, dotProduct_mulVec,
    dotProduct_mulVec]

end Harville

section Basis

variable (W : Matrix n c ℝ) (A : Matrix n d ℝ)

omit [DecidableEq n] [Fintype d] [Fintype c] [DecidableEq c] in
/-- `[A W]ᵀ [A W]` is block diagonal. -/
theorem gram_fromCols (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0) :
    (fromCols A W)ᵀ * fromCols A W = fromBlocks 1 0 0 (Wᵀ * W) := by
  have hWA : Wᵀ * A = 0 := by rw [← transpose_transpose (Wᵀ * A), transpose_mul,
    transpose_transpose, hAW, transpose_zero]
  rw [transpose_fromCols, fromRows_mul_fromCols, hA, hAW, hWA]

/-- Completeness: when `df + c = n`, the orthonormal contrasts and the covariates
together span the sample space, `A Aᵀ + W (WᵀW)⁻¹ Wᵀ = 1`. -/
theorem contrast_complete (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hWW : IsUnit (Wᵀ * W).det)
    (hcard : Fintype.card n = Fintype.card d + Fintype.card c) :
    A * Aᵀ + W * ((Wᵀ * W)⁻¹ * Wᵀ) = 1 := by
  have hWA : Wᵀ * A = 0 := by rw [← transpose_transpose (Wᵀ * A), transpose_mul,
    transpose_transpose, hAW, transpose_zero]
  have hBQ : fromRows Aᵀ ((Wᵀ * W)⁻¹ * Wᵀ) * fromCols A W = 1 := by
    rw [fromRows_mul_fromCols, hA, hAW, Matrix.mul_assoc, Matrix.mul_assoc, hWA,
      Matrix.mul_zero, nonsing_inv_mul _ hWW, fromBlocks_one]
  have e : n ≃ d ⊕ c := Fintype.equivOfCardEq (by rw [hcard, Fintype.card_sum])
  rw [← (mul_eq_one_comm_of_equiv e).mpr hBQ, fromCols_mul_fromRows]

/-- `det (Qᵀ X Q) = det X · det (QᵀQ)` for a square `Q` whose column index is a
relabelling of its row index. -/
theorem det_transpose_mul_mul_same {m : Type*} [Fintype m] [DecidableEq m]
    (Q : Matrix n m ℝ) (X : Matrix n n ℝ) (e : m ≃ n) :
    (Qᵀ * X * Q).det = X.det * (Qᵀ * Q).det := by
  have key : ∀ Y : Matrix n n ℝ,
      Qᵀ * Y * Q = (Q.submatrix e id)ᵀ * Y.submatrix e e * Q.submatrix e id := by
    intro Y
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]
  have hQ := key 1
  rw [Matrix.mul_one] at hQ
  rw [key X, hQ, submatrix_one_equiv, Matrix.mul_one, det_mul, det_mul, det_mul,
    det_submatrix_equiv_self]
  ring

/-- **The REML determinant.** `det (AᵀHA) = det H · det (Wᵀ H⁻¹ W) / det (WᵀW)`. -/
theorem det_contrast (H : Matrix n n ℝ) (hH : IsUnit H.det)
    (hG : IsUnit (Wᵀ * H⁻¹ * W).det) (hWW : IsUnit (Wᵀ * W).det)
    (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcard : Fintype.card n = Fintype.card d + Fintype.card c) :
    (Aᵀ * H * A).det = H.det * (Wᵀ * H⁻¹ * W).det / (Wᵀ * W).det := by
  have hcomp := contrast_complete W A hA hAW hWW hcard
  have e : d ⊕ c ≃ n := Fintype.equivOfCardEq (by rw [hcard, Fintype.card_sum])
  let _ := invertibleOfIsUnitDet _ hG
  -- `N = [A W]ᵀ H⁻¹ [A W]`, computed twice.
  have hblocks : (fromCols A W)ᵀ * H⁻¹ * fromCols A W =
      fromBlocks (Aᵀ * H⁻¹ * A) (Aᵀ * H⁻¹ * W) (Wᵀ * H⁻¹ * A) (Wᵀ * H⁻¹ * W) := by
    rw [transpose_fromCols, fromRows_mul, fromRows_mul_fromCols]
  have hschur : Aᵀ * H⁻¹ * A - Aᵀ * H⁻¹ * W * ⅟(Wᵀ * H⁻¹ * W) * (Wᵀ * H⁻¹ * A) =
      Aᵀ * projP H W * A := by
    rw [invOf_eq_nonsing_inv, projP, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hN := det_transpose_mul_mul_same (fromCols A W) H⁻¹ e
  rw [hblocks, det_fromBlocks₂₂, hschur, gram_fromCols W A hA hAW, det_fromBlocks_zero₁₂,
    det_one, one_mul, det_nonsing_inv] at hN
  have hS := congrArg det (schur_mul_contrast H W A hH hG hA hAW hcomp)
  rw [det_mul, det_one] at hS
  have hHne : H.det ≠ 0 := hH.ne_zero
  have e1 : H.det * ((Wᵀ * H⁻¹ * W).det * (Aᵀ * projP H W * A).det) = (Wᵀ * W).det := by
    rw [hN, Ring.inverse_eq_inv', ← mul_assoc, mul_inv_cancel₀ hHne, one_mul]
  rw [eq_div_iff hWW.ne_zero]
  linear_combination (-(Aᵀ * H * A).det) * e1 + (H.det * (Wᵀ * H⁻¹ * W).det) * hS

end Basis

section Likelihood

open Real

/-- JAMMA's `_reml_logl`, with `logdet_hiw = log det (Wᵀ H⁻¹ W) - log det (WᵀW)` and
`P_yy = yᵀ P y`. -/
noncomputable def remlLogL (df : ℝ) (H : Matrix n n ℝ) (W : Matrix n c ℝ) (y : n → ℝ) : ℝ :=
  loglConst df - log H.det / 2 - (log (Wᵀ * H⁻¹ * W).det - log (Wᵀ * W).det) / 2
    - df / 2 * log (y ⬝ᵥ (projP H W *ᵥ y))

/-- The Gaussian log-likelihood of the contrasts `z = Aᵀy ~ N(0, s M)`, `M = AᵀHA`:
`-(df/2) log (2π s) - ½ log det M - zᵀ M⁻¹ z / (2 s)`. -/
noncomputable def contrastLogL (M : Matrix d d ℝ) (z : d → ℝ) (s : ℝ) : ℝ :=
  gaussLogL (Fintype.card d) (z ⬝ᵥ (M⁻¹ *ᵥ z)) s - log M.det / 2

variable (H : Matrix n n ℝ) (W : Matrix n c ℝ) (A : Matrix n d ℝ)

/-- The positivity facts a positive definite `H` and a full-column-rank `W` give. -/
theorem reml_dets_pos (hH : H.PosDef) (hW : Function.Injective W.mulVec) :
    0 < H.det ∧ 0 < (Wᵀ * H⁻¹ * W).det ∧ 0 < (Wᵀ * W).det := by
  have hG := hH.inv.conjTranspose_mul_mul_same hW
  have hWW := PosDef.conjTranspose_mul_self W hW
  rw [conjTranspose_eq_transpose_of_trivial] at hG hWW
  exact ⟨hH.det_pos, hG.det_pos, hWW.det_pos⟩

/-- `_reml_logl` at any `df` depends on `H` only through `M = AᵀHA`:
`loglConst df - ½ log det M - (df/2) log (zᵀ M⁻¹ z)` with `z = Aᵀy`. -/
theorem remlLogL_eq_contrast_df (hH : H.PosDef) (hW : Function.Injective W.mulVec)
    (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcard : Fintype.card n = Fintype.card d + Fintype.card c) (df : ℝ) (y : n → ℝ) :
    remlLogL df H W y = loglConst df - log (Aᵀ * H * A).det / 2
      - df / 2 * log ((Aᵀ *ᵥ y) ⬝ᵥ ((Aᵀ * H * A)⁻¹ *ᵥ (Aᵀ *ᵥ y))) := by
  obtain ⟨hHp, hGp, hWWp⟩ := reml_dets_pos H W hH hW
  have hcomp := contrast_complete W A hA hAW (isUnit_iff_ne_zero.mpr hWWp.ne') hcard
  rw [contrast_quad_eq_pyy H W A (isUnit_iff_ne_zero.mpr hHp.ne')
      (isUnit_iff_ne_zero.mpr hGp.ne') hA hAW hcomp,
    det_contrast W A H (isUnit_iff_ne_zero.mpr hHp.ne') (isUnit_iff_ne_zero.mpr hGp.ne')
      (isUnit_iff_ne_zero.mpr hWWp.ne') hA hAW hcard,
    log_div (by positivity) hWWp.ne', log_mul hHp.ne' hGp.ne']
  unfold remlLogL
  ring

/-- **JAMMA's REML is the profiled contrast likelihood.** `_reml_logl` equals
`profiledLogL df (zᵀ M⁻¹ z) - ½ log det M` with `z = Aᵀy`, `M = AᵀHA`: no additive
constant is left over, because `logdet_iab` supplies exactly the `log det (WᵀW)` that
converts `log det H + log det (Wᵀ H⁻¹ W)` into `log det (AᵀHA)`. -/
theorem remlLogL_eq_contrast (hH : H.PosDef) (hW : Function.Injective W.mulVec)
    (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcard : Fintype.card n = Fintype.card d + Fintype.card c) (y : n → ℝ) :
    remlLogL (Fintype.card d) H W y =
      profiledLogL (Fintype.card d) ((Aᵀ *ᵥ y) ⬝ᵥ ((Aᵀ * H * A)⁻¹ *ᵥ (Aᵀ *ᵥ y)))
        - log (Aᵀ * H * A).det / 2 := by
  rw [remlLogL_eq_contrast_df H W A hH hW hA hAW hcard, profiledLogL]
  ring

/-- JAMMA's REML bounds the contrast likelihood at every residual variance `s > 0`. -/
theorem contrastLogL_le_remlLogL [Nonempty d] (hH : H.PosDef)
    (hW : Function.Injective W.mulVec) (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcard : Fintype.card n = Fintype.card d + Fintype.card c) (y : n → ℝ)
    (hy : 0 < y ⬝ᵥ (projP H W *ᵥ y)) {s : ℝ} (hs : 0 < s) :
    contrastLogL (Aᵀ * H * A) (Aᵀ *ᵥ y) s ≤ remlLogL (Fintype.card d) H W y := by
  obtain ⟨hHp, hGp, hWWp⟩ := reml_dets_pos H W hH hW
  have hcomp := contrast_complete W A hA hAW (isUnit_iff_ne_zero.mpr hWWp.ne') hcard
  have hq := contrast_quad_eq_pyy H W A (isUnit_iff_ne_zero.mpr hHp.ne')
      (isUnit_iff_ne_zero.mpr hGp.ne') hA hAW hcomp y
  rw [remlLogL_eq_contrast H W A hH hW hA hAW hcard y, contrastLogL]
  have := gaussLogL_le_profiled (m := Fintype.card d)
    (by exact_mod_cast Fintype.card_pos) (hq ▸ hy) hs
  linarith

/-- ... and attains it at `s = P_yy / df`, so `_reml_logl` is the maximum over the
residual variance of the Gaussian log-likelihood of the error contrasts. -/
theorem contrastLogL_at_argmax [Nonempty d] (hH : H.PosDef)
    (hW : Function.Injective W.mulVec) (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcard : Fintype.card n = Fintype.card d + Fintype.card c) (y : n → ℝ)
    (hy : 0 < y ⬝ᵥ (projP H W *ᵥ y)) :
    contrastLogL (Aᵀ * H * A) (Aᵀ *ᵥ y) (y ⬝ᵥ (projP H W *ᵥ y) / Fintype.card d) =
      remlLogL (Fintype.card d) H W y := by
  obtain ⟨hHp, hGp, hWWp⟩ := reml_dets_pos H W hH hW
  have hcomp := contrast_complete W A hA hAW (isUnit_iff_ne_zero.mpr hWWp.ne') hcard
  have hq := contrast_quad_eq_pyy H W A (isUnit_iff_ne_zero.mpr hHp.ne')
      (isUnit_iff_ne_zero.mpr hGp.ne') hA hAW hcomp y
  rw [remlLogL_eq_contrast H W A hH hW hA hAW hcard y, contrastLogL, hq,
    gaussLogL_at_argmax (by exact_mod_cast Fintype.card_pos) hy]

end Likelihood

section Centring

variable (n) in
/-- The centring matrix `Pc = I - (1/n) 11ᵀ`; `Kc = Pc K Pc` is the centred kinship. -/
noncomputable def centering : Matrix n n ℝ :=
  1 - (Fintype.card n : ℝ)⁻¹ • Matrix.of fun _ _ => (1 : ℝ)

variable (W : Matrix n c ℝ) (A : Matrix n d ℝ)

omit [DecidableEq n] [Fintype d] [DecidableEq d] [DecidableEq c] in
/-- With an intercept in `W`, every contrast column sums to zero. -/
theorem contrast_col_sum (hAW : Aᵀ * W = 0) (hone : ∃ v, W *ᵥ v = fun _ => 1) (j : d) :
    ∑ k, A k j = 0 := by
  obtain ⟨v, hv⟩ := hone
  have h : Aᵀ *ᵥ (W *ᵥ v) = 0 := by rw [mulVec_mulVec, hAW, zero_mulVec]
  have := congrFun h j
  rw [hv] at this
  simpa [mulVec, dotProduct] using this

omit [Fintype d] [DecidableEq d] [DecidableEq c] in
theorem transpose_mul_centering (hAW : Aᵀ * W = 0) (hone : ∃ v, W *ᵥ v = fun _ => 1) :
    Aᵀ * centering n = Aᵀ := by
  have h0 : Aᵀ * Matrix.of (fun _ _ : n => (1 : ℝ)) = 0 := by
    ext i j
    simpa [mul_apply] using contrast_col_sum W A hAW hone i
  rw [centering, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, h0, smul_zero, sub_zero]

omit [Fintype d] [DecidableEq d] [DecidableEq c] in
theorem centering_mul (hAW : Aᵀ * W = 0) (hone : ∃ v, W *ᵥ v = fun _ => 1) :
    centering n * A = A := by
  have h0 : Matrix.of (fun _ _ : n => (1 : ℝ)) * A = 0 := by
    ext i j
    simpa [mul_apply] using contrast_col_sum W A hAW hone j
  rw [centering, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, h0, smul_zero, sub_zero]

omit [Fintype d] [DecidableEq d] [DecidableEq c] in
/-- **Centring is invisible to the contrasts.** With an intercept among the covariates,
`Aᵀ Kc A = Aᵀ K A`. -/
theorem contrast_centered_kinship (hAW : Aᵀ * W = 0) (hone : ∃ v, W *ᵥ v = fun _ => 1)
    (K : Matrix n n ℝ) :
    Aᵀ * (centering n * K * centering n) * A = Aᵀ * K * A := by
  calc Aᵀ * (centering n * K * centering n) * A
      = (Aᵀ * centering n) * K * (centering n * A) := by simp only [Matrix.mul_assoc]
    _ = Aᵀ * K * A := by rw [transpose_mul_centering W A hAW hone, centering_mul W A hAW hone]

omit [Fintype d] [DecidableEq d] [DecidableEq c] in
/-- ... hence `Aᵀ H_c A = Aᵀ H A` for `H = λK + I` and every `λ`. -/
theorem contrast_centered_hMat (hAW : Aᵀ * W = 0) (hone : ∃ v, W *ᵥ v = fun _ => 1)
    (K : Matrix n n ℝ) (lam : ℝ) :
    Aᵀ * (lam • (centering n * K * centering n) + 1) * A = Aᵀ * (lam • K + 1) * A := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one]
  rw [contrast_centered_kinship W A hAW hone]

omit [DecidableEq c] in
/-- The contrast likelihood is identical for `K` and `Kc`, at every `λ` and `s`. -/
theorem contrastLogL_centered (hAW : Aᵀ * W = 0) (hone : ∃ v, W *ᵥ v = fun _ => 1)
    (K : Matrix n n ℝ) (lam : ℝ) (y : n → ℝ) (s : ℝ) :
    contrastLogL (Aᵀ * (lam • (centering n * K * centering n) + 1) * A) (Aᵀ *ᵥ y) s =
      contrastLogL (Aᵀ * (lam • K + 1) * A) (Aᵀ *ᵥ y) s := by
  rw [contrast_centered_hMat W A hAW hone]

/-- **JAMMA's REML is invariant to centring the kinship** when an intercept is present:
`_reml_logl` computed from `H_c = λ Kc + I` equals the one from `H = λ K + I`, at every
`λ` where both are positive definite. -/
theorem remlLogL_centered (hW : Function.Injective W.mulVec) (hA : Aᵀ * A = 1)
    (hAW : Aᵀ * W = 0) (hcard : Fintype.card n = Fintype.card d + Fintype.card c)
    (hone : ∃ v, W *ᵥ v = fun _ => 1) (K : Matrix n n ℝ) (lam : ℝ)
    (hH : (lam • K + 1).PosDef) (hHc : (lam • (centering n * K * centering n) + 1).PosDef)
    (y : n → ℝ) :
    remlLogL (Fintype.card d) (lam • (centering n * K * centering n) + 1) W y =
      remlLogL (Fintype.card d) (lam • K + 1) W y := by
  rw [remlLogL_eq_contrast _ W A hHc hW hA hAW hcard, remlLogL_eq_contrast _ W A hH hW hA hAW hcard,
    contrast_centered_hMat W A hAW hone]

end Centring

section Existence

open Module

omit [DecidableEq n] in
/-- **Error contrasts exist.** For a full-column-rank `W` there is an `A` with
orthonormal columns, `AᵀW = 0`, and `df + c = n` columns: an orthonormal basis of
`ker Wᵀ`. -/
theorem exists_contrast_basis (W : Matrix n c ℝ) (hWW : IsUnit (Wᵀ * W).det) :
    ∃ (m : ℕ) (A : Matrix n (Fin m) ℝ), Aᵀ * A = 1 ∧ Aᵀ * W = 0 ∧
      Fintype.card n = Fintype.card (Fin m) + Fintype.card c := by
  let L : EuclideanSpace ℝ n →ₗ[ℝ] (c → ℝ) :=
    (Matrix.mulVecLin Wᵀ).comp (WithLp.linearEquiv 2 ℝ (n → ℝ)).toLinearMap
  have hL : ∀ x, L x = Wᵀ *ᵥ (x : n → ℝ) := fun _ => rfl
  have hsurj : LinearMap.range L = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro u
    refine ⟨WithLp.toLp 2 (W *ᵥ ((Wᵀ * W)⁻¹ *ᵥ u)), ?_⟩
    rw [hL, WithLp.ofLp_toLp, mulVec_mulVec, mulVec_mulVec,
      mul_nonsing_inv _ hWW, one_mulVec]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, finrank_euclideanSpace] at hrank
  let b := stdOrthonormalBasis ℝ (LinearMap.ker L)
  refine ⟨finrank ℝ (LinearMap.ker L), Matrix.of fun i j => (b j : EuclideanSpace ℝ n) i,
    ?_, ?_, ?_⟩
  · ext j j'
    have h := orthonormal_iff_ite.mp b.orthonormal j j'
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    simp only [mul_apply, one_apply, transpose_apply, of_apply]
    simp only [RCLike.inner_apply, conj_trivial] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ext j k
    have hmem : L (b j) = 0 := (b j).2
    have := congrFun hmem k
    rw [hL] at this
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply] at this
    simp only [mul_apply, transpose_apply, of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [Fintype.card_fin]
    omega

end Existence

section CentringFree

variable (n) in
theorem transpose_centering : (centering n)ᵀ = centering n := by
  ext i j
  simp [centering, one_apply, eq_comm]

omit [Fintype n] in
/-- `H = λK + I` is positive definite for a positive semidefinite `K` and `λ ≥ 0`. -/
theorem hMat_posDef {K : Matrix n n ℝ} (hK : K.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam) :
    (lam • K + 1).PosDef :=
  PosDef.posSemidef_add (hK.smul hlam) PosDef.one

/-- Centring keeps a kinship positive semidefinite. -/
theorem centered_posSemidef {K : Matrix n n ℝ} (hK : K.PosSemidef) :
    (centering n * K * centering n).PosSemidef := by
  have := hK.conjTranspose_mul_mul_same (centering n)
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_centering] at this

/-- **JAMMA's `_reml_logl` is invariant to centring the kinship**, with no contrast
matrix in the statement: for a full-rank `W` whose column span contains `1`, a
positive semidefinite `K`, every `λ ≥ 0`, every `df` and every `y`, the value from
`Kc = Pc K Pc` equals the value from `K`. -/
theorem remlLogL_centering_invariant (W : Matrix n c ℝ) (hW : Function.Injective W.mulVec)
    (hone : ∃ v, W *ᵥ v = fun _ => 1) {K : Matrix n n ℝ} (hK : K.PosSemidef)
    {lam : ℝ} (hlam : 0 ≤ lam) (df : ℝ) (y : n → ℝ) :
    remlLogL df (lam • (centering n * K * centering n) + 1) W y =
      remlLogL df (lam • K + 1) W y := by
  have hWW : IsUnit (Wᵀ * W).det := by
    have := PosDef.conjTranspose_mul_self W hW
    rw [conjTranspose_eq_transpose_of_trivial] at this
    exact isUnit_iff_ne_zero.mpr this.det_pos.ne'
  obtain ⟨m, A, hA, hAW, hcard⟩ := exists_contrast_basis W hWW
  rw [remlLogL_eq_contrast_df _ W A (hMat_posDef (centered_posSemidef hK) hlam) hW hA hAW
      hcard, remlLogL_eq_contrast_df _ W A (hMat_posDef hK hlam) hW hA hAW hcard,
    contrast_centered_hMat W A hAW hone]

end CentringFree

section PabBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The Gram matrix of the first `k` covariates, `Pab[0, w_i w_j]`. -/
noncomputable def gram (w : ℕ → E) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ⟪w i, w j⟫

/-- The covariate cross products `Pab[0, w_i a]`. -/
noncomputable def crossVec (w : ℕ → E) (k : ℕ) (a : E) : Fin k → ℝ :=
  fun i => ⟪w i, a⟫

/-- **CalcPab computes the Schur complement.** With an invertible Gram matrix `G`,
`Pab[k, ab] = ⟪a, b⟫ - (G⁻¹ ⟪w, a⟫) · ⟪w, b⟫`: the `k` sequential projections of
`calc_pab` equal the one-shot projection formula. -/
theorem pab_eq_schur (w : ℕ → E) (k : ℕ) (hG : IsUnit (gram w k).det) (a b : E) :
    pab w k a b = ⟪a, b⟫ - ((gram w k)⁻¹ *ᵥ crossVec w k a) ⬝ᵥ crossVec w k b := by
  set coef := (gram w k)⁻¹ *ᵥ crossVec w k a
  set x := a - ∑ j : Fin k, coef j • w j
  have hx_perp : x ∈ (covSpan w k)ᗮ := by
    apply mem_orthogonal_covSpan
    intro i hi
    have h1 := congrFun (show gram w k *ᵥ coef = crossVec w k a by
      rw [mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]) ⟨i, hi⟩
    simp only [mulVec, dotProduct, gram, crossVec, of_apply] at h1
    simp only [x, inner_sub_right, inner_sum, inner_smul_right]
    rw [← h1]
    simp only [mul_comm, sub_self]
  have hx_span : a - x ∈ covSpan w k := by
    have : a - x = ∑ j : Fin k, coef j • w j := by simp [x]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (w_mem_covSpan w j.2)
  rw [pab_eq_inner_resid_left, ← resid_unique w k a x hx_perp hx_span]
  simp only [x, inner_sub_left, sum_inner, inner_smul_left, RCLike.conj_to_real, dotProduct,
    crossVec]

/-- One CalcPab pivot extends the Gram determinant: `det G_{k+1} = det G_k · Pab[k, w_k w_k]`. -/
theorem det_gram_succ (w : ℕ → E) (k : ℕ) (hG : IsUnit (gram w k).det) :
    (gram w (k + 1)).det = (gram w k).det * pab w k (w k) (w k) := by
  let _ := invertibleOfIsUnitDet _ hG
  have hblk : (gram w (k + 1)).submatrix finSumFinEquiv finSumFinEquiv =
      fromBlocks (gram w k) (Matrix.of fun i (_ : Fin 1) => ⟪w i, w k⟫)
        (Matrix.of fun (_ : Fin 1) j => ⟪w k, w j⟫) (Matrix.of fun _ _ => ⟪w k, w k⟫) := by
    ext (i | i) (j | j) <;> simp [gram, Fin.natAdd, Fin.fin_one_eq_zero]
  rw [← det_submatrix_equiv_self finSumFinEquiv, hblk, det_fromBlocks₁₁, det_fin_one,
    pab_eq_schur w k hG, invOf_eq_nonsing_inv]
  congr 1
  simp only [Matrix.sub_apply, of_apply, mul_apply, mulVec, dotProduct, crossVec]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm (w i) (w k)]
  ring

/-- The Gram determinant is the product of the CalcPab pivots `Pab[i, w_i w_i]`. -/
theorem det_gram_eq_prod (w : ℕ → E) (k : ℕ)
    (hpiv : ∀ i < k, 0 < pab w i (w i) (w i)) :
    (gram w k).det = ∏ i ∈ Finset.range k, pab w i (w i) (w i) := by
  induction k with
  | zero => simp [det_isEmpty]
  | succ k ih =>
    have ih' := ih fun i hi => hpiv i (Nat.lt_succ_of_lt hi)
    have hpos : 0 < (gram w k).det := by
      rw [ih']
      exact Finset.prod_pos fun i hi => hpiv i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
    rw [det_gram_succ w k (isUnit_iff_ne_zero.mpr hpos.ne'), ih', Finset.prod_range_succ]

/-- `_logdet_diag(Pab)`, the sum of the logged pivots, is `log det G`. -/
theorem log_det_gram (w : ℕ → E) (k : ℕ) (hpiv : ∀ i < k, 0 < pab w i (w i) (w i)) :
    Real.log (gram w k).det = ∑ i ∈ Finset.range k, Real.log (pab w i (w i) (w i)) := by
  rw [det_gram_eq_prod w k hpiv, Real.log_prod]
  intro i hi
  exact (hpiv i (Finset.mem_range.mp hi)).ne'

end PabBridge

section DenseBridge

variable {k : ℕ}

/-- A rotated, `√Hi_eval`-scaled vector: `Uᵀa` as `calc_pab` weights it. -/
noncomputable def rotVec (U : Matrix n n ℝ) (ev : n → ℝ) (lam : ℝ) (a : n → ℝ) :
    EuclideanSpace ℝ n :=
  weighted (fun r => (lam * ev r + 1)⁻¹) (rot U a)

/-- The covariates as CalcPab sees them: column `i` of `W`, rotated by `Uᵀ` and
scaled by `√Hi_eval`. Indices `≥ k` are unused and set to `0`. -/
noncomputable def covVecs (U : Matrix n n ℝ) (ev : n → ℝ) (lam : ℝ) (W : Matrix n (Fin k) ℝ) :
    ℕ → EuclideanSpace ℝ n :=
  fun i => if h : i < k then rotVec U ev lam fun r => W r ⟨i, h⟩ else 0

omit [DecidableEq n] in
theorem transpose_mul_mul_apply {m : Type*} (W : Matrix n m ℝ) (M : Matrix n n ℝ) (i j : m) :
    (Wᵀ * M * W) i j = (fun r => W r i) ⬝ᵥ (M *ᵥ fun r => W r j) := by
  rw [Matrix.mul_assoc]
  simp only [mul_apply, transpose_apply, mulVec, dotProduct]

theorem hMat_inv_transpose (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, lam * ev i + 1 ≠ 0) : ((hMat U ev lam)⁻¹)ᵀ = (hMat U ev lam)⁻¹ := by
  rw [hMat_inv U hU ev lam hpos, transpose_mul, transpose_mul, transpose_transpose,
    diagonal_transpose, Matrix.mul_assoc]

/-- Row 0 of `Pab` on the covariates is the dense `Wᵀ H⁻¹ W`. -/
theorem gram_covVecs (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (W : Matrix n (Fin k) ℝ) :
    gram (covVecs U ev lam W) k = Wᵀ * (hMat U ev lam)⁻¹ * W := by
  ext i j
  simp only [gram, covVecs, of_apply, i.2, j.2, dite_true, Fin.eta]
  rw [transpose_mul_mul_apply]
  exact pab_row0_eq_dense U hU ev lam hpos _ _

/-- **JAMMA's `P_yy` is `yᵀ P y`.** Running the CalcPab recursion to level `k` on the
rotated, weighted covariates and phenotype gives `yᵀ P y` with the dense
`P = H⁻¹ - H⁻¹ W (Wᵀ H⁻¹ W)⁻¹ Wᵀ H⁻¹`. -/
theorem pab_eq_projP (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (W : Matrix n (Fin k) ℝ)
    (hG : IsUnit (Wᵀ * (hMat U ev lam)⁻¹ * W).det) (a b : n → ℝ) :
    pab (covVecs U ev lam W) k (rotVec U ev lam a) (rotVec U ev lam b) =
      a ⬝ᵥ (projP (hMat U ev lam) W *ᵥ b) := by
  set Hi := (hMat U ev lam)⁻¹ with hHi
  have hdense : ∀ u v : n → ℝ,
      @inner ℝ _ _ (rotVec U ev lam u) (rotVec U ev lam v) = u ⬝ᵥ (Hi *ᵥ v) :=
    fun u v => pab_row0_eq_dense U hU ev lam hpos u v
  have hgram : gram (covVecs U ev lam W) k = Wᵀ * Hi * W := gram_covVecs U hU ev lam hpos W
  have hcross : ∀ u, crossVec (covVecs U ev lam W) k (rotVec U ev lam u) = Wᵀ *ᵥ (Hi *ᵥ u) := by
    intro u
    funext i
    simp only [crossVec, covVecs, i.2, dite_true, Fin.eta]
    rw [hdense]
    simp [mulVec, dotProduct]
  have hsymm : Hiᵀ = Hi := hMat_inv_transpose U hU ev lam fun i => (hpos i).ne'
  rw [pab_comm, pab_eq_schur _ k (hgram ▸ hG), real_inner_comm, hgram, hcross, hcross, hdense,
    projP, ← hHi, sub_mulVec, dotProduct_sub, dotProduct_comm (_ *ᵥ _)]
  congr 1
  calc (Wᵀ *ᵥ (Hi *ᵥ a)) ⬝ᵥ ((Wᵀ * Hi * W)⁻¹ *ᵥ (Wᵀ *ᵥ (Hi *ᵥ b)))
      = ((Hi *ᵥ a) ᵥ* W) ⬝ᵥ ((Wᵀ * Hi * W)⁻¹ *ᵥ (Wᵀ *ᵥ (Hi *ᵥ b))) := by
        rw [mulVec_transpose]
    _ = (a ᵥ* Hi) ⬝ᵥ (W *ᵥ ((Wᵀ * Hi * W)⁻¹ *ᵥ (Wᵀ *ᵥ (Hi *ᵥ b)))) := by
        rw [← dotProduct_mulVec, ← hsymm, mulVec_transpose, hsymm]
    _ = a ⬝ᵥ ((Hi * W * (Wᵀ * Hi * W)⁻¹ * Wᵀ * Hi) *ᵥ b) := by
        rw [← dotProduct_mulVec]
        simp only [mulVec_mulVec, Matrix.mul_assoc]

open Real in
/-- `_reml_logl` as the code evaluates it: `logdet_h = Σ log(λ ev + 1)`, `logdet_hiw` the
logged `Pab` pivots minus the logged `Iab` pivots (`Iab` is `Pab` with `Hi_eval = 1`,
i.e. `λ = 0`), and `P_yy = Pab[k, yy]`. -/
noncomputable def remlLogLPab (df : ℝ) (U : Matrix n n ℝ) (ev : n → ℝ) (lam : ℝ)
    (W : Matrix n (Fin k) ℝ) (y : n → ℝ) : ℝ :=
  let w := covVecs U ev lam W
  let w₀ := covVecs U ev 0 W
  loglConst df - (∑ i, log (lam * ev i + 1)) / 2
    - (∑ i ∈ Finset.range k, log (pab w i (w i) (w i))
        - ∑ i ∈ Finset.range k, log (pab w₀ i (w₀ i) (w₀ i))) / 2
    - df / 2 * log (pab w k (rotVec U ev lam y) (rotVec U ev lam y))

/-- **The code's `Pab`-based `_reml_logl` is the dense REML formula**, given positive
pivots (the condition under which `_logdet_diag` returns a finite value). -/
theorem remlLogLPab_eq (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (W : Matrix n (Fin k) ℝ)
    (hpiv : ∀ i < k, 0 < pab (covVecs U ev lam W) i (covVecs U ev lam W i)
      (covVecs U ev lam W i))
    (hpiv₀ : ∀ i < k, 0 < pab (covVecs U ev 0 W) i (covVecs U ev 0 W i) (covVecs U ev 0 W i))
    (df : ℝ) (y : n → ℝ) :
    remlLogLPab df U ev lam W y = remlLogL df (hMat U ev lam) W y := by
  have hpos₀ : ∀ i, 0 < 0 * ev i + 1 := fun i => by simp
  have hH0 : hMat U ev 0 = 1 := by simp [hMat]
  have hG : IsUnit (Wᵀ * (hMat U ev lam)⁻¹ * W).det := by
    rw [← gram_covVecs U hU ev lam hpos W, det_gram_eq_prod _ k hpiv]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_pos fun i hi =>
      hpiv i (Finset.mem_range.mp hi)).ne'
  have hlog := log_det_gram _ k hpiv
  have hlog₀ := log_det_gram _ k hpiv₀
  rw [gram_covVecs U hU ev lam hpos W] at hlog
  rw [gram_covVecs U hU ev 0 hpos₀ W, hH0, inv_one, Matrix.mul_one] at hlog₀
  simp only [remlLogLPab, remlLogL]
  rw [← hlog, ← hlog₀, ← logdet_hMat U hU ev lam hpos,
    pab_eq_projP U hU ev lam hpos W hG]

/-- `H = U diag(λ ev + 1) Uᵀ` is positive definite when every `λ ev + 1 > 0`. -/
theorem hMat_posDef_of_pos (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) : (hMat U ev lam).PosDef := by
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hinj : Function.Injective Uᵀ.mulVec := by
    intro x y h
    have := congrArg (U *ᵥ ·) h
    simpa [mulVec_mulVec, hUUt] using this
  have := (PosDef.diagonal hpos).conjTranspose_mul_mul_same hinj
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose,
    ← hMat_eq_rotated U hU ev lam] at this

/-- **End to end.** The code's `Pab`-based `_reml_logl`, at `df = n - k`, is the
profiled Gaussian log-likelihood of the error contrasts `Aᵀy ~ N(0, s AᵀHA)`. -/
theorem remlLogLPab_eq_contrast {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (W : Matrix n (Fin k) ℝ)
    (hW : Function.Injective W.mulVec)
    (hpiv : ∀ i < k, 0 < pab (covVecs U ev lam W) i (covVecs U ev lam W i)
      (covVecs U ev lam W i))
    (hpiv₀ : ∀ i < k, 0 < pab (covVecs U ev 0 W) i (covVecs U ev 0 W i) (covVecs U ev 0 W i))
    (A : Matrix n d ℝ) (hA : Aᵀ * A = 1) (hAW : Aᵀ * W = 0)
    (hcard : Fintype.card n = Fintype.card d + k) (y : n → ℝ) :
    remlLogLPab (Fintype.card d) U ev lam W y =
      profiledLogL (Fintype.card d)
          ((Aᵀ *ᵥ y) ⬝ᵥ ((Aᵀ * hMat U ev lam * A)⁻¹ *ᵥ (Aᵀ *ᵥ y)))
        - Real.log (Aᵀ * hMat U ev lam * A).det / 2 := by
  rw [remlLogLPab_eq U hU ev lam hpos W hpiv hpiv₀,
    remlLogL_eq_contrast _ W A (hMat_posDef_of_pos U hU ev lam hpos) hW hA hAW
      (by rw [hcard, Fintype.card_fin])]

end DenseBridge

end JammaLean
