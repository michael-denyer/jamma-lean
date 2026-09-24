import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The eigen-rotation behind `Hi_eval` and `logdet_h`

JAMMA never forms `H = λK + I`. With `K = U diag(ev) Uᵀ` it rotates every vector
once (`UtW`, `Uty`, `Utx`) and then works with the diagonal
`Hi_eval = 1 / (λ ev + 1)`:

* `Pab[0, ab] = Hi_eval @ Uab`, where `Uab[:, ab] = (Uᵀa) * (Uᵀb)` (`pab.py`
  `compute_Uab`, `calc_pab`).
* `logdet_h = Σ log(λ ev + 1)` (`likelihood_numpy.py`
  `_batch_pab_at_lambda_numpy`).

This file proves both equal their dense forms, `aᵀ H⁻¹ b` and `log det H`, and
that row 0 is an inner product on `EuclideanSpace`, so every theorem in
`Pab.lean` applies to it.
-/

namespace JammaLean

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `H = λ U diag(ev) Uᵀ + I`. -/
def hMat (U : Matrix n n ℝ) (ev : n → ℝ) (lam : ℝ) : Matrix n n ℝ :=
  lam • (U * diagonal ev * Uᵀ) + 1

/-- The rotated form of `H`: `U diag(λ ev + 1) Uᵀ`. -/
theorem hMat_eq_rotated (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ) :
    hMat U ev lam = U * diagonal (fun i => lam * ev i + 1) * Uᵀ := by
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hdiag : diagonal (fun i => lam * ev i + 1) = lam • diagonal ev + 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  rw [hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUUt, hMat,
    Matrix.mul_smul, Matrix.smul_mul]

/-- `H⁻¹ = U diag(Hi_eval) Uᵀ`. -/
theorem hMat_inv (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, lam * ev i + 1 ≠ 0) :
    (hMat U ev lam)⁻¹ = U * diagonal (fun i => (lam * ev i + 1)⁻¹) * Uᵀ := by
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  apply Matrix.inv_eq_right_inv
  rw [hMat_eq_rotated U hU]
  calc U * diagonal (fun i => lam * ev i + 1) * Uᵀ *
        (U * diagonal (fun i => (lam * ev i + 1)⁻¹) * Uᵀ)
      = U * (diagonal (fun i => lam * ev i + 1) * (Uᵀ * U) *
          diagonal (fun i => (lam * ev i + 1)⁻¹)) * Uᵀ := by
        simp only [Matrix.mul_assoc]
    _ = U * Uᵀ := by
        rw [hU, Matrix.mul_one, diagonal_mul_diagonal]
        have : (fun i => (lam * ev i + 1) * (lam * ev i + 1)⁻¹) = fun _ => (1 : ℝ) :=
          funext fun i => mul_inv_cancel₀ (hpos i)
        rw [this, diagonal_one, Matrix.mul_one]
    _ = 1 := hUUt

/-- The rotated vector `Uᵀ a`, the `UtW`, `Uty`, `Utx` of the code. -/
def rot (U : Matrix n n ℝ) (a : n → ℝ) : n → ℝ := Uᵀ *ᵥ a

/-- `Hi_eval @ Uab` is the dense `aᵀ H⁻¹ b`. -/
theorem quad_form_rotated (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, lam * ev i + 1 ≠ 0) (a b : n → ℝ) :
    a ⬝ᵥ ((hMat U ev lam)⁻¹ *ᵥ b) =
      ∑ i, (lam * ev i + 1)⁻¹ * (rot U a i * rot U b i) := by
  rw [hMat_inv U hU ev lam hpos, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal, rot]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `det H = ∏ (λ ev + 1)`. -/
theorem det_hMat (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ) :
    (hMat U ev lam).det = ∏ i, (lam * ev i + 1) := by
  rw [hMat_eq_rotated U hU, det_mul, det_mul, det_diagonal]
  have h := congrArg det hU
  rw [det_mul, det_transpose, det_one] at h
  calc (U.det * ∏ i, (lam * ev i + 1)) * Uᵀ.det
      = (U.det * U.det) * ∏ i, (lam * ev i + 1) := by rw [det_transpose]; ring
    _ = ∏ i, (lam * ev i + 1) := by rw [h, one_mul]

/-- `logdet_h = Σ log(λ ev + 1)` is `log det H` when `H` is positive definite
in the eigenbasis. -/
theorem logdet_hMat (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) :
    Real.log (hMat U ev lam).det = ∑ i, Real.log (lam * ev i + 1) := by
  rw [det_hMat U hU, Real.log_prod]
  intro i _
  exact (hpos i).ne'

/-- Scale a rotated vector by `√Hi_eval`, turning the `H⁻¹`-weighted inner product
into the Euclidean one. -/
noncomputable def weighted (h : n → ℝ) (x : n → ℝ) : EuclideanSpace ℝ n :=
  (WithLp.equiv 2 (n → ℝ)).symm fun i => Real.sqrt (h i) * x i

omit [DecidableEq n] in
/-- Row 0 of `Pab`, `Σ Hi_eval * Uab`, is a Euclidean inner product, so the
`Pab.lean` recursion theorems apply to it with `E = EuclideanSpace ℝ n`. -/
theorem inner_weighted (h : n → ℝ) (hh : ∀ i, 0 ≤ h i) (x y : n → ℝ) :
    @inner ℝ _ _ (weighted h x) (weighted h y) = ∑ i, h i * (x i * y i) := by
  simp only [weighted, PiLp.inner_apply, WithLp.equiv_symm_apply, RCLike.inner_apply,
    conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Real.mul_self_sqrt (hh i)
  calc Real.sqrt (h i) * y i * (Real.sqrt (h i) * x i)
      = (Real.sqrt (h i) * Real.sqrt (h i)) * (x i * y i) := by ring
    _ = h i * (x i * y i) := by rw [this]

/-- End to end: row 0 of `Pab` built from the rotated vectors is `aᵀ H⁻¹ b`. -/
theorem pab_row0_eq_dense (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (a b : n → ℝ) :
    let hi := fun i => (lam * ev i + 1)⁻¹
    @inner ℝ _ _ (weighted hi (rot U a)) (weighted hi (rot U b)) =
      a ⬝ᵥ ((hMat U ev lam)⁻¹ *ᵥ b) := by
  intro hi
  rw [inner_weighted hi (fun i => (inv_pos.mpr (hpos i)).le),
    quad_form_rotated U hU ev lam (fun i => (hpos i).ne')]

end JammaLean
