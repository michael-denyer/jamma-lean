import JammaLean.Rotation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The kinship matrix is positive semidefinite

`src/jamma/kinship/stream.py` builds the kinship matrix from the centred
(`-gk 1`) or standardised (`-gk 2`) genotype matrix `X_c` (samples × SNPs) as

    K = X_c X_cᵀ / p.

`Rotation.lean` needs `0 < λ ev i + 1` for every eigenvalue of `K`. This file
discharges that hypothesis for every `λ ≥ 0`:

* `kinship_posSemidef`: `(1/p) X Xᵀ` is positive semidefinite, whatever `X` is.
* `eigen_nonneg`: every eigenvalue in `K = U diag(ev) Uᵀ` with `Uᵀ U = 1` is
  `≥ 0` when `K` is positive semidefinite, since `ev i = uᵢᵀ K uᵢ` for column `uᵢ`.
* `hpos_of_kinship`: hence `0 < λ ev i + 1`, and `logdet_hMat_kinship` and
  `pab_row0_eq_dense_kinship` restate the `Rotation.lean` results with only
  `0 ≤ λ` and the kinship hypotheses.
* `kinship_mulVec_one`: centring each column to mean zero puts the all-ones
  vector in the kernel of `K`.
-/

namespace JammaLean

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {p : ℕ}

/-- `K = X Xᵀ / p`, the `-gk 1` / `-gk 2` kinship of `stream.py`. -/
noncomputable def kinship (X : Matrix n (Fin p) ℝ) : Matrix n n ℝ :=
  (1 / (p : ℝ)) • (X * Xᵀ)

omit [DecidableEq n] in
/-- The kinship matrix is positive semidefinite. -/
theorem kinship_posSemidef (X : Matrix n (Fin p) ℝ) : (kinship X).PosSemidef := by
  have h := posSemidef_self_mul_conjTranspose X
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact h.smul (by positivity)

/-- The eigenvalues of a positive semidefinite `K = U diag(ev) Uᵀ` are non-negative. -/
theorem eigen_nonneg {K U : Matrix n n ℝ} (hU : Uᵀ * U = 1) {ev : n → ℝ}
    (hK : K = U * diagonal ev * Uᵀ) (hpsd : K.PosSemidef) (i : n) : 0 ≤ ev i := by
  have hD : Uᵀ * K * U = diagonal ev := by
    rw [hK]
    calc Uᵀ * (U * diagonal ev * Uᵀ) * U = (Uᵀ * U) * diagonal ev * (Uᵀ * U) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal ev := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  have hq := hpsd.dotProduct_mulVec_nonneg (U *ᵥ Pi.single i 1)
  have hval : star (U *ᵥ Pi.single i 1) ⬝ᵥ (K *ᵥ (U *ᵥ Pi.single i 1)) = ev i := by
    rw [star_trivial, Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, ← dotProduct_mulVec, ← Matrix.mul_assoc, hD]
    simp
  rwa [hval] at hq

/-- `0 < λ ev i + 1` for every `λ ≥ 0`: `Rotation.lean`'s `hpos`, discharged. -/
theorem hpos_of_kinship {K U : Matrix n n ℝ} (hU : Uᵀ * U = 1) {ev : n → ℝ}
    (hK : K = U * diagonal ev * Uᵀ) (hpsd : K.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ i, 0 < lam * ev i + 1 := fun i => by
  have := mul_nonneg hlam (eigen_nonneg hU hK hpsd i)
  linarith

/-- `logdet_h = log det H` for the JAMMA kinship at every `λ ≥ 0`. -/
theorem logdet_hMat_kinship (X : Matrix n (Fin p) ℝ) (U : Matrix n n ℝ) (hU : Uᵀ * U = 1)
    (ev : n → ℝ) (hK : kinship X = U * diagonal ev * Uᵀ) {lam : ℝ} (hlam : 0 ≤ lam) :
    Real.log (hMat U ev lam).det = ∑ i, Real.log (lam * ev i + 1) :=
  logdet_hMat U hU ev lam (hpos_of_kinship hU hK (kinship_posSemidef X) hlam)

/-- Row 0 of `Pab` is `aᵀ H⁻¹ b` for the JAMMA kinship at every `λ ≥ 0`. -/
theorem pab_row0_eq_dense_kinship (X : Matrix n (Fin p) ℝ) (U : Matrix n n ℝ)
    (hU : Uᵀ * U = 1) (ev : n → ℝ) (hK : kinship X = U * diagonal ev * Uᵀ) {lam : ℝ}
    (hlam : 0 ≤ lam) (a b : n → ℝ) :
    let hi := fun i => (lam * ev i + 1)⁻¹
    @inner ℝ _ _ (weighted hi (rot U a)) (weighted hi (rot U b)) =
      a ⬝ᵥ ((hMat U ev lam)⁻¹ *ᵥ b) :=
  pab_row0_eq_dense U hU ev lam (hpos_of_kinship hU hK (kinship_posSemidef X) hlam) a b

omit [DecidableEq n] in
/-- Centred columns (`Σ_i X i j = 0`) put the all-ones vector in the kernel of `K`. -/
theorem kinship_mulVec_one (X : Matrix n (Fin p) ℝ) (hc : ∀ j, ∑ i, X i j = 0) :
    kinship X *ᵥ (fun _ => 1) = 0 := by
  have h : Xᵀ *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    ext j
    simp [mulVec, dotProduct, hc j]
  rw [kinship, smul_mulVec, ← Matrix.mulVec_mulVec, h, mulVec_zero, smul_zero]

end JammaLean
