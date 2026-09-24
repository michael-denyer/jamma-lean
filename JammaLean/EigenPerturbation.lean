import JammaLean.Kinship
import JammaLean.Invariance
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Eigensolver error reaches `Pab` and `logdet` without an eigengap

`docs/GEMMA_NUMERICAL_EQUIVALENCE_BOUND.md` bounds the eigenvector error by
`‖ΔU‖₂ ≤ C_U · ε · ‖K‖₂ / gap(K)` (§2), needs a "well-conditioned eigenspace"
(Assumption 4) to keep that finite, and carries `‖ΔU‖₂` into the `L_λ` and `L_T`
terms of its Theorem. This file shows that for `Pab` row 0 and `logdet_h` the
`‖ΔU‖/gap(K)` term is not needed.

`Invariance.lean` proves that `Pab` and `logdet_h` depend on an orthogonal
eigendecomposition `(U, ev)` only through `H = λ U diag(ev) Uᵀ + I`. A
backward-stable eigensolver returns an orthogonal `Û` and `d̂` with
`Û diag(d̂) Ûᵀ = K + E` for a small `E`. Individual eigenvectors of a clustered
spectrum can then be far from `U`, but the reconstructed `H' = λ(K + E) + I` is
close to `H`, and because `H ⪰ I` the inverse and the log-determinant are
Lipschitz in `H` with no dependence on eigenvalue separation.

**Norm.** `‖E‖` is the spectral norm (`Matrix.Norms.L2Operator`, the operator
norm on `EuclideanSpace`); `eNorm x` is the Euclidean length of a vector.
Write `δ = λ‖E‖`, and assume `0 ≤ λ`, `K` positive semidefinite, `δ < 1`.

* `resolvent_perturb`: `H'` is invertible and `‖H'⁻¹ − H⁻¹‖ ≤ δ/(1 − δ)`. `E`
  need not be symmetric.
* `dot_inv_perturb`: `|aᵀH'⁻¹b − aᵀH⁻¹b| ≤ δ/(1 − δ) · ‖a‖‖b‖`.
* `pab_row0_perturb`: the same bound for `Pab` row 0 as JAMMA computes it, the
  weighted-rotated inner product from `(Û, d̂)` against the one from `(U, ev)`.
  The positivity `0 < λ d̂ᵢ + 1` is derived, not assumed.
* `logdet_perturb`, `logdet_rotated_perturb`: `|log det H' − log det H| ≤
  n · (−log(1 − δ))`, and the same for `Σ log(λ d̂ᵢ + 1) − Σ log(λ evᵢ + 1)`.
  `E` must be symmetric; in the rotated form that follows from `hKE`. The proof
  writes `H' = L (I + M) Lᵀ` with `H = L Lᵀ` and bounds the eigenvalues of the
  symmetric `I + M` in `[1 − δ, 1 + δ]`; no Weyl inequality is used.
  `neg_log_one_sub_le` gives `−log(1 − δ) ≤ δ/(1 − δ)`.

**Approximately orthogonal `Û`** (`ÛᵀÛ = I + F`). The rotation formula then no
longer computes `aᵀH'⁻¹b`: `rotated_quad_eq` shows it computes `aᵀĜb` with
`Ĝ = Û diag(Hi_eval) Ûᵀ` for any `Û`, and `hMat_mul_rotatedInv`,
`rotatedInv_sub_inv` give the exact extra term
`Ĝ − H'⁻¹ = H'⁻¹ (ÛÛᵀ − I + Û (λ diag(d̂) F diag(Hi_eval)) Ûᵀ)`. Every entry of
`λ d̂ᵢ · Hi_eval` is in `[0, 1)` when `d̂ ≥ 0`, so this term is first order in the
loss of orthogonality and, again, has no eigengap. That norm bound is not
formalised here; only the exact identity is.

**What is assumed, not proved.** The backward-stability bound
`‖E‖ ≤ c · ε · ‖K‖` for LAPACK's `DSYEVD`/`DSYEVR` is a hypothesis about the
vendor library. These theorems take any `E` and are stated in exact arithmetic;
they bound the effect of `E`, not its size. They cover `Pab` row 0 and
`logdet_h` only. Higher `Pab` levels divide by pivots, and their sensitivity is
in `Degeneracy.lean`: `pab_step_perturb_le` takes entry errors `η` at one
level, and the row-0 bound proved here is a valid `η` at level 0 (the two are
not composed here). Eigenvalue errors enter only through `E`: the `d̂`
used is exactly the one in `Û diag(d̂) Ûᵀ = K + E`.
-/

namespace JammaLean
open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Euclidean length of a plain vector `n → ℝ` (which Mathlib gives the sup norm). -/
noncomputable def eNorm (x : n → ℝ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖

omit [DecidableEq n] in
theorem eNorm_sq (x : n → ℝ) : eNorm x ^ 2 = x ⬝ᵥ x := by
  rw [eNorm, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp]
  simp

omit [DecidableEq n] in
theorem eNorm_nonneg (x : n → ℝ) : 0 ≤ eNorm x := norm_nonneg _

omit [DecidableEq n] in
/-- Cauchy–Schwarz for `⬝ᵥ`. -/
theorem abs_dot_le (x y : n → ℝ) : |x ⬝ᵥ y| ≤ eNorm x * eNorm y := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ n) (WithLp.toLp 2 y)
  rw [EuclideanSpace.inner_toLp_toLp] at this
  simpa [eNorm, dotProduct_comm] using this

/-- `‖Ax‖ ≤ ‖A‖ ‖x‖` in the spectral norm. -/
theorem eNorm_mulVec_le (A : Matrix n n ℝ) (x : n → ℝ) : eNorm (A *ᵥ x) ≤ ‖A‖ * eNorm x :=
  A.l2_opNorm_mulVec (WithLp.toLp 2 x)

/-- A pointwise bound `‖Ax‖ ≤ C‖x‖` bounds the spectral norm. -/
theorem l2_opNorm_le_of (A : Matrix n n ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, eNorm (A *ᵥ x) ≤ C * eNorm x) : ‖A‖ ≤ C := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have := h (WithLp.ofLp x)
  simp only [eNorm, WithLp.toLp_ofLp] at this
  exact this


omit [DecidableEq n] in
/-- A coercive quadratic form, `c‖y‖² ≤ yᵀAy`, makes `A` expand every vector by at
least `c`. -/
theorem coercive_mulVec {A : Matrix n n ℝ} {c : ℝ}
    (h : ∀ y, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y)) (y : n → ℝ) :
    c * eNorm y ≤ eNorm (A *ᵥ y) := by
  have h1 : c * eNorm y ^ 2 ≤ eNorm y * eNorm (A *ᵥ y) := by
    rw [eNorm_sq]
    exact (h y).trans ((le_abs_self _).trans (abs_dot_le _ _))
  rcases (eNorm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact eNorm_nonneg _
  · nlinarith

/-- A coercive quadratic form with `c > 0` makes `A` invertible. -/
theorem det_ne_zero_of_coercive {A : Matrix n n ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ y, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y)) : A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := h v
  rw [hAv, dotProduct_zero] at this
  have hvv : v ⬝ᵥ v ≤ 0 := by nlinarith [dotProduct_self_star_nonneg v]
  have hvv' : 0 ≤ v ⬝ᵥ v := by simpa using dotProduct_self_star_nonneg v
  exact hv (dotProduct_self_eq_zero.mp (le_antisymm hvv hvv'))

/-- ...and bounds the inverse: `‖A⁻¹‖ ≤ 1/c`. -/
theorem inv_opNorm_le_of_coercive {A : Matrix n n ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ y, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (A *ᵥ y)) : ‖A⁻¹‖ ≤ 1 / c := by
  have hdet := det_ne_zero_of_coercive hc h
  refine l2_opNorm_le_of _ (by positivity) fun x => ?_
  have h1 := coercive_mulVec h (A⁻¹ *ᵥ x)
  rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec] at h1
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]
  exact h1

/-- `yᵀH'y = λ yᵀKy + λ yᵀEy + yᵀy`. -/
theorem quad_pert (K E : Matrix n n ℝ) (lam : ℝ) (y : n → ℝ) :
    y ⬝ᵥ ((lam • (K + E) + 1) *ᵥ y) =
      lam * (y ⬝ᵥ (K *ᵥ y)) + lam * (y ⬝ᵥ (E *ᵥ y)) + y ⬝ᵥ y := by
  simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

/-- `H' = λ(K + E) + I` is coercive with constant `1 − λ‖E‖`. -/
theorem coercive_hPert {K E : Matrix n n ℝ} (hK : K.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam)
    (y : n → ℝ) :
    (1 - lam * ‖E‖) * (y ⬝ᵥ y) ≤ y ⬝ᵥ ((lam • (K + E) + 1) *ᵥ y) := by
  rw [quad_pert]
  have hKy : 0 ≤ y ⬝ᵥ (K *ᵥ y) := by simpa using hK.dotProduct_mulVec_nonneg y
  have hEy : -(‖E‖ * (y ⬝ᵥ y)) ≤ y ⬝ᵥ (E *ᵥ y) := by
    rw [← eNorm_sq]
    have h2 := abs_dot_le y (E *ᵥ y)
    have h3 := eNorm_mulVec_le E y
    have h4 := eNorm_nonneg y
    have h5 := neg_abs_le (y ⬝ᵥ (E *ᵥ y))
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hEy hlam]

/-- The resolvent identity `B⁻¹ − A⁻¹ = −B⁻¹ (B − A) A⁻¹`. -/
theorem matrix_inv_sub_inv {A B : Matrix n n ℝ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    B⁻¹ - A⁻¹ = -(B⁻¹ * (B - A) * A⁻¹) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB),
    Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul,
    Matrix.mul_one, neg_sub]

/-- **Resolvent perturbation.** With `H = λK + I`, `H' = λ(K + E) + I`, `K ⪰ 0`,
`λ ≥ 0` and `λ‖E‖ < 1`: `H'` is invertible and
`‖H'⁻¹ − H⁻¹‖ ≤ λ‖E‖ / (1 − λ‖E‖)` in the spectral norm. -/
theorem resolvent_perturb {K E : Matrix n n ℝ} (hK : K.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam)
    (hδ : lam * ‖E‖ < 1) :
    (lam • (K + E) + 1).det ≠ 0 ∧
      ‖(lam • (K + E) + 1)⁻¹ - (lam • K + 1)⁻¹‖ ≤ lam * ‖E‖ / (1 - lam * ‖E‖) := by
  have hc : 0 < 1 - lam * ‖E‖ := by linarith
  have hH' := coercive_hPert (E := E) hK hlam
  have hH : ∀ y, 1 * (y ⬝ᵥ y) ≤ y ⬝ᵥ ((lam • K + 1) *ᵥ y) := by
    simpa using coercive_hPert (E := 0) hK hlam
  have dH' := det_ne_zero_of_coercive hc hH'
  have dH := det_ne_zero_of_coercive one_pos hH
  refine ⟨dH', ?_⟩
  have hdiff : lam • (K + E) + 1 - (lam • K + 1) = lam • E := by
    rw [smul_add]; abel
  rw [matrix_inv_sub_inv dH dH', hdiff, norm_neg]
  calc ‖(lam • (K + E) + 1)⁻¹ * lam • E * (lam • K + 1)⁻¹‖
      ≤ ‖(lam • (K + E) + 1)⁻¹‖ * ‖lam • E‖ * ‖(lam • K + 1)⁻¹‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 / (1 - lam * ‖E‖)) * (lam * ‖E‖) * (1 / 1) := by
        rw [norm_smul, Real.norm_of_nonneg hlam]
        gcongr
        · exact inv_opNorm_le_of_coercive hc hH'
        · exact inv_opNorm_le_of_coercive one_pos hH
    _ = lam * ‖E‖ / (1 - lam * ‖E‖) := by ring

/-- `|aᵀH'⁻¹b − aᵀH⁻¹b| ≤ λ‖E‖/(1 − λ‖E‖) ‖a‖‖b‖`. -/
theorem dot_inv_perturb {K E : Matrix n n ℝ} (hK : K.PosSemidef) {lam : ℝ} (hlam : 0 ≤ lam)
    (hδ : lam * ‖E‖ < 1) (a b : n → ℝ) :
    |a ⬝ᵥ ((lam • (K + E) + 1)⁻¹ *ᵥ b) - a ⬝ᵥ ((lam • K + 1)⁻¹ *ᵥ b)| ≤
      lam * ‖E‖ / (1 - lam * ‖E‖) * eNorm a * eNorm b := by
  rw [← dotProduct_sub, ← sub_mulVec]
  refine (abs_dot_le _ _).trans ?_
  have h1 := eNorm_mulVec_le ((lam • (K + E) + 1)⁻¹ - (lam • K + 1)⁻¹) b
  have h2 := mul_le_mul_of_nonneg_right (resolvent_perturb hK hlam hδ).2 (eNorm_nonneg b)
  have ha := eNorm_nonneg a
  calc eNorm a * eNorm (((lam • (K + E) + 1)⁻¹ - (lam • K + 1)⁻¹) *ᵥ b)
      ≤ eNorm a * (lam * ‖E‖ / (1 - lam * ‖E‖) * eNorm b) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) ha
    _ = _ := by ring

/-- The quadratic form of `M` at the `i`-th column of `U` is `(UᵀMU)ᵢᵢ`. -/
theorem quad_col (U M : Matrix n n ℝ) (i : n) :
    (U *ᵥ Pi.single i 1) ⬝ᵥ (M *ᵥ (U *ᵥ Pi.single i 1)) = (Uᵀ * M * U) i i := by
  rw [Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← dotProduct_mulVec]
  simp [Matrix.mul_assoc]

/-- If `U diag(d) Uᵀ` has a coercive `λ(·) + I` with constant `c`, every
`λ dᵢ + 1 ≥ c`. -/
theorem hpos_of_coercive {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (d : n → ℝ) {lam c : ℝ}
    (h : ∀ y, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ (hMat U d lam *ᵥ y)) (i : n) : c ≤ lam * d i + 1 := by
  have hy := h (U *ᵥ Pi.single i 1)
  have h1 : (U *ᵥ Pi.single i 1) ⬝ᵥ (U *ᵥ Pi.single i 1) = 1 := by
    have := quad_col U 1 i
    rw [Matrix.one_mulVec, Matrix.mul_one, hU] at this
    simpa using this
  have h2 : (U *ᵥ Pi.single i 1) ⬝ᵥ (hMat U d lam *ᵥ (U *ᵥ Pi.single i 1)) =
      lam * d i + 1 := by
    rw [quad_col, hMat_eq_rotated U hU]
    calc (Uᵀ * (U * diagonal (fun i => lam * d i + 1) * Uᵀ) * U) i i
        = ((Uᵀ * U) * diagonal (fun i => lam * d i + 1) * (Uᵀ * U)) i i := by
          simp only [Matrix.mul_assoc]
      _ = lam * d i + 1 := by simp [hU]
  rw [h1, h2, mul_one] at hy
  exact hy

/-- **`Pab` row 0, no eigengap.** `(U, ev)` is an exact orthogonal
eigendecomposition of the PSD kinship `K`; `(Û, d̂)` is an orthogonal
eigendecomposition of `K + E`, as a backward-stable eigensolver returns. The
weighted-rotated inner products JAMMA forms from each differ by at most
`λ‖E‖/(1 − λ‖E‖) · ‖a‖‖b‖`. -/
theorem pab_row0_perturb {K E U Û : Matrix n n ℝ} {ev d : n → ℝ} (hU : Uᵀ * U = 1)
    (hK : K = U * diagonal ev * Uᵀ) (hpsd : K.PosSemidef) (hÛ : Ûᵀ * Û = 1)
    (hKE : Û * diagonal d * Ûᵀ = K + E) {lam : ℝ} (hlam : 0 ≤ lam) (hδ : lam * ‖E‖ < 1)
    (a b : n → ℝ) :
    |@inner ℝ _ _ (rotEmbed Û d lam a) (rotEmbed Û d lam b) -
        @inner ℝ _ _ (rotEmbed U ev lam a) (rotEmbed U ev lam b)| ≤
      lam * ‖E‖ / (1 - lam * ‖E‖) * eNorm a * eNorm b := by
  have hH' : hMat Û d lam = lam • (K + E) + 1 := by rw [hMat, hKE]
  have hH : hMat U ev lam = lam • K + 1 := by rw [hMat, ← hK]
  have hposÛ : ∀ i, 0 < lam * d i + 1 := fun i =>
    lt_of_lt_of_le (by linarith) (hpos_of_coercive hÛ d
      (fun y => hH' ▸ coercive_hPert (E := E) hpsd hlam y) i)
  rw [rotEmbed, rotEmbed, rotEmbed, rotEmbed, pab_row0_eq_dense Û hÛ d lam hposÛ,
    pab_row0_eq_dense U hU ev lam (hpos_of_kinship hU hK hpsd hlam), hH', hH]
  exact dot_inv_perturb hpsd hlam hδ a b

/-- An orthogonal `U` preserves the dot product of a vector with itself. -/
theorem orth_dot_self {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (w : n → ℝ) :
    (U *ᵥ w) ⬝ᵥ (U *ᵥ w) = w ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← dotProduct_mulVec,
    hU, Matrix.one_mulVec]

omit [DecidableEq n] in
/-- `x ⬝ (A y) = (Aᵀ x) ⬝ y`. -/
theorem dot_mulVec_transpose (A : Matrix n n ℝ) (x y : n → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, Matrix.mulVec_transpose]

/-- For symmetric `A` with `(1 − δ)‖x‖² ≤ xᵀAx ≤ (1 + δ)‖x‖²`, `0 ≤ δ < 1`:
`|log det A| ≤ n·(−log(1 − δ))`. -/
theorem abs_log_det_le {A : Matrix n n ℝ} (hA : A.IsHermitian) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ < 1) (hlo : ∀ x, (1 - δ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x))
    (hhi : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ (1 + δ) * (x ⬝ᵥ x)) :
    0 < A.det ∧ |Real.log A.det| ≤ Fintype.card n * -Real.log (1 - δ) := by
  have hμ : ∀ i, 1 - δ ≤ hA.eigenvalues i ∧ hA.eigenvalues i ≤ 1 + δ := by
    intro i
    have hv : (⇑(hA.eigenvectorBasis i) : n → ℝ) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1 := by
      rw [← eNorm_sq]
      simp [eNorm, hA.eigenvectorBasis.orthonormal.1 i]
    have he := hA.eigenvalues_eq i
    simp only [star_trivial, RCLike.re_to_real] at he
    have h1 := hlo (hA.eigenvectorBasis i)
    have h2 := hhi (hA.eigenvectorBasis i)
    rw [hv, mul_one, ← he] at h1 h2
    exact ⟨h1, h2⟩
  have hpos : ∀ i, 0 < hA.eigenvalues i := fun i => by linarith [(hμ i).1]
  have hdet : A.det = ∏ i, hA.eigenvalues i := by
    simpa using hA.det_eq_prod_eigenvalues
  refine ⟨hdet ▸ Finset.prod_pos fun i _ => hpos i, ?_⟩
  rw [hdet, Real.log_prod (fun i _ => (hpos i).ne')]
  have hc : 0 < 1 - δ := by linarith
  have hbound : ∀ i, |Real.log (hA.eigenvalues i)| ≤ -Real.log (1 - δ) := by
    intro i
    rw [abs_le]
    constructor
    · rw [neg_neg]; exact Real.log_le_log hc (hμ i).1
    · have h1 := Real.log_le_log (hpos i) (hμ i).2
      have h2 : Real.log (1 + δ) + Real.log (1 - δ) ≤ 0 := by
        rw [← Real.log_mul (by linarith) hc.ne']
        exact Real.log_nonpos (by nlinarith) (by nlinarith)
      linarith
  calc |∑ i, Real.log (hA.eigenvalues i)| ≤ ∑ i, |Real.log (hA.eigenvalues i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : n, -Real.log (1 - δ) := Finset.sum_le_sum fun i _ => hbound i
    _ = Fintype.card n * -Real.log (1 - δ) := by simp

/-- `−log(1 − δ) ≤ δ/(1 − δ)`: the logdet bound has the same first-order size as the
resolvent bound. -/
theorem neg_log_one_sub_le {δ : ℝ} (hδ : δ < 1) : -Real.log (1 - δ) ≤ δ / (1 - δ) := by
  have hc : 0 < 1 - δ := by linarith
  rw [← Real.log_inv]
  have := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  have e : (1 - δ)⁻¹ - 1 = δ / (1 - δ) := by field_simp; ring
  linarith

/-- `|log det H' − log det H| ≤ n·(−log(1 − λ‖E‖))` for symmetric `E`. -/
theorem logdet_perturb {K E U : Matrix n n ℝ} {ev : n → ℝ} (hU : Uᵀ * U = 1)
    (hK : K = U * diagonal ev * Uᵀ) (hpsd : K.PosSemidef) (hE : Eᵀ = E) {lam : ℝ}
    (hlam : 0 ≤ lam) (hδ : lam * ‖E‖ < 1) :
    0 < (lam • (K + E) + 1).det ∧
      |Real.log (lam • (K + E) + 1).det - Real.log (lam • K + 1).det| ≤
        Fintype.card n * -Real.log (1 - lam * ‖E‖) := by
  set δ := lam * ‖E‖ with hδdef
  have hδ0 : 0 ≤ δ := mul_nonneg hlam (norm_nonneg _)
  have hge : ∀ i, 1 ≤ lam * ev i + 1 := fun i => by
    have := mul_nonneg hlam (eigen_nonneg hU hK hpsd i); linarith
  -- `H = L Lᵀ` with `L = U diag(√(λ ev + 1))`, and `Li` a right inverse of `L`.
  set s : n → ℝ := fun i => Real.sqrt (lam * ev i + 1) with hs
  have hs1 : ∀ i, 1 ≤ s i := fun i => Real.one_le_sqrt.mpr (hge i)
  have hs0 : ∀ i, 0 < s i := fun i => by linarith [hs1 i]
  set L := U * diagonal s
  set Li := diagonal (fun i => (s i)⁻¹) * Uᵀ
  have hUUt : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hLLi : L * Li = 1 := by
    calc L * Li = U * (diagonal s * diagonal (fun i => (s i)⁻¹)) * Uᵀ := by
          simp only [L, Li, Matrix.mul_assoc]
      _ = 1 := by
          rw [diagonal_mul_diagonal]
          have : (fun i => s i * (s i)⁻¹) = fun _ => (1 : ℝ) :=
            funext fun i => mul_inv_cancel₀ (hs0 i).ne'
          rw [this, diagonal_one, Matrix.mul_one, hUUt]
  have hLLt : L * Lᵀ = lam • K + 1 := by
    have hss : diagonal s * diagonal s = diagonal (fun i => lam * ev i + 1) := by
      rw [diagonal_mul_diagonal]
      congr 1; funext i
      exact Real.mul_self_sqrt (by linarith [hge i])
    calc L * Lᵀ = U * (diagonal s * diagonal s) * Uᵀ := by
          simp only [L, transpose_mul, diagonal_transpose, Matrix.mul_assoc]
      _ = lam • K + 1 := by rw [hss, ← hMat_eq_rotated U hU, hMat, ← hK]
  set M := Li * (lam • E) * Liᵀ
  have hfact : lam • (K + E) + 1 = L * (1 + M) * Lᵀ := by
    have hT : Liᵀ * Lᵀ = 1 := by rw [← transpose_mul, hLLi, transpose_one]
    calc lam • (K + E) + 1 = (lam • K + 1) + lam • E := by rw [smul_add]; abel
      _ = L * Lᵀ + (L * Li) * (lam • E) * (Liᵀ * Lᵀ) := by
          rw [hLLt, hLLi, hT, Matrix.one_mul, Matrix.mul_one]
      _ = L * (1 + M) * Lᵀ := by
          simp only [M, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  -- `A = I + M` is symmetric with quadratic form in `[(1 − δ), (1 + δ)]‖x‖²`.
  have hAherm : (1 + M).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    simp only [M, transpose_add, transpose_one, transpose_mul, transpose_transpose,
      transpose_smul, hE, Matrix.mul_assoc]
  have hquad : ∀ x, |x ⬝ᵥ (M *ᵥ x)| ≤ δ * (x ⬝ᵥ x) := by
    intro x
    set z := Liᵀ *ᵥ x
    have hMx : x ⬝ᵥ (M *ᵥ x) = lam * (z ⬝ᵥ (E *ᵥ z)) := by
      simp only [M, ← Matrix.mulVec_mulVec, dot_mulVec_transpose Li, smul_mulVec,
        dotProduct_smul, smul_eq_mul, z]
    have hz : z ⬝ᵥ z ≤ x ⬝ᵥ x := by
      have : z = U *ᵥ (diagonal (fun i => (s i)⁻¹) *ᵥ x) := by
        simp only [z, Li, transpose_mul, diagonal_transpose, transpose_transpose,
          Matrix.mulVec_mulVec]
      rw [this, orth_dot_self hU]
      simp only [dotProduct, mulVec_diagonal]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : (s i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hs1 i)
      have h2 : 0 ≤ (s i)⁻¹ := (inv_pos.mpr (hs0 i)).le
      nlinarith [mul_self_nonneg (x i), mul_le_mul h1 h1 h2 zero_le_one]
    have hEz : |z ⬝ᵥ (E *ᵥ z)| ≤ ‖E‖ * (z ⬝ᵥ z) := by
      rw [← eNorm_sq]
      have h2 := abs_dot_le z (E *ᵥ z)
      have h3 := eNorm_mulVec_le E z
      have h4 := eNorm_nonneg z
      nlinarith [eNorm_nonneg (E *ᵥ z)]
    rw [hMx, abs_mul, abs_of_nonneg hlam]
    calc lam * |z ⬝ᵥ (E *ᵥ z)| ≤ lam * (‖E‖ * (z ⬝ᵥ z)) :=
          mul_le_mul_of_nonneg_left hEz hlam
      _ ≤ lam * (‖E‖ * (x ⬝ᵥ x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (norm_nonneg _)) hlam
      _ = δ * (x ⬝ᵥ x) := by rw [hδdef]; ring
  have hAx : ∀ x, x ⬝ᵥ ((1 + M) *ᵥ x) = x ⬝ᵥ x + x ⬝ᵥ (M *ᵥ x) := fun x => by
    rw [add_mulVec, one_mulVec, dotProduct_add]
  obtain ⟨hApos, hAlog⟩ := abs_log_det_le hAherm hδ0 hδ
    (fun x => by rw [hAx]; nlinarith [neg_abs_le (x ⬝ᵥ (M *ᵥ x)), hquad x])
    (fun x => by rw [hAx]; nlinarith [le_abs_self (x ⬝ᵥ (M *ᵥ x)), hquad x])
  have hdetH : 0 < (lam • K + 1).det := by
    rw [← hLLt, det_mul, det_transpose]; exact mul_self_pos.mpr (fun h0 => by
      have := congrArg det hLLi; rw [det_mul, h0, zero_mul, det_one] at this
      exact zero_ne_one this)
  have hdet' : (lam • (K + E) + 1).det = (1 + M).det * (lam • K + 1).det := by
    rw [hfact, ← hLLt]; simp only [det_mul, det_transpose]; ring
  rw [hdet']
  refine ⟨mul_pos hApos hdetH, ?_⟩
  rw [Real.log_mul hApos.ne' hdetH.ne', add_sub_cancel_right]
  exact hAlog

/-- `U diag(d) Uᵀ` is symmetric. -/
theorem transpose_eigen (U : Matrix n n ℝ) (d : n → ℝ) :
    (U * diagonal d * Uᵀ)ᵀ = U * diagonal d * Uᵀ := by
  simp only [transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

/-- The logdet form JAMMA evaluates, `Σ log(λ d̂ᵢ + 1)`, from any orthogonal
eigendecomposition `Û diag(d̂) Ûᵀ = K + E`, moves by at most
`n·(−log(1 − λ‖E‖))` from its exact value. No eigengap enters. -/
theorem logdet_rotated_perturb {K E U Û : Matrix n n ℝ} {ev d : n → ℝ} (hU : Uᵀ * U = 1)
    (hK : K = U * diagonal ev * Uᵀ) (hpsd : K.PosSemidef) (hÛ : Ûᵀ * Û = 1)
    (hKE : Û * diagonal d * Ûᵀ = K + E) {lam : ℝ} (hlam : 0 ≤ lam) (hδ : lam * ‖E‖ < 1) :
    |∑ i, Real.log (lam * d i + 1) - ∑ i, Real.log (lam * ev i + 1)| ≤
      Fintype.card n * -Real.log (1 - lam * ‖E‖) := by
  have hE : Eᵀ = E := by
    have h1 : E = Û * diagonal d * Ûᵀ - K := by rw [hKE]; abel
    rw [h1, transpose_sub, transpose_eigen, hK, transpose_eigen]
  have hH' : hMat Û d lam = lam • (K + E) + 1 := by rw [hMat, hKE]
  have hH : hMat U ev lam = lam • K + 1 := by rw [hMat, ← hK]
  have hposÛ : ∀ i, 0 < lam * d i + 1 := fun i =>
    lt_of_lt_of_le (by linarith) (hpos_of_coercive hÛ d
      (fun y => hH' ▸ coercive_hPert (E := E) hpsd hlam y) i)
  rw [← logdet_hMat Û hÛ d lam hposÛ, ← logdet_hMat U hU ev lam (hpos_of_kinship hU hK hpsd hlam),
    hH', hH]
  exact (logdet_perturb hU hK hpsd hE hlam hδ).2

/-- For *any* `Û`, orthogonal or not, the rotated row 0 JAMMA computes is the
quadratic form of `Ĝ = Û diag(Hi_eval) Ûᵀ`. -/
theorem rotated_quad_eq (Û : Matrix n n ℝ) (hi a b : n → ℝ) :
    ∑ i, hi i * (rot Û a i * rot Û b i) = a ⬝ᵥ ((Û * diagonal hi * Ûᵀ) *ᵥ b) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dot_mulVec_transpose]
  simp only [dotProduct, mulVec_diagonal, rot]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- With `ÛᵀÛ = I + F`, `H' Ĝ = ÛÛᵀ + Û (λ diag(d̂) F diag(Hi_eval)) Ûᵀ`, where
`H' = λ Û diag(d̂) Ûᵀ + I` and `Ĝ = Û diag(Hi_eval) Ûᵀ`. At `F = 0` this is
`H' Ĝ = I`. -/
theorem hMat_mul_rotatedInv (Û F : Matrix n n ℝ) (hF : Ûᵀ * Û = 1 + F) (d : n → ℝ)
    (lam : ℝ) (hpos : ∀ i, lam * d i + 1 ≠ 0) :
    hMat Û d lam * (Û * diagonal (fun i => (lam * d i + 1)⁻¹) * Ûᵀ) =
      Û * Ûᵀ + Û * (diagonal (fun i => lam * d i) * F *
        diagonal (fun i => (lam * d i + 1)⁻¹)) * Ûᵀ := by
  set Di := diagonal (fun i => (lam * d i + 1)⁻¹)
  have hsplit : lam • diagonal d * Di + Di = 1 := by
    simp only [Di]
    rw [← diagonal_smul, diagonal_mul_diagonal, diagonal_add, ← diagonal_one]
    congr 1; funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hpos i]
  have hsd : lam • diagonal d = diagonal (fun i => lam * d i) := by
    rw [← diagonal_smul]; rfl
  calc hMat Û d lam * (Û * Di * Ûᵀ)
      = Û * (lam • diagonal d * (Ûᵀ * Û) * Di + Di) * Ûᵀ := by
        simp only [hMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.add_mul, Matrix.mul_assoc]
    _ = Û * (lam • diagonal d * Di + Di) * Ûᵀ +
          Û * (diagonal (fun i => lam * d i) * F * Di) * Ûᵀ := by
        rw [hF, hsd]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
        abel
    _ = _ := by rw [hsplit, Matrix.mul_one]

/-- The extra term a non-orthogonal `Û` adds: `Ĝ − H'⁻¹ = H'⁻¹ (ÛÛᵀ − I + Û (λ diag(d̂) F
diag(Hi_eval)) Ûᵀ)`. Both terms in the bracket vanish at `F = 0`. -/
theorem rotatedInv_sub_inv (Û F : Matrix n n ℝ) (hF : Ûᵀ * Û = 1 + F) (d : n → ℝ)
    (lam : ℝ) (hpos : ∀ i, lam * d i + 1 ≠ 0) (hdet : (hMat Û d lam).det ≠ 0) :
    Û * diagonal (fun i => (lam * d i + 1)⁻¹) * Ûᵀ - (hMat Û d lam)⁻¹ =
      (hMat Û d lam)⁻¹ * (Û * Ûᵀ - 1 + Û * (diagonal (fun i => lam * d i) * F *
        diagonal (fun i => (lam * d i + 1)⁻¹)) * Ûᵀ) := by
  rw [sub_add_eq_add_sub, ← hMat_mul_rotatedInv Û F hF d lam hpos, Matrix.mul_sub,
    ← Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mul,
    Matrix.mul_one]

end JammaLean
