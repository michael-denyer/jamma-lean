import JammaLean.Pab
import JammaLean.Rotation
import JammaLean.Kinship
import JammaLean.ClosedForm

/-!
# Eigenbasis invariance, early row selection, and SNP batching

Three claims in `docs/GEMMA_EQUIVALENCE.md`, proved in exact arithmetic.

**§3, eigenvector signs.** The doc says "Eigenvectors may differ by sign (unique
only up to sign), but all downstream computation uses `U'y`, `U'W`, `U'x` which
are invariant to consistent sign flips." The rotated vectors themselves do flip
sign componentwise; what is invariant is everything computed from them.
This file proves the stronger statement: for *any* two orthogonal
eigendecompositions of the same `K` (sign flips, and also rotations inside a
repeated eigenvalue's eigenspace), every `Pab` level and `logdet_h` agree.

* `pab_congr_of_inner`: `Pab` depends only on the pairwise inner products of
  the original vectors, in any inner product space.
* `inner_rotated_eq`, `pab_rotated_eq`, `pab_rotated_embedCols_eq`: the
  weighted-rotated inner products, hence every `Pab` level, agree between two
  eigendecompositions, since both equal `aᵀ (λK + I)⁻¹ b`.
* `logdet_rotated_eq`: `Σ log(λ ev₁ + 1) = Σ log(λ ev₂ + 1)`.
* `pab_signFlip_eq`, `logdet_signFlip_eq`: the special case `U₂ = U₁ diag(s)`,
  `s i = ±1`, `ev₂ = ev₁`.

**§2, early row selection.** "For a fixed SNP set and transformed genotype
matrix, selecting rows before symmetric accumulation produces the corresponding
principal submatrix of full kinship." `kinship_submatrix` proves it for any
matrix and any row map; `kinship_select_after_centre` instantiates it with the
columns centred over all samples, as the doc says the LMM pipeline does.

**§2, batching.** `dsyrk` accumulates `K` over blocks of 10,000 SNPs.
`kinship_eq_sum_blocks` shows `K = (1/p) Σ_b X_b X_bᵀ` for any partition of the
SNP columns into blocks, with `p` the total SNP count; a `Finset` sum has no
order, so block order does not change `K` in exact arithmetic.
`kinship_eq_append` is the two-block form over `Fin (p₁ + p₂)`.
-/

namespace JammaLean

open Matrix

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

section Gram

variable {α : Type*}
variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- `Pab` is determined by the Gram data: if two embeddings `φ₁`, `φ₂` preserve
the same pairwise inner products, every `Pab` level built through them agrees. -/
theorem pab_congr_of_inner (φ₁ : α → E₁) (φ₂ : α → E₂)
    (h : ∀ x y, ⟪φ₁ x, φ₁ y⟫ = ⟪φ₂ x, φ₂ y⟫) (w : ℕ → α) (p : ℕ) (a b : α) :
    pab (φ₁ ∘ w) p (φ₁ a) (φ₁ b) = pab (φ₂ ∘ w) p (φ₂ a) (φ₂ b) := by
  induction p generalizing a b with
  | zero => simpa using h a b
  | succ p ih =>
    rw [pab_succ, pab_succ]
    simp only [Function.comp_apply]
    rw [ih a b, ih a (w p), ih b (w p), ih (w p) (w p)]

end Gram

section Eigenbasis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The weighted, rotated embedding JAMMA feeds `calc_pab`:
`x ↦ √Hi_eval ⊙ (Uᵀ x)`. -/
noncomputable def rotEmbed (U : Matrix n n ℝ) (ev : n → ℝ) (lam : ℝ) (x : n → ℝ) :
    EuclideanSpace ℝ n :=
  weighted (fun i => (lam * ev i + 1)⁻¹) (rot U x)

/-- Two eigendecompositions of the same `K` give the same `H = λK + I`. -/
theorem hMat_eq_of_eigen {K U₁ U₂ : Matrix n n ℝ} {ev₁ ev₂ : n → ℝ}
    (hK₁ : K = U₁ * diagonal ev₁ * U₁ᵀ) (hK₂ : K = U₂ * diagonal ev₂ * U₂ᵀ) (lam : ℝ) :
    hMat U₁ ev₁ lam = hMat U₂ ev₂ lam := by
  simp only [hMat, ← hK₁, ← hK₂]

/-- The weighted-rotated inner products agree between two orthogonal
eigendecompositions of the same `K`: both are `aᵀ (λK + I)⁻¹ b`. -/
theorem inner_rotated_eq {K U₁ U₂ : Matrix n n ℝ} {ev₁ ev₂ : n → ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1)
    (hK₁ : K = U₁ * diagonal ev₁ * U₁ᵀ) (hK₂ : K = U₂ * diagonal ev₂ * U₂ᵀ) {lam : ℝ}
    (hpos₁ : ∀ i, 0 < lam * ev₁ i + 1) (hpos₂ : ∀ i, 0 < lam * ev₂ i + 1) (a b : n → ℝ) :
    ⟪rotEmbed U₁ ev₁ lam a, rotEmbed U₁ ev₁ lam b⟫ =
      ⟪rotEmbed U₂ ev₂ lam a, rotEmbed U₂ ev₂ lam b⟫ := by
  rw [rotEmbed, rotEmbed, rotEmbed, rotEmbed, pab_row0_eq_dense U₁ hU₁ ev₁ lam hpos₁,
    pab_row0_eq_dense U₂ hU₂ ev₂ lam hpos₂, hMat_eq_of_eigen hK₁ hK₂]

/-- Every `Pab` level is the same for two orthogonal eigendecompositions of the
same `K`, for any covariates `w` and vectors `a`, `b`. -/
theorem pab_rotated_eq {K U₁ U₂ : Matrix n n ℝ} {ev₁ ev₂ : n → ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1)
    (hK₁ : K = U₁ * diagonal ev₁ * U₁ᵀ) (hK₂ : K = U₂ * diagonal ev₂ * U₂ᵀ) {lam : ℝ}
    (hpos₁ : ∀ i, 0 < lam * ev₁ i + 1) (hpos₂ : ∀ i, 0 < lam * ev₂ i + 1)
    (w : ℕ → n → ℝ) (p : ℕ) (a b : n → ℝ) :
    pab (rotEmbed U₁ ev₁ lam ∘ w) p (rotEmbed U₁ ev₁ lam a) (rotEmbed U₁ ev₁ lam b) =
      pab (rotEmbed U₂ ev₂ lam ∘ w) p (rotEmbed U₂ ev₂ lam a) (rotEmbed U₂ ev₂ lam b) :=
  pab_congr_of_inner _ _ (inner_rotated_eq hU₁ hU₂ hK₁ hK₂ hpos₁ hpos₂) w p a b

omit [DecidableEq n] in
theorem rotEmbed_zero (U : Matrix n n ℝ) (ev : n → ℝ) (lam : ℝ) :
    rotEmbed U ev lam 0 = 0 := by
  ext i
  simp [rotEmbed, weighted, rot]

/-- The same, stated with covariates as the columns of a matrix `W`, the form
`pab_rotated_eq_closedForm` uses. -/
theorem pab_rotated_embedCols_eq {K U₁ U₂ : Matrix n n ℝ} {ev₁ ev₂ : n → ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1)
    (hK₁ : K = U₁ * diagonal ev₁ * U₁ᵀ) (hK₂ : K = U₂ * diagonal ev₂ * U₂ᵀ) {lam : ℝ}
    (hpos₁ : ∀ i, 0 < lam * ev₁ i + 1) (hpos₂ : ∀ i, 0 < lam * ev₂ i + 1)
    {p : ℕ} (W : Matrix n (Fin p) ℝ) (a b : n → ℝ) :
    pab (embedCols (rotEmbed U₁ ev₁ lam) W) p (rotEmbed U₁ ev₁ lam a)
        (rotEmbed U₁ ev₁ lam b) =
      pab (embedCols (rotEmbed U₂ ev₂ lam) W) p (rotEmbed U₂ ev₂ lam a)
        (rotEmbed U₂ ev₂ lam b) := by
  have hcomp : ∀ (U : Matrix n n ℝ) (ev : n → ℝ),
      embedCols (rotEmbed U ev lam) W = rotEmbed U ev lam ∘ embedCols id W := by
    intro U ev
    funext i
    simp only [embedCols, Function.comp_apply]
    split_ifs
    · rfl
    · exact (rotEmbed_zero U ev lam).symm
  rw [hcomp, hcomp]
  exact pab_rotated_eq hU₁ hU₂ hK₁ hK₂ hpos₁ hpos₂ _ p a b

/-- `logdet_h` is the same for two orthogonal eigendecompositions of the same
`K`: both are `log det (λK + I)`. -/
theorem logdet_rotated_eq {K U₁ U₂ : Matrix n n ℝ} {ev₁ ev₂ : n → ℝ}
    (hU₁ : U₁ᵀ * U₁ = 1) (hU₂ : U₂ᵀ * U₂ = 1)
    (hK₁ : K = U₁ * diagonal ev₁ * U₁ᵀ) (hK₂ : K = U₂ * diagonal ev₂ * U₂ᵀ) {lam : ℝ}
    (hpos₁ : ∀ i, 0 < lam * ev₁ i + 1) (hpos₂ : ∀ i, 0 < lam * ev₂ i + 1) :
    ∑ i, Real.log (lam * ev₁ i + 1) = ∑ i, Real.log (lam * ev₂ i + 1) := by
  rw [← logdet_hMat U₁ hU₁ ev₁ lam hpos₁, ← logdet_hMat U₂ hU₂ ev₂ lam hpos₂,
    hMat_eq_of_eigen hK₁ hK₂]

/-- Flipping the sign of any set of eigenvectors, `U₂ = U₁ diag(s)` with
`s i = ±1`, keeps `U₂` orthogonal and `K = U₂ diag(ev) U₂ᵀ`. -/
theorem signFlip_eigen {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (ev s : n → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    (U * diagonal s)ᵀ * (U * diagonal s) = 1 ∧
      U * diagonal ev * Uᵀ = (U * diagonal s) * diagonal ev * (U * diagonal s)ᵀ := by
  have hss : ∀ i, s i * s i = 1 := fun i => by rcases hs i with h | h <;> simp [h]
  have hd : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hss)
  refine ⟨?_, ?_⟩
  · rw [transpose_mul, diagonal_transpose]
    calc diagonal s * Uᵀ * (U * diagonal s) = diagonal s * (Uᵀ * U) * diagonal s := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hd]
  · rw [transpose_mul, diagonal_transpose]
    have hmid : diagonal s * diagonal ev * diagonal s = diagonal ev := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      calc s i * ev i * s i = (s i * s i) * ev i := by ring
        _ = ev i := by rw [hss i, one_mul]
    calc U * diagonal ev * Uᵀ = U * (diagonal s * diagonal ev * diagonal s) * Uᵀ := by
          rw [hmid]
      _ = U * diagonal s * diagonal ev * (diagonal s * Uᵀ) := by
          simp only [Matrix.mul_assoc]

/-- §3: consistent sign flips of the eigenvectors leave every `Pab` level
unchanged. -/
theorem pab_signFlip_eq {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (ev s : n → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) {lam : ℝ} (hpos : ∀ i, 0 < lam * ev i + 1)
    (w : ℕ → n → ℝ) (p : ℕ) (a b : n → ℝ) :
    pab (rotEmbed U ev lam ∘ w) p (rotEmbed U ev lam a) (rotEmbed U ev lam b) =
      pab (rotEmbed (U * diagonal s) ev lam ∘ w) p (rotEmbed (U * diagonal s) ev lam a)
        (rotEmbed (U * diagonal s) ev lam b) :=
  have h := signFlip_eigen hU ev s hs
  pab_rotated_eq hU h.1 rfl h.2 hpos hpos w p a b

/-- §3: `log det H` built from sign-flipped eigenvectors is unchanged. (`logdet_h`
itself reads only `ev`, which a sign flip does not touch.) -/
theorem logdet_signFlip_eq {U : Matrix n n ℝ} (hU : Uᵀ * U = 1) (ev s : n → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) {lam : ℝ} (hpos : ∀ i, 0 < lam * ev i + 1) :
    Real.log (hMat U ev lam).det = Real.log (hMat (U * diagonal s) ev lam).det := by
  have h := signFlip_eigen hU ev s hs
  rw [logdet_hMat U hU ev lam hpos, logdet_hMat _ h.1 ev lam hpos]

end Eigenbasis

section RowSelection

variable {n m : Type*} {p : ℕ}

/-- §2: "For a fixed SNP set and transformed genotype matrix, selecting rows
before symmetric accumulation produces the corresponding principal submatrix of
full kinship." Holds for any matrix `X` and any row map `f`. -/
theorem kinship_submatrix (X : Matrix n (Fin p) ℝ) (f : m → n) :
    kinship (X.submatrix f id) = (kinship X).submatrix f f := by
  ext i j
  simp [kinship, Matrix.mul_apply]

/-- Centre every SNP column over all `n` samples. -/
noncomputable def centreCols [Fintype n] (X : Matrix n (Fin p) ℝ) : Matrix n (Fin p) ℝ :=
  fun i j => X i j - (∑ k, X k j) / Fintype.card n

/-- §2 as the LMM pipeline runs it: the doc says it "imputes and centres the
selected genotype columns over all samples", then keeps the analysed rows `f`.
Accumulating kinship over those rows gives the principal submatrix of the
all-sample kinship of the centred matrix. -/
theorem kinship_select_after_centre [Fintype n] (X : Matrix n (Fin p) ℝ) (f : m → n) :
    kinship ((centreCols X).submatrix f id) = (kinship (centreCols X)).submatrix f f :=
  kinship_submatrix _ f

end RowSelection

section Batching

variable {n : Type*}

/-- One block's contribution `X_b X_bᵀ`, with `X_b` the columns of `X` in `S`. -/
def blockGram {p : ℕ} (X : Matrix n (Fin p) ℝ) (S : Finset (Fin p)) : Matrix n n ℝ :=
  X.submatrix id ((↑) : S → Fin p) * (X.submatrix id ((↑) : S → Fin p))ᵀ

/-- §2 batching: for any partition of the SNP columns into blocks `B b`,
`K = (1/p) Σ_b X_b X_bᵀ`, with `p` the total SNP count. The `Finset` sum is
unordered, so the block order does not change `K` in exact arithmetic. -/
theorem kinship_eq_sum_blocks {ι : Type*} {p : ℕ}
    (X : Matrix n (Fin p) ℝ) (s : Finset ι) (B : ι → Finset (Fin p))
    (hdisj : (s : Set ι).PairwiseDisjoint B) (hcover : s.biUnion B = Finset.univ) :
    kinship X = (1 / (p : ℝ)) • ∑ b ∈ s, blockGram X (B b) := by
  ext i j
  simp only [kinship, blockGram, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply,
    submatrix_apply, transpose_apply, id, smul_eq_mul]
  congr 1
  calc ∑ k, X i k * X j k = ∑ k ∈ s.biUnion B, X i k * X j k := by rw [hcover]
    _ = ∑ b ∈ s, ∑ k ∈ B b, X i k * X j k := Finset.sum_biUnion hdisj
    _ = _ := Finset.sum_congr rfl fun b _ =>
        (Finset.sum_coe_sort (B b) fun k => X i k * X j k).symm

/-- Two blocks over `Fin (p₁ + p₂)`: `K = (1/(p₁+p₂)) (X₁X₁ᵀ + X₂X₂ᵀ)`. -/
theorem kinship_eq_append {p₁ p₂ : ℕ} (X : Matrix n (Fin (p₁ + p₂)) ℝ) :
    kinship X = (1 / ((p₁ + p₂ : ℕ) : ℝ)) •
      (X.submatrix id (Fin.castAdd p₂) * (X.submatrix id (Fin.castAdd p₂))ᵀ +
        X.submatrix id (Fin.natAdd p₁) * (X.submatrix id (Fin.natAdd p₁))ᵀ) := by
  ext i j
  simp only [kinship, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, submatrix_apply,
    transpose_apply, id, smul_eq_mul]
  rw [Fin.sum_univ_add]

end Batching

end JammaLean
