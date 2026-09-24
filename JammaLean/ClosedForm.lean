import JammaLean.Pab
import JammaLean.Rotation
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# CalcPab's recursion equals the closed-form projection

The `calc_pab` docstring (`src/jamma/lmm/pab.py`) says "Pab stores v_a P_p v_b",
with GEMMA's projection

    P = H⁻¹ − H⁻¹ W (Wᵀ H⁻¹ W)⁻¹ Wᵀ H⁻¹.

`Pab.lean` shows the recursion computes inner products of Gram–Schmidt
residuals. This file shows those residuals, and so the recursion, equal the
closed form whenever the covariates are linearly independent:

* `resid_eq_closedForm`, `pab_eq_closedForm`: in any real inner product space,
  with `G` the Gram matrix of `w 0, …, w (p-1)` and `v a = (⟪w j, a⟫)ⱼ`,
  `resid w p a = a − Σⱼ (G⁻¹ v a)ⱼ • w j` and
  `Pab[p, ab] = ⟪a, b⟫ − v a ⬝ᵥ G⁻¹ v b`.
* `pab_eq_matrix_closedForm`: when the inner product is `xᵀ M y` for a matrix
  `M`, and the covariates are the columns of `W`, `Pab[p, ab]` is
  `aᵀ (M − M W (Wᵀ M W)⁻¹ Wᵀ M) b`.
* `pab_rotated_eq_closedForm`: the instance JAMMA runs, `M = H⁻¹` reached
  through the eigen-rotation of `Rotation.lean`.

`G` invertible is `IsUnit G.det`; `covGram_isUnit_det` derives it from linear
independence of the covariates (Mathlib's
`Matrix.det_gram_ne_zero_iff_linearIndependent` gives the converse too). With dependent
covariates the recursion still runs (the `ps_ww == 0` branch), but the closed
form's inverse does not exist.
-/

namespace JammaLean

open Matrix

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The Gram matrix of the first `p` covariates. -/
noncomputable def covGram (w : ℕ → E) (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.gram ℝ fun i : Fin p => w i

/-- `v a = (⟪w j, a⟫)ⱼ`, the covariate cross-products `Wᵀ H⁻¹ a`. -/
def covCross (w : ℕ → E) (p : ℕ) (a : E) : Fin p → ℝ :=
  fun j => ⟪w j, a⟫

/-- Linearly independent covariates give an invertible Gram matrix. -/
theorem covGram_isUnit_det (w : ℕ → E) (p : ℕ)
    (h : LinearIndependent ℝ fun i : Fin p => w i) : IsUnit (covGram w p).det :=
  (det_gram_ne_zero_iff_linearIndependent.mpr h).isUnit

/-- The level-`p` residual is `a` minus its least-squares fit on the covariates. -/
theorem resid_eq_closedForm (w : ℕ → E) (p : ℕ) (hG : IsUnit (covGram w p).det) (a : E) :
    resid w p a = a - ∑ j : Fin p, ((covGram w p)⁻¹ *ᵥ covCross w p a) j • w j := by
  set c := (covGram w p)⁻¹ *ᵥ covCross w p a
  apply (resid_unique w p a _ _ _).symm
  · apply mem_orthogonal_covSpan
    intro i hi
    -- `⟪w i, fit⟫ = (G c)ᵢ = (G G⁻¹ v)ᵢ = vᵢ`.
    have hGc : covGram w p *ᵥ c = covCross w p a := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]
    have := congrFun hGc ⟨i, hi⟩
    simp only [mulVec, dotProduct, covGram, gram_apply, covCross] at this
    rw [inner_sub_right, inner_sum, ← this]
    simp only [inner_smul_right]
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rw [sub_sub_cancel]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (w_mem_covSpan w j.isLt)

/-- `Pab[p, ab] = ⟪a, b⟫ − v a ⬝ᵥ G⁻¹ v b`: the recursion equals the closed form. -/
theorem pab_eq_closedForm (w : ℕ → E) (p : ℕ) (hG : IsUnit (covGram w p).det) (a b : E) :
    pab w p a b =
      ⟪a, b⟫ - covCross w p a ⬝ᵥ ((covGram w p)⁻¹ *ᵥ covCross w p b) := by
  rw [pab_comm, pab_eq_inner_resid_left, resid_eq_closedForm w p hG, inner_sub_left,
    sum_inner, real_inner_comm b a, dotProduct_comm]
  simp only [inner_smul_left, RCLike.conj_to_real, dotProduct, covCross]

end Abstract

section MatrixForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The columns of `W`, embedded by `φ` and indexed by `ℕ` as `Pab.lean` expects;
indices past `p` are never read. -/
noncomputable def embedCols {p : ℕ} (φ : (n → ℝ) → E) (W : Matrix n (Fin p) ℝ) :
    ℕ → E :=
  fun i => if h : i < p then φ (Wᵀ ⟨i, h⟩) else 0

omit [DecidableEq n] in
/-- If `φ` carries `xᵀ M y` to the inner product, `Pab[p, ab]` built from the
columns of `W` is `aᵀ (M − M W (Wᵀ M W)⁻¹ Wᵀ M) b`. -/
theorem pab_eq_matrix_closedForm {p : ℕ} (φ : (n → ℝ) → E) (M : Matrix n n ℝ)
    (hφ : ∀ x y, ⟪φ x, φ y⟫ = x ⬝ᵥ (M *ᵥ y)) (W : Matrix n (Fin p) ℝ)
    (hG : IsUnit (Wᵀ * M * W).det) (a b : n → ℝ) :
    pab (embedCols φ W) p (φ a) (φ b) =
      a ⬝ᵥ ((M - M * W * (Wᵀ * M * W)⁻¹ * Wᵀ * M) *ᵥ b) := by
  have hcol : ∀ j : Fin p, embedCols φ W j = φ (Wᵀ j) := fun j => by
    simp [embedCols, j.isLt]
  have hgram : covGram (embedCols φ W) p = Wᵀ * M * W := by
    ext i j
    rw [covGram, gram_apply, hcol, hcol, hφ, dotProduct_mulVec]
    rfl
  have hcross : ∀ x, covCross (embedCols φ W) p (φ x) = Wᵀ *ᵥ (M *ᵥ x) := fun x => by
    ext j
    rw [covCross, hcol, hφ]
    rfl
  -- `M` need not be assumed symmetric: `hφ` and the inner product's symmetry give it.
  have hsymm : ∀ x y, x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := fun x y => by
    rw [← hφ, ← hφ, real_inner_comm]
  have htrans : ∀ z u, z ⬝ᵥ (Wᵀ *ᵥ u) = (W *ᵥ z) ⬝ᵥ u := fun z u => by
    rw [dotProduct_comm (W *ᵥ z), dotProduct_mulVec, dotProduct_comm, vecMul_transpose]
  rw [pab_eq_closedForm _ p (hgram ▸ hG), hgram, hcross, hcross, hφ, sub_mulVec,
    dotProduct_sub, sub_right_inj, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    ← mulVec_mulVec, hsymm, dotProduct_comm, htrans]

/-- The instance JAMMA computes: rotated, `Hi_eval`-weighted covariates and
phenotype give `Pab[p, ab] = aᵀ P b` with `P = H⁻¹ − H⁻¹W(WᵀH⁻¹W)⁻¹WᵀH⁻¹`. -/
theorem pab_rotated_eq_closedForm {p : ℕ} (U : Matrix n n ℝ) (hU : Uᵀ * U = 1)
    (ev : n → ℝ) (lam : ℝ) (hpos : ∀ i, 0 < lam * ev i + 1) (W : Matrix n (Fin p) ℝ)
    (hG : IsUnit (Wᵀ * (hMat U ev lam)⁻¹ * W).det) (a b : n → ℝ) :
    let φ := fun x => weighted (fun i => (lam * ev i + 1)⁻¹) (rot U x)
    let Hi := (hMat U ev lam)⁻¹
    pab (embedCols φ W) p (φ a) (φ b) =
      a ⬝ᵥ ((Hi - Hi * W * (Wᵀ * Hi * W)⁻¹ * Wᵀ * Hi) *ᵥ b) := by
  intro φ Hi
  exact pab_eq_matrix_closedForm φ Hi
    (fun x y => pab_row0_eq_dense U hU ev lam hpos x y) W hG a b

end MatrixForm

end JammaLean
