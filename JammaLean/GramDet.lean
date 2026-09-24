import JammaLean.Pab
import JammaLean.Rotation
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The Pab diagonal is a Gram determinant

JAMMA's REML term (`src/jamma/lmm/likelihood_numpy.py`, `_reml_logl`) is

    logdet_hiw = Σ_{i ≤ n_cvt} log Pab[i, (i+1,i+1)] - Σ log Iab[i, (i+1,i+1)]

where `_logdet_diag` sums the logs over `pab.py` `logdet_diag_indices`, `Pab`
uses `H⁻¹` weights and `Iab` identity weights. `Pab[i, (i+1,i+1)]` is
`pab w i (w i) (w i)`: the squared norm of covariate `i` after the earlier ones
are projected out. This file proves:

* `prod_pab_diag_eq_det_gram`: the product of those entries is the Gram
  determinant `det [⟪w i, w j⟫]`.
* `sum_log_pab_diag_eq_log_det_gram`: with positive entries, the log-sum is
  `log det` of the Gram matrix.
* `gram_weighted_rot_eq`: with the `Rotation.lean` weighting, the Gram matrix
  is `Wᵀ H⁻¹ W`; at `λ = 0` (identity weights) it is `Wᵀ W`.
* `logdet_hiw_eq`: `logdet_hiw = log det (Wᵀ H⁻¹ W) - log det (Wᵀ W)`.

The proof writes each residual as `w i` minus a combination of earlier `w j`:
a unit lower-triangular change of basis (determinant 1) that turns the Gram
matrix of `w` into the diagonal Gram matrix of the pairwise orthogonal residuals.
-/

namespace JammaLean

open Matrix

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- The level-`i` residuals of the covariates themselves are pairwise orthogonal. -/
theorem inner_resid_diag_of_lt (w : ℕ → E) {i j : ℕ} (hij : i < j) :
    ⟪resid w i (w i), resid w j (w j)⟫ = 0 := by
  have hmem : resid w i (w i) ∈ covSpan w j := by
    have : resid w i (w i) = w i - (w i - resid w i (w i)) := by abel
    rw [this]
    exact Submodule.sub_mem _ (w_mem_covSpan w hij)
      (covSpan_mono w hij.le (sub_resid_mem_span w i (w i)))
  rw [real_inner_comm]
  exact (Submodule.mem_orthogonal' _ _).mp (resid_mem_orthogonal w j (w j)) _ hmem

/-- `∏_{i<k} Pab[i, (i+1,i+1)] = det Gram(w 0, …, w (k-1))`. -/
theorem prod_pab_diag_eq_det_gram (w : ℕ → E) (k : ℕ) :
    ∏ i ∈ Finset.range k, pab w i (w i) (w i) = (gram ℝ (fun i : Fin k => w i)).det := by
  classical
  set r : ℕ → E := fun i => resid w i (w i) with hr
  -- Coefficients of `w i - r i` in the earlier covariates.
  have hex : ∀ i : ℕ, ∃ l ∈ Finsupp.supported ℝ ℝ {j | j < i},
      Finsupp.linearCombination ℝ w l = w i - r i := fun i =>
    (Finsupp.mem_span_image_iff_linearCombination ℝ).mp (sub_resid_mem_span w i (w i))
  choose l hl_supp hl_eq using hex
  have hl_zero : ∀ i j : ℕ, ¬ j < i → l i j = 0 := fun i j hj =>
    Finsupp.notMem_support_iff.mp fun h => hj ((Finsupp.mem_supported ℝ _).mp (hl_supp i) h)
  let A : Matrix (Fin k) (Fin k) ℝ := fun i j => (if i = j then 1 else 0) - l i j
  -- `r i = Σ_j A i j • w j`.
  have hrA : ∀ i : Fin k, r i = ∑ j : Fin k, A i j • w j := by
    intro i
    have hlc : Finsupp.linearCombination ℝ w (l i) = ∑ j : Fin k, l i j • w j := by
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset (l i) (s := Finset.range k)]
      · exact (Fin.sum_univ_eq_sum_range (fun j => l i j • w j) k).symm
      · intro j hj
        have := (Finsupp.mem_supported ℝ _).mp (hl_supp i) hj
        exact Finset.mem_range.mpr (lt_trans this i.isLt)
      · intros; simp
    have : r i = w i - Finsupp.linearCombination ℝ w (l i) := by rw [hl_eq]; abel
    rw [this, hlc]
    simp only [A, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Gram of the residuals is `A G Aᵀ`.
  have hgram : gram ℝ (fun i : Fin k => r i) = A * gram ℝ (fun i : Fin k => w i) * Aᵀ := by
    ext i j
    rw [gram_apply, hrA i, hrA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
      Matrix.mul_apply, transpose_apply, gram_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  -- `A` is unit lower triangular.
  have hA_lower : A.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    simp [A, hij'.ne, hl_zero i j (by exact_mod_cast not_lt.mpr hij'.le)]
  have hA_det : A.det = 1 := by
    rw [det_of_isLowerTriangular A hA_lower]
    refine Finset.prod_eq_one fun i _ => ?_
    simp [A, hl_zero i i (lt_irrefl _)]
  -- Gram of the residuals is diagonal.
  have hdiag : gram ℝ (fun i : Fin k => r i) =
      diagonal (fun i : Fin k => pab w i (w i) (w i)) := by
    ext i j
    rw [gram_apply]
    by_cases hij : i = j
    · subst hij; simp [pab, r]
    · rw [diagonal_apply_ne _ hij]
      rcases lt_or_gt_of_ne hij with h | h
      · exact inner_resid_diag_of_lt w (by exact_mod_cast h)
      · rw [real_inner_comm]; exact inner_resid_diag_of_lt w (by exact_mod_cast h)
  have := congrArg det hgram
  rw [hdiag, det_diagonal, det_mul, det_mul, det_transpose, hA_det, one_mul, mul_one] at this
  rw [← this, Fin.prod_univ_eq_prod_range (fun i => pab w i (w i) (w i)) k]

/-- With every diagonal entry positive (which holds exactly when the covariates are
linearly independent; that equivalence is not proved here), the log-sum
`_logdet_diag` computes is `log det` of the Gram matrix. -/
theorem sum_log_pab_diag_eq_log_det_gram (w : ℕ → E) (k : ℕ)
    (hpos : ∀ i < k, 0 < pab w i (w i) (w i)) :
    ∑ i ∈ Finset.range k, Real.log (pab w i (w i) (w i)) =
      Real.log (gram ℝ (fun i : Fin k => w i)).det := by
  rw [← prod_pab_diag_eq_det_gram, Real.log_prod]
  intro i hi
  exact (hpos i (Finset.mem_range.mp hi)).ne'

end Gram

section Rotated

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `H⁻¹`-weighted Gram matrix of the rotated covariate columns is
`Wᵀ H⁻¹ W`, with `W` the dense `n × k` covariate matrix. -/
theorem gram_weighted_rot_eq (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (k : ℕ) (x : ℕ → n → ℝ) :
    gram ℝ (fun i : Fin k => weighted (fun s => (lam * ev s + 1)⁻¹) (rot U (x i))) =
      (of fun (s : n) (i : Fin k) => x i s)ᵀ * (hMat U ev lam)⁻¹ *
        of fun (s : n) (i : Fin k) => x i s := by
  ext i j
  rw [gram_apply, pab_row0_eq_dense U hU ev lam hpos]
  simp only [dotProduct, mulVec, Matrix.mul_apply, transpose_apply, of_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- At `λ = 0` the weights are all one (`Iab`), and the Gram matrix is `Wᵀ W`. -/
theorem gram_rot_eq (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (k : ℕ)
    (x : ℕ → n → ℝ) :
    gram ℝ (fun i : Fin k => weighted (fun s => (0 * ev s + 1)⁻¹) (rot U (x i))) =
      (of fun (s : n) (i : Fin k) => x i s)ᵀ * of fun (s : n) (i : Fin k) => x i s := by
  have h1 : hMat U ev 0 = 1 := by simp [hMat]
  rw [gram_weighted_rot_eq U hU ev 0 (fun i => by simp) k x, h1, inv_one, Matrix.mul_one]

/-- JAMMA's `logdet_hiw`: the `Pab` log-sum (`H⁻¹` weights) minus the `Iab`
log-sum (identity weights) is `log det (Wᵀ H⁻¹ W) - log det (Wᵀ W)`. Covariate
`i` is the column `x i`; both sets of diagonal entries are assumed positive, the
case `_logdet_diag` does not turn into NaN. -/
theorem logdet_hiw_eq (U : Matrix n n ℝ) (hU : Uᵀ * U = 1) (ev : n → ℝ) (lam : ℝ)
    (hpos : ∀ i, 0 < lam * ev i + 1) (k : ℕ) (x : ℕ → n → ℝ)
    (wH wI : ℕ → EuclideanSpace ℝ n)
    (hwH : wH = fun i => weighted (fun s => (lam * ev s + 1)⁻¹) (rot U (x i)))
    (hwI : wI = fun i => weighted (fun s => (0 * ev s + 1)⁻¹) (rot U (x i)))
    (hH : ∀ i < k, 0 < pab wH i (wH i) (wH i))
    (hI : ∀ i < k, 0 < pab wI i (wI i) (wI i)) :
    ∑ i ∈ Finset.range k, Real.log (pab wH i (wH i) (wH i)) -
        ∑ i ∈ Finset.range k, Real.log (pab wI i (wI i) (wI i)) =
      Real.log ((of fun (s : n) (i : Fin k) => x i s)ᵀ * (hMat U ev lam)⁻¹ *
          of fun (s : n) (i : Fin k) => x i s).det -
        Real.log ((of fun (s : n) (i : Fin k) => x i s)ᵀ *
          of fun (s : n) (i : Fin k) => x i s).det := by
  rw [sum_log_pab_diag_eq_log_det_gram wH k hH, sum_log_pab_diag_eq_log_det_gram wI k hI,
    ← gram_weighted_rot_eq U hU ev lam hpos k x, ← gram_rot_eq U hU ev k x, hwH, hwI]

end Rotated

end JammaLean
