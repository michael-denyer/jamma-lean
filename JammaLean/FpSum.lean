import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Rounding-error bounds for summation and dot products

`docs/GEMMA_EQUIVALENCE.md` claims kinship error `O(p·ε)` (§2, the Summary
table) and a Pab row-0 weighted dot product error `O(n·ε)` (§4);
`docs/GEMMA_NUMERICAL_EQUIVALENCE_BOUND.md` §1 cites the dot-product bound
`|fl(xᵀy) − xᵀy| ≤ γ_p …`. This file proves the underlying textbook theorems
(Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., §2.2,
Lemma 3.1, §3.1 and (3.4)/(3.5)) with explicit constants.

## The model, and what it leaves out

This is the **standard model** of floating-point arithmetic: every operation
returns `exact · (1 + δ)` with `|δ| ≤ u`. The rounding operator itself stays
abstract; a computation is an exact real expression with one `δ` per
operation, each constrained only by `|δ| ≤ u`. The model assumes **no
underflow and no overflow**. Nothing here models subnormals, infinities, NaN,
fused multiply-add, or extended-precision accumulators. For IEEE-754 float64
with round-to-nearest, `u = 2^-53`; `docs/` writes `ε = 2^-52` ("machine
epsilon"), so `u = ε / 2`. The numeric corollaries below use `u = 2^-53`.

The summation theorems here cover **recursive (left-to-right) summation**.
Blocked `dsyrk`, 10,000-SNP batching, and pairwise or SIMD-lane summation
compute a different tree; `FpSumTree.lean` proves the same bounds for every
summation tree (Higham §4.2).

## Results

* `fpGamma u n = n u / (1 − n u)`, Higham's `γ_n`; `pow_sub_one_le_fpGamma`:
  `(1 + u)^n − 1 ≤ γ_n` when `n u < 1`; `fpGamma_mono`.
* `abs_prod_sub_one_le_fpGamma` (Lemma 3.1): `|∏_{i<n} (1 + δᵢ) − 1| ≤ γ_n`.
* `fsum_err_le_fpGamma` (recursive summation, N = m + 1 terms):
  `|ŝ − ∑ x| ≤ γ_{N−1} ∑ |x|`.
* `fdot_err_le_fpGamma` (dot product (3.4)/(3.5), N terms, each product
  rounded): `|fl(xᵀy) − xᵀy| ≤ γ_N ∑ |xᵢ yᵢ|`. Backs the kinship entry, a
  length-`p` dot product.
* `fkin_err_le_fpGamma` (one kinship entry `(1/p) ∑ xᵢ yᵢ` with the final
  division also rounded, N terms): `≤ γ_{N+1} (1/p) ∑ |xᵢ yᵢ|`.
* `fwdot_err_le_fpGamma` (Pab row 0, `∑ hᵢ aᵢ bᵢ` computed as
  `fl(fl(hᵢ aᵢ) bᵢ)` then summed, N terms): `≤ γ_{N+1} ∑ |hᵢ aᵢ bᵢ|`;
  `fwdot_err_le_fpGamma_of_nonneg` restates it for weights `hᵢ ≥ 0`.
* `fpGamma_float64_kinship`: `γ_n ≤ 1.111e-10` for `n ≤ 10^6 + 1`, so a
  kinship entry over `p ≤ 10^6` SNPs is within `1.111e-10 · (1/p) ∑ |x_ik x_jk|`
  of exact. `fpGamma_float64_pab`: `γ_n ≤ 2.221e-11` for `n ≤ 2·10^5 + 1`,
  the §4 Pab row-0 case with `n ≤ 200,000` samples.

The bounds are relative to `∑ |terms|`, not to `|∑ terms|`; a near-zero entry
with large cancelling terms can carry a much larger relative error. Two
computations of the same entry (JAMMA and GEMMA, different δ families or term
orders) each lie within the bound of the exact value, so they differ by at most
twice the bound.
-/

namespace JammaLean

open Finset

/-- Higham's `γ_n = n u / (1 − n u)`. Meaningful when `n u < 1`. -/
noncomputable def fpGamma (u : ℝ) (n : ℕ) : ℝ := n * u / (1 - n * u)

/-- Recursive summation in the standard model: `ŝ₀ = x 0`,
`ŝ_{k+1} = (ŝ_k + x (k+1)) (1 + δ (k+1))`. `fsum x δ m` sums `m + 1` terms
with `m` roundings; `δ 0` is unused. -/
noncomputable def fsum (x δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | k + 1 => (fsum x δ k + x (k + 1)) * (1 + δ (k + 1))

/-- Computed dot product of `m + 1` terms: each product `xᵢ yᵢ` rounded by
`ε i`, then recursive summation rounded by `δ`. -/
noncomputable def fdot (x y ε δ : ℕ → ℝ) (m : ℕ) : ℝ :=
  fsum (fun i => x i * y i * (1 + ε i)) δ m

/-- Computed weighted dot product `∑ hᵢ aᵢ bᵢ` of `m + 1` terms, evaluated as
`fl(fl(hᵢ aᵢ) bᵢ)` (roundings `ε i`, `η i`) then summed recursively (`δ`). -/
noncomputable def fwdot (h a b ε η δ : ℕ → ℝ) (m : ℕ) : ℝ :=
  fsum (fun i => h i * a i * (1 + ε i) * b i * (1 + η i)) δ m

/-- Computed kinship entry `(1/p) ∑ xᵢ yᵢ` over `m + 1` SNPs: a computed dot
product, then one rounded division by `p` (rounding `ζ`). -/
noncomputable def fkin (x y ε δ : ℕ → ℝ) (ζ p : ℝ) (m : ℕ) : ℝ :=
  fdot x y ε δ m / p * (1 + ζ)

variable {u : ℝ}

lemma one_add_pow_mul_le (hu : 0 ≤ u) : ∀ n : ℕ, (1 + u) ^ n * (1 - n * u) ≤ 1
  | 0 => by simp
  | n + 1 => by
    have ih := one_add_pow_mul_le hu n
    have e : (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u)
        = (1 + u) ^ n * (1 - n * u) - (1 + u) ^ n * ((n + 1) * u ^ 2) := by
      push_cast; ring
    have : 0 ≤ (1 + u) ^ n * ((n + 1) * u ^ 2) := by positivity
    rw [e]; linarith

lemma pow_sub_one_nonneg (hu : 0 ≤ u) (n : ℕ) : 0 ≤ (1 + u) ^ n - 1 := by
  have := one_le_pow₀ (n := n) (by linarith : (1 : ℝ) ≤ 1 + u)
  linarith

/-- `(1 + u)^n − 1 ≤ γ_n` when `n u < 1`. -/
theorem pow_sub_one_le_fpGamma (hu : 0 ≤ u) {n : ℕ} (hn : n * u < 1) :
    (1 + u) ^ n - 1 ≤ fpGamma u n := by
  unfold fpGamma
  rw [le_div_iff₀ (by linarith)]
  have e : ((1 + u) ^ n - 1) * (1 - n * u) = (1 + u) ^ n * (1 - n * u) - 1 + n * u := by ring
  rw [e]
  have := one_add_pow_mul_le hu n
  linarith

/-- `γ` is monotone in `n` on the range where it is defined. -/
theorem fpGamma_mono (hu : 0 ≤ u) {n N : ℕ} (hnN : n ≤ N) (hN : N * u < 1) :
    fpGamma u n ≤ fpGamma u N := by
  unfold fpGamma
  have h : (n : ℝ) * u ≤ N * u := mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) hu
  exact div_le_div₀ (by positivity) h (by linarith) (by linarith)

/-- Product of `1 + δᵢ`, in the `(1 + u)^n − 1` form. -/
theorem abs_prod_sub_one_le_pow (hu : 0 ≤ u) (δ : ℕ → ℝ) :
    ∀ n : ℕ, (∀ i < n, |δ i| ≤ u) → |∏ i ∈ range n, (1 + δ i) - 1| ≤ (1 + u) ^ n - 1
  | 0, _ => by simp
  | n + 1, h => by
    have ih := abs_prod_sub_one_le_pow hu δ n (fun i hi => h i (by omega))
    have hd := h n (by omega)
    rw [prod_range_succ]
    have e : (∏ i ∈ range n, (1 + δ i)) * (1 + δ n) - 1
        = ((∏ i ∈ range n, (1 + δ i)) - 1) * (1 + δ n) + δ n := by ring
    have h1 : |1 + δ n| ≤ 1 + u := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
    rw [e]
    calc _ ≤ |(∏ i ∈ range n, (1 + δ i)) - 1| * |1 + δ n| + |δ n| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ ((1 + u) ^ n - 1) * (1 + u) + u :=
          add_le_add (mul_le_mul ih h1 (abs_nonneg _) (pow_sub_one_nonneg hu n)) hd
      _ = (1 + u) ^ (n + 1) - 1 := by ring

/-- **Higham Lemma 3.1.** If `|δᵢ| ≤ u` and `n u < 1` then
`∏_{i<n} (1 + δᵢ) = 1 + θ` with `|θ| ≤ γ_n`. -/
theorem abs_prod_sub_one_le_fpGamma (hu : 0 ≤ u) (δ : ℕ → ℝ) {n : ℕ}
    (hδ : ∀ i < n, |δ i| ≤ u) (hn : n * u < 1) :
    |∏ i ∈ range n, (1 + δ i) - 1| ≤ fpGamma u n :=
  (abs_prod_sub_one_le_pow hu δ n hδ).trans (pow_sub_one_le_fpGamma hu hn)

/-- Recursive summation of `m + 1` terms, in the `(1 + u)^m − 1` form. -/
theorem fsum_err_le_pow (hu : 0 ≤ u) (x δ : ℕ → ℝ) :
    ∀ m : ℕ, (∀ i ≤ m, |δ i| ≤ u) →
      |fsum x δ m - ∑ i ∈ range (m + 1), x i| ≤ ((1 + u) ^ m - 1) * ∑ i ∈ range (m + 1), |x i|
  | 0, _ => by simp [fsum]
  | m + 1, h => by
    have ih := fsum_err_le_pow hu x δ m (fun i hi => h i (by omega))
    have hd := h (m + 1) le_rfl
    rw [sum_range_succ, sum_range_succ (fun i => |x i|)]
    simp only [fsum]
    generalize hs : fsum x δ m = s at ih
    generalize hS : ∑ i ∈ range (m + 1), x i = S at ih
    generalize hA : ∑ i ∈ range (m + 1), |x i| = A at ih
    have hSA : |S| ≤ A := hS ▸ hA ▸ abs_sum_le_sum_abs _ _
    have hA0 : 0 ≤ A := (abs_nonneg S).trans hSA
    have e : (s + x (m + 1)) * (1 + δ (m + 1)) - (S + x (m + 1))
        = (s - S) * (1 + δ (m + 1)) + δ (m + 1) * (S + x (m + 1)) := by ring
    have h1 : |1 + δ (m + 1)| ≤ 1 + u := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
    have hSx : |S + x (m + 1)| ≤ A + |x (m + 1)| := (abs_add_le _ _).trans (by linarith)
    have hP := pow_sub_one_nonneg hu m
    have hu1 : u ≤ (1 + u) ^ (m + 1) - 1 := by
      have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ u) (m + 1)
      push_cast at this; nlinarith
    rw [e]
    calc _ ≤ |s - S| * |1 + δ (m + 1)| + |δ (m + 1)| * |S + x (m + 1)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ((1 + u) ^ m - 1) * A * (1 + u) + u * (A + |x (m + 1)|) :=
          add_le_add (mul_le_mul ih h1 (abs_nonneg _) (mul_nonneg hP hA0))
            (mul_le_mul hd hSx (abs_nonneg _) hu)
      _ = ((1 + u) ^ (m + 1) - 1) * A + u * |x (m + 1)| := by ring
      _ ≤ ((1 + u) ^ (m + 1) - 1) * (A + |x (m + 1)|) := by
          nlinarith [abs_nonneg (x (m + 1))]

/-- **Recursive summation** (Higham §4.2 / (3.1) setting): with `N = m + 1`
terms and `m` roundings, `|ŝ − ∑ x| ≤ γ_{N−1} ∑ |x|`. -/
theorem fsum_err_le_fpGamma (hu : 0 ≤ u) (x δ : ℕ → ℝ) (m : ℕ)
    (hδ : ∀ i ≤ m, |δ i| ≤ u) (hm : m * u < 1) :
    |fsum x δ m - ∑ i ∈ range (m + 1), x i| ≤ fpGamma u m * ∑ i ∈ range (m + 1), |x i| :=
  (fsum_err_le_pow hu x δ m hδ).trans
    (mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hm) (sum_nonneg fun _ _ => abs_nonneg _))

/-- Summing terms that each already carry a relative error `(1 + u)^k − 1`. -/
theorem fsum_perturbed_err_le_pow (hu : 0 ≤ u) (t θ δ : ℕ → ℝ) (m k : ℕ)
    (hδ : ∀ i ≤ m, |δ i| ≤ u) (hθ : ∀ i ≤ m, |θ i| ≤ (1 + u) ^ k - 1) :
    |fsum (fun i => t i * (1 + θ i)) δ m - ∑ i ∈ range (m + 1), t i|
      ≤ ((1 + u) ^ (m + k) - 1) * ∑ i ∈ range (m + 1), |t i| := by
  set B := ∑ i ∈ range (m + 1), |t i|
  have hθ' : ∀ i ∈ range (m + 1), |θ i| ≤ (1 + u) ^ k - 1 :=
    fun i hi => hθ i (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hz : ∑ i ∈ range (m + 1), |t i * (1 + θ i)| ≤ (1 + u) ^ k * B := by
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    rw [abs_mul, mul_comm]
    have : |1 + θ i| ≤ (1 + u) ^ k :=
      (abs_add_le _ _).trans (by rw [abs_one]; linarith [hθ' i hi])
    exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hdiff : |∑ i ∈ range (m + 1), t i * (1 + θ i) - ∑ i ∈ range (m + 1), t i|
      ≤ ((1 + u) ^ k - 1) * B := by
    rw [← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
    rw [show t i * (1 + θ i) - t i = θ i * t i by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right (hθ' i hi) (abs_nonneg _)
  have hsum := fsum_err_le_pow hu (fun i => t i * (1 + θ i)) δ m hδ
  have hP := pow_sub_one_nonneg hu m
  calc _ ≤ |fsum (fun i => t i * (1 + θ i)) δ m - ∑ i ∈ range (m + 1), t i * (1 + θ i)|
          + |∑ i ∈ range (m + 1), t i * (1 + θ i) - ∑ i ∈ range (m + 1), t i| :=
        abs_sub_le _ _ _
    _ ≤ ((1 + u) ^ m - 1) * ((1 + u) ^ k * B) + ((1 + u) ^ k - 1) * B :=
        add_le_add (hsum.trans (mul_le_mul_of_nonneg_left hz hP)) hdiff
    _ = ((1 + u) ^ (m + k) - 1) * B := by rw [pow_add]; ring

/-- Dot product of `m + 1` terms, in the `(1 + u)^(m+1) − 1` form. -/
theorem fdot_err_le_pow (hu : 0 ≤ u) (x y ε δ : ℕ → ℝ) (m : ℕ)
    (hε : ∀ i ≤ m, |ε i| ≤ u) (hδ : ∀ i ≤ m, |δ i| ≤ u) :
    |fdot x y ε δ m - ∑ i ∈ range (m + 1), x i * y i|
      ≤ ((1 + u) ^ (m + 1) - 1) * ∑ i ∈ range (m + 1), |x i * y i| :=
  fsum_perturbed_err_le_pow hu (fun i => x i * y i) ε δ m 1 hδ (by simpa using hε)

/-- **Dot product, Higham (3.4)/(3.5).** With `N = m + 1` terms, each product
and each addition rounded: `|fl(xᵀy) − xᵀy| ≤ γ_N ∑ |xᵢ yᵢ|`. Backs the
`O(p·ε)` kinship claim (`docs/GEMMA_EQUIVALENCE.md` §2) with `N = p`. -/
theorem fdot_err_le_fpGamma (hu : 0 ≤ u) (x y ε δ : ℕ → ℝ) (m : ℕ)
    (hε : ∀ i ≤ m, |ε i| ≤ u) (hδ : ∀ i ≤ m, |δ i| ≤ u) (hm : (m + 1 : ℕ) * u < 1) :
    |fdot x y ε δ m - ∑ i ∈ range (m + 1), x i * y i|
      ≤ fpGamma u (m + 1) * ∑ i ∈ range (m + 1), |x i * y i| :=
  (fdot_err_le_pow hu x y ε δ m hε hδ).trans
    (mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hm) (sum_nonneg fun _ _ => abs_nonneg _))

/-- **Kinship entry.** `K_jk = (1/p) ∑_{i<N} x_ji x_ki` over `N = m + 1` SNPs,
the dot product and the division by `p > 0` all rounded:
`|K̂ − K| ≤ γ_{N+1} (1/p) ∑ |x_ji x_ki|`. -/
theorem fkin_err_le_fpGamma (hu : 0 ≤ u) (x y ε δ : ℕ → ℝ) (ζ p : ℝ) (m : ℕ)
    (hε : ∀ i ≤ m, |ε i| ≤ u) (hδ : ∀ i ≤ m, |δ i| ≤ u) (hζ : |ζ| ≤ u) (hp : 0 < p)
    (hm : (m + 2 : ℕ) * u < 1) :
    |fkin x y ε δ ζ p m - (1 / p) * ∑ i ∈ range (m + 1), x i * y i|
      ≤ fpGamma u (m + 2) * ((1 / p) * ∑ i ∈ range (m + 1), |x i * y i|) := by
  have hdot := fdot_err_le_pow hu x y ε δ m hε hδ
  unfold fkin
  generalize fdot x y ε δ m = d at hdot ⊢
  generalize hT : ∑ i ∈ range (m + 1), x i * y i = T at hdot ⊢
  have hTB : |T| ≤ ∑ i ∈ range (m + 1), |x i * y i| := hT ▸ abs_sum_le_sum_abs _ _
  generalize ∑ i ∈ range (m + 1), |x i * y i| = B at hdot hTB ⊢
  have hP := pow_sub_one_nonneg hu (m + 1)
  have h1 : |1 + ζ| ≤ 1 + u := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
  have hcore : |d * (1 + ζ) - T| ≤ ((1 + u) ^ (m + 2) - 1) * B := by
    rw [show d * (1 + ζ) - T = (d - T) * (1 + ζ) + ζ * T by ring]
    calc _ ≤ |d - T| * |1 + ζ| + |ζ| * |T| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ((1 + u) ^ (m + 1) - 1) * B * (1 + u) + u * B :=
          add_le_add (mul_le_mul hdot h1 (abs_nonneg _) (by
              have := abs_nonneg (d - T); linarith))
            (mul_le_mul hζ hTB (abs_nonneg _) hu)
      _ = ((1 + u) ^ (m + 2) - 1) * B := by ring
  rw [show d / p * (1 + ζ) - 1 / p * T = (d * (1 + ζ) - T) / p by field_simp,
    abs_div, abs_of_pos hp, div_le_iff₀ hp]
  calc _ ≤ ((1 + u) ^ (m + 2) - 1) * B := hcore
    _ ≤ fpGamma u (m + 2) * B := by
        have hB : 0 ≤ B := (abs_nonneg _).trans hTB
        exact mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hm) hB
    _ = _ := by field_simp

/-- Weighted dot product of `m + 1` terms, in the `(1 + u)^(m+2) − 1` form. -/
theorem fwdot_err_le_pow (hu : 0 ≤ u) (h a b ε η δ : ℕ → ℝ) (m : ℕ)
    (hε : ∀ i ≤ m, |ε i| ≤ u) (hη : ∀ i ≤ m, |η i| ≤ u) (hδ : ∀ i ≤ m, |δ i| ≤ u) :
    |fwdot h a b ε η δ m - ∑ i ∈ range (m + 1), h i * a i * b i|
      ≤ ((1 + u) ^ (m + 2) - 1) * ∑ i ∈ range (m + 1), |h i * a i * b i| := by
  have e : fwdot h a b ε η δ m
      = fsum (fun i => h i * a i * b i * (1 + ((1 + ε i) * (1 + η i) - 1))) δ m := by
    unfold fwdot; congr 1; funext i; ring
  rw [e]
  refine fsum_perturbed_err_le_pow hu _ _ δ m 2 hδ fun i hi => ?_
  have h1 := hε i hi
  have h2 := hη i hi
  rw [show (1 + ε i) * (1 + η i) - 1 = ε i + η i + ε i * η i by ring]
  calc _ ≤ |ε i| + |η i| + |ε i| * |η i| := by
        rw [← abs_mul]; exact (abs_add_le _ _).trans (by linarith [abs_add_le (ε i) (η i)])
    _ ≤ u + u + u * u := by gcongr
    _ = (1 + u) ^ 2 - 1 := by ring

/-- **Pab row 0**, `Pab[0,(a,b)] = ∑ hᵢ aᵢ bᵢ` over `N = m + 1` samples, with
`hᵢ aᵢ`, then `· bᵢ`, then each addition rounded:
`|P̂ − P| ≤ γ_{N+1} ∑ |hᵢ aᵢ bᵢ|`. Backs the `O(n·ε)` claim of
`docs/GEMMA_EQUIVALENCE.md` §4. -/
theorem fwdot_err_le_fpGamma (hu : 0 ≤ u) (h a b ε η δ : ℕ → ℝ) (m : ℕ)
    (hε : ∀ i ≤ m, |ε i| ≤ u) (hη : ∀ i ≤ m, |η i| ≤ u) (hδ : ∀ i ≤ m, |δ i| ≤ u)
    (hm : (m + 2 : ℕ) * u < 1) :
    |fwdot h a b ε η δ m - ∑ i ∈ range (m + 1), h i * a i * b i|
      ≤ fpGamma u (m + 2) * ∑ i ∈ range (m + 1), |h i * a i * b i| :=
  (fwdot_err_le_pow hu h a b ε η δ m hε hη hδ).trans
    (mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hm) (sum_nonneg fun _ _ => abs_nonneg _))

/-- `fwdot_err_le_fpGamma` for nonnegative weights, the JAMMA case
`hᵢ = 1 / (λ dᵢ + 1) > 0`: the bound is `γ_{N+1} ∑ hᵢ |aᵢ bᵢ|`. -/
theorem fwdot_err_le_fpGamma_of_nonneg (hu : 0 ≤ u) (h a b ε η δ : ℕ → ℝ) (m : ℕ)
    (hh : ∀ i, 0 ≤ h i)
    (hε : ∀ i ≤ m, |ε i| ≤ u) (hη : ∀ i ≤ m, |η i| ≤ u) (hδ : ∀ i ≤ m, |δ i| ≤ u)
    (hm : (m + 2 : ℕ) * u < 1) :
    |fwdot h a b ε η δ m - ∑ i ∈ range (m + 1), h i * a i * b i|
      ≤ fpGamma u (m + 2) * ∑ i ∈ range (m + 1), h i * |a i * b i| := by
  have := fwdot_err_le_fpGamma hu h a b ε η δ m hε hη hδ hm
  have e : ∑ i ∈ range (m + 1), |h i * a i * b i| = ∑ i ∈ range (m + 1), h i * |a i * b i| :=
    sum_congr rfl fun i _ => by rw [mul_assoc, abs_mul, abs_of_nonneg (hh i)]
  rwa [e] at this

/-- float64 round-to-nearest unit roundoff `u = 2^-53` (`= ε/2` in the docs). -/
lemma float64_u_nonneg : (0 : ℝ) ≤ 1 / 2 ^ 53 := by positivity

/-- **Kinship, `p ≤ 10^6`.** With `u = 2^-53`, `γ_n ≤ 1.111e-10` for every
`n ≤ 10^6 + 1`, covering `fkin_err_le_fpGamma` (`γ_{p+1}`) and
`fdot_err_le_fpGamma` (`γ_p`). With the docs' `ε = 2^-52` in place of `u`
this would read about `2.22e-10`; both are the `O(10^-10)` of §2. -/
theorem fpGamma_float64_kinship {n : ℕ} (hn : n ≤ 10 ^ 6 + 1) :
    fpGamma (1 / 2 ^ 53) n ≤ 1.111e-10 := by
  have hN : ((10 ^ 6 + 1 : ℕ) : ℝ) * (1 / 2 ^ 53) < 1 := by norm_num
  refine (fpGamma_mono float64_u_nonneg hn hN).trans ?_
  unfold fpGamma
  rw [div_le_iff₀ (by linarith)]
  norm_num

/-- **Pab row 0, `n ≤ 200,000` samples.** With `u = 2^-53`,
`γ_k ≤ 2.221e-11` for every `k ≤ 2·10^5 + 1`, covering
`fwdot_err_le_fpGamma` (`γ_{n+1}`); the `O(10^-11)` of
`docs/GEMMA_EQUIVALENCE.md` §4. -/
theorem fpGamma_float64_pab {n : ℕ} (hn : n ≤ 2 * 10 ^ 5 + 1) :
    fpGamma (1 / 2 ^ 53) n ≤ 2.221e-11 := by
  have hN : ((2 * 10 ^ 5 + 1 : ℕ) : ℝ) * (1 / 2 ^ 53) < 1 := by norm_num
  refine (fpGamma_mono float64_u_nonneg hn hN).trans ?_
  unfold fpGamma
  rw [div_le_iff₀ (by linarith)]
  norm_num

end JammaLean
