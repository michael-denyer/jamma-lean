import JammaLean.FpSum
import Mathlib.Analysis.Real.Sqrt

/-!
# Rounding-error bounds for summation in any order

`JammaLean/FpSum.lean` proves Higham's bounds for **left-to-right** summation.
JAMMA does not sum left to right: the kinship matrix is accumulated by BLAS
`dsyrk` over 10,000-SNP batches, and Pab row 0 by BLAS `gemv`/`gemm`/
`tensordot`, which sum in blocked, pairwise or SIMD-lane order. This file
proves the same bounds for **every** summation order (Higham, *Accuracy and
Stability of Numerical Algorithms*, 2nd ed., §4.2), so the numeric corollaries
`fpGamma_float64_kinship` and `fpGamma_float64_pab` apply to what BLAS
actually computes.

JAMMA claims backed here:

* `docs/GEMMA_EQUIVALENCE.md`, Summary table ("Kinship K, O(p·ε)") and §2
  Bound: `STree.fkin_err_le_fpGamma`, `STree.fkin_err_float64`.
* `docs/GEMMA_EQUIVALENCE.md` §4 Pab Bound: `STree.fwdot_err_le_fpGamma`,
  `STree.fwdot_err_float64`.
* `docs/GEMMA_NUMERICAL_EQUIVALENCE_BOUND.md` §1, the dot-product bound in
  Cauchy–Schwarz form `|fl(xᵀy) − xᵀy| ≤ γ ‖x‖₂ ‖y‖₂`:
  `STree.fdot_err_le_fpGamma_norm`.
* "JAMMA and GEMMA differ by at most twice the bound": `two_impl_le`.

## The model

A summation order is a binary tree `STree`: `leaf i` is the term with index
`i`, `node δ l r` adds the values of its subtrees and rounds with its own
`δ`, `|δ| ≤ u` (`STree.Bounded`). Any order a BLAS kernel uses is such a
tree. A 10,000-SNP `dsyrk` batch is a subtree; accumulating the batch into
`K` is one `node` whose children are the running `K` and the batch. SIMD
lanes are subtrees joined by the final horizontal reduction. The bound depends
only on the tree's `depth`, and `depth + 1 ≤ #leaves` (`depth_lt_length`), so
every order satisfies the left-to-right `γ_{n−1}` bound; balanced trees
satisfy the much smaller `γ_{⌈log₂ n⌉}`.

The model inherits FpSum's limits: the standard model `fl(a ∘ b) =
(a ∘ b)(1 + δ)`, `|δ| ≤ u`, with **no underflow and no overflow**, no
subnormals, infinities or NaN, and no extended-precision accumulators. A fused
multiply-add is one rounding per fused operation: `fma(a, b, s)` is a `node`
whose child `a·b` is a leaf left unrounded. In the dot-product theorems that
is the case `ε i = 0` for the fused leaf, which the hypotheses allow, so an
FMA-based dot product in any order satisfies the same bound. If every leaf is
fused, `STree.err_le_fpGamma` on the exact products gives the tighter
`γ_depth`.

## Results

* `STree.err_le_fpGamma`: `|ŝ − s| ≤ γ_depth ∑ |xᵢ|`;
  `STree.err_le_fpGamma_length`: `≤ γ_{n−1} ∑ |xᵢ|` for `n` leaves.
* `STree.fdot_err_le_fpGamma`: rounded products `fl(xᵢ yᵢ)` at the leaves,
  `≤ γ_{depth+1} ∑ |xᵢ yᵢ|`.
* `STree.fkin_err_le_fpGamma`: kinship entry with the final `/ p` rounded,
  `≤ γ_{depth+2} (1/p) ∑ |xᵢ yᵢ|`.
* `STree.fwdot_err_le_fpGamma`: Pab row 0, leaves `fl(fl(hᵢ aᵢ) bᵢ)`,
  `≤ γ_{depth+2} ∑ |hᵢ aᵢ bᵢ|`.
* `STree.fkin_err_float64` (`≤ 10^6` SNPs, any order):
  `≤ 1.111e-10 · (1/p) ∑ |xᵢ yᵢ|`; `STree.fwdot_err_float64`
  (`≤ 2·10^5` samples, any order): `≤ 2.221e-11 · ∑ |hᵢ aᵢ bᵢ|`.
* `STree.fdot_err_le_fpGamma_norm`: `≤ γ_{depth+1} ‖x‖₂ ‖y‖₂` over the
  leaf index set, when each index appears once.
* `two_impl_le`: two computations each within `B` of the exact value are
  within `2B` of each other.
-/

namespace JammaLean

open Finset

/-- A summation order: a binary tree whose leaves are term indices and whose
nodes each perform one rounded addition, carrying that addition's `δ`. -/
inductive STree : Type
  | leaf : ℕ → STree
  | node : ℝ → STree → STree → STree

namespace STree

/-- Exact value: the sum of `f` over the leaves. -/
noncomputable def sum (f : ℕ → ℝ) : STree → ℝ
  | leaf i => f i
  | node _ l r => l.sum f + r.sum f

/-- Computed value: leaf `i` contributes `v i`, each node rounds its sum. -/
noncomputable def fl (v : ℕ → ℝ) : STree → ℝ
  | leaf i => v i
  | node δ l r => (l.fl v + r.fl v) * (1 + δ)

/-- Number of rounded additions on the longest root-to-leaf path. -/
def depth : STree → ℕ
  | leaf _ => 0
  | node _ l r => max l.depth r.depth + 1

/-- The leaf indices, left to right. -/
def leaves : STree → List ℕ
  | leaf i => [i]
  | node _ l r => l.leaves ++ r.leaves

/-- Every node's rounding satisfies `|δ| ≤ u`. -/
def Bounded (u : ℝ) : STree → Prop
  | leaf _ => True
  | node δ l r => |δ| ≤ u ∧ l.Bounded u ∧ r.Bounded u

theorem sum_eq_list (f : ℕ → ℝ) : ∀ t : STree, t.sum f = (t.leaves.map f).sum
  | leaf i => by simp [sum, leaves]
  | node _ l r => by simp [sum, leaves, sum_eq_list f l, sum_eq_list f r]

/-- If each index appears once, the tree sums `f` over its leaf set. -/
theorem sum_eq_finset (f : ℕ → ℝ) (t : STree) (hnd : t.leaves.Nodup) :
    t.sum f = ∑ i ∈ t.leaves.toFinset, f i := by
  rw [sum_eq_list, List.sum_toFinset f hnd]

theorem abs_sum_le (f : ℕ → ℝ) : ∀ t : STree, |t.sum f| ≤ t.sum fun i => |f i|
  | leaf _ => le_rfl
  | node _ l r => (abs_add_le _ _).trans (add_le_add (abs_sum_le f l) (abs_sum_le f r))

theorem depth_lt_length : ∀ t : STree, t.depth < t.leaves.length
  | leaf _ => by simp [depth, leaves]
  | node _ l r => by
    have := depth_lt_length l
    have := depth_lt_length r
    simp only [depth, leaves, List.length_append]
    omega

variable {u : ℝ}

/-- **Any-order summation, `(1 + u)^·` form.** Leaves carry computed values
`v i` within relative error `(1 + u)^k − 1` of `e i`; then
`|fl − ∑ e| ≤ ((1 + u)^(depth + k) − 1) ∑ |e|`. Each leaf's error is multiplied
by the at most `depth` factors `(1 + δ)` on its root path. -/
theorem err_le_pow (hu : 0 ≤ u) (v e : ℕ → ℝ) (k : ℕ) :
    ∀ t : STree, t.Bounded u →
      (∀ i ∈ t.leaves, |v i - e i| ≤ ((1 + u) ^ k - 1) * |e i|) →
      |t.fl v - t.sum e| ≤ ((1 + u) ^ (t.depth + k) - 1) * t.sum fun i => |e i|
  | leaf i, _, hv => by simpa [fl, sum, depth, leaves] using hv
  | node δ l r, ⟨hδ, hl, hr⟩, hv => by
    have ihl := err_le_pow hu v e k l hl fun i hi => hv i (List.mem_append_left _ hi)
    have ihr := err_le_pow hu v e k r hr fun i hi => hv i (List.mem_append_right _ hi)
    simp only [fl, sum, depth]
    set D := max l.depth r.depth
    have h1u : (1 : ℝ) ≤ 1 + u := by linarith
    have mono : ∀ d, d ≤ D → (1 + u) ^ (d + k) - 1 ≤ (1 + u) ^ (D + k) - 1 := fun d hd =>
      by linarith [pow_le_pow_right₀ h1u (by omega : d + k ≤ D + k)]
    have hAl := (abs_nonneg _).trans (abs_sum_le e l)
    have hAr := (abs_nonneg _).trans (abs_sum_le e r)
    have el := ihl.trans (mul_le_mul_of_nonneg_right (mono _ (le_max_left _ _)) hAl)
    have er := ihr.trans (mul_le_mul_of_nonneg_right (mono _ (le_max_right _ _)) hAr)
    have hsl := abs_sum_le e l
    have hsr := abs_sum_le e r
    generalize l.fl v = a at el
    generalize r.fl v = b at er
    generalize l.sum e = sl at el hsl
    generalize r.sum e = sr at er hsr
    generalize l.sum (fun i => |e i|) = Al at el hsl hAl
    generalize r.sum (fun i => |e i|) = Ar at er hsr hAr
    have hQ : 0 ≤ (1 + u) ^ (D + k) - 1 := pow_sub_one_nonneg hu _
    have h1 : |1 + δ| ≤ 1 + u := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
    rw [show (a + b) * (1 + δ) - (sl + sr) = ((a - sl) + (b - sr)) * (1 + δ) + δ * (sl + sr)
      by ring, show D + 1 + k = (D + k) + 1 by omega, pow_succ]
    calc _ ≤ (|a - sl| + |b - sr|) * |1 + δ| + |δ| * (|sl| + |sr|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
            gcongr <;> exact abs_add_le _ _
      _ ≤ ((1 + u) ^ (D + k) - 1) * (Al + Ar) * (1 + u) + u * (Al + Ar) := by
          have hab : |a - sl| + |b - sr| ≤ ((1 + u) ^ (D + k) - 1) * (Al + Ar) := by
            nlinarith
          have hs : |sl| + |sr| ≤ Al + Ar := by linarith
          exact add_le_add (mul_le_mul hab h1 (abs_nonneg _) (by positivity))
            (mul_le_mul hδ hs (by positivity) hu)
      _ = _ := by ring

/-- **Higham §4.2, any summation order.** `|fl − ∑ x| ≤ γ_depth ∑ |x|`. -/
theorem err_le_fpGamma (hu : 0 ≤ u) (x : ℕ → ℝ) (t : STree) (ht : t.Bounded u)
    (hd : t.depth * u < 1) :
    |t.fl x - t.sum x| ≤ fpGamma u t.depth * t.sum fun i => |x i| := by
  have h := err_le_pow hu x x 0 t ht (fun i _ => by simp)
  rw [add_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hd)
    ((abs_nonneg _).trans (abs_sum_le x t)))

/-- Any summation order over `n` leaves: `|fl − ∑ x| ≤ γ_{n−1} ∑ |x|`, the
left-to-right bound (`fsum_err_le_fpGamma`) for every tree. -/
theorem err_le_fpGamma_length (hu : 0 ≤ u) (x : ℕ → ℝ) (t : STree) (ht : t.Bounded u)
    (hn : (t.leaves.length - 1 : ℕ) * u < 1) :
    |t.fl x - t.sum x| ≤ fpGamma u (t.leaves.length - 1) * t.sum fun i => |x i| := by
  have hdn : t.depth ≤ t.leaves.length - 1 := by have := depth_lt_length t; omega
  have hd : (t.depth : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hdn) hu) hn
  exact (err_le_fpGamma hu x t ht hd).trans (mul_le_mul_of_nonneg_right
    (fpGamma_mono hu hdn hn) ((abs_nonneg _).trans (abs_sum_le x t)))

/-- Computed dot product in the order `t`: leaf `i` is `fl(xᵢ yᵢ) = xᵢ yᵢ (1 + εᵢ)`. -/
noncomputable def fdot (t : STree) (x y ε : ℕ → ℝ) : ℝ :=
  t.fl fun i => x i * y i * (1 + ε i)

/-- Computed kinship entry `(1/p) ∑ xᵢ yᵢ` in the order `t`, the division by
`p` rounded by `ζ`. -/
noncomputable def fkin (t : STree) (x y ε : ℕ → ℝ) (ζ p : ℝ) : ℝ :=
  t.fdot x y ε / p * (1 + ζ)

/-- Computed weighted dot product `∑ hᵢ aᵢ bᵢ` in the order `t`, leaf `i`
evaluated as `fl(fl(hᵢ aᵢ) bᵢ)`. -/
noncomputable def fwdot (t : STree) (h a b ε η : ℕ → ℝ) : ℝ :=
  t.fl fun i => h i * a i * (1 + ε i) * b i * (1 + η i)

lemma fdot_err_le_pow (hu : 0 ≤ u) (t : STree) (x y ε : ℕ → ℝ) (ht : t.Bounded u)
    (hε : ∀ i ∈ t.leaves, |ε i| ≤ u) :
    |t.fdot x y ε - t.sum (fun i => x i * y i)|
      ≤ ((1 + u) ^ (t.depth + 1) - 1) * t.sum fun i => |x i * y i| :=
  err_le_pow hu _ _ 1 t ht fun i hi => by
    rw [show x i * y i * (1 + ε i) - x i * y i = ε i * (x i * y i) by ring, abs_mul]
    simpa using mul_le_mul_of_nonneg_right (hε i hi) (abs_nonneg (x i * y i))

/-- **Dot product, any order** (Higham (3.4)/(3.5) for every tree):
`|fl(xᵀy) − xᵀy| ≤ γ_{depth+1} ∑ |xᵢ yᵢ|`. `εᵢ = 0` (an FMA-fused product)
is allowed. -/
theorem fdot_err_le_fpGamma (hu : 0 ≤ u) (t : STree) (x y ε : ℕ → ℝ) (ht : t.Bounded u)
    (hε : ∀ i ∈ t.leaves, |ε i| ≤ u) (hd : (t.depth + 1 : ℕ) * u < 1) :
    |t.fdot x y ε - t.sum (fun i => x i * y i)|
      ≤ fpGamma u (t.depth + 1) * t.sum fun i => |x i * y i| :=
  (fdot_err_le_pow hu t x y ε ht hε).trans (mul_le_mul_of_nonneg_right
    (pow_sub_one_le_fpGamma hu hd) ((abs_nonneg _).trans (abs_sum_le _ t)))

/-- **Kinship entry, any order.** `(1/p) ∑ xᵢ yᵢ` accumulated in the order `t`
(any blocking, batching or lane split), then divided by `p > 0` with one more
rounding: `|K̂ − K| ≤ γ_{depth+2} (1/p) ∑ |xᵢ yᵢ|`. -/
theorem fkin_err_le_fpGamma (hu : 0 ≤ u) (t : STree) (x y ε : ℕ → ℝ) (ζ p : ℝ)
    (ht : t.Bounded u) (hε : ∀ i ∈ t.leaves, |ε i| ≤ u) (hζ : |ζ| ≤ u) (hp : 0 < p)
    (hd : (t.depth + 2 : ℕ) * u < 1) :
    |t.fkin x y ε ζ p - (1 / p) * t.sum (fun i => x i * y i)|
      ≤ fpGamma u (t.depth + 2) * ((1 / p) * t.sum fun i => |x i * y i|) := by
  have hdot := fdot_err_le_pow hu t x y ε ht hε
  have hTB := abs_sum_le (fun i => x i * y i) t
  unfold fkin
  generalize t.fdot x y ε = d at hdot ⊢
  generalize t.sum (fun i => x i * y i) = T at hdot hTB ⊢
  generalize t.sum (fun i => |x i * y i|) = B at hdot hTB ⊢
  have hB : 0 ≤ B := (abs_nonneg _).trans hTB
  have hP := pow_sub_one_nonneg hu (t.depth + 1)
  have h1 : |1 + ζ| ≤ 1 + u := (abs_add_le _ _).trans (by rw [abs_one]; linarith)
  have hcore : |d * (1 + ζ) - T| ≤ ((1 + u) ^ (t.depth + 2) - 1) * B := by
    rw [show d * (1 + ζ) - T = (d - T) * (1 + ζ) + ζ * T by ring]
    calc _ ≤ |d - T| * |1 + ζ| + |ζ| * |T| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ ((1 + u) ^ (t.depth + 1) - 1) * B * (1 + u) + u * B :=
          add_le_add (mul_le_mul hdot h1 (abs_nonneg _) (mul_nonneg hP hB))
            (mul_le_mul hζ hTB (abs_nonneg _) hu)
      _ = ((1 + u) ^ (t.depth + 2) - 1) * B := by ring
  rw [show d / p * (1 + ζ) - 1 / p * T = (d * (1 + ζ) - T) / p by field_simp,
    abs_div, abs_of_pos hp, div_le_iff₀ hp]
  calc _ ≤ ((1 + u) ^ (t.depth + 2) - 1) * B := hcore
    _ ≤ fpGamma u (t.depth + 2) * B :=
        mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hd) hB
    _ = _ := by field_simp

/-- **Pab row 0, any order.** `∑ hᵢ aᵢ bᵢ` with leaves `fl(fl(hᵢ aᵢ) bᵢ)`
summed in the order `t`: `|P̂ − P| ≤ γ_{depth+2} ∑ |hᵢ aᵢ bᵢ|`. -/
theorem fwdot_err_le_fpGamma (hu : 0 ≤ u) (t : STree) (h a b ε η : ℕ → ℝ)
    (ht : t.Bounded u) (hε : ∀ i ∈ t.leaves, |ε i| ≤ u) (hη : ∀ i ∈ t.leaves, |η i| ≤ u)
    (hd : (t.depth + 2 : ℕ) * u < 1) :
    |t.fwdot h a b ε η - t.sum (fun i => h i * a i * b i)|
      ≤ fpGamma u (t.depth + 2) * t.sum fun i => |h i * a i * b i| := by
  have hpow := err_le_pow hu (fun i => h i * a i * (1 + ε i) * b i * (1 + η i))
    (fun i => h i * a i * b i) 2 t ht fun i hi => by
      have h1 := hε i hi
      have h2 := hη i hi
      rw [show h i * a i * (1 + ε i) * b i * (1 + η i) - h i * a i * b i
          = (ε i + η i + ε i * η i) * (h i * a i * b i) by ring, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      calc _ ≤ |ε i| + |η i| + |ε i| * |η i| := by
            rw [← abs_mul]; exact (abs_add_le _ _).trans (by linarith [abs_add_le (ε i) (η i)])
        _ ≤ u + u + u * u := by gcongr
        _ = (1 + u) ^ 2 - 1 := by ring
  exact hpow.trans (mul_le_mul_of_nonneg_right (pow_sub_one_le_fpGamma hu hd)
    ((abs_nonneg _).trans (abs_sum_le _ t)))

/-- **Kinship, float64, `≤ 10^6` SNPs, any summation order.** Covers `dsyrk`
blocked over 10,000-SNP batches: `|K̂ − K| ≤ 1.111e-10 · (1/p) ∑ |xᵢ yᵢ|`. -/
theorem fkin_err_float64 (t : STree) (x y ε : ℕ → ℝ) (ζ p : ℝ)
    (ht : t.Bounded (1 / 2 ^ 53)) (hε : ∀ i ∈ t.leaves, |ε i| ≤ 1 / 2 ^ 53)
    (hζ : |ζ| ≤ 1 / 2 ^ 53) (hp : 0 < p) (hn : t.leaves.length ≤ 10 ^ 6) :
    |t.fkin x y ε ζ p - (1 / p) * t.sum (fun i => x i * y i)|
      ≤ 1.111e-10 * ((1 / p) * t.sum fun i => |x i * y i|) := by
  have hdn : t.depth + 2 ≤ 10 ^ 6 + 1 := by have := depth_lt_length t; omega
  have hd : ((t.depth + 2 : ℕ) : ℝ) * (1 / 2 ^ 53) < 1 := by
    have : ((t.depth + 2 : ℕ) : ℝ) ≤ 10 ^ 6 + 1 := by exact_mod_cast hdn
    nlinarith
  have hB : 0 ≤ (1 / p) * t.sum fun i => |x i * y i| :=
    mul_nonneg (by positivity) ((abs_nonneg _).trans (abs_sum_le _ t))
  exact (fkin_err_le_fpGamma float64_u_nonneg t x y ε ζ p ht hε hζ hp hd).trans
    (mul_le_mul_of_nonneg_right (fpGamma_float64_kinship hdn) hB)

/-- **Pab row 0, float64, `≤ 2·10^5` samples, any summation order** (`gemv`,
`gemm`, `tensordot`): `|P̂ − P| ≤ 2.221e-11 · ∑ |hᵢ aᵢ bᵢ|`. -/
theorem fwdot_err_float64 (t : STree) (h a b ε η : ℕ → ℝ)
    (ht : t.Bounded (1 / 2 ^ 53)) (hε : ∀ i ∈ t.leaves, |ε i| ≤ 1 / 2 ^ 53)
    (hη : ∀ i ∈ t.leaves, |η i| ≤ 1 / 2 ^ 53) (hn : t.leaves.length ≤ 2 * 10 ^ 5) :
    |t.fwdot h a b ε η - t.sum (fun i => h i * a i * b i)|
      ≤ 2.221e-11 * t.sum fun i => |h i * a i * b i| := by
  have hdn : t.depth + 2 ≤ 2 * 10 ^ 5 + 1 := by have := depth_lt_length t; omega
  have hd : ((t.depth + 2 : ℕ) : ℝ) * (1 / 2 ^ 53) < 1 := by
    have : ((t.depth + 2 : ℕ) : ℝ) ≤ 2 * 10 ^ 5 + 1 := by exact_mod_cast hdn
    nlinarith
  exact (fwdot_err_le_fpGamma float64_u_nonneg t h a b ε η ht hε hη hd).trans
    (mul_le_mul_of_nonneg_right (fpGamma_float64_pab hdn) ((abs_nonneg _).trans (abs_sum_le _ t)))

/-- Cauchy–Schwarz over the leaf set: `∑ |xᵢ yᵢ| ≤ ‖x‖₂ ‖y‖₂` when each index
appears once. -/
theorem sum_abs_mul_le_norm (t : STree) (x y : ℕ → ℝ) (hnd : t.leaves.Nodup) :
    t.sum (fun i => |x i * y i|)
      ≤ √(∑ i ∈ t.leaves.toFinset, x i ^ 2) * √(∑ i ∈ t.leaves.toFinset, y i ^ 2) := by
  rw [sum_eq_finset _ t hnd]
  simpa [abs_mul, sq_abs] using
    Real.sum_mul_le_sqrt_mul_sqrt t.leaves.toFinset (fun i => |x i|) (fun i => |y i|)

/-- **Dot product, Cauchy–Schwarz form**
(`docs/GEMMA_NUMERICAL_EQUIVALENCE_BOUND.md` §1), any order:
`|fl(xᵀy) − xᵀy| ≤ γ_{depth+1} ‖x‖₂ ‖y‖₂`, norms over the leaf set. -/
theorem fdot_err_le_fpGamma_norm (hu : 0 ≤ u) (t : STree) (x y ε : ℕ → ℝ)
    (ht : t.Bounded u) (hnd : t.leaves.Nodup) (hε : ∀ i ∈ t.leaves, |ε i| ≤ u)
    (hd : (t.depth + 1 : ℕ) * u < 1) :
    |t.fdot x y ε - t.sum (fun i => x i * y i)|
      ≤ fpGamma u (t.depth + 1)
        * (√(∑ i ∈ t.leaves.toFinset, x i ^ 2) * √(∑ i ∈ t.leaves.toFinset, y i ^ 2)) := by
  have hγ : 0 ≤ fpGamma u (t.depth + 1) := by
    unfold fpGamma; exact div_nonneg (by positivity) (by linarith)
  exact (fdot_err_le_fpGamma hu t x y ε ht hε hd).trans
    (mul_le_mul_of_nonneg_left (sum_abs_mul_le_norm t x y hnd) hγ)

end STree

/-- **Two implementations.** If JAMMA's value `J` and GEMMA's value `G` are
each within `B` of the exact value `s`, they differ by at most `2B`. -/
theorem two_impl_le {J G s B : ℝ} (hJ : |J - s| ≤ B) (hG : |G - s| ≤ B) :
    |J - G| ≤ 2 * B := by
  calc |J - G| ≤ |J - s| + |s - G| := abs_sub_le _ _ _
    _ ≤ B + B := add_le_add hJ (by rwa [abs_sub_comm])
    _ = 2 * B := by ring

end JammaLean
