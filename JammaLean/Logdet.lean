import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The mantissa-product `logdet(H)`

`logdet_h_lambda` in `src/jamma/lmm/_lmm_logdet.h` computes
`Σ_i log(λ ev_i + 1)` without a per-element `log`. It splits each
`v = m * 2^e`, multiplies mantissas in four lanes, adds exponents as integers,
renormalises each lane on the schedule `(i & 60) == 60`, folds the tail into
lane 0, combines the lanes, and calls `log` once.

This file models that loop over the reals. `split` stands for
`logdet_frexp_bits` and is assumed only to return a positive mantissa with
`x = m * 2^e` for positive `x`. `logdetKernel_eq_sum_log` proves that the
kernel equals `Σ log v_i` for every such `split`, every `n`, and every
renormalisation schedule. The schedule and the lane count affect only
underflow, which is a floating-point concern outside this model.
-/

namespace JammaLean

open Real

/-- A running product in the form `p * 2^e`. -/
structure Acc where
  p : ℝ
  e : ℤ

namespace Acc

noncomputable def val (s : Acc) : ℝ := s.p * (2 : ℝ) ^ s.e

def one : Acc := ⟨1, 0⟩

end Acc

section Kernel

-- A mantissa-exponent split: `logdet_frexp_bits`.
variable (split : ℝ → ℝ × ℤ)

/-- `p *= frexp(v, &a); e += a;` -/
def absorb (s : Acc) (v : ℝ) : Acc := ⟨s.p * (split v).1, s.e + (split v).2⟩

/-- `p = frexp(p, &a); e += a;` -/
def renorm (s : Acc) : Acc := ⟨(split s.p).1, s.e + (split s.p).2⟩

/-- The four lanes after `k` blocks of four elements. -/
def lanes (v : ℕ → ℝ) : ℕ → Acc × Acc × Acc × Acc
  | 0 => (Acc.one, Acc.one, Acc.one, Acc.one)
  | k + 1 =>
    let (a, b, c, d) := lanes v k
    let i := 4 * k
    let a := absorb split a (v i)
    let b := absorb split b (v (i + 1))
    let c := absorb split c (v (i + 2))
    let d := absorb split d (v (i + 3))
    if i &&& 60 = 60 then (renorm split a, renorm split b, renorm split c, renorm split d)
    else (a, b, c, d)

/-- The scalar tail loop: elements `start, …, start + t - 1` into lane 0. -/
def tail (v : ℕ → ℝ) (start : ℕ) : ℕ → Acc → Acc
  | 0, s => s
  | t + 1, s => tail v start t (absorb split s (v (start + t)))

/-- The whole kernel, ending in `log(p) + e * ln 2`. -/
noncomputable def logdetKernel (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  let (a, b, c, d) := lanes split v (n / 4)
  let a := tail split v (4 * (n / 4)) (n % 4) a
  let a := renorm split a
  let b := renorm split b
  let c := renorm split c
  let d := renorm split d
  let e := a.e + b.e + c.e + d.e
  let s1 := split (a.p * b.p)
  let s2 := split (s1.1 * c.p)
  log (s2.1 * d.p) + ((e + s1.2 + s2.2 : ℤ) : ℝ) * log 2

variable (hsplit : ∀ x, 0 < x → 0 < (split x).1 ∧ x = (split x).1 * (2 : ℝ) ^ (split x).2)
include hsplit

theorem absorb_spec {s : Acc} {v : ℝ} (hs : 0 < s.p) (hv : 0 < v) :
    0 < (absorb split s v).p ∧ (absorb split s v).val = s.val * v := by
  obtain ⟨hm, heq⟩ := hsplit v hv
  refine ⟨mul_pos hs hm, ?_⟩
  simp only [absorb, Acc.val]
  rw [zpow_add₀ two_ne_zero]
  conv_rhs => rw [heq]
  ring

theorem renorm_spec {s : Acc} (hs : 0 < s.p) :
    0 < (renorm split s).p ∧ (renorm split s).val = s.val := by
  obtain ⟨hm, heq⟩ := hsplit s.p hs
  refine ⟨hm, ?_⟩
  simp only [renorm, Acc.val]
  rw [zpow_add₀ two_ne_zero]
  conv_rhs => rw [heq]
  ring

/-- Lane invariant: every lane stays positive, and the four lane values multiply
to the product of the elements absorbed so far. -/
theorem lanes_spec (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (k : ℕ) :
    let (a, b, c, d) := lanes split v k
    0 < a.p ∧ 0 < b.p ∧ 0 < c.p ∧ 0 < d.p ∧
      a.val * b.val * c.val * d.val = ∏ i ∈ Finset.range (4 * k), v i := by
  induction k with
  | zero => simp [lanes, Acc.one, Acc.val]
  | succ k ih =>
    simp only [lanes]
    obtain ⟨ha, hb, hc, hd, hprod⟩ := ih
    set a := (lanes split v k).1
    set b := (lanes split v k).2.1
    set c := (lanes split v k).2.2.1
    set d := (lanes split v k).2.2.2
    obtain ⟨ha', hva⟩ := absorb_spec split hsplit ha (hv (4 * k))
    obtain ⟨hb', hvb⟩ := absorb_spec split hsplit hb (hv (4 * k + 1))
    obtain ⟨hc', hvc⟩ := absorb_spec split hsplit hc (hv (4 * k + 2))
    obtain ⟨hd', hvd⟩ := absorb_spec split hsplit hd (hv (4 * k + 3))
    have hrange : ∏ i ∈ Finset.range (4 * (k + 1)), v i =
        (∏ i ∈ Finset.range (4 * k), v i) *
          (v (4 * k) * v (4 * k + 1) * v (4 * k + 2) * v (4 * k + 3)) := by
      rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by ring]
      simp only [Finset.prod_range_succ]
      ring
    have hmain : (absorb split a (v (4 * k))).val * (absorb split b (v (4 * k + 1))).val *
        (absorb split c (v (4 * k + 2))).val * (absorb split d (v (4 * k + 3))).val =
          ∏ i ∈ Finset.range (4 * (k + 1)), v i := by
      rw [hva, hvb, hvc, hvd, hrange, ← hprod]
      ring
    split_ifs
    · obtain ⟨ra, hra⟩ := renorm_spec split hsplit ha'
      obtain ⟨rb, hrb⟩ := renorm_spec split hsplit hb'
      obtain ⟨rc, hrc⟩ := renorm_spec split hsplit hc'
      obtain ⟨rd, hrd⟩ := renorm_spec split hsplit hd'
      exact ⟨ra, rb, rc, rd, by rw [hra, hrb, hrc, hrd, hmain]⟩
    · exact ⟨ha', hb', hc', hd', hmain⟩

theorem tail_spec (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (start : ℕ) :
    ∀ (t : ℕ) (s : Acc), 0 < s.p →
      0 < (tail split v start t s).p ∧
        (tail split v start t s).val = s.val * ∏ i ∈ Finset.range t, v (start + i) := by
  intro t
  induction t with
  | zero => intro s hs; simp [tail, hs]
  | succ t ih =>
    intro s hs
    obtain ⟨hs', hval⟩ := absorb_spec split hsplit hs (hv (start + t))
    obtain ⟨hpos, htail⟩ := ih _ hs'
    refine ⟨hpos, ?_⟩
    simp only [tail]
    rw [htail, hval, Finset.prod_range_succ]
    ring

/-- The C kernel computes `Σ log v_i` exactly, in real arithmetic, for every
split satisfying `hsplit`. -/
theorem logdetKernel_eq_sum_log (v : ℕ → ℝ) (hv : ∀ i, 0 < v i) (n : ℕ) :
    logdetKernel split v n = ∑ i ∈ Finset.range n, log (v i) := by
  have hL := lanes_spec split hsplit v hv (n / 4)
  unfold logdetKernel
  set a := (lanes split v (n / 4)).1
  set b := (lanes split v (n / 4)).2.1
  set c := (lanes split v (n / 4)).2.2.1
  set d := (lanes split v (n / 4)).2.2.2
  obtain ⟨ha, hb, hc, hd, hprod⟩ := hL
  obtain ⟨ht, htv⟩ := tail_spec split hsplit v hv (4 * (n / 4)) (n % 4) a ha
  obtain ⟨ra, hra⟩ := renorm_spec split hsplit ht
  obtain ⟨rb, hrb⟩ := renorm_spec split hsplit hb
  obtain ⟨rc, hrc⟩ := renorm_spec split hsplit hc
  obtain ⟨rd, hrd⟩ := renorm_spec split hsplit hd
  set A := renorm split (tail split v (4 * (n / 4)) (n % 4) a)
  set B := renorm split b
  set C := renorm split c
  set D := renorm split d
  obtain ⟨hm1, h1⟩ := hsplit (A.p * B.p) (mul_pos ra rb)
  obtain ⟨hm2, h2⟩ := hsplit ((split (A.p * B.p)).1 * C.p) (mul_pos hm1 rc)
  -- The total product of all `n` elements.
  have hall : ∏ i ∈ Finset.range n, v i =
      (∏ i ∈ Finset.range (4 * (n / 4)), v i) *
        ∏ i ∈ Finset.range (n % 4), v (4 * (n / 4) + i) := by
    conv_lhs => rw [← Nat.div_add_mod n 4]
    rw [Finset.prod_range_add]
  have hval : A.val * B.val * C.val * D.val = ∏ i ∈ Finset.range n, v i := by
    rw [hra, hrb, hrc, hrd, htv, hall, ← hprod]
    ring
  -- The final mantissa and exponent carry the same value.
  set s1 := split (A.p * B.p)
  set s2 := split (s1.1 * C.p)
  have hfinal : s2.1 * D.p * (2 : ℝ) ^ (A.e + B.e + C.e + D.e + s1.2 + s2.2) =
      ∏ i ∈ Finset.range n, v i := by
    rw [← hval]
    simp only [Acc.val]
    have e1 : A.p * B.p = s1.1 * (2 : ℝ) ^ s1.2 := h1
    have e2 : s1.1 * C.p = s2.1 * (2 : ℝ) ^ s2.2 := h2
    rw [zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero,
      zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero]
    calc s2.1 * D.p * (2 ^ A.e * 2 ^ B.e * 2 ^ C.e * 2 ^ D.e * 2 ^ s1.2 * 2 ^ s2.2)
        = (s2.1 * 2 ^ s2.2) * D.p * (2 ^ A.e * 2 ^ B.e * 2 ^ C.e * 2 ^ D.e * 2 ^ s1.2) := by
          ring
      _ = (s1.1 * 2 ^ s1.2) * C.p * D.p * (2 ^ A.e * 2 ^ B.e * 2 ^ C.e * 2 ^ D.e) := by
          rw [← e2]; ring
      _ = A.p * 2 ^ A.e * (B.p * 2 ^ B.e) * (C.p * 2 ^ C.e) * (D.p * 2 ^ D.e) := by
          rw [← e1]; ring
  have hpos : 0 < s2.1 * D.p := mul_pos hm2 rd
  rw [← Real.log_prod (fun i _ => (hv i).ne'), ← hfinal,
    Real.log_mul hpos.ne' (zpow_ne_zero _ two_ne_zero), Real.log_zpow]

end Kernel

end JammaLean
