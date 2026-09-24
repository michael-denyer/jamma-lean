import Mathlib.Algebra.Order.Field.Power
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# The bit-level split `logdet_frexp_bits`

`logdet_frexp_bits` in `src/jamma/lmm/_lmm_logdet.h` splits a positive normal
double without calling `frexp`:

```c
*e = (int64_t)((x.u >> 52) & 0x7ff) - 1022;
x.u = (x.u & 0x800fffffffffffffULL) | ((uint64_t)1022 << 52);
```

`Logdet.lean` assumes only that the split returns a positive mantissa `m` with
`x = m * 2^e`. This file models IEEE-754 binary64 decoding of normal numbers
over the bit pattern `u : ℕ` and proves the two C lines meet that assumption:
`frexpBits_eq` connects the bitwise expression to the field arithmetic, and
`frexpBits_split` gives `decode u = decode u' * 2^e` with `decode u' ∈ [1/2, 1)`.
-/

namespace JammaLean

/-! ### Fields of a binary64 pattern -/

/-- Sign bit. -/
def fpSign (u : ℕ) : ℕ := u / 2 ^ 63

/-- Biased exponent, `(u >> 52) & 0x7ff`. -/
def fpExp (u : ℕ) : ℕ := (u / 2 ^ 52) % 2 ^ 11

/-- Fraction bits. -/
def fpFrac (u : ℕ) : ℕ := u % 2 ^ 52

/-- The value of a normal binary64 pattern: `(-1)^s (1 + f/2^52) 2^(E - 1023)`. -/
noncomputable def decode (u : ℕ) : ℝ :=
  (-1) ^ fpSign u * (1 + (fpFrac u : ℝ) / 2 ^ 52) * (2 : ℝ) ^ ((fpExp u : ℤ) - 1023)

/-- `u` encodes a positive normal double. -/
def IsPosNormal (u : ℕ) : Prop :=
  u < 2 ^ 64 ∧ fpSign u = 0 ∧ 1 ≤ fpExp u ∧ fpExp u ≤ 2046

/-! ### The C transform -/

/-- `x.u = (x.u & 0x800fffffffffffff) | (1022 << 52)`. -/
def frexpBits (u : ℕ) : ℕ := (u &&& 0x800fffffffffffff) ||| (1022 <<< 52)

/-- `*e = ((x.u >> 52) & 0x7ff) - 1022`. -/
def frexpExp (u : ℕ) : ℤ := ((u >>> 52) &&& 0x7ff : ℕ) - 1022

private theorem and_split {k a b c d : ℕ} (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * a + b) &&& (2 ^ k * c + d) = 2 ^ k * (a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hd)]
  split_ifs <;> simp [Nat.testBit_and]

private theorem or_split {k a b c d : ℕ} (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * a + b) ||| (2 ^ k * c + d) = 2 ^ k * (a ||| c) + (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.or_lt_two_pow hb hd)]
  split_ifs <;> simp [Nat.testBit_or]

/-- The C exponent expression is the biased exponent minus 1022. -/
theorem frexpExp_eq (u : ℕ) : frexpExp u = (fpExp u : ℤ) - 1022 := by
  have h : (u >>> 52) &&& 0x7ff = fpExp u := by
    rw [Nat.shiftRight_eq_div_pow, show (0x7ff : ℕ) = 2 ^ 11 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
    rfl
  simp [frexpExp, h]

/-- The bitwise transform keeps sign and fraction and sets the biased exponent to 1022. -/
theorem frexpBits_eq {u : ℕ} (hu : u < 2 ^ 64) :
    frexpBits u = fpSign u * 2 ^ 63 + 1022 * 2 ^ 52 + fpFrac u := by
  unfold frexpBits fpSign fpFrac
  have hq : u / 2 ^ 52 < 2 ^ 12 := by omega
  have hs : u / 2 ^ 63 ≤ 1 := by omega
  have hu' : u = 2 ^ 52 * (2 ^ 11 * (u / 2 ^ 63) + fpExp u) + u % 2 ^ 52 := by
    unfold fpExp; omega
  have hmask : (0x800fffffffffffff : ℕ) = 2 ^ 52 * (2 ^ 11 * 1 + 0) + (2 ^ 52 - 1) := by
    norm_num
  have hE : fpExp u < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hs1 : (u / 2 ^ 63) &&& 1 = u / 2 ^ 63 := by
    rw [show (1 : ℕ) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  have hor : 2 ^ 11 * (u / 2 ^ 63) ||| 1022 = 2 ^ 11 * (u / 2 ^ 63) + 1022 :=
    (Nat.two_pow_add_eq_or_of_lt (by norm_num) _).symm
  have hsh : (1022 <<< 52 : ℕ) = 2 ^ 52 * 1022 + 0 := by norm_num [Nat.shiftLeft_eq]
  rw [hmask, hsh]
  conv_lhs => rw [hu']
  rw [and_split (Nat.mod_lt _ (by norm_num)) (by norm_num), and_split hE (by norm_num),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.and_zero, hs1, add_zero,
    or_split (Nat.mod_lt _ (by norm_num)) (by norm_num), Nat.or_zero, hor]
  ring

/-- `frexpBits u` is again a positive normal pattern, with biased exponent 1022. -/
theorem frexpBits_isPosNormal {u : ℕ} (hu : IsPosNormal u) :
    IsPosNormal (frexpBits u) ∧ fpExp (frexpBits u) = 1022 ∧
      fpFrac (frexpBits u) = fpFrac u := by
  obtain ⟨hlt, hs, -, -⟩ := hu
  rw [frexpBits_eq hlt, hs]
  unfold IsPosNormal fpSign fpExp fpFrac
  norm_num
  omega

/-- The C split is exact: `decode u' ∈ [1/2, 1)` and `decode u = decode u' * 2^e`. -/
theorem frexpBits_split {u : ℕ} (hu : IsPosNormal u) :
    1 / 2 ≤ decode (frexpBits u) ∧ decode (frexpBits u) < 1 ∧
      decode u = decode (frexpBits u) * (2 : ℝ) ^ frexpExp u := by
  obtain ⟨⟨-, hs', -, -⟩, hE', hf'⟩ := frexpBits_isPosNormal hu
  have hs := hu.2.1
  have hf : (fpFrac u : ℝ) < 2 ^ 52 := by
    have : fpFrac u < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
    exact_mod_cast this
  have hf0 : (0 : ℝ) ≤ fpFrac u := Nat.cast_nonneg _
  have hm : decode (frexpBits u) = (1 + (fpFrac u : ℝ) / 2 ^ 52) / 2 := by
    rw [decode, hs', hE', hf']
    norm_num
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hm]
    have : 0 ≤ (fpFrac u : ℝ) / 2 ^ 52 := by positivity
    linarith
  · rw [hm]
    have : (fpFrac u : ℝ) / 2 ^ 52 < 1 := by rw [div_lt_one (by positivity)]; exact hf
    linarith
  · rw [hm, frexpExp_eq, decode, hs,
      show (fpExp u : ℤ) - 1023 = -1 + ((fpExp u : ℤ) - 1022) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
    ring

/-- The `hsplit` hypothesis of `logdetKernel_eq_sum_log`, on every positive normal double:
`(decode u', e)` is a positive mantissa with `decode u = decode u' * 2^e`. -/
theorem frexpBits_hsplit {u : ℕ} (hu : IsPosNormal u) :
    0 < decode (frexpBits u) ∧ decode u = decode (frexpBits u) * (2 : ℝ) ^ frexpExp u := by
  obtain ⟨h1, -, h3⟩ := frexpBits_split hu
  exact ⟨by linarith, h3⟩

/-! ### Validation against Lean's `Float` (evaluation, not proof)

For each sample, `frexpBits` and `frexpExp` run on `Float.toBits`; the columns are
`(hex bits of x, mantissa, e, mantissa bits = frExp bits, e = frExp exponent,
  mantissa * 2^e = x)`. -/

#eval [1.0, 0.75, 3.0, 1e-300, 1e300, 1.0 + 1e-16, 1.0000000000000002, 12345.678,
    2.2250738585072014e-308, 1.7976931348623157e308].map fun (x : Float) =>
  let u := x.toBits.toNat
  let m := Float.ofBits (UInt64.ofNat (frexpBits u))
  let e := frexpExp u
  (String.ofList (Nat.toDigits 16 u), m, e,
    m.toBits == x.frExp.1.toBits, e == x.frExp.2, m.scaleB e == x)

end JammaLean
