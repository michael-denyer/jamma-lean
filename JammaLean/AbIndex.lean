import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# GEMMA's `GetabIndex` packing

`get_ab_index` (`src/jamma/lmm/pab.py`) stores the symmetric `(a, b)` table of
`Uab`/`Pab` in one row of length `n_index = (n_cvt + 3)(n_cvt + 2)/2`, with
1-based `a, b ≤ cols = n_cvt + 2`:

    a1, b1 = (a, b) if a <= b else (b, a)
    index = (2 * cols - a1 + 2) * (a1 - 1) // 2 + b1 - a1

`abIndex_image` proves that this maps the `cols(cols+1)/2` unordered pairs onto
`0, …, cols(cols+1)/2 - 1` bijectively: no two pairs share a slot and no slot
is left unused. `abIndex_comm` is the swap. Pairs are enumerated 0-based as
`(k, j)` with `k ≤ j < cols`, that is `a1 = k + 1`, `b1 = j + 1`.
-/

namespace JammaLean

/-- `get_ab_index` with `cols = n_cvt + 2`, verbatim. -/
def abIndex (cols a b : ℕ) : ℕ :=
  let a1 := min a b
  let b1 := max a b
  (2 * cols - a1 + 2) * (a1 - 1) / 2 + b1 - a1

theorem abIndex_comm (cols a b : ℕ) : abIndex cols a b = abIndex cols b a := by
  simp [abIndex, min_comm, max_comm]

/-- The number of slots before row `k`: rows `0, …, k-1` hold `cols - i` entries. -/
def rowStart (cols k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (cols - i)

theorem rowStart_succ (cols k : ℕ) : rowStart cols (k + 1) = rowStart cols k + (cols - k) :=
  Finset.sum_range_succ _ _

theorem rowStart_mono (cols : ℕ) {k k' : ℕ} (h : k ≤ k') : rowStart cols k ≤ rowStart cols k' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- The closed form in `get_ab_index` is `rowStart`. -/
theorem closed_form_eq_rowStart (cols k : ℕ) (hk : k ≤ cols) :
    (2 * cols + 1 - k) * k / 2 = rowStart cols k := by
  induction k with
  | zero => simp [rowStart]
  | succ k ih =>
    rw [rowStart_succ, ← ih (by omega)]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_succ_le hk)
    have e1 : 2 * (k + d + 1) + 1 - (k + 1) = k + 2 * d + 2 := by omega
    have e2 : 2 * (k + d + 1) + 1 - k = k + 2 * d + 3 := by omega
    have e3 : k + d + 1 - k = d + 1 := by omega
    rw [e1, e2, e3]
    have : (k + 2 * d + 2) * (k + 1) = (k + 2 * d + 3) * k + (d + 1) * 2 := by ring
    rw [this, Nat.add_mul_div_right _ _ (by norm_num)]

/-- The 1-based code formula at `a1 = k + 1 ≤ b1 = j + 1` is `rowStart k + (j - k)`. -/
theorem abIndex_eq (cols k j : ℕ) (hkj : k ≤ j) (hj : j < cols) :
    abIndex cols (k + 1) (j + 1) = rowStart cols k + (j - k) := by
  have hmin : min (k + 1) (j + 1) = k + 1 := min_eq_left (by omega)
  have hmax : max (k + 1) (j + 1) = j + 1 := max_eq_right (by omega)
  simp only [abIndex, hmin, hmax]
  have h1 : 2 * cols - (k + 1) + 2 = 2 * cols + 1 - k := by omega
  rw [h1, Nat.add_sub_cancel, closed_form_eq_rowStart cols k (by omega)]
  omega

/-- The 0-based pairs `(k, j)` with `k ≤ j < cols`. -/
def pairs (cols : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.range cols).sigma fun k => Finset.Ico k cols

theorem mem_pairs {cols : ℕ} {p : Σ _ : ℕ, ℕ} : p ∈ pairs cols ↔ p.1 ≤ p.2 ∧ p.2 < cols := by
  simp only [pairs, Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
  omega

theorem card_pairs (cols : ℕ) : (pairs cols).card = rowStart cols cols := by
  simp [pairs, rowStart, Finset.card_sigma]

/-- The packed index as the code evaluates it on a 0-based pair. -/
def slot (cols : ℕ) (p : Σ _ : ℕ, ℕ) : ℕ := abIndex cols (p.1 + 1) (p.2 + 1)

theorem slot_lt {cols : ℕ} {p : Σ _ : ℕ, ℕ} (hp : p ∈ pairs cols) :
    slot cols p < rowStart cols cols := by
  obtain ⟨hkj, hj⟩ := mem_pairs.mp hp
  rw [slot, abIndex_eq cols _ _ hkj hj]
  have := rowStart_mono cols (show p.1 + 1 ≤ cols by omega)
  rw [rowStart_succ] at this
  omega

theorem slot_injOn (cols : ℕ) : Set.InjOn (slot cols) (pairs cols) := by
  intro p hp q hq heq
  obtain ⟨hkj, hj⟩ := mem_pairs.mp hp
  obtain ⟨hkj', hj'⟩ := mem_pairs.mp hq
  simp only [slot, abIndex_eq cols _ _ hkj hj, abIndex_eq cols _ _ hkj' hj'] at heq
  -- Rows are contiguous blocks, so equal slots force equal rows, then equal columns.
  have row_lt : ∀ {k k' j : ℕ}, k < k' → k < cols → j < cols →
      rowStart cols k + (j - k) < rowStart cols k' := by
    intro k k' j hk hkc hj
    have hmono := rowStart_mono cols (show k + 1 ≤ k' by omega)
    rw [rowStart_succ] at hmono
    have hjk : j - k < cols - k := by omega
    omega
  have hk : p.1 = q.1 := by
    rcases Nat.lt_trichotomy p.1 q.1 with h | h | h
    · have := row_lt (j := p.2) h (by omega) hj; omega
    · exact h
    · have := row_lt (j := q.2) h (by omega) hj'; omega
  have hj2 : p.2 = q.2 := by rw [hk] at heq; omega
  cases p; cases q
  simp only at hk hj2
  subst hk hj2
  rfl

/-- `get_ab_index` is a bijection from the unordered pairs onto
`range (cols (cols+1)/2)`: every `Pab` slot is used exactly once. -/
theorem abIndex_image (cols : ℕ) :
    (pairs cols).image (slot cols) = Finset.range (cols * (cols + 1) / 2) := by
  have hclosed : cols * (cols + 1) / 2 = rowStart cols cols := by
    rw [← closed_form_eq_rowStart cols cols le_rfl]
    congr 1
    rw [show 2 * cols + 1 - cols = cols + 1 by omega, mul_comm]
  rw [hclosed]
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_range.mpr (slot_lt hp)
  · rw [Finset.card_range, Finset.card_image_of_injOn (slot_injOn cols), card_pairs]

/-- `n_index(n_cvt) = (n_cvt + 3)(n_cvt + 2)/2` (`core/constants.py`) is the slot count. -/
theorem n_index_eq (n_cvt : ℕ) :
    (n_cvt + 3) * (n_cvt + 2) / 2 = (n_cvt + 2) * (n_cvt + 2 + 1) / 2 := by
  ring_nf

end JammaLean
