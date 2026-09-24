import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-!
# CalcPab is sequential orthogonal projection

`calc_pab` (`src/jamma/lmm/pab.py`) fills level `p` from level `p - 1` with

    Pab[p, ab] = Pab[p-1, ab] - Pab[p-1, aw] * Pab[p-1, bw] / Pab[p-1, ww]

and keeps `Pab[p-1, ab]` when `Pab[p-1, ww] = 0`. Row 0 is the `H⁻¹`-weighted
inner product of the rotated vectors.

This file works in an arbitrary real inner product space `E`; `Rotation.lean`
instantiates `E` with the `H⁻¹`-weighted space. It proves:

* `pab_succ`: the recursion above holds for inner products of residuals, where
  level `p` has the covariates `w 0, …, w (p-1)` projected out.
* `resid_mem_orthogonal`, `sub_resid_mem_span`: the level-`p` residual is the
  component of `a` orthogonal to `span {w 0, …, w (p-1)}`, so `Pab[p, ab]` is
  `aᵀ P_p b` with `P_p` the projection GEMMA's documentation names.
* `pab_eq_inner_resid_left`: `Pab[p, ab] = ⟪resid a, b⟫`, the one-sided form.

Lean defines `x / 0 = 0`, so `projOut 0 a = a`. That is exactly the
`ps_ww == 0` branch of `calc_pab`, and the theorems cover it with no extra case.
-/

namespace JammaLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Remove the component of `a` along `w`. -/
noncomputable def projOut (w a : E) : E :=
  a - (⟪a, w⟫ / ⟪w, w⟫) • w

/-- The inner product of two `projOut` residuals is the one-step CalcPab update. -/
theorem inner_projOut_projOut (w a b : E) :
    ⟪projOut w a, projOut w b⟫ = ⟪a, b⟫ - ⟪a, w⟫ * ⟪b, w⟫ / ⟪w, w⟫ := by
  by_cases hw : ⟪w, w⟫ = 0
  · have : w = 0 := inner_self_eq_zero.mp hw
    subst this
    simp [projOut]
  · simp only [projOut, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real]
    rw [real_inner_comm w a, real_inner_comm w b]
    field_simp
    ring

/-- The residual is orthogonal to the removed direction. -/
theorem inner_projOut_self (w a : E) : ⟪projOut w a, w⟫ = 0 := by
  by_cases hw : ⟪w, w⟫ = 0
  · have : w = 0 := inner_self_eq_zero.mp hw
    subst this
    simp
  · simp only [projOut, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
    field_simp
    ring

/-- The level-`p` residual of `a`: covariates `w 0, …, w (p-1)` projected out in
order, as CalcPab visits them. -/
noncomputable def resid (w : ℕ → E) : ℕ → E → E
  | 0, a => a
  | p + 1, a => projOut (resid w p (w p)) (resid w p a)

/-- `Pab[p, ab]` for the vectors `a` and `b`. -/
noncomputable def pab (w : ℕ → E) (p : ℕ) (a b : E) : ℝ :=
  ⟪resid w p a, resid w p b⟫

/-- Row 0 of `Pab` is the plain inner product. -/
@[simp] theorem pab_zero (w : ℕ → E) (a b : E) : pab w 0 a b = ⟪a, b⟫ := rfl

/-- The CalcPab recursion, `pab.py` `calc_pab`, including its `ps_ww == 0` branch. -/
theorem pab_succ (w : ℕ → E) (p : ℕ) (a b : E) :
    pab w (p + 1) a b =
      pab w p a b - pab w p a (w p) * pab w p b (w p) / pab w p (w p) (w p) := by
  simp only [pab, resid]
  exact inner_projOut_projOut _ _ _

/-- `Pab` is symmetric, which is what lets CalcPab store only `a ≤ b`. -/
theorem pab_comm (w : ℕ → E) (p : ℕ) (a b : E) : pab w p a b = pab w p b a :=
  real_inner_comm _ _

/-- The span of the first `p` covariates. -/
noncomputable def covSpan (w : ℕ → E) (p : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (w '' {i | i < p})

theorem covSpan_mono (w : ℕ → E) {p q : ℕ} (h : p ≤ q) : covSpan w p ≤ covSpan w q :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

theorem w_mem_covSpan (w : ℕ → E) {i p : ℕ} (h : i < p) : w i ∈ covSpan w p :=
  Submodule.subset_span ⟨i, h, rfl⟩

/-- A vector is orthogonal to `covSpan w p` as soon as it is orthogonal to each
of its generators. -/
theorem mem_orthogonal_covSpan (w : ℕ → E) (p : ℕ) (x : E)
    (h : ∀ i < p, ⟪w i, x⟫ = 0) : x ∈ (covSpan w p)ᗮ := by
  rw [covSpan, Submodule.mem_orthogonal]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, hi, rfl⟩ := hv
    exact h i hi
  | zero => simp
  | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
  | smul c v _ hv => rw [inner_smul_left, hv, mul_zero]

/-- Both characterising properties of the level-`p` residual, proved together by
induction on `p`. -/
theorem resid_spec (w : ℕ → E) (p : ℕ) (a : E) :
    resid w p a ∈ (covSpan w p)ᗮ ∧ a - resid w p a ∈ covSpan w p := by
  induction p generalizing a with
  | zero =>
    refine ⟨?_, by simp [resid]⟩
    apply mem_orthogonal_covSpan
    intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  | succ p ih =>
    set r := resid w p a
    set u := resid w p (w p)
    obtain ⟨hr_perp, hr_span⟩ := ih a
    obtain ⟨hu_perp, hu_span⟩ := ih (w p)
    have hle : covSpan w p ≤ covSpan w (p + 1) := covSpan_mono w (Nat.le_succ p)
    have hwp : w p ∈ covSpan w (p + 1) := w_mem_covSpan w (Nat.lt_succ_self p)
    have hu_mem : u ∈ covSpan w (p + 1) := by
      have : u = w p - (w p - u) := by abel
      rw [this]
      exact Submodule.sub_mem _ hwp (hle hu_span)
    have hres : resid w (p + 1) a = projOut u r := rfl
    refine ⟨?_, ?_⟩
    · apply mem_orthogonal_covSpan
      intro i hi
      rw [hres, real_inner_comm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · -- Earlier covariates: `r` and `u` are both already orthogonal to them.
        have hr0 : ⟪r, w i⟫ = 0 :=
          (Submodule.mem_orthogonal' _ _).mp hr_perp _ (w_mem_covSpan w hi)
        have hu0 : ⟪u, w i⟫ = 0 :=
          (Submodule.mem_orthogonal' _ _).mp hu_perp _ (w_mem_covSpan w hi)
        simp [projOut, inner_sub_left, inner_smul_left, hr0, hu0]
      · -- The new covariate: split `w p = u + (w p - u)`.
        have hsplit : w i = u + (w i - u) := by abel
        have hperp : ⟪projOut u r, w i - u⟫ = 0 := by
          have hr0 : ⟪r, w i - u⟫ = 0 :=
            (Submodule.mem_orthogonal' _ _).mp hr_perp _ hu_span
          have hu0 : ⟪u, w i - u⟫ = 0 :=
            (Submodule.mem_orthogonal' _ _).mp hu_perp _ hu_span
          simp [projOut, inner_sub_left, inner_smul_left, hr0, hu0]
        rw [hsplit, inner_add_right, inner_projOut_self, hperp, add_zero]
    · rw [hres]
      have : a - projOut u r = (a - r) + (⟪r, u⟫ / ⟪u, u⟫) • u := by
        simp only [projOut]
        abel
      rw [this]
      exact Submodule.add_mem _ (hle hr_span) (Submodule.smul_mem _ _ hu_mem)

theorem resid_mem_orthogonal (w : ℕ → E) (p : ℕ) (a : E) :
    resid w p a ∈ (covSpan w p)ᗮ :=
  (resid_spec w p a).1

theorem sub_resid_mem_span (w : ℕ → E) (p : ℕ) (a : E) :
    a - resid w p a ∈ covSpan w p :=
  (resid_spec w p a).2

/-- `Pab[p, ab] = ⟪P_p a, b⟫`: one residual suffices, since `P_p` is idempotent
and self-adjoint. -/
theorem pab_eq_inner_resid_left (w : ℕ → E) (p : ℕ) (a b : E) :
    pab w p a b = ⟪resid w p a, b⟫ := by
  have hperp : ⟪resid w p a, b - resid w p b⟫ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (resid_mem_orthogonal w p a) _
      (sub_resid_mem_span w p b)
  unfold pab
  have : b = resid w p b + (b - resid w p b) := by abel
  conv_rhs => rw [this]
  rw [inner_add_right, hperp, add_zero]

/-- The residual depends only on the covariate span: any `x` with the two
characterising properties equals it. This pins `resid` to the orthogonal
projection onto `(covSpan w p)ᗮ`, independent of covariate order. -/
theorem resid_unique (w : ℕ → E) (p : ℕ) (a x : E)
    (hx_perp : x ∈ (covSpan w p)ᗮ) (hx_span : a - x ∈ covSpan w p) :
    x = resid w p a := by
  have hd_span : resid w p a - x ∈ covSpan w p := by
    have : resid w p a - x = (a - x) - (a - resid w p a) := by abel
    rw [this]
    exact Submodule.sub_mem _ hx_span (sub_resid_mem_span w p a)
  have hd_perp : resid w p a - x ∈ (covSpan w p)ᗮ :=
    Submodule.sub_mem _ (resid_mem_orthogonal w p a) hx_perp
  have h0 : resid w p a - x = 0 :=
    (Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint _)) _ hd_span hd_perp
  exact (sub_eq_zero.mp h0).symm

/-- The projected quadratic form is non-negative: `Pab[p, aa] ≥ 0`. JAMMA's
`guard_p_yy` reads a negative `P_yy` as numerical breakdown for this reason. -/
theorem pab_self_nonneg (w : ℕ → E) (p : ℕ) (a : E) : 0 ≤ pab w p a a :=
  real_inner_self_nonneg

end JammaLean
