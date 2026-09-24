import JammaLean.Stats
import JammaLean.Profile

/-!
# The exact likelihood-ratio statistic is non-negative

`_mle_logl` (`src/jamma/lmm/likelihood_numpy.py`) evaluates the MLE
log-likelihood at `λ` as

    logl(λ) = _logl_const(n) - ½ logdet_h(λ) - ½ n log P_yy(λ),

where `P_yy` is the last `Pab` level: `Pab[c, yy]` (`pYY`) for the null model H0
with covariates only, and `Pab[c+1, yy]` (`pxYY`) for the alternative H1 that
also projects out the genotype. The LRT statistic is
`2 (logl_H1(λ₁) - logl_H0(λ₀))` with each model at its own optimal `λ`, and
`batch_lrt_pvalues_numpy` (`src/jamma/lmm/stats.py`) clamps it at 0.

Proved here:

* `mleLogL_H0_le_H1`: at any fixed `λ`, `logl_H1(λ) ≥ logl_H0(λ)`, because
  `Px_YY = P_YY - P_XY² / P_XX ≤ P_YY` and `log` is monotone.
* `lrt_nonneg`: for any `f0 ≤ f1` on a set `S`, the maximum of `f1` over `S`
  is at least the value of `f0` at any point of `S`, so the statistic is `≥ 0`.
* `lrt_stat_nonneg`: the two combined for the `Pab` families; the clamp at 0 in
  `batch_lrt_pvalues_numpy` only absorbs optimiser error.
-/

namespace JammaLean

open Real

/-- `_mle_logl`: `_logl_const(n) - ½ logdet_h - ½ n log P_yy`. -/
noncomputable def mleLogL (n logdetH Pyy : ℝ) : ℝ :=
  profiledLogL n Pyy - logdetH / 2

theorem mleLogL_eq (n logdetH Pyy : ℝ) :
    mleLogL n logdetH Pyy = loglConst n - logdetH / 2 - n / 2 * log Pyy := by
  unfold mleLogL profiledLogL
  ring

/-- With a shared `logdet_h`, a smaller positive `P_yy` gives a larger likelihood. -/
theorem mleLogL_anti {n : ℝ} (hn : 0 ≤ n) (logdetH : ℝ) {P Q : ℝ} (hP : 0 < P)
    (hPQ : P ≤ Q) : mleLogL n logdetH Q ≤ mleLogL n logdetH P := by
  have := Real.log_le_log hP hPQ
  rw [mleLogL_eq, mleLogL_eq]
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Px_YY ≤ P_YY`: projecting out the genotype never increases `P_yy`. -/
theorem pxYY_le_pYY (w : ℕ → E) (c : ℕ) (y : E) : pxYY w c y ≤ pYY w c y := by
  rw [px_yy_eq]
  have := div_nonneg (sq_nonneg (pXY w c y)) (pXX_nonneg w c)
  linarith

/-- At every fixed `λ`, `logl_H1(λ) ≥ logl_H0(λ)`. -/
theorem mleLogL_H0_le_H1 {n : ℝ} (hn : 0 ≤ n) (logdetH : ℝ) (w : ℕ → E) (c : ℕ) (y : E)
    (hpos : 0 < pxYY w c y) :
    mleLogL n logdetH (pYY w c y) ≤ mleLogL n logdetH (pxYY w c y) :=
  mleLogL_anti hn logdetH hpos (pxYY_le_pYY w c y)

/-- If `f0 ≤ f1` on `S`, `λ₀ ∈ S`, and `λ₁` maximises `f1` over `S`, then
`2 (f1 λ₁ - f0 λ₀) ≥ 0`. `λ₀` need not maximise `f0`, nor `λ₁` lie in `S`. -/
theorem lrt_nonneg {S : Set ℝ} {f0 f1 : ℝ → ℝ} (hle : ∀ l ∈ S, f0 l ≤ f1 l)
    {l₀ l₁ : ℝ} (h₀ : l₀ ∈ S) (hmax₁ : ∀ l ∈ S, f1 l ≤ f1 l₁) :
    0 ≤ 2 * (f1 l₁ - f0 l₀) := by
  have := hle l₀ h₀
  have := hmax₁ l₀ h₀
  linarith

/-- The exact LRT statistic of `_mle_logl` families is non-negative. At each `λ`
the rotated data live in their own inner product space, so the families are
indexed by `λ` in a type-valued way; the shared `logdet_h λ` is `ld λ`. -/
theorem lrt_stat_nonneg {F : ℝ → Type*} [∀ l, NormedAddCommGroup (F l)]
    [∀ l, InnerProductSpace ℝ (F l)] {n : ℝ} (hn : 0 ≤ n) (ld : ℝ → ℝ)
    (w : ∀ l, ℕ → F l) (c : ℕ) (y : ∀ l, F l) {S : Set ℝ}
    (hpos : ∀ l ∈ S, 0 < pxYY (w l) c (y l)) {l₀ l₁ : ℝ} (h₀ : l₀ ∈ S)
    (hmax₁ : ∀ l ∈ S, mleLogL n (ld l) (pxYY (w l) c (y l)) ≤
      mleLogL n (ld l₁) (pxYY (w l₁) c (y l₁))) :
    0 ≤ 2 * (mleLogL n (ld l₁) (pxYY (w l₁) c (y l₁)) -
      mleLogL n (ld l₀) (pYY (w l₀) c (y l₀))) :=
  lrt_nonneg (f0 := fun l => mleLogL n (ld l) (pYY (w l) c (y l)))
    (f1 := fun l => mleLogL n (ld l) (pxYY (w l) c (y l)))
    (fun l hl => mleLogL_H0_le_H1 hn (ld l) (w l) c (y l) (hpos l hl)) h₀ hmax₁

end JammaLean
