# jamma-lean

Machine-checked proofs, in Lean 4 with Mathlib, of the mathematical claims in
[JAMMA](https://github.com/michael-denyer/jamma)'s documentation. JAMMA already
demonstrates these claims empirically against GEMMA and a dense oracle on many
datasets. The proofs add a second, independent line of evidence: the formulas
are correct for every input, not only the ones tested.

Most theorems are stated over ℝ (exact arithmetic). `FpSum` and `FpSumTree`
prove floating-point error bounds in the standard rounding model, and
`FrexpBits` works at the level of IEEE-754 bit patterns.

## Quick start

```bash
lake exe cache get
lake build
scripts/check-axioms.sh
```

`scripts/check-axioms.sh` runs `Audit.lean` and fails unless every audited
theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). An unfinished proof would show `sorryAx`. CI runs the same gate
on every push.

## Claims and the evidence behind them

The claim column cites JAMMA's docs. "Test" names the case in JAMMA's
`tests/test_lean_proven_identities.py` that checks the real code against the
theorem numerically; each of those tests was confirmed to fail under a planted
mutation of the production formula.

| JAMMA claim | Lean theorem | Test |
|---|---|---|
| **GEMMA_EQUIVALENCE §2** `K = (1/p) Xc Xcᵀ` is PSD; centred columns put `1` in its kernel | `Kinship.kinship_posSemidef`, `kinship_mulVec_one`, `eigen_nonneg`, `hpos_of_kinship` | `test_centered_kinship_is_psd_with_zero_row_sums` |
| **§2 / Summary** kinship error `O(p·ε)`, in any BLAS summation order | `FpSumTree.fkin_err_le_fpGamma`, `fkin_err_float64` (≤ 1.111e-10·(1/p)Σ\|xᵢyᵢ\| for p ≤ 10⁶) | |
| **§3** results do not depend on the eigenvector signs | `Rotation.pab_row0_eq_dense` (row 0 is `aᵀH⁻¹b` for any orthogonal eigenbasis) | |
| **§4** `log\|H\| = Σ log(λ dᵢ + 1)` | `Rotation.logdet_hMat`, `det_hMat` | `test_numpy_logdet_h_equals_slogdet` |
| **§4** the C mantissa-product logdet equals the log sum | `Logdet.logdetKernel_eq_sum_log`, with the bit split proved in `FrexpBits.frexpBits_hsplit` | `test_native_likelihoods_match_dense_logdet_and_projector` |
| **§4** Pab recursion; `get_ab_index` transcribes `GetabIndex` | `Pab.pab_succ`, `AbIndex.abIndex_image`, `abIndex_comm` | `test_ab_index_is_a_symmetric_bijection_onto_n_index` |
| **§4 / NUMERICAL_EQUIVALENCE_BOUND** Pab is `aᵀPb` with `P = H⁻¹ − H⁻¹W(WᵀH⁻¹W)⁻¹WᵀH⁻¹` | `ClosedForm.pab_rotated_eq_closedForm`, `Reml.pab_eq_projP` | `test_calc_pab_equals_dense_projector_at_every_level` |
| **§4** Pab row-0 error `O(n·ε)`, any summation order | `FpSumTree.fwdot_err_le_fpGamma`, `fwdot_err_float64` (≤ 2.221e-11·Σ\|hᵢaᵢbᵢ\| for n ≤ 2·10⁵) | |
| **§4** REML log-likelihood | `Reml.remlLogL_eq_contrast`, `contrastLogL_at_argmax`, `remlLogLPab_eq_contrast` (JAMMA's formula is the profiled likelihood of the error contrasts `Aᵀy`) | |
| **§4** the `logdet_hiw` term is `log\|WᵀH⁻¹W\| − log\|WᵀW\|` | `GramDet.logdet_hiw_eq`, `prod_pab_diag_eq_det_gram`, `Reml.det_contrast` | |
| **MATHEMATICAL_VALIDATION** REML invariant to centring K (MLE is not) | `Reml.remlLogL_centering_invariant` | `test_reml_is_invariant_to_centring_kinship_and_mle_is_not` |
| **`_logl_const`** is the Gaussian likelihood maximised over σ² | `Profile.gaussLogL_le_profiled`, `gaussLogL_at_argmax`, `gaussLogL_argmax_unique` | `test_profiled_logl_is_the_gaussian_maximum_over_sigma2` |
| **§5** grid then golden section brackets the optimum | `Optimizer.grid_bracket_mem`, `gs_iterate_inv`, `gs_iterate_width`, `golden_error_code` (≤ 3.12e-5 in log λ after 20 steps) | |
| **§5** safeguarded Newton refinement | `Optimizer.newtonLoop_mem`, `lambdaSearch_error`, `newtonLoop_affine`; limit shown by `refine_can_leave_golden_bracket` | |
| **§6** Wald: `Px_yy = P_yy − P_xy²/P_xx`, `F = β²/SE²` | `Stats.px_yy_eq`, `waldF_eq_beta_sq_div_var`, `waldF_eq_r2`, `waldF_nonneg` | `test_wald_statistics_satisfy_the_r2_identities` |
| **§6** p-value complement `f/(df+f) = 1 − df/(df+f)` | `Stats.complement_z` | |
| **§7** Score `F = n P_xy²/(P_yy P_xx)` | `Stats.scoreF_eq_r2`, `scoreF_le_n` | `test_score_f_is_n_r2_and_at_most_n`, `test_native_score_f_is_n_r2` |
| **§8** the exact LRT statistic is non-negative | `Lrt.lrt_stat_nonneg`, `mleLogL_H0_le_H1` | `test_mle_with_genotype_never_below_null_at_shared_lambda` |

## Findings

The proofs back the documented claims, with these qualifications:

* **§4 formula.** `GEMMA_EQUIVALENCE.md` §4 writes the REML term as
  `−½ log|WᵀH⁻¹W|`. JAMMA computes `−½ (log|WᵀH⁻¹W| − log|WᵀW|)`, which is the
  form proved equal to the error-contrast likelihood (`Reml.remlLogL_eq_contrast`).
* **Newton refinement.** The accept rule keeps the result inside the coarse
  grid bracket (`newtonLoop_mem`), but not inside the final golden-section
  bracket: `refine_can_leave_golden_bracket` is a concave objective with a
  piecewise-linear score where one accepted step moves the result from 0.005
  to 0.495 from the peak. The guaranteed worst case after refinement is
  therefore the grid spacing (2h ≈ 0.94 in log λ), not φ²⁰·h. Smooth,
  near-quadratic peaks converge (`newtonLoop_affine`), and JAMMA's committed
  reference roots check real data.
* **§5 wording.** The docs say one Newton step; the code takes up to three.
  The golden-section bound for 20 steps (3.1e-5 in log λ) is above the
  `lambda_rtol` of 2e-5, so interior accuracy at that tolerance comes from the
  refinement, not from golden section alone.
* **NUMERICAL_EQUIVALENCE_BOUND §3** states `|λ̂ − λ*| ≤ τ_opt` in λ; the
  optimizer works in log λ, so the bound is relative: `e^τ − 1`.

## Not proved

* The F and χ² distribution functions (`betainc`, `chi2_sf`). Mathlib has no
  regularised incomplete beta function.
* Floating-point error beyond single sums and dot products: the Pab recursion's
  divisions, the eigendecomposition (backward stability of LAPACK) and the
  optimizer under rounding.
* Uniqueness of the REML optimum. `NUMERICAL_EQUIVALENCE_BOUND` assumes
  concavity in log λ; that is an assumption, not a theorem.

## Layout

Each file in `JammaLean/` opens with a module docstring naming the JAMMA
function it models. `Audit.lean` lists the audited theorems.
