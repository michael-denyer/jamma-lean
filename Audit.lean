import JammaLean

/-! Prints the axioms each headline theorem depends on. Every line must list only
`propext`, `Classical.choice` and `Quot.sound`; `sorryAx` means an unfinished proof. -/

#print axioms JammaLean.abIndex_image
#print axioms JammaLean.abIndex_comm
#print axioms JammaLean.pab_succ
#print axioms JammaLean.resid_spec
#print axioms JammaLean.resid_unique
#print axioms JammaLean.pab_eq_inner_resid_left
#print axioms JammaLean.hMat_inv
#print axioms JammaLean.quad_form_rotated
#print axioms JammaLean.logdet_hMat
#print axioms JammaLean.pab_row0_eq_dense
#print axioms JammaLean.px_yy_eq
#print axioms JammaLean.waldF_eq_beta_sq_div_var
#print axioms JammaLean.waldF_eq_r2
#print axioms JammaLean.scoreF_eq_r2
#print axioms JammaLean.scoreF_le_n
#print axioms JammaLean.waldF_nonneg
#print axioms JammaLean.complement_z
#print axioms JammaLean.gaussLogL_le_profiled
#print axioms JammaLean.gaussLogL_at_argmax
#print axioms JammaLean.gaussLogL_argmax_unique
#print axioms JammaLean.logdetKernel_eq_sum_log
#print axioms JammaLean.kinship_posSemidef
#print axioms JammaLean.eigen_nonneg
#print axioms JammaLean.hpos_of_kinship
#print axioms JammaLean.logdet_hMat_kinship
#print axioms JammaLean.pab_row0_eq_dense_kinship
#print axioms JammaLean.kinship_mulVec_one
#print axioms JammaLean.mleLogL_H0_le_H1
#print axioms JammaLean.lrt_nonneg
#print axioms JammaLean.lrt_stat_nonneg
#print axioms JammaLean.frexpExp_eq
#print axioms JammaLean.frexpBits_eq
#print axioms JammaLean.frexpBits_isPosNormal
#print axioms JammaLean.frexpBits_split
#print axioms JammaLean.frexpBits_hsplit
#print axioms JammaLean.prod_pab_diag_eq_det_gram
#print axioms JammaLean.sum_log_pab_diag_eq_log_det_gram
#print axioms JammaLean.gram_weighted_rot_eq
#print axioms JammaLean.gram_rot_eq
#print axioms JammaLean.logdet_hiw_eq
#print axioms JammaLean.resid_eq_closedForm
#print axioms JammaLean.pab_eq_closedForm
#print axioms JammaLean.covGram_isUnit_det
#print axioms JammaLean.pab_eq_matrix_closedForm
#print axioms JammaLean.pab_rotated_eq_closedForm

-- `abIndex` is computable: the packed slots for n_cvt = 1 (cols = 3), in the
-- order `build_index_table` walks them.
#eval (List.range 3).flatMap fun k => (List.range' k (3 - k)).map fun j =>
  (k + 1, j + 1, JammaLean.abIndex 3 (k + 1) (j + 1))
#print axioms JammaLean.pow_sub_one_le_fpGamma
#print axioms JammaLean.fpGamma_mono
#print axioms JammaLean.abs_prod_sub_one_le_fpGamma
#print axioms JammaLean.fsum_err_le_fpGamma
#print axioms JammaLean.fdot_err_le_fpGamma
#print axioms JammaLean.fkin_err_le_fpGamma
#print axioms JammaLean.fwdot_err_le_fpGamma
#print axioms JammaLean.fwdot_err_le_fpGamma_of_nonneg
#print axioms JammaLean.fpGamma_float64_kinship
#print axioms JammaLean.fpGamma_float64_pab
#print axioms JammaLean.grid_bracket_mem
#print axioms JammaLean.gsStepC_eq
#print axioms JammaLean.gs_iterate_inv
#print axioms JammaLean.gs_iterate_width
#print axioms JammaLean.golden_error
#print axioms JammaLean.grid_golden_error
#print axioms JammaLean.golden_error_code
#print axioms JammaLean.probes_mem
#print axioms JammaLean.newtonLoop_mem
#print axioms JammaLean.lambdaSearch_error
#print axioms JammaLean.lambdaSearch_error_of_not_interior
#print axioms JammaLean.refine_error_code
#print axioms JammaLean.newton_step_toward_root
#print axioms JammaLean.accepted_closer_of_same_side
#print axioms JammaLean.newtonLoop_affine
#print axioms JammaLean.refine_can_leave_golden_bracket
#print axioms JammaLean.STree.err_le_pow
#print axioms JammaLean.STree.err_le_fpGamma
#print axioms JammaLean.STree.err_le_fpGamma_length
#print axioms JammaLean.STree.depth_lt_length
#print axioms JammaLean.STree.fdot_err_le_fpGamma
#print axioms JammaLean.STree.fkin_err_le_fpGamma
#print axioms JammaLean.STree.fwdot_err_le_fpGamma
#print axioms JammaLean.STree.fkin_err_float64
#print axioms JammaLean.STree.fwdot_err_float64
#print axioms JammaLean.STree.sum_abs_mul_le_norm
#print axioms JammaLean.STree.fdot_err_le_fpGamma_norm
#print axioms JammaLean.two_impl_le
