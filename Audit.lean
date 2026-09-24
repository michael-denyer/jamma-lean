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
#print axioms JammaLean.contrast_inv_eq_projP
#print axioms JammaLean.contrast_quad_eq_pyy
#print axioms JammaLean.contrast_complete
#print axioms JammaLean.det_contrast
#print axioms JammaLean.remlLogL_eq_contrast
#print axioms JammaLean.contrastLogL_le_remlLogL
#print axioms JammaLean.contrastLogL_at_argmax
#print axioms JammaLean.contrast_centered_kinship
#print axioms JammaLean.contrastLogL_centered
#print axioms JammaLean.remlLogL_centered
#print axioms JammaLean.remlLogL_eq_contrast_df
#print axioms JammaLean.exists_contrast_basis
#print axioms JammaLean.remlLogL_centering_invariant
#print axioms JammaLean.pab_eq_schur
#print axioms JammaLean.det_gram_eq_prod
#print axioms JammaLean.pab_eq_projP
#print axioms JammaLean.remlLogLPab_eq
#print axioms JammaLean.remlLogLPab_eq_contrast

-- `abIndex` is computable: the packed slots for n_cvt = 1 (cols = 3), in the
-- order `build_index_table` walks them.
#eval (List.range 3).flatMap fun k => (List.range' k (3 - k)).map fun j =>
  (k + 1, j + 1, JammaLean.abIndex 3 (k + 1) (j + 1))
