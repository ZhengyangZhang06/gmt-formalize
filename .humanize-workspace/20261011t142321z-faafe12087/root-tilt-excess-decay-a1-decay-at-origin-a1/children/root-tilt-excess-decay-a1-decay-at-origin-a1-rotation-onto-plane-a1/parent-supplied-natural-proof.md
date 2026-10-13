# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.rotation_onto_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Notation. Let E := Amb n l = EuclideanSpace R (Fin (n+l)); finrank E = n + l (finrank_euclideanSpace_fin). For k in Fin (n+l) let e_k := EuclideanSpace.single k 1, the standard orthonormal basis. By definition horizontalPlane n l = span{e_{Fin.castAdd l i} : i in Fin n} and rotatedPlane q = map q (horizontalPlane n l).
2. Orthonormal basis of T. Since finrank T = n, the orthonormal basis stdOrthonormalBasis R T, reindexed along finrank T = n, is an orthonormal basis (u_i)_{i in Fin n} of T. Viewed in E (the inclusion T -> E is a linear isometry), (u_i) is an orthonormal family in E, and span_R{u_i : i in Fin n} = T, because the span in E of the image of a basis of T is the image of T under the inclusion, i.e. T itself.
3. Extension. Define v : Fin (n+l) -> E by v := Fin.append u 0, so v(Fin.castAdd l i) = u_i, and let s := range (Fin.castAdd l). The restriction of v to s is orthonormal: it is the orthonormal family u composed with the bijection Fin n -> s, i |-> Fin.castAdd l i. Since finrank E = n + l = card (Fin (n+l)), Orthonormal.exists_orthonormalBasis_extension_of_card_eq gives an orthonormal basis b : OrthonormalBasis (Fin (n+l)) R E with b(Fin.castAdd l i) = u_i for every i in Fin n.
4. The isometry. Let q := b.repr.symm. Because E = EuclideanSpace R (Fin (n+l)), q is a linear isometry equivalence of E = Amb n l onto itself, and q(e_k) = b k for every k (OrthonormalBasis.repr_symm_single).
5. Conclusion. rotatedPlane q = map q (span{e_{castAdd l i} : i}) = span{q(e_{castAdd l i}) : i} (Submodule.map_span) = span{b(castAdd l i) : i} = span{u_i : i} = T, by steps 2 to 4.

## Key steps

1. Take an orthonormal basis (u_i)_{i<n} of T (finrank T = n)
2. Place it at the indices castAdd l i and extend it to an orthonormal basis b of R^{n+l} (Orthonormal.exists_orthonormalBasis_extension_of_card_eq)
3. Let q := b.repr.symm, so q(e_k) = b_k
4. rotatedPlane q = span{q e_{castAdd l i}} = span{u_i} = T

## Reference use

### local-project

Queries:
- `rg -n 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_image_le \(h : LipschitzOnWith|theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval|theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub|theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ|theorem exists_measurable_le_lintegral_eq|theorem measure_compl_support|theorem ae_differentiableAt|theorem measurable_fderiv |theorem addHaar_sphere|exists_orthonormalBasis_extension' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*ae_differentiableAt|theorem .*ae_differentiableWithinAt' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'lemma measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean; rg -n "theorem lintegral_withDensity_eq_lintegral_mul₀|theorem ae_withDensity_iff'" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `grep -n 'theorem\|lemma' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean; grep -rln 'AbsolutelyContinuousOnInterval|integral_deriv_eq_sub' <snapshot>/mathlib/Mathlib`
- `sed -n 1,260p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 1025,1060p <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem .*area|theorem .*graph|lemma .*graph' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02 Chapter03; sed -n 40,90p .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `python3 -I: list id/lean_name/status of all 200 nodes in <run>/dag.json; filter lean_statements containing rotatedPlane or graphPoint with span`
- `rg -l -e 'tdo_exists_isometry_rotatedPlane|tdo_graph_plane_dist|tdo_graph_lintegral_le|tdo_one_dim_sup_le|tdo_scaledLpNorm_bounds|tdo_tiltExcess_le_of_subset|tdo_small_tilt_plane|tdo_graph_height_excess|tdo_graph_height_sup' <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare (no match)`
- `sed -n 730,1000p book/chapter-05.txt (printed proof of 4.5)`
- `lake env lean -o /tmp/tdo-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean /tmp/tdo-decomp/checks/Types.lean; lean /tmp/tdo-decomp/checks/TypesPrint.lean; lean /tmp/tdo-decomp/checks/TypesNoOpen.lean; lean /tmp/tdo-decomp/checks/Final2.lean`
- `lean /tmp/tdo-decomp/checks/ParseMine.lean (rfl parse checks of integral bodies followed by +)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/tdo-decomp/checks/Types.lean`
- `/tmp/tdo-decomp/checks/TypesPrint.lean`
- `/tmp/tdo-decomp/checks/TypesNoOpen.lean`
- `/tmp/tdo-decomp/checks/Final2.lean`
- `/tmp/tdo-decomp/checks/ParseMine.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). Its Contract.lean has the same sha256 (c966f51e...) as the workspace Contract.lean and Submission.lean.

Mathlib declarations located for the child proofs (paths under mathlib/Mathlib):
- Area bound (tdo_graph_lintegral_le):
  - EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187): μHE[d] = volume on EuclideanSpace ℝ (Fin d).
  - euclideanHausdorffMeasure_def (same file): μHE[d] is a d-only scalar times μH[d].
  - LipschitzOnWith.hausdorffMeasure_image_le (MeasureTheory/Measure/Hausdorff.lean:733).
- One-dimensional FTC (tdo_one_dim_sup_le):
  - LipschitzOnWith.absolutelyContinuousOnInterval (MeasureTheory/Function/AbsolutelyContinuous.lean:309).
  - AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:225).
  - Rademacher: LipschitzOnWith.ae_differentiableWithinAt_of_mem (Analysis/Calculus/Rademacher.lean:361).
  - measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:378).
- Hoelder (tdo_scaledLpNorm_bounds):
  - ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory/Integral/MeanInequalities.lean:202).
  - eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (MeasureTheory/Function/LpSeminorm/CompareExp.lean:32).
  - exists_measurable_le_lintegral_eq (MeasureTheory/Integral/Lebesgue/Basic.lean:139), for non-measurable integrands.
- Null sphere: addHaar_sphere_of_ne_zero (MeasureTheory/Measure/Lebesgue/EqHaar.lean:519).
- Rotation (tdo_exists_isometry_rotatedPlane): Orthonormal.exists_orthonormalBasis_extension_of_card_eq (Analysis/InnerProductSpace/PiL2.lean:1044).
- Weight measure:
  - measure_compl_support (MeasureTheory/Measure/Support.lean:202).
  - ae_withDensity_iff' (MeasureTheory/Measure/WithDensity.lean:291).
  - lintegral_withDensity_eq_lintegral_mul₀ (MeasureTheory/Measure/WithDensity.lean:458).

No-match results:
- Mathlib has no varifold-specific results; this was already established for the parent.
- None of the nine new tdo_ names occurs anywhere searched.

Other packages and nodes:
- simongmt (outside the snapshot) has a sorry-free injective area formula, injective_area_formula_lipschitzOn_simon_volume (Chapter02/AreaLiteral.lean:61). It is not needed, because the simpler Lipschitz-image bound gives the same constant 2^{n/2}.
- dag.json: allard52_graph_plane_algebra has a rotation-existence conjunct but is not accepted (decomposing), so it cannot be reused. Its type also differs.

The printed proof of 4.5 (book/chapter-05.txt:776-990) was compared with the supplied proof. The children cover its steps (1)-(22) as mapped in the rationale.

Lean: all nine frozen lean_statements elaborate against the compiled Submission olean, with only the expected sorry warnings (Final2.lean). The integral-body parses were confirmed by rfl (ParseMine.lean).
