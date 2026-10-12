# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.euler_lagrange-a1.graph_projection_trace-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 5 of the parent proof (p_{tau_x}(w) = sum_{a,c} g^{ac} <b_c, w> b_a, the rotation p_{P_y} = Q^{-1} o p_{tau_x} o Q, and trace(B_x o p_{tau_x}) = sum_{a,c} g^{ac} <D_c u, D_a phi>).

1. Inner products of graph points: <graphPoint v w, graphPoint v' w'> = <v, v'> + <w, w'>. The inner product of R^(n+l) is the sum over i in Fin (n+l) of the products of coordinates; splitting this sum into the indices Fin.castAdd l j and Fin.natAdd n k (Fin.sum_univ_add) and using Fin.append_left / Fin.append_right gives sum_j v_j v'_j + sum_k w_k w'_k. In particular graphPoint 0 0 = 0 and <graphPoint v w, graphPoint 0 w'> = <w, w'>.
2. Let b_a := L e_a = graphPoint e_a (P e_a). By step 1, <b_a, b_c> = <e_a, e_c> + <P e_a, P e_c> = g_{ac}. The matrix g is symmetric, and det g > 0 by the sibling dohr_vel_linear_graph_area (first conjunct, applied to P); this replaces Matrix.PosDef and Gram-matrix lemmas, which the frozen imports do not reach. Therefore g is invertible, g^{-1} g = 1 (Matrix.nonsing_inv_mul) and (g^{-1})^T = g^{-1} (Matrix.transpose_nonsing_inv and g^T = g), i.e. (g^{-1})_{ac} = (g^{-1})_{ca}.
3. tau := range L is spanned by b_1, ..., b_n: for v = sum_a v_a e_a, L v = sum_a v_a b_a by linearity of L.
4. The orthogonal projection onto tau. For z in R^(n+l) put R(z) := sum_{a,c} (g^{-1})_{ac} <b_c, z> b_a, an element of tau. For every d, <R(z), b_d> = sum_{a,c} (g^{-1})_{ac} <b_c, z> <b_a, b_d> = sum_{a,c} (g^{-1})_{ac} <b_c, z> g_{ad} = sum_c <b_c, z> sum_a (g^{-1})_{ca} g_{ad} (symmetry of g^{-1}) = sum_c <b_c, z> (g^{-1} g)_{cd} = <b_d, z>. Hence z - R(z) is orthogonal to every b_d; since every element of tau is L v = sum_d v_d b_d (expansion of v in the standard basis, linearity of L), z - R(z) is orthogonal to tau. By the characterization of the orthogonal projection (Submodule.eq_starProjection_of_mem_of_inner_eq_zero), p_tau(z) = R(z).
5. Rotation. Q^{-1} is a linear isometry equivalence with inverse Q, so by Submodule.starProjection_map_apply, p(z) = Q^{-1}(p_tau(Q z)) for every z.
6. D o p as a sum of rank-one maps. Put y_a := D(Q^{-1} b_a) = D(Q^{-1}(graphPoint e_a (P e_a))) = Q^{-1}(graphPoint 0 (Psi e_a)) (hypothesis on D with v = e_a, w = P e_a). By steps 4-5 and linearity of D and Q^{-1}: D(p(z)) = sum_{a,c} (g^{-1})_{ac} <b_c, Q z> y_a = sum_{a,c} (g^{-1})_{ac} <Q^{-1} b_c, z> y_a, because <b_c, Q z> = <Q^{-1} b_c, z> (Q is an isometry; LinearIsometryEquiv.inner_map_eq_flip). Thus D o p = sum_{a,c} (g^{-1})_{ac} K_{ac}, where K_{ac}(z) := <Q^{-1} b_c, z> y_a.
7. Trace. The trace of the rank-one map z -> f(z) y (f a linear functional) is f(y) (LinearMap.trace_smulRight); here f = <Q^{-1} b_c, .>. By linearity of the trace, trace(D o p) = sum_{a,c} (g^{-1})_{ac} <Q^{-1} b_c, y_a> = sum_{a,c} (g^{-1})_{ac} <Q^{-1} b_c, Q^{-1}(graphPoint 0 (Psi e_a))> = sum_{a,c} (g^{-1})_{ac} <b_c, graphPoint 0 (Psi e_a)> (Q^{-1} preserves inner products) = sum_{a,c} (g^{-1})_{ac} (<e_c, 0> + <P e_c, Psi e_a>) (step 1) = sum_{a,c} (g^{-1})_{ac} <P e_c, Psi e_a>.

Supplementary machine check (not needed for the argument above). A kernel-checked Lean proof of exactly this frozen declaration, the formal counterpart of the numbered steps above, is stored verbatim at /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_graph_projection_trace.lean.txt (SHA-256 653a515f119c90f0ce3f44d04203ef87111f9bbdef50cf51e92cacf3ede2e3c4). Of the other children it uses only its declared dependency dohr_vel_linear_graph_area. On 2026-10-12, with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d), the eight children of this split were inserted unchanged, one at a time in the order dohr_vel_linear_graph_area, dohr_vel_graph_fderiv, dohr_vel_holder_rigid_transport, dohr_vel_area_integrand_fderiv, dohr_vel_graph_projection_trace, dohr_vel_graph_area_formula, dohr_vel_graph_area_transport, dohr_vel_vertical_test_field, into the frozen GMT/Ch05/Submission.lean inside `namespace Submission ... end Submission` immediately before `theorem main_theorem` (so the contract's `open` commands are in effect). The workflow's leaf_verification.check_source_delta accepted each insertion as a single theorem; the file compiled with no errors (only deprecation and unused-simp-argument linter warnings, which the comparator ignores); this declaration used 22009 heartbeats (default limit 200000); `#print axioms` reports only propext, Classical.choice and Quot.sound; and the configured child comparator's own challenge and solution modules (verifier/gmt-compare.py child_modules, solution `exact Submission.dohr_vel_graph_projection_trace`) compiled without diagnostics.

## Key steps

1. <graphPoint v w, graphPoint v' w'> = <v, v'> + <w, w'>
2. Gram matrix of b_a = L e_a is g; g symmetric with det g > 0 (sibling dohr_vel_linear_graph_area), hence invertible with symmetric inverse
3. p_tau(z) = sum (g^{-1})_{ac} <b_c, z> b_a by the orthogonality characterization
4. rotation: p = Q^{-1} o p_tau o Q
5. D o p is a combination of rank-one maps; trace of z -> <beta, z> y is <beta, y>

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp GMT/Ch05/Submission.lean <snapshot>/project/GMT/Ch05/Submission.lean; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean; cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `rg -l 'dohr_vel_' <snapshot> (no match); rg -l 'dohr_vel_' .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes dag.json .humanize/math-wiki GMT/Ch05 .lake/packages/simongmt/Poincare (matches only this node's decomposition-v1/v2 and their audit/receipt files)`
- `python3 scan of dag.json: lean_name values containing 'dohr', status/children/depends_on of root.density_one_higher_regularity-a1.* nodes, frozen type of dohr_graph_tangent_planes`
- `sha256sum -c GMT/Scratch/dohr_vel/SHA256SUMS`
- `lake env lean -o /tmp/elv3/build/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean`
- `lake env bash -c 'LEAN_PATH=$LEAN_PATH:/tmp/elv3/build lean /tmp/elv3/SplitAll.lean' (copy of GMT/Scratch/dohr_vel/dohr_vel_split_all.lean.txt)`
- `python3 GMT/Scratch/dohr_vel/v3/leaf_insertion_check.py.txt (runs _recursive_lean.leaf_verification.check_source_delta on each one-theorem insertion)`
- `lake env lean --root=/tmp/elv3/srcall -o /tmp/elv3/buildall/GMT/Ch05/Submission.olean /tmp/elv3/srcall/GMT/Ch05/Submission.lean (frozen Submission.lean plus all 8 children)`
- `python3 -I GMT/Scratch/dohr_vel/v3/comparator_modules.py.txt (verifier/gmt-compare.py child_modules in contract mode after validate_lean_statement), then lean on every <key>_Challenge.lean and <key>_Solution.lean`
- `#count_heartbeats in (import Mathlib.Util.CountHeartbeats) on each child and on the parent assembly`
- `#check @Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitzOn, @LinearMap.normDet, @Matrix.PosDef, @Matrix.det_one_add_smul, @MeasureTheory.Measure.addHaar_image_linearMap, @Isometry.euclideanHausdorffMeasure_image, @LipschitzOnWith.hausdorffMeasure_image_le, @ContDiffBump after import GMT.Ch05.Submission`
- `example : (1 + Matrix.of Gram)⁻¹ = Ring.inverse (det ..) • adjugate .. := Matrix.inv_def _; example : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp`
- `rg -n 'theorem addHaar_image_linearMap|theorem (Isometry\.)?euclideanHausdorffMeasure_image|euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_image_le|lemma det_one_add_smul|theorem inv_def|theorem MeasurableSet.image_of_continuousOn_injOn|theorem ContinuousOn.measurableEmbedding|iteratedFDeriv_comp_add_left|theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_right|theorem ContinuousLinearEquiv.iteratedFDeriv_comp_left|norm_compContinuous_linearIsometryEquiv|norm_compContinuousMultilinearMap|theorem starProjection_map_apply|theorem eq_starProjection_of_mem_of_inner_eq_zero|theorem one_of_mem_closedBall|theorem support_eq|trace_smulRight|theorem measurable_fderiv|lemma measure_compl_support|setIntegral_withDensity_eq_setIntegral_smul|MeasurableEmbedding.integral_map' <snapshot>/mathlib/Mathlib`
- `grep -n 'theorem injective_area_formula_lipschitzOn|^namespace' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean; grep -n '^import' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n -i 'area formula' book/chapter-02.txt; sed -n 743,800p book/chapter-02.txt; sed -n 20,130p book/chapter-05.txt; sed -n 1312,1345p book/chapter-05.txt`
- `grep -n 'def check_source_delta|def _solve_children|def _existing_lean_name_problem|def _leaf_author_task' /runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/{leaf_verification,runtime}.py; grep -n 'def lean_diagnostics|def child_modules' verifier/gmt-compare.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/dohr_vel_split_all.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/SHA256SUMS`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/SHA256SUMS`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/SubmissionAll.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/parent_assembly_dohr_vertical_euler_lagrange.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_linear_graph_area.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_graph_fderiv.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_holder_rigid_transport.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_area_integrand_fderiv.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_graph_projection_trace.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_graph_area_formula.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_graph_area_transport.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_vertical_test_field.lean.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-euler-lagrange-a1/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/runtime.py`

Pinned snapshot (manifest.json): project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies and to each other.

Reachability under `import GMT.Ch05.Submission`:
- Not reachable (Lean reports unknown identifiers): simongmt's Chapter02.injective_area_formula_lipschitzOn (it exists in AreaDomain.lean:147 but is not imported; the contract imports only Chapter03.Rectifiable from simongmt), LinearMap.normDet and Matrix.PosDef.
- Reachable, so the children use them: det_one_add_smul (Charpoly/Coeff.lean:207), Measure.addHaar_image_linearMap (EqHaar.lean:297), Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Volume/Measure.lean:131,187), LipschitzOnWith.hausdorffMeasure_image_le (Hausdorff.lean:733), Matrix.inv_def (NonsingularInverse.lean:170), MeasurableSet.image_of_continuousOn_injOn and ContinuousOn.measurableEmbedding (Polish/Basic.lean:821,865), iteratedFDeriv_comp_add_left (FTaylorSeries.lean:958), ContinuousLinearEquiv.iteratedFDeriv_comp_left and iteratedFDerivWithin_comp_right (ContDiff/Basic.lean:283,436), norm_compContinuous_linearIsometryEquiv (Multilinear/Basic.lean:1038), starProjection_map_apply and eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:358,180), ContDiffBump.one_of_mem_closedBall and support_eq, LinearMap.trace_smulRight (Trace.lean:272), measurable_fderiv (FDeriv/Measurable.lean:378), Measure.measure_compl_support (Support.lean:202), setIntegral_withDensity_eq_setIntegral_smul, and MeasurableEmbedding.integral_map (Bochner/Basic.lean:1093).

Therefore the (Area) fact is proved by two new children. The rest of the attempt-2 split is reused unchanged.

Re-verification on 2026-10-12 with the pinned toolchain (record in GMT/Scratch/dohr_vel/v3/):
- dohr_vel_split_all.lean.txt still compiles: the 8 children use only propext, Classical.choice and Quot.sound, and the parent uses these plus the sibling stub.
- Each child passes check_source_delta as a one-theorem leaf insertion.
- The frozen Submission.lean with all 8 children compiles; the only warning is the inherited main_theorem sorry.
- The comparator-generated challenge modules elaborate, and the solution modules (`exact Submission.X`) compile with no diagnostics.
- Per-child heartbeats are at most 58,759; the parent assembly uses 34,734.
- The inline matrix `⁻¹` is the ordinary nonsingular inverse.

No snapshot, simongmt, wiki or DAG entry uses any dohr_vel_ name; the only matches are this node's own decomposition-v1/v2 records. The names are therefore free.
