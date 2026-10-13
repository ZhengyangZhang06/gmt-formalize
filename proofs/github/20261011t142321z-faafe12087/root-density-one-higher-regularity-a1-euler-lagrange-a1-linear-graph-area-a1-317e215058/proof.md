# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.euler_lagrange-a1.linear_graph_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the linear case of the area formula used in Steps 6-7 of the parent proof ((Area) with the Jacobian J(Du) = det(g(Du))^{1/2}); it replaces simongmt's normDet/area formula, which the frozen imports of GMT.Ch05.Submission do not reach.

1. Inner products of graph points. For v, v' in R^n and w, w' in R^l, <graphPoint v w, graphPoint v' w'> = <v, v'> + <w, w'>: the inner product of R^(n+l) is the sum over Fin (n+l) of products of coordinates; split this sum into the indices Fin.castAdd l j and Fin.natAdd n k (Fin.sum_univ_add) and use Fin.append_left / Fin.append_right (graphPoint v w = toLp (Fin.append (ofLp v) (ofLp w))).
2. Lambda := Lambda_P is R-linear (compare coordinates with Fin.addCases; equivalently Lambda = Gamma o (id, P) with Gamma(v, w) = graphPoint v w linear) and injective: the first n coordinates of graphPoint v w are those of v, so pi(Lambda v) = v for the coordinate projection pi.
3. W := range Lambda is a subspace of R^(n+l) of dimension n (LinearMap.finrank_range_of_inj with finrank R^n = n). Let b be an orthonormal basis of W indexed by Fin n (stdOrthonormalBasis of W reindexed along finrank W = n) and e : W -> R^n the linear isometry equivalence b.repr. Define the linear map M := e o Lambda' : R^n -> R^n, where Lambda' : R^n -> W is Lambda with codomain restricted to W, and iota(z) := (e^{-1} z : W) viewed in R^(n+l). iota is an isometry (the inclusion of W composed with the linear isometry e^{-1}) and iota(M v) = Lambda v for all v; hence Lambda(S) = iota(M(S)) for every S.
4. Gram identity. e^{-1} and the inclusion preserve inner products, so <M v, M w> = <Lambda v, Lambda w> for all v, w. Let Mm be the matrix of M in the standard basis (Mm_{ka} = (M e_a)_k, LinearMap.toMatrix_apply). Then (Mm^T Mm)_{ab} = sum_k (M e_a)_k (M e_b)_k = <M e_a, M e_b> = <Lambda e_a, Lambda e_b> = <e_a, e_b> + <P e_a, P e_b> (step 1) = delta_{ab} + <P e_a, P e_b> = g(P)_{ab}. Hence g(P) = Mm^T Mm and det g(P) = det(Mm)^2 = (det M)^2 (Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix).
5. M is injective (iota(M v) = Lambda v and Lambda is injective), hence bijective (finite dimension, LinearMap.injective_iff_surjective), so it is a linear equivalence and det M != 0 (LinearEquiv.isUnit_det'). Therefore det g(P) = (det M)^2 > 0, the first assertion.
6. Measure. For every S: H^n(Lambda(S)) = H^n(iota(M(S))) = H^n(M(S)) because muHE[n] is invariant under isometries (Isometry.euclideanHausdorffMeasure_image); H^n(M(S)) = L^n(M(S)) because muHE[n] is Lebesgue measure on R^n (EuclideanSpace.euclideanHausdorffMeasure_eq_volume); and L^n(M(S)) = |det M| L^n(S) (Measure.addHaar_image_linearMap, valid for every set). Finally |det M| = sqrt((det M)^2) = sqrt(det g(P)) (Real.sqrt_sq_eq_abs and step 4). This is the second assertion.

Supplementary machine check (not needed for the argument above). A kernel-checked Lean proof of exactly this frozen declaration, the formal counterpart of the numbered steps above, is stored verbatim at /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_linear_graph_area.lean.txt (SHA-256 192e5732786ed15797111190d86f9fea1882cf8d5876d8e083e3a222366905c4). It uses no other theorem of this split. On 2026-10-12, with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d), the eight children of this split were inserted unchanged, one at a time in the order dohr_vel_linear_graph_area, dohr_vel_graph_fderiv, dohr_vel_holder_rigid_transport, dohr_vel_area_integrand_fderiv, dohr_vel_graph_projection_trace, dohr_vel_graph_area_formula, dohr_vel_graph_area_transport, dohr_vel_vertical_test_field, into the frozen GMT/Ch05/Submission.lean inside `namespace Submission ... end Submission` immediately before `theorem main_theorem` (so the contract's `open` commands are in effect). The workflow's leaf_verification.check_source_delta accepted each insertion as a single theorem; the file compiled with no errors (only deprecation and unused-simp-argument linter warnings, which the comparator ignores); this declaration used 17453 heartbeats (default limit 200000); `#print axioms` reports only propext, Classical.choice and Quot.sound; and the configured child comparator's own challenge and solution modules (verifier/gmt-compare.py child_modules, solution `exact Submission.dohr_vel_linear_graph_area`) compiled without diagnostics.

## Key steps

1. inner product of graph points splits over the first n and last l coordinates
2. Lambda_P is linear and injective; its range W has dimension n
3. orthonormal coordinates e : W -> R^n give Lambda_P = iota o M with iota an isometry and M : R^n -> R^n linear
4. Gram identity g(P) = Mm^T Mm, hence det g(P) = (det M)^2 > 0
5. H^n(Lambda_P S) = H^n(M S) = L^n(M S) = |det M| L^n(S) = sqrt(det g(P)) L^n(S)

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
