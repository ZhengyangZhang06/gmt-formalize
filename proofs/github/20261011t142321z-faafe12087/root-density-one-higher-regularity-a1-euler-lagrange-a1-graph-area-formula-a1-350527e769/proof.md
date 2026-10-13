# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_higher_regularity-a1.euler_lagrange-a1`
- Child DAG node: `root.density_one_higher_regularity-a1.euler_lagrange-a1.graph_area_formula-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the (Area) fact of Steps 6-7 of the parent proof (area formula for the injective graph parametrization), which the parent cites from simongmt's area formula; that library and Mathlib's normDet are not reachable from the frozen imports, so the formula is proved here from the linear case (sibling dohr_vel_linear_graph_area) by local linearization. Notation: Lambda_P(v) := graphPoint v (P v); pi : R^(n+l) -> R^n the projection onto the first n coordinates (continuous linear, pi(graphPoint v w) = v); all measures are in [0, infinity].

1. Preliminaries. (a) <graphPoint v w, graphPoint v' w'> = <v, v'> + <w, w'> (split the coordinate sum with Fin.sum_univ_add and Fin.append_left/right); hence ||graphPoint v w||^2 = ||v||^2 + ||w||^2, so ||v|| <= ||graphPoint v w|| and ||graphPoint 0 w|| = ||w||; graphPoint is additive in the pair, so G(x) - G(x') = graphPoint (x - x') (u x - u x'). (b) G is injective (pi o G = id) and continuous on D (graphPoint is a continuous linear function of the pair and u is continuous on D). (c) Du is continuous on D (ContDiffOn.continuousOn_fderiv_of_isOpen) and u is differentiable at every point of the open set D. (d) J is continuous on L(R^n, R^l): it is sqrt composed with det of a matrix whose entries delta_{ab} + <P e_a, P e_b> are continuous in P (Continuous.matrix_det, continuous_matrix). (e) J(P) > 0 for every P, by dohr_vel_linear_graph_area (det g(P) > 0).
2. Bi-Lipschitz comparison. Let P be linear, c >= 0 and S a set with ||u x - u y - P(x - y)|| <= c ||x - y|| for all x, y in S. Then H^n(G(S)) <= (1+c)^n H^n(Lambda_P(S)) and H^n(Lambda_P(S)) <= (1+c)^n H^n(G(S)). Indeed, for x, x' in S, G x - G x' = Lambda_P(x - x') + graphPoint 0 (u x - u x' - P(x - x')), so by step 1(a) ||G x - G x'|| <= ||Lambda_P(x - x')|| + c ||x - x'|| <= (1+c) ||Lambda_P x - Lambda_P x'||, and symmetrically ||Lambda_P x - Lambda_P x'|| <= ||G x - G x'|| + c ||x - x'|| <= (1+c) ||G x - G x'||. Hence psi := G o pi is (1+c)-Lipschitz on Lambda_P(S) with psi(Lambda_P(S)) = G(S), and phi := Lambda_P o pi is (1+c)-Lipschitz on G(S) with phi(G(S)) = Lambda_P(S). Apply LipschitzOnWith.hausdorffMeasure_image_le with d = n (H^d of the image is at most K^d times H^d of the set) and multiply by the positive normalizing constant in muHE[n] = c_n muH[n] (Measure.euclideanHausdorffMeasure_def).
3. Local estimate. Let 0 < eps and x0 in D, and put P := Du(x0). By 1(c)-(e) and openness of D choose rho > 0 with B := ball(x0, rho) contained in D such that, for all y in B, ||Du(y) - P|| <= eps and |J(Du y) - J(P)| < eps/(1+eps) J(P). (a) By the mean value inequality on the convex set B (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'), ||u x - u y - P(x - y)|| <= eps ||x - y|| for x, y in B. (b) Elementary algebra gives J(P) <= (1+eps) J(Du y) and J(Du y) <= (1+eps) J(P) for y in B: from J(Du y) > J(P) - eps/(1+eps) J(P) = J(P)/(1+eps), and J(Du y) < J(P) + eps/(1+eps) J(P) <= (1+eps) J(P). (c) Let S be a measurable subset of B. By step 2 (with c = eps), dohr_vel_linear_graph_area and (b): H^n(G S) <= (1+eps)^n H^n(Lambda_P S) = (1+eps)^n J(P) L^n(S) = (1+eps)^n integral_S J(P) <= (1+eps)^(n+1) integral_S J(Du); and integral_S J(Du) <= (1+eps) J(P) L^n(S) = (1+eps) H^n(Lambda_P S) <= (1+eps)^(n+1) H^n(G S).
4. Global estimate. Fix eps > 0 and choose rho(x) as in step 3 for every x in D. The open balls ball(x, rho(x)) (x in D) cover D; by second countability countably many of them cover D (TopologicalSpace.isOpen_iUnion_countable). If this countable family is empty then D, hence A, is empty and both sides are 0; otherwise enumerate it as B_k (k in N). Put C_k := A intersected with disjointed(B)_k: the C_k are measurable, pairwise disjoint, C_k is contained in B_k, and their union is A (union of disjointed(B) = union of B, which contains A). The sets G(C_k) are pairwise disjoint (G injective) and measurable (images of Borel sets under the continuous injective map G on the Polish space R^n: MeasurableSet.image_of_continuousOn_injOn), and G(A) is their union. By countable additivity of H^n and of the set-lintegral (measure_iUnion, lintegral_iUnion) and step 3(c) on each C_k: H^n(G A) = sum_k H^n(G C_k) <= (1+eps)^(n+1) sum_k integral_{C_k} J(Du) = (1+eps)^(n+1) integral_A J(Du), and likewise integral_A J(Du) <= (1+eps)^(n+1) H^n(G A).
5. Limit. In [0, infinity]: if X <= (1+eps)^(n+1) Y for every eps > 0 then X <= Y (trivial if Y = infinity; otherwise ofReal((1+eps)^(n+1)) Y tends to Y as eps -> 0+, by continuity of t -> (1+t)^(n+1) and ENNReal.Tendsto.mul_const). Applying this to both inequalities of step 4 gives H^n(G(A)) = integral_A J(Du(x)) dx.

Supplementary machine check (not needed for the argument above). A kernel-checked Lean proof of exactly this frozen declaration, the formal counterpart of the numbered steps above, is stored verbatim at /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Scratch/dohr_vel/v3/children/dohr_vel_graph_area_formula.lean.txt (SHA-256 9d1e5eaf66cf6be8628d959af5519b17aa423e62d37e216a8379e4abbbaf15c1). Of the other children it uses only its declared dependency dohr_vel_linear_graph_area. On 2026-10-12, with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d), the eight children of this split were inserted unchanged, one at a time in the order dohr_vel_linear_graph_area, dohr_vel_graph_fderiv, dohr_vel_holder_rigid_transport, dohr_vel_area_integrand_fderiv, dohr_vel_graph_projection_trace, dohr_vel_graph_area_formula, dohr_vel_graph_area_transport, dohr_vel_vertical_test_field, into the frozen GMT/Ch05/Submission.lean inside `namespace Submission ... end Submission` immediately before `theorem main_theorem` (so the contract's `open` commands are in effect). The workflow's leaf_verification.check_source_delta accepted each insertion as a single theorem; the file compiled with no errors (only deprecation and unused-simp-argument linter warnings, which the comparator ignores); this declaration used 58759 heartbeats (default limit 200000); `#print axioms` reports only propext, Classical.choice and Quot.sound; and the configured child comparator's own challenge and solution modules (verifier/gmt-compare.py child_modules, solution `exact Submission.dohr_vel_graph_area_formula`) compiled without diagnostics.

## Key steps

1. inner product of graph points; G injective and continuous on D; Du continuous; J continuous and positive
2. bi-Lipschitz comparison: if u is c-close to a linear P on S then H^n(G S) and H^n(Lambda_P S) agree up to (1+c)^n (Lipschitz images of Hausdorff measure)
3. local estimate on small balls via the mean value inequality, continuity of J o Du and the linear area formula
4. countable ball cover, disjointification and countable additivity give the two-sided global estimate with factor (1+eps)^(n+1)
5. let eps -> 0 to obtain equality

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
