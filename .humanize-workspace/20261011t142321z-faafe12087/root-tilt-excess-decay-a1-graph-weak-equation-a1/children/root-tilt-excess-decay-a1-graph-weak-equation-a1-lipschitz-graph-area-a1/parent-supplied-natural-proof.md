# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.lipschitz_graph_area-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This is the area formula of Simon Ch. 2, 3.5, for the graph map F (fact (Area) of the parent proof). It is used by the parent (L^n(A) <= H^n(F(A)) and H^n(F(Z)) = 0 for null Borel Z), by gwe_varifold_graph_transfer and by gwe_graph_tangential_estimate. Throughout, A is a Borel subset of R^n: MeasurableSet on Rn n refers to the Borel sigma-algebra (Mathlib's instance on EuclideanSpace R (Fin n) is the Borel one), and the proof below uses only that A is Borel.

Tools. The Lean proof may add the pinned import Poincare.SimonGMT.Chapter02.AreaLipschitz (the accepted sibling ted_tangent_plane_facts adds the same import). It provides:
- weighted_area_formula_lipschitz_injOn: for a Lipschitz map Phi : E -> F between finite-dimensional real inner product spaces, a Borel set s in E (MeasurableSet s; E carries its Borel sigma-algebra) on which Phi is injective, and an arbitrary g : F -> [0, infinity],
 int_{Phi(s)} g d muHE[finrank E] = int_s ofReal(areaJacobianAt Phi x) * g(Phi x) dx;
- areaJacobianAt_nonneg;
- areaJacobianAt_sq_eq_det_gram: (areaJacobianAt Phi x)^2 = det(gram(fderiv Phi x (b a))) for every orthonormal basis b of E indexed by Fin (finrank E).
From lip_approx_graph_coordinates (GC):
- graphPoint a b - graphPoint a' b' = graphPoint (a - a') (b - b');
- ||graphPoint a b||^2 = ||a||^2 + ||b||^2.
Also, graphPoint a b = E.symm (a, b) with E := EuclideanSpace.finAddEquivProd (compare coordinates with Fin.addCases; an ext/simp proof). So (a, b) |-> graphPoint a b is a continuous linear isomorphism R^n x R^l -> R^{n+l}. Polarizing GC(ii) gives <graphPoint a b, graphPoint a' b'> = <a, a'> + <b, b'>.

1. Lipschitz extension. For j in Fin l, the coordinate f_j(x) := f x j satisfies |f_j x - f_j y| <= ||f x - f y|| <= K ||x - y|| on B_R(0) (|v_j| <= ||v|| in EuclideanSpace, PiLp.norm_apply_le). By McShane (LipschitzOnWith.extend_real) there are K-Lipschitz g_j : R^n -> R with g_j = f_j on B_R(0). Put f~(x) := WithLp.toLp 2 (fun j => g_j x). Then f~ = f on B_R(0), and ||f~ x - f~ y|| <= sum_j |g_j x - g_j y| <= l K ||x - y||, so f~ is globally Lipschitz.
2. The extended graph map F~(x) := q(graphPoint x (f~ x)).
 - Lipschitz: by GC and since q is an isometry, ||F~ x - F~ y||^2 = ||x - y||^2 + ||f~ x - f~ y||^2 <= (1 + l^2 K^2) ||x - y||^2.
 - Injective: if F~ x = F~ y then graphPoint x (f~ x) = graphPoint y (f~ y), and the first block (E(.)).1 gives x = y.
 - Agrees with F: F~ x = F x for x in B_R(0). Hence F~ '' A = F '' A = q '' graphOver f A (graphOver f A = (fun x => graphPoint x (f x)) '' A, image_image).
3. Apply weighted_area_formula_lipschitz_injOn to F~ with s = A and the given g. Since finrank R^n = n (finrank_euclideanSpace_fin),
 int_{q '' graphOver f A} g d muHE[n] = int_A ofReal(areaJacobianAt F~ x) * g(F~ x) dx = int_A ofReal(areaJacobianAt F~ x) * g(F x) dx.
 The last equality holds because F~ = F on the Borel set A (setLIntegral_congr_fun).
4. Good points. Let x be in the open ball B°_R(0) with f differentiable at x, and put D := Df(x).
 - B_R(0) is a neighbourhood of x on which F~ = F, so fderiv F~ x = fderiv F x (Filter.EventuallyEq.fderiv_eq).
 - By the chain rule, F = q o E.symm o (y |-> (y, f y)) has derivative L v = q(graphPoint v (D v)) at x.
5. Jacobian at good points. Take the standard orthonormal basis e_a of R^n (EuclideanSpace.basisFun), reindexed by Fin (finrank R^n) = Fin n via finrank_euclideanSpace_fin. A Gram determinant is unchanged by this reindexing (Matrix.det_reindex_self).
 - By areaJacobianAt_sq_eq_det_gram, (areaJacobianAt F~ x)^2 = det(<L e_a, L e_b>)_{a,b}.
 - Since q preserves inner products, <L e_a, L e_b> = <graphPoint e_a (D e_a), graphPoint e_b (D e_b)> = <e_a, e_b> + <D e_a, D e_b> = delta_ab + <D e_a, D e_b>.
 - Hence (areaJacobianAt F~ x)^2 = det(I + (<D e_a, D e_b>)). Since areaJacobianAt >= 0, areaJacobianAt F~ x = sqrt(det(I + (<D e_a, D e_b>))) = J_f(x).
6. Bad points are null. A minus the good points is contained in (A cap sphere(0, R)) cup {x in B°_R(0) : f is not differentiable at x}.
 - The sphere is L^n-null (Measure.addHaar_sphere, n >= 1).
 - By Rademacher's theorem on a set (LipschitzOnWith.ae_differentiableWithinAt_of_mem applied to f on B_R(0)), for a.e. x in B_R(0), f is differentiable within B_R(0) at x. At an interior point this is differentiability at x (DifferentiableWithinAt.differentiableAt with closedBall_mem_nhds_of_mem). So the second set is null too.
7. By steps 5 and 6, ofReal(areaJacobianAt F~ x) * g(F x) = ofReal(J_f(x)) * g(F x) for a.e. x in A. So (setLIntegral_congr_fun_ae, A Borel) step 3 becomes
 int_{q '' graphOver f A} g d muHE[n] = int_A ofReal(J_f(x)) * g(q(graphPoint x (f x))) dx.
 This is the claim. (If R < 0 then A is empty and both sides are 0; the argument covers it.) QED

## Key steps

1. Extend f from B_R(0) to a globally Lipschitz f~ (McShane on each coordinate).
2. F~(x) = q(graphPoint x (f~ x)) is Lipschitz, injective, and equal to F on B_R(0).
3. SimonGMT weighted_area_formula_lipschitz_injOn: int_{F(A)} g dH^n = int_A ofReal(areaJacobianAt F~) g(F) for Borel A and arbitrary g.
4. At interior differentiability points, fderiv F~ x = q o (v |-> graphPoint v (Df v)); its Gram matrix is I + (<Df e_a, Df e_b>), so areaJacobianAt = J_f.
5. The sphere and the non-differentiability set (Rademacher) are L^n-null, so the integrands agree a.e. on A.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean (both identical)`
- `cat <snapshot>/manifest.json; python3 -I: workspace lake-manifest.json revs; git -C lake-packages-25730c7c/{mathlib,simongmt} rev-parse HEAD vs .lake/packages/{mathlib,simongmt}`
- `python3 -I: dag.json lean_name census for gwe_* and for hsNorm_starProjection_trace_identities, lip_approx_graph_coordinates, exists_smooth_cutoff_half_ball_grad_le (status, lean_statement/title/statement equality, depends_on); regex scan of every nodes/**/*.json for "lean_name": "gwe_`
- `grep -rn gwe_ <snapshot>/project/GMT (no match)`
- `grep -rl -i varifold --include=*.lean <snapshot>/mathlib/Mathlib (0 files)`
- `grep -n -A14 'theorem weighted_area_formula_lipschitz_injOn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean; grep -n 'theorem areaJacobianAt_sq_eq_det_gram' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean; sed -n 15,40p Chapter02/Area.lean`
- `sed -n 1,80p <snapshot>/mathlib/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean | grep -n 'instance|borel|BorelSpace'`
- `grep -n -A4 'theorem MeasurableSet.image_of_continuousOn_injOn' <snapshot>/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `grep -rn -A6 'theorem lintegral_withDensity_eq_lintegral_mul_non_measurable₀|theorem integral_withDensity_eq_integral_toReal_smul ' <snapshot>/mathlib/Mathlib`
- `grep -n 'theorem integral_map ' MeasureTheory/Integral/Bochner/Basic.lean; 'theorem addHaar_sphere ' MeasureTheory/Measure/Lebesgue/EqHaar.lean; 'theorem volume_ball ' MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean; 'theorem norm_fderiv_le_of_lipschitzOn ' Analysis/Calculus/FDeriv/Basic.lean; 'measurableSet_of_differentiableAt|measurable_fderiv' Analysis/Calculus/FDeriv/Measurable.lean; 'ae_differentiableWithinAt_of_mem' Analysis/Calculus/Rademacher.lean; 'LipschitzOnWith.extend_real' Topology/MetricSpace/Lipschitz.lean; 'restrict_withDensity' WithDensity.lean; 'measure_compl_support' Support.lean; 'exists_measurable_superset_of_null' MeasureSpaceDef.lean; 'aemeasurable_indicator_iff₀' AEMeasurable.lean; 'lintegral_indicator₀' Integral/Lebesgue/Basic.lean; 'det_eq_prod_eigenvalues|trace_eq_sum_eigenvalues' Analysis/Matrix/Spectrum.lean (all under <snapshot>/mathlib/Mathlib)`
- `sed -n 540,612p verifier/gmt-compare.py (contract_scope / child_modules: comparator replays the contract scope at main_theorem)`
- `grep -n '4.5 Theorem|(14)|(16)' book/chapter-05.txt; sed -n 780,800p book/chapter-05.txt`
- `lean -o /tmp/gwe-decomp-v2-20261012/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (contract-only)`
- `python3 -I /tmp/gwe-decomp-v2-20261012/scripts/build_v2.py decomposition-v1.json out/subproblems_v2.json (prose-only edits; asserts lean fields unchanged)`
- `python3 -I /tmp/gwe-decomp-v2-20261012/scripts/gen_checks.py verifier/gmt-compare.py GMT/Ch05/Contract.lean out/subproblems_v2.json checks`
- `lean checks/challenge/<X>.lean for all 10 children; lean checks/TypesSubmission.lean (10 sorry warnings, no errors)`
- `lean checks/Assembly.lean (#print axioms parent_check); lean checks/TangWiring.lean (#print axioms tang_check); lean checks/TransferWiring.lean (#print axioms transfer_check); lean checks/Inst.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Matrix/Spectrum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/gwe-decomp-v2-20261012/scripts/build_v2.py`
- `/tmp/gwe-decomp-v2-20261012/scripts/gen_checks.py`
- `/tmp/gwe-decomp-v2-20261012/checks/TypesSubmission.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/Defs.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/Assembly.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/TangWiring.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/TransferWiring.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/Inst.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/challenge/gwe_lipschitz_graph_area_formula.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/challenge/gwe_varifold_graph_transfer.lean`
- `/tmp/gwe-decomp-v2-20261012/checks/challenge/gwe_weighted_energy_weak_equation.lean`

Revisions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The workspace pins simongmt 2b3663083f3fe399b6296fb8eaee52169170e197. The lake-packages used for compilation are at the same Mathlib and simongmt commits.

Names and reuse.
- No gwe_ name occurs in dag.json, in any other node's JSON, or in the snapshot's project sources. The seven new names are free.
- The three reused declarations are 'accepted' in dag.json with byte-identical lean_statement, title and statement, and empty depends_on: hsNorm_starProjection_trace_identities (164f08e), lip_approx_graph_coordinates (e291574), exists_smooth_cutoff_half_ball_grad_le (cfec068).
- No-match: Mathlib has no varifold file (0 matches), so the varifold transfer and first-variation steps are proved in the children from the contract's definitions.

Borel correction, confirmed in the snapshot.
- WithLp.measurableSpace (Analysis/Normed/Lp/MeasurableSpace.lean:26) is the comap of the product structure, and the PiLp.borelSpace instance (line 52) makes it Borel on EuclideanSpace R (Fin n) = PiLp 2 (fun _ => R). So MeasurableSet A on Rn n means Borel A, which is what the corrected prose of the area and transfer children now says.
- SimonGMT weighted_area_formula_lipschitz_injOn (Chapter02/AreaLipschitz.lean:101) takes MeasurableSet s under [BorelSpace E] and an arbitrary g : F -> ENNReal. areaJacobianAt_sq_eq_det_gram is at Chapter02/AreaParametrization.lean:22.
- Lusin-Souslin, MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), needs a Borel source set.

Other Mathlib items located:
- lintegral_withDensity_eq_lintegral_mul_non_measurable₀ (WithDensity.lean:508) and integral_withDensity_eq_integral_toReal_smul (Bochner/ContinuousLinearMap.lean:318). Neither needs sigma-finiteness or integrability.
- integral_map (Bochner/Basic.lean:1081).
- addHaar_sphere (EqHaar.lean:527), for every radius in a nontrivial space.
- EuclideanSpace.volume_ball (VolumeOfBalls.lean:307).
- norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939).
- measurableSet_of_differentiableAt and measurable_fderiv (FDeriv/Measurable.lean:372, 378).
- LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361).
- LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308).
- restrict_withDensity (WithDensity.lean:215).
- measure_compl_support (Support.lean:202).
- exists_measurable_superset_of_null (MeasureSpaceDef.lean:219).
- aemeasurable_indicator_iff₀ (AEMeasurable.lean:323).
- lintegral_indicator₀ (Lebesgue/Basic.lean:518).
- Matrix.IsHermitian.det_eq_prod_eigenvalues and trace_eq_sum_eigenvalues (Analysis/Matrix/Spectrum.lean:192, 239).

Source. Simon's proof of Theorem 4.5 is at book/chapter-05.txt lines 747-930, displays (1)-(16). This node covers displays (5)-(16).

Fresh Lean checks against a newly compiled contract-only Submission olean.
- All 10 exact comparator challenges elaborate. They were generated by the verifier's own contract_scope/child_modules code: namespace GMT.Ch05, opens MeasureTheory Metric Set Filter Topology, scoped ENNReal NNReal, RectifiableVarifold.
- All 10 elaborate as theorem Submission.X.
- The matrix and coordinate instances are as intended.
- Sorry-free parent_check proves the frozen parent type from the child propositions. tang_check and transfer_check prove the two internal dependency derivations.
- All three use only propext, Classical.choice and Quot.sound.
