# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This is Simon 4.5 (8)-(12) on the varifold side (steps 3-5 of the parent proof). The parent transfers it to the parameter domain with (b) of gwe_varifold_graph_transfer and bounds the right side by (K_b E + E + h/4) M sigma^n. Prerequisites:
- gwe_vertical_first_variation (FV);
- gwe_graph_tilt_algebra (TA), part (b);
- gwe_lipschitz_graph_area_formula (AREA);
- lip_approx_graph_coordinates (GC).
(This derivation was checked in Lean from the frozen statements of these four declarations; only propext, Classical.choice and Quot.sound are used.)

Notation. mu := V.weight, F(x') := q(graphPoint x' (f x')), so Gamma = F(B_{sigma/2}) and Gamma' = F(B°_{sigma/4}). e'_j := q(graphPoint 0 (single j 1)).
 Phi(x) := <p_x e'_j, p_x q(graphPoint (grad zeta(a x)) 0)> is the integrand of FV, and phi(x) := <grad f^j(a x), grad zeta(a x)>. B := B_{sigma/2}(0) (closed ball).

1. Basic facts.
 (i) a(F x') = a(q(graphPoint x' y)) = x' (q^{-1} q = id and finAddEquivProd(graphPoint x' y) = (x', y), by coordinates).
 (ii) F is continuous on B^n_{sigma/2}: graphPoint a b = finAddEquivProd.symm (a, b) is continuous, and f is Lipschitz there.
 (iii) ||p_x v|| <= ||v|| for all x, v (p_x is a starProjection or 0).
 (iv) ||q(graphPoint w 0)|| = ||w|| and ||e'_j|| = 1 (GC(ii)).
 (v) grad zeta(y) = 0 for y outside tsupport zeta (support_fderiv_subset). M >= 0.
 Hence |Phi(x)| <= ||e'_j|| ||grad zeta(a x)|| <= M for every x.
2. Measure facts.
 (i) mu(B_sigma(0)) < infinity. By withDensity_apply and Measure.restrict_restrict it equals int_{M cap B_sigma(0)} ofReal(theta) dH^n, which is finite by V.integrableOn_mult (B_sigma(0) is compact and lies in U).
 (ii) mu((spt V)^c) = 0. spt V = U cap supp(mu), mu((supp mu)^c) = 0 (Measure.measure_compl_support), and mu(U^c) = 0 since mu << H^n restricted to the carrier, which lies in U.
 (iii) Gamma is compact (image of a compact ball under a map continuous on it), hence Borel. Gamma' = Gamma cap a^{-1}(B°_{sigma/4}(0)) by (1)(i), hence Borel.
 (iv) Gamma' lies in B. For |x'| < sigma/4: ||F x'||^2 = ||x'||^2 + ||f x'||^2 <= sigma^2/16 + sigma^2/256 <= sigma^2/4.
3. Integrability. Phi is mu-a.e. strongly measurable: it is a continuous function of (p_x, x), x |-> p_x is mu-a.e. strongly measurable by hypothesis, and grad zeta is continuous since zeta is C^1. With |Phi| <= M and mu(B) < infinity, Phi is integrable on B (Measure.integrableOn_of_bounded). Likewise x |-> |p_x - P|^2 is integrable on B_sigma(0): it is a.e. strongly measurable, and bounded by 4(n + l) since ||p_x - P|| <= 2.
4. First variation. By FV, |int_B Phi dmu| <= M (sigma/4) int_B ||H|| dmu.
5. Splitting. By integral_inter_add_sdiff (Gamma' is measurable and contained in B), int_B Phi = int_{Gamma'} Phi + int_{B \ Gamma'} Phi. Again by integral_inter_add_sdiff with the measurable set Gamma,
 int_{B \ Gamma'} Phi = int_{(B \ Gamma') cap Gamma} Phi + int_{(B \ Gamma') \ Gamma} Phi.
6. Graph points outside Gamma' contribute 0. Let x be in (B \ Gamma') cap Gamma, so x = F(x') with |x'| <= sigma/2.
 - Since x is not in Gamma', x' is not in B°_{sigma/4}, hence not in tsupport zeta.
 - By (1)(i) and (1)(v), grad zeta(a x) = grad zeta(x') = 0, so q(graphPoint 0 0) = 0 and Phi(x) = 0.
 - Hence int_{(B \ Gamma') cap Gamma} Phi = 0 (setIntegral_eq_zero_of_forall_eq_zero).
7. Off-graph part. Since |Phi| <= M, norm_setIntegral_le_of_norm_le_const gives |int_{(B \ Gamma') \ Gamma} Phi| <= M mu((B \ Gamma') \ Gamma). Moreover (B \ Gamma') \ Gamma is contained in (B cap (spt V \ Gamma)) cup (spt V)^c, so by (2)(ii) this measure is <= mu(B cap (spt V \ Gamma)). All these measures are finite by (2)(i), so the bound holds after toReal.
8. Non-differentiability points are mu-null. Let Z := {x' in B°_{sigma/2} : f is not differentiable at x'}.
 - Z is Borel (measurableSet_of_differentiableAt). It is L^n-null by Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem on B^n_{sigma/2}; interior points).
 - AREA with g = 1 gives H^n(F(Z)) = int_Z J_f = 0.
 - Since mu << H^n (withDensity of a restriction), mu(F(Z)) = 0.
9. Pointwise comparison on Gamma'. For mu-a.e. x: the tangent-plane hypothesis holds at x, and x is not in F(Z). Let such an x lie in Gamma', i.e. x = F(x') with x' in B°_{sigma/4}, contained in B°_{sigma/2}.
 - Then a(x) = x', and f is differentiable at x' (otherwise x would be in F(Z)). So p_x = S.starProjection, where S := span{q(graphPoint v (Df(x') v))}.
 - ||Df(x')|| <= 1 (norm_fderiv_le_of_lipschitzOn, since B^n_{sigma/2} is a neighbourhood of x').
 - r := grad f^j(x') satisfies <r, v> = (Df(x') v)_j: (fun y => f y j) = (EuclideanSpace.proj j) o f has derivative (proj j) o Df(x') by the chain rule, and <(toDual)^{-1} L, v> = L v.
 - With w := grad zeta(x'), TA(b) gives |Phi(x) - phi(x)| <= |p_x - P|^2 ||w|| <= M |p_x - P|^2.
10. Integration of the comparison.
 - Phi - phi is a.e. strongly measurable (phi is Borel: gradients are Borel by measurable_fderiv, a is continuous, the inner product is continuous) and dominated on Gamma' by M |p_x - P|^2. So it is integrable on Gamma' (Integrable.mono'), and phi = Phi - (Phi - phi) is integrable on Gamma'.
 - Hence |int_{Gamma'} Phi - int_{Gamma'} phi| = |int_{Gamma'} (Phi - phi)| <= int_{Gamma'} M |p_x - P|^2 dmu <= M int_{B_sigma(0)} |p_x - P|^2 dmu, by norm_integral_le_of_norm_le and then setIntegral_mono_set (the integrand is nonnegative and Gamma' lies in B_sigma(0)).
11. Conclusion. By steps 5 and 6, int_{Gamma'} Phi = int_B Phi - int_{(B \ Gamma') \ Gamma} Phi. So
 |int_{Gamma'} phi dmu| <= |int_B Phi| + |int_{(B \ Gamma') \ Gamma} Phi| + |int_{Gamma'} Phi - int_{Gamma'} phi|
  <= M (sigma/4) int_B ||H|| dmu + M mu(B cap (spt V \ Gamma)) + M int_{B_sigma(0)} |p_x - P|^2 dmu,
 by steps 4, 7 and 10. This is the claim. QED

## Key steps

1. FV: |int_{B_{sigma/2}} Phi dmu| <= M (sigma/4) int |H| dmu for Phi = <p_x e'_j, p_x q(grad zeta(a x), 0)>.
2. Split B_{sigma/2} into Gamma' = F(B°_{sigma/4}), (B \ Gamma') cap Gamma (where Phi = 0, since grad zeta(a x) = 0) and (B \ Gamma') \ Gamma (where |Phi| <= M, measure <= mu(B cap (spt V \ Gamma))).
3. Non-differentiability points of f map to an H^n-null, hence mu-null, set (AREA + Rademacher).
4. mu-a.e. on Gamma', p_x is the graph plane of Df(a x), so TA(b) gives |Phi - phi| <= M |p_x - P|^2.
5. Integrate: |int_{Gamma'} phi| <= |int_B Phi| + |off-graph part| + M int_{B_sigma} |p_x - P|^2.

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
