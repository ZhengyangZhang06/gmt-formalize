# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This is Simon 4.5 (14)-(16) (steps 8-9 of the parent proof) in the parameter domain. W plays the role of J_F theta(F) 1_M(F), and its hypotheses are exactly what the parent derives. The parent applies it with K0 := K_b + l + 2 and cJ := exp(n/2)/2, and takes the resulting C.

Constants. omega_n := volume of the unit ball of R^n, so L^n(B°_r(0)) = omega_n r^n (EuclideanSpace.volume_ball; any bound L^n(B°_r(0)) <= c_n r^n also works). Put C_E := (1 + n) K0 and
 C := max{C_E, 2 K0 + 2 cJ C_E, sqrt(omega_n C_E), 1}.
Then C > 0. The choice of C uses only n, K0 and cJ, so C is fixed once n, l, K0 and cJ are fixed and before sigma, kappa, E, h, f and W are chosen, exactly as the quantifier order of the statement (and of the Lean type, where l is bound before the existential C) requires.
Notation. B1 := B°_{3 sigma/8}(0), B2 := B°_{sigma/4}(0), N := B1 cap {W = 0}, |Df|^2 := hsNormSq(Df), f^j(y) := f y j. Integrals over B1, B2 are with respect to L^n.

1. Derivative facts. For x in B°_{sigma/2}(0):
 - ||Df(x)|| <= 1 (norm_fderiv_le_of_lipschitzOn, since B_{sigma/2}(0) is a neighbourhood of x). Hence |Df(x)|^2 = sum_i ||Df(x) e_i||^2 <= n.
 - f^j is 1-Lipschitz on B_{sigma/2}(0) (|y_j| <= ||y||), so ||grad f^j(x)|| = ||D f^j(x)|| <= 1.
 By Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem; interior points), f is differentiable at a.e. x in B°_{sigma/2}(0). At such x, D f^j(x) = (EuclideanSpace.proj j) o Df(x), so ||grad f^j(x)||^2 = sum_i (Df(x) e_i)_j^2 <= |Df(x)|^2.
 Df, grad f^j and grad zeta are Borel (measurable_fderiv), and grad zeta is continuous.
2. Integrability. From (H1) and step 1, 0 <= W <= (1 + kappa)(1 + cJ n) a.e. on B1. So |Df|^2, |Df|^2 W, <grad f^j, grad zeta> and <grad f^j, grad zeta> W are bounded and measurable on the finite-measure balls B1, B2, hence integrable there. Their Bochner integrals equal the toReal of the corresponding lintegrals for nonnegative integrands (ofReal_integral_eq_lintegral_ofReal).
3. Energy bound. For a.e. x in B1: |Df(x)|^2 <= |Df(x)|^2 W(x) + n 1_N(x).
 - If W(x) = 0, then x is in N and |Df(x)|^2 <= n.
 - Otherwise W(x) >= 1 by (H1), and |Df|^2 <= |Df|^2 W.
 Integrating (lintegrals, then toReal) and using (H3), (H2):
 int_{B1} |Df|^2 <= int_{B1} |Df|^2 W + n L^n(N) <= K0 E sigma^n + n K0 E sigma^n = C_E E sigma^n <= C E sigma^n.
 This is the first conclusion.
4. Weak equation: setup. Fix zeta, M, j as in the statement with |int_{B2} u W| <= K0 (E + h) M sigma^n, where u := <grad f^j, grad zeta>. Then M >= ||grad zeta(0)|| >= 0, and |u| <= ||grad f^j|| M <= M on B2 (step 1). By step 2,
 int_{B2} u = int_{B2} u W + int_{B2} u (1 - W).
5. Pointwise bound for a.e. x in B2 (a subset of B1):
 |u(x)| |1 - W(x)| <= M 1_N(x) + M kappa ||grad f^j(x)|| + 2 cJ M |Df(x)|^2.
 - If W(x) = 0: |u||1 - W| = |u| <= M = M 1_N(x).
 - If W(x) >= 1: 0 <= W - 1 <= (1 + kappa)(1 + cJ|Df|^2) - 1 = kappa + (1 + kappa) cJ |Df|^2 <= kappa + 2 cJ |Df|^2 (kappa <= 1). So |u||W - 1| <= M ||grad f^j|| (kappa + 2 cJ |Df|^2) <= M kappa ||grad f^j|| + 2 cJ M |Df|^2, using ||grad f^j|| <= 1.
6. Integrating step 5 over B2:
 |int_{B2} u (1 - W)| <= int_{B2} |u||1 - W| <= M L^n(N) + M kappa int_{B2} ||grad f^j|| + 2 cJ M int_{B2} |Df|^2.
 - L^n(N) <= K0 E sigma^n by (H2).
 - int_{B2} |Df|^2 <= int_{B1} |Df|^2 <= C_E E sigma^n by step 3.
 - Cauchy-Schwarz (Hoelder with p = q = 2, e.g. integral_mul_le_Lp_mul_Lq_of_nonneg with the constant 1) and step 1 (||grad f^j||^2 <= |Df|^2 a.e.):
  int_{B2} ||grad f^j|| <= L^n(B2)^{1/2} (int_{B2} |Df|^2)^{1/2} <= (omega_n (sigma/4)^n)^{1/2} (C_E E sigma^n)^{1/2} <= sqrt(omega_n C_E) sigma^n sqrt(E),
  since (sigma/4)^n sigma^n <= sigma^{2n}.
7. Conclusion. Combining step 4, the hypothesis on int_{B2} u W, and step 6:
 |int_{B2} u| <= K0 (E + h) M sigma^n + M K0 E sigma^n + M kappa sqrt(omega_n C_E) sigma^n sqrt(E) + 2 cJ M C_E E sigma^n
  = M sigma^n [(2 K0 + 2 cJ C_E) E + K0 h + sqrt(omega_n C_E) kappa sqrt(E)]
  <= C (E + h + kappa sqrt(E)) M sigma^n,
 since K0 <= 2 K0 + 2 cJ C_E <= C, sqrt(omega_n C_E) <= C and all terms are nonnegative (E, h, kappa, M, sigma^n >= 0). QED

## Key steps

1. On B°_{sigma/2}: ||Df|| <= 1, |Df|^2 <= n, ||grad f^j|| <= 1, and ||grad f^j||^2 <= |Df|^2 a.e. (Rademacher).
2. Energy: a.e. |Df|^2 <= |Df|^2 W + n 1_{W=0}, so int |Df|^2 <= K0 E sigma^n + n K0 E sigma^n.
3. Weak equation: int u = int u W + int u(1 - W), with |u||1 - W| <= M 1_{W=0} + M kappa |grad f^j| + 2 cJ M |Df|^2 a.e.
4. Cauchy-Schwarz: int_{B°_{sigma/4}} |grad f^j| <= sqrt(omega_n C_E) sigma^n sqrt(E).
5. Collect terms: C = max{(1+n)K0, 2K0 + 2cJ(1+n)K0, sqrt(omega_n (1+n) K0), 1}, chosen after n, l, K0, cJ and before sigma, kappa, E, h, f, W.

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
