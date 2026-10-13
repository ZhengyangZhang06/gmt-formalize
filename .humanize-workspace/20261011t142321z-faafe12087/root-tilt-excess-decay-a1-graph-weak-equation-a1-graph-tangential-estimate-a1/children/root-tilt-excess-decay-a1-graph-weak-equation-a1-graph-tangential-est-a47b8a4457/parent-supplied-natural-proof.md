# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1.tangent_proj_integrands-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This child is step 1(iii) and step 3 of the proof of gwe_graph_tangential_estimate. The parent applies (b1) with S = B_{sigma/2}(0), e = e'_j, g(x) = q(graphPoint (grad zeta(a(x))) 0) and C = M. It applies (b2) with S = B_sigma(0) and T = rotatedPlane q. No extra import is needed.

Notation. e_i := EuclideanSpace.single i 1 for i in Fin(n + l); these vectors have norm 1. For a linear subspace T, P_T := T.starProjection. hsNormSq A = sum_i ||A e_i||^2.

1. Proof of (a). By the definition of V.tangentProj, p_x is either K.starProjection for some linear subspace K (the subspace chosen by Classical.choose when an approximate tangent space exists) or the zero map.
 - In the first case ||K.starProjection|| <= 1 (Submodule.starProjection_norm_le). Hence ||p_x v|| <= ||p_x|| ||v|| <= ||v|| (ContinuousLinearMap.le_opNorm).
 - In the second case p_x v = 0, and ||0|| = 0 <= ||v||.
2. For (b), assume that x |-> p_x is mu-a.e. strongly measurable, and let mu(S) < infinity.
3. (b1), measurability. Consider Psi(L, w) := <L e, L w> on (R^{n+l} ->L R^{n+l}) x R^{n+l}.
 - (L, w) |-> L e and (L, w) |-> L w are continuous, since evaluation of continuous linear maps is jointly continuous (Continuous.clm_apply).
 - The inner product is continuous, so Psi is continuous.
 - Both x |-> p_x and g are mu-a.e. strongly measurable. Hence x |-> Psi(p_x, g(x)) = <p_x e, p_x g(x)> is mu-a.e. strongly measurable (Continuous.comp_aestronglyMeasurable₂).
4. (b1), bound. For every x, |<p_x e, p_x g(x)>| <= ||p_x e|| ||p_x g(x)|| <= ||e|| ||g(x)|| <= ||e|| C. This uses Cauchy-Schwarz (abs_real_inner_le_norm), then (a) twice, then the hypothesis on g.
5. (b1), integrability. A mu-a.e. strongly measurable function that is bounded by a constant on a set of finite mu-measure is integrable on that set (Measure.integrableOn_of_bounded with mu(S) != infinity and the constant ||e|| C).
6. (b2), measurability.
 - A |-> hsNormSq(A) = sum_i ||A e_i||^2 is continuous on R^{n+l} ->L R^{n+l}: it is a finite sum of squares of norms of the continuous evaluations A |-> A e_i.
 - x |-> p_x - P_T is mu-a.e. strongly measurable (a measurable map minus a constant).
 - Hence x |-> hsNormSq(p_x - P_T) is mu-a.e. strongly measurable (Continuous.comp_aestronglyMeasurable).
7. (b2), bound. hsNormSq(p_x - P_T) >= 0, as a sum of squares. Fix i.
 - ||p_x e_i|| <= ||e_i|| = 1 by (a).
 - ||P_T e_i|| <= ||P_T|| ||e_i|| <= 1 (Submodule.starProjection_norm_le).
 - So ||(p_x - P_T) e_i|| <= ||p_x e_i|| + ||P_T e_i|| <= 2.
 Hence 0 <= hsNormSq(p_x - P_T) <= sum_i 2^2 = 4(n + l) for every x.
8. (b2), integrability. As in step 5, with the constant 4(n + l). QED

## Key steps

1. (a): p_x is a starProjection (operator norm <= 1, starProjection_norm_le) or 0, so ||p_x v|| <= ||v||.
2. (b1): (L, w) |-> <L e, L w> is continuous, so x |-> <p_x e, p_x g(x)> is a.e. strongly measurable (Continuous.comp_aestronglyMeasurable₂); it is bounded by ||e|| C by Cauchy-Schwarz and (a); integrable on S by Measure.integrableOn_of_bounded.
3. (b2): hsNormSq is continuous, so x |-> hsNormSq(p_x - P_T) is a.e. strongly measurable; 0 <= it <= 4(n + l) since ||(p_x - P_T) e_i|| <= 2; integrable on S by Measure.integrableOn_of_bounded.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean (both identical)`
- `cat <snapshot>/manifest.json; git -C lake-packages-25730c7c/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^abbrev EuclideanSpace.finAddEquivProd|^theorem measurableSet_of_differentiableAt|^theorem measurable_fderiv |^theorem ae_differentiableWithinAt_of_mem |^theorem norm_fderiv_le_of_lipschitzOn|^theorem support_fderiv_subset|theorem toDual_symm_apply|^theorem integral_inter_add_sdiff|^theorem setIntegral_eq_zero_of_forall_eq_zero|^theorem norm_setIntegral_le_of_norm_le_const |^theorem setIntegral_mono_set|^theorem Integrable.mono' |theorem starProjection_norm_le|^theorem withDensity_absolutelyContinuous|^theorem restrict_apply₀' |^theorem setLIntegral_measure_zero|^theorem setLIntegral_one|^theorem measure_eq_zero_iff_ae_notMem|^theorem Measurable.inner |^theorem withDensity_apply |^theorem restrict_restrict |^theorem norm_integral_le_of_norm_le |^theorem integral_sub |^theorem ContDiff.continuous_fderiv |^theorem IsCompact.image_of_continuousOn|^theorem Continuous.clm_apply|^theorem IsCompact.measurableSet' <snapshot>/mathlib/Mathlib`
- `rg -n 'lemma measure_compl_support|theorem _root_.Continuous.comp_aestronglyMeasurable₂|theorem absolutelyContinuous_of_le|theorem continuous_inner|integrableOn_of_bounded|lemma norm_single' <snapshot>/mathlib/Mathlib`
- `rg -c 'gte_' <snapshot>/project/GMT (no match)`
- `rg -l -i varifold <snapshot>/mathlib/Mathlib (0 files)`
- `python3 -I: dag.json lean_name census for prefix gte_ (0 of 465) and scan of every nodes/**/*.json for the five proposed names (0 hits)`
- `python3 -I: regex scan of dag.json lean_statements (accepted nodes) for V.weight finiteness / null complement of support / absolute continuity / DifferentiableAt / gradient (fun y => f y j) / finAddEquivProd (q.symm patterns`
- `sed -n 520,640p verifier/gmt-compare.py (contract_scope / child_modules); python3 -I scripts/gen_checks.py verifier/gmt-compare.py GMT/Ch05/Contract.lean out/children.json checks`
- `lean -o /tmp/gte-decomp-20261012/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (contract-only); lean checks/challenge/<X>.lean for all 5 children`
- `lean proofs/Child{A,B,C,D,E}.lean; lean -o olean_test/GMT/Ch05/Submission.olean testsub/GMT/Ch05/Submission.lean; lean checks/sol_<X>.lean (#print axioms HumanizeNodeComparator.target, Submission.<X>)`
- `lean checks/Assembly.lean (#print axioms parent_check); lean checks/Wiring.lean (#print axioms wiring_check)`
- `grep -n '4.5 Theorem|(8)|(12)' book/chapter-05.txt; sed -n 800,900p book/chapter-05.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tangential-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-varifold-graph-transfer-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/SpecialFunctions/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Continuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/gte-decomp-20261012/out/children.json`
- `/tmp/gte-decomp-20261012/proofs/ChildA.lean`
- `/tmp/gte-decomp-20261012/proofs/ChildB.lean`
- `/tmp/gte-decomp-20261012/proofs/ChildC.lean`
- `/tmp/gte-decomp-20261012/proofs/ChildD.lean`
- `/tmp/gte-decomp-20261012/proofs/ChildE.lean`
- `/tmp/gte-decomp-20261012/checks/Assembly.lean`
- `/tmp/gte-decomp-20261012/checks/Wiring.lean`
- `/tmp/gte-decomp-20261012/testsub/GMT/Ch05/Submission.lean`

Revisions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The compiling lake-packages-25730c7c/mathlib is at the same commit. The snapshot Contract.lean, the workspace Contract.lean and the workspace Submission.lean are byte-identical.

Mathlib facts used by the five children and the assembly, located in the snapshot (path:line):
- EuclideanSpace.finAddEquivProd (Analysis/InnerProductSpace/PiL2.lean:378).
- Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:202; needs HereditarilyLindelofSpace).
- measurableSet_of_differentiableAt and measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:372, 378; arbitrary f, complete target).
- LipschitzOnWith.ae_differentiableWithinAt_of_mem (Analysis/Calculus/Rademacher.lean:361).
- norm_fderiv_le_of_lipschitzOn (Analysis/Calculus/FDeriv/Basic.lean:939).
- support_fderiv_subset (Analysis/Calculus/FDeriv/Const.lean:379).
- InnerProductSpace.toDual_symm_apply (Analysis/InnerProductSpace/Dual.lean:178).
- In MeasureTheory/Integral/Bochner/Set.lean: integral_inter_add_sdiff (:114), setIntegral_eq_zero_of_forall_eq_zero (:357), norm_setIntegral_le_of_norm_le_const (:613, returns C * mu.real s) and setIntegral_mono_set (:737).
- integral_sub and norm_integral_le_of_norm_le (Bochner/Basic.lean:263, 985).
- Integrable.mono' (Function/L1Space/Integrable.lean:104).
- Measure.integrableOn_of_bounded (Integral/IntegrableOn.lean:716).
- Continuous.comp_aestronglyMeasurable₂ (StronglyMeasurable/AEStronglyMeasurable.lean:263).
- Submodule.starProjection_norm_le (InnerProductSpace/Projection/Basic.lean:386).
- withDensity_apply and withDensity_absolutelyContinuous (Measure/WithDensity.lean:44, 146).
- absolutelyContinuous_of_le (Measure/AbsolutelyContinuous.lean:56).
- restrict_apply₀' and restrict_restrict (Measure/Restrict.lean:136, 205).
- setLIntegral_one and setLIntegral_measure_zero (Integral/Lebesgue/Basic.lean:124, 478).
- measure_eq_zero_iff_ae_notMem (OuterMeasure/AE.lean:145).
- continuous_inner (InnerProductSpace/Continuous.lean:65).
- Continuous.clm_apply (Normed/Operator/BoundedLinearMaps.lean:471).
- IsCompact.image_of_continuousOn (Topology/Compactness/Compact.lean:110).
- IsCompact.measurableSet (Constructions/BorelSpace/Basic.lean:262).
- ContDiff.continuous_fderiv (Calculus/ContDiff/Defs.lean:1271).
- PiLp.norm_single (Normed/Lp/PiLp.lean:1044).
Measurable.inner (Function/SpecialFunctions/Inner.lean:24) exists, but the contract does not import it, so the assembly uses continuous_inner.measurable instead.

No-match results.
- Snapshot Mathlib has no varifold file (0 matches). Varifold facts must be proved from the contract definitions; gte_weight_null_finite and gte_tangentProj_integrands do this.
- No 'gte_' occurs in the snapshot project sources, in the live dag.json (465 names) or in any nodes/**/*.json. All five names are free.
- No accepted DAG declaration states any child as a whole. Partial overlaps are lip_approx_tangent_structure (b2 on compact sets, n >= 1), rsod_graphPoint_eq_finAddEquivProd_symm and arp_rotatedPlane_graphPoint_coords (graphPoint = finAddEquivProd.symm), and anyrad_gc_graph_lintegral_transfer (Borel graph images). These are recorded in the rationale; no reuse edge is needed.

Lean evidence, against a freshly compiled contract-only Submission olean.
- All five verifier-generated challenges elaborate.
- All five children are proved sorry-free.
- The verifier-generated NodeSolution files elaborate against a test Submission containing the proofs.
- parent_check derives the exact frozen parent type from the frozen types of FV, TA, AREA, GC and the five children, and wiring_check connects it to the real Submission.X theorems.
- All of these use only propext, Classical.choice and Quot.sound.
- An independent reviewer reproduced every check.

Source: Simon's proof of Theorem 4.5, displays (8)-(12), is at book/chapter-05.txt:847-888.
