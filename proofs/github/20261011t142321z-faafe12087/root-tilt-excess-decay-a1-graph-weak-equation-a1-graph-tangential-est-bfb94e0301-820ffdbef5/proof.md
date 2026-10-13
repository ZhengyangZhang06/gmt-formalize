# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1.lipschitz_ball_calculus-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This child is the first bullet of step 8 and the second and third bullets of step 9 of the proof of gwe_graph_tangential_estimate. The parent applies it with K = 1 and R = sigma/2. No extra import is needed.

Notation. B := B^n_R(0) is the closed ball and B° := B°^n_R(0) the open ball. D := {x in R^n : f is differentiable at x}, so Z = B° cap D^c. For j in Fin l, pi_j := EuclideanSpace.proj j : R^l -> R is the j-th coordinate map. It is continuous and linear, and f^j = pi_j o f.

1. Proof of (i). For an arbitrary map f from a normed space with its Borel structure into a complete normed space, the set of differentiability points is Borel (measurableSet_of_differentiableAt). No continuity of f and no finite dimension are needed; R^l is complete. So D is Borel, and so is D^c. The open ball B° is Borel. Hence Z = B° cap D^c is Borel.
2. Proof of (ii).
 - B° is contained in B, so f is K-Lipschitz on B° (LipschitzOnWith.mono).
 - By Rademacher's theorem (LipschitzOnWith.ae_differentiableWithinAt_of_mem, for Lebesgue measure on R^n, an additive Haar measure): for L^n-a.e. x, if x is in B° then f is differentiable within B° at x.
 - B° is open, so it is a neighbourhood of each of its points. So differentiability within B° at x is differentiability at x (DifferentiableWithinAt.differentiableAt).
 - Hence for L^n-a.e. x we have x not in Z: if x were in Z, then x would be in B°, f would be differentiable at x, and x would be in D. By measure_eq_zero_iff_ae_notMem, L^n(Z) = 0.
3. Proof of (iii), derivative bound. Let x be in B°. The open ball B° is a neighbourhood of x and lies in B, so B is a neighbourhood of x (mem_of_superset). A map that is K-Lipschitz on a neighbourhood of x satisfies ||fderiv R f x|| <= K (norm_fderiv_le_of_lipschitzOn). This needs no differentiability: if f is not differentiable at x, then fderiv R f x = 0.
4. Proof of (iii), gradient rows. Assume f is differentiable at x, and fix j and v.
 - pi_j is continuous linear, so it is its own derivative everywhere. By the chain rule (HasFDerivAt.comp), f^j = pi_j o f has derivative pi_j o Df(x) at x. Hence fderiv R f^j x = pi_j composed with Df(x).
 - By definition gradient f^j x = (toDual R R^n)^{-1}(fderiv R f^j x).
 - For every continuous linear functional L, <(toDual)^{-1} L, v> = L v (InnerProductSpace.toDual_symm_apply).
 Hence <grad f^j(x), v> = pi_j(Df(x) v) = (Df(x) v)_j. QED

## Key steps

1. (i): {x | DifferentiableAt R f x} is Borel (measurableSet_of_differentiableAt), so Z = ball cap its complement is Borel.
2. (ii): Rademacher (LipschitzOnWith.ae_differentiableWithinAt_of_mem) on the open ball, where differentiability within the ball equals differentiability; so a.e. x is not in Z and L^n(Z) = 0.
3. (iii): B_R(0) is a neighbourhood of every point of the open ball, so ||fderiv R f x|| <= K (norm_fderiv_le_of_lipschitzOn).
4. (iii): f^j = proj_j o f, so by the chain rule fderiv f^j x = proj_j o Df(x); <(toDual)^{-1} L, v> = L v gives <grad f^j(x), v> = (Df(x) v)_j.

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
