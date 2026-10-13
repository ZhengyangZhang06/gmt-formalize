# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1`
- Child DAG node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.weighted_energy_weak_equation-a1.set_integral_cauchy_schwarz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Context. This is the Cauchy-Schwarz (Hoelder, p = q = 2) inequality used in step 6 of the parent proof, stated on an abstract finite-measure set. The parent applies it with S = B°_{sigma/4}(0), g = ||grad f^j|| and D = |Df|^2.

Notation. nu := mu restricted to S. Then int_S h dmu = int h dnu, and nu(X) = mu(S).

1. nu is a finite measure, because nu(X) = mu(S) < infinity.
2. g^2 is nu-integrable. It is a.e.-strongly measurable, being a power of the a.e.-strongly measurable g. Also |g(x)^2| = g(x)^2 <= D(x) for nu-a.e. x, with D nu-integrable (Integrable.mono').
3. L^2 membership.
 - For an a.e.-strongly measurable g, g is in L^2(nu) iff x -> ||g(x)||^2 is nu-integrable (integrable_norm_rpow_iff with p = 2). Since ||g(x)||^2 = g(x)^2, which is integrable by step 2, g is in L^2(nu).
 - The constant function 1 is in L^2(nu), because nu is finite (memLp_const).
4. Hoelder. The exponents p = q = 2 are conjugate (Real.HolderConjugate.two_two). Apply integral_mul_le_Lp_mul_Lq_of_nonneg to the nu-a.e. nonnegative functions g (by hypothesis) and 1:
 int g dnu = int g * 1 dnu <= (int g^2 dnu)^{1/2} (int 1^2 dnu)^{1/2} = (int g^2 dnu)^{1/2} ((mu S).toReal)^{1/2}.
5. Monotonicity.
 - g^2 <= D nu-a.e. and both are nu-integrable, so int g^2 dnu <= int D dnu (integral_mono_ae).
 - int g^2 dnu >= 0 and t -> t^{1/2} is monotone on [0, infinity), so (int g^2 dnu)^{1/2} <= (int D dnu)^{1/2}.
 - Also ((mu S).toReal)^{1/2} >= 0.
6. Conclusion. Combine steps 4 and 5 and use t^{1/2} = sqrt(t) (Real.sqrt_eq_rpow):
 int_S g dmu <= (int_S D dmu)^{1/2} ((mu S).toReal)^{1/2} = sqrt((mu S).toReal) * sqrt(int_S D dmu). QED

## Key steps

1. The restriction nu = mu|_S is finite. g^2 <= D a.e. with D integrable makes g^2 integrable, so g is in L^2(nu) (integrable_norm_rpow_iff), and so is the constant 1.
2. Hoelder with p = q = 2 (integral_mul_le_Lp_mul_Lq_of_nonneg, Real.HolderConjugate.two_two) for g and 1: int_S g <= (int_S g^2)^{1/2} ((mu S).toReal)^{1/2}.
3. int_S g^2 <= int_S D (integral_mono_ae), then monotonicity of t^{1/2} on [0, infinity); rewrite t^{1/2} = sqrt t.

## Reference use

### local-project

Queries:
- `cmp GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean; cmp GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean (both identical); cat <snapshot>/manifest.json`
- `python3 -I over dag.json: status census; selected node (depth 3, decomposing) and its siblings; regex over all lean_names for hsnorm|lipsch|fderiv|grad|energy|weak|coord|deriv|holder; printed lean_statements of accepted lgc_hsNormSq_bounds, arp_opNorm_le_hsNorm, allard52_gpa_hsNorm_bounds, any_radius_gr_la_hsNorm_facts, tdo_slb_setLIntegral_rpow_le_holder, tdo_ods_hsNormSq_fderiv_single`
- `python3 -I: parent node decomposition-v1.json subproblem list (how identical-type reuse was encoded)`
- `grep -c 'gwe_wewe' and each proposed name in dag.json; grep -rl over nodes/, <snapshot>/project, GMT/, .lake/packages/simongmt/Poincare (no match)`
- `grep -n 'theorem ae_differentiableWithinAt_of_mem' Analysis/Calculus/Rademacher.lean; 'theorem norm_fderiv_le_of_lipschitzOn' Analysis/Calculus/FDeriv/Basic.lean; 'measurable_fderiv' Analysis/Calculus/FDeriv/Measurable.lean; 'def gradient|toDual_gradient' Analysis/Calculus/Gradient/Basic.lean; 'abbrev StrongDual' Topology/Algebra/Module/ContinuousLinearMap/Basic.lean; 'theorem norm_apply_le' Analysis/Normed/Lp/PiLp.lean; 'norm_sq_eq|finrank_euclideanSpace_fin' Analysis/InnerProductSpace/PiL2.lean (all under <snapshot>/mathlib/Mathlib)`
- `grep -n 'integral_mul_le_Lp_mul_Lq_of_nonneg|integral_eq_lintegral_of_nonneg_ae|abs_integral_le_integral_abs' MeasureTheory/Integral/Bochner/Basic.lean; 'memLp_two_iff_integrable_sq' MeasureTheory/Function/L2Space.lean; 'integrable_norm_rpow_iff' MeasureTheory/Function/L1Space/Integrable.lean; 'two_two' Basic/Real/ConjExponents.lean; 'addHaar_ball_of_pos' MeasureTheory/Measure/Lebesgue/EqHaar.lean; 'volume_ball' MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean; 'setIntegral_mono_set|integral_indicator_const' MeasureTheory/Integral/Bochner/Set.lean; 'measureReal_restrict_apply' MeasureTheory/Measure/Real.lean; 'Measure.integrableOn_of_bounded' MeasureTheory/Integral/IntegrableOn.lean; 'lintegral_indicator_const|lintegral_mono_ae' MeasureTheory/Integral/Lebesgue/Basic.lean; 'lintegral_add_right' MeasureTheory/Integral/Lebesgue/Add.lean; 'measure_ball_lt_top' MeasureTheory/Measure/Typeclasses/Finite.lean; 'toReal_le_of_le_ofReal' Basic/ENNReal/Real.lean`
- `sed -n 419,640p verifier/gmt-compare.py (load_statement_validator, child_contract, contract_scope, child_modules); grep -n -A80 'def validate_lean_statement' verifier/lean_contract.py`
- `grep -n '4.5 Theorem|(14)|(15)|(16)' book/chapter-05.txt; sed -n 880,935p book/chapter-05.txt`
- `lean -o /tmp/wewe-decomp-20261012/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean (contract-only)`
- `python3 -I /tmp/wewe-decomp-20261012/scripts/gen_checks.py verifier/gmt-compare.py verifier/lean_contract.py GMT/Ch05/Contract.lean spec/children.json <selected handoff> checks`
- `lean checks/challenge/*.lean (4 children + parent); lean checks/TypesSubmission.lean; lean checks/TypesPrint.lean (#check elaborated forms)`
- `lean checks/Assembly.lean (#print axioms parent_check)`
- `lean validate/Child1.lean, validate/Child3.lean, validate/Child12.lean, validate/Child124.lean, validate/FullProof.lean (#print axioms for each child, Submission.gwe_weighted_energy_weak_equation and HumanizeNodeComparator.target)`
- `python3 -I byte-identity check of proved/assembled statements against spec/children.json and the handoff lean_statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-c7907a608e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-c7907a608e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-weighted-energy-weak-c7907a608e/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/Real/ConjExponents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/wewe-decomp-20261012/spec/children.json`
- `/tmp/wewe-decomp-20261012/scripts/gen_checks.py`
- `/tmp/wewe-decomp-20261012/checks/TypesSubmission.lean`
- `/tmp/wewe-decomp-20261012/checks/TypesPrint.lean`
- `/tmp/wewe-decomp-20261012/checks/Assembly.lean`
- `/tmp/wewe-decomp-20261012/checks/challenge/gwe_weighted_energy_weak_equation.lean`
- `/tmp/wewe-decomp-20261012/checks/challenge/gwe_wewe_lipschitz_fderiv_facts.lean`
- `/tmp/wewe-decomp-20261012/checks/challenge/gwe_wewe_energy_bound.lean`
- `/tmp/wewe-decomp-20261012/checks/challenge/gwe_wewe_setIntegral_le_sqrt_mul_sqrt.lean`
- `/tmp/wewe-decomp-20261012/checks/challenge/gwe_wewe_weight_error_bound.lean`
- `/tmp/wewe-decomp-20261012/validate/Child1.lean`
- `/tmp/wewe-decomp-20261012/validate/Child3.lean`
- `/tmp/wewe-decomp-20261012/validate/Child12.lean`
- `/tmp/wewe-decomp-20261012/validate/Child124.lean`
- `/tmp/wewe-decomp-20261012/validate/FullProof.lean`

Revisions. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Compilation used lake-packages-25730c7c (mathlib 25730c7c, simongmt 2b366308) with the pinned Lean v4.35.0-rc3 toolchain.

DAG. The selected node is at depth 3 with status decomposing; max_depth is 6, so splitting is allowed. Its siblings carry gwe_* names. 'gwe_wewe' occurs nowhere in dag.json, in any node file, or in the project, GMT or simongmt sources, so the four proposed names are globally unique.

Reuse considered. Accepted lgc_hsNormSq_bounds (hsNormSq A <= m ||A||^2, continuity) and tdo_slb_setLIntegral_rpow_le_holder (lintegral Hoelder) overlap child content. They are not reused: that would add cross-branch dependencies, and the assembly needs a Bochner-form Cauchy-Schwarz.

Mathlib facts confirmed in the snapshot:
- LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361).
- norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939).
- measurable_fderiv (FDeriv/Measurable.lean:378).
- gradient = (toDual).symm o fderiv (Gradient/Basic.lean:83), toDual_gradient (:128).
- StrongDual is an abbrev (ContinuousLinearMap/Basic.lean:96), so measurability instances go through.
- PiLp.norm_apply_le (PiLp.lean:713).
- integral_mul_le_Lp_mul_Lq_of_nonneg (Bochner/Basic.lean:1230).
- Real.HolderConjugate.two_two (ConjExponents.lean:137).
- integrable_norm_rpow_iff (L1Space/Integrable.lean:228).
- Measure.addHaar_ball_of_pos (EqHaar.lean:445).
- EuclideanSpace.volume_ball (VolumeOfBalls.lean:307).
- setIntegral_mono_set (Bochner/Set.lean:737) and integral_indicator_const (:528).
- measureReal_restrict_apply (Measure/Real.lean:102).
- Measure.integrableOn_of_bounded (IntegrableOn.lean:716).
- lintegral_indicator_const (Lebesgue/Basic.lean:541) and lintegral_add_right (Lebesgue/Add.lean:339).
- integral_eq_lintegral_of_nonneg_ae (Bochner/Basic.lean:515) and ENNReal.toReal_le_of_le_ofReal (ENNReal/Real.lean:283).
- No-match: memLp_two_iff_integrable_sq (L2Space.lean:52) and Measurable.inner are not imported by the contract. integrable_norm_rpow_iff and continuous_inner.measurable work instead, and the child proofs cite those.

Source. Simon's (14)-(16) are at book/chapter-05.txt lines 903-925. The supplied proof is their expanded form for an abstract weight W, and the child proofs are extracted from its steps 1-6.

Lean checks:
- All four child comparator challenges and the parent challenge elaborate. They were generated with the verifier's own contract_scope/child_modules and statement validator.
- parent_check proves the exact frozen parent type from the four child propositions, sorry-free, using only propext, Classical.choice and Quot.sound.
- Each child statement was proved sorry-free in scratch. FullProof.lean then proves Submission.gwe_weighted_energy_weak_equation from the four children, and the comparator-style target 'exact Submission.gwe_weighted_energy_weak_equation' passes with standard axioms only.
- All statements are byte-identical to the frozen strings.
