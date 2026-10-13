# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.lp_scale-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof (the L^p norm); Simon Ch. 4, 4.2.

0. Constants. Since p > n >= 0, p > 0 and so 1/p > 0. Also p - n > 0, kappa = (p - n)/(4p) > 0 and kappa Lambda > 0. As R > 0, c := R^(p-n) > 0, so ofReal(c) != 0.
1. Q_R is finite.
 - Suppose ofReal(c) * Q_R = infinity. Then (ofReal(c) * Q_R)^(1/p) = infinity^(1/p) = infinity, because 1/p > 0 (ENNReal.top_rpow_of_pos).
 - The hypothesis would then give infinity <= ofReal(kappa Lambda). This is impossible, since ofReal of a real number is finite. Hence ofReal(c) * Q_R != infinity.
 - If Q_R were infinity, then ofReal(c) * Q_R = ofReal(c) * infinity = infinity, because ofReal(c) != 0. So Q_R < infinity.
2. Passing to reals.
 - As Q_R < infinity, Q_R = ofReal(Q_R.toReal). Since c >= 0, ofReal(c) * Q_R = ofReal(c * Q_R.toReal).
 - Since c * Q_R.toReal >= 0 and 1/p >= 0, (ofReal(c * Q_R.toReal))^(1/p) = ofReal((c * Q_R.toReal)^(1/p)) (ENNReal.ofReal_rpow_of_nonneg).
 - Since kappa Lambda >= 0, ofReal(A) <= ofReal(kappa Lambda) is equivalent to A <= kappa Lambda (ENNReal.ofReal_le_ofReal_iff).
 - Hence (c * Q_R.toReal)^(1/p) <= kappa Lambda.
3. Factoring. Put N := (Q_R.toReal)^(1/p) >= 0.
 - Both factors are >= 0, so (c * Q_R.toReal)^(1/p) = c^(1/p) * N (Real.mul_rpow).
 - As R >= 0, c^(1/p) = (R^(p-n))^(1/p) = R^((p-n)(1/p)) = R^(1 - n/p) (Real.rpow_mul). Here (p - n)/p = 1 - n/p because p != 0.
 - So R^(1-n/p) * N <= kappa Lambda.
4. Dividing. R^(1-n/p) > 0, and R^(n/p - 1) = R^(-(1 - n/p)) = 1/R^(1-n/p) (Real.rpow_neg). Hence N <= kappa Lambda / R^(1-n/p) = kappa Lambda R^(n/p - 1).
5. The sub-ball.
 - Since t <= R, closedBall y t is contained in closedBall y R. So Q_t <= Q_R by monotonicity of the lower integral in the domain (lintegral_mono_set). Hence Q_t < infinity.
 - toReal is monotone on finite values (ENNReal.toReal_mono, using Q_R != infinity). So 0 <= Q_t.toReal <= Q_R.toReal.
 - u -> u^(1/p) is nondecreasing on [0, infinity), as 1/p >= 0 (Real.rpow_le_rpow). Hence (Q_t.toReal)^(1/p) <= N <= kappa Lambda R^(n/p - 1).

## Key steps

1. If ofReal(R^(p-n)) Q_R were infinite, its 1/p-th power would be infinite, contradicting the finite bound. Since ofReal(R^(p-n)) != 0, Q_R < infinity.
2. In real numbers the hypothesis reads (R^(p-n) Q_R.toReal)^(1/p) <= kappa Lambda.
3. Factor (R^(p-n))^(1/p) = R^(1 - n/p) and divide: (Q_R.toReal)^(1/p) <= kappa Lambda R^(n/p - 1).
4. For t <= R, Q_t <= Q_R by set monotonicity. So Q_t < infinity and (Q_t.toReal)^(1/p) <= (Q_R.toReal)^(1/p).

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `grep -rn 'allard52_am_fc_' <snapshot>/project (exit 1); grep -rln 'allard52_am_fc_' --include=*.lean <snapshot>/mathlib/Mathlib (exit 1); python3 -I over dag.json: lean_name and lean_statement of every node, including aal_curvature_pairing_holder_bound, allard52_am_cutoff_integral_calculus, allard52_am_integrating_factor, allard52_am_annular_tonelli`
- `grep -rn over <snapshot>/mathlib/Mathlib: 'theorem integral_hasDerivAt_right|theorem norm_integral_le_of_norm_le |theorem integral_rpow |theorem intervalIntegrable_rpow'|theorem ContinuousOn.intervalIntegrable |theorem integral_mono_on |integrable_of_forall_notMem_eq_zero|integrableOn_of_bounded|deriv_nonpos|theorem ContinuousOn.stronglyMeasurableAtFilter |theorem integrableOn_const'; then ContDiff.continuous_deriv, EventuallyEq.deriv_eq, top_rpow_of_pos, ofReal_rpow_of_nonneg, mul_rpow, div_rpow, rpow_le_one, lintegral_mono_set, comp_aestronglyMeasurable₂, Integrable.mono', integral_nonpos_of_ae, intervalIntegrable_iff_integrableOn_Ioc_of_le, 'protected theorem inner' (StronglyMeasurable/Inner.lean)`
- `git show a86f40226e595267d72cfbfaf8d5fdbfa472219b:GMT/Ch05/Submission.lean (accepted aal_curvature_pairing_holder_bound, replayed in FCStubsAx.lean)`
- `toolchains/lean-4.35.0-rc3-linux/bin/lean GMT/Ch05/Submission.lean -o /tmp/fc-decomp-98909e/build/lib/GMT/Ch05/Submission.olean (LEAN_PATH = /tmp/fc-decomp-98909e/build/lib plus lake-packages-25730c7c/*/.lake/build/lib/lean)`
- `LEAN_PATH=<same> lean /tmp/fc-decomp-98909e/check/Stubs.lean, FCStubs.lean, Assembly.lean, EndToEnd.lean, FCStubsAx.lean, EndToEndAx.lean, Types.lean; lean /tmp/fc-decomp-98909e/proofs/C1.lean ... C6.lean`
- `python3 -I /tmp/fc-decomp-98909e/scripts/check_types.py (validate_lean_statement on the six child types; byte comparison of the parent and dependency types with the handoff and dag.json)`
- `sed -n 375,570p book/chapter-04.txt (Simon Ch. 4, 3.16-3.17 and 4.1-4.9)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-98909e56b4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/fc-decomp-98909e/check/Assembly.lean`
- `/tmp/fc-decomp-98909e/check/FCStubsAx.lean`
- `/tmp/fc-decomp-98909e/check/EndToEndAx.lean`
- `/tmp/fc-decomp-98909e/check/Types.lean`
- `/tmp/fc-decomp-98909e/proofs/C1.lean`
- `/tmp/fc-decomp-98909e/proofs/C2.lean`
- `/tmp/fc-decomp-98909e/proofs/C3.lean`
- `/tmp/fc-decomp-98909e/proofs/C4.lean`
- `/tmp/fc-decomp-98909e/proofs/C5.lean`
- `/tmp/fc-decomp-98909e/proofs/C6.lean`
- `/tmp/fc-decomp-98909e/proposal_subproblems.json`

Pins. Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Contract.lean and Submission.lean are byte-identical to the snapshot copies.

Names. allard52_am_fc_cutoff_facts, _lp_scale, _a_bound, _primitive, _ball_integrable and _radial_split occur nowhere in the snapshot project or Mathlib (grep exit 1), and none is reserved in dag.json.

Mathlib. All tools the children need are in the import closure of GMT.Ch05.Submission. Snapshot locations:
- Deriv/Slope.lean:214 Antitone.deriv_nonpos
- ContDiff/Deriv.lean:108 ContDiff.continuous_deriv
- Deriv/Basic.lean:638 Filter.EventuallyEq.deriv_eq
- Pow/NNReal.lean:508 ENNReal.top_rpow_of_pos; :971 ofReal_rpow_of_nonneg
- Pow/Real.lean:476 Real.mul_rpow; :487 Real.div_rpow; :661 Real.rpow_le_one
- Lebesgue/Basic.lean:98 lintegral_mono_set
- Integrability/Basic.lean:47 intervalIntegrable_rpow'
- Integrals/Basic.lean:146 integral_rpow
- FundThmCalculus.lean:725 integral_hasDerivAt_right
- IntervalIntegral/Basic.lean:132 intervalIntegrable_iff_integrableOn_Ioc_of_le; :503 ContinuousOn.intervalIntegrable; :756 norm_integral_le_of_norm_le; :1432 integral_mono_on
- IntegrableOn.lean:119 integrableOn_const; :453 integrable_of_forall_notMem_eq_zero; :716 Measure.integrableOn_of_bounded; :856 ContinuousOn.stronglyMeasurableAtFilter
- AEStronglyMeasurable.lean:263 Continuous.comp_aestronglyMeasurable₂
- L1Space/Integrable.lean:104 Integrable.mono'
- Bochner/Basic.lean:649 integral_nonneg; :653 integral_nonpos_of_ae
AEStronglyMeasurable.inner (StronglyMeasurable/Inner.lean:50) exists in the snapshot but is not in the import closure (Lean: unknown constant). ball_integrable therefore uses continuous_inner.comp_aestronglyMeasurable₂ instead.

Lean checks.
- All six child types elaborate after import GMT.Ch05.Submission and pass validate_lean_statement.
- All six children are fully proved (C1-C6.lean) with only propext, Classical.choice and Quot.sound.
- EndToEndAx.lean proves the exact frozen allard52_am_fixed_cutoff type, byte-identical to the handoff and dag.json. It uses the six children, the accepted Hoelder proof replayed from a86f40226e (its type is byte-identical to dag.json), and cutoff_integral_calculus, integrating_factor and annular_tonelli as axioms whose types are byte-identical to dag.json. #print axioms shows no sorryAx.
- No Matrix/IsUnit or other instance-sensitive inline construction occurs. The inline (fun _ => (1 : ℝ)) and inner ℝ (x - y) (H x) unify with the cutoff_integral_calculus instantiations in the checked assembly.

Source. Simon Ch. 4 (book/chapter-04.txt), 4.2-4.5, matches the children:
- the L^p condition 4.2 (lp_scale);
- the Hoelder estimate with a^(1-1/p) <= 1 + a, giving |F_0| <= 2 kappa Lambda R^(-1)(rho/R)^(-n/p) (a_bound);
- integral_0^rho |F_0| <= (1/2) Lambda (rho/R)^(1-n/p) (primitive);
- the first-variation bookkeeping of 4.1 (radial_split, ball_integrable, cutoff_facts).
