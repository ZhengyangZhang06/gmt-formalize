# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.a_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 of the parent proof (the bound on a); Simon Ch. 4, the estimate between 4.2 and 4.3, which uses a^(1-1/p) <= 1 + a.

0. Exponents. From 1 <= n < p we get p > 1. So gamma := 1 - 1/p satisfies 0 <= gamma <= 1. Also t^n > 0 and t^(n+1) > 0.
1. Normalized mass. Put A := I/t^n >= 0, so I = A t^n. Real powers of nonnegative numbers are multiplicative, so I^gamma = A^gamma (t^n)^gamma = A^gamma t^(n gamma) = A^gamma t^(n - n/p). This uses Real.mul_rpow, Real.rpow_natCast, Real.rpow_mul, and n gamma = n - n/p.
2. Absorption: A^gamma <= 1 + A.
 - If A <= 1, then A^gamma <= 1 <= 1 + A (Real.rpow_le_one, since 0 <= A <= 1 and gamma >= 0).
 - If A >= 1, then A^gamma <= A^1 = A <= 1 + A (Real.rpow_le_rpow_of_exponent_le, since A >= 1 and gamma <= 1).
3. Bound by 2 N t^(-n/p).
 - Put X := t N t^(n - n/p) >= 0. By the hypothesis and step 1, |E| <= (1 + eps) t N I^gamma = (1 + eps) X A^gamma.
 - Since eps <= 1 we have 1 + eps <= 2, and X A^gamma >= 0. With step 2, |E| <= 2 X A^gamma <= 2 X (1 + A).
 - As t > 0, real powers of t add: t * t^(n - n/p) = t^(1 + n - n/p) = t^(-n/p) t^(n+1). So 2 X (1 + A) = 2 N t^(-n/p) (t^(n+1) (1 + A)).
 - Since t^(n+1) > 0 and 1 + A > 0, |E / t^(n+1) / (1 + A)| = |E| / (t^(n+1) (1 + A)) <= 2 N t^(-n/p).
4. Substituting N. As t^(-n/p) > 0 and N <= kappa Lambda R^(n/p - 1), we get 2 N t^(-n/p) <= 2 kappa Lambda R^(n/p - 1) t^(-n/p).
5. Rewriting the right side.
 - Since t, R >= 0, (t/R)^(-n/p) = t^(-n/p)/R^(-n/p) = t^(-n/p) R^(n/p) (Real.div_rpow, Real.rpow_neg).
 - Since R != 0, R^(n/p - 1) = R^(n/p)/R (Real.rpow_sub_one).
 - Hence 2 kappa Lambda R^(n/p - 1) t^(-n/p) = 2 kappa Lambda R^(-1) (t/R)^(-n/p).
 Since 1 + I/t^n = 1 + A, steps 3-5 give the claim. Of the hypotheses Lambda > 0 and 0 < eps <= 1, only eps <= 1 is used; the others match the calling context.

## Key steps

1. With A := I/t^n >= 0, I^(1-1/p) = A^(1-1/p) t^(n - n/p).
2. A^(1-1/p) <= 1 + A, splitting into A <= 1 and A >= 1 (0 <= 1 - 1/p <= 1 since p > 1).
3. Using 1 + eps <= 2: |E| <= 2 N t^(-n/p) t^(n+1) (1 + A), so |E/t^(n+1)/(1 + A)| <= 2 N t^(-n/p).
4. Insert N <= kappa Lambda R^(n/p - 1) and rewrite R^(n/p - 1) t^(-n/p) = R^(-1) (t/R)^(-n/p).

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
