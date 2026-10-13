# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child DAG node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.cutoff_facts-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (cutoff facts). The boundedness of phi' is made explicit because step 3(c) of the parent proof uses it.

1. Bounds on phi. Let u be real.
 - Lower bound: if u >= 1 + eps then phi(u) = 0. If u < 1 + eps then phi(u) >= phi(1 + eps) = 0, since phi is nonincreasing.
 - Upper bound: if u <= 1 then phi(u) = 1. If u > 1 then phi(u) <= phi(1) = 1.
 Hence 0 <= phi(u) <= 1. This is (i).
2. Sign of phi'. phi is nonincreasing, so every difference quotient (phi(v) - phi(u))/(v - u) with v != u is <= 0. phi is differentiable at u (it is C^1), so phi'(u) is a limit of such quotients and phi'(u) <= 0. This is (ii). In Mathlib this is Antitone.deriv_nonpos, which needs no differentiability hypothesis because deriv is 0 at points of non-differentiability.
3. Local constancy.
 - Let u > 1 + eps. The open interval (1 + eps, infinity) is a neighbourhood of u on which phi = 0. So phi agrees near u with the constant function 0, and phi'(u) = 0 (Filter.EventuallyEq.deriv_eq, deriv_const). This is (iii).
 - In the same way, for u < 1, phi = 1 on the neighbourhood (-infinity, 1) of u, so phi'(u) = 0.
4. Continuity. phi is C^1, so phi' = deriv phi is continuous (ContDiff.continuous_deriv with 1 <= 1). This is (iv).
5. Boundedness.
 - By step 3, phi'(u) = 0 whenever u < 1 or u > 1 + eps. So the support of phi' lies in the compact interval [1, 1 + eps].
 - phi' is continuous by step 4. By the extreme value theorem, |phi'| attains a maximum C on [1, 1 + eps], and C >= |phi'(1)| >= 0.
 - For u outside [1, 1 + eps], |phi'(u)| = 0 <= C. Hence |phi'(u)| <= C for every u. This is (v).
 - In Mathlib: HasCompactSupport.of_support_subset_isCompact with isCompact_Icc, then Continuous.bounded_above_of_compact_support, and Real.norm_eq_abs.

## Key steps

1. 0 <= phi <= 1 follows from monotonicity and the boundary values phi(1) = 1 and phi(1 + eps) = 0.
2. phi' <= 0 because phi is nonincreasing (Antitone.deriv_nonpos).
3. phi' = 0 on (1 + eps, infinity) and on (-infinity, 1), where phi is locally constant.
4. phi' is continuous because phi is C^1.
5. phi' is continuous with support in [1, 1 + eps], hence bounded by some C.

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
