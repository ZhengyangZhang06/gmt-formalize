# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.tangent_identification-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation.
- mu := V.weight, p_y := V.tangentProj y, P_S := S.starProjection, B_s := closedBall zeta s, m_s := mu(B_s), E_s := V.tiltExcess zeta s S.
- a(y) := ofReal(hsNormSq(p_y - p_zeta)) and b(y) := ofReal(hsNormSq(p_y - P_S)).
- Avg_s := m_s^(-1) times the lower integral of a over B_s; this is the quantity in (L).
- (L8) is from la_basics and (T1) from tilt_integrals.

1. Pointwise inequality. D := hsNormSq(p_zeta - P_S) >= 0 by (L8a). For every y, p_zeta - P_S = (-(p_y - p_zeta)) + (p_y - P_S). By (L8c) and (L8d), D <= 2 hsNormSq(p_y - p_zeta) + 2 hsNormSq(p_y - P_S). ofReal is monotone, and ofReal(2s + 2t) = 2 ofReal(s) + 2 ofReal(t) for s, t >= 0. So ofReal(D) <= 2 a(y) + 2 b(y) for every y.

2. Measurability. M -> ofReal(hsNormSq(M - C)) is continuous for fixed C, and y -> p_y is mu-a.e. strongly measurable. So a and b are mu-a.e. measurable.

3. Estimate at a fixed scale. Let 0 < s <= s_0. By hypothesis 0 < ofReal(c s^n) <= m_s < infinity (c > 0, s > 0).
- Integrate step 1 over B_s. The lower integral of a constant is the constant times the measure; the lower integral is additive when one summand is a.e.-measurable; constants factor out. This gives ofReal(D) m_s <= 2 integral_{B_s} a d mu + 2 integral_{B_s} b d mu.
- By (T1) with T = S (using s > 0, m_s < infinity and the a.e. strong measurability of p): integral_{B_s} b d mu = ofReal(s^n E_s).
- Multiply by m_s^(-1); since m_s is in (0, infinity), m_s m_s^(-1) = 1. So ofReal(D) <= 2 Avg_s + 2 m_s^(-1) ofReal(s^n E_s).
- From ofReal(c s^n) <= m_s: m_s^(-1) <= ofReal(c s^n)^(-1) = ofReal((c s^n)^(-1)). Hence m_s^(-1) ofReal(s^n E_s) <= ofReal((c s^n)^(-1)) ofReal(s^n E_s) = ofReal((c s^n)^(-1) s^n E_s) = ofReal(E_s/c).
So for every s in (0, s_0]:
(*) ofReal(D) <= 2 Avg_s + 2 ofReal(E_s/c).

4. Passage to the limit. Let s -> 0+ along the filter of right neighbourhoods of 0.
- Avg_s -> 0 by (L).
- E_s -> 0 by (T); hence E_s/c -> 0 and, by continuity of ofReal, ofReal(E_s/c) -> 0.
- Multiplication by the finite constant 2 and addition are continuous at these finite limits in [0, infinity], so the right side of (*) tends to 0.
(0, s_0] belongs to this filter, so (*) holds eventually, and the filter is nontrivial. Therefore ofReal(D) <= 0, so ofReal(D) = 0 and D <= 0. With D >= 0, D = 0.

5. Conclusion. By (L8e), hsNormSq(p_zeta - P_S) = 0 implies p_zeta - P_S = 0, i.e. V.tangentProj zeta = S.starProjection.

## Key steps

1. D := hsNormSq(p_zeta - P_S) <= 2 hsNormSq(p_y - p_zeta) + 2 hsNormSq(p_y - P_S) for every y
2. Integrate over B_s(zeta); (T1) converts the second integral to ofReal(s^n E_s); divide by mu(B_s(zeta)) >= c s^n
3. ofReal(D) <= 2 Avg_s + 2 ofReal(E_s/c) for all s in (0, s_0]
4. Let s -> 0+: both terms tend to 0, so D = 0 and p_zeta = P_S by (L8e)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; diff GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 -I scan of every lean_name field in dag.json and nodes/*/*.json for the 8 any_radius_gr_* names; grep -rl any_radius_gr_ --include=*.json <run>; git grep -c any_radius_gr_ <ref> -- '*.lean' over all refs; rg -l any_radius_gr_ <snapshot>/project`
- `python3 -I dump of nodes/root-allard-any-radius-a1/decomposition-v2.json (sibling statements tangent_ae, rescaled_varifold, monotonicity_bounds, tilt_height_l1, tilt_iteration, graph_comparison, radial_height, campanato, pinching) and of this node's parent-child-handoff.json, decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json`
- `sed -n 200,210p and sed -n 515,530p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean (integral_undef, integral_eq_lintegral_of_nonneg_ae)`
- `rg -n 'theorem lintegral_mul_le_Lp_mul_Lq' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean; sed -n 195,215p of the same file`
- `rg -n 'eLpNorm_le_eLpNorm_mul_rpow_measure_univ' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `grep -n 'theorem toReal_rpow|theorem ofReal_rpow_of_nonneg|theorem mul_rpow_of_nonneg' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean; grep -n 'ofReal_norm' <snapshot>/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `grep -n 'theorem integral_map_equiv' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean; grep -n 'theorem lintegral_map_equiv' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean; grep -n 'theorem lintegral_mono_set' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `lake build GMT.Ch05.Submission in /tmp/gr-v2-scratch/proj (fresh copy of the pinned snapshot project, packages symlinked to lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean and Checks/TypesV2.lean (the 8 child lean_statements from v1 and from the final v2 draft, plus the selected parent type)`
- `lake env lean Checks/Iface.lean (14 sibling/child interface examples)`
- `lake env lean Checks/LpBall.lean (complete proof of the frozen lp_ball_bounds type; #print axioms)`
- `lake env lean Checks/Names.lean (#check of every Mathlib name cited in the corrected lp_ball_bounds proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/tmp/gr-v2-scratch/proj/Checks/Types.lean`
- `/tmp/gr-v2-scratch/proj/Checks/TypesV2.lean`
- `/tmp/gr-v2-scratch/proj/Checks/Iface.lean`
- `/tmp/gr-v2-scratch/proj/Checks/LpBall.lean`
- `/tmp/gr-v2-scratch/proj/Checks/Names.lean`

Snapshot
- Pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- Snapshot Contract.lean and Submission.lean are byte-identical to the workspace copies, and Submission equals Contract.

Definitions that shape the split
- scaledLpNorm = (ofReal(sigma^(p-n)) * lintegral over closedBall xi sigma of ‖H x‖ₑ^p)^(1/p).
- tiltExcess = (sigma^n)^-1 times a Bochner integral.
- lp_ball_bounds is stated for an arbitrary H (no measurability hypothesis), so its (K2) proof must split on the integrability of f = ‖H‖ itself.

Mathlib facts behind the correction
- integral_undef (Bochner/Basic.lean:204) applies to the actual integrand f.
- integral_eq_lintegral_of_nonneg_ae (:515) needs only 0 <=ᵐ f and AEStronglyMeasurable f.
- ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202) needs AEMeasurable of both factors.
- ENNReal.toReal_rpow (Pow/NNReal.lean:962) is unconditional.
- ofReal_norm replaces the deprecated ofReal_norm_eq_enorm (Normed/Group/Basic.lean:389).
- IntegrableOn.aestronglyMeasurable does not exist; Integrable.aestronglyMeasurable is cited instead.
- Change of variables along a MeasurableEquiv needs no measurability, which supports translate_identities: integral_map_equiv (Bochner/Basic.lean:1105) and lintegral_map_equiv (Lebesgue/Map.lean:94). Neither does lintegral_mono_set (Lebesgue/Basic.lean:98).

No-match results
- 'any_radius_gr_' occurs in 0 snapshot project files and in 0 .lean files on any git branch.
- In dag.json and nodes/*/*.json it occurs only in this node's own v1 proposal, audit and receipt, so the 8 names are free.

Lean
- All 8 frozen child types and the parent type elaborate.
- The full lp_ball_bounds proof compiles with only propext, Classical.choice and Quot.sound.
- The 14 interface examples compile without sorry.
