# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.translate_identities-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. mu := V.weight, mu' := V'.weight = tau_# mu with tau(x) := x - zeta.

1. Change of variables. tau is a bijection of R^(n+l) with inverse x -> zeta + x, and both maps are continuous. So tau is a measurable equivalence for the Borel sigma-algebra (Mathlib's MeasurableEquiv.subRight). For a measurable equivalence, every set S (measurable or not) satisfies:
(a) tau_# mu(S) = mu(tau^(-1)(S));
(b) (tau_# mu) restricted to S equals tau_#(mu restricted to tau^(-1)(S));
(c) for every measure nu and every function phi, lower integral of phi d(tau_# nu) = lower integral of phi o tau d nu, and likewise for Bochner integrals. No measurability or integrability assumptions are needed along a measurable equivalence.
Combining (b) and (c): the integral of phi over S w.r.t. mu' equals the integral of phi o tau over tau^(-1)(S) w.r.t. mu, for both lower and Bochner integrals.

2. tau^(-1)(B_s(0)) = {y : |y - zeta| <= s} = B_s(zeta) for every real s (both empty for s < 0).

3. (R1). mu'(B_s(0)) = mu(tau^(-1) B_s(0)) = mu(B_s(zeta)) by 1(a) and 2.

4. (R2). By definition and the hypothesis on V'.tangentProj, V'.tiltExcess 0 s T = (s^n)^(-1) times the Bochner integral over B_s(0) of phi d mu', where phi(x) := hsNormSq(V.tangentProj(zeta + x) - P_T). By steps 1 and 2 this equals (s^n)^(-1) times the integral over B_s(zeta) of phi(tau(y)) d mu(y). Since zeta + (y - zeta) = y, phi(tau(y)) = hsNormSq(V.tangentProj y - P_T). Hence V'.tiltExcess 0 s T = (s^n)^(-1) integral_{B_s(zeta)} hsNormSq(V.tangentProj y - P_T) d mu = V.tiltExcess zeta s T.

5. (R3). V'.scaledLpNorm (H(zeta + .)) p 0 s = (ofReal(s^(p-n)) * lower integral over B_s(0) of |H(zeta + x)|^p d mu'(x))^(1/p). By steps 1 and 2, the lower integral equals the lower integral over B_s(zeta) of |H(zeta + (y - zeta))|^p d mu(y), i.e. over B_s(zeta) of |H(y)|^p d mu(y). The prefactor ofReal(s^(p-n)) and the exponent 1/p are the same for V and V', both n-dimensional. So the two scaled L^p norms are equal.

6. (R4). Let Z := {x : not (1 <= V'.mult x)}. Since V'.mult x = V.mult(zeta + x), tau^(-1)(Z) = {y : not (1 <= V.mult(zeta + (y - zeta)))} = {y : not (1 <= V.mult y)}, which is mu-null by assumption. By 1(a), mu'(Z) = mu(tau^(-1) Z) = 0, i.e. 1 <= V'.mult x for mu'-a.e. x.

## Key steps

1. tau(x) = x - zeta is a measurable equivalence; push-forward evaluation and change of variables hold for all sets and functions
2. tau^(-1)(B_s(0)) = B_s(zeta)
3. (R1)-(R3) by change of variables and zeta + (y - zeta) = y
4. (R4): tau^(-1){V'.mult < 1} = {V.mult < 1}, which is mu-null

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
