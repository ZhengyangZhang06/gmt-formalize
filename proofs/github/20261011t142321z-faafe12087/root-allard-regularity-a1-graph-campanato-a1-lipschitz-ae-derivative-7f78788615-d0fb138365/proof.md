# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.segment_integral_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. L = L(R^n, R^l) carries the operator norm. R^n x R^n carries the product topology. I(a, b) := integral_0^1 g(a + tau(b - a))(b - a) dtau.

1. Segments stay in U. Let a, b ∈ U and tau ∈ [0, 1]. Then a + tau(b - a) = (1 - tau)a + tau b ∈ U by convexity, since 1 - tau >= 0, tau >= 0 and the coefficients sum to 1.

2. Reduction. Fix (a0, b0) ∈ U x U. It suffices to show that I is continuous at (a0, b0); then it is continuous within U x U at that point. Let S0 := {a0 + tau(b0 - a0) : tau ∈ [0, 1]}. S0 is compact, being a continuous image of [0, 1], and S0 ⊆ U by step 1.

3. A compact neighbourhood of the segment and a bound for g. S0 is compact, U is open and S0 ⊆ U. So there is delta > 0 such that the closed delta-thickening C := {z : dist(z, S0) <= delta} is contained in U (IsCompact.exists_cthickening_subset_open). C is compact because R^n is proper (IsCompact.cthickening). g is continuous on C ⊆ U, so there is M with ||g(z)|| <= M for all z ∈ C (IsCompact.exists_bound_of_continuousOn).

4. Nearby segments stay in C. Let W := {(a, b) : ||a - a0|| < delta and ||b - b0|| < delta}. It is a neighbourhood of (a0, b0), being the preimage of two open balls under the continuous projections. Let (a, b) ∈ W and tau ∈ [0, 1].
 (a + tau(b - a)) - (a0 + tau(b0 - a0)) = (1 - tau)(a - a0) + tau(b - b0).
Its norm is at most (1 - tau)||a - a0|| + tau||b - b0|| <= (1 - tau)delta + tau delta = delta. Since a0 + tau(b0 - a0) ∈ S0, the point a + tau(b - a) lies in C (mem_cthickening_of_dist_le). Also b - a = (b0 - a0) + (b - b0) - (a - a0), so ||b - a|| <= ||b0 - a0|| + 2 delta.

5. Dominated convergence. Put F((a, b), tau) := g(a + tau(b - a))(b - a) and use the constant bound B := M(||b0 - a0|| + 2 delta). We check the hypotheses of intervalIntegral.continuousAt_of_dominated_interval at (a0, b0) on the interval 0..1. Its set Ι 0 1 = (0, 1] is contained in [0, 1].
 (a) Measurability. Let (a, b) ∈ W. g is continuous on U, and tau |-> a + tau(b - a) is continuous and maps [0, 1] into C ⊆ U (step 4). So tau |-> g(a + tau(b - a)) is continuous on [0, 1]. Evaluating a continuous L-valued map at the fixed vector b - a keeps continuity (ContinuousOn.clm_apply). Hence tau |-> F((a, b), tau) is continuous on (0, 1]. It is therefore a.e.-strongly measurable for Lebesgue measure restricted to (0, 1] (ContinuousOn.aestronglyMeasurable, measurableSet_uIoc). This holds for every (a, b) in the neighbourhood W.
 (b) Domination. Let (a, b) ∈ W and tau ∈ (0, 1]. By ContinuousLinearMap.le_opNorm and steps 3-4,
 ||F((a, b), tau)|| <= ||g(a + tau(b - a))|| ||b - a|| <= M(||b0 - a0|| + 2 delta) = B.
Here M >= ||g(a + tau(b - a))|| >= 0.
 (c) The constant B is interval integrable on 0..1.
 (d) Continuity in the parameter. Fix tau ∈ (0, 1]. The point a0 + tau(b0 - a0) ∈ S0 ⊆ U lies in the open set U, so g is continuous at it (ContinuousOn.continuousAt with IsOpen.mem_nhds). The map (a, b) |-> a + tau(b - a) is continuous and sends (a0, b0) to that point. So (a, b) |-> g(a + tau(b - a)) is continuous at (a0, b0). The map (a, b) |-> b - a is continuous. Hence (a, b) |-> F((a, b), tau) is continuous at (a0, b0) (ContinuousAt.clm_apply).
So (a, b) |-> integral_0^1 F((a, b), tau) dtau = I(a, b) is continuous at (a0, b0).

6. Since (a0, b0) ∈ U x U was arbitrary, I is continuous on U x U. If U is empty there is nothing to prove.

## Key steps

1. Convexity: a + tau(b - a) ∈ U for a, b ∈ U and tau ∈ [0,1]
2. Fix (a0,b0): the segment S0 is compact in U, its closed delta-thickening C ⊆ U is compact, and ||g|| <= M on C
3. If ||a - a0||, ||b - b0|| < delta, every segment point lies in C and ||b - a|| <= ||b0 - a0|| + 2 delta
4. Dominated convergence (intervalIntegral.continuousAt_of_dominated_interval) with constant bound M(||b0 - a0|| + 2 delta): measurability from continuity in tau, pointwise continuity in (a,b) from continuity of g at points of the open set U

## Reference use

### local-project

Queries:
- `sha256sum GMT/Ch05/Submission.lean GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Submission.lean`
- `grep -n 'theorem\|lemma' mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `grep -n '^theorem\|^lemma\|^def' mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `rg -n 'theorem (integral_hasDerivAt_right|measure_prod_null|prod_apply_symm|eqOn_open_of_ae_eq|continuousAt_of_dominated_interval|continuousWithinAt_of_dominated_interval|norm_integral_le_of_norm_le_const|exists_cthickening_subset_open|hasFDerivAt_iff_isLittleO_nhds_zero|exists_measurable_superset_of_null|measure_preimage_add_right|continuous_parametric_intervalIntegral_of_continuous|comp_hasDerivAt)\b' mathlib/Mathlib`
- `rg -n 'theorem (integral_interval_sub_left|Ioo_ae_eq_Icc|ae_ne|stronglyMeasurableAtFilter)\b' mathlib/Mathlib`
- `rg -n 'LipschitzOnWith' mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `grep -rn 'IsCompact.cthickening\|theorem mem_cthickening_of_dist_le' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `grep -rn 'theorem ContinuousOn.clm_apply\|theorem ContinuousAt.clm_apply' mathlib/Mathlib/Analysis/Normed/Operator`
- `python: scan dag.json lean_name / lean_statement for intervalIntegral|HasDerivAt|AbsolutelyContinuous|LipschitzOnWith|volume {t (reuse and name reservation)`
- `grep -rl allard52_lad_ <run>/nodes GMT <simongmt> <snapshot>; git show <each of 1216 run branches>:GMT/Ch05/Submission.lean | grep allard52_lad_`
- `git show <run branches>:GMT/Ch05/Submission.lean | grep '^import' (precedent for extra Mathlib imports, e.g. accepted root-affine-approximation-a1-l1-tilt-height-a1)`
- `lean src/Submission.lean -o build/GMT/Ch05/Submission.olean (toolchains/lean-4.35.0-rc3-linux, LEAN_PATH = scratch build + lake-packages-25730c7c)`
- `lean check/Types2.lean; lean check/Assembly2.lean; lean check/Full.lean; lean check/Inst.lean`
- `python: lean_contract.validate_lean_statement on the five child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OpenPos.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Uniform.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-lipschitz-ae-derivative-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-campanato-a1-c1-holder-extension-a1/decomposition-v1.json`
- `/runtime/flows/gmt-claude-17d09e2ab055/_recursive_lean/lean_contract.py`
- `/tmp/lad-decomp/check/Types2.lean`
- `/tmp/lad-decomp/check/Assembly2.lean`
- `/tmp/lad-decomp/check/Full.lean`
- `/tmp/lad-decomp/check/Inst.lean`

Snapshot pins: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The workspace Submission.lean, Contract.lean and the snapshot Submission.lean are identical (sha256 c966f51efddb5a68ce15ef2a2a322fd9df0ca69da4626c7acef05b05d1691e12).

Usable Mathlib lemmas (snapshot paths):
- AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero (AbsolutelyContinuousFun.lean:169) is valid for normed-space values. integral_deriv_eq_sub (:225) is real-valued only, so the R^l-valued FTC (lipschitz_ftc) is a genuine obligation.
- LipschitzOnWith.absolutelyContinuousOnInterval (Function/AbsolutelyContinuous.lean:309).
- LipschitzOnWith.div / to_additive sub (Normed/Group/Uniform.lean:327).
- intervalIntegral.continuousAt_of_dominated_interval (DominatedConvergence.lean:280). continuous_parametric_intervalIntegral_of_continuous (:613) needs global continuity, so it does not apply.
- Measure.measure_prod_null and prod_apply_symm (Measure/Prod.lean:401, 706).
- exists_measurable_superset_of_null (MeasureSpaceDef.lean:219).
- Measure.eqOn_open_of_ae_eq (OpenPos.lean:115).
- Ioo_ae_eq_Icc (NullSingletonClass.lean:122).
- intervalIntegral.integral_hasDerivAt_right (FundThmCalculus.lean:725).
- intervalIntegral.norm_integral_le_of_norm_le_const and integral_interval_sub_left (IntervalIntegral/Basic.lean:769, 1121).
- hasFDerivAt_iff_isLittleO_nhds_zero (FDeriv/Basic.lean:815).
- HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374).
- IsCompact.exists_cthickening_subset_open, IsCompact.cthickening and mem_cthickening_of_dist_le (Thickening.lean:426, 283, 201).
- ContinuousOn/ContinuousAt.clm_apply (BoundedLinearMaps.lean:476, 482).

What is missing: Mathlib, SimonGMT and the DAG contain no line-wise Fubini lemma, no vector-valued Lipschitz FTC, no segment-integral continuity lemma and no differentiability-from-mean-value criterion. Nothing can be reused.

The AbsolutelyContinuousFun module is outside the frozen import closure. Accepted branches already add Mathlib imports to Submission.lean, so lipschitz_ftc may add it.

Names: none of the five proposed names (or the prefix allard52_lad_) occurs in dag.json (361 names), node artifacts, GMT/, SimonGMT, the snapshot, or Submission.lean on any of 1216 run branches.

Lean checks:
- Types2.lean and Assembly2.lean compile against the frozen olean. Assembly proves the exact frozen parent type from the five child types.
- Full.lean proves all five children and the parent with axioms [propext, Classical.choice, Quot.sound] only.
- Inst.lean confirms the standard instances.
- validate_lean_statement accepts all five types.
