# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1`
- Child DAG node: `root.allard_regularity-a1.graph_campanato-a1.lipschitz_ae_derivative-a1.lipschitz_ftc-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. The integral from u to v is the oriented interval integral for Lebesgue measure on R. Since a <= b, [a, b] = Icc a b = uIcc a b.
Lean note: the absolute-continuity API used below is in Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun. The frozen header does not import it, so add that import to the proof file.

1. Bound and integrability of k. k is continuous on the compact set [a, b], so there is C ∈ R with ||k(t)|| <= C for all t ∈ [a, b] (IsCompact.exists_bound_of_continuousOn). For u, v ∈ [a, b], the closed interval between u and v lies in [a, b]. So k is continuous on it and therefore interval integrable on u..v (ContinuousOn.intervalIntegrable).

2. The primitive Psi(t) := integral_a^t k(s) ds is Lipschitz on [a, b]. Let u, v ∈ [a, b]. Step 1 gives integrability on a..u and a..v, so additivity of the interval integral (intervalIntegral.integral_interval_sub_left) gives Psi(u) - Psi(v) = integral_v^u k. Every s between v and u lies in [a, b], so ||k(s)|| <= C. By intervalIntegral.norm_integral_le_of_norm_le_const,
 ||Psi(u) - Psi(v)|| <= C |u - v| <= C+ |u - v|, where C+ := max(C, 0) (Real.toNNReal C).
Hence Psi is C+-Lipschitz on [a, b] (LipschitzOnWith.of_dist_le_mul).

3. D := phi - Psi is absolutely continuous on [a, b]. phi is L-Lipschitz on [a, b] and Psi is C+-Lipschitz there. So D(t) = phi(t) - Psi(t) is (L + C+)-Lipschitz on [a, b] (LipschitzOnWith.sub, the additive form of LipschitzOnWith.div). A function that is Lipschitz on uIcc a b is absolutely continuous there (LipschitzOnWith.absolutelyContinuousOnInterval).

4. D has derivative 0 at almost every point of [a, b]. The endpoints a and b form an L^1-null set, so Ioo a b =ae Icc a b (Ioo_ae_eq_Icc). Combined with the hypothesis, for a.e. t: if t ∈ [a, b], then t ∈ (a, b) and phi has derivative k(t) at t. Fix such a t ∈ [a, b], so t ∈ (a, b).
 (i) k is continuous at t, since t is an interior point of [a, b] (Icc_mem_nhds) and k is continuous on [a, b].
 (ii) k is strongly measurable at the filter nhds t, since k is continuous on the open set (a, b) containing t (ContinuousOn.stronglyMeasurableAtFilter with isOpen_Ioo).
 (iii) k is interval integrable on a..t, by step 1 with a, t ∈ [a, b].
By the first fundamental theorem of calculus (intervalIntegral.integral_hasDerivAt_right), Psi has derivative k(t) at t. Therefore D = phi - Psi has derivative k(t) - k(t) = 0 at t (HasDerivAt.sub, then sub_self).

5. D is constant on [a, b]. Apply AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero to D with the a.e. statement of step 4. This lemma holds for functions with values in any real normed space, in particular R^l. It gives a constant D0 with D(t) = D0 for all t ∈ uIcc a b = [a, b]. Both a and b lie in [a, b] because a <= b, so D(b) = D(a).

6. Conclusion. Psi(a) = integral_a^a k = 0, so D(a) = phi(a), and D(b) = phi(b) - Psi(b). Hence phi(b) - Psi(b) = phi(a), that is,
 phi(b) - phi(a) = Psi(b) = integral_a^b k(t) dt.
If a = b, both sides are 0 and the argument above covers this case unchanged.

## Key steps

1. k is bounded by C on [a,b] and interval integrable on every subinterval
2. The primitive Psi(t) = integral_a^t k is max(C,0)-Lipschitz on [a,b]
3. D = phi - Psi is Lipschitz, hence absolutely continuous on [a,b]
4. For a.e. t ∈ (a,b), phi' = k(t) by hypothesis and Psi' = k(t) by FTC-1, so D'(t) = 0; the endpoints are null
5. const_of_ae_hasDerivAt_zero: D is constant on [a,b]; with Psi(a) = 0, D(b) = D(a) gives the formula

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
