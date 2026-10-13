# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.isolated_point_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the integral evaluations of steps 2d (with C := M, the possibly non-measurable submanifold, and K := tsupport ω) and 3c (with C the carrier and K a closed ball) of the parent-supplied proof, together with fact (F1). Notation: ∫_C f dH⁰ means ∫ f d(H⁰⌞C), where H⁰⌞C = μHE[0].restrict C; for measurable E and every set C, (H⁰⌞C)(E) = H⁰(E ∩ C).
1. (F1) H⁰ = μHE[0] = μH[0] (Mathlib Measure.euclideanHausdorffMeasure_zero), and μH[0]({z}) = 1 for every point z (Measure.hausdorffMeasure_zero_singleton). In particular H⁰({x}) = 1 < ∞.
2. F = 1_K·F pointwise: for z ∈ K both sides equal F(z); for z ∉ K the right side is 0 and F(z) = 0 by hypothesis. Hence ∫_C F dH⁰ = ∫_C 1_K·F dH⁰.
3. Since K is measurable, (H⁰⌞C)⌞K = H⁰⌞(K ∩ C) = H⁰⌞(C ∩ K) (Measure.restrict_restrict, which needs only K to be measurable), so ∫_C 1_K·F dH⁰ = ∫_{C∩K} F dH⁰ (Mathlib setIntegral_indicator for the measurable set K). No measurability of C is used.
4. Case x ∈ C ∩ K. Then C ∩ K = {x}: the inclusion ⊆ is the hypothesis, and ⊇ holds because x ∈ C ∩ K. So ∫_{C∩K} F dH⁰ = ∫_{{x}} F dH⁰ = H⁰({x})·F(x) = F(x) (Mathlib integral_singleton for the measurable singleton {x}, and step 1). As x ∈ C, 1_C(x)·F(x) = F(x), so both sides agree.
5. Case x ∉ C ∩ K. Then C ∩ K = ∅: if z ∈ C ∩ K, the hypothesis gives z = x, hence x ∈ C ∩ K, a contradiction. So H⁰⌞(C ∩ K) is the zero measure and ∫_{C∩K} F dH⁰ = 0. For the right side: if x ∈ C, then x ∉ K (otherwise x ∈ C ∩ K), so F(x) = 0 and 1_C(x)·F(x) = 0; if x ∉ C, then 1_C(x)·F(x) = 0 by definition of the indicator. So both sides are 0.
6. By steps 2–5, ∫_C F dH⁰ = 1_C(x)·F(x) in all cases.

## Key steps

1. F = 1_K·F, so ∫_C F dH⁰ = ∫_{C∩K} F dH⁰ using only the measurability of K.
2. The hypothesis C ∩ K ⊆ {x} forces C ∩ K = {x} or C ∩ K = ∅.
3. If C ∩ K = {x}, the integral is H⁰({x})·F(x) = F(x) = 1_C(x)·F(x); if C ∩ K = ∅, it is 0, and 1_C(x)·F(x) = 0 because x ∈ C forces x ∉ K and F(x) = 0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `grep -n '^def IsUnitOrientationOf|^structure IMRep|^def IMRep.action|^def IMRep.Represents|^def IsMinimizingIn|^def IsEmbeddedSubmanifold|^def IsOrientation|^def regularSet' project/GMT/Ch07/Contract.lean`
- `grep -n 'theorem hausdorffMeasure_zero_singleton|theorem one_le_hausdorffMeasure_zero_of_nonempty' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'euclideanHausdorffMeasure_zero' mathlib/Mathlib/Geometry mathlib/Mathlib/MeasureTheory`
- `grep -n 'theorem setIntegral_indicator|theorem setIntegral_eq_zero_of_forall_eq_zero|theorem setIntegral_union' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `grep -rn 'theorem integral_singleton' mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean`
- `grep -n 'def constOfIsEmpty' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `grep -n 'theorem one_of_mem_closedBall|theorem nonneg|theorem le_one|theorem tsupport_eq|theorem zero_of_le_dist' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|theorem GeometricCurrentOn.le_massOn' simongmt Chapter06/Mass.lean; grep -n 'zeroRegion|VanishesOn|def GeometricCurrentOn.support' Chapter06/CurrentLocalEquality.lean; grep -n 'TestFormOnConverges|structure GeometricCurrentOn' Chapter06/Currents.lean`
- `grep -rn 'regcomp_cop_zdr|dor_zdm|dor_zero_dim_minimizing' project/GMT (no match in the snapshot)`
- `python3 scan of dag.json: lean_name/status/candidate_commit of dor_zdm_imrep_zero_structure, dor_zdm_point_current, dor_zdm_imrep_zero_erase_point, dor_zero_dim_minimizing_support_disjoint, dtc_*, rsd_cmr_support_subset_of_vanish; no regcomp_cop_zdr name`
- `git grep -l regcomp_cop_zdr over all 1026 distinct ref tips (no match); git show 26a8976b:GMT/Ch07/Submission.lean (accepted proofs of the three reused declarations)`
- `lean /tmp/zdr-decomp/Assembly.lean and /tmp/zdr-decomp/InSitu.lean (#print axioms); simulated leaf_verification.check_source_delta for each new child`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/regcomp_cop_zdr_decomposition/Assembly.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Submission.lean; IsUnitOrientationOf (line 52), IMRep (61), IMRep.action (79), Represents (83), IsMinimizingIn (134), IsEmbeddedSubmanifold (221), IsOrientation (234) and regularSet (244) are the definitions the children unfold. Mathlib supplies the facts used: hausdorffMeasure_zero_singleton (Hausdorff.lean:628), one_le_hausdorffMeasure_zero_of_nonempty (651), MeasureTheory.Measure.euclideanHausdorffMeasure_zero (Geometry/Euclidean/Volume/Measure.lean:82, notation μHE at 72), setIntegral_indicator (Bochner/Set.lean:194), setIntegral_eq_zero_of_forall_eq_zero (357, needs no measurability of the set), setIntegral_union (87), integral_singleton (Bochner/Basic.lean:1254), constOfIsEmpty (Alternating/Basic.lean:301) and ContDiffBump one_of_mem_closedBall/nonneg/le_one/tsupport_eq/zero_of_le_dist (BumpFunction/Basic.lean:137–163). SimonGMT (pinned lake package) supplies covectorEuclideanNorm (Mass.lean:30), massAdmissibleOn (57), massOn (68), le_massOn, zeroRegion/support (CurrentLocalEquality.lean:108, 115) and TestFormOnConverges (Currents.lean:132). The snapshot project contains no regcomp_cop_zdr, dor_zdm or dor_zero_dim_minimizing declaration (no match); the three reused declarations exist only as comparator-accepted DAG nodes (status accepted, candidate commits 39634bad, c422ce6d, 875f0d75) whose frozen types are copied byte-for-byte. A scratch assembly of the eight children and the selected theorem compiles warning-free with axioms propext, Classical.choice, Quot.sound; each new child is a single theorem that passes the leaf source-delta check.
