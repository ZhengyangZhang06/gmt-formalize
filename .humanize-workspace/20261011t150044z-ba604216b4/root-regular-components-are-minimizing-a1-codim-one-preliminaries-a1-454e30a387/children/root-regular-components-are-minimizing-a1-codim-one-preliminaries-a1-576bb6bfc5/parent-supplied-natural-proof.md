# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.isolated_carrier_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 (3a–3c), 4 and 5 of the parent-supplied proof, with the parent's local form (*), T(ω) = m·s·ω(y)(()), taken as the hypothesis with c := m·s. Notation: C = R.carrier, θ = R.mult, ξ_R = R.orient, H⁰ = μHE[0]; for ω ∈ 𝒟^0(U) put F_ω(z) := θ(z)·ξ_R(z)(ω(z)), so that T(ω) = ∫_C F_ω dH⁰.
1. (3a, 3b) By the sibling imrep_zero_structure (Submission.dor_zdm_imrep_zero_structure), (ii) C ∩ K is finite for every compact K ⊆ U, and (iii) for every x ∈ C there is a subspace Q_x with IsUnitOrientationOf (ξ_R(x)) Q_x. By the sibling unit_orientation_zero (Submission.regcomp_cop_zdr_unitOrientation_zero), for every x ∈ C there is s_x ∈ ℝ with |s_x| = 1 and ξ_R(x)(α) = s_x·α(()) for every 0-covector α.
2. (Vanishing off the support.) If ω ∈ 𝒟^0(U) and z ∉ tsupport ω, then ω(z) = 0 and F_ω(z) = θ(z)·ξ_R(z)(0) = 0, because ξ_R(z) is linear.
3. (3c, isolated atoms.) Let x ∈ C and a > 0 with C ∩ closedBall(x, a) ⊆ {x}, and let ω ∈ 𝒟^0(U) with tsupport ω ⊆ closedBall(x, a). By step 2, F_ω vanishes outside the closed, hence measurable, set closedBall(x, a). The sibling isolated_point_integral (Submission.regcomp_cop_zdr_setIntegral_eq_indicator; with the set C, K := closedBall(x, a), the point x and F := F_ω) gives T(ω) = ∫_C F_ω dH⁰ = 1_C(x)·F_ω(x) = θ(x)·ξ_R(x)(ω(x)), since x ∈ C.
4. (Step 4: C ∩ ball(y, r) ⊆ {y}.) Let x ∈ C ∩ ball(y, r) and suppose x ≠ y. Put δ := dist(x, y), so 0 < δ < r, and a₀ := min(r − δ, δ)/2 > 0; then a₀ < r − δ and a₀ < δ.
 (a) closedBall(x, a₀) ⊆ ball(y, r): if dist(z, x) ≤ a₀, then dist(z, y) ≤ dist(z, x) + δ ≤ a₀ + δ < r.
 (b) y ∉ closedBall(x, a₀), because dist(y, x) = δ > a₀.
 (c) closedBall(x, a₀) is compact and contained in ball(y, r) ⊆ U, so C ∩ closedBall(x, a₀) is finite by step 1. Hence F₀ := (C ∩ closedBall(x, a₀)) ∖ {x} is finite, therefore closed, and x ∉ F₀. As the complement of F₀ is an open set containing x, choose ε > 0 with ball(x, ε) ∩ F₀ = ∅, and put a := min(ε/2, a₀) > 0.
 (d) C ∩ closedBall(x, a) ⊆ {x}: if z ∈ C ∩ closedBall(x, a) with z ≠ x, then z ∈ closedBall(x, a₀) (as a ≤ a₀), so z ∈ F₀; and dist(z, x) ≤ a ≤ ε/2 < ε, so z ∈ ball(x, ε) ∩ F₀ = ∅, which is impossible.
 (e) Since closedBall(x, a) ⊆ closedBall(x, a₀) ⊆ ball(y, r) ⊆ U, the sibling bump_form (Submission.regcomp_cop_zdr_exists_bumpForm; centre x, radius a, value 1) gives ω ∈ 𝒟^0(U) with tsupport ω ⊆ closedBall(x, a), ω(x)(()) = 1, and ω(p) = 0 for every p ∉ ball(x, a).
 (f) tsupport ω ⊆ closedBall(x, a) ⊆ ball(y, r), so the hypothesis applies: T(ω) = c·ω(y)(()). Since y ∉ closedBall(x, a₀) ⊇ closedBall(x, a) ⊇ ball(x, a), ω(y) = 0, hence T(ω) = c·0 = 0.
 (g) By step 3 (applicable by (d) and tsupport ω ⊆ closedBall(x, a)) and step 1, T(ω) = θ(x)·ξ_R(x)(ω(x)) = θ(x)·s_x·ω(x)(()) = θ(x)·s_x. Here θ(x) ≥ 1, as θ(x) is a positive natural number for x ∈ C (R.mult_pos), and s_x ≠ 0 since |s_x| = 1; so T(ω) ≠ 0, contradicting (f). Hence x = y, which proves C ∩ ball(y, r) ⊆ {y}.
5. (Step 5: y ∈ C.) Suppose y ∉ C. Then no z ∈ C lies in ball(y, r): by step 4 such a z would equal y, giving y ∈ C. Since closedBall(y, r/2) ⊆ ball(y, r) ⊆ U, the sibling bump_form (centre y, radius r/2, value 1) gives ω ∈ 𝒟^0(U) with tsupport ω ⊆ closedBall(y, r/2) ⊆ ball(y, r) and ω(y)(()) = 1. The hypothesis gives T(ω) = c·1 = c. On the other hand, every z ∈ C satisfies z ∉ ball(y, r) ⊇ tsupport ω, so F_ω(z) = 0 by step 2; the integrand vanishes at every point of C, hence T(ω) = ∫_C F_ω dH⁰ = 0 (Mathlib setIntegral_eq_zero_of_forall_eq_zero, which needs no measurability). Thus c = 0, contradicting c ≠ 0. Therefore y ∈ C.
6. Steps 4 and 5 give y ∈ C and C ∩ ball(y, r) ⊆ {y}.

## Key steps

1. imrep_zero_structure and unit_orientation_zero: C is finite on compact subsets of U, and ξ_R(x) = s_x·eval with |s_x| = 1 at every x ∈ C.
2. isolated_point_integral: if C ∩ closedBall(x, a) ⊆ {x} with x ∈ C and tsupport ω ⊆ closedBall(x, a), then T(ω) = θ(x)·ξ_R(x)(ω(x)).
3. A point x ≠ y of C ∩ ball(y, r) is isolated in C by local finiteness; a bump at x avoiding y gives T(ω) = 0 by the hypothesis but T(ω) = θ(x)·s_x ≠ 0 by the representation.
4. If y ∉ C, then C misses ball(y, r), and a bump at y gives T(ω) = c ≠ 0 by the hypothesis but T(ω) = 0 by the representation.

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
