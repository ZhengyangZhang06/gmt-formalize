# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.bump_form-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: facts (F2), (F3) and (F5) of the parent-supplied proof, used there in steps 4, 5 and 9.
1. (F3) For every 0-covector α, covectorEuclideanNorm(α) = |α(())|. By definition, covectorEuclideanNorm(α) = sqrt(Σ_I [I strictly monotone]·α((e_{I(i)})_{i ∈ Fin 0})²), the sum running over all maps I : Fin 0 → Fin P, with e the standard basis of ℝ^P. There is exactly one such map, the empty map, so the sum has a single term (Fintype.sum_unique). The empty map is vacuously strictly monotone, and the family (e_{I(i)})_{i ∈ Fin 0} is the empty family (), since all functions on Fin 0 coincide. Hence covectorEuclideanNorm(α) = sqrt(α(())²) = |α(())|.
2. Let g be a smooth bump function centred at z with inner radius a/2 and outer radius a (Mathlib ContDiffBump z with rIn = a/2 < rOut = a; valid since a > 0). Then g : ℝ^P → ℝ is C^∞, 0 ≤ g ≤ 1, g = 1 on closedBall(z, a/2) (so g(z) = 1), and g(x) = 0 whenever dist(x, z) ≥ a.
3. Let ε₀ be the constant 0-covector with value 1 (ContinuousAlternatingMap.constOfIsEmpty ℝ (ℝ^P) (Fin 0) 1), so ε₀(v) = 1 for every v : Fin 0 → ℝ^P. Define the 0-form f(x) := (c·g(x))·ε₀.
4. (iii) If x ∉ ball(z, a), then dist(x, z) ≥ a, so g(x) = 0 and f(x) = 0.
5. (i) By step 4, {x : f(x) ≠ 0} ⊆ ball(z, a), so tsupport f = closure{f ≠ 0} ⊆ closure(ball(z, a)) ⊆ closedBall(z, a).
6. f is C^∞, since x ↦ c·g(x) is smooth and a smooth scalar function times the constant covector ε₀ is smooth. f has compact support, because tsupport f is a closed subset of the compact set closedBall(z, a). As tsupport f ⊆ closedBall(z, a) ⊆ U, f ∈ 𝒟^0(U); let ω be f regarded as an element of TestFormOn U 0. Properties (i) and (iii) hold by steps 5 and 4.
7. (ii) ω(z)(()) = c·g(z)·ε₀(()) = c·1·1 = c.
8. (iv) For every x, step 1 gives covectorEuclideanNorm(ω(x)) = |c·g(x)·ε₀(())| = |c|·|g(x)| = |c|·g(x) ≤ |c|, using 0 ≤ g(x) ≤ 1.

## Key steps

1. In degree 0 the coefficient norm of α is |α(())|, because the only index map Fin 0 → Fin P is the empty, strictly monotone one.
2. Take a ContDiffBump g at z with radii a/2 < a and set ω(x) := c·g(x)·ε₀, with ε₀ the constant 0-covector 1.
3. ω is smooth, vanishes outside ball(z, a), has tsupport in closedBall(z, a) ⊆ U, satisfies ω(z)(()) = c, and has coefficient norm |c|·g ≤ |c|.

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
