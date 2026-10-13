# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1`
- Child DAG node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.imrep_zero_structure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the parent-supplied proof (structure of the carrier M; a support point of μ_R in U is a carrier point). Simon treats integer multiplicity currents only for n ≥ 1 (Ch. 6 §3, chapter-06.txt line 731), so this degree-0 argument is supplied in full from the definitions: countably n-rectifiable, Ch. 3, 1.1 (chapter-03.txt lines 13–16); approximate tangent space, Ch. 3, 1.4 (chapter-03.txt lines 77–87); (M, θ, ξ), Ch. 6, 3.1 (chapter-06.txt lines 733–753); H⁰ is counting measure (chapter-02.txt line 787). Notation: M = R.carrier, θ = R.mult, ξ = R.orient, H⁰ = μHE[0], μ_R = R.measure = (H⁰⌞M).withDensity θ.
1. Facts about H⁰. H⁰ = μH[0] (Mathlib Measure.euclideanHausdorffMeasure_zero). H⁰({z}) = 1 for every point z (hausdorffMeasure_zero_singleton), and H⁰(S) ≥ 1 for every nonempty S (one_le_hausdorffMeasure_zero_of_nonempty). Points are Borel, so for a finite set F, H⁰(F) = Σ_{z∈F} H⁰({z}) = #F (sum_measure_singleton). Compact sets are closed, hence Borel.
2. (i) M is countable. R.rectifiable gives M₀ with H⁰(M₀) = 0 and Lipschitz maps F_j : ℝ⁰ → ℝ^P (j ∈ ℕ) with M ⊆ M₀ ∪ ⋃_j range F_j. If M₀ were nonempty, step 1 would give H⁰(M₀) ≥ 1. So M₀ = ∅. The space ℝ⁰ = EuclideanSpace ℝ (Fin 0) has exactly one point, since two functions on the empty index set Fin 0 are equal. So each range F_j is a subsingleton, hence countable, and M ⊆ ⋃_j range F_j is countable.
3. (ii) Let K ⊆ U be compact, hence Borel. By withDensity_apply and Measure.restrict_restrict, μ_R(K) = ∫⁻_K θ d(H⁰⌞M) = ∫⁻_{K∩M} θ dH⁰ = ∫⁻_{M∩K} θ dH⁰ =: I, and I < ∞ by R.locallyIntegrable_mult K. So μ_R(K) < ∞. Next, θ(z) ≥ 1 for z ∈ M (R.mult_pos, θ is ℕ-valued). Hence H⁰(M ∩ K) = ∫⁻_{M∩K} 1 dH⁰ ≤ I < ∞ (setLIntegral_mono' on the Borel set M ∩ K). Suppose M ∩ K were infinite. For every m ∈ ℕ it contains a finite F with #F = m (Set.Infinite.exists_subset_card_eq), so m = H⁰(F) ≤ H⁰(M ∩ K) by step 1 and monotonicity. Taking m = ⌈r⌉ shows H⁰(M ∩ K) ≥ r for every real r ≥ 0, so H⁰(M ∩ K) = ∞, a contradiction. Hence M ∩ K is finite.
4. (iii) Let p(z) be the property '∃ Q, HasApproximateTangentSpaceAt 0 M z Q ∧ IsUnitOrientationOf (ξ(z)) Q'. R.orients says p(z) holds for H⁰⌞M-a.e. z. Since M is Borel, this means H⁰(N) = 0 for N := {z : z ∈ M and not p(z)} (ae_restrict_iff', ae_iff). If some x ∈ M failed p, then {x} ⊆ N and 1 = H⁰({x}) ≤ H⁰(N) = 0, a contradiction. So p(x) holds for every x ∈ M. Now fix x ∈ M, and take Q and τ : Fin 0 → ℝ^P from IsUnitOrientationOf (ξ(x)) Q. Then either ξ(x)(α) = α(τ) for all 0-covectors α, or ξ(x)(α) = −α(τ) for all α. Let α₁ be the constant 0-covector with value 1 (ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) 1), so α₁(τ) = 1 (constOfIsEmpty_apply). Then ξ(x)(α₁) = ±1. If ξ(x) = 0 this would give 0 = ±1, so ξ(x) ≠ 0.
5. (iv) Assume U is open.
(⊇) Let x ∈ M; then x ∈ U by R.carrier_subset. Since {x} is Borel and x ∈ M, μ_R({x}) = ∫⁻_{{x}∩M} θ dH⁰ = ∫⁻_{{x}} θ dH⁰ = θ(x)·H⁰({x}) = θ(x) ≥ 1 (withDensity_apply, Measure.restrict_restrict, lintegral_singleton). For every neighbourhood N of x, μ_R(N) ≥ μ_R({x}) > 0. Hence x ∈ spt μ_R (Measure.mem_support_iff_forall).
(⊆) Let x ∈ U ∩ spt μ_R and suppose x ∉ M. Choose ε > 0 with B_ε(x) ⊆ U (U open). Then B̄_{ε/2}(x) ⊆ U is compact, so by (ii) F := M ∩ B̄_{ε/2}(x) is finite, hence closed, and x ∉ F. Since the complement of F is open and contains x, choose δ > 0 with B_δ(x) ∩ F = ∅, and put η := min(δ, ε/2) > 0. A point z ∈ B_η(x) ∩ M would lie in B̄_{ε/2}(x) ∩ M = F and in B_δ(x), which is impossible. So B_η(x) ∩ M = ∅ and μ_R(B_η(x)) = ∫⁻_{B_η(x)∩M} θ dH⁰ = 0. But B_η(x) is a neighbourhood of x and x ∈ spt μ_R, so μ_R(B_η(x)) > 0 (Measure.mem_support_iff_forall), a contradiction. Hence x ∈ M, and U ∩ spt μ_R = M.

## Key steps

1. H⁰ = μH[0] gives every point mass 1, every nonempty set mass ≥ 1, and finite sets mass equal to their cardinality.
2. The null set M₀ in the rectifiable cover is empty and each Lipschitz image of the one-point space ℝ⁰ is a point, so M is countable.
3. Since θ ≥ 1 on M, H⁰(M ∩ K) ≤ ∫_{M∩K} θ dH⁰ = μ_R(K) < ∞ for compact K ⊆ U, so M ∩ K is finite.
4. Every point of M has positive H⁰⌞M-mass, so the a.e. orientation property holds at every carrier point; ξ(x) maps the constant covector 1 to ±1, so ξ(x) ≠ 0.
5. For U open, a carrier point has μ_R-mass θ(x) ≥ 1, and a point of U off M has a ball missing the locally finite set M, so U ∩ spt μ_R = M.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both byte-identical)`
- `rg -c sorry local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (1 = main_theorem)`
- `rg -n 'euclideanHausdorffMeasure_zero|μHE\[|notation.*μHE' mathlib/Mathlib`
- `rg -n 'theorem (withDensity_dirac|dirac_withDensity|withDensity_add_measure|withDensity_smul_measure)' mathlib/Mathlib`
- `rg -n '^(theorem|lemma) ' mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `sed -n 615,660p mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n -e 'theorem restrict_union ' -e 'theorem setIntegral_union' -e 'theorem integral_singleton' -e 'theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero' -e 'integrableOn_finite' -e 'theorem integrableOn_singleton_iff' -e 'theorem dirac_apply_of_mem' -e 'theorem lintegral_singleton' -e "theorem ae_restrict_iff'" -e 'theorem withDensity_apply ' mathlib/Mathlib/MeasureTheory`
- `rg -n 'sum_measure_singleton|IntegrableOn.of_forall_sdiff_eq_zero|Countable.measurableSet|norm_iteratedFDeriv_zero|Infinite.exists_subset_card_eq' mathlib/Mathlib/{MeasureTheory,Analysis/Calculus/ContDiff,Data/Set}`
- `rg -n 'theorem exists_.*tsupport_subset|tsupport_eq|one_of_mem_closedBall|hasCompactSupport|contDiff' mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `grep -n 'CountablyRectifiable|HasApproximateTangentSpaceAt|blowUpMap|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; cat simongmt Chapter06/{Currents,CurrentLocalEquality,Mass}.lean`
- `rg -l 'dor_zdm|imrep_zero_structure|imrep_zero_erase_point|zdm_point_current' dag.json GMT simongmt; rg -l --glob '*.lean' dor_zdm workspaces/.swarm-worktrees (no match)`
- `grep -n 'countably n-rectifiable|1.4 Definition|2.11|3.1 Definition|counting measure' book/chapter-0{2,3,6}.txt`
- `lake env lean /tmp/zdmt-decomp/Stmts.lean; lake env lean /tmp/zdmt-decomp/spec/Final.lean (exact frozen strings elaborate)`
- `lake env lean /tmp/zdmt-decomp/Inst.lean (pp.explicit instance check)`
- `lake env lean /tmp/zdmt-decomp/Combined.lean (#print axioms of the three children and the assembled parent)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Dirac/Def.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Finite/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-zero-dim-minimizing-trivial-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/.swarm-worktrees/c025f76e99e37e80afe1/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/zdmt-decomp/Stmts.lean`
- `/tmp/zdmt-decomp/Inst.lean`
- `/tmp/zdmt-decomp/Assembly.lean`
- `/tmp/zdmt-decomp/Child1.lean`
- `/tmp/zdmt-decomp/Child2.lean`
- `/tmp/zdmt-decomp/Child3.lean`
- `/tmp/zdmt-decomp/Combined.lean`
- `/tmp/zdmt-decomp/spec/Final.lean`
- `/tmp/zdmt-decomp/spec/children.json`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, and its only sorry is main_theorem.

The pinned SimonGMT package has no degree-0 integer multiplicity facts and no point currents. It provides GeometricCurrentOn, TestFormOnConverges, zeroRegion/support and massOn (Chapter06), and CountablyRectifiable(.mono), HasApproximateTangentSpaceAt and blowUpMap (Chapter03).

The snapshot Mathlib supplies every tool the children need:
- Hausdorff measure in degree 0: euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, one_le_hausdorffMeasure_zero_of_nonempty, sum_measure_singleton.
- Measures and supports: withDensity_apply, withDensity_add_measure, dirac_withDensity, Measure.restrict_union, Measure.restrict_singleton, Measure.restrict_restrict, lintegral_singleton, Measure.mem_support_iff_forall, ae_restrict_iff'.
- Integration: setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_union, integral_singleton, integrableOn_singleton, integrableOn_finite_biUnion, IntegrableOn.of_forall_sdiff_eq_zero.
- Other: Set.Countable.measurableSet, Set.Infinite.exists_subset_card_eq, norm_iteratedFDeriv_zero, ContDiffBump (tsupport_eq, one_of_mem_closedBall, hasCompactSupport, contDiff), ContinuousAlternatingMap.constOfIsEmpty(_apply).

With these, all three children are fully proved in kernel-checked prototypes (/tmp/zdmt-decomp/Combined.lean) using only propext, Classical.choice and Quot.sound. The frozen parent type is assembled from the children plus the declared sibling dor_imrep_massOn_eq_measure_and_support, used at its exact frozen type.

The dor_zdm_* names have no matches anywhere. The related nodes dtc_dim_zero_eq_zero and dimred_zero_dim_minimizing_eq_zero have different, unaccepted types, so nothing is reused.

Book: Simon restricts Ch. 6 §3 to n ≥ 1 (chapter-06.txt line 731), so the degree-0 arguments are supplied in full. They cite Ch. 3 1.1 and 1.4, Ch. 6 2.1, 2.11 and 3.1, and Ch. 2 line 787 (H⁰ is counting measure).
