# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1`
- Child DAG node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.imrep_zero_erase_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent-supplied proof (the competitor's representation R' with carrier M ∖ {x}), together with the measure identity μ_{R'}(W) = μ_R(W) − θ(x) used in its step 7. Simon excludes n = 0 in Ch. 6 §3 (chapter-06.txt line 731), so the argument is supplied in full from Ch. 3, 1.4 (chapter-03.txt lines 77–87; η_{y,λ}(z) = λ⁻¹(z − y), which is blowUpMap y λ) and Ch. 6, 3.1 (chapter-06.txt lines 733–753). It uses the sibling imrep_zero_structure (dor_zdm_imrep_zero_structure), parts (i)–(iii). Notation: M = R.carrier, θ = R.mult, ξ = R.orient, H⁰ = μHE[0] = μH[0] (Measure.euclideanHausdorffMeasure_zero), so H⁰({z}) = 1 for every z (hausdorffMeasure_zero_singleton); M' := M ∖ {x}. Points and countable sets are Borel (Set.Countable.measurableSet).
1. Orientation of M' at its points. Let y ∈ M', so y ∈ M and y ≠ x. By imrep_zero_structure (iii) there is Q with IsUnitOrientationOf (ξ(y)) Q and HasApproximateTangentSpaceAt 0 M y Q. Call the latter h: it gives finrank Q = 0 and, for every f ∈ C_c(ℝ^P, ℝ), ∫_{η_{y,λ}(M)} f dH⁰ → ∫_Q f dH⁰ as λ → 0 in 𝓝[>] 0. We show HasApproximateTangentSpaceAt 0 M' y Q; the dimension part is that of h. Let f ∈ C_c(ℝ^P, ℝ). Its topological support is compact, hence contained in some B̄_b(0). Put a := max(b, 0) + 1 > 0; then f(z) = 0 whenever ‖z‖ ≥ a. Put d := ‖x − y‖ > 0 and let 0 < λ < d/a. Then ‖η_{y,λ}(x)‖ = d/λ > a, so f(η_{y,λ}(x)) = 0. The set t := η_{y,λ}(M) is countable as an image of the countable set M (imrep_zero_structure (i)), hence Borel, and s := η_{y,λ}(M') ⊆ t. If z ∈ t ∖ s, write z = η_{y,λ}(w) with w ∈ M. Then w ∉ M' (otherwise z ∈ s), so w = x and f(z) = 0. By setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, ∫_{η_{y,λ}(M)} f dH⁰ = ∫_{η_{y,λ}(M')} f dH⁰ for every λ ∈ (0, d/a). Since (0, d/a) ∈ 𝓝[>] 0, the function λ ↦ ∫_{η_{y,λ}(M')} f dH⁰ eventually equals λ ↦ ∫_{η_{y,λ}(M)} f dH⁰ along 𝓝[>] 0. The latter tends to ∫_Q f dH⁰ by h, so the former has the same limit (Tendsto.congr'). Hence HasApproximateTangentSpaceAt 0 M' y Q, and Q still satisfies IsUnitOrientationOf (ξ(y)) Q.
2. Construction of R'. Let R' have carrier M', multiplicity θ and orientation ξ. Check each field. (a) M' = M ∖ {x} is Borel. (b) M' ⊆ M ⊆ U. (c) M' is countably 0-rectifiable (CountablyRectifiable.mono, M' ⊆ M). (d) θ is measurable. (e) θ > 0 on M' ⊆ M. (f) For compact K ⊆ U, ∫⁻_{M'∩K} θ dH⁰ ≤ ∫⁻_{M∩K} θ dH⁰ < ∞ (lintegral_mono_set). (g) H⁰⌞M' ≤ H⁰⌞M (Measure.restrict_mono), so ξ is a.e. strongly measurable for H⁰⌞M' (AEStronglyMeasurable.mono_measure). (h) By step 1 the orientation property holds at every point of M', hence H⁰⌞M'-a.e. (ae_restrict_iff' with M' Borel). So R' ∈ IMRep U 0 and R'.carrier = M ∖ {x}.
3. Measure identity. Since x ∈ M, M = M' ∪ {x} with M' and {x} disjoint and {x} Borel. So H⁰⌞M = H⁰⌞M' + H⁰⌞{x} (Measure.restrict_union), and H⁰⌞{x} = H⁰({x})·δ_x = δ_x (Measure.restrict_singleton). withDensity is additive in the measure (withDensity_add_measure), and δ_x.withDensity θ = θ(x)·δ_x since points are Borel (dirac_withDensity). Hence μ_R = (H⁰⌞M).withDensity θ = (H⁰⌞M').withDensity θ + θ(x)·δ_x = μ_{R'} + θ(x)·δ_x.
4. Action identity. Fix ω ∈ 𝒟⁰(U), put g(z) := θ(z)·ξ(z)(ω(z)) ∈ ℝ, and let K := tsupport ω. K is compact because ω has compact support, and K ⊆ U because ω ∈ TestFormOn U 0. (a) If z ∉ K then ω(z) = 0, so g(z) = θ(z)·ξ(z)(0) = 0. (b) M ∩ K is finite by imrep_zero_structure (ii). For each z, g is H⁰-integrable on {z} because H⁰({z}) = 1 < ∞ (integrableOn_singleton). So g is integrable on the finite union M ∩ K = ⋃_{z∈M∩K}{z} (integrableOn_finite_biUnion). Hence g is integrable on M (IntegrableOn.of_forall_sdiff_eq_zero: M is Borel and g = 0 on M ∖ (M ∩ K) by (a)), and therefore on M' ⊆ M and on {x} ⊆ M. (c) By setIntegral_union (M' and {x} disjoint, {x} Borel), R.action(ω) = ∫_M g dH⁰ = ∫_{M'} g dH⁰ + ∫_{{x}} g dH⁰, and ∫_{{x}} g dH⁰ = H⁰({x})·g(x) = g(x) (integral_singleton). Since R' has the same θ and ξ, R'.action(ω) = ∫_{M'} g dH⁰ = R.action(ω) − θ(x)·ξ(x)(ω(x)).

## Key steps

1. At y ∈ M ∖ {x}, the blow-ups of M ∖ {x} and of M differ only at the point η_{y,λ}(x), which leaves the support of each f ∈ C_c once λ < |x − y|/a. So M ∖ {x} inherits the approximate tangent space and orientation of M at y.
2. The remaining IMRep fields (Borel, rectifiable, positivity, local integrability, measurability) pass to the subset M ∖ {x}.
3. H⁰⌞M = H⁰⌞(M ∖ {x}) + δ_x and δ_x.withDensity θ = θ(x)δ_x give μ_R = μ_{R'} + θ(x)δ_x.
4. The integrand θ⟨ω, ξ⟩ is supported on the finite set M ∩ spt ω, hence integrable, and splitting off {x} gives R'.action(ω) = R.action(ω) − θ(x)ξ(x)(ω(x)).

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
