# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1`
- Child DAG node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1.localized_boundary_zero-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof. This is identity (2) in the proof of Simon 7.5.11 (chapter-07.txt lines 996–999): 'if ζ ≡ 0 in some neighborhood of spt T ∖ M₁, then T₁(d(ζω)) = T(d(ζω)) = ∂T(ζω) = 0'. It is made rigorous by the parent's correction [D3]: M₁ is separated from the rest of spt T by a partition of unity subordinate to the neighbourhoods G of (h4), on which T₁ is a multiple of T.
Notation: for a form F, dF(x) is the alternation of DF(x). The operator d is linear on test forms and does not enlarge topological supports (SimonGMT tsupport_exteriorDerivative_subset). By definition ∂S(η) = S(dη). In Lean, `open scoped Manifold` is needed for 𝓘(ℝ, Euclid P); do not open the ContDiff scope, because it makes ω a token.

Let η ∈ 𝒟^m(U) satisfy closure(M₁) ∩ tsupport η ⊆ M₁.

1. (Compactness.) Put K₁ := closure(M₁) ∩ tsupport η. It is a closed subset of the compact set tsupport η (η has compact support), hence compact. By hypothesis K₁ ⊆ M₁.

2. (Finite cover.) For each z ∈ K₁ ⊆ M₁, (h4) gives an open set G_z ∋ z and c_z ∈ ℝ with T₁(θ) = c_z·T(θ) for all θ ∈ 𝒟^{m+1}(U) with tsupport θ ⊆ G_z. The sets G_z, z ∈ K₁, form an open cover of the compact set K₁. Choose z_1, …, z_L ∈ K₁ (L ≥ 0 is allowed) with K₁ ⊆ W := G_{z_1} ∪ … ∪ G_{z_L}. W is open.

3. (Partition of unity.) ℝ^P is locally compact and regular, so there is an open set O₁ with K₁ ⊆ O₁ and closure(O₁) ⊆ W (Mathlib exists_open_between_and_isCompact_closure).
   - closure(O₁) is closed and covered by the open sets G_{z_l}.
   - Apply Mathlib SmoothPartitionOfUnity.exists_isSubordinate to ℝ^P as a manifold modelled on itself with 𝓘(ℝ, ℝ^P); it is Hausdorff, σ-compact and finite-dimensional.
   - This gives a smooth partition of unity (ψ_l)_{l=1..L} on closure(O₁) subordinate to (G_{z_l}). Each ψ_l : ℝ^P → ℝ is C^∞ (contMDiff_iff_contDiff), tsupport ψ_l ⊆ G_{z_l}, and Σ_l ψ_l(x) = 1 for every x ∈ closure(O₁).
   Let χ := Σ_l ψ_l. It is C^∞ and χ = 1 on O₁. If L = 0, then χ ≡ 0 and O₁ = ∅.

4. (Decomposition.) Put η₀(x) := (1 − χ(x))·η(x) and η_l(x) := ψ_l(x)·η(x) for l = 1, …, L.
   - Each is a C^∞ form, as the product of a C^∞ function with the C^∞ form η.
   - Its support is contained in support η. So it has compact support and topological support ⊆ tsupport η ⊆ U. Hence η₀, η_l ∈ 𝒟^m(U).
   - Pointwise, η₀ + Σ_l η_l = (1 − χ + Σ_l ψ_l)·η = η. So η = η₀ + Σ_l η_l in 𝒟^m(U).
   - Since ∂T₁ is linear, ∂T₁(η) = ∂T₁(η₀) + Σ_l ∂T₁(η_l).

5. (∂T₁(η₀) = 0.) Let V := O₁ ∪ (ℝ^P ∖ tsupport η), an open set.
   - η₀ vanishes on V: on O₁ we have χ = 1, and off tsupport η we have η = 0.
   - M₁ ⊆ V: if x ∈ M₁ and x ∈ tsupport η, then x ∈ closure(M₁) ∩ tsupport η = K₁ ⊆ O₁.
   Now let x ∈ M₁. η₀ is identically 0 on the neighbourhood V of x, so x ∉ tsupport η₀. Hence x ∉ tsupport dη₀ and dη₀(x) = 0.
   By (h2), ∂T₁(η₀) = T₁(dη₀) = ∫_{M₁} ξ(x)(dη₀(x)) dH^{m+1}(x). At every x ∈ M₁ the integrand is ξ(x)(0) = 0, because ξ(x) is linear. So the integral is 0 by Mathlib setIntegral_eq_zero_of_forall_eq_zero, which needs no measurability of M₁.

6. (∂T₁(η_l) = 0.) dη_l ∈ 𝒟^{m+1}(U), and tsupport dη_l ⊆ tsupport η_l ⊆ tsupport ψ_l ⊆ G_{z_l}; here support(ψ_l·η) ⊆ support ψ_l (Mathlib tsupport_smul_subset_left). Since z_l ∈ M₁, (h4) and (h1) give
   ∂T₁(η_l) = T₁(dη_l) = c_{z_l}·T(dη_l) = c_{z_l}·∂T(η_l) = c_{z_l}·0 = 0.

7. By steps 4–6, ∂T₁(η) = 0 + Σ_l 0 = 0. ∎

## Key steps

1. K₁ := closure(M₁) ∩ tsupport η is compact and contained in M₁; cover it by finitely many (h4) neighbourhoods G_{z_l}.
2. Choose an open O₁ ⊇ K₁ with closure(O₁) ⊆ ⋃_l G_{z_l}, and a smooth partition of unity (ψ_l) on closure(O₁) subordinate to (G_{z_l}). Then χ := Σ_l ψ_l = 1 on O₁.
3. η = (1 − χ)η + Σ_l ψ_l η in 𝒟^m(U), and ∂T₁ is linear.
4. (1 − χ)η vanishes on the open set O₁ ∪ (ℝ^P ∖ tsupport η) ⊇ M₁. So d((1 − χ)η) = 0 at every point of M₁, and ∂T₁((1 − χ)η) = 0 by (h2) and setIntegral_eq_zero_of_forall_eq_zero.
5. tsupport d(ψ_l η) ⊆ G_{z_l}, so ∂T₁(ψ_l η) = c_{z_l}·∂T(ψ_l η) = 0 by (h4) and (h1).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (identical)`
- `python3 over dag.json: lean_name set of the 58 nodes; regcomp_null_compact_ball_cover, regcomp_smooth_cutoff_product, regcomp_localized_boundary_zero, regcomp_boundary_smul_estimate not reserved; grep -rl of the four names in the run directory and GMT/ (no match); selected node depth 2, status decomposing, frozen lean_statement unchanged`
- `grep -rln 'hausdorffMeasure_apply|ContDiffBump|SmoothPartitionOfUnity|norm_alternatizeUncurryFin_le|extDeriv_smul|fderiv_smul|enorm_integral_le_lintegral_enorm|exists_isSubordinate' simongmt/Poincare`
- `grep -rn 'theorem.*cover|lemma.*cover' simongmt/Poincare/SimonGMT/Chapter0[1-3] (hausdorff/null/finite/ball)`
- `read simongmt Chapter02/WhitneyPartition.lean (exists_whitneyBump_derivative_bound), Chapter01/HausdorffContentDensity.lean, Chapter06/Forms.lean, Chapter06/Currents.lean, Chapter06/CurrentLocalEquality.lean`
- `grep Mathlib snapshot: hausdorffMeasure_apply, hausdorffMeasure_zero_singleton, setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_ae_eq_zero, ae_restrict_of_forall_mem, enorm_integral_le_lintegral_enorm, norm_alternatizeUncurryFin_le, fderiv_smul, opNorm_smul_le, norm_smulRight_apply, HasFDerivAt.finsetProd, ContDiff.lipschitzWith_of_hasCompactSupport, norm_fderiv_le_of_lipschitz, ContDiffBump one_of_mem_closedBall/support_eq/contDiff/hasCompactSupport, SmoothPartitionOfUnity.exists_isSubordinate, exists_open_between_and_isCompact_closure, prod_le_one₀, ENNReal.sum_le_tsum, edist_le_ediam_of_mem, lintegral_indicator_const, ofReal_sum_of_nonneg, tsupport_smul_subset_right, support_smul_subset_right, HasCompactSupport.smul_left, fderiv_const_sub, fderiv_zero, ContDiff.continuous_fderiv, ContDiff.differentiable`
- `sed -n 960,1030p book/chapter-07.txt; grep -n 'Proof of 5.11|Now corresponding to any|The letting|To check (1)' book/chapter-07.txt (5.11 at line 976, proof lines 990-1016)`
- `lake env lean /tmp/cutoff-split-chk/T0.lean and T1.lean (parent and four child types elaborate; ContDiff ℝ (⊤ : ℕ∞) ζ ↔ ContDiff ℝ ∞ ζ is Iff.rfl)`
- `lake env lean /tmp/cutoff-split-chk/Assembly.lean and AssemblyAx.lean (parent frozen type from the four children; #print axioms)`
- `lake env lean /tmp/cutoff-split-chk/C1.lean C2.lean C3.lean C3b.lean C4.lean Full.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/cutoff-split-chk/Syn.lean (#synth IsBoundedSMul ℝ (Euclid 3 →L[ℝ] Covector (Euclid 3) 2) fails; NormedSpace found)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyPartition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Module/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-07-source.txt`
- `/tmp/cutoff-split-chk/T1.lean`
- `/tmp/cutoff-split-chk/Assembly.lean`
- `/tmp/cutoff-split-chk/AssemblyAx.lean`
- `/tmp/cutoff-split-chk/C1.lean`
- `/tmp/cutoff-split-chk/C2.lean`
- `/tmp/cutoff-split-chk/C3b.lean`
- `/tmp/cutoff-split-chk/C4.lean`
- `/tmp/cutoff-split-chk/Full.lean`
- `/tmp/cutoff-split-chk/Syn.lean`

Contract and names:
- The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Submission.lean, and the selected frozen type is unchanged.
- None of the four proposed names is reserved in the 58-node DAG.

What SimonGMT does and does not provide:
- No Hausdorff-null ball-cover lemma for Mathlib's μH; its Chapter01 covers use Simon's normalised content.
- No partition-of-unity localisation for GeometricCurrentOn.
- No Leibniz bound for extDeriv.
- These three gaps become children. Chapter02.exists_whitneyBump_derivative_bound supplies the Lipschitz rescaled-bump technique reused in smooth_cutoff_product.

Mathlib facts the children rely on:
- Child 1: hausdorffMeasure_apply and hausdorffMeasure_zero_singleton.
- Child 2: ContDiffBump, ContDiff.lipschitzWith_of_hasCompactSupport, norm_fderiv_le_of_lipschitz and HasFDerivAt.finsetProd.
- Child 3: exists_open_between_and_isCompact_closure, SmoothPartitionOfUnity.exists_isSubordinate (already imported transitively) and setIntegral_eq_zero_of_forall_eq_zero, which needs no measurability of M₁.
- Child 4: enorm_integral_le_lintegral_enorm, fderiv_smul, norm_alternatizeUncurryFin_le and ContinuousLinearMap.opNorm_smul_le. The last is needed because IsBoundedSMul ℝ (Euclid P →L[ℝ] Covector) is not found by instance search.

Lean checks in the scratch copy:
- All four child types elaborate.
- The parent's frozen type compiles from the four children taken as axioms.
- Full.lean kernel-checks the parent and all four children with only propext, Classical.choice and Quot.sound.
