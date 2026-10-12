# Parent-supplied natural-language proof

- Parent DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- Child DAG node: `root.density_and_tangent_cones-a1.blowup_scaling-a1.mass_scaling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 1; scaling identity (1) in the proof of Simon 7.3.1 (chapter-07.txt lines 329–331); mass M_W of Simon 6.2.5 (SimonGMT massOn with the Euclidean coefficient norm).
Conventions. ℝ^P = Euclid P. For x ∈ ℝ^P and λ > 0, η := η_{x,λ} = dilation x λ, η(y) = −λ⁻¹x + λ⁻¹y = λ⁻¹(y − x), and ι(z) := x + λz. For V ⊆ ℝ^P (any subset), 𝒟ⁿ(V) = TestFormOn V n is the set of C^∞ maps ω : ℝ^P → Λⁿ(ℝ^P) (n-covectors) with compact topological support tsupport ω ⊆ V; elements of 𝒟ⁿ(V) are determined by their underlying forms. η_#Y := η_{x,λ#}Y = blowUp Y x λ for Y ∈ 𝒟_n(U). For a current Y with domain V and W ⊆ ℝ^P put Adm(V,W) := {ω ∈ 𝒟ⁿ(V) : tsupport ω ⊆ W and |ω(y)| ≤ 1 for all y} (|·| the Euclidean coefficient norm; massAdmissibleOn V n W), so M_W(Y) = sup{ofReal(Y(ω)) : ω ∈ Adm(V,W)} ∈ [0,∞]. Put S := η_#T and c := λ^{−n} ≥ 0.
1. Facts on η: η is an affine homeomorphism of ℝ^P with inverse ι: η is y ↦ λ⁻¹y (a homeomorphism, λ⁻¹ ≠ 0) followed by the translation z ↦ z − λ⁻¹x, η(ι(z)) = λ⁻¹(x + λz − x) = z and ι(η(y)) = x + λ·λ⁻¹(y − x) = y. In particular η is injective and η⁻¹(η(W)) = W. For continuous h and any f, tsupport(f∘h) ⊆ h⁻¹(tsupport f), since h⁻¹(tsupport f) is closed and contains {f∘h ≠ 0} = h⁻¹{f ≠ 0}.
2. Upper bound. Let ω ∈ Adm(η(U), η(W)). By testform_correspondence (a) choose ω' ∈ 𝒟ⁿ(U) with ω'(y) = ω(η(y)) for all y. Then ω' ∈ Adm(U,W): since ω' = ω∘η, tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(W)) = W, and |ω'(y)| = |ω(η(y))| ≤ 1. By testform_correspondence (c), S(ω) = c·T(ω'). As c ≥ 0, ofReal(S(ω)) = ofReal(c·T(ω')) = ofReal(c)·ofReal(T(ω')) ≤ ofReal(c)·M_W(T). Taking the supremum over ω gives M_{η(W)}(S) ≤ ofReal(c)·M_W(T).
3. Lower bound. Multiplication by a fixed element of [0,∞] commutes with suprema (ENNReal.mul_sSup), so ofReal(c)·M_W(T) = sup{ofReal(c)·ofReal(T(ω')) : ω' ∈ Adm(U,W)}. Let ω' ∈ Adm(U,W). By testform_correspondence (b) choose ω ∈ 𝒟ⁿ(η(U)) with ω'(y) = ω(η(y)) for all y. For every z, ω(z) = ω(η(ι(z))) = ω'(ι(z)), i.e. ω = ω'∘ι; hence tsupport ω ⊆ ι⁻¹(tsupport ω') ⊆ ι⁻¹(W) ⊆ η(W) (if ι(z) ∈ W then z = η(ι(z)) ∈ η(W)), and |ω(z)| = |ω'(ι(z))| ≤ 1. Thus ω ∈ Adm(η(U), η(W)), and by testform_correspondence (c), ofReal(c)·ofReal(T(ω')) = ofReal(c·T(ω')) = ofReal(S(ω)) ≤ M_{η(W)}(S). Taking the supremum over ω' gives ofReal(c)·M_W(T) ≤ M_{η(W)}(S).
4. By steps 2 and 3, M_{η(W)}(η_{x,λ#}T) = ofReal(λ^{−n})·M_W(T). No hypothesis on U, W or n was used. ∎
Formalization notes (proved in a scratch build from the sibling's exact type): unfold GeometricCurrentOn.massOn and use le_antisymm; for ≤ use sSup_le with `rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩`, `dsimp only`, rewrite with the sibling's evaluation formula and ENNReal.ofReal_mul (positivity), then gcongr and le_sSup; for ≥ rewrite with ENNReal.mul_sSup and use iSup₂_le; supports via tsupport_comp_subset_preimage and Set.preimage_image_eq.

## Key steps

1. Each admissible ω for η_#T on η(W) gives the admissible ω' = ω∘η for T on W with η_#T(ω) = λ^{−n}T(ω'), so M_{η(W)}(η_#T) ≤ ofReal(λ^{−n})M_W(T).
2. Each admissible ω' for T on W gives the admissible ω = ω'∘ι for η_#T on η(W); multiplication by ofReal(λ^{−n}) commutes with suprema, giving the reverse inequality.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean GMT/Ch07/Submission.lean (both identical; manifest project b4d606d, mathlib 25730c7c)`
- `rg -n 'theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|theorem Isometry.euclideanHausdorffMeasure_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem restrict_map \(μ|theorem ae_map_iff \{p' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'MeasurableEmbedding.lintegral_map|MeasurableEmbedding.integral_map |MeasurableEmbedding.aestronglyMeasurable_map_iff' mathlib/Mathlib`
- `rg -n 'theorem map_smul_univ' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean; rg -n 'comp_homeomorph' mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n 'theorem preimage_closure|theorem image_closure' mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `grep -n '^def\|^theorem' simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Mass,CurrentLocalEquality,Currents,Forms}.lean simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (affinePullbackForm, affinePushforward_apply, boundary_affinePushforward, exteriorDerivative_affinePullbackForm, massOn, massAdmissibleOn, restrictDomain_apply, zeroRegion, support, CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap)`
- `grep -rl -F <each proposed lean_name> runs/20261011T150044Z-ba604216b4 (no match) and lean_name inventory of dag.json and all node JSON files (no collision)`
- `contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all eight child types`
- `lake build GMT.Ch07.Submission; lake env lean Check/FinalExact.lean, Check/FinalAssembly.lean, Check/FinalLeaves.lean with #print axioms (scratch /tmp/bscale-decomp-6cU90O/proj)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Homeomorph/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalExact.lean`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalAssembly.lean`
- `/tmp/bscale-decomp-6cU90O/proj/Check/FinalLeaves.lean`

The snapshot contract and submission (project b4d606d, mathlib 25730c7c) are byte-identical to the workspace files. SimonGMT supplies the objects the children reason about: blowUp is an affinePushforward of a restrictDomain; affinePullbackForm comes with affinePushforward_apply, boundary_affinePushforward and exteriorDerivative_affinePullbackForm (used for blowup_structure (iv)); massOn/massAdmissibleOn (mass_scaling); zeroRegion/support/VanishesOn (blowup_structure (iii)); CountablyRectifiable and HasApproximateTangentSpaceAt via blowUpMap (rep_pushforward, tangent_invariance). It contains no dilation or blow-up lemmas, so the children supply them. The pinned Mathlib supplies the measure-theoretic and multilinear ingredients: euclideanHausdorffMeasure_smul₀ and Isometry.euclideanHausdorffMeasure_image (hausdorff_scaling); MeasurableEmbedding.restrict_map, lintegral_map, integral_map, ae_map_iff and aestronglyMeasurable_map_iff (rep_pushforward); ContinuousAlternatingMap.map_smul_univ and HasCompactSupport.comp_homeomorph (testform_correspondence); Homeomorph.preimage_closure and image_closure (blowup_structure, minimality). All eight child types elaborate in the comparator scope. Scratch Lean proofs of every child, and of the parent from the children, compile using only propext, Classical.choice and Quot.sound. No proposed name occurs elsewhere in the run.
