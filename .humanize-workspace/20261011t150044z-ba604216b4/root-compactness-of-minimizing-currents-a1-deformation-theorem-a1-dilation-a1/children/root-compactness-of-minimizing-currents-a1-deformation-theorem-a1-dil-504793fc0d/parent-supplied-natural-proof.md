# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1.support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the supplied proof of cmcdt_dilation_pushforward: zero regions scale by λ (Simon 6.2.11 for supports; 6.5.3 for the change of scale, chapter-06.txt lines 1458–1460).

Notation:
- δ_μ(x) := μx.
- PT is the sibling pullback_testform (cmcdt_dil_pullback_testForm): for μ ≠ 0 and every ω ∈ TestFormOn univ k there is η ∈ TestFormOn univ k with η = affinePullbackForm (μ·id) 0 ω as forms and η(x) = μ^k • ω(μx) for all x.
- 𝒲_T := {W ⊆ ℝ^P : W open, closure W compact, closure W ⊆ univ, T vanishes on W}, so Z_T = ⋃𝒲_T (GeometricCurrentOn.zeroRegion) and spt T = univ \ Z_T (GeometricCurrentOn.support).
- Since λ > 0, λ ≠ 0 and λ⁻¹ ≠ 0.

0. Preliminary facts.
 (a) For μ ≠ 0, δ_μ is a homeomorphism with inverse δ_{μ⁻¹} (Homeomorph.smulOfNeZero). If W is open then δ_μ(W) is open. If closure W is compact, then K := δ_μ(closure W) is compact (a continuous image), hence closed, and it contains δ_μ(W); so closure δ_μ(W) ⊆ K is a closed subset of a compact set and is compact. Trivially closure δ_μ(W) ⊆ univ.
 (b) Support of a pull-back: if ω, η are test forms with η(x) = μ^k·ω(μx) for all x, then tsupport η ⊆ δ_μ⁻¹(tsupport ω). Indeed, if η(x) ≠ 0 then ω(μx) ≠ 0 (otherwise η(x) = μ^k·0 = 0), so x ∈ δ_μ⁻¹(support ω) ⊆ δ_μ⁻¹(tsupport ω); the latter set is closed (preimage of a closed set under the continuous δ_μ), hence contains the closure of the support of η.
 (c) Inverse relation: for every test form η there is a test form ζ with X(η) = Y(ζ) and tsupport ζ ⊆ δ_{λ⁻¹}⁻¹(tsupport η). Take ζ from PT with μ = λ⁻¹ applied to η, so ζ(y) = (λ⁻¹)^k·η(λ⁻¹y). Take η₂ from PT with μ = λ applied to ζ: η₂ = affinePullbackForm (λ·id) 0 ζ and η₂(x) = λ^k·ζ(λx) = λ^k(λ⁻¹)^k·η(λ⁻¹λx) = η(x), so η₂ = η (Subtype.ext, funext). The hypothesis gives Y(ζ) = X(η₂) = X(η). The support bound is (b) with μ = λ⁻¹.

1. δ_λ(Z_X) ⊆ Z_Y. Let x ∈ W ∈ 𝒲_X and W' := δ_λ(W). By (a), W' is open with compact closure and closure W' ⊆ univ, and λx ∈ W'. Y vanishes on W': let ω be a test form with tsupport ω ⊆ W', and take η from PT (μ = λ, ω). By the hypothesis Y(ω) = X(η). By (b), tsupport η ⊆ δ_λ⁻¹(tsupport ω) ⊆ δ_λ⁻¹(δ_λ(W)) = W, as δ_λ is injective. Since X vanishes on W, X(η) = 0, so Y(ω) = 0. Thus W' ∈ 𝒲_Y and λx ∈ Z_Y.

2. Z_Y ⊆ δ_λ(Z_X). Let y ∈ W ∈ 𝒲_Y and W'' := δ_{λ⁻¹}(W). By (a), W'' is open with compact closure and closure W'' ⊆ univ, and λ⁻¹y ∈ W''. X vanishes on W'': let η be a test form with tsupport η ⊆ W'', and take ζ from (c). Then X(η) = Y(ζ) and tsupport ζ ⊆ δ_{λ⁻¹}⁻¹(tsupport η) ⊆ δ_{λ⁻¹}⁻¹(δ_{λ⁻¹}(W)) = W (δ_{λ⁻¹} is injective). Since Y vanishes on W, Y(ζ) = 0, so X(η) = 0. Thus W'' ∈ 𝒲_X, λ⁻¹y ∈ Z_X, and y = λ(λ⁻¹y) ∈ δ_λ(Z_X).

3. By 1 and 2, Z_Y = δ_λ(Z_X). The map δ_λ is injective and surjective (y = δ_λ(λ⁻¹y)), so δ_λ(univ) = univ and images under δ_λ commute with set differences (Set.image_sdiff for injective maps, Set.image_univ_of_surjective):
 spt Y = univ \ δ_λ(Z_X) = δ_λ(univ) \ δ_λ(Z_X) = δ_λ(univ \ Z_X) = δ_λ(spt X) = (fun x => λ•x) '' X.support. ∎

## Key steps

1. tsupport(δ_μ^#ω) ⊆ δ_μ⁻¹(tsupport ω), because (δ_μ^#ω)(x) = μ^k ω(μx); and δ_μ maps open sets with compact closure to open sets with compact closure.
2. Inverse relation: ζ := δ_{λ⁻¹}^#η satisfies δ_λ^#ζ = η, so X(η) = Y(ζ) with tsupport ζ ⊆ λ·tsupport η.
3. If X vanishes on W then Y vanishes on λW; if Y vanishes on W then X vanishes on λ⁻¹W. Hence Z_Y = λZ_X.
4. δ_λ is a bijection of ℝ^P, so spt Y = univ \ λZ_X = λ(univ \ Z_X) = λ spt X.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `sed -n 1,320p GMT/Ch07/Submission.lean (IMRep fields, IMRep.action, IMRep.Represents, IsIntegerMultiplicity, pointwise Sub instance, dilationCLM, dilation, blowUp)`
- `grep -n 'def \|theorem ' simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Mass,CurrentLocalEquality,Currents}.lean (affinePullbackForm, affinePullbackForm_isTestForm, tsupport_affinePullbackForm_subset, affinePullbackTestOn_coe, affinePushforward, affinePushforward_apply, boundary_affinePushforward, covectorEuclideanNorm, massAdmissibleOn, massOn, mass, le_massOn, testFormOnInclusion_coe, restrictDomain_apply, VanishesOn, zeroRegion, support, GeometricCurrentOn.ext)`
- `grep -n 'def CountablyRectifiable\|def blowUpMap\|def HasApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'cmcdt_dil|euclid_hausdorff_dilation_change_of_variables|dtc_approxTangent_dilation' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib lake-packages-25730c7c/simongmt -g '*.lean' (no match)`
- `rg -n 'euclideanHausdorffMeasure_smul|aestronglyMeasurable_map_iff|ae_ennreal_smul_measure_iff|theorem restrict_map|theorem lintegral_map|theorem integral_map|theorem map_smul_univ|theorem image_sdiff|smulOfNeZero' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (all found)`
- `python3 scan of dag.json (995 nodes): lean_name collisions for cmcdt_dil_pullback_testForm, cmcdt_dil_mass_eq, cmcdt_dil_support_eq, cmcdt_dil_isIntegerMultiplicity (none); reused nodes' lean_statement string-equal to the proposal, status accepted, isolated-comparator-result.json passed=true; regex over all lean_statements for affinePullbackForm/affinePushforward/blowUp/dilation together with mass/support/IMRep (dtc_blowUp_algebra, dtc_blowUp_massOn_image, dtc_blowUp_imrep accepted but stated for blowUp on dilation x lam '' U)`
- `grep -rl over nodes/*/decomposition-v*.json and dag.json for the four new names (only this node's own attempt-1 records)`
- `git cat-file -t and git show 22204a6d923d28f1c362798e3e4f529019c709a5:GMT/Ch07/Submission.lean, 2b0c51405c3f7d305798214e74d0447c1d210ae1:GMT/Ch07/Submission.lean (reused declarations present with identical types)`
- `sed -n 400,414p; 760,792p; 1450,1465p book/chapter-06.txt (Simon 6.2.23-2.24, 6.3.3, 6.5.3)`
- `lake env lean /tmp/cmcdt-dil-a2/FullChain.lean (six child types and parent proved; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/cmcdt-dil-a2/Types2.lean (six child types generated from the proposal strings elaborate; pp.explicit instance check; rfl checks)`
- `lake env lean /tmp/cmcdt-dil-a2/Assembly2.lean (frozen parent type from six stubs; axioms propext, sorryAx from stubs only, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/ConstMulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-dilation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-dilation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-dilation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1-862a12a643/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1-862a12a643/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-tangent-invariance-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-tangent-invariance-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_dilation_decomposition/FullChain.lean`
- `/tmp/cmcdt-dil-a2/Types2.lean`
- `/tmp/cmcdt-dil-a2/Assembly2.lean`
- `/tmp/cmcdt-dil-a2/FullChain.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) contract matches the workspace Contract.lean and Submission.lean byte for byte. The installed SimonGMT (2b366308) supplies every object the children use: affinePullbackForm, affinePullbackForm_isTestForm, affinePushforward, boundary_affinePushforward, massAdmissibleOn/massOn/le_massOn, VanishesOn/zeroRegion/support, restrictDomain, CountablyRectifiable, blowUpMap and HasApproximateTangentSpaceAt. Snapshot Mathlib has every cited lemma: euclideanHausdorffMeasure_smul₀, the MeasurableEmbedding API (restrict_map, lintegral_map, integral_map, ae_map_iff, aestronglyMeasurable_map_iff), ae_ennreal_smul_measure_iff, ContinuousAlternatingMap.map_smul_univ, Set.image_sdiff and Homeomorph.smulOfNeZero. The reference library has no dilation push-forward lemmas for currents on univ. The DAG's accepted dtc_blowUp_* lemmas live on the domain dilation x lam '' U, so they are not used. The two reused declarations are accepted, passed the isolated comparator, exist in their candidate commits, and have DAG types string-identical to this proposal. The four new names are free. All six child types elaborate, with the intended instances verified. The frozen parent compiles from the six stubs, and the full chain compiles using only propext, Classical.choice and Quot.sound.
