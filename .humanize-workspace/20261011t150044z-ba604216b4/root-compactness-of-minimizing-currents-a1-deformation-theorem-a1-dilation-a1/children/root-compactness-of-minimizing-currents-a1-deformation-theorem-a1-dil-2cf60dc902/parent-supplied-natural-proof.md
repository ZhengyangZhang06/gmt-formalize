# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1.mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the supplied proof of cmcdt_dilation_pushforward. Simon 6.5.3 (chapter-06.txt lines 1458–1460) obtains the scaled deformation theorem by the changes of scale x ↦ λ⁻¹x and x ↦ λx, which scale masses of k-currents by λ^{∓k}. The coefficient-norm identity |α∘(λ·id)| = λ^k|α| of the supplied step 5 is used in the exact form given by the sibling pullback_testform: λ^{-k}(δ_λ^#ω)(x) = ω(λx) as covectors, so the Euclidean coefficient norms agree pointwise.

Notation:
- |·| = covectorEuclideanNorm (SimonGMT Chapter06/Mass.lean); ofReal = ENNReal.ofReal.
- 𝒜 := massAdmissibleOn univ k univ = {ω ∈ TestFormOn univ k : tsupport ω ⊆ univ and |ω(x)| ≤ 1 for all x}.
- M(T) = T.mass = T.massOn univ = sSup{ofReal(T ω) : ω ∈ 𝒜}. For ω ∈ 𝒜, ofReal(T ω) ≤ M(T) (GeometricCurrentOn.le_massOn).
- Since λ > 0: λ ≠ 0, λ⁻¹ ≠ 0 and λ^k > 0.
- PT is the sibling pullback_testform (cmcdt_dil_pullback_testForm): for μ ≠ 0 and every ω ∈ TestFormOn univ k there is η ∈ TestFormOn univ k with η = affinePullbackForm (μ·id) 0 ω as forms and η(x) = μ^k • ω(μx) for all x.
- Currents are ℝ-linear on the submodule TestFormOn univ k: T(cω) = c·T(ω); and two elements of TestFormOn univ k are equal when their underlying forms are equal (Subtype.ext).

1. Upper bound M(Y) ≤ ofReal(λ^k)·M(X). M(Y) is a supremum, so it suffices to fix ω ∈ 𝒜 and show ofReal(Y ω) ≤ ofReal(λ^k)·M(X).
 (a) Let η be given by PT for μ = λ and ω. By the hypothesis, Y ω = X η.
 (b) Put η' := (λ^k)⁻¹·η ∈ TestFormOn univ k. For every x, η'(x) = (λ^k)⁻¹·λ^k·ω(λx) = ω(λx), so |η'(x)| = |ω(λx)| ≤ 1; also tsupport η' ⊆ univ. Hence η' ∈ 𝒜 and ofReal(X η') ≤ M(X).
 (c) η = λ^k·η' in TestFormOn univ k, so X η = λ^k·X η' by linearity. As λ^k ≥ 0, ofReal(λ^k·X η') = ofReal(λ^k)·ofReal(X η') (ENNReal.ofReal_mul).
 (d) Therefore ofReal(Y ω) = ofReal(X η) = ofReal(λ^k)·ofReal(X η') ≤ ofReal(λ^k)·M(X) (monotonicity of multiplication in [0,∞]).

2. Lower bound ofReal(λ^k)·M(X) ≤ M(Y). Multiplication by a constant commutes with suprema in [0,∞] (ENNReal.mul_sSup), so ofReal(λ^k)·M(X) = sup_{η∈𝒜} ofReal(λ^k)·ofReal(X η). Fix η ∈ 𝒜; it suffices to show ofReal(λ^k)·ofReal(X η) ≤ M(Y).
 (a) Let ζ be given by PT for μ = λ⁻¹ and η, so ζ(y) = (λ⁻¹)^k·η(λ⁻¹y). Put ω := λ^k·ζ ∈ TestFormOn univ k. Then for every y, ω(y) = λ^k·(λ⁻¹)^k·η(λ⁻¹y) = (λλ⁻¹)^k·η(λ⁻¹y) = η(λ⁻¹y).
 (b) Hence |ω(y)| = |η(λ⁻¹y)| ≤ 1 for every y, and tsupport ω ⊆ univ. So ω ∈ 𝒜 and ofReal(Y ω) ≤ M(Y).
 (c) Let η₂ be given by PT for μ = λ and ω: η₂ = affinePullbackForm (λ·id) 0 ω as forms, and for all x, η₂(x) = λ^k·ω(λx) = λ^k·η(λ⁻¹λx) = λ^k·η(x). Thus η₂ = λ^k·η in TestFormOn univ k (Subtype.ext, funext).
 (d) By the hypothesis (applied to ω and η₂) and linearity, Y ω = X η₂ = X(λ^k·η) = λ^k·X η. So ofReal(λ^k)·ofReal(X η) = ofReal(λ^k·X η) = ofReal(Y ω) ≤ M(Y).

3. By 1, 2 and antisymmetry of ≤ on [0,∞], Y.mass = ofReal(λ^k)·X.mass. The argument is uniform in k, including k = 0 (λ^0 = 1), and uses no finiteness of M(X): both sides may be ∞ (if M(X) = ∞, step 2 gives M(Y) = ∞ because ofReal(λ^k) ≠ 0). ∎

## Key steps

1. Upper bound: for admissible ω (|ω| ≤ 1) let η = δ_λ^#ω from pullback_testform; then (λ^k)⁻¹η(x) = ω(λx), so (λ^k)⁻¹η is admissible and Y(ω) = X(η) = λ^k X((λ^k)⁻¹η) ≤ λ^k M(X).
2. Lower bound: for admissible η, ω := λ^k δ_{λ⁻¹}^#η satisfies ω(y) = η(λ⁻¹y), so ω is admissible; and δ_λ^#ω = λ^k η, giving λ^k X(η) = Y(ω) ≤ M(Y).
3. ENNReal.mul_sSup and ENNReal.ofReal_mul turn the two bounds into Y.mass = ofReal(λ^k)·X.mass (le_antisymm), with no finiteness assumption.

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
