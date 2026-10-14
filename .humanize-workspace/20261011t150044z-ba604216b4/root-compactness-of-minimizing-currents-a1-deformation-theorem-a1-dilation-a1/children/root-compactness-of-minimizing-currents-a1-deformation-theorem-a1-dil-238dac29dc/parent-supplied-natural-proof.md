# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.dilation-a1.integer_multiplicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 7 of the supplied proof of cmcdt_dilation_pushforward: δ_{λ#} maps τ(M, θ, ξ) to τ(λM, θ(·/λ), ξ(·/λ)). Compare Simon 6.3.3 (chapter-06.txt lines 766–790), the push-forward of an integer multiplicity current by a 1:1 map, here δ_λ with dδ_λ = λ·id; the argument also uses Hausdorff scaling and the dilation invariance of approximate tangent spaces (Simon Ch. 3, 1.4).

Notation:
- H^k := μHE[k]; ν⌞E := ν.restrict E; δ_μ(x) := μx.
- c₀ := ofReal((λ⁻¹)^k). Since (λ⁻¹)^k > 0, we have 0 < c₀ < ∞.
- PT is the sibling pullback_testform (cmcdt_dil_pullback_testForm): for μ ≠ 0 and every ω ∈ TestFormOn univ k there is η ∈ TestFormOn univ k with η = affinePullbackForm (μ·id) 0 ω as forms and η(x) = μ^k • ω(μx) for all x.
- CV is the sibling hausdorff_change_of_variables (euclid_hausdorff_dilation_change_of_variables): for c > 0 and any set S ⊆ ℝ^P,
 (i) (δ_c)_#(H^k⌞δ_c⁻¹(S)) = ofReal(c^{-k})·H^k⌞S,
 (ii) ∫⁻_{δ_c⁻¹(S)} g(cz) dH^k(z) = ofReal(c^{-k})·∫⁻_S g dH^k for all g : ℝ^P → [0,∞],
 (iii) ∫_{δ_c⁻¹(S)} g(cz) dH^k(z) = c^{-k}·∫_S g dH^k for all g : ℝ^P → ℝ.
- AT is the sibling approx_tangent (dtc_approxTangent_dilation): for μ > 0, HasApproximateTangentSpaceAt k M y Q implies HasApproximateTangentSpaceAt k (dilation x μ '' M) (dilation x μ y) Q.

Let R = (M, θ, ξ) : IMRep univ k represent X, i.e. X(ω) = R.action ω = ∫_M θ(x)·ξ(x)(ω(x)) dH^k(x) for every ω ∈ TestFormOn univ k. Define M' := δ_{λ⁻¹}⁻¹(M) = {y : λ⁻¹y ∈ M}, θ'(y) := θ(λ⁻¹y) and ξ'(y) := ξ(λ⁻¹y).

0. Preliminaries.
 (a) M' = δ_λ(M): if x ∈ M then λ⁻¹(λx) = x ∈ M; if y ∈ M' then y = λ(λ⁻¹y) with λ⁻¹y ∈ M. Moreover δ_λ⁻¹(δ_{λ⁻¹}⁻¹(S)) = S for every set S, since λ⁻¹(λx) = x. In particular δ_λ⁻¹(M') = M and δ_λ⁻¹(M' ∩ K) = M ∩ δ_λ⁻¹(K) for every K.
 (b) δ_λ is a homeomorphism (Homeomorph.smulOfNeZero λ), hence a measurable embedding.
 (c) CV with c = λ and S = M', rewritten by (a), gives:
  (i) (δ_λ)_#(H^k⌞M) = c₀·H^k⌞M';
  (iii) ∫_M g(λz) dH^k(z) = (λ⁻¹)^k·∫_{M'} g dH^k for every g : ℝ^P → ℝ.
 (d) A.e. transfer: if ∀ᵐ x ∂(H^k⌞M), p(λx), then ∀ᵐ y ∂(H^k⌞M'), p(y). By (b) and MeasurableEmbedding.ae_map_iff, p holds a.e. for (δ_λ)_#(H^k⌞M) = c₀·H^k⌞M'. Since c₀ ≠ 0, holding a.e. for c₀·ν is the same as holding a.e. for ν (Measure.ae_ennreal_smul_measure_iff).
 (e) dilation 0 λ⁻¹ = δ_λ: dilation 0 μ y = −(μ⁻¹·0) + μ⁻¹y = μ⁻¹y, and (λ⁻¹)⁻¹ = λ.

1. R' := (M', θ', ξ') is an IMRep in univ of degree k; we verify every field.
 - Borel carrier: M' is the preimage of the Borel set M under the continuous (hence measurable) map δ_{λ⁻¹}.
 - M' ⊆ univ trivially.
 - Countably k-rectifiable: R.rectifiable gives M₀ with H^k(M₀) = 0 and maps F_j : ℝ^k → ℝ^P (j ∈ ℕ), each Lipschitz with some constant K_j, with M ⊆ M₀ ∪ ⋃_j range F_j. Let M₀' := δ_λ(M₀) = λ·M₀ and F_j' := δ_λ ∘ F_j.
  · H^k(λ·M₀) = ‖λ‖₊^k·H^k(M₀) = 0 (Measure.euclideanHausdorffMeasure_smul₀, valid for every set).
  · F_j' is Lipschitz with constant ‖λ‖₊K_j (lipschitzWith_smul composed with F_j).
  · For y ∈ M' we have λ⁻¹y ∈ M. Either λ⁻¹y ∈ M₀, and then y = λ(λ⁻¹y) ∈ M₀'; or λ⁻¹y = F_j(z) for some j and z, and then y = λF_j(z) = F_j'(z).
  Hence M' ⊆ M₀' ∪ ⋃_j range F_j'.
 - θ' = θ ∘ δ_{λ⁻¹} is measurable (composition of measurable maps) and ℕ-valued; for y ∈ M', θ'(y) = θ(λ⁻¹y) > 0 because λ⁻¹y ∈ M.
 - Local integrability: let K be compact (K ⊆ univ). Apply CV(ii) with c = λ and S = M' ∩ K, using δ_λ⁻¹(M' ∩ K) = M ∩ δ_λ⁻¹(K) from (a) and θ'(λz) = θ(z):
  ∫⁻_{M∩δ_λ⁻¹(K)} θ dH^k = c₀·∫⁻_{M'∩K} θ' dH^k.
  The set δ_λ⁻¹(K) = λ⁻¹K is compact (preimage of a compact set under the homeomorphism δ_λ), so the left side is finite by R.locallyIntegrable_mult. If ∫⁻_{M'∩K} θ' dH^k were ∞, the right side would be c₀·∞ = ∞ (as c₀ ≠ 0), a contradiction. So ∫⁻_{M'∩K} θ' dH^k ≠ ∞.
 - A.e. strong measurability of ξ': ξ' ∘ δ_λ = ξ (as ξ'(λx) = ξ(λ⁻¹λx) = ξ(x)), and ξ is a.e. strongly measurable for H^k⌞M. By MeasurableEmbedding.aestronglyMeasurable_map_iff, ξ' is a.e. strongly measurable for (δ_λ)_#(H^k⌞M) = c₀·H^k⌞M'. Multiplying the measure by c₀⁻¹ preserves this (AEStronglyMeasurable.smul_measure), and c₀⁻¹·(c₀·H^k⌞M') = H^k⌞M' because 0 < c₀ < ∞ (ENNReal.inv_mul_cancel).
 - Orientation: by (d), it suffices that for H^k⌞M-a.e. x there is Q with HasApproximateTangentSpaceAt k M' (λx) Q and IsUnitOrientationOf (ξ'(λx)) Q. By R.orients, for a.e. x there is Q with HasApproximateTangentSpaceAt k M x Q and IsUnitOrientationOf (ξ(x)) Q. Then:
  · ξ'(λx) = ξ(λ⁻¹λx) = ξ(x), so the orientation condition carries over;
  · AT with base point 0, scale μ = λ⁻¹ > 0 and y = x gives HasApproximateTangentSpaceAt k (dilation 0 λ⁻¹ '' M) (dilation 0 λ⁻¹ x) Q, and by (e) and (a), dilation 0 λ⁻¹ '' M = δ_λ(M) = M' and dilation 0 λ⁻¹ x = λx.

2. R' represents Y. Fix ω ∈ TestFormOn univ k and let η be given by PT for λ and ω: η = affinePullbackForm (λ·id) 0 ω as forms and η(x) = λ^k·ω(λx). By the hypothesis and R.Represents X,
 Y(ω) = X(η) = ∫_M θ(x)·ξ(x)(η(x)) dH^k(x) = ∫_M θ(x)·ξ(x)(λ^k·ω(λx)) dH^k(x) = λ^k·∫_M θ(x)·ξ(x)(ω(λx)) dH^k(x),
 using linearity of the continuous linear functional ξ(x) and pulling the constant out of the Bochner integral (integral_const_mul, valid without integrability). Now apply (c)(iii) to g(y) := θ'(y)·ξ'(y)(ω(y)); since g(λz) = θ(z)·ξ(z)(ω(λz)),
 ∫_M θ(z)·ξ(z)(ω(λz)) dH^k(z) = (λ⁻¹)^k·∫_{M'} θ'(y)·ξ'(y)(ω(y)) dH^k(y) = (λ⁻¹)^k·R'.action ω.
 Hence Y(ω) = λ^k(λ⁻¹)^k·R'.action ω = (λλ⁻¹)^k·R'.action ω = R'.action ω.

3. So R' represents Y, and Y is integer multiplicity (witness R'). Nothing in the argument depends on k, so it holds in every degree, including k = 0. ∎

## Key steps

1. New triple: M' = δ_{λ⁻¹}⁻¹(M) = λM, θ' = θ(·/λ), ξ' = ξ(·/λ); M' is Borel and θ' is measurable, ℕ-valued and positive on M'.
2. Rectifiability via λM₀ (Hausdorff-null by euclideanHausdorffMeasure_smul₀) and the Lipschitz maps λF_j.
3. Change of variables (euclid_hausdorff_dilation_change_of_variables, c = λ): (δ_λ)_#(H^k⌞M) = λ^{-k} H^k⌞M'; this gives local integrability, a.e. strong measurability of ξ' and a.e. transfer from M to M'.
4. Approximate tangent planes are dilation invariant (dtc_approxTangent_dilation with dilation 0 λ⁻¹ = δ_λ), so ξ'(λx) = ξ(x) orients T_{λx}M'.
5. Representation: Y(ω) = X(δ_λ^#ω) = λ^k∫_M θ ξ(ω(λ·)) dH^k = λ^kλ^{-k}∫_{M'} θ' ξ'(ω) dH^k = R'.action ω.

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
