# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.rescale-a1.weighted_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the 'Orientation' bullet of Step 7(ii) of the parent proof, isolated as a pointwise lemma. Conventions: ℝ^P := Eucl P (EuclideanSpace ℝ (Fin P)); Hⁿ := μHE[n]; η(w) := r⁻¹ • (w − x) (definitionally Poincare.SimonGMT.Chapter03.blowUpMap x r); θ′(z) := θ(x + r • z).
Definition used (SimonGMT Chapter03.HasWeightedApproximateTangentSpaceAt): HasWeightedApproximateTangentSpaceAt n N ϑ p Q means finrank ℝ Q = n and, for every f ∈ C_c(ℝ^P, ℝ), Tendsto (s ↦ ∫_{u ∈ blowUpMap p s '' N} f(u) · ϑ(p + s • u) dHⁿ(u)) (𝓝[>] 0) (𝓝 (ϑ(p) · ∫_{u ∈ Q} f(u) dHⁿ(u))), where blowUpMap p s (w) = s⁻¹ • (w − p).
Let z₀ := r⁻¹ • (y − x) = η(y). For f ∈ C_c(ℝ^P, ℝ) and t ∈ ℝ, write F_f(t) := ∫_{u ∈ blowUpMap y t '' M} f(u) · θ(y + t • u) dHⁿ(u). The hypothesis gives finrank Q = n and F_f → θ(y) · ∫_Q f dHⁿ along 𝓝[>] 0, for every f.
1. Value at the point: θ′(z₀) = θ(x + r • r⁻¹ • (y − x)) = θ(x + (y − x)) = θ(y), using r ≠ 0 (smul_inv_smul₀) and add_sub_cancel.
2. Dimension: finrank ℝ Q = n is part of the hypothesis and does not depend on the set or the multiplicity.
3. Set identity: for every s ∈ ℝ, blowUpMap z₀ s '' (η '' M) = blowUpMap y (r s) '' M. By Set.image_image the left side is the image of M under w ↦ s⁻¹ • (r⁻¹ • (w − x) − r⁻¹ • (y − x)). This equals s⁻¹ • r⁻¹ • ((w − x) − (y − x)) = (s⁻¹ r⁻¹) • (w − y) (smul_sub, smul_smul). Also (r s)⁻¹ = s⁻¹ r⁻¹ = r⁻¹ s⁻¹ (mul_inv_rev and commutativity; this holds in the field ℝ for every s, including s = 0). So the map is w ↦ (r s)⁻¹ • (w − y) = blowUpMap y (r s) w.
4. Weight identity: for all s, u, θ′(z₀ + s • u) = θ(x + r • (r⁻¹ • (y − x) + s • u)) = θ(x + (y − x) + (r s) • u) = θ(y + (r s) • u), by smul_add, smul_inv_smul₀ and smul_smul.
5. By steps 3 and 4, for every f ∈ C_c(ℝ^P, ℝ) and every s, ∫_{u ∈ blowUpMap z₀ s '' (η '' M)} f(u) · θ′(z₀ + s • u) dHⁿ(u) = F_f(r s). So the function whose limit is required equals F_f ∘ (s ↦ r s).
6. Tendsto (s ↦ r s) (𝓝[>] 0) (𝓝[>] 0), via tendsto_nhdsWithin_iff:
   (i) s ↦ r s is continuous with value r · 0 = 0 at 0, so it tends to 𝓝 0 along 𝓝 0 and therefore along 𝓝[>] 0 ⊆ 𝓝 0 (nhdsWithin_le_nhds);
   (ii) for s > 0 we have r s > 0 (mul_pos), so the values eventually lie in (0, ∞) (eventually_nhdsWithin_of_forall).
7. Composing the hypothesis with step 6 (Tendsto.comp) gives F_f(r s) → θ(y) · ∫_Q f dHⁿ as s → 0⁺. By step 1 this limit is θ′(z₀) · ∫_Q f dHⁿ, and by step 5 this is exactly the required convergence for f.
8. Steps 2 and 7, the latter for every f ∈ C_c(ℝ^P, ℝ), give HasWeightedApproximateTangentSpaceAt n (η '' M) θ′ (r⁻¹ • (y − x)) Q. ∎

## Key steps

1. θ′(η y) = θ(y) and finrank Q = n is unchanged.
2. blowUpMap (η y) s '' η(M) = blowUpMap y (r s) '' M and θ′(η y + s u) = θ(y + (r s) u), so the rescaled integral at s equals the original one at r s.
3. s ↦ r s maps 𝓝[>] 0 to 𝓝[>] 0; compose the defining limit with it (Tendsto.comp).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/{Contract,Submission}.lean against the workspace copies (identical; Submission imports Densities, Rectifiable, Mass, FormsDuality, CurrentLocalEquality only)`
- `grep -rln AffineCurrentPushforward lake-packages-25730c7c/simongmt/Poincare (only SimonGMT.lean and Chapter06/GeometricPointProduct.lean; not in the Submission import closure)`
- `grep -n '^def\|^theorem' simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Currents,Mass,Forms,FormsDuality}.lean`
- `sed -n 90,140p; 320,360p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, blowUpMap, HasWeightedApproximateTangentSpaceAt)`
- `python3 -I scan of dag.json lean_name/lean_statement/status (362 nodes): ind_*, fiw_*, lpf_wtc_*, deformation_dilation, iwl_sp_massOn_le_of_compatible; grep -rl 'ind_rs_' over the run dir (no match)`
- `git show 8389acdfdd73d9fc3fa8f08ede1aff9d04d17e88:GMT/Ch06/Submission.lean (accepted proof of Submission.lpf_wtc_blowup_setIntegral_image)`
- `grep -rn mathlib/Mathlib for euclideanHausdorffMeasure_smul₀ | Isometry.euclideanHausdorffMeasure_image | euclideanHausdorffMeasure_homothety_image | MeasurePreserving.integrableOn_image | restrict_image_emb | MeasurableEmbedding.map_apply | ae_map_iff | aestronglyMeasurable_map_iff | ae_smul_measure | NullMeasurableSet.congr | toMeasurable_ae_eq | ae_eq_set | map_smul_univ | compContinuousLinearMap_apply | Homeomorph.isProperMap | setIntegral_image_emb | integral_smul_measure`
- `cmp local-references/197bdd4b88278494/mathlib/Mathlib/<14 cited files> against .lake/packages/mathlib/Mathlib (all identical)`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') + verifier/lean_contract.py validate_lean_statement on the 5 child statements`
- `lake env lean /tmp/ind-rs-decomp/{Stmts,Assembly}.lean and /tmp/ind-rs-decomp/children/{C1,C2,C3,C4,C5,EndToEnd}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Module.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Maps/Proper/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-rescale-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ind-rs-decomp/Stmts.lean`
- `/tmp/ind-rs-decomp/Assembly.lean`
- `/tmp/ind-rs-decomp/children/EndToEnd.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract and a byte-identical Submission. All 14 cited Mathlib files match the build tree.

Imports and available API:
- The Submission does not import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward. That module supplies affinePullbackForm/affinePullbackTestOn, TestFormOnConverges.affinePullback, GeometricCurrentOn.affinePushforward(_apply) and boundary_affinePushforward. The parent implementation uses them; child statements avoid them.
- SimonGMT gives blowUpMap, HasWeightedApproximateTangentSpaceAt (Chapter03), massAdmissibleOn, massOn and le_massOn (Chapter06/Mass), and GeometricCurrentOn.ext and zero_apply (Currents).
- Mathlib gives Measure.euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, MeasurePreserving.{integrableOn_image, restrict_image_emb, setIntegral_image_emb}, MeasurableEmbedding.{map_apply, ae_map_iff, aestronglyMeasurable_map_iff}, Measure.ae_smul_measure, NullMeasurableSet.congr, toMeasurable_ae_eq, ae_eq_set, ContinuousAlternatingMap.map_smul_univ and Homeomorph.isProperMap.

Existing declarations (no-match results):
- No accepted DAG declaration covers dilation measure-preservation, weighted-tangent transfer, rectifiable-triple transfer or the dilation mass bound.
- deformation_dilation (decomposing, different form ρ^k ω(ρ x)) and iwl_sp_massOn_le_of_compatible (decomposing) are not accepted, so they are not reused.
- The accepted Submission.lpf_wtc_blowup_setIntegral_image (identical frozen type, PR still open) is reused by tau_action, which also carries a self-contained fallback.
- No ind_rs_* name exists anywhere in the run.

Lean verification:
- All five child statements elaborate in the replayed contract scope.
- Assembly.lean derives the exact frozen ind_rescaled_current type from the triple_image, tau_action and mass_bound types; axioms: propext, Classical.choice, Quot.sound.
- Scratch proofs of all five children compile with only `import GMT.Ch06.Submission`.
- EndToEnd.lean proves the children and the parent with standard axioms only.
