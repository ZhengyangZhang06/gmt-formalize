# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1`
- Child DAG node: `root.integral_compactness-a1.rescaled_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step B4 of the parent proof of Simon 8.5.9 ("each W_k is integral: homotheties and restriction to open sets preserve IsVarifoldOf with integer θ; approximate tangent planes are local and homothety-invariant; H^n(ξ + λA) = λ^n H^n(A)"), written out. Notation: G := Grassmannian N n; H^n := μHE[n]; approx(M,θ,x,S) abbreviates HasWeightedApproximateTangentSpaceAt n M θ x S.plane; rescaledMeasure V ξ t = ofReal(t^{-n}) • (V.measure).map Φ with Φ(z,S) := (t^{-1}(z − ξ), S).

1. The similarity. Let σ(y) := ξ + t y and η := σ^{-1}, η(x) = t^{-1}(x − ξ); both are homeomorphisms, hence measurable equivalences, of ℝ^N. For every A ⊆ ℝ^N, H^n(σ(A)) = t^n H^n(A) and H^n(η(A)) = t^{-n} H^n(A) (translation invariance of μHE[n] together with Mathlib MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ / MeasureTheory.euclideanHausdorffMeasure_homothety_image). Consequently σ and η map H^n-null sets to H^n-null sets, Borel sets to Borel sets and H^n-null-measurable sets to H^n-null-measurable sets. Moreover, for every A ⊆ ℝ^N (measurable or not), H^n⌞σ(A) = t^n·σ_#(H^n⌞A) as measures: for Borel B, σ_#(H^n⌞A)(B) = H^n(σ^{-1}(B) ∩ A) = H^n(η(B ∩ σ(A))) = t^{-n}H^n(B ∩ σ(A)). Hence, by MeasureTheory.lintegral_map_equiv (for the measurable equivalence σ), ∫⁻_{σ(A)} g dH^n = t^n ∫⁻_A g∘σ dH^n for every g : ℝ^N → [0,∞] and every A ⊆ ℝ^N; likewise ∫⁻_{η(A)} g dH^n = t^{-n} ∫⁻_A g∘η dH^n.

2. Data. By IsIntegral V choose M, θ with IsVarifoldOf V M θ and θ ∈ ℕ for (H^n⌞M)-a.e. point. Define M̂ := {y ∈ O : σ(y) ∈ M} = O ∩ η(M) and θ̂ := θ∘σ. We verify IsVarifoldOf W M̂ θ̂ (steps 3–9) and integrality (step 10).

3. M̂ ⊆ O by definition.

4. M̂ is H^n-null-measurable, because η(M) is (step 1; M is H^n-null-measurable) and O is open.

5. M̂ is countably n-rectifiable. CountablyRectifiable n M gives M_0 with H^n(M_0) = 0 and Lipschitz maps F_j : ℝ^n → ℝ^N (j ∈ ℕ) with M ⊆ M_0 ∪ ⋃_j F_j(ℝ^n). Then η(M) ⊆ η(M_0) ∪ ⋃_j (η∘F_j)(ℝ^n), H^n(η(M_0)) = t^{-n}H^n(M_0) = 0, and η∘F_j is Lipschitz (constant Lip(F_j)/t). So η(M) is countably n-rectifiable, and so is its subset M̂ (CountablyRectifiable.mono).

6. θ̂(y) = θ(σ(y)) > 0 for y ∈ M̂, since σ(y) ∈ M.

7. Local integrability. Let K ⊆ O be compact. Then σ(K) is compact and σ(K) ⊆ U by the hypothesis ξ + t y ∈ U (y ∈ O), so θ is H^n-integrable on M ∩ σ(K). Since K ⊆ O, M̂ ∩ K = η(M ∩ σ(K)), and by step 1 (with g := |θ|∘σ, so g∘η = |θ|), ∫⁻_{M̂∩K} |θ̂| dH^n = ∫⁻_{η(M∩σ(K))} |θ|∘σ dH^n = t^{-n} ∫⁻_{M∩σ(K)} |θ| dH^n < ∞. A Borel function θ_K with θ_K = θ H^n-a.e. on M ∩ σ(K) gives the Borel function θ_K∘σ, equal to θ̂ H^n-a.e. on M̂ ∩ K (η maps null sets to null sets); so θ̂ is a.e.-strongly measurable on M̂ ∩ K, hence H^n-integrable there.

8. Approximate tangent planes are local and homothety-invariant. Claim: for y ∈ O and S ∈ G, approx(M̂, θ̂, y, S) ⇔ approx(M, θ, σ(y), S). Put x := σ(y). For r > 0: blowUpMap y r '' M̂ = {r^{-1}(w − y) : w ∈ O, σ(w) ∈ M}, while blowUpMap x (tr) '' M = {(tr)^{-1}(z − x) : z ∈ M} = {r^{-1}(w − y) : σ(w) ∈ M} (substitute z = σ(w) and use (tr)^{-1}(σ(w) − σ(y)) = r^{-1}(w − y)). Moreover θ̂(y + r v) = θ(x + (tr)v) and θ̂(y) = θ(x). Let f ∈ C_c(ℝ^N) with support in B_R(0) (closed ball). If O = ℝ^N, or rR < dist(y, ℝ^N ∖ O), then y + r v ∈ O for every |v| ≤ R, so the two (possibly non-measurable) image sets have the same intersection with B_R(0). Since f vanishes off B_R(0), each set integral equals the integral of the same function against H^n restricted to (image set) ∩ B_R(0) (Measure.restrict_restrict for the Borel set B_R(0)); these restricted measures coincide, so integrability and the values agree: ∫_{blowUpMap y r '' M̂} f(v) θ̂(y + r v) dH^n(v) = ∫_{blowUpMap x (tr) '' M} f(v) θ(x + (tr)v) dH^n(v). Since r ↦ tr maps 𝓝[>]0 onto 𝓝[>]0 (t > 0) and the prescribed limits θ̂(y)∫_{S.plane} f dH^n and θ(x)∫_{S.plane} f dH^n are equal, the left side converges to its prescribed limit iff the right side does; the condition finrank S.plane = n is common to both definitions. This proves the claim.

9. Representation identity. Let A ⊆ ℝ^N × G be Borel. By Measure.restrict_apply, Measure.smul_apply and Measure.map_apply (Φ is measurable, A ∩ (O × G) is Borel): W(A) = (rescaledMeasure V ξ t)(A ∩ (O × G)) = t^{-n} V(Φ^{-1}(A ∩ (O × G))). Φ^{-1}(A ∩ (O×G)) is Borel, so by IsVarifoldOf V M θ: V(Φ^{-1}(A ∩ (O × G))) = ∫⁻_{E_1} θ dH^n with E_1 := {x ∈ M : ∃ S, approx(M,θ,x,S) ∧ η(x) ∈ O ∧ (η(x), S) ∈ A}. Now E_1 = σ(E_2) with E_2 := {y ∈ O : σ(y) ∈ M ∧ ∃ S, approx(M, θ, σ(y), S) ∧ (y,S) ∈ A}, and by step 8, E_2 = {y ∈ M̂ : ∃ S, approx(M̂, θ̂, y, S) ∧ (y,S) ∈ A}. By step 1: W(A) = t^{-n}∫⁻_{σ(E_2)} ofReal θ dH^n = t^{-n} t^n ∫⁻_{E_2} ofReal(θ∘σ) dH^n = ∫⁻_{E_2} ofReal θ̂ dH^n. Together with steps 3–7 this proves IsVarifoldOf W M̂ θ̂.

10. Integer multiplicity. Y := {x ∈ M : θ(x) ∉ ℕ} is H^n-null (M is H^n-null-measurable and θ ∈ ℕ (H^n⌞M)-a.e., ae_restrict_iff'₀). {y ∈ M̂ : θ̂(y) ∉ ℕ} ⊆ η(Y), which is H^n-null by step 1. Since M̂ is H^n-null-measurable, ∃ k ∈ ℕ, θ̂(y) = k holds for (H^n⌞M̂)-a.e. y. With step 9, IsIntegral W holds with witnesses M̂, θ̂. ∎

## Key steps

1. The similarity σ(y) = ξ + ty scales H^n by t^n on all sets, so it preserves null sets, Borel and null-measurable sets, and ∫_{σ(A)} g dH^n = t^n ∫_A g∘σ dH^n.
2. Carrier M̂ := O ∩ σ^{-1}(M), multiplicity θ̂ := θ∘σ: null-measurable, countably n-rectifiable (η∘F_j Lipschitz), positive, locally integrable (σ(K) ⊆ U compact).
3. Weighted approximate tangent planes are local and homothety invariant: approx(M̂,θ̂,y,S) ⇔ approx(M,θ,σ(y),S) for y ∈ O.
4. Change of variables gives the IsVarifoldOf identity for W; θ̂ ∈ ℕ H^n-a.e. on M̂ since η maps null sets to null sets.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -l -i varifold mathlib/Mathlib (0 files)`
- `rg -n 'theorem exist_disjoint_covering_families|theorem hausdorffMeasure_image_le|theorem lintegral_iUnion₀|theorem lintegral_tsum|theorem _root_.Monotone.measure_iUnion|theorem lintegral_map_equiv|theorem restrict_restrict_of_subset|theorem measure_toMeasurable_inter_of_sFinite|theorem restrict_toMeasurable_of_sFinite|euclideanHausdorffMeasure_smul₀|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_zero_singleton|theorem lintegral_withDensity_eq_lintegral_mul₀|IsCompact.exists_cthickening_subset_open|Set.PairwiseDisjoint.countable_of_nonempty_interior|theorem eventually_lt_of_lt_liminf|theorem ae_restrict_iff'₀|theorem exists_measurable_subset_ae_eq|theorem AEMeasurable.indicator₀|theorem measure_inter_add_sdiff₀|theorem lintegral_eq_lintegral_meas_lt' mathlib/Mathlib`
- `grep -n 'structure Varifold|def weight|def firstVariationNormOn|def HasLocallyBoundedFirstVariation|def domainMeasure|def project|def projectionLinearMap' simongmt Chapter08/Varifold.lean; grep RadonConverges Chapter08/VarifoldConvergence.lean`
- `grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'theorem simon_theorem_3_3|theorem simon_theorem_3_6|theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|measurable_dimensional(Upper|Lower)Density|exists_besicovitchCovering_families' simongmt Chapter01/{DensityComparison,Densities}.lean`
- `grep -n 'hasDerivAt_normalized_weightedCutoffMass|weightedCutoffMass|weightedRadialVectorField|weightedRadialGradientTerm' simongmt Chapter08/WeightedRadialIdentity.lean; grep -n 'scaledRadialCutoff|squaredRadialVectorField' Chapter04/FirstVariation.lean`
- `grep -n 'isFirstVariationPolarRepresentation_riesz|firstVariationRieszMeasure_eq_norm|isFirstVariationMeasure_riesz' simongmt Chapter08/FirstVariationRiesz.lean`
- `python3 gmt-compare.py contract_scope(Contract.lean) -> replayed scope: open Set Filter MeasureTheory Metric; open scoped Topology ENNReal CompactlySupported Pointwise; namespace GMT.Ch08; open Poincare.SimonGMT; open Poincare.SimonGMT.Chapter08; section/end Definitions`
- `lake build GMT.Ch08.Submission && lake env lean Test/Assembly2.lean (scratch copy /tmp/ic-decomp-cAI8Ux: 8 child statements in comparator form + 6 sibling stubs + parent term Submission.integral_compactness_theorem : IntegralCompactnessTheorem; no sorry in the parent)`
- `lake env lean Test/Axioms.lean (#print axioms for 11 cited SimonGMT lemmas: propext, Classical.choice, Quot.sound only)`
- `python3 -c validate_lean_statement (verifier/lean_contract.py) on all 8 lean_statements; dag.json lean_name scan for collisions`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/AEMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/VarifoldConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/FirstVariationRiesz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/WeightedRadialIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root/decomposition-v2.json`
- `/tmp/ic-decomp-cAI8Ux/Test/Assembly2.lean`
- `/tmp/ic-decomp-cAI8Ux/Test/Axioms.lean`

Snapshot = project 63436ae6 + Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission. Mathlib has no varifold theory (0 files), so all Ch. 8 obligations are proved in the DAG. Every Mathlib lemma cited in the child proofs exists in the snapshot with suitable hypotheses: the Besicovitch covering families, the Lipschitz/Hölder image bounds for Hausdorff measure, Euclidean Hausdorff measure scaling, isometry invariance and agreement with volume, the s-finite measurable-hull identities, restrict_restrict_of_subset, Monotone.measure_iUnion, lintegral_iUnion₀/tsum/map_equiv/withDensity, cthickening, countability of disjoint families, and the liminf lemmas. The SimonGMT lemmas used — Theorems 3.3/3.6, Borel-measurable densities, the Besicovitch families 3.12, the weighted radial identity 3.5, the Riesz polar representation and 2.5 characterization, and simonHausdorffMeasureReal = μHE[n] — exist in the pinned package and use only propext, Classical.choice and Quot.sound. 3.5 lives in Chapter08.WeightedRadialIdentity, which Submission does not import. In a scratch copy with the comparator's replayed contract scope, all 8 child lean_statements elaborate in the exact comparator form and pass validate_lean_statement. With the 8 children and 6 frozen root-level sibling types as sorried stubs, the parent assembly `Submission.integral_compactness_theorem : IntegralCompactnessTheorem` type-checks with no sorry of its own. dag.json and the node files reserve no `intcpt_*` names, so all 8 lean_names are fresh.
