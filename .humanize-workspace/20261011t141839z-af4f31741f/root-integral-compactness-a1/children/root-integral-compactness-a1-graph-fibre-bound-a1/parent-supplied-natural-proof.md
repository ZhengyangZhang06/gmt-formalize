# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1`
- Child DAG node: `root.integral_compactness-a1.graph_fibre_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step B6 (iii)–(iv) of the parent proof of Simon 8.5.9 (the graph inequality that replaces the area formula on rectifiable carriers). Notation: H^n := μHE[n]; p := Grassmannian.project P (orthogonal projection onto P.plane: linear, symmetric, idempotent, |p v| ≤ |v|), q := id − p, |v|² = |p v|² + |q v|²; for a ∈ ℝ^N the fibre sum is Σ_{y∈G, p(y)=a} u(y) := the [0,∞]-valued sum (tsum) of u over the subtype {y ∈ G : p(y) = a}.

1. Geometry of one graph. For y, z ∈ Γ_i: |p(y) − p(z)| ≤ |y − z| = (|p(y − z)|² + |q(y − z)|²)^{1/2} ≤ (1 + L²)^{1/2}|p(y) − p(z)|. Hence p is injective on Γ_i, its inverse h_i : p(Γ_i) → Γ_i is (1+L²)^{1/2}-Lipschitz, and p(Γ_i) is closed (if p(y_k) → a with y_k ∈ Γ_i, then (y_k) is Cauchy by the inequality, converges to some y ∈ Γ_i because Γ_i is closed, and p(y) = a). So p|_{Γ_i} : Γ_i → p(Γ_i) is a homeomorphism between closed sets, and p(Γ_i) ⊆ P.plane.

2. Transfer of measurability and of null sets. Let B ⊆ Γ_i. If B is Borel, then p(B) = {a ∈ p(Γ_i) : h_i(a) ∈ B} is Borel (h_i is continuous on the closed set p(Γ_i), so this is the preimage of a Borel set under a continuous map on a closed, hence Borel, domain). If H^n(B) = 0, then H^n(p(B)) = 0, since p is 1-Lipschitz (Mathlib LipschitzWith.hausdorffMeasure_image_le; μHE[n] is a positive constant multiple of μH[n]). Hence, if B is H^n-null-measurable, so is p(B): write B = B_1 ∪ Y with B_1 Borel, B_1 ⊆ Γ_i and H^n(Y) = 0 (intersect a Borel/null decomposition of B with the closed set Γ_i), so p(B) = p(B_1) ∪ p(Y).

3. Disjoint pieces and fibres. Let A_i := (G ∩ Γ_i) ∖ ⋃_{j<i} Γ_j (i ∈ ℕ). The A_i are pairwise disjoint, H^n-null-measurable (G is, the Γ_j are closed), A_i ⊆ Γ_i, and ⋃_i A_i = G because G ⊆ ⋃_i Γ_i. Fix a ∈ ℝ^N. Since p is injective on each Γ_i, sending y ∈ G with p(y) = a to the unique i with y ∈ A_i is a bijection from {y ∈ G : p(y) = a} onto {i : a ∈ p(A_i)}, with inverse i ↦ h_i(a). Hence, for every u : ℝ^N → [0,∞], Σ_{y∈G, p(y)=a} u(y) = Σ_i 1_{p(A_i)}(a)·u(h_i(a)) (sums of non-negative terms; both sides vanish for a ∉ P.plane).

4. Borel simple integrands. Let s = Σ_{j=1}^J c_j·1_{E_j} be a Borel simple function (c_j ∈ [0,∞], E_j Borel and pairwise disjoint). Fix i. Extend h_i to all of ℝ^N by h_i := Function.invFunOn p Γ_i (so h_i(p(y)) = y for y ∈ Γ_i) and let s_i := 1_{p(A_i)}·(s∘h_i). For each j, A_i ∩ E_j ⊆ Γ_i is H^n-null-measurable, so p(A_i ∩ E_j) is H^n-null-measurable by step 2 (NullMeasurableSet.exists_measurable_subset_ae_eq gives the Borel/null split), h_i(p(A_i ∩ E_j)) = A_i ∩ E_j, and by the Lipschitz image bound (Mathlib LipschitzOnWith.hausdorffMeasure_image_le for h_i on p(Γ_i), constant ((1+L²)^{1/2})^n; μHE[n] is a positive constant multiple of μH[n]) H^n(A_i ∩ E_j) ≤ (1+L²)^{n/2} H^n(p(A_i ∩ E_j)). Because p is injective on Γ_i ⊇ A_i, for a ∈ p(A_i) we have 1_{E_j}(h_i(a)) = 1_{p(A_i ∩ E_j)}(a), so s_i = Σ_j c_j·1_{p(A_i ∩ E_j)}; in particular s_i is H^n-a.e.-measurable (AEMeasurable.indicator₀ / lintegral_indicator_const₀) and vanishes off p(A_i) ⊆ P.plane. Hence ∫⁻_{A_i} s dH^n = Σ_j c_j H^n(A_i ∩ E_j) ≤ (1+L²)^{n/2} Σ_j c_j H^n(p(A_i ∩ E_j)) = (1+L²)^{n/2} ∫⁻ s_i dH^n = (1+L²)^{n/2} ∫⁻_{P.plane} s_i dH^n (no layer-cake formula is needed, and the values c_j = ∞ are allowed). Summing over i (lintegral_iUnion₀ for the pairwise disjoint null-measurable A_i, and lintegral_tsum for the a.e.-measurable s_i) and using step 3 with u := s: ∫⁻_G s dH^n = Σ_i ∫⁻_{A_i} s dH^n ≤ (1+L²)^{n/2} ∫⁻_{P.plane} Σ_i s_i dH^n = (1+L²)^{n/2} ∫⁻_{P.plane} (Σ_{y∈G, p(y)=a} s(y)) dH^n(a).

5. Arbitrary g. The lower Lebesgue integral ∫⁻_G g dH^n is the supremum of ∫⁻_G s dH^n over Borel simple functions s ≤ g (definition of MeasureTheory.lintegral and SimpleFunc.lintegral_eq_lintegral, for the measure H^n⌞G). For each such s, step 4 and the pointwise inequality Σ_{y∈G,p(y)=a} s(y) ≤ Σ_{y∈G,p(y)=a} g(y) (lintegral_mono needs no measurability) give ∫⁻_G s dH^n ≤ (1+L²)^{n/2} ∫⁻_{P.plane} Σ_{y∈G,p(y)=a} g(y) dH^n(a). Taking the supremum over s proves ∫⁻_G g dH^n ≤ ofReal((1 + L²)^{n/2}) · ∫⁻_{P.plane} Σ_{y∈G, p(y)=a} g(y) dH^n(a). ∎

## Key steps

1. On each L-graph p is bi-Lipschitz onto a closed set, with (1+L²)^{1/2}-Lipschitz inverse h_i.
2. p maps Borel, null and null-measurable subsets of Γ_i to sets of the same kind.
3. Disjointify G into A_i ⊆ Γ_i; fibre sums equal Σ_i 1_{p(A_i)} u∘h_i.
4. Borel simple integrands: the Lipschitz image bound H^n(A_i ∩ E_j) ≤ (1+L²)^{n/2}H^n(p(A_i ∩ E_j)), summed over the values and over i.
5. Arbitrary g: lower integral as a supremum over Borel simple functions and monotonicity of fibre sums.

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
