# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1`
- Child DAG node: `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.local_differentiation-a1.weighted_density_point-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 2, 3(b), 5(b), 6(i) and 6(iii) of the parent-supplied proof of fiw_tl_ald_local_differentiation. They are specialized to one weight (M, θ) (the parent's (M₂, θ₂)) and a subset E ⊆ M (the parent's A = M₁ ∩ M₂), with H replaced by an arbitrary measure μ; that proof uses no property of H.

Notation: K := B̄_r(y) = closedBall y r, S := M ∩ K, B_s := B̄_s(x) = closedBall x s, t⁺ := ENNReal.ofReal t, ν := (μ⌞S).withDensity (z ↦ θ(z)⁺) and λ := μ⌞(E ∩ B_r(y)).

1. Null-measurability. K is closed, hence measurable, so S is μ-null-measurable, and μ⌞S-a.e. z lies in S (ae_restrict_mem₀). E ∩ B_r(y) is μ-null-measurable, since open balls are measurable. E is null-measurable for μ⌞S (NullMeasurableSet.mono with Measure.restrict_le_self). Hence so is E ∩ B_s for every s, since closed balls are measurable.

2. Finiteness. ν(ℝ^P) = ∫⁻_S θ⁺ dμ ≤ ∫⁻_S ‖θ‖ₑ dμ < ∞, because θ is μ-integrable on S. Formally, isFiniteMeasure_withDensity_ofReal applied to the HasFiniteIntegral part of the hypothesis gives IsFiniteMeasure ν. So ν is locally finite.

3. Reverse absolute continuity. θ⁺ is AEMeasurable for μ⌞S: take the AEStronglyMeasurable part of the integrability of θ and apply AEMeasurable.ennreal_ofReal. For μ⌞S-a.e. z we have z ∈ M, so θ(z) > 0 and θ(z)⁺ ≠ 0 (ENNReal.ofReal_pos). By withDensity_absolutelyContinuous', μ⌞S ≪ ν.

4. Absolute continuity of λ with respect to ν⌞E.
(a) By step 1 and Measure.restrict_restrict₀, (μ⌞S)⌞E = μ⌞(E ∩ S).
(b) Since E ⊆ M and ball y r ⊆ closedBall y r, we have E ∩ B_r(y) ⊆ E ∩ S. So λ ≤ (μ⌞S)⌞E (Measure.restrict_mono).
(c) Restricting step 3 to E (AbsolutelyContinuous.restrict) gives (μ⌞S)⌞E ≪ ν⌞E.
(d) Hence λ ≪ ν⌞E (Measure.absolutelyContinuous_of_le and AbsolutelyContinuous.trans).

5. Besicovitch density theorem. ℝ^P is a second-countable metric space with its Borel σ-algebra and the Besicovitch covering property (instHasBesicovitchCovering for finite-dimensional normed spaces), and ν is locally finite by step 2. Besicovitch.ae_tendsto_measure_inter_div ν E holds for an arbitrary set E. It gives: for ν⌞E-a.e. x, Q(s) := ν(E ∩ B_s) / ν(B_s) → 1 as s → 0⁺. By step 4 and AbsolutelyContinuous.ae_le, this holds for λ-a.e. x. Also λ-a.e. x lies in E ∩ B_r(y) (ae_restrict_mem₀, step 1). Fix x with both properties (filter_upwards).

6. Identification on small balls. Since x ∈ B_r(y), ρ := r − dist(x, y) > 0, and (0, ρ) ∈ 𝓝[>] 0 (Ioo_mem_nhdsGT). For s ∈ (0, ρ) we have s + dist(x, y) ≤ r, so B_s ⊆ K (closedBall_subset_closedBall').
(i) E ∩ B_s is null-measurable for μ⌞S by step 1. So withDensity_apply₀ and Measure.restrict_restrict₀ give ν(E ∩ B_s) = ∫⁻_{E∩B_s} θ⁺ d(μ⌞S) = ∫⁻_{(E∩B_s)∩S} θ⁺ dμ. Moreover (E ∩ B_s) ∩ S = E ∩ B_s, because E ⊆ M and B_s ⊆ K. So ν(E ∩ B_s) = ∫⁻_{E∩B_s} θ⁺ dμ.
(ii) B_s is measurable, so withDensity_apply and Measure.restrict_restrict give ν(B_s) = ∫⁻_{B_s∩S} θ⁺ dμ. Moreover B_s ∩ S = M ∩ B_s, because B_s ⊆ K. So ν(B_s) = ∫⁻_{M∩B_s} θ⁺ dμ.
Thus Q(s) equals the quotient in the statement for every s ∈ (0, ρ). The two functions of s agree eventually along 𝓝[>] 0, and Tendsto.congr' transfers the limit 1 from step 5 to the stated quotient. This holds for λ-almost every x, which is the claim. ∎

## Key steps

1. ν := (μ⌞(M∩K)).withDensity θ⁺ with K = B̄_r(y) is finite, because θ ∈ L¹(μ⌞(M∩K)). Also μ⌞(M∩K) ≪ ν, because θ > 0 on M (withDensity_absolutelyContinuous').
2. λ = μ⌞(E ∩ B_r(y)) ≤ (μ⌞(M∩K))⌞E = μ⌞(E ∩ (M∩K)) ≪ ν⌞E, using E ⊆ M, Measure.restrict_restrict₀ and AbsolutelyContinuous.restrict.
3. Besicovitch.ae_tendsto_measure_inter_div ν E: ν(E ∩ B̄_s(x))/ν(B̄_s(x)) → 1 for ν⌞E-a.e. x, hence λ-a.e. Also x ∈ E ∩ B_r(y) λ-a.e.
4. For 0 < s < r − dist(x, y), B̄_s(x) ⊆ K, so ν(E ∩ B̄_s(x)) = ∫⁻_{E∩B̄_s(x)} θ⁺ dμ and ν(B̄_s(x)) = ∫⁻_{M∩B̄_s(x)} θ⁺ dμ (withDensity_apply₀ / withDensity_apply with restrict_restrict₀ / restrict_restrict). Conclude by Tendsto.congr'.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (identical); diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); grep -n 'namespace|^end|theorem main_theorem' GMT/Ch06/Submission.lean`
- `grep -rn 'indicator₀' mathlib/Mathlib/MeasureTheory --include=*.lean (Integral/IntegrableOn.lean:335-375: integrable_indicator_iff₀, Integrable.indicator₀, integrableOn_indicator_iff)`
- `grep -rn 'theorem integrable_withDensity_iff_integrable_smul' mathlib/Mathlib (Function/L1Space/Integrable.lean:790-844)`
- `grep -n 'theorem ae_tendsto_measure_inter_div|protected def vitaliFamily|theorem tendsto_filterAt' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean; grep -n instHasBesicovitchCovering mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `grep -n 'withDensity_apply |withDensity_apply₀|setLIntegral_withDensity_eq_lintegral_mul₀|withDensity_absolutelyContinuous'' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean; grep -n isFiniteMeasure_withDensity_ofReal mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `grep -n 'restrict_restrict₀|restrict_restrict |ae_restrict_mem₀|ae_restrict_of_ae_restrict_of_subset|restrict_mono ' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean; grep for NullMeasurableSet.mono (Measure/Filter.lean), absolutelyContinuous_of_le (Measure/AbsolutelyContinuous.lean), AEStronglyMeasurable mono_ac, AEMeasurable.real_toNNReal (Constructions/BorelSpace/Real.lean), closedBall_subset_closedBall' (Topology/MetricSpace/Pseudo/Defs.lean)`
- `lake env lean /tmp/ld_split_check/T0.lean (#check Besicovitch.ae_tendsto_measure_inter_div, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, withDensity_absolutelyContinuous', isFiniteMeasure_withDensity_ofReal, withDensity_apply₀, setLIntegral_withDensity_eq_lintegral_mul₀, lintegral_withDensity_eq_lintegral_mul₀)`
- `python3 -I /tmp/ld_scripts/gen.py: lean_contract.validate_lean_statement and gmt-compare.py child_modules(mode=contract) for the 2 child types and the frozen parent; lake env lean /tmp/ld_split_check/Cmp/*_Challenge.lean (3 files, only the expected sorry warning)`
- `lake env lean /tmp/ld_split_check/Audit/Combined.lean and /tmp/ld_split_check/Audit/RealLayout.lean (exit 0; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I scan of dag.json lean_name (458 nodes) for weighted|lebesgue_point|density_point|fiw_tl_ald; grep -rl fiw_tl_ald_ld_ over the run directory; git grep -l fiw_tl_ald_ld_ over 1614 refs; grep -rl fiw_tl_ald_ld_ over .lake/packages/simongmt and GMT (no match)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-local-diff-09eb4db1f4/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-closed-bal-73c57412a9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1/parent-supplied-natural-proof.md`
- `/tmp/ld_split_check/Cmp/fiw_tl_ald_ld_weighted_lebesgue_point_Challenge.lean`
- `/tmp/ld_split_check/Cmp/fiw_tl_ald_ld_weighted_density_point_Challenge.lean`
- `/tmp/ld_split_check/Cmp/fiw_tl_ald_local_differentiation_Challenge.lean`
- `/tmp/ld_split_check/Audit/Combined.lean`
- `/tmp/ld_split_check/Audit/RealLayout.lean`

Snapshot: project d8d46c9587747dee0751a1f780fcafdba16a3886 with Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot's Contract.lean is byte-identical to the workspace's, and Submission.lean equals Contract.lean at the frozen commit.

Mathlib supplies everything the children and the assembly need:
- Besicovitch: ae_tendsto_measure_inter_div (arbitrary set, IsLocallyFiniteMeasure; Besicovitch.lean:1105), vitaliFamily [SFinite] (:1021), tendsto_filterAt (:1060);
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div (LocallyIntegrable; Differentiation.lean:818) and instHasBesicovitchCovering (BesicovitchVectorSpace.lean:499);
- withDensity_apply (WithDensity.lean:44), withDensity_apply₀ (:152), setLIntegral_withDensity_eq_lintegral_mul₀ (:463), withDensity_absolutelyContinuous' (:576);
- isFiniteMeasure_withDensity_ofReal (HasFiniteIntegral.lean:310) and integrable_withDensity_iff_integrable_smul₀ (Integrable.lean:838);
- integrableOn_indicator_iff for null-measurable sets (IntegrableOn.lean:373);
- Measure.restrict_mono (Restrict.lean:89), Measure.restrict_restrict₀ (:198), Measure.restrict_restrict (:205), ae_restrict_mem₀ (:637), ae_restrict_of_ae_restrict_of_subset (:654);
- NullMeasurableSet.mono (Filter.lean:66), absolutelyContinuous_of_le (AbsolutelyContinuous.lean:56), AEStronglyMeasurable.mono_ac (AEStronglyMeasurable.lean:207), AEMeasurable.real_toNNReal (BorelSpace/Real.lean:152), closedBall_subset_closedBall' (Pseudo/Defs.lean:547).

No accepted project or SimonGMT declaration has these exact types. The similar ind_ab_weighted_lebesgue_point is vector-valued with an IsRectifiableTriple hypothesis, so it is a different type. The new names fiw_tl_ald_ld_weighted_lebesgue_point and fiw_tl_ald_ld_weighted_density_point appear nowhere in dag.json, the run directory, the 1614 git refs, simongmt or GMT.

In the frozen build, both child types and the frozen parent type elaborate in the comparator's exact challenge layout. Both children have complete sorry-free proofs, and the byte-exact frozen parent type is derived from them as Submission declarations, using only propext, Classical.choice and Quot.sound.
