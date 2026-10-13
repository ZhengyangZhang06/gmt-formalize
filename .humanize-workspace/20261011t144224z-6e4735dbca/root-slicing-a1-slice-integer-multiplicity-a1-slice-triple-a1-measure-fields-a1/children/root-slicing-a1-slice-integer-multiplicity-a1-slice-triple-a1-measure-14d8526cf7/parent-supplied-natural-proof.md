# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_integrable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k), with inner product ⟨·,·⟩ and norm |·|; ‖·‖ₑ is the extended norm (‖r‖ₑ = |r| ∈ [0, ∞) for r ∈ ℝ). Hᵏ := μHE[k] (Mathlib's Euclidean Hausdorff measure on ℝ^P). L¹ := volume on ℝ. n := m + 1. For a measure μ and an arbitrary set S, μ⌞S := μ.restrict S; it is a measure for every S, (μ⌞S)(A) = μ(A ∩ S) for Borel A (Measure.restrict_apply), and μ(A ∩ S) ≤ (μ⌞S)(A) for every A (Measure.le_restrict_apply). 'p holds μ-a.e. on S' means ∀ᵐ x ∂(μ⌞S), p x. (CA) is the co-area hypothesis for (M, f, G): for every Borel g : ℝ^P → [0, ∞], t ↦ ∫_{M∩f⁻¹{t}} g dH^m is L¹-a.e.-measurable and ∫_ℝ ∫_{M∩f⁻¹{t}} g dH^m dt = ∫_M ‖G‖ₑ g dHⁿ. (NT) is the null-transfer hypothesis for (M, f): for every predicate p on ℝ^P with p(x) for Hⁿ⌞M-a.e. x, for L¹-a.e. t ∈ ℝ, p(x) holds for H^m⌞(M ∩ f⁻¹{t})-a.e. x. In the parent node it is the conclusion of the sibling slicing_im_st_ae_transfer applied to the co-area identity, and enters here as a hypothesis because children may depend only on their own siblings. This is Steps 1–4 and 5(b) of the parent proof (slicing_im_st_measure_fields), stated for the whole slice M ∩ f⁻¹{t}, with two simplifications: the compact exhaustion is the sibling exhaustion (the comparator-accepted cmb_exists_compactly_contained_exhaustion) instead of the rational-ball construction, and the nonnegative Borel modification of θ is |θ₀| (used through ‖θ₀‖ₑ) instead of max(θ₀, 0), so neither θ > 0 nor null-measurability of M is needed.
1. (Exhaustion.) By the sibling exhaustion (cmb_exists_compactly_contained_exhaustion) applied to the open set U there are W_i ⊆ ℝ^P (i ∈ ℕ) with CompactlyContainedOpen W_i U for every i and such that every compact C ⊆ U satisfies C ⊆ W_i for some i. Put K_i := closure(W_i). By CompactlyContainedOpen, K_i is compact and K_i ⊆ U; K_i is closed, hence Borel (isClosed_closure.measurableSet). Every compact C ⊆ U lies in some W_i ⊆ K_i (subset_closure). For x ∈ M we have x ∈ U (M ⊆ U), {x} is compact and {x} ⊆ U, so x ∈ K_i for some i; hence M = ⋃_i (M ∩ K_i).
2. (Borel version of θ on M.) For each i, θ is Hⁿ-integrable on M ∩ K_i (hypothesis with K := K_i), in particular Hⁿ⌞(M ∩ K_i)-a.e. strongly measurable (Integrable.aestronglyMeasurable; IntegrableOn θ S μ is Integrable θ (μ⌞S)). Since ℕ is countable and M = ⋃_i (M ∩ K_i), θ is Hⁿ⌞M-a.e. strongly measurable (aestronglyMeasurable_iUnion_iff). Let θ₀ := AEStronglyMeasurable.mk θ: θ₀ : ℝ^P → ℝ is strongly measurable (hence Borel) and θ = θ₀ Hⁿ⌞M-a.e. (AEStronglyMeasurable.ae_eq_mk).
3. (Transfer.) By (NT) applied to p(x) :⟺ θ(x) = θ₀(x), there is a set T₁ ⊆ ℝ of full L¹-measure such that for t ∈ T₁: θ = θ₀ H^m⌞(M ∩ f⁻¹{t})-a.e.
4. (Finite slice integrals.) Fix i ∈ ℕ. The function g_i := 1_{K_i}·‖θ₀‖ₑ : ℝ^P → [0, ∞] (Set.indicator (K_i) (fun y => ‖θ₀ y‖ₑ)) is Borel (Measurable.enorm, Measurable.indicator). Let J_i(t) := ∫_{M∩f⁻¹{t}} g_i dH^m. By (CA) with g := g_i, J_i is L¹-a.e.-measurable and ∫_ℝ J_i dt = ∫_M ‖G‖ₑ g_i dHⁿ. Now:
   (i) ‖G(x)‖ₑ ≤ L for every x, because |G(x)| ≤ L (enorm_le_coe, NNReal.coe_le_coe, coe_nnnorm). Hence ∫_M ‖G‖ₑ g_i dHⁿ ≤ ∫_M L·g_i dHⁿ = L·∫_M g_i dHⁿ (lintegral_mono; lintegral_const_mul' since L ≠ ∞).
   (ii) As K_i is Borel, ∫_M g_i dHⁿ = ∫_{K_i ∩ M} ‖θ₀‖ₑ dHⁿ (lintegral_indicator, then Measure.restrict_restrict) = ∫_{M ∩ K_i} ‖θ‖ₑ dHⁿ: indeed θ = θ₀ Hⁿ⌞M-a.e. implies θ = θ₀ Hⁿ⌞(M ∩ K_i)-a.e. (ae_restrict_of_ae_restrict_of_subset, M ∩ K_i ⊆ M), and the integrals of a.e.-equal functions agree (lintegral_congr_ae).
   (iii) ∫_{M∩K_i} ‖θ‖ₑ dHⁿ < ∞, because θ is Hⁿ-integrable on M ∩ K_i (its HasFiniteIntegral component).
   Hence ∫_ℝ J_i dt ≤ L·∫_{M∩K_i} ‖θ‖ₑ dHⁿ < ∞ (ENNReal.mul_lt_top), and therefore J_i(t) < ∞ for L¹-a.e. t (ae_lt_top', using the a.e.-measurability of J_i).
5. (All i at once.) By ae_all_iff (ℕ countable), there is a set T₂ of full L¹-measure such that J_i(t) < ∞ for all i ∈ ℕ and all t ∈ T₂. Fix t ∈ T₁ ∩ T₂ (a set of full L¹-measure).
6. (Integrability on M ∩ f⁻¹{t} ∩ K_i.) Fix i and put S := M ∩ f⁻¹{t} ∩ K_i. Since S ⊆ M ∩ f⁻¹{t}, Step 3 gives θ = θ₀ H^m⌞S-a.e. (ae_restrict_of_ae_restrict_of_subset).
   (i) θ₀ is strongly measurable, so θ is H^m⌞S-a.e. strongly measurable (AEStronglyMeasurable.congr).
   (ii) As K_i is Borel, J_i(t) = ∫_{K_i ∩ (M ∩ f⁻¹{t})} ‖θ₀‖ₑ dH^m (lintegral_indicator, Measure.restrict_restrict) = ∫_S ‖θ₀‖ₑ dH^m (K_i ∩ (M ∩ f⁻¹{t}) = S, Set.inter_comm) = ∫_S ‖θ‖ₑ dH^m (lintegral_congr_ae with θ = θ₀ H^m⌞S-a.e.). Hence ∫_S ‖θ‖ₑ dH^m = J_i(t) < ∞, i.e. θ has finite integral for H^m⌞S.
   By (i) and (ii), θ is H^m-integrable on S. No measurability of M ∩ f⁻¹{t} is used: only the Borel set K_i is ever measured or restricted to first.
7. (Arbitrary compact K.) Let K ⊆ U be compact. By Step 1, K ⊆ W_i ⊆ K_i for some i, so M ∩ f⁻¹{t} ∩ K ⊆ M ∩ f⁻¹{t} ∩ K_i, and θ is H^m-integrable on M ∩ f⁻¹{t} ∩ K (IntegrableOn.mono_set). This holds for every compact K ⊆ U and every t in the full-measure set T₁ ∩ T₂, which proves the claim. ∎

## Key steps

1. exhaustion sibling: compact K_i := closure W_i ⊆ U, every compact C ⊆ U lies in some K_i, M = ⋃_i (M ∩ K_i)
2. θ is Hⁿ⌞M-a.e. strongly measurable (aestronglyMeasurable_iUnion_iff); θ₀ := its strongly measurable version
3. null transfer: for a.e. t, θ = θ₀ H^m⌞(M ∩ f⁻¹{t})-a.e.
4. co-area with g_i = 1_{K_i}‖θ₀‖ₑ and ‖G‖ₑ ≤ L: ∫ J_i dt ≤ L ∫_{M∩K_i} |θ| dHⁿ < ∞, so J_i(t) < ∞ for a.e. t and all i
5. J_i(t) = ∫_{M∩f⁻¹{t}∩K_i} |θ| dH^m < ∞ gives integrability on M ∩ f⁻¹{t} ∩ K_i, then on M ∩ f⁻¹{t} ∩ K by mono_set

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); sed -n 1,80p GMT/Ch06/Contract.lean (IsRectifiableTriple fields subset/nullMeasurableSet/integrableOn/aestronglyMeasurable)`
- `python3 -I over dag.json: status/depends_on/children of the slice_triple subtree; frozen lean_statement of slicing_im_st_ae_transfer and slicing_im_st_measure_fields; accepted nodes matching exhaust/measurab/contraction (cmb_exists_compactly_contained_exhaustion, lpf_pi_measurability, polyhedral_approx_exhaustion_function, lpf_lli_inner_compact_approx)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json and its decomposition-scope/review-receipt/audit (fiw_ims_frame_sign reuse precedent; reuse resolved to the existing accepted node in dag.json)`
- `read nodes/root-compactness-mass-bounds-a1-exhaustion-a1/{parent-supplied-natural-proof.md,parent-supplied-natural-proof.json,accepted-candidate.json} and nodes/root-compactness-mass-bounds-a1/decomposition-v1.json (accepted proof text, key steps, candidate cb89cc7f, comparator_passed)`
- `grep -c slicing_im_st_mf dag.json DAG.md issue-workers.json; grep -rl for the 4 new lean names in nodes/, local-references/197bdd4b88278494/project and lake-packages-25730c7c/simongmt (no match)`
- `rg in mathlib snapshot: norm_alternatizeUncurryFin_le / alternatizeUncurryFinCLM / alternatizeUncurryFin_apply; le_restrict_apply, restrict_congr_set, ae_restrict_of_ae_restrict_of_subset; exists_measurable_subset_ae_eq; aestronglyMeasurable_iUnion_iff; ae_lt_top'; lintegral_indicator; Continuous.clm_comp; norm_smulRight_apply; LipschitzWith.of_dist_le_mul`
- `lake env lean /tmp/mf-split-a1/Scope.lean and Names.lean (#check of about 50 cited lemma names and signatures)`
- `python3 -I verifier/gmt-compare.py contract_scope/child_modules and verifier/lean_contract.py validate_lean_statement on all 5 child types`
- `lake env lean /tmp/mf-split-a1/Challenge_<lean_name>.lean for the 5 children (only sorry warnings)`
- `lake env lean /tmp/mf-split-a1/Iota.lean (CLM-composition route fails: TopologicalSpace (Covector (Eucl P) m →L[ℝ] Eucl P →L[ℝ] Covector (Eucl P) m) not synthesized; Lipschitz route compiles)`
- `lake env lean /tmp/mf-split-a1/Null.lean, Orient.lean, Integ.lean, Stmts.lean, Final.lean (complete proofs of the 4 new children; selected frozen type from ae_transfer + exhaustion types + children; #print axioms: propext, Classical.choice, Quot.sound)`
- `independent adversarial reviewer subagent (/tmp/mf-review): regenerated challenge modules, independent assembly and non-vacuity checks, lemma-name checks; verdict ACCEPT-WITH-FIXES, fixes applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-measure-fields-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-exhaustion-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-exhaustion-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/mf-split-a1/Challenge_slicing_im_st_mf_slice_null_measurable.lean`
- `/tmp/mf-split-a1/Challenge_cmb_exists_compactly_contained_exhaustion.lean`
- `/tmp/mf-split-a1/Challenge_slicing_im_st_mf_slice_integrable.lean`
- `/tmp/mf-split-a1/Challenge_slicing_im_st_mf_contraction_lipschitz.lean`
- `/tmp/mf-split-a1/Challenge_slicing_im_st_mf_slice_orientation_aesm.lean`
- `/tmp/mf-split-a1/Iota.lean`
- `/tmp/mf-split-a1/Final.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract, and Submission is byte-identical to it. IsRectifiableTriple supplies exactly the fields the three conclusions need, separately: nullMeasurableSet for (a); subset and integrableOn for (b); aestronglyMeasurable for (c). Mathlib at this pin has every measure-theoretic lemma cited by the children, plus alternatizeUncurryFin_apply and norm_alternatizeUncurryFin_le for ι. The CLM-composition route to continuity of ι fails on a missing TopologicalSpace instance, so the Lipschitz route is used. Neither Mathlib nor SimonGMT has slice null-measurability, slice integrability or interior-product continuity lemmas. The DAG has an accepted, comparator-checked compact exhaustion (cmb_exists_compactly_contained_exhaustion, candidate cb89cc7f), reused with an identical type per the fiw_ims_frame_sign precedent. All 5 child types elaborate in the exact comparator scope. Complete scratch proofs of the 4 new children compile, as does the selected frozen type from ae_transfer plus the children, using only standard axioms. The new names (prefix slicing_im_st_mf_) occur nowhere in the DAG, nodes, snapshot or simongmt.
