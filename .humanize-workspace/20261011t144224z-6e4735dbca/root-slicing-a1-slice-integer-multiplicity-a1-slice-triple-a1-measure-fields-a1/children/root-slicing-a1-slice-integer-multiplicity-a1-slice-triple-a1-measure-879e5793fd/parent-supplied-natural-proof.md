# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.measure_fields-a1.slice_null_measurable-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k), with inner product ⟨·,·⟩ and norm |·|; ‖·‖ₑ is the extended norm (‖r‖ₑ = |r| ∈ [0, ∞) for r ∈ ℝ). Hᵏ := μHE[k] (Mathlib's Euclidean Hausdorff measure on ℝ^P). L¹ := volume on ℝ. n := m + 1. For a measure μ and an arbitrary set S, μ⌞S := μ.restrict S; it is a measure for every S, (μ⌞S)(A) = μ(A ∩ S) for Borel A (Measure.restrict_apply), and μ(A ∩ S) ≤ (μ⌞S)(A) for every A (Measure.le_restrict_apply). 'p holds μ-a.e. on S' means ∀ᵐ x ∂(μ⌞S), p x. (NT) is the null-transfer hypothesis for (M, f): for every predicate p on ℝ^P with p(x) for Hⁿ⌞M-a.e. x, for L¹-a.e. t ∈ ℝ, p(x) holds for H^m⌞(M ∩ f⁻¹{t})-a.e. x. In the parent node it is the conclusion of the sibling slicing_im_st_ae_transfer applied to the co-area identity, and enters here as a hypothesis because children may depend only on their own siblings. This is Steps 2 (the Borel kernel B), 3 and 5(a) of the parent proof (slicing_im_st_measure_fields), stated for the whole slice M ∩ f⁻¹{t}.
1. (Borel kernel.) M is Hⁿ-null-measurable, so there is a Borel set B ⊆ M with B = M Hⁿ-a.e. (NullMeasurableSet.exists_measurable_subset_ae_eq).
2. (x ∈ B holds Hⁿ⌞M-a.e.) Since B = M Hⁿ-a.e., Hⁿ⌞B = Hⁿ⌞M (Measure.restrict_congr_set). As B is Borel, x ∈ B for Hⁿ⌞B-a.e. x (ae_restrict_mem). Hence the predicate p(x) :⟺ x ∈ B holds for Hⁿ⌞M-a.e. x.
3. (Transfer.) By (NT) applied to p there is a set of full L¹-measure of t such that x ∈ B for H^m⌞(M ∩ f⁻¹{t})-a.e. x, i.e. (H^m⌞(M ∩ f⁻¹{t}))({x : x ∉ B}) = 0 (ae_iff). Fix such a t.
4. (The part outside B is null.) Put Y := {x : x ∉ B} ∩ (M ∩ f⁻¹{t}). By Measure.le_restrict_apply, H^m(Y) ≤ (H^m⌞(M ∩ f⁻¹{t}))({x : x ∉ B}) = 0, so H^m(Y) = 0 (nonpos_iff_eq_zero).
5. (Decomposition.) M ∩ f⁻¹{t} = (B ∩ f⁻¹{t}) ∪ Y. Indeed, if x ∈ M ∩ f⁻¹{t} then either x ∈ B, so x ∈ B ∩ f⁻¹{t}, or x ∉ B, so x ∈ Y; conversely B ∩ f⁻¹{t} ⊆ M ∩ f⁻¹{t} because B ⊆ M, and Y ⊆ M ∩ f⁻¹{t} by definition.
6. (Conclusion.) B ∩ f⁻¹{t} is Borel because B is Borel and f is measurable (f⁻¹{t} is Borel: hf (measurableSet_singleton t)), hence H^m-null-measurable (MeasurableSet.nullMeasurableSet). Y is H^m-null, hence H^m-null-measurable (NullMeasurableSet.of_null). A union of two null-measurable sets is null-measurable (NullMeasurableSet.union). So M ∩ f⁻¹{t} is H^m-null-measurable for every t in the full-measure set of Step 3, which proves the claim. No measurability of M ∩ f⁻¹{t} is used anywhere: restriction to an arbitrary set is a measure. ∎

## Key steps

1. Borel B ⊆ M with B = M Hⁿ-a.e.; then x ∈ B holds Hⁿ⌞M-a.e. (restrict_congr_set, ae_restrict_mem)
2. null transfer: for a.e. t, (H^m⌞(M ∩ f⁻¹{t}))({x ∉ B}) = 0, hence H^m({x ∉ B} ∩ M ∩ f⁻¹{t}) = 0 (le_restrict_apply)
3. M ∩ f⁻¹{t} = (B ∩ f⁻¹{t}) ∪ ({x ∉ B} ∩ M ∩ f⁻¹{t}) = Borel ∪ H^m-null, hence H^m-null-measurable

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
