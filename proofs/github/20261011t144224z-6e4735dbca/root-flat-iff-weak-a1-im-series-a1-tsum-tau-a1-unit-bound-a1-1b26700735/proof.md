# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: s(τ) := simpleNVector τ. For an n-covector α (a continuous alternating map (ℝ^P)^n → ℝ), ‖α‖ is its operator norm.

1. (Unit vectors.) Since τ is orthonormal, ‖τ_i‖ = 1 for every i ∈ Fin n (first component of Orthonormal). Hence ∏_i ‖τ_i‖ = 1; for n = 0 the empty product is also 1.
2. (Evaluation.) By the definition of simpleNVector (simpleNVector_apply), s(τ)(α) = α(τ) = α(τ_1, …, τ_n).
3. (Operator-norm inequality.) For continuous alternating maps, ‖α(τ)‖ ≤ ‖α‖·∏_i ‖τ_i‖ (ContinuousAlternatingMap.le_opNorm). By step 1 the right side equals ‖α‖. The norm on ℝ is the absolute value (Real.norm_eq_abs), so steps 2–3 give |s(τ)(α)| ≤ ‖α‖.
4. (Case w = s(τ).) Then |w(α)| = |s(τ)(α)| ≤ ‖α‖ by step 3.
5. (Case w = −s(τ).) Evaluating a negated continuous linear map negates the value, so w(α) = −(s(τ)(α)). Hence |w(α)| = |s(τ)(α)| (abs_neg) ≤ ‖α‖ by step 3.
6. The hypothesis gives one of the cases 4 or 5, so |w(α)| ≤ ‖α‖. ∎

Lean note (checked at this pin):
- `have h1 : |simpleNVector τ α| ≤ ‖α‖ := by rw [simpleNVector_apply, ← Real.norm_eq_abs]; calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ; _ = ‖α‖ := by simp [hτ.1]`
- then `rcases hw with rfl | rfl`, with `exact h1` and `simpa [abs_neg] using h1`.
- Axioms: propext, Classical.choice, Quot.sound.

## Key steps

1. Orthonormal τ gives ‖τ_i‖ = 1, so ∏_i ‖τ_i‖ = 1
2. simpleNVector τ α = α(τ) and ‖α(τ)‖ ≤ ‖α‖·∏_i ‖τ_i‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm)
3. the case w = −simpleNVector τ reduces to the same bound by |−a| = |a|

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read project GMT/Ch06/Submission.lean (= Contract.lean): IsRectifiableTriple fields subset/nullMeasurableSet/pos/integrableOn/aestronglyMeasurable/orients, tauAction, CompactlyContainedOpen`
- `read SimonGMT Chapter06/Forms.lean (Covector, DifferentialForm, IsTestForm), FormsDuality.lean (NVector, simpleNVector via mkContinuous, simpleNVector_apply), Currents.lean (testFormOnSubmodule, TestFormOn)`
- `rg -n simpleNVector project (only Contract.lean, Submission.lean, README.md); rg -n tauAction project (only Contract.lean, Submission.lean, README.md); rg -n simpleNVector SimonGMT (only Chapter06/FormsDuality.lean); rg 'norm_simpleNVector|simpleNVector_norm|abs_simpleNVector' project+SimonGMT (no match)`
- `rg Mathlib snapshot: exists_open_between_and_isCompact_closure, Continuous.bounded_above_of_compact_support, ContinuousAlternatingMap.le_opNorm, isBoundedBilinearMap_apply, Continuous.comp_aestronglyMeasurable, AEStronglyMeasurable.prodMk, aestronglyMeasurable_indicator_iff₀, ae_restrict_iff'₀, lintegral_mono_ae, lintegral_indicator₀, lintegral_const_mul', Real.enorm_eq_ofReal_abs, integral_tsum, hasSum_integral_of_summable_integral_norm, integral_norm_eq_lintegral_enorm, ENNReal.summable_toReal, ENNReal.tsum_mul_left, integral_indicator₀, integral_const_mul, Set.indicator_mul_right, image_eq_one_of_notMem_mulTSupport, HasFiniteIntegral`
- `python3 -I: all lean_names in dag.json and nodes/*/decomposition-v*.json (282 names; fiw_ims_tt_unit_bound / fiw_ims_tt_term_bound absent); statements of related nodes fiw_imf_simple_dual, fiw_imf_massOn_le, ltg_tau_integrable, iwlp_tau_integrable, polyhedral_approx_ot_tau_mass_le, lpf_simple_nvector_algebra, isoperimetric_abs_covector_apply_le (no identical type)`
- `git archive d8d46c9 into /tmp/tsumtau_decomp.RSBst6 with .lake/packages -> lake-packages-25730c7c; lake build GMT.Ch06.Submission (success)`
- `gmt-compare.py child_modules (mode contract, root GMT.Ch06.main_theorem) + lean_contract.validate_lean_statement on both child types; lake env lean Scratch/Child_fiw_ims_tt_unit_bound.lean, Scratch/Child_fiw_ims_tt_term_bound.lean (only the challenge sorry warning)`
- `lake env lean Scratch/Assembly.lean: #print axioms Submission.fiw_ims_tsum_tau = [propext, sorryAx, Classical.choice, Quot.sound] (sorryAx only from the two child stubs)`
- `lake env lean Scratch/ChildProofs.lean and Scratch/Full.lean: both children proved; parent assembled from them with no sorry; #print axioms = [propext, Classical.choice, Quot.sound]`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/GroupWithZero/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Child_fiw_ims_tt_unit_bound.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Child_fiw_ims_tt_term_bound.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Assembly.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/ChildProofs.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Full.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract.

No project or pinned SimonGMT lemma bounds simpleNVector or the τ-integrand:
- simpleNVector occurs only in FormsDuality.lean (definition, simpleNVector_apply, pushforward) and in the contract's orients field;
- tauAction occurs only in the contract and README;
- searches for norm_simpleNVector, simpleNVector_norm and abs_simpleNVector find nothing.
So the operator-norm unit bound and the single-triple integrand estimate become the two children.

No DAG declaration has an identical type, so fresh names fiw_ims_tt_* are used:
- fiw_imf_simple_dual and polyhedral_approx_ot_tau_mass_le use covectorEuclideanNorm;
- ltg/iwlp_tau_integrable give integrability without the explicit bound;
- lpf_simple_nvector_algebra is a Gram-determinant identity.

Mathlib at this pin supplies every tool cited in the child proofs and the assembly, at the files listed: ContinuousAlternatingMap.le_opNorm (Alternating/Basic.lean:212), isBoundedBilinearMap_apply (BoundedLinearMaps.lean:391), Continuous.comp_aestronglyMeasurable and AEStronglyMeasurable.prodMk (AEStronglyMeasurable.lean:233,256), aestronglyMeasurable_indicator_iff₀ (:558), ae_restrict_iff'₀ (Restrict.lean:624), lintegral_indicator₀ (Lebesgue/Basic.lean:518), lintegral_const_mul' (Lebesgue/Add.lean:420), exists_open_between_and_isCompact_closure (Regular.lean:364), Continuous.bounded_above_of_compact_support (Bounded.lean:153), hasSum_integral_of_summable_integral_norm (DominatedConvergence.lean:96), integral_norm_eq_lintegral_enorm (Bochner/Basic.lean:537), integral_indicator₀ (Bochner/Set.lean:170), ENNReal.summable_toReal (InfiniteSum/ENNReal.lean:350).

Scratch kernel checks:
- both child types elaborate in the comparator's exact child scope;
- the frozen parent type follows from the two child stubs (sorryAx only from the stubs);
- both children are fully proved, and the end-to-end file gives Submission.fiw_ims_tsum_tau with axioms [propext, Classical.choice, Quot.sound] only.
