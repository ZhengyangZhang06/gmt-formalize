# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.orientation_sign-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Let μ := H.restrict(M₁ ∩ M₂) and s(τ) := simpleNVector τ.

1. (Points of the overlap.) M₁ ∩ M₂ is H-null-measurable (field nullMeasurableSet of both triples, NullMeasurableSet.inter). So μ-a.e. x lies in M₁ ∩ M₂ (ae_restrict_mem₀). For such x, x ∈ M₂, so θ₂(x) > 0 (field pos of the second triple); in particular θ₂(x) ≠ 0.

2. (Frames from both orientation conditions.)
   - The field orients of the first triple holds H.restrict M₁-a.e., hence μ-a.e. because M₁ ∩ M₂ ⊆ M₁ (ae_restrict_of_ae_restrict_of_subset). It gives an orthonormal τ¹ : Fin n → ℝ^P with HasWeightedApproximateTangentSpaceAt n M₁ θ₁ x (span(range τ¹)) and ξ₁(x) = s(τ¹) or ξ₁(x) = −s(τ¹).
   - Likewise, using M₁ ∩ M₂ ⊆ M₂, μ-a.e. there is an orthonormal τ² with HasWeightedApproximateTangentSpaceAt n M₂ θ₂ x (span(range τ²)) and ξ₂(x) = ±s(τ²).

3. (Equal spans.)
   - Intersect the μ-a.e. statements of steps 1–2 with the hypothesis (filter_upwards), and fix such an x.
   - The hypothesis with Q := span(range τ¹) shows that span(range τ¹) is also a weighted approximate tangent space of (M₂, θ₂) at x.
   - Since θ₂(x) ≠ 0, HasWeightedApproximateTangentSpaceAt.unique gives span(range τ¹) = span(range τ²).

4. (Combine the signs.)
   - The sibling frame_sign with τ := τ¹, τ' := τ² gives s(τ²) = ε·s(τ¹) with ε ∈ {1, −1}.
   - Write ξ₁(x) = ε₁·s(τ¹) and ξ₂(x) = ε₂·s(τ²) with ε₁, ε₂ ∈ {1, −1}.
   - Then ξ₂(x) = ε₂ε·s(τ¹), so s(τ¹) = ε₂ε·ξ₂(x) because (ε₂ε)² = 1.
   - Hence ξ₁(x) = ε₁ε₂ε·ξ₂(x) with ε₁ε₂ε ∈ {1, −1}, i.e. ξ₁(x) = ξ₂(x) or ξ₁(x) = −ξ₂(x). This is an eight-case check using neg_neg. ∎

## Key steps

1. μ-a.e. x ∈ M₁ ∩ M₂ has θ₂(x) > 0 and orthonormal frames τ¹, τ² from the two orientation conditions
2. the hypothesis makes span τ¹ a weighted tangent space of (M₂, θ₂); uniqueness gives span τ¹ = span τ²
3. frame_sign gives s(τ²) = ±s(τ¹); combining the signs gives ξ₁ = ±ξ₂

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (identical); read IsRectifiableTriple, tauAction, IsIntegerMultiplicity, CompactlyContainedOpen; sed GMT/Ch06/README.md (reused SimonGMT definitions, NVector ContinuousENorm remark)`
- `grep '^theorem|^def|^structure|^abbrev' SimonGMT Chapter06/{Currents,Mass,Forms,FormsDuality}.lean and Chapter03/Rectifiable.lean (massAdmissibleOn, massOn, le_massOn, covectorEuclideanNorm, TestFormOnConverges, simpleNVector via mkContinuous, wedgeCovectors_apply_det, CountablyRectifiable.mono, countablyRectifiable_iUnion, countablyRectifiable_of_measure_zero, HasWeightedApproximateTangentSpaceAt.unique)`
- `grep -rn 'simpleNVector' SimonGMT (only FormsDuality.lean); grep -rn 'tauAction|IsIntegerMultiplicity|natAbs' SimonGMT (no match); grep 'fiw_ims|simpleNVector|Orthonormal' project/GMT outside the Ch06 contract (no related lemma)`
- `rg Mathlib snapshot: exists_open_between_and_isCompact_closure, measure_null_of_locally_null, integral_tsum, hasSum_integral_of_summable_integral_norm, lintegral_tsum, integral_indicator₀, lintegral_indicator₀, ae_restrict_iff'₀, ae_restrict_mem₀, ae_lt_top', AEMeasurable.ennreal_tsum, aestronglyMeasurable_iUnion_iff, aestronglyMeasurable_indicator_iff₀, aestronglyMeasurable_of_tendsto_ae, StronglyMeasurable.measurableSet_eq_fun, ContinuousLinearMap.aestronglyMeasurable_comp₂, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, LinearMap.mkContinuous_norm_le, ContinuousAlternatingMap.le_opNorm, norm_iteratedFDeriv_zero, ENNReal.ofReal_tsum_of_nonneg, norm_tsum_le_tsum_norm, IsSigmaCompact API, PseudoMetrizableSpace definition`
- `python3 listing of dag.json lean_names and of all nodes/*/decomposition-v*.json subproblem lean_names (no fiw_ims_* reserved)`
- `git archive d8d46c9 into /tmp/ims_check.FWdVje with .lake/packages -> shared lake-packages-25730c7c; lake build GMT.Ch06.Submission (success)`
- `gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on the 7 child statements; lake env lean Scratch/AllChildren.lean (0 errors)`
- `lake env lean Scratch/Assembly.lean: #print axioms Submission.fiw_im_series = [propext, sorryAx, Classical.choice, Quot.sound] (sorryAx only from stubbed children/prerequisites)`
- `lake env lean Scratch/Plumbing.lean (im_combine hypotheses feed overlap_finite, tsum_tau, orientation_sign; 0 errors)`
- `lake env lean Scratch/Inst{2,3,6,8,9}.lean: #synth on NVector (Eucl P) n; local PseudoMetrizableSpace via UniformSpace.pseudoMetrizableSpace + EMetric.instIsCountablyGeneratedUniformity; isBoundedBilinearMap_apply.continuous measurability route; |simpleNVector τ α| ≤ ‖α‖ for orthonormal τ`
- `book/chapter-06.txt: 3.2 Remarks (1),(3), 3.13 Lemma and proof, use of 3.13 for R^(ℓ), S^(ℓ) in the proof of 7.2`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Metrizable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Metrizable/Uniformity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/ims_check.FWdVje/Scratch/AllChildren.lean`
- `/tmp/ims_check.FWdVje/Scratch/Assembly.lean`
- `/tmp/ims_check.FWdVje/Scratch/Plumbing.lean`
- `/tmp/ims_check.FWdVje/Scratch/Inst6.lean`
- `/tmp/ims_check.FWdVje/Scratch/Inst8.lean`
- `/tmp/ims_check.FWdVje/Scratch/Inst9.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract (Contract.lean = Submission.lean). The pinned SimonGMT has the needed library pieces:
- massAdmissibleOn, massOn, le_massOn and covectorEuclideanNorm;
- TestFormOnConverges;
- simpleNVector, defined by mkContinuous with bound ∏‖v_i‖;
- CountablyRectifiable.mono, countablyRectifiable_iUnion and HasWeightedApproximateTangentSpaceAt.unique.
It has no integer-multiplicity calculus, mass bound, frame-sign or termwise-integration lemma (simpleNVector is used nowhere else; tauAction and IsIntegerMultiplicity appear only in the contract), so these become the children.

Mathlib supplies every tool cited in the child proofs: exists_open_between_and_isCompact_closure, measure_null_of_locally_null, lintegral_tsum, integral_tsum and hasSum_integral_of_summable_integral_norm, the indicator₀ and ae_restrict₀ lemmas, aestronglyMeasurable_iUnion_iff and aestronglyMeasurable_of_tendsto_ae, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, and ContinuousAlternatingMap.le_opNorm.

At this pin, NVector (Eucl P) n lacks PseudoMetrizableSpace, MetrizableSpace, ContinuousAdd and SecondCountableTopology instances via search. A local PseudoMetrizableSpace instance and the isBoundedBilinearMap_apply.continuous route compile, and are recorded in the proofs.

Scratch build of the frozen commit:
- all 7 child types elaborate in the comparator's exact child scope;
- fiw_im_series is derived from fiw_ims_series_current, fiw_ims_combine and the two prerequisite stubs (axioms propext, Classical.choice, Quot.sound plus sorryAx from stubs only);
- the child-to-child plumbing type-checks.

No fiw_ims_* name is reserved in the DAG. Book 3.13 proves completeness via L¹ convergence of multiplicities. The supplied series proof (steps 1–9) is the contract followed here.
