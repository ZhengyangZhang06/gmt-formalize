# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: |c_r| := ((c_r).natAbs : ℝ≥0∞); ‖·‖ is the operator norm on n-covectors; s(τ) := simpleNVector τ.

1. (Localization.)
   - K := tsupport ω is compact and K ⊆ U (ω ∈ TestFormOn U n).
   - exists_open_between_and_isCompact_closure gives an open W ⊇ K with L := closure W compact and L ⊆ U. So CompactlyContainedOpen W U, and A := Σ'_r |c_r|·∫⁻_{M_r ∩ W} ofReal θ_r dH < ∞.
   - ω is continuous (smooth) and vanishes off the compact set K. So there is B ≥ 0 with ‖ω(x)‖ ≤ B for all x, and ω(x) = 0 for x ∉ K.

2. (Unit bound.)
   - If τ is orthonormal and α is an n-covector, then |s(τ)(α)| = |α(τ)| ≤ ‖α‖·∏_i ‖τ_i‖ = ‖α‖ (simpleNVector_apply, ContinuousAlternatingMap.le_opNorm, ‖τ_i‖ = 1). The same holds for −s(τ).
   - The field orients of the r-th triple says that for H.restrict M_r-a.e. x, ξ_r(x) = ±s(τ) with τ orthonormal.
   - Hence |ξ_r(x)(ω(x))| ≤ ‖ω(x)‖ ≤ B·1_K(x) for H.restrict M_r-a.e. x.

3. (Domination.) θ_r > 0 on M_r and F_r = 0 off M_r. So step 2, transferred by ae_restrict_iff'₀ (M_r is null-measurable), gives for H-a.e. x:
   |F_r(x)| ≤ |c_r|·B·1_{M_r ∩ W}(x)·θ_r(x)   (using K ⊆ W).

4. (Measurability.)
   - For x ∉ L we have x ∉ K, so ω(x) = 0 and ξ_r(x)(ω(x)) = 0. Hence F_r = 1_{M_r ∩ L}·g_r with g_r(x) := c_r·θ_r(x)·ξ_r(x)(ω(x)).
   - On M_r ∩ L:
     • θ_r is integrable, hence a.e.-strongly measurable (L is compact and L ⊆ U);
     • ξ_r is a.e.-strongly measurable (field aestronglyMeasurable, restricted from M_r to M_r ∩ L);
     • ω is continuous;
     • the evaluation (v, α) ↦ v(α), NVector × Covector → ℝ, is continuous (bounded bilinear).
   - Hence x ↦ ξ_r(x)(ω(x)) and g_r are a.e.-strongly measurable for H.restrict(M_r ∩ L).
   - So F_r is a.e.-strongly measurable for H (aestronglyMeasurable_indicator_iff₀; M_r ∩ L is null-measurable).
   - Lean note (checked at this pin): `(isBoundedBilinearMap_apply.continuous : Continuous fun p : NVector (Eucl P) n × Covector (Eucl P) n => p.1 p.2).comp_aestronglyMeasurable (hξ.prodMk hω.aestronglyMeasurable)` gives the measurability of x ↦ ξ x (ω x). The curried ContinuousLinearMap.apply route fails, because no TopologicalSpace instance is found on `NVector (Eucl P) n →L[ℝ] ℝ`.

5. (Summable integrals.)
   - By step 3, lintegral_mono_ae and lintegral_indicator₀: ∫⁻ ‖F_r‖ₑ dH ≤ |c_r|·ofReal B·∫⁻_{M_r ∩ W} ofReal θ_r dH.
   - So Σ'_r ∫⁻ ‖F_r‖ₑ dH ≤ ofReal B·A < ∞ (ENNReal.tsum_mul_left).
   - In particular every F_r is integrable (step 4 plus finite integral), and r ↦ ∫ |F_r| dH is summable.

6. (Termwise integration.) By hasSum_integral_of_summable_integral_norm (or integral_tsum together with step 5):
   HasSum (r ↦ ∫ F_r dH) (∫ Σ'_r F_r dH).

7. (Identification of the terms.) By integral_indicator₀ (M_r null-measurable) and integral_const_mul:
   ∫ F_r dH = ∫_{M_r} c_r·(θ_r(x)·ξ_r(x)(ω(x))) dH = c_r·∫_{M_r} θ_r(x)·ξ_r(x)(ω(x)) dH = c_r·tauAction n M_r θ_r ξ_r ω   (definition of tauAction).
   Substituting into step 6 proves the claim. ∎

## Key steps

1. tsupport ω ⊆ W ⊂⊂ U and ‖ω(x)‖ ≤ B
2. |ξ_r(x)(α)| ≤ ‖α‖ a.e. on M_r, since ξ_r = ±simpleNVector of an orthonormal frame
3. |F_r| ≤ |c_r|·B·1_{M_r∩W}·θ_r, so Σ∫|F_r| ≤ B·A < ∞; F_r is a.e.-strongly measurable
4. hasSum_integral_of_summable_integral_norm, and ∫F_r = c_r·tauAction(M_r, θ_r, ξ_r)(ω)

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
