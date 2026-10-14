# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation:
- |α| := covectorEuclideanNorm α; ‖α‖ := the operator norm of α as a continuous alternating map.
- |c_r| := ((c_r).natAbs : ℝ≥0∞) = ENNReal.ofReal|(c_r : ℝ)|.
- A(W) := Σ'_r |c_r|·M_W(T_r) ∈ [0, ∞] for a set W.
- 'mass_bound' is the sibling: ofReal|X(η)| ≤ M_V(X)·ofReal C whenever C > 0, tsupport η ⊆ V and |η(x)| ≤ C for all x.

0. (Auxiliary facts.)
   (a) For every compact K ⊆ U there is W with CompactlyContainedOpen W U and K ⊆ W. Indeed ℝ^P is locally compact and regular, so exists_open_between_and_isCompact_closure gives an open W with K ⊆ W, closure W ⊆ U and closure W compact.
   (b) |α| ≤ D·‖α‖ for every n-covector α, where D := √(P^n).
       - For every I : Fin n → Fin P, |α(e_{I_1}, …, e_{I_n})| ≤ ‖α‖·∏_i ‖e_{I_i}‖ = ‖α‖ (ContinuousAlternatingMap.le_opNorm; basis vectors have norm 1).
       - The sum defining |α|² has at most P^n nonzero terms.
   (c) For every ω ∈ D^n(U) there is B_ω ≥ 0 with ‖ω(x)‖ ≤ B_ω for all x: ω is continuous (smooth) and vanishes outside the compact set tsupport ω, on which it is bounded. By (b), |ω(x)| ≤ D·B_ω for all x.
   (d) Multiplying an inequality a ≤ b in [0, ∞] by |c_r| keeps it valid, also when c_r = 0 (both sides become 0) and when b = ∞.

1. (Absolute summability; definition of S(ω).) Fix ω ∈ D^n(U).
   - K := tsupport ω is compact and K ⊆ U (definition of TestFormOn). By 0(a) there is W ⊂⊂ U with K ⊆ W, and A(W) < ∞ by hypothesis.
   - Put C := D·B_ω + 1 > 0, so |ω(x)| ≤ C for all x.
   - mass_bound with X := T_r, V := W, η := ω gives ofReal|T_r(ω)| ≤ M_W(T_r)·ofReal C.
   - By 0(d), for every r: ofReal|c_r T_r(ω)| = |c_r|·ofReal|T_r(ω)| ≤ ofReal C·|c_r|·M_W(T_r).
   - Hence Σ'_r ofReal|c_r T_r(ω)| ≤ ofReal C·A(W) < ∞ (ENNReal.tsum_le_tsum, ENNReal.tsum_mul_left).
   - Nonnegative reals with finite [0, ∞]-valued sum are summable, so r ↦ |c_r T_r(ω)| is summable. As ℝ is complete, r ↦ c_r T_r(ω) is summable.
   - Define S₀(ω) := Σ'_r c_r T_r(ω). Then:
     • HasSum (r ↦ c_r T_r(ω)) (S₀(ω)) (Summable.hasSum);
     • |S₀(ω)| ≤ Σ'_r |c_r T_r(ω)| (norm_tsum_le_tsum_norm);
     • ofReal|S₀(ω)| ≤ Σ'_r ofReal|c_r T_r(ω)| (ENNReal.ofReal_tsum_of_nonneg).

2. (Linearity.) Let ω, η ∈ D^n(U) and a ∈ ℝ.
   - By linearity of each T_r: c_r T_r(ω + η) = c_r T_r(ω) + c_r T_r(η), and c_r T_r(a • ω) = a·(c_r T_r(ω)).
   - HasSum.add and HasSum.mul_left give HasSum (r ↦ c_r T_r(ω + η)) (S₀ω + S₀η) and HasSum (r ↦ c_r T_r(a • ω)) (a·S₀ω).
   - By uniqueness of sums (HasSum.unique together with step 1 for ω + η and a • ω): S₀(ω + η) = S₀ω + S₀η and S₀(a • ω) = a·S₀ω.
   - So S₀ is an ℝ-linear map TestFormOn U n →ₗ[ℝ] ℝ.

3. (Sequential continuity.) Let (ω_q) satisfy TestFormOnConverges ω_q 0.
   - There is a compact K ⊆ U with tsupport ω_q ⊆ K for all q such that, for k = 0, iteratedFDeriv ℝ 0 ω_q → iteratedFDeriv ℝ 0 0 = 0 uniformly on K.
   - Since ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ (norm_iteratedFDeriv_zero), sup_{x∈K} ‖ω_q(x)‖ → 0. Also ω_q(x) = 0 for x ∉ K.
   - Choose W ⊂⊂ U with K ⊆ W (0(a)), so A(W) < ∞.
   - Let ε > 0. For all large q, ‖ω_q(x)‖ ≤ ε/(D + 1) for all x, hence |ω_q(x)| ≤ D·ε/(D + 1) ≤ ε for all x by 0(b).
   - For such q, mass_bound with X := T_r, V := W, η := ω_q, C := ε, together with 0(d), gives ofReal|c_r T_r(ω_q)| ≤ ofReal ε·|c_r|·M_W(T_r).
   - So by step 1, ofReal|S₀(ω_q)| ≤ Σ'_r ofReal|c_r T_r(ω_q)| ≤ ofReal ε·A(W).
   - As A(W) < ∞ and ε > 0 is arbitrary, S₀(ω_q) → 0.
   - Hence S := ⟨S₀, this continuity proof⟩ is a GeometricCurrentOn U n with S(ω) = S₀(ω), and step 1 gives HasSum (r ↦ c_r T_r(ω)) (S(ω)) for every ω.

4. (Mass bound.) Let W ⊆ ℝ^P be any set and ω ∈ massAdmissibleOn U n W, i.e. tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x.
   - mass_bound with V := W and C := 1 gives ofReal|T_r(ω)| ≤ M_W(T_r).
   - With 0(d) and step 1:
     ofReal(S(ω)) ≤ ofReal|S(ω)| ≤ Σ'_r ofReal|c_r T_r(ω)| = Σ'_r |c_r|·ofReal|T_r(ω)| ≤ Σ'_r |c_r|·M_W(T_r).
   - M_W(S) is the supremum of ofReal(S(ω)) over such ω (definition of massOn; sSup_le), so M_W(S) ≤ Σ'_r |c_r|·M_W(T_r). ∎

## Key steps

1. choose W ⊂⊂ U ⊇ tsupport ω; mass_bound gives Σ|c_r T_r(ω)| ≤ C·Σ|c_r|M_W(T_r) < ∞
2. S(ω) := Σ' c_r T_r(ω); linearity from HasSum.add / HasSum.mul_left and uniqueness of sums
3. continuity: k = 0 uniform convergence and |α| ≤ √(P^n)‖α‖ give sup|ω_q| → 0, so |S(ω_q)| ≤ ε·A(W)
4. mass bound: ofReal(S ω) ≤ Σ'|c_r|M_W(T_r) for admissible ω (mass_bound with C = 1); take the supremum

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
