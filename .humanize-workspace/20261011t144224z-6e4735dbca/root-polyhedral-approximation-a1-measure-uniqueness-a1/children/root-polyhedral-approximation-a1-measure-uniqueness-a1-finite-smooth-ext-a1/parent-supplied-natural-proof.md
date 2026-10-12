# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Child DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1.finite_smooth_ext-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–6 of the supplied proof of polyhedral_approx_measure_uniqueness (Radon–Nikodym with respect to λ₁ + λ₂, then IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero on O), isolated here for two arbitrary finite measures. The supplied proof gets the density identity from integral_rnDeriv_smul. That lemma, Measure.withDensity_rnDeriv_eq and Measure.integrable_toReal_rnDeriv live in Mathlib files (RadonNikodym, IntegralRNDeriv) that the frozen GMT.Ch06.Submission header does not import. Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue is imported, so step 2 derives the identity from the Lebesgue decomposition. Every lemma named below is in scope under the frozen imports.

Throughout, ℝ^P = Eucl P carries its Borel σ-algebra.

1. (Common reference measure.) Put ν := ν₁ + ν₂, a finite measure. For i = 1, 2 we have ν_i ≤ ν, hence ν_i ≪ ν: if ν(s) = 0 then ν_i(s) ≤ ν(s) = 0. (Lean: Measure.AbsolutelyContinuous.rfl.add_right ν₂ gives ν₁ ≪ ν₁ + ν₂. For ν₂, rewrite ν₁ + ν₂ = ν₂ + ν₁ with add_comm and use Measure.AbsolutelyContinuous.rfl.add_right ν₁.)

2. (Each ν_i has a density with respect to ν.) Fix i ∈ {1, 2} and let ρ_i := ν_i.rnDeriv ν : ℝ^P → [0, ∞], a measurable function (Measure.measurable_rnDeriv).
   - ν_i and ν are finite, so the pair has a Lebesgue decomposition (the HaveLebesgueDecomposition instance is found automatically): ν_i = ν_i.singularPart ν + ν.withDensity ρ_i (Measure.haveLebesgueDecomposition_add ν_i ν).
   - The singular part is mutually singular with ν, is ≤ ν_i, and ν_i ≪ ν. A measure that is both absolutely continuous and singular with respect to ν is zero, so ν_i.singularPart ν = 0 (Measure.singularPart_eq_zero_of_ac applied to ν_i ≪ ν).
   - Hence ν_i = ν.withDensity ρ_i.

3. (Integration against ν_i.) Since ν_i is finite, ρ_i < ∞ ν-almost everywhere (Measure.rnDeriv_lt_top ν_i ν). Put f_i(x) := (ρ_i(x)).toReal ∈ [0, ∞). For a measurable, ν-a.e. finite density, integrating any function c against ν.withDensity ρ_i equals integrating x ↦ f_i(x)·c(x) against ν (integral_withDensity_eq_integral_toReal_smul with Measure.measurable_rnDeriv and Measure.rnDeriv_lt_top). This identity holds for every c : ℝ^P → ℝ: both sides use the Bochner convention, and c is integrable for ν.withDensity ρ_i exactly when f_i·c is integrable for ν. With step 2 we get, for every c : ℝ^P → ℝ,
   (∗) ∫ c dν_i = ∫ f_i(x) c(x) dν(x).

4. (The densities are ν-integrable.) ρ_i is measurable and ∫⁻ ρ_i dν ≤ ν_i(ℝ^P) < ∞ (Measure.lintegral_rnDeriv_lt_top, using that ν_i is finite). So f_i = (ρ_i)·toReal is ν-integrable (integrable_toReal_of_lintegral_ne_top). Hence F := f₁ − f₂ is ν-integrable, so F is locally integrable on O with respect to ν (Integrable.locallyIntegrable, then LocallyIntegrable.locallyIntegrableOn O).

5. (F annihilates smooth tests supported in O.) Let ψ be C^∞ with compact support and tsupport ψ ⊆ O.
   - ψ is continuous (ContDiff.continuous) with compact support, and f_i is ν-integrable, hence locally integrable. So x ↦ ψ(x) f_i(x) is ν-integrable (LocallyIntegrable.integrable_smul_left_of_hasCompactSupport).
   - By linearity of the integral (integral_sub) and (∗) with c = ψ (commuting the product ψ(x) f_i(x) = f_i(x) ψ(x)):
     ∫ ψ F dν = ∫ ψ f₁ dν − ∫ ψ f₂ dν = ∫ ψ dν₁ − ∫ ψ dν₂ = 0.
   The last equality is the hypothesis applied to ψ.

6. (F vanishes a.e. on O.) ℝ^P is a finite-dimensional real normed space with its Borel σ-algebra, O is open, and ν is a measure on ℝ^P.
   - By step 4, F is locally integrable on O. By step 5, ∫ ψ(x)·F(x) dν(x) = 0 for every ψ with ContDiff ℝ ∞ ψ, compact support and tsupport ψ ⊆ O. The smoothness class ∞ in that Mathlib lemma is exactly ((⊤ : ℕ∞) : WithTop ℕ∞) used here, so the hypothesis applies verbatim.
   - IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero therefore gives: for ν-a.e. x, x ∈ O implies F(x) = 0, i.e. f₁(x) = f₂(x).

7. (Conclusion.) Let b : ℝ^P → ℝ satisfy b(x) = 0 for all x ∉ O.
   - For ν-a.e. x we have f₁(x) b(x) = f₂(x) b(x). If x ∈ O this follows from step 6. If x ∉ O, then b(x) = 0 and both sides are 0.
   - Functions that agree ν-a.e. have equal Bochner integrals, with no measurability needed (integral_congr_ae). So by (∗) with c = b,
     ∫ b dν₁ = ∫ f₁ b dν = ∫ f₂ b dν = ∫ b dν₂. ∎

## Key steps

1. ν := ν₁ + ν₂ is finite and ν₁ ≪ ν, ν₂ ≪ ν.
2. Lebesgue decomposition plus absolute continuity (haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac): ν_i = ν.withDensity(ν_i.rnDeriv ν).
3. (∗) ∫ c dν_i = ∫ f_i·c dν for every c, where f_i = (ν_i.rnDeriv ν)·toReal is ν-integrable (integral_withDensity_eq_integral_toReal_smul, lintegral_rnDeriv_lt_top).
4. ∫ ψ·(f₁ − f₂) dν = 0 for every C^∞ ψ with compact support in O, by (∗) and the hypothesis.
5. IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero: f₁ = f₂ ν-a.e. on O.
6. For b vanishing outside O, f₁b = f₂b ν-a.e.; conclude ∫ b dν₁ = ∫ b dν₂ by (∗).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Submission.lean and GMT/Ch06/Contract.lean against local-references/197bdd4b88278494/project/GMT/Ch06/* (SUBMISSION_IDENTICAL, CONTRACT_IDENTICAL)`
- `rg -o --no-filename "polyhedral_approx_[A-Za-z0-9_']*" .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca | sort | uniq -c`
- `python3 dag.json dump of root.polyhedral_approximation-a1.* and root.slicing-a1.representation_unique-a1.* statements/lean_names/status`
- `rg -n "theorem integral_rnDeriv_smul|integrable_toReal_rnDeriv|integral_withDensity_eq_integral_toReal_smul|theorem integral_withDensity_eq_integral_smul" mathlib/Mathlib/MeasureTheory`
- `rg -n "^(theorem|lemma|instance) " mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `cat mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') via verifier/gmt-compare.py; validate_lean_statement via verifier/lean_contract.py on the 3 child statements`
- `lake build GMT.Ch06.Submission (scratch /tmp/mu_decomp_check, frozen d8d46c9, pinned package tree)`
- `lake env lean Scratch/Checks.lean; lake env lean Scratch/Checks2.lean (#check under frozen imports: integral_rnDeriv_smul / Measure.withDensity_rnDeriv_eq / Measure.integrable_toReal_rnDeriv unknown; Measure.haveLebesgueDecomposition_add, Measure.rnDeriv_lt_top, Measure.lintegral_rnDeriv_lt_top, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, integral_withDensity_eq_integral_toReal_smul₀, isFiniteMeasure_withDensity_ofReal, Integrable.bdd_mul, Integrable.of_bound, exists_open_between_and_isCompact_closure available)`
- `lake env lean Scratch/Stmts.lean (parent + 3 child statements as _root_.HumanizeNodeComparator.target_<key> in comparator scope)`
- `lake env lean Scratch/ProofA.lean; lake env lean Scratch/ProofB.lean; lake env lean Scratch/Assembly.lean (#print axioms = propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/FullCheck.lean (Submission + 4 Submission.* theorems + comparator-style `exact Submission.X` targets; #print axioms = propext, Classical.choice, Quot.sound)`
- `grep -n "2.7\|2.8\|2.9" book/chapter-06.txt; sed -n 255,300p book/chapter-06.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/IntegralRNDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-measure-uniqueness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/mu_decomp_check/Scratch/Stmts.lean`
- `/tmp/mu_decomp_check/Scratch/Checks.lean`
- `/tmp/mu_decomp_check/Scratch/Checks2.lean`
- `/tmp/mu_decomp_check/Scratch/ProofA.lean`
- `/tmp/mu_decomp_check/Scratch/ProofB.lean`
- `/tmp/mu_decomp_check/Scratch/Assembly.lean`
- `/tmp/mu_decomp_check/Scratch/FullCheck.lean`

Snapshot facts:
- The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract and a byte-identical Submission. Neither contains polyhedral_approx_* declarations.
- The run uses only the seven sibling names polyhedral_approx_{pairing_expansion, measure_uniqueness, restriction_exists, restriction_tau, open_truncation, truncation_seq, finite_mass_seq}. The proposed polyhedral_approx_finite_smooth_ext, polyhedral_approx_density_split and polyhedral_approx_integrable_smooth_ext are unused.

Mathlib in scope:
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean) is in scope under the frozen imports and needs no local-finiteness hypothesis.
- integral_rnDeriv_smul, which the supplied proof cites, and withDensity_rnDeriv_eq live in RadonNikodym.lean. Measure.integrable_toReal_rnDeriv lives in IntegralRNDeriv.lean. None of these files is imported by GMT.Ch06.Submission: all three names are unknown identifiers there.
- Lebesgue.lean is imported and supplies haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac, rnDeriv_lt_top, lintegral_rnDeriv_lt_top and measurable_rnDeriv. The child proof is built on these.
- ContinuousLinearMap.lean supplies integral_withDensity_eq_integral_toReal_smul(₀) with no integrability hypothesis.

Other sources:
- SimonGMT has no measure-uniqueness lemma.
- Simon's text (2.7)–(2.9) asserts the uniqueness without proof.
- The slicing branch's similar children are not comparator-accepted, so they cannot be reused.

Scratch-build results:
- All three child statements validate and elaborate in the comparator scope.
- Full proofs of the three children compile using only the frozen imports, as does the parent derived from child (3).
- The comparator-style `exact Submission.X` targets for all three children and the parent depend only on propext, Classical.choice and Quot.sound.
