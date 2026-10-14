# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Child DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1.integrable_smooth_ext-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–6 of the supplied proof of polyhedral_approx_measure_uniqueness. The measures μ_i⌞L there are replaced by arbitrary measures μ_i on which g_i is integrable. The construction of ν_i^± (supplied steps 2–3) is the sibling polyhedral_approx_density_split. The Radon–Nikodym / distribution step (supplied step 5) is the sibling polyhedral_approx_finite_smooth_ext. Every other lemma named below is in scope under the frozen GMT.Ch06.Submission imports.

1. (Split both signed measures.) Apply polyhedral_approx_density_split to (μ₁, g₁) and to (μ₂, g₂). This gives finite measures p₁, n₁, p₂, n₂ on ℝ^P such that, for i = 1, 2 and every Borel measurable bounded c : ℝ^P → ℝ,
   ∫ c dp_i − ∫ c dn_i = ∫ c g_i dμ_i.

2. (Two finite measures.) Put λ₁ := p₁ + n₂ and λ₂ := p₂ + n₁. Both are finite, being sums of finite measures.

3. (Identity (★).) Let c be Borel measurable with |c(x)| ≤ C for all x.
   - c is integrable against each of the finite measures p₁, n₁, p₂, n₂: it is measurable, hence a.e.-strongly measurable, and ‖c(x)‖ ≤ C everywhere (Integrable.of_bound).
   - So the integral is additive in the measure (integral_add_measure):
     ∫ c dλ₁ = ∫ c dp₁ + ∫ c dn₂ and ∫ c dλ₂ = ∫ c dp₂ + ∫ c dn₁.
   - Subtracting and using step 1:
     (★) ∫ c dλ₁ − ∫ c dλ₂ = (∫ c dp₁ − ∫ c dn₁) − (∫ c dp₂ − ∫ c dn₂) = ∫ c g₁ dμ₁ − ∫ c g₂ dμ₂.

4. (λ₁ and λ₂ agree on smooth tests supported in O.) Let ψ be C^∞ with compact support and tsupport ψ ⊆ O.
   - ψ is continuous (ContDiff.continuous), hence Borel measurable.
   - Being continuous with compact support, ψ is bounded: there is C with ‖ψ(x)‖ ≤ C for all x (Continuous.bounded_above_of_compact_support).
   - By (★) with c = ψ and the hypothesis ∫ ψ g₁ dμ₁ = ∫ ψ g₂ dμ₂: ∫ ψ dλ₁ − ∫ ψ dλ₂ = 0, i.e. ∫ ψ dλ₁ = ∫ ψ dλ₂.

5. (Apply the finite-measure uniqueness.) λ₁ and λ₂ are finite measures, O is open, and step 4 holds for every C^∞ ψ with compact support and tsupport ψ ⊆ O. Since b vanishes outside O, polyhedral_approx_finite_smooth_ext gives ∫ b dλ₁ = ∫ b dλ₂.

6. (Conclusion.) b is Borel measurable and bounded, so (★) applies with c = b. With step 5:
   ∫ b g₁ dμ₁ − ∫ b g₂ dμ₂ = ∫ b dλ₁ − ∫ b dλ₂ = 0.
   Hence ∫ b g₁ dμ₁ = ∫ b g₂ dμ₂. ∎

## Key steps

1. polyhedral_approx_density_split for (μ₁, g₁) and (μ₂, g₂) gives finite p_i, n_i with ∫ c dp_i − ∫ c dn_i = ∫ c g_i dμ_i for bounded Borel c.
2. λ₁ := p₁ + n₂ and λ₂ := p₂ + n₁ are finite, and (★) ∫ c dλ₁ − ∫ c dλ₂ = ∫ c g₁ dμ₁ − ∫ c g₂ dμ₂ for bounded Borel c (Integrable.of_bound, integral_add_measure).
3. (★) and the hypothesis give ∫ ψ dλ₁ = ∫ ψ dλ₂ for C^∞ ψ with compact support in O (smooth ψ is Borel and bounded).
4. polyhedral_approx_finite_smooth_ext gives ∫ b dλ₁ = ∫ b dλ₂ for b vanishing outside O.
5. (★) with c = b gives ∫ b g₁ dμ₁ = ∫ b g₂ dμ₂.

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
