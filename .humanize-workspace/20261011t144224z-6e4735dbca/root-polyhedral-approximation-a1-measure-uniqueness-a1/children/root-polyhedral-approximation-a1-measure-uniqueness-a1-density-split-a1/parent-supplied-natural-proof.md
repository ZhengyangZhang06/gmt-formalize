# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1`
- Child DAG node: `root.polyhedral_approximation-a1.measure_uniqueness-a1.density_split-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the supplied proof of polyhedral_approx_measure_uniqueness: the measures ν_i^± and the identity behind (★), for one integrable density. The supplied proof applies this to μ_i⌞L, on which g_i is integrable. Here the a.e.-measurable density ofReal ∘ (±g) is used directly, instead of first choosing a Borel version h of g. Every lemma named below is in scope under the frozen GMT.Ch06.Submission imports.

Throughout, r⁺ := max(r, 0) for r ∈ ℝ, and ofReal r ∈ [0, ∞) ⊆ [0, ∞] denotes r⁺ viewed as an extended nonnegative real (ENNReal.ofReal).

1. (Definition.) Put νpos := μ.withDensity (x ↦ ofReal(g(x))) and νneg := μ.withDensity (x ↦ ofReal(−g(x))).

2. (Finiteness.) νpos(ℝ^P) = ∫⁻ ofReal(g) dμ ≤ ∫⁻ |g| dμ < ∞, since a μ-integrable g has finite integral. Likewise νneg(ℝ^P) = ∫⁻ ofReal(−g) dμ ≤ ∫⁻ |−g| dμ < ∞. So both measures are finite. (Lean: isFiniteMeasure_withDensity_ofReal applied to hg.2 : HasFiniteIntegral g μ, and to hg.neg.2.)

3. (Integrals against νpos and νneg.) g is μ-integrable, hence μ-a.e. measurable. So x ↦ ofReal(g(x)) and x ↦ ofReal(−g(x)) are μ-a.e. measurable (AEMeasurable.ennreal_ofReal, applied to g and to x ↦ −g(x)), and they are finite everywhere (ENNReal.ofReal_lt_top). For such densities, integration against the withDensity measure is integration of the real density times the integrand (integral_withDensity_eq_integral_toReal_smul₀). Since (ofReal r).toReal = r⁺ (ENNReal.toReal_ofReal'), for every b : ℝ^P → ℝ:
   ∫ b dνpos = ∫ g(x)⁺ b(x) dμ(x),  ∫ b dνneg = ∫ (−g(x))⁺ b(x) dμ(x).

4. (Integrability.) Fix a Borel measurable b with |b(x)| ≤ C for all x.
   - g⁺ = max(g, 0) and (−g)⁺ = max(−g, 0) are μ-integrable (Integrable.pos_part applied to g and to −g).
   - b is measurable, hence a.e.-strongly measurable, and ‖b(x)‖ ≤ C for all x.
   - So g⁺·b and (−g)⁺·b are μ-integrable: a bounded a.e.-strongly measurable factor times an integrable function is integrable (Integrable.bdd_mul, then commute the product).

5. (Combination.) By step 3, linearity of the integral for the two integrable functions of step 4 (integral_sub), and the identity r⁺ − (−r)⁺ = r (max_zero_sub_max_neg_zero_eq_self):
   ∫ b dνpos − ∫ b dνneg = ∫ (g(x)⁺ − (−g(x))⁺) b(x) dμ = ∫ g(x) b(x) dμ = ∫ b(x) g(x) dμ.
   This holds for every bounded Borel b, which proves the claim with ν⁺ := νpos and ν⁻ := νneg. ∎

## Key steps

1. Define νpos := μ.withDensity(ofReal ∘ g) and νneg := μ.withDensity(ofReal ∘ (−g)).
2. Both are finite because ∫⁻ ofReal(±g) dμ ≤ ∫⁻ |g| dμ < ∞ (isFiniteMeasure_withDensity_ofReal).
3. ∫ b dνpos = ∫ g⁺ b dμ and ∫ b dνneg = ∫ (−g)⁺ b dμ for every b (integral_withDensity_eq_integral_toReal_smul₀, ENNReal.toReal_ofReal').
4. For bounded Borel b, g⁺b and (−g)⁺b are μ-integrable (Integrable.pos_part, Integrable.bdd_mul).
5. Subtract and use g⁺ − (−g)⁺ = g.

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
