# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.im_closure-a1`
- Child DAG node: `root.integrality_weak_limits-a1.im_closure-a1.restriction_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P := Eucl P and H := Hᵏ := μHE[k]. D_k(U) := GeometricCurrentOn U k and D^k(U) := TestFormOn U k. τ(M, θ, ξ)(ω) := tauAction k M θ ξ ω = ∫_M θ(x)·ξ(x)(ω(x)) dH(x). "i.m." means IsIntegerMultiplicity. HasWATS k M θ x Q abbreviates HasWeightedApproximateTangentSpaceAt k M θ x Q. IsRestriction X A S means: A is a measurable (Borel) set, and there is a measure representation (μ, v) of X (IsMeasureRepresentation X μ v) with S(ω) = ∫_A v(x)(ω(x)) dμ(x) for every ω ∈ D^k(U).

The hypothesis (T) of the statement says the following. Let M₁′, M₂′ ⊆ U be H-null-measurable and θ₁′, θ₂′ : ℝ^P → ℝ, with θ_l′ ≥ 1 on M_l′ and θ_l′ H-integrable on M_l′ ∩ K for every compact K ⊆ U. Then for H⌞(M₁′ ∩ M₂′)-a.e. x, every Q with HasWATS k M₁′ θ₁′ x Q also satisfies HasWATS k M₂′ θ₂′ x Q. In the parent, (T) is supplied by the sibling iwl_imc_tangent_overlap.

Source. This is part (b) of the parent proof.
- Step 1 there identifies the restriction with τ(M ∩ A, θ, ξ). The parent obtains this from (R1) of iwl_restriction_theory; here it is obtained from the uniqueness of measure representations (sibling `slicing_representation_unique`), which is the principle behind (R1).
- Step 2 there (orientation of M ∩ A through density zero and tangent locality) is one application of (T).

Statement. Let U ⊆ ℝ^P be open and assume (T). If X ∈ D_k(U) is i.m., A ⊆ ℝ^P and S ∈ D_k(U) satisfy IsRestriction X A S, then S is i.m.

1. (Data.)
   - X is i.m., so there are M, θ, ξ with IsRectifiableTriple U k M θ ξ, θ(x) ∈ ℕ for x ∈ M, and X(ω) = τ(M, θ, ξ)(ω) for every ω ∈ D^k(U).
   - IsRestriction X A S gives: A is measurable, a measure μ and v : ℝ^P → Λ_k with IsMeasureRepresentation X μ v, and S(ω) = ∫_A v(ω) dμ for every ω.
   - Since θ(x) > 0 (field `pos`) and θ(x) ∈ ℕ, we get θ ≥ 1 on M.

2. (A second representation.) By the sibling `iwl_imc_tau_measure_representation`, (H⌞M, θ • ξ) is a measure representation of X.

3. (Restriction formula, parent step (b)1.) Apply the sibling `slicing_representation_unique` with U (open), μ₁ := μ, v₁ := v, μ₂ := H⌞M, v₂ := θ • ξ, and W := U (open). Its hypotheses hold:
   - integrability of x ↦ v₁(x)(ω(x)) and x ↦ v₂(x)(ω(x)) for every ω (steps 1–2);
   - for every ω ∈ D^k(U), ∫ v₁(ω) dμ₁ = X(ω) = ∫ v₂(ω) dμ₂ (both representations of X);
   - tsupport ω ⊆ U holds for every ω ∈ D^k(U).
   For the measurable set A it gives, for every ω:
     S(ω) = ∫_A v(ω) dμ = ∫_A (θ • ξ)(ω) d(H⌞M).
   Since A is measurable, (H⌞M)⌞A = H⌞(A ∩ M) = H⌞(M ∩ A) (`Measure.restrict_restrict`, `inter_comm`), and (θ(x) • ξ(x))(ω(x)) = θ(x)·ξ(x)(ω(x)). Hence S(ω) = ∫_{M∩A} θ(x)·ξ(x)(ω(x)) dH(x) = τ(M ∩ A, θ, ξ)(ω) for every ω ∈ D^k(U).

4. (The restricted triple, parent step (b)2.) We check IsRectifiableTriple U k (M ∩ A) θ ξ field by field.
   - subset: M ∩ A ⊆ M ⊆ U.
   - nullMeasurableSet: M is H-null-measurable and A is measurable, so M ∩ A is H-null-measurable.
   - countablyRectifiable: M ∩ A ⊆ M (`CountablyRectifiable.mono`).
   - pos: θ > 0 on M ∩ A ⊆ M.
   - integrableOn: for compact K ⊆ U, (M ∩ A) ∩ K ⊆ M ∩ K and θ is integrable on M ∩ K (`IntegrableOn.mono_set`).
   - aestronglyMeasurable: H⌞(M ∩ A) ≤ H⌞M (`Measure.restrict_mono`), so ξ stays a.e.-strongly measurable (`AEStronglyMeasurable.mono_measure`).
   - orients:
     · Apply (T) with (M₁′, θ₁′) := (M, θ) and (M₂′, θ₂′) := (M ∩ A, θ). Its hypotheses are the fields just listed together with θ ≥ 1 on M ⊇ M ∩ A.
     · Since M ∩ (M ∩ A) = M ∩ A, for H⌞(M ∩ A)-a.e. x every weighted tangent space of (M, θ) at x is one of (M ∩ A, θ) at x.
     · The field `orients` of (M, θ, ξ) holds H⌞M-a.e., hence H⌞(M ∩ A)-a.e. (`ae_restrict_of_ae_restrict_of_subset`).
     · Combining the two a.e. statements: for H⌞(M ∩ A)-a.e. x there is an orthonormal τ with HasWATS k M θ x (span(range τ)) and ξ(x) = ±simpleNVector τ. Then HasWATS k (M ∩ A) θ x (span(range τ)) holds, which is the orientation condition for (M ∩ A, θ, ξ) at x.

5. (Conclusion, parent step (b)3.) θ(x) ∈ ℕ for x ∈ M ∩ A ⊆ M. Together with step 4 and the formula S = τ(M ∩ A, θ, ξ) of step 3, this shows S is integer multiplicity, with data (M ∩ A, θ, ξ). ∎

Formalization notes (a complete Lean proof of exactly this statement compiled in a scratch build of frozen commit d8d46c9, with the siblings as stubs):
- Step 3 is
  `Submission.slicing_representation_unique P k U hU μ (μHE[k].restrict M) v (fun x => θ x • ξ x) (fun ω => (hrepr ω).1) (fun ω => (hrepr2 ω).1) U hU (fun ω _ => by rw [← (hrepr ω).2, ← (hrepr2 ω).2]) A hA ω ω.2.2`,
  followed by `rw [Measure.restrict_restrict hA, inter_comm]` and `simp only [tauAction, smul_apply, smul_eq_mul]`.
- For θ ≥ 1, use `exact_mod_cast` from `0 < (n : ℝ)`.
- M ∩ (M ∩ A) = M ∩ A follows from `rw [← inter_assoc, inter_self]`.
- The `orients` field is closed by `filter_upwards`.

## Key steps

1. Unpack X = τ(M, θ, ξ) with θ ∈ ℕ (so θ ≥ 1 on M) and IsRestriction X A S: A measurable, a representation (μ, v) of X, S(ω) = ∫_A v(ω) dμ.
2. (Hᵏ⌞M, θξ) also represents X (sibling tau_repr); uniqueness of measure representations (sibling representation_unique with W = U) gives S(ω) = ∫_A (θ • ξ)(ω) d(Hᵏ⌞M) = τ(M ∩ A, θ, ξ)(ω).
3. (M ∩ A, θ, ξ) inherits subset, null-measurability, countable rectifiability, positivity, local integrability and measurability of ξ from (M, θ, ξ).
4. Orientation: (T) applied to (M, θ) and (M ∩ A, θ) transfers the weighted tangent space span τ of (M, θ) at a.e. x ∈ M ∩ A, with ξ(x) = ±simpleNVector τ unchanged; hence S is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); cmp workspace Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (identical)`
- `python3 dag.json scans (re-run just before submission): status/candidate_commit/lean_statement/title/statement of rectifiability_density_comparison, slicing_representation_unique, ltg_tau_integrable, fiw_ims_frame_sign, fiw_ims_orientation_sign, iwl_restriction_theory, iwl_weighted_tangent_locality, lpf_wtc_ae_zero_density_off_set, br_weightedTangent_congr; regex scan of all accepted nodes for Lebesgue|IsMeasureRepresentation|tauAction|HasWeightedApproximateTangentSpaceAt|density; reserved names (no iwl_imc_*)`
- `sed -n 6532,6575p and 2364,2368p /runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py (_existing_lean_name_problem / _accepted_checkpoint: why attempt 1's lpf reuse was rejected)`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity|realUnitBallVolume' simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div|theorem tendsto_filterAt|protected def vitaliFamily' mathlib/Mathlib/MeasureTheory/Covering/{Differentiation,Besicovitch}.lean (Differentiation.lean:818, Besicovitch.lean:1021 and 1060)`
- `grep -rn 'theorem withDensity_apply |theorem setLIntegral_measure_zero|theorem _root_.Set.measure_eq_iInf_isOpen|theorem nullMeasurableSet_eq_fun' mathlib/Mathlib/MeasureTheory (found in Measure/WithDensity.lean:44, Integral/Lebesgue/Basic.lean:478, Measure/Regular.lean:368, Function/StronglyMeasurable/AEStronglyMeasurable.lean:575)`
- `sed -n 724,770p book/chapter-06.txt (Simon Ch. 6, 3.1 and 3.2 Remarks (1)-(3)); grep -n "3.3 Theorem|3.6 Theorem|3.7 Remarks" book/chapter-01.txt`
- `verifier/gmt-compare.py child_modules (contract mode) + verifier/lean_contract.validate_lean_statement on all 11 child types and the parent`
- `lean v4.35.0-rc3 (LEAN_PATH scratch build + lake-packages-25730c7c): lean -o build3/GMT/Ch06/Submission.olean src3/Submission.lean; lean checks/NodeChallenge_00..11.lean (frozen build) and checks/NodeSolution_00..11.lean (build3) with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/imc-decomp-v2/src3/Submission.lean`
- `/tmp/imc-decomp-v2/logs/src3.out`
- `/tmp/imc-decomp-v2/checks/NodeSolution_11.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract, and Submission is byte-identical to it.

Available tools:
- SimonGMT: HasWeightedApproximateTangentSpaceAt (Ch. 3, 1.7, a limit over blow-ups, so it is invariant under a nonzero constant factor), its uniqueness lemma, CountablyRectifiable.mono / countablyRectifiable_iUnion, dimensionalUpperDensity and realUnitBallVolume.
- Mathlib (imported via Covering.DensityTheorem): Lebesgue–Besicovitch differentiation (VitaliFamily.ae_tendsto_lintegral_enorm_sub_div with Besicovitch.vitaliFamily / tendsto_filterAt), withDensity, outer regularity of finite measures, and AEStronglyMeasurable.nullMeasurableSet_eq_fun.
- The contract does not import SimonGMT's Chapter01.DensityComparison. Density comparison is therefore taken from the accepted Submission theorem rectifiability_density_comparison, and the Upper Density Theorem is the new child iwl_imc_density_zero_off_set.

Controller code (runtime.py) explains the rejected attempt: reuse requires an accepted checkpoint in the controller's view. The replacement child sidesteps the reservation on lpf_wtc_ae_zero_density_off_set.

Scratch Lean results (/tmp/imc-decomp-v2):
- All 11 child types and the parent elaborate in the exact comparator child scope.
- Complete single-theorem proofs of the 6 new children compile.
- The parent assembles from the children plus iwl_weighted_tangent_locality and iwl_restriction_theory.
- Axiom footprints are [propext, Classical.choice, Quot.sound] plus the intended stubs.
