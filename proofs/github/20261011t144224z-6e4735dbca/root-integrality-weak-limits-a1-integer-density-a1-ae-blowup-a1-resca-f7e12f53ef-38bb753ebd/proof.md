# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.rescaled_tangent_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 4 and 9b–9c of the parent proof: the change of variables (★), and the identification A(r) = ∫_{η_{x,r}(M)} f(z)θ(x + rz) dHⁿ(z) followed by the definition of the weighted approximate tangent space. Here they are stated for an arbitrary f ∈ C_c(ℝ^P, ℝ).

Notation: Hⁿ := μHE[n] on ℝ^P, and η_r(y) := blowUpMap x r y = r⁻¹•(y − x) for r ∈ ℝ.

1. Packaging f. Since f is continuous with compact support, F := ⟨⟨f, hf⟩, hfc⟩ is an element of C_c(ℝ^P, ℝ) whose underlying function is f.

2. The tangent condition. By definition, HasWeightedApproximateTangentSpaceAt n M θ x Q is the conjunction of two statements:
- finrank_ℝ Q = n;
- for every G ∈ C_c(ℝ^P, ℝ), ∫_{η_r(M)} G(z)θ(x + r•z) dHⁿ(z) → θ(x)∫_Q G dHⁿ as r → 0⁺ (filter 𝓝[>] 0).
Apply the second conjunct to G := F:
  J(r) := ∫_{η_r(M)} f(z)θ(x + r•z) dHⁿ(z) → θ(x)∫_Q f dHⁿ as r → 0⁺.

3. Change of variables (★). Fix r > 0. Use the comparator-accepted declaration Submission.lpf_wtc_blowup_setIntegral_image, reused by name with its identical frozen type
  ∀ Q n y r S g, 0 < r → ∫ z in blowUpMap y r '' S, g z ∂μHE[n] = (r ^ n)⁻¹ * ∫ x in S, g (blowUpMap y r x) ∂μHE[n].
Take ambient dimension P, centre x, S := M and g(z) := f(z)θ(x + r•z). This gives
  J(r) = (rⁿ)⁻¹ ∫_M f(η_r(y)) θ(x + r•η_r(y)) dHⁿ(y).
Why (★) holds: η_r is a homeomorphism (a translation followed by z ↦ r⁻¹z), hence a measurable embedding. Since η_r⁻¹(B) = x + r•B, translation invariance of Hⁿ (Isometry.euclideanHausdorffMeasure_image) and the scaling Hⁿ(r•B) = rⁿHⁿ(B) (Measure.euclideanHausdorffMeasure_smul₀) show that η_r pushes (rⁿ)⁻¹Hⁿ forward to Hⁿ. The image formula for measure-preserving measurable embeddings (MeasurePreserving.setIntegral_image_emb) then gives the identity for every S and g. Both sides are 0 when the integrand is not integrable.

4. Simplifying the integrand. For r > 0 and every y:
  x + r•η_r(y) = x + r•(r⁻¹•(y − x)) = x + (y − x) = y, and η_r(y) = r⁻¹•(y − x).
So the integrand in step 3 equals f(r⁻¹•(y − x))θ(y) = θ(y)f(r⁻¹•(y − x)) for every y. Hence for every r > 0:
  J(r) = (rⁿ)⁻¹ ∫_M θ(y)f(r⁻¹•(y − x)) dHⁿ(y).

5. Conclusion. The function r ↦ (rⁿ)⁻¹ ∫_M θ(y)f(r⁻¹•(y − x)) dHⁿ(y) agrees with J on (0, ∞), and (0, ∞) belongs to 𝓝[>] 0. Functions that agree eventually along a filter have the same limits along it (Tendsto.congr'). By step 2, this function therefore tends to θ(x)∫_Q f dHⁿ as r → 0⁺. ∎

Appendix (formalization aid; not part of the mathematical argument). The following script was kernel-checked in scratch against the frozen environment (Lean v4.35.0-rc3, Mathlib 25730c7c, `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open`s) and depends only on propext, Classical.choice and Quot.sound:

theorem Submission.ind_ab_rescaled_tangent_limit :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (Q : Submodule ℝ (Eucl P)) (f : Eucl P → ℝ), HasWeightedApproximateTangentSpaceAt n M θ x Q → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ y in M, θ y * f (r⁻¹ • (y - x)) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 (θ x * ∫ z in (Q : Set (Eucl P)), f z ∂(μHE[n] : Measure (Eucl P)))) := by
  intro P n M θ x Q f hQ hf hfc
  let F : CompactlySupportedContinuousMap (Eucl P) ℝ := ⟨⟨f, hf⟩, hfc⟩
  have h := hQ.2 F
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  rw [Submission.lpf_wtc_blowup_setIntegral_image P n x r M _ hr]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hy : x + r • Poincare.SimonGMT.Chapter03.blowUpMap x r y = y := by
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr0, one_smul]
    abel
  simp only [hy]
  show f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) * θ y = θ y * f (r⁻¹ • (y - x))
  rw [mul_comm]
  rfl

## Key steps

1. Package f as F ∈ C_c(ℝ^P, ℝ) and apply the second conjunct of HasWeightedApproximateTangentSpaceAt n M θ x Q to F.
2. For r > 0, rewrite ∫_{blowUpMap x r '' M} f(z)θ(x + r•z) dHⁿ with the accepted Submission.lpf_wtc_blowup_setIntegral_image (S := M, g(z) := f(z)θ(x + r•z)).
3. Simplify using x + r•(r⁻¹•(y − x)) = y: the integrand becomes θ(y)f(r⁻¹•(y − x)).
4. The two functions agree on (0, ∞) ∈ 𝓝[>] 0, so they have the same limit (Tendsto.congr').

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (identical); diff snapshot Contract.lean vs workspace GMT/Ch06/Contract.lean (identical)`
- `rg -n 'ind_ab_' project/ and simongmt/Poincare (no match); python3 scan of dag.json lean_name and theorems lists for ind_ab_* (362 nodes, no match); git grep -l 'ind_ab_' over all local branch heads (no match)`
- `python3 scan of dag.json for the accepted lpf_wtc_blowup_setIntegral_image, fiw_ims_tt_unit_bound, ltg_tau_integrable, lpf_wtc_density_bound_of_tangent, lpf_wtc_wtt_remainder_vanishes and lpf_wtc_wtt_blowup_integral_split, and for the sibling ind_* statements`
- `sed -n '/def blowUpMap/,/^$/p;/def HasWeightedApproximateTangentSpaceAt/,/^$/p' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def simpleNVector|abbrev Covector|abbrev DifferentialForm' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean Chapter06/Forms.lean`
- `rg -n 'HasWeightedApproximateTangentSpaceAt|theorem .*blowUp|ae_tendsto_lintegral_enorm_sub_div|vitaliFamily|Besicovitch|withDensity' simongmt/Poincare -g '*.lean'`
- `rg -n 'protected def vitaliFamily|theorem tendsto_filterAt' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; rg -n 'theorem ae_tendsto_lintegral_enorm_sub_div' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n 'lemma withDensity_absolutelyContinuous|setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀|theorem withDensity_apply' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `rg -n 'aestronglyMeasurable_iUnion_iff|Continuous.comp_aestronglyMeasurable₂|IntegrableOn.of_ae_sdiff_eq_zero|Measure.integrableOn_of_bounded|Integrable.lintegral_lt_top|enorm_integral_le_lintegral_enorm|ofReal_integral_eq_lintegral_ofReal|sigmaFinite_of_locallyFinite|isBoundedBilinearMap_apply|HasCompactMulSupport.exists_bound_of_continuous|div_le_iff|div_mul_cancel|div_zero|instHasBesicovitchCovering' in the snapshot mathlib/Mathlib files listed`
- `git show <lpf blow-up branch>:GMT/Ch06/Submission.lean (accepted proof of Submission.lpf_wtc_blowup_setIntegral_image)`
- `sed -n 2400,2440p book/chapter-06.txt (printed Proof of 8.2, display (7))`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on the 4 child statements`
- `lake env lean /tmp/ab-decomp-scratch/{Stmts,Pairing,Enorm,C1,C24,C3,Assembly,Full}.lean (#synth, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ab-decomp-scratch/Stmts.lean`
- `/tmp/ab-decomp-scratch/Assembly.lean`
- `/tmp/ab-decomp-scratch/Full.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract, byte-identical to its Submission and to the workspace Contract.

Available API and reuse:
- The contract's own scope opens only CountablyRectifiable and HasWeightedApproximateTangentSpaceAt from Chapter03. The statements therefore spell blow-ups as r⁻¹ • (y - x), not blowUpMap.
- SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap and the definition of HasWeightedApproximateTangentSpaceAt (finrank plus a C_c blow-up limit).
- Chapter06 supplies NVector = Covector →L ℝ and simpleNVector (built with mkContinuous, bound ∏‖v_i‖).
- SimonGMT has no weighted Lebesgue-point or rescaled-tangent lemma for general (M, θ). Chapter04/WeightedBlowUp.lean (tendsto_rescaled_weight_of_weighted_approximateTangent) is a varifold-specific analogue of child 1. It is not imported by the contract and does not apply to arbitrary M and θ.
- The snapshot Mathlib supplies everything children 3 and 4 need: Besicovitch.vitaliFamily, Besicovitch.tendsto_filterAt, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, withDensity_apply, withDensity_absolutelyContinuous(') and setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀; aestronglyMeasurable_iUnion_iff, IntegrableOn.of_ae_sdiff_eq_zero, Measure.integrableOn_of_bounded, Integrable.lintegral_lt_top, enorm_integral_le_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal and sigmaFinite_of_locallyFinite; instHasBesicovitchCovering, isBoundedBilinearMap_apply, the ENNReal division lemmas and HasCompactSupport.exists_bound_of_continuous.
- Accepted DAG declarations reused with identical frozen types: Submission.lpf_wtc_blowup_setIntegral_image (child 1; its proof was inspected on its branch). Optionally Submission.fiw_ims_tt_unit_bound (unit bound, child 3 and the parent).
- No ind_ab_* names exist in the DAG, the snapshot, SimonGMT or the local branches.

Scratch kernel checks:
- All 4 child statements pass validate_lean_statement and elaborate in the contract_scope replay.
- The parent assembly and complete proofs of all 4 children check with only propext, Classical.choice and Quot.sound. So do the comparator-style `exact Submission.X` replays of all 4 children and of the parent ind_ae_blowup_limit.
