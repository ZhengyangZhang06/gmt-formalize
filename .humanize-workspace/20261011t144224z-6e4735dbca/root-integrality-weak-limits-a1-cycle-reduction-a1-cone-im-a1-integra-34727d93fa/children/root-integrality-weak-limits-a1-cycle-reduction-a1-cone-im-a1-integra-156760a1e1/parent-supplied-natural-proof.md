# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.finite_measure-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1–2 of the parent proof of iwl_cr_ci_integral_exchange. Those steps show θ ≥ 1 on M and then μ(M ∩ K) ≤ ∫_{M∩K} |θ| dHᵐ < ∞. Here they are stated for an arbitrary domain U and an arbitrary compact K ⊆ U, with details filled in.

Notation: E := ℝ^P = Eucl P and μ := μHE[n], the Hausdorff measure Hⁿ on E. For real r, ‖r‖ₑ = ENNReal.ofReal |r| (Real.enorm_eq_ofReal_abs). The hypotheses are IsRectifiableTriple U n M θ ξ (frozen contract), the integer property ∀ x ∈ M, ∃ k : ℕ, θ x = k, IsCompact K and K ⊆ U. The proof uses only three fields of IsRectifiableTriple:
- nullMeasurableSet: M is μ-null-measurable;
- pos: θ(x) > 0 for x ∈ M;
- integrableOn: θ is μ-integrable on M ∩ K' for every compact K' ⊆ U.

1. (θ ≥ 1 on M.) Let x ∈ M. By hypothesis θ(x) = k for some k ∈ ℕ, and by `pos`, 0 < θ(x) = k. If k = 0 then θ(x) = 0, which is impossible. So k ≥ 1 (Nat.one_le_iff_ne_zero) and θ(x) = k ≥ 1 (cast to ℝ).
2. (Integrability.) K is compact and K ⊆ U, so `integrableOn` gives IntegrableOn θ (M ∩ K) μ, i.e. θ is integrable for μ.restrict (M ∩ K). In particular its integral is finite (Integrable.hasFiniteIntegral): ∫⁻ ‖θ‖ₑ d(μ.restrict (M ∩ K)) < ∞.
3. (Null-measurability.) M is μ-null-measurable. K is compact in the Hausdorff space E, hence closed, hence Borel measurable. So M ∩ K is μ-null-measurable (NullMeasurableSet.inter), and μ.restrict (M ∩ K)-a.e. x lies in M ∩ K (ae_restrict_mem₀).
4. (A.e. lower bound.) For μ.restrict (M ∩ K)-a.e. x we have x ∈ M by step 3, so θ(x) ≥ 1 by step 1. Then |θ(x)| = θ(x) ≥ 1, so ‖θ(x)‖ₑ = ENNReal.ofReal |θ(x)| ≥ 1 (ENNReal.one_le_ofReal).
5. (Conclusion.) The lower integral of the constant 1 for μ.restrict (M ∩ K) equals μ(M ∩ K). Therefore μ(M ∩ K) = ∫⁻_{M∩K} 1 dμ ≤ ∫⁻_{M∩K} ‖θ‖ₑ dμ < ∞. The inequality is lintegral_mono_ae with step 4, and the strict bound is step 2. ∎

Lean note (non-normative; kernel-checked in scratch at this pin, in the comparator scope after `import GMT.Ch06.Submission`, as `theorem Submission.iwl_cr_ci_ie_measure_inter_compact_lt_top : <frozen type> := by …`; axioms propext, Classical.choice, Quot.sound):
```
  intro P n U M θ ξ K hT hint hK hKU
  have h1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hint x hx
    have hpos := hT.pos x hx
    rw [hk] at hpos ⊢
    have hk0 : k ≠ 0 := by rintro rfl; simp at hpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hθ : IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) := hT.integrableOn K hK hKU
  have hnm : NullMeasurableSet (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    hT.nullMeasurableSet.inter hK.isClosed.measurableSet.nullMeasurableSet
  have hae : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict (M ∩ K)), (1 : ℝ≥0∞) ≤ ‖θ x‖ₑ := by
    filter_upwards [ae_restrict_mem₀ hnm] with x hx
    have h := h1 x hx.1
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by linarith)]
    exact ENNReal.one_le_ofReal.mpr h
  calc (μHE[n] : Measure (Eucl P)) (M ∩ K)
        = ∫⁻ _ in M ∩ K, (1 : ℝ≥0∞) ∂(μHE[n] : Measure (Eucl P)) := by simp
    _ ≤ ∫⁻ x in M ∩ K, ‖θ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hae
    _ < ∞ := hθ.hasFiniteIntegral
```

## Key steps

1. θ(x) = k ∈ ℕ and θ(x) > 0 force k ≥ 1, so θ ≥ 1 on M.
2. θ is Hⁿ-integrable on M ∩ K (field integrableOn, K compact ⊆ U), and M ∩ K is Hⁿ-null-measurable, so Hⁿ⌞(M ∩ K)-a.e. x lies in M and has ‖θ(x)‖ₑ ≥ 1.
3. Hⁿ(M ∩ K) = ∫⁻_{M∩K} 1 ≤ ∫⁻_{M∩K} ‖θ‖ₑ < ∞ (lintegral_mono_ae, HasFiniteIntegral).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `rg -ln 'tauAction|IsRectifiableTriple' local-references/197bdd4b88278494/project (only GMT/Ch06/Contract.lean, Submission.lean, README.md)`
- `rg -n 'integral_integral_swap|intervalIntegral_comp_comm|integral_comp_comm' lake-packages-25730c7c/simongmt/Poincare/SimonGMT (one match: Chapter05/CurveAreaRemainder.lean:238, innerSL ℝ c).intervalIntegral_comp_comm)`
- `grep -n '^theorem|^def|^abbrev|^structure' SimonGMT Chapter06/{Forms,Currents,FormsDuality,Mass}.lean`
- `python3 -I: dag.json nodes of the cone_im branch (statuses, children, depends_on); lean_statement search for 'simpleNVector', '∩ K) < ∞', '1 ≤ θ x', 'IsFiniteMeasure', '∫ s in (0 : ℝ)..1'`
- `python3 -I: statements and status of fiw_ims_tt_unit_bound, iwl_sp_sn_signed_simpleNVector_bound_ne_zero, fiw_ims_tt_term_bound, ltg_tau_integrable, br_loc_tauAction_current, polyhedral_approx_open_truncation, lpf_pi_covector_finiteDimensional, isoperimetric_mass_lt_top`
- `python3 -I: read nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/{decomposition-v1.json,decomposition-audit-v1.json}, nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json, nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json, nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json (reuse format)`
- `python3 -I: nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/{parent-supplied-natural-proof.json,accepted-candidate.json}; git show 27af9b191b732eae73e3d693d8903e52f89962ce:GMT/Ch06/Submission.lean`
- `python3 -I: exact-type and name collision scan of dag.json and nodes/*/decomposition-v*.json for the 4 proposed lean_names; grep -rl iwl_cr_ci_ie_ over the run directory (no match)`
- `rg -n -F over local-references/197bdd4b88278494/mathlib/Mathlib: 'theorem integral_integral_swap ', 'theorem Integrable.mul_prod', 'theorem quasiMeasurePreserving_fst', 'theorem quasiMeasurePreserving_snd', 'theorem _root_.ContinuousLinearMap.intervalIntegral_comp_comm', 'def toContinuousMultilinearMapCLM', 'theorem setIntegral_indicator ', 'theorem enorm_eq_ofReal_abs', 'lemma one_le_ofReal', 'theorem ae_restrict_mem₀', 'theorem ae_restrict_of_ae_restrict_of_subset', 'theorem integral_of_le', 'theorem integral_const_mul', 'theorem Continuous.clm_apply', 'theorem lintegral_mono_ae', 'AEStronglyMeasurable.comp_snd', 'comp_aestronglyMeasurable₂', 'theorem ae ('`
- `lake env lean /tmp/ie_decomp/probe/Names.lean (#check of cited API; SecondCountableTopology/FiniteDimensional for Covector are not inferred, CompleteSpace is) and /tmp/ie_decomp/probe/Where.lean (module of each cited declaration; #synth CompleteSpace (Covector …) = ContinuousAlternatingMap.instCompleteSpace)`
- `python3 -I /tmp/ie_decomp/scripts/gen.py (verifier gmt-compare.py child_modules, mode contract, + lean_contract.validate_lean_statement) -> /tmp/ie_decomp/gen/*__NodeChallenge.lean; lake env lean on each`
- `lake env lean /tmp/ie_decomp/probe/Assembly.lean (frozen parent type from the four child types as hypotheses; #print axioms)`
- `lake env lean /tmp/ie_decomp/probe/ChildProofs.lean, /tmp/ie_decomp/probe/EndToEnd.lean and /tmp/ie_decomp/probe/EndToEnd2.lean (children proved, parent assembled, NodeSolution-style exact checks, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-integra-34727d93fa/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/CurveAreaRemainder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ie_decomp/scripts/gen.py`
- `/tmp/ie_decomp/gen/iwl_cr_ci_ie_measure_inter_compact_lt_top__NodeChallenge.lean`
- `/tmp/ie_decomp/gen/fiw_ims_tt_unit_bound__NodeChallenge.lean`
- `/tmp/ie_decomp/gen/iwl_cr_ci_ie_nvector_intervalIntegral__NodeChallenge.lean`
- `/tmp/ie_decomp/gen/iwl_cr_ci_ie_param_fubini__NodeChallenge.lean`
- `/tmp/ie_decomp/probe/Names.lean`
- `/tmp/ie_decomp/probe/Where.lean`
- `/tmp/ie_decomp/probe/Assembly.lean`
- `/tmp/ie_decomp/probe/ChildProofs.lean`
- `/tmp/ie_decomp/probe/EndToEnd.lean`
- `/tmp/ie_decomp/probe/EndToEnd2.lean`

Snapshot: project d8d46c95 and Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…).

Project and SimonGMT:
- tauAction and IsRectifiableTriple occur only in Contract.lean, Submission.lean and README.md.
- SimonGMT has no Fubini or integral-exchange result for currents or τ-integrands. Its only CLM/interval-integral commutation is (innerSL ℝ c).intervalIntegral_comp_comm in Chapter05/CurveAreaRemainder.lean:238, the pattern used by nvector_integral.

DAG:
- fiw_ims_tt_unit_bound (root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1) is accepted, comparator_passed, candidate 27af9b19, and has exactly the needed type. It is reused, as in earlier decompositions.
- No DAG or decomposition entry has the type of the three new children. The prefix iwl_cr_ci_ie_ is unused in the run directory.
- ltg_tau_integrable and fiw_ims_tt_term_bound give single-form integrability, not the product-measure or Fubini statement.

Mathlib, all present at this pin:
- integral_integral_swap and Integrable.mul_prod (Integral/Prod.lean:478, :297); AEStronglyMeasurable.comp_snd (Integral/Prod.lean:135);
- quasiMeasurePreserving_fst/_snd (Measure/Prod.lean:463, :470); QuasiMeasurePreserving.ae (QuasiMeasurePreserving.lean:108);
- ContinuousLinearMap.intervalIntegral_comp_comm (IntervalIntegral/Basic.lean:870); integral_of_le (:677); integral_const_mul (:817);
- toContinuousMultilinearMapCLM (Alternating/Topology.lean:175); ContinuousAlternatingMap.instCompleteSpace (found by #synth);
- setIntegral_indicator (Bochner/Set.lean:194); ae_restrict_mem₀ and ae_restrict_of_ae_restrict_of_subset (Restrict.lean:637, :654);
- Real.enorm_eq_ofReal_abs (Normed/Group/Real.lean:110); ENNReal.one_le_ofReal (Basic/ENNReal/Real.lean:216);
- Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:263); Continuous.clm_apply (BoundedLinearMaps.lean:471); lintegral_mono_ae (Lebesgue/Basic.lean:217);
- IsCompact.exists_bound_of_continuousOn (module Mathlib.Analysis.Normed.Group.Bounded); image_eq_zero_of_notMem_tsupport (module Mathlib.Topology.Algebra.Support).
SecondCountableTopology and FiniteDimensional instances for Covector are not inferred. The proofs avoid them: measurability comes from continuity on the second-countable domain and Continuous.comp_aestronglyMeasurable₂.

Lean checks:
- All 4 child statements elaborate in the comparator's exact challenge form.
- The frozen parent type follows from the four child types as hypotheses, with standard axioms only.
- All three new children are fully proved by the Lean notes embedded in their natural proofs. With the accepted unit_bound, the parent is assembled end-to-end with no sorry and only propext, Classical.choice and Quot.sound.
