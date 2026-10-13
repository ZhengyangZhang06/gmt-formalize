# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.nvector_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 8 of the parent proof of iwl_cr_ci_integral_exchange. That step identifies ∫ φ(s)(x) ds with ψ(x) through evaluation functionals, then moves the continuous linear functional ξ(x) inside the s-integral. Here it is stated for a general interval and a general continuous family of covectors, with details filled in.

Notation: Λ^m := Covector (Eucl P) m = (ℝ^P)[⋀^Fin m]→L[ℝ] ℝ with the operator norm. NVector (Eucl P) m = Λ^m →L[ℝ] ℝ. All integrals ∫_a^b are interval integrals for Lebesgue measure.

1. (The Bochner integral exists.) Λ^m is a complete normed space (ContinuousAlternatingMap.instCompleteSpace, since ℝ is complete). f is continuous, so it is interval integrable on [a, b] (Continuous.intervalIntegrable). Hence I := ∫_a^b f(s) ds ∈ Λ^m is the genuine Bochner interval integral.
2. (Evaluation functionals.) Fix v : Fin m → ℝ^P and define L_v : Λ^m → ℝ by L_v(α) := α(v). L_v is continuous linear: it is ContinuousMultilinearMap.apply ℝ (fun _ => ℝ^P) ℝ v composed with the continuous linear map ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ. The identity L_v(α) = α(v) holds definitionally.
3. (Continuous linear maps commute with interval integrals.) Let L : G →L[ℝ] H with G, H complete normed spaces, and let g be interval integrable. Then ∫_a^b L(g(s)) ds = L(∫_a^b g(s) ds) (ContinuousLinearMap.intervalIntegral_comp_comm).
4. (I = c.) For each v, step 3 with L = L_v and g = f gives I(v) = L_v(I) = ∫_a^b L_v(f(s)) ds = ∫_a^b f(s)(v) ds. By hypothesis the last integral is c(v). Two continuous alternating maps that agree at every v are equal (ContinuousAlternatingMap.ext), so I = c.
5. (Conclusion.) w is a continuous linear functional on the complete space Λ^m. Step 3 with L = w and g = f, then step 4, gives ∫_a^b w(f(s)) ds = w(∫_a^b f(s) ds) = w(I) = w(c). ∎

Lean note (non-normative; kernel-checked in scratch at this pin, in the comparator scope, as `theorem Submission.iwl_cr_ci_ie_nvector_intervalIntegral : <frozen type> := by …`; axioms propext, Classical.choice, Quot.sound):
```
  intro P m a b f c w hf hc
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  have hI : (∫ s in a..b, f s) = c := by
    ext v
    rw [hc v]
    let L : Covector (Eucl P) m →L[ℝ] ℝ :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Eucl P) ℝ v).comp
        (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
    have hL : ∀ α : Covector (Eucl P) m, L α = α v := fun α => rfl
    have h := L.intervalIntegral_comp_comm hfi
    simp only [hL] at h
    exact h.symm
  rw [w.intervalIntegral_comp_comm hfi, hI]
```

## Key steps

1. f is continuous, hence interval integrable, and Covector (Eucl P) m is complete, so I := ∫_a^b f(s) ds exists.
2. Evaluation at v is a continuous linear functional and commutes with the interval integral: I(v) = ∫_a^b f(s)(v) ds = c(v) for all v, so I = c (ContinuousAlternatingMap.ext).
3. w commutes with the interval integral: ∫_a^b w(f(s)) ds = w(I) = w(c) (ContinuousLinearMap.intervalIntegral_comp_comm).

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
