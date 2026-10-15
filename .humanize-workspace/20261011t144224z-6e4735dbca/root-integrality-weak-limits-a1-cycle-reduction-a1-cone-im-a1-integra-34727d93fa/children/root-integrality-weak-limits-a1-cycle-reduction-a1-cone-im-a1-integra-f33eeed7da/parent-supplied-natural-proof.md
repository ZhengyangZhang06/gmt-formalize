# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_im-a1.integral_exchange-a1.param_fubini-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 5, 6 and 8 of the parent proof of iwl_cr_ci_integral_exchange (integrability on the product, Fubini, the inner s-integral), together with the domination estimate of its step 4. Two things are abstracted:
- the localized finite measure μ_K becomes an arbitrary s-finite measure μ;
- the slice family φ becomes an arbitrary jointly continuous family Φ that is uniformly bounded by B on [0, 1] × ℝ^P.
Details are filled in. The proof uses the sibling nvector_integral (Submission.iwl_cr_ci_ie_nvector_intervalIntegral).

Notation:
- E := ℝ^P and Λ^m := Covector E m with the operator norm;
- ν := volume.restrict (Ioc 0 1), Lebesgue measure on (0, 1];
- F(s, x) := θ(x) · ξ(x)(Φ(s)(x)) for (s, x) ∈ ℝ × E, viewed as the uncurried function of the curried F s x;
- ∫_0^1 denotes the interval integral for Lebesgue measure.

1. (The factor measures.) ν(ℝ) = vol(Ioc 0 1) = 1 < ∞, so ν is finite and hence s-finite. μ is s-finite by hypothesis. So the product measure ν.prod μ on ℝ × E is available, together with the Fubini lemmas for s-finite factors.
2. (F is AEStronglyMeasurable for ν.prod μ.)
   (a) θ is μ-integrable, hence μ-AEStronglyMeasurable. So (s, x) ↦ θ(x) is ν.prod μ-AEStronglyMeasurable (AEStronglyMeasurable.comp_snd, using SFinite μ).
   (b) In the same way, (s, x) ↦ ξ(x) is ν.prod μ-AEStronglyMeasurable.
   (c) (s, x) ↦ Φ(s)(x) is continuous on ℝ × E. That space is second countable with its Borel σ-algebra, and Λ^m is a metric space, so the map is AEStronglyMeasurable (Continuous.aestronglyMeasurable).
   (d) The evaluation (w, α) ↦ w(α) on NVector E m × Λ^m is continuous (continuous_fst.clm_apply continuous_snd). Hence (s, x) ↦ ξ(x)(Φ(s)(x)) is AEStronglyMeasurable (Continuous.comp_aestronglyMeasurable₂ applied to (b) and (c)).
   (e) F is the product of (a) and (d), so it is AEStronglyMeasurable (AEStronglyMeasurable.mul).
3. (Integrable majorant.) Let G(s, x) := B · |θ(x)|.
   - The constant B is ν-integrable (integrable_const, since ν is finite).
   - |θ| = ‖θ‖ is μ-integrable (Integrable.norm).
   So G is ν.prod μ-integrable (Integrable.mul_prod, using SFinite μ).
4. (Domination a.e.)
   - ν-a.e. s lies in Ioc 0 1 (ae_restrict_mem; Ioc 0 1 is measurable).
   - By hypothesis, μ-a.e. x satisfies |ξ(x)(α)| ≤ ‖α‖ for every α ∈ Λ^m.
   Prod.fst : (ℝ × E, ν.prod μ) → (ℝ, ν) and Prod.snd : (ℝ × E, ν.prod μ) → (E, μ) are quasi-measure-preserving (Measure.quasiMeasurePreserving_fst / _snd). So both properties hold for ν.prod μ-a.e. (s, x) (QuasiMeasurePreserving.ae). Fix such an (s, x). Then s ∈ Ioc 0 1 ⊆ Icc 0 1, so ‖Φ(s)(x)‖ ≤ B by the bound hypothesis. Hence ‖F(s, x)‖ = |θ(x)| · |ξ(x)(Φ(s)(x))| ≤ |θ(x)| · ‖Φ(s)(x)‖ ≤ |θ(x)| · B = G(s, x), multiplying by |θ(x)| ≥ 0. No sign or size condition on B or θ is needed.
5. (Integrability.) Steps 2, 3 and 4 with Integrable.mono' show that F is ν.prod μ-integrable.
6. (Fubini.) By MeasureTheory.integral_integral_swap (both factors s-finite): ∫ (∫ F(s, x) dμ(x)) dν(s) = ∫ (∫ F(s, x) dν(s)) dμ(x).
7. (Left side.) Since 0 ≤ 1, ∫_0^1 g(s) ds = ∫_{Ioc 0 1} g(s) ds = ∫ g dν for every g : ℝ → ℝ (intervalIntegral.integral_of_le). With g(s) := ∫ θ(x) ξ(x)(Φ(s)(x)) dμ(x), the left side of the claim is therefore the left side of step 6.
8. (Inner s-integral.) Fix x ∈ E. By integral_of_le again, ∫ F(s, x) dν(s) = ∫_0^1 θ(x) · ξ(x)(Φ(s)(x)) ds. Pulling out the constant gives θ(x) · ∫_0^1 ξ(x)(Φ(s)(x)) ds (intervalIntegral.integral_const_mul). The map s ↦ Φ(s)(x) is continuous: it is the jointly continuous map composed with s ↦ (s, x) (Continuous.prodMk continuous_id continuous_const). By hypothesis Ψ(x)(v) = ∫_0^1 Φ(s)(x)(v) ds for every v. Apply the sibling nvector_integral with a = 0, b = 1, f = (s ↦ Φ(s)(x)), c = Ψ(x) and w = ξ(x). This gives ∫_0^1 ξ(x)(Φ(s)(x)) ds = ξ(x)(Ψ(x)), hence ∫ F(s, x) dν(s) = θ(x) · ξ(x)(Ψ(x)).
9. (Conclusion.) Combining steps 7, 6 and 8: ∫_0^1 ∫ θ(x) ξ(x)(Φ(s)(x)) dμ(x) ds = ∫ (∫ F(s, x) dν(s)) dμ(x) = ∫ θ(x) ξ(x)(Ψ(x)) dμ(x). ∎

Lean note (non-normative; kernel-checked in scratch at this pin, in the comparator scope, as `theorem Submission.iwl_cr_ci_ie_param_fubini : <frozen type> := by …`, after the sibling; axioms propext, Classical.choice, Quot.sound):
```
  intro P m μ θ ξ Φ Ψ B hμ hθ hξ hbd hΦ hB hΨ
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have _instν : IsFiniteMeasure ν := ⟨by simp [hν]⟩
  set F : ℝ → Eucl P → ℝ := fun s x => θ x * ξ x (Φ s x) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (ν.prod μ) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × Eucl P => θ p.2) (ν.prod μ) :=
      hθ.aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × Eucl P => ξ p.2) (ν.prod μ) := hξ.comp_snd
    have h3 : AEStronglyMeasurable (fun p : ℝ × Eucl P => Φ p.1 p.2) (ν.prod μ) :=
      hΦ.aestronglyMeasurable
    have h4 : AEStronglyMeasurable (fun p : ℝ × Eucl P => ξ p.2 (Φ p.1 p.2)) (ν.prod μ) :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ h2 h3
    exact h1.mul h4
  have hG : Integrable (fun p : ℝ × Eucl P => B * ‖θ p.2‖) (ν.prod μ) :=
    (integrable_const B).mul_prod hθ.norm
  have hbound : ∀ᵐ p ∂(ν.prod μ), ‖Function.uncurry F p‖ ≤ B * ‖θ p.2‖ := by
    have hs : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ Ioc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    have hx : ∀ᵐ p ∂(ν.prod μ), ∀ α : Covector (Eucl P) m, |ξ p.2 α| ≤ ‖α‖ :=
      Measure.quasiMeasurePreserving_snd.ae hbd
    filter_upwards [hs, hx] with p hp1 hp2
    simp only [Function.uncurry, hF, norm_mul, Real.norm_eq_abs]
    calc |θ p.2| * |ξ p.2 (Φ p.1 p.2)| ≤ |θ p.2| * B := by
          gcongr
          exact (hp2 _).trans (hB p.1 (Ioc_subset_Icc_self hp1) p.2)
      _ = B * |θ p.2| := mul_comm _ _
  have hint : Integrable (Function.uncurry F) (ν.prod μ) := hG.mono' hmeas hbound
  have hswap := integral_integral_swap hint
  rw [intervalIntegral.integral_of_le zero_le_one]
  change ∫ s, ∫ x, F s x ∂μ ∂ν = _
  rw [hswap]
  congr 1
  funext x
  change ∫ s in Ioc (0 : ℝ) 1, θ x * ξ x (Φ s x) = _
  rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul]
  congr 1
  exact Submission.iwl_cr_ci_ie_nvector_intervalIntegral P m 0 1 (fun s => Φ s x) (Ψ x) (ξ x)
    (hΦ.comp (Continuous.prodMk continuous_id continuous_const)) (hΨ x)
```

## Key steps

1. Put ν := Lebesgue⌞(0, 1] (finite) and F(s, x) := θ(x) ξ(x)(Φ(s)(x)). F is AEStronglyMeasurable on ν ⊗ μ (comp_snd for θ and ξ, continuity of Φ, continuous evaluation).
2. ν ⊗ μ-a.e., s ∈ (0, 1] and |ξ(x)(α)| ≤ ‖α‖, so |F(s, x)| ≤ B |θ(x)|. B|θ| is ν ⊗ μ-integrable (Integrable.mul_prod), so F is integrable (Integrable.mono').
3. Fubini (integral_integral_swap) exchanges ∫ dν and ∫ dμ; ∫_0^1 = ∫ dν by intervalIntegral.integral_of_le.
4. The inner integral is θ(x) ∫_0^1 ξ(x)(Φ(s)(x)) ds = θ(x) ξ(x)(Ψ(x)) by nvector_integral.

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
