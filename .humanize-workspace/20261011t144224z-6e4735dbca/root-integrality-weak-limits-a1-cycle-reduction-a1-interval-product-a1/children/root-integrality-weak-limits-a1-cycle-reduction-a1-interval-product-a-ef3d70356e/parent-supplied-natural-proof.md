# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.measure_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 of the parent proof (the product formula (PF) and its extension to integrable and a.e.-Borel integrands), recast as an identity of measures; the extensions then follow by general measure theory (MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff, MeasurableEmbedding.aestronglyMeasurable_map_iff) and are carried out in the sibling children. In the parent, the lintegral hypothesis is part (b) of the sibling DAG node iwl_cr_hausdorff_product_formula.

Notation. Hᵏ := μHE[k]; S := π⁻¹(A) = {y : π(y) ∈ A}; ν := Hᵐ⌞A; Φ′ : ℝ × ℝ^P → ℝ^{P+1}, Φ′(p) := Φ(p.1, p.2); L¹ := volume on ℝ.

1. (ν is σ-finite.) Let K ⊆ ℝ^P be compact. K is closed, hence Borel, so ν(K) = Hᵐ(K ∩ A) = Hᵐ(A ∩ K) < ∞ (Measure.restrict_apply). Thus ν is finite on compact sets; since ℝ^P = ⋃_n B̄(0, n) is σ-compact, ν is σ-finite (instance SigmaFinite.of_isFiniteMeasureOnCompacts), in particular s-finite, so Measure.prod_apply applies to L¹ ⊗ ν.
2. (Φ′ is Borel.) EuclideanSpace.equiv and its inverse are continuous linear equivalences and p ↦ Fin.cons p.1 (equiv p.2) is continuous (Continuous.finCons, continuous_fst, continuous_snd). Hence Φ′ is continuous, so Borel measurable, and Φ′⁻¹(B) is Borel for every Borel B ⊆ ℝ^{P+1}.
3. (Left side.) Let B ⊆ ℝ^{P+1} be Borel. Then (H^{m+1}⌞S)(B) = ∫⁻ 1_B d(H^{m+1}⌞S) = ∫⁻_S 1_B dH^{m+1} (lintegral_indicator_one).
4. (Hypothesis.) 1_B is Borel and [0,∞]-valued, so by the hypothesis ∫⁻_S 1_B dH^{m+1} = ∫⁻_ℝ ∫⁻_A 1_B(Φ(s, x)) dHᵐ(x) ds.
5. (Sections.) Fix s ∈ ℝ and let C_s := (Prod.mk s)⁻¹(Φ′⁻¹(B)) = {x : Φ(s, x) ∈ B}, a Borel set (measurable_prodMk_left). Then 1_B(Φ(s, x)) = 1_{C_s}(x) for every x, so ∫⁻_A 1_B(Φ(s, x)) dHᵐ(x) = ∫⁻ 1_{C_s} dν = ν(C_s) (lintegral_indicator_one).
6. (Product measure.) By Measure.prod_apply (Φ′⁻¹(B) is Borel, ν is s-finite), ∫⁻_ℝ ν(C_s) ds = (L¹ ⊗ ν)(Φ′⁻¹(B)), and by Measure.map_apply (Φ′ measurable, B Borel) this equals (Φ′_*(L¹ ⊗ ν))(B).
7. (Conclusion.) Steps 3–6 give (H^{m+1}⌞S)(B) = (Φ′_*(L¹ ⊗ ν))(B) for every Borel B ⊆ ℝ^{P+1}. Two measures on ℝ^{P+1} that agree on all Borel sets are equal (Measure.ext). Hence H^{m+1}⌞π⁻¹(A) = Φ′_*(L¹ ⊗ Hᵐ⌞A). ∎

Formalization aid. The following tactic proof, placed after `theorem Submission.iwl_cr_ip_restrict_preimage_eq_map : (<the frozen Lean type of this child, verbatim>) := by`, was kernel-checked in the contract scope (namespace GMT.Ch06 with the contract's opens) after import GMT.Ch06.Submission at the frozen commit d8d46c9 with the pinned toolchain; #print axioms = [propext, Classical.choice, Quot.sound]. It uses no helper declarations.

  intro P m A hfin hPF
  have : IsFiniteMeasureOnCompacts ((μHE[m] : Measure (Eucl P)).restrict A) :=
    ⟨fun K hK => by
      rw [Measure.restrict_apply hK.measurableSet, inter_comm]
      exact hfin K hK⟩
  have hΦ : Measurable (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) := by
    refine ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm.continuous.comp ?_).measurable
    exact Continuous.finCons continuous_fst
      ((EuclideanSpace.equiv (Fin P) ℝ).continuous.comp continuous_snd)
  ext B hB
  rw [Measure.map_apply hΦ hB, Measure.prod_apply (hΦ hB), ← lintegral_indicator_one hB,
    hPF (B.indicator 1) (measurable_one.indicator hB)]
  refine lintegral_congr fun s => ?_
  rw [← lintegral_indicator_one (measurable_prodMk_left (hΦ hB))]
  rfl

## Key steps

1. ν := Hᵐ⌞A is finite on compacts, hence σ-finite (s-finite), so Measure.prod_apply is available.
2. Φ′(s, x) = Φ(s, x) is continuous, hence Borel measurable.
3. For Borel B: (H^{m+1}⌞π⁻¹A)(B) = ∫⁻_{π⁻¹A} 1_B dH^{m+1} = ∫⁻_ℝ ∫⁻_A 1_B(Φ(s,x)) dHᵐ ds by the hypothesis with g = 1_B.
4. The inner integral is ν((Prod.mk s)⁻¹ Φ′⁻¹B); Measure.prod_apply and Measure.map_apply turn the outer integral into (Φ′_*(L¹ ⊗ ν))(B).
5. Measures agreeing on Borel sets are equal (Measure.ext).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3 -I: dag.json lean_name/status of all root.integrality_weak_limits-a1* nodes and of all accepted nodes; lean_statement of iwl_cr_hausdorff_product_formula, iwl_cr_interval_product_im, iwl_cycle_reduction, br_loc_tauAction_current, ltg_tau_integrable, fiw_tl_blowup_setIntegral, fiw_tl_growth_bound, br_weightedTangent_congr, iwl_weighted_tangent_locality, fiw_im_mass_formula, lpf_pic_current_of_dominated_density, lpf_wtc_blowup_setIntegral_image, polyhedral_approx_rt_tau_integrableOn, isoperimetric_abs_covector_apply_le, lpf_simple_nvector_algebra`
- `grep -rl iwl_cr_ip .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca (no match); grep -rho 'iwl_cr_[a-z_]*' dag.json`
- `python3 -I: nodes/{root-boundary-rectifiability-a1-localization-a1-tau-current-a1, root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1, root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1}/accepted-candidate.json: contract lean_statement == dag.json lean_statement, audit.comparator_passed`
- `rg -n 'def curryLeft|curryLeftLI|theorem curryLeft_apply_apply|def compContinuousLinearMapCLM' mathlib/Mathlib/Analysis/Normed/Module/Alternating/ mathlib/Mathlib/Topology/Algebra/Module/Alternating/`
- `rg -n 'μHE|euclideanHausdorffMeasure_eq_volume|Isometry.euclideanHausdorffMeasure_image|Isometry.map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_smul' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n in mathlib/Mathlib (snapshot) for MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff, MeasurableEmbedding.aestronglyMeasurable_map_iff, restrict_map, prod_restrict, restrict_restrict, prod_apply, integral_prod, Integrable.comp_snd, Integrable.mul_prod, AEStronglyMeasurable.comp_snd, integral_comp_mul_add, integral_Ioc_eq_integral_Ioo, integral_of_le, tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, norm_integral_le_of_norm_le, finrank_span_eq_card, restrict_apply₀', ae_restrict_mem₀, lintegral_indicator_one, setIntegral_congr_fun, SigmaFinite.of_isFiniteMeasureOnCompacts, Continuous.finCons, Homeomorph.measurableEmbedding, aestronglyMeasurable_iUnion_iff, NullMeasurableSet.congr, IntegrableOn.mono_set, IntegrableOn.of_ae_sdiff_eq_zero, Integrable.bdd_mul, norm_iteratedFDeriv_zero`
- `grep -n '^theorem|^def|^structure|^abbrev' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean and simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,FormsDuality,Product}.lean`
- `python3 -I /tmp/ipdec/scripts/gen.py and /tmp/ipdec/scripts/build.py (lean_contract.validate_lean_statement on the 7 child types, the parent type and the sibling type; comparator challenge layout of gmt-compare.py child_modules)`
- `lake env lean /tmp/ipdec/Check.lean (7 comparator-layout challenge targets; parent assembly from child and sibling stubs; #print axioms)`
- `lake env lean /tmp/ipdec/Appendix2.lean (complete proofs of iwl_cr_ip_restrict_preimage_eq_map and iwl_cr_ip_slice_formula; contraction snippet; #print axioms)`
- `lake env lean /tmp/ipdec/Sanity3.lean (construction of the contraction map; product_tangent conclusion feeds product_triple orients)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ipdec/scripts/gen.py`
- `/tmp/ipdec/scripts/build.py`
- `/tmp/ipdec/Check.lean`
- `/tmp/ipdec/Appendix2.lean`
- `/tmp/ipdec/Sanity3.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

DAG and naming:
- The DAG contains no product current and no Hausdorff product formula except the sibling iwl_cr_hausdorff_product_formula (decomposing). It is used only by the parent, through hMP.
- Reusable accepted declarations, each with identical frozen types and comparator_passed: br_loc_tauAction_current (τ is a current), ltg_tau_integrable, and fiw_tl_blowup_setIntegral. lpf_wtc_blowup_setIntegral_image is an alpha-equivalent duplicate; fiw_tl_growth_bound and br_weightedTangent_congr are not needed.
- The names iwl_cr_ip_* are unreserved: no match in dag.json, in any decomposition file, or in the run directory.

SimonGMT:
- Chapter06/Product.lean has only point products (pointProduct, pointSliceTest), no interval product. No match for a Hausdorff product formula there or in Mathlib, where only hausdorffMeasure_pi_real exists.
- Chapter03/Rectifiable.lean supplies blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, countablyRectifiable_range and regular_euclideanHausdorffMeasure_restrict_submodule.

Mathlib supplies every tool cited in the child proofs:
- ContinuousAlternatingMap.curryLeft, curryLeftLI and curryLeft_apply_apply (Analysis/Normed/Module/Alternating/Curry.lean), and compContinuousLinearMapCLM;
- μHE lemmas: Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff and MeasurableEmbedding.aestronglyMeasurable_map_iff, Homeomorph.measurableEmbedding;
- Measure.restrict_map, Measure.prod_restrict, Measure.restrict_restrict, Measure.prod_apply, Measure.restrict_apply₀', ae_restrict_mem₀, SigmaFinite.of_isFiniteMeasureOnCompacts;
- integral_prod, Integrable.comp_snd, Integrable.mul_prod, AEStronglyMeasurable.comp_snd, aestronglyMeasurable_iUnion_iff;
- intervalIntegral.integral_comp_mul_add, intervalIntegral.integral_of_le, integral_Ioc_eq_integral_Ioo;
- tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, norm_integral_le_of_norm_le;
- finrank_span_eq_card, NullMeasurableSet.congr, IntegrableOn.mono_set, Continuous.finCons.

Lean checks:
- Comparator-layout elaboration of all 7 child types.
- The parent assembly.
- Complete proofs of measure_identity and slice_formula (axioms: propext, Classical.choice, Quot.sound).
- The ℒ construction and the product_tangent→product_triple interface.

Public citation for the product formula: Federer, Geometric Measure Theory (1969) 3.2.23. The product current and its integer multiplicity: Simon, Introduction to GMT, Ch. 6, 3.2(2).
