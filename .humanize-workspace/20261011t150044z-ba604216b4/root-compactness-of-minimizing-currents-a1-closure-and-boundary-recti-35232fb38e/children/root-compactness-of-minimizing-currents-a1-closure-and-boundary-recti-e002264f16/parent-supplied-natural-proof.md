# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.mass_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof, with (N3) supplied as the hypothesis |γ∘pL| ≤ |γ|; the integral is estimated in ℝ≥0∞ (lower Lebesgue integral), which needs neither integrability nor measurability of F. Notation: Φ_ω(x) := ξ(x)(ω(pL x)∘pL); for r ∈ ℝ, ‖r‖ₑ = ofReal|r|; 1_E is the indicator of E.
1. By definition M_U(Y) = sSup{ofReal(Y(ω)) : ω ∈ massAdmissibleOn U l U}. By sSup_le it suffices to fix ω ∈ 𝒟^l(U) with tsupport ω ⊆ U and |ω(y)| ≤ 1 for all y, and to show ofReal(Y(ω)) ≤ μ(F ∩ pL⁻¹(U)).
2. pL⁻¹(U) is open (U is open and pL is continuous), hence measurable.
3. (Pointwise bound.) The ξ-bound holds μ-a.e., hence μ⌞F-a.e. (ae_restrict_of_ae). For such x: if pL x ∈ U, then |Φ_ω(x)| ≤ |ω(pL x)∘pL| ≤ |ω(pL x)| ≤ 1 (ξ-bound, pull-back hypothesis, admissibility of ω), so ‖Φ_ω(x)‖ₑ = ofReal|Φ_ω(x)| ≤ 1 = 1_{pL⁻¹(U)}(x); if pL x ∉ U, then pL x ∉ tsupport ω (as tsupport ω ⊆ U for ω ∈ 𝒟^l(U)), so ω(pL x) = 0 (image_eq_zero_of_notMem_tsupport), ω(pL x)∘pL = 0 and Φ_ω(x) = ξ(x)(0) = 0, so ‖Φ_ω(x)‖ₑ = 0 ≤ 1_{pL⁻¹(U)}(x). Thus ‖Φ_ω‖ₑ ≤ 1_{pL⁻¹(U)} μ⌞F-a.e.
4. (Chain of inequalities.) ofReal(Y(ω)) = ofReal(∫_F Φ_ω dμ) ≤ ofReal|∫_F Φ_ω dμ| = ‖∫_F Φ_ω dμ‖ₑ ≤ ∫⁻_F ‖Φ_ω‖ₑ dμ (enorm_integral_le_lintegral_enorm, valid for every function because a non-integrable function has Bochner integral 0) ≤ ∫⁻_F 1_{pL⁻¹(U)} dμ (lintegral_mono_ae with step 3) = (μ⌞F)(pL⁻¹(U)) (lintegral_indicator_one, using step 2) = μ(pL⁻¹(U) ∩ F) (Measure.restrict_apply, using step 2) = μ(F ∩ pL⁻¹(U)).
5. Step 4 holds for every admissible ω, so M_U(Y) ≤ μ(F ∩ pL⁻¹(U)) by step 1. ∎

Formalization aid (not part of the mathematical argument). During decomposition, the following proof of exactly this frozen type was compiled in the contract scope (after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s; Lean v4.35.0-rc3, Mathlib 25730c7c), using only the sibling declarations named in it and the standard axioms [propext, Classical.choice, Quot.sound]. It passes the leaf rule (one appended theorem, no helper declarations) and may be used directly or adapted:
```lean
theorem Submission.cbr_ci_pw_proj_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l) (Y : GeometricCurrentOn U l), IsOpen U → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ) → Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) := by
  intro P m l pL U F μ ξ Y hU hξb hN3 hY
  have hUm : MeasurableSet (pL ⁻¹' U) := (hU.preimage pL.continuous).measurableSet
  apply sSup_le
  rintro r ⟨ω, ⟨-, hω1⟩, rfl⟩
  show ENNReal.ofReal (Y ω) ≤ _
  rw [hY ω]
  have hpt : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ≤ (pL ⁻¹' U).indicator 1 x := by
    filter_upwards [ae_restrict_of_ae hξb] with x hx
    by_cases hxU : pL x ∈ U
    · rw [indicator_of_mem (show x ∈ pL ⁻¹' U from hxU), Pi.one_apply, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((hx _).trans ((hN3 _).trans (hω1 _)))
    · have h0 : (ω : DifferentialForm (Euclid m) l) (pL x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxU (ω.property.2 h))
      have hβ0 : ((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL = 0 := by
        ext v
        simp [h0]
      rw [hβ0, map_zero, enorm_zero]
      exact zero_le
  calc ENNReal.ofReal (∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ)
      ≤ ‖∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in F, ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in F, (pL ⁻¹' U).indicator 1 x ∂μ := lintegral_mono_ae hpt
    _ = μ (F ∩ pL ⁻¹' U) := by
        rw [lintegral_indicator_one hUm, Measure.restrict_apply hUm, inter_comm]
```

## Key steps

1. Reduce M_U(Y) ≤ μ(F ∩ pL⁻¹U) to ofReal(Y ω) ≤ μ(F ∩ pL⁻¹U) for each admissible ω (sSup_le).
2. For μ⌞F-a.e. x: |Φ_ω(x)| ≤ |ω(pL x)∘pL| ≤ |ω(pL x)| ≤ 1, and Φ_ω(x) = 0 when pL x ∉ U ⊇ tsupport ω.
3. ofReal(Y ω) ≤ ‖∫_F Φ_ω‖ₑ ≤ ∫⁻_F ‖Φ_ω‖ₑ ≤ ∫⁻_F 1_{pL⁻¹U} = μ(F ∩ pL⁻¹U).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `sed of SimonGMT Chapter06 Forms.lean, Currents.lean, Mass.lean, FormSupNorm.lean in lake-packages-25730c7c/simongmt (DifferentialForm, exteriorDerivative = extDeriv, TestFormOn, TestFormOnConverges, GeometricCurrentOn, boundary_apply, exteriorDerivativeTestOn, covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn)`
- `rg -n in local-references/123e8435b4a2469b/mathlib/Mathlib: extDeriv_pullback (Analysis/Calculus/DifferentialForm/Basic.lean:259), Filter.EventuallyEq.extDeriv_eq (:188), exists_contDiff_support_eq_eq_one_iff (Geometry/Manifold/PartitionOfUnity.lean:789), IsCompact.exists_cthickening_subset_open (Topology/MetricSpace/Thickening.lean:426), IsCompact.cthickening (:283), closure_thickening_subset_cthickening (:293), compContinuousLinearMapCLM (Topology/Algebra/Module/Alternating/Topology.lean:281), ContinuousAlternatingMap.le_opNorm (Analysis/Normed/Module/Alternating/Basic.lean:212), isBoundedBilinearMap_apply (Analysis/Normed/Operator/BoundedLinearMaps.lean:391), Continuous.comp_aestronglyMeasurable (MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:233), norm_iteratedFDeriv_zero (Analysis/Calculus/ContDiff/FTaylorSeries.lean:823), iteratedFDeriv_zero (Analysis/Calculus/ContDiff/Basic.lean:75), enorm_integral_le_lintegral_enorm and norm_integral_le_of_norm_le (MeasureTheory/Integral/Bochner/Basic.lean:333, 985), setIntegral_congr_fun and integral_indicator (MeasureTheory/Integral/Bochner/Set.lean:73, 185), lintegral_indicator_one (MeasureTheory/Integral/Lebesgue/Basic.lean:572), tsupport_smul_subset_left and HasCompactSupport.smul_right (Topology/Algebra/Support.lean:168, 466)`
- `rg -n 'add_compContinuousLinearMap|zero_compContinuousLinearMap|theorem extDeriv_zero' in the Mathlib snapshot: no match (the proofs use ext/congr instead)`
- `rg -n 'compContinuousLinearMap|extDeriv_pullback|exists_contDiff_support_eq_eq_one_iff|massAdmissibleOn' in local-references/123e8435b4a2469b/project/GMT: no match (no project lemma to reuse)`
- `python3 -I scans of dag.json: no lean_name with prefix cbr_ci_pw_proj_ except the selected parent cbr_ci_pw_projected_current; existing cutoff/pull-back declarations (dgcr_bwd_normal_cutoff, rsd_mw_tfa_smooth_cutoff, cbr_rlim_smooth_cutoff, dor_lmb_fc_dtop_cutoff_pullback, ...) have different frozen types, so none is reusable; selected node depth 5, depends_on covector_bounds-a1 (cbr_ci_pw_orthonormal_covector_bounds)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _solve_children, _existing_lean_name_problem, _overlay_accepted_children), leaf_verification.py check_source_delta, prompts.py DECOMPOSITION_AUDIT; verifier/gmt-compare.py contract_scope and child_modules; verifier/lean_contract.py validate_lean_statement; swarm-project.json (max_depth 6, max_children 12, max_nodes 5000)`
- `lake env lean /tmp/proj-decomp-b5/Children.lean, A.lean, B.lean, C1.lean, C2.lean, D.lean, E.lean, All.lean (#print axioms) and /tmp/proj-decomp-b5/cmp/NodeChallenges.lean (comparator-replayed scope); extracted check_source_delta run on each child proof`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-35232fb38e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-35232fb38e/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/tmp/proj-decomp-b5/All.lean`
- `/tmp/proj-decomp-b5/cmp/NodeChallenges.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Every Mathlib lemma the child proofs use exists in the snapshot at the paths and lines listed. Mathlib has no lemma for add or zero of compContinuousLinearMap or for extDeriv of the zero form; the proofs handle these with ext/congr. The project snapshot has no lemma to reuse. Apart from the parent, no DAG declaration has the prefix cbr_ci_pw_proj_, so the six names are fresh. No accepted cutoff or pull-back declaration has an identical frozen type, so none is reused. The runtime caps depth at 6, so these depth-6 children are leaves (one appended theorem each). All six child types elaborate in the comparator's replayed contract scope and pass validate_lean_statement. Complete Lean proofs of all six compile with only [propext, Classical.choice, Quot.sound] and pass check_source_delta. The parent assembly compiles against them and the covector_bounds type; its only sorryAx comes from that placeholder.
