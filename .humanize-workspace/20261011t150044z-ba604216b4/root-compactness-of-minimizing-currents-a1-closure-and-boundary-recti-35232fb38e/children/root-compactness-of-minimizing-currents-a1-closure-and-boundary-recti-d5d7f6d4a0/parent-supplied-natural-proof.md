# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.integral_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–3 of the parent proof (integrability, linearity, continuity), with the integrability and the estimate taken from the sibling integral_estimate. Notation: for ω ∈ 𝒟^l(U), Φ_ω(x) := ξ(x)(ω(pL x)∘pL) and T(ω) := ∫_F Φ_ω dμ.
1. (Integrability.) Let ω ∈ 𝒟^l(U). Then ω is C^∞, hence continuous; tsupport ω is compact and tsupport ω ⊆ U, so S ∩ pL⁻¹(tsupport ω) is compact by hypothesis; ω vanishes outside tsupport ω (image_eq_zero_of_notMem_tsupport); and, being continuous with compact support, ω is bounded: ‖ω(y)‖ ≤ M for some M and all y (Continuous.bounded_above_of_compact_support). The sibling integral_estimate with K := tsupport ω (its remaining hypotheses — F measurable, F ⊆ S, μ finite on compact sets, ξ a.e. strongly measurable, the ξ-bound, the pull-back bound — are hypotheses here) shows that Φ_ω is μ⌞F-integrable.
2. (Additivity.) Let ω, η ∈ 𝒟^l(U) and x ∈ ℝ^P. Then (ω + η)(pL x) = ω(pL x) + η(pL x), the map α ↦ α∘pL is linear (it is the continuous linear map compContinuousLinearMapCLM pL), and ξ(x) is linear, so Φ_{ω+η}(x) = Φ_ω(x) + Φ_η(x). By step 1 both summands are μ⌞F-integrable, so T(ω + η) = T(ω) + T(η) (integral_add).
3. (Homogeneity.) For c ∈ ℝ, (cω)(pL x) = c·ω(pL x), so Φ_{cω} = c·Φ_ω and T(cω) = c·T(ω) (integral_const_mul; no integrability needed). By steps 2 and 3, T is an ℝ-linear map 𝒟^l(U) → ℝ (an element of CurrentOn U l).
4. (Sequential continuity: set-up.) Let (ω_j) be a sequence in 𝒟^l(U) with TestFormOnConverges ω_j 0. By definition there is a compact K ⊆ U with tsupport ω_j ⊆ K for all j, and, for derivative order k = 0, iteratedFDeriv ℝ 0 ω_j → iteratedFDeriv ℝ 0 0 = 0 uniformly on K (iteratedFDeriv of the zero function is 0). Since ‖iteratedFDeriv ℝ 0 f y‖ = ‖f(y)‖ (norm_iteratedFDeriv_zero), for every δ > 0 there is N such that ‖ω_j(y)‖ < δ for all j ≥ N and y ∈ K (Metric.tendstoUniformlyOn_iff).
5. Apply integral_estimate with this K (S ∩ pL⁻¹K is compact because K ⊆ U is compact): there is c ≥ 0 with |T(η)| ≤ c·M whenever η is a continuous l-form vanishing off K and ‖η(y)‖ ≤ M for all y.
6. Let ε > 0, δ := ε/(c + 1) > 0, and N as in step 4 for this δ. For j ≥ N and every y: if y ∈ K then ‖ω_j(y)‖ < δ; if y ∉ K then y ∉ tsupport ω_j, so ω_j(y) = 0. Thus ‖ω_j(y)‖ ≤ δ for all y; ω_j is continuous and vanishes off K, so step 5 gives |T(ω_j)| ≤ c·δ = c·ε/(c + 1) < ε. Hence T(ω_j) → 0.
7. Therefore Y := ⟨T, (continuity from step 6)⟩ is an element of GeometricCurrentOn U l, and Y(ω) = T(ω) = ∫_F ξ(x)(ω(pL x)∘pL) dμ(x) for every ω ∈ 𝒟^l(U), by definition. ∎

Formalization aid (not part of the mathematical argument). During decomposition, the following proof of exactly this frozen type was compiled in the contract scope (after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s; Lean v4.35.0-rc3, Mathlib 25730c7c), using only the sibling declarations named in it and the standard axioms [propext, Classical.choice, Quot.sound]. It passes the leaf rule (one appended theorem, no helper declarations) and may be used directly or adapted:
```lean
theorem Submission.cbr_ci_pw_proj_integral_current : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ Y : GeometricCurrentOn U l, ∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ := by
  intro P m l pL U S F μ ξ hF hFS hcpt hμ hξm hξb hN3
  have hint : ∀ ω : TestFormOn U l, Integrable (fun x => ξ x
      (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)) (μ.restrict F) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid m) l) := ω.property.1.1.continuous
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid m) l)) := ω.property.1.2
    obtain ⟨c, -, hc⟩ := Submission.cbr_ci_pw_proj_integral_estimate P m l pL S F
      (tsupport (ω : DifferentialForm (Euclid m) l)) μ ξ hF hFS (hcpt _ hK ω.property.2) hμ hξm hξb hN3
    obtain ⟨M, hM⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
    exact (hc _ M hωc (fun y hy => image_eq_zero_of_notMem_tsupport hy) hM).1
  let T : CurrentOn U l :=
    { toFun := fun ω => ∫ x in F, ξ x
        (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ
      map_add' := fun ω η => by
        rw [← integral_add (hint ω) (hint η)]
        congr 1
        funext x
        rw [← map_add]
        congr 1
      map_smul' := fun c ω => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext x
        rw [← smul_eq_mul, ← map_smul]
        congr 1 }
  refine ⟨⟨T, fun ωs hωs => ?_⟩, fun ω => rfl⟩
  obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hωs
  obtain ⟨c, hc0, hc⟩ := Submission.cbr_ci_pw_proj_integral_estimate P m l pL S F K μ ξ hF hFS
    (hcpt K hK hKU) hμ hξm hξb hN3
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (c + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 (hconv 0) _ hδ).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  have hbd : ∀ y, ‖(ωs n : DifferentialForm (Euclid m) l) y‖ ≤ ε / (c + 1) := by
    intro y
    by_cases hy : y ∈ K
    · have := hN n hn y hy
      simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
        norm_iteratedFDeriv_zero] at this
      exact this.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)), norm_zero]
      exact hδ.le
  have hωc : Continuous (ωs n : DifferentialForm (Euclid m) l) := (ωs n).property.1.1.continuous
  have := (hc _ _ hωc (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h))) hbd).2
  rw [Real.dist_eq, sub_zero]
  calc |T (ωs n)| ≤ c * (ε / (c + 1)) := this
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
```

## Key steps

1. Every integrand Φ_ω is μ⌞F-integrable by integral_estimate with K = tsupport ω (ω is bounded, compactly supported in U).
2. T(ω) := ∫_F Φ_ω dμ is ℝ-linear: ω ↦ Φ_ω is pointwise linear; integral_add and integral_const_mul.
3. If ω_j → 0 in 𝒟^l(U) with supports in a compact K ⊆ U, the order-0 uniform convergence gives sup_y ‖ω_j(y)‖ → 0.
4. integral_estimate for K gives |T(ω_j)| ≤ c·sup‖ω_j‖ → 0, so Y := ⟨T, continuity⟩ ∈ 𝒟_l(U) satisfies the integral formula by definition.

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
