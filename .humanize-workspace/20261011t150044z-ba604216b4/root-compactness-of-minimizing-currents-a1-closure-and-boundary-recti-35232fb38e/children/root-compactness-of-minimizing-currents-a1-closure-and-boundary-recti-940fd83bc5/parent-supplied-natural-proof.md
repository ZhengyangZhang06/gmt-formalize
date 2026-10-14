# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.projection-a1.smooth_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the cutoff (N4) of the parent proof (used there in steps 5 and 6), extracted as a stand-alone lemma. Notation: thickening δ K = {x : dist(x, K) < δ} (open) and cthickening δ K = {x : dist(x, K) ≤ δ} (closed), taken in the Euclidean metric of ℝ^P.
1. Since K is compact, O is open and K ⊆ O, there is δ > 0 with cthickening δ K ⊆ O (IsCompact.exists_cthickening_subset_open). Put r := δ/2, so 0 < r < δ.
2. A := thickening δ K is open (isOpen_thickening) and B := cthickening r K is closed (isClosed_cthickening); B ⊆ A because 0 < δ and r < δ (cthickening_subset_thickening').
3. ℝ^P is a finite-dimensional real normed space, so the smooth Urysohn lemma exists_contDiff_support_eq_eq_one_iff, applied with smoothness ∞ to the open set A and the closed set B ⊆ A, gives χ : ℝ^P → ℝ with χ ∈ C^∞, range χ ⊆ [0, 1], support χ = A, and, for every x, χ(x) = 1 ⟺ x ∈ B.
4. tsupport χ = closure(support χ) = closure(thickening δ K) ⊆ cthickening δ K (closure_thickening_subset_cthickening) ⊆ O (step 1).
5. cthickening δ K is compact because K is compact and ℝ^P is a proper metric space (IsCompact.cthickening). tsupport χ is closed and, by step 4, contained in this compact set, so it is compact (IsCompact.of_isClosed_subset); that is, χ has compact support.
6. For every x, χ(x) ∈ range χ ⊆ [0, 1], i.e. 0 ≤ χ(x) ≤ 1.
7. Let O' := thickening r K. It is open (isOpen_thickening); K ⊆ O' because r > 0 (self_subset_thickening); and O' ⊆ cthickening r K = B (thickening_subset_cthickening), so χ(x) = 1 for every x ∈ O' by step 3.
8. Steps 3–7 give all required properties of χ and O' (smoothness by step 3, compact support by step 5, tsupport χ ⊆ O by step 4, the bounds by step 6, and O' by step 7). ∎

Formalization aid (not part of the mathematical argument). During decomposition, the following proof of exactly this frozen type was compiled in the contract scope (after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's `open`s; Lean v4.35.0-rc3, Mathlib 25730c7c), using only the sibling declarations named in it and the standard axioms [propext, Classical.choice, Quot.sound]. It passes the leaf rule (one appended theorem, no helper declarations) and may be used directly or adapted:
```lean
theorem Submission.cbr_ci_pw_proj_smooth_cutoff : ∀ (P : ℕ) (K O : Set (Euclid P)), IsCompact K → IsOpen O → K ⊆ O → ∃ (χ : Euclid P → ℝ) (O' : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen O' ∧ K ⊆ O' ∧ ∀ x ∈ O', χ x = 1 := by
  intro P K O hK hO hKO
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hr : 0 < δ / 2 := half_pos hδ
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K))
      (isClosed_cthickening (δ := δ / 2) (E := K))
      (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  have hts : tsupport χ ⊆ cthickening δ K := by
    rw [tsupport, hsupp]
    exact closure_thickening_subset_cthickening δ K
  refine ⟨χ, thickening (δ / 2) K, hχ, ?_, hts.trans hδO, fun x => ?_, isOpen_thickening,
    self_subset_thickening hr K, fun x hx => (hone x).1 (thickening_subset_cthickening _ _ hx)⟩
  · exact (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport χ) hts
  · exact hrange (mem_range_self x)
```

## Key steps

1. Choose δ > 0 with cthickening δ K ⊆ O (IsCompact.exists_cthickening_subset_open).
2. Smooth Urysohn (exists_contDiff_support_eq_eq_one_iff): χ ∈ C^∞ with values in [0,1], support χ = thickening δ K and χ = 1 exactly on cthickening (δ/2) K.
3. tsupport χ ⊆ cthickening δ K ⊆ O, and cthickening δ K is compact, so χ has compact support.
4. O' := thickening (δ/2) K is an open set containing K on which χ = 1.

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
