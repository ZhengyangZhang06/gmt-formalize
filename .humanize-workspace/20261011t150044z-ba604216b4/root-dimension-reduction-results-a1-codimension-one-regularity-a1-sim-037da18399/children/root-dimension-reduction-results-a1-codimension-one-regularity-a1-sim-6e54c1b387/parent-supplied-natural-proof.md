# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_area-a1.lintegral_image_of_local-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 5, 6 and 8 of the parent proof: the Lusin–Souslin theorem, a countable chart cover via Lindelöf, disjointification, and countable additivity. Here the additivity is applied to set integrals rather than to measures. No sibling is used.

Proof. Fix a Borel set B ⊆ N and g : ℝ^P → [0, ∞].
1. (Φ maps Borel sets to Borel sets.) ℝ^P is a Polish space, and Φ is continuous and injective. By the Lusin–Souslin theorem Φ is a measurable embedding (Continuous.measurableEmbedding). So Φ(E) is Borel for every Borel E (MeasurableEmbedding.measurableSet_image).
2. (Trivial case.) If N = ∅, then B = ∅ and Φ(B) = ∅, so both sides are integrals over the empty set and equal 0. From now on assume N ≠ ∅.
3. (Countable subcover.) For each y ∈ N choose an open W_y ∋ y as in the hypothesis. The sets W_y (y ∈ N) are open and cover N. ℝ^P is second countable, hence hereditarily Lindelöf, so N is a Lindelöf set (HereditarilyLindelofSpace.isLindelof). Since N is nonempty, there is a sequence (y_k)_{k∈ℕ} in N with N ⊆ ⋃_k W_{y_k} (IsLindelof.indexed_countable_subcover).
4. (Disjoint Borel pieces.) Let S_k := B ∩ W_{y_k} and B_k := S_k ∖ ⋃_{i<k} S_i, i.e. disjointed S.
- Each S_k is Borel (B is Borel and W_{y_k} is open), hence each B_k is Borel (MeasurableSet.disjointed).
- The B_k are pairwise disjoint (disjoint_disjointed).
- ⋃_k B_k = ⋃_k S_k = B ∩ ⋃_k W_{y_k} = B, because B ⊆ N ⊆ ⋃_k W_{y_k} (iUnion_disjointed).
- B_k ⊆ S_k ⊆ W_{y_k} ∩ N, because B ⊆ N.
5. (Images.) Each Φ(B_k) is Borel by step 1. The Φ(B_k) are pairwise disjoint because Φ is injective. ⋃_k Φ(B_k) = Φ(⋃_k B_k) = Φ(B).
6. (Countable additivity.) Let E_k be pairwise disjoint Borel sets and f : ℝ^P → [0, ∞], measurable or not. Then ∫⁻_{⋃_k E_k} f dμ = Σ_k ∫⁻_{E_k} f dμ (lintegral_iUnion), because μ restricted to the union is the sum of the restrictions. Hence:
 ∫⁻_{Φ(B)} g dμ = Σ_k ∫⁻_{Φ(B_k)} g dμ, by steps 5 and 6;
 = Σ_k ∫⁻_{B_k} w(x)·g(Φ(x)) dμ(x), by the hypothesis for y_k applied to the Borel set B_k ⊆ W_{y_k} ∩ N (step 4);
 = ∫⁻_{⋃_k B_k} w(x)·g(Φ(x)) dμ(x) = ∫⁻_B w(x)·g(Φ(x)) dμ(x), by steps 4 and 6. ∎

Lean notes. No import may be added (depth-6 leaf), and none is needed. Use `choose!` on the local hypothesis to obtain y ↦ W_y. Then use `(HereditarilyLindelofSpace.isLindelof N).indexed_countable_subcover` with an instance `Nonempty N`.

Appendix (Lean proof checked with Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308). Placed as `theorem Submission.codim1_ac_saf_lintegral_image_of_local : <frozen type> := by` followed by this tactic block, inside `namespace GMT.Ch07` after the contract's `end` of the noncomputable section, with no import beyond the frozen contract (`import GMT.Ch07.Submission` only); it passes the runtime leaf gate leaf_verification.check_source_delta. `#print axioms` reported: [propext, Classical.choice, Quot.sound].
```lean
  intro P μ N Φ w hΦc hΦinj hloc B hBN hB g
  classical
  have hemb : MeasurableEmbedding Φ := hΦc.measurableEmbedding hΦinj
  rcases N.eq_empty_or_nonempty with hN0 | hNne
  · have hB0 : B = ∅ := subset_empty_iff.1 (hN0 ▸ hBN)
    subst hB0
    simp
  choose! Wf hWo hyW hform using hloc
  have : Nonempty N := hNne.to_subtype
  obtain ⟨j, hj⟩ := (HereditarilyLindelofSpace.isLindelof N).indexed_countable_subcover
    (fun y : N => Wf y) (fun y => hWo y y.2) (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, hyW y hy⟩)
  set S : ℕ → Set (Euclid P) := fun k => B ∩ Wf (j k) with hSdef
  set D : ℕ → Set (Euclid P) := disjointed S with hDdef
  have hDm : ∀ k, MeasurableSet (D k) :=
    MeasurableSet.disjointed (fun k => hB.inter (hWo _ (j k).2).measurableSet)
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed S
  have hDU : ⋃ k, D k = B := by
    rw [hDdef, iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset fun k => inter_subset_left
    · intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hj (hBN hx))
      exact mem_iUnion.2 ⟨k, hx, hk⟩
  have hDsub : ∀ k, D k ⊆ Wf (j k) ∩ N := fun k x hx =>
    ⟨(disjointed_subset S k hx).2, hBN (disjointed_subset S k hx).1⟩
  have hImDisj : Pairwise (Disjoint on fun k => Φ '' D k) := fun a b hab =>
    (hDdisj hab).image hΦinj.injOn (subset_univ _) (subset_univ _)
  calc ∫⁻ z in Φ '' B, g z ∂μ = ∫⁻ z in ⋃ k, Φ '' D k, g z ∂μ := by rw [← image_iUnion, hDU]
    _ = ∑' k, ∫⁻ z in Φ '' D k, g z ∂μ :=
        lintegral_iUnion (fun k => hemb.measurableSet_image.2 (hDm k)) hImDisj g
    _ = ∑' k, ∫⁻ x in D k, w x * g (Φ x) ∂μ := by
        congr 1; funext k; exact hform (j k) (j k).2 (D k) (hDsub k) (hDm k) g
    _ = ∫⁻ x in ⋃ k, D k, w x * g (Φ x) ∂μ := (lintegral_iUnion hDm hDdisj _).symm
    _ = ∫⁻ x in B, w x * g (Φ x) ∂μ := by rw [hDU]
```

## Key steps

1. Lusin–Souslin: the continuous injective Φ on Polish ℝ^P maps Borel sets to Borel sets.
2. Lindelöf: countably many neighbourhoods W_{y_k} cover N; disjointify B into Borel pieces B_k ⊆ W_{y_k} ∩ N with union B.
3. Countable additivity of set integrals on both sides (lintegral_iUnion, any integrand); injectivity makes the Φ(B_k) disjoint with union Φ(B); apply the local hypothesis on each piece.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD (b4d606db); git -C .lake/packages/mathlib rev-parse HEAD (25730c7c); git -C .lake/packages/simongmt rev-parse HEAD (2b366308)`
- `sha256sum GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean <snapshot>/project/GMT/Ch07/Contract.lean (all e4148e7f…); git show 785373c2:GMT/Ch07/Submission.lean | sha256sum (node proof base = contract)`
- `sha256sum <snapshot>/mathlib/X vs .lake/packages/mathlib/X for X in {MeasureTheory/Constructions/Polish/Basic, MeasureTheory/Integral/Lebesgue/Basic, Topology/Compactness/Lindelof, Analysis/Calculus/FDeriv/Comp, Analysis/Calculus/ContDiff/{Defs,Comp}, Analysis/InnerProductSpace/{PiL2,NormDet}, MeasureTheory/Constructions/BorelSpace/Basic, Order/Disjointed, MeasureTheory/MeasurableSpace/Constructions, Topology/Instances/Matrix}.lean (all SAME)`
- `rg -n -F in <snapshot>/mathlib/Mathlib: 'theorem lintegral_iUnion ', 'theorem Continuous.measurableEmbedding', 'theorem IsLindelof.indexed_countable_subcover', 'HereditarilyLindelofSpace.isLindelof', 'theorem fderiv_comp ', 'theorem ContDiffOn.continuousOn_fderiv_of_isOpen', 'theorem ContDiff.comp_contDiffOn', 'theorem ContinuousOn.measurable_piecewise', 'theorem setLIntegral_congr_fun ', 'theorem finrank_euclideanSpace_fin', 'theorem LinearMap.finrank_range_of_inj', 'theorem Continuous.matrix_det', 'theorem iUnion_disjointed', 'theorem disjointed_subset', 'theorem MeasurableSet.disjointed', 'theorem sqrt_mul\' '`
- `rg -n 'normDet|codim1_ac_saf' <snapshot>/project (normDet only in GMT/Ch03 and the Ch02 README, not in the Ch07 closure; codim1_ac_saf: no match)`
- `grep -n 'def IsEmbeddedSubmanifold|def tangentSpace' GMT/Ch07/Contract.lean (lines 221, 228)`
- `python3 scans of dag.json at 18:15Z, 18:19Z, 18:31:49Z and 19:12:29Z: status/candidate/updated_at and lean_statement identity of chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, codim1_lura_gram_det_comp_orthonormal, dpf_det_gram_stdOrthonormalBasis_eq, codim1_lura_gram_area_formula; count of codim1_ac_saf (0); titles matching area|gram|jacobian (alternatives dpf_raf_piece_area_formula_gram, codim1_lur_cd_injective_area_formula_gram, dpf_area_formula_bilipschitz_rectifiable, codim1_hcp_submanifold_area_formula)`
- `issue-workers.json (worker 0b7443da… for issue 5877 started 16:35:02Z); .humanize/swarm-configs/0b7443da79c04f0ca0fa6637366c6d18.json (max_depth 6, max_children 12, max_nodes 5000, decomposition_attempts 5, github_shared_issue_runtime true)`
- `runtime.py: _existing_lean_name_problem, _accepted_checkpoint, _decompose (start-of-attempt store.update), activation existing_by_name mapping, _install_parent_supplied_child_handoff (returns early for accepted checkpoints), _overlay_accepted_children; store.py Store.refresh/update; parallel.py enabled; leaf_verification.py check_source_delta`
- `git log --all --oneline -S codim1_ac_saf -- GMT/Ch07/Submission.lean over 6521 refs (no match)`
- `for c in d626082a 5e4b2158 d596f85a 5ac0181c d5ba41d6: git show $c:GMT/Ch07/Submission.lean | grep '^import' | md5sum (all equal to HEAD: 8 contract imports), grep -n 'theorem Submission.<reused name>' (present, type byte-identical)`
- `python3 -I scripts/gen.py (Assembly.lean, Child_*.lean, Combined.lean); lake env lean -DautoImplicit=false on each (exit 0, no error/warning lines)`
- `python3 scripts/gate.py: check_source_delta(contract, contract + theorem, name) for the four new children and the parent assembly (all PASS)`
- `python3 scripts/merge.py; lake env lean -DautoImplicit=false /tmp/saf3-q9w4/lean/Merged.lean (exit 0, 2m54s; parent axioms [propext, Classical.choice, Quot.sound])`
- `sed -n 750,800p; 845,875p; 950,1000p book/chapter-02.txt (Simon 3.2–3.5, 4.1–4.3, 4.11–4.14)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Compactness/Lindelof.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Real/Sqrt.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/0b7443da79c04f0ca0fa6637366c6d18.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-037da18399/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-037da18399/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-mean-curvature-monotonicity-a1-ch-0f11358db9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-12e3a7fde6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-orientati-3f0e6c2b24/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-db95546c3f/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parallel.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/tmp/saf3-q9w4/lean/Assembly.lean`
- `/tmp/saf3-q9w4/lean/Combined.lean`
- `/tmp/saf3-q9w4/lean/Merged.lean`
- `/tmp/saf3-q9w4/out/Merged.out`
- `/tmp/saf3-q9w4/scripts/gate.py`

Pins match.
- The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib; SimonGMT is at 2b366308, as pinned.
- The snapshot Contract.lean, the workspace Contract.lean and Submission.lean, and the node proof base 785373c2 all carry the same contract (sha256 e4148e7f…).
- The 12 Mathlib files hashed are byte-identical between the snapshot and the workspace.
Library (snapshot).
- Every Mathlib lemma the new children use exists: lintegral_iUnion (any integrand), Continuous.measurableEmbedding, IsLindelof.indexed_countable_subcover, HereditarilyLindelofSpace.isLindelof, fderiv_comp, ContDiffOn.continuousOn_fderiv_of_isOpen, ContDiff.comp_contDiffOn, ContinuousOn.measurable_piecewise, setLIntegral_congr_fun, finrank_euclideanSpace_fin, LinearMap.finrank_range_of_inj, Continuous.matrix_det, iUnion_disjointed, disjointed_subset, MeasurableSet.disjointed, Real.sqrt_mul'.
- NormDet.lean (normDet_comp, normDet_sq_eq_det_gram) is in the snapshot but not in the Ch07 import closure. Depth-6 leaves cannot add imports, so the children use Gram determinants.
- The snapshot has no codim1_ac_saf declaration.
DAG reuse.
- Five accepted checkpoints are reused, each with a byte-identical frozen type and the 8 contract imports in its candidate commit: chart_tangentSpace_eq_range_fderiv (d626082a), dsmc_chart_inverse_continuity (5e4b2158), codim1_lura_gram_det_comp_orthonormal (d596f85a), dpf_det_gram_stdOrthonormalBasis_eq (5ac0181c) and codim1_lura_gram_area_formula (d5ba41d6).
- codim1_lura_gram_area_formula was flagged as active in attempt 1. It has been accepted since 17:18:18Z, so _accepted_checkpoint now holds and _existing_lean_name_problem permits its exact reuse.
- Rejected alternatives:
  - dpf_raf_piece_area_formula_gram needs globally Lipschitz maps.
  - codim1_lur_cd_injective_area_formula_gram is a Bochner, real-valued version.
  - dpf_area_formula_bilipschitz_rectifiable uses approxTangentPlane and a Lipschitz φ.
  - codim1_hcp_submanifold_area_formula is still decomposing and has a different type.
- The four new codim1_ac_saf_* names are free in dag.json (1585 nodes at 19:12:29Z), in the snapshot and in the Submission.lean history on 6521 refs.
Lean (only the contract imports).
- All nine child types elaborate, and the parent follows from the children (Assembly.lean).
- Each new child compiles from its declared siblings alone and passes check_source_delta, as does the 11-line parent assembly.
- Merged.lean (contract + real accepted proof text from the five candidate commits + four new children + assembly) compiles. It proves codim1_ac_submanifold_area_formula with axioms [propext, Classical.choice, Quot.sound].
