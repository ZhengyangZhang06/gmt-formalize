# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.measurable_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 9 ('g is Borel'). Lusin–Souslin theorem (Mathlib MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurableEmbedding). Countable piecewise gluing (Mathlib Measurable.find). Write M_j := ψ_j(Y_j).

1. Measurable embeddings.
   - ℝ^m is a Polish space. For each j, ψ_j is continuous and injective on the Borel set Y_j.
   - By the Lusin–Souslin theorem, the restriction e_j := ψ_j|_{Y_j} : Y_j → ℝ^P maps Borel subsets of Y_j to Borel subsets of ℝ^P. It is also measurable, so it is a measurable embedding (ContinuousOn.measurableEmbedding).
   - In particular M_j is Borel (MeasurableSet.image_of_continuousOn_injOn).

2. One piece.
   - Φ_j|_{Y_j} : Y_j → ℝ^P is continuous (continuousOn_iff_continuous_restrict), hence Borel.
   - Let g_j : ℝ^P → ℝ^P be the extension of Φ_j|_{Y_j} along e_j by the zero function (Function.extend). So g_j(e_j(y)) = Φ_j(y) for y ∈ Y_j, which is well defined because e_j is injective, and g_j(x) = 0 for x ∉ M_j.
   - The extension of a measurable function along a measurable embedding by a measurable function is measurable (MeasurableEmbedding.measurable_extend). So g_j is Borel.
   - g_j(ψ_j(y)) = Φ_j(y) for every y ∈ Y_j (Injective.extend_apply).

3. Gluing. Index the pieces by n ∈ ℕ:
   - piece 0 is the Borel set R := ℝ^P ∖ ⋃_j M_j, with component function f_0 := 0;
   - piece j+1 is M_j, with component function f_{j+1} := g_j.
   Every x ∈ ℝ^P lies in some piece. Let n(x) be the least n such that x lies in piece n, and put g(x) := f_{n(x)}(x).
   - All pieces and all component functions are Borel. By Mathlib's Measurable.find, a function glued this way from countably many pieces is Borel.
   - Explicitly, for Borel B, g⁻¹(B) = ⋃_n ({x : n(x) = n} ∩ f_n⁻¹(B)), and {x : n(x) = n} = piece n ∖ ⋃_{k<n} piece k is Borel.

4. Values on M_j. Let y ∈ Y_j and x := ψ_j(y) ∈ M_j.
   - x ∉ R.
   - x ∉ M_i for i ≠ j, by pairwise disjointness.
   So piece j+1 is the only piece containing x, n(x) = j+1, and g(x) = g_j(x) = Φ_j(y) by step 2.

5. Zero elsewhere. If x ∉ ⋃_j M_j, then x ∈ R = piece 0, so n(x) = 0 and g(x) = 0. ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound.
```lean
  classical
  intro m P Y ψ Φ hY hdisj
  have hemb : ∀ j, MeasurableEmbedding ((Y j).restrict (ψ j)) := fun j =>
    (hY j).2.1.measurableEmbedding (hY j).1 (hY j).2.2.1
  let gj : ℕ → Euclid P → Euclid P := fun j =>
    Function.extend ((Y j).restrict (ψ j)) ((Y j).restrict (Φ j)) 0
  have hgj : ∀ j, Measurable (gj j) := fun j =>
    (hemb j).measurable_extend (continuousOn_iff_continuous_restrict.1 (hY j).2.2.2).measurable
      measurable_const
  have hgj_val : ∀ j, ∀ y ∈ Y j, gj j (ψ j y) = Φ j y := by
    intro j y hy
    have := (hemb j).injective.extend_apply ((Y j).restrict (Φ j)) 0 ⟨y, hy⟩
    exact this
  have hMm : ∀ j, MeasurableSet (ψ j '' Y j) := fun j =>
    (hY j).1.image_of_continuousOn_injOn (hY j).2.1 (hY j).2.2.1
  let p : ℕ → Euclid P → Prop := fun n x =>
    match n with
    | 0 => x ∉ ⋃ j, ψ j '' Y j
    | j + 1 => x ∈ ψ j '' Y j
  let f : ℕ → Euclid P → Euclid P := fun n =>
    match n with
    | 0 => 0
    | j + 1 => gj j
  have hp : ∀ x, ∃ n, p n x := by
    intro x
    by_cases hx : x ∈ ⋃ j, ψ j '' Y j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact ⟨j + 1, hj⟩
    · exact ⟨0, hx⟩
  have hpm : ∀ n, MeasurableSet {x | p n x} := by
    intro n
    cases n with
    | zero => exact (MeasurableSet.iUnion hMm).compl
    | succ j => exact hMm j
  have hfm : ∀ n, Measurable (f n) := by
    intro n
    cases n with
    | zero => exact measurable_const
    | succ j => exact hgj j
  refine ⟨fun x => f (Nat.find (hp x)) x, Measurable.find hfm hpm hp, ?_, ?_⟩
  · intro j y hy
    have hx : p (j + 1) (ψ j y) := ⟨y, hy, rfl⟩
    have hfind : Nat.find (hp (ψ j y)) = j + 1 := by
      refine le_antisymm (Nat.find_min' _ hx) ?_
      by_contra hlt
      push_neg at hlt
      have hspec := Nat.find_spec (hp (ψ j y))
      cases hn : Nat.find (hp (ψ j y)) with
      | zero =>
        rw [hn] at hspec
        exact hspec (mem_iUnion.2 ⟨j, y, hy, rfl⟩)
      | succ i =>
        rw [hn] at hspec hlt
        have hij : i ≠ j := by omega
        exact Set.disjoint_left.1 (hdisj hij) hspec ⟨y, hy, rfl⟩
    simp only [hfind, f]
    exact hgj_val j y hy
  · intro x hx
    have h0 : p 0 x := by
      simp only [p, mem_iUnion, not_exists]
      exact hx
    have hfind : Nat.find (hp x) = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' _ h0)
    simp only [hfind, f, Pi.zero_apply]
```

## Key steps

1. Lusin–Souslin: ψ_j|Y_j is a measurable embedding, so M_j = ψ_j(Y_j) is Borel.
2. g_j, the extension of Φ_j|Y_j along ψ_j|Y_j by 0, is Borel, with g_j(ψ_j y) = Φ_j y.
3. Glue the pieces ℝ^P ∖ ⋃M_j (value 0) and M_j (value g_j) by the least-index rule; Measurable.find gives a Borel g.
4. Disjointness pins the piece index, so g(ψ_j y) = Φ_j y; and g = 0 off ⋃ M_j.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical); manifest.json (project b4d606d, mathlib 25730c7c); lakefile.toml simongmt rev 2b36630`
- `python3 -I dag.json scans: frozen lean_statement/status of slice_family-a1 children c1_approx, c1_cover, image_tangent, density_directions; selected node status/depth/lean_statement; regex scan for related nodes (disjoint_refinement|image_null|IsEmbeddedSubmanifold 1|tangential gradient|density point|adjoint); lean_name collision check for dor_lmbsf_cp_* (1535 nodes, none)`
- `git grep -l dor_lmbsf_cp_ over all local branch heads (no match); git show <recent branch>:GMT/Ch07/Submission.lean | grep import (extra imports are allowed but not needed)`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique' simongmt Chapter03/Rectifiable.lean; grep -n euclideanHausdorffMeasure_image_le_of_lipschitzOn simongmt Chapter02/Lipschitz.lean; grep -rln 'import Mathlib.Topology.MetricSpace.HausdorffDimension' simongmt`
- `grep mathlib snapshot: isOpen_iUnion_countable, ContinuousOn.isOpen_inter_preimage, LipschitzOnWith.extend_real, ContDiffOn.exists_lipschitzOnWith, ContDiffAt.exists_lipschitzOnWith, DifferentiableOn.hausdorffMeasure_image_eq_zero, euclideanHausdorffMeasure_def/_eq_volume, ae_tendsto_measure_inter_div_of_measurableSet, HasFDerivWithinAt.lim, exists_measurable_superset_of_null, MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurableEmbedding, ContinuousOn.measurable_piecewise, Measurable.find, MeasurableEmbedding.measurable_extend, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot, NormedRing.inverse_continuousAt, ContinuousLinearMap.adjoint_inner_left, disjointed/iUnion_disjointed/MeasurableSet.disjointed`
- `#check and instance probes in the contract scope (/tmp/cp-decomp/probe/Probe.lean, Probe2.lean): isOpen_iUnion_countable must be TopologicalSpace-qualified; DifferentiableOn.hausdorffMeasure_image_eq_zero is not in the import closure; IsLocallyFiniteMeasure volume, HasBesicovitchCovering, PolishSpace, BorelSpace and CompleteSpace instances on Euclid m resolve`
- `python3 -I verifier lean_contract.validate_lean_statement and gmt-compare.child_modules on the 8 statements; lake env lean on /tmp/cp-decomp/v2/Final.lean (8 child proofs plus the parent assembly; #print axioms)`
- `book/chapter-03.txt lines 20–140 and 320–445 (Lemma 1.2, Remark 1.3, Remarks 1.5, proof of Thm 1.6, Def. 2.1); book/chapter-02.txt lines 33, 59–62, 165 (Thms 1.2, 1.4, 1.5)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-5c77656dd0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/cp-decomp/v2/Final.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Reuse. No existing declaration has any of the 8 child types. Related accepted nodes have different types:
- cbrg_exists_countable_disjoint_refinement;
- dsmc_att_blowUpMap_image_null;
- cmr_volume_coordProj_image_null;
- approxTangent_le_submanifold_tangentSpace.
So all children get fresh dor_lmbsf_cp_ names.

Reusable library facts used by the child proofs:
- SimonGMT: Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib topology and analysis: TopologicalSpace.isOpen_iUnion_countable (Lindelöf), LipschitzOnWith.extend_real (McShane), ContDiffOn.exists_lipschitzOnWith, ContDiffAt.exists_lipschitzOnWith, HasFDerivWithinAt.lim.
- Mathlib measure theory: Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, exists_measurable_superset_of_null, ContinuousOn.measurable_piecewise, MeasurableSet.image_of_continuousOn_injOn / ContinuousOn.measurableEmbedding (Lusin–Souslin), MeasurableEmbedding.measurable_extend, Measurable.find.
- Mathlib operators: ContinuousLinearMap.adjoint, NormedRing.inverse_continuousAt, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.
- DifferentiableOn.hausdorffMeasure_image_eq_zero exists but needs an extra import, so c1_image_null uses the self-contained local-Lipschitz route.

Lean checks:
- All 8 child types elaborate in the exact comparator scope.
- All 8 are proved, each with axioms [propext, Classical.choice, Quot.sound].
- The exact frozen parent type is assembled from them plus the 4 uncle frozen types; its only sorryAx comes from the uncle stubs.
