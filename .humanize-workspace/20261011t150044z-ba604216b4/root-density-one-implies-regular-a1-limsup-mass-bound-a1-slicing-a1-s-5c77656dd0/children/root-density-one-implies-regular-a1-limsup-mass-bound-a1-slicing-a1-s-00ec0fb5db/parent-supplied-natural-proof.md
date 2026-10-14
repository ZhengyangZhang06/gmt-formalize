# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.disjoint_refinement-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 4–6; Simon Ch. 3, Remark 1.3 (chapter-03.txt lines 67–72).

1. Images. E_j := ψ_j(C_j) is compact, as the continuous image of a compact set. So E_j is closed and Borel, and A_j := M ∩ E_j is Borel.

2. Exceptional sets.
   - Let p_j(x) mean: every y ∈ C_j with ψ_j(y) = x satisfies Good_j(y). The hypothesis says μ⌞A_j({x : ¬p_j(x)}) = 0.
   - By exists_measurable_superset_of_null, applied to the measure μ⌞A_j, choose a Borel set T_j ⊇ {x : ¬p_j(x)} with μ⌞A_j(T_j) = 0.
   - Since T_j is Borel, μ⌞A_j(T_j) = μ(T_j ∩ A_j) (Measure.restrict_apply). So μ(T_j ∩ A_j) = 0.

3. Disjointification (Remark 1.3). Let D_j := A_j ∖ ⋃_{i<j} A_i (Mathlib disjointed A j). Then:
   - the D_j are Borel (MeasurableSet.disjointed);
   - they are pairwise disjoint (disjoint_disjointed);
   - D_j ⊆ A_j (disjointed_subset);
   - ⋃_j D_j = ⋃_j A_j (iUnion_disjointed).

4. Definitions. Put M'_j := D_j ∖ T_j, which is Borel, and Y_j := C_j ∩ ψ_j⁻¹(M'_j).

5. Y_j is Borel. Let ψ̃_j equal ψ_j on C_j and 0 off C_j. ψ̃_j is continuous on the closed set C_j and constant on its complement, so it is Borel (ContinuousOn.measurable_piecewise). Since Y_j = C_j ∩ ψ̃_j⁻¹(M'_j), it is an intersection of two Borel sets.

6. ψ_j(Y_j) = M'_j. The inclusion '⊆' is immediate. Conversely, let x ∈ M'_j. Then x ∈ D_j ⊆ A_j ⊆ E_j, so x = ψ_j(y) for some y ∈ C_j, and this y lies in Y_j.

7. Properties.
   - Y_j ⊆ C_j by definition.
   - ψ_j(Y_j) = M'_j ⊆ D_j ⊆ A_j ⊆ M.
   - Good points: let y ∈ Y_j and x := ψ_j(y) ∈ M'_j. Then x ∉ T_j ⊇ {¬p_j}, so p_j(x) holds. Applying p_j(x) to y (y ∈ C_j and ψ_j(y) = x) gives Good_j(y).
   - Disjointness: for i ≠ j, ψ_i(Y_i) = M'_i ⊆ D_i and ψ_j(Y_j) ⊆ D_j, which are disjoint.

8. Null remainder. Let x ∈ M ∖ ⋃_j ψ_j(Y_j).
   - If x ∉ ⋃_j E_j, then x ∈ M ∖ ⋃_j E_j.
   - Otherwise x ∈ M ∩ E_{j₀} = A_{j₀} for some j₀. So x ∈ ⋃_j A_j = ⋃_j D_j, and x ∈ D_j for some j. Since x ∉ ψ_j(Y_j) = M'_j = D_j ∖ T_j, we get x ∈ T_j, and x ∈ D_j ⊆ A_j.
   Hence M ∖ ⋃_j ψ_j(Y_j) ⊆ (M ∖ ⋃_j E_j) ∪ ⋃_j (T_j ∩ A_j). By countable subadditivity its μ-measure is at most 0 + Σ_j 0 = 0. ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound.
```lean
  classical
  intro m P μ M C ψ Good hM hC hnull hgood
  let E : ℕ → Set (Euclid P) := fun j => ψ j '' C j
  have hEc : ∀ j, IsCompact (E j) := fun j => (hC j).1.image_of_continuousOn (hC j).2
  have hEm : ∀ j, MeasurableSet (E j) := fun j => (hEc j).isClosed.measurableSet
  let A : ℕ → Set (Euclid P) := fun j => M ∩ E j
  have hAm : ∀ j, MeasurableSet (A j) := fun j => hM.inter (hEm j)
  have hT : ∀ j, ∃ T : Set (Euclid P), {x | ¬ ∀ y ∈ C j, ψ j y = x → Good j y} ⊆ T ∧
      MeasurableSet T ∧ μ (T ∩ A j) = 0 := by
    intro j
    obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hgood j))
    exact ⟨T, hsub, hTm, by rwa [Measure.restrict_apply hTm] at hT0⟩
  choose T hTsub hTm hT0 using hT
  let D : ℕ → Set (Euclid P) := disjointed A
  let M' : ℕ → Set (Euclid P) := fun j => D j \ T j
  have hDm : ∀ j, MeasurableSet (D j) := MeasurableSet.disjointed hAm
  have hM'm : ∀ j, MeasurableSet (M' j) := fun j => (hDm j).diff (hTm j)
  have hDA : ∀ j, D j ⊆ A j := disjointed_subset A
  have himg : ∀ j, ψ j '' (C j ∩ ψ j ⁻¹' M' j) = M' j := by
    intro j
    ext x
    constructor
    · rintro ⟨y, ⟨_, hy⟩, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (hDA j hx.1).2
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  refine ⟨fun j => C j ∩ ψ j ⁻¹' M' j, fun j => ⟨?_, inter_subset_left, ?_, ?_⟩, ?_, ?_⟩
  · have hpw : Measurable ((C j).piecewise (ψ j) (fun _ => 0)) :=
      (hC j).2.measurable_piecewise continuousOn_const (hC j).1.isClosed.measurableSet
    have : C j ∩ ψ j ⁻¹' M' j = C j ∩ (C j).piecewise (ψ j) (fun _ => 0) ⁻¹' M' j := by
      ext y
      constructor
      · rintro ⟨hy, hy'⟩
        exact ⟨hy, by simpa [Set.piecewise_eq_of_mem _ _ _ hy] using hy'⟩
      · rintro ⟨hy, hy'⟩
        exact ⟨hy, by simpa [Set.piecewise_eq_of_mem _ _ _ hy] using hy'⟩
    show MeasurableSet (C j ∩ ψ j ⁻¹' M' j)
    rw [this]
    exact (hC j).1.isClosed.measurableSet.inter (hpw (hM'm j))
  · rw [himg j]
    exact fun x hx => (hDA j hx.1).1
  · intro y hy
    have hx : ψ j y ∉ T j := hy.2.2
    have : ψ j y ∉ {x | ¬ ∀ y ∈ C j, ψ j y = x → Good j y} := fun h => hx (hTsub j h)
    simp only [mem_setOf_eq, not_not] at this
    exact this y hy.1 rfl
  · intro i j hij
    simp only
    rw [himg i, himg j]
    exact (disjoint_disjointed A hij).mono diff_subset diff_subset
  · have hsub : M \ ⋃ j, ψ j '' (C j ∩ ψ j ⁻¹' M' j) ⊆ (M \ ⋃ j, E j) ∪ ⋃ j, (T j ∩ A j) := by
      rintro x ⟨hxM, hxnot⟩
      by_cases hxE : x ∈ ⋃ j, E j
      · right
        have hxA : x ∈ ⋃ j, A j := by
          obtain ⟨j, hj⟩ := mem_iUnion.1 hxE
          exact mem_iUnion.2 ⟨j, hxM, hj⟩
        rw [← iUnion_disjointed] at hxA
        obtain ⟨j, hj⟩ := mem_iUnion.1 hxA
        have hxT : x ∈ T j := by
          by_contra hxT
          exact hxnot (mem_iUnion.2 ⟨j, by rw [himg j]; exact ⟨hj, hxT⟩⟩)
        exact mem_iUnion.2 ⟨j, hxT, hDA j hj⟩
      · exact Or.inl ⟨hxM, hxE⟩
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨hnull, measure_iUnion_null hT0⟩
```

## Key steps

1. E_j = ψ_j(C_j) is compact and Borel; set A_j = M ∩ E_j.
2. Choose a Borel μ⌞A_j-null set T_j ⊇ the bad set (exists_measurable_superset_of_null); then μ(T_j ∩ A_j) = 0.
3. D_j = disjointed A, M'_j = D_j ∖ T_j and Y_j = C_j ∩ ψ_j⁻¹(M'_j); Y_j is Borel via ContinuousOn.measurable_piecewise.
4. ψ_j(Y_j) = M'_j ⊆ M; Good holds on Y_j; disjointness comes from the D_j.
5. M ∖ ⋃ ψ_j(Y_j) ⊆ (M ∖ ⋃ E_j) ∪ ⋃ (T_j ∩ A_j), which is μ-null.

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
