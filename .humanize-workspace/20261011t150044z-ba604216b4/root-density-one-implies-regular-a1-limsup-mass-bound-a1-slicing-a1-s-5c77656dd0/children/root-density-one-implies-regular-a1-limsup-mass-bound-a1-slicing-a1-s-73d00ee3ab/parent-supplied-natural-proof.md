# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_tangent_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 7. Simon Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 '⇒' (chapter-03.txt lines 86–140), with (TL) in place of the upper-density argument.

1. The set S. S := ψ(C') is compact, because ψ is C¹, hence continuous, on the compact set C'. So S is closed and Borel. S ⊆ U by hypothesis.

2. S has finite measure.
   - ψ is C¹ on the convex compact set C', so it is Λ-Lipschitz on C' for some Λ ≥ 0 (ContDiffOn.exists_lipschitzOnWith).
   - By the Lipschitz image bound (SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn), H^m(S) ≤ Λ^m · H^m(C').
   - On Euclid m, H^m(C') = L^m(C') (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), and L^m(C') < ∞ because C' is compact.
   - So H^m(S ∩ K) ≤ H^m(S) < ∞ for every compact K ⊆ U.

3. The set A := M ∩ ψ(C).
   - ψ(C) is compact (C is compact, C ⊆ C', ψ is continuous on C'), so A is Borel.
   - A ⊆ ψ(C) ⊆ ψ(C') = S, because C ⊆ int C' ⊆ C'.
   - A ⊆ M.

4. First application of (TL), with (P, n, U, A, B) := (P, m, U, A, S). Its hypotheses hold: U is open, A and S are Borel, A ⊆ S ⊆ U, and H^m(S ∩ K) < ∞ for every compact K ⊆ U (step 2). Hence, for μHE[m]⌞A-a.e. x and every subspace Q: S has approximate tangent space Q at x iff A has approximate tangent space Q at x.

5. Second application of (TL), with (P, m, U, A, M). Its hypotheses hold: M is Borel, A ⊆ M ⊆ U, and H^m(M ∩ K) < ∞ for compact K ⊆ U by hypothesis. Hence, for μHE[m]⌞A-a.e. x and every Q: M has Q at x iff A has Q at x.

6. Conclusion.
   - The intersection of the two full-measure sets of steps 4 and 5 again has full μHE[m]⌞A-measure (filter_upwards).
   - Let x be in it and y ∈ C with ψ(y) = x. Since y ∈ C ⊆ int C', (IT) says that S = ψ(C') has approximate tangent space Q := Dψ(y)(ℝ^m) at ψ(y) = x.
   - By step 4, A has Q at x; by step 5, M has Q at x. ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound.
```lean
  intro TL P m U M C C' ψ hU hM hMU hfin hψ hψU hC hC' hconv hCC' hIT
  have hψC' : ContinuousOn ψ C' := hψ.continuousOn
  have hCsub : C ⊆ C' := hCC'.trans interior_subset
  have hS : IsCompact (ψ '' C') := hC'.image_of_continuousOn hψC'
  have hSC : IsCompact (ψ '' C) := hC.image_of_continuousOn (hψC'.mono hCsub)
  obtain ⟨Λ, hΛ⟩ := hψ.exists_lipschitzOnWith one_ne_zero hconv hC'
  have hSfin : μHE[m] (ψ '' C') ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hΛ) ?_)
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hC'.measure_lt_top
  have hA : MeasurableSet (M ∩ ψ '' C) := hM.inter hSC.isClosed.measurableSet
  have h1 := TL P m U (M ∩ ψ '' C) (ψ '' C') hU hA hS.isClosed.measurableSet
    (fun x hx => image_mono hCsub hx.2) hψU
    (fun K _ _ => ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
  have h2 := TL P m U (M ∩ ψ '' C) M hU hA hM inter_subset_left hMU hfin
  filter_upwards [h1, h2] with x hx1 hx2 y hy hyx
  have hS' := hIT y (hCC' hy)
  rw [hyx] at hS'
  exact (hx2 _).2 ((hx1 _).1 hS')
```

## Key steps

1. S = ψ(C') is compact, Borel and ⊆ U; ψ is Lipschitz on the convex compact C', so H^m(S) ≤ Λ^m · L^m(C') < ∞.
2. A = M ∩ ψ(C) is Borel, with A ⊆ S and A ⊆ M.
3. Apply (TL) to (A, S) and to (A, M).
4. At a.e. x ∈ A and every y ∈ C with ψ(y) = x, (IT) gives S's tangent plane Dψ(y)(ℝ^m) at x; transfer it to A and then to M.

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
