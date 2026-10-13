# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 2 (Simon Ch. 2, §4 (4.1) local representations; Ch. 3, Lemma 1.2 and Remark 1.3, chapter-03.txt lines 25–72).

A chart below is a pair (V', ψ') such that:
- V' ⊆ ℝ^m is open;
- ψ' is C¹ on V' and injective on V';
- Dψ'(y) is injective for every y ∈ V';
- ψ'(V') ⊆ U.

1. Local charts. Fix l ∈ ℕ and z ∈ N_l. The definition IsEmbeddedSubmanifold 1 m N_l, applied at z, gives:
   - an open V_{l,z} ⊆ ℝ^m;
   - an open W_{l,z} ⊆ ℝ^P with z ∈ W_{l,z};
   - a map ψ_{l,z} : ℝ^m → ℝ^P.
   They satisfy:
   - ψ_{l,z} is C¹ on V_{l,z}. The definition gives the order ((1 : ℕ) : WithTop ℕ∞), which equals 1 (Nat.cast_one; simpa).
   - ψ_{l,z} is injective on V_{l,z}.
   - ψ_{l,z}(V_{l,z}) = W_{l,z} ∩ N_l.
   - Dψ_{l,z}(y) is injective for every y ∈ V_{l,z}.
   The properness clause of the definition is not used. Choose such data for all (l, z) (axiom of choice).

2. Countable subcover. Fix l. The sets W_{l,z}, z ∈ N_l, are open in the second-countable space ℝ^P. Apply Lindelöf's property (Mathlib TopologicalSpace.isOpen_iUnion_countable) to the family z ↦ W_{l,z}, indexed by the subtype N_l. It gives a countable set T_l ⊆ N_l with ⋃_{z∈T_l} W_{l,z} = ⋃_{z∈N_l} W_{l,z}. Since z ∈ W_{l,z} for every z ∈ N_l, N_l ⊆ ⋃_{z∈T_l} W_{l,z}.

3. Shrinking into U. Let I := {(l, z) : l ∈ ℕ, z ∈ T_l}, formally the sigma type Σ l, T_l. It is countable, being a countable union of countable sets. For i = (l, z) ∈ I put V'_i := V_{l,z} ∩ ψ_{l,z}⁻¹(U) and ψ'_i := ψ_{l,z}.
   - V'_i is open: ψ_{l,z} is C¹, hence continuous, on the open set V_{l,z}, and U is open (ContinuousOn.isOpen_inter_preimage).
   - Since V'_i ⊆ V_{l,z}:
     - ψ'_i is C¹ on V'_i (ContDiffOn.mono);
     - ψ'_i is injective on V'_i (InjOn.mono);
     - Dψ'_i(y) is injective for y ∈ V'_i.
   - ψ'_i(V'_i) ⊆ U by the definition of V'_i.
   So (V'_i, ψ'_i) is a chart.

4. Enumeration. Add one index ∗ with V'_∗ := ∅ and ψ'_∗ := 0. This is a chart, because every condition quantifies over the empty set: ∅ is open and ψ'_∗(∅) = ∅ ⊆ U. The index set I ∪ {∗} (formally Option I) is countable and nonempty, so there is a surjection σ : ℕ → I ∪ {∗} (exists_surjective_nat). Put V_s := V'_{σ(s)} and ψ_s := ψ'_{σ(s)}. By step 3 and the choice of ∗, every (V_s, ψ_s) satisfies the five chart properties of the conclusion.

5. Covering. Let x ∈ M. If x ∈ N₀ there is nothing to prove. Otherwise x ∈ N_l for some l, by the hypothesis M ⊆ N₀ ∪ ⋃_l N_l.
   - By step 2, x ∈ W_{l,z} for some z ∈ T_l. So x ∈ W_{l,z} ∩ N_l = ψ_{l,z}(V_{l,z}); write x = ψ_{l,z}(v) with v ∈ V_{l,z}.
   - Since x ∈ M ⊆ U, v ∈ ψ_{l,z}⁻¹(U), i.e. v ∈ V'_{(l,z)}.
   - Choose s with σ(s) = (l, z). Then v ∈ V_s and x = ψ_s(v) ∈ ψ_s(V_s).
   Hence M ⊆ N₀ ∪ ⋃_s ψ_s(V_s). ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound. Use it as the body of `theorem Submission.dor_lmbsf_cp_submanifold_chart_cover : <frozen type> := by`.
```lean
  classical
  intro P m U M N₀ N hU hMU hN hMN
  have hch : ∀ (l : ℕ) (z : N l), ∃ (V : Set (Euclid m)) (W : Set (Euclid P))
      (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ (z : Euclid P) ∈ W ∧
      ContDiffOn ℝ 1 ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ N l ∧ ∀ y ∈ V, Injective (fderiv ℝ ψ y) := by
    intro l z
    obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, -, hD⟩ := hN l z z.2
    exact ⟨V, W, ψ, hV, hW, hzW, by simpa using hψ, hinj, himg, hD⟩
  choose V W ψ hV hW hzW hψ hinj himg hD using hch
  have hT : ∀ l, ∃ T : Set (N l), T.Countable ∧ ⋃ z ∈ T, W l z = ⋃ z, W l z :=
    fun l => TopologicalSpace.isOpen_iUnion_countable (W l) (hW l)
  choose T hTc hTU using hT
  let I := Σ l : ℕ, T l
  haveI : ∀ l, Countable (T l) := fun l => (hTc l).to_subtype
  haveI : Countable I := inferInstance
  let V' : Option I → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some i => V i.1 i.2 ∩ ψ i.1 i.2 ⁻¹' U
  let ψ' : Option I → Euclid m → Euclid P := fun o =>
    match o with
    | none => 0
    | some i => ψ i.1 i.2
  have hchart : ∀ o : Option I, IsOpen (V' o) ∧ ContDiffOn ℝ 1 (ψ' o) (V' o) ∧
      InjOn (ψ' o) (V' o) ∧ (∀ y ∈ V' o, Injective (fderiv ℝ (ψ' o) y)) ∧ ψ' o '' V' o ⊆ U := by
    intro o
    cases o with
    | none => simp [V', ψ']
    | some i =>
      refine ⟨(hψ i.1 i.2).continuousOn.isOpen_inter_preimage (hV i.1 i.2) hU,
        (hψ i.1 i.2).mono inter_subset_left, (hinj i.1 i.2).mono inter_subset_left,
        fun y hy => hD i.1 i.2 y hy.1, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (Option I)
  refine ⟨fun s => V' (σ s), fun s => ψ' (σ s), fun s => hchart (σ s), ?_⟩
  intro x hxM
  rcases hMN hxM with h0 | hx
  · exact Or.inl h0
  · right
    obtain ⟨l, hxl⟩ := mem_iUnion.1 hx
    have hxW : x ∈ ⋃ z ∈ T l, W l z := by
      rw [hTU l]
      exact mem_iUnion.2 ⟨⟨x, hxl⟩, hzW l ⟨x, hxl⟩⟩
    obtain ⟨z, hzT, hxz⟩ := mem_iUnion₂.1 hxW
    have hx' : x ∈ ψ l z '' V l z := by
      rw [himg l z]
      exact ⟨hxz, hxl⟩
    obtain ⟨v, hv, hvx⟩ := hx'
    obtain ⟨s, hs⟩ := hσ (some ⟨l, ⟨z, hzT⟩⟩)
    refine mem_iUnion.2 ⟨s, v, ?_, ?_⟩
    · show v ∈ V' (σ s)
      rw [hs]
      exact ⟨hv, by simpa [hvx] using hMU hxM⟩
    · show ψ' (σ s) v = x
      rw [hs]
      exact hvx
```

## Key steps

1. From IsEmbeddedSubmanifold 1 m N_l choose a chart (V_{l,z}, W_{l,z}, ψ_{l,z}) at every z ∈ N_l, with ψ(V) = W ∩ N_l and order cast ↑1 = 1.
2. Lindelöf (TopologicalSpace.isOpen_iUnion_countable): countably many W_{l,z}, z ∈ T_l, cover N_l.
3. Shrink the domain to V_{l,z} ∩ ψ_{l,z}⁻¹(U): it is open (ContinuousOn.isOpen_inter_preimage), inherits the chart properties by mono, and has image ⊆ U.
4. Enumerate Option (Σ l, T_l) by a surjection from ℕ; the extra index carries the empty chart.
5. Each x ∈ M ∖ N₀ lies in some W_{l,z} ∩ N_l = ψ_{l,z}(V_{l,z}); its preimage lies in the shrunken domain because M ⊆ U.

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
