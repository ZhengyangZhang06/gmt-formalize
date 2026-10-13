# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_tangent_lift-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 9: Φ_j(y) = Dψ_j(y)Γ_j(y)⁻¹∇F_j(y) with Γ_j = Dψ_jᵀDψ_j, the defining identity, and |g| ≤ L. Simon Ch. 2, §4 (gradient ∇^N on a submanifold) and Ch. 3, 2.1.

Notation. E := ℝ^m and H := ℝ^P are finite-dimensional, hence complete, real inner product spaces. For y ∈ ℝ^m:
- A(y) := Dψ(y) : E → H;
- A(y)* : H → E is its adjoint (ContinuousLinearMap.adjoint), so ⟨A(y)*h, e⟩ = ⟨h, A(y)e⟩;
- Γ(y) := A(y)* ∘ A(y) : E → E;
- a(y) := (InnerProductSpace.toDual ℝ E).symm (DF(y)) is the Riesz vector of DF(y), so ⟨a(y), e⟩ = DF(y)e;
- Γ(y)⁻¹ := Ring.inverse Γ(y) in the Banach algebra E →L[ℝ] E (the inverse if Γ(y) is a unit, 0 otherwise).

1. Definition. Φ(y) := A(y)(Γ(y)⁻¹a(y)) for every y ∈ ℝ^m.

2. Γ(y) is a unit for y ∈ V.
   - If Γ(y)e = 0, then 0 = ⟨Γ(y)e, e⟩ = ⟨A(y)e, A(y)e⟩ = |A(y)e|². So A(y)e = 0, and e = 0 because Dψ(y) is injective.
   - Thus the endomorphism Γ(y) of the finite-dimensional space E has trivial kernel, so it is invertible as a linear map (LinearMap.isUnit_iff_ker_eq_bot). Hence it is a unit of E →L[ℝ] E (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap).
   - Writing Γ(y) = u for a unit u, Ring.inverse Γ(y) = u⁻¹ (Ring.inverse_unit), and Γ(y)(Γ(y)⁻¹v) = v for every v.

3. Defining identity. Fix y ∈ V and put w := Γ(y)⁻¹a(y), so Γ(y)w = a(y) by step 2.
   - Φ(y) = A(y)w ∈ range A(y) = Dψ(y)(ℝ^m).
   - For e ∈ E: ⟨Φ(y), A(y)e⟩ = ⟨A(y)w, A(y)e⟩ = ⟨A(y)*A(y)w, e⟩ = ⟨Γ(y)w, e⟩ = ⟨a(y), e⟩ = DF(y)e (ContinuousLinearMap.adjoint_inner_left).

4. Norm bound. Let L ≥ 0 with |DF(y)e| ≤ L·|A(y)e| for all e. With w as in step 3: |Φ(y)|² = ⟨Φ(y), A(y)w⟩ = DF(y)w ≤ |DF(y)w| ≤ L·|A(y)w| = L·|Φ(y)|. If |Φ(y)| = 0, then |Φ(y)| ≤ L because L ≥ 0. Otherwise divide by |Φ(y)| > 0.

5. Continuity on V.
   - (i) y ↦ A(y) is continuous on V, because ψ is C¹ on the open set V (ContDiffOn.continuousOn_fderiv_of_isOpen).
   - (ii) The adjoint operation is a linear isometric equivalence (E →L H) ≃ (H →L E), hence continuous. So y ↦ A(y)* is continuous on V.
   - (iii) Composition of continuous linear maps is jointly continuous, so y ↦ Γ(y) is continuous on V (ContinuousOn.clm_comp).
   - (iv) In the complete normed ring E →L[ℝ] E, Ring.inverse is continuous at every unit (NormedRing.inverse_continuousAt). Since Γ(y) is a unit for y ∈ V (step 2), y ↦ Γ(y)⁻¹ is continuous on V.
   - (v) y ↦ DF(y) is continuous on ℝ^m because F is C¹ (ContDiff.continuous_fderiv), and toDual.symm is continuous. So y ↦ a(y) is continuous.
   - (vi) Evaluation (T, v) ↦ Tv is jointly continuous (ContinuousOn.clm_apply). So y ↦ Γ(y)⁻¹a(y) is continuous on V, and then so is y ↦ A(y)(Γ(y)⁻¹a(y)) = Φ(y). ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound.
```lean
  classical
  intro m P V ψ F hV hψ hinj hF
  let A : Euclid m → (Euclid m →L[ℝ] Euclid P) := fun y => fderiv ℝ ψ y
  let Γ : Euclid m → (Euclid m →L[ℝ] Euclid m) :=
    fun y => (ContinuousLinearMap.adjoint (A y)).comp (A y)
  let a : Euclid m → Euclid m := fun y => (InnerProductSpace.toDual ℝ (Euclid m)).symm (fderiv ℝ F y)
  have hunit : ∀ y ∈ V, IsUnit (Γ y) := by
    intro y hy
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro e he
    have h1 : inner ℝ (Γ y e) e = ‖A y e‖ ^ 2 := by
      simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      exact real_inner_self_eq_norm_sq (A y e)
    have h2 : Γ y e = 0 := he
    rw [h2, inner_zero_left] at h1
    have h3 : A y e = 0 := by
      have : ‖A y e‖ = 0 := by nlinarith [norm_nonneg (A y e)]
      exact norm_eq_zero.1 this
    exact hinj y hy (by simpa [A] using h3)
  refine ⟨fun y => A y (Ring.inverse (Γ y) (a y)), ?_, ?_⟩
  · have hA : ContinuousOn A V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
    have hAadj : ContinuousOn (fun y => ContinuousLinearMap.adjoint (A y)) V :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous.comp_continuousOn hA
    have hΓ : ContinuousOn Γ V := hAadj.clm_comp hA
    have hinv : ContinuousOn (fun y => Ring.inverse (Γ y)) V := by
      intro y hy
      obtain ⟨u, hu⟩ := hunit y hy
      have hc := NormedRing.inverse_continuousAt u
      rw [hu] at hc
      exact hc.comp_continuousWithinAt (hΓ y hy)
    have ha : Continuous a :=
      (InnerProductSpace.toDual ℝ (Euclid m)).symm.continuous.comp (hF.continuous_fderiv one_ne_zero)
    exact hA.clm_apply (hinv.clm_apply ha.continuousOn)
  · intro y hy
    set w := Ring.inverse (Γ y) (a y) with hw
    have hΓw : Γ y w = a y := by
      obtain ⟨u, hu⟩ := hunit y hy
      rw [hw, ← hu, Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, Units.mul_inv,
        ContinuousLinearMap.one_apply]
    have hdef : ∀ e : Euclid m, inner ℝ (A y w) (fderiv ℝ ψ y e) = fderiv ℝ F y e := by
      intro e
      have : inner ℝ (A y w) (A y e) = inner ℝ (Γ y w) e := by
        simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      change inner ℝ (A y w) (A y e) = _
      rw [this, hΓw]
      simp [a, InnerProductSpace.toDual_symm_apply]
    refine ⟨⟨w, rfl⟩, hdef, fun L hL => ?_⟩
    have hsq : ‖A y w‖ ^ 2 ≤ (L : ℝ) * ‖A y w‖ := by
      rw [← real_inner_self_eq_norm_sq]
      calc inner ℝ (A y w) (A y w) = fderiv ℝ F y w := hdef w
        _ ≤ |fderiv ℝ F y w| := le_abs_self _
        _ ≤ (L : ℝ) * ‖fderiv ℝ ψ y w‖ := hL w
    change ‖A y w‖ ≤ (L : ℝ)
    by_cases h0 : ‖A y w‖ = 0
    · rw [h0]; exact L.coe_nonneg
    · have hpos : 0 < ‖A y w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
```

## Key steps

1. Set A(y) = Dψ(y), Γ(y) = A(y)*A(y), a(y) = Riesz vector of DF(y), and Φ(y) = A(y)Γ(y)⁻¹a(y) (Ring.inverse).
2. Γ(y) is injective, hence a unit of E →L E, for y ∈ V.
3. ⟨Φ(y), A(y)e⟩ = ⟨Γ(y)w, e⟩ = ⟨a(y), e⟩ = DF(y)e, and Φ(y) ∈ range A(y).
4. |Φ(y)|² = DF(y)w ≤ L·|A(y)w| = L·|Φ(y)|, so |Φ(y)| ≤ L.
5. Continuity on V: fderiv is continuous; adjoint and composition are continuous; Ring.inverse is continuous at units.

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
