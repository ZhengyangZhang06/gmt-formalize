# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.gradient_bound_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 8 (= Step 3(a) of the slice-family proof); Lebesgue density theorem (Mathlib Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet).

1. Density points.
   - Lebesgue measure L^m on ℝ^m is locally finite, and ℝ^m has the Besicovitch covering property. Since Z is Borel, Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet gives: for L^m-a.e. y, L^m(Z ∩ B̄_r(y))/L^m(B̄_r(y)) → 1_Z(y) as r ↓ 0 (filter 𝓝[>] 0).
   - Fix such a y with y ∈ Z. Then the limit is 1, i.e. y satisfies the density hypothesis of (DD).
   - It suffices to prove the bound at this y.

2. Unit directions. Let v ∈ ℝ^m with |v| = 1. By (DD), with (d, Z', y', v) := (m, Z, y, v), there are y_i ∈ Z with y_i ≠ y and y_i → y, such that w_i := t_i⁻¹(y_i − y) → v, where t_i := |y_i − y| > 0.

3. Lipschitz comparison. For each i, y and y_i lie in Z, so |F(y_i) − F(y)| = |f(ψ(y_i)) − f(ψ(y))| ≤ L·|ψ(y_i) − ψ(y)|. Multiplying by t_i⁻¹ ≥ 0 gives |t_i⁻¹(F(y_i) − F(y))| ≤ L·|t_i⁻¹(ψ(y_i) − ψ(y))|.

4. Difference quotients.
   - Put d_i := y_i − y and c_i := t_i⁻¹. Then d_i → 0, c_i·d_i = w_i → v, and y + d_i = y_i.
   - F has derivative DF(y) at y, so c_i(F(y + d_i) − F(y)) → DF(y)v (HasFDerivWithinAt.lim with s = ℝ^m, from the HasFDerivAt given by differentiability).
   - Likewise c_i(ψ(y + d_i) − ψ(y)) → Dψ(y)v.
   - Direct argument: F(y + d_i) − F(y) − DF(y)d_i = o(|d_i|) and |c_i d_i| = 1, so c_i(F(y + d_i) − F(y)) − DF(y)w_i → 0. Also DF(y)w_i → DF(y)v by continuity of DF(y).

5. Limit. Absolute value and norm are continuous, and non-strict inequalities pass to the limit (le_of_tendsto_of_tendsto'). So step 3 yields |DF(y)v| ≤ L·|Dψ(y)v|.

6. General e. If e = 0, both sides vanish. Otherwise v := |e|⁻¹e has |v| = 1. By linearity of DF(y) and Dψ(y), |e|⁻¹|DF(y)e| = |DF(y)v| ≤ L|Dψ(y)v| = |e|⁻¹·L|Dψ(y)e|. Multiply by |e| > 0. ∎

Appendix — Lean proof of the frozen type. Compiled against Lean v4.35.0-rc3 and Mathlib 25730c7c after `import GMT.Ch07.Submission`, in the exact comparator scope. Axioms: propext, Classical.choice, Quot.sound.
```lean
  intro DD m P Z F ψ f L hZ hdiff heq hf
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hZ] with y hy hyZ
  have hdens : Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1) := by
    simpa [Set.indicator_of_mem hyZ] using hy
  have hunit : ∀ v : Euclid m, ‖v‖ = 1 → |fderiv ℝ F y v| ≤ (L : ℝ) * ‖fderiv ℝ ψ y v‖ := by
    intro v hv
    obtain ⟨ys, hys, hlim, hdir⟩ := DD m Z y hdens v hv
    have hd0 : Tendsto (fun i => ys i - y) atTop (𝓝 0) := by
      simpa using hlim.sub_const y
    have hF' := ((hdiff y hyZ).1.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    have hψ' := ((hdiff y hyZ).2.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    simp only [add_sub_cancel] at hF' hψ'
    have hineq : ∀ i, |‖ys i - y‖⁻¹ • (F (ys i) - F y)| ≤
        (L : ℝ) * ‖‖ys i - y‖⁻¹ • (ψ (ys i) - ψ y)‖ := by
      intro i
      have hci : 0 ≤ ‖ys i - y‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      rw [smul_eq_mul, abs_mul, abs_of_nonneg hci, norm_smul, Real.norm_of_nonneg hci,
        ← heq _ (hys i).1, ← heq y hyZ]
      have h1 := hf.dist_le_mul (ψ (ys i)) (ψ y)
      rw [Real.dist_eq, dist_eq_norm] at h1
      calc ‖ys i - y‖⁻¹ * |f (ψ (ys i)) - f (ψ y)|
          ≤ ‖ys i - y‖⁻¹ * ((L : ℝ) * ‖ψ (ys i) - ψ y‖) := mul_le_mul_of_nonneg_left h1 hci
        _ = (L : ℝ) * (‖ys i - y‖⁻¹ * ‖ψ (ys i) - ψ y‖) := by ring
    exact le_of_tendsto_of_tendsto' hF'.abs (hψ'.norm.const_mul _) hineq
  intro e
  by_cases he : e = 0
  · simp [he]
  · have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    have hv : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have h := hunit _ hv
    rw [map_smul, map_smul, smul_eq_mul, abs_mul, norm_smul, abs_inv, abs_norm, norm_inv,
      norm_norm] at h
    have hpos : 0 < ‖e‖⁻¹ := inv_pos.2 (norm_pos_iff.2 he)
    have h2 : ‖e‖⁻¹ * |fderiv ℝ F y e| ≤ ‖e‖⁻¹ * ((L : ℝ) * ‖fderiv ℝ ψ y e‖) := by
      calc ‖e‖⁻¹ * |fderiv ℝ F y e| ≤ (L : ℝ) * (‖e‖⁻¹ * ‖fderiv ℝ ψ y e‖) := h
        _ = ‖e‖⁻¹ * ((L : ℝ) * ‖fderiv ℝ ψ y e‖) := by ring
    exact le_of_mul_le_mul_left h2 hpos
```

## Key steps

1. Lebesgue density (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet): a.e. y ∈ Z is a density point of Z.
2. (DD): for a unit v, there are y_i ∈ Z ∖ {y} with y_i → y and (y_i − y)/|y_i − y| → v.
3. Since F = f∘ψ on Z, |F(y_i) − F(y)| ≤ L·|ψ(y_i) − ψ(y)|.
4. The difference quotients converge (HasFDerivWithinAt.lim), giving |DF(y)v| ≤ L·|Dψ(y)v|.
5. Scale to an arbitrary e by linearity.

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
