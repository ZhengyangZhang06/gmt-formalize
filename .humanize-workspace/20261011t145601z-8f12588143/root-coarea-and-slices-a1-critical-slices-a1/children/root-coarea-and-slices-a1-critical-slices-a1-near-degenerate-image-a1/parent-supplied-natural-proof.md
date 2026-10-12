# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.critical_slices-a1`
- Child DAG node: `root.coarea_and_slices-a1.critical_slices-a1.near_degenerate_image-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the supplied proof of c1_critical_slices_null ("the image of a critical subcube lies in a thin slab"), with the subcube Q replaced by an arbitrary convex set S of radius d about u₀, the tolerance 1/j by ε, and the bound ‖DG‖ ≤ Λ on the cube by the hypothesis ‖P‖ ≤ Λ. Uses the sibling slab_volume (critSlices_slab_volume_le).
1. (Signs.) Since u₀ ∈ S, ε ≥ ‖DG(u₀) − P‖ ≥ 0 and d ≥ |u₀ − u₀| = 0.
2. (A unit normal to the range of P.) Let V := range P, a linear subspace of ℝᵐ. V ≠ ℝᵐ because P is not surjective. In the finite-dimensional space ℝᵐ, V^⊥ = {0} holds iff V = ℝᵐ (Submodule.orthogonal_eq_bot_iff; finite-dimensional subspaces are complete and so have orthogonal projections), so there is ν₀ ∈ V^⊥ with ν₀ ≠ 0 (Submodule.exists_mem_ne_zero_of_ne_bot). Put ν := |ν₀|⁻¹ ν₀. Then |ν| = 1 and ⟨P x, ν⟩ = |ν₀|⁻¹ ⟨P x, ν₀⟩ = 0 for every x ∈ ℝⁿ, because P x ∈ V and ν₀ ∈ V^⊥ (Submodule.mem_orthogonal).
3. (Mean value inequality.) Let u ∈ S. G is differentiable at every point of the convex set S and ‖DG(v) − P‖ ≤ ε for v ∈ S, so the mean value inequality for G − P on S (Convex.norm_image_sub_le_of_norm_fderiv_le') gives, for e := G(u) − G(u₀) − P(u − u₀), |e| ≤ ε|u − u₀| ≤ εd, using ε ≥ 0 and |u − u₀| ≤ d.
4. (The image lies in a slab.) Let w := G(u) − G(u₀) = P(u − u₀) + e. Then ⟨w, ν⟩ = ⟨P(u − u₀), ν⟩ + ⟨e, ν⟩ = ⟨e, ν⟩ by step 2, so by Cauchy–Schwarz |⟨w, ν⟩| ≤ |e||ν| = |e| ≤ εd. Moreover |w| ≤ |P(u − u₀)| + |e| ≤ ‖P‖ |u − u₀| + εd ≤ Λd + εd = (Λ + ε)d, using ‖P‖ ≤ Λ, |u − u₀| ≤ d, |u − u₀| ≥ 0 and Λ ≥ ‖P‖ ≥ 0.
5. (Conclusion.) By step 4, G(S) ⊆ W := {w' ∈ ℝᵐ : |⟨w' − G(u₀), ν⟩| ≤ εd and |w' − G(u₀)| ≤ (Λ + ε)d}. The sibling slab_volume (critSlices_slab_volume_le applied with this m, ν, c := G(u₀), r := εd, R := (Λ + ε)d, and |ν| = 1) gives Lᵐ(W) ≤ ofReal(2(εd)·(2((Λ + ε)d))^{m−1}). By monotonicity of Lᵐ (measure_mono), Lᵐ(G(S)) ≤ Lᵐ(W) ≤ ofReal(2(εd)·(2(Λ + ε)d)^{m−1}). ∎

## Key steps

1. u₀ ∈ S gives ε ≥ 0 and d ≥ 0.
2. P not surjective gives a unit vector ν ⊥ range P (Submodule.orthogonal_eq_bot_iff).
3. Mean value inequality for G − P on convex S: |G(u) − G(u₀) − P(u − u₀)| ≤ εd.
4. Hence G(S) lies in {w : |⟨w − G(u₀), ν⟩| ≤ εd, |w − G(u₀)| ≤ (Λ+ε)d}.
5. Apply slab_volume (critSlices_slab_volume_le) with r = εd, R = (Λ+ε)d.

## Reference use

### local-project

Queries:
- `cat local-references/d498d77b74ea2063/manifest.json`
- `grep -n "theorem hausdorffMeasure_le_liminf_sum\|theorem hausdorffMeasure_le_liminf_tsum" -A8 mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -n "euclideanHausdorffMeasure\|μHE" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "theorem hausdorffMeasure_le_liminf_tsum|theorem lintegral_liminf_le\b|theorem measure_toMeasurable\b" mathlib/Mathlib`
- `grep -rn "norm_image_sub_le_of_norm_hasFDerivWithin_le'\|norm_image_sub_le_of_norm_fderiv_le'" mathlib/Mathlib`
- `rg -n "theorem reflection_sub|theorem volume_Icc_pi\b|theorem PiLp.volume_preserving_ofLp|theorem measurePreserving_div_right|theorem norm_apply_le \[|theorem ediam_le \{|theorem orthogonal_eq_bot_iff" mathlib/Mathlib`
- `grep -n "inner_map_map" mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `grep -n "def ediam\|theorem ediam_le\|ediam_empty\|ediam_mono" mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `rg -l -i "coarea" mathlib/Mathlib (no match)`
- `rg -n "theorem addHaar_image_eq_zero_of_det_fderivWithin_eq_zero\b|theorem addHaar_image_le_mul_of_det_lt" mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `rg -n "slab|Slab" mathlib/Mathlib -t lean (no match)`
- `rg -n "slice|Sard|critical" project/GMT/Ch03/Contract.lean`
- `grep -rln "hausdorffMeasure_le_liminf\|lintegral_liminf_le" lake-packages-25730c7c/simongmt/Poincare/SimonGMT (no match)`
- `grep -n "^theorem" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean; grep import Chapter03/Rectifiable.lean Chapter02/BV.lean`
- `grep -rl "critSlices_" dag.json nodes GMT simongmt mathlib (no match)`
- `grep -n "An important consequence of 6.3" book/chapter-02.txt`
- `lake env lean /tmp/critslices-decomp/Challenge.lean (four child types in the comparator's replayed Contract scope) and /tmp/critslices-decomp/Final.lean = GMT/Scratch/CritSlicesSplitFull.lean (full proofs of the four children and of the parent assembled from them; #print axioms)`
- `lake env lean /tmp/critslices-decomp/ImpCheck.lean (env.contains `Poincare.SimonGMT.Chapter02.area_image_criticalSet_eq_zero after import GMT.Ch03.Submission: false; module imported: false)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Reflection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Group/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/CritSlicesSplitFull.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/CritSlicesSplitChallenge.lean`

Snapshot d498d77b74ea2063: project d09bc8a, Mathlib 25730c7c, with the pinned simongmt package. Mathlib declarations found and used by the children: Measure.hausdorffMeasure_le_liminf_tsum (Hausdorff.lean:555; countable covers, diameter Metric.ediam, real power); lintegral_liminf_le (Lebesgue/Add.lean:233); measure_toMeasurable (MeasureSpaceDef.lean:348) with measurableSet_toMeasurable and subset_toMeasurable; lintegral_tsum, Measurable.tsum, Measurable.liminf, lintegral_eq_zero_iff; MeasureTheory.Measure.euclideanHausdorffMeasure_def (Volume/Measure.lean:74: μHE[d] = addHaarScalarFactor • μH[d]); Convex.norm_image_sub_le_of_norm_fderiv_le' (MeanValue.lean:549); Submodule.orthogonal_eq_bot_iff (Projection/Submodule.lean:122); Submodule.reflection_sub (Projection/Reflection.lean:153); LinearIsometryEquiv.inner_map_map (InnerProductSpace/LinearMap.lean:117); LinearIsometryEquiv.measurePreserving; measurePreserving_sub_right (to_additive of measurePreserving_div_right, Group/Measure.lean:228); PiLp.volume_preserving_ofLp (Haar/InnerProductSpace.lean:134); Real.volume_Icc_pi (Lebesgue/Basic.lean:235); PiLp.norm_apply_le (PiLp.lean:713); EuclideanSpace.norm_eq and dist_eq; Metric.ediam_le, ediam_mono and ediam_empty (EMetricSpace/Diam.lean). The parent assembly also uses ContDiff.continuous_fderiv, IsCompact.uniformContinuousOn_of_continuous, Metric.uniformContinuousOn_iff_le, IsCompact.exists_bound_of_continuousOn, ae_all_iff and measure_iUnion_null. No match: Mathlib has no co-area formula (rg 'coarea'), no slab or box volume bound for {|⟨w−c,ν⟩| ≤ r, |w−c| ≤ R} (rg 'slab'), no grid-subdivision covering lemma, and no a.e.-slice nullity criterion. Its Sard-type results are equidimensional only: addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (Jacobian.lean:645) and addHaar_image_le_mul_of_det_lt (Jacobian.lean:285), for maps E → E. They do not apply to G : ℝ^{m+k} → ℝ^m. SimonGMT has no co-area critical-slice lemma and no use of hausdorffMeasure_le_liminf or lintegral_liminf_le. Its Chapter02/AreaCritical.lean (area_image_criticalSet_eq_zero) concerns area-formula critical images and is not imported by GMT.Ch03.Submission. The contract imports only Chapter02.BV and Chapter03.Rectifiable from SimonGMT, and a Lean environment check after import GMT.Ch03.Submission found neither the module nor the lemma. The project's Contract.lean has no such lemma; line 261 only mentions slices in SlicesAreRectifiable. Book: chapter-02.txt lines 1476–1478 (p. 66) state the result without proof. Hence the four children are new, reusable obligations, and the names critSlices_* occur nowhere in dag.json, the run's nodes, GMT/, SimonGMT or Mathlib. Verification: GMT/Scratch/CritSlicesSplitFull.lean compiles against import GMT.Ch03.Submission with 0 errors, 0 warnings and no sorry. It holds the four child proofs and the frozen parent type assembled from them, and every theorem's axioms are [propext, Classical.choice, Quot.sound]. GMT/Scratch/CritSlicesSplitChallenge.lean elaborates the four lean_statements as comparator targets in the replayed scope.
