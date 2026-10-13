# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.critical_slices-a1`
- Child DAG node: `root.coarea_and_slices-a1.critical_slices-a1.slab_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the last two sentences of step 5 of the supplied proof of c1_critical_slices_null ("A linear isometry of ℝᵐ taking ν to the first basis vector preserves Lᵐ and maps this set of w into the box [−r, r] × [−R, R]^{m−1}. Therefore Lᵐ(...) ≤ 2r·(2R)^{m−1}"), with the translation by c and the degenerate cases made explicit.
Let W := {w ∈ ℝᵐ : |⟨w − c, ν⟩| ≤ r and |w − c| ≤ R}.
1. (Degenerate radii.) If r < 0 then W = ∅, because |⟨w − c, ν⟩| ≥ 0 > r. If R < 0 then W = ∅, because |w − c| ≥ 0 > R. In both cases Lᵐ(W) = 0 ≤ ofReal(2r(2R)^{m−1}). From now on r ≥ 0 and R ≥ 0.
2. (m ≥ 1.) If m = 0 then ℝ⁰ = {0}, so ν = 0 and |ν| = 0 ≠ 1, a contradiction. Hence m = m' + 1 with m' = m − 1.
3. (Rotation taking ν to e₀.) Let e₀ := EuclideanSpace.single 0 1 be the first standard basis vector, so |e₀| = 1 = |ν|. Let ρ be the orthogonal reflection of ℝᵐ in the subspace (ℝ·(ν − e₀))^⊥ (Mathlib Submodule.reflection). It is a linear isometry equivalence of ℝᵐ, and ρ(ν) = e₀ because |ν| = |e₀| (Submodule.reflection_sub; if ν = e₀ the subspace is all of ℝᵐ and ρ is the identity).
4. (W lies in a box after translation and rotation.) Put Φ(w) := ρ(w − c) and write x = Φ(w) with coordinates x_0, …, x_{m'}. Let a := (−r, −R, …, −R) and b := (r, R, …, R) ∈ ℝ^{Fin m} (first coordinate ±r, the others ±R). For w ∈ W:
   • x_0 = ⟨x, e₀⟩ (EuclideanSpace.inner_single_right) = ⟨ρ(w − c), ρ(ν)⟩ = ⟨w − c, ν⟩ (ρ preserves inner products, LinearIsometryEquiv.inner_map_map), so −r ≤ x_0 ≤ r;
   • for every coordinate i, |x_i| ≤ |x| (PiLp.norm_apply_le) = |w − c| (ρ is an isometry) ≤ R, so −R ≤ x_i ≤ R; this is used for i ≠ 0.
   Hence the coordinate vector of Φ(w) lies in the box Icc a b, i.e. W ⊆ (ofLp ∘ ρ ∘ (· − c))⁻¹(Icc a b), where ofLp : ℝᵐ = EuclideanSpace ℝ (Fin m) → (Fin m → ℝ) is the coordinate map.
5. (Measure preservation.) The translation w ↦ w − c preserves Lebesgue measure (measurePreserving_sub_right), ρ preserves Lebesgue measure because it is a linear isometry equivalence of a finite-dimensional inner product space (LinearIsometryEquiv.measurePreserving), and ofLp carries volume on EuclideanSpace ℝ (Fin m) to the product Lebesgue measure on Fin m → ℝ (PiLp.volume_preserving_ofLp). So the composite ofLp ∘ ρ ∘ (· − c) is measure preserving, and since the box Icc a b is measurable, Lᵐ((ofLp ∘ ρ ∘ (· − c))⁻¹(Icc a b)) = L^{Fin m}(Icc a b) (MeasurePreserving.measure_preimage).
6. (Box volume.) By Real.volume_Icc_pi, L^{Fin m}(Icc a b) = Π_{i ∈ Fin m} ofReal(b_i − a_i) = ofReal(2r) · Π_{i ∈ Fin m'} ofReal(2R) (Fin.prod_univ_succ) = ofReal(2r) · ofReal(2R)^{m'} = ofReal(2r·(2R)^{m'}) (ENNReal.ofReal_mul and ENNReal.ofReal_pow, using r, R ≥ 0), and m' = m − 1.
7. By monotonicity of Lᵐ and steps 4–6, Lᵐ(W) ≤ ofReal(2r·(2R)^{m−1}). ∎

## Key steps

1. If r < 0 or R < 0 the set is empty; otherwise |ν| = 1 forces m = m' + 1 ≥ 1.
2. The reflection ρ in (ℝ(ν − e₀))^⊥ is a linear isometry equivalence with ρ(ν) = e₀.
3. w ↦ ρ(w − c) maps the set into the box [−r,r] × [−R,R]^{m'}, since ⟨ρ(w−c), e₀⟩ = ⟨w−c, ν⟩ and |x_i| ≤ |x| = |w − c|.
4. Translation, ρ and the coordinate map ofLp preserve Lebesgue measure, and the box has volume 2r·(2R)^{m−1}.

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
