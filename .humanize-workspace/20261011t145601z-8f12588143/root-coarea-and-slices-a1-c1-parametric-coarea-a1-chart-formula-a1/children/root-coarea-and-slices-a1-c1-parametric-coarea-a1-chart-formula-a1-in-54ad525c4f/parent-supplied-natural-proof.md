# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.integrand_tonelli-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 4 (F is Borel) and 5 (Tonelli through toLp).

1. B' := Φ(B) is Borel and B' ⊆ Ω: B ⊆ O and Φ is continuous and injective on O (Φ.continuousOn, Φ.injOn), ℝⁿ is Polish and P is a Borel space (WithLp.borelSpace), so MeasurableSet.image_of_continuousOn_injOn applies; and Φ(u) ∈ Ω for u ∈ O (Φ.map_source).

2. A Borel version of ρ. ρ = ψ ∘ Φ⁻¹ is continuous on Ω: Φ⁻¹ is continuous on Ω (Φ.continuousOn_symm) and maps Ω into O (Φ.map_target), where ψ is continuous (ContinuousOn.comp). Let ρ̃ := Ω.piecewise ρ (fun _ ↦ 0) (classical decidability). Since Ω is open, hence Borel, and the constant map is continuous on Ωᶜ, ContinuousOn.measurable_piecewise shows that ρ̃ is Borel; ρ̃ = ρ on Ω (Set.piecewise_eq_of_mem), in particular on B'.

3. The Jacobian factor is Borel. Let a(w) := ofReal(normDet(Dρ(w) ∘L j)).
- w ↦ Dρ(w) = fderiv ℝ ρ w is Borel from P to P →L[ℝ] ℝᴺ by Mathlib measurable_fderiv, which holds for every function ρ.
- L ↦ L ∘L j is continuous (Continuous.clm_comp continuous_id continuous_const).
- M ↦ normDet(M) is continuous on ℝᵏ →L[ℝ] ℝᴺ: since normDet(M) ≥ 0 (LinearMap.normDet_nonneg) and normDet(M)² = det(M† ∘L M) (ContinuousLinearMap.normDet_sq), Real.sqrt_sq gives normDet(M) = √det(M† ∘L M), and the adjoint (ContinuousLinearMap.adjoint, continuous), composition (Continuous.clm_comp), ContinuousLinearMap.continuous_det and Real.continuous_sqrt are continuous. (This is the argument of the pinned SimonGMT lemma Poincare.SimonGMT.Chapter02.continuous_normDet in Chapter02/AreaApproximation.lean; that module is not imported by GMT.Ch03.Submission, so the three-line argument is given inline.)
- ENNReal.ofReal is measurable (ENNReal.measurable_ofReal). Hence a is Borel.

4. F is Borel. 1_{B'}·h = 1_{B'}·((φ ∘ ρ̃)·a) because ρ̃ = ρ on B' (Set.indicator_congr with step 2). The right-hand side is Borel (φ, ρ̃ and a are Borel, B' is Borel: Measurable.comp, Measurable.mul, Measurable.indicator). Thus F is Borel.

5. Transport to ℝᵐ × ℝᵏ. toLp : ℝᵐ × ℝᵏ → P is measurable (WithLp.measurable_toLp) and measure preserving from volume on ℝᵐ × ℝᵏ to volume on P (WithLp.volume_preserving_toLp (Rn m) (Rn k)). Hence F ∘ toLp is Borel, and since F is measurable, MeasurePreserving.lintegral_comp gives ∫_P F = ∫_{ℝᵐ×ℝᵏ} F(toLp p) dp.

6. Tonelli. The volume of ℝᵐ × ℝᵏ is Lᵐ ⊗ Lᵏ (Measure.volume_eq_prod) and Lᵏ is σ-finite. As F ∘ toLp is measurable, lintegral_prod gives ∫_{ℝᵐ×ℝᵏ} F(toLp p) d(Lᵐ⊗Lᵏ)(p) = ∫_{ℝᵐ} ∫_{ℝᵏ} F(toLp(y, z)) dz dy; with step 5 this is (ii). Measurable.lintegral_prod_right' applied to F ∘ toLp shows that y ↦ ∫_{ℝᵏ} F(toLp(y, z)) dz is measurable, which is (i). ∎

Appendix (supplementary; the numbered argument above is complete without it). The following tactic script, placed after `theorem Submission.pcoarea_chart_integrand_tonelli : <frozen type> := by` inside `namespace GMT.Ch03` with the Contract's `open` commands and `import GMT.Ch03.Submission`, compiled in the parent's decomposition session (Lean v4.35.0-rc3, Mathlib 25730c7c) with axioms propext, Classical.choice and Quot.sound only:
```lean
  intro m k N ψ Φ hψ B hB hBm φ hφ
  classical
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) := (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)) with hj
  have hB' : MeasurableSet (Φ '' B) :=
    hBm.image_of_continuousOn_injOn (Φ.continuousOn.mono hB) (Φ.injOn.mono hB)
  have hB'Ω : Φ '' B ⊆ Φ.target := by
    rintro _ ⟨u, hu, rfl⟩; exact Φ.map_source (hB hu)
  have hρ : ContinuousOn (ψ ∘ Φ.symm) Φ.target :=
    hψ.comp Φ.continuousOn_symm (fun w hw ↦ Φ.map_target hw)
  have hρm : Measurable (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0)) :=
    hρ.measurable_piecewise continuousOn_const Φ.open_target.measurableSet
  have hnd : Continuous (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) := by
    have heq : (fun M : Rn k →L[ℝ] Rn N ↦ M.toLinearMap.normDet) =
        fun M ↦ Real.sqrt ((M.adjoint ∘L M).det) := by
      funext M
      rw [← M.normDet_sq]
      simpa only [RCLike.ofReal_real_eq_id, id_eq] using (Real.sqrt_sq M.normDet_nonneg).symm
    rw [heq]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  have ha : Measurable (fun w ↦ ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) :=
    ENNReal.measurable_ofReal.comp ((hnd.comp (continuous_id.clm_comp continuous_const)).measurable.comp
      (measurable_fderiv ℝ _))
  have hFeq : (Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) =
      (Φ '' B).indicator (fun w ↦ φ (Φ.target.piecewise (ψ ∘ Φ.symm) (fun _ ↦ 0) w) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet)) := by
    apply Set.indicator_congr
    intro w hw
    simp only [Set.piecewise_eq_of_mem _ _ _ (hB'Ω hw), Function.comp_apply]
  have hFm : Measurable ((Φ '' B).indicator (fun w ↦ φ (ψ (Φ.symm w)) * ENNReal.ofReal (((fderiv ℝ (ψ ∘ Φ.symm) w).comp j).toLinearMap.normDet))) := by
    rw [hFeq]
    exact ((hφ.comp hρm).mul ha).indicator hB'
  have hmp := WithLp.volume_preserving_toLp (Rn m) (Rn k)
  have hFp := hFm.comp (WithLp.measurable_toLp 2 (Rn m × Rn k))
  refine ⟨hFp.lintegral_prod_right', ?_⟩
  rw [← hmp.lintegral_comp hFm, Measure.volume_eq_prod]
  exact lintegral_prod _ hFp.aemeasurable
```

## Key steps

1. Φ(B) is Borel by Lusin–Souslin, and Φ(B) ⊆ Ω.
2. ρ = ψ ∘ Φ⁻¹ is continuous on the open Ω, so Ω.piecewise ρ 0 is Borel and equals ρ on Φ(B).
3. w ↦ ofReal(normDet(Dρ(w) ∘ j)) is Borel: measurable_fderiv, continuity of L ↦ L ∘ j and of normDet = √det(M†M).
4. Hence F = 1_{Φ(B)}·(φ∘ρ̃)·ofReal(normDet(Dρ ∘ j)) is Borel.
5. WithLp.volume_preserving_toLp, Measure.volume_eq_prod and lintegral_prod give ∫_P F = ∫∫ F(toLp(y, z)) dz dy; Measurable.lintegral_prod_right' gives measurability in y.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json  (project d09bc8a18ce60face651f042976e8465f21f0f68, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum of the snapshot copies vs the compiler-package copies (/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c) of NormDet.lean, ProdLp.lean, Lp/MeasurableSpace.lean, Function/Jacobian.lean, Haar/InnerProductSpace.lean, FDeriv/Measurable.lean and of project/GMT/Ch03/Contract.lean vs the workspace Contract (all identical; the package tree is the same Mathlib revision 25730c7c, so the remaining Mathlib files were read there)`
- `grep -n 'theorem\|lemma\|def ' Mathlib/Analysis/InnerProductSpace/NormDet.lean (normDet, normDet_nonneg, ContinuousLinearMap.normDet_sq, normDet_comp_of_finrank_eq, normDet_eq_abs_det, LinearIsometry.normDet_eq_one)`
- `grep -n 'fst|snd|fstL|sndL|inr|linearEquiv|prodContinuousLinearEquiv' Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `sed -n 1,60p Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean (WithLp.measurableSpace, WithLp.borelSpace)`
- `sed -n 150,215p Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean (LinearIsometryEquiv.measurePreserving, WithLp.volume_preserving_toLp)`
- `rg -n 'theorem lintegral_image_eq_lintegral_abs_det_fderiv_mul' -A 8 Mathlib/MeasureTheory/Function/Jacobian.lean`
- `grep -n 'variable|MeasurableSpace|OpensMeasurable' Mathlib/Analysis/Calculus/FDeriv/Measurable.lean (measurable_fderiv context)`
- `per-file grep over Mathlib/Analysis/Calculus, Mathlib/MeasureTheory, Mathlib/Geometry/Manifold/IsManifold: of_local_left_inverse|hasFDerivAt_symm|contDiffAt_symm|lintegral_prod|lintegral_prod_right'|ContinuousOn.measurable_piecewise|lintegral_indicator|setLIntegral_comp_emb|lintegral_comp_emb|EventuallyEq.fderiv_eq|ContDiffOn.differentiableOn|volume_eq_prod|setLIntegral_congr_fun`
- `grep 'continuous_normDet|Measurable.*normDet' Poincare/SimonGMT/Chapter02/*.lean Chapter03/*.lean (found Chapter02/AreaApproximation.lean continuous_normDet; not imported by GMT.Ch03.Submission)`
- `grep -rn 'pcoarea_chart|chart_slice_lintegral|integrand_tonelli|chart_change_of_variables|pointwise_jacobian' snapshot project/ and SimonGMT (no match)`
- `python3 -I scan of dag.json lean_name/theorems of all 200 nodes against the four proposed names (no collision)`
- `python3 -I gen_lean.py: gmt-compare.py contract_scope + lean_contract.validate_lean_statement, then lean ChartFormulaSplitScope.lean (exit 0)`
- `lean ChartFormulaSplitAssembly.lean (#print axioms Submission.pcoarea_formula_on_chart: propext, sorryAx, Classical.choice, Quot.sound)`
- `lean ChartFormulaSplitFull.lean (four real child proofs: propext, Classical.choice, Quot.sound; parent: plus sorryAx from the two sibling stubs)`
- `lean Inst.lean (#synth MeasureSpace/BorelSpace on WithLp 2 (Rn m × Rn k); j z = WithLp.toLp 2 (0, z) by rfl)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Lp/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/Piecewise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/lakefile.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1-chart-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-parametric-coarea-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartFormulaSplitScope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartFormulaSplitAssembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Scratch/ChartFormulaSplitFull.lean`

The snapshot is at project d09bc8a and Mathlib 25730c7c. Its Mathlib sources and Contract.lean are byte-identical to the compiler packages and the workspace. No-match results: the snapshot project and SimonGMT contain no slice, Tonelli-on-WithLp, change-of-variables-into-WithLp or chart-Jacobian lemma for this setting. None of the four proposed names exists anywhere or collides with the 200 DAG nodes. So the four children are new obligations. Every library fact the child proofs cite exists with the stated form in this snapshot. This covers the normDet API (normDet_nonneg, ContinuousLinearMap.normDet_sq, normDet_comp_of_finrank_eq, normDet_eq_abs_det, LinearIsometry.normDet_eq_one), WithLp.prodContinuousLinearEquiv, fstL, borelSpace, volume_preserving_toLp, LinearIsometryEquiv.measurePreserving, lintegral_image_eq_lintegral_abs_det_fderiv_mul (arbitrary integrand), measurable_fderiv (no hypothesis on the function), MeasurableSet.image_of_continuousOn_injOn, ContinuousOn.measurable_piecewise, lintegral_prod, Measurable.lintegral_prod_right', Measure.volume_eq_prod, lintegral_indicator, setLIntegral_congr_fun, MeasurePreserving.setLIntegral_comp_emb, Filter.EventuallyEq.fderiv_eq, HasFDerivAt.unique and congr_of_eventuallyEq, and ContDiffOn.differentiableOn (n ≠ 0). SimonGMT's continuous_normDet (Chapter02/AreaApproximation.lean) is not imported by GMT.Ch03.Submission, so its three-line argument is reproduced inline. Lean results: all four types elaborate in the comparator's Contract scope; the parent assembly proves the exact frozen type from them; and each child was itself proved in full with only propext, Classical.choice and Quot.sound.
