# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_parametric_coarea-a1.chart_formula-a1.pointwise_jacobian-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 1 (derivatives of the chart) and 7 (Jacobian identity). Hypothesis (FJ) is exactly the conclusion of the sibling flat_jacobian (Submission.pcoarea_flat_jacobian_identity m k N); the parent discharges it with that sibling.

Fix u ∈ O and put w := Φ(u) ∈ Ω (Φ.map_source); then Φ⁻¹(w) = u (Φ.left_inv). Let T := DΦ(u) = fderiv ℝ Φ u : ℝⁿ →L[ℝ] P and Λ := DΦ⁻¹(w) = fderiv ℝ Φ.symm w : P →L[ℝ] ℝⁿ.

1. Differentiability. Φ is C¹ on the open set O ∋ u, Φ⁻¹ is C¹ on the open set Ω ∋ w and ψ is C¹ on O ∋ u, so (ContDiffOn.differentiableOn with 1 ≠ 0, DifferentiableOn.differentiableAt with IsOpen.mem_nhds) Φ is differentiable at u, Φ⁻¹ at w, and ψ at u.

2. Λ ∘L T = id. By the chain rule (HasFDerivAt.comp, Φ⁻¹ being differentiable at Φ(u) = w), Φ⁻¹ ∘ Φ has derivative Λ ∘L T at u. The maps Φ⁻¹ ∘ Φ and id agree on the neighbourhood O of u (Φ.left_inv), so Φ⁻¹ ∘ Φ also has derivative id at u (HasFDerivAt.congr_of_eventuallyEq applied to hasFDerivAt_id). Uniqueness of derivatives (HasFDerivAt.unique) gives Λ ∘L T = id.

3. T ∘L Λ = id. Φ has derivative T at Φ⁻¹(w) = u, so Φ ∘ Φ⁻¹ has derivative T ∘L Λ at w; Φ ∘ Φ⁻¹ agrees with id on the neighbourhood Ω of w (Φ.right_inv), and as in step 2, T ∘L Λ = id.

4. T is bijective (as a linear map ℝⁿ → P): if T v = T v′ then v = Λ(T v) = Λ(T v′) = v′ by step 2; every p ∈ P equals T(Λ p) by step 3.

5. (T v).fst = DG(u) v for every v. G agrees with x ↦ (Φ x).fst on the neighbourhood O of u (hypothesis), so DG(u) = D(fst ∘ Φ)(u) (Filter.EventuallyEq.fderiv_eq). As fst = WithLp.fstL 2 ℝ (Rn m) (Rn k) is a continuous linear map, the chain rule gives D(fst ∘ Φ)(u) = fstL ∘L T (HasFDerivAt.fderiv). Evaluating at v: DG(u) v = (T v).fst.

6. Put E := Λ ∘L j (as a linear map ℝᵏ → ℝⁿ). For every z, T(E z) = (T ∘L Λ)(j z) = j z = toLp(0, z) by step 3.

7. Chain rule for ρ. Since ψ is differentiable at Φ⁻¹(w) = u and Φ⁻¹ at w, fderiv_comp gives Dρ(w) = Dψ(Φ⁻¹ w) ∘L Λ = Dψ(u) ∘L Λ. Hence the underlying linear map of Dρ(Φ u) ∘L j is (Dψ u) ∘ₗ E (composition of continuous linear maps is associative and toLinearMap preserves composition, definitionally).

8. Apply (FJ) with A := Dψ(u), Γ := DG(u), T := DΦ(u) and E (all as linear maps); its three hypotheses are steps 4, 5 and 6. It yields normDet(Dψ(u) ∘ E)·normDet(T) = normDet(Dψ(u) ∘ ι_{ker DG(u)})·normDet(DG(u)*). By step 7 the first factor equals normDet(Dρ(Φ u) ∘ j), which is the claim. ∎

Appendix (supplementary; the numbered argument above is complete without it). The following tactic script, placed after `theorem Submission.pcoarea_chart_pointwise_jacobian : <frozen type> := by` inside `namespace GMT.Ch03` with the Contract's `open` commands and `import GMT.Ch03.Submission`, compiled in the parent's decomposition session (Lean v4.35.0-rc3, Mathlib 25730c7c) with axioms propext, Classical.choice and Quot.sound only:
```lean
  intro m k N ψ G Φ hψ hΦ hΦs hfst hFJ u hu
  set j : Rn k →L[ℝ] WithLp 2 (Rn m × Rn k) := (WithLp.prodContinuousLinearEquiv 2 ℝ (Rn m) (Rn k)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Rn m) (Rn k)) with hj
  have hw : Φ u ∈ Φ.target := Φ.map_source hu
  have hleft : Φ.symm (Φ u) = u := Φ.left_inv hu
  have hΦd : DifferentiableAt ℝ Φ u :=
    (hΦ.differentiableOn one_ne_zero u hu).differentiableAt (Φ.open_source.mem_nhds hu)
  have hΦsd : DifferentiableAt ℝ Φ.symm (Φ u) :=
    (hΦs.differentiableOn one_ne_zero _ hw).differentiableAt (Φ.open_target.mem_nhds hw)
  have hψd : DifferentiableAt ℝ ψ u :=
    (hψ.differentiableOn one_ne_zero u hu).differentiableAt (Φ.open_source.mem_nhds hu)
  set T := fderiv ℝ Φ u with hT
  set Λ := fderiv ℝ Φ.symm (Φ u) with hΛ
  have hLT : Λ.comp T = ContinuousLinearMap.id ℝ _ := by
    have h1 : HasFDerivAt (Φ.symm ∘ Φ) (Λ.comp T) u := hΦsd.hasFDerivAt.comp u hΦd.hasFDerivAt
    have h2 : HasFDerivAt (Φ.symm ∘ Φ) (ContinuousLinearMap.id ℝ _) u := by
      apply (hasFDerivAt_id u).congr_of_eventuallyEq
      filter_upwards [Φ.open_source.mem_nhds hu] with x hx
      exact Φ.left_inv hx
    exact h1.unique h2
  have hTL : T.comp Λ = ContinuousLinearMap.id ℝ _ := by
    have hΦd' : HasFDerivAt Φ T (Φ.symm (Φ u)) := by rw [hleft]; exact hΦd.hasFDerivAt
    have h1 : HasFDerivAt (Φ ∘ Φ.symm) (T.comp Λ) (Φ u) := hΦd'.comp (Φ u) hΦsd.hasFDerivAt
    have h2 : HasFDerivAt (Φ ∘ Φ.symm) (ContinuousLinearMap.id ℝ _) (Φ u) := by
      apply (hasFDerivAt_id (Φ u)).congr_of_eventuallyEq
      filter_upwards [Φ.open_target.mem_nhds hw] with x hx
      exact Φ.right_inv hx
    exact h1.unique h2
  have hbij : Function.Bijective (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) := by
    constructor
    · intro v v' h
      have h' : Λ (T v) = Λ (T v') := congrArg Λ h
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, hLT] at h'
      simpa using h'
    · intro p
      refine ⟨Λ p, ?_⟩
      show T (Λ p) = p
      rw [← ContinuousLinearMap.comp_apply, hTL]
      rfl
  have hG : fderiv ℝ G u = (WithLp.fstL 2 ℝ (Rn m) (Rn k)).comp T := by
    have heq : G =ᶠ[𝓝 u] (fun x ↦ (Φ x).fst) := by
      filter_upwards [Φ.open_source.mem_nhds hu] with x hx
      exact (hfst x hx).symm
    rw [heq.fderiv_eq]
    exact ((WithLp.fstL 2 ℝ (Rn m) (Rn k)).hasFDerivAt.comp u hΦd.hasFDerivAt).fderiv
  have hfstT : ∀ v, ((T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) v).fst =
      (fderiv ℝ G u : Rn (m + k) →ₗ[ℝ] Rn m) v := by
    intro v; rw [hG]; rfl
  let E : Rn k →ₗ[ℝ] Rn (m + k) := ((Λ.comp j : Rn k →L[ℝ] Rn (m + k)) : Rn k →ₗ[ℝ] Rn (m + k))
  have hE : ∀ z, (T : Rn (m + k) →ₗ[ℝ] WithLp 2 (Rn m × Rn k)) (E z) = WithLp.toLp 2 (0, z) := by
    intro z
    show T (Λ (j z)) = _
    rw [← ContinuousLinearMap.comp_apply, hTL]
    rfl
  have hchain : fderiv ℝ (ψ ∘ Φ.symm) (Φ u) = (fderiv ℝ ψ u).comp Λ := by
    have hψd' : DifferentiableAt ℝ ψ (Φ.symm (Φ u)) := by rw [hleft]; exact hψd
    rw [fderiv_comp (Φ u) hψd' hΦsd, hleft]
  have key := hFJ (fderiv ℝ ψ u) (fderiv ℝ G u) T E hbij hfstT hE
  rw [hchain]
  exact key
```

## Key steps

1. Φ, Φ⁻¹ and ψ are differentiable at u, Φ(u) and u (C¹ on open sets).
2. Chain rule plus local identities Φ⁻¹∘Φ = id near u and Φ∘Φ⁻¹ = id near Φ(u): DΦ⁻¹(Φ u) and DΦ(u) are mutually inverse, so DΦ(u) is bijective.
3. G = fst ∘ Φ near u, so DG(u) = fstL ∘ DΦ(u), i.e. (DΦ(u) v).fst = DG(u) v.
4. E := DΦ⁻¹(Φ u) ∘ j satisfies DΦ(u)(E z) = toLp(0, z), and Dρ(Φ u) ∘ j = Dψ(u) ∘ E by the chain rule.
5. Hypothesis (FJ) with A = Dψ(u), Γ = DG(u), T = DΦ(u), E gives the identity.

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
