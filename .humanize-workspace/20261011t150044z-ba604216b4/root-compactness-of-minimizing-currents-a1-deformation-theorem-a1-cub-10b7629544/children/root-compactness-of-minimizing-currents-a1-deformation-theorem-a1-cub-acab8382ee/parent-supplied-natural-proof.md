# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_trace-a1.div_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof of `cmcdt_cbm_smooth_trace` (product rule for H := vG: ∂_iH_i = (∂_i v)G_i + v ∂_iG_i) together with fact (F1) (div G = trace DG = Σ_i ⟨e_i, DG e_i⟩ = Σ_i ∂_iG_i, via `LinearMap.trace_eq_sum_inner`). It is stated at a single point and assumes only differentiability at that point.

Notation.
- m ∈ ℕ and ℝⁿ := `Euclid (m+1)`. w_i := w.ofLp i is the i-th coordinate (i ∈ Fin (m+1)).
- e_i := EuclideanSpace.single i 1. These are the vectors of the standard orthonormal basis `EuclideanSpace.basisFun (Fin (m+1)) ℝ` (`EuclideanSpace.basisFun_apply`).
- G_i(y) := (G y)_i.

Hypotheses: v : ℝⁿ → ℝ and G : ℝⁿ → ℝⁿ are differentiable at the point x. Claim: v(x)·trace DG(x) = Σ_i D(vG_i)(x)e_i − Dv(x)(G(x)). Here trace DG(x) = `LinearMap.trace ℝ (Euclid (m+1)) (fderiv ℝ G x)` and D(vG_i)(x)e_i = `fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1)`.

1. Coordinates. G_i = π_i ∘ G, where π_i := EuclideanSpace.proj i : ℝⁿ →L[ℝ] ℝ, w ↦ w_i, is continuous linear. By the chain rule (π_i is its own derivative), G_i has derivative π_i ∘ DG(x) at x. In particular DG_i(x)e_i = (DG(x)e_i)_i.
2. Product rule at x. v and G_i are differentiable at x, so D(vG_i)(x) = v(x)·DG_i(x) + G_i(x)·Dv(x) (`HasFDerivAt.mul`). Evaluating at e_i: D(vG_i)(x)e_i = v(x)(DG(x)e_i)_i + G_i(x)·Dv(x)e_i.
3. Trace in the standard orthonormal basis. trace DG(x) = Σ_i ⟨e_i, DG(x)e_i⟩ (`LinearMap.trace_eq_sum_inner` with `EuclideanSpace.basisFun`). Also ⟨e_i, w⟩ = w_i (`EuclideanSpace.inner_single_left` with coefficient 1). Hence trace DG(x) = Σ_i (DG(x)e_i)_i.
4. Expansion of G(x). G(x) = Σ_i G_i(x)e_i: the j-th coordinate of the right side is Σ_i G_i(x)·[j = i] = G_j(x). Since Dv(x) is linear, Dv(x)(G(x)) = Σ_i G_i(x)·Dv(x)e_i.
5. Sum step 2 over i and use steps 3 and 4: Σ_i D(vG_i)(x)e_i = v(x) Σ_i (DG(x)e_i)_i + Σ_i G_i(x) Dv(x)e_i = v(x)·trace DG(x) + Dv(x)(G(x)). Subtracting Dv(x)(G(x)) from both sides gives the claim. ∎

Formalization notes. A scratch build checked the Lean proof below against exactly this frozen type. It used Lean v4.35.0-rc3 and Mathlib 25730c7c, with the declaration inserted into a copy of `GMT/Ch07/Submission.lean` after the contract's `noncomputable section … end` and before `main_theorem`, in namespace `GMT.Ch07` with the contract's `open`s. It needs no imports beyond the frozen header, and `#print axioms` lists only propext, Classical.choice and Quot.sound. Use an explicitly typed `have h : HasFDerivAt (fun y => v y * G y i) (…) x := hv.hasFDerivAt.mul (hGi i)`. Without the type ascription, `HasFDerivAt.mul` elaborates the function as the pointwise product `v * fun y => …`, and `rw [h.fderiv]` then fails to match.

```lean
theorem Submission.cmcdt_cbm_st_div_product : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (x : Euclid (m + 1)), DifferentiableAt ℝ v x → DifferentiableAt ℝ G x → v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = ∑ i, fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) - fderiv ℝ v x (G x) := by
  intro m v G x hv hG
  -- derivative of the coordinate `G_i = proj_i ∘ G`
  have hGi : ∀ i : Fin (m + 1), HasFDerivAt (fun y => G y i)
      ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x)) x := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x hG.hasFDerivAt
  -- product rule, evaluated at `e_i`
  have hprod : ∀ i : Fin (m + 1),
      fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) =
        v x * (fderiv ℝ G x (EuclideanSpace.single i 1)) i +
          G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    intro i
    have h : HasFDerivAt (fun y => v y * G y i)
        (v x • (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x) +
          G x i • fderiv ℝ v x) x := hv.hasFDerivAt.mul (hGi i)
    rw [h.fderiv]
    simp
  -- trace in the standard orthonormal basis
  have htrace : LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      ∑ i, (fderiv ℝ G x (EuclideanSpace.single i 1)) i := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    simp
  -- `G x = ∑ i, (G x)_i e_i`, hence `Dv(x)(G x) = ∑ i, (G x)_i ∂_i v(x)`
  have hexp : G x = ∑ i, G x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hDvG : fderiv ℝ v x (G x) = ∑ i, G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hexp]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [htrace, hDvG, Finset.mul_sum]
  simp only [hprod, Finset.sum_add_distrib]
  ring
```

## Key steps

1. G_i = proj_i ∘ G, so DG_i(x)e_i = (DG(x)e_i)_i.
2. Product rule: D(vG_i)(x)e_i = v(x)(DG(x)e_i)_i + G_i(x)·Dv(x)e_i.
3. trace DG(x) = Σ_i ⟨e_i, DG(x)e_i⟩ = Σ_i (DG(x)e_i)_i (LinearMap.trace_eq_sum_inner, EuclideanSpace.inner_single_left).
4. G(x) = Σ_i G_i(x)e_i, so Dv(x)(G(x)) = Σ_i G_i(x)·Dv(x)e_i.
5. Sum the product rule over i and rearrange.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C <snapshot>/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (matches manifest)`
- `rg -c 'cmcdt_cbm_st_' <snapshot> -g '*.lean' (no match); python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name/theorems fields for the five proposed names (no collision)`
- `rg -n 'theorem volume_preserving_piFinSuccAbove|theorem PiLp.volume_preserving_toLp|theorem integral_prod_symm|theorem MeasurePreserving.setIntegral_preimage_emb|theorem MeasurePreserving.integrableOn_comp_preimage|lemma trace_eq_sum_inner|theorem EuclideanSpace.inner_single_left|theorem norm_apply_le|theorem contDiff_piLp_apply|theorem integral_deriv_eq_sub|theorem integral_mono_interval|theorem norm_integral_le_abs_integral_norm|theorem Integrable.integral_prod_right|theorem forall_iff_succAbove|theorem basisFun_apply' <snapshot>/mathlib/Mathlib -g '*.lean'`
- `grep -n 'def piFinSuccAbove' <snapshot>/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `rg -n 'piFinSuccAbove|insertNth|trace_eq_sum_inner|integral_divergence|integral_prod_symm|volume_preserving_toLp' <snapshot>/project -g '*.lean' (no match) and lake-packages-25730c7c/simongmt -g '*.lean' (only proof-internal uses; euclideanDivergence_eq_sum_inner in Chapter02/BV.lean is a wrapper of LinearMap.trace_eq_sum_inner)`
- `lake env lean /tmp/st-decomp-ch07/final/FromProofs.lean (copy of GMT/Ch07/Submission.lean + the five children + the parent; axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/st-decomp-ch07/final/CompareSim.lean (comparator-style challenges via gmt-compare.py contract_scope); python3 -I verifier/lean_contract.py validate_lean_statement on all six types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/WithLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-10b7629544/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/st-decomp-ch07/final/FromProofs.lean`
- `/tmp/st-decomp-ch07/final/CompareSim.lean`

Nothing in the snapshot can be reused for this node.
- The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace, and Submission.lean is byte-identical to Contract.lean.
- The project has no slicing, Fubini, trace or divergence lemma.
- SimonGMT only wraps LinearMap.trace_eq_sum_inner (euclideanDivergence_eq_sum_inner).

Mathlib 25730c7c supplies every tool used, all within the import closure of GMT.Ch07.Submission:
- volume_preserving_piFinSuccAbove and MeasurableEquiv.piFinSuccAbove;
- PiLp.volume_preserving_toLp;
- MeasurePreserving.setIntegral_preimage_emb and integrableOn_comp_preimage;
- Measure.prod_restrict, integral_prod_symm and Integrable.integral_prod_right;
- intervalIntegral.integral_deriv_eq_sub, integral_mono_interval and norm_integral_le_abs_integral_norm;
- LinearMap.trace_eq_sum_inner, EuclideanSpace.inner_single_left, PiLp.norm_apply_le and contDiff_piLp_apply;
- Fin.forall_iff_succAbove and Fin.succAboveCases.

The five child proofs and the parent assembly compile in a copy of Submission.lean with no extra imports, and #print axioms gives propext, Classical.choice and Quot.sound only. The proposed names cmcdt_cbm_st_* collide with nothing in the snapshot or the DAG.
