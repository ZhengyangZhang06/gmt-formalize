# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.weak_smooth-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 3, “Integration by parts” (Simon Ch. 6, proof of 4.5(2)), specialized to globally Lipschitz functions.

1. The limit u is K-Lipschitz. For x, z ∈ ℝ^d, uniform convergence gives u_k(x) → u(x) and u_k(z) → u(z). So |u(x) − u(z)| = lim_k |u_k(x) − u_k(z)| ≤ K|x − z|. In particular u is continuous.
2. Derivative bounds and measurability. If v : ℝ^d → ℝ is C-Lipschitz, then ‖Dv(y)‖ ≤ C for every y. At points of differentiability this is the Lipschitz bound for the derivative (norm_fderiv_le_of_lipschitz); elsewhere Dv(y) = 0. For each fixed e ∈ ℝ^d, y ↦ Dv(y)[e] is Borel measurable (measurable_fderiv_apply_const).
3. Coordinates. Let e_1, …, e_d be the standard basis of ℝ^d and Ψ_l(y) := Ψ(y)_l. Then Ψ(y) = Σ_l Ψ_l(y) e_l, so Λ(Ψ(y)) = Σ_l Λ(e_l) Ψ_l(y) for every linear functional Λ. Each Ψ_l is Ψ composed with a continuous linear coordinate map, hence C¹. Since support Ψ_l ⊆ support Ψ, Ψ_l has compact support. A C¹ function with compact support has bounded derivative, so Ψ_l is Lipschitz, continuous and integrable.
4. Splitting the integral. Let v be C-Lipschitz. By step 3, Dv(y)[Ψ(y)] = Σ_l Dv(y)[e_l]·Ψ_l(y). Each summand is measurable by step 2 and bounded by C|e_l|·|Ψ_l(y)| = C|Ψ_l(y)|, hence integrable. So ∫ Dv[Ψ] = Σ_l ∫ Dv(y)[e_l]·Ψ_l(y) dy.
5. Integration by parts. Let v be Lipschitz and fix l. By Rademacher's theorem v is differentiable at a.e. y, and there lineDeriv v y e_l = Dv(y)[e_l]. Integration by parts for a Lipschitz function against a Lipschitz compactly supported function (Mathlib LipschitzWith.integral_lineDeriv_mul_eq) then gives
 ∫ Dv(y)[e_l]·Ψ_l(y) dy = ∫ lineDeriv v y e_l · Ψ_l(y) dy = ∫ q_l(y)·v(y) dy,
 where q_l(y) := lineDeriv Ψ_l y (−e_l) = DΨ_l(y)[−e_l], since Ψ_l is differentiable everywhere. The function q_l is continuous because Ψ_l is C¹, and has compact support because DΨ_l does.
6. Apply steps 4–5 with v = u_k (K-Lipschitz by hypothesis) and v = u (K-Lipschitz by step 1). This gives ∫ Du_k[Ψ] = Σ_l ∫ q_l u_k and ∫ Du[Ψ] = Σ_l ∫ q_l u.
7. Convergence of each term. Fix l. By uniform convergence there is N with |u_k(y) − u(y)| ≤ 1 for all k ≥ N and all y. Hence |q_l(y)u_k(y)| ≤ |q_l(y)|(|u(y)| + 1) for k ≥ N. The bound is continuous with compact support, hence integrable, and q_l(y)u_k(y) → q_l(y)u(y) for every y. By dominated convergence, ∫ q_l u_k → ∫ q_l u.
8. Summing the finitely many limits of step 7 and using step 6 gives ∫ Du_k[Ψ] → ∫ Du[Ψ]. For d = 0 the sums are empty and both sides are 0. ∎

Lean realization: compiled during decomposition with the pinned toolchain in the Submission layout, as the body of `theorem Submission.dor_lmbsf_pwl_fderiv_weak_smooth : (frozen lean_statement) := by` inside `namespace GMT.Ch07`. #print axioms reports only propext, Classical.choice and Quot.sound. Extra imports: Mathlib.Analysis.Calculus.Rademacher.
```lean
  intro d K us u Ψ hus hU hΨ hΨc
  have hu : LipschitzWith K u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hU.tendsto_at x).dist (hU.tendsto_at y))
      (Eventually.of_forall fun k => (hus k).dist_le_mul x y)
  set e : Fin d → Euclid d := fun l => EuclideanSpace.single l 1 with he
  set g : Fin d → Euclid d → ℝ := fun l y => Ψ y l with hg
  have hg_smooth : ∀ l, ContDiff ℝ 1 (g l) := fun l =>
    (EuclideanSpace.proj l : Euclid d →L[ℝ] ℝ).contDiff.comp hΨ
  have hg_supp : ∀ l, HasCompactSupport (g l) := fun l =>
    hΨc.comp_left (g := fun v : Euclid d => v l) (by simp)
  have hdecomp : ∀ (L : Euclid d →L[ℝ] ℝ) (x : Euclid d), L x = ∑ l, L (e l) * x l := by
    intro L x
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp [map_sum, map_smul, e, EuclideanSpace.basisFun_apply, mul_comm]
  set q : Fin d → Euclid d → ℝ := fun l y => lineDeriv ℝ (g l) y (-(e l)) with hq
  have hq_eq : ∀ l, q l = fun y => fderiv ℝ (g l) y (-(e l)) := fun l => funext fun y =>
    ((hg_smooth l).differentiable one_ne_zero y).lineDeriv_eq_fderiv
  have hq_cont : ∀ l, Continuous (q l) := by
    intro l
    rw [hq_eq l]
    exact ((hg_smooth l).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hq_supp : ∀ l, HasCompactSupport (q l) := by
    intro l
    rw [hq_eq l]
    exact ((hg_supp l).fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euclid d →L[ℝ] ℝ => L (-(e l)))
      (by simp)
  have hsum : ∀ (v : Euclid d → ℝ) (C : NNReal), LipschitzWith C v →
      ∫ y, fderiv ℝ v y (Ψ y) = ∑ l, ∫ y, q l y * v y := by
    intro v C hv
    have h1 : (fun y => fderiv ℝ v y (Ψ y)) = fun y => ∑ l, fderiv ℝ v y (e l) * g l y := by
      funext y
      exact hdecomp _ _
    rw [h1, integral_finset_sum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      obtain ⟨D, hD⟩ := (hg_smooth l).lipschitzWith_of_hasCompactSupport (hg_supp l) one_ne_zero
      rw [← hv.integral_lineDeriv_mul_eq hD (hg_supp l) (e l)]
      apply integral_congr_ae
      filter_upwards [hv.ae_differentiableAt] with y hy
      rw [hy.lineDeriv_eq_fderiv]
    · intro l _
      have hgi : Integrable (g l) :=
        (hg_smooth l).continuous.integrable_of_hasCompactSupport (hg_supp l)
      refine Integrable.bdd_mul (c := C * ‖e l‖) hgi
        (measurable_fderiv_apply_const ℝ v (e l)).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
  rw [hsum u K hu]
  have hk : (fun k => ∫ y, fderiv ℝ (us k) y (Ψ y)) = fun k => ∑ l, ∫ y, q l y * us k y := by
    funext k
    exact hsum (us k) K (hus k)
  rw [hk]
  refine tendsto_finset_sum _ fun l _ => ?_
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖q l y‖ * (‖u y‖ + 1))
  · exact Eventually.of_forall fun k => ((hq_cont l).mul (hus k).continuous).aestronglyMeasurable
  · rw [Metric.tendstoUniformly_iff] at hU
    filter_upwards [hU 1 one_pos] with k hk
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    gcongr
    have h1 := hk y
    rw [dist_eq_norm] at h1
    have h2 : ‖us k y‖ ≤ ‖u y‖ + ‖u y - us k y‖ := by
      have := norm_sub_norm_le (us k y) (u y)
      rw [norm_sub_rev] at this
      linarith
    linarith
  · exact ((hq_cont l).norm.mul (hu.continuous.norm.add continuous_const)).integrable_of_hasCompactSupport
      (hq_supp l).norm.mul_right
  · exact Eventually.of_forall fun y => ((hU.tendsto_at y).const_mul (q l y))
```

## Key steps

1. The uniform limit u of the K-Lipschitz u_k is K-Lipschitz.
2. Write Dv[Ψ] = Σ_l Dv[e_l]·Ψ_l; each term is integrable because ‖Dv‖ ≤ Lip(v) and Ψ_l is continuous with compact support.
3. Rademacher gives Dv[e_l] = lineDeriv v · e_l a.e.; integrate by parts against the Lipschitz compactly supported Ψ_l (LipschitzWith.integral_lineDeriv_mul_eq) to get ∫ q_l v.
4. Dominated convergence with bound |q_l|(|u| + 1) gives ∫ q_l u_k → ∫ q_l u.
5. Sum over the d coordinates.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; cmp snapshot project/GMT/Ch07/Contract.lean against workspace GMT/Ch07/Contract.lean (identical); cmp snapshot mathlib Analysis/Calculus/Rademacher.lean, Analysis/Normed/Lp/SmoothApprox.lean, MeasureTheory/Covering/Besicovitch.lean, Geometry/Manifold/PartitionOfUnity.lean, Analysis/Calculus/FDeriv/Basic.lean, Geometry/Euclidean/Volume/Measure.lean against lake-packages-25730c7c/mathlib (all identical)`
- `python3 -I scan of dag.json: frozen types of dor_lmbsf_piece_weak_limit and dor_lmbsf_density_directions (exact string match); regex 'lineDeriv|Rademacher|weak|McShane|extend_real|density point|Besicovitch|ae_tendsto_measure_inter_div|integral_lineDeriv_mul_eq|dense_hasCompactSupport|areaJacobian|area formula|uniformly Lipschitz|TendstoUniformly' over node statements; lean_name collision check for the seven dor_lmbsf_pwl_* names (1523 nodes, none)`
- `grep -n 'integral_area_formula_of_injective_derivative|weighted_area_formula_of_injective_derivative|map_withDensity_areaJacobian_eq|integrableOn_image_iff_integrableOn_areaJacobian_smul|areaJacobianAt_eq_zero_iff_not_injective|measurable_areaJacobianAt|def areaJacobianAt|areaJacobianAt_nonneg' simongmt/Poincare/SimonGMT/Chapter02`
- `rg/grep -n 'integral_lineDeriv_mul_eq|ae_differentiableAt|HasFDerivWithinAt.lim|ae_tendsto_measure_inter_div|exist_eLpNorm_sub_le|dense_hasCompactSupport_contDiff|exists_contDiff_zero_iff_one_iff_of_isClosed|lipschitzWith_of_nnnorm_fderiv_le|ContDiff.lipschitzWith_of_hasCompactSupport|norm_fderiv_le_of_lipschitz|measurable_fderiv|NormedRing.inverse_continuousAt|ContinuousLinearMap.isUnit_iff_bijective|euclideanHausdorffMeasure_eq_volume|exists_cthickening_subset_open|cthickening_subset_thickening|tendsto_integral_filter_of_dominated_convergence|Integrable.smul_bdd|Integrable.bdd_mul|setIntegral_indicator|setIntegral_eq_integral_of_forall_compl_eq_zero|setIntegral_congr_ae|ae_withDensity_iff|ae_of_ae_map' in the snapshot/package mathlib`
- `python3 -I verifier gmt-compare.contract_scope(Contract.lean, 'GMT.Ch07.main_theorem') and lean_contract.validate_lean_statement on the seven child types`
- `git show proof-workspace/gmt-ch07/20261011t150044z-ba604216b4/theorems/solutions/root-density-and-tangent-cones-a1-blowup-scaling-a1-testform-correspondence-a1-7af5165c95:GMT/Ch07/Submission.lean (child layout: theorem Submission.X inside namespace GMT.Ch07)`
- `toolchains/lean-4.35.0-rc3-linux/bin/lake env lean on /tmp/pwl-decomp/{Types,Assembly,Probe2,ProtoA1,ProtoA,ProtoB,ProtoE,ProtoC,ProtoF,ProtoD,All,Layout,LayoutCmp}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-eead01d0c5/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-eead01d0c5/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pwl-decomp/Types.lean`
- `/tmp/pwl-decomp/Assembly.lean`
- `/tmp/pwl-decomp/All.lean`
- `/tmp/pwl-decomp/Layout.lean`
- `/tmp/pwl-decomp/LayoutCmp.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot Contract.lean and the cited mathlib files are byte-identical to the workspace and package trees.

No existing or accepted DAG declaration has any of the seven child types. The closest node, dor_lmb_fcd_jacobian_weak_continuity, is unaccepted and states a different, Jacobian-minor result. So all seven children get fresh dor_lmbsf_pwl_* names, none used among the 1523 nodes.

Library facts that suffice, all confirmed by compilation:
- SimonGMT Chapter02: integral_area_formula_of_injective_derivative, integrableOn_image_iff_integrableOn_areaJacobian_smul, map_withDensity_areaJacobian_eq, areaJacobianAt_eq_zero_iff_not_injective, measurable_areaJacobianAt.
- Mathlib: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, MemLp.exist_eLpNorm_sub_le, Besicovitch.ae_tendsto_measure_inter_div, HasFDerivWithinAt.lim (in this version it takes dlim : d → 0), exists_contDiff_zero_iff_one_iff_of_isClosed, lipschitzWith_of_nnnorm_fderiv_le, NormedRing.inverse_continuousAt, ContinuousLinearMap.isUnit_iff_bijective, EuclideanSpace.euclideanHausdorffMeasure_eq_volume.

Lean checks:
- All seven child types validate and elaborate in the comparator scope.
- The parent assembly compiles with only standard axioms.
- All seven children are fully proven in the Submission layout with only standard axioms, and `exact Submission.X` closes each comparator challenge.
