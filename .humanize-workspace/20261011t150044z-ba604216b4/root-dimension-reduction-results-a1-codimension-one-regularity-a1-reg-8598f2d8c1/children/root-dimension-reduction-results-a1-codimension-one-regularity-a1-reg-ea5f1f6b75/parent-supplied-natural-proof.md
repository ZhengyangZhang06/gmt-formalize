# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.rescaled_gauss_green-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Extracted from step 3 of the supplied parent proof (Simon Ch. 3, 4.3 (†), the change of variable x → λ_k x of Simon's (8)): 'φ(z) := g((z − y)/r) is C¹ with compact support, tsupport φ ⊆ y + r·tsupport g … ⊆ D, and div φ(z) = r^{-1}(div g)((z − y)/r). By (GG) and the substitution z = y + rw (Jacobian r^{m+1}; F_r = {w : y + rw ∈ F}): r^m ∫_{F_r} div g dL = ∫_F div φ dL = −∫ ⟨g((z − y)/r), ν(z)⟩ dμ(z).' Notation: A(w) := y + r w, T := div g = trace Dg, F_{y,r} := A^{-1}(F) = {w : y + r w ∈ F}, L := L^{m+1}.

1. A is an affine homeomorphism of ℝ^{m+1} (r ≠ 0) with inverse A^{-1}(z) = r^{-1}(z − y). Put φ := g ∘ A^{-1}, i.e. φ(z) = g(r^{-1}(z − y)).
2. φ is C¹ (a C¹ map composed with an affine map). Since A is a homeomorphism, tsupport φ = A(tsupport g); this set is compact (continuous image of a compact set), so φ has compact support, and tsupport φ ⊆ D because A(w) = y + r w ∈ D for every w ∈ tsupport g by hypothesis.
3. Chain rule: Dφ(z) = Dg(r^{-1}(z − y)) ∘ (r^{-1} Id) = r^{-1} Dg(r^{-1}(z − y)); by linearity of the trace, div φ(z) = r^{-1} T(r^{-1}(z − y)).
4. Applying (GG) to φ and taking the constant r^{-1} out of the integral: r^{-1} ∫_F T(r^{-1}(z − y)) dz = −∫ ⟨g(r^{-1}(z − y)), ν(z)⟩ dμ(z).
5. Change of variables. F_{y,r} is Borel, being the preimage of the Borel set F under the continuous map A. Let Ψ := 1_F · T(r^{-1}(· − y)). For every w, 1_{F_{y,r}}(w) T(w) = Ψ(r w + y): both sides vanish unless y + r w ∈ F, and then T(r^{-1}((y + r w) − y)) = T(w). By the scaling law of Lebesgue measure, ∫ f(r w) dw = |r^{m+1}|^{-1} ∫ f(x) dx for every function f (Mathlib `Measure.integral_comp_smul`; dim ℝ^{m+1} = m + 1), and by translation invariance ∫ Ψ(x + y) dx = ∫ Ψ(x) dx. Hence ∫_{F_{y,r}} T = ∫ Ψ(r w + y) dw = r^{-(m+1)} ∫ Ψ = r^{-(m+1)} ∫_F T(r^{-1}(z − y)) dz, that is, ∫_F T(r^{-1}(z − y)) dz = r^{m+1} ∫_{F_{y,r}} T.
6. Substituting step 5 into step 4: r^{-1} r^{m+1} ∫_{F_{y,r}} T = r^m ∫_{F_{y,r}} T = −∫ ⟨g(r^{-1}(z − y)), ν⟩ dμ. Multiplying by r^{-m} (r > 0) gives r^{-m} ∫ ⟨g(r^{-1}(z − y)), ν(z)⟩ dμ(z) = −∫_{F_{y,r}} div g dL. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it uses no other child, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_rescaled_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r : ℝ) (g : Euclid (m + 1) → Euclid (m + 1)), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → ContDiff ℝ 1 g → HasCompactSupport g → (∀ w ∈ tsupport g, y + r • w ∈ D) → (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ = -∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by
  intro m D F μ ν y r g hF hGG hr hg hgc hD
  set T : Euclid (m + 1) → ℝ := fun w =>
    LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
    with hTdef
  -- the affine homeomorphism A w = y + r • w and its inverse
  let A : Euclid (m + 1) ≃ₜ Euclid (m + 1) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y)
  have hA : ∀ w, A w = y + r • w := fun w => rfl
  have hAsymm : ∀ z, A.symm z = r⁻¹ • (z - y) := by
    intro z
    apply A.injective
    rw [A.apply_symm_apply, hA, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  set φ : Euclid (m + 1) → Euclid (m + 1) := fun z => g (r⁻¹ • (z - y)) with hφdef
  have hφA : φ = g ∘ A.symm := by
    funext z
    simp [hφdef, hAsymm]
  have hφ : ContDiff ℝ 1 φ := hg.comp (by fun_prop)
  have hφts : tsupport φ = A '' tsupport g := by
    rw [hφA, tsupport_comp_eq_preimage _ A.symm, A.preimage_symm]
  have hφc : HasCompactSupport φ := by
    rw [HasCompactSupport, hφts]
    exact hgc.isCompact.image A.continuous
  have hφD : tsupport φ ⊆ D := by
    rw [hφts]
    rintro _ ⟨w, hw, rfl⟩
    rw [hA]
    exact hD w hw
  have hfd : ∀ z, fderiv ℝ φ z = r⁻¹ • fderiv ℝ g (r⁻¹ • (z - y)) := by
    intro z
    have hin : HasFDerivAt (fun z : Euclid (m + 1) => r⁻¹ • (z - y))
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) z :=
      ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const y).const_smul (r⁻¹ : ℝ)
    have hgd := ((hg.differentiable one_ne_zero) (r⁻¹ • (z - y))).hasFDerivAt
    have h2 : HasFDerivAt φ ((fderiv ℝ g (r⁻¹ • (z - y))).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1)))) z := hgd.comp z hin
    rw [h2.fderiv]
    ext x
    simp
  have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = r⁻¹ * T (r⁻¹ • (z - y)) := by
    intro z
    rw [hfd]
    simp [hTdef, map_smul]
  have hGG' := hGG φ hφ hφc hφD
  simp_rw [htr] at hGG'
  rw [integral_const_mul] at hGG'
  -- change of variables z = y + r • w
  have hcv : ∫ z in F, T (r⁻¹ • (z - y)) =
      r ^ (m + 1) * ∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
    have hpre : MeasurableSet ((fun w => y + r • w) ⁻¹' F) := hF.preimage (by fun_prop)
    rw [← integral_indicator hF, ← integral_indicator hpre]
    set Ψ : Euclid (m + 1) → ℝ := F.indicator (fun z => T (r⁻¹ • (z - y))) with hΨ
    have h1 : (fun w => ((fun w => y + r • w) ⁻¹' F).indicator T w) =
        fun w => Ψ (r • w + y) := by
      funext w
      rw [add_comm (r • w) y]
      by_cases hw : y + r • w ∈ F
      · rw [indicator_of_mem (show w ∈ (fun w => y + r • w) ⁻¹' F from hw), hΨ,
          indicator_of_mem hw]
        simp [smul_smul, inv_mul_cancel₀ hr.ne']
      · rw [indicator_of_notMem (show w ∉ (fun w => y + r • w) ⁻¹' F from hw), hΨ,
          indicator_of_notMem hw]
    rw [h1, Measure.integral_comp_smul volume (fun x => Ψ (x + y)) r,
      integral_add_right_eq_self Ψ y]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    rw [abs_of_pos (inv_pos.2 (pow_pos hr _))]
    field_simp
  rw [hcv] at hGG'
  have hrm : (r ^ m) ≠ 0 := pow_ne_zero _ hr.ne'
  have key : ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ =
      -(r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, T w) := by
    have : r⁻¹ * (r ^ (m + 1) * ∫ w in (fun w => y + r • w) ⁻¹' F, T w) =
        r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
      rw [pow_succ]
      field_simp
    rw [this] at hGG'
    linarith
  rw [key]
  field_simp

## Key steps

1. φ := g(r^{-1}(· − y)) is C¹ with compact support and tsupport φ = y + r·tsupport g ⊆ D.
2. div φ(z) = r^{-1} div g(r^{-1}(z − y)) by the chain rule and linearity of the trace.
3. (GG) for φ, then the substitution z = y + r w with Jacobian r^{m+1}.
4. r^m ∫_{F_{y,r}} div g = −∫ ⟨g(r^{-1}(z − y)), ν⟩ dμ; divide by r^m.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07 rev-parse HEAD; git -C /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib rev-parse HEAD`
- `python3 scans of dag.json: frozen lean_statement of the selected node and of siblings normal_average_ae-a1, cutoff_estimates-a1, blowup_halfspace-a1; accepted nodes grepped for μHE[, ᗮ, LinearMap.trace, symmDiff, Ioi and smooth-approximation statements; collision check of the 10 names codim1_rdo_dg_tma_* (0 hits among 993 nodes)`
- `grep -rn codim1_rdo_dg_tma GMT/ and lake-packages-25730c7c/simongmt (no match)`
- `sed -n 1,420p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE API)`
- `rg in snapshot mathlib: trace_eq_sum_inner, integral_Ioi_of_hasDerivAt_of_tendsto, HasCompactSupport.integral_Ioi_deriv_eq, hasDerivAt_integral_of_dominated_loc_of_deriv_le, measurePreserving_repr_symm, LinearIsometryEquiv.measurePreserving, setIntegral_comp_smul_of_pos, integral_comp_smul, integral_mul_right_eq_self, volume_preserving_piFinSuccAbove, snocEquiv, OrthonormalBasis.sum_repr_symm, integral_prod, support_fderiv_subset, contDiff_convolution_left, support_convolution_subset, exists_contDiff_tsupport_subset, finrank_orthogonal_span_singleton, basisOfOrthonormalOfCardEqFinrank, integral_inner, dist_normed_convolution_le, Submodule.measurePreserving_measurableEquivProd`
- `#check probes after import GMT.Ch07.Submission (/tmp/tma-split-check/Probe*.lean): ContDiffBump.normed, ContDiffBump.dist_normed_convolution_le, integral_inner and EuclideanSpace.volume_preserving_measurableEquiv are unknown constants in the contract's import closure; (volume : Measure (Euclid m × ℝ)) = (volume : Measure (Euclid m)).prod volume holds by rfl`
- `sed -n 540,760p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt (printed proof of Simon Ch. 3, 4.3)`
- `lake env lean -DautoImplicit=false /tmp/tma-split-check/Full.lean (exit 0; #print axioms for the 10 children and the selected node)`
- `sed -n runtime.py _decompose, _dependency_problem, _existing_lean_name_problem, _solve_children; cat swarm-project.json (max_depth 6, max_children 12)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-8598f2d8c1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-8598f2d8c1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/tma-split-check/Full.lean`
- `/tmp/tma-split-check/Assembly.lean`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`

Pins: snapshot manifest project b4d606db… and Mathlib 25730c7c… equal the workspace HEAD and .lake/packages/mathlib. Library: snapshot Mathlib supplies everything the children need: Isometry.map_euclideanHausdorffMeasure (Geometry/Euclidean/Volume/Measure.lean:141), EuclideanSpace.euclideanHausdorffMeasure_eq_volume (:187), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), HasCompactSupport.integral_Ioi_deriv_eq (IntegralEqImproper.lean:820), hasDerivAt_integral_of_dominated_loc_of_deriv_le (ParametricIntegral.lean:286), OrthonormalBasis.measurePreserving_repr_symm (Haar/InnerProductSpace.lean:114), setIntegral_comp_smul_of_pos (Haar/NormedSpace.lean:148), volume_preserving_piFinSuccAbove (Constructions/Pi.lean:818), integral_prod (Integral/Prod.lean:440), support_fderiv_subset (FDeriv/Const.lean:379), HasCompactSupport.contDiff_convolution_left (ContDiff/Convolution.lean:427), support_convolution_subset (Convolution.lean:670), exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45), finrank_orthogonal_span_singleton (Projection/FiniteDimensional.lean:125). ContDiffBump.dist_normed_convolution_le (BumpFunction/Convolution.lean:71) and integral_inner (Function/L2Space.lean:89) exist in the snapshot but are not in the contract's import closure, so the child proofs avoid them. No Mathlib, SimonGMT or accepted-DAG declaration states the half-space Gauss–Green formula, the rescaled Gauss–Green identity, the normal-defect estimate or the C¹-to-C⁰ extension; accepted candidates dimred_rpd_bilipschitz_image_measure, pit_setIntegral_range_linear and dgcr_stc_exists_normalized_mollifier were inspected and not needed, so no reuse. The 10 names codim1_rdo_dg_tma_* have no match among 993 DAG nodes, GMT/ or SimonGMT. Lean: /tmp/tma-split-check/Full.lean elaborates all 10 child types in the frozen contract scope, proves each with axioms propext, Classical.choice, Quot.sound, and proves the selected frozen type (byte-identical to dag.json) from them plus the three sibling stubs with exact frozen types (sorryAx only from the stubs). Runtime: depth 5 < max_depth 6, so the children are depth-6 leaves; 10 ≤ max_children 12.
