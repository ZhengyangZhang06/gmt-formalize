# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.halfspace_gauss_green-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Step 2 of the supplied parent proof (Gauss–Green for the half-space, Simon Ch. 3, 4.3 (†)), assembled from its three ingredients. Dependencies: hyperplane_param, tangential_halfspace, normal_halfspace. Notation: H := {w : ⟨w, v⟩ > 0}, P_v := (span{v})^⊥, div g := trace Dg, H^m := μHE[m], L^k := Lebesgue measure.

1. v ≠ 0 because |v| = 1. By hyperplane_param there is a linear isometry ι : ℝ^m → ℝ^{m+1} with ⟨ι x, v⟩ = 0 for all x and μHE[m]⌞P_v = ι_# L^m.
2. Orthonormal basis. Let b_j := ι(e_j) for j < m (e_j the standard unit vectors of ℝ^m) and b_m := v. Since ι preserves inner products, ⟨ι e_j, v⟩ = 0 and |v| = 1, the family (b_0, …, b_m) is orthonormal and has m + 1 = dim ℝ^{m+1} members, so it is an orthonormal basis of ℝ^{m+1}.
3. Components. For each j put h_j(w) := ⟨b_j, g(w)⟩. h_j is C¹ (a fixed linear functional composed with g), has compact support (h_j(w) ≠ 0 forces g(w) ≠ 0), and Dh_j(w)(b_j) = ⟨b_j, Dg(w) b_j⟩ (derivative of an inner product with a constant vector).
4. Trace. For an orthonormal basis, trace A = Σ_j ⟨b_j, A b_j⟩ for every linear map A (Mathlib `LinearMap.trace_eq_sum_inner`). Hence div g(w) = Σ_j ⟨b_j, Dg(w) b_j⟩ = Σ_j Dh_j(w)(b_j) for every w.
5. Linearity. Each w ↦ Dh_j(w)(b_j) is continuous with compact support (h_j is C¹ with compact support), hence integrable on H. Therefore ∫_H div g = Σ_j ∫_H Dh_j(w)(b_j) dw.
6. Tangential terms. For j < m, ⟨b_j, v⟩ = ⟨ι e_j, v⟩ = 0, so tangential_halfspace (with P = m + 1, u = b_j, h = h_j) gives ∫_H Dh_j(w)(b_j) dw = 0.
7. Normal term. normal_halfspace (with ι, v and h = h_m = ⟨v, g(·)⟩) gives ∫_H Dh_m(w)(v) dw = −∫_{ℝ^m} ⟨v, g(ι x)⟩ dx.
8. Boundary term. z ↦ ⟨g(z), v⟩ is continuous; integrating it against μHE[m]⌞P_v = ι_# L^m gives ∫_{P_v} ⟨g, v⟩ dH^m = ∫_{ℝ^m} ⟨g(ι x), v⟩ dx (integral against a push-forward measure, Mathlib `integral_map`).
9. By steps 5–8 and symmetry of the real inner product, ∫_H div g = 0 + … + 0 − ∫_{ℝ^m} ⟨g(ι x), v⟩ dx = −∫_{P_v} ⟨g, v⟩ dH^m. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it refers only to the sibling theorem(s) `Submission.codim1_rdo_dg_tma_hyperplane_param`, `Submission.codim1_rdo_dg_tma_tangential_halfspace`, `Submission.codim1_rdo_dg_tma_normal_halfspace` with their frozen types, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_halfspace_gauss_green : ∀ (m : ℕ) (v : Euclid (m + 1)) (g : Euclid (m + 1) → Euclid (m + 1)), ‖v‖ = 1 → ContDiff ℝ 1 g → HasCompactSupport g → ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v}, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), inner ℝ (g z) v ∂μHE[m] := by
  intro m v g hv hg hgc
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hιv, hmap⟩ := Submission.codim1_rdo_dg_tma_hyperplane_param m v hv0
  -- the adapted orthonormal basis (ι e₀, …, ι e_{m-1}, v)
  let b : Fin (m + 1) → Euclid (m + 1) :=
    Fin.lastCases v (fun i => ι (EuclideanSpace.single i (1 : ℝ)))
  have hb_last : b (Fin.last m) = v := by simp [b]
  have hb_cs : ∀ i : Fin m, b (Fin.castSucc i) = ι (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    simp [b]
  have hb : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hb_last, real_inner_self_eq_norm_sq, hv]
      | cast j =>
        rw [hb_last, hb_cs, real_inner_comm, hιv]
        simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        have := j.isLt
        simp
        omega
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [hb_last, hb_cs, hιv]
        simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        have := i.isLt
        simp
        omega
      | cast j =>
        rw [hb_cs, hb_cs, LinearIsometry.inner_map_map, EuclideanSpace.inner_single_left]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Fin.castSucc_inj]
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Euclid (m + 1)) := by simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rw [← coe_basisOfOrthonormalOfCardEqFinrank hb hcard,
      (basisOfOrthonormalOfCardEqFinrank hb hcard).span_eq]
  let B : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)) := OrthonormalBasis.mk hb hsp
  have hB : ∀ i, B i = b i := by
    intro i
    simp [B]
  -- scalar components
  set h : Fin (m + 1) → Euclid (m + 1) → ℝ := fun i w => inner ℝ (b i) (g w) with hhdef
  have hh_cd : ∀ i, ContDiff ℝ 1 (h i) := fun i => contDiff_const.inner ℝ hg
  have hh_cs : ∀ i, HasCompactSupport (h i) := by
    intro i
    exact hgc.mono' (fun w hw => by
      by_contra hgw
      exact hw (by simp [hhdef, image_eq_zero_of_notMem_tsupport hgw]))
  have hfd : ∀ i w, fderiv ℝ (h i) w (b i) =
      inner ℝ (b i) ((fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (b i)) := by
    intro i w
    have hgd : DifferentiableAt ℝ g w := (hg.differentiable one_ne_zero) w
    rw [hhdef]
    simp only
    rw [fderiv_inner_apply ℝ (differentiableAt_const (b i)) hgd]
    simp
  have htr : ∀ w, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = ∑ i, fderiv ℝ (h i) w (b i) := by
    intro w
    rw [LinearMap.trace_eq_sum_inner _ B]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfd, hB]
  have hint : ∀ i, Integrable (fun w => fderiv ℝ (h i) w (b i))
      (volume.restrict {w : Euclid (m + 1) | 0 < inner ℝ w v}) := by
    intro i
    have hc : Continuous (fun w => fderiv ℝ (h i) w (b i)) :=
      ((hh_cd i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun w => fderiv ℝ (h i) w (b i)) :=
      ((hh_cs i).fderiv ℝ).mono' (fun w hw => by
        by_contra hne
        exact hw (by simp [image_eq_zero_of_notMem_tsupport hne]))
    exact (hc.integrable_of_hasCompactSupport hcs).integrableOn
  simp_rw [htr]
  rw [integral_finsetSum _ (fun i _ => hint i), Fin.sum_univ_castSucc]
  have htan : ∀ i : Fin m, ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v},
      fderiv ℝ (h (Fin.castSucc i)) w (b (Fin.castSucc i)) = 0 := by
    intro i
    exact Submission.codim1_rdo_dg_tma_tangential_halfspace (m + 1) v (b (Fin.castSucc i))
      (h (Fin.castSucc i)) (by rw [hb_cs]; exact hιv _) (hh_cd _) (hh_cs _)
  simp_rw [htan, Finset.sum_const_zero, zero_add]
  rw [hb_last]
  have hnorm := Submission.codim1_rdo_dg_tma_normal_halfspace m ι v (h (Fin.last m)) hv hιv
    (hh_cd _) (hh_cs _)
  rw [hnorm, hmap]
  congr 1
  have hcont : Continuous (fun z => inner ℝ (g z) v) := hg.continuous.inner continuous_const
  rw [integral_map ι.continuous.aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [hhdef, hb_last, real_inner_comm]

## Key steps

1. hyperplane_param: an isometry ι : ℝ^m → v^⊥ with H^m⌞v^⊥ = ι_# L^m.
2. (ι e_0, …, ι e_{m−1}, v) is an orthonormal basis, so div g = Σ_j D⟨b_j, g⟩(b_j).
3. tangential_halfspace kills the m terms with b_j ⊥ v.
4. normal_halfspace turns the v-term into −∫ ⟨v, g(ι x)⟩ dx.
5. Push-forward identity: ∫ ⟨g(ι x), v⟩ dx = ∫_{v^⊥} ⟨g, v⟩ dH^m.

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
