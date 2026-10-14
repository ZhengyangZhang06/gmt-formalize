# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.orthogonal_fubini-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Extracted from step 2 of the supplied parent proof (Simon Ch. 3, 4.3 (†)): 'The coordinate map Ψ(z) := (⟨z, b_i⟩)_{i ≤ m+1} is a linear isometry E → ℝ^{m+1} preserving Lebesgue measure (Mathlib OrthonormalBasis.measurePreserving_repr) … Use Fubini for the product decomposition ℝ^{m+1} = ℝ^m × ℝ of Lebesgue measure (only measure preservation is used, not the product norm).' Notation: ℝ^k := Euclid k with Lebesgue measure L^k (= volume); the volume of ℝ^m × ℝ is the product measure L^m ⊗ L^1; Θ(x, s) := ι x + s v.

1. Adapted orthonormal basis. Let e_0, …, e_{m−1} be the standard unit vectors of ℝ^m. Define b_j := ι(e_j) for j < m (index Fin.castSucc j) and b_m := v (index Fin.last m). Since ι preserves inner products, ⟨b_i, b_j⟩ = ⟨e_i, e_j⟩ = δ_ij for i, j < m; ⟨b_j, b_m⟩ = ⟨ι e_j, v⟩ = 0 by hypothesis; ⟨b_m, b_m⟩ = |v|^2 = 1. So (b_0, …, b_m) is an orthonormal family of m + 1 = dim ℝ^{m+1} vectors. An orthonormal family is linearly independent, and a linearly independent family with dim-many vectors spans, so it is an orthonormal basis B of ℝ^{m+1} (Mathlib `basisOfOrthonormalOfCardEqFinrank`, `OrthonormalBasis.mk`).
2. Φ := (B.repr)^{-1} : ℝ^{m+1} → ℝ^{m+1}, c ↦ Σ_j c_j b_j, is a linear isometric equivalence of finite-dimensional inner product spaces and therefore preserves Lebesgue measure (`OrthonormalBasis.measurePreserving_repr_symm`).
3. Coordinates. Let S : ℝ^m × ℝ → ℝ^{m+1}, S(x, s) := (x_0, …, x_{m−1}, s). S is measure preserving from L^m ⊗ L^1 to L^{m+1}: it is the composition of (i) (x, s) ↦ (x viewed as a plain tuple in Fin m → ℝ, s), measure preserving because L^m corresponds to the product Lebesgue measure on Fin m → ℝ (`PiLp.volume_preserving_ofLp`) and a product of measure-preserving maps is measure preserving (`MeasurePreserving.prod`); (ii) the swap (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ) (`Measure.measurePreserving_swap`); (iii) the inverse of the measurable equivalence (Fin (m+1) → ℝ) ≃ ℝ × (Fin m → ℝ) that splits off the last coordinate, which preserves the product Lebesgue measures (`volume_preserving_piFinSuccAbove` at `Fin.last m`, inverted) and sends (s, x) to `Fin.snoc x s`; (iv) the identification (Fin (m+1) → ℝ) → ℝ^{m+1} (`PiLp.volume_preserving_toLp`).
4. Identification of Θ. For every (x, s): Φ(S(x, s)) = Σ_{j<m} x_j b_j + s b_m (splitting off the last summand, `Fin.sum_univ_castSucc`) = Σ_{j<m} x_j ι(e_j) + s v = ι(Σ_{j<m} x_j e_j) + s v = ι x + s v, by linearity of ι and x = Σ_j x_j e_j.
5. Hence Θ = Φ ∘ S is a composition of measure-preserving maps; so Θ is measurable and Θ_#(L^m ⊗ L^1) = L^{m+1}, i.e. Θ is measure preserving. ∎

Appendix (formal check; the numbered proof above is the argument). The Lean proof below of exactly this frozen statement was compiled in the pinned project (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract's opens (`open Filter Function Set MeasureTheory Metric`, `open scoped ENNReal Topology`, `open Poincare.SimonGMT.Chapter06`), as part of one file containing all ten children; it uses no other child, and `#print axioms` reports propext, Classical.choice, Quot.sound.

theorem Submission.codim1_rdo_dg_tma_orthogonal_fubini : ∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → MeasurePreserving (fun p : Euclid m × ℝ => ι p.1 + p.2 • v) volume volume := by
  intro m ι v hv hιv
  -- the adapted orthonormal basis
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
      | last => simp [hb_last, hv]
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
  -- coordinates: Euclid m × ℝ → EuclideanSpace ℝ (Fin (m+1))
  let S : Euclid m × ℝ → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun p => WithLp.toLp 2 (Fin.snoc (WithLp.ofLp p.1) p.2)
  have hS : MeasurePreserving S volume volume := by
    have h1 : MeasurePreserving (fun p : Euclid m × ℝ => (WithLp.ofLp p.1, p.2))
        ((volume : Measure (Euclid m)).prod (volume : Measure ℝ))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) :=
      (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
    have h2 : MeasurePreserving (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      Measure.measurePreserving_swap
    have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
    have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
    have := h4.comp (h3.comp (h2.comp h1))
    convert this using 1
    funext p
    simp [S, MeasurableEquiv.piFinSuccAbove]
    rfl
  have hΦ : MeasurePreserving (B.repr.symm : EuclideanSpace ℝ (Fin (m + 1)) → Euclid (m + 1))
      volume volume := B.measurePreserving_repr_symm
  have := hΦ.comp hS
  convert this using 1
  funext p
  simp only [comp_apply, S]
  rw [← OrthonormalBasis.sum_repr_symm, Fin.sum_univ_castSucc]
  simp only [hB, hb_last, hb_cs, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr p.1]
  simp [map_sum, map_smul]

## Key steps

1. (ι e_0, …, ι e_{m−1}, v) is an orthonormal basis B of ℝ^{m+1}.
2. (B.repr)^{-1} preserves Lebesgue measure.
3. (x, s) ↦ (x_0, …, x_{m−1}, s) preserves the product Lebesgue measure (ofLp × id, swap, piFinSuccAbove^{-1}, toLp).
4. (B.repr)^{-1}(x_0, …, x_{m−1}, s) = ι x + s v, so Θ is a composition of measure-preserving maps.

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
