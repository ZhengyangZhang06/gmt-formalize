# Parent-supplied natural-language proof

- Parent DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1`
- Child DAG node: `root.harmonic_approximation-a1.boundary_layer_estimate-a1.l2_sq_norm_tendsto-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and role. This is the Minkowski step ("By Minkowski the L^2 norms converge") of step 3 of the supplied proof of the parent theorem w12_ball_boundary_layer_estimate. The parent uses it three times: for f on the annulus B_s \ B_{rs}, for f on B_s, and for the vector-valued g on B_s, with the smooth approximants phi_j, resp. grad phi_j, of the sibling w12_ball_smooth_approximation. It is the continuity of the L^2 norm, stated for lintegrals of squared extended norms. The pinned Mathlib has no lemma that turns eLpNorm (phi_j - f) -> 0 into convergence of the norms eLpNorm phi_j -> eLpNorm f. tendsto_Lp_iff_tendsto_eLpNorm, tendsto_Lp_iff_tendsto_eLpNorm'' and their relatives characterize convergence in Lp, not convergence of the norms.

Hypotheses: (alpha, mu) is a measure space and E is a normed additive commutative group. f : alpha -> E satisfies MemLp f 2 mu, i.e. f is mu-a.e. strongly measurable with eLpNorm f 2 mu < infinity. phi_j : alpha -> E (j in N) are mu-a.e. strongly measurable, and int ‖phi_j - f‖ₑ^2 dmu -> 0 in [0, infinity]. Claim: int ‖phi_j‖ₑ^2 dmu -> int ‖f‖ₑ^2 dmu in [0, infinity]. All integrals are lintegrals.

Proof.

1. Norm-square identity. For h : alpha -> E write N(h) := eLpNorm h 2 mu, in [0, infinity]. If h is mu-a.e. strongly measurable, then int ‖h‖ₑ^2 dmu = N(h)^2. This is eLpNorm_nnreal_pow_eq_lintegral with p = 2 : NNReal, which reads N(h)^(2:R) = int ‖h‖ₑ^(2:R) dmu, combined with ENNReal.rpow_two (x^(2:R) = x^2) on both sides. Measurability matters here: for non-measurable h, eLpNorm is infinity by definition.

2. Finiteness and measurability. By MemLp.aestronglyMeasurable f is mu-a.e. strongly measurable, and c := N(f) < infinity by MemLp.eLpNorm_lt_top. Each phi_j - f is mu-a.e. strongly measurable as a difference of such functions.

3. The errors tend to 0. Let a_j := N(phi_j - f). By steps 1 and 2, a_j^2 = int ‖phi_j - f‖ₑ^2 dmu -> 0. The map x -> x^(1/2) is continuous on [0, infinity] (ENNReal.continuous_rpow_const), (a_j^2)^(1/2) = a_j (ENNReal.rpow_natCast, ENNReal.rpow_mul) and 0^(1/2) = 0. Hence a_j -> 0.

4. Minkowski. Let b_j := N(phi_j). Since phi_j = f + (phi_j - f) and f = phi_j - (phi_j - f), the triangle inequality in L^2 (eLpNorm_add_le and eLpNorm_sub_le with 1 <= 2) gives
b_j <= c + a_j and c <= b_j + a_j.
The second inequality is equivalent to c - a_j <= b_j for truncated subtraction in [0, infinity] (tsub_le_iff_right).

5. Squeeze. c + a_j -> c + 0 = c, and c - a_j -> c - 0 = c by ENNReal.Tendsto.sub. Its side condition (one of the two limits c, 0 is finite) holds because c ≠ infinity; the finiteness of the limit 0 would also do. By the squeeze theorem (tendsto_of_tendsto_of_tendsto_of_le_of_le), b_j -> c.

6. Conclusion. Squaring is continuous on [0, infinity] (ENNReal.Tendsto.pow), so b_j^2 -> c^2. By step 1 (phi_j and f are a.e. strongly measurable), b_j^2 = int ‖phi_j‖ₑ^2 dmu and c^2 = int ‖f‖ₑ^2 dmu. This is the claim. QED

Formalization note. During decomposition the following Lean proof of exactly the frozen statement compiled against the pinned Mathlib (lake env lean, namespace GMT.Ch05.Submission after `import GMT.Ch05.Submission`). `#print axioms` showed only propext, Classical.choice and Quot.sound.

theorem ble_lintegral_sq_tendsto_of_l2_tendsto : ∀ {α : Type} [MeasurableSpace α] {E : Type} [NormedAddCommGroup E] (μ : Measure α) (f : α → E) (φ : ℕ → α → E), MemLp f 2 μ → (∀ j, AEStronglyMeasurable (φ j) μ) → Tendsto (fun j => ∫⁻ x, ‖φ j x - f x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) → Tendsto (fun j => ∫⁻ x, ‖φ j x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ)) := by
  intro α _ E _ μ f φ hf hφ hlim
  have hfm : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  -- `∫⁻ ‖h‖ₑ ^ 2 = (eLpNorm h 2 μ) ^ 2` for a.e.-strongly measurable `h`.
  have hsq : ∀ h : α → E, AEStronglyMeasurable h μ →
      ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ = eLpNorm h 2 μ ^ 2 := by
    intro h hh
    have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hh
    simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at this
    simp only [ENNReal.rpow_two] at this
    exact this.symm
  -- Notation: `a j` is the error norm, `b j` the approximant norm, `c` the limit norm.
  set a : ℕ → ℝ≥0∞ := fun j => eLpNorm (φ j - f) 2 μ with ha
  set b : ℕ → ℝ≥0∞ := fun j => eLpNorm (φ j) 2 μ with hb
  set c : ℝ≥0∞ := eLpNorm f 2 μ with hc
  have hc_top : c ≠ ∞ := hf.eLpNorm_lt_top.ne
  -- `a j → 0`.
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have h2 : Tendsto (fun j => a j ^ 2) atTop (𝓝 0) := by
      exact hlim.congr fun j => hsq _ ((hφ j).sub hfm)
    have h3 : Tendsto (fun j => (a j ^ 2) ^ (1 / 2 : ℝ)) atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp h2
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr fun j => ?_
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  -- Triangle inequalities.
  have hup : ∀ j, b j ≤ c + a j := by
    intro j
    have : φ j = f + (φ j - f) := by abel
    calc b j = eLpNorm (f + (φ j - f)) 2 μ := by rw [hb]; dsimp only; rw [← this]
      _ ≤ eLpNorm f 2 μ + eLpNorm (φ j - f) 2 μ := eLpNorm_add_le (by norm_num)
  have hlow : ∀ j, c ≤ b j + a j := by
    intro j
    have : f = φ j - (φ j - f) := by abel
    calc c = eLpNorm (φ j - (φ j - f)) 2 μ := by rw [hc]; rw [← this]
      _ ≤ eLpNorm (φ j) 2 μ + eLpNorm (φ j - f) 2 μ := eLpNorm_sub_le (by norm_num)
  -- `b j → c`.
  have hbc : Tendsto b atTop (𝓝 c) := by
    have hU : Tendsto (fun j => c + a j) atTop (𝓝 (c + 0)) := tendsto_const_nhds.add ha0
    have hL : Tendsto (fun j => c - a j) atTop (𝓝 (c - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds ha0 (Or.inl hc_top)
    rw [add_zero] at hU
    rw [tsub_zero] at hL
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hL hU
      (fun j => tsub_le_iff_right.2 (hlow j)) hup
  -- Square and convert back.
  have := ENNReal.Tendsto.pow (n := 2) hbc
  rw [hsq f hfm]
  exact this.congr fun j => (hsq _ (hφ j)).symm

## Key steps

1. For a.e.-strongly measurable h, int ‖h‖ₑ^2 = eLpNorm(h, 2)^2
2. eLpNorm(phi_j - f) -> 0 because x -> x^(1/2) is continuous on [0, infinity]
3. Minkowski: eLpNorm(phi_j) <= eLpNorm(f) + eLpNorm(phi_j - f) and eLpNorm(f) - eLpNorm(phi_j - f) <= eLpNorm(phi_j)
4. The squeeze gives eLpNorm(phi_j) -> eLpNorm(f); squaring is continuous on [0, infinity]

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean`
- `rg -n "theorem (lintegral_comp_smul|setLIntegral_comp_smul|lintegral_comp_inv_smul|lintegral_comp_mul|setLIntegral_comp_mul)" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem (integral_comp_smul|integral_comp_inv_smul|setIntegral_comp_smul|map_smul|addHaar_smul|addHaar_image_homothety|lintegral_comp|addHaar_preimage_smul|map_addHaar_smul|addHaar_smul_of_nonneg)" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Haar/ <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/`
- `rg -n "theorem (lintegral_map_equiv|setLIntegral_map_equiv|lintegral_smul_measure|setLIntegral_map|lintegral_map_le)" <snapshot>/mathlib/Mathlib; rg -n "theorem (lintegral_lintegral_swap|lintegral_prod_swap|lintegral_prod)\b" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem (eLpNorm_eq_lintegral_rpow_enorm|eLpNorm_add_le|eLpNorm_sub_le|MemLp.eLpNorm_lt_top|lintegral_rpow_enorm_eq_rpow_eLpNorm')" <snapshot>/mathlib/Mathlib/MeasureTheory/Function`
- `rg -n "theorem [a-zA-Z_.']*tendsto[a-zA-Z_.']*eLpNorm[a-zA-Z_.']*|theorem [a-zA-Z_.']*eLpNorm[a-zA-Z_.']*tendsto[a-zA-Z_.']*" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem (lintegral_iUnion_mono|tendsto_setLIntegral_of_monotone|restrict_iUnion_apply_eq_iSup|setLIntegral_iUnion_of_directed|lintegral_iUnion_le)" <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n "theorem (ENNReal.lintegral_mul_le_Lp_mul_Lq|lintegral_mul_le_Lp_mul_Lq|integral_mul_le_Lp_mul_Lq_of_nonneg)" <snapshot>/mathlib/Mathlib`
- `rg -n "^(theorem|lemma|def)" <snapshot>/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean; rg -n "theorem toDual_symm_apply" <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `rg -n "protected theorem Tendsto.(const_mul|mul_const|pow)|protected theorem continuous_pow" <snapshot>/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean; rg -n "theorem (ContDiff.of_le|ContDiff.continuous_fderiv|measurable_fderiv)\b" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem integral_eq_sub_of_hasDerivAt\b|theorem HasFDerivAt.comp_hasDerivAt\b|lemma eLpNorm_nnreal_pow_eq_lintegral|theorem rpow_two\b|protected theorem Tendsto.sub\b|theorem finrank_euclideanSpace_fin\b|theorem Measurable.lintegral_prod_right'|theorem lintegral_add_left\b|theorem abs_real_inner_le_norm\b|theorem restrict_map\b" <snapshot>/mathlib/Mathlib`
- `rg -n "smooth_annulus|lintegral_sq_tendsto|annulus_estimate" <snapshot>/mathlib/Mathlib <snapshot>/project; python scan of dag.json lean_name fields (105 nodes) and nodes/*/decomposition*.json proposed lean_name fields (150)`
- `lake env lean /tmp/ble-decomp-check/proj/CheckAll.lean (frozen Submission olean + (A) axiom + child 1 sorry + child 2 proved + parent assembled + #print axioms); also CheckC2.lean, CheckDil.lean, CheckPP.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Gradient/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-harmonic-approximation-a1-boundary-layer-estimate-a1/parent-child-handoff.json`
- `/tmp/ble-decomp-check/proj/CheckAll.lean`
- `/tmp/ble-decomp-check/proj/CheckDil.lean`

Pinned snapshot: project ea5607598f3133b40a13241f2e51517a8c6423cd, Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). The snapshot's GMT/Ch05/Contract.lean and Submission.lean are byte-identical to the workspace copies, and to the copy compiled in the scratch project (cmp; Contract sha256 c966f51e…). IsW12WithGradient is at Contract.lean:227.

No usable match (gaps the children fill):
- There is no lintegral dilation lemma. lintegral_comp_smul and setLIntegral_comp_smul do not exist; only the Bochner versions integral_comp_smul and setIntegral_comp_smul_of_pos exist (Haar/NormedSpace.lean:92,148).
- There is no lemma turning eLpNorm (φ_j - f) → 0 into convergence of eLpNorm φ_j or of ∫⁻‖φ_j‖ₑ^2. The tendsto*eLpNorm hits are only Lp-convergence characterizations (LpSpace/Complete.lean:113-145) and convergence in measure (ConvergenceInMeasure.lean:406-452).
- The proposed names have no match in the snapshot, among the 105 reserved DAG declarations, or among the 150 names proposed in decomposition files.

Usable lemmas, all verified to exist and cited in the child proofs:
- Haar measure scaling: Measure.map_addHaar_smul (Lebesgue/EqHaar.lean:336) and finrank_euclideanSpace_fin (PiL2.lean:205).
- Change of variables: MeasurableEmbedding.lintegral_map and lintegral_map_equiv (Lebesgue/Map.lean:94), restrict_map (Measure/Restrict.lean:890), lintegral_smul_measure (Lebesgue/Basic.lean:418).
- Tonelli and measurability: lintegral_lintegral_swap (Measure/Prod.lean:1071), Measurable.lintegral_prod_right' (Prod.lean:123), lintegral_add_left (Lebesgue/Add.lean:316).
- Set lintegrals: lintegral_mono_set (Lebesgue/Basic.lean:98), setLIntegral_iUnion_of_directed (Lebesgue/Basic.lean:668).
- Lp seminorms: eLpNorm_nnreal_pow_eq_lintegral (LpSeminorm/Defs.lean:169; eLpNorm is ∞ for non-a.e.-strongly-measurable functions, so measurability hypotheses are needed), eLpNorm_add_le and eLpNorm_sub_le (TriangleInequality.lean:54,145), MemLp.eLpNorm_lt_top (LpSeminorm/Basic.lean:36).
- ENNReal limits and powers: ENNReal.Tendsto.const_mul, Tendsto.sub, Tendsto.pow (ENNReal/Lemmas.lean:354,309,448), ENNReal.rpow_two (Pow/NNReal.lean:701).
- Calculus: ContDiff.of_le and ContDiff.continuous_fderiv (ContDiff/Defs.lean:1140,1271), inner_gradient_left (Gradient/Basic.lean:292), intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148), HasFDerivAt.comp_hasDerivAt (Deriv/Comp.lean:374).
- Cauchy-Schwarz: ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202).

Lean checks (lake env lean, scratch project with the frozen Submission olean):
- CheckAll.lean (exit 0) proves the parent's exact frozen type from child 1 (sorry), child 2 (fully proved) and (A) (axiom). Axioms: parent {propext, sorryAx, Classical.choice, Quot.sound, w12_ball_smooth_approximation}; child 2 {propext, Classical.choice, Quot.sound}.
- CheckDil.lean proves the dilation formula ∫⁻ x in E, F (t • x) = ofReal ((t^n)⁻¹) * ∫⁻ y in t • E, F y for any F, E and t > 0. It requires open scoped Pointwise.

An independent reviewer agent re-ran these checks and confirmed both child proofs and the type faithfulness.
