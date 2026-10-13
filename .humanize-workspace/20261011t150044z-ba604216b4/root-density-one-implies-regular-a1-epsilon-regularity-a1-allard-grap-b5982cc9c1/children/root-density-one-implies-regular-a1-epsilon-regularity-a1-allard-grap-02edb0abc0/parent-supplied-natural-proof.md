# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.hs_operator_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 3, the inequality ‖p_x − p_S‖ ≤ |p_x − p_S| (operator norm ≤ Hilbert–Schmidt norm) used for the cross term.

1. Write v = Σ_i v_i e_i with v_i := v(i) the coordinates of v (expansion in the orthonormal basis EuclideanSpace.basisFun); then |v|² = Σ_i v_i² (EuclideanSpace.norm_sq_eq).
2. By linearity Av = Σ_i v_i A e_i, so the triangle inequality and homogeneity of the norm give |Av| ≤ Σ_i |v_i|·|A e_i|.
3. By the Cauchy–Schwarz inequality for finite sums, (Σ_i |v_i|·|A e_i|)² ≤ (Σ_i |v_i|²)(Σ_i |A e_i|²) = |v|²·Σ_i |A e_i|².
4. Both sides of the inequality in step 2 are nonnegative, so squaring it and using step 3: |Av|² ≤ (Σ_i |v_i|·|A e_i|)² ≤ (Σ_i |A e_i|²)·|v|². ∎

Appendix — machine-checked Lean realization (verified during decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, inside `namespace GMT.Ch07` of the frozen Submission scope; `#print axioms` gives [propext, Classical.choice, Quot.sound]; the numbered argument above is the proof, this block only records one verified formalization of it):
```lean
theorem Submission.dorag_th_norm_apply_sq_le_hs : ∀ (P : ℕ) (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P), ‖A v‖ ^ 2 ≤ (∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v‖ ^ 2 := by
  intro P A v
  have hv : v = ∑ i : Fin P, v i • EuclideanSpace.single i (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v
    simpa using this.symm
  have hAv : A v = ∑ i : Fin P, v i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  have h1 : ‖A v‖ ≤ ∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAv]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_smul]
  have h2 : (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin P, |v i| ^ 2) * ∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin P, |v i| ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  calc ‖A v‖ ^ 2 ≤ (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = _ := by rw [h3, mul_comm]
```

## Key steps

1. Expand v = Σ v_i e_i, so Av = Σ v_i A e_i and |v|² = Σ v_i².
2. Triangle inequality: |Av| ≤ Σ |v_i||A e_i|.
3. Cauchy–Schwarz for finite sums and squaring give |Av|² ≤ (Σ|A e_i|²)|v|².

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'tilt|cutoff|cut-off|hilbert.?schmidt|trace' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07  (only the frozen tangentialDivergence definition, Contract.lean:264-267, and README.md:59; no tilt/cut-off/Hilbert–Schmidt lemma)`
- `rg -n -i 'TiltExcessHeight' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean  (Prop definition at :240, used only in main_theorem := by sorry at :461)`
- `rg -n 'theorem (integral_withDensity_eq_integral_smul|setLIntegral_congr_fun|setLIntegral_le_lintegral|setLIntegral_const|lintegral_add_right|lintegral_const_mul|withDensity_absolutelyContinuous|ofReal_integral_eq_lintegral_ofReal)' and 'lemma setLIntegral_eq_of_support_subset' in the snapshot Mathlib`
- `rg -n 'theorem fderiv_of_notMem_tsupport|support_fderiv_subset' Analysis/Calculus/FDeriv/Const.lean; rg -n 'IsProj.trace' LinearAlgebra/Trace.lean; rg -n trace Analysis/InnerProductSpace/Trace.lean  (in the snapshot Mathlib)`
- `rg -n 'starProjection_(apply_eq_zero_iff|eq_self_iff)|sub_starProjection_mem_orthogonal|isIdempotentElem_starProjection|starProjection_isSymmetric|norm_starProjection_apply_le' Analysis/InnerProductSpace/Projection/Basic.lean  (in the snapshot Mathlib)`
- `grep -rn 'bounded_above_of_compact_support|integrableOn_const|comp_aestronglyMeasurable₂|apply_continuousLinearMap|AEStronglyMeasurable.inner' MeasureTheory Topology Analysis  (in the snapshot Mathlib; AEStronglyMeasurable.inner lives in MeasureTheory/Function/StronglyMeasurable/Inner.lean, which is outside the Submission's import closure)`
- `grep -n HasApproximateTangentSpaceAt /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean  (simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197, pinned by /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json)`
- `rg -n -i 'cutoff|trace|tilt' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare  (Chapter04/FirstVariation.lean trace_starProjection :122 and trace_radialEndomorphism :135; Chapter05/Basic.lean has no tilt-height lemma)`
- `#check @Poincare.SimonGMT.Chapter04.trace_starProjection after import GMT.Ch07.Submission  (unknown identifier: not in the Submission's import closure); #check of LinearMap.trace_eq_sum_inner, LinearMap.trace_smulRight, Real.smoothTransition, contDiffAt_norm, Finset.sum_mul_sq_le_sq_mul_sq (all available)`
- `python3: lean_name collision scan of the 5 dorag_th_* names over every workspace's dag.json, nodes/*/*.json and .humanize/math-wiki/*.md, plus grep of GMT/*/Submission.lean  (no hits)`
- `python3 -I lean_contract.validate_lean_statement on the 5 child lean_statements; lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on 5 comparator-format modules Challenge_<key>.lean`
- `lean Final.lean / Final2.lean (5 children proved as theorem Submission.<name> with the frozen types; #print axioms; parent from children plus sibling stub; exact Submission.<name> comparator checks); lean Assembly.lean, EProof.lean, BCD.lean, AProof.lean, Full.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b5982cc9c1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/tiltheight-decomp-4Xk0Bt/Final.lean`
- `/tmp/tiltheight-decomp-4Xk0Bt/Final2.lean`
- `/tmp/tiltheight-decomp-4Xk0Bt/Assembly.lean`
- `/tmp/tiltheight-decomp-4Xk0Bt/EProof.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, which is the compiler context of every child type.

Nothing in the snapshot proves the tilt–height estimate or any child, so no comparator-accepted declaration can be reused:
- GMT/Ch07 contains only the frozen definitions (tangentialDivergence, firstVariation, approxTangentPlane).
- GMT/Ch05 states TiltExcessHeightEstimate only behind main_theorem := by sorry, for a different varifold type.
- SimonGMT Chapter05/Basic.lean has no tilt-height lemma.
- SimonGMT Chapter04/FirstVariation.lean:122 (trace_starProjection) is outside the Submission's import closure, so child B re-derives trace p_T = dim T.

Pinned facts the proofs rely on:
- SimonGMT Chapter03/Rectifiable.lean:102: HasApproximateTangentSpaceAt includes finrank = n, which gives dim T_xM = n μ-a.e. in E.
- Snapshot Mathlib: integral_withDensity_eq_integral_smul (ContinuousLinearMap.lean:251), setLIntegral_eq_of_support_subset (Lebesgue/Basic.lean:545), fderiv_of_notMem_tsupport (FDeriv/Const.lean:375), LinearMap.trace_eq_sum_inner (InnerProductSpace/Trace.lean:25), starProjection_apply_eq_zero_iff (Projection/Basic.lean:689) and Continuous.comp_aestronglyMeasurable₂ (AEStronglyMeasurable.lean:263) all exist.

Lean checks:
- All 5 child types elaborate in comparator scope and pass the lexical validator.
- Each child is proved as Submission.<name> with axioms propext, Classical.choice and Quot.sound only.
- The exact frozen parent type follows from A, E and the sibling dorag_approxTangent_starProjection_aesm, with axioms propext, Classical.choice and Quot.sound only.
- None of the 5 dorag_th_* names collides with any reservation.
