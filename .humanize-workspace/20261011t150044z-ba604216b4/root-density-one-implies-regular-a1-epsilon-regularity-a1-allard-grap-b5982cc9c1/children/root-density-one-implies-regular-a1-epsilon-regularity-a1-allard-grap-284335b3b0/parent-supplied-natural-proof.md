# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.test_field_divergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 2 (Simon, proof of Ch. 5, Lemma 2.1: the test field X = ζ²(x)x′ and the computation of div_M X, book/chapter-05.txt, lines 222–247). Write q := I − p_S (a continuous linear map) and w(y) := (y − ξ) − p_S(y − ξ) = q(y − ξ).

1. w is affine, w(y) = q(y) − q(ξ), hence differentiable at every point with Dw(x) = q.
2. g(y) := ζ(y)² is differentiable at x with Dg(x) = 2ζ(x)·Dζ(x) (chain rule for t ↦ t²).
3. Product rule for a scalar function times a vector function: X = g·w is differentiable at x and, for every h ∈ ℝ^P, DX(x)h = g(x)·Dw(x)h + (Dg(x)h)·w(x) = ζ(x)² q h + 2ζ(x)(Dζ(x)h)·w(x). In operator form DX(x) = ζ(x)²·q + (2ζ(x)Dζ(x)) ⊗ w(x), where (L ⊗ u)(h) := L(h)u is the rank-one map (Mathlib: ContinuousLinearMap.smulRight). As X is differentiable at x, fderiv ℝ X x is this operator.
4. Composing with p_T (linear): p_T∘DX(x) = ζ(x)²·(p_T∘q) + (2ζ(x)Dζ(x)) ⊗ p_T w(x), because p_T(L(h)u) = L(h)·p_T u.
5. The trace is linear and trace(L ⊗ u) = L(u): in the standard basis, Σ_i ⟨e_i, L(e_i)u⟩ = Σ_i L(e_i)u_i = L(Σ_i u_i e_i) = L(u) (Mathlib: LinearMap.trace_smulRight).
6. Therefore trace(p_T∘DX(x)) = ζ(x)²·trace(p_T∘(I − p_S)) + 2ζ(x)·Dζ(x)[p_T((x − ξ) − p_S(x − ξ))], which is the claim. ∎

Appendix — machine-checked Lean realization (verified during decomposition: Lean v4.35.0-rc3, Mathlib 25730c7c, inside `namespace GMT.Ch07` of the frozen Submission scope; `#print axioms` gives [propext, Classical.choice, Quot.sound]; the numbered argument above is the proof, this block only records one verified formalization of it):
```lean
theorem Submission.dorag_th_trace_comp_fderiv_test_field : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)) (ζ : Euclid P → ℝ) (ξ x : Euclid P), DifferentiableAt ℝ ζ x → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))) x).toLinearMap) = ζ x ^ 2 * LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) + 2 * ζ x * fderiv ℝ ζ x (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
  intro P T S ζ ξ x hζ
  set q : Euclid P →L[ℝ] Euclid P := ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection with hq
  have hw : HasFDerivAt (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ)) q x := by
    have h1 : HasFDerivAt (fun y : Euclid P => y - ξ) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const ξ
    have h3 : HasFDerivAt (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ))
        (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection.comp (ContinuousLinearMap.id ℝ (Euclid P))) x :=
      h1.sub (S.starProjection.hasFDerivAt.comp x h1)
    rwa [ContinuousLinearMap.comp_id] at h3
  have hg : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    have := hζ.hasFDerivAt.pow 2
    convert this using 1
    ext v
    simp
    try ring
  have hX : HasFDerivAt (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ)))
      (ζ x ^ 2 • q + ((2 * ζ x) • fderiv ℝ ζ x).smulRight ((x - ξ) - S.starProjection (x - ξ))) x :=
    hg.smul hw
  rw [hX.fderiv]
  have hcomp : T.starProjection.toLinearMap ∘ₗ (ζ x ^ 2 • q +
        ((2 * ζ x) • fderiv ℝ ζ x).smulRight ((x - ξ) - S.starProjection (x - ξ))).toLinearMap =
      ζ x ^ 2 • (T.starProjection.toLinearMap ∘ₗ q.toLinearMap) +
        (2 * ζ x) • (fderiv ℝ ζ x).toLinearMap.smulRight
          (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
    ext v
    simp [map_smul, smul_smul]
  rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight]
  simp [smul_eq_mul, hq]
  try ring
```

## Key steps

1. w(y) = (y − ξ) − p_S(y − ξ) is affine with Dw = I − p_S; D(ζ²)(x) = 2ζ(x)Dζ(x).
2. Product rule: DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x).
3. p_T∘DX(x) = ζ(x)² p_T(I − p_S) + (2ζ(x)Dζ(x)) ⊗ p_T w(x); trace is linear and trace(L ⊗ u) = L(u).

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
