# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_height_estimate-a1`
- Child DAG node: `root.tilt_excess_height_estimate-a1.smooth_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the cutoff in step 2 of the supplied proof (Simon 5.2.1 proof: "ζ ≡ 1 in B_{ρ/2}, ζ ≡ 0 outside B_ρ, |∇ζ| <= 3/ρ"), constructed explicitly. In Lean, ContDiff ℝ (⊤ : ℕ∞) means C^infinity.

Let S := Real.smoothTransition. Mathlib (Analysis/SpecialFunctions/SmoothTransition.lean) gives:
- S is C^infinity (Real.smoothTransition.contDiff);
- 0 <= S <= 1 (nonneg, le_one);
- S(s) = 0 for s <= 0 (zero_of_nonpos);
- S(s) = 1 for s >= 1 (one_of_one_le).

1. The bump g. Define g(t) := S(12(t − 1/2)) · S(12(1 − t)) for t ∈ R.
  - g is C^infinity, as a product of compositions of C^infinity maps with affine maps.
  - 0 <= g <= 1.
  - g(t) = 0 for t <= 1/2 (first factor) and for t >= 1 (second factor).
  - g(t) = 1 for 7/12 <= t <= 11/12, where both arguments are >= 1.

2. The normalizing constant. Let c := ∫_{1/2}^{1} g(s) ds. Since g >= 0 on [1/2, 1] and g = 1 on [7/12, 11/12] ⊆ [1/2, 1], monotonicity of the integral gives c >= ∫_{7/12}^{11/12} 1 ds = 1/3 > 0. (In fact c = 5/12 by the symmetry S(s) + S(1 − s) = 1, but only c >= 1/3 is used.)

3. The profile φ. Define φ(t) := 1 − c^{-1} ∫_{1/2}^{t} g(s) ds (oriented interval integral).
  - g is continuous, so the fundamental theorem of calculus (intervalIntegral.integral_hasDerivAt_right) shows φ is differentiable everywhere with φ'(t) = −c^{-1} g(t).
  - φ' = −c^{-1} g is C^infinity, so φ is C^infinity (contDiff_infty_iff_deriv).
  - |φ'(t)| = c^{-1} g(t) <= c^{-1} <= 3 for all t, so φ is 3-Lipschitz by the mean value theorem.

4. Values of φ.
  - If t <= 1/2: g = 0 on [t, 1/2], so ∫_{1/2}^{t} g = −∫_{t}^{1/2} g = 0 and φ(t) = 1.
  - If t >= 1: ∫_{1/2}^{t} g = ∫_{1/2}^{1} g + ∫_{1}^{t} g = c + 0, so φ(t) = 0.
  - If 1/2 <= t <= 1: g >= 0 gives 0 <= ∫_{1/2}^{t} g <= ∫_{1/2}^{1} g = c, so 0 <= φ(t) <= 1.
  Hence 0 <= φ <= 1 on R.

5. The cutoff. Given m, ξ ∈ R^m and ρ > 0, define ζ(x) := φ(‖x − ξ‖/ρ). By step 4:
  - 0 <= ζ <= 1;
  - if x ∈ closedBall ξ (ρ/2), then ‖x − ξ‖/ρ <= 1/2 and ζ(x) = 1;
  - if dist(x, ξ) = ‖x − ξ‖ >= ρ, then ‖x − ξ‖/ρ >= 1 and ζ(x) = 0.

6. Smoothness. Let x ∈ R^m.
  - Case A, ‖x − ξ‖ < ρ/2: the open ball B°_{ρ/2}(ξ) is a neighbourhood of x on which ζ ≡ 1 (step 5). So ζ agrees with a constant near x, ζ is C^infinity at x, and Dζ(x) = 0.
  - Case B, x ≠ ξ: y ↦ ‖y − ξ‖ is C^infinity near x, since the Euclidean norm is C^infinity away from 0 (contDiffAt_norm, composed with y ↦ y − ξ). So ζ = φ ∘ (y ↦ ‖y − ξ‖/ρ) is C^infinity at x.
  Every x falls in case A or case B (x = ξ is in case A). So ζ is C^infinity at every point, i.e. ContDiff ℝ (⊤ : ℕ∞) ζ (contDiff_iff_contDiffAt).

7. The gradient bound. ζ is (3/ρ)-Lipschitz on R^m, because φ is 3-Lipschitz and the norm is 1-Lipschitz:
    |ζ(x) − ζ(y)| <= 3 · |‖x − ξ‖/ρ − ‖y − ξ‖/ρ| <= (3/ρ) ‖x − y‖.
  A K-Lipschitz function has ‖Dζ(x)‖ <= K at every point (norm_fderiv_le_of_lipschitz). Hence ‖fderiv ℝ ζ x‖ <= 3/ρ for every x.
  Equivalently, by the chain rule in case B, Dζ(x)v = φ'(‖x − ξ‖/ρ) ρ^{-1} ⟨(x − ξ)/‖x − ξ‖, v⟩, so ‖Dζ(x)‖ = |φ'(‖x − ξ‖/ρ)|/ρ <= 3/ρ; and Dζ(x) = 0 in case A. ∎

## Key steps

1. g(t) = S(12(t−1/2))·S(12(1−t)) with S = Real.smoothTransition: C^∞, 0 <= g <= 1, zero off (1/2,1), equal to 1 on [7/12,11/12]
2. c = ∫_{1/2}^1 g >= 1/3
3. φ(t) = 1 − c^{-1}∫_{1/2}^t g is C^∞ (FTC), |φ'| <= 3, φ = 1 for t <= 1/2, φ = 0 for t >= 1, 0 <= φ <= 1
4. ζ(x) = φ(‖x−ξ‖/ρ): ζ = 1 on closedBall ξ (ρ/2), ζ = 0 when dist x ξ >= ρ
5. ζ is C^∞: locally constant near ξ, and a composition with the smooth norm away from ξ
6. ζ is (3/ρ)-Lipschitz, hence ‖fderiv ℝ ζ x‖ <= 3/ρ

## Reference use

### local-project

Queries:
- `python3 -I scan of .humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json nodes[*].lean_name (reserved declaration names)`
- `grep -n 'HasWeightedApproximateTangentSpaceAt\|def CountablyRectifiable\|HasApproximateTangentSpaceAt\|theorem .*ae.*tangent' -r .lake/packages/simongmt/Poincare/SimonGMT/Chapter03`
- `grep -rn 'C¹ approximation\|C1 approximation\|Approximation Theorem\|upper density\|Upper density' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01 .lake/packages/simongmt/Poincare/SimonGMT/Chapter02`
- `grep -n '^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `grep -rn 'theorem simon_theorem_1_17\|theorem area_image_criticalSet_eq_zero\|theorem hausdorff_blowUp_image\|theorem integral_weighted_blowUp\|theorem norm_normalProjection_eq_infDist' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -n 'theorem (zero_of_nonpos|one_of_one_le|nonneg|le_one|contDiff|pos_of_pos)\b' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `rg -n '^theorem contDiff_infty_iff_deriv|theorem contDiffAt_norm\b|theorem trace_smulRight|starProjection_minimal|theorem infDist_eq_iInf\b|theorem starProjection_add_starProjection_orthogonal|IsProj.trace' -g '*.lean' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_smul|euclideanHausdorffMeasure_smul₀|hausdorffMeasure_homothety_image' -g '*.lean' <snapshot>/mathlib/Mathlib; rg -ln Lusin -g '*.lean' <snapshot>/mathlib/Mathlib`
- `grep -rn 'theorem norm_fderiv_le_of_lipschitz\b\|theorem integral_hasDerivAt_right\b\|theorem contDiff_iff_contDiffAt\b\|trace_mul_comm' <snapshot>/mathlib/Mathlib/{Analysis/Calculus/FDeriv/Basic,MeasureTheory/Integral/IntervalIntegral/FundThmCalculus,Analysis/Calculus/ContDiff/Defs,LinearAlgebra/Trace}.lean`
- `diff GMT/Ch05/Contract.lean <snapshot>/project/GMT/Ch05/Contract.lean`
- `lean GMT/Ch05/Submission.lean -o /tmp/teh-decomp-elab/mybuild/GMT/Ch05/Submission.olean; lean /tmp/teh-decomp-elab/NodeCheck.lean (import GMT.Ch05.Submission + replayed contract scope + the 4 frozen child types)`
- `lean /tmp/teh-decomp-elab/Skel.lean and Skel2.lean (parent assembly from the 4 children as hypotheses; sorry-free admissibility of X)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-height-estimate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/ClassicalTangent.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`

The snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot project/GMT/Ch05/Contract.lean is byte-identical to the workspace contract.

None of the four proposed declarations exists locally. dag.json reserves only the 13 depth-0/1 names.

Child ae_tangent_planes is a genuine open obligation:
- SimonGMT Chapter03/Rectifiable.lean defines HasWeightedApproximateTangentSpaceAt and proves .unique, but says Simon 1.6/1.9 are "not asserted here".
- SubmanifoldCover.lean has only the easy direction of Lemma 1.2.
- Differential.lean calls the existence direction of 1.6 "still-open".

Tools available for that child:
- simon_theorem_3_6 (Upper Density, Chapter01/DensityComparison.lean);
- Lusin 1.17 (Chapter01/Lusin.lean);
- area_image_criticalSet_eq_zero (Chapter02/AreaCritical.lean);
- the injective area formula (Chapter02/AreaLipschitz.lean);
- Rademacher and the Lipschitz image bound (Chapter02/Lipschitz.lean);
- Whitney C^1 extension (Chapter02/WhitneyExtension.lean), towards the missing Ch. 2, 1.5 C^1 approximation;
- Chapter04.hausdorff_blowUp_image;
- Mathlib euclideanHausdorffMeasure_smul₀ and hausdorffMeasure_homothety_image.

Child smooth_cutoff: Real.smoothTransition (contDiff, zero_of_nonpos, one_of_one_le, nonneg, le_one), contDiff_infty_iff_deriv, intervalIntegral.integral_hasDerivAt_right, contDiffAt_norm, contDiff_iff_contDiffAt, norm_fderiv_le_of_lipschitz.

Child projection_algebra: LinearMap.trace_smulRight, IsProj.trace, trace_mul_comm, Submodule.starProjection_minimal, dist_starProjection_eq_infDist, starProjection_add_starProjection_orthogonal. SimonGMT Chapter04.norm_normalProjection_eq_infDist is exactly part (ii) for a general E.

Lean checks:
- After compiling Submission.lean to an olean in /tmp, NodeCheck.lean elaborates all four frozen types in the comparator's scope (import GMT.Ch05.Submission plus the replayed open/namespace commands), with only sorry warnings.
- Skel.lean (the four children as hypotheses) elaborates the parent's infinite case, the first-variation application, the mu-a.e. divergence rewrite and the operator/distance bound.
- Skel2.lean proves sorry-free that X is C^1, compactly supported, has tsupport X ⊆ U, and that D zeta = 0 off B_rho(xi).

The book texts supply the printed proofs that are copied: Ch. 5 2.1; Ch. 3 1.2, 1.3, 1.6, 1.8, 1.9; Ch. 1 1.17, 3.6; Ch. 2 1.5, 3.1-3.5, 4.4.
