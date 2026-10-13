# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.one_dim_sup-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

1. Interval coordinates. Let e := EuclideanSpace.single 0 1 in R^1 and ι : R -> R^1, ι(t) := t e. ι is a linear isometry equivalence (||ι t|| = |t|, inverse z |-> z 0) mapping [-a, a] onto B̄_a(0) and (-a, a) onto B_a(0), and it is measure preserving from Lebesgue measure on R to volume on R^1 (the inverse of the composition of EuclideanSpace.measurableEquiv and MeasurableEquiv.funUnique, both volume preserving). Hence for every function φ on R^1, ∫_{B_a(0)} φ = ∫_{(-a,a)} φ(ι t) dt.
2. Let W := w ∘ ι : R -> R^l. W is K-Lipschitz on [-a, a], hence continuous there.
3. Derivatives. For every t, hsNormSq(fderiv w (ι t)) = ||deriv W t||^2. Indeed hsNormSq B = ||B e||^2 for B : R^1 ->L R^l (the defining sum has the single index 0). If w is differentiable at ι t, the chain rule gives deriv W t = fderiv w (ι t) (ι 1) = fderiv w (ι t) e. If w is not differentiable at ι t, then W is not differentiable at t (otherwise w = W ∘ ι^{-1} would be differentiable at ι t), so fderiv w (ι t) = 0 and deriv W t = 0.
4. Integrability. By Rademacher's theorem (LipschitzOnWith.ae_differentiableWithinAt_of_mem for W on [-a, a]; at interior points differentiability within [-a, a] is differentiability), W is differentiable at almost every t in (-a, a), and there ||deriv W t|| <= K because the difference quotients are bounded by K. deriv W is measurable (measurable_deriv). Hence ||deriv W|| and ||deriv W||^2 are integrable on (-a, a); ||W|| and ||W||^2 are integrable on (-a, a) since W is continuous on the compact interval [-a, a].
5. Fundamental theorem of calculus. For s, t in [-a, a]: ||W(t) - W(s)|| <= ∫_{(-a,a)} ||deriv W||. If W(t) = W(s) this is clear. Otherwise let u := (W(t) - W(s))/||W(t) - W(s)|| and φ(r) := <W(r), u>. Then φ is K-Lipschitz on [-a, a], hence absolutely continuous on uIcc s t (LipschitzOnWith.absolutelyContinuousOnInterval), so ∫_s^t deriv φ = φ(t) - φ(s) = ||W(t) - W(s)|| (AbsolutelyContinuousOnInterval.integral_deriv_eq_sub). At every r in (-a, a) where W is differentiable, deriv φ r = <deriv W r, u>, so |deriv φ r| <= ||deriv W r|| for almost every r between s and t. Therefore ||W(t) - W(s)|| = ∫_s^t deriv φ <= ∫_{uIoc s t} |deriv φ| <= ∫_{uIoc s t} ||deriv W|| <= ∫_{(-a,a)} ||deriv W|| (the integrand is nonnegative, uIoc s t ⊆ [-a, a], and the endpoints are null).
6. Averaging. Fix x in B̄_a(0) and let t := x 0, so t in [-a, a] and ι t = x. By step 5, ||W(t)|| <= ||W(s)|| + D for every s in (-a, a), where D := ∫_{(-a,a)} ||deriv W||. Integrating over s in (-a, a), an interval of length 2a, and dividing by 2a: ||W(t)|| <= (2a)^{-1} ∫_{(-a,a)} ||W|| + D.
7. Cauchy-Schwarz on (-a, a): ∫ ||W|| <= (2a)^{1/2} (∫ ||W||^2)^{1/2} and D <= (2a)^{1/2} (∫ ||deriv W||^2)^{1/2}. Hence ||W(t)|| <= ((2a)^{-1} ∫_{(-a,a)} ||W||^2)^{1/2} + (2a ∫_{(-a,a)} ||deriv W||^2)^{1/2}.
8. Back to R^1. By steps 1 and 3, ∫_{(-a,a)} ||W(s)||^2 ds = ∫_{B_a(0)} ||w y||^2 dy and ∫_{(-a,a)} ||deriv W s||^2 ds = ∫_{B_a(0)} hsNormSq(fderiv w y) dy, and ||w(x)|| = ||W(t)||. This is the claim.

## Key steps

1. Transfer to W := w ∘ ι on [-a, a] by the measure-preserving isometry ι(t) = t e, with hsNormSq(fderiv w (ι t)) = ||deriv W t||^2
2. Rademacher: deriv W exists a.e. on (-a, a), is bounded by K and measurable
3. FTC for the absolutely continuous scalar function <W, u>: ||W(t) - W(s)|| <= ∫_{(-a,a)} ||deriv W||
4. Average over s and apply Cauchy-Schwarz, then transfer back to B_a(0)

## Reference use

### local-project

Queries:
- `rg -n 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem hausdorffMeasure_image_le \(h : LipschitzOnWith|theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval|theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub|theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ|theorem exists_measurable_le_lintegral_eq|theorem measure_compl_support|theorem ae_differentiableAt|theorem measurable_fderiv |theorem addHaar_sphere|exists_orthonormalBasis_extension' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem .*ae_differentiableAt|theorem .*ae_differentiableWithinAt' <snapshot>/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; rg -n 'lemma measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean; rg -n "theorem lintegral_withDensity_eq_lintegral_mul₀|theorem ae_withDensity_iff'" <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `grep -n 'theorem\|lemma' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean; grep -rln 'AbsolutelyContinuousOnInterval|integral_deriv_eq_sub' <snapshot>/mathlib/Mathlib`
- `sed -n 1,260p <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; sed -n 1025,1060p <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n 'theorem .*area|theorem .*graph|lemma .*graph' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02 Chapter03; sed -n 40,90p .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `python3 -I: list id/lean_name/status of all 200 nodes in <run>/dag.json; filter lean_statements containing rotatedPlane or graphPoint with span`
- `rg -l -e 'tdo_exists_isometry_rotatedPlane|tdo_graph_plane_dist|tdo_graph_lintegral_le|tdo_one_dim_sup_le|tdo_scaledLpNorm_bounds|tdo_tiltExcess_le_of_subset|tdo_small_tilt_plane|tdo_graph_height_excess|tdo_graph_height_sup' <run>/dag.json <run>/nodes <snapshot>/project <snapshot>/mathlib/Mathlib GMT .lake/packages/simongmt/Poincare (no match)`
- `sed -n 730,1000p book/chapter-05.txt (printed proof of 4.5)`
- `lake env lean -o /tmp/tdo-decomp/olean/GMT/Ch05/Submission.olean GMT/Ch05/Submission.lean; lean /tmp/tdo-decomp/checks/Types.lean; lean /tmp/tdo-decomp/checks/TypesPrint.lean; lean /tmp/tdo-decomp/checks/TypesNoOpen.lean; lean /tmp/tdo-decomp/checks/Final2.lean`
- `lean /tmp/tdo-decomp/checks/ParseMine.lean (rfl parse checks of integral bodies followed by +)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/tmp/tdo-decomp/checks/Types.lean`
- `/tmp/tdo-decomp/checks/TypesPrint.lean`
- `/tmp/tdo-decomp/checks/TypesNoOpen.lean`
- `/tmp/tdo-decomp/checks/Final2.lean`
- `/tmp/tdo-decomp/checks/ParseMine.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). Its Contract.lean has the same sha256 (c966f51e...) as the workspace Contract.lean and Submission.lean.

Mathlib declarations located for the child proofs (paths under mathlib/Mathlib):
- Area bound (tdo_graph_lintegral_le):
  - EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187): μHE[d] = volume on EuclideanSpace ℝ (Fin d).
  - euclideanHausdorffMeasure_def (same file): μHE[d] is a d-only scalar times μH[d].
  - LipschitzOnWith.hausdorffMeasure_image_le (MeasureTheory/Measure/Hausdorff.lean:733).
- One-dimensional FTC (tdo_one_dim_sup_le):
  - LipschitzOnWith.absolutelyContinuousOnInterval (MeasureTheory/Function/AbsolutelyContinuous.lean:309).
  - AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean:225).
  - Rademacher: LipschitzOnWith.ae_differentiableWithinAt_of_mem (Analysis/Calculus/Rademacher.lean:361).
  - measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:378).
- Hoelder (tdo_scaledLpNorm_bounds):
  - ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory/Integral/MeanInequalities.lean:202).
  - eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ (MeasureTheory/Function/LpSeminorm/CompareExp.lean:32).
  - exists_measurable_le_lintegral_eq (MeasureTheory/Integral/Lebesgue/Basic.lean:139), for non-measurable integrands.
- Null sphere: addHaar_sphere_of_ne_zero (MeasureTheory/Measure/Lebesgue/EqHaar.lean:519).
- Rotation (tdo_exists_isometry_rotatedPlane): Orthonormal.exists_orthonormalBasis_extension_of_card_eq (Analysis/InnerProductSpace/PiL2.lean:1044).
- Weight measure:
  - measure_compl_support (MeasureTheory/Measure/Support.lean:202).
  - ae_withDensity_iff' (MeasureTheory/Measure/WithDensity.lean:291).
  - lintegral_withDensity_eq_lintegral_mul₀ (MeasureTheory/Measure/WithDensity.lean:458).

No-match results:
- Mathlib has no varifold-specific results; this was already established for the parent.
- None of the nine new tdo_ names occurs anywhere searched.

Other packages and nodes:
- simongmt (outside the snapshot) has a sorry-free injective area formula, injective_area_formula_lipschitzOn_simon_volume (Chapter02/AreaLiteral.lean:61). It is not needed, because the simpler Lipschitz-image bound gives the same constant 2^{n/2}.
- dag.json: allard52_graph_plane_algebra has a rotation-existence conjunct but is not accepted (decomposing), so it cannot be reused. Its type also differs.

The printed proof of 4.5 (book/chapter-05.txt:776-990) was compared with the supplied proof. The children cover its steps (1)-(22) as mapped in the rationale.

Lean: all nine frozen lean_statements elaborate against the compiled Submission olean, with only the expected sorry warnings (Final2.lean). The integral-body parses were confirmed by rfl (ParseMine.lean).
