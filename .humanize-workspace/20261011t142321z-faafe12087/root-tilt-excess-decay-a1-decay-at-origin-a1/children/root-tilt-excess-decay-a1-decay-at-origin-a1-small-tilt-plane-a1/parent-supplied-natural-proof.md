# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.small_tilt_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: γ := 1/(2n+2), so 0 < γ <= 1/4; σ := δρ; μ := V.weight; p_x := V.tangentProj x; for a subspace P, p_P := P.starProjection, E(P) := V.tiltExcess 0 σ P = σ^{-n} ∫_{B̄_σ(0)} hsNormSq(p_x - p_P) dμ and E_*(P) := V.tiltExcessStar H p δ 0 σ P = max{E(P), Y} with Y := δ^{-1} (V.scaledLpNorm H p 0 σ).toReal^2 (Y does not depend on P); ω := unitBallVolume n > 0; K(y, r) := V.scaledLpNorm H p y r.
Constants: let C_A > 0 be the constant given by AffineApproximationLemma for (n, l, p); put C_2 := 2^n C_A^2 (C_A + 1)^2, C_3 := 2 C_A + 2 (8 C_2/ω)^{1/2} and C := max{C_2, C_3} > 0.
1. Preliminaries. By AllardHypotheses: ρ > 0, 0 ∈ spt V, B̄_ρ(0) ⊆ U, μ(B̄_ρ(0)) <= ofReal((1+δ) ω ρ^n) < ∞ and K(0, ρ) <= ofReal δ. As 0 < δ <= 1/4: σ > 0 and 2σ <= ρ/2 < ρ.
(1a) K(0, 2σ) <= ofReal δ: by tdo_scaledLpNorm_bounds part (a) with z = w = 0, s = 2σ, t = ρ (p > n >= 1 > 0), K(0, 2σ) <= ofReal((2σ/ρ)^{(p-n)/p}) K(0, ρ) <= ofReal δ, since 0 < 2σ/ρ <= 1 and (p - n)/p > 0 give (2σ/ρ)^{(p-n)/p} <= 1.
(1b) δ <= δ^γ, because 0 < δ <= 1 and 0 < γ <= 1.
2. Affine approximation. Apply AffineApproximationLemma (hypotheses: U open, 0 < δ <= 1/4, AllardHypotheses) at ξ := 0, which lies in spt V ∩ B̄_{δρ}(0), with radius σ_2 := 2δρ in (0, 2δρ]: there is a subspace T~ with finrank n such that
(2a) ofReal(C_A^{-1} sqrt((σ_2^n)^{-1} ∫_{B̄_{σ_2/2}(0)} hsNormSq(p_x - p_T~) dμ)) <= ofReal(σ_2^{-1}) · heightSup(0, σ_2, T~) + K(0, σ_2),
(2b) ofReal(σ_2^{-1}) · heightSup(0, σ_2, T~) <= ofReal(C_A δ^γ),
where σ_2 = 2σ and σ_2/2 = σ.
3. Height for T~. For x in spt V ∩ B̄_{2σ}(0), ofReal(infDist(x - 0, T~)) <= heightSup(0, 2σ, T~) (le_biSup), so (2b) gives ofReal((2σ)^{-1} infDist(x, T~)) <= ofReal(C_A δ^γ), i.e. infDist(x, T~) <= 2 C_A δ^γ σ.   (H~)
4. Tilt for T~. Let J~ := ∫_{B̄_σ(0)} hsNormSq(p_x - p_T~) dμ >= 0. By (2b), (1a), (1b), the right side of (2a) is <= ofReal(C_A δ^γ) + ofReal(δ^γ) = ofReal((C_A + 1) δ^γ). Hence C_A^{-1} sqrt((2σ)^{-n} J~) <= (C_A + 1) δ^γ (ENNReal.ofReal_le_ofReal_iff, the right side being >= 0), so (2σ)^{-n} J~ <= C_A^2 (C_A + 1)^2 (δ^γ)^2 (square both nonnegative sides), and E(T~) = σ^{-n} J~ = 2^n (2σ)^{-n} J~ <= C_2 (δ^γ)^2.   (E~)
5. Case A: E(T) > C_2 (δ^γ)^2. Take T' := T~. Then finrank T' = n; E(T~) <= C_2 (δ^γ)^2 < E(T), hence E_*(T~) = max{E(T~), Y} <= max{E(T), Y} = E_*(T); E(T') <= C_2 (δ^γ)^2 <= C (δ^γ)^2; and by (H~), infDist(x, T') <= 2 C_A δ^γ σ <= C_3 δ^γ σ <= C δ^γ σ for x in spt V ∩ B̄_{2σ}(0).
6. Case B: E(T) <= C_2 (δ^γ)^2. Take T' := T. Then finrank T' = n, E_*(T') <= E_*(T) trivially, and E(T') <= C_2 (δ^γ)^2 <= C (δ^γ)^2. It remains to bound the height.
(6a) Integrability. For P in {T, T~}, φ_P(x) := hsNormSq(p_x - p_P) is μ-integrable on B̄_σ(0): it is μ-a.e. strongly measurable (hsNormSq is continuous and x |-> p_x is a.e. strongly measurable by hypothesis), it is bounded by 4(n+l) (||p_x|| <= 1 because by definition p_x is an orthogonal projection or 0, ||p_P|| <= 1, and hsNormSq B <= (n+l) ||B||^2), and μ(B̄_σ(0)) <= μ(B̄_ρ(0)) < ∞.
(6b) Let D := p_T - p_T~. For every x, D = (p_x - p_T~) - (p_x - p_T), so hsNormSq D <= 2 φ_T(x) + 2 φ_T~(x) (apply ||u - v||^2 <= 2||u||^2 + 2||v||^2 to each column D e_i).
(6c) Integrating (6b) over B̄_σ(0), using (6a): μ(B̄_σ(0)).toReal · hsNormSq D <= 2 σ^n E(T) + 2 σ^n E(T~) <= 4 C_2 (δ^γ)^2 σ^n, by Case B and (E~).
(6d) By hypothesis ofReal(ω σ^n/2) <= μ(B̄_σ(0)) < ∞, so μ(B̄_σ(0)).toReal >= ω σ^n/2 > 0. Hence hsNormSq D <= 8 C_2 (δ^γ)^2/ω and hsNorm D = sqrt(hsNormSq D) <= (8 C_2/ω)^{1/2} δ^γ.
(6e) For every y, ||D y|| <= hsNorm D ||y|| (write y = sum_i y_i e_i and use Cauchy-Schwarz).
(6f) Let x in spt V ∩ B̄_{2σ}(0). Since p_T x ∈ T, infDist(x, T) <= ||x - p_T x|| <= ||x - p_T~ x|| + ||D x||. The orthogonal projection onto the closed subspace T~ gives a nearest point, so ||x - p_T~ x|| = infDist(x, T~) <= 2 C_A δ^γ σ by (H~). With (6d), (6e) and ||x|| <= 2σ: infDist(x, T) <= 2 C_A δ^γ σ + (8 C_2/ω)^{1/2} δ^γ (2σ) = C_3 δ^γ σ <= C δ^γ σ.
7. In both cases T' has all the required properties, and C depends only on n, l, p.

## Key steps

1. K(0, 2δρ) <= δ by the scaling bound, and δ <= δ^γ
2. Affine approximation 2.5 at ξ = 0, radius 2δρ: plane T~ with height <= 2 C_A δ^γ δρ and E(0, δρ, T~) <= C_2 (δ^γ)^2
3. If E(0, δρ, T) > C_2 (δ^γ)^2 take T' = T~ (then E_* does not increase)
4. Otherwise take T' = T; the lower mass bound gives |p_T - p_T~| <= (8 C_2/ω_n)^{1/2} δ^γ and hence the height bound C_3 δ^γ δρ for T

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
