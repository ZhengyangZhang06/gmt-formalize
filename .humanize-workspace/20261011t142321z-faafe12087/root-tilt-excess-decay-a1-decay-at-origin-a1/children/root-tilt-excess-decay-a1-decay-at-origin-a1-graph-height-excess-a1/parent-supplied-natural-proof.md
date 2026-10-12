# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1`
- Child DAG node: `root.tilt_excess_decay-a1.decay_at_origin-a1.graph_height_excess-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation: μ := V.weight, M := V.carrier, θ := V.mult, H^n := μHE[n] on R^{n+l}; τ, S, λ, Γ as in the statement; d(x) := infDist(x - τ, S); B := B̄_r(τ); F(x') := q(graphPoint x' (f x')), so Γ = F(B̄^n_R(0)).
1. Facts about μ.
(1a) μ-a.e. point lies in spt V. Indeed μ(μ.support^c) = 0 (measure_compl_support; R^{n+l} is second countable), and μ = (H^n.restrict M).withDensity(ofReal ∘ θ) is absolutely continuous with respect to H^n.restrict M, for which almost every point lies in the null-measurable set M ⊆ U (ae_restrict_mem₀); as spt V = U ∩ μ.support, μ-a.e. point lies in spt V. Consequently μ(E) <= μ(E ∩ spt V) for every set E (subadditivity and μ((spt V)^c) = 0).
(1b) μ(B̄_R(0)) < ∞: B̄_R(0) is compact and contained in U, and μ(B̄_R(0)) = ∫⁻_{M ∩ B̄_R(0)} ofReal(θ) dH^n <= ∫⁻_{M ∩ B̄_R(0)} ‖θ‖ₑ dH^n < ∞ by the structure field integrableOn_mult. Hence μ(B) < ∞.
(1c) For every measurable E ⊆ B and measurable g >= 0: ∫⁻_E g dμ <= 2 ∫⁻_E g dH^n. Indeed ∫⁻_E g dμ = ∫⁻_E g · ofReal(θ) d(H^n.restrict M) (lintegral_withDensity_eq_lintegral_mul₀; θ is AEMeasurable for H^n.restrict M by the field aemeasurable_mult). The hypothesis that θ <= 2 μ-a.e. on B means, by ae_withDensity_iff', that for H^n.restrict M-a.e. x: ofReal(θ x) ≠ 0 implies (x ∈ B → θ x <= 2). Hence g · ofReal(θ) <= 2 g holds H^n.restrict M-a.e. on E (where ofReal(θ x) = 0 the left side vanishes), and integrating and using H^n.restrict M <= H^n gives the claim.
2. Measurability and bounds. d is 1-Lipschitz, hence continuous and Borel. F is continuous on the compact set B̄^n_R(0) (f is Lipschitz there; graphPoint and q are continuous), so Γ is compact, hence closed and measurable. For x in B, 0 <= d(x) <= ||x - τ|| <= r because 0 ∈ S.
3. The part on Γ. Let g := indicator of B times ofReal(d^2) (measurable). By (1c) with E := B ∩ Γ, ∫⁻_{B ∩ Γ} ofReal(d^2) dμ <= 2 ∫⁻_{B ∩ Γ} ofReal(d^2) dH^n = 2 ∫⁻_Γ g dH^n. By tdo_graph_lintegral_le (D := B̄^n_R(0), measurable; L := 1, f being 1-Lipschitz on D; sqrt(1 + 1^2) = sqrt 2), ∫⁻_Γ g dH^n <= ofReal(sqrt(2)^n) ∫⁻_{B̄^n_R(0)} g(F x') dx'. Let x' in B̄^n_R(0). If F x' ∉ B then g(F x') = 0. If F x' ∈ B then, by tdo_graph_plane_dist (iv) with y := f x', ||x'|| <= ||F x' - τ|| <= r, and by tdo_graph_plane_dist (iii), d(F x') <= ||f x' - λ(x')||. Hence g(F x') <= (indicator of B̄^n_r(0))(x') · ofReal(||f x' - λ(x')||^2) for every x' in B̄^n_R(0), and ∫⁻_{B̄^n_R(0)} g∘F <= ∫⁻_{B̄^n_r(0)} ofReal(||f - λ||^2). The sphere {||x'|| = r} is Lebesgue-null (r ≠ 0, Measure.addHaar_sphere_of_ne_zero), so the last integral equals ∫⁻_{B^n_r(0)} ofReal(||f - λ||^2). As r <= R, f - λ is continuous on B̄^n_r(0), so ||f - λ||^2 is bounded and integrable on the bounded set B^n_r(0), and ∫⁻_{B^n_r(0)} ofReal(||f - λ||^2) = ofReal(X) with X := ∫_{B^n_r(0)} ||f - λ||^2 >= 0 (ofReal_integral_eq_lintegral_ofReal). Altogether ∫⁻_{B ∩ Γ} ofReal(d^2) dμ <= ofReal(2 sqrt(2)^n X).
4. The part off Γ. By (1a), μ-a.e. x in B \ Γ lies in spt V ∩ B, where 0 <= d(x) <= h by hypothesis; so ofReal(d(x)^2) <= ofReal(h^2) for μ-a.e. x in B \ Γ, and ∫⁻_{B \ Γ} ofReal(d^2) dμ <= ofReal(h^2) μ(B \ Γ). By (1a), μ(B \ Γ) <= μ((B \ Γ) ∩ spt V) <= μ(B̄_R(0) ∩ (spt V \ Γ)) <= ofReal β, since B ⊆ B̄_R(0). Hence ∫⁻_{B \ Γ} ofReal(d^2) dμ <= ofReal(h^2) ofReal(β) = ofReal(h^2 β) (β >= 0).
5. As Γ is measurable, ∫⁻_B ofReal(d^2) dμ = ∫⁻_{B ∩ Γ} ofReal(d^2) dμ + ∫⁻_{B \ Γ} ofReal(d^2) dμ <= ofReal(2 sqrt(2)^n X) + ofReal(h^2 β) = ofReal(2 sqrt(2)^n X + h^2 β), both arguments being >= 0.
6. d^2 is continuous and bounded by r^2 on B and μ(B) < ∞ (1b), so d^2 is μ-integrable on B and ∫_B d^2 dμ = (∫⁻_B ofReal(d^2) dμ).toReal <= 2 sqrt(2)^n X + h^2 β (integral_eq_lintegral_of_nonneg_ae, ENNReal.toReal_le_of_le_ofReal). Since sqrt(2)^n = 2^{n/2}, this is the claim.

## Key steps

1. μ-a.e. point lies in spt V; B̄_R(0) has finite weight; θ <= 2 on B̄_r(τ) gives μ <= 2 H^n there
2. On Γ: the area bound tdo_graph_lintegral_le with L = 1 and the graph-plane estimates (iii), (iv) bound the integral by 2 · 2^{n/2} ∫_{B^n_r(0)} ||f - λ||^2
3. Off Γ: μ-a.e. such point is in spt V \ Γ, where dist <= h, and that set has weight <= β
4. Add the two parts and convert the lower integral back to the Bochner integral

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
