# Parent-supplied natural-language proof

- Parent DAG node: `root.tilt_excess_decay-a1`
- Child DAG node: `root.tilt_excess_decay-a1.lemma_a_tilt_height-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. mu := V.weight, p_x := V.tangentProj x, p_T := T.starProjection, |A|^2 := hsNormSq A (Hilbert-Schmidt), ||A|| operator norm (||A|| <= |A|), spt V := V.support. B_s(z) closed ball, B°_s(z) open ball. x' := p_{T^perp}(x - z), so |x'| = dist(x - z, T) = infDist (x - z) T.

Basic facts used. (F2) mu-a.e. point lies in spt V (mu(R^{n+l} \ spt mu) = 0 and mu(R^{n+l} \ U) = 0); mu(K) < infinity for compact K contained in U (contract integrableOn_mult); H is mu-integrable on compact subsets of U (first conjunct of HasGeneralizedMeanCurvature). The hypotheses give: x |-> p_x is mu-a.e. strongly measurable, and for mu-a.e. x, p_x = P.starProjection for an n-dimensional subspace P (a rank-n orthogonal projection).

Proof.
1. Cut-off. Fix phi in C^infinity(R, [0, 1]) with phi = 1 on (-infinity, 1/2], phi = 0 on [1, infinity) and |phi'| <= 3 (possible since the transition interval has length 1/2). Put zeta(x) := phi(|x - z|/r). zeta is C^infinity (phi is constant near 0, so the non-smoothness of |x - z| at z is irrelevant), 0 <= zeta <= 1, zeta = 1 on B_{r/2}(z), zeta = 0 outside B°_r(z), and |grad zeta| <= 3/r.

2. Test field. X(x) := zeta(x)^2 x'. X is C^infinity, has compact support, and tsupport X is contained in B_r(z), which is contained in U; so X is admissible in the definition of generalized mean curvature: int div_M X dmu = - int X . H dmu. X . H is mu-integrable because H is integrable on the compact set B_r(z) and X is bounded.

3. Divergence. DX(x) v = zeta^2 p_{T^perp} v + 2 zeta (grad zeta . v) x'. At every x where p_x is the orthogonal projection onto an n-dimensional subspace (mu-a.e. x by hypothesis):
 div_M X(x) = trace(DX(x) o p_x) = zeta^2 trace(p_{T^perp} p_x) + 2 zeta grad zeta . p_x x' = zeta^2 s + 2 zeta grad zeta . (p_x - p_T) x',
where s := (1/2)|p_x - p_T|^2. Here trace(v |-> (w . p_x v) u) = w . p_x u was used; p_T x' = 0; and for rank-n orthogonal projections trace(p_{T^perp} p_x) = trace(p_x) - trace(p_T p_x) = n - trace(p_T p_x) = (1/2)|p_x - p_T|^2, because |p_x - p_T|^2 = trace((p_x - p_T)^2) = trace(p_x) + trace(p_T) - 2 trace(p_T p_x) = 2n - 2 trace(p_T p_x).

4. Integrability. All integrands (zeta^2 s, zeta grad zeta . (p_x - p_T) x', zeta^2 |x'||H|, |grad zeta|^2 |x'|^2) are mu-measurable (x |-> p_x is mu-measurable by hypothesis), bounded except for the factor |H|, which is integrable on B_r(z), and vanish outside B_r(z), which has finite mu-measure. So all integrals below are finite.

5. Identity. By steps 2 and 3, int zeta^2 s dmu = - int 2 zeta grad zeta . (p_x - p_T) x' dmu - int zeta^2 x' . H dmu.

6. Absorption. |(p_x - p_T) x'| <= ||p_x - p_T|| |x'| <= |p_x - p_T| |x'| = sqrt(2s) |x'|. By 2AB <= t A^2 + B^2/t with t = 1/2, A = zeta sqrt(s), B = sqrt(2) |grad zeta| |x'|:
 |2 zeta grad zeta . (p_x - p_T) x'| <= 2 sqrt(2) zeta sqrt(s) |grad zeta| |x'| <= (1/2) zeta^2 s + 4 |grad zeta|^2 |x'|^2.
Hence int zeta^2 s <= (1/2) int zeta^2 s + 4 int |grad zeta|^2 |x'|^2 + int zeta^2 |x'| |H|, and since int zeta^2 s is finite,
 int zeta^2 s dmu <= 8 int |grad zeta|^2 |x'|^2 dmu + 2 int zeta^2 |x'| |H| dmu.

7. Conclusion. zeta = 1 on B_{r/2}(z), 0 <= zeta <= 1, |grad zeta| <= 3/r, zeta = 0 off B_r(z), and |x'| <= h for mu-a.e. x in B_r(z) (such x lie in spt V by (F2), and the hypothesis gives infDist (x - z) T <= h there). Therefore
 (1/2) int_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= int zeta^2 s dmu <= 72 r^{-2} int_{B_r(z)} |x'|^2 dmu + 2 h int_{B_r(z)} |H| dmu,
and multiplying by 2:
 int_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= 144 r^{-2} int_{B_r(z)} dist(x - z, T)^2 dmu + 4 h int_{B_r(z)} |H| dmu,
which is the claim (the left side is the Bochner integral of the integrable function hsNormSq (V.tangentProj x - T.starProjection) over closedBall z (r/2)).

## Key steps

1. Cut-off zeta and test field X = zeta^2 p_{T^perp}(x - z)
2. div_M X = zeta^2 |p_x - p_T|^2/2 + 2 zeta grad zeta . (p_x - p_T) x' mu-a.e.
3. First-variation identity; integrability
4. Absorb the cross term by Young's inequality
5. Use zeta = 1 on B_{r/2}(z), |grad zeta| <= 3/r and |x'| <= h

## Reference use

### local-project

Queries:
- `rg -n 'ted_lp_monotonicity|ted_density_ge_one|ted_allard_density_bounds' <snapshot> (no match)`
- `grep -rhoE '"lean_name": *"[^"]*"' <run>/nodes <run>/dag.json | sort | uniq -c`
- `rg -n 'theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le|theorem monotoneOn_of_deriv_nonneg|theorem lintegral_mul_le_Lp_mul_Lq|theorem le_toOuterMeasure_caratheodory|theorem tendsto_measure_biInter_gt|theorem withDensity_apply|euclideanHausdorffMeasure_def' <snapshot>/mathlib/Mathlib`
- `rg -n 'exists_measurable_subset_ae_eq' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean; rg -n 'measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -l -i 'varifold|monotonicity formula' <snapshot>/mathlib/Mathlib (no match)`
- `rg -n 'theorem simon_theorem_3_6|def dimensionalUpperDensity|def simonHausdorffMeasureReal|theorem simonHausdorffMeasureReal_toOuterMeasure|theorem measure_toOuterMeasure_isBorelRegular|def IsBorelRegularOuterMeasure|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT`
- `rg -c sorry .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{DensityComparison,Hausdorff,Basic}.lean (no match)`
- `sed -n 215,600p book/chapter-04.txt; sed -n 590,735p book/chapter-01.txt`
- `lean /tmp/ted-decomp-v2/checks/Types.lean; lean /tmp/ted-decomp-v2/checks/Props.lean; lean /tmp/ted-decomp-v2/checks/PrintNew.lean`
- `lean /tmp/ted-decomp-v2/checks/Assembly.lean (#print axioms parent_check)`
- `lean /tmp/ted-decomp-v2/checks/Wiring.lean (#print axioms wiring_lp_hyps)`
- `lean /tmp/ted-decomp-v2/checks/WiringUD.lean (#print axioms wiring_upper_density)`
- `python3 -I /tmp/ted-decomp-v2/scripts/numcheck.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-lp-monotonicity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-density-ge-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/ted-decomp-v2/checks/Types.lean`
- `/tmp/ted-decomp-v2/checks/Props.lean`
- `/tmp/ted-decomp-v2/checks/PrintNew.lean`
- `/tmp/ted-decomp-v2/checks/Assembly.lean`
- `/tmp/ted-decomp-v2/checks/Wiring.lean`
- `/tmp/ted-decomp-v2/checks/WiringUD.lean`
- `/tmp/ted-decomp-v2/scripts/numcheck.py`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json). Its Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

No prior declarations: ted_lp_monotonicity, ted_density_ge_one and ted_allard_density_bounds have no match in the snapshot, in dag.json or in any other node's files.

No-match search: Mathlib has no varifold or monotonicity-formula results ('varifold|monotonicity formula' matches no file). The monotonicity is therefore proved in the child ted_lp_monotonicity directly from the contract's first-variation identity.

Mathlib items located for the new proofs (paths under mathlib/Mathlib):
- LocallyIntegrableOn.integrableOn_compact_subset (MeasureTheory/Function/LocallyIntegrable.lean:122).
- hasDerivAt_integral_of_dominated_loc_of_deriv_le (Analysis/Calculus/ParametricIntegral.lean:286).
- monotoneOn_of_deriv_nonneg (Analysis/Calculus/Deriv/MeanValue.lean:411).
- Hoelder, lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top (MeasureTheory/Integral/MeanInequalities.lean:147).
- NullMeasurableSet.exists_measurable_subset_ae_eq (MeasureTheory/Measure/NullMeasurable.lean:214).
- measure_compl_support (MeasureTheory/Measure/Support.lean:202).
- le_toOuterMeasure_caratheodory (MeasureTheory/Measure/OuterMeasure.lean:37).
- tendsto_measure_biInter_gt (MeasureTheory/Measure/Continuity.lean:266).
- withDensity_apply (MeasureTheory/Measure/WithDensity.lean:44).
- euclideanHausdorffMeasure_def (Geometry/Euclidean/Volume/Measure.lean:74): μHE[d] is a scalar multiple of μH[d].

The pinned simongmt package lies outside the snapshot; 'rg -c sorry' finds no match in the Chapter01 files used. It provides:
- simon_theorem_3_6 (Chapter01/DensityComparison.lean:332).
- measure_toOuterMeasure_isBorelRegular (Chapter01/Basic.lean:309).
- simonHausdorffMeasureReal = (omega_m/2^m) • μH[m] (Chapter01/Hausdorff.lean:283), with simonHausdorffMeasureReal_toOuterMeasure (:445).
- HasWeightedApproximateTangentSpaceAt and blowUpMap (Chapter03/Rectifiable.lean:330, 96), used by translate_varifold.
No Chapter04 declaration is used anywhere in v2.

The proofs of aal_lp_monotonicity, aal_density_ge_one and aal_pinched_density_bounds in the affine-approximation branch were consulted; these were reviewed as natural proofs, but the declarations are not accepted. The v2 children re-derive the needed arguments under ted_ names, with lp_monotonicity in a weaker, inequality-only form.

Lean checks:
- All nine child types elaborate in the contract scope.
- The sorry-free assembly proves TiltExcessDecayTheorem from translate_varifold, allard_density_bounds, decay_at_origin and the four sibling Props, using only propext, Classical.choice and Quot.sound.
- The sorry-free wiring lemmas for both monotonicity call sites, and for applying the Upper Density Theorem to V.weight with the μHE[n] normalization, use only the same three axioms.
