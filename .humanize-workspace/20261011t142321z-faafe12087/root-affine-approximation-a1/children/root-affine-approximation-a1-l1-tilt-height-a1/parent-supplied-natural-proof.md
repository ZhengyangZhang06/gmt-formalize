# Parent-supplied natural-language proof

- Parent DAG node: `root.affine_approximation-a1`
- Child DAG node: `root.affine_approximation-a1.l1_tilt_height-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the computation proving Simon, Ch. 5, Lemma 2.1 (pp. 107-108), kept in L^1 form (Lemma A of the parent proof, correction (b)): instead of absorbing the mean-curvature term by Cauchy-Schwarz (which produces integral |H|^2 and, via Remark 2.2, needs p >= 2), we use |x'| <= h. No lower bound on theta and no integrability exponent p are needed.

Notation: mu := V.weight; p_x := V.tangentProj x; for a linear map A of R^(n+l), |A|^2 := hsNormSq A = sum_i |A e_i|^2 = trace(A^* A), and ||A|| is the operator norm, so ||A|| <= |A|; p_T := T.starProjection and p_{T^perp} := I - p_T.

0. Preliminaries. B_r(z) is compact and contained in U, so mu(B_r(z)) < infinity (V.integrableOn_mult) and H is mu-integrable on B_r(z) (H is locally integrable on U). By aal_tangent_structure, for mu-a.e. x, p_x is the orthogonal projection onto an n-dimensional subspace (symmetric, idempotent, trace n), and x -> p_x is mu-a.e. strongly measurable. Also mu-a.e. x lies in spt V (mu(R^(n+l) minus spt mu) = 0 by Mathlib Measure.measure_compl_support, and mu(R^(n+l) minus U) = 0 because mu is concentrated on M contained in U). The function x -> |p_x - p_T|^2 is mu-a.e. strongly measurable and bounded (|p_x - p_T| <= |p_x| + |p_T| <= 2 sqrt(n + l)), and x -> dist(x - z, T)^2 is continuous and <= r^2 on B_r(z); hence all integrals in the statement are integrals of integrable functions on sets of finite measure.

1. Cutoff and test field. Fix phi in C^1(R; [0,1]) with phi = 1 on (-infinity, 1/2], phi = 0 on [1, infinity) and |phi'| <= 3 (possible since the transition interval has length 1/2 and 3 > 2; e.g. a C^1 smoothing of the piecewise linear function with slope -2). Put zeta(x) := phi(|x - z|/r); zeta is C^1 (phi is constant near 0), 0 <= zeta <= 1, zeta = 1 on B_{r/2}(z), zeta = 0 outside B^o_r(z), and |grad zeta| <= 3/r. Put x' := p_{T^perp}(x - z) = (x - z) - p_T(x - z), so |x'| = dist(x - z, T) (Mathlib Submodule.dist_starProjection_eq_infDist), and X(x) := zeta(x)^2 x'. X is C^1, has compact support, and tsupport X is contained in B_r(z), hence in U; so X is admissible in V.HasGeneralizedMeanCurvature H.

2. Tangential divergence (Simon (1)-(3) in the proof of 2.1). DX(x) v = zeta^2 p_{T^perp} v + 2 zeta (grad zeta . v) x'. At every x where p_x is a rank-n orthogonal projection (mu-a.e.), since the trace of v -> (grad zeta . p_x v) x' equals grad zeta . p_x x' (p_x symmetric),
 div_M X(x) = trace(DX(x) o p_x) = zeta^2 trace(p_{T^perp} p_x) + 2 zeta grad zeta . p_x x'.
Here trace(p_{T^perp} p_x) = trace(p_x) - trace(p_T p_x) = n - trace(p_T p_x), while |p_x - p_T|^2 = trace((p_x - p_T)^2) = trace(p_x) + trace(p_T) - 2 trace(p_T p_x) = 2n - 2 trace(p_T p_x); hence trace(p_{T^perp} p_x) = s(x) := (1/2)|p_x - p_T|^2. Moreover p_T x' = 0, so p_x x' = (p_x - p_T) x'. Thus div_M X = zeta^2 s + 2 zeta grad zeta . (p_x - p_T) x' mu-a.e.

3. First variation. The functions zeta^2 s, zeta grad zeta . (p_x - p_T) x', and zeta^2 x' . H are mu-integrable (bounded measurable functions vanishing off B_r(z), resp. a bounded function times |H| on B_r(z)). The identity integral div_M X dmu = - integral X . H dmu gives
 integral zeta^2 s dmu = - integral 2 zeta grad zeta . (p_x - p_T) x' dmu - integral zeta^2 x' . H dmu.

4. Absorption. |(p_x - p_T) x'| <= ||p_x - p_T|| |x'| <= |p_x - p_T| |x'| = sqrt(2 s) |x'|. With a := zeta sqrt(s) and b := sqrt(2) |grad zeta| |x'|, 2ab <= (1/2) a^2 + 2 b^2 gives |2 zeta grad zeta . (p_x - p_T) x'| <= 2 sqrt(2) zeta sqrt(s) |grad zeta| |x'| <= (1/2) zeta^2 s + 4 |grad zeta|^2 |x'|^2. Therefore integral zeta^2 s <= (1/2) integral zeta^2 s + 4 integral |grad zeta|^2 |x'|^2 + integral zeta^2 |x'| |H|, and since integral zeta^2 s < infinity,
 integral zeta^2 s dmu <= 8 integral |grad zeta|^2 |x'|^2 dmu + 2 integral zeta^2 |x'| |H| dmu.

5. Conclusion. Since zeta = 1 on B_{r/2}(z) and s >= 0, (1/2) integral_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= integral zeta^2 s dmu. Since |grad zeta|^2 <= 9/r^2 and grad zeta = 0 off B_r(z), 8 integral |grad zeta|^2 |x'|^2 dmu <= 72 r^(-2) integral_{B_r(z)} dist(x - z, T)^2 dmu. Since zeta^2 <= indicator of B_r(z) and |x'| <= h for mu-a.e. x in B_r(z) (such x lie in spt V cap B_r(z), where dist(x - z, T) <= h by hypothesis), 2 integral zeta^2 |x'| |H| dmu <= 2 h integral_{B_r(z)} |H| dmu. Multiplying by 2:
 integral_{B_{r/2}(z)} |p_x - p_T|^2 dmu <= 144 r^(-2) integral_{B_r(z)} dist(x - z, T)^2 dmu + 4 h integral_{B_r(z)} |H| dmu,
which is the assertion (with |p_x - p_T|^2 = hsNormSq(V.tangentProj x - T.starProjection)).

## Key steps

1. aal_tangent_structure: p_x is a rank-n orthogonal projection mu-a.e. and measurable; all integrands are integrable on B_r(z).
2. Test field X = zeta^2 p_{T^perp}(x - z) with zeta = phi(|x-z|/r), |grad zeta| <= 3/r, tsupport in B_r(z).
3. div_M X = zeta^2 (1/2)|p_x - p_T|^2 + 2 zeta grad zeta . (p_x - p_T) x'.
4. First variation plus 2ab <= a^2/2 + 2b^2 absorbs the gradient term: int zeta^2 s <= 8 int |grad zeta|^2 |x'|^2 + 2 int zeta^2 |x'||H|.
5. Use zeta = 1 on B_{r/2}, |grad zeta| <= 3/r and |x'| <= h mu-a.e. on B_r(z).

## Reference use

### local-project

Queries:
- `timeout 500 rg -n 'aal_|affine_approximation_lemma' <snapshot>/project`
- `grep -n 'lemma measure_compl_support' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `grep -rn 'theorem lintegral_mul_le_Lp_mul_Lq' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `grep -n 'theorem mul_meas_ge_le_lintegral₀' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `grep -n 'theorem hausdorffMeasure_homothety_image' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep -rn 'theorem finrank_span_eq_card' <snapshot>/mathlib/Mathlib/LinearAlgebra/Dimension/`
- `grep -rn 'theorem volume_ball' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `grep -rn 'theorem.*infDist' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/*.lean`
- `grep -n '^def \|^theorem ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt, .unique)`
- `grep -n 'lpMeanCurvatureKappa|LpAnnularCorrection|exists_lpAnnularCorrection|def radialNormalSq|def HasGeneralizedMeanCurvatureIn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/*.lean`
- `grep -rn 'area_image_criticalSet_eq_zero|area_formula_lipschitz_multiplicity|simon_remark_1_3|simon_theorem_1_17|contDiff_whitneyExtension|exists_contDiff_one_extension_of_whitney|simon_theorem_3_6|rademacher_ae_differentiableAt|injective_area_formula_lipschitz_simon' .lake/packages/simongmt/Poincare/SimonGMT`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all 8 child lean_statements`
- `lake env lean /tmp/claude-1000/aal-check/Check2.lean (Contract lines 1-459 + 8 sorried child types in GMT.Ch05.Submission + sorry-free assembly aal_assembly_check : AffineApproximationLemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/LpAnnular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-03-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-04-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-05-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/claude-1000/aal-check/Check2.lean`

Snapshot a7f8fcd21d5c8fc7 pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d (manifest.json).

No prior declarations: 'aal_' and 'affine_approximation_lemma' have no matches in the snapshot project, and no DAG node reserves an aal_ name.

Mathlib items located for the children and the assembly (paths under mathlib/Mathlib):
- Measure.measure_compl_support (MeasureTheory/Measure/Support.lean:202): mu-a.e. point lies in spt V.
- lintegral_mul_le_Lp_mul_Lq (MeasureTheory/Integral/MeanInequalities.lean:202): Hoelder.
- mul_meas_ge_le_lintegral₀ (MeasureTheory/Integral/Lebesgue/Markov.lean:52): Chebyshev.
- hausdorffMeasure_homothety_image (MeasureTheory/Measure/Hausdorff.lean:1060): H^n scaling of blow-ups.
- finrank_span_eq_card (LinearAlgebra/Dimension/Constructions.lean:463): used in the Lean assembly to show finrank(horizontalPlane n l) = n.
- EuclideanSpace.volume_ball (MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:307): omega_n.
- Submodule.dist_starProjection_eq_infDist (Analysis/InnerProductSpace/Projection/Basic.lean:234): dist(v,T) = |v - p_T v|.

Pinned SimonGMT (outside the snapshot; paths under .lake/packages/simongmt/Poincare/SimonGMT), what it provides:
- HasWeightedApproximateTangentSpaceAt and .unique (Chapter03/Rectifiable.lean:330, 345).
- simon_remark_1_3 and simon_remark_1_3_nullMeasurable (Chapter03/DisjointCover.lean:90).
- Lusin, simon_theorem_1_17 (Chapter01/Lusin.lean:328).
- Upper density, simon_theorem_3_6 (Chapter01/DensityComparison.lean:332).
- rademacher_ae_differentiableAt (Chapter02/Lipschitz.lean:192).
- exists_contDiff_one_extension_of_whitney (Chapter02/WhitneyExtension.lean:373).
- area_image_criticalSet_eq_zero (Chapter02/AreaCritical.lean:185).
- area_formula_lipschitz_multiplicity (Chapter02/AreaNoninjective.lean:144).
- injective_area_formula_lipschitz_simon (Chapter02/AreaLipschitz.lean:126).

What SimonGMT lacks:
- Only the easy direction of Ch. 3 Lemma 1.2 (Chapter03/SubmanifoldCover.lean).
- No C^1 approximation theorem and no Thm 1.9. So aal_tangent_structure carries the printed proofs, and that child should expect to split further.

Chapter04 monotonicity:
- lpMeanCurvatureKappa = (p-n)/(4p) (LpMeanCurvature.lean:76).
- LpAnnularCorrection and exists_lpAnnularCorrection (LpAnnular.lean:335, 358) match aal_lp_monotonicity field by field, including the larger ball S > R.
- They are stated for the strengthened Chapter04.RectifiableVarifold, so reuse needs a bridge; this is not assumed.

Lean check:
- All 8 child types elaborate in the contract scope and pass validate_lean_statement.
- The assembly aal_assembly_check : AffineApproximationLemma compiles from aal_tilt_height_curvature_bound and aal_height_bound_small_delta. The only warnings are sorry warnings for the placeholder children, plus a push_neg deprecation warning in the scratch assembly.
