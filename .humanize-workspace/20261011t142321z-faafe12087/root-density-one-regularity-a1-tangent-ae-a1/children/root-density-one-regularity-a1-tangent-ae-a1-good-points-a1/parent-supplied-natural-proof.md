# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_regularity-a1.tangent_ae-a1`
- Child DAG node: `root.density_one_regularity-a1.tangent_ae-a1.good_points-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4 ('Tangent spaces at good points', proof of Simon 1.6 'only if' with Remark 1.8(1)), with the parent's piece C_{m,i,k} = C_{m,i} cap M_k replaced by C' := C cap N and the parent's finite measure mu_m by mu restricted to a compact neighbourhood K' of C in U. Notation and conventions (shared): H^n = muHE[n] (Mathlib's normalized n-dimensional Hausdorff measure; on R^n it equals Lebesgue measure L^n = volume, Mathlib InnerProductSpace.euclideanHausdorffMeasure_eq_volume, and on an n-dimensional subspace P it is n-dimensional Lebesgue measure on P, so H^n(P cap B_s(0)) = omega_n s^n). Balls B_s(y) are closed, B'_s(y) open. eta_{x,r}(y) = r^{-1}(y - x) (SimonGMT blowUpMap). For r > 0, eta_{x,r} is a homeomorphism (a similarity with ratio 1/r), H^n(eta_{x,r}(S)) = r^{-n} H^n(S) for every set S, and the pushforward of H^n restricted to eta_{x,r}(S) under eta_{x,r}^{-1}(y) = x + r y is r^{-n} H^n restricted to S (SimonGMT Chapter04 hausdorff_blowUp_image, map_inverse_blowUp_carrier). Consequently, for every set S and every function h (Bochner integrals, the identity holding exactly, including the value 0 for non-integrable integrands, because it comes from a measurable embedding and a scalar multiple of a measure):
(CV) int_{eta_{x,r}(S)} h(y) dH^n(y) = r^{-n} int_S h(eta_{x,r}(z)) dH^n(z), and H^n(eta_{x,r}(S) cap B_R(0)) = r^{-n} H^n(S cap B_{rR}(x)).
Write mu := V.weight = theta H^n restricted to M, C' := C cap N (Borel, contained in M and in N), ||f|| := sup|f|.
1. (Compact neighbourhood.) If C is empty there is nothing to prove. C is compact and contained in the open set U (C contained in M contained in U), so there is delta > 0 with K' := {y : dist(y, C) <= delta} contained in U (Mathlib IsCompact.exists_cthickening_subset_open); K' is closed and bounded, hence compact. Since theta is integrable on M cap K' (contract field integrableOn_mult), mu' := mu restricted to K' is a finite Borel measure; H^n restricted to N is a finite Borel measure (H^n(N) < infinity). Both are Borel regular in Simon's sense (SimonGMT Chapter01.measure_toOuterMeasure_isBorelRegular: the outer measure of a Borel measure is Borel regular).
2. (Upper Density Theorem.) By the Upper Density Theorem (Simon Ch. 1, 3.6; SimonGMT Chapter01.simon_theorem_3_6, whose Hausdorff measure simonHausdorffOuterMeasureReal n is a positive finite multiple of mu_H[n] by simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure, as is muHE[n] by Mathlib euclideanHausdorffMeasure_def, so the two have the same null sets):
   (i) applied to H^n restricted to N and the Borel set N \ C': there is an H^n-null set E_1 such that for every x outside (N \ C') union E_1, rho^{-n} H^n((N \ C') cap B_rho(x)) -> 0 as rho -> 0+;
   (ii) applied to the finite Borel regular measure mu' and the Borel set R^(n+l) \ C' (finite mu'-measure): there is an H^n-null set E_2 such that for every x in C' \ E_2, rho^{-n} mu'((R^(n+l) \ C') cap B_rho(x)) -> 0 as rho -> 0+. Since mu' is carried by M (mu'(S) = mu'(S cap M) for every set S), mu'((R^(n+l) \ C') cap B_rho(x)) = mu'((M \ C') cap B_rho(x)); hence rho^{-n} mu'((M \ C') cap B_rho(x)) -> 0 for every x in C' \ E_2.
   E := E_1 union E_2 is H^n-null and does not depend on any test function. It suffices to prove the weighted tangent property at every x in C' \ E (the set of x in C' where it fails is then contained in E, hence H^n-null, which is the asserted a.e. statement for H^n restricted to C'). Fix such an x; x is not in N \ C', so both (i) and (ii) apply at x.
3. (Dimension.) x is in N, so dim T(x) = n by the hypothesis on N.
4. (Splitting.) Fix f in C_c(R^(n+l)) and R >= 1 with f = 0 outside B_R(0); let r_0 := delta/R, so that B_{rR}(x) is contained in K' for 0 < r < r_0 (x in C). For such r define I(r) := int_{eta_{x,r}(M)} f(y) theta(x + r y) dH^n(y). By (CV) with h(y) := f(y) theta(x + r y), and since x + r eta_{x,r}(z) = z:
   I(r) = r^{-n} int_M f(eta_{x,r} z) theta(z) dH^n(z).
   The integrand is a.e.-measurable for H^n restricted to M (theta is, f o eta_{x,r} is continuous), vanishes outside B_{rR}(x), contained in K', and is bounded by ||f|| theta 1_{K'}, which is integrable on M; so it is integrable and, as C' is contained in M, I(r) = I_1(r) + theta(x) I_2(r) + I_3(r) with
   I_1(r) := r^{-n} int_{M \ C'} f(eta_{x,r} z) theta(z) dH^n(z), I_2(r) := r^{-n} int_{C'} f(eta_{x,r} z) dH^n(z), I_3(r) := r^{-n} int_{C'} f(eta_{x,r} z)(theta(z) - theta(x)) dH^n(z)
   (all finite: f o eta is bounded, H^n(C') <= H^n(N) < infinity, theta is integrable on C', contained in M cap K').
5. (I_1 -> 0.) |I_1(r)| <= ||f|| r^{-n} int_{(M \ C') cap B_{rR}(x)} theta dH^n = ||f|| r^{-n} mu'((M \ C') cap B_{rR}(x)) = ||f|| R^n (rR)^{-n} mu'((M \ C') cap B_{rR}(x)) -> 0 by 2(ii).
6. (I_2 -> int_{T(x)} f.) By (CV), I_2(r) = int_{eta_{x,r}(C')} f dH^n. eta_{x,r}(N) is the disjoint union of the Borel sets eta_{x,r}(C') and eta_{x,r}(N \ C') and has finite measure r^{-n}H^n(N), so I_2(r) = int_{eta_{x,r}(N)} f dH^n - int_{eta_{x,r}(N \ C')} f dH^n. The first term tends to int_{T(x)} f dH^n because T(x) is the approximate tangent space of N at x in N. For the second, |int_{eta_{x,r}(N \ C')} f dH^n| <= ||f|| H^n(eta_{x,r}(N \ C') cap B_R(0)) = ||f|| r^{-n} H^n((N \ C') cap B_{rR}(x)) = ||f|| R^n (rR)^{-n} H^n((N \ C') cap B_{rR}(x)) -> 0 by 2(i).
7. (Local mass bound.) Let phi in C_c(R^(n+l)) with 0 <= phi <= 1 and phi = 1 on B_R(0) (e.g. phi(y) = min(1, max(0, R + 1 - |y|))). Then r^{-n} H^n(C' cap B_{rR}(x)) <= r^{-n} H^n(N cap B_{rR}(x)) = H^n(eta_{x,r}(N) cap B_R(0)) <= int_{eta_{x,r}(N)} phi dH^n -> int_{T(x)} phi dH^n < infinity. Hence there are r_1 in (0, r_0) and Lambda < infinity with r^{-n} H^n(C' cap B_{rR}(x)) <= Lambda for 0 < r < r_1.
8. (I_3 -> 0.) Let omega(s) := sup{|theta(z) - theta(x)| : z in C, |z - x| <= s}; omega(s) -> 0 as s -> 0+ by continuity of theta restricted to C at x in C. For 0 < r < r_1, as f(eta_{x,r} z) = 0 unless |z - x| <= rR, |I_3(r)| <= ||f|| omega(rR) r^{-n} H^n(C' cap B_{rR}(x)) <= ||f|| Lambda omega(rR) -> 0.
9. (Conclusion.) By steps 4-8, I(r) -> theta(x) int_{T(x)} f dH^n as r -> 0+, for every f in C_c(R^(n+l)); with step 3 this is HasWeightedApproximateTangentSpaceAt n M theta x (T x). This holds for every x in C' \ E, hence for H^n-a.e. x in C cap N.

## Key steps

1. Choose a compact neighbourhood K' of C inside U; mu restricted to K' and H^n restricted to N are finite Borel measures
2. Upper Density Theorem twice: outside an H^n-null set E, N \ C' and M \ C' have zero n-density at points of C' = C cap N
3. Change of variables splits the weighted blow-up into the M \ C' part, theta(x) times the C' part, and the oscillation part
4. The M \ C' part vanishes in the limit by the density of mu' on M \ C'
5. The C' part converges to int_{T(x)} f because N has tangent T(x) and N \ C' has zero density
6. The oscillation part vanishes by continuity of theta on C and the local mass bound from the tangent of N

## Reference use

### local-project

Queries:
- `grep -n '^def \|^theorem \|^noncomputable def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 1,365p (CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt, HasWeightedApproximateTangentSpaceAt, .unique)`
- `cat .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/{SubmanifoldCover,Differential,DisjointCover,CoordinateProjection}.lean`
- `grep -rn -i 'approximation theorem\|theorem_1_5\|C¹ approximation\|c1_approximation\|contDiff_approx' .lake/packages/simongmt/Poincare/SimonGMT`
- `grep -n '^theorem \|^def ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter02/*.lean; sed -n on Chapter02/{AreaCritical,AreaFormula,WeightedArea,Area,AreaLinearWeighted,Lipschitz,WhitneyExtension,WhitneyJet}.lean`
- `sed -n on .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/{Lusin,DensityComparison,Densities,Hausdorff,Basic}.lean (simon_theorem_3_6, simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure, measure_toOuterMeasure_isBorelRegular)`
- `sed -n on .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/{TangentDensity,WeightedBlowUp,WeightedDensity,ClassicalTangent,LowerDensityTangents,MultiplicityBridge}.lean`
- `rg -n -i 'lusin' <snapshot>/mathlib/Mathlib`
- `rg -n 'aestronglyMeasurable_iUnion_iff|ae_restrict_iUnion_iff|ae_restrict_union_iff|ContinuousOn.aestronglyMeasurable|aestronglyMeasurable_zero_measure|restrict_eq_zero|ae_restrict_mem' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -n 'WeaklyRegular.of_pseudoMetrizableSpace|exists_isClosed_sdiff_lt|exists_isClosed_diff_lt' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'measurableSet_of_differentiableAt|measurable_fderiv|isOpen_iUnion_countable|integral_withDensity_eq_integral_toReal_smul₀|tendsto_integral_filter_of_dominated_convergence|exists_measurable_superset_of_null|exists_measurable_subset_ae_eq|euclideanHausdorffMeasure_eq_volume|LipschitzWith.ae_differentiableAt|tendstoUniformlyOn_of_ae_tendsto' <snapshot>/mathlib/Mathlib`
- `sed -n 150,300p book/chapter-02.txt (Thm 1.5 and its printed proof, Whitney 1.6); sed -n 1,360p book/chapter-03.txt (1.1-1.9)`
- `cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean`
- `python3 scan of all lean_name fields in dag.json and nodes/**/*.json; grep -rl <six proposed names> .humanize GMT .lake/packages/simongmt`
- `lake env lean /tmp/tae-dec-k7q2/Check7.lean (contract lines 1-460 + six children as sorry + full parent assembly + #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLinearWeighted.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-tangent-ae-a1/parent-supplied-natural-proof.md`
- `/tmp/tae-dec-k7q2/Check7.lean`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace copy (cmp).

What SimonGMT already has:
- the definitions CountablyRectifiable, blowUpMap, HasApproximateTangentSpaceAt and HasWeightedApproximateTangentSpaceAt, with uniqueness;
- Whitney C^1 extension (exists_contDiff_one_extension_of_whitney);
- the critical-image theorem (area_image_criticalSet_eq_zero);
- Bochner and linear area formulas (integral_area_formula_of_injective_derivative, measurePreserving_linearMap_normDet_smul);
- the Lipschitz image bound;
- Lusin for weakly regular finite measures;
- the Upper Density Theorem (simon_theorem_3_6) with the Hausdorff normalization bridge and measure_toOuterMeasure_isBorelRegular;
- generic blow-up scaling lemmas (hausdorff_blowUp_image, map_inverse_blowUp_carrier, planeMeasure_unit_closedBall, tangentDensityCutoff).

What no searched source has (grep/rg no-match):
- no a.e.-existence result for (weighted) approximate tangents (Simon 1.6/1.9);
- no Lemma 1.2 'only if' (SubmanifoldCover.lean says it 'remains a separate theorem');
- no C^1 approximation theorem (Simon 2.1.5);
- Mathlib has no Lusin continuity theorem (only Lusin separation / Lusin-Souslin).

Mathlib gluing and regularity lemmas used by the assembly and the child proofs exist: aestronglyMeasurable_iUnion_iff, ae_restrict_iUnion_iff, ContinuousOn.aestronglyMeasurable, MeasurableSet.exists_isClosed_sdiff_lt, Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, and others.

Lean check:
- All six child types elaborate in the contract scope.
- The parent assembly compiles to the exact frozen type, with axioms propext, Classical.choice, Quot.sound plus sorryAx from the six children only.

The six tae_ names have no match in .humanize, GMT or simongmt.
