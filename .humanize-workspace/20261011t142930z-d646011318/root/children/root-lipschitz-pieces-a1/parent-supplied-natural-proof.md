# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.lipschitz_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. n ≥ 1 and ℓ ≥ 0 are integers; ℝⁿ := EuclideanSpace ℝ (Fin n) with Lebesgue measure Lⁿ (volume) and Euclidean norm |·|; E := Ambient n ℓ = ℝ^{n+ℓ}; Hⁿ := μHE[n] (on E, and on ℝⁿ, where Hⁿ = Lⁿ by Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume); B_r(q) is the closed ball; a linear map L: ℝⁿ → E is injective iff min_{|e|=1}|Le| > 0. Lip(F) denotes a Lipschitz constant of F. M is countably n-rectifiable (Simon Ch. 3, 1.1; Poincare.SimonGMT.Chapter03.CountablyRectifiable n M): M ⊆ M_0 ∪ ⋃_{j∈ℕ} F_j(ℝⁿ) with Hⁿ(M_0) = 0 and every F_j: ℝⁿ → E Lipschitz.

Source and role. Simon Ch. 3, Lemma 1.2 ('only if') covers M, up to an Hⁿ-null set, by countably many embedded C¹ submanifolds, using the C¹ Approximation Theorem (Ch. 2, Thm 1.5), whose printed proof rests on Whitney's extension theorem (Ch. 2, Thm 1.6, quoted there without proof). Neither theorem is available as an axiom-checked declaration in the pinned references: GMT/Ch02/Contract.lean states C1Approximation and WhitneyExtension only as unproved conjuncts of the Chapter 2 contract, and SimonGMT's Chapter02/WhitneyExtension.lean is not part of the built library. The printed proofs of Ch. 3, 1.6 '⇒', 1.8(1), 1.9 and of the area formula 2.4 use the submanifolds only through countably many injective parametrizations whose derivative is injective and continuous on the parameter set. This lemma provides exactly such a covering, by Lipschitz pieces with continuous injective derivative on compact parameter sets, directly from Rademacher's theorem, the Lipschitz area formula and Lusin's theorem. All results used are pinned, axiom-checked declarations (standard axioms only):
(L1) Rademacher (Simon Ch. 2, 1.4): a Lipschitz map ℝⁿ → E is differentiable Lⁿ-a.e. [Mathlib LipschitzWith.ae_differentiableAt; SimonGMT Chapter02.rademacher_ae_differentiableAt].
(L2) Lipschitz images (Simon Ch. 2, 1.8(i)): Hⁿ(F(A)) ≤ Lip(F)ⁿ Hⁿ(A) for every A ⊆ ℝⁿ [SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn].
(L3) Regular set and the null image of its complement (area formula, Simon Ch. 2, §3): for Lipschitz F: ℝⁿ → E the set R_F := {w : F is differentiable at w and DF(w) is injective} (SimonGMT Chapter02.areaRegularSet F) is Borel [Chapter02.measurableSet_areaRegularSet], and Hⁿ(F(S ∖ R_F)) = 0 for every S ⊆ ℝⁿ [Chapter02.area_image_compl_regularSet_eq_zero].
(L4) w ↦ DF(w) is Borel measurable [Mathlib measurable_fderiv].
(L5) Lusin (Simon Ch. 1, 1.17): if ν is a Borel measure on ℝⁿ that is inner regular by closed sets on Borel sets of finite measure, A is Borel with ν(A) < ∞ and g: ℝⁿ → ℝ is Borel, then for each δ > 0 there is a closed C ⊆ A with ν(A ∖ C) < δ and g continuous on C [SimonGMT Chapter01.exists_isClosed_continuousOn_of_measurable]. Lⁿ is weakly regular, so it is inner regular by closed sets on Borel sets of finite measure [Mathlib MeasurableSet.exists_isClosed_sdiff_lt], and also by compact sets.
(L6) Every Hⁿ-null set is contained in a Borel Hⁿ-null set [Mathlib MeasureTheory.exists_measurable_superset_of_null].

Step 1 (regular points lie in Borel sets of uniform local injectivity). Fix a Lipschitz map F: ℝⁿ → E. For an integer k ≥ 1 let
S_k := R_F ∩ ⋂_{u ∈ ℝⁿ, |u| ≤ 1/k} {w ∈ ℝⁿ : |F(w + u) − F(w)| ≥ |u|/k}.
For fixed u the set {w : |F(w + u) − F(w)| ≥ |u|/k} is closed because F is continuous, so the intersection over u is closed, and S_k (a closed set intersected with the Borel set R_F) is Borel. We claim R_F = ⋃_{k≥1} S_k. The inclusion ⊇ is clear. Let w ∈ R_F. Since DF(w) is injective and the unit sphere of ℝⁿ is compact and nonempty (n ≥ 1), m := min_{|e|=1}|DF(w)e| > 0, so |DF(w)u| ≥ m|u| for all u ∈ ℝⁿ. By differentiability of F at w there is r > 0 with |F(w + u) − F(w) − DF(w)u| ≤ (m/2)|u| whenever |u| ≤ r; then |F(w + u) − F(w)| ≥ |DF(w)u| − (m/2)|u| ≥ (m/2)|u| for |u| ≤ r. Choose an integer k ≥ max(2/m, 1/r). For |u| ≤ 1/k we have |u| ≤ r, hence |F(w + u) − F(w)| ≥ (m/2)|u| ≥ |u|/k; so w ∈ S_k.

Step 2 (injectivity with a lower Lipschitz bound). Fix k ≥ 1 and an enumeration (q_m)_{m∈ℕ} of the points of ℝⁿ with rational coordinates. The closed balls Q_{k,m} := B_{1/(2k)}(q_m), m ∈ ℕ, cover ℝⁿ (these points are dense). If v, w ∈ S_k ∩ Q_{k,m}, then |v − w| ≤ 1/k, and the defining property of S_k at the point w, applied with u := v − w, gives
(2.1) |F(v) − F(w)| ≥ |v − w|/k for all v, w ∈ S_k ∩ Q_{k,m}.

Step 3 (compact pieces on which DF is continuous; Lusin). Fix k, m and put S := S_k ∩ Q_{k,m}, a bounded Borel set, so Lⁿ(S) < ∞. Fix j ≥ 1. Choose orthonormal bases (e_a) of ℝⁿ and (e'_b) of E; the N := n(n + ℓ) matrix entries g_{ab}(w) := ⟨DF(w)e_a, e'_b⟩ are real Borel functions by (L4) (evaluation at e_a and the inner product with e'_b are continuous). For each (a, b), (L5) applied to ν := Lⁿ, A := S and g := g_{ab} gives a closed D_{ab} ⊆ S with Lⁿ(S ∖ D_{ab}) < 1/(2Nj) on which g_{ab} is continuous; inner regularity of Lⁿ gives a compact K' ⊆ S with Lⁿ(S ∖ K') < 1/(2j). Put C_{k,m,j} := K' ∩ ⋂_{a,b} D_{ab}. Then C_{k,m,j} is compact, C_{k,m,j} ⊆ S, Lⁿ(S ∖ C_{k,m,j}) < 1/(2j) + N/(2Nj) = 1/j, and every entry of DF is continuous on C_{k,m,j}; since DF(w) = Σ_{a,b} g_{ab}(w)·E_{ab} with the fixed linear maps E_{ab} := ⟨e_a, ·⟩e'_b, w ↦ DF(w) is continuous on C_{k,m,j}. The set Z_{k,m} := S ∖ ⋃_{j≥1} C_{k,m,j} satisfies Lⁿ(Z_{k,m}) ≤ Lⁿ(S ∖ C_{k,m,j}) < 1/j for every j, hence Lⁿ(Z_{k,m}) = 0.

Step 4 (properties of each piece). Let C := C_{k,m,j}. Then: C is compact; C ⊆ S_k ⊆ R_F, so F is differentiable at every w ∈ C and DF(w) is injective; w ↦ DF(w) is continuous on C (Step 3); and, as C ⊆ S_k ∩ Q_{k,m}, (2.1) gives (1/k)|v − w| ≤ |F(v) − F(w)| for all v, w ∈ C, so the constant c := 1/k > 0 works.

Step 5 (the remainder has null image). By Steps 1 and 2, ℝⁿ = (ℝⁿ ∖ R_F) ∪ ⋃_{k≥1, m∈ℕ} (S_k ∩ Q_{k,m}), and by Step 3, S_k ∩ Q_{k,m} ⊆ Z_{k,m} ∪ ⋃_{j≥1} C_{k,m,j}. Hence F(ℝⁿ) ⊆ F(ℝⁿ ∖ R_F) ∪ F(Z_F) ∪ ⋃_{k,m,j} F(C_{k,m,j}) with Z_F := ⋃_{k,m} Z_{k,m}, a countable union of Lⁿ-null sets. By (L3), Hⁿ(F(ℝⁿ ∖ R_F)) = 0; by (L2) and Hⁿ = Lⁿ on ℝⁿ, Hⁿ(F(Z_F)) ≤ Lip(F)ⁿ Lⁿ(Z_F) = 0. So Y_F := F(ℝⁿ ∖ R_F) ∪ F(Z_F) is Hⁿ-null and F(ℝⁿ) ⊆ Y_F ∪ ⋃_{k,m,j} F(C_{k,m,j}).

Step 6 (all parametrizations; conclusion). Write M ⊆ M_0 ∪ ⋃_{j∈ℕ} F_j(ℝⁿ) as in 1.1 and apply Steps 1–5 to every F_j, obtaining compact pieces C^{(j)}_{k,m,p} (k ≥ 1, m ∈ ℕ, p ≥ 1) with the properties of Step 4 for the map F_j (constant 1/k), and Hⁿ-null sets Y_{F_j}. The set of all quadruples (j, k, m, p) is countable; fix a bijection from ℕ onto it, i ↦ (j(i), k(i), m(i), p(i)), and put F_i := F_{j(i)} (Lipschitz) and C_i := C^{(j(i))}_{k(i),m(i),p(i)}. Then
M ⊆ M_0 ∪ ⋃_j Y_{F_j} ∪ ⋃_{i∈ℕ} F_i(C_i),
and N_0' := M_0 ∪ ⋃_j Y_{F_j} is Hⁿ-null as a countable union of null sets. By (L6) there is a Borel set N_0 ⊇ N_0' with Hⁿ(N_0) = 0, and M ⊆ N_0 ∪ ⋃_i F_i(C_i). For every i, C_i is compact, F_i is Lipschitz, F_i is differentiable at every w ∈ C_i with injective derivative, w ↦ DF_i(w) is continuous on C_i, and c_i := 1/k(i) > 0 satisfies c_i|v − w| ≤ |F_i(v) − F_i(w)| for all v, w ∈ C_i (Step 4). This is the assertion.

## Key steps

1. Rademacher and the area formula: the image of the non-regular set ℝⁿ ∖ R_F (DF missing or not injective) is Hⁿ-null
2. R_F = ⋃_k S_k with S_k Borel, where |F(w+u) − F(w)| ≥ |u|/k for |u| ≤ 1/k
3. On S_k ∩ B_{1/(2k)}(q), F is injective with |F(v) − F(w)| ≥ |v − w|/k
4. Lusin (entrywise) and inner regularity give compact C ⊆ S_k ∩ B_{1/(2k)}(q) with DF|_C continuous, exhausting it up to an Lⁿ-null set whose image is Hⁿ-null
5. Enumerate the pieces of all parametrizations and absorb the null images into a Borel Hⁿ-null N_0

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `rg -n 'def C1Approximation|def WhitneyExtension|def Rademacher' <snapshot>/project/GMT`
- `rg -n 'theorem .*[Ll]usin' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem ae_tendsto_measure_inter_div|theorem exists_measurable_superset_of_null|theorem measurableSet_of_differentiableAt |theorem measurable_fderiv |euclideanHausdorffMeasure_eq_volume' <snapshot>/mathlib/Mathlib`
- `rg -n 'exists_disjoint_subfamily_covering_enlargement_closedBall|geometric_hahn_banach_point_closed|lintegral_eq_lintegral_meas_lt|eq_pos_convex_span_of_mem_convexHull|isCompact_convexHull|measure_compl_support|normDet_comp|exists_isClosed_diff_lt|ext_of_integral_eq_on_compactlySupported' <snapshot>/mathlib/Mathlib`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' <snapshot>/mathlib/Mathlib`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,WhitneyExtension}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/Rectifiable.lean`
- `grep -n 'Whitney' simongmt/Poincare/SimonGMT.lean; test -f simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02/WhitneyExtension.olean`
- `git -C lake-packages-25730c7c/simongmt rev-parse HEAD`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-v2-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-v2-audit/olean lean /tmp/ch04-v2-audit/ChildTypes.lean`
- `LEAN_PATH=... lean /tmp/ch04-v2-audit/Inspect.lean (rfl check of the elaborated piece-cover type; #print axioms of Mathlib lemmas)`
- `lake env lean /tmp/ch04-v2-audit/Axioms.lean (#print axioms of the cited SimonGMT lemmas)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/LocallyConvex/Separation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root/decomposition-audit-v1.json`
- `/tmp/ch04-v2-audit/ChildTypes.lean`
- `/tmp/ch04-v2-audit/Axioms.lean`

The snapshot contract (sha256 6e58e5dd…0f4770b) is byte-identical to the workspace Contract.lean and Submission.lean; the pinned SimonGMT revision is 2b3663083f3fe399b6296fb8eaee52169170e197 as in project/lake-manifest.json. No axiom-checked C¹ approximation or Whitney extension is available: project/GMT/Ch02/Contract.lean has C1Approximation and WhitneyExtension only as Props inside the sorry'd Ch. 2 main theorem, SimonGMT's Chapter02/WhitneyExtension.lean is not imported by Poincare/SimonGMT.lean and has no built olean, and the snapshot Mathlib has no Lusin-type C¹ approximation (no 'theorem …Lusin' match). The v2 split therefore replaces that step by the new child rectifiable_lipschitz_piece_cover, whose cited inputs exist and depend only on propext, Classical.choice and Quot.sound (#print axioms): SimonGMT Chapter02.rademacher_ae_differentiableAt, euclideanHausdorffMeasure_image_le_of_lipschitzOn, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn, Chapter01.exists_isClosed_continuousOn_of_measurable, ae_dimensionalUpperDensity_eq_zero_outside, simon_theorem_3_3, Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, Chapter03.support_euclideanHausdorffMeasure_restrict_submodule; Mathlib Besicovitch.ae_tendsto_measure_inter_div, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, measurable_fderiv, Measure.ext_of_integral_eq_on_compactlySupported. Also present: Mathlib LinearMap.normDet_comp, MeasurableSet.exists_isClosed_sdiff_lt, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, geometric_hahn_banach_point_closed, eq_pos_convex_span_of_mem_convexHull, lintegral_eq_lintegral_meas_lt, Measure.measure_compl_support; SimonGMT Chapter01.measure_toOuterMeasure_isBorelRegular, Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule, Chapter02.areaJacobian_comp_eq_parametrization_mul_tangential. No compact-convex-hull-of-compact-set lemma was found (only Set.Finite.isCompact_convexHull), so support_convex_hull proves compactness of conv K via Carathéodory. With GMT.Ch04.Submission compiled to an olean, all twelve child types elaborate after `import GMT.Ch04.Submission` inside `namespace GMT.Ch04` with the contract's opens and `open RectifiableVarifold`, the elaborated piece-cover type is checked by rfl against a fully explicit form (μHE[n] on Ambient n ℓ, fderiv on EuclideanSpace ℝ (Fin n)), and the parent assembly from the twelve sorry'd children typechecks with exactly the type of GMT.Ch04.main_theorem; the only diagnostics are the expected sorry warnings.
