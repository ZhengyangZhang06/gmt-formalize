# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.density_eq_multiplicity_ae-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, Remarks 1.8(1),(2) and Theorem 1.9 (density of θH^n⌞M equals θ H^n-a.e. on a countably n-rectifiable M) and Ch. 1, Theorem 3.6 with Remark 3.7(2) (upper density theorem), which the parent proof cites in step 3 ("Θ_S equals the multiplicity of S μ_S-a.e.") and in step 5(iii) ("μ_A = ϑ_A·H^n"). Notation: M := R.carrier, θ := R.mult, H^n := μHE[n], ν := H^n⌞M, μ := R.measure = θ·ν; for a Borel measure λ on ℝ^P and x ∈ ℝ^P put D(λ, x) := limsup_{ρ↓0} λ(B_ρ(x))/(ω_nρ^n) ∈ [0, ∞] (open balls; closed balls give the same value because B_ρ ⊆ B̄_ρ ⊆ B_{ρ(1+ε)}).
1. (Local finiteness.) θ ≥ 1 on M (mult_pos, ℕ-valued), so ν(K) ≤ μ(K) < ∞ for every compact K ⊆ ℝ^P. Thus ν and μ are locally finite Borel measures on ℝ^P (hence Radon and σ-finite, ℝ^P being σ-compact), and θ ∈ L¹_loc(ν) because ∫_K θ dν = μ(K) < ∞.
2. (Upper density theorem.) If λ is a locally finite Borel measure on ℝ^P and A ⊆ ℝ^P is Borel, then D(λ⌞A, x) = 0 for H^n-a.e. x ∈ ℝ^P ∖ A. This is Simon Ch. 1, Theorem 3.6 (for λ(A) < ∞) together with Remark 3.7(2) (cover ℝ^P by the open balls B_j(0), each of finite λ-measure); in the library it is SimonGMT `ae_dimensionalUpperDensity_eq_zero_outside_of_openSigmaFinite` (Chapter01/DensityComparison.lean), stated for the Borel regular outer measure λ (open-σ-finite because λ is locally finite), with closed-ball density quotients, and almost everywhere with respect to Simon's normalized Hausdorff measure `simonHausdorffMeasureReal n`, a positive constant multiple of μH[n]; closed and open balls give the same upper density, and the null sets of `simonHausdorffMeasureReal n`, μH[n] and μHE[n] coincide. [Proof sketch, Simon 1.3.3: for t > 0 and closed C ⊆ A, every x ∈ S_t := {x ∉ A : D(λ⌞A, x) ≥ t} satisfies D(λ⌞(A ∖ C), x) ≥ t, so the Vitali covering argument gives t·H^n(S_t) ≤ λ(A ∖ C), and λ(A ∖ C) can be made arbitrarily small.]
3. (Off M.) μ = μ⌞M, so by (2) with λ := μ and A := M, D(μ, x) = 0 for H^n-a.e. x ∈ ℝ^P ∖ M. At every such x the nonnegative ratio μ(B_ρ(x))/(ω_nρ^n) has limsup 0, hence tends to 0 = 1_M(x)θ(x).
4. (Lusin decomposition, Simon Ch. 3, Remark 1.8(1).) By Lusin's theorem (Simon Ch. 1, 1.17) applied to the measurable function θ and the locally finite measure ν, there are compact sets M_1 ⊆ M_2 ⊆ ⋯ ⊆ M with θ|M_j continuous and ν(M ∖ ∪_jM_j) = 0. By (2) with A := M ∖ M_j and λ := ν, resp. λ := μ: D(ν⌞(M ∖ M_j), x) = 0 and D(μ⌞(M ∖ M_j), x) = 0 for H^n-a.e. x ∈ M_j.
5. (Approximate tangent planes.) By the field `orients` of the structure IMRep, for H^n-a.e. x ∈ M there is an n-dimensional subspace Q_x with HasApproximateTangentSpaceAt n M x Q_x, i.e. ∫_{η_{x,r}(M)} f dH^n → ∫_{Q_x} f dH^n as r ↓ 0 for every f ∈ C_c(ℝ^P) (these integrals are those of the locally finite measures H^n⌞η_{x,r}(M), by (1) and scaling). Let G be the set of x ∈ M such that x has such a Q_x, x ∈ M_j for some j, and the two upper densities in (4) vanish at x for every j with x ∈ M_j; by (4), (5) and ν(M ∖ ∪M_j) = 0, H^n(M ∖ G) = 0.
6. (Density of ν at x ∈ G.) H^n(η_{x,ρ}(A)) = ρ^{−n}H^n(A) for every A (homothety scaling of μHE[n], Mathlib `euclideanHausdorffMeasure_homothety_image`), so ν(B_ρ(x))/ρ^n = H^n(η_{x,ρ}(M) ∩ B_1(0)). For ε ∈ (0, 1) choose continuous f, g : ℝ^P → [0, 1] with compact support and 1_{B_{1−ε}(0)} ≤ f ≤ 1_{B_1(0)} ≤ g ≤ 1_{B_{1+ε}(0)}. Then ∫_{Q_x} f dH^n ≤ liminf_{ρ↓0} H^n(η_{x,ρ}(M) ∩ B_1(0)) ≤ limsup_{ρ↓0} H^n(η_{x,ρ}(M) ∩ B_1(0)) ≤ ∫_{Q_x} g dH^n, and H^n(Q_x ∩ B_s(0)) = ω_ns^n (μHE[n] on the n-dimensional subspace Q_x is the image of Lebesgue measure of ℝ^n under a linear isometry; Mathlib `Isometry.euclideanHausdorffMeasure_image`, `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`). So ω_n(1 − ε)^n ≤ liminf ≤ limsup ≤ ω_n(1 + ε)^n for every ε, i.e. ν(B_ρ(x))/(ω_nρ^n) → 1. (The scaling of μHE[n] under dilations used here is the accepted `Submission.dtc_hausdorff_dilation`, which may be reused.)
7. (Density of μ at x ∈ G.) Let x ∈ G ∩ M_j. Then μ(B_ρ(x)) = ∫_{M_j ∩ B_ρ(x)} θ dH^n + μ⌞(M ∖ M_j)(B_ρ(x)). The second term is o(ρ^n) because D(μ⌞(M ∖ M_j), x) = 0. Given ε > 0, continuity of θ|M_j at x gives |θ(y) − θ(x)| ≤ ε for y ∈ M_j ∩ B_ρ(x) and small ρ, so the first term lies between (θ(x) − ε)ν(M_j ∩ B_ρ(x)) and (θ(x) + ε)ν(M_j ∩ B_ρ(x)); and ν(M_j ∩ B_ρ(x)) = ν(B_ρ(x)) − ν⌞(M ∖ M_j)(B_ρ(x)) = ω_nρ^n(1 + o(1)) by (6) and D(ν⌞(M ∖ M_j), x) = 0. Hence θ(x) − ε ≤ liminf μ(B_ρ(x))/(ω_nρ^n) ≤ limsup ≤ θ(x) + ε for every ε > 0, so μ(B_ρ(x))/(ω_nρ^n) → θ(x) = 1_M(x)θ(x).
8. (Conclusion.) The exceptional set is contained in the union of the H^n-null sets of (3) and of M ∖ G, so the ratio μ(B_ρ(x))/(ω_nρ^n) tends to 1_M(x)θ(x) in [0, ∞] for μHE[n]-a.e. x ∈ ℝ^P. ∎

## Key steps

1. ν := μHE[n]⌞M ≤ μ_R, so ν and μ_R are locally finite and θ ∈ L¹_loc(ν).
2. Upper density theorem (Simon 1.3.6, 1.3.7(2)): the upper density of λ⌞A vanishes H^n-a.e. off A.
3. Off M the density of μ_R is 0 H^n-a.e.
4. Lusin: compact M_j ⊆ M with θ|M_j continuous exhaust M up to a ν-null set; the upper densities of ν⌞(M∖M_j), μ_R⌞(M∖M_j) vanish H^n-a.e. on M_j.
5. At points with an approximate tangent plane (field `orients`), ν(B_ρ(x))/(ω_nρ^n) → 1, by homothety scaling and continuous cutoffs.
6. Continuity of θ on M_j gives μ_R(B_ρ(x))/(ω_nρ^n) → θ(x) H^n-a.e. on M.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -n '^theorem\|^def' simongmt Chapter02/{AreaNoninjective,AreaLipschitz,AreaMultiplicity,AreaBranches,AreaApproximation,WeightedArea}.lean Chapter03/{Rectifiable,Differential,SubmanifoldCover}.lean`
- `grep -rn 'weighted_area_formula_lipschitz_injOn|area_image_compl_regularSet_eq_zero|measurable_areaJacobianAt|weightedAreaFiberSum_iUnion|exists_injective_partition_of_regular|ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt/Poincare/SimonGMT`
- `grep -rn 'normDet_sq_eq_det_gram|normDet_comp|euclideanHausdorffMeasure_image|exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|LipschitzWith.ae_differentiableAt|Besicovitch.ae_tendsto_measure_inter_div|extend_finite_dimension|ContDiffOn.exists_lipschitzOnWith|lintegral_withDensity_eq_lintegral_mul_non_measurable|EventuallyEq.fderiv_eq|AEMeasurable.ennreal_tsum|lintegral_tsum|restrict_iUnion|exists_antilipschitzWith' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `grep -rln 'C1Approximation|c1_approximation|lusin_c1' simongmt/Poincare/SimonGMT (no match); grep -n 'area formula' book/chapter-03.txt; sed -n 330,412p book/chapter-03.txt`
- `python3 scan of dag.json: lean_names containing idtp (none) or area; lean statements of dpf_rectifiable_bilipschitz_pieces, dpf_approxTangent_ae_bilipschitz_piece, dpf_area_formula_bilipschitz_rectifiable, imrep_approxTangent_starProjection_aesm, dtc_* lemmas and dimred_* siblings`
- `grep -l idtp_ nodes/*/*.json outside this node (none); for d in .swarm-worktrees/*/gmt-ch07/GMT: grep -rl 'idtp_|carrier_area_formula' (none)`
- `lean /tmp/idtp_v3/check/Probe.lean (normDet, weightedAreaFiberSum, areaJacobianAt, tangentialJacobian are not in the import closure of GMT.Ch07.Submission)`
- `lean /tmp/idtp_v3/check/NewChild.lean; lean /tmp/idtp_v3/check/GramCheck.lean (#print axioms idtp_v3_gram_sqrt_eq_normDet)`
- `lean /tmp/idtp_v3/check/FromJsonV3.lean (#print axioms idtp_parent_check_json_v3)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-bilipschi-4344c8c0d8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-supplied-natural-proof.md`
- `/tmp/idtp_v3/check/FromJsonV3.lean`
- `/tmp/idtp_v3/check/GramCheck.lean`
- `/tmp/idtp_v3/check/NewChild.lean`
- `/tmp/idtp_v3/check/Probe.lean`

Pins match. The snapshot has project b4d606d (equal to workspace HEAD) and mathlib 25730c7c; SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Library support for the new child.
- SimonGMT provides the Euclidean-domain Lipschitz area formulas: weighted_area_formula_lipschitz_fiberSum and aemeasurable_weightedAreaFiberSum_lipschitz (AreaNoninjective.lean); weighted_area_formula_lipschitz_injOn with arbitrary weights, areaRegularSet, measurableSet_areaRegularSet and area_image_compl_regularSet_eq_zero (AreaLipschitz.lean); measurable_areaJacobianAt; weightedAreaFiberSum_iUnion.
- SimonGMT also provides HasApproximateTangentSpaceAt.unique and ae_eq_const_of_weak_coordinate_derivatives_zero (C¹ test functions).
- SimonGMT has no area formula on rectifiable carriers, no C¹ approximation theorem, and no rectifiable⇒C¹-cover direction of Ch. 3 Lemma 1.2 (searches found no match; the SubmanifoldCover header confirms this). The new child therefore proves Simon 2.4–2.5 from Lipschitz bi-Lipschitz pieces.
- Mathlib provides normDet_sq_eq_det_gram, normDet_comp, LinearMap.euclideanHausdorffMeasure_image, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Rademacher's theorem, Besicovitch density, Lipschitz extension, ContDiffOn.exists_lipschitzOnWith, lintegral_withDensity_eq_lintegral_mul_non_measurable and EventuallyEq.fderiv_eq.

Lean statement of the new child. normDet, weightedAreaFiberSum, areaJacobianAt and tangentialJacobian are not in the import closure of GMT.Ch07.Submission. The new type therefore writes the Jacobian as Real.sqrt (Matrix.det (Matrix.of Gram)) and the fibre sum as a tsum over a subtype. GramCheck.lean proves that this equals normDet of the restricted derivative (axioms propext, Classical.choice, Quot.sound).

DAG. The related other-branch nodes dpf_rectifiable_bilipschitz_pieces and dpf_approxTangent_ae_bilipschitz_piece are not comparator-accepted, so they are not reused; their arguments are re-proved inside the new child. Accepted lemmas cited by children (imrep_approxTangent_starProjection_aesm, dtc_*) have DAG types matching their uses.

Names. No idtp_* name occurs in dag.json, in other nodes' decompositions or in any worktree's GMT sources, so the 11 names are unreserved.

Lean check. All 11 statements elaborate, and the hypothesis-only assembly proves IntegerDensityAndTangentPlanes. Its axioms are propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only.
