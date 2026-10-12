# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.support_convex_hull-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (used throughout). n ≥ 1 and ℓ ≥ 0 are integers, E = Ambient n ℓ = ℝ^{n+ℓ}, Hⁿ = μHE[n] (equal to Simon's Hⁿ), B_ρ(ξ) = closedBall ξ ρ (closed ball), ω_n = omega n ∈ (0, ∞), and Hⁿ(P ∩ B_s(0)) = ω_n sⁿ for every n-dimensional subspace P. For a rectifiable n-varifold V: μ = μ_V = V.weight; T_x = V.tangentSpace x; p_x and p_x^⊥ are the orthogonal projections onto T_x and T_x^⊥; div_M X(x) = V.tangentialDiv X x = trace(DX(x)∘p_x); ∇^M h(x) = V.tangentialGradient h x = p_x(∇h(x)); r = |x − ξ|; q_ξ(x) = V.normalRadialSq ξ x = |p_x^⊥(x − ξ)|²/|x − ξ|² ∈ [0, 1] (q_ξ(ξ) = 0 because division by 0 is 0); w_ξ(x) = q_ξ(x)/|x − ξ|ⁿ (w_ξ(ξ) = 0); a_ξ(ρ) = μ(B_ρ(ξ))/ρⁿ (a real number); Θ(ξ) = V.density ξ. A test field in U is a C¹ map X: E → E with compact support and tsupport X ⊆ U (IsTestField). 'V has mean curvature H in U' (HasMeanCurvatureIn) means H ∈ L¹_loc(U, μ) and ∫div_M X dμ = −∫⟨X, H⟩dμ for every test field X in U; 'stationary in U' means ∫div_M X dμ = 0 for every test field X in U. (FV) for V means: (FV1) μ(K) < ∞ for every compact K; (FV2) dim T_x = n for μ-a.e. x; (FV3) x ↦ p_x is μ-a.e. strongly measurable. (GF) is the statement that (FV) holds for every n ≥ 1, every ℓ and every V : RectifiableVarifold n ℓ (exactly the second conjunct of the sibling tangent_structure_first_variation); (AT) is the contract Prop ApproxTangentAE. Under (FV): q_ξ, w_ξ, ∇^M h (for h ∈ C¹(U), on U) and div_M X (for X ∈ C¹) are μ-a.e. strongly measurable, being continuous functions of p_x and of continuous data; |div_M X| ≤ (n+ℓ)‖DX‖ and div_M X = 0 off tsupport X, so div_M X is μ-integrable for every test field X; μ is a locally finite, hence outer regular, Borel measure, and μ(E ∖ spt μ) = 0 (spt V = spt μ).

Source: Simon Ch. 4, 6.1 and 6.2. In 6.1 the printed identity is the first variation identity of the sibling radial_first_variation, applied to X(x) = ζ(x)γ(|x − ξ|)(x − ξ) with ζ ≡ 1 near spt V and γ ≥ 0 nondecreasing, γ = 0 on (−∞, R + ε]; with the sign convention 3.14(‡) its right side is −∫ γ(r)⟨x − ξ, H⟩ dμ (only |⟨x − ξ, H⟩| is used, so the printed sign is immaterial). 6.2 is reduced to 6.1 through the description of conv K by balls, which we prove.

Assume (GF).

SupportInBall.
1. Let n ≥ 1, R ≥ 0, U := E ∖ B_R(ξ) (open), V with mean curvature H in U, |⟨H(x), x − ξ⟩| < n for μ-a.e. x ∈ U, and spt V compact; μ = μ_V. Fix ε > 0.
2. Test field. Let W be the open 1-neighbourhood of spt V (bounded) and choose ζ ∈ C^∞_c(E) with 0 ≤ ζ ≤ 1 and ζ = 1 on W. Let γ(t) := (max(t − R − ε, 0))²: γ ∈ C¹(ℝ), γ ≥ 0, γ'(t) = 2 max(t − R − ε, 0) ≥ 0, γ(t) = 0 for t ≤ R + ε and γ(t) > 0 for t > R + ε. The field X(x) := (ζ(x)γ(|x − ξ|))(x − ξ) is C¹ (γ(|x − ξ|) vanishes on ball ξ (R + ε), a neighbourhood of ξ, and is C¹ away from ξ), has compact support (inside tsupport ζ), and tsupport X ⊆ {x : |x − ξ| ≥ R + ε} ⊆ U. So X is a test field in U, and ζ ∈ C¹(U).
3. By (GF), dim T_x = n for μ-a.e. x. The sibling radial_first_variation (with h := ζ and this γ) gives
∫_U [ζ(nγ(r) + rγ'(r)(1 − q_ξ)) + γ(r)⟨x − ξ, ∇^Mζ⟩] dμ = −∫_U ζγ(r)⟨x − ξ, H⟩ dμ.
4. μ(E ∖ spt V) = 0, and on the open set W ⊇ spt V we have ζ = 1 and ∇ζ = 0, hence ∇^Mζ = 0. So μ-a.e. the integrands equal nγ(r) + rγ'(r)(1 − q_ξ) and γ(r)⟨x − ξ, H⟩. These functions are μ-integrable on U: μ-a.e. on U they vanish off the compact set spt V ∩ {|x − ξ| ≥ R + ε} ⊆ U, on which γ(r) and rγ'(r) are bounded, q_ξ ∈ [0, 1] is μ-measurable by (GF), and H is μ-integrable (H ∈ L¹_loc(U, μ)). Therefore
n∫_U γ(r) dμ + ∫_U rγ'(r)(1 − q_ξ) dμ = −∫_U γ(r)⟨x − ξ, H⟩ dμ ≤ ∫_U γ(r)|⟨x − ξ, H⟩| dμ.
5. As rγ'(r)(1 − q_ξ) ≥ 0, ∫_U γ(r)(n − |⟨H, x − ξ⟩|) dμ ≤ 0. The integrand is ≥ 0 μ-a.e. on U (γ ≥ 0, and n − |⟨H, x − ξ⟩| > 0 μ-a.e. on U), so it vanishes μ-a.e. on U, whence γ(r) = 0 μ-a.e. on U. Since γ(r) > 0 on the open set O_ε := {x : |x − ξ| > R + ε} ⊆ U, μ(O_ε) = 0, so O_ε ∩ spt V = ∅, i.e. spt V ⊆ B_{R+ε}(ξ).
6. Since ε > 0 is arbitrary and ⋂_{ε>0} B_{R+ε}(ξ) = B_R(ξ), spt V ⊆ B_R(ξ).

ConvexHullProperty.
7. Let n ≥ 1, K compact, spt V compact, V stationary in E ∖ K, and y ∉ conv K. It suffices to find c ∈ E and R' ≥ 0 with K ⊆ B_{R'}(c) and y ∉ B_{R'}(c). Indeed, then E ∖ B_{R'}(c) ⊆ E ∖ K, so every test field in E ∖ B_{R'}(c) is a test field in E ∖ K and V has mean curvature 0 in E ∖ B_{R'}(c) (the zero field is locally integrable, and ∫ div_M X dμ = 0 = −∫⟨X, 0⟩ dμ); the hypothesis n^{-1}|⟨0, x − c⟩| = 0 < 1 holds everywhere; so SupportInBall gives spt V ⊆ B_{R'}(c), which does not contain y. As y ∉ conv K was arbitrary, spt V ⊆ conv K.
8. If K = ∅, take any c ≠ y (E has dimension n + ℓ ≥ 1) and R' = 0. If K ≠ ∅: conv K is convex and compact: by Carathéodory's theorem (Mathlib eq_pos_convex_span_of_mem_convexHull) every point of conv K is a convex combination of at most N + 1 points of K, N := n + ℓ, so conv K is the image of the compact set Δ_N × K^{N+1} (Δ_N the standard simplex of weights) under the continuous map (λ, x_0, …, x_N) ↦ Σ_i λ_i x_i, every such combination lying in conv K. By the separation theorem for the closed convex set conv K and the point y ∉ conv K (Mathlib geometric_hahn_banach_point_closed, with the Riesz representation of the separating functional) there are a unit vector e and m ∈ ℝ with ⟨e, x⟩ ≤ m for all x ∈ conv K and ⟨e, y⟩ = m + η with η > 0. Let z := y − ηe (so ⟨e, z⟩ = m), D := max_{x∈K} |x − z|, and for L > 0 let c_L := z − Le and R_L := (L² + D²)^{1/2}. For x ∈ K, |x − c_L|² = |x − z|² + 2L⟨e, x − z⟩ + L² ≤ D² + L², because ⟨e, x − z⟩ = ⟨e, x⟩ − m ≤ 0; so K ⊆ B_{R_L}(c_L). And |y − c_L|² = |ηe + Le|² = η² + 2Lη + L² > L² + D² as soon as L > D²/(2η); so y ∉ B_{R_L}(c_L). This proves ConvexHullProperty.

## Key steps

1. Test field X = ζγ(|x−ξ|)(x−ξ) with ζ ≡ 1 near spt V and γ(t) = ((t − R − ε)^+)², supported in E ∖ B_{R+ε}(ξ)
2. radial_first_variation gives n∫γ + ∫rγ'(1 − q) = −∫γ⟨x−ξ, H⟩ after ∇^Mζ = 0 μ-a.e.
3. Since rγ'(1 − q) ≥ 0 and |⟨H, x−ξ⟩| < n a.e., γ(r) = 0 μ-a.e. on U, so spt V ⊆ B_{R+ε}(ξ); let ε ↓ 0
4. Every y ∉ conv K is separated from K by a closed ball containing K (separation theorem, large balls)
5. Stationarity in E ∖ K gives mean curvature 0 outside that ball, and 6.1 excludes y from spt V

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
