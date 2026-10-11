# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.weighted_monotonicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (used throughout). n ≥ 1 and ℓ ≥ 0 are integers, E = Ambient n ℓ = ℝ^{n+ℓ}, Hⁿ = μHE[n] (equal to Simon's Hⁿ), B_ρ(ξ) = closedBall ξ ρ (closed ball), ω_n = omega n ∈ (0, ∞), and Hⁿ(P ∩ B_s(0)) = ω_n sⁿ for every n-dimensional subspace P. For a rectifiable n-varifold V: μ = μ_V = V.weight; T_x = V.tangentSpace x; p_x and p_x^⊥ are the orthogonal projections onto T_x and T_x^⊥; div_M X(x) = V.tangentialDiv X x = trace(DX(x)∘p_x); ∇^M h(x) = V.tangentialGradient h x = p_x(∇h(x)); r = |x − ξ|; q_ξ(x) = V.normalRadialSq ξ x = |p_x^⊥(x − ξ)|²/|x − ξ|² ∈ [0, 1] (q_ξ(ξ) = 0 because division by 0 is 0); w_ξ(x) = q_ξ(x)/|x − ξ|ⁿ (w_ξ(ξ) = 0); a_ξ(ρ) = μ(B_ρ(ξ))/ρⁿ (a real number); Θ(ξ) = V.density ξ. A test field in U is a C¹ map X: E → E with compact support and tsupport X ⊆ U (IsTestField). 'V has mean curvature H in U' (HasMeanCurvatureIn) means H ∈ L¹_loc(U, μ) and ∫div_M X dμ = −∫⟨X, H⟩dμ for every test field X in U; 'stationary in U' means ∫div_M X dμ = 0 for every test field X in U. (FV) for V means: (FV1) μ(K) < ∞ for every compact K; (FV2) dim T_x = n for μ-a.e. x; (FV3) x ↦ p_x is μ-a.e. strongly measurable. (GF) is the statement that (FV) holds for every n ≥ 1, every ℓ and every V : RectifiableVarifold n ℓ (exactly the second conjunct of the sibling tangent_structure_first_variation); (AT) is the contract Prop ApproxTangentAE. Under (FV): q_ξ, w_ξ, ∇^M h (for h ∈ C¹(U), on U) and div_M X (for X ∈ C¹) are μ-a.e. strongly measurable, being continuous functions of p_x and of continuous data; |div_M X| ≤ (n+ℓ)‖DX‖ and div_M X = 0 off tsupport X, so div_M X is μ-integrable for every test field X; μ is a locally finite, hence outer regular, Borel measure, and μ(E ∖ spt μ) = 0 (spt V = spt μ).

Source: Simon Ch. 4, 3.3–3.6 (case H = 0, h = 1), 3.16 and 4.1 (mean curvature term), 5.1 (weight h), with the documented corrections: with the sign convention 3.14(‡) the curvature term enters as +τ^{-n-1}∫φ(r/τ)⟨x − ξ, hH⟩; and in 3.5 the prefactors are reversed — the correct two-sided bound is s^{-n} ≤ τ^{-n} ≤ (1 + ε)ⁿs^{-n} (Step 5). The printed route (first variation of X = hφ(r/τ)(x − ξ), differentiate in τ, integrate from σ to ρ, let ε ↓ 0) is followed exactly, with no integrating factor; the hypotheses (FV1)–(FV3) are given.

Notation: B_τ = B_τ(ξ), r = |x − ξ|, q = q_ξ, w = w_ξ = q/rⁿ, G(x) := ⟨x − ξ, ∇^M h(x) + h(x)H(x)⟩, L(τ) := ∫_{B_τ} G dμ.

Step 0 (room). K_0 := tsupport h ∩ B_ρ is compact and ⊆ U. There is ε_0 ∈ (0, 1) with K_1 := tsupport h ∩ B_{(1+ε_0)ρ} ⊆ U: otherwise there are x_m ∈ tsupport h ∩ B_{(1+1/m)ρ} ∖ U, a subsequence converges to some x ∈ tsupport h ∩ B_ρ (tsupport h is closed) with x ∉ U (E ∖ U is closed), contradicting K_0 ⊆ U. K_1 is compact. On the open set E ∖ tsupport h, h ≡ 0, hence h = 0 and ∇h = 0 there. Consequently there is A_0 with |h| ≤ A_0 and |∇h| ≤ A_0 on B_{(1+ε_0)ρ} (continuity on the compact K_1 ⊆ U, zero elsewhere in the ball), H is μ-integrable on K_1 (H ∈ L¹_loc(U, μ)), and h, ∇^M h, hH, G vanish on B_{(1+ε_0)ρ} ∖ K_1.

Step 1 (measurability; the two integrability conclusions). By (FV3) and continuity of ∇h on U, ∇^M h and q are μ-a.e. strongly measurable on B_{(1+ε_0)ρ}. By Step 0, |G| ≤ (1 + ε_0)ρA_0(1 + |H|)1_{K_1} on B_{(1+ε_0)ρ}, so G is μ-integrable there ((FV1): μ(K_1) < ∞). The function L is bounded by ‖G 1_{K_1}‖_{L¹(μ)} on (0, ρ] and Borel, since L(τ) = ∫_{B_τ} G⁺ dμ − ∫_{B_τ} G⁻ dμ is a difference of two nondecreasing functions of τ; so τ ↦ L(τ)/τ^{n+1} is bounded by σ^{-n-1}‖G 1_{K_1}‖_{L¹(μ)} on (σ, ρ] and integrable there. On B_ρ ∖ B_σ we have r > σ, so |h w| ≤ A_0σ^{-n}; h w is μ-a.e. strongly measurable and μ(B_ρ) < ∞, so h w is μ-integrable on B_ρ ∖ B_σ.

Step 2 (cutoff and test fields). Fix ε ∈ (0, ε_0/2] and a C^∞ nonincreasing φ = φ_ε: ℝ → [0, 1] with φ = 1 on (−∞, 1] and φ = 0 on [1 + ε, ∞) (so −2/ε ≤ φ' ≤ 0 may be arranged; only boundedness of φ' is used). Let Ω := (σ/2, (1 + ε_0)ρ/(1 + ε)), an open interval containing [σ, ρ]. For τ ∈ Ω let γ_τ(t) := φ(t/τ), a C¹ function with γ_τ'(t) = φ'(t/τ)/τ, and X_τ(x) := h(x)γ_τ(r)(x − ξ). Since (1 + ε)τ < (1 + ε_0)ρ, tsupport h ∩ B_{(1+ε)τ} ⊆ K_1 ⊆ U. X_τ is a test field in U: it is C¹ on U (product of C¹ functions; x ↦ γ_τ(r)(x − ξ) is C^∞ because γ_τ is constant near 0), it vanishes on the open set W_τ := E ∖ (tsupport h ∩ B_{(1+ε)τ}) (there h = 0 or γ_τ(r) = 0), U ∪ W_τ = E, so X_τ is C¹ on E; and tsupport X_τ ⊆ tsupport h ∩ B_{(1+ε)τ}, a compact subset of U.

Step 3 (first variation; 3.3 and 5.1). By the sibling theorem radial_first_variation (hypothesis (FV2)) applied to X_τ:
∫_U [h(nφ(r/τ) + (r/τ)φ'(r/τ)(1 − q)) + φ(r/τ)⟨x − ξ, ∇^M h⟩] dμ = −∫_U hφ(r/τ)⟨x − ξ, H⟩ dμ.
All integrands vanish outside K_1 ⊆ U (Step 0, and φ(r/τ) = φ'(r/τ) = 0 for r ≥ (1 + ε)τ), and they are μ-integrable (bounded by a constant times (1 + |H|)1_{K_1}). So the integrals may be taken over E and split. With I(τ) := ∫ hφ(r/τ) dμ, J(τ) := ∫ hφ(r/τ) q dμ and L_ε(τ) := ∫ φ(r/τ) G dμ this reads
(3.1) n I(τ) + ∫ h (r/τ)φ'(r/τ) dμ − ∫ h (r/τ)φ'(r/τ) q dμ + L_ε(τ) = 0 (τ ∈ Ω).
Since ∂_τ[φ(r/τ)] = −(r/τ²)φ'(r/τ) is continuous in τ and bounded by sup|φ'|(1 + ε_0)ρ/τ² uniformly in x, differentiation under the integral sign (dominating function a constant times |h|1_{K_1}) shows that I and J are C¹ on Ω with τI'(τ) = −∫ h (r/τ)φ'(r/τ) dμ and τJ'(τ) = −∫ h (r/τ)φ'(r/τ) q dμ. Thus (3.1) becomes n I(τ) − τI'(τ) + τJ'(τ) + L_ε(τ) = 0.

Step 4 (3.4). Hence (τ^{-n}I(τ))' = τ^{-n-1}(τI'(τ) − nI(τ)) = τ^{-n}J'(τ) + τ^{-n-1}L_ε(τ) on Ω, and integrating over [σ, ρ] (fundamental theorem of calculus for the C¹ function τ^{-n}I):
(4.1) ρ^{-n}I_ε(ρ) − σ^{-n}I_ε(σ) = ∫_σ^ρ τ^{-n}J_ε'(τ) dτ + ∫_σ^ρ τ^{-n-1}L_ε(τ) dτ.
By Fubini (the integrand (τ, x) ↦ τ^{-n}h(x)q(x)(r/τ²)(−φ'(r/τ)) is bounded on [σ, ρ] × K_1 and vanishes for x ∉ K_1), ∫_σ^ρ τ^{-n}J_ε'(τ) dτ = ∫ h(x)q(x)k_ε(r(x)) dμ(x), where k_ε(s) := ∫_σ^ρ τ^{-n}∂_τ[φ(s/τ)] dτ.

Step 5 (the kernel k_ε; corrected 3.5). For s > 0, ∂_τ[φ(s/τ)] = −(s/τ²)φ'(s/τ) ≥ 0 vanishes unless 1 ≤ s/τ ≤ 1 + ε, i.e. s/(1 + ε) ≤ τ ≤ s, where s^{-n} ≤ τ^{-n} ≤ (1 + ε)ⁿs^{-n}. Since ∫_σ^ρ ∂_τ[φ(s/τ)] dτ = φ(s/ρ) − φ(s/σ) ≥ 0,
s^{-n}(φ(s/ρ) − φ(s/σ)) ≤ k_ε(s) ≤ (1 + ε)ⁿ s^{-n}(φ(s/ρ) − φ(s/σ)).
In particular k_ε(s) = 0 for s ≤ σ (both values of φ equal 1), 0 ≤ k_ε ≤ 2ⁿσ^{-n}, and since φ_ε(t) → 1 for t ≤ 1 and φ_ε(t) → 0 for t > 1 as ε ↓ 0, k_ε(s) → s^{-n}1_{σ<s≤ρ} for every s ≥ 0 (k_ε(0) = 0).

Step 6 (ε ↓ 0). Let ε = ε_m ↓ 0 with ε_m ≤ ε_0/2. By dominated convergence (dominating functions A_0 1_{K_1}, 2ⁿσ^{-n}A_0 1_{K_1}, |G| 1_{K_1}, all μ-integrable): I_ε(τ) → ∫_{B_τ} h dμ for each τ ∈ [σ, ρ] (φ_ε(r/τ) → 1_{B_τ}); ∫ h q k_ε(r) dμ → ∫_{B_ρ∖B_σ} h q r^{-n} dμ = ∫_{B_ρ∖B_σ} h w dμ; L_ε(τ) → L(τ) for each τ with |L_ε(τ)| ≤ ‖G 1_{K_1}‖_{L¹(μ)}, so by dominated convergence on [σ, ρ], ∫_σ^ρ τ^{-n-1}L_ε(τ) dτ → ∫_{(σ,ρ]} τ^{-n-1}L(τ) dτ. Passing to the limit in (4.1):
ρ^{-n}∫_{B_ρ} h dμ − σ^{-n}∫_{B_σ} h dμ = ∫_{B_ρ∖B_σ} h q_ξ |x − ξ|^{-n} dμ + ∫_{(σ,ρ]} τ^{-n-1}∫_{B_τ}⟨x − ξ, ∇^M h + hH⟩ dμ dτ,
which, with Step 1, is the asserted conjunction.

## Key steps

1. Compactness gives ε_0 > 0 with tsupport h ∩ B_{(1+ε_0)ρ}(ξ) ⊆ U; h, ∇h bounded there and zero off tsupport h; H integrable there
2. Measurability from (FV3); boundedness gives the two integrability conclusions
3. X_τ = hφ_ε(r/τ)(x−ξ) is a test field; radial_first_variation gives nI − τI' + τJ' + L_ε = 0 (3.3/5.1)
4. (τ^{-n}I)' = τ^{-n}J' + τ^{-n-1}L_ε; integrate over [σ, ρ] and use Fubini for the J' term (3.4)
5. Kernel bounds s^{-n}(φ(s/ρ)−φ(s/σ)) ≤ k_ε(s) ≤ (1+ε)ⁿ s^{-n}(φ(s/ρ)−φ(s/σ)) (corrected 3.5)
6. Let ε ↓ 0 by dominated convergence to obtain the identity with closed balls

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
