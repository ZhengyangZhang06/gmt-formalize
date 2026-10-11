# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.poincare_inequality-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (used throughout). n ≥ 1 and ℓ ≥ 0 are integers, E = Ambient n ℓ = ℝ^{n+ℓ}, Hⁿ = μHE[n] (equal to Simon's Hⁿ), B_ρ(ξ) = closedBall ξ ρ (closed ball), ω_n = omega n ∈ (0, ∞), and Hⁿ(P ∩ B_s(0)) = ω_n sⁿ for every n-dimensional subspace P. For a rectifiable n-varifold V: μ = μ_V = V.weight; T_x = V.tangentSpace x; p_x and p_x^⊥ are the orthogonal projections onto T_x and T_x^⊥; div_M X(x) = V.tangentialDiv X x = trace(DX(x)∘p_x); ∇^M h(x) = V.tangentialGradient h x = p_x(∇h(x)); r = |x − ξ|; q_ξ(x) = V.normalRadialSq ξ x = |p_x^⊥(x − ξ)|²/|x − ξ|² ∈ [0, 1] (q_ξ(ξ) = 0 because division by 0 is 0); w_ξ(x) = q_ξ(x)/|x − ξ|ⁿ (w_ξ(ξ) = 0); a_ξ(ρ) = μ(B_ρ(ξ))/ρⁿ (a real number); Θ(ξ) = V.density ξ. A test field in U is a C¹ map X: E → E with compact support and tsupport X ⊆ U (IsTestField). 'V has mean curvature H in U' (HasMeanCurvatureIn) means H ∈ L¹_loc(U, μ) and ∫div_M X dμ = −∫⟨X, H⟩dμ for every test field X in U; 'stationary in U' means ∫div_M X dμ = 0 for every test field X in U. (FV) for V means: (FV1) μ(K) < ∞ for every compact K; (FV2) dim T_x = n for μ-a.e. x; (FV3) x ↦ p_x is μ-a.e. strongly measurable. (GF) is the statement that (FV) holds for every n ≥ 1, every ℓ and every V : RectifiableVarifold n ℓ (exactly the second conjunct of the sibling tangent_structure_first_variation); (AT) is the contract Prop ApproxTangentAE. Under (FV): q_ξ, w_ξ, ∇^M h (for h ∈ C¹(U), on U) and div_M X (for X ∈ C¹) are μ-a.e. strongly measurable, being continuous functions of p_x and of continuous data; |div_M X| ≤ (n+ℓ)‖DX‖ and div_M X = 0 off tsupport X, so div_M X is μ-integrable for every test field X; μ is a locally finite, hence outer regular, Borel measure, and μ(E ∖ spt μ) = 0 (spt V = spt μ).

Source: Simon Ch. 4, 5.1–5.6, with 4.10(1), 4.10(2) and 4.11. Documented corrections: the coefficient in 5.2 is Λ (not Λρ), which produces the factor e^{Λρ} of 5.4 (here via a Gronwall argument); only the full-ball case (σ = 0) of 4.10(2) is used — the annular version is false as printed. In the frozen statement the constants are quantified as ∀ α Γ, ∃ β c, so β and c may depend on n, α and Γ; we take β as in the printed proof and c := 8Γ/(α²ω_n), both fixed after n, α, Γ and before ℓ, V, U, H, Λ, h, ξ, ρ. (The defining inequality of β happens not to involve Γ; this extra observation is neither needed nor asserted by the frozen statement.)

Assume (AT) and (GF).

Choice of constants. Let n ≥ 1, α ∈ (0, 1) and Γ > 0 be given. Since (1 − α²)(1 − β')^{−n} → 1 − α² < 1 − α²/2 as β' ↓ 0, we may fix β ∈ (0, ½) with (1 − α²)(1 − β)^{−n} ≤ 1 − α²/2, and we put c := 8Γ/(α²ω_n) > 0. These β and c are the witnesses for ∃ β c in PoincareInequality (which comes after ∀ α Γ). Now let ℓ, V, U, H, Λ, h, ξ_0 := ξ and ρ satisfy the hypotheses, and write μ = μ_V.

1. Reductions. Replacing Λ by max(Λ, 0) preserves all hypotheses (|H| ≤ Λ ≤ max(Λ, 0), and e^{max(Λ,0)ρ} = max(e^{Λρ}, 1) ≤ 1 + α), so assume Λ ≥ 0. H is locally integrable on U and |H| ≤ Λ μ-a.e. on U, so H ∈ L^{n+1}(μ⌞K) for every compact K ⊆ U (bounded, strongly measurable, μ(K) < ∞): IsLocallyLp U H (n + 1) with n + 1 > n. By the siblings mean_curvature_monotonicity (LpDensity) and canonical_representatives (LpSupportRepresentation, with MultiplicityGE 1 U), both applied with (AT) and (GF): for every ζ ∈ U, μ(B_s(ζ))/(ω_n sⁿ) → Θ(ζ) as s ↓ 0, and Θ(ζ) ≥ 1 for every ζ ∈ spt μ ∩ U.

2. Gronwall form of 5.4. Let y ∈ E and r_1 > 0 with B_{r_1}(y) ⊆ U, and g ∈ C¹(U) with g ≥ 0 on U. Put f(s) := s^{−n}∫_{B_s(y)} g dμ for 0 < s ≤ r_1 and P := ∫_{(0,r_1]} τ^{−n−1}∫_{B_τ(y)} |x − y||∇^M g(x)| dμ(x) dτ ∈ [0, ∞]. Claim: f(s) ≤ e^{Λ(r_1−s)}(f(r_1) + P) for 0 < s ≤ r_1. Proof: by the sibling weighted_monotonicity_identity (function g, centre y, radii s' ≤ r_1; tsupport g ∩ B_{r_1}(y) ⊆ U), for s ≤ s' ≤ r_1, f(r_1) − f(s') = ∫_{B_{r_1}∖B_{s'}} g w_y dμ + ∫_{(s',r_1]} τ^{−n−1}∫_{B_τ(y)}⟨x − y, ∇^M g + gH⟩ dμ dτ. The first term is ≥ 0, and μ-a.e. on B_τ(y) ⊆ U, ⟨x − y, ∇^M g + gH⟩ ≥ −|x − y||∇^M g| − τΛg. Hence f(s') ≤ f(r_1) + P + Λ∫_{s'}^{r_1} f(τ) dτ for all s' ∈ [s, r_1], where f is bounded and Borel on [s, r_1]. If P = ∞ there is nothing to prove. Otherwise let C_0 := f(r_1) + P and u(s') := ∫_{s'}^{r_1} f; v(s') := e^{Λs'}u(s') is Lipschitz with v' = e^{Λs'}(Λu − f) ≥ −C_0e^{Λs'} a.e., so integrating from s' to r_1 gives Λu(s') ≤ C_0(e^{Λ(r_1−s')} − 1) (for Λ = 0 the claim is immediate), and f(s') ≤ C_0 + Λu(s') ≤ C_0e^{Λ(r_1−s')}. By Tonelli, P = ∫_{B_{r_1}(y)} |x − y||∇^M g(x)|∫_{(|x−y|,r_1]} τ^{−n−1} dτ dμ(x) ≤ (1/n)∫_{B_{r_1}(y)} |∇^M g(x)||x − y|^{1−n} dμ(x) (the point x = y contributes 0; here |x − y|^{1−n} ∈ [0, ∞]).
Growth bound: for y ∈ B_ρ(ξ_0), B_ρ(y) ⊆ B_{2ρ}(ξ_0) ⊆ U; with g ≡ 1 (∇^M g = 0, P = 0) and r_1 = ρ: μ(B_s(y)) ≤ e^{Λρ}(s/ρ)ⁿμ(B_ρ(y)) ≤ (1 + α)Γsⁿ ≤ 2Γsⁿ for 0 < s ≤ ρ; in particular μ({y}) = 0.
Kernel bound (4.10(2) for full balls, via 4.11): for y ∈ B_ρ(ξ_0) and 0 < s ≤ ρ, ∫_{B_s(y)} |x − y|^{1−n} dμ(x) ≤ 2nΓs. For n = 1 the integrand is 1 and this is the growth bound. For n ≥ 2 the layer-cake formula gives ∫_{B_s(y)}|x − y|^{1−n} dμ = ∫_0^∞ μ({x ∈ B_s(y) : |x − y|^{1−n} > λ}) dλ ≤ ∫_0^{s^{1−n}} μ(B_s(y)) dλ + ∫_{s^{1−n}}^∞ μ(B_{λ^{−1/(n−1)}}(y)) dλ ≤ 2Γs + 2Γ∫_{s^{1−n}}^∞ λ^{−n/(n−1)} dλ = 2Γs + 2Γ(n − 1)s.

3. Pointwise inequality (proof of 5.6, (1)–(2)). Fix ε > 0 and a C¹ nondecreasing ψ: ℝ → [0, 1] with ψ = 0 on (−∞, 0] and ψ = 1 on [ε, ∞). For t ≥ 0 let h_t := ψ(h − t) ∈ C¹(U): 0 ≤ h_t ≤ 1, h_t = 0 where h ≤ t, and ∇^M h_t = ψ'(h − t)∇^M h on U (chain rule; p_x is linear). Let r_0 := (1 − β)ρ and ζ ∈ B_{βρ}(ξ_0) ∩ spt μ with h(ζ) > t + ε; then B_{r_0}(ζ) ⊆ B_ρ(ξ_0) ⊆ U. Apply step 2 with g = h_t, y = ζ, r_1 = r_0 and let s ↓ 0: h_t is continuous at ζ and μ(B_s(ζ))/(ω_n sⁿ) → Θ(ζ) ≥ 1 (step 1), so s^{−n}∫_{B_s(ζ)} h_t dμ → ω_n h_t(ζ)Θ(ζ) ≥ ω_n h_t(ζ) = ω_n (h_t(ζ) = 1 because h(ζ) − t > ε). Using e^{Λr_0} ≤ e^{Λρ} ≤ 1 + α:
ω_n ≤ (1 + α)[r_0^{−n}∫_{B_{r_0}(ζ)} h_t dμ + (1/n)∫_{B_{r_0}(ζ)} ψ'(h − t)|∇^M h||x − ζ|^{1−n} dμ(x)].
Since h_t ≤ 1_{h>0} (t ≥ 0) and B_{r_0}(ζ) ⊆ B_ρ(ξ_0), r_0^{−n}∫_{B_{r_0}(ζ)} h_t dμ ≤ (1 − β)^{−n}ρ^{−n}μ({x ∈ B_ρ(ξ_0) : h(x) > 0}) ≤ (1 − β)^{−n}(1 − α)ω_n. Dividing by ω_n and using (1 + α)(1 − α)(1 − β)^{−n} ≤ 1 − α²/2 and 1 + α ≤ 2:
(3.1) α²/2 ≤ (2/(nω_n))∫_{B_ρ(ξ_0)} ψ'(h(x) − t)|∇^M h(x)||x − ζ|^{1−n}1_{|x−ζ|≤r_0} dμ(x).

4. Integration over ζ. Let A_t := {ζ ∈ B_{βρ}(ξ_0) : h(ζ) > t + ε}. μ-a.e. ζ ∈ A_t lies in spt μ (μ(E ∖ spt μ) = 0), so integrating (3.1) over A_t with respect to μ and using Tonelli (nonnegative measurable integrands), (α²/2)μ(A_t) ≤ (2/(nω_n))∫_{B_ρ(ξ_0)} ψ'(h(x) − t)|∇^M h(x)|[∫_{B_{r_0}(x)} |x − ζ|^{1−n} dμ(ζ)] dμ(x) ≤ (4Γρ/ω_n)∫_{B_ρ(ξ_0)} ψ'(h − t)|∇^M h| dμ, by the kernel bound of step 2 (x ∈ B_ρ(ξ_0), r_0 ≤ ρ).

5. Integration over t (4.11). By the layer-cake formula (Mathlib MeasureTheory.lintegral_eq_lintegral_meas_lt) ∫_0^∞ μ(A_t) dt = ∫_{B_{βρ}(ξ_0)} (h − ε)^+ dμ, and ∫_0^∞ ψ'(h(x) − t) dt = ψ(h(x)) ≤ 1 for x ∈ U (h(x) ≥ 0). By Tonelli, ∫_{B_{βρ}(ξ_0)} (h − ε)^+ dμ ≤ (8Γ/(α²ω_n))ρ∫_{B_ρ(ξ_0)} |∇^M h| dμ. Letting ε ↓ 0 (monotone convergence; h ≥ 0 on B_{βρ}(ξ_0) ⊆ U) gives ∫_{B_{βρ}(ξ_0)} h dμ ≤ cρ∫_{B_ρ(ξ_0)} |∇^M h| dμ, which is PoincareInequality with the constants β, c chosen above (0 < β < ½, c > 0).

## Key steps

1. Given n, α, Γ (frozen order ∀ α Γ ∃ β c), fix β ∈ (0, ½) with (1−α²)(1−β)^{−n} ≤ 1 − α²/2 and c = 8Γ/(α²ω_n), before ℓ and all data
2. Bounded H is L^{n+1}_loc, so LpDensity and LpSupportRepresentation give existence of Θ on U and Θ ≥ 1 on spt V ∩ U
3. weighted_monotonicity_identity plus Gronwall gives 5.4: f(s) ≤ e^{Λ(r_1−s)}(f(r_1) + (1/n)∫|∇^M g||x−y|^{1−n})
4. Growth μ(B_s(y)) ≤ 2Γsⁿ and the full-ball kernel bound ∫_{B_s(y)}|x−y|^{1−n} ≤ 2nΓs
5. Apply 5.4 to the truncations ψ(h − t) at ζ ∈ B_{βρ} ∩ spt V with h(ζ) > t + ε to get α²/2 ≤ (2/(nω_n))∫ψ'(h−t)|∇^M h||x−ζ|^{1−n}
6. Integrate over ζ (Tonelli + kernel bound) and over t (layer cake), then let ε ↓ 0

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
