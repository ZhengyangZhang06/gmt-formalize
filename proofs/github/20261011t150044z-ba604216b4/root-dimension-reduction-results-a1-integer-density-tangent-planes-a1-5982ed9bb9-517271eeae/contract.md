<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1 -->

## Theorem `Submission.idtp_fons_cone_closed_class`

Assume (DEM), (MON), (DTC) and (PS). Here (DEM) is the frozen statement of Submission.idtp_imrep_measure_density_ae (the registered dependency density_eq_multiplicity_ae of the selected node); (MON) is the frozen type of the sibling child monotonicity (Submission.idtp_fons_minimizing_monotonicity); (DTC) is the contract proposition DensityAndTangentCones (the frozen type of the sibling child tangent_cones, Submission.idtp_fons_density_tangent_cones); (PS) is the conclusion of the sibling child planar_support (Submission.idtp_fons_invariant_planar_support). (DEM): For all P, n ∈ ℕ with n ≥ 1, every set U ⊆ ℝ^P and every integer multiplicity triple R = (M, θ, ξ) ∈ IMRep U n (carrier M, multiplicity θ : ℝ^P → ℕ, orientation ξ), if the measure μ_R := R.measure = θ·μHE[n]⌞M satisfies μ_R(K) < ∞ for every compact K ⊆ ℝ^P, then for μHE[n]-almost every x ∈ ℝ^P the ratio μ_R(B_ρ(x))/(ω_nρ^n) (open balls, ω_n = unitBallVolume n, computed in [0, ∞]) tends to 1_M(x)·θ(x) as ρ ↓ 0. (MON): Let P, n, d ∈ ℕ with 1 ≤ n ≤ d ≤ P, let U ⊆ ℝ^P be open, let N ⊆ ℝ^P be an embedded C² d-dimensional submanifold (IsEmbeddedSubmanifold 2 d N) with (closure N ∖ N) ∩ U = ∅, and let T ∈ 𝒟_n(U) be minimizing in U ∩ N (IsMinimizingIn T (U ∩ N)) with spt T ⊆ U ∩ N and ∂T = 0 in U (BoundaryVanishes T). Then: (i) for every compact K ⊆ U there is Λ ≥ 0 such that for every y ∈ ℝ^P and R > 0 with closedBall y R ⊆ K the function ρ ↦ e^{Λρ}ρ^{−n}·M_{B_ρ(y)}(T) (in [0, ∞], written ofReal(e^{Λρ}/ρ^n)·T.massOn (ball y ρ)) is nondecreasing on (0, R); (ii) if N = ℝ^P, then for every y and R with B_R(y) ⊆ U the function ρ ↦ ρ^{−n}·M_{B_ρ(y)}(T) is nondecreasing on (0, R); (iii) there is Θ : ℝ^P → ℝ with HasMassDensity T y (Θ(y)) (Θ^n(μ_T, y) = Θ(y)) for every y ∈ U and Θ upper semicontinuous on U; (iv) if y ∈ spt T and HasMassDensity T y θ, then θ ≥ 1. (DTC): Let ℓ ≤ k, U ⊆ ℝ^{n+k} open, N an embedded C² (n+ℓ)-submanifold with (N̄∖N) ∩ U = ∅, and T ∈ 𝒟_n(U) minimizing in U ∩ N with spt T ⊆ U ∩ N. Then (1) there is Θ: ℝ^{n+k} → ℝ such that Θ^n(μ_T, x) = Θ(x) (limit of M_{B_ρ(x)}(T)/(ω_nρ^n) as ρ ↓ 0, with Θ(x) ≥ 0) for every x ∈ U ∖ spt ∂T, and Θ is upper semicontinuous on U ∖ spt ∂T; (2) for every x ∈ spt T ∖ spt ∂T and every sequence λ_j > 0, λ_j → 0, there are a subsequence λ_{j'} and an integer multiplicity C ∈ 𝒟_n(ℝ^{n+k}), minimizing in ℝ^{n+k}, with η_{x,λ_{j'}#}T ⇀ C in ℝ^{n+k}, μ_{η_{x,λ_{j'}#}T} → μ_C (for all representations), η_{0,λ#}C = C for all λ > 0, and Θ^n(μ_C, 0) = Θ^n(μ_T, x). (PS): For all P, n ∈ ℕ, every S ∈ 𝒟_n(ℝ^P) and every linear subspace L ⊆ ℝ^P with n ≤ P and dim L + 1 = n: if S is minimizing in ℝ^P (IsMinimizingIn S univ), ∂S = 0 (BoundaryVanishes S), and HasMassDensity S w θ implies HasMassDensity S (y + λw) θ for all y ∈ L, λ > 0, w ∈ ℝ^P and θ ∈ ℝ, then there is an n-dimensional linear subspace Q ⊆ ℝ^P with spt S ⊆ Q. Under these hypotheses: let n, k, ℓ ∈ ℕ with ℓ ≤ k and n ≥ 1, P := n + k, U ⊆ ℝ^P open, N an embedded C² (n+ℓ)-dimensional submanifold (IsEmbeddedSubmanifold 2 (n + ℓ) N) with (closure N ∖ N) ∩ U = ∅, and T ∈ 𝒟_n(U) minimizing in U ∩ N with spt T ⊆ U ∩ N and ∂T = 0 in U (BoundaryVanishes T). Let z ∈ ℝ^P and r > 0 with closedBall z (2r) ⊆ U and spt T ∩ B_{2r}(z) ≠ ∅. For a measure μ on ℝ^P and x ∈ ℝ^P let dens μ x := (limsup_{ρ↓0} μ(B_ρ(x))/(ω_nρ^n)).toReal (limsup in [0, ∞] along ρ → 0⁺, ω_n = unitBallVolume n; in the Lean statement dens is a universally quantified function fixed by this defining equation); for y ∈ ℝ^P and λ > 0, μ^{y,λ} := ofReal(λ^{−n})•μ.map(η_{y,λ}) (= λ^{−n}(η_{y,λ})_#μ, η_{y,λ} = dilation y λ); spt μ := {w : μ(B_ε(w)) ≠ 0 for every ε > 0}; μ_j → μ vaguely means ∫ f dμ_j → ∫ f dμ for every continuous compactly supported f : ℝ^P → ℝ. Then there are a set 𝓜 of measures on ℝ^P, a map D from measures on ℝ^P to subsets of ℝ^P, a measure μ₀ and Λ ∈ ℝ such that μ₀ ∈ 𝓜, D(μ₀) = B_2(0), for every w ∈ B_2(0): w ∈ spt μ₀ ⟺ z + rw ∈ spt T, and (M1) every μ ∈ 𝓜 is finite on compact sets; (M2) every μ ∈ 𝓜 equals Hⁿ.withDensity(ofReal ∘ dens μ) (Hⁿ = μHE[n]); (M3) for μ ∈ 𝓜, 0 < λ < 1 and |y| ≤ 1 − λ: μ^{y,λ} ∈ 𝓜 and D(μ^{y,λ}) = η_{y,λ}(D μ); (M4) for μ ∈ 𝓜, |y| < 1 and every strictly decreasing sequence λ_j > 0 with λ_j → 0 there are a strictly increasing sub : ℕ → ℕ and ν ∈ 𝓜 with dens ν(tw) = dens ν(w) for all t > 0 and w, and μ^{y,λ_{sub(j)}} → ν vaguely; (M5) for μ ∈ 𝓜, D μ is open and contains B_2(0); (M6) if μ ∈ 𝓜, μ_j ∈ 𝓜 (j ∈ ℕ) and μ_j → μ vaguely, then every compact K ⊆ D μ satisfies K ⊆ D(μ_j) for all large j; (M7) for μ ∈ 𝓜, y ∈ spt μ and ρ > 0 with closedBall y ρ ⊆ D μ: e^{−Λρ}·ω_nρ^n ≤ μ(B_ρ(y)); (M8) if ν ∈ 𝓜 and L is a linear subspace with dim L + 1 = n and dens ν(y + tw) = dens ν(w) for all y ∈ L, t > 0 and w, then spt ν ⊆ Q for some n-dimensional linear subspace Q; (M9) if ν ∈ 𝓜 and dens ν(tw) = dens ν(w) for all t > 0 and w, then D ν = ℝ^P.

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4842

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1016, https://github.com/ZhengyangZhang06/gmt-formalize/issues/818, https://github.com/ZhengyangZhang06/gmt-formalize/issues/864

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6873, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6880, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6888, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6891, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6899, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6901, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1016, https://github.com/ZhengyangZhang06/gmt-formalize/issues/818, https://github.com/ZhengyangZhang06/gmt-formalize/issues/864, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5302, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4717, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4643

## Lean problem

Declaration: `Submission.idtp_fons_cone_closed_class`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), 1 ≤ n → (∀ K : Set (Euclid P), IsCompact K → R.measure K ≠ ∞) → ∀ᵐ x ∂μHE[n], Tendsto (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator R.carrier (fun y => (R.mult y : ℝ≥0∞)) x))) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → DensityAndTangentCones → (∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), n ≤ P → Module.finrank ℝ L + 1 = n → IsMinimizingIn S univ → BoundaryVanishes S → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ) → ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ S.support ⊆ (Q : Set (Euclid P))) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (dens : Measure (Euclid (n + k)) → Euclid (n + k) → ℝ), 0 < r → closedBall z (2 * r) ⊆ U → (T.support ∩ ball z (2 * r)).Nonempty → (∀ (μ : Measure (Euclid (n + k))) (x : Euclid (n + k)), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → ∃ (𝓜 : Set (Measure (Euclid (n + k)))) (D : Measure (Euclid (n + k)) → Set (Euclid (n + k))) (μ₀ : Measure (Euclid (n + k))) (Λ : ℝ), μ₀ ∈ 𝓜 ∧ D μ₀ = ball 0 2 ∧ (∀ w ∈ ball (0 : Euclid (n + k)) 2, ((∀ ε : ℝ, 0 < ε → μ₀ (ball w ε) ≠ 0) ↔ z + r • w ∈ T.support)) ∧ (∀ μ ∈ 𝓜, ∀ K : Set (Euclid (n + k)), IsCompact K → μ K ≠ ∞) ∧ (∀ μ ∈ 𝓜, μ = (μHE[n] : Measure (Euclid (n + k))).withDensity (fun x => ENNReal.ofReal (dens μ x))) ∧ (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜 ∧ D (ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam)) = dilation y lam '' D μ) ∧ (∀ μ ∈ 𝓜, ∀ y : Euclid (n + k), ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid (n + k))), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ t : ℝ, 0 < t → ∀ w : Euclid (n + k), dens ν (t • w) = dens ν w) ∧ ∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν))) ∧ (∀ μ ∈ 𝓜, IsOpen (D μ) ∧ ball (0 : Euclid (n + k)) 2 ⊆ D μ) ∧ (∀ μ ∈ 𝓜, ∀ μs : ℕ → Measure (Euclid (n + k)), (∀ j, μs j ∈ 𝓜) → (∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))) → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ D μ → ∀ᶠ j in atTop, K ⊆ D (μs j)) ∧ (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (ρ : ℝ), 0 < ρ → closedBall y ρ ⊆ D μ → (∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ μ (ball y ρ)) ∧ (∀ ν ∈ 𝓜, ∀ L : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ L + 1 = n → (∀ y ∈ L, ∀ t : ℝ, 0 < t → ∀ w : Euclid (n + k), dens ν (y + t • w) = dens ν w) → ∃ Q : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ Q = n ∧ ∀ w : Euclid (n + k), (∀ ε : ℝ, 0 < ε → ν (ball w ε) ≠ 0) → w ∈ Q) ∧ (∀ ν ∈ 𝓜, (∀ t : ℝ, 0 < t → ∀ w : Euclid (n + k), dens ν (t • w) = dens ν w) → D ν = univ)
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 7 "Area Minimizing Currents"
(printed pp. 181–204)

Frozen contract.  Currents, boundary, mass, support and weak convergence are the clean SimonGMT
objects of `Poincare.SimonGMT.Chapter06`: `GeometricCurrentOn U n` (Simon 6.2.1), `T.boundary`
(6.2.3), `T.massOn W` = `M_W(T)` (6.2.5, Euclidean coefficient norm), `T.mass` (6.2.4),
`T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13), and the proper affine push-forward
`GeometricCurrentOn.affinePushforward` (6.2.23).  Everything else (integer multiplicity currents,
minimizing currents, densities, blow-ups, tangent cones, `reg T`, `sing T`, the associated
varifold) is defined below from primitive data.  `Hⁿ` is Mathlib's normalized `μHE[n]`; null-set
statements use Mathlib's `μH[s]` (same null sets as Simon's `Hˢ`).

**Conventions.**  The ambient space is `ℝ^{n+k}` (`Euclid (n + k)`); when a submanifold `N` is
present it has dimension `n + ℓ`, `ℓ ≤ k` (Simon writes `N^{n+ℓ} ⊂ ℝ^{n+ℓ}`, `ℓ ≤ k`, a
misprint for `ℝ^{n+k}`; `N = ℝ^{n+k}` is the case `ℓ = k`).  For an `n`-current, `∂T = 0`,
`∂S = ∂T`, `spt ∂T`, `M_W(∂T)` are read with Simon's convention `∂T = 0` if `n = 0` (6.2.3).
-/

open Filter Function Set MeasureTheory Metric
open scoped ENNReal Topology

namespace GMT.Ch07

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)

noncomputable section

/-- Euclidean space `ℝᴾ`. -/
abbrev Euclid (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Multivectors and integer multiplicity currents (Simon Ch. 6, §1 and 3.1) -/

/-- `n`-vectors `Λₙ(ℝᴾ)`, realized as the dual of `n`-covectors (Simon 6.1, `Λₙ ≅ (Λⁿ)*`);
`ξ α` is the pairing `⟨α, ξ⟩` of Simon (6.1.7). -/
abbrev MultiVector (P n : ℕ) := Covector (Euclid P) n →L[ℝ] ℝ

/-- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the subspace `Q`, i.e.
`⟨α, ξ⟩ = ±α(τ₁, …, τₙ)` (Simon 6.1.1, 6.1.7; 6.2.2).  The sign matters only for `n = 0`. -/
def IsUnitOrientationOf {n : ℕ} (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) : Prop :=
  ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = Q ∧
    ((∀ α : Covector (Euclid P) n, ξ α = α τ) ∨ ∀ α : Covector (Euclid P) n, ξ α = -α τ)

/-- Simon Ch. 6, Definition 3.1 (p. 146): a triple `(M, θ, ξ)` in `U`.  `M ⊆ U` is
`Hⁿ`-measurable (taken Borel; this loses nothing, `Hⁿ⌞M` being σ-finite) and countably
`n`-rectifiable; `θ` is positive integer-valued on `M` and locally `Hⁿ`-integrable in `U`; `ξ` is
`Hⁿ`-measurable and, `Hⁿ`-a.e. on `M`, orients the approximate tangent space `TₓM`
(Ch. 3, 1.4). -/
structure IMRep (U : Set (Euclid P)) (n : ℕ) where
  carrier : Set (Euclid P)
  mult : Euclid P → ℕ
  orient : Euclid P → MultiVector P n
  measurableSet_carrier : MeasurableSet carrier
  carrier_subset : carrier ⊆ U
  rectifiable : CountablyRectifiable n carrier
  measurable_mult : Measurable mult
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  locallyIntegrable_mult : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
    ∫⁻ x in carrier ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞
  aestronglyMeasurable_orient : AEStronglyMeasurable orient (μHE[n].restrict carrier)
  orients : ∀ᵐ x ∂(μHE[n].restrict carrier), ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n carrier x Q ∧ IsUnitOrientationOf (orient x) Q

variable {U : Set (Euclid P)} {n : ℕ}

/-- `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)` (Simon 6.3.1 (‡)). -/
def IMRep.action (R : IMRep U n) (ω : DifferentialForm (Euclid P) n) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]

/-- `T = τ(M, θ, ξ)` in `U`. -/
def IMRep.Represents (R : IMRep U n) (T : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, T ω = R.action (ω : DifferentialForm (Euclid P) n)

/-- The weight `μ_V = θ Hⁿ⌞M` of the associated varifold `V = v(M, θ)`; it equals the mass
measure `μ_T` of `T = τ(M, θ, ξ)` (Simon 6.3.2(3), 4.1.1). -/
def IMRep.measure (R : IMRep U n) : Measure (Euclid P) :=
  (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)

/-- Simon 6.3.1: `T` is an integer multiplicity (rectifiable) current. -/
def IsIntegerMultiplicity (T : GeometricCurrentOn U n) : Prop :=
  ∃ R : IMRep U n, R.Represents T

/-- Difference of currents (needed for `spt(S − T)` in 7.1.1). -/
instance : Sub (GeometricCurrentOn U n) where
  sub S T :=
    { toCurrent := S.toCurrent - T.toCurrent
      continuous' := fun ωs h => by
        simpa using (S.continuous' ωs h).sub (T.continuous' ωs h) }

/-! ## Boundary conventions in arbitrary degree -/

/-- `∂S = ∂T` in `U` (vacuous for `n = 0`, where `∂ = 0`). -/
def SameBoundary : {n : ℕ} → GeometricCurrentOn U n → GeometricCurrentOn U n → Prop
  | 0, _, _ => True
  | _ + 1, S, T => S.boundary = T.boundary

/-- `∂T = 0` in `U`. -/
def BoundaryVanishes : {n : ℕ} → GeometricCurrentOn U n → Prop
  | 0, _ => True
  | _ + 1, T => T.boundary = 0

/-- `spt ∂T` (empty for `n = 0`). -/
def boundarySupport : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P)
  | 0, _ => ∅
  | _ + 1, T => T.boundary.support

/-- `M_W(∂T)` (zero for `n = 0`). -/
def boundaryMassOn : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P) → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, T, W => T.boundary.massOn W

/-! ## Minimizing currents (Simon 7.1.1) -/

/-- `W ⊂⊂ U`: `closure W` is a compact subset of `U`. -/
def CompactlyContained (W U : Set (Euclid P)) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- **Simon 7.1.1 (p. 181).**  The integer multiplicity `T ∈ 𝒟ₙ(U)` is *minimizing in `A`*
(`A ⊆ U`): `M_W(T) ≤ M_W(S)` whenever `W ⊂⊂ U` is open, `S ∈ 𝒟ₙ(U)` is integer multiplicity,
`∂S = ∂T` in `U` and `spt(S − T)` is a compact subset of `A ∩ W`.  Competitors are integer
multiplicity, as required by Remark 7.2.2(1) and the proofs of 7.1.4 and 7.2.4. -/
def IsMinimizingIn (T : GeometricCurrentOn U n) (A : Set (Euclid P)) : Prop :=
  IsIntegerMultiplicity T ∧
    ∀ (W : Set (Euclid P)) (S : GeometricCurrentOn U n), IsOpen W → CompactlyContained W U →
      IsIntegerMultiplicity S → SameBoundary S T → IsCompact (S - T).support →
        (S - T).support ⊆ A ∩ W → T.massOn W ≤ S.massOn W

/-! ## Densities, blow-ups, tangent cones (Simon 7.3) -/

/-- `ωₙ`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ := volume (ball (0 : Euclid n) 1)

/-- `Θⁿ(μ_T, x) = θ`: `(ωₙρⁿ)⁻¹ μ_T(B_ρ(x)) → θ` as `ρ ↓ 0`, with `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)`
for small `ρ` (Simon 6.2.8; open and closed balls give the same limit). -/
def HasMassDensity (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ Tendsto (fun ρ : ℝ => T.massOn (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))

/-- Value of a current in `U` on an ambient form: `T(ω)` if `ω ∈ 𝒟ⁿ(U)`, else `0`.  Used for
convergence of currents on varying domains (Simon: "`η_{x,λⱼ#}T ⇀ C` in `ℝ^{n+ℓ}`"). -/
def currentEval (T : GeometricCurrentOn U n) (ω : DifferentialForm (Euclid P) n) : ℝ := by
  classical
  exact if h : IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0

/-- `Tⱼ ⇀ T` in `V`, for currents `Tⱼ ∈ 𝒟ₙ(Uⱼ)` whose domains eventually contain every compact
subset of `V` (as for blow-ups): `Tⱼ(ω) → T(ω)` for every `ω ∈ 𝒟ⁿ(V)` (Simon 6.2.13). -/
def ConvergesWeakly {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ ω : TestFormOn V n,
    Tendsto (fun j => currentEval (Ts j) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (T ω))

/-- `μ_{Tⱼ} → μ_T` as Radon measures in `V` (Simon 7.2.4, Remark 7.2.5(1)): for all integer
multiplicity representations of the `Tⱼ` and of `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for every
continuous `f` with compact support in `V`. -/
def MassMeasuresConverge {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ts j)) →
    ∀ R : IMRep V n, R.Represents T →
      ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
        Tendsto (fun j => ∫ x, f x ∂(Rs j).measure) atTop (𝓝 (∫ x, f x ∂R.measure))

/-- The linear part `y ↦ λ⁻¹y` of the dilation `η_{x,λ}`. -/
def dilationCLM (P : ℕ) (lam : ℝ) : Euclid P →L[ℝ] Euclid P :=
  lam⁻¹ • ContinuousLinearMap.id ℝ (Euclid P)

/-- Simon's dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, written `y ↦ −λ⁻¹x + λ⁻¹y`. -/
def dilation (x : Euclid P) (lam : ℝ) : Euclid P → Euclid P :=
  fun y => -(lam⁻¹ • x) + dilationCLM P lam y

/-- The blow-up `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))`, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` (Simon 6.2.23 for
the proper affine diffeomorphism `η_{x,λ}`, `λ ≠ 0`). -/
def blowUp (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : lam ≠ 0) :
    GeometricCurrentOn (dilation x lam '' U) n :=
  (T.restrictDomain (show (fun y => -(lam⁻¹ • x) + dilationCLM P lam y) ⁻¹'
      (dilation x lam '' U) ⊆ U by
    rintro y ⟨z, hz, hzy⟩
    have hzy' : lam⁻¹ • z = lam⁻¹ • y := by
      simpa [dilation, dilationCLM] using hzy
    rwa [← smul_right_injective (Euclid P) (inv_ne_zero hlam) hzy'])).affinePushforward
    (dilationCLM P lam) (-(lam⁻¹ • x)) (by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • x)))).isProperMap using 1
      funext y
      simp [dilationCLM])

/-- `C ∈ 𝒟ₙ(ℝᴾ)` is a cone: `η_{0,λ#}C = C` for every `λ > 0` (Simon 7.3.1(2)). -/
def IsConeCurrent (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam) (ω : TestFormOn (univ : Set (Euclid P)) n),
    currentEval (blowUp C 0 lam hlam.ne') (ω : DifferentialForm (Euclid P) n) = C ω

/-- Simon 7.3.2(1): `C` is a tangent cone of `T` at `x`, i.e. `η_{x,λⱼ#}T ⇀ C` in `ℝᴾ` for some
sequence `λⱼ > 0`, `λⱼ → 0`. -/
def IsTangentConeAt (T : GeometricCurrentOn U n) (x : Euclid P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∃ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) ∧
    ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C

/-- Simon 7.3.2(1): `T` has a (multiplicity `m`) tangent plane at `x`: some tangent cone has
support an `n`-dimensional subspace. -/
def HasTangentPlaneAt (T : GeometricCurrentOn U n) (x : Euclid P) : Prop :=
  ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, IsTangentConeAt T x C ∧
    ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ C.support = (Q : Set (Euclid P))

/-! ## Submanifolds, `reg T`, `sing T` (Simon Ch. 2, §4 and 7.4.1) -/

/-- Simon Ch. 2, §4, (4.1) (p. 55): `M ⊂ ℝᴾ` is a `d`-dimensional (embedded) `Cʳ` submanifold:
each `y ∈ M` has an open `W ∋ y` and a 1:1 `Cʳ` map `ψ : V → W`, `V ⊆ ℝᵈ` open, with
`ψ(V) = W ∩ M`, `ψ` proper, and `Dψ` of rank `d` on `V`. -/
def IsEmbeddedSubmanifold (r d : ℕ) (M : Set (Euclid P)) : Prop :=
  ∀ y ∈ M, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ z ∈ V, Injective (fderiv ℝ ψ z)

/-- Simon Ch. 2, §4 (p. 55): `T_yM = {γ'(0) : γ ∈ C¹((−1,1); ℝᴾ), γ((−1,1)) ⊆ M, γ(0) = y}`. -/
def tangentSpace (M : Set (Euclid P)) (y : Euclid P) : Set (Euclid P) :=
  {v | ∃ γ : ℝ → Euclid P, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ v 0}

/-- An orientation of the `d`-dimensional submanifold `M` (Simon 6.2.2): `ξ` is continuous on
`M` and `ξ(y) = ±τ₁ ∧ ⋯ ∧ τ_d` for an orthonormal basis `τ` of `T_yM`, for every `y ∈ M`. -/
def IsOrientation (d : ℕ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P d) : Prop :=
  ContinuousOn ξ M ∧ ∀ y ∈ M, ∃ Q : Submodule ℝ (Euclid P),
    (Q : Set (Euclid P)) = tangentSpace M y ∧ IsUnitOrientationOf (ξ y) Q

/-- **Simon 7.4.1 (p. 193)**: `reg T` is the set of `y ∈ spt T` such that, for some `ρ > 0`
(with `B_ρ(y) ⊆ U`), `m ∈ ℤ \ {0}` and embedded `n`-dimensional oriented `C¹` submanifold `M`
(of locally finite `Hⁿ`-measure in `B_ρ(y)`, as `[[M]]` requires, 6.2.2), `T = m[[M]]` in
`B_ρ(y)` (6.2.16), i.e. `T(ω) = m ∫_M ⟨ω, ξ_M⟩ dHⁿ` whenever `spt ω ⊆ B_ρ(y)`.
The point `y` itself must lie on `M` (as in 4.4(8) and the proof of 5.8): otherwise a singular
point could be declared regular by deleting it from `M`, e.g. the vertex of the Simons cone. -/
def regularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  {y | y ∈ T.support ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball y ρ ⊆ U ∧
    ∃ (m : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P n), m ≠ 0 ∧ y ∈ M ∧
      IsEmbeddedSubmanifold 1 n M ∧ IsOrientation n M ξ ∧
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[n] (M ∩ K) ≠ ∞) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y ρ →
        T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]}

/-- **Simon 7.4.1**: `sing T = spt T \ reg T`. -/
def singularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  T.support \ regularSet T

/-! ## The associated varifold `V = v(M, θ)` (Simon Ch. 4, 2.3–2.7 and 3.14) -/

/-- The approximate tangent plane `TₓM` (Ch. 3, 1.4; unique when it exists), `⊥` otherwise. -/
def approxTangentPlane (n : ℕ) (M : Set (Euclid P)) (x : Euclid P) :
    Submodule ℝ (Euclid P) := by
  classical
  exact if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥

/-- `div_M X(x) = Σⱼ eⱼ · ∇^M Xʲ = trace(p_{TₓM} ∘ DX(x))` (Simon Ch. 4, 2.3). -/
def tangentialDivergence (n : ℕ) (M : Set (Euclid P)) (X : Euclid P → Euclid P)
    (x : Euclid P) : ℝ :=
  LinearMap.trace ℝ (Euclid P)
    ((approxTangentPlane n M x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

/-- First variation `δV(X) = ∫_M div_M X dμ_V` of `V = v(M, θ)` (Simon Ch. 4, 2.2). -/
def IMRep.firstVariation (R : IMRep U n) (X : Euclid P → Euclid P) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x ∂μHE[n]

/-- Simon Ch. 4, 2.6 (computed form, p. 88): `V` is stationary in `U ∩ N`: `δV(X) = 0` for all
`X ∈ C¹_c(U; ℝᴾ)` with `X(x) ∈ TₓN` for every `x ∈ N ∩ U`. -/
def IMRep.IsStationaryAlong (R : IMRep U n) (N : Set (Euclid P)) : Prop :=
  ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → R.firstVariation X = 0

/-- Simon Ch. 4, 3.14: `V` has generalized mean curvature `H` in `U`
(`∫ div_M X dμ_V = −∫ X · H dμ_V`, `X ∈ C¹_c(U; ℝᴾ)`), with `H` bounded on compact subsets. -/
def IMRep.HasLocallyBoundedMeanCurvature (R : IMRep U n) : Prop :=
  ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧
    (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ᵐ x ∂R.measure, x ∈ K → ‖H x‖ ≤ Λ) ∧
    ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure

/-! ## Codimension one (Simon 7.5) -/

/-- Simon 7.5 (p. 197): `N ∈ 𝒪`, an oriented embedded `C²` submanifold of dimension `n + 1` with
`(N̄ \ N) ∩ U = ∅` and `N ∩ U ≠ ∅`, with chosen orientation `ξN`. -/
def InClassO (n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  IsEmbeddedSubmanifold 2 (n + 1) N ∧ IsOrientation (n + 1) N ξN ∧ (closure N \ N) ∩ U = ∅ ∧
    (N ∩ U).Nonempty

/-- Simon 7.5.1: `T = ∂[[E]]` in `U`, where `[[E]](ω) = ∫_E ⟨ω, ξ_N⟩ dH^{n+1}`. -/
def IsBoundaryOfRegion (T : GeometricCurrentOn U n) (E : Set (Euclid P))
    (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  ∀ ω : TestFormOn U n,
    T ω = ∫ x in E, ξN x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]

/-! ## Headline results -/

/-- **Simon 7.1.2 (Lemma, pp. 181–182).**  Let `N` be an embedded `C²` `(n+ℓ)`-dimensional
submanifold of `ℝ^{n+k}`, `(N̄ \ N) ∩ U = ∅`.  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`,
`spt T ⊆ N` and `∂T = 0` in `U`, then the associated varifold `V = v(M, θ)` (for any
representation `T = τ(M, θ, ξ)`) is stationary in `N ∩ U` (Ch. 4, 2.6) and has locally bounded
generalized mean curvature in `U` (Ch. 4, 3.14).
*Correction*: `spt T ⊆ N` and `(N̄ \ N) ∩ U = ∅` are implicit in the book (they are part of the
setting of Ch. 4, 2.5–2.6 and of §3); without `spt T ⊆ N` the lemma is false. -/
def MinimizingImpliesStationary : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    T.support ⊆ N → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T →
    ∀ R : IMRep U n, R.Represents T → R.IsStationaryAlong N ∧ R.HasLocallyBoundedMeanCurvature

/-- **Simon 7.2.1 (Lemma, p. 183).**  Let `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` be integer multiplicity with
`spt S` compact and `∂S = 0`.  Then there is an integer multiplicity `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`spt T` compact, `∂T = S`, and `M(T) ≤ M(R)` for every integer multiplicity `R` with `spt R`
compact and `∂R = S`.  Here `n = m + 2`: integer multiplicity currents have dimension `≥ 1`
(Ch. 6, §3).  *Correction*: the printed statement omits the conclusion `∂T = S` (proved: `T ∈ 𝓘_S`);
without it `T = 0` would do. -/
def ExistenceOfMinimizingFilling : Prop :=
  ∀ (m ℓ : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 1)),
    IsIntegerMultiplicity S → IsCompact S.support → S.boundary = 0 →
    ∃ T : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity T ∧ IsCompact T.support ∧ T.boundary = S ∧
      ∀ R : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R → IsCompact R.support → R.boundary = S → T.mass ≤ R.mass

/-- **Simon 7.2.4 (Theorem, p. 184).**  If `Tⱼ` are minimizing in `U`,
`supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for each open `W ⊂⊂ U`, and `Tⱼ ⇀ T ∈ 𝒟ₙ(U)`, then `T` is
(integer multiplicity, Remark 7.2.5(1), and) minimizing in `U`, and `μ_{Tⱼ} → μ_T` as Radon
measures in `U`. -/
def CompactnessOfMinimizingCurrents : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n),
    IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U →
      ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) →
    WeaklyConvergesOn Ts T → IsMinimizingIn T U ∧ MassMeasuresConverge (Us := fun _ => U) Ts T

/-- **Simon 7.3.1 (Theorem, p. 187).**  `N` as in 7.1.2 (`C²`).  If `T ∈ 𝒟ₙ(U)` is minimizing in
`U ∩ N` and `spt T ⊆ U ∩ N`, then (1) `Θⁿ(μ_T, x)` exists at every `x ∈ U \ spt ∂T` and is upper
semicontinuous there; (2) for `x ∈ spt T \ spt ∂T` and `λⱼ ↓ 0` (any `λⱼ > 0`, `λⱼ → 0`) there
are a subsequence `λⱼ'` and an integer multiplicity `C ∈ 𝒟ₙ(ℝ^{n+k})`, minimizing in `ℝ^{n+k}`,
with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η_{x,λⱼ'#}T} → μ_C`, `η_{0,λ#}C = C` (`λ > 0`) and
`Θⁿ(μ_C, 0) = Θⁿ(μ_T, x)`.
*Correction*: the printed hypothesis "`x ∈ spt T \ spt ∂T`" and "(1) … everywhere in `U`" are
garbled; the monotonicity proof gives (1) on `U \ spt ∂T`, which is what is stated. -/
def DensityAndTangentCones : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N →
    (∃ Θ : Euclid (n + k) → ℝ, (∀ x ∈ U \ boundarySupport T, HasMassDensity T x (Θ x)) ∧
        UpperSemicontinuousOn Θ (U \ boundarySupport T)) ∧
    ∀ x ∈ T.support \ boundarySupport T, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j),
      Tendsto lams atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧
        ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        IsMinimizingIn C univ ∧ IsConeCurrent C ∧
        ∃ θ : ℝ, HasMassDensity T x θ ∧ HasMassDensity C 0 θ

/-- **Simon 7.3.3 (Theorem, p. 189).**  `N` as in 7.3.1.  If `T` is minimizing in `U ∩ N`,
`spt T ⊆ U ∩ N` and `∂T = 0` in `U`, then (1) `Θⁿ(μ_T, x) ∈ ℤ` for all `x ∈ U \ E`, where
`H^{n−3+α}(E) = 0` for all `α > 0`; (2) there is `F ⊇ E` with `H^{n−2+α}(F) = 0` for all `α > 0`
such that `T` has a tangent plane at each `x ∈ spt T \ F`.
*Correction*: printed "`F ⊂ E`" must read `F ⊃ E` (non-integer density excludes tangent planes). -/
def IntegerDensityAndTangentPlanes : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∃ E F : Set (Euclid (n + k)), E ⊆ F ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧
      (∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m) ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧
      ∀ x ∈ T.support \ F, HasTangentPlaneAt T x

/-- **Simon 7.4.2 (Theorem, p. 194).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and minimizing in
`U ∩ N` (`N` an embedded `C²` `(n+ℓ)`-submanifold, `(N̄ \ N) ∩ U = ∅`), `spt T ⊆ U ∩ N` and
`∂T = 0` in `U`, then `reg T` is dense in `spt T`. -/
def RegularSetDense : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    T.support ⊆ closure (regularSet T)

/-- **Simon 7.4.3 (Theorem, p. 194)**, for a fixed `N` (`Nᵢ = N`).  Let `Tᵢ, T` be minimizing in
`U ∩ N`, `spt Tᵢ, spt T ⊆ N`, `∂Tᵢ = ∂T = 0` in `U`, `Tᵢ ⇀ T`, with
`supᵢ M_W(Tᵢ) < ∞` for `W ⊂⊂ U`.  If `y ∈ N ∩ U`, `Θⁿ(μ_T, y) = 1`, `y = lim yⱼ`, `yⱼ ∈ spt Tⱼ`,
then `y ∈ reg T` and `yⱼ ∈ reg Tⱼ` for all large `j`.
*Deviations*: the book allows `Nᵢ → N` "in the `C²` sense" (not defined at this point of the
book); we take `Nᵢ = N`.  The local mass bound is the hypothesis of 7.2.4, which the proof uses
for `μ_{Tⱼ} → μ_T`; it is added explicitly. -/
def DensityOneImpliesRegular : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n) (ys : ℕ → Euclid (n + k)) (y : Euclid (n + k)),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsMinimizingIn T (U ∩ N) →
    (∀ j, (Ts j).support ⊆ N) → T.support ⊆ N →
    (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) →
    WeaklyConvergesOn Ts T → y ∈ N ∩ U → HasMassDensity T y 1 →
    Tendsto ys atTop (𝓝 y) → (∀ j, ys j ∈ (Ts j).support) →
    y ∈ regularSet T ∧ ∀ᶠ j in atTop, ys j ∈ regularSet (Ts j)

/-- **Simon 7.4.4 (Theorem, p. 194).**  If `T` is as in 7.4.2 and `ξ ∈ spt T` has
`Θⁿ(μ_T, ξ) < 2`, then there is `ρ > 0` with `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0` for all `α > 0`. -/
def SingularSetSmallWhereDensityBelowTwo : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∀ ξ ∈ T.support, ∀ θ : ℝ, HasMassDensity T ξ θ → θ < 2 →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] (singularSet T ∩ ball ξ ρ) = 0

/-- **Simon 7.4.5 (Theorem, p. 195).**  If `C ∈ 𝒟ₙ(ℝ^{n+k})` is minimizing in `ℝ^{n+k}`, `∂C = 0`,
`C` is a cone, and `spt C ⊆ H̄` for an open half-space `H = {x : v · x > 0}` (`v ≠ 0`, so
`0 ∈ ∂H`), then `spt C ⊆ ∂H`. -/
def HalfSpaceConeLiesInBoundary : Prop :=
  ∀ (n k : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (v : Euclid (n + k)),
    IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → v ≠ 0 →
    C.support ⊆ closure {x | 0 < inner ℝ v x} → C.support ⊆ frontier {x | 0 < inner ℝ v x}

/-- **Simon 7.5.8 (Theorem, p. 200).**  Let `N ∈ 𝒪` (oriented by `ξN`), `E ⊆ N ∩ U`
`H^{n+1}`-measurable, `T = ∂[[E]] ∈ 𝒟ₙ(U)` integer multiplicity and minimizing in `N ∩ U`.  Then
`sing T = ∅` if `n ≤ 6`; `sing T` is locally finite in `U` (finite on compact subsets of `U`) if
`n = 7`; `H^{n−7+α}(sing T) = 0` for all `α > 0` if `n > 7`.  (`N = ℝ^{n+1}` is the case `k = 1`.)
-/
def CodimensionOneRegularity : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    (n ≤ 6 → singularSet T = ∅) ∧
    (n = 7 → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ U → (singularSet T ∩ K).Finite) ∧
    (7 < n → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 7 + α] (singularSet T) = 0)

/-- **Simon 7.5.11 (Corollary, p. 202).**  If `T` is as in 7.5.8, `T = τ(M, θ, ξ)`, and
`T₁ ∈ 𝒟ₙ(U)` is obtained by equipping a connected component `M₁` of `reg T` with multiplicity
`1` and the orientation `ξ` of `T`, then `∂T₁ = 0` in `U` and `T₁` is minimizing in `U ∩ N`. -/
def RegularComponentsAreMinimizing : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    ∀ R : IMRep U n, R.Represents T → ∀ y ∈ regularSet T, ∀ T₁ : GeometricCurrentOn U n,
      (∀ ω : TestFormOn U n, T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
        R.orient x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]) →
      BoundaryVanishes T₁ ∧ IsMinimizingIn T₁ (U ∩ N)

end

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 1 and 2 — (a)–(f), density functions (i)–(ix) and (T3s) — and the extremal analysis of step 4; Simon 7.3.3, proof of 3.3(1) (chapter-07.txt lines 454–478: the class 𝒯, (6)–(12)) and proof of 3.3(2) (lines 511–533: (1), (4), (5)), with the parent's departures [D1] (members encoded by their mass measures; the domain is a function D of the measure, recovered from total mass and barycenter) and [D2] (one rescaled ball), and one further departure [D3]. [D3] The zero-scale part of the class is the set of weights of ALL minimizing cycles S ∈ 𝒟_n(ℝ^P) (IsMinimizingIn S univ, ∂S = 0), not only of the weak limits of blow-ups of T at moving centres. Appendix A.4 (consumed by the sibling class_reduction through (M1)–(M9)) needs the class only to be closed under the rescalings of A.1 and to contain the tangent limits of A.2. Tangent limits of positive-scale members are tangent cones of T at points of spt T (DTC (2)) or 0; tangent limits of minimizing cycles of ℝ^P are their tangent cones (DTC (2) with U = N = ℝ^P) or 0; all of these are again minimizing cycles of ℝ^P (step 4(e), step 5). Hence the moving-centre compactness theorem (moving_blowups), the diagonal lemma, the uniform mass bounds and the countable-test criterion of parent step 2(b), (d), (e) are not needed, and neither are moving_blowups nor weak_limit_mass_bound. Every property consumed later, (M1)–(M9), is verified below for this class. Positive-scale members are the rescalings μ_{x,λ} of μ₀ = μ_{T'} (parent (a)). The hypotheses enter as follows: (MON) gives monotonicity and density bounds, (DTC) gives tangent cones, (PS) gives the planar support of (n−1)-invariant members, and (DEM) gives μ = Hⁿ.withDensity(dens μ). The selected node discharges (MON), (DTC) and (PS) with its registered children monotonicity, tangent_cones and planar_support (the last applied to cone_splitting and one_dim_cones), and (DEM) with its registered dependency density_eq_multiplicity_ae. Uses the reused accepted siblings im_mass_measure (Submission.dimred_im_mass_measure), blowup_scaling (Submission.dtc_blowUp_scaling) and cone_measure_homogeneous (Submission.cone_current_imrep_measure_smul_image).
Conventions. P := n + k ≥ 1. η_{a,t} := dilation a t for t > 0, η_{a,t}(v) = t^{−1}(v − a): an affine homeomorphism and measurable embedding with inverse v ↦ a + tv; η_{y,s}∘η_{a,t} = η_{a+ty,ts}; η_{a,t}^{−1}(B_ρ(w)) = B_{tρ}(a + tw); η_{a,t}(B_ρ(v)) = B_{ρ/t}(η_{a,t}(v)); η_{a,t}(ℝ^P) = ℝ^P. For a measure μ, μ^{a,t} := ofReal(t^{−n})•μ.map(η_{a,t}); thus μ^{a,t}(A) = t^{−n}μ(η_{a,t}^{−1}A) for Borel A and (μ^{a,t})^{y,s} = μ^{a+ty,ts} (Measure.map_map, smul). ω_n := unitBallVolume n ∈ (0, ∞). For A ∈ 𝒟_n(V), η_{a,t#}A := blowUp A a t ∈ 𝒟_n(η_{a,t}(V)). For a current A on an open set V and an IMRep R of A, μ_A := R.measure; by im_mass_measure: (IM-a) M_W(A) = μ_A(W) for open W ⊆ V; (IM-b) for x ∈ V, x ∈ spt A ⟺ μ_A(B_ε(x)) ≠ 0 for all ε > 0; (IM-c) μ_A does not depend on R. spt μ, dens and vague convergence are as in the statement.
Basic facts. (F1) (Boundaries of blow-ups.) Let V ⊆ ℝ^P, A ∈ 𝒟_n(V) with ∂A = 0 in V (n ≥ 1), a ∈ ℝ^P and t > 0. By the contract's definition, blowUp A a t is the affine push-forward of the restriction of A to η_{a,t}^{−1}(η_{a,t}(V)) = V. The boundary commutes with the affine push-forward (SimonGMT GeometricCurrentOn.boundary_affinePushforward) and with restriction of the domain (both sides evaluate A on dω). Hence ∂(η_{a,t#}A) = η_{a,t#}(∂A) = 0, i.e. BoundaryVanishes (η_{a,t#}A). (F2) (blowup_scaling.) Let V be open, A ∈ 𝒟_n(V), a ∈ ℝ^P, t > 0, n ≥ 1. (2) If R represents A, some IMRep R' of η_{a,t#}A has R'.measure = (R.measure)^{a,t} (the Borel-set identity of blowup_scaling (2) and Measure.ext). (3) If A is minimizing in A₀ ⊆ ℝ^P, then η_{a,t#}A is minimizing in η_{a,t}(A₀). (F3) (ℝ^P as a submanifold.) ℝ^P is an embedded C² (n+k)-dimensional submanifold of itself: for every point take V = W = ℝ^P and ψ = id, which is open, C² and injective, with ψ(V) = W ∩ ℝ^P, V ∩ ψ^{−1}(K) = K compact for compact K, and Dψ = id injective. Also (closure ℝ^P ∖ ℝ^P) ∩ ℝ^P = ∅. So (MON) and (DTC) apply to a current minimizing in ℝ^P with U = N = ℝ^P, d := n + k, ℓ := k (U ∩ N = ℝ^P, spt ⊆ ℝ^P). (F4) (Vanishing off the support.) If A has open domain V and x ∈ V ∖ spt A, then x lies in the zero region of A (spt A = V ∖ zeroRegion A). So there is ε > 0 with B_ε(x) ⊆ V and μ_A(B_ε(x)) = 0 (IM-b, shrinking ε). Consequently, if t_j > 0 and t_j → 0, then μ_A^{x,t_j}(B_{ε/t_j}(0)) = t_j^{−n}μ_A(B_ε(x)) = 0. So ∫ f dμ_A^{x,t_j} = 0 as soon as tsupport f ⊆ B_{ε/t_j}(0), and ∫ f dμ_A^{x,t_j} → 0 for f ∈ C_c(ℝ^P). (F5) (Cone weights.) Let C ∈ 𝒟_n(ℝ^P) be a cone and R represent C. Then cone_measure_homogeneous gives μ_C(t·A) = t^nμ_C(A) for t > 0 and Borel A. Hence μ_C(B_ρ(tw)) = μ_C(t·B_{ρ/t}(w)) = t^nμ_C(B_{ρ/t}(w)), so the density ratio of μ_C at (tw, ρ) equals the ratio at (w, ρ/t). Since ρ ↦ ρ/t maps 𝓝[>]0 onto 𝓝[>]0, the limsups agree: dens μ_C(tw) = dens μ_C(w). (F6) (Uniqueness of vague limits.) If μ, ν are finite on compact sets and ∫ f dμ = ∫ f dν for all f ∈ C_c(ℝ^P), then μ = ν. Proof: let O be open and m ≥ 1; put f_m(x) := min(1, m·infDist(x, Oᶜ))·min(1, (m − |x|)⁺) if O ≠ ℝ^P and f_m(x) := min(1, (m − |x|)⁺) if O = ℝ^P. Each f_m is continuous with support in closedBall 0 m, 0 ≤ f_m ≤ 1_O, and f_m ↑ 1_O pointwise (for x ∈ O, infDist(x, Oᶜ) > 0 since Oᶜ is closed; for x ∉ O, f_m(x) = 0). By monotone convergence, μ(O) = lim_m ∫ f_m dμ = lim_m ∫ f_m dν = ν(O). Open sets form a π-system (isPiSystem_isOpen) generating the Borel σ-algebra (borel α is by definition generateFrom {s | IsOpen s}, and BorelSpace.measurable_eq), and the open balls B_m(0), m ∈ ℕ, are open sets of finite measure covering ℝ^P, so μ = ν (Measure.ext_of_generateFrom_of_iUnion). (F7) (Weak limits of blow-ups of cycles are cycles.) Let V ⊆ ℝ^P be open, A ∈ 𝒟_n(V) with ∂A = 0 in V, p ∈ V, s_j > 0 with s_j → 0, and C ∈ 𝒟_n(ℝ^P) with η_{p,s_j#}A ⇀ C in ℝ^P (ConvergesWeakly). Then ∂C = 0. Proof: write n = m + 1 and let ω ∈ 𝒟^m(ℝ^P), with tsupport ω ⊆ B_R(0). Then dω ∈ 𝒟^n(ℝ^P) and tsupport dω ⊆ tsupport ω (dω vanishes on the open set where ω vanishes). Choose δ > 0 with B_δ(p) ⊆ V. Then η_{p,s_j}(V) ⊇ η_{p,s_j}(B_δ(p)) = B_{δ/s_j}(0) ⊇ closedBall 0 R for all large j. For such j, ω and dω are test forms on η_{p,s_j}(V), so currentEval(η_{p,s_j#}A, dω) = (η_{p,s_j#}A)(dω) = ∂(η_{p,s_j#}A)(ω) = 0 by (F1). By ConvergesWeakly, C(dω) = lim_j currentEval(η_{p,s_j#}A, dω) = 0, i.e. (∂C)(ω) = 0. Hence ∂C = 0 (BoundaryVanishes C). (F8) (The zero current.) The zero current 0 ∈ 𝒟_n(ℝ^P) is represented by the IMRep with empty carrier, so it is integer multiplicity with weight 0. It is minimizing in ℝ^P (M_W(0) = 0 ≤ M_W(S') for every competitor S') and ∂0 = 0, and dens 0 ≡ 0. (F9) (Density representation; parent step 2 (iii), Simon Ch. 3, Remark 1.8(2) and Theorem 1.9.) Let V ⊆ ℝ^P and R ∈ IMRep V n with R.measure(K) < ∞ for every compact K ⊆ ℝ^P. Then R.measure = Hⁿ.withDensity(ofReal ∘ dens(R.measure)). Proof: (DEM) (n ≥ 1) gives, for Hⁿ-a.e. x, R.measure(B_ρ(x))/(ω_n·ofReal(ρ^n)) → g(x) := 1_{R.carrier}(x)·R.mult(x) ∈ ℕ as ρ → 0⁺. At such x, the limsup along the nontrivial filter 𝓝[>]0 equals the limit (Filter.Tendsto.limsup_eq). As g(x) ≠ ∞, ofReal(dens(R.measure)(x)) = ofReal(toReal(g(x))) = g(x) (ENNReal.ofReal_toReal). So ofReal ∘ dens(R.measure) = g Hⁿ-a.e. Hence Hⁿ.withDensity(ofReal ∘ dens(R.measure)) = Hⁿ.withDensity(g) (withDensity_congr_ae) = (Hⁿ.restrict R.carrier).withDensity(R.mult) (withDensity_indicator, R.carrier measurable) = R.measure (definition of IMRep.measure).
1. (Facts about T.) T is integer multiplicity (part of IsMinimizingIn); fix an IMRep R_T and put μ_T := R_T.measure. K := closedBall z (2r) is a compact subset of U. (a) μ_T(K) < ∞ (IMRep.locallyIntegrable_mult). (b) As n ≥ 1 and ∂T = 0, boundarySupport T = spt 0 = ∅ (every point of the open set U lies in the zero region of the zero current). (c) (MON) with d := n + ℓ (1 ≤ n ≤ n + ℓ ≤ n + k) gives the following: Λ_K ≥ 0 such that σ ↦ ofReal(e^{Λ_Kσ}/σ^n)·M_{B_σ(y)}(T) is nondecreasing on (0, R') whenever closedBall y R' ⊆ K; a function Θ with HasMassDensity T y Θ(y) for y ∈ U; and θ ≥ 1 whenever y ∈ spt T and HasMassDensity T y θ. (d) (Lower bound.) If p ∈ spt T, closedBall p R' ⊆ K and 0 < σ < R', then μ_T(B_σ(p)) ≥ e^{−Λ_Kσ}ω_nσ^n. Indeed f(τ) := ofReal(e^{Λ_Kτ}/τ^n)M_{B_τ(p)}(T) is nondecreasing on (0, R'). HasMassDensity T p Θ(p) says M_{B_τ(p)}(T)/(ω_nτ^n) → Θ(p), so f(τ) → ω_nΘ(p) as τ → 0⁺ (e^{Λ_Kτ} → 1). By monotonicity f(σ) ≥ ω_nΘ(p) ≥ ω_n, and M_{B_σ(p)}(T) = μ_T(B_σ(p)) by (IM-a).
2. (The measure μ₀.) μ₀ := (μ_T.restrict B_{2r}(z))^{z,r}, so μ₀(A) = r^{−n}μ_T(η_{z,r}^{−1}(A) ∩ B_{2r}(z)) and μ₀ is concentrated on η_{z,r}(B_{2r}(z)) = B_2(0). m₀ := μ₀(ℝ^P) = r^{−n}μ_T(B_{2r}(z)) ∈ (0, ∞). It is finite by 1(a). It is positive because some x ∈ spt T ∩ B_{2r}(z) (hypothesis) has μ_T(B_ε(x)) > 0 for a ball B_ε(x) ⊆ B_{2r}(z) (IM-b). Its barycenter b₀ := m₀^{−1}∫v dμ₀(v) exists (finite measure with bounded support).
3. (Positive-scale members.) Par := {(x, λ) ∈ ℝ^P × ℝ : 0 < λ ≤ 1, |x| ≤ 1 − λ}. For (x, λ) ∈ Par put μ_{x,λ} := μ₀^{x,λ} and G_{x,λ} := η_{x,λ}(B_2(0)) = B_{2/λ}(−x/λ). (a) μ_{0,1} = μ₀ and G_{0,1} = B_2(0) (η_{0,1} = id). (b) μ_{x,λ}(ℝ^P) = λ^{−n}m₀ ∈ (0, ∞), and μ_{x,λ} is concentrated on G_{x,λ}. Its barycenter μ_{x,λ}(ℝ^P)^{−1}∫w dμ_{x,λ}(w) equals (b₀ − x)/λ, because by change of variables ∫w dμ_{x,λ}(w) = λ^{−n}∫η_{x,λ}(v) dμ₀(v) = λ^{−n}λ^{−1}(m₀b₀ − m₀x). (c) (Injectivity.) If μ_{x,λ} = μ_{x',λ'} for (x, λ), (x', λ') ∈ Par, then λ = λ' (equal total masses, n ≥ 1, m₀ ∈ (0, ∞)) and x = x' (equal barycenters). (d) G_{x,λ} is open. It contains B_2(0) (|x|/λ + 2 ≤ 2/λ ⟸ |x| ≤ 2 − 2λ ⟸ |x| ≤ 1 − λ) and B_{1/λ}(0) (|x|/λ + 1/λ ≤ 2/λ as |x| ≤ 1). (e) (Rescaling.) For (x, λ) ∈ Par, y ∈ ℝ^P and t > 0, μ_{x,λ}^{y,t} = μ₀^{x+λy,λt}. If moreover 0 < t < 1 and |y| ≤ 1 − t, then (x + λy, λt) ∈ Par (|x + λy| ≤ 1 − λ + λ(1 − t) = 1 − λt), μ_{x,λ}^{y,t} = μ_{x+λy,λt} and G_{x+λy,λt} = η_{y,t}(G_{x,λ}). (f) (Relation to T.) For w ∈ ℝ^P, ρ > 0 and p := z + r(x + λw): μ_{x,λ}(B_ρ(w)) = (rλ)^{−n}μ_T(B_{rλρ}(p) ∩ B_{2r}(z)) (as η_{x,λ}∘η_{z,r} = η_{z+rx,rλ}). If closedBall w ρ ⊆ G_{x,λ}, then closedBall p (rλρ) ⊆ B_{2r}(z) (apply v ↦ z + r(x + λv)), and the intersection with B_{2r}(z) may be dropped. (g) (Continuity.) For f ∈ C_c(ℝ^P), (x, λ) ↦ ∫ f dμ₀^{x,λ} = λ^{−n}∫ f(η_{x,λ}(v)) dμ₀(v) is continuous on ℝ^P × (0, ∞), by dominated convergence (μ₀ is finite, f is bounded and continuous, η_{x,λ}(v) is continuous in (x, λ)). (h) (IMRep.) Each μ_{x,λ} is the weight of an IMRep that is finite on compact sets. By (F2)(2) applied to R_T and (z + rx, rλ), there is an IMRep R' of η_{z+rx,rλ#}T with R'.measure = μ_T^{z+rx,rλ}. Let R'' be its restriction to the open set G_{x,λ} = η_{z+rx,rλ}(B_{2r}(z)): carrier R'.carrier ∩ G_{x,λ}, same multiplicity and orientation, same domain. R'' is an IMRep. The carrier is Borel, contained in the domain, and countably n-rectifiable (a subset of a countably rectifiable set). The multiplicity is measurable, positive on the carrier and locally integrable (smaller carrier). The orientation is a.e. strongly measurable for the smaller restricted measure. For Hⁿ-a.e. v ∈ R'.carrier ∩ G_{x,λ}, the approximate tangent space of R'.carrier ∩ G_{x,λ} at v equals that of R'.carrier, because HasApproximateTangentSpaceAt is local: if B_δ(v) ⊆ G_{x,λ}, the images of R'.carrier ∩ G_{x,λ} and of R'.carrier under blowUpMap v ρ agree on B_{δ/ρ}(0), so the integrals of a fixed compactly supported f agree for all small ρ. Finally R''.measure = R'.measure.restrict G_{x,λ} = μ_{x,λ}: for the measurable embedding g = η_{z+rx,rλ}, (ν.restrict s).map g = (ν.map g).restrict (g(s)), and η_{z+rx,rλ} = η_{x,λ}∘η_{z,r}. It is finite by (b).
4. (Zero-scale members.) Let 𝒞 be the set of S ∈ 𝒟_n(ℝ^P) that are minimizing in ℝ^P (IsMinimizingIn S univ) with ∂S = 0 (BoundaryVanishes S). Let S ∈ 𝒞. (a) S is integer multiplicity (first conjunct of IsMinimizingIn); fix an IMRep R_S and put μ_S := R_S.measure (IM-c). (b) μ_S(K) < ∞ for compact K (IMRep.locallyIntegrable_mult, domain ℝ^P). (c) (MON) applied to S (U = N = ℝ^P, d := n + k, by (F3) and n ≤ n + k) gives the following. First, ρ ↦ ofReal(1/ρ^n)·μ_S(B_ρ(w)) is nondecreasing on (0, ∞) for every w (part (ii) with any R, and IM-a). Second, there is Θ_S with HasMassDensity S w Θ_S(w) for every w. Third, Θ_S ≥ 1 on spt S. Hence: (c1) μ_S(B_ρ(w)) ≥ ω_nρ^n for w ∈ spt S and ρ > 0 (as in 1(d), with Λ_K replaced by 0); (c2) HasMassDensity S w θ implies θ = dens μ_S(w): the ratio μ_S(B_ρ(w))/(ω_nρ^n) = M_{B_ρ(w)}(S)/(ω_nρ^n) converges to ofReal θ, so its limsup is ofReal θ, and toReal gives θ because θ ≥ 0; in particular dens μ_S = Θ_S; (c3) μ_S(ℝ^P) ∈ {0, ∞}: if some w ∈ spt S, then μ_S(ℝ^P) ≥ ω_nρ^n for all ρ; otherwise every point has a μ_S-null ball (IM-b), and as ℝ^P is a countable union of such balls (Lindelöf), μ_S = 0. (d) (Rescaling.) For every y ∈ ℝ^P and t > 0, let S' be η_{y,t#}S, regarded as a current on ℝ^P: its domain η_{y,t}(ℝ^P) equals ℝ^P. Formally, S' and the IMReps below are transported along this equality of sets, which changes none of the properties used. By (F2)(3) with A₀ = ℝ^P, S' is minimizing in η_{y,t}(ℝ^P) = ℝ^P. By (F1), ∂S' = 0. So S' ∈ 𝒞, and by (F2)(2), μ_{S'} = μ_S^{y,t}. (e) (Tangent measures.) Let y ∈ ℝ^P and λ_j > 0 with λ_j → 0. Claim: there are a strictly increasing sub and C ∈ 𝒞 with dens μ_C(tw) = dens μ_C(w) for all t > 0 and w and μ_S^{y,λ_{sub(j)}} → μ_C vaguely. Proof: suppose first y ∈ spt S, and apply (DTC)(2) to S at y. Its hypotheses hold with U = N = ℝ^P and ℓ := k by (F3) and (a), and boundarySupport S = ∅ as in 1(b). It gives a strictly increasing sub and C ∈ 𝒟_n(ℝ^P), minimizing in ℝ^P and a cone, with η_{y,λ_{sub(j)}#}S ⇀ C (ConvergesWeakly) and MassMeasuresConverge. By (F7) (V = ℝ^P, A = S, p = y, s_j = λ_{sub(j)}), ∂C = 0; so C ∈ 𝒞. MassMeasuresConverge, applied with the IMReps of (F2)(2) (weights μ_S^{y,λ_{sub(j)}}) and an IMRep of C (tsupport f ⊆ ℝ^P trivially), is the vague convergence. dens μ_C is homogeneous by (F5). If y ∉ spt S, take sub := id and C := 0 ∈ 𝒞 (F8): by (F4), μ_S^{y,λ_j} → 0 = μ_0 vaguely, and dens 0 ≡ 0.
5. (Tangent measures of positive-scale members.) Let (x, λ) ∈ Par, |y| < 1, λ_j > 0, λ_j → 0. Put p := z + r(x + λy) (|x + λy| < 1 − λ + λ = 1, so p ∈ B_r(z) ⊆ U) and s_j := rλλ_j. By 3(e) and the composition rule, μ_{x,λ}^{y,λ_j} = μ₀^{x+λy,λλ_j} = (μ_T.restrict B_{2r}(z))^{p,s_j}. This agrees with ν_j := μ_T^{p,s_j} on Borel subsets of η_{p,s_j}(B_{2r}(z)) ⊇ B_{R_j}(0), R_j := (2r − |p − z|)/s_j → ∞. Suppose first p ∈ spt T. (DTC)(2) at p (boundarySupport T = ∅, 1(b)) gives a strictly increasing sub and C ∈ 𝒟_n(ℝ^P), minimizing in ℝ^P and a cone, with η_{p,s_{sub(j)}#}T ⇀ C and MassMeasuresConverge. By (F7) (V = U, A = T), ∂C = 0, so C ∈ 𝒞. With the IMReps of (F2)(2) (weights ν_{sub(j)}), ∫ f dν_{sub(j)} → ∫ f dμ_C for f ∈ C_c(ℝ^P). Since tsupport f ⊆ B_{R_{sub(j)}}(0) for large j, ∫ f dμ_{x,λ}^{y,λ_{sub(j)}} = ∫ f dν_{sub(j)} eventually. So μ_{x,λ}^{y,λ_{sub(j)}} → μ_C vaguely, and dens μ_C is homogeneous by (F5). If p ∉ spt T, (F4) gives ν_j → 0 vaguely, hence μ_{x,λ}^{y,λ_j} → 0 vaguely (the two measures agree on B_{R_j}(0)); take sub := id and C := 0 ∈ 𝒞.
6. (Definition.) 𝓜 := {μ_{x,λ} : (x, λ) ∈ Par} ∪ {μ_S : S ∈ 𝒞}. D(μ) := G_{x,λ} if μ = μ_{x,λ} for some (x, λ) ∈ Par (unique by 3(c)), and D(μ) := ℝ^P otherwise. Λ := rΛ_K ≥ 0. No μ_S equals some μ_{x,λ} (total masses: 3(b) versus 4(c3)), so D(μ_S) = ℝ^P.
7. (μ₀ and the support relation.) μ₀ = μ_{0,1} ∈ 𝓜 and D(μ₀) = G_{0,1} = B_2(0) (3(a)). Let w ∈ B_2(0). For 0 < ε < 2 − |w|, 3(f) (x = 0, λ = 1) gives μ₀(B_ε(w)) = r^{−n}μ_T(B_{rε}(z + rw)). Both sides are nondecreasing in ε. Hence (μ₀(B_ε(w)) ≠ 0 for all ε > 0) ⟺ (μ_T(B_{ε'}(z + rw)) ≠ 0 for all ε' > 0) ⟺ z + rw ∈ spt T by (IM-b) (z + rw ∈ B_{2r}(z) ⊆ U).
8. (M1) holds by 3(b) and 4(b). (M2): every member is the weight of an IMRep finite on compact sets (3(h); 4(a), (b)), so (F9) gives μ = Hⁿ.withDensity(ofReal ∘ dens μ) for the given dens.
9. (M3) For μ = μ_{x,λ}, 3(e) gives μ^{y,t} = μ_{x+λy,λt} ∈ 𝓜 and D(μ^{y,t}) = G_{x+λy,λt} = η_{y,t}(G_{x,λ}) = η_{y,t}(D μ). For μ = μ_S, 4(d) gives μ^{y,t} = μ_{S'} with S' ∈ 𝒞, so D(μ^{y,t}) = ℝ^P = η_{y,t}(ℝ^P) = η_{y,t}(D μ).
10. (M4) holds by 5 (μ = μ_{x,λ}) and 4(e) (μ = μ_S), with ν := μ_C ∈ 𝓜 (the monotonicity of (λ_j) is not needed).
11. (M5) holds by 3(d) and D(μ_S) = ℝ^P.
12. (M6) Let μ, μ_j ∈ 𝓜 with μ_j → μ vaguely and K ⊆ D μ compact, and suppose K ⊄ D(μ_{j_i}) along a strictly increasing sequence (j_i). Since D(μ_S) = ℝ^P, μ_{j_i} = μ_{x_i,λ_i} with (x_i, λ_i) ∈ Par. As G_{x_i,λ_i} ⊇ B_{1/λ_i}(0) (3(d)) and K ⊆ B_{R_K}(0) for some R_K > 0, λ_i ≥ λ₀ := 1/R_K. The set {(x, λ) ∈ Par : λ ≥ λ₀} is compact, so along a further subsequence (x_i, λ_i) → (x*, λ*) in it. By 3(g), μ_{x_i,λ_i} → μ_{x*,λ*} vaguely; also μ_{x_i,λ_i} → μ vaguely. By (F6) (all finite on compact sets, (M1)), μ = μ_{x*,λ*}, so D μ = G_{x*,λ*} = B_{2/λ*}(−x*/λ*). The compact K lies in this open ball, so K ⊆ B_{2/λ*−ε}(−x*/λ*) for some ε > 0. As −x_i/λ_i → −x*/λ* and 2/λ_i → 2/λ*, K ⊆ B_{2/λ_i}(−x_i/λ_i) = G_{x_i,λ_i} for large i — a contradiction. Hence K ⊆ D(μ_j) for all large j.
13. (M7) Let μ ∈ 𝓜, y ∈ spt μ, ρ > 0 with closedBall y ρ ⊆ D μ. If μ = μ_S: y ∈ spt S by (IM-b), so (c1) gives μ(B_ρ(y)) ≥ ω_nρ^n ≥ e^{−Λρ}ω_nρ^n (Λ ≥ 0). If μ = μ_{x,λ}: put p := z + r(x + λy). By 3(f), closedBall p (rλρ) ⊆ B_{2r}(z) and μ(B_σ(y)) = (rλ)^{−n}μ_T(B_{rλσ}(p)) for 0 < σ ≤ ρ. As y ∈ spt μ, μ_T(B_{ε'}(p)) ≠ 0 for every ε' > 0, so p ∈ spt T (IM-b). Since closedBall p (rλρ) is a compact subset of the open ball B_{2r}(z), some R' > rλρ has closedBall p R' ⊆ K. Then 1(d) with σ := rλρ gives μ(B_ρ(y)) = (rλ)^{−n}μ_T(B_{rλρ}(p)) ≥ (rλ)^{−n}e^{−Λ_Krλρ}ω_n(rλρ)^n = e^{−Λ_Krλρ}ω_nρ^n ≥ e^{−Λρ}ω_nρ^n (λ ≤ 1, Λ_K ≥ 0).
14. (M9) Let ν ∈ 𝓜 with dens ν(tw) = dens ν(w) for all t > 0 and w. For t > 0 put m_t(u) := tu. Hⁿ(m_t(A)) = t^nHⁿ(A) for every set A (euclideanHausdorffMeasure_smul₀), so Hⁿ.map(m_t) = t^{−n}Hⁿ and ∫ h dHⁿ = t^n∫ h(tu) dHⁿ(u) for measurable h ≥ 0. With (M2) and h := 1_{t·A}·ofReal(dens ν): ν(t·A) = t^n∫_A ofReal(dens ν(tu)) dHⁿ(u) = t^n∫_A ofReal(dens ν(u)) dHⁿ(u) = t^nν(A) for Borel A. Hence ν(B_R(0)) = R^nν(B_1(0)) for R > 0, and ν(ℝ^P) = sup_R R^nν(B_1(0)) ∈ {0, ∞}. By 3(b), ν is not of the form μ_{x,λ}, so D ν = ℝ^P.
15. (M8) Let ν ∈ 𝓜 and L with dim L + 1 = n and dens ν(y + tw) = dens ν(w) for y ∈ L, t > 0, w. Taking y = 0, step 14 shows that ν is not of the form μ_{x,λ}; so ν = μ_S with S ∈ 𝒞. Let y ∈ L, t > 0, w ∈ ℝ^P and HasMassDensity S w θ. By 4(c2), θ = dens ν(w) = dens ν(y + tw) = Θ_S(y + tw), and HasMassDensity S (y + tw) Θ_S(y + tw) by 4(c); so HasMassDensity S (y + tw) θ. Thus the density of S is invariant as (PS) requires. (PS) applies (n ≤ n + k = P, dim L + 1 = n, S minimizing in ℝ^P, ∂S = 0) and gives an n-dimensional Q with spt S ⊆ Q. Every w with ν(B_ε(w)) ≠ 0 for all ε > 0 lies in spt S by (IM-b), hence in Q. ∎

## Key steps

1. (MON) on K = closedBall z (2r) gives lower density bounds at support points of T; μ₀ is the rescaled restriction of μ_T to B_{2r}(z).
2. Positive-scale members μ_{x,λ} = λ^{−n}(η_{x,λ})_#μ₀ with domains η_{x,λ}(B_2(0)); the parameters are recovered from total mass and barycenter.
3. Zero-scale members are the weights of all minimizing cycles of ℝ^P: closed under blow-ups (blowup_scaling, ∂ commutes with push-forward), weight 0 or ∞, density ≥ ω_nρ^n on balls at support points.
4. Tangent measures: (DTC)(2) at support points (of T, or of a minimizing cycle with U = N = ℝ^P) gives minimizing cones, which are cycles because ∂ passes to weak limits; off the support the limit is 0; cone weights are homogeneous.
5. (M2) from (DEM); (M6) from compactness of the parameter set and uniqueness of vague limits; (M7) from monotonicity; (M9) from homogeneity forcing total mass 0 or ∞; (M8) from (PS).

## Reference use

### local-project

Queries:
- `python3 -I -c json.load(/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `python3 scan of dag.json: status, candidate_commit, depends_on and children of root.dimension_reduction_results-a1.{monotonicity,moving_blowups,cone_splitting,one_dim_cones}-a1, root.density_and_tangent_cones-a1, root.minimizing_implies_stationary-a1, root.compactness_of_minimizing_currents-a1 (three levels)`
- `grep -n '_dependency_problem|_existing_lean_name_problem|_overlay_accepted_children|def _accepted_checkpoint' /runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py (lines 3159–3196, 2364–2368, 6512–6575)`
- `grep -l 'not inherited|dependency gap|unregistered|not registered' nodes/*/decomposition-audit-v*.json (precedents: density-gap-a1 audits v2–v8, threshold-reduction-a1 audit v4)`
- `python3 extraction of subproblem.natural_proof, lean_statement and proof_key_steps from the parent-child-handoff.json of the five unaccepted originals and of root.density_and_tangent_cones-a1.blowup_scaling-a1`
- `grep -c <name> dag.json; grep -rl <name> nodes (outside this node's own unactivated attempt-1 files); grep -rl <name> ../.swarm-worktrees/*/gmt-ch07/GMT for the eight fresh idtp_fons_ names (all zero)`
- `grep -n 'theorem GeometricCurrentOn.boundary_affinePushforward|restrictDomain_apply|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean`
- `grep -rn 'euclideanHausdorffMeasure_smul₀|ext_of_generateFrom_of_iUnion|isPiSystem_isOpen|def borel|withDensity_congr_ae|withDensity_indicator|Filter.Tendsto.limsup_eq|theorem ofReal_toReal|hausdorffMeasure_image_le|measure_biUnion_null_iff|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `lake env lean /tmp/fons_v2/check/Types.lean; lake env lean /tmp/fons_v2/check/Assembly.lean; lake env lean /tmp/fons_v2/check/AssemblyAx.lean (Lean v4.35.0-rc3 toolchain of the run)`
- `python3 replay of Runtime._topological, Runtime._dependency_problem and Runtime._existing_lean_name_problem on /tmp/fons_v2/subs.json against dag.json (updated_at 2026-10-13T10:29:45Z)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-4fcbfb5d62/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-monotonicity-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-one-dim-cones-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-abstract-dimension-reduction-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-im-mass-measure-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v8.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/operator-dependency-edits/20261013T091722Z-revert/receipt.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/tmp/fons_v2/check/Types.lean`
- `/tmp/fons_v2/check/Assembly.lean`
- `/tmp/fons_v2/check/AssemblyAx.lean`

Pins match: the snapshot manifest records project b4d606d (workspace HEAD) and Mathlib 25730c7c; SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Dependency status (dag.json 11:00Z): dimred_minimizing_monotonicity rlcr-lean, dimred_blowup_limit_moving_centres, density_and_tangent_cones, dimred_invariant_cone_splitting, dimred_one_dim_minimizing_cone and minimizing_implies_stationary speculative-ready — none accepted, all owned by other parents, so runtime.py (_existing_lean_name_problem; _accepted_checkpoint requires accepted/integrating/merged with a candidate commit, or proved) forbids reusing them here, and _overlay_accepted_children overlays only this node's children and depends_on (the handoff registers weak_limit_mass_bound and density_eq_multiplicity_ae only; the operator's dependency edit on the monotonicity node was reverted because the dependency was not in the frozen handoff). The accepted precedent for this situation is density-gap-a1 (audit v6 accepted fresh-named duplicates of unaccepted cross-branch theorems). Hence the split registers fresh-named obligations with types byte-identical to monotonicity, density_and_tangent_cones, cone_splitting, one_dim_cones and minimizing_implies_stationary, whose proofs are their handoff proofs with re-targeted sibling references, and removes moving_blowups and weak_limit_mass_bound altogether. Reused: abstract_dimension_reduction (9ab8e5d6), dimred_im_mass_measure (01ae2c59), dtc_blowUp_scaling (a94d596c), cone_current_imrep_measure_smul_image (e183b985), all accepted with isolated-comparator passes and identical types. Library: SimonGMT supplies GeometricCurrentOn.boundary_affinePushforward (AffineCurrentPushforward.lean:188), restrictDomain_apply and support = U ∖ zeroRegion (CurrentLocalEquality.lean); the snapshot Mathlib supplies euclideanHausdorffMeasure_smul₀ and addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (Geometry/Euclidean/Volume/Measure.lean), ext_of_generateFrom_of_iUnion (Measure/Restrict.lean:491), isPiSystem_isOpen and def borel = generateFrom {IsOpen} (BorelSpace/Basic.lean), withDensity_congr_ae and withDensity_indicator (WithDensity.lean), Filter.Tendsto.limsup_eq (Topology/Order/LiminfLimsup.lean:190), ENNReal.ofReal_toReal (Basic/ENNReal/Basic.lean:248), LipschitzWith.hausdorffMeasure_image_le (Hausdorff.lean:745), measure_biUnion_null_iff and exists_countable_dense. No library or accepted declaration provides Federer–Fleming compactness, Simon 7.1.2, 7.3.1 or Lemma 7.3.5 for the contract's currents; these enter only as the registered obligations. Lean: all 12 types elaborate; the parent assembly compiles from the 12 children and the registered dependency only, and the axiom-stub variant shows it uses exactly 7 children plus idtp_imrep_measure_density_ae; no fresh name is reserved anywhere.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
