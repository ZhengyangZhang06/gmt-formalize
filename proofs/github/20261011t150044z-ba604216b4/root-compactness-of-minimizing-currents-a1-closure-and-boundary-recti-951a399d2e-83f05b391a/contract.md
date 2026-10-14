<!-- theorem-id: gmt-ch07/root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1 -->

## Theorem `Submission.cbr_ci_plane_weight_ge_one`

Hypothesis names: (REP), (MR), (SL) are the exact frozen statements of the DAG theorems cmc_exists_massRepresentation, cmc_massOn_eq_imRep_measure, cmc_slice_mass_bounds (hypotheses of the selected parent cbr_cycle_isIntegerMultiplicity); (RU) is the exact frozen statement of the sibling cbr_setIntegral_eq_of_integral_eq, (CT) = (T1) ∧ (T2) ∧ (MM) that of cbr_measure_convergence_tools, (RECT) that of cbr_rectifiable_of_approx_tangent; whichever are needed appear verbatim as hypotheses of the Lean statement. In words: (REP) a current T ∈ 𝒟_n(U), U open, with M_W(T) < ∞ for open W ⊂⊂ U has a mass representation (μ, ξ): μ(ℝ^P∖U) = 0, μ(K) < ∞ for compact K ⊆ U, μ(W) = M_W(T) for open W, ξ μ-a.e. strongly measurable with |ξ(x)(α)| ≤ |α| for all x, α, T(ω) = ∫ξ(ω)dμ, and μ(E) = 0 whenever Hⁿ(E) = 0 provided also M_W(∂T) < ∞ for open W ⊂⊂ U; (MR) M_W(T) = R.measure(W) for an IMRep R of T in an open U and open W; (SL) for T ∈ 𝒟_{k+1}(U) with admissible representations (μ, ξ) of T and (μ', ξ') of ∂T and L-Lipschitz f there are currents A_t, B_t with A_t(ω) = ∫_{f<t}ξ(ω)dμ, B_t(η) = ∫_{f<t}ξ'(η)dμ', ∂A_t = B_t on forms supported off {f = t}, M_W(∂A_t − B_t) ≤ L·liminf_{h↓0}h⁻¹μ(W ∩ {t−h < f < t}) and ∫_a^b M_W(∂A_t − B_t)dt ≤ Lμ(W ∩ {a < f < b}) for open W; (RU) an identity ∫ξ₁(ω)dμ₁ = ∫ξ₂(ω)dμ₂ + ∫ξ₃(ω)dμ₃ between admissible pairs, valid for all test forms on an open U, remains valid with all integrals restricted to any Borel set; (T1) measures μ_j with sup_jμ_j(K) < ∞ on compacts have a subsequence converging to a Radon μ (against C_c, limsup on compacts ≤ μ, liminf on open sets ≥ μ); (T2) if X_j ⇀ X with admissible representations (μ_j, ξ_j), (μ_X, ξ_X), limsup_jμ_j(K) ≤ μ(K) on compacts, f continuous and μ{f = t} = 0, then ∫_{f<t}ξ_j(ω)dμ_j → ∫_{f<t}ξ_X(ω)dμ_X; (MM) if Z_j(t) ≤ L·liminf_{h↓0}h⁻¹μ_j(G ∩ {t−h < f < t}) on (a, b) then some measurable g ≥ liminf_jZ_j a.e. on (a, b) has ∫_a^b g ≤ L·liminf_jμ_j(G ∩ {a < f < b}); (RECT) a Borel M with Hⁿ(M) < ∞ having approximate tangent spaces Q(x) at Hⁿ-a.e. x ∈ M with x ↦ p_{Q(x)} Hⁿ⌞M-a.e. strongly measurable is countably n-rectifiable. Assume (REP), (SL), (CT). Let P, d ∈ ℕ, n := d+1, v = (v_1, …, v_n) orthonormal in ℝ^P, V₀ := span(v), θ₀ > 0, N ∈ ℕ, pairwise distinct w_1, …, w_N ∈ ℝ^P orthogonal to every v_j, α_1, …, α_N > 0, and ν := Σ_iα_iHⁿ⌞(V₀ + w_i) (Hⁿ = μHE[n]). Let C ∈ 𝒟_n(ℝ^P) with C(ω) = θ₀∫ω(y)(v_1, …, v_n)dν(y). Let Γ_k ∈ 𝒟_n(ℝ^P) with Γ_k ⇀ C and ∂Γ_k = 0, Borel measures μ_k finite on compacts and fields ξ_k μ_k-a.e. strongly measurable with |ξ_k(x)(β)| ≤ |β| μ_k-a.e. and Γ_k(ω) = ∫ξ_k(ω)dμ_k, such that limsup_kμ_k(K) ≤ θ₀ν(K) for every compact K; and let N_k ⊆ ℝ^P with μ_k(ℝ^P∖N_k) = 0 and limsup_kHⁿ(N_k ∩ K) ≤ ν(K) for every compact K. Then α_i ≥ 1 for every i.

Node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4831

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1297, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6132, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6137, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6146, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6148, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6156, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6165, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6175, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6181, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6190, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6198, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6218

## Lean problem

Declaration: `Submission.cbr_ci_plane_weight_ge_one`

```lean
(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) → ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P) (θ₀ : ℝ) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ) (ν : Measure (Euclid P)) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (Γs : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P (d + 1)) (Ns : ℕ → Set (Euclid P)), Orthonormal ℝ v → 0 < θ₀ → Injective w → (∀ (i : Fin N) (j : Fin (d + 1)), inner ℝ (w i) (v j) = 0) → (∀ i, 0 < α i) → ν = ∑ i, ENNReal.ofReal (α i) • (μHE[(d + 1)]).restrict {y : Euclid P | y - w i ∈ Submodule.span ℝ (Set.range v)} → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = θ₀ * ∫ y, (ω : DifferentialForm (Euclid P) (d + 1)) y v ∂ν) → WeaklyConvergesOn Γs C → (∀ k, (Γs k).boundary = 0) → (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → μs k K < ∞) → (∀ k, AEStronglyMeasurable (ξs k) (μs k)) → (∀ k, ∀ᵐ x ∂(μs k), ∀ β : Covector (Euclid P) (d + 1), |ξs k x β| ≤ covectorEuclideanNorm β) → (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)), Γs k ω = ∫ x, ξs k x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(μs k)) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μs k K) atTop ≤ ENNReal.ofReal θ₀ * ν K) → (∀ k, μs k (Ns k)ᶜ = 0) → (∀ K : Set (Euclid P), IsCompact K → limsup (fun k => μHE[(d + 1)] (Ns k ∩ K)) atTop ≤ ν K) → ∀ i, 1 ≤ α i
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

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 8 (V11, each α_i ≥ 1), stated for an abstract sequence: in the parent, Γ_k are the blow-ups, μ_k their mass measures and N_k = η_k(M'). Fact (O) (orthogonal invariance of the coefficient norm; proved here because the accepted DAG lemmas regcomp_covector_sq_sum_orthonormalBasis / regcomp_covector_eval_orthonormal_le / regcomp_exists_covector_eval_orthonormal_eq_one are not prerequisites of this node). For an orthonormal basis f = (f_1, …, f_P) of ℝ^P and a k-covector α, Σ_{j : Fin k → Fin P} α(f_{j(1)}, …, f_{j(k)})² = k!·|α|²: the left side is the squared Hilbert–Schmidt norm of the multilinear map α and does not depend on the orthonormal basis (expand α(Of_{j(1)}, …) multilinearly and use Σ_l O_{la}O_{lb} = δ_{ab}); for the standard basis non-injective j contribute 0 and each increasing multi-index I contributes k! equal terms α(e_I)². Consequences: (O1) if v = (v_1, …, v_k) is orthonormal then |α(v)| ≤ |α| (extend v to an orthonormal basis; the k! permutations of (1, …, k) already contribute k!α(v)²); (O2) β_v(u) := det(⟨u_i, v_j⟩)_{i,j} is a k-covector (multilinear and alternating in u) with β_v(v) = 1 and |β_v| = 1 (in a basis extending v its only non-zero values are ±1 on the permutations of (1, …, k)); (O3) if p : ℝ^P → ℝ^k, p(x) = (⟨x, v_1⟩, …, ⟨x, v_k⟩) with v orthonormal, then the pulled-back covector p^#γ := γ∘(p × ⋯ × p) of an l-covector γ on ℝ^k has |p^#γ| = |γ| (in a basis f extending v, p(f_i) = e_i for i ≤ k and 0 otherwise). 
0. Set-up. Fix i₀; α := α_{i₀}, w := w_{i₀}. Extend v to an orthonormal basis v_1, …, v_P of ℝ^P; p : ℝ^P → ℝⁿ, p(x) := (⟨x, v_1⟩, …, ⟨x, v_n⟩); q := orthogonal projection onto V₀^⊥. p is 1-Lipschitz and maps each plane V₀ + w_j isometrically onto ℝⁿ (w_j ⊥ V₀). By (O3), |p^#γ| = |γ| for covectors γ on ℝⁿ. dy := dy¹∧⋯∧dyⁿ; β_v := p^#dy, i.e. β_v(u) = det(⟨u_i, v_j⟩), so β_v(v) = 1 and |β_v| = 1 (O2). δ' := min_{j≠i₀}|w_j − w|/3 (δ' := 1 if N = 1), δ' > 0 since the w_j are distinct. g(x) := dist(x, V₀ + w) = |q(x) − w|, 1-Lipschitz; on V₀ + w_j, g ≡ |w_j − w|, which is 0 for j = i₀ and ≥ 3δ' for j ≠ i₀. Fix R > 0, Ω := p⁻¹(B_{3R}) (open), B_ρ := B_ρ(0) ⊆ ℝⁿ, ω_n := Lⁿ(B_1).
1. Empty annulus. A'' := p⁻¹(B̄_{3R}) ∩ {δ' ≤ g ≤ 2δ'} is compact (closed, and |p(x)| ≤ 3R, |q(x)| ≤ |w| + 2δ' bound |x|) and meets no plane V₀ + w_j, so ν(A'') = 0 and limsup_kμ_k(A'') ≤ θ₀ν(A'') = 0.
2. Slicing. For each k apply (SL) with U := ℝ^P, T := Γ_k, the admissible representation (μ_k, ξ_k), the admissible representation (0, 0) of ∂Γ_k = 0, f := g, L := 1: there are A_k(t) ∈ 𝒟_n(ℝ^P), B_k(t) ∈ 𝒟_d(ℝ^P) with A_k(t)(ω) = ∫_{g<t}ξ_k(ω)dμ_k, B_k(t)(φ) = ∫_{g<t}0 d0 = 0, and M_Ω(∂A_k(t) − B_k(t)) ≤ liminf_{h↓0}h⁻¹μ_k(Ω ∩ {t − h < g < t}). Write Z_{k,t} := A_k(t); since B_k(t) = 0, M_Ω(∂Z_{k,t}) ≤ liminf_{h↓0}h⁻¹μ_k(Ω ∩ {t − h < g < t}).
3. A good level t. Apply (CT)(MM) with μs := (μ_k), f := g, G := Ω, (a, b) := (δ', 2δ'), L := 1, Z_k(t) := M_Ω(∂Z_{k,t}); μ_k(Ω ∩ {δ' < g < 2δ'}) ≤ μ_k(A'') < ∞. It gives a measurable G̃ ≥ 0 with liminf_kM_Ω(∂Z_{k,t}) ≤ G̃(t) for a.e. t ∈ (δ', 2δ') and ∫_{(δ',2δ')}G̃ ≤ liminf_kμ_k(Ω ∩ {δ' < g < 2δ'}) ≤ limsup_kμ_k(A'') = 0. So G̃ = 0 a.e. on (δ', 2δ'); fix t ∈ (δ', 2δ') with liminf_kM_Ω(∂Z_{k,t}) = 0. The level set {g = t} meets no plane, so ν({g = t}) = 0.
4. Convergence of slices. Apply (CT)(T2) with U := ℝ^P, Xs := (Γ_k) with the representations (μ_k, ξ_k), X := C with the admissible representation (θ₀ν, ξ_v), ξ_v the constant n-vector β ↦ β(v) (|ξ_v(β)| ≤ |β| by (O1); C(ω) = ∫ξ_v(ω)d(θ₀ν)), limit measure θ₀ν (finite on compacts, limsup_kμ_k(K) ≤ θ₀ν(K), θ₀ν({g = t}) = 0), f := g: for every ω, Z_{k,t}(ω) = ∫_{g<t}ξ_k(ω)dμ_k → θ₀∫_{g<t}ω(y)(v)dν(y) = θ₀α∫_{V₀+w}ω(y)(v)dHⁿ(y), since among the planes only V₀ + w meets {g < t} (t < 2δ' < 3δ') and it lies inside {g < t}. Pass to a subsequence (not relabelled; all hypotheses and this convergence persist) with M_Ω(∂Z_k) → 0, Z_k := Z_{k,t}; dropping finitely many k, M_Ω(∂Z_k) < ∞ for all k.
5. Localisation of Z_k. If ω is a test form with tsupport ω ∩ {g ≤ t} = ∅, then ω vanishes on {g < t}, so Z_k(ω) = ∫_{g<t}ξ_k(ω(x))dμ_k = 0.
6. The projected currents. For b ∈ C_c^∞(B_{2R}) set Y_k(b dy) := ∫_{g<t}b(p(x))ξ_k(x)(β_v)dμ_k(x) (absolutely convergent: the integrand is bounded by sup|b| and vanishes outside the compact set p⁻¹(spt b) ∩ {g ≤ t}). Y_k is linear and |Y_k(b dy)| ≤ sup|b|·μ_k(p⁻¹(spt b) ∩ {g ≤ t}), so Y_k ∈ 𝒟_n(B_{2R}) (test forms converging to 0 in 𝒟ⁿ(B_{2R}) have supports in a fixed compact subset and converge uniformly). Mass: |ξ_k(β_v)| ≤ |β_v| = 1, so M(Y_k) ≤ μ_k(p⁻¹(B̄_{2R}) ∩ {g ≤ t}), a compact set; limsup_kM(Y_k) ≤ θ₀ν(p⁻¹(B̄_{2R}) ∩ {g ≤ t}) < ∞; dropping finitely many k, Λ := sup_kM(Y_k) < ∞.
7. ∂Y_k is small. Let γ be a test (n−1)-form on B_{2R} and χ ∈ C_c^∞(Ω; [0, 1]) with χ = 1 on a neighbourhood of the compact set {g ≤ t} ∩ p⁻¹(spt γ) ⊆ p⁻¹(B_{2R}) ⊆ Ω. Then ∂Y_k(γ) = Y_k(dγ) = ∫_{g<t}ξ_k((p^#dγ)(x))dμ_k = Z_k(χ·p^#dγ). As p^#dγ = d(p^#γ), χp^#dγ = d(χp^#γ) − dχ∧p^#γ, and dχ∧p^#γ vanishes on a neighbourhood of {g ≤ t} (there either χ ≡ 1 or p^#γ = 0), so Z_k(dχ∧p^#γ) = 0 by step 5. Hence ∂Y_k(γ) = ∂Z_k(χp^#γ); χp^#γ is a test form supported in Ω with |χp^#γ| ≤ |γ∘p| ≤ 1 if |γ| ≤ 1 (O3). Therefore M_{B_{2R}}(∂Y_k) ≤ M_Ω(∂Z_k) → 0.
8. Weak limit of Y_k. Fix χ₀ ∈ C_c^∞(Ω; [0, 1]) with χ₀ = 1 on the compact set {g ≤ t} ∩ p⁻¹(B̄_{2R}). For b ∈ C_c^∞(B_{2R}), Y_k(b dy) = Z_k(χ₀(b∘p)β_v) → θ₀α∫_{V₀+w}χ₀(y)b(p(y))β_v(v)dHⁿ(y) = θ₀α∫_{V₀+w}b(p(y))dHⁿ(y) = θ₀α∫_{B_{2R}}b dLⁿ (p|_{V₀+w} is an isometry onto ℝⁿ and Hⁿ = Lⁿ on ℝⁿ, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.map_euclideanHausdorffMeasure).
9. Densities. Apply (REP) with ambient ℝⁿ, U := B_{2R}, degree n, T := Y_k: locally finite mass (step 6) and locally finite boundary mass (step 7) give a mass representation (μ_{Y_k}, ξ_{Y_k}) with μ_{Y_k}(E) = 0 whenever Hⁿ(E) = 0, i.e. μ_{Y_k} ≪ Lⁿ, and μ_{Y_k}(B_{2R}) = M(Y_k) < ∞. By the Lebesgue decomposition (Measure.haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac) μ_{Y_k} = ρ_kLⁿ⌞B_{2R} with ρ_k := μ_{Y_k}.rnDeriv Lⁿ, and u_k := ρ_k.toReal·ξ_{Y_k}(dy) ∈ L¹(B_{2R}) (|u_k| ≤ ρ_k.toReal, ∫ρ_k = M(Y_k)) satisfies Y_k(b dy) = ∫b u_k dLⁿ for all b ∈ C_c^∞(B_{2R}) (integral_withDensity_eq_integral_toReal_smul).
10. u_k vanishes off the projection of N_k. S_k := p(N_k ∩ {g < t} ∩ p⁻¹(B_{2R})), E_k := toMeasurable(Lⁿ, S_k) (a Borel superset with Lⁿ(E_k ∩ B) = Lⁿ(S_k ∩ B) for Borel B, Lⁿ being σ-finite). Write h_k := ξ_k(β_v) (|h_k| ≤ 1 μ_k-a.e.), F := {g < t} ∩ p⁻¹(B_{2R}), and consider the finite Borel measures on B_{2R}: σ₁ := u_k⁺Lⁿ + p_*(h_k⁻μ_k⌞F) and σ₂ := u_k⁻Lⁿ + p_*(h_k⁺μ_k⌞F) (finite: ∫|u_k| < ∞ and μ_k(F) ≤ μ_k({g ≤ t} ∩ p⁻¹(B̄_{2R})) < ∞). By the definition of u_k and of Y_k, ∫b dσ₁ = ∫b dσ₂ for every b ∈ C_c^∞(B_{2R}). Two finite Borel measures on the open set B_{2R} with equal integrals of all of C_c^∞(B_{2R}) agree on every open G ⊆ B_{2R} (take smooth cutoffs 0 ≤ b_j ≤ 1_G with b_j ↑ 1_G, built from ContDiffBump/exists_contDiff_tsupport_subset as in a smooth Urysohn lemma, and monotone convergence), hence on all Borel sets (open sets form a π-system generating the Borel σ-algebra; Measure.ext_of_generate_finite). For a Borel set B ⊆ B_{2R}∖E_k, F ∩ p⁻¹(B) ⊆ ℝ^P∖N_k (a point of N_k in it would project into S_k ∩ B ⊆ E_k ∩ B = ∅), which is μ_k-null; so p_*(h_k^±μ_k⌞F)(B) = 0 and σ₁(B) = σ₂(B) gives ∫_Bu_k⁺dLⁿ = ∫_Bu_k⁻dLⁿ. With B := (B_{2R}∖E_k) ∩ {u_k > 0} and B := (B_{2R}∖E_k) ∩ {u_k < 0} this yields u_k = 0 Lⁿ-a.e. on B_{2R}∖E_k.
11. L¹ convergence to θ₀α on B_R. Fix 0 < s₀ < R/2 and a mollifier φ_{s₀} ∈ C_c^∞(B_{s₀}), φ_{s₀} ≥ 0, ∫φ_{s₀} = 1 (a ContDiffBump divided by its integral). (a) For x ∈ B̄_R, (u_k∗φ_{s₀})(x) = ∫u_k(y)φ_{s₀}(x − y)dy = Y_k(φ_{s₀}(x − ·)dy) (support in B_{R+s₀} ⊆ B_{2R}), which tends to θ₀α by step 8, and |Y_k(φ_{s₀}(x − ·)dy) − Y_k(φ_{s₀}(x' − ·)dy)| ≤ Λ·Lip(φ_{s₀})|x − x'| (step 6); pointwise convergence and equicontinuity on the compact B̄_R give sup_{B̄_R}|u_k∗φ_{s₀} − θ₀α| → 0. (b) BV estimate ∫_{B_R}|u_k − u_k∗φ_{s₀}| ≤ s₀M_{B_{2R}}(∂Y_k), by duality. Let g be Borel with |g| ≤ 1 and g = 0 off B_R. For ϑ ∈ (0, s₀) let g_ϑ := g∗φ_ϑ ∈ C_c^∞(B_{R+ϑ}) (|g_ϑ| ≤ 1, ∇g_ϑ = g∗∇φ_ϑ) and h_ϑ := g_ϑ − φ̌_{s₀}∗g_ϑ ∈ C_c^∞(B_{R+2s₀}) ⊆ C_c^∞(B_{2R}), φ̌(z) := φ(−z), so that h_ϑ(x) = ∫φ_{s₀}(z)(g_ϑ(x) − g_ϑ(x + z))dz = −∫φ_{s₀}(z)∫_0^1∇g_ϑ(x + sz)·z ds dz. By Fubini for the absolutely convergent integral defining Y_k, Y_k(h_ϑdy) = −∫φ_{s₀}(z)∫_0^1Y_k((∇g_ϑ(· + sz)·z)dy)ds dz. With ε_j := (−1)^{j−1}dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ (ε_1 := 1 if n = 1), for every smooth compactly supported f, (∇f·z)dy = d(f·Σ_jz_jε_j), so Y_k((∇f·z)dy) = ∂Y_k(f·Σ_jz_jε_j) and |f·Σ_jz_jε_j| ≤ |z|sup|f| (the ε_j are orthonormal for the coefficient norm); with f := g_ϑ(· + sz) (|f| ≤ 1, support in B_{R+ϑ+s₀} ⊆ B_{2R}) this gives |Y_k(h_ϑdy)| ≤ ∫φ_{s₀}(z)|z|dz·M_{B_{2R}}(∂Y_k) ≤ s₀M_{B_{2R}}(∂Y_k). Moreover Y_k(h_ϑdy) = ∫u_kh_ϑ = ∫(u_k − u_k∗φ_{s₀})g_ϑ (Fubini). As ϑ ↓ 0, g_ϑ → g at every Lebesgue point of g, i.e. Lⁿ-a.e. (|g∗φ_ϑ(x) − g(x)| ≤ sup|φ|ϑ^{−n}∫_{B_ϑ(x)}|g − g(x)|; Lebesgue differentiation via VitaliFamily/Besicovitch), with |g_ϑ| ≤ 1, so by dominated convergence (u_k − u_k∗φ_{s₀} ∈ L¹(B_{2R})) |∫(u_k − u_k∗φ_{s₀})g| ≤ s₀M_{B_{2R}}(∂Y_k). Choosing g := sign(u_k − u_k∗φ_{s₀})·1_{B_R} gives the estimate. (c) Hence ∫_{B_R}|u_k − θ₀α| ≤ s₀M_{B_{2R}}(∂Y_k) + Lⁿ(B_R)sup_{B̄_R}|u_k∗φ_{s₀} − θ₀α|, and limsup_k∫_{B_R}|u_k − θ₀α| ≤ 0 by step 7 and (a): ∫_{B_R}|u_k − θ₀α| → 0.
12. Conclusion. Since u_k = 0 a.e. on B_R∖E_k: θ₀α·Lⁿ(B_R∖E_k) ≤ ∫_{B_R}|u_k − θ₀α| → 0 (θ₀α > 0). Moreover Lⁿ(B_R ∩ E_k) = Lⁿ(B_R ∩ S_k) ≤ Lⁿ(p(N_k ∩ {g < t} ∩ p⁻¹(B_R))) ≤ Hⁿ(N_k ∩ {g < t} ∩ p⁻¹(B_R)) (p is 1-Lipschitz: LipschitzWith.hausdorffMeasure_image_le for μH[n], hence for μHE[n]; Hⁿ = Lⁿ on ℝⁿ) ≤ Hⁿ(N_k ∩ A') with A' := {g ≤ t} ∩ p⁻¹(B̄_R) compact. Hence ω_nRⁿ = Lⁿ(B_R) ≤ Lⁿ(B_R∖E_k) + Hⁿ(N_k ∩ A') and ω_nRⁿ ≤ limsup_kHⁿ(N_k ∩ A') ≤ ν(A') = αHⁿ((V₀ + w) ∩ p⁻¹(B̄_R)) = αω_nRⁿ, because only V₀ + w meets A' (t < 3δ'). Therefore α_{i₀} = α ≥ 1. ∎

## Key steps

1. Slice Γ_k by g = dist(·, V₀ + w); (MM) and the empty annulus give a level t with liminf_k M_Ω(∂(Γ_k⌞{g<t})) = 0.
2. (T2) gives Γ_k⌞{g<t} ⇀ θ₀α v-oriented Hⁿ⌞(V₀ + w); the slices vanish on forms supported off {g ≤ t}.
3. Project to V₀: Y_k = p_#(Γ_k⌞{g<t}) has M(∂Y_k) → 0, Y_k ⇀ θ₀α[[ℝⁿ]], and density u_k (REP) vanishing off p(N_k).
4. Mollification and the BV estimate give u_k → θ₀α in L¹(B_R); then Lⁿ(B_R) ≤ o(1) + Hⁿ(N_k ∩ A') yields α ≥ 1.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp Contract.lean Submission.lean (identical)`
- `rg -n 'cbr_ci_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project (no match); python3 -I scan of dag.json lean_name values (755 names, none with prefix cbr_ci_, so all 12 proposed names are fresh)`
- `rg -l --fixed-strings in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib for 'theorem ae_tendsto_average_norm_sub', 'theorem tendsto_filterAt', 'lemma isMulLeftInvariant_eq_smul ', 'theorem withDensity_rnDeriv_eq', 'theorem integral_map_equiv', 'theorem setIntegral_map', 'theorem Isometry.map_euclideanHausdorffMeasure', 'theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume', 'theorem MeasureTheory.euclideanHausdorffMeasure_homothety_image', 'theorem hausdorffMeasure_image_le', 'theorem ext_of_generateFrom_of_iUnion', 'ext_of_integral_eq_on_compactlySupported', 'theorem exists_contDiff_tsupport_subset', 'theorem integral_withDensity_eq_integral_toReal_smul', 'theorem measure_toMeasurable_inter', 'theorem tendsto_of_subseq_tendsto', 'theorem liminf_const_mul_of_ne_top', 'theorem integral_smul_measure', 'theorem finrank_span_eq_card', "theorem aemeasurable_of_tendsto_metrizable_ae'" (all found); rg -il isodiametric over Mathlib (no match)`
- `sed -n 1,130p Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d] := addHaarScalarFactor(volume, μH[d]) • μH[d]; the normalisation constant is an open TODO)`
- `lake env lean on scratch files importing GMT.Ch07.Submission with #check of every lemma cited in the child proofs (Besicovitch.vitaliFamily, VitaliFamily.ae_tendsto_average_norm_sub, Measure.isAddLeftInvariant_eq_smul, haveLebesgueDecomposition_add, singularPart_eq_zero_of_ac, setIntegral_map_equiv, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, Measure.hausdorffMeasure_le_liminf_tsum, Measure.addHaar_image_linearMap, Set.exists_isOpen_lt_of_lt, Real.smoothTransition, ... reachable; withDensity_rnDeriv_eq, Matrix.IsHermitian.det_eq_prod_eigenvalues, simon_theorem_3_3, ae_hausdorff_dimensionalUpperDensity_le_one not reachable and therefore avoided)`
- `grep in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT: ae_hausdorff_dimensionalUpperDensity_le_one, simon_theorem_3_3, simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure, HasApproximateTangentSpaceAt.unique, CountablyRectifiable.mono, GeometricCurrentOn.affinePushforward_apply, boundary_affinePushforward, exteriorDerivative_apply; import headers of Chapter01 Steiner*/IsodiametricBounds/EuclideanNormalization/HausdorffDensityBounds/DensityComparison (outside the contract's import closure)`
- `sed -n 380,720p and 1190,1215p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt (Simon Ch. 1, 2.1–2.10 isodiametric via Steiner symmetrization, 3.3–3.6, 3.26)`
- `sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py check_source_delta (a leaf may append one theorem only: no imports, no helper declarations) and runtime.py _existing_lean_name_problem/_solve_children (reuse of accepted names only with identical types; children get only their own depends_on/children as prerequisites)`
- `python3 scan of dag.json: frozen lean_statement of the siblings restrict_unique, convergence_tools, slice_limit, lower_density, rectifiable and of the selected node (component extraction of REP, MR, IMC, SL, DT, VO, CL(d), ISP, SLIM_{P,d}, LD_{P,d} with equality assertions); accepted nodes with related content (dtc_blowUp_imrep, dtc_hausdorff_dilation, dtc_approxTangent_dilation, regcomp_covector_*, exists_plane_cutoff_quadratic_moment_eq, continuous_blowUp_image_setIntegral, aemeasurable_starProjection_of_aemeasurable_norm_sq, hasApproximateTangentSpaceAt_iff_of_null_sdiff)`
- `lake env lean /tmp/cyc-decomp/lean/Final.lean: the 12 exact child types (elaborate), cbr_ci_assembly_check (frozen parent type from density_rep, good_points, pointwise, im_criterion + sibling statements as hypotheses) and cbr_ci_k10_glue_check (pointwise from blowup_limit, constant_planes, weight_ge_one, plane_integer + plane uniqueness); #print axioms: propext, Classical.choice, Quot.sound; verifier/lean_contract.py validate_lean_statement on all 12 (pass)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-33509b6e86/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/Unique.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/EuclideanNormalization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/IsodiametricBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cyc-decomp/lean/Final.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). No 'cbr_ci_' declaration exists in the snapshot or among the 755 DAG names. Every library lemma the child proofs rely on exists in the snapshot and is reachable from `import GMT.Ch07.Submission` (checked with #check); unreachable ones (RadonNikodym.withDensity_rnDeriv_eq, matrix eigenvalue/Hadamard lemmas, the SimonGMT density and isodiametric modules) are avoided. Mathlib has no isodiametric inequality and leaf proofs cannot add imports, so the parent's appeal to Simon 3.26(1) (upper density ≤ 1) is supplied by the new child isodiametric_bound (Simon 2.9–2.10, Steiner symmetrization) and reproved in good_points. All 12 exact propositions elaborate in the contract scope and pass the verifier's lexical check; a hypothesis-only Lean assembly proves the frozen parent type from density_rep, good_points, pointwise, im_criterion and the sibling statements, and pointwise follows from blowup_limit, constant_planes, weight_ge_one, plane_integer; both checks use only propext, Classical.choice, Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
