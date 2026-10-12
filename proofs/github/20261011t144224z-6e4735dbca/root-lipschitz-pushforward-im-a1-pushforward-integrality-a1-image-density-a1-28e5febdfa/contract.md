<!-- theorem-id: gmt-ch06/root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1 -->

## Theorem `Submission.lpf_pi_image_density`

Let P, Q, n ∈ ℕ and V ⊆ ℝ^Q open. Let M ⊆ ℝ^P be Hⁿ-null-measurable, and let θ : ℝ^P → ℝ satisfy θ(x) > 0 and θ(x) ∈ ℕ for x ∈ M, with θ Hⁿ⌞M-a.e. measurable. Let Ξ : ℝ^P → NVector(ℝ^Q, n) be Hⁿ⌞M-a.e. strongly measurable. Let f : ℝ^P → ℝ^Q be continuous on M with f(M) ⊆ V and Hⁿ(f(Z)) = 0 for every Z ⊆ M with Hⁿ(Z) = 0. Let G_k : ℝⁿ → ℝ^Q and O_k ⊆ ℝⁿ (k ∈ ℕ) be arbitrary, and S ∈ D_n(V). Assume:
(AF) for every Hⁿ-null-measurable A ⊆ M and every Hⁿ⌞A-a.e. measurable h : ℝ^P → [0, ∞], the fibre sum y ↦ Σ'_{x ∈ A, f(x) = y} h(x) is Hⁿ-a.e. measurable on ℝ^Q, and ∫⁻_A h·‖Ξ‖ₑ dHⁿ = ∫⁻ Σ'_{x ∈ A, f(x) = y} h(x) dHⁿ(y);
(LF) ∫⁻_{M ∩ f⁻¹(K)} ofReal(θ)·‖Ξ‖ₑ dHⁿ < ∞ for every compact K ⊆ V;
(CH) for Hⁿ⌞M-a.e. x with Ξ(x) ≠ 0 there are k, w ∈ O_k with G_k(w) = f(x), and an orthonormal σ : Fin n → ℝ^Q with span(range σ) = range DG_k(w), such that Ξ(x) = ‖Ξ(x)‖ • simpleNVector σ or Ξ(x) = −(‖Ξ(x)‖ • simpleNVector σ);
(S) S(ω) = ∫_M θ(x)·Ξ(x)(ω(f(x))) dHⁿ(x) for every ω ∈ Dⁿ(V).
Then there are Y ⊆ ℝ^Q and Ψ : ℝ^Q → NVector(ℝ^Q, n) with: Y ⊆ V; Y is Hⁿ-null-measurable; Hⁿ(Y ∩ K) < ∞ for every compact K ⊆ V; Ψ is Hⁿ⌞Y-a.e. strongly measurable; y ↦ ‖Ψ(y)‖ is Hⁿ-integrable on Y ∩ K for every compact K ⊆ V; for Hⁿ⌞Y-a.e. y, there are m ∈ ℕ, integers a_1,…,a_m, indices k_1,…,k_m ∈ ℕ, points w_i ∈ O_{k_i} with G_{k_i}(w_i) = y, and orthonormal σ_i : Fin n → ℝ^Q with span(range σ_i) = range DG_{k_i}(w_i) (i = 1,…,m), such that Ψ(y) = Σ_i a_i • simpleNVector σ_i; and S(ω) = ∫_Y Ψ(y)(ω(y)) dHⁿ(y) for every ω ∈ Dⁿ(V).

Node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/741

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2621, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2635

Decomposition children: None

## Lean problem

Declaration: `Submission.lpf_pi_image_density`

```lean
∀ (P Q n : ℕ) (V : Set (Eucl Q)) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (Ξ : Eucl P → NVector (Eucl Q) n) (f : Eucl P → Eucl Q) (G : ℕ → Eucl n → Eucl Q) (O : ℕ → Set (Eucl n)) (S : GeometricCurrentOn V n), IsOpen V → NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ x ∈ M, 0 < θ x) → (∀ x ∈ M, ∃ k : ℕ, θ x = k) → AEMeasurable θ ((μHE[n] : Measure (Eucl P)).restrict M) → AEStronglyMeasurable Ξ ((μHE[n] : Measure (Eucl P)).restrict M) → ContinuousOn f M → MapsTo f M V → (∀ Z ⊆ M, (μHE[n] : Measure (Eucl P)) Z = 0 → (μHE[n] : Measure (Eucl Q)) (f '' Z) = 0) → (∀ (A : Set (Eucl P)) (h : Eucl P → ℝ≥0∞), A ⊆ M → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → AEMeasurable h ((μHE[n] : Measure (Eucl P)).restrict A) → AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x) (μHE[n] : Measure (Eucl Q)) ∧ ∫⁻ x in A, h x * ‖Ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ A ∧ f x = y}, h x ∂(μHE[n] : Measure (Eucl Q))) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) < ∞) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), Ξ x ≠ 0 → ∃ k, ∃ w ∈ O k, G k w = f x ∧ ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧ Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧ (Ξ x = ‖Ξ x‖ • simpleNVector σ ∨ Ξ x = -(‖Ξ x‖ • simpleNVector σ))) → (∀ ω : TestFormOn V n, S ω = ∫ x in M, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))) → ∃ (Y : Set (Eucl Q)) (Ψ : Eucl Q → NVector (Eucl Q) n), Y ⊆ V ∧ NullMeasurableSet Y (μHE[n] : Measure (Eucl Q)) ∧ (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → (μHE[n] : Measure (Eucl Q)) (Y ∩ K) < ∞) ∧ AEStronglyMeasurable Ψ ((μHE[n] : Measure (Eucl Q)).restrict Y) ∧ (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) (μHE[n] : Measure (Eucl Q))) ∧ (∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ) (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q), (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧ Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧ Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i)) ∧ ∀ ω : TestFormOn V n, S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂(μHE[n] : Measure (Eucl Q))
```

### Frozen project context

`GMT/Ch06/Contract.lean` at `d8d46c9587747dee0751a1f780fcafdba16a3886` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 6 "Currents" (pp. 131–180)

Frozen contract.  Currents, boundary, mass and weak convergence are the clean SimonGMT
objects (`Poincare.SimonGMT.Chapter06`):

* `GeometricCurrentOn U n`: sequentially continuous linear functionals on `𝒟ⁿ(U)` (Simon 2.1);
* `T.boundary` (2.3), `T.massOn W` (2.5, Euclidean coefficient norm of Remark 2.6),
  `T.mass = T.massOn U` (2.4), `T.support` (2.11), `WeaklyConvergesOn` (2.13).

Integer multiplicity currents `τ(M, θ, ξ)` (3.1), restriction `T ⌞ A` (2.9), slices (4.6),
the Lipschitz push-forward (3.6), lattice polyhedral chains (§5) and the flat pseudometric
`d_W` (7.1) are defined below from primitive data.  Hausdorff measure `Hⁿ` is Mathlib's
normalized `μHE[n]` (equal to Lebesgue measure on `ℝⁿ`).

**Degree convention.**  `GeometricCurrentOn.boundary` is defined on degree `m + 1`.  Whenever
the book's statement involves `∂T` for an `n`-current with `n ≥ 1`, the Lean statement writes
the book's `n` as `m + 1`.  The ambient space is `ℝ^P` (book: `ℝ^P` in §2, §8, `ℝ^{n+ℓ}`
elsewhere); in §5–§6, where constants are `c(n, ℓ)`, the ambient space is `ℝ^{(m+1)+ℓ}`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace GMT.Ch06

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt)
open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity)

noncomputable section

/-- Euclidean space `ℝ^P`. -/
abbrev Eucl (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Basic notions -/

/-- Simon's `W ⊂⊂ U` for open `W`: `W` is open and `closure W` is a compact subset of `U`. -/
def CompactlyContainedOpen (W U : Set (Eucl P)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U

/-- Simon Ch. 6, 3.1 (p. 146) and 8.1 (p. 173): the conditions on the triple `(M, θ, ξ)`.

* `M ⊆ U` is `Hⁿ`-measurable and countably `n`-rectifiable (Ch. 3, 1.1);
* `θ` is positive on `M` and locally `Hⁿ`-integrable on `M` in `U`;
* `ξ : M → Λₙ(ℝ^P)` is `Hⁿ`-measurable and for `Hⁿ`-a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an
  orthonormal basis `τ` of the approximate tangent space `TₓM` of `M` (w.r.t. `θ`, Ch. 3, 1.7).

`n`-vectors are `NVector (ℝ^P) n` (the dual of `n`-covectors), so `⟨ω, ξ⟩ = ξ ω` and
`τ₁ ∧ ⋯ ∧ τₙ = simpleNVector τ`.  The sign `±` (as printed in 8.1) is only needed for `n = 0`,
where there is no frame to flip. -/
structure IsRectifiableTriple (U : Set (Eucl P)) (n : ℕ) (M : Set (Eucl P))
    (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) : Prop where
  subset : M ⊆ U
  nullMeasurableSet : NullMeasurableSet M (μHE[n] : Measure (Eucl P))
  countablyRectifiable : CountablyRectifiable n M
  pos : ∀ x ∈ M, 0 < θ x
  integrableOn : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
    IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))
  aestronglyMeasurable : AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M)
  orients : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∃ τ : Fin n → Eucl P,
    Orthonormal ℝ τ ∧
    HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
    (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)

/-- Simon Ch. 6, 3.1 (‡) (p. 146): `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)`. -/
def tauAction (n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (ω : DifferentialForm (Eucl P) n) : ℝ :=
  ∫ x in M, θ x * ξ x (ω x) ∂(μHE[n] : Measure (Eucl P))

/-- Simon Ch. 6, 8.1 (p. 173): `T` is *rectifiable*, `T = τ(M, θ, ξ)` with `θ` real-valued
(positive, locally `Hⁿ`-integrable; footnote 4). -/
def IsRectifiableCurrent {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Simon Ch. 6, 3.1 (p. 146): `T ∈ 𝒟ₙ(U)` is an *integer multiplicity (rectifiable) current*:
`T = τ(M, θ, ξ)` with `θ` positive integer-valued. -/
def IsIntegerMultiplicity {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ (∀ x ∈ M, ∃ k : ℕ, θ x = k) ∧
    ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Integral current (the hypothesis of Simon Ch. 6, 8.2, p. 176): `T` and `∂T` are both integer
multiplicity (both then have locally finite mass). -/
def IsIntegralCurrent {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) : Prop :=
  IsIntegerMultiplicity T ∧ IsIntegerMultiplicity T.boundary

/-! ## Measure representation, restriction, slices -/

/-- Simon Ch. 6, (2.7) (p. 136): `T(ω) = ∫ ⟨ω, v⟩ dμ`, with `⟨ω, v⟩` `μ`-integrable for every
test form `ω` (testing with `φ dx^α`, `φ = 1` on a compact `K ⊆ U`, this is equivalent to `v`
being locally `μ`-integrable on `U`).  No normalization of `v` is required: such `(μ, v)` exists
iff `T` has locally finite mass (Riesz, Ch. 1, 4.14), and the vector measure `v μ` on `U` is
then uniquely determined by `T`. -/
def IsMeasureRepresentation {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) : Prop :=
  ∀ ω : TestFormOn U n, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) n) x)) μ ∧
    T ω = ∫ x, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.9) (p. 136): `S = T ⌞ A` for a Borel set `A`, i.e.
`S(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`.  Defined through any representation of `T` as in (2.7); the result
does not depend on the representation (uniqueness of the vector measure `T⃗ μ_T`). -/
def IsRestriction {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) (A : Set (Eucl P))
    (S : GeometricCurrentOn U n) : Prop :=
  MeasurableSet A ∧ ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
    IsMeasureRepresentation T μ v ∧
    ∀ ω : TestFormOn U n, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.8) (p. 136): `μ` is the total variation (mass) measure `μ_T` of `T`:
`μ_T(W) = M_W(T)` for every open `W ⊂⊂ U`, and `μ_T` lives on `U`. -/
def IsMassMeasure {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) : Prop :=
  μ Uᶜ = 0 ∧ ∀ W, CompactlyContainedOpen W U → μ W = T.massOn W

/-- Simon Ch. 6, (4.6) (p. 157): the slice `⟨T, f, t₋⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}`
(sets taken inside `U`), for `T` with `M_W(T) + M_W(∂T) < ∞`. -/
def IsSlice {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ)
    (t : ℝ) (S : GeometricCurrentOn U m) : Prop :=
  ∃ (A : GeometricCurrentOn U (m + 1)) (B : GeometricCurrentOn U m),
    IsRestriction T {x | x ∈ U ∧ f x < t} A ∧
    IsRestriction T.boundary {x | x ∈ U ∧ f x < t} B ∧
    ∀ ω : TestFormOn U m, S ω = A.boundary ω - B ω

/-! ## Lipschitz push-forward -/

/-- Simon Ch. 6, (3.6) (p. 147) and Ch. 3, 2.1–2.2: `S = f_# T` for `T = τ(M, θ, ξ)` and `f`
locally Lipschitz, `f_# T(ω) = ∫_M ⟨ω(f(x)), (d^M f_x)_# ξ(x)⟩ θ(x) dHⁿ(x)`.

`L x` is any linear map agreeing with `d^M f_x` on `TₓM`; by Ch. 3, §2 (p. 76),
`d^M f_x(τ) = (d/dt) f(x + tτ)|_{t=0}` for `τ ∈ TₓM`, `Hⁿ`-a.e. `x ∈ M`.  As `ξ(x) ∈ Λₙ(TₓM)`,
the integrand only depends on `L x` restricted to `TₓM`, so `S` is uniquely determined. -/
def IsLipschitzPushforward {Q n : ℕ} {U : Set (Eucl P)} {V : Set (Eucl Q)}
    (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q) (S : GeometricCurrentOn V n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)),
    IsRectifiableTriple U n M θ ξ ∧ (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) ∧
    (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt n M θ x Tx →
        ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) ∧
    ∀ ω : TestFormOn V n, S ω =
      ∫ x in M, θ x * nVectorPushforward n (L x) (ξ x)
        ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))

/-! ## Lattice polyhedral chains (§5) -/

/-- Index of an `n`-face of the cubical lattice in `ℝ^N` (Simon Ch. 6, §5, p. 159): a lattice
point `z ∈ ℤ^N` and the increasing multi-index `α` of the `n` coordinate directions spanned. -/
abbrev LatticeFaceIndex (n N : ℕ) := (Fin N → ℤ) × SimonMultiIndex n N

/-- The closed face `ρ (z + F_α) ∈ 𝓛ₙ(ρ)`, `F_α = {x : xᵢ ∈ [0,1] (i ∈ α), xᵢ = 0 (i ∉ α)}`.
Every closed `n`-face of the decomposition `⋃_z ρ(z + C)` arises from exactly one index. -/
def latticeFace {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N) : Set (Eucl N) :=
  {x | ∀ i : Fin N,
    (i ∈ range F.2 → ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)) ∧
    (i ∉ range F.2 → x i = ρ * (F.1 i : ℝ))}

/-- `[[F]](ω) = ∫_F ⟨ω, e_{α₁} ∧ ⋯ ∧ e_{αₙ}⟩ dHⁿ` (2.2), `F` oriented by its coordinate
directions in increasing order. -/
def latticeFaceAction {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N)
    (ω : DifferentialForm (Eucl N) n) : ℝ :=
  ∫ x in latticeFace ρ F, ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))
    ∂(μHE[n] : Measure (Eucl N))

/-- `Pc = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]` as a current in `U` (the sum is locally finite). -/
def IsLatticeChain {n N : ℕ} {U : Set (Eucl N)} (ρ : ℝ) (β : LatticeFaceIndex n N → ℝ)
    (Pc : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, Pc ω = ∑' F, β F * latticeFaceAction ρ F ω

/-! ## Flat pseudometric (§7) -/

/-- Simon Ch. 6, (7.1) (p. 170): `d_W(T₁, T₂) = inf {M_W(S) + M_W(R) : T₁ − T₂ = ∂R + S,
R ∈ 𝒟ₙ₊₁(U), S ∈ 𝒟ₙ(U) integer multiplicity}`. -/
def flatDistance {U : Set (Eucl P)} {n : ℕ} (W : Set (Eucl P))
    (T₁ T₂ : GeometricCurrentOn U n) : ℝ≥0∞ :=
  ⨅ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n)
    (_ : IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
      ∀ ω : TestFormOn U n, T₁ ω - T₂ ω = R.boundary ω + S ω),
    S.massOn W + R.massOn W

/-! ## Headline results -/

/-- **Simon Ch. 6, Lemma 2.15 (p. 137).**  If `T_q ∈ 𝒟ₙ(U)` and `sup_q M_W(T_q) < ∞` for each
`W ⊂⊂ U`, there are a subsequence `T_{q'}` and `T ∈ 𝒟ₙ(U)` with `T_{q'} ⇀ T` and
`∫ ⟨ω, T⃗_{q'}⟩ dμ_{T_{q'}} → ∫ ⟨ω, T⃗⟩ dμ_T` for every continuous compactly supported `n`-form
`ω` on `U` (for all representations (2.7) of the `T_{q'}` and of `T`). -/
def CompactnessUnderMassBounds : Prop :=
  ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U n,
    (∀ W, CompactlyContainedOpen W U → (⨆ q, (T q).massOn W) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U n), StrictMono φ ∧
      WeaklyConvergesOn (fun q => T (φ q)) T₀ ∧
      ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U →
        ∀ (μ : ℕ → Measure (Eucl P)) (v : ℕ → Eucl P → NVector (Eucl P) n)
          (μ₀ : Measure (Eucl P)) (v₀ : Eucl P → NVector (Eucl P) n),
          (∀ q, IsMeasureRepresentation (T (φ q)) (μ q) (v q)) →
          IsMeasureRepresentation T₀ μ₀ v₀ →
          Tendsto (fun q => ∫ x, v q x (ω x) ∂(μ q)) atTop (𝓝 (∫ x, v₀ x (ω x) ∂μ₀))

/-- **Simon Ch. 6, Theorem 2.34 (Constancy Theorem, p. 142).**  If `U ⊆ ℝⁿ` is open and
connected, `T ∈ 𝒟ₙ(U)` and `∂T = 0`, then `T = c [[U]]` for a constant `c`, where
`[[U]](ω) = ∫_U ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.  (Book `n = m + 1`.) -/
def ConstancyTheorem : Prop :=
  ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → IsConnected U →
    ∀ T : GeometricCurrentOn U (m + 1), T.boundary = 0 →
      ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1),
        T ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume

/-- **Simon Ch. 6, Lemma 3.9 (p. 148).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity,
`f : U → V` (`V ⊆ ℝ^Q` open) is locally Lipschitz and `f | spt T` is proper, then the
push-forward `f_# T` of (3.6) exists in `𝒟ₙ(V)` and is integer multiplicity. -/
def LipschitzPushforwardIntegerMultiplicity : Prop :=
  ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
    ∀ (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q),
      IsIntegerMultiplicity T → LocallyLipschitzOn U f → MapsTo f U V →
      (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) →
      ∃ S : GeometricCurrentOn V n, IsLipschitzPushforward T f S ∧ IsIntegerMultiplicity S

/-- **Simon Ch. 6, Theorem 3.11 (Federer–Fleming Compactness Theorem, p. 149).**  If
`T_j ∈ 𝒟ₙ(U)` are integer multiplicity and `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all
`W ⊂⊂ U`, then some subsequence converges weakly in `U` to an integer multiplicity
`T ∈ 𝒟ₙ(U)`.  (Book `n = m + 1`.) -/
def FedererFlemingCompactness : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U (m + 1),
    (∀ j, IsIntegerMultiplicity (T j)) →
    (∀ W, CompactlyContainedOpen W U → (⨆ j, ((T j).massOn W + (T j).boundary.massOn W)) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U (m + 1)), StrictMono φ ∧
      IsIntegerMultiplicity T₀ ∧ WeaklyConvergesOn (fun j => T (φ j)) T₀

/-- **Simon Ch. 6, §4 Slicing (4.4–4.10, pp. 153–158).**  Let `T ∈ 𝒟ₙ(U)` with
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, and `f` Lipschitz on `U` (constant `L`).  Then the
slices `⟨T, f, t⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}` (4.6) exist for every `t`, satisfy
`spt ⟨T, f, t⟩ ⊆ spt T ∩ {f = t}` (4.8); if `T` is integer multiplicity they are integer
multiplicity for `L¹`-a.e. `t` (4.4, 4.5(2)); and for every open `W ⊆ U`, every `L_W` with
`|Df| ≤ L_W` a.e. on `W` (i.e. `L_W ≥ ess sup_W |Df|`) and `a < b` (4.10, upper integral):
`∫*_a^b M_W(⟨T, f, t⟩) dt ≤ L_W · M_W(T ⌞ {a < f < b})`.
The book prints `M(T ⌞ {a < f < b})` on the right of 4.10; its proof (4.9) gives the stronger
`M_W`, stated here.  (Book `n = m + 1`.) -/
def SlicingTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
    ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
    ∃ S : ℝ → GeometricCurrentOn U m,
      (∀ t, IsSlice T f t (S t)) ∧
      (∀ t, (S t).support ⊆ T.support ∩ {x | f x = t}) ∧
      (IsIntegerMultiplicity T → ∀ᵐ t ∂(volume : Measure ℝ), IsIntegerMultiplicity (S t)) ∧
      ∀ W, IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ a b : ℝ, a < b →
        ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R →
          ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧
            ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W

/-- **Simon Ch. 6, 5.3 (Deformation Theorem, scaled version, p. 160); `ρ = 1` is 5.1 (p. 159).**
For `n, ℓ ≥ 1` there is `C = C(n, ℓ)` such that for every `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`M(T) + M(∂T) < ∞` and every `ρ > 0`, `T − P = ∂R + S` where `P = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]`,
`M(P) ≤ C M(T)`, `M(∂P) ≤ C M(∂T)`, `M(R) ≤ C ρ M(T)`, `M(S) ≤ C ρ M(∂T)`,
`spt P ∪ spt R ⊆ {dist(·, spt T) < 2√(n+ℓ) ρ}`, `spt ∂P ∪ spt S ⊆ {dist(·, spt ∂T) < 2√(n+ℓ) ρ}`;
if `T` is integer multiplicity, `P, R` are integer multiplicity with `β_F ∈ ℤ`, and if moreover
`∂T` is integer multiplicity then so is `S`.
Errata: the book prints `n, k ∈ {1,2,…}` and `C(n, k)` for `n, ℓ`; `𝓛_j(ρ)` for `𝓛ₙ(ρ)`;
"so is s" for "so is S".  (Book `n = m + 1`.) -/
def DeformationTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ (T : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
    T.mass + T.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ →
    ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1))
      (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ)
      (R : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 2))
      (S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
      IsLatticeChain ρ β Pc ∧
      (∀ ω, T ω - Pc ω = R.boundary ω + S ω) ∧
      Pc.mass ≤ C * T.mass ∧ Pc.boundary.mass ≤ C * T.boundary.mass ∧
      R.mass ≤ C * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ C * ENNReal.ofReal ρ * T.boundary.mass ∧
      Pc.support ∪ R.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.support ∧
      Pc.boundary.support ∪ S.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.boundary.support ∧
      (IsIntegerMultiplicity T →
        (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity R) ∧
      (IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → IsIntegerMultiplicity S)

/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem, p. 168).**  For `n ≥ 2`, `ℓ ≥ 1` there is
`c = c(n, ℓ)` such that every integer multiplicity `T ∈ 𝒟ₙ₋₁(ℝ^{n+ℓ})` with compact support and
`∂T = 0` bounds an integer multiplicity `R ∈ 𝒟ₙ(ℝ^{n+ℓ})` with compact support and
`M(R)^{(n−1)/n} ≤ c M(T)`.  (Book `n = m + 2`.) -/
def IsoperimetricTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 1),
    IsIntegerMultiplicity T → IsCompact T.support → T.boundary = 0 →
    ∃ R : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = T ∧
      R.mass ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤ c * T.mass

/-- **Simon Ch. 6, 6.2 (Weak Polyhedral Approximation Theorem, p. 169).**  For integer
multiplicity `T ∈ 𝒟ₙ(U)`, `U ⊆ ℝ^{n+ℓ}` open, with `M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U`,
there are `ρ_k ↓ 0` and `P_k = ∑_{F ∈ 𝓛ₙ(ρ_k)} β^{(k)}_F [[F]]` with `β^{(k)}_F ∈ ℤ` and
`P_k ⇀ T` in `U`.  (Printed `F_n(ρ_k)`, `β_R^{(k)}` mean `𝓛ₙ(ρ_k)`, `β_F^{(k)}`.  Book `n = m + 1`.) -/
def PolyhedralApproximation : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ U : Set (Eucl (m + 1 + ℓ)), IsOpen U →
    ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℤ)
        (Pk : ℕ → GeometricCurrentOn U (m + 1)),
        (∀ k, 0 < ρ k) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧
        WeaklyConvergesOn Pk T

/-- **Simon Ch. 6, 6.3 (Boundary Rectifiability Theorem, p. 170).**  If `T ∈ 𝒟ₙ(U)` is integer
multiplicity and `M_W(∂T) < ∞` for all `W ⊂⊂ U` (printed `M(∂T)`), then `∂T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def BoundaryRectifiability : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) →
    IsIntegerMultiplicity T.boundary

/-- **Simon Ch. 6, Theorem 7.2 (p. 170).**  Let `T, T_j ∈ 𝒟ₙ(U)` be integer multiplicity with
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`.  Then `T_j ⇀ T` iff `d_W(T_j, T) → 0`
for every `W ⊂⊂ U`.  (Book `n = m + 1`.) -/
def FlatConvergenceIffWeakConvergence : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      (WeaklyConvergesOn Tj T ↔
        ∀ W, CompactlyContainedOpen W U →
          Tendsto (fun j => flatDistance W (Tj j) T) atTop (𝓝 0))

/-- **Simon Ch. 6, 8.1 (Rectifiability Theorem, p. 173).**  If `T ∈ 𝒟ₙ(U)` has
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and the upper density `Θ*ⁿ(μ_T, x) > 0` for `μ_T`-a.e.
`x ∈ U`, then `T = τ(M, θ, ξ)` is rectifiable (with real `θ`).  (Book `n = m + 1`.) -/
def RectifiabilityTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) →
    (∃ μ : Measure (Eucl P), IsMassMeasure T μ ∧
      ∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) →
    IsRectifiableCurrent T

/-- **Simon Ch. 6, Theorem 8.2 (p. 176).**  If `T_j, ∂T_j` are integer multiplicity,
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U` and `T_j ⇀ T ∈ 𝒟ₙ(U)`, then `T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def IntegralityOfWeakLimits : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)),
      (∀ j, IsIntegralCurrent (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      WeaklyConvergesOn Tj T → IsIntegerMultiplicity T

end

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) (Lean `Eucl P`) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which equals Lebesgue measure Lⁿ = volume on ℝⁿ. An n-covector on E is a continuous alternating n-linear map α : Eⁿ → ℝ with the operator norm. An n-vector is a continuous linear functional on n-covectors (`NVector E n`), also with the operator norm. simpleNVector v is the n-vector α ↦ α(v₁,…,vₙ). For a continuous linear map A, A_#u := nVectorPushforward n A u = u ∘ A^#, where A^#α = α(A·,…,A·). Thus A_# is linear in u, and A_#(simpleNVector v) = simpleNVector(A∘v) (`nVectorPushforward_simple`). `HasWeightedApproximateTangentSpaceAt n M θ x T` is Simon's weighted approximate tangent space (Ch. 3, 1.7). By SimonGMT `HasWeightedApproximateTangentSpaceAt.unique` it is unique when θ(x) ≠ 0, and its first component says dim T = n. The derivative clause for (M, θ, f, L) means: for Hⁿ⌞M-a.e. x, for every subspace T with HasWeightedApproximateTangentSpaceAt n M θ x T and every v ∈ T, the map t ↦ f(x + t v) has derivative L(x)v at t = 0. Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is Steps 4(b), 5, 8 and 9 of the parent proof, stated for an abstract n-vector field Ξ. The parent applies it with Ξ(x) = L(x)_#ξ(x). Two changes from the parent's write-up. First, the image set is taken as Y := {y ∈ V : 1 ≤ N(y) < ∞}, defined by the fibre counting function N; the parent used f(M₊) minus a null set. Second, the density c(y)ζ(y) of the parent is built directly as the fibre sum Ψ(y) = Σ_{x ∈ F_y} θ(x)η_x. Its measurability comes from the fibre-sum measurability in (AF), which the parent's Step 9 also uses, instead of from inverse charts. Throughout, Hⁿ = μHE[n] on ℝ^P and on ℝ^Q, and Σ' is the unordered (tsum) sum.

1. (Positive part.) Put M₊ := {x ∈ M : Ξ(x) ≠ 0} = M ∩ {‖Ξ‖ ≠ 0}. It is Hⁿ-null-measurable. The real function ‖Ξ‖ is Hⁿ⌞M-a.e. measurable, so it agrees with a measurable φ off a set N₀ with Hⁿ⌞M(N₀) = 0; then Hⁿ(N₀ ∩ M) ≤ Hⁿ⌞M(N₀) = 0 (`Measure.le_restrict_apply`). M ∩ {φ ≠ 0} is null-measurable, and its symmetric difference with M₊ lies in the Hⁿ-null set N₀ ∩ M. Since θ(x) ∈ ℕ and θ(x) > 0, θ ≥ 1 on M. For x ∈ M₊ put η(x) := ‖Ξ(x)‖⁻¹ • Ξ(x) and ϑ(x) := θ(x) • η(x) = (θ(x)‖Ξ(x)‖⁻¹) • Ξ(x). Then ‖η(x)‖ = 1 and ‖ϑ(x)‖ = θ(x). For y ∈ ℝ^Q let F_y := {x ∈ M₊ : f(x) = y}.
2. (Counting function.) N(y) := Σ'_{x ∈ F_y} ofReal(θ(x)) ∈ [0, ∞]. By (AF) with A := M₊ and h := ofReal∘θ (Hⁿ⌞M₊-a.e. measurable), N is Hⁿ-a.e. measurable.
3. (Local finiteness.) Let K ⊆ V be compact. f is continuous on M, so M ∩ f⁻¹(K) = M ∩ C for some closed C ⊆ ℝ^P (`continuousOn_iff_isClosed`). Apply (AF) with A := M₊ and h := ofReal(θ)·1_C, which is a.e. measurable on M₊. For x ∈ F_y, 1_C(x) = 1_K(f(x)) = 1_K(y), so the fibre sum of h is 1_K(y)·N(y). Hence ∫⁻ 1_K N dHⁿ = ∫⁻_{M₊} h‖Ξ‖ₑ ≤ ∫⁻_M 1_C ofReal(θ)‖Ξ‖ₑ = ∫⁻_{M ∩ C} ofReal(θ)‖Ξ‖ₑ = ∫⁻_{M ∩ f⁻¹(K)} ofReal(θ)‖Ξ‖ₑ < ∞, using (LF).
4. (N < ∞ a.e.) For y ∉ V, F_y = ∅ because f(M) ⊆ V, so N(y) = 0. The open set V is a countable union of compact sets K_i ⊆ V (V is σ-compact: the subtype V is locally compact by `IsOpen.locallyCompactSpace`, so `SigmaCompactSpace.exists_compact_covering` applies to it; take the images of its compact sets in ℝ^Q). By Step 3 and `ae_lt_top'`, 1_{K_i}N < ∞ Hⁿ-a.e. for each i. Hence Hⁿ({y : N(y) = ∞}) = 0.
5. (The set Y.) Y := {y : y ∈ V, N(y) ≠ 0, N(y) ≠ ∞}. Clearly Y ⊆ V, and Y is Hⁿ-null-measurable (V open, N a.e. measurable). Let y ∈ Y. Then F_y ≠ ∅, since an empty sum is 0. F_y is finite: each term ofReal(θ(x)) is ≥ 1, so any m distinct points of F_y contribute ≥ m to N(y) < ∞ (`ENNReal.sum_le_tsum`). Moreover N(y) ≥ 1. For compact K ⊆ V, Y ∩ K ⊆ {y : 1 ≤ 1_K(y)N(y)}, so Markov's inequality (`meas_ge_le_lintegral_div` or `mul_meas_ge_le_lintegral₀`) gives Hⁿ(Y ∩ K) ≤ ∫⁻ 1_K N < ∞ (Step 3).
6. (The density.) Ψ(y) := Σ'_{x ∈ F_y} ϑ(x), a tsum in the finite-dimensional normed space NVector(ℝ^Q, n); in Lean the sum runs over the subtype {x // x ∈ M₊ ∧ f x = y}. For y ∈ Y the fibre is finite, so Ψ(y) = Σ_{x ∈ F_y} ϑ(x) (`tsum_fintype`) and ‖Ψ(y)‖ ≤ Σ_{x ∈ F_y} θ(x) = N(y).toReal.
7. (Measurability of Ψ on Y.) Let β be an n-covector on ℝ^Q and g_β(x) := ϑ(x)(β), a real function that is Hⁿ⌞M₊-a.e. strongly measurable (θ, Ξ are, and ζ ↦ ζ(β) is continuous). Let N^±_β be the fibre sums over M₊ of ofReal(±g_β). By (AF) both are Hⁿ-a.e. measurable. For y ∈ Y (finite fibre), Ψ(y)(β) = Σ_{x ∈ F_y} g_β(x) = N⁺_β(y).toReal − N⁻_β(y).toReal. So y ↦ Ψ(y)(β) is Hⁿ⌞Y-a.e. measurable for every β. The space Covector(ℝ^Q, n) of n-covectors is finite-dimensional by the sibling lemma lpf_pi_covector_finiteDimensional (in Lean: `haveI := Submission.lpf_pi_covector_finiteDimensional Q n`). Do not use the instance `Module.Finite.multilinearMap`: its module Mathlib.LinearAlgebra.Multilinear.FiniteDimensional is not imported by GMT.Ch06.Submission, and a child may not add imports. Choose a basis b_1,…,b_D of Covector(ℝ^Q, n) (e.g. `Module.finBasis`) and put b*_i := the i-th coordinate functional of this basis, a continuous linear functional on Covector(ℝ^Q, n) (every linear functional on a finite-dimensional space is continuous, `LinearMap.toContinuousLinearMap`). Then b*_i is an n-vector with b*_i(b_l) = δ_il. Every n-vector ζ equals Σ_i ζ(b_i) • b*_i: evaluate at α = Σ_l (coord_l α) b_l (`Module.Basis.sum_repr`) and use linearity of ζ. Hence Ψ = Σ_i Ψ(·)(b_i) • b*_i on Y, a finite sum of (a.e. measurable real function) • (constant n-vector). So Ψ is Hⁿ⌞Y-a.e. strongly measurable (`AEStronglyMeasurable.smul_const`, `Finset.aestronglyMeasurable_fun_sum`; see the Lean note below for the needed `ContinuousAdd` instance).
8. (Integrability.) Let K ⊆ V be compact. ‖Ψ‖ is Hⁿ⌞(Y ∩ K)-a.e. strongly measurable by Step 7, and ∫⁻_{Y∩K} ‖Ψ‖ₑ ≤ ∫⁻_{Y∩K} N ≤ ∫⁻ 1_K N < ∞ by Steps 3 and 6. So ‖Ψ‖ is integrable on Y ∩ K.
9. (Chart family.) Let B := {x ∈ M : Ξ(x) ≠ 0 and the conclusion of (CH) fails at x}. By (CH) and null-measurability of M, Hⁿ(B) = 0, so E := f(B) is Hⁿ-null by the null-image hypothesis (B ⊆ M). Let y ∈ Y ∖ E. Every x ∈ F_y lies in M₊ ∖ B (else y = f(x) ∈ E). So (CH) gives k_x, w_x ∈ O_{k_x} with G_{k_x}(w_x) = f(x) = y, and an orthonormal σ_x with span(range σ_x) = range DG_{k_x}(w_x) and Ξ(x) = ε_x‖Ξ(x)‖ • simpleNVector σ_x, ε_x ∈ {1, −1}. Then ϑ(x) = (ε_x θ(x)) • simpleNVector σ_x, and a_x := ε_x·θ(x) ∈ ℤ because θ(x) ∈ ℕ. Enumerate the finite set F_y as x_1,…,x_m via an equivalence with Fin m (`Fintype.equivFin`). Set a_i := a_{x_i}, k_i := k_{x_i}, w_i := w_{x_i}, σ_i := σ_{x_i}. Reindexing the finite sum of Step 6 gives Ψ(y) = Σ_i a_i • simpleNVector σ_i. Hⁿ⌞Y-a.e. y lies in Y ∖ E (Y null-measurable, E null), so this is the asserted a.e. family.
10. (Representation.) Fix ω ∈ Dⁿ(V). K_ω := tsupport ω is compact with K_ω ⊆ V, ω is continuous, and C_ω := sup_y |ω(y)| < ∞.
 (a) On M ∖ M₊, Ξ = 0, so the integrand of (S) vanishes. With M null-measurable and M₊ ⊆ M, `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero` gives S(ω) = ∫_{M₊} θ(x)Ξ(x)(ω(f(x))) dHⁿ.
 (b) Let g(x) := ϑ(x)(ω(f(x))). It is Hⁿ⌞M₊-a.e. strongly measurable, because ω∘f is continuous on M and evaluation (ζ, α) ↦ ζ(α) is continuous. Since M is only null-measurable, pick a measurable M₀ ⊆ M with Hⁿ(M ∖ M₀) = 0 (`NullMeasurableSet.exists_measurable_subset_ae_eq`). Then Hⁿ⌞M = Hⁿ⌞M₀ and `ContinuousOn.aestronglyMeasurable` applies on M₀ ⊆ M. On M₊, g(x)·‖Ξ(x)‖ = θ(x)Ξ(x)(ω(f(x))). Also |g(x)|·‖Ξ(x)‖ = θ(x)|Ξ(x)(ω(f(x)))| ≤ C_ω θ(x)‖Ξ(x)‖ 1_{K_ω}(f(x)). So ∫⁻_{M₊} ‖g‖ₑ‖Ξ‖ₑ ≤ C_ω ∫⁻_{M ∩ f⁻¹(K_ω)} ofReal(θ)‖Ξ‖ₑ < ∞, by (LF) and the closed-set argument of Step 3.
 (c) Apply the sibling lemma lpf_pi_signed_fibre_sum with (X, μ) := (ℝ^P, Hⁿ), (Y, ν) := (ℝ^Q, Hⁿ), the map f, A := M₊, J := ‖Ξ‖ₑ (a.e. measurable), and g. Its area-identity hypothesis is (AF) for A = M₊. Since ‖Ξ(x)‖ₑ.toReal = ‖Ξ(x)‖, it gives ∫_{M₊} g‖Ξ‖ dHⁿ = ∫ Σ'_{x ∈ F_y} g(x) dHⁿ(y). By (b) the left side is the integral in (a).
 (d) For y ∈ Y: Σ'_{x ∈ F_y} g(x) = Σ_{x ∈ F_y} ϑ(x)(ω(y)) = (Σ_{x ∈ F_y} ϑ(x))(ω(y)) = Ψ(y)(ω(y)). Here f(x) = y on F_y, and a finite sum of linear maps is evaluated termwise. For y ∉ Y with N(y) ≠ ∞: either y ∉ V or N(y) = 0, and in both cases F_y = ∅, so the sum is 0. Since Hⁿ({N = ∞}) = 0 (Step 4), Σ'_{x ∈ F_y} g(x) = 1_Y(y)·Ψ(y)(ω(y)) for Hⁿ-a.e. y.
 (e) By (a)–(d) and null-measurability of Y (`integral_indicator₀`), S(ω) = ∫ 1_Y·Ψ(ω) dHⁿ = ∫_Y Ψ(y)(ω(y)) dHⁿ(y). ∎

Lean note (verified in this environment; engineering advice, not part of the mathematics). For maps into `NVector (Eucl Q) n`, instance search fails for `ContinuousAdd`, `TopologicalSpace.PseudoMetrizableSpace`, `ContinuousENorm` and `ContinuousEval`. So `AEStronglyMeasurable.add/.norm/.enorm`, `Finset.aestronglyMeasurable_fun_sum` and `continuous_eval` do not apply out of the box. Working replacements: (1) `have : ContinuousAdd (NVector (Eucl Q) n) := ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl Q) n)).toContinuousAdd.continuous_add⟩`, after which finite sums and `.add` of a.e.-strongly-measurable n-vector fields work; (2) `(@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable h` for y ↦ ‖Ψ y‖, then `ofReal_norm` to pass to ‖·‖ₑ; (3) `continuous_fst.clm_apply continuous_snd` for continuity of (ζ, α) ↦ ζ α; (4) express sets such as {Ψ ≠ 0} as {‖Ψ‖ ≠ 0}, so null-measurability comes from the real-valued a.e.-measurable function ‖Ψ‖.

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_image_density : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses the declared siblings `Submission.lpf_pi_signed_fibre_sum`, `Submission.lpf_pi_covector_finiteDimensional`. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro P Q n V M θ Ξ f G O S hV hM hθpos hθnat hθm hΞm hfc hfV hnull hAF hLF hCH hS
  classical
  generalize hμdef : (μHE[n] : Measure (Eucl P)) = μ at *
  generalize hνdef : (μHE[n] : Measure (Eucl Q)) = ν at *
  have hCA : ContinuousAdd (NVector (Eucl Q) n) :=
    ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl Q) n)).toContinuousAdd.continuous_add⟩
  -- Step 1: positive part
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθnat x hx
    have h0 := hθpos x hx
    rw [hk] at h0 ⊢
    have hk0 : 0 < k := by exact_mod_cast h0
    exact_mod_cast hk0
  obtain ⟨Mp, hMp⟩ : ∃ Mp : Set (Eucl P), Mp = {x | x ∈ M ∧ Ξ x ≠ 0} := ⟨_, rfl⟩
  have hMp_mem : ∀ x, x ∈ Mp ↔ x ∈ M ∧ Ξ x ≠ 0 := by intro x; rw [hMp]; rfl
  have hMpM : Mp ⊆ M := fun x hx => ((hMp_mem x).1 hx).1
  obtain ⟨M₀, hM₀M, hM₀m, hM₀ae⟩ := hM.exists_measurable_subset_ae_eq
  have hrestr : μ.restrict M₀ = μ.restrict M := Measure.restrict_congr_set hM₀ae
  have hnΞ : AEStronglyMeasurable (fun x => ‖Ξ x‖) (μ.restrict M₀) := by
    rw [hrestr]
    exact (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΞm
  have hMpnm : NullMeasurableSet Mp μ := by
    obtain ⟨φ, hφm, hφeq⟩ : ∃ φ : Eucl P → ℝ, Measurable φ ∧
        (fun x => ‖Ξ x‖) =ᵐ[μ.restrict M₀] φ :=
      ⟨hnΞ.mk _, hnΞ.stronglyMeasurable_mk.measurable, hnΞ.ae_eq_mk⟩
    have h1 : ∀ᵐ x ∂μ, x ∈ M₀ → ‖Ξ x‖ = φ x :=
      (ae_restrict_iff' hM₀m).1 hφeq
    have h2 : ∀ᵐ x ∂μ, x ∈ M₀ ↔ x ∈ M := eventuallyEqSet_iff.1 hM₀ae
    have hmeas : MeasurableSet (M₀ ∩ {x | φ x ≠ 0}) :=
      hM₀m.inter (hφm (measurableSet_singleton 0).compl)
    refine hmeas.nullMeasurableSet.congr (eventuallyEqSet_iff.2 ?_)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hMp_mem]
    constructor
    · rintro ⟨hxM₀, hφx⟩
      refine ⟨hx2.1 hxM₀, ?_⟩
      intro hΞx
      apply hφx
      rw [← hx1 hxM₀, hΞx]
      exact ContinuousLinearMap.opNorm_zero
    · rintro ⟨hxM, hΞx⟩
      have hxM₀ : x ∈ M₀ := hx2.2 hxM
      refine ⟨hxM₀, ?_⟩
      show φ x ≠ 0
      rw [← hx1 hxM₀]
      exact fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
  have hAFp : ∀ h : Eucl P → ℝ≥0∞, AEMeasurable h (μ.restrict Mp) →
      AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, h x) ν ∧
      ∫⁻ x in Mp, h x * ‖Ξ x‖ₑ ∂μ = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, h x ∂ν :=
    fun h hh => hAF Mp h hMpM hMpnm hh
  -- Step 2: counting function
  obtain ⟨N, hN⟩ : ∃ N : Eucl Q → ℝ≥0∞,
      N = fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := ⟨_, rfl⟩
  have hθmp : AEMeasurable (fun x => ENNReal.ofReal (θ x)) (μ.restrict Mp) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hθm).mono_set hMpM
  have hNm : AEMeasurable N ν := by rw [hN]; exact (hAFp _ hθmp).1
  -- Step 3: closed-set argument and local finiteness
  have hclosed : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      ∃ C : Set (Eucl P), IsClosed C ∧ (∀ x ∈ M, (x ∈ C ↔ f x ∈ K)) ∧
        ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ < ∞ := by
    intro K hK hKV
    obtain ⟨C, hCc, hCeq⟩ := (continuousOn_iff_isClosed.mp hfc) K hK.isClosed
    refine ⟨C, hCc, ?_, ?_⟩
    · intro x hx
      constructor
      · intro hxC
        have : x ∈ C ∩ M := ⟨hxC, hx⟩
        rw [← hCeq] at this
        exact this.1
      · intro hfx
        have : x ∈ f ⁻¹' K ∩ M := ⟨hfx, hx⟩
        rw [hCeq] at this
        exact this.1
    · calc ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ
          ≤ ∫⁻ x in M, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ :=
            lintegral_mono_set hMpM
        _ = ∫⁻ x in C ∩ M, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂μ := by
            rw [lintegral_indicator hCc.measurableSet, Measure.restrict_restrict hCc.measurableSet]
        _ = ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂μ := by
            rw [← hCeq, Set.inter_comm]
        _ < ∞ := hLF K hK hKV
  have hfib_ind : ∀ (K : Set (Eucl Q)) (C : Set (Eucl P)), (∀ x ∈ M, (x ∈ C ↔ f x ∈ K)) →
      ∀ (u : Eucl P → ℝ≥0∞) (y : Eucl Q),
        ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, C.indicator u x =
          K.indicator (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, u x) y := by
    intro K C hC u y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      refine tsum_congr fun x => ?_
      have hxC : (x : Eucl P) ∈ C := (hC x (hMpM x.2.1)).2 (by rw [x.2.2]; exact hy)
      rw [Set.indicator_of_mem hxC]
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, C.indicator u x = 0 := by
        intro x
        have hxC : (x : Eucl P) ∉ C := fun h => hy (by rw [← x.2.2]; exact (hC x (hMpM x.2.1)).1 h)
        rw [Set.indicator_of_notMem hxC]
      simp only [this, tsum_zero]
  have hNK : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∫⁻ y, K.indicator N y ∂ν < ∞ := by
    intro K hK hKV
    obtain ⟨C, hCc, hCK, hCfin⟩ := hclosed K hK hKV
    have hh : AEMeasurable (C.indicator (fun x => ENNReal.ofReal (θ x))) (μ.restrict Mp) :=
      hθmp.indicator hCc.measurableSet
    have key := (hAFp _ hh).2
    calc ∫⁻ y, K.indicator N y ∂ν
        = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y},
            C.indicator (fun x => ENNReal.ofReal (θ x)) x ∂ν := by
          refine lintegral_congr fun y => ?_
          rw [hfib_ind K C hCK, hN]
      _ = ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x)) x * ‖Ξ x‖ₑ ∂μ := key.symm
      _ = ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ := by
          refine lintegral_congr fun x => ?_
          by_cases hx : x ∈ C <;> simp [hx]
      _ < ∞ := hCfin
  -- Step 4/5: fibre facts
  have hNy : ∀ y, N y = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := by
    intro y; rw [hN]
  have hfin : ∀ y, N y ≠ ∞ → Finite {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    apply hy
    rw [hNy, ← top_le_iff]
    calc (∞ : ℝ≥0∞) = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, (1 : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hθ1 x (hMpM x.2.1))
  have hempty : ∀ y, N y = 0 → IsEmpty {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    rw [hNy, ENNReal.tsum_eq_zero] at hy
    refine ⟨fun x => ?_⟩
    have h1 := hy x
    rw [ENNReal.ofReal_eq_zero] at h1
    linarith [hθ1 x (hMpM x.2.1)]
  have hNge1 : ∀ y, N y ≠ 0 → 1 ≤ N y := by
    intro y hy
    rw [hNy] at hy ⊢
    obtain ⟨x, hx⟩ : ∃ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (ENNReal.tsum_eq_zero.2 h)
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (θ x) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hθ1 x (hMpM x.2.1))
      _ ≤ ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) :=
          ENNReal.le_tsum (f := fun x : {x : Eucl P // x ∈ Mp ∧ f x = y} => ENNReal.ofReal (θ x)) x
  have hnotV : ∀ y, y ∉ V → IsEmpty {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    refine ⟨fun x => hy ?_⟩
    rw [← x.2.2]
    exact hfV (hMpM x.2.1)
  -- Step 5: the set Y
  obtain ⟨Y, hY⟩ : ∃ Y : Set (Eucl Q), Y = {y | y ∈ V ∧ N y ≠ 0 ∧ N y ≠ ∞} := ⟨_, rfl⟩
  have hY_mem : ∀ y, y ∈ Y ↔ y ∈ V ∧ N y ≠ 0 ∧ N y ≠ ∞ := by intro y; rw [hY]; rfl
  have hYV : Y ⊆ V := fun y hy => ((hY_mem y).1 hy).1
  have hYnm : NullMeasurableSet Y ν := by
    have h1 : NullMeasurableSet (N ⁻¹' {0}ᶜ) ν :=
      hNm.nullMeasurable (measurableSet_singleton 0).compl
    have h2 : NullMeasurableSet (N ⁻¹' {∞}ᶜ) ν :=
      hNm.nullMeasurable (measurableSet_singleton ∞).compl
    have : Y = V ∩ (N ⁻¹' {0}ᶜ ∩ N ⁻¹' {∞}ᶜ) := by
      ext y; rw [hY_mem]; simp
    rw [this]
    exact hV.measurableSet.nullMeasurableSet.inter (h1.inter h2)
  have hYK : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ν (Y ∩ K) < ∞ := by
    intro K hK hKV
    have hsub : Y ∩ K ⊆ {y | 1 ≤ K.indicator N y} := by
      rintro y ⟨hyY, hyK⟩
      rw [Set.mem_ofPred_eq, Set.indicator_of_mem hyK]
      exact hNge1 y ((hY_mem y).1 hyY).2.1
    have hmk := mul_meas_ge_le_lintegral₀ (hNm.indicator hK.measurableSet) 1
    rw [one_mul] at hmk
    exact lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt hmk (hNK K hK hKV))
  -- Step 6: the density
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : Eucl P → NVector (Eucl Q) n,
      ϑ = fun x => (θ x * ‖Ξ x‖⁻¹) • Ξ x := ⟨_, rfl⟩
  have hϑx : ∀ x, ϑ x = (θ x * ‖Ξ x‖⁻¹) • Ξ x := fun x => by rw [hϑ]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Eucl Q → NVector (Eucl Q) n,
      Ψ = fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := ⟨_, rfl⟩
  have hΨy : ∀ y, Ψ y = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := fun y => by rw [hΨ]
  have hnormΞ : AEStronglyMeasurable (fun x => ‖Ξ x‖) (μ.restrict M) :=
    (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΞm
  have hϑm : AEStronglyMeasurable ϑ (μ.restrict Mp) := by
    rw [hϑ]
    have h1 : AEStronglyMeasurable (fun x => θ x * ‖Ξ x‖⁻¹) (μ.restrict M) :=
      (hθm.mul hnormΞ.aemeasurable.inv).aestronglyMeasurable
    exact (h1.smul hΞm).mono_set hMpM
  have hgβ : ∀ β : Covector (Eucl Q) n,
      AEStronglyMeasurable (fun x => ϑ x β) (μ.restrict Mp) :=
    fun β => (continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hϑm
  -- Step 7: measurability of Ψ on Y
  have hΨβ : ∀ β : Covector (Eucl Q) n, AEMeasurable (fun y => Ψ y β) (ν.restrict Y) := by
    intro β
    have hp := (hAFp (fun x => ENNReal.ofReal (ϑ x β))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hgβ β).aemeasurable)).1
    have hm := (hAFp (fun x => ENNReal.ofReal (-ϑ x β))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hgβ β).aemeasurable.neg)).1
    refine ((hp.ennreal_toReal.sub hm.ennreal_toReal).mono_measure
      Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem₀ hYnm] with y hy
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hy).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    simp only [Pi.sub_apply]
    rw [hΨy, tsum_fintype, tsum_fintype, tsum_fintype,
      ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top),
      ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top), ← Finset.sum_sub_distrib,
      sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    exact max_zero_sub_eq_self _
  have := Submission.lpf_pi_covector_finiteDimensional Q n
  obtain ⟨D, b, bs, hexp⟩ : ∃ (D : ℕ) (b : Fin D → Covector (Eucl Q) n)
      (bs : Fin D → NVector (Eucl Q) n), ∀ ζ : NVector (Eucl Q) n, ζ = ∑ i, ζ (b i) • bs i := by
    let bb := Module.finBasis ℝ (Covector (Eucl Q) n)
    refine ⟨_, bb, fun i => LinearMap.toContinuousLinearMap (bb.coord i), fun ζ => ?_⟩
    ext α
    have hα : α = ∑ i, bb.repr α i • bb i := (bb.sum_repr α).symm
    calc ζ α = ζ (∑ i, bb.repr α i • bb i) := by rw [← hα]
      _ = ∑ i, bb.repr α i * ζ (bb i) := by simp only [map_sum, map_smul, smul_eq_mul]
      _ = (∑ i, ζ (bb i) • LinearMap.toContinuousLinearMap (bb.coord i)) α := by
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
  have hΨm : AEStronglyMeasurable Ψ (ν.restrict Y) := by
    have h1 : AEStronglyMeasurable (fun y => ∑ i, Ψ y (b i) • bs i) (ν.restrict Y) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (hΨβ (b i)).aestronglyMeasurable.smul_const (bs i)
    exact h1.congr (Eventually.of_forall fun y => (hexp (Ψ y)).symm)
  -- Step 8: integrability
  have hϑnorm : ∀ x ∈ Mp, ‖ϑ x‖ ≤ θ x := by
    intro x hx
    obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
    have hpos : 0 < ‖Ξ x‖ := lt_of_le_of_ne (norm_nonneg (Ξ x))
      (Ne.symm fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h))
    rw [hϑx]
    calc ‖(θ x * ‖Ξ x‖⁻¹) • Ξ x‖ ≤ ‖θ x * ‖Ξ x‖⁻¹‖ * ‖Ξ x‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ = θ x := by
          rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hθpos x hxM) (inv_pos.2 hpos)),
            inv_mul_cancel_right₀ hpos.ne']
  have hΨnorm : ∀ y ∈ Y, ENNReal.ofReal ‖Ψ y‖ ≤ N y := by
    intro y hy
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hy).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    rw [hΨy, hNy, tsum_fintype, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg (fun (x : {x : Eucl P // x ∈ Mp ∧ f x = y}) _ =>
        zero_le_one.trans (hθ1 x (hMpM x.2.1)))]
    refine ENNReal.ofReal_le_ofReal ?_
    refine ContinuousLinearMap.opNorm_le_bound _
      (Finset.sum_nonneg fun x _ => zero_le_one.trans (hθ1 x (hMpM x.2.1))) fun α => ?_
    rw [sum_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hϑnorm x x.2.1) (norm_nonneg α))
  have hint : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) ν := by
    intro K hK hKV
    refine ⟨((@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΨm).mono_set
      Set.inter_subset_left, ?_⟩
    show ∫⁻ y in Y ∩ K, ‖‖Ψ y‖‖ₑ ∂ν < ∞
    calc ∫⁻ y in Y ∩ K, ‖‖Ψ y‖‖ₑ ∂ν ≤ ∫⁻ y in Y ∩ K, K.indicator N y ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ (hYnm.inter hK.measurableSet.nullMeasurableSet)]
            with y hy
          rw [Real.enorm_eq_ofReal (norm_nonneg (Ψ y)), Set.indicator_of_mem hy.2]
          exact hΨnorm y hy.1
      _ ≤ ∫⁻ y, K.indicator N y ∂ν := setLIntegral_le_lintegral _ _
      _ < ∞ := hNK K hK hKV
  -- Step 9: chart family
  have hCH' := (ae_restrict_iff'₀ hM).1 hCH
  obtain ⟨Gd, hGd_ae, hGd⟩ := hCH'.exists_mem
  have hGdc : μ Gdᶜ = 0 := mem_ae_iff.1 hGd_ae
  have hBnull : μ (Gdᶜ ∩ M) = 0 := measure_mono_null Set.inter_subset_left hGdc
  have hE : ν (f '' (Gdᶜ ∩ M)) = 0 := hnull _ Set.inter_subset_right hBnull
  have hchart : ∀ᵐ y ∂(ν.restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ)
      (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q),
      (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧
        Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧
      Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i) := by
    have hE' : ∀ᵐ y ∂ν, y ∉ f '' (Gdᶜ ∩ M) := measure_eq_zero_iff_ae_notMem.1 hE
    filter_upwards [ae_restrict_mem₀ hYnm, ae_restrict_of_ae hE'] with y hyY hyE
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hyY).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    have hdata : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ∃ k, ∃ w ∈ O k, G k w = y ∧
        ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧
          Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧
          ∃ a : ℤ, ϑ x = (a : ℝ) • simpleNVector σ := by
      intro x
      obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 x.2.1
      have hxGd : (x : Eucl P) ∈ Gd := by
        by_contra hc
        exact hyE ⟨x, ⟨hc, hxM⟩, x.2.2⟩
      obtain ⟨k, w, hw, hGw, σ, hσ, hspan, hsign⟩ := hGd x hxGd hxM hΞx
      obtain ⟨j, hj⟩ := hθnat x hxM
      refine ⟨k, w, hw, hGw.trans x.2.2, σ, hσ, hspan, ?_⟩
      have hpos : ‖Ξ x‖ ≠ 0 := fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
      rcases hsign with h | h
      · refine ⟨j, ?_⟩
        calc ϑ x = (θ x * ‖Ξ x‖⁻¹) • Ξ x := hϑx x
          _ = (θ x * ‖Ξ x‖⁻¹) • (‖Ξ x‖ • simpleNVector σ) := by rw [← h]
          _ = (θ x * ‖Ξ x‖⁻¹ * ‖Ξ x‖) • simpleNVector σ := smul_smul _ _ _
          _ = ((j : ℤ) : ℝ) • simpleNVector σ := by
              rw [inv_mul_cancel_right₀ hpos, hj, Int.cast_natCast]
      · refine ⟨-(j : ℤ), ?_⟩
        have hα : ∀ α : Covector (Eucl Q) n, Ξ x α = -(‖Ξ x‖ * α σ) := fun α =>
          congrArg (fun z : NVector (Eucl Q) n => z α) h
        rw [hϑx]
        ext α
        show (θ x * ‖Ξ x‖⁻¹) * Ξ x α = ((-(j : ℤ) : ℤ) : ℝ) * α σ
        rw [hα α, hj]
        have hr : ‖Ξ x‖⁻¹ * ‖Ξ x‖ = 1 := inv_mul_cancel₀ hpos
        calc (j : ℝ) * ‖Ξ x‖⁻¹ * -(‖Ξ x‖ * α σ) = -((j : ℝ) * (‖Ξ x‖⁻¹ * ‖Ξ x‖) * α σ) := by
              ring
          _ = ((-(j : ℤ) : ℤ) : ℝ) * α σ := by rw [hr]; push_cast; ring
    choose k w hw hGw σ hσ hspan a ha using hdata
    let e := Fintype.equivFin {x : Eucl P // x ∈ Mp ∧ f x = y}
    refine ⟨Fintype.card {x : Eucl P // x ∈ Mp ∧ f x = y}, fun i => a (e.symm i),
      fun i => k (e.symm i), fun i => w (e.symm i), fun i => σ (e.symm i),
      fun i => ⟨hw _, hGw _, hσ _, hspan _⟩, ?_⟩
    calc Ψ y = ∑ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := by rw [hΨy, tsum_fintype]
      _ = ∑ i, ϑ (e.symm i) := (e.symm.sum_comp (fun x => ϑ x)).symm
      _ = ∑ i, (a (e.symm i) : ℝ) • simpleNVector (σ (e.symm i)) :=
          Finset.sum_congr rfl fun i _ => ha (e.symm i)
  -- Step 10: representation
  have hrep : ∀ ω : TestFormOn V n,
      S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂ν := by
    intro ω
    obtain ⟨⟨hωs, hωc⟩, hωV⟩ := ω.2
    obtain ⟨Cω, hCω⟩ := hωc.exists_bound_of_continuous hωs.continuous
    have hCω0 : 0 ≤ Cω := (norm_nonneg _).trans (hCω 0)
    obtain ⟨Cl, hCl_closed, hCl_iff, hCl_fin⟩ := hclosed _ hωc.isCompact hωV
    obtain ⟨g, hg⟩ : ∃ g : Eucl P → ℝ,
        g = fun x => ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x)) := ⟨_, rfl⟩
    have hgx : ∀ x, g x = ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x)) := fun x => by rw [hg]
    -- (a)
    have ha : S ω = ∫ x in Mp, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂μ := by
      rw [hS ω]
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hM hMpM
        (Eventually.of_forall fun x hx => ?_)
      have : Ξ x = 0 := by
        by_contra hne
        exact hx.2 ((hMp_mem x).2 ⟨hx.1, hne⟩)
      rw [this, zero_apply, mul_zero]
    -- (b)
    have hb : ∫ x in Mp, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂μ =
        ∫ x in Mp, g x * (‖Ξ x‖ₑ).toReal ∂μ := by
      refine setIntegral_congr_fun₀ hMpnm fun x hx => ?_
      obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
      have hpos : ‖Ξ x‖ ≠ 0 := fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
      rw [hgx, hϑx, toReal_enorm, smul_apply, smul_eq_mul]
      field_simp
    have hωf : AEStronglyMeasurable (fun x => (ω : DifferentialForm (Eucl Q) n) (f x))
        (μ.restrict Mp) := by
      have h0 : AEStronglyMeasurable (fun x => (ω : DifferentialForm (Eucl Q) n) (f x))
          (μ.restrict M₀) :=
        (hωs.continuous.comp_continuousOn (hfc.mono hM₀M)).aestronglyMeasurable hM₀m
      rw [hrestr] at h0
      exact h0.mono_set hMpM
    have hgm : AEStronglyMeasurable g (μ.restrict Mp) := by
      rw [hg]
      exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hϑm.prodMk hωf)
    have hgfin : ∫⁻ x in Mp, ‖g x‖ₑ * ‖Ξ x‖ₑ ∂μ < ∞ := by
      calc ∫⁻ x in Mp, ‖g x‖ₑ * ‖Ξ x‖ₑ ∂μ
          ≤ ∫⁻ x in Mp, ENNReal.ofReal Cω *
              Cl.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem₀ hMpnm] with x hx
            obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
            by_cases hxC : x ∈ Cl
            · rw [Set.indicator_of_mem hxC]
              have hgle : ‖g x‖ₑ ≤ ENNReal.ofReal Cω * ENNReal.ofReal (θ x) := by
                rw [← ENNReal.ofReal_mul hCω0, hgx, Real.enorm_eq_ofReal_abs]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [← Real.norm_eq_abs]
                calc ‖ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x))‖
                    ≤ ‖ϑ x‖ * ‖(ω : DifferentialForm (Eucl Q) n) (f x)‖ :=
                      ContinuousLinearMap.le_opNorm _ _
                  _ ≤ θ x * Cω := mul_le_mul (hϑnorm x hx) (hCω _) (norm_nonneg _)
                      (zero_le_one.trans (hθ1 x hxM))
                  _ = Cω * θ x := mul_comm _ _
              calc ‖g x‖ₑ * ‖Ξ x‖ₑ ≤ (ENNReal.ofReal Cω * ENNReal.ofReal (θ x)) * ‖Ξ x‖ₑ := by
                    gcongr
                _ = ENNReal.ofReal Cω * (ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) := mul_assoc _ _ _
            · have hfx : f x ∉ tsupport (ω : DifferentialForm (Eucl Q) n) :=
                fun h => hxC ((hCl_iff x hxM).2 h)
              have : g x = 0 := by rw [hgx, image_eq_zero_of_notMem_tsupport hfx, map_zero]
              rw [this, enorm_zero, zero_mul]
              exact zero_le
        _ = ENNReal.ofReal Cω *
              ∫⁻ x in Mp, Cl.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCl_fin
    have hJm : AEMeasurable (fun x => ‖Ξ x‖ₑ) (μ.restrict Mp) := by
      have h0 := (hnormΞ.aemeasurable.ennreal_ofReal).mono_set hMpM
      exact h0.congr (Eventually.of_forall fun x => ofReal_norm (Ξ x))
    obtain ⟨-, -, heq⟩ := Submission.lpf_pi_signed_fibre_sum (Eucl P) (Eucl Q) μ ν f Mp
      (fun x => ‖Ξ x‖ₑ) hJm hAFp g hgm hgfin
    -- (d)
    have hNfin : ∀ᵐ y ∂ν, y ∈ tsupport (ω : DifferentialForm (Eucl Q) n) → N y < ∞ := by
      have h1 := ae_lt_top' (hNm.indicator hωc.isCompact.measurableSet)
        (hNK _ hωc.isCompact hωV).ne
      filter_upwards [h1] with y hy hyK
      rwa [Set.indicator_of_mem hyK] at hy
    have hd : (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, g x) =ᵐ[ν]
        Y.indicator (fun y => Ψ y ((ω : DifferentialForm (Eucl Q) n) y)) := by
      filter_upwards [hNfin] with y hy
      by_cases hyY : y ∈ Y
      · rw [Set.indicator_of_mem hyY]
        have hyN : N y ≠ ∞ := ((hY_mem y).1 hyY).2.2
        have := hfin y hyN
        have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
        rw [tsum_fintype, hΨy, tsum_fintype, sum_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hgx, x.2.2]
      · rw [Set.indicator_of_notMem hyY]
        by_cases hyV : y ∈ V
        · by_cases hN0 : N y = 0
          · have := hempty y hN0
            exact tsum_empty
          · have hNinf : N y = ∞ := by
              by_contra h
              exact hyY ((hY_mem y).2 ⟨hyV, hN0, h⟩)
            have hyK : y ∉ tsupport (ω : DifferentialForm (Eucl Q) n) :=
              fun hyK => (hy hyK).ne hNinf
            have : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, g x = 0 := by
              intro x
              rw [hgx, x.2.2, image_eq_zero_of_notMem_tsupport hyK, map_zero]
            simp only [this, tsum_zero]
        · have := hnotV y hyV
          exact tsum_empty
    rw [ha, hb]
    refine heq.trans ?_
    rw [integral_congr_ae hd, integral_indicator₀ hYnm]
  exact ⟨Y, Ψ, hYV, hYnm, hYK, hΨm, hint, hchart, hrep⟩
```

## Key steps

1. M₊ = {Ξ ≠ 0} null-measurable; θ ≥ 1; normalised η = Ξ/‖Ξ‖ and ϑ = θη on M₊
2. Counting function N(y) = Σ_{F_y} θ is a.e. measurable; ∫_K N ≤ ∫_{M∩f⁻¹K} θ‖Ξ‖ < ∞ via (AF) and (LF)
3. N < ∞ a.e.; Y := {y ∈ V : 1 ≤ N < ∞} null-measurable with finite fibres and Hⁿ(Y ∩ K) < ∞
4. Ψ(y) = Σ_{F_y} ϑ: measurable via coordinate fibre sums N^±_β and a basis of the finite-dimensional covector space (sibling), locally integrable via ‖Ψ‖ ≤ N
5. Outside the null set f(B), every fibre point carries chart data from (CH), giving the integer chart family
6. Representation: restrict to M₊, apply lpf_pi_signed_fibre_sum to g = ϑ(ω∘f), identify fibre sums with Ψ(ω) a.e.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean (identical)`
- `python3 over dag.json: frozen lean_statement/status of the 8 uncle nodes; all lean_name fields (226 unique); grep -c 'lpf_pi_' dag.json (0 matches)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (replay: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `lean_contract.validate_lean_statement on all 11 child statements`
- `grep -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def covectorPullback|def nVectorPushforward|def simpleNVector|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' Chapter06/Forms.lean; 'abbrev TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; 'def GeometricCurrentOn.support|theorem GeometricCurrentOn.support_subset_domain' Chapter06/CurrentLocalEquality.lean`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (line 216)`
- `grep -n 'LocallyLipschitzOn.comp|protected lemma comp' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean (only LocallyLipschitz.comp exists)`
- `lake build GMT.Ch06.Submission in /tmp/lpi3_scratch (scratch copy, .lake/packages linked to the pinned package tree)`
- `lake env lean Scratch/Stmts.lean (11 statements in comparator scope, only sorry warnings)`
- `lake env lean Scratch/Names.lean (#check of ~90 cited Mathlib/SimonGMT names; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm, ENorm via SeminormedAddGroup.toContinuousENorm, MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace, Norm (Covector ..) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm)`
- `lake env lean Scratch/Inst.lean (#synth ContinuousAdd / PseudoMetrizableSpace / ContinuousENorm (NVector (Eucl 3) 2) fail; documented workarounds compile)`
- `lake env lean Scratch/Assembly.lean (parent from 19 stubs; #print axioms propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean Scratch/AllChildren.lean and Scratch/E2E.lean (all 11 children proved in dependency order + parent assembly; per-child #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpi3_scratch/Scratch/Stmts.lean`
- `/tmp/lpi3_scratch/Scratch/Names.lean`
- `/tmp/lpi3_scratch/Scratch/Inst.lean`
- `/tmp/lpi3_scratch/Scratch/Assembly.lean`
- `/tmp/lpi3_scratch/Scratch/AllChildren.lean`
- `/tmp/lpi3_scratch/Scratch/E2E.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) is byte-identical to the workspace Contract and Submission. The child scope is import GMT.Ch06.Submission plus the replayed namespace and opens. It provides the contract notions (IsRectifiableTriple, tauAction, IsIntegerMultiplicity) and SimonGMT Ch03 Rectifiable (CountablyRectifiable with mono/range/iUnion, HasWeightedApproximateTangentSpaceAt, .unique for θ x ≠ 0). It also provides Ch06 n-vectors (NVector = Covector →L[ℝ] ℝ with the operator norm, simpleNVector, nVectorPushforward_simple), test forms, currents and support_subset_domain, plus Ch02 euclideanHausdorffMeasure_image_le_of_lipschitzOn.

It does not provide:
- SimonGMT SubmanifoldCover (countablyRectifiable_image_contDiffOn_open) or Mathlib's Multilinear.FiniteDimensional; both facts are therefore separate import-free leaves.
- LocallyLipschitzOn.comp.
- Instance search on NVector for ContinuousAdd, PseudoMetrizableSpace, ContinuousENorm and NormSMulClass; the verified workarounds are recorded in the child texts.

No lpf_pi_* name is reserved in dag.json, and leaf plans forbid helper declarations, so every child script is a single theorem. All 11 frozen statements validate and elaborate in the comparator scope. All 11 children are fully proved in Lean with only propext, Classical.choice and Quot.sound, using only their declared siblings. The frozen parent type follows from them and the eight uncles by the stated assembly; its only sorryAx comes from the uncle stubs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
