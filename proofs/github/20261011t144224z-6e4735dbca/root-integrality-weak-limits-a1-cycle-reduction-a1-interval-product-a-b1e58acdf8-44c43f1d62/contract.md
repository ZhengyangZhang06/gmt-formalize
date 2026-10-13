<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1 -->

## Theorem `Submission.iwl_cr_ip_product_weighted_tangent`

Let P, m ∈ ℕ, Hᵏ := μHE[k], and use Φ, π, Φ′(s, x) := Φ(s, x), y₀ := (EuclideanSpace.equiv (Fin (P+1)) ℝ y) 0, e₀ := EuclideanSpace.single 0 1 = Φ(1, 0) and ι(v) := Φ(0, v) as in the parent (Φ(s, x) = (s, x_1, …, x_P), π(y) = (y_1, …, y_P)). Assume (MP): for every A ⊆ ℝ^P that is Hᵐ-null-measurable, countably m-rectifiable and has Hᵐ(A ∩ K) < ∞ for every compact K, H^{m+1}⌞{y : π(y) ∈ A} = Φ′_*(L¹ ⊗ Hᵐ⌞A). Let M ⊆ ℝ^P be Hᵐ-null-measurable and countably m-rectifiable with Hᵐ(M ∩ K) < ∞ for every compact K; let θ : ℝ^P → ℝ with θ ≥ 0 on M and θ Hᵐ-integrable on M ∩ K for every compact K; let x ∈ ℝ^P and let τ = (τ_1, …, τ_m) be orthonormal in ℝ^P such that span τ is a weighted approximate tangent space of (M, θ) at x in the sense of Simon Ch. 3, 1.7 (HasWeightedApproximateTangentSpaceAt m M θ x (span ℝ (range τ))); let s₀ ∈ (0, 1). Put M̃ := {y ∈ ℝ^{P+1} : π(y) ∈ M ∧ y₀ ∈ (0, 1)} and θ̃ := θ ∘ π. Then the (m+1)-plane spanned by (e₀, ιτ_1, …, ιτ_m) (Lean: Fin.cons e₀ (fun i => Φ(0, τ_i))) is a weighted approximate tangent space of (M̃, θ̃) at Φ(s₀, x): HasWeightedApproximateTangentSpaceAt (m+1) M̃ θ̃ (Φ s₀ x) (span ℝ (range (Fin.cons e₀ (fun i => Φ 0 (τ i))))).

Node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2777

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2157

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4515, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4521, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4529, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4542, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4556, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4572, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2157

## Lean problem

Declaration: `Submission.iwl_cr_ip_product_weighted_tangent`

```lean
∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (τ : Fin m → Eucl P) (s₀ : ℝ), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → Orthonormal ℝ τ → HasWeightedApproximateTangentSpaceAt m M θ x (Submodule.span ℝ (range τ)) → s₀ ∈ Ioo (0 : ℝ) 1 → HasWeightedApproximateTangentSpaceAt (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1))))
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

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof (“blow-ups of the product are products of blow-ups”; dominated convergence in the interval variable), with the product formula of Step 1 in the measure form (MP). Instead of applying (PF) to the blow-ups M_r, the blow-ups are undone by the blow-up change of variables (sibling blowup_cov = the accepted declaration fiw_tl_blowup_setIntegral), so (MP) is only applied to A = M and to the plane A = T.

Notation. E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1), Hᵏ := μHE[k], L¹ := Lebesgue measure on ℝ. Φ(s, x) := (s, x_1, …, x_P) (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))); π(y) := (y_1, …, y_P) (Lean: (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y))); y₀ := (EuclideanSpace.equiv (Fin (P+1)) ℝ y) 0; Φ′ : ℝ × E → E′, Φ′(p) := Φ(p.1, p.2); e₀ := EuclideanSpace.single 0 1 = Φ(1, 0); ι(v) := Φ(0, v); M̃ := {y ∈ E′ : π(y) ∈ M ∧ y₀ ∈ (0,1)}; θ̃ := θ ∘ π (Lean: fun y => θ (π y)); O := {y ∈ E′ : y₀ ∈ (0,1)} (open), so M̃ = O ∩ {π ∈ M}. (MP) denotes the hypothesis: for every A ⊆ E that is Hᵐ-null-measurable, countably m-rectifiable and has Hᵐ(A ∩ K) < ∞ for every compact K, H^{m+1}⌞{y : π(y) ∈ A} = Φ′_*(L¹ ⊗ Hᵐ⌞A).
Coordinate facts (all by Fin.cons/Fin.tail computations, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons, Fin.cons_zero, Fin.cons_self_tail): (F1) π(Φ(s,u)) = u, (Φ(s,u))₀ = s and Φ(y₀, π(y)) = y; (F2) Φ is linear: Φ(s,u) − Φ(s′,u′) = Φ(s − s′, u − u′), Φ(s,u) + Φ(s′,u′) = Φ(s + s′, u + u′), c·Φ(s,u) = Φ(cs, cu); in particular ι is linear and π is linear; (F3) ⟨Φ(a,u), Φ(b,w)⟩ = ab + ⟨u,w⟩ (sum over Fin (P+1) split by Fin.sum_univ_succ), hence ‖Φ(s,u)‖² = s² + ‖u‖², |s| ≤ ‖Φ(s,u)‖ and ‖u‖ ≤ ‖Φ(s,u)‖; (F4) Φ′ is a homeomorphism ℝ × E → E′ with continuous inverse y ↦ (y₀, π(y)) (Continuous.finCons, continuous_pi), hence a measurable embedding (Homeomorph.measurableEmbedding); in particular Φ′ and π are Borel measurable.
Further notation. y* := Φ(s₀, x); T := span τ; τ̃ := (e₀, ιτ_1, …, ιτ_m); Q := span τ̃; ν := Hᵐ⌞M; ρ := (L¹⌞(0,1)) ⊗ ν. For r > 0, η_r := blowUpMap y* r (η_r(z) = r⁻¹(z − y*)) on E′ and η′_r := blowUpMap x r on E. The sibling blowup_cov states: for every n, every centre c, every r > 0, every set S and every function g, ∫_{blowUpMap c r '' S} g dHⁿ = (rⁿ)⁻¹ ∫_S g(blowUpMap c r z) dHⁿ(z) (no measurability or integrability assumption).

1. (τ̃ is orthonormal; dim Q = m + 1; dim T = m.) By (F3): ‖e₀‖² = 1 + ‖0‖² = 1; ‖ιτ_i‖ = ‖τ_i‖ = 1; ⟨e₀, ιτ_i⟩ = 1·0 + ⟨0, τ_i⟩ = 0; ⟨ιτ_i, ιτ_j⟩ = 0·0 + ⟨τ_i, τ_j⟩ = 0 for i ≠ j. Hence τ̃ is orthonormal, so linearly independent (Orthonormal.linearIndependent), and finrank Q = card (Fin (m+1)) = m + 1 (finrank_span_eq_card). Likewise finrank T = m.
2. (Q = {z : π(z) ∈ T} as sets.) π is linear, so Z := {z : π(z) ∈ T} is a linear subspace (the comap of T). It contains e₀ (π(e₀) = 0 ∈ T) and every ιτ_i (π(ιτ_i) = τ_i ∈ T), so Q ⊆ Z (Submodule.span_le). Conversely, if π(z) ∈ T, write π(z) = Σ_i c_i τ_i (Submodule.mem_span_range_iff_exists_fun); by (F1), (F2), z = Φ(z₀, π(z)) = z₀·e₀ + Σ_i c_i·ιτ_i ∈ Q.
3. (Measure identities.) (a) M satisfies the hypotheses of (MP) (null-measurable, countably m-rectifiable, Hᵐ(M ∩ K) < ∞), and ν is σ-finite: it is finite on compacts (ν(K) = Hᵐ(K ∩ M) < ∞ for compact, hence Borel, K; Measure.restrict_apply), so SigmaFinite.of_isFiniteMeasureOnCompacts applies. O is open, hence Borel, Φ′⁻¹(O) = (0,1) × E by (F1), and M̃ = O ∩ {π ∈ M}. Hence H^{m+1}⌞M̃ = (H^{m+1}⌞{π ∈ M})⌞O (Measure.restrict_restrict) = (Φ′_*(L¹ ⊗ ν))⌞O (MP) = Φ′_*((L¹ ⊗ ν)⌞((0,1) × E)) (Measure.restrict_map, Φ′ measurable) = Φ′_*((L¹⌞(0,1)) ⊗ ν) = Φ′_*ρ (Measure.prod_restrict, Measure.restrict_univ). (b) The plane T satisfies the hypotheses of (MP): T is closed (finite-dimensional subspace, Submodule.closed_of_finiteDimensional), hence Borel and null-measurable; T is the range of Λ : Eucl m → E, Λ(u) := Σ_i u_i τ_i (u_i the coordinates of u), which is a linear isometry because τ is orthonormal (‖Λu‖² = Σ_i u_i² = ‖u‖²), so LipschitzWith 1 Λ and T is countably m-rectifiable (countablyRectifiable_range; range Λ = span τ by Submodule.mem_span_range_iff_exists_fun); and since finrank T = m, Hᵐ⌞T is a regular, in particular finite-on-compacts, measure (regular_euclideanHausdorffMeasure_restrict_submodule; alternatively Hᵐ⌞T = Λ_*(Hᵐ on Eucl m) = Λ_*(volume) by Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume, and Λ⁻¹(K) is compact), so Hᵐ(T ∩ K) = (Hᵐ⌞T)(K) < ∞ for compact K. Therefore H^{m+1}⌞{π ∈ T} = Φ′_*(L¹ ⊗ Hᵐ⌞T), and Hᵐ⌞T is σ-finite.
4. (Measurability of θ.) For each n ∈ ℕ, θ is Hᵐ-integrable, hence a.e. strongly measurable, on M ∩ B̄(0, n); since M = ⋃_n (M ∩ B̄(0, n)), θ is a.e. strongly measurable for ν (aestronglyMeasurable_iUnion_iff). Consequently (s, u) ↦ θ(u) is a.e. strongly measurable for ρ (AEStronglyMeasurable.comp_snd), and products of θ with continuous functions are a.e. strongly measurable for ν and ρ. Also, ν-a.e. u lies in M (ae_restrict_mem₀, M null-measurable), so θ(u) ≥ 0 for ν-a.e. u.
5. (Fix f.) Let f ∈ C_c(E′). Choose R ≥ 0 with tsupport f ⊆ B̄(0, R) and C_f ≥ 0 with |f(z)| ≤ C_f for all z (continuous with compact support). By (F3): (*) if f(Φ(σ, w)) ≠ 0 then |σ| ≤ R and ‖w‖ ≤ R.
6. (Notation.) For σ ∈ ℝ let f_σ(w) := f(Φ(σ, w)); f_σ is continuous and by (*) its support lies in B̄(0, R), so f_σ ∈ C_c(E). For r > 0 put A(r) := ∫_{η_r(M̃)} f(z) θ̃(y* + r z) dH^{m+1}(z) (the integral in Simon 1.7 for (M̃, θ̃) at y*) and a_r(σ) := ∫_{η′_r(M)} f_σ(w) θ(x + r w) dHᵐ(w) (the integral in Simon 1.7 for (M, θ) at x with test function f_σ).
7. (Undoing the blow-ups.) Let r > 0. blowup_cov in E′ with n = m + 1, c = y*, S = M̃ and g(z) = f(z)θ̃(y* + r z), together with y* + r·r⁻¹(w − y*) = w, gives A(r) = (r^{m+1})⁻¹ ∫_{M̃} f(η_r(w)) θ(π(w)) dH^{m+1}(w). blowup_cov in E with n = m, c = x, S = M and g(w) = f_σ(w)θ(x + r w), together with x + r·η′_r(u) = u, gives a_r(σ) = (r^m)⁻¹ h_r(σ), where h_r(σ) := ∫_M f(Φ(σ, η′_r(u))) θ(u) dHᵐ(u).
8. (Blow-ups of products are products of blow-ups.) By (F2), η_r(Φ(s, u)) = r⁻¹(Φ(s, u) − Φ(s₀, x)) = Φ(r⁻¹(s − s₀), η′_r(u)).
9. (Fubini.) Let G_r(s, u) := f(Φ(r⁻¹(s − s₀), η′_r(u))) θ(u). By Step 3(a), MeasurableEmbedding.integral_map (F4) (valid for every integrand), Step 8 and (F1): ∫_{M̃} f(η_r(w)) θ(π(w)) dH^{m+1}(w) = ∫ G_r dρ. G_r is ρ-integrable: it is a.e. strongly measurable (Step 4); by (*), G_r(s, u) ≠ 0 forces ‖η′_r(u)‖ ≤ R, i.e. u ∈ B̄(x, rR), so |G_r(s, u)| ≤ C_f |θ(u)| 1_{B̄(x, rR)}(u); and (s, u) ↦ |θ(u)| 1_{B̄(x, rR)}(u) is ρ-integrable because θ is integrable on M ∩ B̄(x, rR) (compact) and L¹⌞(0,1) is finite (Integrable.comp_snd). By Fubini (integral_prod), ∫ G_r dρ = ∫_{(0,1)} H_r(s) ds with H_r(s) := ∫_M G_r(s, u) dHᵐ(u).
10. (Change of variables in the interval variable.) ∫_{(0,1)} H_r(s) ds = ∫_0^1 H_r(s) ds (intervalIntegral.integral_of_le gives the integral over (0,1], and integral_Ioc_eq_integral_Ioo since {1} is L¹-null). Put a_r := −s₀/r and b_r := (1 − s₀)/r, so a_r < 0 < b_r, r·a_r + s₀ = 0 and r·b_r + s₀ = 1. intervalIntegral.integral_comp_mul_add (c = r ≠ 0, d = s₀) gives ∫_{a_r}^{b_r} H_r(rσ + s₀) dσ = r⁻¹ ∫_0^1 H_r(s) ds. Since r⁻¹((rσ + s₀) − s₀) = σ, H_r(rσ + s₀) = h_r(σ) = r^m a_r(σ) (Step 7). Combining Steps 7, 9 and 10: A(r) = (r^{m+1})⁻¹ · r · r^m ∫_{a_r}^{b_r} a_r(σ) dσ = ∫_ℝ 1_{(a_r, b_r]}(σ) a_r(σ) dσ for every r > 0 (intervalIntegral.integral_of_le, integral_indicator).
11. (Pointwise limit.) Fix σ ∈ ℝ. The tangent hypothesis for (M, θ) at x, applied to f_σ ∈ C_c(E), gives a_r(σ) → θ(x) ∫_T f_σ dHᵐ as r → 0⁺. Since 0 < s₀ < 1, a_r → −∞ and b_r → +∞ as r → 0⁺, so σ ∈ (a_r, b_r] for all sufficiently small r > 0. Hence 1_{(a_r, b_r]}(σ) a_r(σ) → θ(x) ∫_T f(Φ(σ, w)) dHᵐ(w) as r → 0⁺, for every σ.
12. (Uniform domination.) Let g₀(w) := max(0, min(1, R + 1 − ‖w‖)). Then g₀ ∈ C_c(E), 0 ≤ g₀ ≤ 1, g₀ = 1 on B̄(0, R) and g₀ = 0 off B̄(0, R + 1). Put b(r) := ∫_{η′_r(M)} g₀(w) θ(x + r w) dHᵐ(w); by blowup_cov as in Step 7, b(r) = (r^m)⁻¹ ∫_M g₀(η′_r(u)) θ(u) dHᵐ(u). The tangent hypothesis applied to g₀ gives b(r) → θ(x) ∫_T g₀ dHᵐ as r → 0⁺, so there is r₀ > 0 with b(r) ≤ B₀ := θ(x) ∫_T g₀ dHᵐ + 1 for 0 < r < r₀. For ν-a.e. u (namely u ∈ M) and every σ, |f(Φ(σ, η′_r(u))) θ(u)| ≤ C_f g₀(η′_r(u)) θ(u): θ(u) ≥ 0, and if f(Φ(σ, η′_r(u))) ≠ 0 then ‖η′_r(u)‖ ≤ R by (*), so g₀(η′_r(u)) = 1. The function u ↦ C_f g₀(η′_r(u)) θ(u) is ν-integrable (a.e. strongly measurable, bounded by C_f |θ(u)| 1_{B̄(x, r(R+1))}(u)). Hence |h_r(σ)| ≤ C_f ∫_M g₀(η′_r(u)) θ(u) dHᵐ(u) (norm_integral_le_of_norm_le), i.e. |a_r(σ)| ≤ C_f b(r) ≤ K₀ := C_f B₀ for all σ and all 0 < r < r₀. Moreover, if |σ| > R then f(Φ(σ, ·)) ≡ 0 by (*), so a_r(σ) = 0. Therefore |1_{(a_r, b_r]}(σ) a_r(σ)| ≤ K₀ 1_{[−R, R]}(σ) for every σ and every 0 < r < r₀, and K₀ 1_{[−R, R]} is L¹-integrable.
13. (Measurability in σ.) For r > 0, σ ↦ h_r(σ) is continuous (continuous_of_dominated): for each σ, u ↦ f(Φ(σ, η′_r(u))) θ(u) is a.e. strongly measurable for ν; it is bounded by C_f |θ(u)| 1_{B̄(x, rR)}(u), a ν-integrable function independent of σ (by (*)); and σ ↦ f(Φ(σ, η′_r(u))) θ(u) is continuous for every u. Hence σ ↦ 1_{(a_r, b_r]}(σ) a_r(σ) = 1_{(a_r, b_r]}(σ) (r^m)⁻¹ h_r(σ) is a.e. strongly measurable.
14. (Dominated convergence.) The filter 𝓝[>] 0 is countably generated. By Steps 10–13 and tendsto_integral_filter_of_dominated_convergence, A(r) → ∫_ℝ θ(x) ∫_T f(Φ(σ, w)) dHᵐ(w) dσ = θ(x) ∫_ℝ ∫_T f(Φ(σ, w)) dHᵐ(w) dσ as r → 0⁺ (integral_mul_left; the identity of Step 10 holds for all r > 0, i.e. eventually in 𝓝[>] 0, so Tendsto.congr' applies).
15. (Identification of the limit.) By Step 3(b) and MeasurableEmbedding.integral_map, ∫_{π⁻¹(T)} f dH^{m+1} = ∫ f∘Φ′ d(L¹ ⊗ Hᵐ⌞T). The function f∘Φ′ is continuous, and by (*) it is bounded by C_f 1_{[−R, R]}(σ) 1_{B̄(0, R)}(w), which is L¹ ⊗ Hᵐ⌞T-integrable because Hᵐ(T ∩ B̄(0, R)) < ∞ (Step 3(b); Integrable.mul_prod). By Fubini (integral_prod), ∫ f∘Φ′ d(L¹ ⊗ Hᵐ⌞T) = ∫_ℝ ∫_T f(Φ(σ, w)) dHᵐ(w) dσ. By Step 2, (Q : Set E′) = π⁻¹(T). Hence the limit in Step 14 equals θ(x) ∫_Q f dH^{m+1} = θ̃(y*) ∫_Q f dH^{m+1}, since θ̃(y*) = θ(π(Φ(s₀, x))) = θ(x) by (F1).
16. (Conclusion.) finrank Q = m + 1 (Step 1), and for every f ∈ C_c(E′), ∫_{blowUpMap y* r '' M̃} f(z) θ̃(y* + r·z) dH^{m+1}(z) → θ̃(y*) ∫_Q f dH^{m+1} as r → 0⁺ (Steps 5–15). This is HasWeightedApproximateTangentSpaceAt (m+1) M̃ θ̃ (Φ s₀ x) Q. ∎

## Key steps

1. τ̃ = (e₀, ιτ) is orthonormal, so finrank span τ̃ = m + 1, and span τ̃ = π⁻¹(span τ) as sets.
2. (MP) for M and the restriction to O give H^{m+1}⌞M̃ = Φ′_*((L¹⌞(0,1)) ⊗ Hᵐ⌞M); (MP) also applies to the plane T = span τ.
3. blowup_cov undoes both blow-ups: A(r) = (r^{m+1})⁻¹∫_{M̃} f(η_r w)θ(πw) and a_r(σ) = (r^m)⁻¹∫_M f(Φ(σ, η′_r u))θ(u).
4. η_r(Φ(s,u)) = Φ(r⁻¹(s − s₀), η′_r u); Fubini and the substitution s = s₀ + rσ give A(r) = ∫ 1_{(−s₀/r, (1−s₀)/r]}(σ) a_r(σ) dσ.
5. Pointwise a_r(σ) → θ(x)∫_T f(Φ(σ,·)) by the tangent hypothesis, and the indicator tends to 1 since 0 < s₀ < 1.
6. Domination |a_r(σ)| ≤ C_f b(r) ≤ K₀ for small r via a cut-off g₀ and the tangent hypothesis for g₀; a_r(σ) = 0 for |σ| > R; continuity in σ gives measurability.
7. Dominated convergence gives A(r) → θ(x)∫_ℝ∫_T f(Φ(σ,w)) = θ̃(Φ(s₀,x))∫_Q f by (MP) for T and Fubini.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3 -I: dag.json lean_name/status of all root.integrality_weak_limits-a1* nodes and of all accepted nodes; lean_statement of iwl_cr_hausdorff_product_formula, iwl_cr_interval_product_im, iwl_cycle_reduction, br_loc_tauAction_current, ltg_tau_integrable, fiw_tl_blowup_setIntegral, fiw_tl_growth_bound, br_weightedTangent_congr, iwl_weighted_tangent_locality, fiw_im_mass_formula, lpf_pic_current_of_dominated_density, lpf_wtc_blowup_setIntegral_image, polyhedral_approx_rt_tau_integrableOn, isoperimetric_abs_covector_apply_le, lpf_simple_nvector_algebra`
- `grep -rl iwl_cr_ip .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca (no match); grep -rho 'iwl_cr_[a-z_]*' dag.json`
- `python3 -I: nodes/{root-boundary-rectifiability-a1-localization-a1-tau-current-a1, root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1, root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1}/accepted-candidate.json: contract lean_statement == dag.json lean_statement, audit.comparator_passed`
- `rg -n 'def curryLeft|curryLeftLI|theorem curryLeft_apply_apply|def compContinuousLinearMapCLM' mathlib/Mathlib/Analysis/Normed/Module/Alternating/ mathlib/Mathlib/Topology/Algebra/Module/Alternating/`
- `rg -n 'μHE|euclideanHausdorffMeasure_eq_volume|Isometry.euclideanHausdorffMeasure_image|Isometry.map_euclideanHausdorffMeasure|euclideanHausdorffMeasure_homothety_image|euclideanHausdorffMeasure_smul' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n in mathlib/Mathlib (snapshot) for MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff, MeasurableEmbedding.aestronglyMeasurable_map_iff, restrict_map, prod_restrict, restrict_restrict, prod_apply, integral_prod, Integrable.comp_snd, Integrable.mul_prod, AEStronglyMeasurable.comp_snd, integral_comp_mul_add, integral_Ioc_eq_integral_Ioo, integral_of_le, tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, norm_integral_le_of_norm_le, finrank_span_eq_card, restrict_apply₀', ae_restrict_mem₀, lintegral_indicator_one, setIntegral_congr_fun, SigmaFinite.of_isFiniteMeasureOnCompacts, Continuous.finCons, Homeomorph.measurableEmbedding, aestronglyMeasurable_iUnion_iff, NullMeasurableSet.congr, IntegrableOn.mono_set, IntegrableOn.of_ae_sdiff_eq_zero, Integrable.bdd_mul, norm_iteratedFDeriv_zero`
- `grep -n '^theorem|^def|^structure|^abbrev' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean and simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,FormsDuality,Product}.lean`
- `python3 -I /tmp/ipdec/scripts/gen.py and /tmp/ipdec/scripts/build.py (lean_contract.validate_lean_statement on the 7 child types, the parent type and the sibling type; comparator challenge layout of gmt-compare.py child_modules)`
- `lake env lean /tmp/ipdec/Check.lean (7 comparator-layout challenge targets; parent assembly from child and sibling stubs; #print axioms)`
- `lake env lean /tmp/ipdec/Appendix2.lean (complete proofs of iwl_cr_ip_restrict_preimage_eq_map and iwl_cr_ip_slice_formula; contraction snippet; #print axioms)`
- `lake env lean /tmp/ipdec/Sanity3.lean (construction of the contraction map; product_tangent conclusion feeds product_triple orients)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1-tau-current-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ipdec/scripts/gen.py`
- `/tmp/ipdec/scripts/build.py`
- `/tmp/ipdec/Check.lean`
- `/tmp/ipdec/Appendix2.lean`
- `/tmp/ipdec/Sanity3.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

DAG and naming:
- The DAG contains no product current and no Hausdorff product formula except the sibling iwl_cr_hausdorff_product_formula (decomposing). It is used only by the parent, through hMP.
- Reusable accepted declarations, each with identical frozen types and comparator_passed: br_loc_tauAction_current (τ is a current), ltg_tau_integrable, and fiw_tl_blowup_setIntegral. lpf_wtc_blowup_setIntegral_image is an alpha-equivalent duplicate; fiw_tl_growth_bound and br_weightedTangent_congr are not needed.
- The names iwl_cr_ip_* are unreserved: no match in dag.json, in any decomposition file, or in the run directory.

SimonGMT:
- Chapter06/Product.lean has only point products (pointProduct, pointSliceTest), no interval product. No match for a Hausdorff product formula there or in Mathlib, where only hausdorffMeasure_pi_real exists.
- Chapter03/Rectifiable.lean supplies blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_of_measure_zero, CountablyRectifiable.mono, countablyRectifiable_range and regular_euclideanHausdorffMeasure_restrict_submodule.

Mathlib supplies every tool cited in the child proofs:
- ContinuousAlternatingMap.curryLeft, curryLeftLI and curryLeft_apply_apply (Analysis/Normed/Module/Alternating/Curry.lean), and compContinuousLinearMapCLM;
- μHE lemmas: Isometry.map_euclideanHausdorffMeasure and EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- MeasurableEmbedding.integral_map, MeasurableEmbedding.integrable_map_iff and MeasurableEmbedding.aestronglyMeasurable_map_iff, Homeomorph.measurableEmbedding;
- Measure.restrict_map, Measure.prod_restrict, Measure.restrict_restrict, Measure.prod_apply, Measure.restrict_apply₀', ae_restrict_mem₀, SigmaFinite.of_isFiniteMeasureOnCompacts;
- integral_prod, Integrable.comp_snd, Integrable.mul_prod, AEStronglyMeasurable.comp_snd, aestronglyMeasurable_iUnion_iff;
- intervalIntegral.integral_comp_mul_add, intervalIntegral.integral_of_le, integral_Ioc_eq_integral_Ioo;
- tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, norm_integral_le_of_norm_le;
- finrank_span_eq_card, NullMeasurableSet.congr, IntegrableOn.mono_set, Continuous.finCons.

Lean checks:
- Comparator-layout elaboration of all 7 child types.
- The parent assembly.
- Complete proofs of measure_identity and slice_formula (axioms: propext, Classical.choice, Quot.sound).
- The ℒ construction and the product_tangent→product_triple interface.

Public citation for the product formula: Federer, Geometric Measure Theory (1969) 3.2.23. The product current and its integer multiplicity: Simon, Introduction to GMT, Ch. 6, 3.2(2).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
