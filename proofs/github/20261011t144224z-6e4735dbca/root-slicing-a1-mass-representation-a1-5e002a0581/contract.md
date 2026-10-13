<!-- theorem-id: gmt-ch06/root.slicing-a1.mass_representation-a1 -->

## Theorem `Submission.slicing_mass_representation`

For all P, k ∈ ℕ, every open U ⊆ ℝ^P and every X ∈ D_k(U) with M_W(X) < ∞ for every open W whose closure is a compact subset of U, there are a Borel measure μ on ℝ^P and v : ℝ^P → Λ_k(ℝ^P) (k-vectors, i.e. continuous linear functionals on k-covectors) such that: (a) IsMeasureRepresentation X μ v, i.e. for every test form ω ∈ D^k(U) the function x ↦ v(x)(ω(x)) is μ-integrable and X(ω) = ∫ v(x)(ω(x)) dμ(x); (b) μ(ℝ^P ∖ U) = 0; (c) μ(K) < ∞ for every compact K ⊆ U; (d) |v(x)(α)| ≤ |α| for every x ∈ ℝ^P and every k-covector α, where |α| is the Euclidean coefficient norm (covectorEuclideanNorm); (e) for every Borel A ⊆ ℝ^P there is S ∈ D_k(U) with S(ω) = ∫_A v(x)(ω(x)) dμ(x) for all ω ∈ D^k(U); (f) for every Borel A, every S ∈ D_k(U) with S(ω) = ∫_A v(x)(ω(x)) dμ(x) for all ω, and every open W ⊆ U, M_W(S) = μ(W ∩ A) in [0,∞].

Node: `root.slicing-a1.mass_representation-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/322

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1322, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1323, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1324, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1325, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1326, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1327, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1328, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1329, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1331

## Lean problem

Declaration: `Submission.slicing_mass_representation`

```lean
∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ X : GeometricCurrentOn U k, (∀ W, CompactlyContainedOpen W U → X.massOn W < ∞) → ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), IsMeasureRepresentation X μ v ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) ∧ (∀ A : Set (Eucl P), MeasurableSet A → ∃ S : GeometricCurrentOn U k, ∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) ∧ ∀ A : Set (Eucl P), MeasurableSet A → ∀ S : GeometricCurrentOn U k, (∀ ω : TestFormOn U k, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) k) x) ∂μ) → ∀ W : Set (Eucl P), IsOpen W → W ⊆ U → S.massOn W = μ (W ∩ A)
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

- Parent DAG node: `root.slicing-a1`
- Child DAG node: `root.slicing-a1.mass_representation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (as in the parent proof). D^k(U) is the space of test k-forms on U (smooth, compact support, tsupport ⊆ U; `TestFormOn U k`), D_k(U) the currents (`GeometricCurrentOn U k`: linear, and X(ω_j) → 0 whenever ω_j → 0 in D^k(U), i.e. all tsupports lie in one compact K ⊆ U and every iterated derivative of ω_j tends to 0 uniformly on K). I(k,P) is the set of strictly increasing β : {1,…,k} → {1,…,P}; e_β := (e_{β_1},…,e_{β_k}); dx^β is the coordinate k-covector, dx^β(e_γ) = δ_{βγ} for β, γ ∈ I(k,P). Fact A: every k-covector α equals Σ_β α(e_β) dx^β, and |α|² = Σ_β α(e_β)², where |α| := covectorEuclideanNorm α. A k-vector is a continuous linear functional w on k-covectors (`NVector`); put w^β := w(dx^β), so w(α) = Σ_β α(e_β) w^β and |w(α)| ≤ |α|·|w| with |w| := (Σ_β (w^β)²)^{1/2} (Cauchy–Schwarz). For a form ω, ‖ω‖ := sup_x |ω(x)|. M_W(X) = X.massOn W is the supremum of X(ω) over ω ∈ D^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. ρ_ε is a standard mollifier (smooth, ≥ 0, supported in the closed ε-ball, ∫ρ_ε = 1); for a continuous compactly supported form φ, ρ_ε*φ (componentwise convolution) is smooth, supported in the closed ε-neighbourhood of tsupport φ, satisfies |ρ_ε*φ(x)| ≤ ‖φ‖ (|·| is a norm, hence convex) and ρ_ε*φ → φ uniformly as ε ↓ 0. All measures are Borel measures on ℝ^P = Eucl P.

Source: Simon Ch. 6, 2.7–2.9 (pp. 136–137), with Ch. 1, Theorem 4.14 (Riesz) and Theorem 1.17 (Lusin). This is the parent proof's preliminaries R0, R1, R1′ and R3, specialized to the statement. Let P, k, U open and X ∈ D_k(U) with M_W(X) < ∞ for every open W with compact closure ⊆ U.

1. (Mass estimate, R0.) If ω ∈ D^k(U) and tsupport ω ⊆ W, then |X(ω)| ≤ M_W(X)‖ω‖ (in [0,∞]). Indeed, if ‖ω‖ = 0 then ω = 0 and X(ω) = 0; otherwise ±ω/‖ω‖ are admissible for M_W(X), so ±X(ω)/‖ω‖ ≤ M_W(X).

2. (Extension to continuous forms.) Let H := ℝ^{I(k,P)} with the Euclidean inner product ⟨·,·⟩_H and J : α ↦ (α(e_β))_β, a linear isometry of (k-covectors, |·|) onto H (Fact A). Let C_c(U;H) be the continuous maps U → H with compact support in U; identify φ ∈ C_c(U;H) with the continuous k-form on ℝ^P equal to J⁻¹φ on U and 0 off U (continuous because its support is a compact subset of the open set U). For φ ∈ C_c(U;H) with K := tsupport φ choose r > 0 such that the closed 2r-neighbourhood of K lies in U, and let W_K := {x : dist(x,K) < 2r}; W_K is open with compact closure ⊆ U, so M_{W_K}(X) < ∞. For 0 < ε < r, φ_ε := ρ_ε*φ ∈ D^k(U), tsupport φ_ε ⊆ W_K and φ_ε → φ uniformly. By step 1, |X(φ_ε) − X(φ_δ)| ≤ M_{W_K}(X)‖φ_ε − φ_δ‖ → 0, so X̄(φ) := lim_{ε↓0} X(φ_ε) exists. Two families of test forms supported in a common open set with compact closure in U and converging uniformly to φ have X-values whose difference tends to 0 (step 1 again), so X̄(φ) does not depend on r or on the mollifier. X̄ is linear (ρ_ε*(aφ+bψ) = aρ_ε*φ + bρ_ε*ψ), X̄(ω) = X(ω) for ω ∈ D^k(U) (ρ_ε*ω → ω uniformly with supports in a fixed W_K), and |X̄(φ)| ≤ M_{W_K}(X)‖φ‖ whenever tsupport φ ⊆ K (because ‖φ_ε‖ ≤ ‖φ‖). Hence for every compact K ⊆ U, sup{X̄(φ) : φ ∈ C_c(U;H), |φ| ≤ 1, tsupport φ ⊆ K} < ∞.

3. (Riesz representation on U, R1.) U with the subspace topology is a locally compact Hausdorff space and H is a finite-dimensional real Hilbert space. By step 2, X̄ satisfies the hypothesis of the Riesz Representation Theorem (Simon Ch. 1, Theorem 4.14; in the pinned library `Poincare.SimonGMT.Chapter01.simon_theorem_4_14`, with hypothesis `IsLocallyBoundedCcFunctional`). Hence there are a Radon measure μ_U on U (Borel regular, finite on compact subsets of U) and a μ_U-measurable ν : U → H with |ν| = 1 μ_U-a.e. and X̄(φ) = ∫_U ⟨φ(x), ν(x)⟩_H dμ_U(x) for all φ ∈ C_c(U;H). Since U is σ-compact and μ_U is finite on compact subsets of U, μ_U is σ-finite; being Borel regular, every μ_U-measurable set differs from a Borel set by a μ_U-null set, so ν agrees μ_U-a.e. with a Borel map ν₀. Put ν₁(x) := ν₀(x) if |ν₀(x)| = 1 and ν₁(x) := 0 otherwise. Then ν₁ is Borel, |ν₁| ≤ 1 everywhere, ν₁ = ν and |ν₁| = 1 μ_U-a.e. Below μ_U denotes the restriction of the Radon measure to the Borel subsets of U.

4. (Extension by zero to ℝ^P; conclusions (a)–(d).) Define μ(B) := μ_U(B ∩ U) for Borel B ⊆ ℝ^P (the push-forward of μ_U under the inclusion U ↪ ℝ^P, which is Borel since U is open). For x ∈ U let v(x) be the k-vector α ↦ ⟨Jα, ν₁(x)⟩_H, and let v(x) := 0 for x ∉ U (a linear functional on a finite-dimensional space, hence continuous). Then:
 (b) μ(ℝ^P ∖ U) = μ_U(∅) = 0.
 (c) If K ⊆ U is compact, K is a compact subset of U and μ(K) = μ_U(K) < ∞.
 (d) |v(x)(α)| ≤ |Jα|·|ν₁(x)| ≤ |α| (Cauchy–Schwarz; 0 off U). Moreover v(x)^β = ν₁^β(x), so |v(x)| = 1 for μ-a.e. x.
 (a) Let ω ∈ D^k(U) and K := tsupport ω (compact, ⊆ U). The function x ↦ v(x)(ω(x)) = 1_U(x)⟨Jω(x), ν₁(x)⟩_H is Borel, vanishes off K and is bounded by ‖ω‖, and μ(K) < ∞, so it is μ-integrable; and ∫ v(ω) dμ = ∫_U ⟨Jω, ν₁⟩_H dμ_U = ∫_U ⟨Jω, ν⟩_H dμ_U = X̄(ω|_U) = X(ω). Hence IsMeasureRepresentation X μ v.
 (R1′: no finiteness of μ on compact subsets of ℝ^P meeting ∂U is claimed or used; e.g. for P = 1, U = (0,1), X(a dx) := ∫_0^1 a(x)x⁻¹dx one has M_W(X) < ∞ for W ⊂⊂ U but μ([0,1]) = ∞.)

5. (Restrictions are currents, conclusion (e), Simon 2.9.) Let A ⊆ ℝ^P be Borel and S(ω) := ∫_A v(x)(ω(x)) dμ(x) for ω ∈ D^k(U); by (a) the integrand is integrable, so S is a well-defined linear functional. If ω_j → 0 in D^k(U), there is a compact K ⊆ U containing every tsupport ω_j with ω_j → 0 uniformly on K (zeroth iterated derivative); by (d), |S(ω_j)| ≤ ∫_K |ω_j(x)| dμ ≤ μ(K)·sup_K |ω_j| → 0, since |·| is a norm on the finite-dimensional space of k-covectors (hence bounded by a constant times the operator norm) and μ(K) < ∞ by (c). Thus S ∈ D_k(U) and S(ω) = ∫_A v(ω) dμ for every ω.

6. (Mass of restrictions, conclusion (f), R3.) Let A be Borel, S ∈ D_k(U) with S(ω) = ∫_A v(ω) dμ for all ω, and W ⊆ U open.
 (≤) If ω is admissible for M_W(S) (tsupport ω ⊆ W, |ω(x)| ≤ 1), then by (d) S(ω) ≤ ∫_A |v(x)(ω(x))| dμ ≤ μ(A ∩ tsupport ω) ≤ μ(W ∩ A). Taking the supremum, M_W(S) ≤ μ(W ∩ A).
 (≥) Let 0 ≤ c < μ(W ∩ A) and η > 0. (i) Choose compacts K_j with K_j ⊆ int K_{j+1} and ⋃_j K_j = U. Each μ⌞K_j is a finite Borel measure on the Polish space ℝ^P, hence inner regular by compact sets, and μ(W ∩ A ∩ K_j) ↑ μ(W ∩ A); so there is a compact C ⊆ W ∩ A with c < μ(C) < ∞. (ii) N := {x : |v(x)| ≠ 1} is a μ-null Borel set. By Lusin's theorem (Simon Ch. 1, 1.17, applied to the finite Borel measure μ⌞C and the Borel functions v^β) and inner regularity there is a compact C′ ⊆ C ∖ N with μ(C ∖ C′) < η such that every v^β is continuous on C′. (iii) Y(x) := Σ_β v(x)^β dx^β (x ∈ C′) is a continuous covector field on C′ with |Y(x)| = 1 and v(x)(Y(x)) = Σ_β (v(x)^β)² = 1. By Tietze's theorem (applied to the coefficients) Y extends to a continuous Ỹ on ℝ^P; replacing Ỹ by π∘Ỹ with π(y) := y/max(1,|y|) (continuous, |π(y)| ≤ 1, π(y) = y for |y| ≤ 1) we may assume |Ỹ| ≤ 1, still Ỹ = Y on C′. (iv) Choose r₀ > 0 with the closed 2r₀-neighbourhood of C′ inside W. The open sets O_j := {dist(·,C′) < r₀/j} decrease to the closed set C′ and μ(O_1) ≤ μ({dist(·,C′) ≤ r₀}) < ∞ (compact ⊆ U), so there is an open O ⊇ C′ with closure O ⊆ {dist(·,C′) ≤ r₀} and μ(O ∖ C′) < η. Let ψ be continuous with 0 ≤ ψ ≤ 1, ψ = 1 on C′, tsupport ψ ⊆ O (Urysohn), and φ := ψỸ. Then φ is a continuous form with compact support in W, |φ| ≤ 1, and, since C′ ⊆ C ⊆ A, v(φ) = 1 on C′, |v(φ)| ≤ 1 on O ∖ C′ (by (d)) and φ = 0 off O:
 ∫_A v(φ) dμ ≥ μ(C′) − μ(O ∖ C′) ≥ μ(C) − 2η.
 (v) For 0 < ε < r₀, φ_ε := ρ_ε*φ ∈ D^k(U) has tsupport in the compact set K′ := {dist(·,C′) ≤ 2r₀} ⊆ W, |φ_ε| ≤ 1 and φ_ε → φ uniformly; thus φ_ε is admissible for M_W(S) and, by dominated convergence (|v(φ_ε)| ≤ 1_{K′}, μ(K′) < ∞), S(φ_ε) → ∫_A v(φ) dμ. Hence M_W(S) ≥ μ(C) − 2η > c − 2η. As c < μ(W ∩ A) and η > 0 are arbitrary, M_W(S) ≥ μ(W ∩ A).
 Therefore M_W(S) = μ(W ∩ A) in [0,∞].

7. (Conclusion.) The pair (μ, v) of step 4 satisfies (a) IsMeasureRepresentation X μ v, (b) μ Uᶜ = 0, (c) μ K < ∞ for compact K ⊆ U, (d) |v x α| ≤ covectorEuclideanNorm α for all x, α, (e) existence of the restriction currents (step 5) and (f) the mass formula (step 6). ∎

## Key steps

1. Mass estimate |X(ω)| ≤ M_W(X)‖ω‖ for tsupport ω ⊆ W (R0).
2. Extend X by mollification to a locally bounded linear functional X̄ on C_c(U; H), H = ℝ^{I(k,P)} ≅ Λ^k with the Euclidean coefficient norm.
3. Riesz (Simon Ch. 1, 4.14 / SimonGMT simon_theorem_4_14) on the locally compact space U: Radon μ_U and unit field ν; replace ν by a Borel field ν₁ with |ν₁| ≤ 1 everywhere, = 1 a.e.
4. Extend by zero: μ(B) = μ_U(B ∩ U), v = 0 off U; get the representation, μ Uᶜ = 0, finiteness on compacts of U and |v x α| ≤ |α|.
5. Restrictions ∫_A v(ω) dμ are sequentially continuous (dominated by μ(K) sup_K |ω_j|), hence currents.
6. M_W(X⌞A) ≤ μ(W∩A) by (d); ≥ by inner regularity, Lusin, Tietze, Urysohn and mollification.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all identical)`
- `read project/GMT/Ch06/Contract.lean: IsMeasureRepresentation, IsRestriction, IsSlice, IsIntegerMultiplicity, IsRectifiableTriple, CompactlyContainedOpen, SlicingTheorem`
- `read simongmt Chapter06/{Currents,Mass,FormsDuality,CurrentLocalEquality,Forms,Representation}.lean: GeometricCurrentOn, TestFormOnConverges, GeometricCurrentOn.boundary, tsupport_exteriorDerivative_subset, massOn, massAdmissibleOn, covectorEuclideanNorm, zeroRegion, support, NVector`
- `grep -rn 'theorem simon_theorem_4_14' simongmt/Poincare/SimonGMT/Chapter01 (RadonPolarRepresentation.lean; IsLocallyBoundedCcFunctional in VectorFunctionalEnvelope.lean; IsRadonOuterMeasure in RadonOuterMeasure.lean)`
- `grep -rln 'coarea|co-area' simongmt/Poincare/SimonGMT (only linear co-area: Chapter02/CoareaLinear.lean, CoareaProjection.lean; no co-area formula for rectifiable sets)`
- `grep -n '^def |^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt)`
- `grep -rn 'Monotone.ae_differentiableAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegrable_deriv' mathlib/Mathlib`
- `grep -rn 'LipschitzOnWith.extend_real|LipschitzOnWith.ae_differentiableWithinAt_of_mem|theorem measurable_deriv|theorem ext_of_generate_finite' mathlib/Mathlib`
- `grep -rln 'Lusin' mathlib/Mathlib/MeasureTheory (only Lusin–Souslin; Lusin's continuity theorem is cited from Simon Ch. 1, 1.17)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission (scratch /tmp/slicing_split_check_r1, frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalChallenge.lean (6 child statements as _root_ comparator targets in the contract scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (SlicingTheorem from slicing_exists, slicing_support_subset, slicing_mass_bound, slicing_integer_multiplicity_ae; #print axioms)`
- `lake env lean Scratch/Glue.lean (slicing_exists from slicing_mass_representation; slicing_support_subset from slicing_representation_unique; restriction-mass identification from both; #print axioms)`
- `python3 listing of dag.json lean_name values (20 nodes) and grep of the run's nodes/ for the six proposed names (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/parent-child-handoff.json`
- `/tmp/slicing_split_check_r1/Scratch/Stmts.lean`
- `/tmp/slicing_split_check_r1/Scratch/FinalChallenge.lean`
- `/tmp/slicing_split_check_r1/Scratch/Assembly.lean`
- `/tmp/slicing_split_check_r1/Scratch/Glue.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract; Submission is byte-identical, so child statements may use only contract, SimonGMT and Mathlib names. SimonGMT provides currents with sequential continuity, boundary, massOn (Euclidean coefficient norm), support/zeroRegion and the vector Riesz theorem `simon_theorem_4_14` on any locally compact Hausdorff space (Radon outer measure, unit field a.e.). It has only linear co-area and no co-area for rectifiable sets, and Mathlib has neither (nor Lusin's continuity theorem), so these are cited from Simon Ch. 3 §2 and Ch. 1, 1.17. Mathlib provides McShane (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`), Lebesgue's theorem for monotone functions (`Monotone.ae_differentiableAt`, `MonotoneOn.intervalIntegral_deriv_mem_uIcc`) and π-system uniqueness of finite measures (`ext_of_generate_finite`). In a scratch build of the frozen project, all six child statements elaborate in the comparator's child scope. `SlicingTheorem` follows from the four property children by `choose` plus assembly. `slicing_exists` follows from `slicing_mass_representation`, `slicing_support_subset` from `slicing_representation_unique`, and the restriction-mass identification used by `slicing_mass_bound` from both. All of these are kernel-checked with axioms [propext, Classical.choice, Quot.sound]. The DAG (20 nodes) reserves none of the six proposed names; the concurrently added polyhedral children have different names and types. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
