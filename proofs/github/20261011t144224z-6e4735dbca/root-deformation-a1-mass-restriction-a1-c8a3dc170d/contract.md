<!-- theorem-id: gmt-ch06/root.deformation-a1.mass_restriction-a1 -->

## Theorem `Submission.deformation_mass_restriction`

Mass measure, representation and restriction (Simon 2.7–2.9, 2.12; restriction of integer multiplicity currents). For N, k ∈ ℕ and every X ∈ D_k(ℝ^N) (GeometricCurrentOn univ k) with M(X) < ∞ there are a finite Borel measure μ and a field v of k-vectors such that: X(ω) = ∫ v(x)(ω(x)) dμ(x) with integrable integrand for every test form ω (IsMeasureRepresentation X μ v); μ(ℝ^N ∖ spt X) = 0; for every other measure representation (μ′, v′) of X, every bounded Borel set A and every k-covector α, ∫_A v′(x)(α) dμ′ = ∫_A v(x)(α) dμ; and for every Borel set A there is Y ∈ D_k(ℝ^N) with IsRestriction X A Y, Y(ω) = ∫_A v(x)(ω(x)) dμ for all ω, M_W(Y) = μ(W ∩ A) for every open W, Y′ = Y for every Y′ with IsRestriction X A Y′, and Y integer multiplicity whenever X is.

Node: `root.deformation-a1.mass_restriction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1019, https://github.com/ZhengyangZhang06/gmt-formalize/issues/666, https://github.com/ZhengyangZhang06/gmt-formalize/issues/530, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1274, https://github.com/ZhengyangZhang06/gmt-formalize/issues/927, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4215, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4219, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4228, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4237

## Lean problem

Declaration: `Submission.deformation_mass_restriction`

```lean
∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k), X.mass < ∞ → ∃ (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) k), IsFiniteMeasure μ ∧ IsMeasureRepresentation X μ v ∧ μ X.supportᶜ = 0 ∧ (∀ (μ' : Measure (Eucl N)) (v' : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation X μ' v' → ∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A → ∀ α : Covector (Eucl N) k, ∫ x in A, v' x α ∂μ' = ∫ x in A, v x α ∂μ) ∧ ∀ A : Set (Eucl N), MeasurableSet A → ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y ∧ (∀ ω : TestFormOn (univ : Set (Eucl N)) k, Y ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl N) k) x) ∂μ) ∧ (∀ W : Set (Eucl N), IsOpen W → Y.massOn W = μ (W ∩ A)) ∧ (∀ Y' : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y' → Y' = Y) ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y)
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

- Parent DAG node: `root.deformation-a1`
- Child DAG node: `root.deformation-a1.mass_restriction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, 2.6–2.9 and 2.12 (pp. 136–137: representation 2.7 via the Riesz Representation Theorem, Ch. 1, 4.14; characterization 2.8 of μ_T; restriction 2.9; spt T = spt μ_T, 2.12), as summarized in A1 of the parent proof, and A4(b) of the parent proof (restriction of an integer multiplicity current; Ch. 1, 3.6). The steps below supply the details behind those printed statements; the uniqueness argument of Step 7 is the one written in (II.3) of the parent's A3.

Conventions (from the parent proof). I(k,N) is the set of increasing multi-indices γ = (γ₁ < ⋯ < γ_k) in {1,…,N}, e_γ := (e_{γ₁},…,e_{γ_k}), dx^γ := dx^{γ₁}∧⋯∧dx^{γ_k}. For a k-covector α, |α| := (Σ_γ α(e_γ)²)^{1/2} = covectorEuclideanNorm α; for a k-vector w (a linear functional on k-covectors), w^γ := w(dx^γ), |w| := (Σ_γ (w^γ)²)^{1/2}, ⟨α, w⟩ := w(α). Coordinate fact: α = Σ_γ α(e_γ)dx^γ for every k-covector α, hence w(α) = Σ_γ α(e_γ)w^γ and |w(α)| ≤ |α||w|; the map α ↦ (α(e_γ))_γ is a linear isometry of (Λ^k(ℝ^N), |·|) onto ℝ^{I(k,N)}. Unit fact: if τ₁,…,τ_k are orthonormal then |simpleNVector τ| = 1, because its coordinates (simpleNVector τ)^γ = det(τ_i·e_{γ_j}) are the k×k minors of the matrix with columns τ₁,…,τ_k and, by the Cauchy–Binet formula, Σ_γ det(τ_i·e_{γ_j})² = det(τ_i·τ_j) = 1; consequently, whenever IsRectifiableTriple U k M θ ξ holds, |ξ| = 1 H^k-a.e. on M (orientation clause). For a test form ω, ‖ω‖ := sup_x |ω(x)|. H^k = μHE[k]. Fix N, k and X ∈ D_k(ℝ^N) with M(X) < ∞. Degenerate dimensions: if k > N every k-covector on ℝ^N is 0, so every test form and every current of degree k vanish and μHE[k] = 0 on ℝ^N; then μ := 0, v := 0 and Y := 0 satisfy every conclusion (0 is integer multiplicity with M = ∅), and the steps below are also valid verbatim. For k = 0 covectors are scalars (I(0,N) has one element, the empty multi-index), and N = 0 needs no change.

1. Sup-norm bound. If ω is a test form with ‖ω‖ > 0, then ±ω/‖ω‖ is admissible in the definition of M(X) = M_{ℝ^N}(X), so ±X(ω) ≤ M(X)‖ω‖. Thus |X(ω)| ≤ M(X)‖ω‖, and similarly |X(ω)| ≤ M_W(X)‖ω‖ if tsupport ω ⊆ W.

2. Extension to continuous forms. Let C_c denote the continuous compactly supported maps f : ℝ^N → Λ^k(ℝ^N). For f ∈ C_c and a mollifier ϕ_δ, f_δ := ϕ_δ * f is a smooth compactly supported k-form (a test form), ‖f_δ‖ ≤ ‖f‖ (|·| is a norm; Jensen) and f_δ → f uniformly as δ ↓ 0. By Step 1, (X(f_δ)) is Cauchy, so L(f) := lim_{δ↓0} X(f_δ) exists; L is linear, |L(f)| ≤ M(X)‖f‖, and L(ω) = X(ω) for test forms ω (|X(ω_δ) − X(ω)| ≤ M(X)‖ω_δ − ω‖ → 0).

3. Riesz representation (Simon Ch. 1, 4.14 with H := Λ^k(ℝ^N) ≅ ℝ^{I(k,N)}). L satisfies sup{L(f) : |f| ≤ 1, spt f ⊆ K} ≤ M(X) < ∞, so there are a Radon measure μ on ℝ^N and a μ-measurable ν : ℝ^N → ℝ^{I(k,N)} with |ν| = 1 μ-a.e. and L(f) = ∫ Σ_γ f(x)(e_γ)ν^γ(x) dμ(x) for all f ∈ C_c. Let v(x) be the k-vector with v(x)(α) := Σ_γ α(e_γ)ν^γ(x); then v^γ = ν^γ, |v| = |ν| = 1 μ-a.e., and, after changing v on a μ-null set, v is Borel and |v| ≤ 1 everywhere. Thus X(ω) = ∫ v(x)(ω(x)) dμ(x) for every test form ω.

4. Mass of a current with a unit density (2.8). Lemma. Let λ be a finite Borel measure on ℝ^N, u a λ-measurable field of k-vectors with |u| ≤ 1 everywhere and |u| = 1 λ-a.e., A a Borel set, and Y ∈ D_k(ℝ^N) with Y(ω) = ∫_A u(x)(ω(x)) dλ for all test forms ω. Then M_W(Y) = λ(W ∩ A) for every open W ⊆ ℝ^N.
 Proof. (≤) If tsupport ω ⊆ W and |ω| ≤ 1, then Y(ω) ≤ ∫_{A∩W} |ω||u| dλ ≤ λ(A ∩ W). (≥) Let ε > 0. The finite Borel measure λ is inner regular (Simon Ch. 1, 1.15), so there is a compact K ⊆ A ∩ W with λ((A ∩ W) ∖ K) < ε, and by Lusin's theorem (Ch. 1, 1.17) a compact K′ ⊆ K with λ(K ∖ K′) < ε such that u|_{K′} is continuous and |u| = 1 on K′. Let u♭(x) := Σ_γ u^γ(x)dx^γ (continuous on K′, |u♭| = 1 and ⟨u♭, u⟩ = |u|² = 1 there). Extend u♭|_{K′} to a continuous f₀ : ℝ^N → Λ^k (Tietze, coordinatewise), let R(y) := y/max{1,|y|} and choose a continuous χ with 0 ≤ χ ≤ 1, χ = 1 on K′ and compact support in W; then f := χ·(R∘f₀) ∈ C_c, |f| ≤ 1, spt f ⊆ W, f = u♭ on K′, so ∫_A⟨f, u⟩dλ ≥ λ(K′) − λ((A ∩ W) ∖ K′) ≥ λ(A ∩ W) − 4ε. The mollifications f_δ are test forms with tsupport f_δ ⊆ W for small δ (spt f is a compact subset of the open W), |f_δ| ≤ 1 and f_δ → f uniformly, so by dominated convergence (λ finite) Y(f_δ) → ∫_A⟨f, u⟩dλ. Hence M_W(Y) ≥ λ(A ∩ W) − 4ε for all ε > 0.

5. μ is finite and is the mass measure; the representation. For R > 0 apply Step 4 to λ := μ⌞B_R(0) (finite, since μ is Radon), u := v, A := ℝ^N and the current X — legitimate for test forms supported in B_R(0) — to get M_W(X) = μ(W) for open W ⊆ B_R(0). Since admissible forms have compact support, M_W(X) = sup_R M_{W∩B_R(0)}(X) and μ(W) = sup_R μ(W ∩ B_R(0)), so μ(W) = M_W(X) for every open W; in particular μ(ℝ^N) = M(X) < ∞: μ is a finite Borel measure (IsFiniteMeasure μ). For each test form ω, x ↦ v(x)(ω(x)) is μ-measurable and bounded by ‖ω‖, hence μ-integrable, and its integral is X(ω) (Step 3): IsMeasureRepresentation X μ v.

6. Support (2.12). The zero region Z of X is the union of the open sets W with compact closure on which X vanishes; ℝ^N being second countable, Z is a countable union of such W, and μ(W) = M_W(X) = 0 for each (every admissible form supported in W is annihilated). Hence μ(ℝ^N ∖ spt X) = μ(Z) = 0.

7. Uniqueness of the vector measure (as in (II.3) of the parent). Let (μ′, v′) satisfy IsMeasureRepresentation X μ′ v′.
 (a) Local integrability. If A is bounded Borel and α a k-covector, choose φ ∈ C_c^∞(ℝ^N) with φ = 1 on the compact set closure(A); ω := φα is a test form and v′(x)(ω(x)) = φ(x)v′(x)(α) is μ′-integrable, so x ↦ v′(x)(α) is μ′-integrable on A. The same holds for (μ, v).
 (b) Fix R > 0 and a covector α. On the Borel subsets B of the open ball B_R(0), Ξ′(B) := ∫_B v′(α)dμ′ and Ξ(B) := ∫_B v(α)dμ are finite signed measures (countable additivity by dominated convergence and (a)). (1) For φ ∈ C_c^∞(B_R(0)): ∫φ dΞ′ = X(φα) = ∫φ dΞ. (2) For φ ∈ C_c(B_R(0)): the mollifications φ_δ ∈ C_c^∞(B_R(0)) (δ small) are supported in a fixed compact subset K of B_R(0), |φ_δ| ≤ ‖φ‖ and φ_δ → φ uniformly; dominated convergence (dominators ‖φ‖·|v′(α)|1_K and ‖φ‖·|v(α)|1_K) gives ∫φdΞ′ = ∫φdΞ. (3) For compact K_c ⊆ B_R(0), φ_i := max{0, 1 − i·dist(·, K_c)} (i large) are continuous, supported in a fixed compact subset of B_R(0), 0 ≤ φ_i ≤ 1, and φ_i ↓ 1_{K_c}; hence Ξ′(K_c) = Ξ(K_c). (4) The compact subsets of B_R(0) form a π-system generating its Borel σ-algebra (open subsets of B_R(0) are countable unions of compact sets), and {B : Ξ′(B) = Ξ(B)} is a Dynkin system (it contains B_R(0), an increasing union of compact sets, and is closed under relative complements and countable disjoint unions). By Dynkin's π–λ theorem Ξ′ = Ξ on all Borel subsets of B_R(0).
 Since every bounded Borel set lies in some B_R(0): for every bounded measurable A and every covector α, ∫_A v′(x)(α)dμ′ = ∫_A v(x)(α)dμ. This is the uniqueness conjunct of the statement.

8. Restrictions (2.9). Let A be Borel and define Y(ω) := ∫_A v(x)(ω(x))dμ. Y is linear; |Y(ω)| ≤ μ(ℝ^N)‖ω‖ since |v| ≤ 1; if ω_j → 0 in the test-form topology then ‖ω_j‖ → 0 (uniform convergence of the 0-th derivatives on a common compact support), so Y(ω_j) → 0. Hence Y ∈ D_k(ℝ^N) (GeometricCurrentOn univ k). With the representation (μ, v) of Step 5, IsRestriction X A Y holds (A is measurable), and Y(ω) = ∫_A v(ω)dμ by definition. By Step 4 (λ := μ, u := v), M_W(Y) = μ(W ∩ A) for every open W.
 Uniqueness. Let IsRestriction X A Y′ hold via some representation (μ′, v′) of X: Y′(ω) = ∫_A v′(x)(ω(x))dμ′. Fix ω and R with tsupport ω ⊆ B_R(0). By the coordinate fact, v′(x)(ω(x)) = Σ_γ ω_γ(x)v′(x)(dx^γ) with ω_γ := ω(·)(e_γ) ∈ C_c^∞, and similarly for v. By Step 7(b) (α := dx^γ) the signed measures Ξ′_γ, Ξ_γ agree on Borel subsets of B_R(0); the bounded Borel function ω_γ1_A, supported in B_R(0), is a uniform limit of Borel simple functions supported in B_R(0), so ∫ω_γ1_A dΞ′_γ = ∫ω_γ1_A dΞ_γ. Summing over γ, Y′(ω) = Y(ω) for every ω, i.e. Y′ = Y (GeometricCurrentOn.ext).

9. Integer multiplicity is preserved (parent A4(b)). Suppose IsIntegerMultiplicity X: X = τ(M, θ, ξ) with IsRectifiableTriple univ k M θ ξ and θ(x) ∈ {1,2,…} for x ∈ M.
 (a) (H^k⌞M, θξ) is a measure representation of X: for a test form ω, x ↦ θ(x)ξ(x)(ω(x)) is H^k⌞M-measurable (triple conditions), bounded in absolute value by ‖ω‖θ1_{tsupport ω} H^k-a.e. on M (unit fact), hence integrable (θ is integrable on M ∩ tsupport ω), and its integral is tauAction k M θ ξ ω = X(ω). By the uniqueness of Step 8 (applied to the restriction defined through this representation), Y(ω) = ∫_A θ(x)ξ(x)(ω(x))dH^k⌞M = tauAction k (M ∩ A) θ ξ ω for all ω.
 (b) The triple (M ∩ A, θ, ξ) satisfies IsRectifiableTriple univ k: M ∩ A ⊆ univ; it is H^k-null-measurable (M null-measurable, A Borel); it is countably k-rectifiable (subset of M; CountablyRectifiable.mono); θ > 0 on M ∩ A; θ is integrable on (M ∩ A) ∩ K for compact K (subset of M ∩ K); ξ is a.e. strongly measurable for H^k⌞(M ∩ A) (a measure dominated by H^k⌞M). Orientation: let ν := θH^k⌞(M ∖ A); ν(K) < ∞ for compact K. By the Upper Density Theorem (Simon Ch. 1, 3.6, with Remark 3.7(2) to remove the finiteness assumption by means of the open balls B_j(0)), applied to the measure θH^k⌞M and its subset M ∖ A, Θ*^k(ν, x) = limsup_{r↓0} ν(B_r(x))/(ω_k r^k) = 0 for H^k-a.e. x ∉ M ∖ A, in particular for H^k-a.e. x ∈ M ∩ A. Fix such an x, a k-dimensional subspace Π, f ∈ C_c(ℝ^N) with spt f ⊆ B_R(0), and r > 0. The blow-up η_{x,r}(y) := r⁻¹(y − x) (blowUpMap x r) is injective, so η_{x,r}(M) is the disjoint union of η_{x,r}(M ∩ A) and η_{x,r}(M ∖ A); η_{x,r} is a similarity of ratio 1/r, so H^k(η_{x,r}(E)) = r^{−k}H^k(E) and ∫_{η_{x,r}(E)} g dH^k = r^{−k}∫_E g∘η_{x,r} dH^k; and x + r·η_{x,r}(z) = z. Therefore
 |∫_{η_{x,r}(M∖A)} f(y)θ(x + ry)dH^k(y)| = r^{−k}|∫_{M∖A} f(η_{x,r}(z))θ(z)dH^k(z)| ≤ ‖f‖ r^{−k}ν(B_{Rr}(x)) → 0 (r ↓ 0).
 Hence the integrals ∫_{η_{x,r}(M)} f(y)θ(x+ry)dH^k(y) and ∫_{η_{x,r}(M∩A)} f(y)θ(x+ry)dH^k(y) have the same limit as r ↓ 0, and HasWeightedApproximateTangentSpaceAt k M θ x Π implies HasWeightedApproximateTangentSpaceAt k (M ∩ A) θ x Π. Since the orientation clause of (M, θ, ξ) holds at H^k-a.e. x ∈ M, the orientation clause of (M ∩ A, θ, ξ) holds at H^k-a.e. x ∈ M ∩ A with the same orthonormal frame.
 (c) θ is natural-valued on M ∩ A. By (a)–(c), IsIntegerMultiplicity Y.

10. Conclusion. μ, v of Steps 3 and 5 satisfy IsFiniteMeasure μ, IsMeasureRepresentation X μ v (Step 5), μ(X.supportᶜ) = 0 (Step 6) and the uniqueness conjunct (Step 7); for every measurable A the current Y of Step 8 satisfies IsRestriction X A Y, the integral formula, the mass formula M_W(Y) = μ(W ∩ A) for open W, the uniqueness among all Y′ with IsRestriction X A Y′ (Step 8), and IsIntegerMultiplicity X → IsIntegerMultiplicity Y (Step 9). ∎

## Key steps

1. |X(ω)| ≤ M(X)‖ω‖; continuous extension L of X to continuous compactly supported forms.
2. Riesz representation (Ch. 1, 4.14): μ Radon, unit density v with X(ω) = ∫ v(ω) dμ.
3. Mass lemma via inner regularity, Lusin, Tietze and mollification: a current with unit density over A has M_W = λ(W ∩ A); hence μ(W) = M_W(X), μ finite, μ(ℝ^N ∖ spt X) = 0.
4. Uniqueness of the vector measure of any representation on bounded Borel sets (test forms φα, mollification, compacts, Dynkin).
5. Restrictions Y = ∫_A v(ω)dμ: currents, IsRestriction, mass formula, uniqueness among all IsRestriction witnesses.
6. Integer multiplicity: Y = τ(M ∩ A, θ, ξ); weighted tangent spaces of (M∩A, θ) and (M, θ) agree a.e. by the Upper Density Theorem.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (all byte-identical)`
- `rg -n '^def (latticeFace|latticeFaceAction|IsLatticeChain|DeformationTheorem|IsRestriction|IsMeasureRepresentation)' project/GMT/Ch06/Contract.lean (lines 107, 115, 164, 171, 177, 274)`
- `python3 over dag.json: lean_name of all 86 nodes vs the nine proposed deformation_* names (no collision; only deformation_theorem, the selected node, is reserved)`
- `rg -n 'deformation_(retraction|good_center|mass_restriction|im_completeness|im_pushforward_limit|onto_skeleton|skeleton_polyhedral|im_combination|dilation)' project lake-packages-25730c7c/simongmt (no match)`
- `python3 over nodes/root-deformation-a1/decomposition-audit-v1.json (only skeleton_polyhedral natural_proof_acceptable = false; required change: R = √n/2, δ = 1/(2√n))`
- `rg -il 'poincar' mathlib/Mathlib (curve integrals, Lie algebras, dynamics, Poincaré conjecture only: no BV Poincaré inequality on convex domains)`
- `rg -l 'BoundedVariationOn|eVariationOn' mathlib/Mathlib (one-dimensional bounded variation only)`
- `rg -l 'Sobolev|GagliardoNirenberg|gagliardo' mathlib/Mathlib; rg -n '^theorem [a-zA-Z_.]*(lintegral_pow_le|eLpNorm_le_eLpNorm_fderiv)' mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean (Gagliardo–Nirenberg–Sobolev for compactly supported C¹ maps only)`
- `rg -n 'theorem (cthickening_subset_thickening'|cthickening_cthickening_subset|mem_thickening_iff) ' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean (lines 143, 261, 638)`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib (Topology/MetricSpace/Lipschitz.lean:308, McShane extension)`
- `sed -n '440,780p' book/chapter-02.txt (Simon Ch. 2, 2.1–2.9: 2.7 assumes δ ∈ (0,1) and B_{δR}(ξ) ⊂ U ⊂ B_R(ξ); the proof of 2.8 uses display (1) only where d(x) < dist(B_δ(0), ∂U))`
- `sed -n '560,720p;1780,1920p' book/chapter-06.txt (2.34–2.37 and printed displays (18)–(37) of the proof of 5.1)`
- `python3 -I: validate_lean_statement (verifier/lean_contract.py) on the nine lean_statements (all valid and unchanged)`
- `lake env lean Scratch/V2_NC_<key>.lean for the nine keys: `theorem _root_.HumanizeNodeComparator.target : (stmt) := by sorry` in the contract scope (all exit 0; only the expected sorry warning)`
- `lake env lean Scratch/V2_Assembly.lean (assembly : SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → Stmt_onto_skeleton → Stmt_skeleton_polyhedral → Stmt_im_combination → Stmt_dilation → DeformationTheorem; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/deform_check/Scratch/V2_Assembly.lean`
- `/tmp/deform_check/Scratch/V2_NC_skeleton_polyhedral.lean`
- `/tmp/deform_v2/logs/assembly.log`
- `/tmp/deform_v2/logs/nc_skeleton_polyhedral.log`

Pinned revisions confirmed and the frozen contract is byte-identical to the snapshot (Submission = Contract), so the nine v1 interfaces remain valid. None of the nine bare names collides with a DAG reservation or with a declaration in the project or SimonGMT sources. All nine statements pass validate_lean_statement and elaborate in the exact comparator NodeChallenge scope. The parent assembly re-derives DeformationTheorem from onto_skeleton, skeleton_polyhedral, im_combination and dilation plus SlicingTheorem and LipschitzPushforwardIntegerMultiplicity, with axioms [propext, Classical.choice, Quot.sound]. No Matrix/IsUnit construction occurs. The pinned Mathlib has no multi-dimensional BV Poincaré inequality or BV cut-off/extension lemma (only one-dimensional BoundedVariationOn and the compact-support Gagliardo–Nirenberg–Sobolev inequality), so (T4) of deformation_skeleton_polyhedral is proved from Simon Ch. 2, 2.7–2.9 and [GT01, (7.45)]. Simon's printed 2.7 requires δ ∈ (0,1), and his proof of 2.8 needs the inner ball at positive distance from ∂U. The corrected parameters R = √n/2, δ = 1/(2√n) (δR = 1/4, distance 1/4) meet both requirements for every n ≥ 1, as the revised (T4) verifies explicitly.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
