<!-- theorem-id: gmt-ch06/root.rectifiability-a1.projection_null-a1 -->

## Theorem `Submission.rectifiability_projection_null`

Let P, m ∈ ℕ, n := m + 1, U ⊆ ℝ^P open, T ∈ D_n(U) with M_W(T) + M_W(∂T) < ∞ for every open W ⊂⊂ U, and μ a Borel measure on ℝ^P with IsMassMeasure T μ. Let Q be a linear isometry of ℝ^P and E ⊆ ℝ^P a Borel set such that Lⁿ(p_α(Q(E))) = 0 for every α ∈ I(n,P), where p_α : ℝ^P → ℝⁿ, x ↦ (x^{α(1)}, …, x^{α(n)}), and Lⁿ is Lebesgue measure (volume) on ℝⁿ. Then μ(E) = 0.

Node: `root.rectifiability-a1.projection_null-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/340

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1019

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2387, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2396, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2404, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2415, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2428, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2441, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2448, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2454, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2462

## Lean problem

Declaration: `Submission.rectifiability_projection_null`

```lean
∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ μ : Measure (Eucl P), IsMassMeasure T μ → ∀ (Q : Eucl P ≃ₗᵢ[ℝ] Eucl P) (E : Set (Eucl P)), MeasurableSet E → (∀ α : SimonMultiIndex (m + 1) P, (volume : Measure (Eucl (m + 1))) ((fun x : Eucl P => (WithLp.toLp 2 (fun i : Fin (m + 1) => Q x (α i)) : Eucl (m + 1))) '' E) = 0) → μ E = 0
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

- Parent DAG node: `root.rectifiability-a1`
- Child DAG node: `root.rectifiability-a1.projection_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Lemma 2.36 with its printed proof (displays (1)-(4)), Remark 2.37(2) and the inner-regularity step of Remark 2.37(1) (pp. 143-145). Following 2.37(2), the printed proof is run for Q_#T and read back on ℝ^P: π_α := p_α∘Q replaces p_α, and Q^*dx^α = π_α^*dy. It is given first for compact K (the printed step 'letting K be an arbitrary compact subset of E') and then extended to Borel E by inner regularity. The currents p_{α#}(T⌞ω_α) of the printed proof are realized as explicit linear functionals Y_α, so no general push-forward or restriction machinery is needed.

One input is proved differently. The printed proof takes from Remark 2.35 that the top-dimensional current p_{α#}(T⌞ω_α), which has finite mass and finite boundary mass, is given by a BV density. The only consequence it uses is that this current does not charge Lⁿ-null sets. Remark 2.35 rests on the compactness theorem for BV functions (Simon Ch. 2, 2.6), which the pinned library lacks: SimonGMT Chapter02/BV.lean only proves closure statements for sequences that already converge. Step 3 therefore replaces 2.35 by a self-contained quantitative estimate. It uses the Newtonian-potential representation of a compactly supported smooth function (D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Lemma 7.14). Step 4 turns it into the bound |Y_α(a)| ≤ C_α sup|a|·Lⁿ(spt a)^{1/n}, which is what display (2) of the printed proof needs.

Erratum: in 2.37(2) the printed implication 'Lⁿ(Q(E)) = 0 for each α ⇒ μ_T(E) = 0' should read 'Lⁿ(p_α(Q(E))) = 0 for each α ⇒ μ_T(E) = 0'.

1. Notation and the degenerate case. Throughout, n = m + 1. |·| is the Euclidean coefficient norm on covectors and multivectors (Simon 6, Remark 2.6; covectorEuclideanNorm), and I := I(n,P).
 For J = (j₁ < ⋯ < j_r) ⊆ {1, …, P} write dx^J := dx^{j₁}∧⋯∧dx^{j_r}, and let Q^*dx^J denote its pull-back by Q.
 π_α := p_α∘Q : ℝ^P → ℝⁿ is linear. On ℝⁿ use coordinates y¹, …, yⁿ, and write dy := dy¹∧⋯∧dyⁿ and dy^{(ĵ)} := dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ. Then π_α^*dy^i = Q^*dx^{α(i)}, π_α^*dy = Q^*dx^α and π_α^*dy^{(ĵ)} = Q^*dx^{α_ĵ}, where α_ĵ ∈ I(n−1,P) is α with its j-th entry removed.
 By the Cauchy-Binet formula, for r = n and for r = n − 1 the covectors Q^*dx^J (J ∈ I(r,P)) form an orthonormal basis of the r-covectors for the Euclidean inner product: their Gram matrix (det((QQ^T)_{JJ′}))_{J,J′} is the identity.
 Constants: ω_n := Lⁿ(B_1(0)), and c_n is a constant with |γ∧φ| ≤ c_n|γ||φ| for all 1-covectors γ and (n−1)-covectors φ on ℝ^P (the wedge product is bilinear on finite-dimensional spaces; in fact c_n = 1 works).
 If P < n, then I = ∅, every n-covector on ℝ^P is 0, every ω ∈ Dⁿ(U) is 0, T = 0 and M_W(T) = 0. Hence μ(W) = 0 for every open W ⊂⊂ U and μ(ℝ^P∖U) = 0. Since U is a countable union of open W ⊂⊂ U, μ = 0 and the claim holds. Assume P ≥ n from now on.

2. Representation and mass bounds. Apply the sibling mass_measure_representation to T, whose local masses are finite. It gives a strongly measurable ξ : ℝ^P → Λ_n(ℝ^P) with |ξ| = 1 μ-a.e. such that T(ω) = ∫⟨ω, ξ⟩dμ for every ω ∈ Dⁿ(U), with μ-integrable integrand. Also μ(W) = M_W(T) < ∞ for open W ⊂⊂ U.
 M_W is the supremum of T(φ) over φ with tsupport φ ⊆ W and |φ| ≤ 1 (SimonGMT massOn, massAdmissibleOn). Applying the definition to ±φ/sup|φ| gives the mass bounds: |T(φ)| ≤ sup|φ|·M_W(T) and |∂T(ψ)| ≤ sup|ψ|·M_W(∂T) whenever φ ∈ Dⁿ(U) and ψ ∈ D^{n−1}(U) have tsupport in the open set W ⊂⊂ U.

3. A potential estimate (replaces Remark 2.35). For w ∈ ℝⁿ∖{0} and j = 1, …, n put K_j(w) := w_j/(nω_n|w|ⁿ), and K_j(0) := 0.
 Claim: let a ∈ C_c^∞(ℝⁿ) and ψ_j := K_j * a, i.e. ψ_j(y) = ∫K_j(y − z)a(z)dz. Then each ψ_j is C^∞ on ℝⁿ, Σ_{j=1}^n ∂_jψ_j = a, and sup_{ℝⁿ}|ψ_j| ≤ ((n+1)/n)·sup|a|·(Lⁿ(spt a)/ω_n)^{1/n} for every j.
 Proof. (i) We have |K_j(w)| ≤ |w|^{1−n}/(nω_n). By polar coordinates, ∫_{B_ρ(0)}|w|^{1−n}dw = nω_nρ (Mathlib Measure.measurePreserving_homeomorphUnitSphereProd; the surface measure of S^{n−1} is nω_n by Measure.toSphere_apply_univ). So K_j ∈ L¹_loc(ℝⁿ). Being the convolution of a locally integrable function with a compactly supported smooth function, ψ_j = K_j * a is C^∞, and ∂^βψ_j = K_j * ∂^βa for every multi-index β (Mathlib HasCompactSupport.contDiff_convolution_right, HasCompactSupport.hasFDerivAt_convolution_right).
 (ii) Fix y ∈ ℝⁿ. For every unit vector θ, since a has compact support, a(y) = −∫_0^∞(d/dt)a(y + tθ)dt = −∫_0^∞∇a(y + tθ)·θ dt. Integrate over θ ∈ S^{n−1} with respect to the surface measure σ, where σ(S^{n−1}) = nω_n. Then use polar coordinates about y: ∫_{ℝⁿ}g(z)dz = ∫_{S^{n−1}}∫_0^∞g(y + tθ)t^{n−1}dt dσ(θ), with g(z) := ∇a(z)·(z − y)/|z − y|ⁿ. For this g, g(y + tθ)t^{n−1} = ∇a(y + tθ)·θ, and g is integrable because |g(z)| ≤ sup|∇a|·1_{spt a}(z)·|z − y|^{1−n}. This gives nω_n·a(y) = −∫∇a(z)·(z − y)|z − y|^{−n}dz. Equivalently, a(y) = Σ_j∫K_j(y − z)∂_ja(z)dz = Σ_j(K_j * ∂_ja)(y), which equals Σ_j∂_jψ_j(y) by (i). For n = 1, S⁰ = {±1} carries counting measure, nω_n = 2, and this is the fundamental theorem of calculus.
 (iii) Let S := spt a. If Lⁿ(S) = 0, then the open set {a ≠ 0} ⊆ S is Lⁿ-null, hence empty, so a ≡ 0, ψ_j ≡ 0 and the claim is trivial. Otherwise let ρ := (Lⁿ(S)/ω_n)^{1/n} > 0. Then |ψ_j(y)| ≤ sup|a|·(nω_n)^{−1}∫_S|y − z|^{1−n}dz. Moreover ∫_S|y − z|^{1−n}dz ≤ ∫_{B_ρ(y)}|y − z|^{1−n}dz + ∫_{S∖B_ρ(y)}ρ^{1−n}dz ≤ nω_nρ + ρ^{1−n}Lⁿ(S) = (n + 1)ω_nρ. Hence |ψ_j(y)| ≤ ((n+1)/n)·sup|a|·ρ. ∎

4. The functionals Y_α (printed (1)) and their potential bound. Fix an open W ⊂⊂ U and ω ∈ Dⁿ(U) with tsupport ω ⊆ W and |ω| ≤ 1.
 Write ω = Σ_{α∈I}ω_αQ^*dx^α with ω_α := ⟨ω, Q^*dx^α⟩ (the orthonormal expansion of step 1). Then ω_α ∈ C_c^∞(ℝ^P), tsupport ω_α ⊆ W, |ω_α| ≤ |ω| ≤ 1, and T(ω) = Σ_αT(ω_αQ^*dx^α).
 Fix α and write π := π_α. For a ∈ C^∞(ℝⁿ) set Y_α(a) := T(ω_α·(a∘π)·Q^*dx^α). The form is smooth with tsupport in tsupport ω_α ⊆ W, so it lies in Dⁿ(U). (Y_α(a) is Simon's p_{α#}(T⌞ω_α)(a dy), written for Q_#T.) By step 2, Y_α(a) = ∫ω_α(x)a(π(x))⟨Q^*dx^α, ξ(x)⟩dμ(x).
 Claim: for every a ∈ C_c^∞(ℝⁿ), |Y_α(a)| ≤ C_α·sup|a|·Lⁿ(spt a)^{1/n}, where C_α := (n + 1)ω_n^{−1/n}(M_W(∂T)·sup|ω_α| + c_nM_W(T)·sup|dω_α|).
 Proof. Take the ψ_j of step 3 and the smooth (n−1)-form ψ̂ := Σ_j(−1)^{j−1}ψ_j dy^{(ĵ)} on ℝⁿ; then dψ̂ = (Σ_j∂_jψ_j)dy = a dy. Its pull-back π^#ψ̂ = Σ_j(−1)^{j−1}(ψ_j∘π)Q^*dx^{α_ĵ} is smooth on ℝ^P, and d(π^#ψ̂) = π^#(dψ̂) = (a∘π)Q^*dx^α.
 Put Φ := ω_απ^#ψ̂ ∈ D^{n−1}(U); its tsupport lies in tsupport ω_α ⊆ W. Then dΦ = dω_α∧π^#ψ̂ + ω_α(a∘π)Q^*dx^α, so
 Y_α(a) = T(dΦ) − T(dω_α∧π^#ψ̂) = ∂T(Φ) − T(dω_α∧π^#ψ̂).
 The (n−1)-covectors Q^*dx^{α_ĵ} (j = 1, …, n) are orthonormal (step 1). So by step 3, |π^#ψ̂(x)| = (Σ_jψ_j(πx)²)^{1/2} ≤ n·max_jsup|ψ_j| ≤ (n + 1)ω_n^{−1/n}·sup|a|·Lⁿ(spt a)^{1/n}.
 Both forms have tsupport in W, so the mass bounds of step 2 give |∂T(Φ)| ≤ M_W(∂T)·sup|ω_α|·sup|π^#ψ̂| and |T(dω_α∧π^#ψ̂)| ≤ M_W(T)·c_n·sup|dω_α|·sup|π^#ψ̂|. Adding the two bounds proves the claim. ∎

5. Printed (2)-(4) for compact K. Let K ⊆ U be compact with Lⁿ(π_α(K)) = 0 for every α ∈ I. Fix W, ω and α as in step 4, and let F := π_α(K), a compact Lⁿ-null set.
 For ε > 0 let G_ε := {y ∈ ℝⁿ : dist(y, F) < ε}. The G_ε are open, decrease as ε ↓ 0, and intersect to F. By continuity from above (Lⁿ(G_1) < ∞), Lⁿ(G_ε) → Lⁿ(F) = 0.
 Let φ_ε be a mollifier supported in B_{ε/4}(0), and set b_ε := 1_{G_{ε/2}} * φ_ε. Then b_ε ∈ C_c^∞(ℝⁿ), 0 ≤ b_ε ≤ 1, b_ε = 1 on G_{ε/4} (a neighbourhood of F), and spt b_ε ⊆ G_ε. Fix χ ∈ C_c^∞(ℝⁿ) with 0 ≤ χ ≤ 1 and χ = 1 on a neighbourhood of the compact set π_α(tsupport ω_α). Then ω_α·(χ∘π_α) = ω_α, so
 T(ω_αQ^*dx^α) = Y_α(χ) = Y_α(b_εχ) + Y_α((1 − b_ε)χ).
 First term: sup|b_εχ| ≤ 1 and spt(b_εχ) ⊆ G_ε, so step 4 gives |Y_α(b_εχ)| ≤ C_α·Lⁿ(G_ε)^{1/n}.
 Second term: by the integral formula of step 4, Y_α((1 − b_ε)χ) = ∫ω_α(x)(1 − b_ε(π_αx))⟨Q^*dx^α, ξ(x)⟩dμ(x). The integrand vanishes outside tsupport ω_α ⊆ W and on K, where b_ε∘π_α = 1. It is bounded by 1 μ-a.e., because |ω_α| ≤ 1, 0 ≤ 1 − b_ε ≤ 1 and |⟨Q^*dx^α, ξ⟩| ≤ |Q^*dx^α||ξ| = 1. Hence |Y_α((1 − b_ε)χ)| ≤ μ(W∖K).
 Letting ε ↓ 0 gives |T(ω_αQ^*dx^α)| ≤ μ(W∖K). Summing over α gives T(ω) ≤ N·μ(W∖K) with N := #I. Taking the supremum over admissible ω, M_W(T) ≤ N·μ(W∖K) (printed (3)), i.e. μ(W) ≤ N·μ(W∖K) for every open W ⊂⊂ U (printed (4)).
 Now choose r₀ > 0 with {x : dist(x, K) ≤ r₀} ⊆ U (possible since K is compact and U open; any r₀ works if U = ℝ^P), and put W_q := {x : dist(x, K) < r₀/q}. The W_q are open, ⊂⊂ U and decreasing, with ⋂_qW_q = K. Since μ(W₁) < ∞, continuity from above gives μ(W_q∖K) → μ(∅) = 0. Hence μ(K) ≤ μ(W_q) ≤ N·μ(W_q∖K) → 0, i.e. μ(K) = 0.

6. Borel E (inner regularity, 1.15 of Ch. 1, as in 2.37(1)). Let E be Borel with Lⁿ(p_α(Q(E))) = Lⁿ(π_α(E)) = 0 for all α. Since μ(ℝ^P∖U) = 0, μ(E) = μ(E ∩ U).
 Let (W_q) be open sets ⊂⊂ U with U = ⋃_qW_q. Each μ⌞W_q is a finite Borel measure on the metric space ℝ^P, so by Simon Ch. 1, 1.15(2), μ(E ∩ W_q) = sup{μ(C) : C ⊆ E ∩ W_q closed}.
 Every such C lies in the compact set closure(W_q) ⊆ U, so it is a compact subset of U, and π_α(C) ⊆ π_α(E) is Lⁿ-null for every α. Hence μ(C) = 0 by step 5. Thus μ(E ∩ W_q) = 0 for all q, and μ(E) ≤ Σ_qμ(E ∩ W_q) = 0. ∎

## Key steps

1. Run Simon's proof of 2.36 with π_α = p_α∘Q (Remark 2.37(2)). The covectors Q^*dx^J are orthonormal by Cauchy–Binet, and P < n forces T = 0 and μ = 0.
2. Use the representation T(ω) = ∫⟨ω,ξ⟩dμ with |ξ| = 1 (sibling mass_measure_representation) and the mass bounds |T(φ)| ≤ M_W(T)sup|φ|, |∂T(ψ)| ≤ M_W(∂T)sup|ψ|.
3. Potential estimate replacing Remark 2.35 (no BV compactness): for a ∈ C_c^∞(ℝⁿ), ψ_j := K_j*a with K_j(x) = x_j/(nω_n|x|ⁿ) satisfy Σ∂_jψ_j = a and sup|ψ_j| ≤ ((n+1)/n)sup|a|(Lⁿ(spt a)/ω_n)^{1/n}.
4. Writing a dy = dψ̂ and pulling back by π_α gives Y_α(a) = ∂T(ω_απ^#ψ̂) − T(dω_α∧π^#ψ̂), hence |Y_α(a)| ≤ C_α sup|a| Lⁿ(spt a)^{1/n}.
5. Let K be compact with Lⁿ(π_α(K)) = 0. Cut off near π_α(K) with b_ε supported in sets whose measure tends to 0. This gives |T(ω_αQ^*dx^α)| ≤ μ(W∖K), hence μ(W) ≤ Nμ(W∖K) (printed (3),(4)), and W_q ↓ K gives μ(K) = 0.
6. Inner regularity of the finite measures μ⌞W_q extends μ(K) = 0 to Borel E.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean (all identical)`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurePreserving_homeomorphUnitSphereProd|theorem ae_tendsto_average_norm_sub|theorem exists_disjoint_subfamily_covering_enlargement|theorem haarMeasure_unique|theorem addHaar_image_linearMap' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n 'euclideanHausdorffMeasure_eq_volume|LipschitzOnWith.extend_real|contDiff_convolution_right|LipschitzWith.ae_differentiableAt|toSphere_apply_univ :|theorem ae_tendsto_measure_inter_div|theorem hausdorffMeasure_apply|measure_toMeasurable_inter|hausdorffMeasure_smul₀' local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -c 'Besicovitch.Federer|purely unrectifiable|PurelyUnrectifiable|Mickle' local-references/197bdd4b88278494/mathlib/Mathlib (no match)`
- `grep -n '^theorem\|^def' simongmt Chapter03/{Rectifiable,SubmanifoldCover}.lean, Chapter02/{AreaLipschitz,AreaCritical,Area,AreaBranches,Lipschitz,BV,WhitneyExtension}.lean, Chapter01/{DensityComparison,HausdorffDensityBounds,HausdorffContentDensity,Lusin,Densities,RadonPolarRepresentation,VectorFunctionalEnvelope}.lean, Chapter06/{Mass,FormsDuality,Currents}.lean`
- `grep -n 'def massOn|def massAdmissibleOn|def covectorEuclideanNorm|abbrev SimonMultiIndex|def HasWeightedApproximateTangentSpaceAt|def PurelyUnrectifiable|def CountablyRectifiable' simongmt Chapter06/Mass.lean, Chapter06/FormsDuality.lean, Chapter03/Rectifiable.lean`
- `sed -n chapter-02.txt 140,330 (Ch.2 1.5-1.8); chapter-03.txt 1,560 (Ch.3 §1 and §3); chapter-06.txt 560,720 and 2130,2300 (2.34-2.37, 8.1)`
- `lake build GMT.Ch06.Submission (scratch /tmp/rect_a1_v2_check, frozen commit d8d46c9, pinned packages lake-packages-25730c7c)`
- `lake env lean Scratch/V2_Names.lean and Scratch/V2_Names2.lean (#check and #print axioms of every cited Mathlib/SimonGMT declaration)`
- `lake env lean Scratch/V2_Challenge.lean (12 child statements generated with verifier/gmt-compare.py contract_scope/child_modules; 0 errors)`
- `lake env lean Scratch/Assembly.lean, Scratch/C4fromC3.lean, Scratch/C5Check.lean, Scratch/V2_Glue.lean (#print axioms)`
- `python3 lean_name collision scan of dag.json and nodes/*/decomposition-v*.json (86 DAG names; no rectifiability_* or mickle_* collision)`
- `python3 audit of nodes/root-rectifiability-a1/decomposition-v1.json and decomposition-audit-v1.json (accepted and rejected children, required changes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaBranches.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffDensityBounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/HausdorffContentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-audit-v1.json`
- `/tmp/rect_a1_v2_check/Scratch/V2_Challenge.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Names.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Names2.lean`
- `/tmp/rect_a1_v2_check/Scratch/V2_Glue.lean`
- `/tmp/rect_a1_v2_check/Scratch/Assembly.lean`
- `/tmp/rect_a1_v2_check/Scratch/C4fromC3.lean`
- `/tmp/rect_a1_v2_check/Scratch/C5Check.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract; it is byte-identical to the workspace Contract and Submission. The pinned Mathlib has no Besicovitch-Federer, purely-unrectifiable or Mickle-Radó result (rg: no match), and SimonGMT has neither BV compactness (Chapter02/BV.lean proves only closure statements) nor the rectifiable-to-C¹ cover (SubmanifoldCover.lean proves only the converse). This confirms the three gaps the v1 audit identified. The pinned libraries do contain every ingredient that the rewritten proofs cite. Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LipschitzWith.ae_differentiableAt (Rademacher.lean:385), Measure.measurePreserving_homeomorphUnitSphereProd and toSphere_apply_univ (HaarToSphere.lean), IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub and ae_tendsto_measure_inter_div (DensityTheorem.lean), Besicovitch.ae_tendsto_measure_inter_div, Vitali.exists_disjoint_subfamily_covering_enlargement, Measure.haarMeasure_unique, Measure.addHaar_image_linearMap, hausdorffMeasure_apply, Measure.hausdorffMeasure_smul₀, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.extend_real, HasCompactSupport.contDiff_convolution_right and hasFDerivAt_convolution_right. SimonGMT: weighted_area_formula_lipschitz_injOn, area_image_criticalSet_eq_zero, linear_area_formula, euclideanHausdorffMeasure_image_le_of_lipschitzOn, simon_theorem_3_3, simon_theorem_3_6, IsBorelRegularOuterMeasure.simon_theorem_1_17, measurable_rectifiable_purelyUnrectifiable_decomposition, countablyRectifiable_range, simon_theorem_4_14_caratheodory and simon_theorem_4_14_positive_envelope. #print axioms gives [propext, Classical.choice, Quot.sound] for all of them. In the scratch build of the frozen project, all 12 child statements elaborate in the comparator's exact child scope (0 errors). Re-run with standard axioms only: the parent assembly from mass_measure_representation, mass_measure_rectifiable and orientation, the C4-from-C3 reduction, the C5 proof, and the glue lemmas v2_glue_rows, v2_glue_volume and v2_glue_infinite_density. The product-measure instance on Fin (m+1) → Eucl N was confirmed by rfl. No proposed lean_name collides with the 86 names in dag.json. These checks certify the statements, the assembly, the glue and the library inputs, not the new analytic proofs; three independent referees reviewed those (all ACCEPT after the minor fixes, which were applied).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
