<!-- theorem-id: gmt-ch06/root.deformation-a1.retraction-a1.cube_core-a1 -->

## Theorem `Submission.deformation_retraction_cube_core`

Let m, ℓ ∈ ℕ with ℓ ≥ 1, n := m + 1, d := n + ℓ, C := [0,1]^d ⊂ ℝ^d = Eucl d. There is c₁ = c₁(m,ℓ) ∈ [0,∞) such that for every a ∈ ℝ^d with 1/4 < a_i < 3/4 for all i, writing La := {y ∈ ℝ^d : there is a set J of m + 2 coordinate indices with y_i − a_i ∈ ℤ for all i ∈ J}, there is a map ψ₀ : ℝ^d → ℝ^d such that (α) for every x ∈ C ∖ La, ψ₀(x) ∈ C and there is a set I of exactly ℓ indices with ψ₀(x)_i ∈ {0,1} for i ∈ I; (β) for all x, x′ ∈ C ∖ La with x′_i − x_i ∈ ℤ for all i, ψ₀(x′)_i − ψ₀(x)_i = x′_i − x_i for all i; (γ) for every x ∈ C ∖ La and every ε > 0 there is δ > 0 such that |ψ₀(x′) − ψ₀(x)| ≤ (c₁/dist(x, La) + ε)|x′ − x| for all x′ ∈ C ∖ La with |x′ − x| < δ (dist(x, La) = infDist x La, Euclidean distances).

Node: `root.deformation-a1.retraction-a1.cube_core-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1102

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3593, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3599, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3606, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3614, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3616, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3618, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3620

## Lean problem

Declaration: `Submission.deformation_retraction_cube_core`

```lean
∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ a : Eucl (m + 1 + ℓ), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∃ ψ₀ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ), (∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → (∀ i, 0 ≤ ψ₀ x i ∧ ψ₀ x i ≤ 1) ∧ ∃ I : Finset (Fin (m + 1 + ℓ)), I.card = ℓ ∧ ∀ i ∈ I, ψ₀ x i = 0 ∨ ψ₀ x i = 1) ∧ (∀ x x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → (∀ i, ∃ k : ℤ, x' i - x i = k) → ∀ i, ψ₀ x' i - ψ₀ x i = x' i - x i) ∧ ∀ x : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x i ∧ x i ≤ 1) → x ∉ La → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' : Eucl (m + 1 + ℓ), (∀ i, 0 ≤ x' i ∧ x' i ≤ 1) → x' ∉ La → dist x' x < δ → dist (ψ₀ x') (ψ₀ x) ≤ (c₁ / infDist x La + ε) * dist x' x
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

- Parent DAG node: `root.deformation-a1.retraction-a1`
- Child DAG node: `root.deformation-a1.retraction-a1.cube_core-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Lemma 5.4, printed proof pp. 161–163 (radial retractions ψ_F, displays (1)–(8), the composite ψ₀ = ψ^{(n+1)}∘⋯∘ψ^{(n+ℓ)}, its translation property, and claim (3) proved by induction), as reproduced in Steps 1–4 of the parent proof, with the parent's errata: the book's k is ℓ; the printed “|y − a| ≥ 3/4” before (6) is replaced by the correct similarity bound 6.2 below (constant 1/4); the a.e. bound on |Dψ| is replaced by the pointwise upper Lipschitz constant, written here as “K-Lipschitz at x within A”. The printed induction on ℓ applies the lemma to the faces of C (a j-face F is an (n + (j − n))-dimensional cube in its affine hull Π_F, L ∩ F = F ∩ L̃_F where L̃_F := {w ∈ Π_F : #{i free in F : w_i − a_i ∈ ℤ} ≥ n + 1} is the dual skeleton of F, by 1(d), and on F ∖ L the composite ψ₀ is that cube's composite map, because the maps ψ^{(j′)} with j′ > dim F fix every point of F by (c1),(c2)); below it is written out directly as an induction over the dimension j of the faces of C inside ℝ^d, with distances measured to L itself instead of to L̃_F. Since L̃_F ⊆ L, the resulting induction hypothesis P(j − 1) is weaker than the printed one; the extra first case of the similarity bound 6.2 (planes using a fixed coordinate of the face) compensates, and re-embedding faces into lower-dimensional spaces is avoided. Only 1/4 < a_i < 3/4 is used about a.

0. Notation. n := m + 1, d := n + ℓ ≥ n + 1, C := [0,1]^d, |·| is the Euclidean norm of ℝ^d = Eucl d, L := La, and d_a(x) := dist(x, L) = inf_{w∈L} |x − w| (this is infDist x La). For A ⊆ ℝ^d, a map f defined on A, x ∈ A and K ≥ 0, say that f is K-Lipschitz at x within A if for every ε > 0 there is δ > 0 with |f(x′) − f(x)| ≤ (K + ε)|x′ − x| for all x′ ∈ A with |x′ − x| < δ (i.e. limsup_{x′→x, x′∈A} |f(x′) − f(x)|/|x′ − x| ≤ K). This property persists if K is increased or A is shrunk (to a subset still containing x), and conclusion (γ) says exactly that ψ₀ is (c₁/d_a(x))-Lipschitz at x within C ∖ L. Put β := 1 + 4√d, c₁(n+1) := β√d, c₁(j) := 4√d·β·c₁(j−1) for n + 2 ≤ j ≤ d, and c₁ := c₁(d) = β√d·(4√d·β)^{ℓ−1} ≥ 0; it depends only on m and ℓ, and is fixed before a. (The ambient √d and β are used at every face dimension, so c₁ differs numerically from the parent's c₁(n, ℓ) of Step 4; only its existence matters.) Fix a with 1/4 < a_i < 3/4 for all i, and La as in the statement.

1. Elementary facts.
(a) For all i, all k ∈ ℤ and all b ∈ {0,1}: |b − (a_i + k)| > 1/4. For all i, all k ∈ ℤ ∖ {0} and all s ∈ [0,1]: |s − (a_i + k)| > 1/4. Proof: a_i + k ∈ (k + 1/4, k + 3/4), whose points are at distance > 1/4 from every integer. If k ≥ 1 then a_i + k > 5/4 ≥ s + 1/4; if k ≤ −1 then a_i + k < −1/4 ≤ s − 1/4.
(b) L is closed and a ∈ L; hence d_a(x) > 0 for x ∉ L, and d_a(x) ≤ |x − w| for every w ∈ L. Proof: {y : y_i − a_i ∈ ℤ} is the preimage of the closed set ℤ ⊂ ℝ under the continuous map y ↦ y_i − a_i, and L = ⋃_{|J| = n+1} ⋂_{i∈J} {y : y_i − a_i ∈ ℤ} is a finite union of finite intersections of closed sets. Since n + 1 ≤ d there is a J with |J| = n + 1, and a_i − a_i = 0 ∈ ℤ, so a ∈ L. A point outside a closed nonempty set has positive distance to it.
(c) Faces. For J ⊆ {1,…,d} and e = (e_i)_{i∉J} with e_i ∈ {0,1}, put F_{J,e} := {x ∈ C : x_i = e_i for all i ∉ J}; these are the faces of C, J is the set of free coordinates and dim F_{J,e} := |J|; C is the only face of dimension d. Each face is closed. For F = F_{J,e}: relint F := {x ∈ F : 0 < x_i < 1 for all i ∈ J}, ∂F := F ∖ relint F = {x ∈ F : x_i ∈ {0,1} for some i ∈ J}. The centre a_F is given by (a_F)_i := a_i (i ∈ J), (a_F)_i := e_i (i ∉ J) (the orthogonal projection of a onto the affine hull of F); a_F ∈ relint F.
 (c1) Carrier. For x ∈ C put J(x) := {i : 0 < x_i < 1} and F(x) := F_{J(x),(x_i)_{i∉J(x)}} (note x_i ∈ {0,1} for i ∉ J(x)). Then x ∈ relint F(x) and dim F(x) = |J(x)|.
 (c2) If x ∈ F = F_{J,e} then J(x) ⊆ J; if |J(x)| < |J| then x ∈ ∂F; if |J(x)| = |J| then F(x) = F. Proof: for i ∉ J, x_i = e_i ∈ {0,1}, so i ∉ J(x). If J(x) ⊊ J, an index i ∈ J ∖ J(x) has x_i ∈ {0,1}, so x ∈ ∂F. If |J(x)| = |J| then J(x) = J and e_i = x_i for i ∉ J.
 (c3) If |J| = j ≥ 1, then ∂F_{J,e} is the union of the 2j faces F_{J∖{i}, e∪{i↦b}} (i ∈ J, b ∈ {0,1}), each of dimension j − 1, closed and contained in F_{J,e} (by the definition of ∂F); every y ∈ ∂F_{J,e} has dim F(y) = |J(y)| ≤ j − 1 (by (c1),(c2): J(y) ⊆ J and some i ∈ J has y_i ∈ {0,1}).
 (c4) |x − y| ≤ √d for all x, y ∈ C.
(d) L inside a face (printed (1),(2)). Let F = F_{J,e} and x ∈ F. Then x ∈ L iff #{i ∈ J : x_i = a_i} ≥ n + 1. Proof: for i ∉ J, x_i − a_i = e_i − a_i ∉ ℤ by (a); for i ∈ J, x_i − a_i ∈ [−a_i, 1 − a_i] ⊂ (−3/4, 3/4), which is an integer iff it is 0. So a set J′ of n + 1 indices witnesses x ∈ L iff J′ ⊆ {i ∈ J : x_i = a_i}. Consequences:
 (d1) if dim F ≥ n + 1 then a_F ∈ L (indeed, as printed, the whole segment from a to a_F lies in L);
 (d2) if x ∈ F, λ > 0 and x^λ := a_F + λ(x − a_F) ∈ F, then x^λ ∈ L iff x ∈ L, because x^λ_i − a_i = λ(x_i − a_i) for i ∈ J;
 (d3) if dim F ≥ n + 1 and x ∈ F ∖ L, then x ≠ a_F and d_a(x) ≤ |x − a_F| (by (d1) and (b)).

2. The radial retraction ψ_F (printed definition, and printed (8)). Let F = F_{J,e} with j := |J| ≥ n + 1. For v ∈ ℝ^d put N_J(v) := max_{i∈J} max{v_i/(1 − a_i), −v_i/a_i}.
 (N1) N_J(λv) = λ·N_J(v) for λ ≥ 0.
 (N2) |N_J(v) − N_J(w)| ≤ 4|v − w|: each of v ↦ v_i/(1 − a_i) and v ↦ −v_i/a_i is Lipschitz with constant 1/(1 − a_i) < 4, resp. 1/a_i < 4 (as |v_i − w_i| ≤ |v − w|), and a maximum of finitely many 4-Lipschitz functions is 4-Lipschitz.
 (N3) Let x ∈ ℝ^d with x_i = e_i for i ∉ J, and v := x − a_F. Then x ∈ F iff N_J(v) ≤ 1; for x ∈ F, x ∈ ∂F iff N_J(v) = 1; and N_J(v) > 0 if x ≠ a_F. Proof: for i ∈ J, v_i = x_i − a_i, so x_i ≤ 1 iff v_i/(1 − a_i) ≤ 1, with equality iff x_i = 1, and x_i ≥ 0 iff −v_i/a_i ≤ 1, with equality iff x_i = 0. If x ≠ a_F, some i ∈ J has v_i ≠ 0, and then one of v_i/(1 − a_i), −v_i/a_i is positive.
 Definition. For x ∈ F ∖ {a_F}: ψ_F(x) := a_F + (x − a_F)/N_J(x − a_F); in coordinates ψ_F(x)_i = a_i + (x_i − a_i)/N_J(x − a_F) for i ∈ J and ψ_F(x)_i = x_i = e_i for i ∉ J.
 (R1) Let x ∈ F ∖ {a_F} and t := 1/N_J(x − a_F). Then t ≥ 1, ψ_F(x) = a_F + t(x − a_F) ∈ ∂F, ψ_F(x)_i = x_i for i ∉ J, and |ψ_F(x) − a_F| = t|x − a_F|. (By (N1),(N3): N_J(ψ_F(x) − a_F) = 1, while N_J(x − a_F) ≤ 1 because x ∈ F.) Thus ψ_F is the printed radial retraction of F ∖ {a_F} onto ∂F with origin a_F: x lies on the segment from a_F to ψ_F(x).
 (R2) ψ_F(x) = x for x ∈ ∂F (then N_J(x − a_F) = 1; note a_F ∉ ∂F).
 (R3) ψ_F maps F ∖ L into ∂F ∖ L: for x ∈ F ∖ L, x ≠ a_F by (d3), ψ_F(x) ∈ ∂F by (R1), and ψ_F(x) = x^t ∉ L by (d2).
 (R4) (printed (8)) For x ∈ F ∖ {a_F} and t := 1/N_J(x − a_F), ψ_F is βt-Lipschitz at x within F ∖ {a_F}. Proof: let v := x − a_F and ν := N_J(v) = 1/t. For x′ ∈ F with |x′ − x| < ν/8 put w := x′ − a_F; by (N2), N_J(w) ≥ ν − 4|x′ − x| > ν/2 > 0, so x′ ≠ a_F, and
  ψ_F(x′) − ψ_F(x) = w/N_J(w) − v/ν = (w − v)/N_J(w) + (v/ν)·(ν − N_J(w))/N_J(w).
 Since |v/ν| = |ψ_F(x) − a_F| ≤ √d by (c4), |w − v| = |x′ − x| and |ν − N_J(w)| ≤ 4|x′ − x|, this gives |ψ_F(x′) − ψ_F(x)| ≤ β|x′ − x|/N_J(w); moreover 1/N_J(w) = t + (ν − N_J(w))/(ν·N_J(w)) ≤ t + 8t²|x′ − x|. Given ε > 0, δ := min{ν/8, ε/(8βt²)} yields |ψ_F(x′) − ψ_F(x)| ≤ (βt + ε)|x′ − x| for all x′ ∈ F with |x′ − x| < δ (all such x′ differ from a_F).
 (R5) For x ∈ F ∖ L: t = |ψ_F(x) − a_F|/|x − a_F| ≤ √d/|x − a_F| ≤ √d/d_a(x), by (R1), (c4) and (d3).

3. The composite ψ₀ (printed construction). For n + 1 ≤ j ≤ d and x ∈ C ∖ L with dim F(x) ≤ j put ψ^{(j)}(x) := ψ_{F(x)}(x) if dim F(x) = j, and ψ^{(j)}(x) := x if dim F(x) < j. This is the printed map “ψ^{(j)} := ψ_F on F ∖ {a_F} for every j-face F”, restricted to C ∖ L: if x lies in a j-face F with x ≠ a_F, then either dim F(x) = j and F(x) = F, or dim F(x) < j, x ∈ ∂F and ψ_F(x) = x (by (c2),(R2)); so the printed definition does not depend on the choice of F. When dim F(x) = j ≥ n + 1, x ≠ a_{F(x)} by (d3). By (R1),(R3),(c3), ψ^{(j)} maps {x ∈ C ∖ L : dim F(x) ≤ j} into {x ∈ C ∖ L : dim F(x) ≤ j − 1}. Hence
  ψ₀ := ψ^{(n+1)} ∘ ψ^{(n+2)} ∘ ⋯ ∘ ψ^{(d)}
 is defined on C ∖ L and maps C ∖ L into {y ∈ C ∖ L : dim F(y) ≤ n}; put ψ₀(x) := x for x ∉ C ∖ L (these values play no role).
 Equivalent one-step form (convenient for formalization). Define R : ℝ^d → ℝ^d by R(y) := ψ_{F(y)}(y) if y ∈ C ∖ L and |J(y)| ≥ n + 1, and R(y) := y otherwise; explicitly, for y ∈ C ∖ L with J := J(y), |J| ≥ n + 1, N(y) := max_{i∈J} max{(y_i − a_i)/(1 − a_i), (a_i − y_i)/a_i} > 0 and R(y)_i = a_i + (y_i − a_i)/N(y) (i ∈ J), R(y)_i = y_i (i ∉ J). Then ψ₀ = R^ℓ on C ∖ L: each ψ^{(j)} acts as R on points of carrier dimension j and as the identity on points of smaller carrier dimension, each non-trivial application lowers the carrier dimension by at least one, R fixes points of carrier dimension ≤ n, and at most ℓ = d − n non-trivial applications occur; so both ψ₀(x) and R^ℓ(x) equal the point obtained from x by applying R until the carrier dimension is ≤ n. Either definition may be used below. Two structural facts:
 (S1) If x ∈ C ∖ L and dim F(x) ≤ n, then ψ₀(x) = x (every ψ^{(j)}, j ≥ n + 1, fixes x; equivalently R fixes x).
 (S2) If F is a face with j := dim F ≥ n + 1 and x ∈ F ∖ L, then ψ₀(x) = ψ₀(ψ_F(x)). Proof: if x ∈ ∂F then ψ_F(x) = x. Otherwise x ∈ relint F, so |J(x)| = |J| and F(x) = F by (c1),(c2); ψ^{(d)},…,ψ^{(j+1)} fix x and ψ^{(j)}(x) = ψ_F(x) =: y, so ψ₀(x) = ψ^{(n+1)}∘⋯∘ψ^{(j−1)}(y) (= y if j = n + 1). Since dim F(y) ≤ j − 1 by (c3), ψ^{(d)},…,ψ^{(j)} fix y, so ψ₀(y) = ψ^{(n+1)}∘⋯∘ψ^{(j−1)}(y) = ψ₀(x). (In the R-form: R(x) = ψ_F(x) = y, and since dim F(y) ≤ d − 1, at most ℓ − 1 non-trivial applications of R occur from y, so R^ℓ(y) = R^{ℓ−1}(y) = R^ℓ(x).)

4. Proof of (α). For x ∈ C ∖ L, y := ψ₀(x) ∈ C and |J(y)| = dim F(y) ≤ n, so at least d − n = ℓ coordinates of y lie in [0,1] ∖ (0,1) = {0,1}; let I be a set of exactly ℓ of these indices.

5. Proof of (β) (printed translation property). Let x, x′ ∈ C with z := x′ − x ∈ ℤ^d. Then z_i ∈ {−1, 0, 1}; if 0 < x_i < 1 then x_i + z_i ∈ [0,1] forces z_i = 0, and symmetrically for x′. Hence J(x) = J(x′) =: J, z_i = 0 for i ∈ J, F(x′) = z + F(x), a_{F(x′)} = z + a_{F(x)}, and both faces have the same gauge N_J. Claim B(k), n ≤ k ≤ d: ψ₀(x′) − ψ₀(x) = x′ − x for all x, x′ ∈ C ∖ L with x′ − x ∈ ℤ^d and dim F(x) ≤ k. B(n) holds by (S1), since dim F(x′) = dim F(x) ≤ n. Let n + 1 ≤ k ≤ d, assume B(k − 1), and let dim F(x) = k (if dim F(x) < k, B(k − 1) applies). With F := F(x) and F′ := F(x′) we have x′ − a_{F′} = x − a_F, hence ψ_{F′}(x′) = ψ_F(x) + z. The points u := ψ_F(x) and u′ := ψ_{F′}(x′) = u + z lie in C ∖ L by (R3), and dim F(u) ≤ k − 1 by (c3), so B(k − 1) gives ψ₀(u′) − ψ₀(u) = z. By (S2), ψ₀(x) = ψ₀(u) and ψ₀(x′) = ψ₀(u′). Hence ψ₀(x′) − ψ₀(x) = z = x′ − x. B(d), read coordinatewise, is (β).

6. Proof of (γ) (printed claim (3)).
 6.1 Two rules. (Composition) If f : A → B is K₁-Lipschitz at x within A and g (defined on B) is K₂-Lipschitz at f(x) within B, with K₁, K₂ ≥ 0, then g ∘ f is K₁K₂-Lipschitz at x within A: given ε > 0 choose η ∈ (0,1] with η(K₁ + K₂ + 1) ≤ ε, δ₁ for f and δ₂ for g with this η, and δ := min{δ₁, δ₂/(K₁ + η)}; for x′ ∈ A with |x′ − x| < δ we get |f(x′) − f(x)| ≤ (K₁ + η)|x′ − x| < δ₂ and |g(f(x′)) − g(f(x))| ≤ (K₂ + η)(K₁ + η)|x′ − x| ≤ (K₁K₂ + ε)|x′ − x|. (Union) Let G₁,…,G_r ⊆ ℝ^d be closed and nonempty, B := (G₁ ∪ ⋯ ∪ G_r) ∖ L, y ∈ B, and suppose g is K-Lipschitz at y within G_k ∖ L for every k with y ∈ G_k. Then g is K-Lipschitz at y within B: put η := min{dist(y, G_k) : y ∉ G_k} > 0 (η := 1 if there is no such k); given ε > 0 let δ_k be the radii for the k with y ∈ G_k and δ := min{η, min_k δ_k}; a point y′ ∈ B with |y′ − y| < δ lies in some G_k, which must contain y, and then |g(y′) − g(y)| ≤ (K + ε)|y′ − y|.
 6.2 Similarity bound (printed (4)–(7), corrected). Let F = F_{J,e} be a face, x, y ∈ F and t > 0 with y − a_F = t(x − a_F) (it is used with t ≥ 1; only y ∈ F is actually needed). Then d_a(y) ≥ min{1/4, t·d_a(x)}. Proof: let w ∈ L, with a set J′ of n + 1 indices and integers k_i such that w_i = a_i + k_i for i ∈ J′. If some i ∈ J′ is not in J, then y_i = e_i ∈ {0,1} and |y − w| ≥ |y_i − w_i| > 1/4 by 1(a). If J′ ⊆ J and k_i ≠ 0 for some i ∈ J′, then y_i ∈ [0,1] and |y − w| ≥ |y_i − w_i| > 1/4 by 1(a). If J′ ⊆ J and all k_i = 0, put w′ := a_F + (w − a_F)/t; for i ∈ J′ ⊆ J, w′_i = a_i + (a_i − a_i)/t = a_i, so w′ ∈ L, and y − w = t(x − a_F) − (w − a_F) = t(x − w′), so |y − w| = t|x − w′| ≥ t·d_a(x). Hence |y − w| ≥ min{1/4, t·d_a(x)} for all w ∈ L, and since L ≠ ∅ the claim follows.
 6.3 Claim P(j), for n + 1 ≤ j ≤ d: for every face F of dimension j and every x ∈ F ∖ L, ψ₀ is (c₁(j)/d_a(x))-Lipschitz at x within F ∖ L. (P(j) is the analogue of the printed claim (3) for the j-dimensional cube F, with distances measured to L instead of to the dual skeleton of F.)
 6.4 Base j = n + 1 (the printed case ℓ = 1). Let dim F = n + 1 and x ∈ F ∖ L. For x′ ∈ F ∖ L, ψ_F(x′) ∈ ∂F ∖ L has carrier dimension ≤ n by (c3), so ψ₀(x′) = ψ₀(ψ_F(x′)) = ψ_F(x′) by (S2),(S1). Thus ψ₀ = ψ_F on F ∖ L, and by (R4) (restricted to F ∖ L ⊆ F ∖ {a_F}) and (R5), ψ₀ is βt-Lipschitz at x within F ∖ L with βt ≤ β√d/d_a(x) = c₁(n+1)/d_a(x).
 6.5 Induction step (printed), n + 2 ≤ j ≤ d. Assume P(j − 1). Let F = F_{J,e} with |J| = j, x ∈ F ∖ L, y := ψ_F(x) and t := 1/N_J(x − a_F) ≥ 1; then y − a_F = t(x − a_F) and y ∈ ∂F ∖ L by (R1),(R3).
  (i) ψ_F maps F ∖ L into ∂F ∖ L and is K₁ := βt-Lipschitz at x within F ∖ L, by (R3),(R4).
  (ii) ∂F ∖ L = (G₁ ∪ ⋯ ∪ G_{2j}) ∖ L for the closed (j − 1)-faces G_k ⊆ F of (c3). For each G_k containing y, P(j − 1) says that ψ₀ is (c₁(j − 1)/d_a(y))-Lipschitz at y within G_k ∖ L (d_a(y) > 0 by 1(b)). By the union rule, ψ₀ is K₂ := c₁(j − 1)/d_a(y)-Lipschitz at y within ∂F ∖ L.
  (iii) By (S2), ψ₀ = ψ₀ ∘ ψ_F on F ∖ L, so by the composition rule (the printed chain rule) ψ₀ is K₁K₂-Lipschitz at x within F ∖ L.
  (iv) By 6.2, d_a(y) ≥ min{1/4, t·d_a(x)}. If t·d_a(x) ≤ 1/4, then K₁K₂ ≤ βt·c₁(j − 1)/(t·d_a(x)) = β·c₁(j − 1)/d_a(x) ≤ c₁(j)/d_a(x), as 4√d ≥ 1. Otherwise K₁K₂ ≤ 4βt·c₁(j − 1) ≤ 4β√d·c₁(j − 1)/d_a(x) = c₁(j)/d_a(x), by (R5). Hence P(j).
 6.6 Conclusion. P(d) for the unique d-face C says that for every x ∈ C ∖ L, ψ₀ is (c₁/d_a(x))-Lipschitz at x within C ∖ L with c₁ = c₁(d); unwinding the definition (with d_a(x) = infDist x La and |·| = dist) this is (γ). Together with (α), (β), and since c₁ = β√d(4√dβ)^{ℓ−1} ≥ 0 does not depend on a, the theorem is proved. ∎

## Key steps

1. Elementary facts: a_i + ℤ is 1/4-separated from {0,1} and a_i + (ℤ∖{0}) from [0,1]; La is closed and contains a; faces F_{J,e}, carrier faces F(x), relative boundaries; La ∩ F = {x ∈ F : #{i ∈ J : x_i = a_i} ≥ n+1}, a_F ∈ La, cone property (printed (1),(2)).
2. Gauge N_J (positively homogeneous, 4-Lipschitz) and radial retraction ψ_F : F ∖ La → ∂F ∖ La, which is (1+4√d)t-Lipschitz at x with t = 1/N_J(x − a_F) ≤ √d/d_a(x) (printed (8)).
3. Composite ψ₀ = ψ^{(n+1)}∘⋯∘ψ^{(d)} on C ∖ La (equivalently R^ℓ for the one-step carrier retraction R); (S1) identity on carrier dimension ≤ n; (S2) ψ₀ = ψ₀∘ψ_F on F ∖ La for faces of dimension ≥ n+1; hence (α).
4. (β): translation compatibility by induction on the carrier dimension (printed remark).
5. Similarity bound d_a(y) ≥ min{1/4, t·d_a(x)} for y − a_F = t(x − a_F) in a face (printed (4)–(7), corrected).
6. (γ): induction over face dimension j = n+1,…,d (the printed induction on ℓ): base from the radial estimate; step by the composition and union rules over the (j−1)-faces through y; c₁(j) = 4√d(1+4√d)c₁(j−1), c₁ = c₁(d) independent of a.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d; workspace HEAD = d8d46c9, lake-manifest mathlib 25730c7c, simongmt 2b366308)`
- `cmp project/GMT/Ch06/Contract.lean <workspace>/GMT/Ch06/Contract.lean; cmp <workspace>/GMT/Ch06/Submission.lean <workspace>/GMT/Ch06/Contract.lean (both byte-identical)`
- `sha256 of the handoff natural_proof = f9b0bcb279bf1f28ada1344b4844ae5656e9881b857082eece03bd18e8da3a36 (= proof_sha256 of decomposition-scope-v1.json; also contained verbatim in parent-supplied-natural-proof.md)`
- `rg -n -i 'retract|radial|gauge|skeleton' project/GMT (only Ch04 normalRadialSq; no cubical or radial retraction, no skeleton lemma)`
- `rg -n 'deformation_retraction_' project .lake/packages/simongmt/Poincare; grep -rn 'deformation_retraction_' GMT .lake/packages/simongmt/Poincare (no match)`
- `rg -l -i 'retraction|radialRetraction' .lake/packages/simongmt/Poincare (only unrelated Chapter08 ConstancyNormalCharts/PolarNorm/ConstancyRemarks)`
- `rg -n 'abbrev SimonMultiIndex' simongmt Poincare/SimonGMT/Chapter06 (FormsDuality.lean:22, Fin n ↪o Fin p)`
- `rg -n 'theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary' mathlib/Mathlib/Analysis/Calculus/MeanValue.lean (line 223)`
- `rg -n 'def orderEmbOfFin|theorem range_orderEmbOfFin' mathlib/Mathlib/Data/Finset/Sort.lean (194, 216)`
- `rg -n 'theorem infDist_image|theorem infDist_le_infDist_add_dist|theorem infDist_zero_of_mem|lemma le_infDist|theorem lipschitz_infDist_pt' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean (596, 518, 492, 508, 547)`
- `rg -n 'of_dist_le_mul' mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean (57); grep -n nhdsLE_sup_nhdsGE mathlib/Mathlib/Topology/Order/LeftRight.lean (97); grep -n 'lt_floor_add_one|floor_intCast' mathlib/Mathlib/Algebra/Order/Floor/Ring.lean (128, 164); grep -n dist_eq mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (158)`
- `python3 over dag.json (263 nodes): the five proposed deformation_retraction_* names vs all lean_name reservations (no collision); no existing node has a reusable identical statement`
- `sed -n '1440,1680p' book/chapter-06.txt (printed Lemma 5.4 and its proof, pp. 160–163)`
- `cat nodes/root-deformation-a1-retraction-a1/decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json (prior accepted five-child proposal of attempt 1; its /tmp scratch files no longer exist, so every check was re-run)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope on the five lean_statements (all valid; NodeChallenge scope replayed)`
- `lake env lean /tmp/retraction-a2-scratch/stmts/NC_<key>.lean for the five keys (exit 0; only the expected sorry warning)`
- `lake env lean /tmp/retraction-a2-scratch/Assembly.lean (skeleton_mem, cube_core, periodic_extension, globalize types ⇒ parent type; #print axioms = [propext, Classical.choice, Quot.sound])`
- `lake env lean /tmp/retraction-a2-scratch/AllProofs.lean (complete proofs of dini_segment, skeleton_mem, periodic_extension, globalize against the exact frozen strings, and deformation_retraction_of_cube_core : cube_core type → parent type; all axioms [propext, Classical.choice, Quot.sound])`
- `python3 -I /tmp/retraction-a2-scratch/numeric/stress.py and stress_nearL.py (numeric stress test of ψ₀ = R^ℓ for (m,ℓ) up to (2,2), (1,3), (0,4), (3,1): (α), (β) and the similarity bound hold; ratio·dist(x, La) ≤ 5 ≪ c₁)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/PolarNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/LeftRight.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Floor/Ring.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/retraction-a2-scratch/stmts/statements.json`
- `/tmp/retraction-a2-scratch/stmts/NC_cube_core.lean`
- `/tmp/retraction-a2-scratch/Assembly.lean`
- `/tmp/retraction-a2-scratch/AllProofs.lean`
- `/tmp/retraction-a2-scratch/proofs/DiniSkeleton.lean`
- `/tmp/retraction-a2-scratch/proofs/Periodic.lean`
- `/tmp/retraction-a2-scratch/proofs/Globalize.lean`
- `/tmp/retraction-a2-scratch/numeric/stress.py`
- `/tmp/retraction-a2-scratch/numeric/stress_nearL.py`

The pinned revisions are confirmed, and the frozen Contract (= Submission) is byte-identical to the snapshot. The handoff proof matches the frozen proof_sha256. Neither the project nor SimonGMT contains a cubical or radial retraction or a lattice-skeleton lemma; the only relevant declarations are the frozen latticeFace/LatticeFaceIndex, with SimonMultiIndex = Fin n ↪o Fin p. Lemma 5.4 is therefore built from pinned Mathlib primitives: the fencing theorem or a sup argument (dini_segment), Finset.orderEmbOfFin/range_orderEmbOfFin and Int.floor (skeleton_mem), IsometryEquiv.subRight with Metric.infDist_image (periodic_extension), and LipschitzOnWith.of_dist_le_mul, infDist_le_infDist_add_dist and nhdsLE_sup_nhdsGE (globalize). All five child types pass validate_lean_statement and elaborate in the exact comparator challenge scope. dini_segment, skeleton_mem, periodic_extension and globalize were fully proved in scratch against the exact frozen strings. The parent type was kernel-checked from the cube_core type plus those four, with axioms [propext, Classical.choice, Quot.sound], so cube_core is the only open obligation; it is supported by numeric stress tests and an independent line-by-line review. The five names collide with none of the 263 DAG reservations or with any project/SimonGMT declaration. No Matrix/IsUnit construction occurs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
