<!-- theorem-id: gmt-ch06/root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1 -->

## Theorem `Submission.fiw_tb_top_dim_approx`

Assume MF (as in support_null) and LC: for all P, n, every open U ⊆ ℝ^P, all integer multiplicity T₁, T₂ ∈ D_n(U), integers a, b and S ∈ D_n(U) with S(ω) = aT₁(ω) + bT₂(ω) for every ω, S is integer multiplicity. Let m ∈ ℕ and n := m + 1. Then there is c ∈ [0, ∞) such that for every integer multiplicity X ∈ D_n(ℝ^n) with M(X) < ∞ and M(∂X) < ∞ and every ρ > 0 there are β : LatticeFaceIndex n n → ℝ and Pc, S ∈ D_n(ℝ^n) with: IsLatticeChain ρ β Pc; every β_F an integer; β_F ≠ 0 ⟹ latticeFace ρ F ⊆ cthickening(√n ρ, spt X); |β_F| ρ^n ≤ 2 M(X) for every F; S integer multiplicity; X(ω) − Pc(ω) = S(ω) for every ω; and M(S) ≤ c ρ M(∂X).

Node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/826

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2343, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2375

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3220, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3222, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3229, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3235, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3245, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3256, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3269, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3284

## Lean problem

Declaration: `Submission.fiw_tb_top_dim_approx`

```lean
(∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T₁ T₂ S : GeometricCurrentOn U n) (a b : ℤ), IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω, S ω = (a : ℝ) * T₁ ω + (b : ℝ) * T₂ ω) → IsIntegerMultiplicity S) → ∀ m : ℕ, ∃ c : ℝ≥0, ∀ X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1), IsIntegerMultiplicity X → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ → ∃ (β : LatticeFaceIndex (m + 1) (m + 1) → ℝ) (Pc S : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)), IsLatticeChain ρ β Pc ∧ (∀ F, ∃ k : ℤ, β F = k) ∧ (∀ F, β F ≠ 0 → latticeFace ρ F ⊆ cthickening (Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) X.support) ∧ (∀ F, ENNReal.ofReal (|β F| * ρ ^ (m + 1)) ≤ 2 * X.mass) ∧ IsIntegerMultiplicity S ∧ (∀ ω, X ω - Pc ω = S ω) ∧ S.mass ≤ c * ENNReal.ofReal ρ * X.boundary.mass
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

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2 (a), (c)–(f), i.e. the printed steps (27)–(37) of the proof of Simon 5.1 with Q := X and R := 0, the cubewise Poincaré inequality (32) being used in summed form via the sibling translation_estimate. MF and LC are the frozen statements of the parent's siblings fiw_im_mass_formula and fiw_im_lincomb. Uses the siblings support_null and translation_estimate.

Notation and constants. n = m + 1; ℝ^n = Eucl n; L := volume = μHE[n] on ℝ^n (EuclideanSpace.euclideanHausdorffMeasure_eq_volume). e := (e_0, …, e_m), e_i := EuclideanSpace.single i 1, and η_e(x) := η(x)(e) for an n-form η. Put c := (2√n)^n √n ∈ [0, ∞), which depends only on m. The only order embedding Fin n ↪o Fin n is the identity (it is strictly monotone, hence injective, hence surjective since Fin n is finite, hence an order isomorphism Fin n ≃o Fin n, and that type is a subsingleton; this is not an instance and must be proved), so every face index is F = (z, id) with z ∈ ℤ^n. Write F_z := latticeFace ρ (z, id) = ρ(z + [0, 1]^n) (closed cube) and F̊_z := ρ(z + (0, 1)^n) (open cube). Then latticeFaceAction ρ (z, id) η = ∫_{F_z} η_e dL. The open cubes are pairwise disjoint, ℝ^n ∖ ⋃_z F̊_z ⊆ ⋃_{i,k} {x_i = ρk} is L-null, L(F_z) = ρ^n, L(F_z ∖ F̊_z) = 0 and diam F_z = √n ρ. (Volumes of coordinate boxes in Eucl n are computed with the measure-preserving map WithLp.ofLp : Eucl n → (Fin n → ℝ) (PiLp.volume_preserving_ofLp) and Real.volume_Icc_pi; a coordinate hyperplane {x_i = c} is L-null because its image is a product set with the null factor {c}.) For α ∈ Λ^n(ℝ^n), covectorEuclideanNorm α = |α(e)| (the sum in its definition has the single term I = id).

Fix an integer multiplicity X with M(X) < ∞, Λ := M(∂X) < ∞, and ρ > 0.
1. Density ((27)–(28)). Write X = τ(M, θ, ξ) with IsRectifiableTriple univ n M θ ξ and θ ∈ ℕ on M. Let e* := wedgeCovectors n (fun j => EuclideanSpace.proj j), so e*(e) = 1. Every alternating n-form α on ℝ^n satisfies α(v) = det[v] α(e), where det[v] is the determinant of the coordinate matrix of v (AlternatingMap.eq_smul_basis_det for the standard basis), and an orthonormal frame τ of ℝ^n has det[τ] = ±1 (its matrix Q satisfies QᵀQ = I). So for L-a.e. x ∈ M, ξ(x) = ±simpleNVector τ(x) gives ξ(x)(α) = ε(x) α(e) for all α, where ε(x) := ξ(x)(e*) ∈ {−1, 1}. Define u(x) := ξ(x)(e*) θ(x) for x ∈ M and u(x) := 0 otherwise. θ is a.e.-measurable for L⌞M: by IsRectifiableTriple.integrableOn it is integrable, hence a.e.-strongly measurable, on each M ∩ closedBall(0, k), and M = ⋃_k M ∩ closedBall(0, k). Hence u is a.e.-strongly measurable (ξ and θ are, and M is null-measurable), u takes integer values a.e., and |u| = θ·1_M a.e. Replace u by a Borel representative that is integer-valued everywhere: ũ := Int.cast ∘ round ∘ u₀, where u₀ is a strongly measurable modification of u (AEStronglyMeasurable.mk); ũ = u a.e. because u is integer-valued a.e. All integrals below are unchanged; from now on write u for ũ, so every set {u ≤ k} is measurable and u(x) ∈ ℤ for every x. By MF with U = W = univ, M(X) = ∫⁻_M ofReal θ dL = ∫⁻ ofReal|u| dL < ∞, so u ∈ L¹(L). For every ω ∈ D^n(ℝ^n), X(ω) = ∫_M θ(x) ξ(x)(ω(x)) dL = ∫ u ω_e dL. By the sibling support_null (with MF, U = univ), L(M ∖ spt X) = 0; since u = 0 a.e. off M, u = 0 a.e. outside spt X.
2. Translation estimate. By the sibling translation_estimate applied to X and u: ∫ |u(x + h) − u(x)| dx ≤ ‖h‖ Λ for every h ∈ ℝ^n.
3. Integer medians ((31), (35)). Fix z ∈ ℤ^n and let a_z(k) := L(F_z ∩ {u ≤ k}) for k ∈ ℤ. a_z is nondecreasing, a_z(k) → ρ^n as k → ∞ and a_z(k) → 0 as k → −∞ (continuity of the finite measure L⌞F_z; u is real-valued). So the set {k ∈ ℤ : a_z(k) ≥ ρ^n/2} is nonempty and bounded below; let β_z be its least element. Then (i) L(F_z ∩ {u ≤ β_z}) ≥ ρ^n/2, and (ii) L(F_z ∩ {u ≤ β_z − 1}) < ρ^n/2, hence, as u is integer-valued, L(F_z ∩ {u ≥ β_z}) = ρ^n − L(F_z ∩ {u ≤ β_z − 1}) > ρ^n/2. Consequences:
   (M1) |β_z| ρ^n ≤ 2 ∫_{F_z} |u| dL: if β_z ≥ 1 then |u| ≥ β_z on F_z ∩ {u ≥ β_z}, of measure > ρ^n/2; if β_z ≤ −1 then |u| ≥ |β_z| on F_z ∩ {u ≤ β_z}, of measure ≥ ρ^n/2; if β_z = 0 there is nothing to prove.
   (M2) If β_z ≠ 0 then L(F_z ∩ {u ≠ 0}) > 0: otherwise u = 0 a.e. on F_z, so a_z(0) = ρ^n ≥ ρ^n/2 and a_z(−1) = 0 < ρ^n/2, which gives β_z = 0.
   (M3) For every real c', ∫_{F_z} |u − β_z| ≤ ∫_{F_z} |u − c'|. If c' ≥ β_z: on {u ≤ β_z}, |u − c'| = |u − β_z| + (c' − β_z); on {u > β_z}, |u − c'| ≥ |u − β_z| − (c' − β_z). Integrating over F_z, ∫|u − c'| ≥ ∫|u − β_z| + (c' − β_z)(L(F_z ∩ {u ≤ β_z}) − L(F_z ∩ {u > β_z})) ≥ ∫|u − β_z|, because L(F_z ∩ {u ≤ β_z}) ≥ ρ^n/2 ≥ ρ^n − L(F_z ∩ {u ≤ β_z}) = L(F_z ∩ {u > β_z}) by (i). If c' < β_z the argument is symmetric, using (ii).
   (M4) ∫_{F_z} |u − β_z| ≤ ρ^{−n} ∫_{F_z} ∫_{F_z} |u(x) − u(y)| dy dx: take c' := ū_z := ρ^{−n} ∫_{F_z} u in (M3), and use |u(x) − ū_z| = |ρ^{−n} ∫_{F_z} (u(x) − u(y)) dy| ≤ ρ^{−n} ∫_{F_z} |u(x) − u(y)| dy.
4. Coefficients. Define β(z, id) := β_z (an integer, as a real number). Face condition: if β_z ≠ 0 then by (M2) L(F_z ∩ {u ≠ 0}) > 0; as {u ≠ 0} ∖ M is L-null (u agrees a.e. with a function vanishing off M) and L(M ∖ spt X) = 0, L(F_z ∩ spt X) ≥ L(F_z ∩ {u ≠ 0}) > 0, so there is p ∈ F_z ∩ spt X. Every x ∈ F_z satisfies ‖x − p‖ ≤ diam F_z = √n ρ, so infDist(x, spt X) ≤ √n ρ and F_z ⊆ cthickening(√n ρ, spt X). Coefficient bound: by (M1), |β_z| ρ^n ≤ 2 ∫_{F_z}|u| ≤ 2 ∫|u| = 2 M(X) (step 1), i.e. ofReal(|β(z, id)| ρ^n) ≤ 2 M(X). Moreover Σ_z |β_z| ρ^n ≤ 2 Σ_z ∫_{F_z} |u| = 2 ∫ |u| < ∞, since the cubes overlap only in L-null sets.
5. The chain Pc ((29), (34)). Define v pointwise: v(x) := β_z with z := (⌊x_i/ρ⌋)_i if no coordinate x_i/ρ is an integer (then x ∈ F̊_z), and v(x) := 0 otherwise. Thus v = Σ_z β_z 1_{F̊_z} (at every point at most one term is nonzero); v is Borel measurable (composition of floor maps with a function on the countable set ℤ^n, on a Borel set), integer-valued, and ∫|v| dL = Σ_z |β_z| ρ^n < ∞. For ω ∈ D^n(ℝ^n) put Pc(ω) := ∫ v ω_e dL. Pc is linear. It is sequentially continuous: if ω_j → 0 in D^n(ℝ^n) (TestFormOnConverges), then ω_j → 0 uniformly (0-th derivatives converge uniformly on the common compact set, and ω_j = 0 outside it), and |ω_{j,e}(x)| ≤ ‖ω_j(x)‖ (since ‖e_i‖ = 1), so |Pc(ω_j)| ≤ ‖v‖_{L¹} sup_x |ω_{j,e}(x)| → 0. So Pc ∈ D_n(ℝ^n).
   (a) IsLatticeChain ρ β Pc. Let ω ∈ D^n(ℝ^n) with compact support C. Only finitely many cubes F_z meet C, and for the others latticeFaceAction ρ (z, id) ω = ∫_{F_z} ω_e dL = 0. So Σ'_F β(F) latticeFaceAction ρ F ω is the finite sum Σ_{z : F_z ∩ C ≠ ∅} β_z ∫_{F_z} ω_e dL (tsum_eq_sum) = Σ_{z : F_z ∩ C ≠ ∅} β_z ∫_{F̊_z} ω_e dL = ∫ v ω_e dL (boundaries are null, and ω_e = 0 off C) = Pc(ω).
   (b) Pc is integer multiplicity. Let M_P := ⋃_{z : β_z ≠ 0} F̊_z (open), θ_P := |v|, and ξ_P(x) := sign(v(x)) · simpleNVector e. Triple conditions in univ: M_P ⊆ univ; M_P is open, hence null-measurable; M_P is countably n-rectifiable, being contained in the range of the Lipschitz map id : EuclideanSpace ℝ (Fin n) → Eucl n; θ_P = |β_z| ∈ ℕ ∖ {0} on F̊_z, so θ_P > 0 and θ_P ∈ ℕ on M_P; θ_P ∈ L¹, so θ_P is integrable on M_P ∩ K for every compact K; ξ_P is measurable. Orientation: let x ∈ M_P, say x ∈ F̊_z with β_z ≠ 0, and τ := e (orthonormal; span(range τ) = ⊤). HasWeightedApproximateTangentSpaceAt n M_P θ_P x ⊤: finrank ⊤ = n; for f ∈ C_c(ℝ^n) choose R > 0 with tsupport f ⊆ closedBall(0, R); for 0 < r < infDist(x, ℝ^n ∖ F̊_z)/R and ‖y‖ ≤ R, x + r y ∈ F̊_z ⊆ M_P, so y ∈ blowUpMap x r '' M_P and θ_P(x + r y) = |β_z| = θ_P(x). Since the integrand vanishes off closedBall(0, R), restricting both measures to this ball (Measure.restrict_restrict) gives ∫_{blowUpMap x r '' M_P} f(y) θ_P(x + r y) dL(y) = θ_P(x) ∫ f dL = θ_P(x) ∫_{(⊤ : Set ℝ^n)} f dL for all such r; so the function of r is eventually constant along 𝓝[>] 0, equal to the required limit. And ξ_P(x) = ±simpleNVector τ. Representation: τ(M_P, θ_P, ξ_P)(ω) = ∫_{M_P} |v| sign(v) ω_e dL = ∫ v ω_e dL = Pc(ω), because v = 0 off M_P. So Pc is integer multiplicity.
6. The current S ((34), (38) with R := 0). Define S(ω) := X(ω) − Pc(ω): linear and sequentially continuous (difference of two currents), so S ∈ D_n(ℝ^n), and X(ω) − Pc(ω) = S(ω) for every ω. By LC with U := univ (open), T₁ := X, T₂ := Pc, a := 1, b := −1, S is integer multiplicity.
7. Mass of S ((32), (34)). For every ω, S(ω) = ∫ (u − v) ω_e dL. If ω is admissible for M(S) = S.massOn univ, then |ω_e(x)| = covectorEuclideanNorm(ω(x)) ≤ 1, so S(ω) ≤ ∫ |u − v| dL; hence M(S) ≤ ofReal(∫ |u − v| dL). Since the open cubes cover ℝ^n up to a null set and v = β_z on F̊_z, ∫|u − v| = Σ_z ∫_{F̊_z} |u − β_z| = Σ_z ∫_{F_z} |u − β_z|. By (M4),
   Σ_z ∫_{F_z} |u − β_z| ≤ ρ^{−n} Σ_z ∫∫ 1_{F_z}(x) 1_{F_z}(y) |u(x) − u(y)| dy dx ≤ ρ^{−n} ∫∫ 1_{‖x − y‖ ≤ √n ρ} |u(x) − u(y)| dy dx,
   (all integrands are Borel because u and v are; in particular (x, h) ↦ |u(x + h) − u(x)| is Borel on ℝ^n × ℝ^n, which justifies Tonelli and the change of variables below) because for a.e. x there is exactly one z with x ∈ F_z, and then Σ_{z'} 1_{F_{z'}}(x) 1_{F_{z'}}(y) = 1_{F_z}(y) ≤ 1_{‖x − y‖ ≤ √n ρ} (Tonelli to exchange sum and integrals). Substituting y = x + h (Tonelli and translation invariance of L) and using step 2,
   ρ^{−n} ∫_{‖h‖ ≤ √n ρ} ∫ |u(x + h) − u(x)| dx dh ≤ ρ^{−n} ∫_{‖h‖ ≤ √n ρ} ‖h‖ Λ dh ≤ ρ^{−n} · L(closedBall(0, √n ρ)) · √n ρ Λ ≤ ρ^{−n} (2√n ρ)^n √n ρ Λ = c ρ Λ,
   where L(closedBall(0, r)) ≤ (2r)^n because closedBall(0, r) ⊆ [−r, r]^n (|x_i| ≤ ‖x‖ for x ∈ Eucl n, and the box volume as above). Hence M(S) ≤ ofReal(c ρ Λ) = c · ofReal ρ · M(∂X).
8. β, Pc and S have all the asserted properties (steps 4, 5, 6, 7), and c depends only on m. ∎

Remark (adaptable accepted Lean proof; not needed for the argument above). In step 1, write τ_i = Σ_j ⟨τ_i, e_j⟩ e_j. Then simpleNVector τ = det[⟨τ_i, e_j⟩] • simpleNVector e is the second conjunct of the comparator-accepted Submission.lpf_simple_nvector_algebra (commit d57bd3700c220d24cf66f12e852624be7dd975e4): simpleNVector (fun i => Σ_j B i j • τ j) = B.det • simpleNVector τ. Its Lean proof may be copied under a fresh name.
Further adaptable accepted Lean proof (optional): Submission.br_latticeFace_setIntegral_eq_cube (commit 0561b355216f4041a30f4aaf2a4b139abdf038ca) rewrites the cube integrals ∫_{F_z} η_e dμHE[n] of latticeFaceAction as box integrals over [0, ρ]^n. All library facts cited above (Fubini/Tonelli, translation invariance of L, AlternatingMap.eq_smul_basis_det, PiLp.volume_preserving_ofLp, Real.volume_Icc_pi) are available under the imports of GMT.Ch06.Submission.
Further adaptable accepted Lean proof (optional) for step 1. The comparator-accepted Submission.fiw_ims_frame_sign (DAG node root.flat_iff_weak-a1.im_series-a1.frame_sign-a1, commit c90a40505abdbff33b9174acf9b20037eb2cb2a1) has type: ∀ (P n : ℕ) (τ τ' : Fin n → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ τ' → Submodule.span ℝ (range τ) = Submodule.span ℝ (range τ') → simpleNVector τ' = simpleNVector τ ∨ simpleNVector τ' = -simpleNVector τ. Take P := n, τ := e and τ' := the orthonormal frame τ(x) of the orientation condition. Both spans equal ℝ^n, because an orthonormal family of n vectors in the n-dimensional space ℝ^n is a basis. So simpleNVector τ(x) = ±simpleNVector e; since ξ(x) = ±simpleNVector τ(x), ξ(x) = ±simpleNVector e, i.e. ξ(x)(α) = ±α(e) for every α (simpleNVector_apply). This can replace the determinant computation in step 1; its Lean proof may be copied under a fresh name.

## Key steps

1. X = τ(M, θ, ξ) in ℝ^n has an integer-valued density u ∈ L¹ with X(ω) = ∫ u ω(e), ∫|u| = M(X) (MF), and u = 0 a.e. off spt X (support_null).
2. Integer medians β_z of u on the lattice cubes satisfy |β_z| ρ^n ≤ 2∫_{F_z}|u|, β_z ≠ 0 ⟹ F_z meets spt X, and ∫_{F_z}|u − β_z| ≤ ρ^{−n}∫∫_{F_z×F_z}|u(x) − u(y)|.
3. Pc(ω) := ∫ v ω(e) with v = Σ β_z 1_{F̊_z} is a lattice chain with these coefficients, and it is integer multiplicity (constant density on open cubes).
4. S := X − Pc is integer multiplicity by LC.
5. Summing the cube estimates and applying translation_estimate gives M(S) ≤ ∫|u − v| ≤ (2√n)^n √n ρ M(∂X).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, Mathlib 25730c7c)`
- `python3 scan of dag.json (235 nodes): no lean_name containing fiw_tb; frozen lean_statement of root.flat_iff_weak-a1.im_mass_formula-a1 (accepted) and im_lincomb-a1 compared textually with the MF/LC premises`
- `git log --all --oneline -S fiw_tb_ (687 refs, no match); grep -rl fiw_tb_ .humanize/math-wiki (no match)`
- `git show <commit>:GMT/Ch06/Submission.lean | grep -c 'theorem Submission.<name>' for the 12 cited accepted declarations (all present), including br_la_abs_apply_le_mul_mass @ d771ac3a and fiw_ims_frame_sign @ c90a4050`
- `grep -n max_nodes /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py; read _decompose, _solve_children, _existing_lean_name_problem; swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json (max_nodes 1000, max_children 12, max_depth 6)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def TestFormOnConverges|structure GeometricCurrentOn|zero_apply|boundary_apply|restrictDomain_apply|def testFormOnInclusion|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|abbrev SimonMultiIndex|def CountablyRectifiable|countablyRectifiable_of_measure_zero|def blowUpMap|def HasWeightedApproximateTangentSpaceAt' in SimonGMT Chapter06/Chapter03`
- `grep Mathlib: theorem exists_nnreal_pos_mul_lt, Finite.exists_infinite_fiber, Infinite.exists_ne_map_eq_of_mapsTo, thickening_subset_of_subset, cthickening_subset_of_subset, thickening_subset_cthickening, mul_le_mul_right`
- `lake build GMT.Ch06.Submission in /tmp/tb5-Hq3Nws (git archive d8d46c9, packages linked)`
- `python3 -I /tmp/tb5_tools/gen_challenges.py (verifier/gmt-compare.py child_modules mode contract + lean_contract.validate_lean_statement); lake env lean Scratch/V4/Ch_*.lean and Scratch/V4/Remaining3.lean (0 errors)`
- `lake env lean Scratch/V4/Assembly.lean and Scratch/V4/FiniteNet.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 2028,2090p book/chapter-06.txt (Simon 7.2 and its proof, (1)–(3))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-br-la-abs-apply-le-mul-mass.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-frame-sign.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-im-mass-formula.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Assembly.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/FiniteNet.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Remaining3.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract (IsIntegerMultiplicity, IsRectifiableTriple, tauAction, latticeFace, latticeFaceAction, IsLatticeChain, DeformationTheorem). Neither the project nor SimonGMT has an integer-multiplicity calculus, a flat-norm lemma or a lattice-chain coefficient bound, so these become the 10 children.

SimonGMT supplies the API used in the child proofs:
- massOn and mass via massAdmissibleOn and covectorEuclideanNorm, and le_massOn / massOn_mono;
- restrictDomain(_apply), testFormOnInclusion, zero_apply, boundary_apply and GeometricCurrentOn.ext;
- zeroRegion and support = U \ zeroRegion;
- SimonMultiIndex = Fin n ↪o Fin p, CountablyRectifiable (with countablyRectifiable_of_measure_zero and .mono), blowUpMap and HasWeightedApproximateTangentSpaceAt.
Mathlib supplies ENNReal.exists_nnreal_pos_mul_lt and the thickening lemmas.

Accepted Submission declarations, cited in the remarks as optional reuse pointers, were checked at their commits. The two new pointers are:
- br_la_abs_apply_le_mul_mass (d771ac3a), the evaluation bound;
- fiw_ims_frame_sign (c90a4050), the frame sign.

Scratch checks:
- all 10 child types elaborate in the comparator's exact challenge scope;
- the parent type follows from MF, LC, fiw_tb_finite_net and fiw_tb_flat_sub;
- fiw_tb_finite_net follows from its five siblings;
- both derivations use only [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
