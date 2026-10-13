<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.im_closure-a1.tangent_overlap-a1 -->

## Theorem `Submission.iwl_imc_tangent_overlap`

Let P, k ∈ ℕ and Hᵏ := μHE[k] on ℝ^P = Eucl P. Assume (TL), the frozen statement of iwl_weighted_tangent_locality specialized to P and k: for all Hᵏ-null-measurable M, M′ ⊆ ℝ^P, all θ, θ′ : ℝ^P → ℝ and every x with θ(x) = θ′(x), if for some ρ > 0 θ is Hᵏ-integrable on M ∩ B̄_ρ(x) and θ′ on M′ ∩ B̄_ρ(x), and r^{−k}·∫⁻_{B̄_{Rr}(x)} |1_Mθ − 1_{M′}θ′| dHᵏ → 0 as r ↓ 0 for every R > 0, then for every linear subspace Q of ℝ^P, HasWeightedApproximateTangentSpaceAt k M θ x Q ↔ HasWeightedApproximateTangentSpaceAt k M′ θ′ x Q (Simon Ch. 3, 1.7). Then for every open U ⊆ ℝ^P, all Hᵏ-null-measurable M₁, M₂ ⊆ U and all θ₁, θ₂ : ℝ^P → ℝ with θ_l(x) ≥ 1 for x ∈ M_l and θ_l Hᵏ-integrable on M_l ∩ K for every compact K ⊆ U (l = 1, 2): for Hᵏ⌞(M₁ ∩ M₂)-almost every x, every Q with HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q also satisfies HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q.

Node: `root.integrality_weak_limits-a1.im_closure-a1.tangent_overlap-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/940

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2799, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2814

Decomposition children: None

## Lean problem

Declaration: `Submission.iwl_imc_tangent_overlap`

```lean
∀ (P k : ℕ), (∀ (M M' : Set (Eucl P)) (θ θ' : Eucl P → ℝ) (x : Eucl P), NullMeasurableSet M (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M' (μHE[k] : Measure (Eucl P)) → θ x = θ' x → (∃ ρ : ℝ, 0 < ρ ∧ IntegrableOn θ (M ∩ closedBall x ρ) (μHE[k] : Measure (Eucl P)) ∧ IntegrableOn θ' (M' ∩ closedBall x ρ) (μHE[k] : Measure (Eucl P))) → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ENNReal.ofReal ((r ^ k)⁻¹) * ∫⁻ z in closedBall x (R * r), ‖M.indicator θ z - M'.indicator θ' z‖ₑ ∂(μHE[k] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Q ↔ HasWeightedApproximateTangentSpaceAt k M' θ' x Q) → ∀ U : Set (Eucl P), IsOpen U → ∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl P)) → (∀ x ∈ M₁, 1 ≤ θ₁ x) → (∀ x ∈ M₂, 1 ≤ θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q
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

- Parent DAG node: `root.integrality_weak_limits-a1.im_closure-a1`
- Child DAG node: `root.integrality_weak_limits-a1.im_closure-a1.tangent_overlap-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions.
- ℝ^P := Eucl P and H := Hᵏ := μHE[k]. B̄_s(x) := closedBall x s.
- ‖t‖ₑ = |t| ∈ [0, ∞] for t ∈ ℝ. For r > 0, ofReal((r^k)⁻¹) = r^{−k}.
- HasWATS k M θ x Q abbreviates HasWeightedApproximateTangentSpaceAt k M θ x Q. By definition this means: finrank Q = k, and for every f ∈ C_c(ℝ^P, ℝ),
  ∫_{η_{x,r}(M)} f(y)·θ(x + r•y) dH(y) → θ(x)·∫_Q f dH as r ↓ 0, where η_{x,r}(y) = r⁻¹•(y − x) (blowUpMap).
- "const c" is the constant function y ↦ c. 1_A is the indicator of A. M₁ Δ M₂ := (M₁ ∖ M₂) ∪ (M₂ ∖ M₁) (symmDiff).

The hypothesis (TL) is the frozen statement of the parent's dependency `iwl_weighted_tangent_locality`, specialized to P and k. For H-null-measurable M, M′, functions θ, θ′ and a point x with θ(x) = θ′(x), suppose:
- there is ρ > 0 with θ H-integrable on M ∩ B̄_ρ(x) and θ′ H-integrable on M′ ∩ B̄_ρ(x); and
- for every R > 0, r^{−k} ∫⁻_{B̄_{Rr}(x)} ‖1_Mθ − 1_{M′}θ′‖ₑ dH → 0 as r ↓ 0.
Then HasWATS k M θ x Q ⟺ HasWATS k M′ θ′ x Q for every subspace Q. The parent discharges (TL) with `Submission.iwl_weighted_tangent_locality P k`.

Source. This is steps 1–2 of part (c) of the parent proof: tangent planes agree on the overlap.
- Property (G2) (normalized Lebesgue points, finite density) comes from the sibling `iwl_imc_normalized_lebesgue_points`.
- Property (G3) (density zero of M₁ Δ M₂, preliminary (iv), the Upper Density Theorem) comes from the sibling `iwl_imc_density_zero_off_set`. Its conclusion is stated for all scaled radii Rr (R > 0), exactly the form (D) used in step 3.
- Each (M_l, θ_l) is compared by (TL) with the constant θ_l(x) on M₁ ∩ M₂, as in the parent's step 2. The two constants are then related by preliminary (vii).
- The conclusion here is stated for two arbitrary weighted carriers, not only for those of two currents.

Statement. Assume (TL). Let U ⊆ ℝ^P be open, and let M₁, M₂ ⊆ U be H-null-measurable. Let θ₁, θ₂ : ℝ^P → ℝ satisfy θ_l(x) ≥ 1 for x ∈ M_l, and let θ_l be H-integrable on M_l ∩ K for every compact K ⊆ U (l = 1, 2). Then for H⌞(M₁ ∩ M₂)-a.e. x and every Q: HasWATS k M₁ θ₁ x Q ⟹ HasWATS k M₂ θ₂ x Q.

1. (Local finiteness.) Let K ⊆ U be compact.
   - Since ‖θ₁(y)‖ₑ ≥ 1 for y ∈ M₁, H(M₁ ∩ K) = ∫⁻_{M₁∩K} 1 dH ≤ ∫⁻_{M₁∩K} ‖θ₁‖ₑ dH < ∞. The last integral is finite by integrability of θ₁ on M₁ ∩ K.
   - Hence H(M₁ ∩ M₂ ∩ K) ≤ H(M₁ ∩ K) < ∞.
   - M₁ ∩ M₂ ⊆ U is H-null-measurable, and θ_l is H-integrable on M₁ ∩ M₂ ∩ K ⊆ M_l ∩ K.

2. (Normalized Lebesgue points, (G2).) Apply the sibling `iwl_imc_normalized_lebesgue_points` with M := M₁ ∩ M₂ and f := θ_l (l = 1, 2); its hypotheses are step 1. For H⌞(M₁ ∩ M₂)-a.e. x and every R > 0:
   (L_l) r^{−k} ∫⁻_{M₁∩M₂∩B̄_{Rr}(x)} ‖θ_l(y) − θ_l(x)‖ₑ dH(y) → 0 as r ↓ 0.

3. (Density zero of the symmetric difference, (G3).) Put S := M₁ Δ M₂, which is H-null-measurable, and g := 1_{M₁}‖θ₁‖ₑ + 1_{M₂}‖θ₂‖ₑ : ℝ^P → [0, ∞].
   - For compact K ⊆ U: ∫⁻_{S∩K} g dH ≤ ∫⁻_{M₁∩K} ‖θ₁‖ₑ dH + ∫⁻_{M₂∩K} ‖θ₂‖ₑ dH < ∞. The lintegral of the sum splits because the first summand is a.e.-measurable for H⌞(S ∩ K): θ₁ is a.e.-strongly measurable on M₁ ∩ K, and M₁ is null-measurable (`aemeasurable_indicator_iff₀`, `lintegral_add_left'`). Also ∫⁻_{S∩K} 1_{M_l}φ = ∫⁻_{M_l∩S∩K} φ ≤ ∫⁻_{M_l∩K} φ (`lintegral_indicator₀`, `Measure.restrict_restrict₀`, `lintegral_mono_set`).
   - The sibling `iwl_imc_density_zero_off_set` applies with this U, S and g. Its hypotheses are: U is open, S is H-null-measurable, and ∫⁻_{S∩K} g dH < ∞ for every compact K ⊆ U (just shown). It gives: for H-a.e. x with x ∈ U and x ∉ S, and for every R > 0,
     (D) r^{−k} ∫⁻_{S∩B̄_{Rr}(x)} g dH → 0 as r ↓ 0.
   - Every x ∈ M₁ ∩ M₂ lies in U and not in S. So (D) holds for H⌞(M₁ ∩ M₂)-a.e. x (`ae_restrict_of_ae`).

4. (Scaling, preliminary (vii).) For every set N, φ : ℝ^P → ℝ, c ≠ 0, point x and subspace Q: HasWATS k N (y ↦ c·φ(y)) x Q ⟺ HasWATS k N φ x Q.
   - The dimension conditions coincide.
   - For f ∈ C_c: ∫_{η_{x,r}(N)} f(y)·(c·φ(x + r•y)) dH = c·∫_{η_{x,r}(N)} f(y)·φ(x + r•y) dH. This is `integral_const_mul`, valid for the Bochner integral without integrability.
   - The limit value is (c·φ(x))·∫_Q f = c·(φ(x)·∫_Q f).
   - Multiplication by c is a homeomorphism of ℝ. So F(r) → L iff c·F(r) → c·L (`Tendsto.const_mul` with c and c⁻¹).

5. (Comparison with constants on the overlap, parent step 2.) By steps 2–3 and `ae_restrict_mem₀`, H⌞(M₁ ∩ M₂)-a.e. x satisfies x ∈ M₁ ∩ M₂, (L₁), (L₂) and (D). Fix such an x; then x ∈ U. Fix l ∈ {1, 2}. Apply (TL) to (M, θ) := (M_l, θ_l) and (M′, θ′) := (M₁ ∩ M₂, const θ_l(x)):
   - Both sets are H-null-measurable, and θ_l(x) = θ′(x).
   - U is open, so choose ρ > 0 with B̄_ρ(x) ⊆ U. Then B̄_ρ(x) is compact, so θ_l is integrable on M_l ∩ B̄_ρ(x). The constant θ_l(x) is integrable on M₁ ∩ M₂ ∩ B̄_ρ(x), which has finite H-measure by step 1 (`integrableOn_const`).
   - Pointwise bound: for every z,
     ‖1_{M_l}θ_l(z) − 1_{M₁∩M₂}(z)θ_l(x)‖ₑ ≤ 1_{M₁∩M₂}(z)‖θ_l(z) − θ_l(x)‖ₑ + 1_S(z)g(z).
     · If z ∈ M₁ ∩ M₂ (⊆ M_l), the left side equals the first term on the right.
     · If z ∈ M_l ∖ (M₁ ∩ M₂), then z ∈ S and the left side is ‖θ_l(z)‖ₑ ≤ g(z).
     · If z ∉ M_l, then z ∉ M₁ ∩ M₂ and the left side is 0.
   - Fix R > 0. For all small r > 0 we have B̄_{Rr}(x) ⊆ B̄_ρ(x). On B̄_{Rr}(x) the first term on the right is a.e.-measurable for H⌞B̄_{Rr}(x), because θ_l is a.e.-strongly measurable on M_l ∩ B̄_ρ(x) ⊇ M₁ ∩ M₂ ∩ B̄_{Rr}(x). So the integral of the right side splits, and
     ∫⁻_{B̄_{Rr}(x)} ‖1_{M_l}θ_l − 1_{M₁∩M₂}θ_l(x)‖ₑ dH ≤ ∫⁻_{M₁∩M₂∩B̄_{Rr}(x)} ‖θ_l − θ_l(x)‖ₑ dH + ∫⁻_{S∩B̄_{Rr}(x)} g dH.
   - Multiply by r^{−k}. By (L_l) and (D) the right side tends to 0 + 0. The left side is ≥ 0 and eventually ≤ the right side, so it tends to 0 (squeeze, `tendsto_of_tendsto_of_tendsto_of_le_of_le'`).
   - (TL) yields, for every Q: HasWATS k M_l θ_l x Q ⟺ HasWATS k (M₁ ∩ M₂) (const θ_l(x)) x Q.

6. (Conclusion.)
   - At x, θ₁(x) ≥ 1 and θ₂(x) ≥ 1, so c := θ₂(x)/θ₁(x) ≠ 0 and const θ₂(x) = (y ↦ c·(const θ₁(x))(y)).
   - Let Q satisfy HasWATS k M₁ θ₁ x Q.
   - By step 5 with l = 1: HasWATS k (M₁ ∩ M₂) (const θ₁(x)) x Q.
   - By step 4 with N := M₁ ∩ M₂, φ := const θ₁(x) and this c: HasWATS k (M₁ ∩ M₂) (const θ₂(x)) x Q.
   - By step 5 with l = 2: HasWATS k M₂ θ₂ x Q.
   - This holds for H⌞(M₁ ∩ M₂)-a.e. x and every Q. ∎

Formalization notes (a complete Lean proof of exactly this statement compiled in a scratch build of frozen commit d8d46c9, together with complete proofs of the two siblings):
- Step 3: `hD := Submission.iwl_imc_density_zero_off_set P k U S g hU hS hg`, with S := symmDiff M₁ M₂ and g y := M₁.indicator (‖θ₁ ·‖ₑ) y + M₂.indicator (‖θ₂ ·‖ₑ) y.
- Use `filter_upwards [hL₁, hL₂, ae_restrict_of_ae hD, ae_restrict_mem₀ (hM₁.inter hM₂)]`.
- The weight of the second comparison is `fun _ => θ_l x`. Prove a local `compare` for any (M, θ) with M₁ ∩ M₂ ⊆ M, M ∖ (M₁ ∩ M₂) ⊆ S and ‖θ‖ₑ ≤ g on M, then use it for l = 1, 2.
- Scaling: unfold HasWeightedApproximateTangentSpaceAt, then `and_congr_right`, `forall_congr'`, `integral_const_mul` and `Tendsto.const_mul`. The image set is `Poincare.SimonGMT.Chapter03.blowUpMap x r '' N`.
- Measurability: `aemeasurable_indicator_iff₀`, `Measure.restrict_restrict₀`, `lintegral_indicator₀`, `lintegral_add_left'`.
- ρ comes from `Metric.isOpen_iff` with closedBall x (ε/2) ⊆ ball x ε ⊆ U. Use `isCompact_closedBall` and `closedBall_subset_closedBall`.
- Give subset proofs explicit types with `show … ⊆ … from …`; anonymous-constructor subset proofs otherwise fail to elaborate.
- Write `bot_le` (or `zero_le` without argument) for the lower bound.

## Key steps

1. Hᵏ⌞M_l is locally finite on U because θ_l ≥ 1, so Hᵏ(M₁ ∩ M₂ ∩ K) < ∞ for compact K ⊆ U.
2. Sibling lebesgue_points (M := M₁ ∩ M₂, f := θ_l) and sibling density_zero_off_set (S := M₁ Δ M₂, g := 1_{M₁}|θ₁| + 1_{M₂}|θ₂|, all radii Rr) hold at Hᵏ⌞(M₁ ∩ M₂)-a.e. x.
3. At such x, |1_{M_l}θ_l − θ_l(x)1_{M₁∩M₂}| ≤ 1_{M₁∩M₂}|θ_l − θ_l(x)| + 1_S g, so the normalized L¹ distance tends to 0 and (TL) gives HasWATS(M_l, θ_l) ⟺ HasWATS(M₁ ∩ M₂, const θ_l(x)) at x.
4. Scaling by c = θ₂(x)/θ₁(x) ≠ 0 identifies the two constant-weight conditions (preliminary (vii)); chaining gives HasWATS(M₁, θ₁) ⟹ HasWATS(M₂, θ₂) at x.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical); cmp workspace Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (identical)`
- `python3 dag.json scans (re-run just before submission): status/candidate_commit/lean_statement/title/statement of rectifiability_density_comparison, slicing_representation_unique, ltg_tau_integrable, fiw_ims_frame_sign, fiw_ims_orientation_sign, iwl_restriction_theory, iwl_weighted_tangent_locality, lpf_wtc_ae_zero_density_off_set, br_weightedTangent_congr; regex scan of all accepted nodes for Lebesgue|IsMeasureRepresentation|tauAction|HasWeightedApproximateTangentSpaceAt|density; reserved names (no iwl_imc_*)`
- `sed -n 6532,6575p and 2364,2368p /runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py (_existing_lean_name_problem / _accepted_checkpoint: why attempt 1's lpf reuse was rejected)`
- `grep -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity|realUnitBallVolume' simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `grep -n 'theorem ae_tendsto_lintegral_enorm_sub_div|theorem tendsto_filterAt|protected def vitaliFamily' mathlib/Mathlib/MeasureTheory/Covering/{Differentiation,Besicovitch}.lean (Differentiation.lean:818, Besicovitch.lean:1021 and 1060)`
- `grep -rn 'theorem withDensity_apply |theorem setLIntegral_measure_zero|theorem _root_.Set.measure_eq_iInf_isOpen|theorem nullMeasurableSet_eq_fun' mathlib/Mathlib/MeasureTheory (found in Measure/WithDensity.lean:44, Integral/Lebesgue/Basic.lean:478, Measure/Regular.lean:368, Function/StronglyMeasurable/AEStronglyMeasurable.lean:575)`
- `sed -n 724,770p book/chapter-06.txt (Simon Ch. 6, 3.1 and 3.2 Remarks (1)-(3)); grep -n "3.3 Theorem|3.6 Theorem|3.7 Remarks" book/chapter-01.txt`
- `verifier/gmt-compare.py child_modules (contract mode) + verifier/lean_contract.validate_lean_statement on all 11 child types and the parent`
- `lean v4.35.0-rc3 (LEAN_PATH scratch build + lake-packages-25730c7c): lean -o build3/GMT/Ch06/Submission.olean src3/Submission.lean; lean checks/NodeChallenge_00..11.lean (frozen build) and checks/NodeSolution_00..11.lean (build3) with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-im-closure-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/imc-decomp-v2/src3/Submission.lean`
- `/tmp/imc-decomp-v2/logs/src3.out`
- `/tmp/imc-decomp-v2/checks/NodeSolution_11.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract, and Submission is byte-identical to it.

Available tools:
- SimonGMT: HasWeightedApproximateTangentSpaceAt (Ch. 3, 1.7, a limit over blow-ups, so it is invariant under a nonzero constant factor), its uniqueness lemma, CountablyRectifiable.mono / countablyRectifiable_iUnion, dimensionalUpperDensity and realUnitBallVolume.
- Mathlib (imported via Covering.DensityTheorem): Lebesgue–Besicovitch differentiation (VitaliFamily.ae_tendsto_lintegral_enorm_sub_div with Besicovitch.vitaliFamily / tendsto_filterAt), withDensity, outer regularity of finite measures, and AEStronglyMeasurable.nullMeasurableSet_eq_fun.
- The contract does not import SimonGMT's Chapter01.DensityComparison. Density comparison is therefore taken from the accepted Submission theorem rectifiability_density_comparison, and the Upper Density Theorem is the new child iwl_imc_density_zero_off_set.

Controller code (runtime.py) explains the rejected attempt: reuse requires an accepted checkpoint in the controller's view. The replacement child sidesteps the reservation on lpf_wtc_ae_zero_density_off_set.

Scratch Lean results (/tmp/imc-decomp-v2):
- All 11 child types and the parent elaborate in the exact comparator child scope.
- Complete single-theorem proofs of the 6 new children compile.
- The parent assembles from the children plus iwl_weighted_tangent_locality and iwl_restriction_theory.
- Axiom footprints are [propext, Classical.choice, Quot.sound] plus the intended stubs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
