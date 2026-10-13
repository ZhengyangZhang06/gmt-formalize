<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.im_closure-a1.lincomb_im-a1 -->

## Theorem `Submission.iwl_imc_lincomb_im`

Let P, k ∈ ℕ, Hᵏ := μHE[k] on ℝ^P = Eucl P, U ⊆ ℝ^P open, and assume the tangent comparison principle (T) in U: for all Hᵏ-null-measurable M₁, M₂ ⊆ U and all θ₁, θ₂ : ℝ^P → ℝ with θ_l(x) ≥ 1 for x ∈ M_l and θ_l Hᵏ-integrable on M_l ∩ K for every compact K ⊆ U (l = 1, 2), for Hᵏ⌞(M₁ ∩ M₂)-almost every x, every linear subspace Q of ℝ^P that is a weighted approximate tangent space of (M₁, θ₁) at x (HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q, Simon Ch. 3, 1.7) is also one of (M₂, θ₂) at x (the parent obtains (T) from the sibling iwl_imc_tangent_overlap applied to iwl_weighted_tangent_locality P k and U; this child takes (T) as a hypothesis and does not use that sibling). If X, Y ∈ D_k(U) are integer multiplicity, a, b ∈ ℤ, and Z ∈ D_k(U) satisfies Z(ω) = a·X(ω) + b·Y(ω) for every ω ∈ D^k(U), then Z is integer multiplicity.

Node: `root.integrality_weak_limits-a1.im_closure-a1.lincomb_im-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/940

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2809, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1250

Decomposition children: None

## Lean problem

Declaration: `Submission.iwl_imc_lincomb_im`

```lean
∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → (∀ (M₁ M₂ : Set (Eucl P)) (θ₁ θ₂ : Eucl P → ℝ), M₁ ⊆ U → M₂ ⊆ U → NullMeasurableSet M₁ (μHE[k] : Measure (Eucl P)) → NullMeasurableSet M₂ (μHE[k] : Measure (Eucl P)) → (∀ x ∈ M₁, 1 ≤ θ₁ x) → (∀ x ∈ M₂, 1 ≤ θ₂ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₁ (M₁ ∩ K) (μHE[k] : Measure (Eucl P))) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ₂ (M₂ ∩ K) (μHE[k] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict (M₁ ∩ M₂)), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M₁ θ₁ x Q → HasWeightedApproximateTangentSpaceAt k M₂ θ₂ x Q) → ∀ (X Y Z : GeometricCurrentOn U k) (a b : ℤ), IsIntegerMultiplicity X → IsIntegerMultiplicity Y → (∀ ω : TestFormOn U k, Z ω = (a : ℝ) * X ω + (b : ℝ) * Y ω) → IsIntegerMultiplicity Z
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
- Child DAG node: `root.integrality_weak_limits-a1.im_closure-a1.lincomb_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P := Eucl P. H := Hᵏ := μHE[k] (Mathlib's normalized k-dimensional Hausdorff measure). D_k(U) := GeometricCurrentOn U k and D^k(U) := TestFormOn U k. τ(M, θ, ξ)(ω) := tauAction k M θ ξ ω = ∫_M θ(x)·ξ(x)(ω(x)) dH(x). "i.m." means IsIntegerMultiplicity. HasWATS k M θ x Q abbreviates HasWeightedApproximateTangentSpaceAt k M θ x Q (Simon Ch. 3, 1.7). s(τ) := simpleNVector τ. For t ∈ ℝ, sgn(t) := 1, −1, 0 according as t > 0, t < 0, t = 0, so that |t|·sgn(t) = t. k-vectors are elements of NVector (Eucl P) k (continuous linear functionals on k-covectors). The scalar product t • w acts by (t • w)(α) = t·w(α).

The hypothesis (T) of the statement says: for all H-null-measurable M₁′, M₂′ ⊆ U and θ₁′, θ₂′ : ℝ^P → ℝ with θ_l′ ≥ 1 on M_l′ and θ_l′ H-integrable on M_l′ ∩ K for every compact K ⊆ U, the following holds for H⌞(M₁′ ∩ M₂′)-a.e. x: every Q with HasWATS k M₁′ θ₁′ x Q also satisfies HasWATS k M₂′ θ₂′ x Q. In the parent, (T) is discharged by the sibling iwl_imc_tangent_overlap.

Source. This is part (c) of the parent proof (Simon Ch. 6, 3.2(1)): steps 3–7 there.
- Steps 1–2 of the parent (agreement of tangent planes on M₁ ∩ M₂) and the comparisons in its step 6 are each one application of (T).
- The orientation step 3 is the sibling `fiw_ims_orientation_sign`.

Statement. Let U ⊆ ℝ^P be open and assume (T). Let X, Y, Z ∈ D_k(U) and a, b ∈ ℤ, with X and Y i.m. and Z(ω) = a·X(ω) + b·Y(ω) for every ω ∈ D^k(U). Then Z is i.m.

0. (Data.)
   - By definition of i.m., X = τ(M₁, θ₁, ξ₁) and Y = τ(M₂, θ₂, ξ₂) on D^k(U), with IsRectifiableTriple U k M_l θ_l ξ_l and θ_l(x) ∈ ℕ for x ∈ M_l (l = 1, 2).
   - Since θ_l > 0 on M_l (field `pos`), θ_l(x) is a positive integer, so θ_l ≥ 1 on M_l.
   - By the sibling `iwl_imc_tau_measure_representation`, for every ω ∈ D^k(U) the function h_l^ω(x) := θ_l(x)·ξ_l(x)(ω(x)) is H-integrable on M_l. Moreover X(ω) = ∫_{M₁} h₁^ω dH and Y(ω) = ∫_{M₂} h₂^ω dH.

1. (Orientations agree up to sign on the overlap; parent step 3.)
   - Apply (T) to (M₁, θ₁), (M₂, θ₂). All hypotheses are fields of the two triples together with θ_l ≥ 1. For H⌞(M₁ ∩ M₂)-a.e. x, every Q with HasWATS k M₁ θ₁ x Q satisfies HasWATS k M₂ θ₂ x Q.
   - The sibling `fiw_ims_orientation_sign` gives: for H⌞(M₁ ∩ M₂)-a.e. x, ξ₁(x) = ξ₂(x) or ξ₁(x) = −ξ₂(x).
   - Let N₀ ⊆ M₁ ∩ M₂ be the H-null set where this fails; it is H-null because M₁ ∩ M₂ is null-measurable (`Measure.restrict_apply₀'`/`ae_restrict_iff'₀`).

2. (New multiplicity, carrier and orientation; parent step 4.) Define, for x ∈ ℝ^P:
   - ε(x) := 1 if ξ₁(x) = ξ₂(x), and ε(x) := −1 otherwise;
   - c(x) := aθ₁(x) + bε(x)θ₂(x) if x ∈ M₁ ∩ M₂; aθ₁(x) if x ∈ M₁ ∖ M₂; bθ₂(x) if x ∈ M₂ ∖ M₁; 0 if x ∉ M₁ ∪ M₂;
   - ξ₀(x) := ξ₁(x) if x ∈ M₁, and ξ₀(x) := ξ₂(x) if x ∉ M₁;
   - V := M₁ ∪ M₂, M := {x ∈ V : c(x) ≠ 0}, θ(x) := |c(x)|, ξ(x) := sgn(c(x)) • ξ₀(x).
   Then:
   (a) c(x) ∈ ℤ for every x, because θ_l(x) ∈ ℕ on M_l, a, b ∈ ℤ and ε(x) ∈ {1, −1}. Hence for x ∈ M, θ(x) = |c(x)| ∈ ℕ and θ(x) ≥ 1, since a nonzero integer has absolute value ≥ 1.
   (b) For every x and every k-covector α: c(x)·ξ₀(x)(α) = θ(x)·ξ(x)(α), because |c|·sgn(c) = c.
   (c) For x ∈ V ∖ N₀ and every k-covector α (a scalar identity):
       a·1_{M₁}(x)θ₁(x)·ξ₁(x)(α) + b·1_{M₂}(x)θ₂(x)·ξ₂(x)(α) = c(x)·ξ₀(x)(α).
       · If x ∈ M₁ ∖ M₂, both sides are aθ₁(x)·ξ₁(x)(α).
       · If x ∈ M₂ ∖ M₁, both sides are bθ₂(x)·ξ₂(x)(α).
       · If x ∈ (M₁ ∩ M₂) ∖ N₀ and ξ₁(x) = ξ₂(x), then ε(x) = 1 and the left side is (aθ₁(x) + bθ₂(x))·ξ₁(x)(α).
       · If x ∈ (M₁ ∩ M₂) ∖ N₀ and ξ₁(x) ≠ ξ₂(x), then by step 1 ξ₁(x) = −ξ₂(x), so ξ₂(x)(α) = −ξ₁(x)(α), and ε(x) = −1. The left side is (aθ₁(x) − bθ₂(x))·ξ₁(x)(α).
   (d) For every x: |c(x)| ≤ |a|·1_{M₁}(x)|θ₁(x)| + |b|·1_{M₂}(x)|θ₂(x)|.

3. (Measurability.)
   (a) An open U ⊆ ℝ^P is a countable union of compact sets K_j ⊆ U (σ-compactness, e.g. closed balls with rational centres and radii contained in U). θ_l is integrable, hence a.e.-strongly measurable, on each M_l ∩ K_j. Since M_l ⊆ U = ⋃_j K_j, θ_l is a.e.-strongly measurable for H⌞M_l (`aestronglyMeasurable_iUnion_iff`). ξ_l is a.e.-strongly measurable for H⌞M_l (field `aestronglyMeasurable`).
   (b) V, M₁, M₂ are H-null-measurable. A function that is a.e.-(strongly) measurable for H⌞M_l, multiplied by the indicator 1_{M_l}, is a.e.-(strongly) measurable for H⌞V (`aemeasurable_indicator_iff₀`, `Measure.restrict_restrict₀`). In particular 1_{M₁}θ₁, 1_{M₂}θ₂, 1_{M₁ ∖ M₂}θ₁, 1_{M₂ ∖ M₁}θ₂ are a.e.-measurable, and 1_{M₁}ξ₁, 1_{V ∖ M₁}ξ₂ are a.e.-strongly measurable, for H⌞V.
   (c) The aligned part E⁺ := {x ∈ M₁ ∩ M₂ : ξ₁(x) = ξ₂(x)} and the anti-aligned part E⁻ := (M₁ ∩ M₂) ∖ E⁺ of the overlap are H-null-measurable.
       · The k-vectors NVector (Eucl P) k (continuous linear functionals on the finite-dimensional space of k-covectors) form a normed space under the operator norm (`ContinuousLinearMap.toNormedAddCommGroup`), so this space is metrizable.
       · 1_{M₁}ξ₁ and 1_{M₂}ξ₂ are a.e.-strongly measurable for H: ξ_l is a.e.-strongly measurable for H⌞M_l (field `aestronglyMeasurable`) and M_l is H-null-measurable (`aestronglyMeasurable_indicator_iff₀`).
       · For two H-a.e.-strongly measurable maps into a metrizable space, the set where they agree is H-null-measurable (`AEStronglyMeasurable.nullMeasurableSet_eq_fun`). Hence B := {x : 1_{M₁}ξ₁(x) = 1_{M₂}ξ₂(x)} is H-null-measurable.
       · For x ∈ M₁ ∩ M₂, x ∈ B iff ξ₁(x) = ξ₂(x). So E⁺ = (M₁ ∩ M₂) ∩ B and E⁻ = (M₁ ∩ M₂) ∩ Bᶜ are H-null-measurable.
       · (Equivalent route: the coordinate k-covectors dx^I separate k-vectors, each x ↦ ξ_l(x)(dx^I) is a.e.-measurable, and E⁺ is M₁ ∩ M₂ intersected with the corresponding equality sets.)
       Hence 1_{M₁∩M₂}·ε = 1_{E⁺} − 1_{E⁻} is a.e.-measurable for H⌞V.
   (d) Consequently c is a.e.-measurable for H⌞V, as a sum of products of the functions in (b) and (c). Hence {x ∈ V : c(x) ≠ 0} = M is H-null-measurable. Indeed, if c = c′ H⌞V-a.e. with c′ measurable, then M differs from V ∩ {c′ ≠ 0} by an H-null subset of V (`Measure.restrict_apply₀'`).
   (e) θ = |c| and sgn∘c are a.e.-measurable for H⌞V, hence for H⌞M (M ⊆ V). ξ = sgn(c) • ξ₀ is a.e.-strongly measurable for H⌞M, as the product of an a.e.-measurable scalar function with ξ₀. On M ∩ M₁, ξ₀ = ξ₁; on M ∖ M₁ ⊆ M₂, ξ₀ = ξ₂. Each piece is a.e.-strongly measurable by (a)–(b).

4. (Representation; parent step 5.) Fix ω ∈ D^k(U) and put F(x) := c(x)·ξ₀(x)(ω(x)). By 2(b), F(x) = θ(x)·ξ(x)(ω(x)).
   - By 2(c) with α := ω(x), for H-a.e. x ∈ V (all x ∈ V ∖ N₀): F(x) = a·1_{M₁}(x)h₁^ω(x) + b·1_{M₂}(x)h₂^ω(x).
   - The right side is H-integrable on V. Indeed 1_{M_l}h_l^ω is integrable on V with ∫_V 1_{M_l}h_l^ω dH = ∫_{M_l} h_l^ω dH, since M_l ⊆ V and M_l is null-measurable (`integral_indicator₀`, `setIntegral_indicator`).
   - Hence F is H-integrable on V and ∫_V F dH = a∫_{M₁}h₁^ω dH + b∫_{M₂}h₂^ω dH = aX(ω) + bY(ω) = Z(ω).
   - On V ∖ M we have c = 0, hence F = 0. Since M ⊆ V are null-measurable, ∫_V F dH = ∫_M F dH (`setIntegral_eq_of_subset_of_ae_diff_eq_zero` or splitting V = M ∪ (V ∖ M)).
   - Finally ∫_M F dH = ∫_M θ(x)·ξ(x)(ω(x)) dH(x) = τ(M, θ, ξ)(ω).
   Thus Z(ω) = τ(M, θ, ξ)(ω) for every ω ∈ D^k(U).

5. (The triple; parent step 6.) We check IsRectifiableTriple U k M θ ξ.
   - subset: M ⊆ V = M₁ ∪ M₂ ⊆ U.
   - nullMeasurableSet: step 3(d).
   - countablyRectifiable: M₁ ∪ M₂ is countably k-rectifiable, as a countable union of countably k-rectifiable sets (`countablyRectifiable_iUnion`, or the defining covers concatenated). So is its subset M (`CountablyRectifiable.mono`).
   - pos: θ ≥ 1 > 0 on M (2(a)).
   - integrableOn: let K ⊆ U be compact. θ is a.e.-measurable for H⌞(M ∩ K) (3(e)). By 2(d), |θ| ≤ |a|·1_{M₁}|θ₁| + |b|·1_{M₂}|θ₂|. The right side is H-integrable on M ∩ K, since 1_{M_l}|θ_l| is integrable on K exactly when θ_l is integrable on M_l ∩ K. Hence θ is H-integrable on M ∩ K (`Integrable.mono'`).
   - aestronglyMeasurable: step 3(e).
   - orients:
     · Apply (T) to (M₁, θ₁), (M, θ) and to (M₂, θ₂), (M, θ). The hypotheses hold: M ⊆ U is null-measurable, θ ≥ 1 on M, and θ is integrable on M ∩ K, as just shown. So for H⌞(M₁ ∩ M)-a.e. x (resp. H⌞(M₂ ∩ M)-a.e. x), every weighted tangent space of (M₁, θ₁) (resp. (M₂, θ₂)) at x is one of (M, θ) at x.
     · The field `orients` of triple l holds H⌞M_l-a.e., hence H⌞(M_l ∩ M)-a.e.
     · Since M = (M ∩ M₁) ∪ (M ∩ (M₂ ∖ M₁)), these statements combine (`ae_restrict_union_iff`, monotonicity of restriction). For H⌞M-a.e. x:
       ◦ If x ∈ M ∩ M₁: by `orients` of triple 1 there is an orthonormal τ : Fin k → ℝ^P with HasWATS k M₁ θ₁ x (span(range τ)) and ξ₁(x) = ±s(τ). By (T), HasWATS k M θ x (span(range τ)). Moreover ξ(x) = sgn(c(x)) • ξ₁(x), with sgn(c(x)) ∈ {1, −1} because c(x) ≠ 0. So ξ(x) = s(τ) or ξ(x) = −s(τ) (`one_smul`, `neg_one_smul`, `neg_neg`; four cases).
       ◦ If x ∈ M ∖ M₁ (so x ∈ M₂): the same argument with triple 2, using ξ₀(x) = ξ₂(x).
6. (Conclusion.) By steps 2(a), 4 and 5, (M, θ, ξ) is a rectifiable triple with θ(x) ∈ ℕ on M, and Z(ω) = τ(M, θ, ξ)(ω) for every ω ∈ D^k(U). Hence Z is integer multiplicity. (If a = b = 0 then c ≡ 0 and M = ∅; the argument covers this case.) ∎

Formalization notes (a complete Lean proof of exactly this statement, inside the single theorem, compiled in a scratch build of frozen commit d8d46c9 with the siblings as stubs; about 33k heartbeats):
- Equivalent, Lean-friendly data:
  · E⁻ := (M₁ ∩ M₂) ∖ {1_{M₁}ξ₁ = 1_{M₂}ξ₂}, the anti-aligned part of the overlap (step 3(c));
  · c := a·1_{M₁}θ₁ + b·1_{M₂}θ₂ − 2b·1_{E⁻}θ₂, which equals the c of step 2 (on E⁻, ε = −1; on E⁺, ε = 1);
  · M := {c ≠ 0}, since c vanishes off M₁ ∪ M₂; θ := |c|;
  · ξ := (if 0 ≤ c then 1 else −1) • ξ₀ with ξ₀ := M₁.piecewise ξ₁ (M₂.indicator ξ₂).
- Measurability:
  · θ_l is a.e.-strongly measurable for H⌞M_l by `LocallyIntegrableOn.aestronglyMeasurable`, using closed balls inside U;
  · E⁻ is null-measurable by `AEStronglyMeasurable.nullMeasurableSet_eq_fun`, which needs a local `MetrizableSpace (NVector (Eucl P) k)` obtained via `ContinuousLinearMap.toNormedAddCommGroup`;
  · M is null-measurable by `AEStronglyMeasurable.nullMeasurableSet_support`; `nullMeasurable` of {c ≠ 0} timed out.
  · Other lemmas: `aestronglyMeasurable_indicator_iff₀`, `AEStronglyMeasurable.piecewise`, `integrable_indicator_iff₀`, `Measure.restrict_restrict'`.
- Representation: `integral_indicator₀`, `setIntegral_eq_integral_of_forall_compl_eq_zero`, `integral_add`, `integral_const_mul`, `integral_congr_ae`.
- Integer values: `Int.one_le_abs`, `Nat.cast_natAbs`, `Int.cast_abs`.
- Rectifiability: `Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion`, `CountablyRectifiable.mono`.
- Pitfalls:
  · on NVector (Eucl P) k the instances ContinuousAdd, MetrizableSpace and AddCommGroup are not found automatically, so avoid adding k-vectors (use piecewise/indicator);
  · prove sign identities such as (−1) • (−w) = w by `ext α; simp`;
  · never state Integrable of NVector-valued functions (ContinuousENorm is missing);
  · `ContinuousLinearMap.smul_apply` is deprecated in favour of `smul_apply`.

## Key steps

1. Unpack X = τ(M₁, θ₁, ξ₁) and Y = τ(M₂, θ₂, ξ₂) with θ_l ∈ ℕ, θ_l ≥ 1; (T) for (M₁, θ₁), (M₂, θ₂) and the sibling orientation_sign give ξ₁ = ±ξ₂ a.e. on M₁ ∩ M₂.
2. Define ε = ±1 (sign of ξ₂ relative to ξ₁) and the integer function c = aθ₁ + bεθ₂ on M₁ ∩ M₂, aθ₁ on M₁ ∖ M₂, bθ₂ on M₂ ∖ M₁; M = {c ≠ 0}, θ = |c|, ξ = sgn(c)·ξ₀; all are a.e.-measurable and M is null-measurable.
3. a1_{M₁}θ₁ξ₁(α) + b1_{M₂}θ₂ξ₂(α) = c·ξ₀(α) a.e., so Z(ω) = aX(ω) + bY(ω) = ∫_M θ ξ(ω) dHᵏ = τ(M, θ, ξ)(ω) (integrability from sibling tau_repr).
4. (M, θ, ξ) is a rectifiable triple with θ ∈ ℕ: the orientation condition follows from (T) applied to (M_l, θ_l) and (M, θ), because ξ = ±ξ_l on M ∩ M_l.

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
