<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.orientation_error_vanishes-a1 -->

## Theorem `Submission.ind_ab_orientation_error_vanishes`

Let P, n ∈ ℕ and Hⁿ = μHE[n] on ℝ^P. Let M ⊆ ℝ^P be Hⁿ-null-measurable, θ : ℝ^P → ℝ with θ ≥ 0 on M, ξ : ℝ^P → NVector(ℝ^P, n), x ∈ ℝ^P, and ω : ℝ^P → Λⁿ(ℝ^P) continuous with compact support. Put a(s) := ∫⁻_{M∩B̄_s(x)} ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ dHⁿ(y) and b(s) := ∫⁻_{M∩B̄_s(x)} ofReal(θ) dHⁿ. Assume: (i) there is C ∈ ℝ≥0 with b(s) ≤ C·ofReal(sⁿ) for all sufficiently small s > 0; (ii) a(s)/b(s) → 0 in [0, ∞] as s → 0⁺. Then E(r) := ∫_M θ(y)·(ξ(y) − ξ(x))((rⁿ)⁻¹•ω(r⁻¹•(y − x))) dHⁿ(y) → 0 as r → 0⁺. E(r) is a Bochner set integral, and no integrability is assumed.

Node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.orientation_error_vanishes-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2486

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.ind_ab_orientation_error_vanishes`

```lean
∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (x : Eucl P) (ω : Eucl P → Covector (Eucl P) n), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → Continuous ω → HasCompactSupport ω → (∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤ C * ENNReal.ofReal (s ^ n)) → Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0)
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

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.ae_blowup-a1.orientation_error_vanishes-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 6 (the normalized Lebesgue point, condition (G2)) and 8 (the error term) of the parent proof. The outputs of the parent's steps 3 and 5 enter here as the hypotheses (i) and (ii).

Notation:
- Hⁿ := μHE[n] on ℝ^P, and ν := Hⁿ⌞M;
- a(s) := ∫⁻_{M∩B̄_s(x)} ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ dHⁿ(y);
- b(s) := ∫⁻_{M∩B̄_s(x)} ofReal(θ) dHⁿ;
- ε(s) := a(s)/ofReal(sⁿ) ∈ [0, ∞].

1. An inequality in [0, ∞]. Let a', b', d ∈ [0, ∞] and c ∈ ℝ≥0 with 0 < d < ∞, b' ≤ c·d and a'/b' < 1. Then a'/d ≤ c·(a'/b').
Proof: by ENNReal.div_le_iff (d ≠ 0, d ≠ ∞) it suffices to show a' ≤ c·(a'/b')·d.
- If b' = 0, then a' = 0: otherwise a'/b' = ∞ (ENNReal.div_zero), contradicting a'/b' < 1. The inequality is then trivial.
- If b' ≠ 0, then b' ≤ c·d < ∞, so a' = (a'/b')·b' ≤ (a'/b')·c·d (ENNReal.div_mul_cancel).

2. ε(s) → 0 as s → 0⁺. The set {t : t < 1} is a neighbourhood of 0 in [0, ∞]. So by (i) and (ii), for all s in a set belonging to 𝓝[>] 0 we have s > 0, b(s) ≤ C·ofReal(sⁿ) and a(s)/b(s) < 1. For such s, d := ofReal(sⁿ) satisfies 0 < d < ∞, and step 1 gives 0 ≤ ε(s) ≤ C·(a(s)/b(s)). Since C < ∞, (ii) gives C·(a(s)/b(s)) → C·0 = 0 (ENNReal.Tendsto.const_mul). By the squeeze theorem, ε(s) → 0.

3. Radius and bound. tsupport ω is compact, hence bounded, so it lies in some closed ball B̄_{R₀}(0). Put R := max(R₀, 1) > 0; then tsupport ω ⊆ B̄_R(0). Since ω is continuous with compact support, there is B with ‖ω(z)‖ ≤ B for all z (HasCompactSupport.exists_bound_of_continuous). Also B ≥ ‖ω(0)‖ ≥ 0.

4. Pointwise bound. Fix r > 0, put c_r := (rⁿ)⁻¹ ≥ 0, and let F_r(y) := θ(y)·(ξ(y) − ξ(x))(c_r•ω(r⁻¹•(y − x))).
 (a) If y ∉ B̄_{Rr}(x), then ‖r⁻¹•(y − x)‖ = r⁻¹‖y − x‖ > R. So r⁻¹•(y − x) ∉ tsupport ω, hence ω(r⁻¹•(y − x)) = 0 and F_r(y) = 0.
 (b) If y ∈ M, then θ(y) ≥ 0. Using |w(α)| ≤ ‖w‖‖α‖ for n-vectors w and ‖c•α‖ = |c|‖α‖, we get |F_r(y)| ≤ θ(y)‖ξ(y) − ξ(x)‖·c_r·B. In [0, ∞]:
  ‖F_r(y)‖ₑ ≤ ofReal(c_r·B)·ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ.
 Since M is null-measurable, ν-a.e. y lies in M. So by (a) and (b), for ν-a.e. y:
  ‖F_r(y)‖ₑ ≤ 1_{B̄_{Rr}(x)}(y)·ofReal(c_r·B)·ofReal(θ(y))‖ξ(y) − ξ(x)‖ₑ.

5. Integral bound. Let E(r) := ∫_M F_r dHⁿ. Then
  ‖E(r)‖ₑ ≤ ∫⁻_M ‖F_r‖ₑ dHⁿ   [enorm_integral_le_lintegral_enorm; valid whether or not F_r is integrable, since the Bochner integral is otherwise 0]
  ≤ ∫⁻_M 1_{B̄_{Rr}(x)}·ofReal(c_r·B)·ofReal(θ)‖ξ − ξ(x)‖ₑ dHⁿ   [step 4, lintegral_mono_ae]
  = ofReal(c_r·B)·∫⁻_{M∩B̄_{Rr}(x)} ofReal(θ)‖ξ − ξ(x)‖ₑ dHⁿ   [lintegral_indicator on the measurable ball, Measure.restrict_restrict, lintegral_const_mul' with a finite constant]
  = ofReal(c_r·B)·a(Rr).
Since 0 < ofReal((Rr)ⁿ) < ∞, a(Rr) = ε(Rr)·ofReal((Rr)ⁿ). Also ofReal(c_r·B)·ofReal((Rr)ⁿ) = ofReal((rⁿ)⁻¹·B·Rⁿrⁿ) = ofReal(B·Rⁿ). Hence ‖E(r)‖ₑ ≤ ofReal(B·Rⁿ)·ε(Rr) for every r > 0.

6. Limit. Since R > 0, the map r ↦ Rr sends (0, ∞) into (0, ∞) and tends to 0, so it tends to 0 within (0, ∞) as r → 0⁺. By step 2, ε(Rr) → 0, and hence ofReal(B·Rⁿ)·ε(Rr) → 0, the constant being finite. By step 5 and the squeeze theorem, ‖E(r)‖ₑ → 0 as r → 0⁺, i.e. E(r) → 0 in ℝ (tendsto_zero_iff_enorm_tendsto_zero). ∎

Formalization note: for n-vectors, the bridge between ofReal ‖·‖ and ‖·‖ₑ must be written ofReal_norm_eq_enorm (E := NVector (Eucl P) n). Without the explicit E, the instance paths of the norm on NVector (ContinuousLinearMap.hasOpNorm versus the normed-group norm) do not unify. Avoid `set` over large integral expressions, which causes heartbeat timeouts.

Appendix (formalization aid; not part of the mathematical argument). The following script was kernel-checked in scratch against the frozen environment (Lean v4.35.0-rc3, Mathlib 25730c7c, `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open`s) and depends only on propext, Classical.choice and Quot.sound:

theorem Submission.ind_ab_orientation_error_vanishes :
    ∀ (P n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) (x : Eucl P) (ω : Eucl P → Covector (Eucl P) n), NullMeasurableSet M (μHE[n] : Measure (Eucl P)) → (∀ y ∈ M, 0 ≤ θ y) → Continuous ω → HasCompactSupport ω → (∃ C : ℝ≥0, ∀ᶠ s in 𝓝[>] (0 : ℝ), ∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)) ≤ C * ENNReal.ofReal (s ^ n)) → Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))) (𝓝[>] 0) (𝓝 0) := by
  intro P n M θ ξ x ω hM hθ hω hωc hgrowth hratio
  obtain ⟨C, hC⟩ := hgrowth
  -- an elementary ENNReal estimate
  have key : ∀ (a b d : ℝ≥0∞) (c : ℝ≥0), d ≠ 0 → d ≠ ⊤ → b ≤ c * d → a / b < 1 →
      a / d ≤ c * (a / b) := by
    intro a b d c hd0 hdtop hbd hab
    rw [ENNReal.div_le_iff hd0 hdtop]
    by_cases hb0 : b = 0
    · have ha0 : a = 0 := by
        by_contra hne
        rw [hb0, ENNReal.div_zero hne] at hab
        exact absurd hab (not_lt.2 le_top)
      rw [ha0]; exact zero_le
    · have hbtop : b ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hdtop) hbd
      calc a = (a / b) * b := (ENNReal.div_mul_cancel hb0 hbtop).symm
        _ ≤ (a / b) * ((c : ℝ≥0∞) * d) := by gcongr
        _ = (c : ℝ≥0∞) * (a / b) * d := by ring
  -- Step 1: the normalized error tends to 0
  have hε : Tendsto (fun s : ℝ => (∫⁻ y in M ∩ closedBall x s,
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) / ENNReal.ofReal (s ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (∫⁻ y in M ∩ closedBall x s,
        ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
          ENNReal.ofReal (s ^ n) ≤
        (C : ℝ≥0∞) * ((∫⁻ y in M ∩ closedBall x s,
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            (∫⁻ y in M ∩ closedBall x s, ENNReal.ofReal (θ y) ∂(μHE[n] : Measure (Eucl P)))) := by
      filter_upwards [hC, hratio.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from zero_lt_one)),
        self_mem_nhdsWithin] with s hbs hrs hs
      have hs' : (0 : ℝ) < s := hs
      exact key _ _ _ C (ENNReal.ofReal_pos.2 (pow_pos hs' n)).ne' ENNReal.ofReal_ne_top hbs hrs
    have h2 := ENNReal.Tendsto.const_mul hratio (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun _ => zero_le) h1
  -- Step 2: radius and bound of ω
  obtain ⟨R₀, hR₀⟩ := (hωc.isCompact.isBounded).subset_closedBall (0 : Eucl P)
  obtain ⟨R, hRpos, hRsub⟩ : ∃ R : ℝ, 0 < R ∧ tsupport ω ⊆ closedBall (0 : Eucl P) R :=
    ⟨max R₀ 1, lt_max_of_lt_right one_pos,
      hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨B, hB⟩ := hωc.exists_bound_of_continuous hω
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  -- Step 3/4: integral bound
  have hbound : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal ((r ^ n)⁻¹ * B) *
          ∫⁻ y in M ∩ closedBall x (R * r), ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ
            ∂(μHE[n] : Measure (Eucl P)) := by
    intro r hr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hpt : ∀ᵐ y ∂((μHE[n] : Measure (Eucl P)).restrict M),
        ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ ≤
          (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y := by
      filter_upwards [ae_restrict_mem₀ hM] with y hy
      by_cases hyB : y ∈ closedBall x (R * r)
      · rw [indicator_of_mem hyB]
        have hcn : 0 ≤ (r ^ n)⁻¹ := inv_nonneg.2 (pow_nonneg hr.le n)
        have hreal : ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ ≤
            ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by
          rw [norm_mul, Real.norm_of_nonneg (hθ y hy)]
          have hθy := hθ y hy
          calc θ y * ‖(ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖
              ≤ θ y * (‖ξ y - ξ x‖ * ‖(r ^ n)⁻¹ • ω (r⁻¹ • (y - x))‖) := by
                gcongr
                exact (ξ y - ξ x).le_opNorm _
            _ ≤ θ y * (‖ξ y - ξ x‖ * ((r ^ n)⁻¹ * B)) := by
                gcongr
                rw [norm_smul, Real.norm_of_nonneg hcn]
                gcongr
                exact hB _
            _ = ((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖) := by ring
        calc ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
            = ENNReal.ofReal ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ :=
              (ofReal_norm_eq_enorm _).symm
          _ ≤ ENNReal.ofReal (((r ^ n)⁻¹ * B) * (θ y * ‖ξ y - ξ x‖)) := ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ) := by
              have he : ENNReal.ofReal ‖ξ y - ξ x‖ = ‖ξ y - ξ x‖ₑ :=
                ofReal_norm_eq_enorm (E := NVector (Eucl P) n) _
              rw [ENNReal.ofReal_mul (mul_nonneg hcn hB0), ENNReal.ofReal_mul (hθ y hy), he]
      · rw [indicator_of_notMem hyB]
        have hω0 : ω (r⁻¹ • (y - x)) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          apply hyB
          have h1 := hRsub hmem
          rw [mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_le_iff₀ hr] at h1
          rw [mem_closedBall, dist_eq_norm]
          linarith
        simp [hω0]
    calc ∫⁻ y in M, ‖θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x)))‖ₑ
          ∂(μHE[n] : Measure (Eucl P))
        ≤ ∫⁻ y in M, (closedBall x (R * r)).indicator
            (fun y => ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)) y
            ∂(μHE[n] : Measure (Eucl P)) := lintegral_mono_ae hpt
      _ = ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal ((r ^ n)⁻¹ * B) * (ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ)
            ∂(μHE[n] : Measure (Eucl P)) := by
          rw [lintegral_indicator measurableSet_closedBall,
            Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      _ = ENNReal.ofReal ((r ^ n)⁻¹ * B) * ∫⁻ y in M ∩ closedBall x (R * r),
            ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hbound2 : ∀ r : ℝ, 0 < r →
      ‖∫ y in M, θ y * (ξ y - ξ x) ((r ^ n)⁻¹ • ω (r⁻¹ • (y - x))) ∂(μHE[n] : Measure (Eucl P))‖ₑ ≤
        ENNReal.ofReal (B * R ^ n) * ((∫⁻ y in M ∩ closedBall x (R * r),
          ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P))) /
            ENNReal.ofReal ((R * r) ^ n)) := by
    intro r hr
    refine (hbound r hr).trans (le_of_eq ?_)
    have hRr : 0 < R * r := mul_pos hRpos hr
    have hd0 : ENNReal.ofReal ((R * r) ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hRr n)).ne'
    have hdt : ENNReal.ofReal ((R * r) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
    conv_lhs => rw [← ENNReal.div_mul_cancel hd0 hdt (b := ∫⁻ y in M ∩ closedBall x (R * r),
      ENNReal.ofReal (θ y) * ‖ξ y - ξ x‖ₑ ∂(μHE[n] : Measure (Eucl P)))]
    rw [mul_comm _ (ENNReal.ofReal ((R * r) ^ n)), ← mul_assoc,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 (pow_nonneg hr.le n)) hB0)]
    congr 2
    rw [mul_pow]
    field_simp
  have hcomp : Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hRpos hr
  have hlim := ENNReal.Tendsto.const_mul (hε.comp hcomp)
    (Or.inr (ENNReal.ofReal_ne_top (r := B * R ^ n)))
  rw [mul_zero] at hlim
  rw [tendsto_zero_iff_enorm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hbound2 r hr

## Key steps

1. ENNReal inequality: if 0 < d < ∞, b ≤ c·d and a/b < 1, then a/d ≤ c·(a/b) (b = 0 forces a = 0).
2. Hence ε(s) := a(s)/ofReal(sⁿ) ≤ C·(a(s)/b(s)) eventually, so ε(s) → 0.
3. Choose R > 0 with tsupport ω ⊆ B̄_R(0) and a bound B ≥ 0 for ‖ω‖.
4. For r > 0, the integrand vanishes off B̄_{Rr}(x) and is bounded on M by (rⁿ)⁻¹B·θ‖ξ − ξ(x)‖.
5. ‖E(r)‖ₑ ≤ ∫⁻_M ‖F_r‖ₑ ≤ ofReal((rⁿ)⁻¹B)·a(Rr) = ofReal(BRⁿ)·ε(Rr).
6. As r → 0⁺, Rr → 0⁺, so ε(Rr) → 0 and E(r) → 0.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (identical); diff snapshot Contract.lean vs workspace GMT/Ch06/Contract.lean (identical)`
- `rg -n 'ind_ab_' project/ and simongmt/Poincare (no match); python3 scan of dag.json lean_name and theorems lists for ind_ab_* (362 nodes, no match); git grep -l 'ind_ab_' over all local branch heads (no match)`
- `python3 scan of dag.json for the accepted lpf_wtc_blowup_setIntegral_image, fiw_ims_tt_unit_bound, ltg_tau_integrable, lpf_wtc_density_bound_of_tangent, lpf_wtc_wtt_remainder_vanishes and lpf_wtc_wtt_blowup_integral_split, and for the sibling ind_* statements`
- `sed -n '/def blowUpMap/,/^$/p;/def HasWeightedApproximateTangentSpaceAt/,/^$/p' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def simpleNVector|abbrev Covector|abbrev DifferentialForm' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean Chapter06/Forms.lean`
- `rg -n 'HasWeightedApproximateTangentSpaceAt|theorem .*blowUp|ae_tendsto_lintegral_enorm_sub_div|vitaliFamily|Besicovitch|withDensity' simongmt/Poincare -g '*.lean'`
- `rg -n 'protected def vitaliFamily|theorem tendsto_filterAt' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean; rg -n 'theorem ae_tendsto_lintegral_enorm_sub_div' mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `rg -n 'lemma withDensity_absolutelyContinuous|setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀|theorem withDensity_apply' mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `rg -n 'aestronglyMeasurable_iUnion_iff|Continuous.comp_aestronglyMeasurable₂|IntegrableOn.of_ae_sdiff_eq_zero|Measure.integrableOn_of_bounded|Integrable.lintegral_lt_top|enorm_integral_le_lintegral_enorm|ofReal_integral_eq_lintegral_ofReal|sigmaFinite_of_locallyFinite|isBoundedBilinearMap_apply|HasCompactMulSupport.exists_bound_of_continuous|div_le_iff|div_mul_cancel|div_zero|instHasBesicovitchCovering' in the snapshot mathlib/Mathlib files listed`
- `git show <lpf blow-up branch>:GMT/Ch06/Submission.lean (accepted proof of Submission.lpf_wtc_blowup_setIntegral_image)`
- `sed -n 2400,2440p book/chapter-06.txt (printed Proof of 8.2, display (7))`
- `verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') and lean_contract.validate_lean_statement on the 4 child statements`
- `lake env lean /tmp/ab-decomp-scratch/{Stmts,Pairing,Enorm,C1,C24,C3,Assembly,Full}.lean (#synth, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-ae-blowup-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ab-decomp-scratch/Stmts.lean`
- `/tmp/ab-decomp-scratch/Assembly.lean`
- `/tmp/ab-decomp-scratch/Full.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract, byte-identical to its Submission and to the workspace Contract.

Available API and reuse:
- The contract's own scope opens only CountablyRectifiable and HasWeightedApproximateTangentSpaceAt from Chapter03. The statements therefore spell blow-ups as r⁻¹ • (y - x), not blowUpMap.
- SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap and the definition of HasWeightedApproximateTangentSpaceAt (finrank plus a C_c blow-up limit).
- Chapter06 supplies NVector = Covector →L ℝ and simpleNVector (built with mkContinuous, bound ∏‖v_i‖).
- SimonGMT has no weighted Lebesgue-point or rescaled-tangent lemma for general (M, θ). Chapter04/WeightedBlowUp.lean (tendsto_rescaled_weight_of_weighted_approximateTangent) is a varifold-specific analogue of child 1. It is not imported by the contract and does not apply to arbitrary M and θ.
- The snapshot Mathlib supplies everything children 3 and 4 need: Besicovitch.vitaliFamily, Besicovitch.tendsto_filterAt, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, withDensity_apply, withDensity_absolutelyContinuous(') and setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀; aestronglyMeasurable_iUnion_iff, IntegrableOn.of_ae_sdiff_eq_zero, Measure.integrableOn_of_bounded, Integrable.lintegral_lt_top, enorm_integral_le_lintegral_enorm, ofReal_integral_eq_lintegral_ofReal and sigmaFinite_of_locallyFinite; instHasBesicovitchCovering, isBoundedBilinearMap_apply, the ENNReal division lemmas and HasCompactSupport.exists_bound_of_continuous.
- Accepted DAG declarations reused with identical frozen types: Submission.lpf_wtc_blowup_setIntegral_image (child 1; its proof was inspected on its branch). Optionally Submission.fiw_ims_tt_unit_bound (unit bound, child 3 and the parent).
- No ind_ab_* names exist in the DAG, the snapshot, SimonGMT or the local branches.

Scratch kernel checks:
- All 4 child statements pass validate_lean_statement and elaborate in the contract_scope replay.
- The parent assembly and complete proofs of all 4 children check with only propext, Classical.choice and Quot.sound. So do the comparator-style `exact Submission.X` replays of all 4 children and of the parent ind_ae_blowup_limit.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
