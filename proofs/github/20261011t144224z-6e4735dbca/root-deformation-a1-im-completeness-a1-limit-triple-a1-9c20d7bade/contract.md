<!-- theorem-id: gmt-ch06/root.deformation-a1.im_completeness-a1.limit_triple-a1 -->

## Theorem `Submission.imc_isRectifiableTriple_of_eventually_mem`

Let N, k ∈ ℕ and H := μHE[k] on ℝ^N. For every j ∈ ℕ let (M_j, θ_j, ξ_j) satisfy IsRectifiableTriple ℝ^N k M_j θ_j ξ_j with θ_j ≥ 1 on M_j. Let M₀ ⊆ ℝ^N be H-null-measurable, θ₀ : ℝ^N → ℝ with θ₀ ≥ 1 on M₀ and θ₀ H-integrable on M₀ ∩ K for every compact K, and ξ₀ : ℝ^N → Λ_k(ℝ^N) (NVector). Assume that for H-a.e. x ∈ M₀ (H⌞M₀-a.e.) x ∈ M_j for all sufficiently large j and ξ_j(x) → ξ₀(x). Then IsRectifiableTriple ℝ^N k M₀ θ₀ ξ₀: M₀ is countably k-rectifiable, θ₀ > 0 on M₀ and locally H-integrable, ξ₀ is H⌞M₀-a.e. strongly measurable, and for H-a.e. x ∈ M₀ there is an orthonormal τ : Fin k → ℝ^N such that span τ is the weighted approximate tangent space of (M₀, θ₀) at x and ξ₀(x) = ±simpleNVector τ.

Node: `root.deformation-a1.im_completeness-a1.limit_triple-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1106

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3266, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3282, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1249

Decomposition children: None

## Lean problem

Declaration: `Submission.imc_isRectifiableTriple_of_eventually_mem`

```lean
∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k) (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), (∀ j, IsRectifiableTriple (univ : Set (Eucl N)) k (M j) (θ j) (ξ j)) → (∀ j, ∀ x ∈ M j, 1 ≤ θ j x) → NullMeasurableSet M₀ (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M₀, 1 ≤ θ₀ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict M₀), (∀ᶠ j in atTop, x ∈ M j) ∧ Tendsto (fun j => ξ j x) atTop (𝓝 (ξ₀ x))) → IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀
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

- Parent DAG node: `root.deformation-a1.im_completeness-a1`
- Child DAG node: `root.deformation-a1.im_completeness-a1.limit_triple-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 6 of the parent proof (the triple conditions for (M₊, θ, ξ) and the orientation argument), with the pointwise facts established there ("there is j(x) with θ_j(x) = θ(x) for j ≥ j(x); then x ∈ M_j … and ξ_j(x) → ξ(x)") isolated as hypotheses; it is the last paragraph of Simon's printed proof ("ξ_Q(x) ∈ Λ_n(T_xM_Q) … T_xM₊ = T_xM_Q except for a set of small measure … ξ(x) ∈ Λ_n(T_xM₊)"). It uses the siblings approx_tangent_locality (Lemma A) and weighted_tangent_equiv (Lemma B), the accepted sibling frame_sign (fiw_ims_frame_sign) and the library theorem HasWeightedApproximateTangentSpaceAt.unique.

Notation. H := μHE[k]. For an H-null-measurable A, "H⌞A-a.e." means ∀ᵐ x ∂(H.restrict A). We use three facts about restricted measures: (R1) if A ⊆ B then H⌞A ≤ H⌞B, so an H⌞B-a.e. property holds H⌞A-a.e.; (R2) if A ⊆ B are H-null-measurable, a property holds H⌞A-a.e. iff "x ∈ A → property" holds H⌞B-a.e. (ae_restrict_iff'₀ and (H⌞B)⌞A = H⌞A); (R3) H⌞B-a.e. x lies in B (ae_restrict_mem₀). In particular, an H⌞M_j-a.e. property P yields, by (R1) for M_j ∩ M₀ ⊆ M_j, (R2) for M_j ∩ M₀ ⊆ M₀ and (R3), that "x ∈ M_j → P(x)" holds H⌞M₀-a.e.; we call this converting to H⌞M₀. W(A, ϑ, x, Q) abbreviates HasWeightedApproximateTangentSpaceAt k A ϑ x Q and T(A, x, Q) abbreviates HasApproximateTangentSpaceAt k A x Q. Let Good ⊆ M₀ be the set of x ∈ M₀ at which the hypothesis holds; H(M₀ ∖ Good) = 0.

1. (Local finiteness.) For every j and compact K, H(M_j ∩ K) ≤ ∫⁻_{M_j∩K} ENNReal.ofReal(θ_j) dH < ∞, because θ_j ≥ 1 on M_j and θ_j is H-integrable on M_j ∩ K (field integrableOn of the triple, K ⊆ univ). Likewise H(M₀ ∩ K) < ∞.

2. (Elementary fields.) subset: M₀ ⊆ univ. nullMeasurableSet: hypothesis. pos: θ₀ ≥ 1 > 0 on M₀. integrableOn: hypothesis, for every compact K ⊆ univ.

3. (Countable rectifiability.) Every x ∈ Good belongs to some M_j, so Z := M₀ ∖ ⋃_j M_j ⊆ M₀ ∖ Good is H-null. Z is countably k-rectifiable (countablyRectifiable_of_measure_zero), each M_j is (field countablyRectifiable of its triple), so the countable union Z ∪ ⋃_j M_j is countably k-rectifiable (countablyRectifiable_iUnion applied to the sequence Z, M_0, M_1, …), and M₀ ⊆ Z ∪ ⋃_j M_j is countably k-rectifiable (CountablyRectifiable.mono).

4. (Measurability of ξ₀.) For each j, ξ_j is H⌞M_j-a.e. strongly measurable (field aestronglyMeasurable) and M_j is H-null-measurable, so g_j := M_j.indicator ξ_j is H-a.e. strongly measurable (aestronglyMeasurable_indicator_iff₀) and hence H⌞M₀-a.e. strongly measurable. For x ∈ Good, g_j(x) = ξ_j(x) for all large j, so g_j(x) → ξ₀(x). Thus ξ₀ is an H⌞M₀-a.e. limit of a.e. strongly measurable maps into NVector (Eucl N) k, a finite-dimensional normed space whose topology is metrizable, hence ξ₀ is H⌞M₀-a.e. strongly measurable (aestronglyMeasurable_of_tendsto_ae).

5. (Tangent transfer.) Fix j. The following hold:
 (i) Lemma B (weighted_tangent_equiv) for E := M_j, θ := θ_j (null-measurable, locally finite by Step 1, θ_j > 0 and integrable on M_j ∩ K by the triple): H⌞M_j-a.e., ∀Q, W(M_j, θ_j, x, Q) ↔ T(M_j, x, Q).
 (ii) Lemma A (approx_tangent_locality) for E := M_j ∩ M₀ ⊆ E′ := M_j (both null-measurable, M_j locally finite): H⌞(M_j ∩ M₀)-a.e., ∀Q, T(M_j ∩ M₀, x, Q) ↔ T(M_j, x, Q).
 (iii) Lemma A for E := M_j ∩ M₀ ⊆ E′ := M₀ (M₀ locally finite): H⌞(M_j ∩ M₀)-a.e., ∀Q, T(M_j ∩ M₀, x, Q) ↔ T(M₀, x, Q).
 (iv) Lemma B for E := M₀, θ := θ₀ (θ₀ > 0, locally finite by Step 1, integrable by hypothesis): H⌞M₀-a.e., ∀Q, W(M₀, θ₀, x, Q) ↔ T(M₀, x, Q).
 Converting (i) to H⌞M₀, converting (ii) and (iii) to H⌞M₀ by (R2) for M_j ∩ M₀ ⊆ M₀ (with guard x ∈ M_j ∩ M₀, which by (R3) is x ∈ M_j for H⌞M₀-a.e. x), and chaining (i) →, (ii) ←, (iii) →, (iv) ←, we obtain (T_j): for H⌞M₀-a.e. x, if x ∈ M_j then for every Q, W(M_j, θ_j, x, Q) implies W(M₀, θ₀, x, Q).

6. (Orientation of the approximants.) For each j, the field orients of (M_j, θ_j, ξ_j) holds H⌞M_j-a.e.; converting it to H⌞M₀ gives (O_j): for H⌞M₀-a.e. x, if x ∈ M_j then there is an orthonormal τ^j : Fin k → ℝ^N with W(M_j, θ_j, x, span τ^j) and ξ_j(x) = simpleNVector τ^j or ξ_j(x) = −simpleNVector τ^j.

7. (Orientation of the limit.) A countable intersection of H⌞M₀-a.e. properties holds H⌞M₀-a.e. (ae_all_iff), so for H⌞M₀-a.e. x: x ∈ Good, x ∈ M₀, and (T_j), (O_j) hold for every j. Fix such an x. Then θ₀(x) ≥ 1, so θ₀(x) ≠ 0; there is J with x ∈ M_j for all j ≥ J; and ξ_j(x) → ξ₀(x).
 - For j ≥ J, (O_j) gives an orthonormal τ^j with W(M_j, θ_j, x, span τ^j) and ξ_j(x) = ±simpleNVector τ^j, and (T_j) gives W(M₀, θ₀, x, span τ^j).
 - Uniqueness of the weighted approximate tangent space at a point where the weight is nonzero (HasWeightedApproximateTangentSpaceAt.unique, θ₀(x) ≠ 0) gives span τ^J = span τ^j for every j ≥ J.
 - Put τ := τ^J and s := simpleNVector τ. For j ≥ J, frame_sign (fiw_ims_frame_sign with P := N, n := k, applied to the orthonormal families τ^J, τ^j with equal spans) gives simpleNVector τ^j = s or = −s; hence ξ_j(x) ∈ {s, −s} (using −(−s) = s).
 - The set {s, −s} is finite, hence closed in the Hausdorff space NVector (Eucl N) k. The sequence ξ_j(x) lies in it for all j ≥ J and converges to ξ₀(x), so ξ₀(x) ∈ {s, −s} (IsClosed.mem_of_tendsto).
 - Hence τ is orthonormal, W(M₀, θ₀, x, span τ) holds (case j = J of the first item), and ξ₀(x) = simpleNVector τ or ξ₀(x) = −simpleNVector τ: the field orients of (M₀, θ₀, ξ₀) holds at x.

8. (Conclusion.) Steps 2, 3, 4 and 7 give all fields of IsRectifiableTriple univ k M₀ θ₀ ξ₀. ∎

Formalization note. The following Lean proof of exactly this declaration compiles against the frozen commit d8d46c9 (default maxHeartbeats, no set_option, no sorry), with the three sibling declarations as its only non-standard inputs (#print axioms: propext, Classical.choice, Quot.sound and the siblings). It follows Steps 1–8. One instance workaround is needed: Lean does not synthesize TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl N) k), whose topology is ContinuousLinearMap.topologicalSpace; the instance is supplied by ⟨⟨inferInstance, rfl, @EMetric.instIsCountablyGeneratedUniformity (NVector (Eucl N) k) _⟩⟩.
```lean
theorem Submission.imc_isRectifiableTriple_of_eventually_mem :
    ∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k) (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), (∀ j, IsRectifiableTriple (univ : Set (Eucl N)) k (M j) (θ j) (ξ j)) → (∀ j, ∀ x ∈ M j, 1 ≤ θ j x) → NullMeasurableSet M₀ (μHE[k] : Measure (Eucl N)) → (∀ x ∈ M₀, 1 ≤ θ₀ x) → (∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) (μHE[k] : Measure (Eucl N))) → (∀ᵐ x ∂((μHE[k] : Measure (Eucl N)).restrict M₀), (∀ᶠ j in atTop, x ∈ M j) ∧ Tendsto (fun j => ξ j x) atTop (𝓝 (ξ₀ x))) → IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ := by
  have hA := Submission.imc_approxTangent_iff_of_subset
  have hB := Submission.imc_weightedTangent_iff_approxTangent
  have hFrame := Submission.fiw_ims_frame_sign
  intro N k M θ ξ M₀ θ₀ ξ₀ hTri hθ1 hM₀ hθ₀1 hθ₀int hpt
  set H : Measure (Eucl N) := (μHE[k] : Measure (Eucl N)) with hH
  -- 1. local finiteness from θ ≥ 1
  have hfinGen : ∀ (E : Set (Eucl N)) (ϑ : Eucl N → ℝ), NullMeasurableSet E H →
      (∀ x ∈ E, 1 ≤ ϑ x) → ∀ K : Set (Eucl N), IsCompact K → IntegrableOn ϑ (E ∩ K) H →
      H (E ∩ K) < ∞ := by
    intro E ϑ hE h1 K hK hint
    have hEK : NullMeasurableSet (E ∩ K) H := hE.inter hK.measurableSet.nullMeasurableSet
    calc H (E ∩ K) = ∫⁻ _x in E ∩ K, 1 ∂H := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in E ∩ K, ‖ϑ x‖ₑ ∂H := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ hEK] with x hx
          have h := h1 x hx.1
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by linarith)]
          exact ENNReal.one_le_ofReal.mpr h
      _ < ∞ := hint.hasFiniteIntegral
  have hfin : ∀ j, ∀ K : Set (Eucl N), IsCompact K → H (M j ∩ K) < ∞ := fun j K hK =>
    hfinGen (M j) (θ j) (hTri j).nullMeasurableSet (hθ1 j) K hK
      ((hTri j).integrableOn K hK (subset_univ K))
  have hfin₀ : ∀ K : Set (Eucl N), IsCompact K → H (M₀ ∩ K) < ∞ := fun K hK =>
    hfinGen M₀ θ₀ hM₀ hθ₀1 K hK (hθ₀int K hK)
  -- 2. the four tangent statements per j
  have hBj : ∀ j, ∀ᵐ x ∂(H.restrict (M j)), ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j) x Q := fun j =>
    hB N k (M j) (θ j) (hTri j).nullMeasurableSet (hfin j) (hTri j).pos
      (fun K hK => (hTri j).integrableOn K hK (subset_univ K))
  have hB₀ : ∀ᵐ x ∂(H.restrict M₀), ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k M₀ x Q :=
    hB N k M₀ θ₀ hM₀ hfin₀ (fun x hx => lt_of_lt_of_le one_pos (hθ₀1 x hx)) hθ₀int
  have hAj : ∀ j, ∀ᵐ x ∂(H.restrict (M j ∩ M₀)), ∀ Q : Submodule ℝ (Eucl N),
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j ∩ M₀) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j) x Q := fun j =>
    hA N k (M j ∩ M₀) (M j) inter_subset_left ((hTri j).nullMeasurableSet.inter hM₀)
      (hTri j).nullMeasurableSet (hfin j)
  have hA₀ : ∀ j, ∀ᵐ x ∂(H.restrict (M j ∩ M₀)), ∀ Q : Submodule ℝ (Eucl N),
      Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k (M j ∩ M₀) x Q ↔
        Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt k M₀ x Q := fun j =>
    hA N k (M j ∩ M₀) M₀ inter_subset_right ((hTri j).nullMeasurableSet.inter hM₀) hM₀ hfin₀
  -- 3. transfer (T_j) and orientation (O_j), as M₀-a.e. statements guarded by x ∈ M j
  have hTj : ∀ j, ∀ᵐ x ∂(H.restrict M₀), x ∈ M j → ∀ Q : Submodule ℝ (Eucl N),
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x Q →
        HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x Q := by
    intro j
    have hjM : NullMeasurableSet (M j ∩ M₀) H := (hTri j).nullMeasurableSet.inter hM₀
    have h1 := (ae_restrict_iff'₀ (hTri j).nullMeasurableSet).1 (hBj j)
    have h2 := (ae_restrict_iff'₀ hjM).1 (hAj j)
    have h3 := (ae_restrict_iff'₀ hjM).1 (hA₀ j)
    have h4 := (ae_restrict_iff'₀ hM₀).1 hB₀
    rw [ae_restrict_iff'₀ hM₀]
    filter_upwards [h1, h2, h3, h4] with x h1 h2 h3 h4 hx0 hxj Q hW
    exact (h4 hx0 Q).2 ((h3 ⟨hxj, hx0⟩ Q).1 ((h2 ⟨hxj, hx0⟩ Q).2 ((h1 hxj Q).1 hW)))
  have hOj : ∀ j, ∀ᵐ x ∂(H.restrict M₀), x ∈ M j → ∃ τ : Fin k → Eucl N, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k (M j) (θ j) x (Submodule.span ℝ (range τ)) ∧
      (ξ j x = simpleNVector τ ∨ ξ j x = -simpleNVector τ) := fun j =>
    ae_restrict_of_ae ((ae_restrict_iff'₀ (hTri j).nullMeasurableSet).1 (hTri j).orients)
  -- 4. orientation of the limit
  have horients : ∀ᵐ x ∂(H.restrict M₀), ∃ τ : Fin k → Eucl N, Orthonormal ℝ τ ∧
      HasWeightedApproximateTangentSpaceAt k M₀ θ₀ x (Submodule.span ℝ (range τ)) ∧
      (ξ₀ x = simpleNVector τ ∨ ξ₀ x = -simpleNVector τ) := by
    have hTall := ae_all_iff.2 hTj
    have hOall := ae_all_iff.2 hOj
    have hmem : ∀ᵐ x ∂(H.restrict M₀), x ∈ M₀ := ae_restrict_mem₀ hM₀
    filter_upwards [hpt, hTall, hOall, hmem] with x hx hT hO hxM
    obtain ⟨hev, hlim⟩ := hx
    have hθx : θ₀ x ≠ 0 := (lt_of_lt_of_le one_pos (hθ₀1 x hxM)).ne'
    obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
    choose! τ hτon hτW hτξ using hO
    refine ⟨τ J, hτon J (hJ J le_rfl), hT J (hJ J le_rfl) _ (hτW J (hJ J le_rfl)), ?_⟩
    set s := simpleNVector (τ J) with hs
    have hmem' : ∀ᶠ j in atTop, ξ j x ∈ ({s, -s} : Set (NVector (Eucl N) k)) := by
      filter_upwards [eventually_ge_atTop J] with j hj
      have hxj : x ∈ M j := hJ j hj
      have hspan : Submodule.span ℝ (range (τ J)) = Submodule.span ℝ (range (τ j)) :=
        HasWeightedApproximateTangentSpaceAt.unique hθx
          (hT J (hJ J le_rfl) _ (hτW J (hJ J le_rfl))) (hT j hxj _ (hτW j hxj))
      have hsign := hFrame N k (τ J) (τ j) (hτon J (hJ J le_rfl)) (hτon j hxj) hspan
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hτξ j hxj with h | h <;> rcases hsign with h' | h'
      · exact Or.inl (by rw [h, h'])
      · exact Or.inr (by rw [h, h'])
      · exact Or.inr (by rw [h, h'])
      · exact Or.inl (by rw [h, h']; ext α; simp [s])
    have hcl : IsClosed ({s, -s} : Set (NVector (Eucl N) k)) := (Set.toFinite _).isClosed
    have := hcl.mem_of_tendsto hlim hmem'
    simpa using this
  -- 5. countable rectifiability
  have hcr : CountablyRectifiable k M₀ := by
    have hZ : H (M₀ \ ⋃ j, M j) = 0 := by
      have h : ∀ᵐ x ∂(H.restrict M₀), x ∈ ⋃ j, M j := by
        filter_upwards [hpt] with x hx
        obtain ⟨j, hj⟩ := hx.1.exists
        exact mem_iUnion.2 ⟨j, hj⟩
      rw [ae_restrict_iff'₀ hM₀, ae_iff] at h
      refine measure_mono_null (fun x hx => ?_) h
      simp only [Set.mem_ofPred_eq, not_imp]
      exact ⟨hx.1, hx.2⟩
    let S : ℕ → Set (Eucl N) := fun i => Nat.casesOn i (M₀ \ ⋃ j, M j) (fun j => M j)
    have hS : ∀ i, CountablyRectifiable k (S i) := by
      intro i
      cases i with
      | zero => exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero hZ
      | succ j => exact (hTri j).countablyRectifiable
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion S hS).mono fun x hx => ?_
    by_cases h : x ∈ ⋃ j, M j
    · obtain ⟨j, hj⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨j + 1, hj⟩
    · exact mem_iUnion.2 ⟨0, ⟨hx, h⟩⟩
  -- 6. measurability of ξ₀
  have hmeas : AEStronglyMeasurable ξ₀ (H.restrict M₀) := by
    have : TopologicalSpace.PseudoMetrizableSpace (NVector (Eucl N) k) :=
      ⟨⟨inferInstance, rfl, @EMetric.instIsCountablyGeneratedUniformity (NVector (Eucl N) k) _⟩⟩
    have hg : ∀ j, AEStronglyMeasurable ((M j).indicator (ξ j)) (H.restrict M₀) := fun j =>
      ((aestronglyMeasurable_indicator_iff₀ (hTri j).nullMeasurableSet).2
        (hTri j).aestronglyMeasurable).restrict
    refine aestronglyMeasurable_of_tendsto_ae atTop hg ?_
    filter_upwards [hpt] with x hx
    refine hx.2.congr' ?_
    filter_upwards [hx.1] with j hj
    rw [indicator_of_mem hj]
  exact { subset := subset_univ _, nullMeasurableSet := hM₀, countablyRectifiable := hcr,
          pos := fun x hx => lt_of_lt_of_le one_pos (hθ₀1 x hx),
          integrableOn := fun K hK _ => hθ₀int K hK,
          aestronglyMeasurable := hmeas, orients := horients }
```

## Key steps

1. θ ≥ 1 gives local finiteness of H⌞M_j and H⌞M₀; subset, measurability, positivity and integrability of (M₀, θ₀) are hypotheses.
2. M₀ ⊆ ⋃_j M_j up to an H-null set (countable rectifiability); ξ₀ is the H⌞M₀-a.e. limit of M_j.indicator ξ_j (measurability).
3. Lemma B, Lemma A twice and Lemma B: for H⌞M₀-a.e. x ∈ M_j, weighted tangent spaces of (M_j, θ_j) at x are weighted tangent spaces of (M₀, θ₀).
4. At a.e. x: for j ≥ J(x), span τ^j is the unique weighted tangent space of (M₀, θ₀) at x, and frame_sign puts ξ_j(x) in {s, −s}, s = simpleNVector τ^J.
5. {s, −s} is closed, so ξ₀(x) = lim ξ_j(x) = ±s with W(M₀, θ₀, x, span τ^J): the orientation field holds.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp <snapshot>/project/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Submission.lean (all byte-identical)`
- `grep '^import' <snapshot>/project/GMT/Ch06/Contract.lean (8 imports) and a transitive SimonGMT import-closure walk (13 modules; Chapter01.Lusin not included)`
- `rg -n 'theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le|exists_hasCompactSupport_integral_sub_le' <snapshot>/mathlib/Mathlib (ContinuousMapDense.lean:141, :226); rg -n 'theorem ContinuousMap.exists_extension' <snapshot>/mathlib/Mathlib (TietzeExtension.lean:77): both files are outside the frozen closure`
- `rg -n 'theorem cauchySeq_of_edist_le_of_tsum_ne_top|theorem edist_le_tsum_of_edist_le_of_tendsto|theorem tendsto_integral_of_L1|theorem lintegral_tsum|theorem integral_indicator₀|theorem dist_convolution_le|theorem exists_continuous_zero_one_of_isClosed' <snapshot>/mathlib/Mathlib`
- `rg -n 'imc_' <snapshot>/project <snapshot>/mathlib and lake-packages-25730c7c/simongmt (no match); git log --all -S <each new imc_ name> (no commit); grep of the new names over runs/*/nodes (no match)`
- `python3 -I over dag.json: status, candidate commit, parent and lean_statement of the five reused names and of lpf_wtc_ae_zero_density_off_set; comparison of every new child type against all DAG node types (no duplicate); simulation of runtime.py _existing_lean_name_problem/_accepted_checkpoint and _topological on the current DAG (no problem; acyclic)`
- `sed -n 6532,6575p /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (reuse rule), leaf_verification.py check_source_delta (no set_option in a leaf delta), decomposition_scope.py (recomputed parent_contract_digest 94deade2…)`
- `git show 12d217bba2a4:GMT/Ch06/Submission.lean (accepted zero-density proof) and git show 83e1f61809c1:GMT/Ch06/Submission.lean (accepted fiw_im_mass_formula: inline L¹ density and mollification)`
- `lake env lean /tmp/imc_v2/lean/Avail2.lean, Api3–Api7.lean (closure probes: Tietze, ContinuousMapDense, UniformContinuous.exists_contDiff_dist_le and Measurable.nat_floor absent; ContDiffBump, HasCompactSupport.contDiff_convolution_left and Lp.ae_tendsto_of_cauchy_eLpNorm present; NVector ContinuousAdd/PseudoMetrizableSpace workarounds)`
- `python3 -I /tmp/imc_v2/scripts/build_stmts.py (validate_lean_statement on all 13 types) and lake env lean /tmp/imc_v2/lean/Stmts.lean (all elaborate; only sorry warnings)`
- `lake env lean /tmp/imc_v2/lean/Test_deformation_im_completeness.lean, Test_imc_im_density_limit.lean, Test_imc_isRectifiableTriple_of_eventually_mem.lean, Test_imc_ae_tendsto_of_summable_lintegral.lean, Test_imc_ae_zero_density_off_set.lean (all compile at default heartbeats; standard axioms plus the stand-in sibling axioms)`
- `sed -n 560,735p book/sources/chapter-01-source.txt (Simon Ch. 1, 3.3–3.7 and the 5-times covering lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-lusi-5c440af24d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-blow-7c8d1035a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-mass-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/decomposition_scope.py`
- `/tmp/imc_v2/lean/Stmts.lean`
- `/tmp/imc_v2/lean/Test_deformation_im_completeness.lean`
- `/tmp/imc_v2/lean/Test_imc_im_density_limit.lean`
- `/tmp/imc_v2/lean/Test_imc_isRectifiableTriple_of_eventually_mem.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_tendsto_of_summable_lintegral.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_zero_density_off_set.lean`

Pinned revisions confirmed: the frozen contract is byte-identical to the snapshot (Submission = Contract). The frozen import closure lacks Tietze (TietzeExtension.lean), L¹ density of C_c (ContinuousMapDense.lean) and SimonGMT Lusin. So mass_lower_bound's approximation step is proved inline from regularity, Urysohn and MemLp.induction_dense, as the accepted fiw_im_mass_formula does. Mathlib supplies the Riesz–Fischer and limit tools used by l1_cauchy_limit and density_limit (cauchySeq_of_edist_le_of_tsum_ne_top, edist_le_tsum_of_edist_le_of_tendsto, tendsto_integral_of_L1). Following the correction, the zero-density child uses the fresh name imc_ae_zero_density_off_set and is the W = ℝ^Q case of the accepted lpf_wtc_ae_zero_density_off_set; its Lean proof embeds that accepted proof (commit 12d217bb) and compiles. The five reused names are accepted checkpoints with identical types, and the controller's name check simulated on the current DAG passes. All 13 types validate and elaborate in the comparator scope. The parent compiles from mass_lower_bound, density_limit and tau_integrable; density_limit, limit_triple and l1_cauchy_limit also compile from their siblings; all at default heartbeats with axioms propext, Classical.choice and Quot.sound only. No imc_ name occurs in the project, SimonGMT, Mathlib, git history or the DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
