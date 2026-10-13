<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1 -->

## Theorem `Submission.dph_hausdorff_product_formula`

Let P, m ∈ ℕ. Write Φ(s, x) := (s, x_1, …, x_P) ∈ ℝ^{P+1} for s ∈ ℝ, x ∈ ℝ^P (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) and π(y) := (y_1, …, y_P) ∈ ℝ^P for y = (y_0, …, y_P) ∈ ℝ^{P+1} (Lean: (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y))), so {y : π(y) ∈ S} = Φ(ℝ × S). Hᵏ := μHE[k]. (a) If N ⊆ ℝ^P and H^m(N) = 0 then H^{m+1}({y : π(y) ∈ N}) = 0. (b) If A ⊆ ℝ^P is H^m-null-measurable, countably m-rectifiable and H^m(A ∩ K) < ∞ for every compact K, then for every Borel g : ℝ^{P+1} → [0, ∞]: ∫⁻_{ {y : π(y) ∈ A} } g dH^{m+1} = ∫⁻_ℝ ∫⁻_A g(Φ(s, x)) dH^m(x) ds (product formula H^{m+1}⌞(ℝ × A) = L¹ ⊗ H^m⌞A, Federer 3.2.23).

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4586

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3756, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3758, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3765, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3768

## Lean problem

Declaration: `Submission.dph_hausdorff_product_formula`

```lean
(∀ (P m : ℕ) (N : Set (Eucl P)), (μHE[m] : Measure (Eucl P)) N = 0 → (μHE[m + 1] : Measure (Eucl (P + 1))) {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ N} = 0) ∧ (∀ (P m : ℕ) (A : Set (Eucl P)), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P)))
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

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.hausdorff_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Role and provenance. This child is the product formula 3.5(b) of the supplied proof of deformation_pushforward_homotopy (H^{k+1}⌞(ℝ × A) = L¹ ⊗ H^k⌞A for null-measurable, countably k-rectifiable, locally H^k-finite A, together with the null-cylinder property), stated for the whole line ℝ; the sibling interval_product_im derives the slab version over a bounded interval I by applying it to g·1_{t∈I}. It is a fresh declaration, Submission.dph_hausdorff_product_formula, whose frozen Lean type, title and statement are byte-identical to those of the comparator-accepted declaration Submission.iwl_cr_hausdorff_product_formula (DAG node root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1, candidate commit 0bfba9891418f887822d6878214d8c1c46326aaa). The first decomposition attempt of this parent reused that name and was rejected because the name was still reserved by that node while it was active under another parent; as the correction requires, a globally unique bare identifier is used here. Since the two statements are identical, the accepted, independently audited natural-language proof of that statement proves this child, and it is reproduced verbatim below. In the reproduced text, "the parent proof" means the proof of root.integrality_weak_limits-a1.cycle_reduction-a1 (where the same formula was first isolated, as its Part I, item 5); here the formula plays the role of item 3.5(b) of the supplied proof. The variables are named P, m as in the statement (the sibling interval_product_im applies it with P := m and m := k). No sibling declaration is used (depends_on = []).

Proof.

Source. This is the product formula cited in Part I, item 5 of the parent proof: “H^{m+1}⌞((0,1) × M) = L¹⌞(0,1) ⊗ H^m⌞M (product formula for Hausdorff measure on rectifiable sets, Federer 3.2.23)” and “(0,1) × M_0 is H^{m+1}-null”. It is isolated as a named lemma and proved completely here.
- Part (a) is an elementary covering argument.
- Part (b) follows Federer's route to 3.2.23 (H. Federer, Geometric Measure Theory, 1969, 3.2.23; cf. its use in arXiv:2505.11279). Cut the Lipschitz parametrizations of A into injective Lipschitz pieces, apply the area formula for Lipschitz maps in dimensions m and m + 1, and use Tonelli.
- No C¹ chart cover is used, and no DAG declaration is needed (depends_on = []).
- The piece construction of Steps 6–7 is the one in the comparator-accepted proof of rectifiability_weighted_tangent_ae (node root.rectifiability-a1.weighted_tangent_ae-a1, Step 4(a)–(d) of its natural proof; Lean code in commit 2f36576, hypothesis `hpart`), specialized to dimension m.
- Every external input is a theorem of the pinned libraries (Library account below); each has #print axioms = [propext, Classical.choice, Quot.sound].

Library account (pinned Mathlib 25730c7c and SimonGMT 2b36630).
- (L1) Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn (simongmt Poincare/SimonGMT/Chapter02/AreaLipschitz.lean:101).
  - Statement: let E, F be finite-dimensional real inner product spaces with Borel σ-algebras, f : E → F with LipschitzWith K f, s ⊆ E a MeasurableSet with InjOn f s, and g : F → [0, ∞] arbitrary (no measurability is needed). Then ∫⁻_{f '' s} g dμHE[finrank ℝ E] = ∫⁻_{x ∈ s} ENNReal.ofReal(J_f(x))·g(f(x)) dvolume(x).
  - Normalization: the target measure is Mathlib's normalized Hausdorff measure μHE. The source measure is Lebesgue measure volume. J_f(x) := Poincare.SimonGMT.Chapter02.areaJacobianAt f x = (fderiv ℝ f x).normDet (areaJacobianAt_eq_normDet), which is Simon's √det(Df(x)* Df(x)) of (3.3) (areaJacobianAt_eq_sqrt_det_adjoint_comp). For E = Eucl k, finrank ℝ E = k (finrank_euclideanSpace_fin), so the left side is the integral with respect to μHE[k].
  - Provenance: AreaLipschitz.lean derives (L1) from weighted_area_formula_volume_of_injective_derivative (Chapter02/WeightedArea.lean:120). That is the volume-normalized form of weighted_area_formula_of_injective_derivative (WeightedArea.lean:76), the area formula for maps that are injective on s with injective derivative at every point of s. The derivation discards the null images of the Rademacher exceptional set and of the critical set, so no rank or everywhere-differentiability hypothesis remains.
- (L2) Poincare.SimonGMT.Chapter02.areaRegularSet f := {x | DifferentiableAt ℝ f x ∧ Injective (fderiv ℝ f x)}. It is measurable (measurableSet_areaRegularSet, AreaLipschitz.lean:34). For Lipschitz f and every s, μHE[finrank ℝ E](f '' (s ∖ areaRegularSet f)) = 0 (area_image_compl_regularSet_eq_zero, AreaLipschitz.lean:59; Rademacher's theorem and the null critical image).
- (L3) Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt (Chapter02/AreaApproximation.lean:44): x ↦ J_f(x) is Borel.
- (L4) Mathlib exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255), for f : E → F with E finite-dimensional and F second countable.
  - Input: hf′ : ∀ x ∈ s, HasFDerivWithinAt f (f′ x) s x, and r : (E →L[ℝ] F) → ℝ≥0 with r A ≠ 0.
  - Output: pairwise disjoint measurable t_n with s ⊆ ⋃_n t_n, and A_n with ApproximatesLinearOn f (A_n) (s ∩ t_n) (r(A_n)), i.e. ‖f x − f y − A_n(x − y)‖ ≤ r(A_n)‖x − y‖ on s ∩ t_n; moreover s.Nonempty → ∀ n, ∃ y ∈ s, A_n = f′ y.
- (L5) Mathlib MeasurableSet.image_of_continuousOn_injOn (Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:821): the image of a Borel subset of a Polish space under a map that is continuous and injective on it is Borel.
- (L6) Mathlib LinearMap.injective_iff_antilipschitz (Mathlib/Analysis/Normed/Module/FiniteDimension.lean:242), and LinearMap.normDet_sq_eq_det_gram (Mathlib/Analysis/InnerProductSpace/NormDet.lean:303): normDet(L)² = det(⟨L b_i, L b_j⟩)_{i,j} for every orthonormal basis b of the source.
- (L7) Measure theory:
  - Sets and Hausdorff measures: NullMeasurableSet.exists_measurable_subset_ae_eq; Measure.euclideanHausdorffMeasure_def (μHE[k] = c_k • μH[k] with c_k := volume.addHaarScalarFactor μH[k] ∈ ℝ≥0, nonzero by addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, hence 0 < c_k < ∞); Measure.euclideanHausdorffMeasure_zero (μHE[0] = μH[0]); Measure.hausdorffMeasure_zero_singleton (μH[0]{x} = 1); Measure.hausdorffMeasure_apply (the δ-cover formula for μH[d]).
  - Integrals: lintegral_prod; Measurable.lintegral_prod_right'; lintegral_iUnion; lintegral_tsum; setLIntegral_congr.
  - Volume: measurePreserving_piFinSuccAbove; PiLp.volume_preserving_ofLp; PiLp.volume_preserving_toLp.

Conventions.
- E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1), and Hᵏ := μHE[k] on the relevant space. vol denotes Lebesgue measure (volume) on ℝ and on Eucl k.
- For s ∈ ℝ and x ∈ E, Φ(s,x) := (s, x_1, …, x_P) ∈ E′ (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))). For y ∈ E′, y_0 is its 0-th coordinate and π(y) := (y_1, …, y_P) ∈ E (Lean as in the statement).
- Then π(Φ(s,x)) = x, y = Φ(y_0, π(y)), and ⟨Φ(s,x), Φ(s′,x′)⟩ = ss′ + ⟨x, x′⟩. In particular ‖Φ(s,x) − Φ(s′,x′)‖² = (s − s′)² + ‖x − x′‖².
- For S ⊆ E write Ŝ := {y : π(y) ∈ S} = Φ(ℝ × S). The map S ↦ Ŝ commutes with unions, intersections and differences, and Ŝ is Borel when S is (π is continuous linear).
- By (L7), μHE[k] and μH[k] have the same null sets.

Part (a). Let N ⊆ E with H^m(N) = 0. We show H^{m+1}(N̂) = 0.
1. (m = 0.) μHE[0] = μH[0] and μH[0]({x}) = 1 for every x (L7). So H^0(N) = 0 forces N = ∅, and then N̂ = ∅.
2. (m ≥ 1: what suffices.) N̂ = ⋃_{a ∈ ℤ} Φ([a, a+1] × N), so by countable subadditivity it suffices to show μH[m+1](Φ([a, a+1] × N)) = 0 for each a ∈ ℤ.
   - By hausdorffMeasure_apply, μH[m+1](S) = sup_{r>0} inf Σ_n diam(t_n)^{m+1}, the infimum over countable covers (t_n) of S with diam t_n ≤ r. (For m + 1 ≥ 1 the factor ⨆_{t_n ≠ ∅} is harmless because diam ∅ = 0.)
   - So it suffices: for every r > 0 and ε′ > 0, Φ([a, a+1] × N) has a countable cover by sets of diameter ≤ r with Σ diam^{m+1} ≤ ε′.
   - Given r, fix δ ∈ (0, 1) with √2·δ ≤ r. Steps 3–4 produce, for every ε ∈ (0, (δ/2)^m), such a cover with diameters ≤ √2·δ and Σ diam^{m+1} ≤ 2^{2+(m+1)/2}·ε.
3. (Covering N.) Since μH[m](N) = 0, the infimum in hausdorffMeasure_apply for the radius δ/2 is 0. So there are sets C_i (i ∈ ℕ) with N ⊆ ⋃_i C_i, diam C_i ≤ δ/2 and Σ_i (diam C_i)^m < ε. (Because m ≥ 1, (diam ∅)^m = 0^m = 0, so the factor ⨆_{C_i ≠ ∅} can be dropped. All diameters here are finite, so ediam = diam.)
   - Put d_i := max(diam C_i, (ε·2^{−i−1})^{1/m}).
   - Then 0 < d_i ≤ max(δ/2, ε^{1/m}) < δ < 1, and d_i^m ≤ (diam C_i)^m + ε·2^{−i−1}, so Σ_i d_i^m < 2ε.
4. (Covering the strip.) Let k_i := ⌈1/d_i⌉ ≤ 1/d_i + 1 ≤ 2/d_i.
   - [a, a+1] ⊆ ⋃_{k=0}^{k_i−1} [a + k·d_i, a + (k+1)·d_i], so Φ([a, a+1] × C_i) ⊆ ⋃_{k<k_i} Q_{i,k} with Q_{i,k} := Φ([a + k·d_i, a + (k+1)·d_i] × C_i).
   - By the distance formula, diam Q_{i,k} ≤ √(d_i² + (diam C_i)²) ≤ √2·d_i < √2·δ.
   - The countable family (Q_{i,k}) covers Φ([a, a+1] × N), and Σ_{i,k} (diam Q_{i,k})^{m+1} ≤ Σ_i (2/d_i)(√2·d_i)^{m+1} = 2^{1+(m+1)/2}·Σ_i d_i^m ≤ 2^{2+(m+1)/2}·ε.
   - To apply hausdorffMeasure_apply, index the family by ℕ: send n to Q_{i,k} if n = Nat.pair i k with k < k_i, and to ∅ otherwise. Empty sets contribute 0 because of the factor ⨆_{t_n ≠ ∅}.
   - By Step 2, μH[m+1](Φ([a, a+1] × N)) = 0 for every a, hence H^{m+1}(N̂) = 0.

Part (b). Let A be as in (b) and g : E′ → [0, ∞] measurable.
For B ⊆ E and s ∈ ℝ write:
- LHS(B) := ∫⁻_{B̂} g dH^{m+1};
- φ_B(s) := ∫⁻_{x ∈ B} g(Φ(s,x)) dH^m(x);
- RHS(B) := ∫⁻_ℝ φ_B(s) ds.
The goal is LHS(A) = RHS(A). The function (s, x) ↦ g(Φ(s,x)) is Borel on ℝ × E (Φ is continuous).

5. (Reduction to Borel A.) By NullMeasurableSet.exists_measurable_subset_ae_eq there is a Borel A₀ ⊆ A with H^m(A ∖ A₀) = 0.
   - Â = Â₀ ∪ (A ∖ A₀)^, and H^{m+1}((A ∖ A₀)^) = 0 by Part (a). So Â =ᵐ Â₀ for H^{m+1}, and LHS(A) = LHS(A₀) (setLIntegral_congr).
   - For every s, A =ᵐ A₀ for H^m, so φ_A(s) = φ_{A₀}(s) and RHS(A) = RHS(A₀).
   - A₀ is countably m-rectifiable (CountablyRectifiable.mono) and H^m(A₀ ∩ K) ≤ H^m(A ∩ K) < ∞ for compact K.
   - So we may and do assume that A is Borel.
   - Then H^m⌞A is σ-finite: E = ⋃_k B̄_k(0) and H^m(A ∩ B̄_k(0)) < ∞. Hence H^m⌞A′ is σ-finite (in particular s-finite) for every Borel A′ ⊆ A.
6. (Injective Lipschitz pieces.) By CountablyRectifiable m A, A ⊆ M₀ ∪ ⋃_i F_i(Eucl m) with H^m(M₀) = 0 and F_i : Eucl m → E satisfying LipschitzWith K_i F_i.
   - Fix i and let R_i := areaRegularSet F_i, which is Borel by (L2). For b ∈ R_i, F_i has Fréchet derivative fderiv ℝ F_i b at b, hence HasFDerivWithinAt F_i (fderiv ℝ F_i b) R_i b.
   - For each injective continuous linear L : Eucl m → E, fix by (L6) a constant c_L > 0 with ‖Lv‖ ≥ c_L‖v‖ for all v, and put r(L) := c_L/2. Put r(L) := 1 if L is not injective. Then r(L) ≠ 0 for all L.
   - Apply (L4) to F_i, s := R_i, f′ := fderiv ℝ F_i and r. This gives pairwise disjoint Borel sets t_{i,l} (l ∈ ℕ) with R_i ⊆ ⋃_l t_{i,l}, and continuous linear maps A_{i,l}, with the following properties.
     - Put S_{i,l} := R_i ∩ t_{i,l} (Borel). Then ‖F_i(b) − F_i(b′) − A_{i,l}(b − b′)‖ ≤ r(A_{i,l})·‖b − b′‖ for b, b′ ∈ S_{i,l}.
     - If R_i ≠ ∅, then A_{i,l} = fderiv ℝ F_i y for some y ∈ R_i, which is injective by the definition of R_i.
   - Hence, if S_{i,l} ≠ ∅, A_{i,l} is injective and, with c := c_{A_{i,l}} > 0, for b, b′ ∈ S_{i,l}: ‖F_i(b) − F_i(b′)‖ ≥ ‖A_{i,l}(b − b′)‖ − (c/2)‖b − b′‖ ≥ (c/2)‖b − b′‖. So F_i is injective on S_{i,l} (trivially also if S_{i,l} = ∅).
   - Enumerate the pairs (i, l) by p ∈ ℕ via (i, l) = Nat.unpair p, and write G_p := F_i and S_p := S_{i,l}. Then:
     - G_p is LipschitzWith K_i and S_p is Borel;
     - G_p is injective on S_p and differentiable at every point of S_p (S_p ⊆ R_i);
     - G_p '' S_p is Borel by (L5) (Eucl m is Polish and G_p is continuous).
   - Let N := M₀ ∪ ⋃_i F_i '' (Eucl m ∖ R_i). Then H^m(N) = 0 by (L2) (with s := Eucl m and finrank ℝ (Eucl m) = m) and countable subadditivity.
   - A ⊆ N ∪ ⋃_p G_p '' S_p. Indeed, if x ∈ A ∖ M₀, then x = F_i(b) for some i and b. If b ∉ R_i then x ∈ N. Otherwise b ∈ t_{i,l} for some l, so x ∈ G_p '' S_p for the index p of (i, l).
7. (Disjoint pieces.) Put A_p := (A ∩ G_p '' S_p) ∖ ⋃_{q<p} G_q '' S_q and B_p := S_p ∩ G_p⁻¹(A_p).
   - Both are Borel (Step 5, Step 6, continuity of G_p).
   - The A_p are pairwise disjoint subsets of A.
   - A ∖ ⋃_p A_p ⊆ N: if x ∈ A ∖ N, let p be the least index with x ∈ G_p '' S_p; then x ∈ A_p.
   - G_p maps B_p bijectively onto A_p, because A_p ⊆ G_p '' S_p and G_p is injective on S_p ⊇ B_p.
8. (Area formula in dimension m.) For each p and every function u : E → [0, ∞], (L1) with f := G_p and s := B_p (measurable, InjOn, G_p '' B_p = A_p) gives
   ∫⁻_{A_p} u dH^m = ∫⁻_{b ∈ B_p} J_p(b)·u(G_p(b)) db, where J_p(b) := ENNReal.ofReal(areaJacobianAt G_p b).   (8.1)
9. (The lifted pieces.) For w ∈ Eucl (m+1), let w_0 be its 0-th coordinate and tl(w) ∈ Eucl m its remaining coordinates (Lean: (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ w))). Then ‖w − w′‖² = (w_0 − w′_0)² + ‖tl w − tl w′‖².
   Define G̃_p : Eucl (m+1) → E′ by G̃_p(w) := Φ(w_0, G_p(tl w)), and B̃_p := {w : tl w ∈ B_p} (Borel).
   (i) G̃_p is Lipschitz: ‖G̃_p(w) − G̃_p(w′)‖² = (w_0 − w′_0)² + ‖G_p(tl w) − G_p(tl w′)‖² ≤ max(1, K_i)²·‖w − w′‖².
   (ii) G̃_p is injective on B̃_p. If G̃_p(w) = G̃_p(w′), then w_0 = w′_0 and G_p(tl w) = G_p(tl w′). Hence tl w = tl w′, as both lie in B_p ⊆ S_p, and so w = w′.
   (iii) G̃_p '' B̃_p = Â_p.
       - For w ∈ B̃_p, π(G̃_p(w)) = G_p(tl w) ∈ A_p.
       - Conversely, if π(y) ∈ A_p, then π(y) = G_p(b) with b ∈ B_p. The w with w_0 = y_0 and tl w = b satisfies G̃_p(w) = Φ(y_0, π(y)) = y.
   (iv) (Jacobian.) Let w ∈ B̃_p, b := tl w ∈ S_p and L := fderiv ℝ G_p b (G_p is differentiable at b). We show areaJacobianAt G̃_p w = areaJacobianAt G_p (tl w), so J̃_p(w) = J_p(tl w) on B̃_p.
       - By the chain rule G̃_p is differentiable at w with derivative L̃(ω) = ω_0·Φ(1,0) + Φ(0, L(tl ω)).
       - Let (e_0, …, e_m) and (e′_0, …, e′_{m−1}) be the standard orthonormal bases of Eucl (m+1) and Eucl m (0-based, as in Lean's Fin). Then L̃e_0 = Φ(1,0) and L̃e_{j+1} = Φ(0, L e′_j) for 0 ≤ j < m, since (e_{j+1})_0 = 0 and tl e_{j+1} = e′_j (Lean: tl (single j.succ 1) = single j 1).
       - Since ‖Φ(1,0)‖ = 1, ⟨Φ(1,0), Φ(0,v)⟩ = 0 and ⟨Φ(0,u), Φ(0,v)⟩ = ⟨u, v⟩, the Gram matrix (⟨L̃e_i, L̃e_j⟩)_{0≤i,j≤m} has first row and column (1, 0, …, 0). Its entry at (i+1, j+1) is ⟨Le′_i, Le′_j⟩.
       - Expanding along the first row (Matrix.det_succ_row_zero), its determinant is det(⟨Le′_i, Le′_j⟩)_{0≤i,j<m}.
       - By (L6) and areaJacobianAt = normDet ∘ fderiv, (areaJacobianAt G̃_p w)² = (areaJacobianAt G_p b)². Both are ≥ 0, so they are equal.
       - For m = 0 both sides equal 1: the Gram matrices are (1) and the empty matrix.
10. (Area formula in dimension m+1, then Tonelli.) Fix p.
   - By (L1) with f := G̃_p and s := B̃_p (finrank ℝ (Eucl (m+1)) = m+1), using 9(i)–(iv):
     LHS(A_p) = ∫⁻_{Â_p} g dH^{m+1} = ∫⁻_{w ∈ B̃_p} J_p(tl w)·g(Φ(w_0, G_p(tl w))) dw.
   - Ψ(w) := (w_0, tl w) is measure preserving from vol on Eucl (m+1) to vol ⊗ vol on ℝ × Eucl m. It is the composite of PiLp.volume_preserving_ofLp, measurePreserving_piFinSuccAbove at index 0, and PiLp.volume_preserving_toLp on the second factor. Moreover B̃_p = Ψ⁻¹(ℝ × B_p).
   - The function h(s, b) := 1_{B_p}(b)·J_p(b)·g(Φ(s, G_p(b))) is Borel on ℝ × Eucl m, by (L3), Borel g, and continuity of Φ and G_p.
   - The change of variables along Ψ, Tonelli (lintegral_prod) and (8.1) give
     LHS(A_p) = ∫⁻ h d(vol ⊗ vol) = ∫⁻_ℝ ∫⁻_{b ∈ B_p} J_p(b)·g(Φ(s, G_p(b))) db ds = ∫⁻_ℝ φ_{A_p}(s) ds = RHS(A_p).
     The third equality is (8.1) applied, for each fixed s, to u := g(Φ(s, ·)).
11. (Summation.)
   - The sets Â_p are Borel and pairwise disjoint, and ⋃_p Â_p ⊆ Â. Moreover Â ∖ ⋃_p Â_p = (A ∖ ⋃_p A_p)^ ⊆ N̂, which is H^{m+1}-null by Part (a). Hence, by setLIntegral_congr and lintegral_iUnion, LHS(A) = Σ_p LHS(A_p).
   - For every s, A =ᵐ ⋃_p A_p for H^m (the difference lies in N), so φ_A(s) = Σ_p φ_{A_p}(s).
   - Each φ_{A_p} is measurable by Measurable.lintegral_prod_right', applied to the Borel function (s, x) ↦ g(Φ(s,x)) and the s-finite measure H^m⌞A_p (Step 5). So lintegral_tsum gives RHS(A) = Σ_p RHS(A_p).
   - By Step 10, LHS(A) = Σ_p LHS(A_p) = Σ_p RHS(A_p) = RHS(A). ∎

Implementation notes.
- Submission.lean may add imports: Poincare.SimonGMT.Chapter02.AreaLipschitz, Poincare.SimonGMT.Chapter02.AreaApproximation, Mathlib.MeasureTheory.Function.Jacobian, Mathlib.MeasureTheory.Constructions.Polish.Basic, Mathlib.Analysis.InnerProductSpace.NormDet and Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace. The comparator byte-checks only the frozen inputs.
- During this decomposition, two steps were checked in Lean against the frozen project, with only standard axioms. The checks used the definitions of Φ, tl and G̃_p above.
  - Step 9(iv), as `areaJacobianAt (fun w => Φ(w 0, G (tl w))) w = areaJacobianAt G (tl w)` whenever G is differentiable at tl w. The derivative is (EuclideanSpace.proj 0).smulRight e_0 + Φ(0,·) ∘L fderiv G (tl w) ∘L tl. The proof uses LinearMap.normDet_sq_eq_det_gram with EuclideanSpace.basisFun, Matrix.det_succ_row_zero and pow_left_inj₀.
  - The measure preservation of w ↦ (w 0, tl w) in Step 10, via PiLp.volume_preserving_ofLp, measurePreserving_piFinSuccAbove (index 0) and (MeasurePreserving.id).prod (PiLp.volume_preserving_toLp).

Additional implementation note for this fresh declaration. The comparator-accepted Lean proof of the identical statement (commit 0bfba9891418f887822d6878214d8c1c46326aaa: Submission.iwl_cr_hp_cylinder_null, Submission.iwl_cr_hp_injective_pieces, Submission.iwl_cr_hp_lift_gram_det, Submission.iwl_cr_hp_piece_product and the assembly Submission.iwl_cr_hausdorff_product_formula) formalizes exactly the proof above. A later decomposition of this child may reuse those four comparator-accepted sub-declarations by name with their identical frozen types (they are accepted, so reuse is permitted). In the DAG, iwl_cr_hp_piece_product itself depends on iwl_cr_hp_lift_gram_det, so such a decomposition should include iwl_cr_hp_lift_gram_det among the reused siblings and list it as a dependency of iwl_cr_hp_piece_product. If instead their code is transplanted into this node's candidate, every auxiliary declaration must be renamed with a fresh prefix (for example dph_hp_) so that no Submission.* name of this branch collides with the other branch when the histories are combined.

## Key steps

1. Φ(s,x) = (s,x) is a linear isometry ℝ × ℝ^P → ℝ^{P+1} with {π ∈ S} = Φ(ℝ × S); μHE[k] and μH[k] have the same null sets.
2. (a) Null sets: for m = 0, N = ∅; for m ≥ 1 cover N by sets C_i with Σ diam^m < ε and each strip [a,a+1] × C_i by ≤ 2/d_i boxes of diameter ≤ √2 d_i, so the (m+1)-dimensional δ-content is O(ε).
3. (b) Reduce to Borel A via (a). Cut the Lipschitz parametrizations into injective Lipschitz pieces G_p|S_p (Rademacher and null critical images by area_image_compl_regularSet_eq_zero, Mathlib's approximately-linear partition, Borel injective images). Disjointify to A_p = G_p(B_p), leaving an H^m-null set N.
4. Apply SimonGMT's injective Lipschitz area formula (weighted_area_formula_lipschitz_injOn) to G_p on B_p and to the lift G̃_p(w) = Φ(w_0, G_p(tl w)) on ℝ × B_p. The two Jacobians agree, since the Gram matrix is block-diagonal diag(1, Gram(DG_p)).
5. The measure-preserving splitting ℝ^{m+1} ≅ ℝ × ℝ^m, Tonelli and the m-dimensional area formula give LHS(A_p) = RHS(A_p). Sum over p with lintegral_iUnion and lintegral_tsum; the remainders are null by (a).

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sed -n 1,364p GMT/Ch06/Contract.lean; diff GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical): IsRectifiableTriple, tauAction, IsIntegerMultiplicity, IsLipschitzPushforward, scope namespace GMT.Ch06 with its opens`
- `grep -n '^structure|^def|^abbrev|^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality,FormsDuality,Product,GeometricPointProduct,ParametricCurrentContinuity,AffineCurrentPushforward}.lean: GeometricCurrentOn (sequential continuity at 0), TestFormOnConverges, boundary = T ∘ exteriorDerivativeTestOn, massOn = sSup over covectorEuclideanNorm ≤ 1, support = U \ zeroRegion, covectorPullback = compContinuousLinearMapCLM, nVectorPushforward n L w = w.comp (covectorPullback n L), SimonMultiIndex = Fin n ↪o Fin p. Only point products {p}×T on E × F and affine push-forwards exist; there are no products with [[0,1]] in Eucl (m+1), no Lipschitz push-forward of normal currents and no homotopy formula`
- `grep -n 'def CountablyRectifiable|def HasWeightedApproximateTangentSpaceAt|def blowUpMap' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (lines 34, 330, 96)`
- `sed -n 180,275p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean (Filter.EventuallyEq.extDeriv_eq, extDeriv_apply, extDeriv_pullback)`
- `grep for the library inputs cited in the child proofs: weighted_area_formula_lipschitz_injOn, areaRegularSet, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero (simongmt Chapter02/AreaLipschitz.lean:101,31,34,59); measurable_areaJacobianAt (AreaApproximation.lean:44); exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255); MeasurableSet.image_of_continuousOn_injOn (Constructions/Polish/Basic.lean:821); LinearMap.normDet_sq_eq_det_gram (InnerProductSpace/NormDet.lean:303); LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308); HasCompactSupport.contDiff_convolution_left (Calculus/ContDiff/Convolution.lean:427); exists_contDiff_tsupport_subset (BumpFunction/FiniteDimension.lean:45); norm_fderiv_le_of_lipschitzOn (FDeriv/Basic.lean:939); intervalIntegral.integral_eq_sub_of_hasDerivAt (FundThmCalculus.lean:1148). All found`
- `python3 over dag.json (645 nodes): statuses, lean_names, depends_on and candidate commits of the deformation subtree and of all push-forward/product/homotopy/cutoff/mollifier/slice/hausdorff nodes. Also the isolated-comparator-result.json of the five reused nodes (passed) and the accepted status of every declaration that the child proofs name as reusable later`
- `python3: byte comparison of the hausdorff_product proof, key steps, lean_statement, title and statement with nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json (identical)`
- `git show --stat 0bfba9891418f887822d6878214d8c1c46326aaa; git show 0bfba989:GMT/Ch06/Submission.lean | grep iwl_cr_hp_ (the accepted Lean proof of the identical statement and its four sub-lemmas are present)`
- `rg 'dph_' over GMT/, the local reference project snapshot and simongmt; python3 over dag.json lean_names; git grep 'dph_' over the 1581 distinct commits of all 3680 local refs (no match)`
- `read /runtime/flows/*/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, child activation by Lean name, accepted reused children without handoff) and store.py (Store.update refreshes the shared DAG). Attempt 1's name check ran on a DAG view taken when its attempt started, before the hausdorff node was accepted`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on all 12 child statements and the parent statement (all valid); verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) for the exact child-comparator scope`
- `lake env lean /tmp/dph2/lean/AllStmts.lean: the 12 child statements and the parent statement, each as `theorem _root_.HumanizeNodeComparator.target_<key> : (stmt) := by sorry` after the replayed scope (EXIT 0, 13 sorry warnings, no errors)`
- `lake env lean /tmp/dph2/lean/IfaceCheck.lean: attempt-1 interface check whose hypotheses are byte-identical to the current lipschitz_pushforward and smooth_homotopy statements (clause (8), tail/cons, (E1) and (Aff) instantiations); EXIT 0, no errors`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-im-a1-slice-forms-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-support-null-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dph2/lean/AllStmts.lean`
- `/tmp/dph2/lean/IfaceCheck.lean`

The pinned project and SimonGMT have no push-forward of normal currents, no products with [[0,1]] in Eucl (m+1) and no homotopy formula (only point products on E × F and affine push-forwards), so Parts 1–5 of the supplied proof are new obligations. Five comparator-accepted declarations with no sibling prerequisites cover facts that the supplied proof uses as black boxes, and they are reused by name with byte-identical types: cmb_abs_apply_le_of_massOn_le (F1), isoperimetric_apply_eq_zero_of_disjoint_support (F2), iwl_sp_exists_compatible_testForm (2.1), iwl_cr_ci_slice_testForm (3.1 slices) and iwl_sp_rectifiable_support_null (F9, same type as lpf_rectifiable_support_null). The product formula 3.5(b) becomes the fresh child dph_hausdorff_product_formula, as attempt 1's correction requires; its type is identical to the accepted iwl_cr_hausdorff_product_formula, its proof is that node's accepted proof verbatim, and its accepted Lean code and four accepted sub-declarations can be reused. iwl_cr_interval_product_im (unaccepted) and iwl_smooth_pushforward (integer multiplicity only) are not reused. Every library lemma cited in the child proofs exists in the pinned snapshot. All 12 child statements and the parent elaborate in the exact comparator scope. The seven new names are globally unique, and the Lean interface check of the parent's operator plumbing recompiles against the current statements.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
