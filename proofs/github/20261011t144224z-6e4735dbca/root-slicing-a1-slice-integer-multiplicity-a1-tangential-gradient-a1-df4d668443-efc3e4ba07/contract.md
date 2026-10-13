<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_tangent-a1 -->

## Theorem `Submission.slicing_im_tg_weighted_tangent_chart`

Let Q, n ∈ ℕ (ℝᵏ = EuclideanSpace ℝ (Fin k), Hⁿ = μHE[n]), V ⊆ ℝ^Q open, M ⊆ V Hⁿ-null-measurable, and θ : ℝ^Q → ℝ with θ(y) > 0 for y ∈ M and θ Hⁿ-integrable on M ∩ K for every compact K ⊆ V. Let Ω ⊆ ℝⁿ be open and Φ : ℝⁿ → ℝ^Q of class C¹ such that for some c > 0, c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω. Then for Hⁿ-a.e. y ∈ M ∩ Φ(Ω) and every w ∈ Ω with Φ(w) = y, the subspace DΦ(w)(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w) is a weighted approximate tangent space of (M, θ) at y in the sense of Simon Ch. 3, 1.7, i.e. HasWeightedApproximateTangentSpaceAt n M θ y (DΦ(w)(ℝⁿ)).

Node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_tangent-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2474

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1264, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1266, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1268, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1271, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1273, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1274, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1275, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1276, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1277

## Lean problem

Declaration: `Submission.slicing_im_tg_weighted_tangent_chart`

```lean
∀ (Q n : ℕ) (V M : Set (Eucl Q)) (θ : Eucl Q → ℝ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)), IsOpen V → M ⊆ V → NullMeasurableSet M (μHE[n] : Measure (Eucl Q)) → (∀ y ∈ M, 0 < θ y) → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl Q))) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∀ᵐ y ∂((μHE[n] : Measure (Eucl Q)).restrict (M ∩ Φ '' Ω)), ∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt n M θ y (LinearMap.range (fderiv ℝ Φ w).toLinearMap)
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.tangential_gradient-a1.chart_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝᵏ := EuclideanSpace ℝ (Fin k), |·| Euclidean norm, ⟨·,·⟩ inner product; Lⁿ := volume on ℝⁿ; Hⁿ := μHE[n] on ℝ^Q (translation invariant; Hⁿ(λS) = λⁿHⁿ(S) for λ > 0, Mathlib `MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀`; Hⁿ = Lⁿ on ℝⁿ). B_ρ(y), B̄_ρ(y) are the open and closed balls. η_{y,r}(x) := r⁻¹(x − y) (SimonGMT `blowUpMap y r`), r > 0. By definition, HasWeightedApproximateTangentSpaceAt n M θ y T means: dim T = n and, for every φ ∈ C_c(ℝ^Q), ∫_{η_{y,r}(M)} φ(z) θ(y + rz) dHⁿ(z) → θ(y) ∫_T φ dHⁿ as r ↓ 0; SimonGMT `HasApproximateTangentSpaceAt n S y T` (Simon 1.4) is the same with θ ≡ 1 and S in place of M. Put N := Φ(Ω). This lemma is the existence half of Step 6 of the parent proof, which cites Simon Ch. 3, Remark 1.5(2), the proof of Theorem 1.6 “⟹” and Remark 1.8(1) (weighted version); those printed arguments are copied below, specialised to the single C¹ chart N, with all details filled in. (The parent's parenthetical treats the term θ − θ(y) on M ∩ N via Lebesgue points; following the cited Remark 1.8(1), the same estimate is obtained from compact Lusin pieces C on which θ is continuous, steps 1–4.)

0. Preliminaries on the chart.
 (a) Let w ∈ Ω, s ∈ ℝⁿ. For small |t|, w + ts ∈ Ω (Ω open), so c|t||s| ≤ |Φ(w + ts) − Φ(w)|; dividing by |t| and letting t → 0 gives c|s| ≤ |DΦ(w)s|. Hence DΦ(w) is injective and T_w := DΦ(w)(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w) has dimension n. Φ is injective on Ω (Φ(w) = Φ(w′) forces c|w − w′| ≤ 0). For y ∈ N let w_y denote the unique point of Ω with Φ(w_y) = y; the clause “∀ w ∈ Ω, Φ w = y → …” of the claim only concerns w = w_y. Put T_y := T_{w_y}. The inverse Ψ := (Φ|Ω)⁻¹ : N → Ω is c⁻¹-Lipschitz.
 (b) N is σ-compact (Ω is a countable union of compact sets and Φ is continuous), hence Borel; so M ∩ N is Hⁿ-null-measurable.
 (c) (N is locally Hⁿ-finite.) Let K ⊆ ℝ^Q be compact. Ψ(N ∩ K) has diameter ≤ c⁻¹ diam K, so it lies in a closed ball B̄ ⊆ ℝⁿ. Φ is Λ-Lipschitz on the compact convex set B̄, Λ := max_{B̄}‖DΦ‖ (mean value inequality; Φ is C¹). Hence Hⁿ(N ∩ K) ≤ Hⁿ(Φ(B̄)) ≤ Λⁿ Lⁿ(B̄) < ∞ (SimonGMT `Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn`).
 (d) (Blow-up change of variables.) η_{y,r} is a translation followed by the dilation by r⁻¹, so for every set S ⊆ ℝ^Q and every g : ℝ^Q → ℝ, ∫_{η_{y,r}(S)} g dHⁿ = r^{−n} ∫_S g(η_{y,r}(x)) dHⁿ(x) (Bochner integrals; this is the accepted DAG lemma `lpf_wtc_blowup_setIntegral_image`), and Hⁿ(η_{y,r}(S) ∩ B̄_R(0)) = r^{−n} Hⁿ(S ∩ B̄_{rR}(y)).
 (e) (C¹ blow-up of N; Simon: “since x ∈ N_j and N_j is a C¹ submanifold, lim ∫_{η_{x,λ}(N_j)} f dHⁿ = ∫_{T_x N_j} f dHⁿ”.) Claim: for every y ∈ N and φ ∈ C_c(ℝ^Q), ∫_{η_{y,r}(N)} φ dHⁿ → ∫_{T_y} φ dHⁿ as r ↓ 0 (so N has approximate tangent space T_y at y), and for every R > 0, sup_{0<r≤1} r^{−n} Hⁿ(N ∩ B̄_{rR}(y)) < ∞.
 Proof. Let w := w_y, spt φ ⊆ B_R(0), 0 < r ≤ 1. By (d), ∫_{η(N)} φ dHⁿ = r^{−n} ∫_N φ((x − y)/r) dHⁿ(x). If the integrand is nonzero at x then x = Φ(v) with v ∈ Ω and |Φ(v) − Φ(w)| < rR, hence c|v − w| < rR and |v − w| < R/c. Let Ω′ := Ω ∩ B_{R/c+1}(w): a bounded open set on which Φ is injective and Lipschitz (argument of (c)). By the injective area formula (Simon Ch. 2, (3.5); SimonGMT `Chapter02.injective_area_formula_lipschitzOn`, and in weighted form `Chapter02.weighted_area_formula_lipschitz_injOn` applied to a global Lipschitz extension of Φ|Ω′, which agrees with Φ on the open set Ω′ and so has the same derivative there; applied to φ⁺ and φ⁻ separately), with the area Jacobian JΦ(v) := √det(⟨DΦ(v)e_i, DΦ(v)e_j⟩)_{i,j} (this equals SimonGMT's area Jacobian normDet DΦ(v), by Mathlib `LinearMap.normDet_sq_eq_det_gram` for the standard orthonormal basis of ℝⁿ together with `LinearMap.normDet_nonneg`),
 r^{−n} ∫_N φ((x − y)/r) dHⁿ(x) = r^{−n} ∫_{Ω′} φ((Φ(v) − Φ(w))/r) JΦ(v) dv = ∫_{ℝⁿ} 1_{Ω′}(w + rs) φ((Φ(w + rs) − Φ(w))/r) JΦ(w + rs) ds,
 the last step by the substitution v = w + rs (dv = rⁿ ds). The last integrand vanishes for |s| ≥ R/c and is bounded by sup|φ| · max_{|z−w|≤R/c} JΦ(z) < ∞ (JΦ is continuous since DΦ is; accepted DAG lemma `lpf_wtc_cat_gram_jacobian_continuous`). For fixed s, as r ↓ 0: w + rs ∈ Ω′ eventually (Ω′ open), (Φ(w + rs) − Φ(w))/r → DΦ(w)s, and JΦ(w + rs) → JΦ(w). By dominated convergence the integral tends to JΦ(w) ∫_{ℝⁿ} φ(DΦ(w)s) ds (this limit is the accepted DAG lemma `lpf_wtc_cat_rescaled_integral_tendsto`), which equals ∫_{T_y} φ dHⁿ by the area formula for the injective linear (hence Lipschitz) map s ↦ DΦ(w)s, whose Jacobian is the constant JΦ(w). For the density bound, take φ₀ ∈ C_c(ℝ^Q) with 1_{B̄_R(0)} ≤ φ₀ ≤ 1_{B_{2R}(0)}; the same identity (with 2R in place of R) gives r^{−n} Hⁿ(N ∩ B̄_{rR}(y)) = Hⁿ(η(N) ∩ B̄_R(0)) ≤ ∫_{η(N)} φ₀ dHⁿ ≤ max_{|z−w|≤2R/c} JΦ(z) · Lⁿ(B_{2R/c}(0)) for all 0 < r ≤ 1. □
 (f) (Upper Density Theorem, Simon Ch. 1, 3.6 with Remark 3.7(2); SimonGMT `Chapter01.simon_theorem_3_6`.) Let W ⊆ ℝ^Q be open, S ⊆ ℝ^Q Hⁿ-null-measurable and g : ℝ^Q → [0, ∞] with ∫_{S∩K} g dHⁿ < ∞ for every compact K ⊆ W. Then for Hⁿ-a.e. y ∈ W ∖ S, ρ^{−n} ∫_{S ∩ B̄_ρ(y)} g dHⁿ → 0 as ρ ↓ 0. Proof: cover W by countably many open balls B with closure B ⊆ W; μ_B := g·Hⁿ⌞(S ∩ B) is a finite Borel (hence Borel regular) measure, so by 3.6 its upper n-density vanishes at Hⁿ-a.e. point outside S ∩ B; for y ∈ B ∖ S and small ρ, B̄_ρ(y) ⊆ B, so μ_B(B̄_ρ(y)) = ∫_{S ∩ B̄_ρ(y)} g dHⁿ. The constant ω_n and the positive factor between Simon's Hⁿ and μHE[n] change neither null sets nor the vanishing of the limit. (This is the accepted DAG lemma `lpf_wtc_ae_zero_density_off_set`.)

1. (Compact pieces with continuous weight; Remark 1.8(1).) There are compact C_k ⊆ M (k ∈ ℕ) with θ|C_k continuous, Hⁿ(C_k) < ∞ and Hⁿ(M ∖ ⋃_k C_k) = 0. (The accepted DAG lemma `lpf_wtc_lusin_compact_pieces` has exactly this statement.) Proof: let V_i (i ≥ 1) be open sets with compact closures closure V_i ⊆ V and ⋃_i V_i = V (e.g. V_i := {x ∈ V : |x| < i, dist(x, ℝ^Q ∖ V) > 1/i}). Fix i. θ is Hⁿ-integrable on M ∩ closure V_i, so there are a Borel function θ_i and a Borel set M_i′ ⊆ M ∩ V_i with Hⁿ((M ∩ V_i) ∖ M_i′) = 0 and θ = θ_i on M_i′ (M is Hⁿ-null-measurable); θ_i > 0 on M_i′ because θ > 0 on M. ν_i(B) := ∫_{B ∩ M_i′} θ_i dHⁿ is a finite Borel measure on ℝ^Q, hence closed- and compact-inner regular. For j ≥ 1, Lusin's theorem (Simon Ch. 1, 1.17; SimonGMT `Chapter01.exists_isClosed_continuousOn_of_measurable`, applicable because ν_i is finite and closed-inner regular) gives a closed C_{i,j} ⊆ M_i′ with ν_i(M_i′ ∖ C_{i,j}) < 1/j and θ_i|C_{i,j} continuous. C_{i,j} is closed and contained in the compact set closure V_i, hence compact; C_{i,j} ⊆ M, and θ|C_{i,j} = θ_i|C_{i,j} is continuous; so ν_i(M_i′ ∖ ⋃_j C_{i,j}) = 0, and since θ_i > 0 on M_i′, Hⁿ(M_i′ ∖ ⋃_j C_{i,j}) = 0, whence Hⁿ((M ∩ V_i) ∖ ⋃_j C_{i,j}) = 0. θ is continuous and positive on the compact C_{i,j}, so θ ≥ m > 0 there and Hⁿ(C_{i,j}) ≤ m⁻¹ ∫_{C_{i,j}} θ dHⁿ < ∞ (trivial if C_{i,j} = ∅). Since M = ⋃_i (M ∩ V_i), enumerating all C_{i,j} as C_k gives the claim.

2. (Unweighted tangent of a piece on the chart; proof of 1.6 “⟹”.) Fix C := C_k. Apply (f):
 (i) with W := ℝ^Q, S := C ∖ N, g := 1 (Hⁿ(S) ≤ Hⁿ(C) < ∞): for Hⁿ-a.e. y ∈ C ∩ N, ρ^{−n} Hⁿ((C ∖ N) ∩ B̄_ρ(y)) → 0;
 (ii) with W := ℝ^Q, S := N ∖ C, g := 1 (locally finite by 0(c)): for Hⁿ-a.e. y ∈ C ∩ N, ρ^{−n} Hⁿ((N ∖ C) ∩ B̄_ρ(y)) → 0.
 Let y ∈ C ∩ N satisfy (i) and (ii) and let φ ∈ C_c(ℝ^Q), spt φ ⊆ B_R(0), η := η_{y,r}. As η is a bijection, η(C) = η(C ∩ N) ⊔ η(C ∖ N) and η(N) = η(C ∩ N) ⊔ η(N ∖ C), all these sets are Hⁿ-measurable with locally finite measure (by (d), Hⁿ(C) < ∞ and 0(c)), and φ is bounded with compact support, so
 ∫_{η(C)} φ dHⁿ = ∫_{η(N)} φ dHⁿ − ∫_{η(N∖C)} φ dHⁿ + ∫_{η(C∖N)} φ dHⁿ.
 By (d), |∫_{η(N∖C)} φ| ≤ sup|φ| · r^{−n} Hⁿ((N ∖ C) ∩ B̄_{rR}(y)) = sup|φ| · Rⁿ (rR)^{−n} Hⁿ((N ∖ C) ∩ B̄_{rR}(y)) → 0 by (ii), and likewise |∫_{η(C∖N)} φ| → 0 by (i), while ∫_{η(N)} φ → ∫_{T_y} φ by 0(e). Hence C has approximate tangent space T_y at y (dim T_y = n by 0(a)). Moreover r^{−n} Hⁿ(C ∩ B̄_{rR}(y)) ≤ r^{−n} Hⁿ(N ∩ B̄_{rR}(y)) + r^{−n} Hⁿ((C ∖ N) ∩ B̄_{rR}(y)) is bounded for 0 < r ≤ 1 small (0(e) and (i)). (The accepted DAG lemma `lpf_wtc_density_bound_of_tangent` derives such a bound from the tangent property alone.)

3. (Remaining mass of M.) Apply (f) with W := V, S := M ∖ C, g := θ (θ ≥ 0 on M and ∫_{(M∖C)∩K} θ ≤ ∫_{M∩K} θ < ∞ for compact K ⊆ V): for Hⁿ-a.e. y ∈ C (C ⊆ M ⊆ V and y ∉ M ∖ C), ρ^{−n} ∫_{(M∖C) ∩ B̄_ρ(y)} θ dHⁿ → 0.

4. (Weighted blow-up; Remark 1.8(1).) Let y ∈ C ∩ N satisfy the conclusions of steps 2 and 3, let φ ∈ C_c(ℝ^Q) with spt φ ⊆ B_R(0), and choose r₀ ∈ (0, 1] with B̄_{r₀R}(y) ⊆ V (V open). For 0 < r < r₀, by (d),
 ∫_{η(M)} φ(z) θ(y + rz) dHⁿ(z) = r^{−n} ∫_M φ(η(x)) θ(x) dHⁿ(x),
 where x ↦ φ(η(x))θ(x) vanishes off M ∩ B_{rR}(y) and is Hⁿ-integrable (|φ(η(x))θ(x)| ≤ sup|φ| θ(x) and θ is integrable on M ∩ B̄_{r₀R}(y)); also x ↦ φ(η(x)) and x ↦ φ(η(x))(θ(x) − θ(y)) are integrable on C (Hⁿ(C) < ∞, θ integrable on the compact C ⊆ M ∩ V). Splitting M = C ⊔ (M ∖ C) and writing θ = θ(y) + (θ − θ(y)) on C (accepted DAG lemma `lpf_wtc_wtt_blowup_integral_split`):
 r^{−n} ∫_M φ(η(x)) θ(x) dHⁿ(x) = I₁ + I₂ + I₃, where
 I₁ := θ(y) r^{−n} ∫_C φ(η(x)) dHⁿ(x) = θ(y) ∫_{η(C)} φ dHⁿ → θ(y) ∫_{T_y} φ dHⁿ (step 2 and (d));
 I₂ := r^{−n} ∫_{C ∩ B̄_{rR}(y)} φ(η(x))(θ(x) − θ(y)) dHⁿ(x), so |I₂| ≤ sup|φ| · sup_{C ∩ B̄_{rR}(y)} |θ − θ(y)| · r^{−n} Hⁿ(C ∩ B̄_{rR}(y)) → 0, because θ|C is continuous at y and the density ratio is bounded (step 2) — this is the Lebesgue-point estimate of the parent's sketch;
 I₃ := r^{−n} ∫_{(M∖C) ∩ B̄_{rR}(y)} φ(η(x)) θ(x) dHⁿ(x), so |I₃| ≤ sup|φ| · Rⁿ (rR)^{−n} ∫_{(M∖C) ∩ B̄_{rR}(y)} θ dHⁿ → 0 (step 3; accepted DAG lemma `lpf_wtc_wtt_remainder_vanishes`).
 Hence ∫_{η_{y,r}(M)} φ(z) θ(y + rz) dHⁿ(z) → θ(y) ∫_{T_y} φ dHⁿ for every φ ∈ C_c(ℝ^Q); with dim T_y = n (0(a)) this is HasWeightedApproximateTangentSpaceAt n M θ y T_y.

5. (Conclusion.) Let Z be the set of y ∈ M ∩ N at which the claim fails, i.e. HasWeightedApproximateTangentSpaceAt n M θ y (range DΦ(w_y)) does not hold. Then Z ⊆ (M ∖ ⋃_k C_k) ∪ ⋃_k Z_k, where Z_k ⊆ C_k ∩ N is the union of the Hⁿ-null exceptional sets of steps 2(i), 2(ii) and 3 for C = C_k: indeed every y ∈ (C_k ∩ N) ∖ Z_k satisfies the claim by step 4, and w_y is the only w ∈ Ω with Φ(w) = y (0(a)). By step 1 and countable subadditivity Hⁿ(Z) = 0. As M ∩ N is Hⁿ-null-measurable (0(b)), this is exactly ∀ᵐ y ∂(Hⁿ⌞(M ∩ Φ(Ω))), ∀ w ∈ Ω, Φ(w) = y → HasWeightedApproximateTangentSpaceAt n M θ y (LinearMap.range (fderiv ℝ Φ w)). ∎
 (For n = 0 all steps hold verbatim: ℝ⁰ is a point, H⁰ = μHE[0] is counting measure, λ⁰ = 1, N is empty or a single point and T_y = {0}.)

Implementation remarks (not part of the mathematical argument). (i) The frozen type of this lemma is byte-identical to that of `lpf_weighted_tangent_on_c1_chart` (lipschitz-pushforward branch; speculative-ready, not comparator-accepted at the time of this split, hence the fresh name). If that declaration is comparator-accepted when this node is decomposed, it can be reused as a reuse child with its exact name and identical type. (ii) Otherwise, in this node's own decomposition the following comparator-accepted declarations can be included as reuse children (exact names, identical frozen types): `lpf_wtc_cat_fderiv_lower_bound` (0(a)), `lpf_wtc_chart_image_measurable_locally_finite` (0(b), 0(c)), `lpf_wtc_blowup_setIntegral_image` (0(d)), `lpf_wtc_caf_lipschitz_localization` and `lpf_wtc_caf_signed_of_lintegral` (the area formula on Ω′ in 0(e)), `lpf_wtc_cat_gram_jacobian_continuous` and `lpf_wtc_cat_rescaled_integral_tendsto` (the limit in 0(e)), `lpf_wtc_ae_zero_density_off_set` (0(f)), `lpf_wtc_lusin_compact_pieces` (step 1), `lpf_wtc_tangent_transfer` and `lpf_wtc_density_bound_of_tangent` (step 2), `lpf_wtc_wtt_blowup_integral_split`, `lpf_wtc_wtt_continuity_error_vanishes` and `lpf_wtc_wtt_remainder_vanishes` (step 4). (iii) Imports: the SimonGMT modules `Chapter02.AreaDomain`, `Chapter02.AreaLipschitz`, `Chapter01.DensityComparison` and `Chapter01.Lusin` are prebuilt in the shared package and may be added to Submission.lean, as accepted nodes do.

## Key steps

1. Chart facts: |DΦ(w)s| ≥ c|s|, Φ injective on Ω with c⁻¹-Lipschitz inverse, N = Φ(Ω) Borel and locally Hⁿ-finite.
2. Blow-up change of variables; C¹ blow-up via the injective area formula and dominated convergence: N has approximate tangent space DΦ(w_y)(ℝⁿ) at y with bounded density ratios.
3. Remark 1.8(1): Lusin compact pieces C_k ⊆ M with θ|C_k continuous and Hⁿ(C_k) < ∞ cover M up to an Hⁿ-null set.
4. Upper Density Theorem: Hⁿ⌞(C∖N), Hⁿ⌞(N∖C) and θHⁿ⌞(M∖C) have zero n-density at Hⁿ-a.e. point of C ∩ N, so C has approximate tangent T_y there (proof of 1.6 ⟹).
5. Weighted blow-up = θ(y)·(blow-up of C) + continuity error on C + zero-density remainder → θ(y)∫_{T_y}φ; the exceptional set is a countable union of null sets.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (both identical; workspace HEAD d8d46c95)`
- `python3 importlib verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') -> scope prefix: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique|def blowUpMap' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n '^theorem|^def' simongmt Chapter02/{Lipschitz,AreaLipschitz,AreaCritical,AreaDomain,WhitneyExtension,WhitneyJet}.lean Chapter01/{Lusin,DensityComparison}.lean Chapter03/{SubmanifoldCover,Differential,DisjointCover}.lean`
- `grep -n '^theorem' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,200p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_smul0)`
- `grep -rn 'theorem Measurable.find|theorem measurable_find|theorem ContinuousOn.measurableEmbedding|theorem MeasurableSet.image_of_continuousOn_injOn|theorem measurable_fderiv|theorem measurableSet_of_differentiableAt|theorem DifferentiableWithinAt.differentiableAt|theorem ae_restrict_iff|theorem tendstoUniformlyOn_of_ae_tendsto|IsSigmaCompact.image|theorem normDet_sq_eq_det_gram|theorem normDet_nonneg|theorem hausdorffMeasure_image_le' mathlib/Mathlib`
- `ls lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 and Chapter01 (WhitneyExtension.olean absent; AreaCritical, AreaLipschitz, AreaDomain, WhitneyJet, Lusin, DensityComparison present)`
- `python3 scan of dag.json (360 nodes): uniqueness of slicing_im_tg_* names; byte-identity of child types with lpf_countably_rectifiable_c1_cover / lpf_weighted_tangent_on_c1_chart (speculative-ready); live statuses and statements of lpf_c1r_*, lpf_c1_local_antilipschitz, lpf_lipschitz_c1_immersion_pieces, lpf_wtc_*, lpf_tde_chart_directional_deriv, lpf_ccr_hasDerivAt_line_of_comp, rectifiability_weighted_tangent_ae, br_weightedTangent_congr, iwl_weighted_tangent_locality`
- `read nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json, nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (twin proofs; reuse-child mechanism)`
- `git show <workspace_result_commit>:GMT/Ch06/Submission.lean for 138 accepted nodes (extra SimonGMT imports such as Chapter02.AreaDomain, Chapter01.DensityComparison, Chapter02.AreaBranches are allowed)`
- `lake env lean /tmp/tg_split/Stmts.lean (four child types in exact comparator scope; 0 errors)`
- `lake env lean /tmp/tg_split/Assembly.lean (frozen parent type proved from chart_cover, chart_tangent, chart_gradient stubs; #print axioms: propext, sorryAx [stubs only], Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/CProof.lean (complete proof of the line_deriv frozen type; axioms propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/tg_split/Avail.lean (#check of cited Mathlib and SimonGMT lemmas in the Submission import closure)`
- `python3 verifier/lean_contract.py validate_lean_statement on the four child types (all OK)`
- `rg 'slicing_im_tg' local-references/197bdd4b88278494/project and lake-packages-25730c7c/simongmt (no match)`
- `sed book/chapter-03.txt (1.1-1.9, 2.1-2.2), chapter-02.txt (1.4-1.8, 4.1-4.11), chapter-01.txt (3.6-3.7)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Egorov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyJet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-tangential-gradient-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/tmp/tg_split/Stmts.lean`
- `/tmp/tg_split/Assembly.lean`
- `/tmp/tg_split/CProof.lean`
- `/tmp/tg_split/Avail.lean`

Snapshot and imports:
- The snapshot (project d8d46c95, the workspace HEAD; Mathlib 25730c7c) contains the frozen Ch06 contract, byte-identical to the workspace Contract.lean and Submission.lean. Child types may therefore use only contract, SimonGMT and Mathlib names. The comparator scope is namespace GMT.Ch06 with the contract's opens.
- SimonGMT supplies the following:
  - CountablyRectifiable as countably many Lipschitz images plus an Hⁿ-null set, and HasWeightedApproximateTangentSpaceAt with uniqueness at θ(x) ≠ 0.
  - Lipschitz image bounds for μHE[n].
  - Area-formula critical-image and injective results (AreaCritical, AreaLipschitz, AreaDomain), Lusin (Chapter01.Lusin) and the upper density theorem 3.6 (Chapter01.DensityComparison). These modules are not imported by the contract but are prebuilt and may be added to the imports, as accepted nodes do.
  - Its Chapter02.WhitneyExtension module is not prebuilt, so it cannot be imported.
- SimonGMT lacks the chart-cover direction of Simon Lemma 1.2 (SubmanifoldCover proves only the easy direction), a tangential gradient for Lipschitz functions, and tangent identification on C¹ charts.
- Mathlib supplies Rademacher on sets (LipschitzOnWith.ae_differentiableWithinAt_of_mem), μHE[n] = volume on ℝⁿ, measurable_fderiv, measurableSet_of_differentiableAt, Lusin–Souslin images and measurable embeddings, Measurable.find, Egorov, and normDet_sq_eq_det_gram.

DAG and reuse:
- The chart-cover and chart-tangent lemmas exist in the DAG only as the speculative-ready lpf twins. Their types are byte-identical to the children chart_cover and chart_tangent, but they are not yet comparator-accepted, so fresh names are used.
- Many of the twins' leaves are comparator-accepted and are listed in the child proofs for reuse in those children's own decompositions.
- No accepted declaration has a type identical to any child. slicing_im_tg_* matches nowhere: not in the snapshot project, not in SimonGMT, not among the 360 DAG nodes.

Kernel checks:
- All four child types elaborate in the exact scope and pass the verifier's statement validator.
- The frozen parent type is proved from chart_cover, chart_tangent and chart_gradient; sorryAx comes only from the stubs.
- line_deriv is fully proved with standard axioms.

These checks do not certify the analytic proofs of chart_cover, chart_tangent and chart_gradient.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
