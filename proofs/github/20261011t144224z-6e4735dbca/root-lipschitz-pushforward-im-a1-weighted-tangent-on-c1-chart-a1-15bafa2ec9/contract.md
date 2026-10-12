<!-- theorem-id: gmt-ch06/root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1 -->

## Theorem `Submission.lpf_weighted_tangent_on_c1_chart`

Let V ⊆ ℝ^Q be open, M ⊆ V Hⁿ-null-measurable, θ > 0 on M with θ Hⁿ-integrable on M ∩ K for every compact K ⊆ V, and let Φ : ℝⁿ → ℝ^Q be C¹ and antilipschitz on an open Ω ⊆ ℝⁿ. Then for Hⁿ-a.e. y ∈ M ∩ Φ(Ω) and the (unique) w ∈ Ω with Φ(w) = y, DΦ(w)(ℝⁿ) is the weighted approximate tangent space of M with respect to θ at y (HasWeightedApproximateTangentSpaceAt n M θ y (range DΦ(w))).

Node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/319

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1264, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1266, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1268, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1271, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1273, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1274, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1275, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1276, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1277

## Lean problem

Declaration: `Submission.lpf_weighted_tangent_on_c1_chart`

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

- Parent DAG node: `root.lipschitz_pushforward_im-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions used below. ℝ^P = EuclideanSpace ℝ (Fin P) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n] (Mathlib's Euclidean-normalized n-dimensional Hausdorff measure; on ℝⁿ it equals Lebesgue measure Lⁿ = volume, it is invariant under isometries and translations and scales by λⁿ under x ↦ λx). An n-covector α is a continuous alternating n-linear map (ℝ^P)ⁿ → ℝ with the operator norm ‖α‖ (least C with |α(u₁,…,u_n)| ≤ C Π|u_i|); an n-vector is a continuous linear functional on n-covectors with the operator norm; simpleNVector v is the n-vector α ↦ α(v₁,…,v_n), so |simpleNVector v (α)| ≤ ‖α‖ Π|v_i|; for a linear map A, A_# w := nVectorPushforward n A w = w ∘ A^#, where A^#α = α(A·,…,A·), it is linear in w and A_#(simpleNVector v) = simpleNVector(A v) (`nVectorPushforward_simple`). A map Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This lemma combines item (P4)(a),(b) of the parent proof with Simon Ch. 3, Definition 1.4/1.7, the proof of Theorem 1.6 “⇒” and Remark 1.8(1) (printed arguments, specialized to one C¹ chart), as used in Steps 1, 5.3 and 7 of the parent proof. Setting: V ⊆ ℝ^Q open, M ⊆ V Hⁿ-null-measurable, θ > 0 on M, θ Hⁿ-integrable on M ∩ K for every compact K ⊆ V; Φ : ℝⁿ → ℝ^Q of class C¹, Ω ⊆ ℝⁿ open, Φ c-antilipschitz on Ω (c > 0). Put N := Φ(Ω). Recall η_{y,λ}(z) := λ⁻¹(z − y) (`blowUpMap y λ`) and that HasWeightedApproximateTangentSpaceAt n M θ y P means: dim P = n and for every φ ∈ C_c(ℝ^Q), ∫_{η_{y,λ}(M)} φ(z) θ(y + λz) dHⁿ(z) → θ(y) ∫_P φ dHⁿ as λ ↓ 0. If n > Q then Hⁿ ≡ 0 on ℝ^Q (Hausdorff dimension of ℝ^Q is Q; `hausdorffMeasure_of_dimH_lt`) and there is nothing to prove; assume n ≤ Q.

0. (Preliminaries on the chart.)
 (a) For w ∈ Ω and s ∈ ℝⁿ: w + ts ∈ Ω for small t, and |Φ(w+ts) − Φ(w)| ≥ c|t||s|; dividing by |t| and letting t → 0 gives |DΦ(w)s| ≥ c|s|. So DΦ(w) is injective and T_w := DΦ(w)(ℝⁿ) = LinearMap.range (fderiv ℝ Φ w) has dimension n. Φ is injective on Ω; for y ∈ N let w_y ∈ Ω be the unique point with Φ(w_y) = y, and T_y := T_{w_y}. (The Lean conclusion “∀ w ∈ Ω, Φ w = y → …” concerns exactly w = w_y.)
 (b) Ψ := (Φ|Ω)⁻¹ : N → Ω is (1/c)-Lipschitz. N is σ-compact (Ω is a countable union of compact sets and Φ is continuous), hence Borel; M ∩ N is Hⁿ-null-measurable.
 (c) N is locally Hⁿ-finite: if K ⊆ ℝ^Q is compact, Ψ(N ∩ K) has diameter ≤ diam(K)/c, so lies in a closed ball B̄ ⊆ ℝⁿ; Φ is Lipschitz on B̄ (C¹ on a compact convex set), say with constant Λ, and Hⁿ(N ∩ K) ≤ Λⁿ Lⁿ(B̄) < ∞.
 (d) (Change of variables under blow-ups.) η_{y,λ} is a similarity of ratio λ⁻¹, so for every set S and every g ≥ 0 or Hⁿ⌞S-integrable g: ∫_{η_{y,λ}(S)} g dHⁿ = λ^{−n} ∫_S g∘η_{y,λ} dHⁿ (translation invariance and μHE[n](λS) = λⁿ μHE[n](S), Mathlib `euclideanHausdorffMeasure_smul₀`).
 (e) (C¹ blow-up of N; Simon: “since x ∈ N_j and N_j is a C¹ submanifold, lim ∫_{η(N_j)} f = ∫_{T N_j} f”.) For every y ∈ N and φ ∈ C_c(ℝ^Q): lim_{λ↓0} ∫_{η_{y,λ}(N)} φ dHⁿ = ∫_{T_y} φ dHⁿ. Proof: let spt φ ⊆ B_R(0), w := w_y. By (d) and the injective area formula for Φ on Ω (Φ injective, Lipschitz on bounded subsets of Ω; Simon Ch. 2 (3.2)/(3.5), SimonGMT `injective_area_formula_lipschitzOn` and its weighted fibre-sum form) the integral equals λ^{−n} ∫_Ω φ((Φ(v) − y)/λ) JΦ(v) dv, JΦ(v) := √det(DΦ(v)*DΦ(v)), and the substitution v = w + λs turns it into I_λ := ∫ 1_{(Ω−w)/λ}(s) φ((Φ(w+λs) − Φ(w))/λ) JΦ(w+λs) ds. If the integrand is nonzero then w, w + λs ∈ Ω and |Φ(w+λs) − Φ(w)| < λR, so c|λs| < λR, i.e. |s| < R/c. For λ ≤ 1 the integrand is bounded by sup|φ| · max_{|z−w| ≤ R/c} JΦ(z) and vanishes for |s| ≥ R/c; for fixed s, as λ ↓ 0: w + λs ∈ Ω eventually (Ω open), (Φ(w+λs) − Φ(w))/λ → DΦ(w)s and JΦ(w+λs) → JΦ(w). By dominated convergence I_λ → ∫_{ℝⁿ} φ(DΦ(w)s) JΦ(w) ds = ∫_{T_y} φ dHⁿ, the last equality being the linear area formula for the injective linear map DΦ(w) (Simon Ch. 2 (3.1); Mathlib `LinearMap.hausdorffMeasure_image`/normDet). Note that for nonnegative φ ≥ 1_{B_R(0)} this also shows sup_{0<λ≤1} λ^{−n} Hⁿ(N ∩ B_{λR}(y)) < ∞.
 (f) (Upper Density Theorem, Simon Ch. 1, 3.6; SimonGMT `Chapter01.simon_theorem_3_6`.) If μ is a Borel regular measure on ℝ^Q and A is μ-measurable with μ(A) < ∞, then for Hⁿ-a.e. y ∈ ℝ^Q ∖ A, lim_{ρ↓0} ρ^{−n} μ(A ∩ B_ρ(y)) = 0. (Finite Borel measures on ℝ^Q, and Hⁿ restricted to sets of finite measure, are Borel regular.)

1. (Compact pieces with continuous weight — Remark 1.8(1).) Let V_1 ⊆ V_2 ⊆ ⋯ be open sets with compact closures closure V_i ⊆ V_{i+1} ⊆ V and ⋃_i V_i = V. Fix i. ν_i(B) := ∫_{B ∩ M ∩ V_i} θ dHⁿ defines a finite Borel measure (∫_{M ∩ closure V_i} θ < ∞), and θ is ν_i-measurable (θ is a.e. strongly measurable on M ∩ closure V_i by `IntegrableOn`). Choose a Borel M_i′ ⊆ M ∩ V_i with Hⁿ((M ∩ V_i) ∖ M_i′) = 0. For each j ≥ 1, Lusin's theorem for the finite Borel measure ν_i (Simon Ch. 1, 1.17; SimonGMT `Chapter01.Lusin`) gives a closed F with ν_i(ℝ^Q ∖ F) < 1/(2j) and θ|F continuous, and inner regularity gives a compact C_{i,j} ⊆ M_i′ ∩ F with ν_i((M_i′ ∩ F) ∖ C_{i,j}) < 1/(2j). Thus C_{i,j} ⊆ M ∩ V_i is compact, θ|C_{i,j} is continuous and ν_i((M ∩ V_i) ∖ C_{i,j}) < 1/j. Hence ν_i((M ∩ V_i) ∖ ⋃_j C_{i,j}) = 0, and since θ > 0 on M, also Hⁿ((M ∩ V_i) ∖ ⋃_j C_{i,j}) = 0. As M = ⋃_i (M ∩ V_i), it suffices to prove: for each fixed C := C_{i,j}, the conclusion holds at Hⁿ-a.e. y ∈ C ∩ N. Note that θ ≥ m_C := min_C θ > 0 on C (continuous positive function on a compact set), so Hⁿ(C) ≤ m_C^{−1} ∫_C θ dHⁿ < ∞.

2. (Unweighted tangent plane of C on the chart — proof of 1.6 “⇒”.) Exceptional sets, by (f):
 (i) μ := Hⁿ⌞C (finite), A := C ∖ N: for Hⁿ-a.e. y ∈ C ∩ N, ρ^{−n} Hⁿ((C ∖ N) ∩ B_ρ(y)) → 0.
 (ii) For each of the countably many rational balls B ⊆ ℝ^Q, μ := Hⁿ⌞(N ∩ B) (finite by (c)), A := (N ∩ B) ∖ C: for Hⁿ-a.e. y ∈ C ∩ B, ρ^{−n} Hⁿ((N ∖ C) ∩ B ∩ B_ρ(y)) → 0; since B_ρ(y) ⊆ B for small ρ when y ∈ B, and the rational balls cover ℝ^Q: for Hⁿ-a.e. y ∈ C ∩ N, ρ^{−n} Hⁿ((N ∖ C) ∩ B_ρ(y)) → 0.
 Let y ∈ C ∩ N satisfy (i) and (ii). For φ ∈ C_c(ℝ^Q) with spt φ ⊆ B_R(0), using (d),
 ∫_{η_{y,λ}(C)} φ = ∫_{η_{y,λ}(N)} φ − ∫_{η_{y,λ}(N ∖ C)} φ + ∫_{η_{y,λ}(C ∖ N)} φ,
 and |∫_{η_{y,λ}(N∖C)} φ| ≤ sup|φ| λ^{−n} Hⁿ((N ∖ C) ∩ B_{λR}(y)) → 0, |∫_{η_{y,λ}(C∖N)} φ| ≤ sup|φ| λ^{−n} Hⁿ((C ∖ N) ∩ B_{λR}(y)) → 0, while the first term tends to ∫_{T_y} φ by (e). Hence lim_{λ↓0} ∫_{η_{y,λ}(C)} φ dHⁿ = ∫_{T_y} φ dHⁿ for every φ (the exceptional set does not depend on φ). Moreover λ^{−n} Hⁿ(C ∩ B_{λR}(y)) ≤ λ^{−n} Hⁿ(N ∩ B_{λR}(y)) + λ^{−n} Hⁿ((C ∖ N) ∩ B_{λR}(y)) stays bounded as λ ↓ 0 (by (e) and (i)).

3. (Exceptional set for the rest of M.) By (f) with μ := ν_i and A := (M ∩ V_i) ∖ C (ν_i(A) < ∞): for Hⁿ-a.e. y ∈ C, ρ^{−n} ∫_{((M ∩ V_i) ∖ C) ∩ B_ρ(y)} θ dHⁿ → 0.

4. (Weighted blow-up — Remark 1.8(1).) Let y ∈ C ∩ N satisfy the conclusions of steps 2 and 3, let φ ∈ C_c(ℝ^Q) with spt φ ⊆ B_R(0), and let λ > 0 be so small that closure B_{λR}(y) ⊆ V_i (possible: y ∈ C ⊆ V_i open). Then z ↦ φ(z)θ(y + λz) is Hⁿ-integrable on η_{y,λ}(M): it vanishes unless y + λz ∈ M ∩ B_{λR}(y), and by (d) its absolute integral is ≤ sup|φ| λ^{−n} ∫_{M ∩ closure B_{λR}(y)} θ < ∞. By (d),
 ∫_{η_{y,λ}(M)} φ(z) θ(y+λz) dHⁿ(z) = λ^{−n} ∫_M φ((x−y)/λ) θ(x) dHⁿ(x) = I₁ + I₂ + I₃, where
 I₁ := θ(y) λ^{−n} ∫_C φ((x−y)/λ) dHⁿ(x) = θ(y) ∫_{η_{y,λ}(C)} φ dHⁿ → θ(y) ∫_{T_y} φ dHⁿ (step 2);
 I₂ := λ^{−n} ∫_{C ∩ B_{λR}(y)} φ((x−y)/λ)(θ(x) − θ(y)) dHⁿ(x), |I₂| ≤ sup|φ| · sup_{C ∩ B_{λR}(y)} |θ − θ(y)| · λ^{−n} Hⁿ(C ∩ B_{λR}(y)) → 0, because θ|C is continuous at y and the density ratio is bounded (step 2);
 I₃ := λ^{−n} ∫_{(M ∖ C) ∩ B_{λR}(y)} φ((x−y)/λ) θ(x) dHⁿ(x), and since (M ∖ C) ∩ B_{λR}(y) = ((M ∩ V_i) ∖ C) ∩ B_{λR}(y), |I₃| ≤ sup|φ| λ^{−n} ∫_{((M∩V_i)∖C) ∩ B_{λR}(y)} θ dHⁿ → 0 (step 3).
 Hence the weighted blow-up integrals converge to θ(y) ∫_{T_y} φ dHⁿ for every φ ∈ C_c(ℝ^Q); together with dim T_y = n (0(a)) this is HasWeightedApproximateTangentSpaceAt n M θ y T_y with T_y = LinearMap.range (fderiv ℝ Φ w_y).

5. (Conclusion.) The set of y ∈ M ∩ N where the conclusion fails is contained in ⋃_i ((M ∩ V_i) ∖ ⋃_j C_{i,j}) ∪ ⋃_{i,j} (the exceptional subsets of C_{i,j} ∩ N from steps 2–3), a countable union of Hⁿ-null sets. Since M ∩ N is Hⁿ-null-measurable (0(b)), this is exactly the statement “∀ᵐ y ∂ Hⁿ⌞(M ∩ Φ(Ω)), ∀ w ∈ Ω, Φ w = y → HasWeightedApproximateTangentSpaceAt n M θ y (range DΦ(w))”. ∎
 (For n = 0 all steps hold verbatim: ℝ⁰ is a point, H⁰ = μHE[0] = μH[0] is counting measure, λ⁰ = 1, N is a single point or empty and T_y = {0}.)

## Key steps

1. Chart facts: DΦ(w) injective with |DΦ(w)s| ≥ c|s|, Φ(Ω) σ-compact and locally Hⁿ-finite, inverse (1/c)-Lipschitz.
2. C¹ blow-up: via the injective area formula and dominated convergence, blow-ups of Φ(Ω) at y = Φ(w) converge to Hⁿ⌞DΦ(w)(ℝⁿ).
3. Remark 1.8(1): by Lusin, M ∩ V_i is covered up to null sets by compact C with θ|C continuous and Hⁿ(C) < ∞.
4. Proof of 1.6 ⇒: by the Upper Density Theorem, Hⁿ⌞(C∖N) and Hⁿ⌞(N∖C) have zero density at a.e. point of C ∩ N, so blow-ups of C converge to T_y with bounded density ratios.
5. Weighted blow-up of (M,θ) = θ(y)·blow-up of C + continuity error on C + θHⁿ⌞(M∖C) term of zero density, giving the weighted tangent space T_y.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspace GMT/Ch06/Contract.lean against snapshot project/GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean (all identical)`
- `python3 listing of lean_name fields in dag.json (only GMT.Ch06.main_theorem and its 12 children reserved; no lpf_* names)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py to generate the exact child scope; lean_contract.validate_lean_statement on all 11 child statements`
- `rg -n 'μHE' mathlib/Mathlib (Geometry/Euclidean/Volume/Measure.lean: euclideanHausdorffMeasure_def, euclideanHausdorffMeasure_zero, euclideanHausdorffMeasure_smul₀, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib`
- `rg -n 'theorem measurable_fderiv' mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_of_dimH_lt' mathlib/Mathlib`
- `rg -n 'theorem abs_volumeForm_apply_le|normDet_sq_eq_det_gram|theorem map_linearDependent|theorem LipschitzOnWith.extend_pi' mathlib/Mathlib`
- `rg -n -i 'hadamard.s inequality|det_le_prod|abs_det_le' mathlib/Mathlib (no packaged Hadamard inequality besides Orientation.abs_volumeForm_apply_le)`
- `grep -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter03/{Rectifiable,SubmanifoldCover,Differential}.lean`
- `grep -n '^theorem' simongmt/Poincare/SimonGMT/Chapter02/{Lipschitz,AreaDomain,AreaLipschitz,AreaNoninjective,AreaCompletion,AreaMultiplicity,LipschitzMeasurability,WhitneyExtension,WhitneyCover}.lean`
- `grep -n 'simon_theorem_3_6' simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean; grep -n '^theorem' Chapter01/Lusin.lean Chapter01/GeneralDifferentiation.lean`
- `ls simongmt/.lake/build/lib/lean/Poincare/SimonGMT/Chapter02 | grep -i whitney (WhitneyCover/Jet/Partition built; WhitneyExtension.olean absent)`
- `lake env lean Scratch/Probe*.lean (#print GeometricCurrentOn.support/zeroRegion/VanishesOn, TestFormOn, IsTestForm, TestFormOnConverges, simpleNVector, covectorPullback; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm; Norm (Covector (Eucl 3) 2) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm; MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace; Chapter02.IsSimonSubmanifold not in child scope; LinearMap.range needs (fderiv ℝ Φ w).toLinearMap)`
- `lake env lean Scratch/Stmts.lean (11 child statements in comparator child scope; only sorry warnings)`
- `lake env lean Scratch/Assembly.lean (parent from lpf_tangential_differential_exists, lpf_pushforward_is_current, lpf_pushforward_integrality; #print axioms)`
- `grep -n 'Lemma|Theorem|Remark' book/chapter-03.txt; sed -n 1,445p book/chapter-03.txt; sed -n 160,270p and 900,1000p book/chapter-02.txt; sed -n 740,900p book/chapter-06.txt`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Differential.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaDomain.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaMultiplicity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WhitneyExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/lpim_scratch/Scratch/scope_prefix.txt`
- `/tmp/lpim_scratch/Scratch/Stmts.lean`
- `/tmp/lpim_scratch/Scratch/Assembly.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, byte-identical to the workspace Contract and Submission. Only GMT.Ch06.main_theorem and its 12 children are reserved in the DAG, so the bare lpf_* names are free.

The child scope (import GMT.Ch06.Submission plus the replayed namespace and opens) gives the contract notions and SimonGMT Ch01 Densities, Ch03 Rectifiable (HasWeightedApproximateTangentSpaceAt, blowUpMap, CountablyRectifiable, .unique) and Ch06 (NVector, simpleNVector, nVectorPushforward, nVectorPushforward_simple, TestFormOn, GeometricCurrentOn, support). Chapter02.IsSimonSubmanifold is not in scope, so C¹ pieces are stated as C¹ maps that are antilipschitz on open sets.

Instance checks:
- NVector carries the operator norm over the ContinuousAlternatingMap norm, so ‖simpleNVector v‖² is the Gram determinant and ‖L_#ξ‖ is the area Jacobian.
- volume on Eucl n is measureSpaceOfInnerProductSpace, and μHE[n] = volume there.
- μHE[0] = μH[0].

Mathlib provides the fundamental lemma (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero), measurable_fderiv, hausdorffMeasure_of_dimH_lt, Hadamard via Orientation.abs_volumeForm_apply_le, normDet_sq_eq_det_gram, AlternatingMap.map_linearDependent and LipschitzOnWith.extend_pi.

SimonGMT provides Rademacher, Lipschitz image bounds and image measurability (Ch02/Lipschitz). It provides the full Euclidean area formula with fibre sums and its a.e.-measurability (Ch02/AreaDomain: weighted_area_formula_lipschitzOn_fiberSum, aemeasurable_weightedAreaFiberSum_lipschitzOn, ae_fderivWithin_eq_of_lipschitz_extension) and null critical images (Ch02/AreaLipschitz: area_image_compl_regularSet_eq_zero). It also provides the upper density theorem (Ch01 simon_theorem_3_6), Lusin (Ch01/Lusin), and the C¹-cover-to-rectifiable direction (Ch03/SubmanifoldCover).

SimonGMT does not provide:
- Lemma 1.2 ⇒, Theorem 1.6/1.9 existence, or the rectifiable area formula; these are the new children.
- A packaged C¹ approximation theorem: Whitney machinery exists in Ch02/WhitneyExtension.lean, but that file is not built.

All 11 child statements pass the lexical validator and elaborate in the comparator child scope. The parent assembly from 3 children is kernel-checked with the standard axioms only. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
