<!-- theorem-id: gmt-ch06/root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1 -->

## Theorem `Submission.rectifiability_bf_infinite_fibre_null`

Let N, m ∈ ℕ and k := m + 1. Let ℝ^N = Eucl N carry Hᵏ := μHE[k], the normalized Euclidean k-dimensional Hausdorff measure, and let ℝᵏ = Eucl k carry Lebesgue measure Lᵏ (volume). Let E ⊆ ℝ^N be a Borel set with Hᵏ(E) < ∞. Let f : ℝ^N → ℝᵏ be Lipschitz with constant K ∈ [0, ∞), i.e. |f(x) − f(x′)| ≤ K|x − x′| for all x, x′. Then the set {y ∈ ℝᵏ : E ∩ f⁻¹({y}) is infinite} has Lebesgue measure zero.

Node: `root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1033

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.rectifiability_bf_infinite_fibre_null`

```lean
∀ (N m : ℕ) (E : Set (Eucl N)) (f : Eucl N → Eucl (m + 1)) (K : ℝ≥0), MeasurableSet E → (μHE[m + 1] : Measure (Eucl N)) E < ∞ → LipschitzWith K f → (volume : Measure (Eucl (m + 1))) {y : Eucl (m + 1) | (E ∩ f ⁻¹' {y}).Infinite} = 0
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

- Parent DAG node: `root.rectifiability-a1.bf_projection_null_ae-a1`
- Child DAG node: `root.rectifiability-a1.bf_projection_null_ae-a1.infinite_fibre_null-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. This is the fibre-counting half of Eilenberg's inequality (Simon, Ch. 2, 1.8(ii); Federer 2.10.25; Lemma 2.3 of Hovila–Järvenpää–Järvenpää–Ledrappier, Geom. Dedicata 161 (2012)), specialised to the finiteness of almost every fibre. It is extracted from step 3(c) of the parent proof, with two changes. Fatou's lemma replaces monotone convergence, so neither the nesting of dyadic cubes nor the identity sup_i N_i = #fibre is needed. Measurable hulls replace σ-compactness of the pieces, so a Borel E suffices.

Notation. k := m + 1 ≥ 1. A point x of ℝ^N = Eucl N has coordinates x_j = x j for j ∈ Fin N; ℝᵏ = Eucl k. Hᵏ := μHE[k] on ℝ^N and Lᵏ := volume on ℝᵏ. Measures are evaluated on arbitrary sets as outer measures, which are monotone and countably subadditive; [0,∞] = ℝ≥0∞. The hypotheses are: E is Borel, Hᵏ(E) < ∞, and f is K-Lipschitz with K ∈ ℝ≥0. Put Y := {y ∈ ℝᵏ : E ∩ f⁻¹({y}) is infinite}. We must show Lᵏ(Y) = 0.

1. Two library facts.
 (a) On ℝᵏ, μHE[k] = Lᵏ. This is Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume k; Eucl k is EuclideanSpace ℝ (Fin k).
 (b) For every S ⊆ ℝ^N, Lᵏ(f(S)) ≤ K^k·Hᵏ(S). Indeed f is K-Lipschitz on S (LipschitzWith.lipschitzOnWith). SimonGMT Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn k then gives μHE[k](f(S)) ≤ (K:[0,∞])^k·μHE[k](S). Finally (a) rewrites the left side as Lᵏ(f(S)).

2. Dyadic cubes. For i ∈ ℕ let g_i : ℝ^N → ℤ^N (ℤ^N := Fin N → ℤ) be g_i(x) := (⌊2^i·x_j⌋)_{j ∈ Fin N}. For z ∈ ℤ^N let Q_i(z) := g_i⁻¹({z}) = {x : z_j ≤ 2^i·x_j < z_j + 1 for every j}.
 (a) For fixed i, the sets Q_i(z) (z ∈ ℤ^N) are pairwise disjoint, being preimages of distinct values of the function g_i. Moreover x ∈ Q_i(g_i(x)) for every x. The index set ℤ^N is countable.
 (b) Each Q_i(z) is Borel. It is the intersection, over the finitely many j, of the preimages of the interval [z_j, z_j + 1) under the continuous maps x ↦ 2^i·x_j. Alternatively, g_i is measurable by Mathlib Int.measurable_floor (module Mathlib.MeasureTheory.Function.Floor), and singletons of ℤ^N are measurable.
 (c) Separation. Let x, x′ ∈ ℝ^N and j ∈ Fin N with 1 ≤ 2^i·|x_j − x′_j|. Then g_i(x) ≠ g_i(x′). Otherwise ⌊2^i x_j⌋ = ⌊2^i x′_j⌋, and Int.abs_sub_lt_one_of_floor_eq_floor gives 2^i|x_j − x′_j| = |2^i x_j − 2^i x′_j| < 1, a contradiction.
 (d) Eventual separation. Let x ≠ x′. A point of ℝ^N is determined by its coordinates (ext), so there is j with c := |x_j − x′_j| > 0. Since 2^i → ∞ and i ↦ 2^i is monotone, there is i₀ with 2^i·c ≥ 1 for all i ≥ i₀. By (c), g_i(x) ≠ g_i(x′) for all i ≥ i₀; that is, ∀ᶠ i in atTop, g_i(x) ≠ g_i(x′).

3. Splitting Hᵏ(E). For every i, Σ_{z∈ℤ^N} Hᵏ(E ∩ Q_i(z)) = Hᵏ(E). The sets E ∩ Q_i(z), z ∈ ℤ^N, are countably many. They are Borel (E is Borel, and 2(b)), pairwise disjoint (2(a)), and their union is E (2(a)). Countable additivity of the measure Hᵏ (Mathlib measure_iUnion) gives the identity.

4. Counting functions and their integrals. Fix i.
 (a) For z ∈ ℤ^N put A_i(z) := f(E ∩ Q_i(z)) ⊆ ℝᵏ and B_i(z) := toMeasurable Lᵏ (A_i(z)). Then B_i(z) is Borel, A_i(z) ⊆ B_i(z), and Lᵏ(B_i(z)) = Lᵏ(A_i(z)) (Mathlib measurableSet_toMeasurable, subset_toMeasurable, measure_toMeasurable).
 (b) Define N_i : ℝᵏ → [0,∞] by N_i(y) := Σ_{z∈ℤ^N} 1_{B_i(z)}(y), the tsum of the indicator functions (B_i z).indicator 1. Each summand is Borel measurable, hence so is N_i, as a countable sum of measurable [0,∞]-valued functions (Measurable.ennreal_tsum, or Measurable.tsum).
 (c) We have ∫ N_i dLᵏ = Σ_z Lᵏ(B_i(z)) = Σ_z Lᵏ(A_i(z)) ≤ Σ_z K^k·Hᵏ(E ∩ Q_i(z)) = K^k·Σ_z Hᵏ(E ∩ Q_i(z)) = K^k·Hᵏ(E). The first equality is the monotone convergence theorem for series (lintegral_tsum) together with ∫ 1_B dLᵏ = Lᵏ(B) for Borel B (lintegral_indicator_one). The second is (a). The inequality is 1(b) with S := E ∩ Q_i(z), applied termwise (ENNReal.tsum_le_tsum). The next equality is ENNReal.tsum_mul_left, and the last is step 3.
 (d) Put C := K^k·Hᵏ(E). Since (K:[0,∞])^k < ∞ and Hᵏ(E) < ∞, C < ∞. By (c), ∫ N_i dLᵏ ≤ C for every i.

5. Large counts on infinite fibres. Let y ∈ Y and M ∈ ℕ. We claim that N_i(y) ≥ M for all sufficiently large i.
 (a) The fibre E ∩ f⁻¹({y}) is infinite, so it contains a finite set T with exactly M elements (Set.Infinite.exists_subset_card_eq).
 (b) For each of the finitely many pairs (x, x′) ∈ T × T, step 2(d) gives ∀ᶠ i, (x ≠ x′ → g_i(x) ≠ g_i(x′)). A finite conjunction of eventually-true statements is eventually true (Filter.eventually_all_finset over T ×ˢ T). Hence there is i₀ such that g_i is injective on T for every i ≥ i₀.
 (c) Fix i ≥ i₀. Every x ∈ T satisfies x ∈ E, f(x) = y and x ∈ Q_i(g_i(x)). Hence y ∈ f(E ∩ Q_i(g_i(x))) = A_i(g_i(x)) ⊆ B_i(g_i(x)), so 1_{B_i(g_i(x))}(y) = 1.
 (d) The image Z := g_i(T) ⊆ ℤ^N is finite with #Z = #T = M (Finset.card_image_of_injOn), and by (c) 1_{B_i(z)}(y) = 1 for every z ∈ Z. All terms of the series N_i(y) are nonnegative, so N_i(y) is at least its finite partial sum over Z (ENNReal.sum_le_tsum): N_i(y) ≥ Σ_{z∈Z} 1_{B_i(z)}(y) = Σ_{z∈Z} 1 = #Z = M.
 (e) Hence, for every y ∈ Y and every M ∈ ℕ, M ≤ N_i(y) for all large i. So M ≤ liminf_{i→∞} N_i(y) (Filter.le_liminf_of_le; the coboundedness side condition is automatic in the complete lattice [0,∞]). M ∈ ℕ is arbitrary and sup_M M = ∞ in [0,∞] (ENNReal.iSup_natCast). Therefore liminf_{i→∞} N_i(y) = ∞ for every y ∈ Y.

6. Fatou's lemma. Let F(y) := liminf_{i→∞} N_i(y). F is Borel measurable (Measurable.liminf). By Fatou's lemma (lintegral_liminf_le) and step 4(d), ∫ F dLᵏ ≤ liminf_{i→∞} ∫ N_i dLᵏ ≤ C < ∞. The second inequality holds because a liminf of a sequence bounded above by C is ≤ C (e.g. Filter.liminf_le_of_frequently_le' with Filter.Frequently.of_forall). A measurable [0,∞]-valued function with finite integral is finite almost everywhere (ae_lt_top). Hence Lᵏ({y : F(y) = ∞}) = 0.

7. Conclusion. By step 5(e), Y ⊆ {y : F(y) = ∞}. By monotonicity of Lᵏ (measure_mono_null), Lᵏ(Y) = 0. That is, volume {y | (E ∩ f ⁻¹' {y}).Infinite} = 0. ∎

## Key steps

1. On ℝᵏ, μHE[k] equals volume. With the SimonGMT Lipschitz image bound this gives Lᵏ(f(S)) ≤ K^k·Hᵏ(S) for every S ⊆ ℝ^N.
2. The dyadic cubes Q_i(z) = g_i⁻¹{z}, with g_i(x) = (⌊2^i x_j⌋)_j, form a countable Borel partition of ℝ^N at each level i. Two distinct points lie in distinct level-i cubes for all large i, by the floor estimate |a − b| < 1 when ⌊a⌋ = ⌊b⌋.
3. Countable additivity gives Σ_z Hᵏ(E ∩ Q_i(z)) = Hᵏ(E).
4. Take Borel hulls B_i(z) ⊇ f(E ∩ Q_i(z)) of equal Lebesgue measure. Then N_i := Σ_z 1_{B_i(z)} is measurable and ∫N_i dLᵏ ≤ K^k·Hᵏ(E) =: C < ∞.
5. If the fibre over y is infinite, then for every M, N_i(y) ≥ M for all large i, because M fibre points eventually occupy M distinct cubes. Hence liminf_i N_i(y) = ∞.
6. Fatou gives ∫ liminf_i N_i dLᵏ ≤ C < ∞, so liminf_i N_i < ∞ almost everywhere. Hence the infinite-fibre set is Lᵏ-null.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `git archive d8d46c9 | tar -x -C /tmp/bfpn_scratch; cmp /tmp/bfpn_scratch/GMT/Ch06/Submission.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical)`
- `python3 read of nodes/root-rectifiability-a1-bf-projection-null-ae-a1/parent-child-handoff.json, parent-supplied-natural-proof.md, parent-supplied-plan.md`
- `python3 listing of nodes/root-rectifiability-a1/decomposition-v1.json and decomposition-v2.json subproblems (frozen sibling types of bf_cone_density, bf_trichotomy, density_comparison)`
- `python3 scan of dag.json and nodes/*/decomposition-v*.json lean_name values (rectifiability_bf_infinite_fibre_null: no match; lpf_lli_inner_compact_approx: accepted node root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.inner_compact_approx-a1, candidate d24e9e7b; title, statement and lean_statement equal to its handoff)`
- `git show --stat d24e9e7b54d326f9d566fb5543e6cdea196355d1 (Prove lpf_lli_inner_compact_approx)`
- `python3 read of nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/parent-child-handoff.json (accepted proof and audit)`
- `python3 count of dag.json nodes (195 at 01:57, 197 at 02:21) and max_nodes in swarm-project.json and all .humanize/swarm-configs/*.json (200)`
- `sed /runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/runtime.py 945-1120, 1380-1600, 1793-1960, 4274-4360, 6498-6538; github_runtime.py 191-330, 777-790; parallel.py 60-137 (node bound, accepted-name reuse, reused-child publication)`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean; grep -n 'def PurelyUnrectifiable|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'notation "μHE\["|euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn 'measurable_floor' mathlib/Mathlib/MeasureTheory/Function/Floor.lean; grep -n 'InnerRegularCompactLTTop' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `lake build GMT.Ch06.Submission (scratch /tmp/bfpn_scratch, frozen commit d8d46c9, pinned lake-packages-25730c7c; success)`
- `python3 -I /tmp/bfpn_tools/gen.py: verifier gmt-compare.py child_modules (contract mode) -> Scratch/Ch_parent.lean, Ch_reuse.lean, Ch_eilenberg.lean; lake env lean on each (only 'declaration uses sorry')`
- `lake env lean Scratch/Glue1.lean (σ-compact Borel core from the reused type; ∃ K, LipschitzWith K L_v; #check lintegral_liminf_le, ae_lt_top, lintegral_tsum, lintegral_indicator_one, toMeasurable lemmas, Int.abs_sub_lt_one_of_floor_eq_floor, Set.Infinite.exists_subset_card_eq, Filter.eventually_all_finset, Finset.card_image_of_injOn, ENNReal.sum_le_tsum, measure_iUnion, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `lake env lean Scratch/Names2.lean (#check ENNReal.iSup_natCast, Measurable.liminf, measure_mono_null, ENNReal.tsum_mul_left, ENNReal.tsum_le_tsum, LipschitzWith.lipschitzOnWith, ae_all_iff, Measure.restrict_apply', PurelyUnrectifiable.mono, isSigmaCompact_iUnion_of_isCompact, measurableSet_Ico; EuclideanSpace coordinate ext)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-projection-null-ae-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-bf-projection-null-ae-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/557a8bd5919a409fb101d7854de51cef.json`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/github_runtime.py`
- `/runtime/flows/gmt-claude-8e94f3625cb4/_recursive_lean/parallel.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/MeasureTheory/Measure/RegularityCompacts.lean`
- `/tmp/bfpn_scratch/Scratch/Ch_parent.lean`
- `/tmp/bfpn_scratch/Scratch/Ch_reuse.lean`
- `/tmp/bfpn_scratch/Scratch/Ch_eilenberg.lean`
- `/tmp/bfpn_scratch/Scratch/Glue1.lean`
- `/tmp/bfpn_scratch/Scratch/Names2.lean`
- `/tmp/bfpn_tools/gen.py`

The frozen Submission at d8d46c9 is byte-identical to the workspace copy.

Pinned libraries. Pinned Mathlib and SimonGMT supply everything the split and the new child need:
- μHE[k] = volume on Eucl k (EuclideanSpace.euclideanHausdorffMeasure_eq_volume);
- the Lipschitz image bound for μHE (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn);
- toMeasurable hulls, lintegral_tsum, lintegral_indicator_one, measure_iUnion and the floor estimate Int.abs_sub_lt_one_of_floor_eq_floor;
- Set.Infinite.exists_subset_card_eq, Filter.eventually_all_finset and Finset.card_image_of_injOn;
- Fatou (lintegral_liminf_le), ae_lt_top and ENNReal.iSup_natCast;
- Int.measurable_floor, which exists but lives in Mathlib.MeasureTheory.Function.Floor, outside the Submission import closure; the proof also gives an Ico-preimage route.
Neither library has an Eilenberg/fibre-finiteness theorem.

Reuse. The DAG already holds the comparator-accepted Submission.lpf_lli_inner_compact_approx (accepted, candidate d24e9e7b), whose frozen type is exactly the parent's step-1 inner compact approximation. Its title, statement and type are reused verbatim. The controller code maps a reused accepted name to the existing node, so it needs no new node, and the normal publication path skips reused accepted theorems.

Budget. dag.json holds 197 of max_nodes = 200, and this split needs exactly one new node, rectifiability_bf_infinite_fibre_null. That name is unused.

Scratch checks (frozen commit, pinned packages). The parent type, the reused type and the new type all elaborate in the comparator's exact child scope, generated by gmt-compare.py child_modules in contract mode, with only the expected sorry warning. Lean also accepts two pieces of parent glue: the σ-compact Borel core from the reused type, and the Lipschitz property of L_v.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
