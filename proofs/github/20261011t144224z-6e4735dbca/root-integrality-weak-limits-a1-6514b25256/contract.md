<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1 -->

## Theorem `Submission.integrality_of_weak_limits`

For all P, m ∈ ℕ and every open U ⊆ ℝ^P: if T_j ∈ D_{m+1}(U) are integral currents (T_j and ∂T_j integer multiplicity) with sup_j (M_W(T_j) + M_W(∂T_j)) < ∞ for every open W ⊂⊂ U and T_j ⇀ T ∈ D_{m+1}(U), then T is integer multiplicity.

Node: `root.integrality_weak_limits-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/340, https://github.com/ZhengyangZhang06/gmt-formalize/issues/329, https://github.com/ZhengyangZhang06/gmt-formalize/issues/322, https://github.com/ZhengyangZhang06/gmt-formalize/issues/319

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/927, https://github.com/ZhengyangZhang06/gmt-formalize/issues/928, https://github.com/ZhengyangZhang06/gmt-formalize/issues/931, https://github.com/ZhengyangZhang06/gmt-formalize/issues/934, https://github.com/ZhengyangZhang06/gmt-formalize/issues/938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/940, https://github.com/ZhengyangZhang06/gmt-formalize/issues/942, https://github.com/ZhengyangZhang06/gmt-formalize/issues/950, https://github.com/ZhengyangZhang06/gmt-formalize/issues/951, https://github.com/ZhengyangZhang06/gmt-formalize/issues/953, https://github.com/ZhengyangZhang06/gmt-formalize/issues/954, https://github.com/ZhengyangZhang06/gmt-formalize/issues/955

## Lean problem

Declaration: `Submission.integrality_of_weak_limits`

```lean
IntegralityOfWeakLimits
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

- Parent DAG node: `root`
- Child DAG node: `root.integrality_weak_limits-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Theorem 8.2, Remarks 8.3(1),(2) and the printed “Proof of 8.2” (pp. 176–179), displays (1)–(10) and footnote 5; Remark 3.12 (p. 149: the case P = n “is a direct consequence of Remark 2.35 and the Compactness Theorem for BV functions”); and the tools it cites: 2.27, 2.30–2.31 (cones), 2.35, 3.2, 3.10, 4.5, 4.9, 6.1, 8.1, Ch. 1 (3.3, 3.11(3) covering, 4.16 compactness of Radon measures) and Ch. 2 (2.6 BV compactness). Book n = m + 1. The printed proof (induction on n) is copied below in numbered form. Points filled in for the exact Lean statement: (a) the printed localization 8.3(1) is carried out with an explicit choice of radii (slicing, Fatou, Helly) and a patching lemma; (b) the case P = n uses Remark 3.12 and the case P < n is trivial, because the isoperimetric theorem 6.1 is stated (and proved) for codimension ℓ ≥ 1; (c) the a.e. inequality (2) M(∂(T⌞B_r)) ≤ f′(r) (printed “by virtue of 4.9”) is derived from the integrated form of 4.9/4.10 in the sibling slicing theorem; (d) the comparison currents S_j^{(δ)} given by 6.1 are first composed with a smooth radial compression so that their supports lie in B̄_{3r_j}(ξ_j) — the printed cone estimate “(by 2.27, 2.30) |(S_j − T⌞B_j)(ω)| ≤ cM(S_j − T⌞B_j)|dω|” needs this support control (6.1 as stated only asserts compact support); (e) in the integrality step the rescaled masses of T_{j′} are kept bounded by choosing x with Θ*ⁿ(ν,x) < ∞ for a weak limit ν of the mass measures, which justifies the printed “(8) remains valid with T_{j′} instead of T”. Errata: “??(2) of Ch. 1” is the covering property 3.11(3) of Ch. 1 (Besicovitch: every Radon measure on ℝ^P has the Symmetric Vitali Property); in the justification of (3) the printed bound δ⁻¹f^{1/n}(δ) ≤ ω_n^{1/n}ε is wrong — from f(δ) < εω_nδⁿ one gets δ⁻¹f^{1/n}(δ) ≤ (ω_nε)^{1/n} — so (3) reads (d/dr)f^{1/n}(r) ≤ 2(ω_nε)^{1/n}, and (4) becomes M(S_r) ≤ c₂ε^{1/(n−1)}M(T⌞B_r(ξ)) for n ≥ 2 (instead of the printed cε); the threshold ε₀ is chosen accordingly (c₂ε₀^{1/(n−1)} ≤ ½), which is all the covering argument needs; “for Lⁿ-a.e. x ∈ M” in (7) means Hⁿ-a.e.; “σ, ρ” in footnote 5 mean ε.

Sibling results used: `RectifiabilityTheorem` (8.1), `IsoperimetricTheorem` (6.1), `SlicingTheorem` (§4), `LipschitzPushforwardIntegerMultiplicity` (3.9; used for smooth maps, where the push-forward of 3.6 is the classical one 2.23–2.24).

Statement proved, by induction on m: (I_m) for all P, all open U ⊆ ℝ^P, all T_j, T ∈ D_{m+1}(U) with T_j and ∂T_j integer multiplicity, sup_j(M_W(T_j) + M_W(∂T_j)) < ∞ for all W ⊂⊂ U, and T_j ⇀ T: T is integer multiplicity. Write n := m + 1.

Preliminaries.
(P1) Representation, restriction, mass (2.7–2.9, 2.14): currents of locally finite mass are X(ω) = ∫⟨ω,X⃗⟩dμ_X, μ_X(W) = M_W(X) (W open), X⌞A the unique restriction with M_W(X⌞A) = μ_X(W∩A), |X(ω)| ≤ M_W(X)‖ω‖ (tsupport ω ⊆ W); mass is weakly lower semicontinuous; M(X) = 0 ⇒ X = 0.
(P2) Integer multiplicity calculus (3.2): 0, restrictions to Borel sets, integer linear combinations, products [[(0,1)]]×X, images under isometries and dilations, and M-limits (3.13) of integer multiplicity currents are integer multiplicity; an integer multiplicity k-current has locally finite mass and its 0-dimensional (k = 0) version is Σ_{x∈D}c(x)δ_x with D locally finite, c ∈ ℤ∖{0}.
(P3) Smooth push-forwards (2.23–2.24) and cones (2.30–2.31, 3.10). If f is smooth and f|spt X proper, f_#X(ω) = X(ζf^#ω) (ζ ∈ C_c^∞(U) with ζ = 1 near the compact set spt X ∩ spt f^#ω; 2.23), ∂f_# = f_#∂, M_W(f_#X) ≤ sup‖Df‖^kM(X), spt f_#X ⊆ closure f(spt X); if X is integer multiplicity so is f_#X (`LipschitzPushforwardIntegerMultiplicity` gives an integer multiplicity S with `IsLipschitzPushforward X f S`; for smooth f its linear maps agree with Df on T_xM a.e., so S = f_#X. In detail: `IsLipschitzPushforward X f S` provides a representation X = τ(M′,θ′,ξ′) with θ′ > 0 real and integrable on compact subsets of U (not necessarily integer valued or ≥ 1) and linear maps L′ with S(ω) = ∫_{M′}θ′⟨ω(f(x)), L′(x)_#ξ′(x)⟩dHᵏ. At Hᵏ-a.e. x ∈ M′ the orthonormal frame τ with ξ′(x) = ±simpleNVector τ spans a weighted tangent space of (M′,θ′) at x, so the directional-derivative clause gives L′(x)τ_i = Df(x)τ_i and hence L′(x)_#ξ′(x) = Df(x)_#ξ′(x). Moreover Hᵏ(M′ ∖ spt X) = 0, because the mass measure of X is μ_X = θ′Hᵏ⌞M′ (|ξ′| = 1 a.e.), μ_X(U ∖ spt X) = 0 and θ′ > 0 on M′. Therefore, using the representation X(ζf^#ω) = ∫_{M′}θ′⟨ζf^#ω, ξ′⟩dHᵏ (ζf^#ω is a test form) and the duality ⟨(f^#ω)(x), ξ′(x)⟩ = ⟨ω(f(x)), Df(x)_#ξ′(x)⟩ (1.9), f_#X(ω) = X(ζf^#ω) = ∫_{M′}θ′ζ⟨ω(f(x)), Df(x)_#ξ′(x)⟩dHᵏ = ∫_{M′}θ′⟨ω(f(x)), L′(x)_#ξ′(x)⟩dHᵏ = S(ω); ζ may be dropped because at Hᵏ-a.e. x ∈ M′ with (f^#ω)(x) ≠ 0 we have x ∈ spt X ∩ spt f^#ω, where ζ = 1. No integrality or lower bound of θ′ is used). For X ∈ D_k(ℝ^P) with compact support and ξ ∈ ℝ^P, the cone ξ⨯X := h_#([[(0,1)]]×X), h(t,x) := ξ + t(x−ξ) (smooth), satisfies ∂(ξ⨯X) = X − ξ⨯∂X for k ≥ 1, ∂(ξ⨯X) = X − X(1)δ_ξ for k = 0 (homotopy formula 2.25 between the constant map ξ and the identity), M(ξ⨯X) ≤ sup_{x∈spt X}|x−ξ|·M(X) (2.27), spt ξ⨯X ⊆ convex hull of {ξ} ∪ spt X, and ξ⨯X is integer multiplicity if X is (P2 product + this paragraph). If ∂X = 0 (k ≥ 1), or k = 0 and X = ∂Y with Y compactly supported (then X(1) = Y(d1) = 0 after cutting off), then X = ∂(ξ⨯X).
(P4) Domains: a current X ∈ D_k(U) with compact support in U extends to X̃ ∈ D_k(ℝ^P) (X̃(ω) := X(χω), χ ∈ C_c^∞(U), 0 ≤ χ ≤ 1, χ = 1 near spt X; independent of χ), with ∂X̃ = (∂X)~, the same masses, X̃ = X on D^k(U), integer multiplicity preserved; conversely Y ∈ D_k(ℝ^P) restricts to Y|_U ∈ D_k(U), and Y = τ(M,θ,ξ) gives Y|_U = τ(M∩U,θ,ξ) integer multiplicity. Patching lemma: let X ∈ D_k(U) and suppose every x ∈ U has an open neighbourhood V_x ⊆ U and an integer multiplicity Y_x ∈ D_k(U) with X(ω) = Y_x(ω) whenever tsupport ω ⊆ V_x. Then X is integer multiplicity. Proof: by Lindelöf choose x_i with U = ⋃_iV_i (V_i := V_{x_i}), Y_i = τ(M_i,θ_i,ξ_i). (i) For all i, i′ the currents Y_i, Y_{i′} agree on test forms supported in V_i ∩ V_{i′}, so the ℝ^{#I(k,P)}-valued (I(k,P) = the strictly increasing k-tuples in {1,…,P}) Radon measures θ_iξ_iHᵏ⌞M_i and θ_{i′}ξ_{i′}Hᵏ⌞M_{i′} coincide on V_i ∩ V_{i′}; taking total variations (|ξ| = 1 a.e.), θ_iHᵏ⌞M_i = θ_{i′}Hᵏ⌞M_{i′} there, so Hᵏ((M_i Δ M_{i′}) ∩ V_i ∩ V_{i′}) = 0 (θ > 0), and θ_i = θ_{i′}, ξ_i = ξ_{i′} Hᵏ-a.e. on M_i ∩ M_{i′} ∩ V_i ∩ V_{i′} (Radon–Nikodym uniqueness with respect to Hᵏ⌞(M_i ∪ M_{i′}), which is σ-finite, indeed locally finite in U, because θ_i, θ_{i′} take values in {1,2,…} and are integrable on compact subsets of U). (ii) Let D_i := V_i ∖ ⋃_{j<i}V_j (disjoint Borel sets covering U), M := ⋃_i(M_i ∩ D_i), and θ := θ_i, ξ := ξ_i on M_i ∩ D_i (so θ(x) = θ_i(x) exactly for x ∈ M ∩ D_i). (iii) X = τ(M,θ,ξ): for a test form ω choose finitely many V_1,…,V_I covering tsupport ω and χ_i ∈ C_c^∞(V_i) with Σχ_i = 1 on tsupport ω; then X(ω) = Σ_iY_i(χ_iω) = Σ_i∫_{M_i}θ_iχ_i⟨ω,ξ_i⟩dHᵏ = Σ_i∫_Mθχ_i⟨ω,ξ⟩dHᵏ = ∫_Mθ⟨ω,ξ⟩dHᵏ, using (i) on each V_i ∩ D_j. (iv) `IsRectifiableTriple U k M θ ξ`: M ⊆ U, Hᵏ-measurable, countably k-rectifiable; θ ∈ {1,2,…}; for compact K ⊆ U, K ⊆ V_1 ∪ ⋯ ∪ V_I for some I, so K ∩ D_j = ∅ for j > I and ∫_{M∩K}θ = Σ_{j≤I}∫_{M_j∩D_j∩K}θ_j < ∞; ξ is measurable; by (i), (M,θ) agrees with (M_i,θ_i) on V_i up to Hᵏ-null sets, and the weighted approximate tangent space at x ∈ V_i depends only on M ∩ V_i and θ|V_i modulo Hᵏ-null sets (for small r the blow-up integrals only see x + r·spt f ⊆ V_i, and Hᵏ(η_{x,r}Z) = r^{−k}Hᵏ(Z) = 0 for null Z), so the `orients` property of Y_i transfers to (M,θ,ξ) at Hᵏ-a.e. x ∈ M ∩ D_i (where θ(x) = θ_i(x)).
(P5) The case n = 0 (“trivial” in the printed proof): if X_j ∈ D_0(U) are integer multiplicity with sup_jM_W(X_j) < ∞ (W ⊂⊂ U) and X_j ⇀ X, then X is integer multiplicity. Proof: X_j = Σ_{x∈M_j}c_j(x)δ_x, c_j ∈ ℤ∖{0}, Σ_{x∈M_j∩W}|c_j(x)| = M_W(X_j) ≤ C_W; for fixed W pass to a subsequence along which the ≤ C_W points of M_j ∩ W converge to points x_i ∈ closure W with constant integer coefficients a_i; then X(φ) = Σ_ia_iφ(x_i) for φ ∈ C_c^∞(W), i.e. X = Σ_{y∈W}c(y)δ_y with c(y) := Σ_{x_i=y}a_i ∈ ℤ; these local representations are compatible, so X = τ({c ≠ 0}, |c|, sign c), a locally finite integer combination of Dirac masses, which is integer multiplicity (weighted tangent space {0} at isolated points).
(P6) Restrictions converging weakly. Let X_j ⇀ X in U, W ⊆ U open with sup_jμ_{X_j}(W) < ∞ and μ_X(W) < ∞, φ : U → ℝ Lipschitz, and F_j(s) := μ_{X_j}(W ∩ {φ < s}). By Helly's selection theorem a subsequence has F_j → F pointwise, F nondecreasing. If s is a continuity point of F, then X_j⌞{φ < s}(ω) → X⌞{φ < s}(ω) along this subsequence for every test form ω with tsupport ω ⊆ W. (Proof: let χ_η := κ_η∘φ_ε with φ_ε a mollification of φ near tsupport ω (|φ_ε − φ| < η/4 there) and κ_η smooth, κ_η = 1 on (−∞, s−3η/4], κ_η = 0 on [s−η/4, ∞), so χ_η = 1 where φ ≤ s−η and χ_η = 0 where φ ≥ s on tsupport ω; then |X_j⌞{φ<s}(ω) − X_j(χ_ηω)| ≤ ‖ω‖μ_{X_j}(W ∩ {s−η < φ < s}) ≤ ‖ω‖(F_j(s) − F_j(s−η)) → ‖ω‖(F(s) − F(s−η)), similarly |X⌞{φ<s}(ω) − X(χ_ηω)| ≤ ‖ω‖μ_X(W ∩ {s−η<φ<s}), X_j(χ_ηω) → X(χ_ηω), and both error bounds → 0 as η ↓ 0.) If moreover spt X_j ∩ {φ ≤ s} lies in a fixed compact subset of W for all j, then X_j⌞{φ<s} ⇀ X⌞{φ<s} on all test forms (multiply ω by a cutoff ζ ∈ C_c^∞(W), 0 ≤ ζ ≤ 1, ζ = 1 near that compact set).
(P7) Ch. 1, 3.3: Hⁿ({x ∈ A : Θ*ⁿ(ν,x) > t}) ≤ t⁻¹ν(A) for Radon ν; in particular Hⁿ{Θ*ⁿ(ν,·) = ∞} = 0. Ch. 1, 4.16: a sequence of Radon measures with locally bounded masses has a weakly convergent subsequence. Ch. 1, 3.11(3) + 3.10: for a Radon measure ν on ℝ^P, every fine cover by closed balls of a set A of finite ν-measure has a countable disjoint subfamily covering ν-almost all of A.

Proof of (I_m).

1. (Trivial dimensions.) If P < n all n-covectors vanish, so T = 0 is integer multiplicity.

2. (The case P = n — Remark 3.12.) By 2.35 (printed: mollification as in 2.34 and Ch. 2, 2.7, 2.6), each T_j = θ_j[[U]], i.e. T_j(a dx¹∧⋯∧dxⁿ) = ∫aθ_jdLⁿ, with θ_j ∈ BV_loc(U), ∫_W|θ_j| = M_W(T_j), |Dθ_j|(W) = M_W(∂T_j); θ_j is integer valued since T_j is integer multiplicity (T_j = τ(M_j,θ′_j,±e₁∧⋯∧e_n)). By the BV compactness theorem (Ch. 2, 2.6) a subsequence θ_j → θ in L¹_loc(U), and a further subsequence converges a.e., so θ is integer valued. Then T(a dx) = lim T_j(a dx) = ∫aθ dLⁿ, so T = τ({θ ≠ 0}, |θ|, sign(θ)e₁∧⋯∧e_n), which is integer multiplicity (at Lⁿ-a.e. point of {θ ≠ 0} the weighted tangent space of ({θ≠0}, |θ|) is ℝⁿ by Lebesgue's differentiation theorem; e₁∧⋯∧e_n = simpleNVector of the standard frame). Assume from now on P ≥ n + 1.

3. (Inductive hypothesis.) (IH) If n − 1 ≥ 1, (I_{m−1}) holds (degree n − 1, all P, all U); if n − 1 = 0, (P5) holds. In both cases: weak limits of integer multiplicity (n−1)-currents with integer multiplicity boundaries and locally bounded masses and boundary masses are integer multiplicity.

4. (Localization — Remark 8.3(1).) Fix ξ₀ ∈ U and r₀ > 0 with B̄_{2r₀}(ξ₀) ⊆ U, d₀ := |· − ξ₀|, W₀ := B_{2r₀}(ξ₀), Λ₀ := sup_j(M_{W₀}(T_j) + M_{W₀}(∂T_j)). By `SlicingTheorem` (T_j has locally finite mass and boundary mass) the slices S^j_r of T_j by d₀ satisfy ∂(T_j⌞B_r(ξ₀)) = S^j_r + (∂T_j)⌞B_r(ξ₀), are integer multiplicity for a.e. r, and ∫_{r₀/2}^{r₀}M_{W₀}(S^j_r)dr ≤ ∫g_j ≤ M_{W₀}(T_j) ≤ Λ₀ (measurable majorants g_j). By Fatou, liminf_jM(S^j_r) < ∞ for a.e. r ∈ (r₀/2,r₀) (spt S^j_r ⊆ ∂B_r(ξ₀) ⊆ W₀). By (P6) (with φ = d₀, W = W₀) pass to a subsequence with F_j → F (spt(T_j⌞B_r(ξ₀)) ⊆ B̄_r(ξ₀), a fixed compact subset of W₀, so (P6) gives weak convergence on all test forms). Choose r ∈ (r₀/2,r₀) such that all S^j_r are integer multiplicity, liminf_jM(S^j_r) < ∞, and r is a continuity point of F; pass to a further subsequence with sup_jM(S^j_r) < ∞. Then X_j := T_j⌞B_r(ξ₀) and ∂X_j = S^j_r + (∂T_j)⌞B_r(ξ₀) are integer multiplicity (P2), spt X_j ⊆ B̄_r(ξ₀) =: K₀, sup_j(M(X_j) + M(∂X_j)) < ∞, and X_j ⇀ X := T⌞B_r(ξ₀) (P6). Extend to ℝ^P (P4). If we show (Steps 5–12, the special case U = ℝ^P, spt T_j ⊆ K compact) that X̃ is integer multiplicity, then X = X̃|_U is integer multiplicity and T agrees with X on the open ball B_r(ξ₀) ∋ ξ₀; by the patching lemma (P4), T is integer multiplicity. So assume U = ℝ^P, spt T_j ⊆ K (compact), Λ := sup_j(M(T_j) + M(∂T_j)) < ∞, T_j ⇀ T; then spt T ⊆ K.

5. (Reduction to ∂T = 0 — printed paragraph before (2).) ∂T_j ⇀ ∂T, the ∂T_j are integer multiplicity with ∂∂T_j = 0 and M(∂T_j) ≤ Λ, so ∂T is integer multiplicity by (IH). The cones 0⨯∂T_j, 0⨯∂T (P3) are integer multiplicity, ∂(0⨯∂T_j) = ∂T_j (P3; for n−1 = 0 use ∂T_j(1) = 0), M(0⨯∂T_j) ≤ R_KΛ (R_K := max_K|x|), supports in the compact hull of K ∪ {0}, and 0⨯∂T_j ⇀ 0⨯∂T (0⨯Y(ω) = Y(Hω) for the fixed homotopy-operator form Hω, after a cutoff near the hull). Thus T′_j := T_j − 0⨯∂T_j are integer multiplicity (P2) with ∂T′_j = 0, bounded masses, supports in a fixed compact set, and T′_j ⇀ T′ := T − 0⨯∂T. If T′ is integer multiplicity then so is T = T′ + 0⨯∂T (P2). Hence we assume ∂T_j = 0 for all j and ∂T = 0.

6. (Slices of T at balls are integer multiplicity — printed (1).) Fix ξ ∈ ℝ^P and let f(r) := μ_T(B_r(ξ)). For each j the slice of T_j by |·−ξ| at r is ∂(T_j⌞B_r(ξ)) (∂T_j = 0), integer multiplicity for a.e. r, and by `SlicingTheorem` and Fatou liminf_jM(∂(T_j⌞B_r(ξ))) < ∞ for a.e. r > 0 (on every bounded interval ∫g_j ≤ Λ). With (P6) (Helly for F_j(s) := μ_{T_j}(B_s(ξ)), along a subsequence depending on ξ), for a.e. r > 0 there is a subsequence along which T_j⌞B_r(ξ) ⇀ T⌞B_r(ξ) and sup_jM(∂(T_j⌞B_r(ξ))) < ∞; then ∂(T_j⌞B_r(ξ)) ⇀ ∂(T⌞B_r(ξ)), and by (IH) (zero boundaries) (1) ∂(T⌞B_r(ξ)) is integer multiplicity for L¹-a.e. r > 0. Its support lies in ∂B_r(ξ) and its boundary is 0.

7. (The derivative bound — printed (2), “by virtue of 4.9”.) Claim: (2) M(∂(T⌞B_r(ξ))) ≤ f′(r) for L¹-a.e. r > 0 (f is nondecreasing, hence differentiable a.e.). By `SlicingTheorem` applied to T (∂T = 0), f₀ := |·−ξ|, W = ℝ^P, L_W = 1, for every rational a < b there is a measurable g_{a,b} with M(∂(T⌞B_r(ξ))) ≤ g_{a,b}(r) on (a,b) and ∫_a^bg_{a,b} ≤ μ_T({a < |·−ξ| < b}) ≤ f(b) − f(a). Suppose the set E_q := {r : f′(r) exists, M(∂(T⌞B_r(ξ))) > f′(r) + q} had positive outer measure for some rational q > 0; then so would E_{q,k} := {r ∈ E_q : kq/4 ≤ f′(r) < (k+1)q/4} for some k ∈ ℕ. Let H be a measurable hull of E_{q,k} and r* ∈ E_{q,k} a density point of H (a.e. point of H is one, and L¹*(E_{q,k} ∖ {density points}) = 0). For rational a < r* < b close to r*: L¹(H ∩ (a,b)) ≥ (1−δ)(b−a) and f(b) − f(a) ≤ (f′(r*) + q/8)(b−a). On E_{q,k} ∩ (a,b), g_{a,b} > f′(r) + q ≥ f′(r*) + 3q/4, and {g_{a,b} > f′(r*) + 3q/4} ∩ (a,b) is a measurable superset of E_{q,k} ∩ (a,b), so its measure is ≥ L¹(H ∩ (a,b)) ≥ (1−δ)(b−a). Hence (f′(r*) + q/8)(b−a) ≥ ∫_a^bg_{a,b} ≥ (f′(r*) + 3q/4)(1−δ)(b−a), which fails for δ small (f′(r*) < (k+1)q/4). So each E_q is null, proving (2).

8. (Comparison surfaces — printed (3), (4), footnote 5.) Let ε ∈ (0, ⅛] and ξ with Θ*ⁿ(μ_T,ξ) < ε. Then limsup_{σ↓0}f(σ)/(ω_nσⁿ) < ε, so for small δ > 0, δ⁻¹∫_0^δ(d/dr)f^{1/n}dr ≤ δ⁻¹f^{1/n}(δ) ≤ (ω_nε)^{1/n} (f^{1/n} is nondecreasing, so the integral of its a.e. derivative is at most its increment), and therefore (3) (d/dr)f^{1/n}(r) ≤ 2(ω_nε)^{1/n} on a subset of (0,δ) of measure ≥ δ/2 (Chebyshev). Choose r in this set which also satisfies (1), (2), f′(r) exists and μ_T(∂B_r(ξ)) = 0 (all a.e. conditions). If f(r) = 0, put S_r := 0. Otherwise:
 • n = 1 (footnote 5): M(∂(T⌞B_r(ξ))) ≤ f′(r) = (f^{1/1})′(r) ≤ 2ω₁ε = 4ε ≤ ½ < 1 (ω₁ = 2, ε ≤ ⅛); a nonzero integer multiplicity 0-current has mass ≥ 1, so ∂(T⌞B_r(ξ)) = 0; put S_r := 0.
 • n ≥ 2: ∂(T⌞B_r(ξ)) ∈ D_{n−1}(ℝ^P) is integer multiplicity with compact support and zero boundary; apply `IsoperimetricTheorem` with m′ := n − 2, ℓ := P − n ≥ 1 (so that P = m′ + 2 + ℓ; rewrite the ambient dimension): there are c₁ = c₁(n,P) and an integer multiplicity S′_r ∈ D_n(ℝ^P) with compact support, ∂S′_r = ∂(T⌞B_r(ξ)) and M(S′_r)^{(n−1)/n} ≤ c₁M(∂(T⌞B_r(ξ))) ≤ c₁f′(r) = c₁n f(r)^{(n−1)/n}(f^{1/n})′(r) ≤ 2c₁n(ω_nε)^{1/n} f(r)^{(n−1)/n}. Hence M(S′_r) ≤ (2c₁n)^{n/(n−1)}(ω_nε)^{1/(n−1)}f(r) =: c₂ε^{1/(n−1)} M(T⌞B_r(ξ)). Support control (filled-in step): let h ∈ C^∞(ℝ), 0 ≤ h ≤ 1, h = 1 on (−∞, 2r], h = 0 on [5r/2, ∞), κ(s) := ∫_0^s h, and Φ(x) := ξ + κ(|x−ξ|)(x−ξ)/|x−ξ| (Φ = id on B_{2r}(ξ), so Φ is smooth; |Φ(x) − ξ| ≤ 5r/2). Φ is smooth with ‖DΦ‖ ≤ 1 (eigenvalues κ′ = h ∈ [0,1] and κ(s)/s ∈ [0,1]). Put S_r := Φ_#S′_r: integer multiplicity (P3), spt S_r ⊆ B̄_{3r}(ξ), ∂S_r = Φ_#∂(T⌞B_r(ξ)) = ∂(T⌞B_r(ξ)) (Φ = id near spt ∂(T⌞B_r(ξ)) ⊆ ∂B_r(ξ)), M(S_r) ≤ M(S′_r).
 In all cases: (4) S_r is integer multiplicity, spt S_r ⊆ B̄_{3r}(ξ), ∂S_r = ∂(T⌞B_r(ξ)), M(S_r) ≤ c₂ε^{1/(n−1)}M(T⌞B_r(ξ)) for n ≥ 2 and M(S_r) = 0 for n = 1, with c₂ = c₂(n,P); and such r exist in (0,δ) for every small δ > 0.

9. (Covering argument — printed (5), (6).) Fix ε := ε₀ := min{⅛, (2c₂)^{−(n−1)}} for n ≥ 2 (ε₀ := ⅛ for n = 1), so that M(S_r) ≤ ½M(T⌞B_r(ξ)) in (4). Let C be a compact subset of {x : Θ*ⁿ(μ_T,x) < ε₀} and δ > 0. The closed balls B̄_r(ξ) (ξ ∈ C, r < δ as in Step 8) cover C finely, so by (P7) there is a countable disjoint subfamily B_i := B̄_{r_i}(ξ_i) covering μ_T-almost all of C, with ⋃_iB_i ⊆ C_δ := {dist(·,C) < δ}. Let S_i := S_{r_i} (centred at ξ_i). Since μ_T(∂B_i) = 0, T⌞B_i = T⌞B_{r_i}(ξ_i) and (5) Z_i := S_i − T⌞B_i satisfies ∂Z_i = 0 and spt Z_i ⊆ B̄_{3r_i}(ξ_i); so Z_i = ∂(ξ_i⨯Z_i) and, by 2.27, |Z_i(ω)| = |(ξ_i⨯Z_i)(dω)| ≤ 3r_iM(Z_i)‖dω‖ ≤ 3δ(1 + ½)μ_T(B_i)‖dω‖. The series Σ_iS_i and Σ_iT⌞B_i converge absolutely in mass (Σ_iμ_T(B_i) ≤ M(T) ≤ Λ), so X_δ := T + Σ_iZ_i = T⌞(ℝ^P∖⋃_iB_i) + Σ_iS_i is a current with |X_δ(ω) − T(ω)| ≤ (9/2)δΛ‖dω‖; hence (6) X_δ ⇀ T as δ ↓ 0. For an open V := C_{δ₀} and δ < δ₀: M_V(X_δ) ≤ μ_T(V ∖ ⋃_iB_i) + Σ_iM(S_i) ≤ μ_T(V∖C) + ½Σ_iμ_T(B_i) ≤ μ_T(V∖C) + ½μ_T(V). By lower semicontinuity, μ_T(V) ≤ liminf_{δ↓0}M_V(X_δ) ≤ μ_T(V∖C) + ½μ_T(V), i.e. μ_T(C_{δ₀}) ≤ 2μ_T(C_{δ₀}∖C) → 0 as δ₀ ↓ 0. So μ_T(C) = 0, and by inner regularity μ_T{Θ*ⁿ(μ_T,·) < ε₀} = 0: Θ*ⁿ(μ_T,x) ≥ ε₀ > 0 for μ_T-a.e. x.

10. (Rectifiability — printed “We can therefore apply 8.1”.) T ∈ D_n(ℝ^P) has finite mass and ∂T = 0; μ_T satisfies `IsMassMeasure T μ_T` (P1) and Θ*ⁿ(μ_T,·) > 0 μ_T-a.e. (Step 9). By `RectifiabilityTheorem`, T = τ(M,θ,ξ) with `IsRectifiableTriple ℝ^P n M θ ξ` (θ real, positive).

11. (Integrality of θ — printed (7)–(10).) By Ch. 1, 4.16 pass to a subsequence with μ_{T_j} → ν weakly (ν Radon, ν(ℝ^P) ≤ Λ). For Hⁿ-a.e. x ∈ M: (a) the weighted tangent space T_xM exists, ξ(x) = ±(unit simple n-vector of T_xM), and x is a Lebesgue point of ξ for θHⁿ⌞M, so that (7) η_{x,λ#}T ⇀ θ(x)[[T_xM]] (oriented by ξ(x)) as λ ↓ 0 (as in the proof of 8.1: η_{x,λ#}T(ω) = ∫_{η_{x,λ}M}θ(x+λz)⟨ω(z),ξ(x+λz)⟩dHⁿ(z)); (b) Θ*ⁿ(ν,x) < ∞ (P7). Fix such x; after a rotation (P2) T_xM = ℝⁿ×{0} =: L₀. Let d(y) := |(y_{n+1},…,y_P)| = dist(y, L₀), p : ℝ^P → ℝⁿ the orthogonal projection, Ω := B₁ⁿ(0)×ℝ^{P−n}, W′ := B₁ⁿ(0)×B_{3/4}^{P−n}(0) ⊆ B₂(0).
 (i) Choose λ_k ↓ 0 with ν(∂B_{2λ_k}(x)) = 0; then μ_{T_j}(B_{2λ_k}(x)) → ν(B_{2λ_k}(x)) ≤ C₀λ_kⁿ (k large; C₀ := 2^{n+1}ω_n(Θ*ⁿ(ν,x)+1)). Fix a countable ‖·‖-dense family {ω_i} in Dⁿ(B₂(0)) (as in the proof of 2.15). Choose j(k) increasing with μ_{T_{j(k)}}(B_{2λ_k}(x)) ≤ 2C₀λ_kⁿ and |η_{x,λ_k#}T_{j(k)}(ω_i) − η_{x,λ_k#}T(ω_i)| < 1/k for i ≤ k. Let Y_k := η_{x,λ_k#}T_{j(k)} (as currents in B₂(0)): integer multiplicity (P2), ∂Y_k = 0, M_{B₂(0)}(Y_k) ≤ 2C₀; and since also M_{B₂(0)}(η_{x,λ_k#}T) = λ_k^{−n}μ_T(B_{2λ_k}(x)) is bounded (μ_T ≤ ν by lower semicontinuity), the density of {ω_i} and (7) give Y_k ⇀ Y := θ(x)[[L₀]] in B₂(0).
 (ii) (printed (8), with T_{j′}.) Apply `SlicingTheorem` to each Y_k (in B₂(0)) with f = d, W = W′, L_W = 1 on γ ∈ (¼,½): ∫_{1/4}^{1/2}M_{W′}(⟨Y_k,d,γ⟩)dγ ≤ M_{W′}(Y_k) ≤ 2C₀, ⟨Y_k,d,γ⟩ = ∂(Y_k⌞{d<γ}) (∂Y_k = 0), integer multiplicity for a.e. γ. By Fatou and (P6) (with W = W′, φ = d, Helly for G_k(γ) := μ_{Y_k}(W′ ∩ {d < γ})) choose γ ∈ (¼,½) and a subsequence such that all ⟨Y_k,d,γ⟩ are integer multiplicity, sup_kM_{W′}(⟨Y_k,d,γ⟩) < ∞, and Y_k⌞{d<γ}(ω) → Y⌞{d<γ}(ω) = Y(ω) for every test form ω with tsupport ω ⊆ W′ (Y is carried by {d = 0}).
 (iii) (printed (9).) Define S_k ∈ D_n(Ω) by S_k(ω) := (Y_k⌞{d<γ})(ζ_ωω), where ζ_ω ∈ C_c^∞(W′), 0 ≤ ζ_ω ≤ 1, ζ_ω = 1 on a neighbourhood of tsupport ω ∩ {d ≤ γ} (a compact subset of B₁ⁿ×B̄_γ^{P−n} ⊆ W′ since γ < ¾); the value does not depend on ζ_ω. Inside Ω, spt S_k ⊆ B₁ⁿ×B̄_γ^{P−n}. S_k is integer multiplicity (restriction, P2/P4), M_Ω(S_k) ≤ μ_{Y_k}(B₂(0)) ≤ 2C₀, ∂S_k is (the localization of) ⟨Y_k,d,γ⟩ with M_Ω(∂S_k) ≤ M_{W′}(⟨Y_k,d,γ⟩), so sup_k(M_Ω(S_k) + M_Ω(∂S_k)) < ∞; and by (ii), applied form by form to ζ_ωω, S_k ⇀ θ(x)[[L₀ ∩ Ω]] in Ω.
 (iv) (printed (10).) p|spt S_k is proper into B₁ⁿ(0), so p_#S_k ∈ D_n(B₁ⁿ(0)) is integer multiplicity (P3) with M(p_#S_k) ≤ M_Ω(S_k), M(∂p_#S_k) = M(p_#∂S_k) ≤ M_Ω(∂S_k) (‖Dp‖ = 1). By 2.35, p_#S_k(a dx) = ∫_{B₁ⁿ}aθ_kdLⁿ with θ_k ∈ BV(B₁ⁿ(0)) integer valued and ∫|θ_k| + |Dθ_k|(B₁ⁿ(0)) ≤ c (independent of k). By Ch. 2, 2.6, a subsequence θ_k → θ_∞ in L¹(B₁ⁿ(0)) with θ_∞ integer valued a.e. On the other hand p_#S_k ⇀ θ(x)p_#[[L₀ ∩ Ω]] = ±θ(x)[[B₁ⁿ(0)]] (sign of ξ(x) = ±e₁∧⋯∧e_n; p_# is weakly continuous on currents supported in the fixed set B̄₁ⁿ×B̄_γ^{P−n}). Hence θ_∞ = ±θ(x) a.e. on B₁ⁿ(0), so θ(x) ∈ ℤ, and θ(x) ≥ 1 since θ(x) > 0.
 Therefore θ ∈ {1,2,…} Hⁿ-a.e. on M; removing the Hⁿ-null set where this fails (and where the orientation property fails) from M does not change τ(M,θ,ξ) or the triple properties. So T is integer multiplicity.

12. (Conclusion.) Steps 5–11 prove the special case; Step 4 gives the general case on U via patching; Steps 1–2 cover P ≤ n; Step 3 supplies the induction. Hence (I_m) holds for all m, which is `IntegralityOfWeakLimits` (hypotheses: `IsIntegralCurrent (Tj j)` for all j, the uniform local mass bounds, and `WeaklyConvergesOn Tj T`).

## Key steps

1. Induction on m (all P, U simultaneously); base n−1 = 0 is the 0-dimensional compactness of integer Dirac sums.
2. P < m+1 trivial; P = m+1 by Remark 3.12 (2.35 + BV compactness).
3. Localize to balls (slicing, Fatou, Helly) and reduce to U = ℝ^P with supports in a fixed compact; patch back with the patching lemma.
4. Cone construction reduces to ∂T_j = 0, using the inductive hypothesis for ∂T.
5. For a.e. r, ∂(T⌞B_r(ξ)) is integer multiplicity (induction) and M(∂(T⌞B_r(ξ))) ≤ f′(r) (integrated slicing bound + density points).
6. Where Θ*ⁿ(μ_T,ξ) < ε: sibling isoperimetric theorem plus a radial compression give comparison currents S_r ⊂ B̄_{3r}(ξ) with M(S_r) ≤ c₂ε^{1/(n−1)}M(T⌞B_r(ξ)) (corrected constant).
7. Besicovitch–Vitali covering and the cone estimate show μ_T{Θ*ⁿ(μ_T) < ε₀} = 0.
8. Sibling rectifiability theorem gives T = τ(M,θ,ξ).
9. Blow-up at points with Θ*ⁿ(ν,x) < ∞, slicing in normal directions, projection and BV compactness show θ(x) ∈ ℤ, so T is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^theorem main_theorem' project/GMT/Ch06/Contract.lean`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all byte-identical)`
- `python3 listing of dag.json nodes (only 'root'; no reserved child lean_name)`
- `python3 audit of nodes/root/decomposition-audit-v2.json and decomposition-v2.json (only deformation A3 rejected; search of all 12 proofs for 'θ′ ≥ 1', 'σ-finite', 'Radon–Nikodym', 'IsLipschitzPushforward', 'LipschitzPushforwardIntegerMultiplicity', 'as in the conventions')`
- `rg -n 'theorem sigmaFinite_of_countable' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `rg -n 'theorem mul_meas_ge_le_lintegral₀' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n 'theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite|theorem Integrable.ae_eq_of_forall_setIntegral_eq' mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n 'theorem hausdorffMeasure_image_le (h : LipschitzWith' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem restrict_congr_set|theorem restrict_restrict [(]|theorem ae_restrict_iff.₀|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -il 'coarea|co-area' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -il 'Besicovitch.Federer|purely unrectifiable' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'abbrev NVector|def simpleNVector|def nVectorPushforward|theorem nVectorPushforward_simple|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/`
- `#print MeasureTheory.Measure.euclideanHausdorffMeasure (μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `grep -n '1.12|1.15|Borel-regular|3.19|3.24' book/chapter-01.txt`
- `lake build GMT.Ch06.Submission (scratch /tmp/gmt_ch06_v3_check, frozen commit d8d46c9, pinned packages)`
- `lake env lean Scratch/V3_Stmts.lean (12 child statements in gmt-compare.py contract_scope; 0 errors)`
- `lake env lean Scratch/V3_Assembly.lean (exact Submission.<name>; 12-way assembly vs type_of% GMT.Ch06.main_theorem; ff_from_siblings; parent_from_children; #print axioms)`
- `lake env lean Scratch/V3_SigmaFinite.lean (v3_sigmaFinite_restrict; #print axioms)`
- `lake env lean Scratch/V3_Tangent.lean (v3_weightedTangent_congr; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Stmts.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Assembly.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_SigmaFinite.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Tangent.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, a byte-identical Submission with no Submission.* declarations, and the README. The DAG contains only root, so the 12 bare child names are unreserved. All 12 conjuncts are `def … : Prop` in namespace GMT.Ch06. In a scratch build of the frozen project, every child statement elaborates in the comparator's child scope, `exact Submission.<name>` resolves for all 12 children, and the 12-way assembly typechecks against `type_of% GMT.Ch06.main_theorem`. FedererFlemingCompactness follows from its three declared siblings and the parent from the other 11 children, with axioms [propext, Classical.choice, Quot.sound]. The contract's `IsLipschitzPushforward` supplies only an `IsRectifiableTriple` representation (θ′ > 0 real, integrable on compacts), confirming the v2 defect. The repaired deformation A3 uses only that. Its σ-finiteness step is kernel-checked as `v3_sigmaFinite_restrict` (via Mathlib `Measure.sigmaFinite_of_countable`, `mul_meas_ge_le_lintegral₀`, `Measure.restrict_restrict`, `ae_restrict_mem₀`), and its tangent-space step as `v3_weightedTangent_congr`, against the actual SimonGMT `HasWeightedApproximateTangentSpaceAt`/`blowUpMap` definitions (via `LipschitzWith.hausdorffMeasure_image_le`, `Measure.restrict_congr_set`, `ae_restrict_iff'₀`; μHE[d] is a scalar multiple of μH[d]), both with standard axioms only. Mathlib provides Radon–Nikodym-type uniqueness (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`, `Integrable.ae_eq_of_forall_setIntegral_eq`). SimonGMT provides `nVectorPushforward_simple`, `covectorEuclideanNorm` and `HasWeightedApproximateTangentSpaceAt.unique`. Simon Ch. 1 gives 1.12 (μ⌞Y is Borel regular for measurable Y of finite measure), 1.15(2) (inner regularity) and 2.6 (H^m is Borel regular), as cited. There is no Mathlib match for co-area or for Besicovitch–Federer/purely unrectifiable; these are cited from Simon Ch. 3, as SimonGMT omits them. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
