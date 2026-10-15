<!-- theorem-id: gmt-ch06/root.boundary_rectifiability-a1 -->

## Theorem `Submission.boundary_rectifiability`

For all P, m ∈ ℕ, every open U ⊆ ℝ^P and every integer multiplicity T ∈ D_{m+1}(U) with M_W(∂T) < ∞ for every open W ⊂⊂ U, the boundary ∂T ∈ D_m(U) is integer multiplicity.

Node: `root.boundary_rectifiability-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325, https://github.com/ZhengyangZhang06/gmt-formalize/issues/322, https://github.com/ZhengyangZhang06/gmt-formalize/issues/341

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/847, https://github.com/ZhengyangZhang06/gmt-formalize/issues/852, https://github.com/ZhengyangZhang06/gmt-formalize/issues/857, https://github.com/ZhengyangZhang06/gmt-formalize/issues/859, https://github.com/ZhengyangZhang06/gmt-formalize/issues/863, https://github.com/ZhengyangZhang06/gmt-formalize/issues/868, https://github.com/ZhengyangZhang06/gmt-formalize/issues/871, https://github.com/ZhengyangZhang06/gmt-formalize/issues/873, https://github.com/ZhengyangZhang06/gmt-formalize/issues/877, https://github.com/ZhengyangZhang06/gmt-formalize/issues/880

## Lean problem

Declaration: `Submission.boundary_rectifiability`

```lean
BoundaryRectifiability
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
- Child DAG node: `root.boundary_rectifiability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, 6.3 (Boundary Rectifiability Theorem) and its printed proof “A direct consequence of 6.2 above and the Compactness 3.11”, Remark 6.4 (“only the case ∂T_j = 0 ∀j of 3.11 is needed in the above proof”), the introduction to §6 (“in the case k = 0 this has already been established in 3.14”), the proof of 6.2 (approximation by the deformation theorem with the mass bounds M(P_k) ≤ cM(T), M(∂P_k) ≤ cM(∂T)), the printed steps (27)–(37) of the proof of 5.1, and the base case n = 0 of the induction in the proof of 8.2 (“the theorem is trivial in case n = 0”). Book n = m + 1. The printed argument is: approximate T (localized so that it has finite mass and boundary mass) by integer polyhedral chains P_k as in the proof of 6.2, with P_k ⇀ T and sup_k M(∂P_k) < ∞; then ∂P_k are integer multiplicity cycles of bounded mass converging weakly to ∂T, so ∂T is integer multiplicity by 3.11 in the case of zero boundaries, i.e. by 8.2 (Remark 6.4 shows this is not circular). It is written out below, with these points made explicit for the Lean statement (general ambient dimension P): (a) the mass bounds needed are those of the deformation theorem, not of the statement `PolyhedralApproximation` (which records no mass bounds), so the deformation theorem is invoked directly as in the printed proof of 6.2; (b) localization by slicing and a patching lemma replace the printed “U = ℝ^{n+ℓ} first” reduction; (c) when P = m + 1 (book k = 0) the polyhedral approximation is provided by the printed steps (27)–(37) of the proof of 5.1 with Q = T (the retraction ψ is the identity because L_n = ℝⁿ); (d) when m = 0 the case “n = 0” of the compactness theorem (trivial, as printed in 8.2) is written out. Erratum applied: the hypothesis printed “M(∂T) < ∞ ∀W ⊂⊂ U” means M_W(∂T) < ∞ (README).

Sibling results used: `DeformationTheorem` (5.3), `SlicingTheorem` (§4), `IntegralityOfWeakLimits` (8.2).

Setting. U ⊆ ℝ^P open, T ∈ D_{m+1}(U) integer multiplicity, M_W(∂T) < ∞ for all W ⊂⊂ U. Write n := m + 1. Being integer multiplicity, T has locally finite mass (M_W(T) ≤ ∫_{M∩closure W}θ dHⁿ < ∞).

Preliminaries.
(P1) Representation, restriction (Simon 2.7–2.9): currents X of locally finite mass satisfy X(ω) = ∫⟨ω,X⃗⟩dμ_X, μ_X(W) = M_W(X) for open W, X⌞A(ω) := ∫_A⟨ω,X⃗⟩dμ_X is the unique restriction, M_W(X⌞A) = μ_X(W∩A), |X(ω)| ≤ M_W(X)‖ω‖ if tsupport ω ⊆ W, and M(X) = 0 ⇒ X = 0. If X vanishes on an open set V, then μ_X(V) = 0.
(P2) Restriction of an integer multiplicity current to a Borel set is integer multiplicity (τ(M,θ,ξ)⌞A = τ(M∩A,θ,ξ); weighted tangent spaces agree a.e. by the density theorem Ch. 1, 3.6).
(P3) Extension/restriction of domains: a current X ∈ D_k(U) with compact support in U extends to X̃ ∈ D_k(ℝ^P) (X̃(ω) := X(χω), χ ∈ C_c^∞(U), 0 ≤ χ ≤ 1, χ = 1 near spt X; independent of χ because X annihilates test forms vanishing near spt X), with ∂X̃ = (∂X)~, the same masses, X̃ = X on D^k(U), integer multiplicity preserved; conversely Y ∈ D_k(ℝ^P) restricts to Y|_U ∈ D_k(U), and if Y = τ(M,θ,ξ) then Y|_U = τ(M∩U,θ,ξ) is integer multiplicity (the weighted tangent space at x ∈ U only depends on M, θ near x).
(P4) Integer lattice chains. For β : 𝓛_k(ρ) → ℤ, Σβ_F[[F]] is integer multiplicity (disjoint relative interiors, Hᵏ-null relative boundaries, local finiteness). By Stokes' theorem on a cube (Fubini and the fundamental theorem of calculus), ∂[[F]] = Σ_{i=1}^{k}(−1)^{i−1}([[F_i⁺]] − [[F_i⁻]]) for the (k−1)-faces F_i^± of F (for k = 1: ∂[[F]] = δ_{end} − δ_{start}). Hence the boundary of an integer lattice k-chain is an integer lattice (k−1)-chain, hence integer multiplicity, and its boundary is 0.
(P5) Patching lemma. Let X ∈ D_k(U). Suppose every x ∈ U has an open neighbourhood V_x ⊆ U and an integer multiplicity Y_x ∈ D_k(U) with X(ω) = Y_x(ω) whenever tsupport ω ⊆ V_x. Then X is integer multiplicity. Proof: by Lindelöf choose x_i with U = ⋃_iV_i (V_i := V_{x_i}), Y_i = τ(M_i,θ_i,ξ_i). (i) For all i, i′ the currents Y_i, Y_{i′} agree on test forms supported in V_i ∩ V_{i′}, so the ℝ^{#I(k,P)}-valued (I(k,P) = the strictly increasing k-tuples in {1,…,P}) Radon measures θ_iξ_iHᵏ⌞M_i and θ_{i′}ξ_{i′}Hᵏ⌞M_{i′} coincide on V_i ∩ V_{i′}; taking total variations (|ξ| = 1 a.e.), θ_iHᵏ⌞M_i = θ_{i′}Hᵏ⌞M_{i′} there, so Hᵏ((M_i Δ M_{i′}) ∩ V_i ∩ V_{i′}) = 0 (θ > 0), θ_i = θ_{i′} and ξ_i = ξ_{i′} Hᵏ-a.e. on M_i ∩ M_{i′} ∩ V_i ∩ V_{i′} (Radon–Nikodym uniqueness with respect to Hᵏ⌞(M_i ∪ M_{i′}), which is σ-finite, indeed locally finite in U, because θ_i, θ_{i′} take values in {1,2,…} and are integrable on compact subsets of U). (ii) Let D_i := V_i ∖ ⋃_{j<i}V_j (disjoint Borel sets covering U), M := ⋃_i(M_i ∩ D_i), θ := θ_i and ξ := ξ_i on M_i ∩ D_i. (iii) X = τ(M,θ,ξ): for a test form ω choose finitely many V_1,…,V_I covering tsupport ω and χ_i ∈ C_c^∞(V_i) with Σχ_i = 1 on tsupport ω; then X(ω) = Σ_iY_i(χ_iω) = Σ_i∫_{M_i}θ_iχ_i⟨ω,ξ_i⟩dHᵏ = Σ_i∫_Mθχ_i⟨ω,ξ⟩dHᵏ = ∫_Mθ⟨ω,ξ⟩dHᵏ, using (i) on each V_i ∩ D_j (the D_j partition U, D_j ⊆ V_j, and on V_i ∩ D_j the triple (M,θ,ξ) = (M_j,θ_j,ξ_j) agrees with (M_i,θ_i,ξ_i) up to Hᵏ-null sets). (iv) `IsRectifiableTriple U k M θ ξ`: M ⊆ U, Hᵏ-measurable, countably k-rectifiable (countable union of subsets of rectifiable sets); θ ∈ {1,2,…}; for compact K ⊆ U, K ⊆ V_1 ∪ ⋯ ∪ V_I for some I, so K ∩ D_j = ∅ for j > I and ∫_{M∩K}θ = Σ_{j≤I}∫_{M_j∩D_j∩K}θ_j < ∞; ξ is measurable; by (i), (M,θ) agrees with (M_i,θ_i) on V_i up to Hᵏ-null sets, and the weighted approximate tangent space at x ∈ V_i depends only on M ∩ V_i and θ|V_i modulo Hᵏ-null sets (for small r the blow-up integrals only see x + r·spt f ⊆ V_i, and Hᵏ(η_{x,r}Z) = r^{−k}Hᵏ(Z) = 0 for null Z), so the `orients` property of Y_i transfers to (M,θ,ξ) at Hᵏ-a.e. x ∈ M ∩ D_i.
(P6) The case n = 0 of the compactness theorem (printed: trivial). Let X_j ∈ D_0(U′) (U′ ⊆ ℝ^P open) be integer multiplicity with sup_j M_W(X_j) < ∞ for all W ⊂⊂ U′, and X_j ⇀ X. Then X is integer multiplicity. Proof: a 0-dimensional integer multiplicity current is X_j(φ) = Σ_{x∈M_j}c_j(x)φ(x) with M_j locally finite (countable, H⁰ = counting measure, θ_j ≥ 1 locally summable) and c_j = θ_jξ_j ∈ ℤ∖{0} (simple 0-vectors are ±1); M_W(X_j) = Σ_{x∈M_j∩W}|c_j(x)| (test with bumps of the right sign). Fix W ⊂⊂ U′ and C ≥ sup_jM_W(X_j). Then M_j ∩ W has at most C points; pass to a subsequence along which #(M_j ∩ W) = N is constant, the points x_{j,1},…,x_{j,N} converge to x_1,…,x_N ∈ closure(W), and the coefficients c_j(x_{j,i}) (integers bounded by C) are constant = a_i. For φ ∈ C_c^∞(W), X_j(φ) = Σ_ia_iφ(x_{j,i}) → Σ_ia_iφ(x_i) (φ = 0 on ∂W), so X(φ) = Σ_{y∈W}c(y)φ(y) with c(y) := Σ_{i : x_i = y}a_i ∈ ℤ. Using an exhaustion W_1 ⊆ W_2 ⊆ … of U′ and the fact that the coefficients of a finite sum of Dirac masses are determined by the functional, these representations are compatible, so X = Σ_{y∈D}c(y)δ_y with D := {c ≠ 0} locally finite in U′. Hence X = τ(D, |c|, sign c): D is countable (countably 0-rectifiable, H⁰-measurable), |c| ∈ {1,2,…} is locally summable, sign c = ±simpleNVector(∅), and the weighted tangent space at each isolated point of D is {0} = span ∅.
(P7) Polyhedral approximation with mass bounds. Let X ∈ D_n(ℝ^P) be integer multiplicity with M(X) + M(∂X) < ∞, and ρ > 0. Then there are integer lattice chains Pc_ρ = Σ_{F∈𝓛_n(ρ)}β_F[[F]] (β_F ∈ ℤ) with M(∂Pc_ρ) ≤ C·M(∂X) and |X(ω) − Pc_ρ(ω)| ≤ Cρ(M(X)‖dω‖ + M(∂X)‖ω‖) for all ω ∈ Dⁿ(ℝ^P), C independent of ρ:
 – if P ≥ n + 1, write ℓ := P − n ≥ 1 (so `Eucl P` = `Eucl (m+1+ℓ)` after rewriting P = m+1+ℓ) and apply `DeformationTheorem`: X − Pc = ∂R + S with M(∂Pc) ≤ CM(∂X), M(R) ≤ CρM(X), M(S) ≤ CρM(∂X), β integer valued; then |X(ω) − Pc(ω)| ≤ M(R)‖dω‖ + M(S)‖ω‖;
 – if P = n (book k = 0), use the printed steps (27)–(37) of the proof of 5.1 with Q := X: by Simon 2.35, X(a dx¹∧⋯∧dxⁿ) = ∫aθ dLⁿ with θ ∈ BV(ℝⁿ) integer valued (X integer multiplicity), M(X) = ∫|θ|, M(∂X) = |Dθ|(ℝⁿ); θLⁿ does not charge the (n−1)-skeleton of 𝓛_n(ρ), so X = Σ_{F}(θ1_{F̊})[[ℝⁿ]]; choose for each cube F ∈ 𝓛_n(ρ) an integer median β_F of θ on F̊ (31) and let Pc := Σβ_F[[F]]; by Ch. 2, 2.7 and 2.9 rescaled to cubes of side ρ (32), ∫_{F̊}|θ − β_F| ≤ cρ|Dθ|(F̊) and |D((θ−β_F)1_{F̊})|(ℝⁿ) ≤ c|Dθ|(F̊); summing over F (34),(37): M(X − Pc) ≤ cρM(∂X) and M(∂Pc) ≤ M(∂X) + M(∂(X − Pc)) ≤ (1+c)M(∂X); so |X(ω) − Pc(ω)| ≤ cρM(∂X)‖ω‖.

Proof.

1. (Trivial dimensions.) If P < n, every n-covector on ℝ^P is 0, so Dⁿ(U) = {0} and ∂T(ω) = T(dω) = T(0) = 0 for all ω; ∂T = 0 is integer multiplicity (M = ∅). Assume P ≥ n.

2. (Localization by slicing; printed 4.5 as used in 6.2.) Fix x₀ ∈ U and r₀ > 0 with B̄_{2r₀}(x₀) ⊆ U. Apply `SlicingTheorem` to T (locally finite mass and boundary mass), f := |· − x₀| (1-Lipschitz), with W := B_{2r₀}(x₀), L_W := 1, (a,b) := (r₀/2, r₀), R := T⌞{r₀/2 < f < r₀}: the slices S_r (`IsSlice T f r S_r`, i.e. ∂(T⌞B_r(x₀)) = S_r + (∂T)⌞B_r(x₀)) satisfy M_W(S_r) ≤ g(r) with ∫_{r₀/2}^{r₀}g ≤ μ_T(B_{r₀}(x₀)) < ∞, so M_W(S_r) < ∞ for a.e. r ∈ (r₀/2, r₀); since spt S_r ⊆ ∂B_r(x₀) ⊆ W is compact, M(S_r) = M_W(S_r) < ∞ for such r. Fix such an r.

3. (The localized current.) T′ := T⌞B_r(x₀) is integer multiplicity (P2), spt T′ ⊆ B̄_r(x₀) (compact ⊆ U), M(T′) ≤ μ_T(B_r(x₀)) < ∞ and M(∂T′) ≤ M(S_r) + μ_{∂T}(B_r(x₀)) < ∞. Let X := T̃′ ∈ D_n(ℝ^P) (P3): integer multiplicity, M(X) + M(∂X) < ∞, and X(η) = T(η) for every η ∈ Dⁿ(U) with tsupport η ⊆ B_r(x₀).

4. (Approximation — printed proof of 6.2, first paragraph.) For k ≥ 1 let Pc_k := Pc_{1/k} from (P7). Then for ω ∈ D^m(ℝ^P): |∂X(ω) − ∂Pc_k(ω)| = |X(dω) − Pc_k(dω)| ≤ (C/k)(M(X)‖ddω‖ + M(∂X)‖dω‖) = (C/k)M(∂X)‖dω‖ → 0, i.e. ∂Pc_k ⇀ ∂X in ℝ^P; and M(∂Pc_k) ≤ CM(∂X) for all k. By (P4) each Y_k := ∂Pc_k is integer multiplicity with ∂Y_k = 0 (when m ≥ 1).

5. (Compactness for cycles — 3.11 with ∂T_j = 0, Remark 6.4.) If m ≥ 1, write m = m′ + 1; then Y_k ∈ D_{m′+1}(ℝ^P) satisfy `IsIntegralCurrent` (Y_k and ∂Y_k = 0 are integer multiplicity), sup_k(M_W(Y_k) + M_W(∂Y_k)) ≤ CM(∂X) < ∞ for every W, and Y_k ⇀ ∂X; by `IntegralityOfWeakLimits` (with P, m′, U = ℝ^P), ∂X is integer multiplicity. If m = 0, the Y_k are integer multiplicity 0-currents with M(Y_k) ≤ CM(∂X) converging weakly to ∂X, so ∂X is integer multiplicity by (P6).

6. (Local agreement.) Let Z := (∂X)|_U ∈ D_m(U) (P3), integer multiplicity. For ω ∈ D^m(U) with tsupport ω ⊆ B_r(x₀): ∂T(ω) = T(dω) = X(dω) = ∂X(ω) = Z(ω) (Step 3, tsupport dω ⊆ B_r(x₀)). So ∂T agrees on the open neighbourhood V_{x₀} := B_r(x₀) of x₀ with an integer multiplicity current in D_m(U).

7. (Patching.) Since x₀ ∈ U was arbitrary, (P5) applied to X := ∂T (k = m) shows that ∂T is integer multiplicity. This proves `BoundaryRectifiability`.

## Key steps

1. If P < m+1 all (m+1)-forms vanish and ∂T = 0.
2. Localize: by the sibling slicing theorem, for a.e. small r, T⌞B_r(x₀) is integer multiplicity with finite mass and boundary mass; extend to ℝ^P.
3. Polyhedral approximation with mass bounds: sibling deformation theorem (P ≥ m+2) or printed steps (27)–(37) of 5.1 with Q = T (P = m+1); ∂P_k ⇀ ∂X and sup M(∂P_k) < ∞.
4. ∂P_k are integer lattice cycles (Stokes on cubes).
5. Compactness for cycles (Remark 6.4): sibling 8.2 for m ≥ 1, the n = 0 case (finitely many integer Dirac masses) for m = 0; so ∂X is integer multiplicity.
6. ∂T agrees with ∂X near x₀; the patching lemma gives ∂T integer multiplicity.

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

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/8641

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
