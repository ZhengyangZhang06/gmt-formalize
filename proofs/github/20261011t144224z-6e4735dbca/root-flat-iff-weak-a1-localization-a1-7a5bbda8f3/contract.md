<!-- theorem-id: gmt-ch06/root.flat_iff_weak-a1.localization-a1 -->

## Theorem `Submission.fiw_localization`

Assume the Slicing Theorem (SlicingTheorem) and the Boundary Rectifiability Theorem (BoundaryRectifiability). Let P, m ∈ ℕ, U ⊆ ℝ^P open, T, T_j ∈ D_{m+1}(U) integer multiplicity with sup_j (M_V(T_j) + M_V(∂T_j)) < ∞ for every open V ⊂⊂ U and T_j ⇀ T, and let W ⊂⊂ U be open. Then there exist a strictly increasing ψ : ℕ → ℕ, a compact K ⊆ U, a finite B ∈ [0, ∞) and currents T', T'_j ∈ D_{m+1}(U) such that: every T'_j and every ∂T'_j is integer multiplicity; spt T'_j ⊆ K; M(T'_j) + M(∂T'_j) ≤ B (M = M_U); T'_j ⇀ T'; and for every j and all integer multiplicity R ∈ D_{m+2}(U), S ∈ D_{m+1}(U) with T'_j − T' = ∂R + S, flatDistance W (T_{ψ(j)}) T ≤ M_W(S) + M_W(R).

Node: `root.flat_iff_weak-a1.localization-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/338

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/819, https://github.com/ZhengyangZhang06/gmt-formalize/issues/814, https://github.com/ZhengyangZhang06/gmt-formalize/issues/809

Decomposition children: None

## Lean problem

Declaration: `Submission.fiw_localization`

```lean
SlicingTheorem → BoundaryRectifiability → ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → ∀ W, CompactlyContainedOpen W U → ∃ (ψ : ℕ → ℕ) (K : Set (Eucl P)) (B : ℝ≥0∞) (T' : GeometricCurrentOn U (m + 1)) (T'j : ℕ → GeometricCurrentOn U (m + 1)), StrictMono ψ ∧ IsCompact K ∧ K ⊆ U ∧ B ≠ ∞ ∧ (∀ j, IsIntegerMultiplicity (T'j j)) ∧ (∀ j, IsIntegerMultiplicity (T'j j).boundary) ∧ (∀ j, (T'j j).support ⊆ K) ∧ (∀ j, (T'j j).mass + (T'j j).boundary.mass ≤ B) ∧ WeaklyConvergesOn T'j T' ∧ ∀ (j : ℕ) (R : GeometricCurrentOn U (m + 1 + 1)) (S : GeometricCurrentOn U (m + 1)), IsIntegerMultiplicity R → IsIntegerMultiplicity S → (∀ ω, T'j j ω - T' ω = R.boundary ω + S ω) → flatDistance W (Tj (ψ j)) T ≤ S.massOn W + R.massOn W
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

- Parent DAG node: `root.flat_iff_weak-a1`
- Child DAG node: `root.flat_iff_weak-a1.localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 7.2, the reduction (4): “by 4.5(1),(2) and an argument as in 6.7(2) of Ch. 2 we can find a subsequence {T_j'} … such that sup_j' M(∂(T_j'⌞W_i)) < ∞ … Thus from now on we can assume without loss of generality that … spt T_j ⊆ W̄”. This is combined with the parent proof's fill-in (b): the localized currents converge weakly to the localized limit, for a good level, after passing to a subsequence. This is Step 4 (i)–(v) of the parent proof, written out. Here 4.5(1) is the 4.10 clause of SlicingTheorem, 4.5(2) is IsSlice, and the boundaries of the localized currents are integer multiplicity by BoundaryRectifiability (6.3).

Notation. n := m + 1; H := μHE[n]; |α| := covectorEuclideanNorm α; ‖ω‖ := sup_x |ω(x)| for test forms; M := M_U (GeometricCurrentOn.mass). For currents X, Y and integers a, b, “aX + bY” denotes the current ω ↦ aX(ω) + bY(ω). “V ⊂⊂ U” means CompactlyContainedOpen V U. B_V := sup_j (M_V(T_j) + M_V(∂T_j)) < ∞ for V ⊂⊂ U (hypothesis).

Preliminary facts.
(F0) (Cauchy–Binet bound; self-contained.) Let τ = (τ₁,…,τ_k) be orthonormal in ℝ^P and ζ := ±simpleNVector τ, so ζ(α) = ±α(τ₁,…,τ_k). Let A_{jl} := ⟨τ_j, e_l⟩ and, for strictly increasing I : Fin k → Fin P, let A_I be the k×k minor of A on the columns I. Let dx^I ∈ Λ^k be the covector with dx^I(e_J) = δ_{IJ} for increasing J, so α = Σ_I α(e_I) dx^I.
   (a) For every α ∈ Λ^k, α(τ) = Σ_I α(e_I) det A_I. Expand τ_j = Σ_l A_{jl} e_l by multilinearity; terms with a repeated basis vector vanish by alternation; group the remaining terms by their increasing rearrangement I, the sign of the sorting permutation producing det A_I.
   (b) Σ_I (det A_I)² = 1. Apply (a) to the alternating form α₀(v₁,…,v_k) := det(⟨τ_i, v_j⟩)_{i,j}, for which α₀(e_I) = det A_I and α₀(τ) = det(⟨τ_i, τ_j⟩) = 1.
   Consequently, by Cauchy–Schwarz in the coordinates (α(e_I))_I, |ζ(α)| ≤ |α| for every α ∈ Λ^k; in particular |ζ(dx^I)| ≤ 1. For k = 0 this is immediate (ζ(α) = ±α(), |α| = |α()|).
(F1) The zero current is integer multiplicity: take M = ∅, so every condition of IsRectifiableTriple is vacuous and the integral over ∅ is 0. Also ∂0 = 0, M_V(0) = 0 for every V, and spt 0 = ∅ (every x ∈ U has a ball with compact closure in U on which 0 vanishes). M_∅(X) = 0 for every current X, since the only form with tsupport ⊆ ∅ is 0.
(F2) For X, Y ∈ D_k(U) and a, b ∈ ℤ, the map ω ↦ aX(ω) + bY(ω) is linear and sequentially continuous, hence a current, with boundary a∂X + b∂Y. If X and Y are integer multiplicity, so is aX + bY (sibling im_lincomb). For every set V: M_V(X + Y) ≤ M_V(X) + M_V(Y), since ofReal(s + t) ≤ ofReal s + ofReal t; and M_V(−X) = M_V(X), since ω is admissible iff −ω is.
(F3) Mass bound: ofReal |X(η)| ≤ M_V(X) · ofReal ‖η‖ whenever tsupport η ⊆ V. Apply GeometricCurrentOn.le_massOn to ±η/‖η‖; if ‖η‖ = 0 then η = 0.
(F4) Mass formula (sibling im_mass_formula): if X(ω) = ∫_M θ ξ(ω) dH for a rectifiable triple (M, θ, ξ) in U, then M_V(X) = ∫_{M∩V} θ dH for every open V. For an integer multiplicity X = τ(M_X, θ_X, ξ_X) write μ_X(E) := ∫_{M_X∩E} θ_X dH; then μ_X(V) = M_V(X) < ∞ for V ⊂⊂ U. Also |ξ_X(x)(α)| ≤ |α| for H-a.e. x ∈ M_X, because ξ_X(x) = ±simpleNVector of an orthonormal frame by the orientation condition (F0).
(F5) Restriction formula (uniqueness of the representing vector measure). Let X ∈ D_k(U) with X(ω) = ∫_M θ ξ(ω) dH for a rectifiable triple (M, θ, ξ), let A ⊆ ℝ^P be Borel, and let Y ∈ D_k(U) with IsRestriction X A Y, i.e. Y(ω) = ∫_A v(x)(ω(x)) dμ(x) for some (μ, v) with IsMeasureRepresentation X μ v. Then Y(ω) = ∫_{M∩A} θ ξ(ω) dH for all ω ∈ D^k(U).
   Proof.
   (i) Put v_I(x) := v(x)(dx^I), ξ_I(x) := ξ(x)(dx^I) and ω_I(x) := ω(x)(e_I). Then v(x)(ω(x)) = Σ_I ω_I(x) v_I(x) and ξ(x)(ω(x)) = Σ_I ω_I(x) ξ_I(x).
   (ii) Let O be open with closure O compact ⊆ U, and φ_O ∈ C_c^∞(U) with 0 ≤ φ_O ≤ 1 and φ_O = 1 on closure O. Testing the representation with φ_O dx^I ∈ D^k(U) shows that v_I is μ-integrable on O. Also θ ξ_I is H-integrable on M ∩ O, since |ξ_I| ≤ 1 a.e. on M (F0) and θ is integrable on M ∩ closure O. So λ_I(E) := ∫_{E∩O} v_I dμ and λ'_I(E) := ∫_{E∩O∩M} θ ξ_I dH (E ⊆ ℝ^P Borel) are finite signed Borel measures on ℝ^P concentrated on O, and ∫ ψ dλ_I = X(ψ dx^I) = ∫ ψ dλ'_I for every ψ ∈ C_c^∞(O).
   (iii) Every ψ ∈ C_c(O) is the uniform limit of its mollifications, which are uniformly bounded with supports in a fixed compact subset of O; so ∫ ψ dλ_I = ∫ ψ dλ'_I for ψ ∈ C_c(O) by dominated convergence. For a compact C ⊆ O, 1_C is the decreasing limit of ψ_q(x) := max(0, 1 − q·dist(x, C)), which lie in C_c(O) for q large (dist(C, ℝ^P ∖ O) > 0); so λ_I(C) = λ'_I(C). Let K_q be compact sets increasing to O. For a closed F ⊆ ℝ^P the compact sets F ∩ K_q increase to F ∩ O, so λ_I(F) = lim_q λ_I(F ∩ K_q) = lim_q λ'_I(F ∩ K_q) = λ'_I(F), both measures being concentrated on O. The closed sets form a π-system generating the Borel σ-algebra of ℝ^P. So the finite positive measures ν₁ := v_I⁺·μ⌞O + (θξ_I)⁻·H⌞(M ∩ O) and ν₂ := (θξ_I)⁺·H⌞(M ∩ O) + v_I⁻·μ⌞O, which agree on closed sets (including ℝ^P), are equal (MeasureTheory.ext_of_generate_finite). Hence λ_I = λ'_I.
   (iv) Given ω, choose O as in (ii) with tsupport ω ⊆ O. Each ω_I is bounded, Borel and vanishes off tsupport ω, so Y(ω) = Σ_I ∫ 1_A ω_I dλ_I = Σ_I ∫ 1_A ω_I dλ'_I = ∫_{M∩A} θ ξ(ω) dH. Points outside U contribute nothing to either side, since ω = 0 there. ∎
(F6) Restrictions of integer multiplicity currents. Let X = τ(M, θ, ξ) be integer multiplicity in U and A Borel. Then (M ∩ A, θ, ξ) is an integer multiplicity rectifiable triple in U:
   - M ∩ A ⊆ U is null-measurable and countably n-rectifiable (CountablyRectifiable.mono);
   - θ ∈ ℕ and θ > 0 on M ∩ A, and θ is integrable on M ∩ A ∩ K for compact K ⊆ U;
   - ξ is measurable for H⌞(M ∩ A);
   - orientation: apply the sibling tangent_locality to (M₁, θ₁) := (M, θ) and (M₂, θ₂) := (M ∩ A, θ). For H-a.e. x ∈ M ∩ A, the weighted approximate tangent space span τ(x) of (M, θ) at x (given by the orientation condition of X) is also that of (M ∩ A, θ), and ξ(x) = ±simpleNVector τ(x).
   The functional X⌞A(ω) := ∫_{M∩A} θ ξ(ω) dH is linear and satisfies |X⌞A(ω)| ≤ ‖ω‖ μ_X(K) when tsupport ω ⊆ K, hence is sequentially continuous. So X⌞A is a current, and it is integer multiplicity. IsRestriction X A (X⌞A) holds with the representation μ := H⌞M (μHE[n].restrict M) and v := θ • ξ: for each ω, x ↦ v(x)(ω(x)) = θ(x) ξ(x)(ω(x)) is μ-integrable (bounded by ‖ω‖ θ 1_{M∩tsupport ω}, F0), ∫ v(ω) dμ = tauAction n M θ ξ ω = X(ω), and ∫_A v(ω) dμ = X⌞A(ω). By F5, every Y with IsRestriction X A Y equals X⌞A; in particular it is integer multiplicity. By F4, M_V(X⌞A) = μ_X(V ∩ A) for open V.

Main proof.
1. (Trivial cases.) Suppose W = ∅, or every (m+1)-covector on ℝ^P vanishes (this happens exactly when P < m + 1, e.g. P = 0). Take ψ := id, K := ∅, B := 0, T' := 0 and T'_j := 0. All assertions except the last hold by F1. For the last one, R₀ := 0 and S₀ := T_j − T (integer multiplicity by F2) satisfy T_j − T = ∂R₀ + S₀, so flatDistance W (T_j) T ≤ M_W(S₀) + M_W(R₀). If W = ∅ this is 0 (F1). If P < m + 1, all currents of degree m + 1 vanish, so S₀ = 0 and it is again 0. Hence flatDistance W (T_j) T ≤ M_W(S) + M_W(R) for all R, S. From now on W ≠ ∅ and P ≥ m + 1 ≥ 1.
2. (Level function.) closure W is compact and ⊆ U, so there is δ > 0 with cthickening(2δ, closure W) ⊆ U. Let W' := thickening(δ, closure W). Then W' is open and bounded, closure W' ⊆ cthickening(δ, closure W) is compact and ⊆ U, so W' ⊂⊂ U, and closure W ⊆ W'. As W' is bounded and P ≥ 1, ℝ^P ∖ W' ≠ ∅. Let φ(x) := infDist(x, ℝ^P ∖ W'); φ is 1-Lipschitz on ℝ^P, and φ(x) > 0 iff x ∈ W' (W' is open). Let 2r₀ := min_{closure W} φ > 0, a := r₀/2 and b := r₀. For t > 0 put A_t := {x : φ(x) ≥ t}. A_t is closed, contained in W' ⊆ U (so A_t = {x ∈ U : φ(x) ≥ t}) and bounded, hence compact; and closure W ⊆ {φ > t} ⊆ A_t for t < 2r₀. Put B' := B_{W'} < ∞.
3. (Representations.) Write T_j = τ(M_j, θ_j, ξ_j) and T = τ(M_T, θ_T, ξ_T). For every V ⊂⊂ U, M_V(∂T_j) ≤ B_V < ∞, so ∂T_j is integer multiplicity by BoundaryRectifiability: ∂T_j = τ(M'_j, θ'_j, ξ'_j). Let μ_j := μ_{T_j}, μ'_j := μ_{∂T_j} and μ_T as in F4. Then μ_j(W') = M_{W'}(T_j) ≤ B', μ'_j(W') ≤ B' and μ_T(W') = M_{W'}(T) < ∞.
4. (Helly-type selection; parent Step 4(i).) For t > 0 let F_j(t) := μ_j(A_t) ∈ [0, B'] (A_t ⊆ W'); each F_j is nonincreasing. Enumerate the positive rationals. By Bolzano–Weierstrass and Cantor's diagonal argument there is a strictly increasing ψ₁ : ℕ → ℕ such that G(q) := lim_j F_{ψ₁(j)}(q) exists for every rational q > 0; G is nonincreasing on ℚ_{>0}. For t > 0 let G₋(t) := inf{G(q) : q ∈ ℚ, 0 < q < t} and G₊(t) := sup{G(q) : q ∈ ℚ, q > t}; then G₊(t) ≤ G₋(t). The set D := {t > 0 : G₊(t) < G₋(t)} is countable: for t < t' in D, G₋(t') ≤ G(q) ≤ G₊(t) for a rational q ∈ (t, t'), so the nonempty open intervals (G₊(t), G₋(t)), t ∈ D, are pairwise disjoint and each contains a rational.
5. (Slices and Fatou; parent Step 4(ii).) For each j apply SlicingTheorem to T_{ψ₁(j)}, with f := φ and L := 1 (LipschitzOnWith 1 φ U). Its hypothesis holds: M_V(T_{ψ₁(j)}) < ∞ and M_V(∂T_{ψ₁(j)}) < ∞ for V ⊂⊂ U. This gives slices S^j_t ∈ D_m(U) with IsSlice T_{ψ₁(j)} φ t (S^j_t) for every t ∈ ℝ. Apply its last clause with:
   - the open set U ⊆ U in place of W;
   - L_W := 1 (for every x, ‖fderiv ℝ φ x‖₊ ≤ 1: at points of differentiability by the Lipschitz bound, and fderiv = 0 elsewhere);
   - the interval (a, b);
   - R := T_{ψ₁(j)}⌞{x ∈ U : a < φ(x) < b}, for which IsRestriction holds by F6.
   This gives a measurable g_j : ℝ → [0, ∞] with M_U(S^j_t) ≤ g_j(t) for t ∈ (a, b) and ∫⁻_{(a,b)} g_j ≤ 1 · M_U(R) = μ_{ψ₁(j)}({a < φ < b}) ≤ μ_{ψ₁(j)}(W') ≤ B' (F6, F4; {φ > a} ⊆ W'). By Fatou's lemma (lintegral_liminf_le), ∫⁻_{(a,b)} liminf_j g_j ≤ liminf_j ∫⁻_{(a,b)} g_j ≤ B' < ∞. So liminf_j g_j(t) < ∞ for Lebesgue-a.e. t ∈ (a, b).
6. (Choice of the level; parent Step 4(iii).) The set of t ∈ (a, b) with t ∉ D and liminf_j g_j(t) < ∞ has full measure in (a, b) (D is countable), hence is nonempty; fix such an s. Let L_s := liminf_j g_j(s) < ∞. The set {j : g_j(s) < L_s + 1} is infinite, so there is a strictly increasing ψ₂ with g_{ψ₂(k)}(s) ≤ L_s + 1 for all k. Put ψ := ψ₁ ∘ ψ₂ (strictly increasing) and, for k ∈ ℕ, T*_k := T_{ψ(k)} and S_k := S^{ψ₂(k)}_s. Write M*_k, θ*_k, ξ*_k, μ*_k, μ'*_k for the data of T*_k and ∂T*_k. Then F_{ψ(k)}(q) → G(q) for every rational q > 0, and G₊(s) = G₋(s). Set K := A_s (compact, ⊆ U) and B := 2B' + L_s + 1 < ∞.
7. (Localized currents.) Let E_s := {x ∈ U : φ(x) < s} (Borel) and note U ∖ E_s = A_s. By IsSlice T*_k φ s S_k there are A_k ∈ D_n(U), B_k ∈ D_m(U) with IsRestriction T*_k E_s A_k, IsRestriction (∂T*_k) E_s B_k, and S_k(ω) = ∂A_k(ω) − B_k(ω) for all ω. By F5 (with the representations of step 3), A_k = T*_k⌞E_s and B_k = (∂T*_k)⌞E_s. Define T'_k := T*_k − A_k (a current by F2) and T' := T⌞A_s (F6). Since M*_k ⊆ U, T'_k(ω) = ∫_{M*_k∩A_s} θ*_k ξ*_k(ω) dH, i.e. T'_k = T*_k⌞A_s.
   (a) T'_k and T' are integer multiplicity (F6).
   (b) ∂T'_k = ∂T*_k − ∂A_k = (∂T*_k − B_k) − S_k, and ∂T*_k − B_k = (∂T*_k)⌞A_s (F5, and F6 for the integer multiplicity current ∂T*_k).
   (c) Masses: M(T'_k) = μ*_k(A_s) ≤ μ*_k(W') ≤ B' (F6, F4). Also M(∂T'_k) ≤ M((∂T*_k)⌞A_s) + M(S_k) ≤ μ'*_k(W') + g_{ψ₂(k)}(s) ≤ B' + L_s + 1, by F2, F6, step 5 with s ∈ (a, b), and step 6. Hence M(T'_k) + M(∂T'_k) ≤ B.
   (d) ∂T'_k is integer multiplicity, by BoundaryRectifiability applied to T'_k: M_V(∂T'_k) ≤ M(∂T'_k) < ∞ for V ⊂⊂ U, by massOn_mono.
   (e) spt T'_k ⊆ K: let x ∈ U ∖ A_s. Then x ∈ E_s, which is open, so there is ρ > 0 such that the ball B_ρ(x) has compact closure contained in E_s. Every ω with tsupport ω ⊆ B_ρ(x) vanishes on A_s, so T'_k(ω) = 0. Thus B_ρ(x) lies in zeroRegion(T'_k) and x ∉ spt T'_k.
8. (Weak convergence T'_k ⇀ T'; parent Step 4(iv).) Fix ω ∈ D^n(U) and ε > 0.
   - Choose rationals q₂ > s and q₁ ∈ (a, s) with G(q₁) − G(q₂) < ε and μ_T({q₁ < φ < s}) < ε. This is possible: G(q) → G₋(s) as q ↑ s and G(q) → G₊(s) = G₋(s) as q ↓ s through rationals; and μ_T({q < φ < s}) → 0 as q ↑ s by continuity from above of the finite measure μ_T⌞W', the sets decreasing to ∅.
   - Let χ : ℝ^P → [0, 1] be smooth with χ = 1 on {φ ≥ s} and χ = 0 on {φ ≤ q₁} (smooth Urysohn lemma for these disjoint closed sets, exists_contMDiffMap_zero_one_of_isClosed). Then χω ∈ D^n(U) and, on U, |1_{A_s} − χ| ≤ 1_{q₁ < φ < s}.
   - Using F0 and F4 (|ξ*_k(x)(ω(x))| ≤ ‖ω‖ for H-a.e. x ∈ M*_k):
     |T'_k(ω) − T*_k(χω)| = |∫_{M*_k} θ*_k (1_{A_s} − χ) ξ*_k(ω) dH| ≤ ‖ω‖ μ*_k({q₁ < φ < s}) ≤ ‖ω‖ (F_{ψ(k)}(q₁) − F_{ψ(k)}(q₂)),
     because {q₁ < φ < s} ⊆ A_{q₁} ∖ A_{q₂} and μ*_k(A_{q₂}) ≤ μ*_k(A_{q₁}) < ∞. Likewise |T'(ω) − T(χω)| ≤ ‖ω‖ μ_T({q₁ < φ < s}) ≤ ε ‖ω‖.
   - Since (T*_k) is a subsequence of (T_j) and T_j ⇀ T, T*_k(χω) → T(χω).
   Hence limsup_k |T'_k(ω) − T'(ω)| ≤ ‖ω‖ (G(q₁) − G(q₂)) + ε ‖ω‖ ≤ 2ε ‖ω‖. As ε > 0 is arbitrary, T'_k(ω) → T'(ω); thus WeaklyConvergesOn T'_k T'.
9. (Transfer; parent Step 4(v).) Let k ∈ ℕ, and let R ∈ D_{n+1}(U), S ∈ D_n(U) be integer multiplicity with T'_k(ω) − T'(ω) = ∂R(ω) + S(ω) for all ω. Put Z*_k := T*_k − T'_k = A_k = T*_k⌞E_s and Z := T − T' = T⌞E_s (as M_T ⊆ U); both are integer multiplicity (F6). Let Ŝ := S + Z*_k − Z, integer multiplicity by F2 applied twice. Then for all ω,
T*_k(ω) − T(ω) = (T'_k(ω) − T'(ω)) + Z*_k(ω) − Z(ω) = ∂R(ω) + Ŝ(ω).
So (R, Ŝ) is admissible in the infimum defining flatDistance W (T_{ψ(k)}) T, whence flatDistance W (T_{ψ(k)}) T ≤ M_W(Ŝ) + M_W(R). If tsupport ω ⊆ W, then ω = 0 on E_s (as W ⊆ {φ ≥ 2r₀} and s < 2r₀), so Z*_k(ω) = Z(ω) = 0 and Ŝ(ω) = S(ω). Therefore M_W(Ŝ) = M_W(S), and flatDistance W (T_{ψ(k)}) T ≤ M_W(S) + M_W(R).
10. (Conclusion.) By steps 6–9: ψ is strictly increasing; K is compact with K ⊆ U; B ≠ ∞; every T'_k and ∂T'_k is integer multiplicity; spt T'_k ⊆ K; M(T'_k) + M(∂T'_k) ≤ B; T'_k ⇀ T'; and the transfer inequality holds. ∎

## Key steps

1. Trivial cases (W = ∅, or P < m + 1): zero localized currents and flatDistance ≤ 0.
2. W' := thickening of closure W, φ := infDist(·, ℝ^P ∖ W'), A_t := {φ ≥ t} compact; restriction calculus: any IsRestriction of τ(M, θ, ξ) to A equals τ(M ∩ A, θ, ξ) (uniqueness of the representing vector measure) and is integer multiplicity (tangent_locality).
3. Diagonal subsequence along which μ_{T_j}(A_q) converges for all rational q; the limit G has countably many jumps.
4. Slicing (4.10 clause with W := U, L_W := 1) and Fatou give liminf_j M(slice_j(t)) < ∞ for a.e. t; choose a level s that is also a continuity point of G, and a further subsequence with bounded slice masses.
5. T'_j := T_{ψ(j)}⌞A_s is integer multiplicity; ∂T'_j = (∂T_{ψ(j)})⌞A_s − slice is integer multiplicity by BoundaryRectifiability; spt T'_j ⊆ A_s; uniform mass bound B.
6. T'_j ⇀ T⌞A_s via smooth cutoffs between rational levels q₁ < s < q₂ and continuity of G at s.
7. Transfer: T_{ψ(j)} − T = ∂R + (S + Z_j − Z), with Z_j, Z the integer multiplicity restrictions to {φ < s}, which vanish on forms supported in W.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def (flatDistance|FlatConvergenceIffWeakConvergence|DeformationTheorem|SlicingTheorem|BoundaryRectifiability|IsIntegerMultiplicity|IsRestriction|IsSlice|IsLatticeChain|IsMeasureRepresentation|CompactlyContainedOpen)|^structure IsRectifiableTriple' project/GMT/Ch06/Contract.lean`
- `rg -n 'IsIntegerMultiplicity|flatDistance' project/GMT (no match outside Contract.lean/Submission.lean)`
- `rg -n 'theorem ae_tendsto_measure_inter_div \(μ|theorem ae_tendsto_lintegral_enorm_sub_div \{|theorem exists_contMDiffMap_zero_one_of_isClosed|theorem tendsto_of_subseq_tendsto|theorem lintegral_liminf_le \{|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀|theorem hasProd_prod_of_ne_finset_one|theorem IsometryEquiv.measurePreserving_euclideanHausdorffMeasure' mathlib/Mathlib`
- `grep -n '^theorem|^def|^structure|^abbrev' over SimonGMT Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,FormsDuality,FormSupNorm}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, massOn, massOn_mono, le_massOn, WeaklyConvergesOn.massOn_le_liminf, restrictDomain, zeroRegion/support, HasWeightedApproximateTangentSpaceAt and .unique, CountablyRectifiable.mono, simpleNVector, testFormEuclideanSupNorm)`
- `rg -n -i 'flat (norm|distance|metric)|integer multiplicity|approximate tangent.*(local|subset)' SimonGMT Chapter06 Chapter03 (no integer-multiplicity calculus or flat-norm lemmas)`
- `grep Cauchy–Binet / det-of-minors in Mathlib and SimonGMT (no match; proved inline in the children)`
- `python3 listing of dag.json lean_names and nodes/*/decomposition-v1.json (no fiw_* names reserved)`
- `lake build GMT.Ch06.Submission in /tmp/fiw_check (git archive of the frozen commit d8d46c9, .lake/packages linked to the shared tree, which was left unchanged)`
- `gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement on the 8 statements; lake env lean Scratch/Ch_fiw_*.lean (0 errors)`
- `lake env lean Scratch/AssemblyExact.lean (#print axioms assembly_exact: propext, Classical.choice, Quot.sound)`
- `lake env lean Scratch/LincombExact.lean (#print axioms lincomb_exact: propext, Classical.choice, Quot.sound)`
- `book/chapter-06.txt §7 (7.1–7.3, proof of 7.2), 3.1–3.2, 3.13, 4.4–4.5, 5.1 (27)–(37); chapter-03.txt 1.4–1.9; chapter-02.txt 2.6–2.9`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/CountablyGenerated.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/fiw_check/Scratch/AssemblyExact.lean`
- `/tmp/fiw_check/Scratch/LincombExact.lean`
- `/tmp/fiw_check/Scratch/Ch_fiw_localization.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract. It defines flatDistance, IsIntegerMultiplicity, IsRestriction, IsSlice and IsLatticeChain, plus the three sibling Props this node uses (SlicingTheorem, DeformationTheorem, BoundaryRectifiability).

Neither the project nor SimonGMT has any integer-multiplicity calculus (restriction, sums, 3.13), the mass formula 3.2(3), a flat-norm lemma, or Cauchy–Binet. These are therefore introduced as children, or proved inline (Cauchy–Binet).

Mathlib in the snapshot supplies the tools cited in the child proofs:
- Besicovitch.ae_tendsto_measure_inter_div;
- VitaliFamily.ae_tendsto_lintegral_enorm_sub_div with Besicovitch.vitaliFamily;
- exists_contMDiffMap_zero_one_of_isClosed (smooth Urysohn);
- tendsto_of_subseq_tendsto;
- lintegral_liminf_le;
- euclideanHausdorffMeasure_smul₀ and IsometryEquiv.measurePreserving_euclideanHausdorffMeasure;
- hasSum_sum_of_ne_finset_zero (to_additive of hasProd_prod_of_ne_finset_one).
SimonGMT supplies massOn_mono, le_massOn, restrictDomain, zeroRegion/support and HasWeightedApproximateTangentSpaceAt.unique.

Scratch build of the frozen commit:
- all 8 child types elaborate in the comparator's exact challenge text;
- FlatConvergenceIffWeakConvergence is kernel-checked from fiw_flat_to_weak, fiw_localization, fiw_total_boundedness, fiw_flat_cauchy_limit and the three root siblings;
- fiw_im_lincomb is kernel-checked from fiw_im_series and fiw_im_mass_formula.
Both derivations use only [propext, Classical.choice, Quot.sound]. These checks do not certify the analytic child proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
