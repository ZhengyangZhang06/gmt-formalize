<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.integer_density-a1 -->

## Theorem `Submission.iwl_integer_density`

Assume m + 2 ≤ P, SlicingTheorem and LipschitzPushforwardIntegerMultiplicity. Let T_j, T ∈ D_{m+1}(ℝ^P) with T_j integer multiplicity, ∂T_j = 0, sup_j M(T_j) < ∞, T_j ⇀ T, and suppose T is rectifiable (IsRectifiableCurrent: T = τ(M,θ,ξ) with real θ > 0). Then T is integer multiplicity.

Node: `root.integrality_weak_limits-a1.integer_density-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/341

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/927, https://github.com/ZhengyangZhang06/gmt-formalize/issues/934, https://github.com/ZhengyangZhang06/gmt-formalize/issues/938, https://github.com/ZhengyangZhang06/gmt-formalize/issues/942, https://github.com/ZhengyangZhang06/gmt-formalize/issues/950

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2476, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2486, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2495, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2508, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2520, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2534, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2546

## Lean problem

Declaration: `Submission.iwl_integer_density`

```lean
∀ (P m : ℕ), m + 2 ≤ P → SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ j, (Tj j).boundary = 0) → (⨆ j, (Tj j).mass) < ∞ → WeaklyConvergesOn Tj T → IsRectifiableCurrent T → IsIntegerMultiplicity T
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

- Parent DAG node: `root.integrality_weak_limits-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (fixed for this proof). ℝ^P := Eucl P with standard orthonormal basis e_1,…,e_P. Hᵏ := μHE[k], the normalized k-dimensional Hausdorff measure (a positive constant multiple of μH[k]; it equals Lebesgue measure on a k-dimensional Euclidean space, and μHE[0] = μH[0] is the counting measure). D_k(U) := GeometricCurrentOn U k; D^k(U) := TestFormOn U k (C^∞ k-forms on ℝ^P with compact tsupport contained in U). I(k,P) := the strictly increasing maps {1,…,k} → {1,…,P}; for I ∈ I(k,P), e_I := (e_{I(1)},…,e_{I(k)}) and dx^I is the constant k-covector with dx^I(e_J) = δ_{IJ} (J ∈ I(k,P)); every k-covector is α = Σ_I α(e_I) dx^I. |α| := covectorEuclideanNorm α = (Σ_I α(e_I)²)^{1/2} (the norm used in the definition of mass), and ‖ω‖ := sup_x |ω(x)| for a form ω. For a k-vector w (an element of NVector = the dual of the k-covectors) put w^I := w(dx^I) and |w|_* := (Σ_I (w^I)²)^{1/2}; then w(α) = Σ_I α(e_I) w^I, so |w(α)| ≤ |α| |w|_* (Cauchy–Schwarz). M_W(X) := X.massOn W, M(X) := X.mass = M_U(X), spt X := X.support, X_j ⇀ X := WeaklyConvergesOn, ∂ := boundary. τ(M,θ,ξ)(ω) := tauAction = ∫_M θ ⟨ω,ξ⟩ dHᵏ with ⟨ω,ξ⟩(x) := ξ(x)(ω(x)); "i.m." := IsIntegerMultiplicity; "X⌞A" denotes a current S with IsRestriction X A S; W ⊂⊂ U := CompactlyContainedOpen W U. B_r(x), B̄_r(x) denote open and closed balls.

Source: Step 11 of the parent proof = the printed displays (7)–(10) of the "Proof of 8.2" (pp. 178–179), with the documented corrections: "for Lⁿ-a.e. x ∈ M" in (7) means Hⁿ-a.e.; the rescaled masses of T_{j′} are kept bounded by choosing x with Θ*ⁿ(ν,x) < ∞ for a weak limit ν of the mass measures, which justifies the printed "(8) remains valid with T_{j′} instead of T"; the final BV step is the top-dimensional case (Remark 3.12, sibling `iwl_top_dim_integrality`). Book n = m + 1, P ≥ n + 1.

Hypotheses: m + 2 ≤ P; SlicingTheorem; LipschitzPushforwardIntegerMultiplicity; T_j, T ∈ D_n(ℝ^P) with T_j i.m., ∂T_j = 0, Λ := sup_j M(T_j) < ∞, T_j ⇀ T; T rectifiable: T = τ(M,θ,ξ) with IsRectifiableTriple ℝ^P n M θ ξ (θ > 0 real). Goal: T is i.m.

Facts used. (F1) |Z(ω)| ≤ ‖ω‖M_W(Z) if tsupport ω ⊆ W. (F2) If η, η′ agree on an open set containing spt Z then Z(η) = Z(η′). (F3) Lower semicontinuity of M_W. (F4) `iwl_restriction_theory` ((R1) uniqueness, (R2) mass measures, restrictions, mass identity); restrictions of the zero current are 0. (F5) For a diffeomorphism g of ℝ^P which is affine, the classical push-forward g_#Y(ω) := Y(g^#ω) of any Y ∈ D_n(ℝ^P) is a current (g^#ω ∈ D^n(ℝ^P) since g is proper), and if Y is i.m. then g_#Y is i.m. and equals the current given by `iwl_smooth_pushforward` (take η := g^#ω in its formula (1)); ∂g_#Y = g_#∂Y; and if ‖Dg‖ ≤ c then M_W(g_#Y) ≤ cⁿ M_{g⁻¹(W)}(Y) (part (3) of `iwl_smooth_pushforward` for i.m. Y; for general Y directly from |g^#ω| ≤ cⁿ|ω∘g| and tsupport g^#ω = g⁻¹(tsupport ω)).

1. (Mass measures.) By (R2) each T_j has a mass measure μ_j with μ_j(ℝ^P) = M(T_j) ≤ Λ. By the compactness theorem for Radon measures (Simon Ch. 1, 4.16) we may pass to a subsequence (still denoted T_j; still T_j ⇀ T) such that μ_j → ν weakly (∫φ dμ_j → ∫φ dν for φ ∈ C_c(ℝ^P)) for a Radon measure ν with ν(ℝ^P) ≤ Λ. Consequently (portmanteau): limsup_j μ_j(K) ≤ ν(K) for compact K, and μ_j(B) → ν(B) for every ball B with ν(∂B) = 0. Also μ_T(B_s(y)) = M_{B_s(y)}(T) ≤ liminf_j M_{B_s(y)}(T_j) ≤ limsup_j μ_j(B̄_s(y)) ≤ ν(B̄_s(y)) (F3, mass identity).
2. (Good points.) Let G be the set of x ∈ M such that:
   (G1) the orients property holds at x: an orthonormal τ spans a weighted tangent space T_x of (M,θ) at x and ξ(x) = ±simpleNVector τ;
   (G2) x is a normalized Lebesgue point of ξ with respect to λ := θHⁿ⌞M: r^{−n}∫_{B̄_r(x)} |ξ − ξ(x)|_* dλ → 0;
   (G3) Θ*ⁿ(ν, x) < ∞.
   Hⁿ(M ∖ G) = 0: (G1) holds a.e. by assumption. λ is a locally finite Borel measure (θ is integrable on compact sets) and ξ is bounded (|ξ|_* = 1 a.e., Cauchy–Binet), so by the Lebesgue–Besicovitch differentiation theorem (Simon Ch. 1, 3.23 with 3.11(3); Mathlib `VitaliFamily.ae_tendsto_average_abs_sub`), λ(B̄_r(x))⁻¹∫_{B̄_r(x)}|ξ − ξ(x)|_* dλ → 0 for λ-a.e., hence (θ > 0) Hⁿ-a.e., x ∈ M; at points of (G1), λ(B̄_r(x)) ≤ C_x rⁿ for small r (test the tangent-space limit with f ∈ C_c, f ≥ 0, f = 1 on B̄_1(0)), giving (G2). (G3) fails only on {Θ*ⁿ(ν,·) = ∞}, which is Hⁿ-null by the comparison theorem (Simon Ch. 1, 3.3): Hⁿ({Θ*ⁿ(ν,·) ≥ t}) ≤ t⁻¹ν(ℝ^P) for all t > 0.
   We show θ(x) ∈ ℕ for every x ∈ G; fix x ∈ G.
3. (Blow-up of T; printed (7).) Fix a linear isometry Q_0 of ℝ^P with Q_0(T_x) = L_0 := ℝⁿ × {0} (dim T_x = n), and for λ > 0 let g_λ(y) := Q_0((y − x)/λ) (an affine diffeomorphism, ‖Dg_λ‖ = 1/λ). Q_0 maps τ to an orthonormal frame of L_0, so Q_{0#}ξ(x) = σ e_1∧⋯∧e_n with σ ∈ {±1}. Let Y_∞ ∈ D_n(ℝ^P), Y_∞(ω) := σθ(x)∫_{L_0} ω(e_1,…,e_n) dHⁿ (= θ(x)[[L_0]] oriented by Q_{0#}ξ(x)). Claim: g_{λ#}T ⇀ Y_∞ as λ ↓ 0. Indeed, for ω ∈ D^n(ℝ^P), using (g_λ^#ω)(y) = λ^{−n}(Q_0^#ω)((y−x)/λ) and the change of variables z = η_{x,λ}(y) := (y − x)/λ (Hⁿ(η_{x,λ}(A)) = λ^{−n}Hⁿ(A) by translation invariance and scaling of Hausdorff measure, so ∫_{η_{x,λ}(A)} g dHⁿ = λ^{−n}∫_A g∘η_{x,λ} dHⁿ),
   g_{λ#}T(ω) = ∫_M θ(y) ⟨(g_λ^#ω)(y), ξ(y)⟩ dHⁿ(y) = ∫_{η_{x,λ}(M)} θ(x + λz) ⟨(Q_0^#ω)(z), ξ(x + λz)⟩ dHⁿ(z).
   Replacing ξ(x + λz) by ξ(x) changes this by at most ‖ω‖ λ^{−n}∫_{B̄_{Rλ}(x)} |ξ − ξ(x)|_* dλ → 0 (spt ω ⊆ B_R(0); (G2) with the radius Rλ), and ∫_{η_{x,λ}(M)} θ(x + λz) ⟨(Q_0^#ω)(z), ξ(x)⟩ dHⁿ(z) → θ(x)∫_{T_x} ⟨(Q_0^#ω)(z), ξ(x)⟩ dHⁿ(z) = Y_∞(ω) by (G1) applied to the function z ↦ ⟨(Q_0^#ω)(z), ξ(x)⟩ ∈ C_c(ℝ^P) (and the isometry invariance of Hⁿ).
4. (Selection; printed (8) with T_{j′}.) Let B := B_2(0), W′ := B_1ⁿ(0) × B_{3/4}^{P−n}(0) ⊆ B (open), Ω := B_1ⁿ(0) × ℝ^{P−n}, and C_0 := 2^{n+1}ω_n(Θ*ⁿ(ν,x) + 1). Choose λ_k ↓ 0 with ν(∂B_{2λ_k}(x)) = 0 and ν(B̄_{2λ_k}(x)) ≤ (Θ*ⁿ(ν,x) + 1)ω_n(2λ_k)ⁿ (all small λ satisfy the second condition, all but countably many the first). By step 1, μ_j(B_{2λ_k}(x)) → ν(B_{2λ_k}(x)) ≤ C_0λ_kⁿ/2 as j → ∞. Fix a countable family {ω_i} ⊆ D^n(B) (forms with tsupport in B) which is dense for ‖·‖: for every ω ∈ D^n(B) and ε > 0 some ω_i has ‖ω − ω_i‖ < ε (separability of C_c(B; Λⁿ) in the sup norm and density of smooth forms). Choose j(k) strictly increasing with μ_{j(k)}(B_{2λ_k}(x)) ≤ C_0λ_kⁿ and |g_{λ_k#}T_{j(k)}(ω_i) − g_{λ_k#}T(ω_i)| < 1/k for i ≤ k (possible since g_{λ_k#}T_j(ω_i) = T_j(g_{λ_k}^#ω_i) → T(g_{λ_k}^#ω_i)). Let Y_k ∈ D_n(B) be g_{λ_k#}T_{j(k)} restricted to the domain B (`restrictDomain`), and Y the restriction of Y_∞ to B.
   - Y_k is i.m. (F5, and restricting the domain of τ(M′,θ′,ξ′) to the open set B gives τ(M′ ∩ B, θ′, ξ′), whose weighted tangent spaces at points of B are unchanged by `iwl_weighted_tangent_locality`, M′ and M′ ∩ B being null-measurable), and ∂Y_k = 0.
   - M_B(Y_k) ≤ λ_k^{−n} M_{B_{2λ_k}(x)}(T_{j(k)}) = λ_k^{−n} μ_{j(k)}(B_{2λ_k}(x)) ≤ C_0 (F5 with c = 1/λ_k, g_{λ_k}⁻¹(B) = B_{2λ_k}(x); mass identity). Similarly M_B(g_{λ_k#}T) ≤ λ_k^{−n} μ_T(B_{2λ_k}(x)) ≤ λ_k^{−n} ν(B̄_{2λ_k}(x)) ≤ C_0 (step 1), and M_B(Y) = θ(x)Hⁿ(L_0 ∩ B) < ∞.
   - Y_k ⇀ Y in B: for ω ∈ D^n(B), ε > 0 and i with ‖ω − ω_i‖ < ε, |Y_k(ω) − Y(ω)| ≤ |Y_k(ω − ω_i)| + |Y_k(ω_i) − g_{λ_k#}T(ω_i)| + |g_{λ_k#}T(ω_i) − Y(ω_i)| + |Y(ω_i − ω)| ≤ C_0ε + 1/k + o(1) + M_B(Y)ε for k ≥ i (F1, step 3).
5. (Slicing in normal directions.) Let d(y) := |(y_{n+1},…,y_P)| = dist(y, L_0) (1-Lipschitz). For each k apply SlicingTheorem in U := B to Y_k (masses finite, ∂Y_k = 0), f := d, L := 1: slices ⟨Y_k,d,γ⟩ = ∂(Y_k⌞{d<γ}) (the restriction of ∂Y_k = 0 vanishes, F4), i.m. for a.e. γ, and with W := W′, L_W := 1, (a,b) := (1/4,1/2) and the restriction of Y_k to {1/4 < d < 1/2} (exists by (R2); its M_{W′} is ≤ μ_{Y_k}(B) = M_B(Y_k) ≤ C_0): a measurable g_k ≥ M_{W′}(⟨Y_k,d,·⟩) on (1/4,1/2) with ∫⁻_{(1/4,1/2)} g_k ≤ C_0. Apply `iwl_restriction_weak_limit` in U := B to X_k := Y_k, X := Y, W := W′ (sup_k M_{W′}(Y_k) ≤ C_0), φ := d: a strictly increasing ψ and a countable E. By Fatou, liminf_k g_{ψ(k)} < ∞ a.e. on (1/4,1/2); choose γ ∈ (1/4,1/2) ∖ E with ⟨Y_{ψ(k)},d,γ⟩ i.m. for all k and liminf_k g_{ψ(k)}(γ) < ∞, then a further strictly increasing σ with sup_k M_{W′}(⟨Y_{ψσ(k)},d,γ⟩) < ∞. Relabel Y_k := Y_{ψσ(k)}. Since Y has the representation (Hⁿ⌞(L_0∩B), σθ(x)e_1∧⋯∧e_n) and L_0 ⊆ {d = 0} ⊆ {d < γ}, Y⌞{d<γ} = Y (R1). By part (A) of `iwl_restriction_weak_limit` (and passing to the subsequence σ): (Y_k⌞{d<γ})(ω) → Y(ω) for every ω with tsupport ω ⊆ W′.
6. (Localization to Ω; printed (9).) For ω ∈ D^n(Ω) the set tsupport ω ∩ {d ≤ γ} is a compact subset of W′ (its projection to ℝⁿ is a compact subset of B_1ⁿ(0), and γ < 3/4); choose ζ_ω ∈ C_c^∞(W′), 0 ≤ ζ_ω ≤ 1, ζ_ω = 1 on a neighbourhood of it, and set S_k(ω) := (Y_k⌞{d<γ})(ζ_ωω). The value does not depend on ζ_ω (two choices differ by a form vanishing on {d < γ} ∩ tsupport ω, and Y_k⌞{d<γ} only sees {d < γ}); S_k is linear and sequentially continuous (one ζ serves for a convergent sequence with supports in a fixed compact subset of Ω), so S_k ∈ D_n(Ω). Properties:
   (a) S_k is i.m.: write Y_k = τ(M_k,θ_k,ξ_k). The pair (Hⁿ⌞M_k, θ_kξ_k) is a measure representation of Y_k (|ξ_k|_* = 1 a.e. by Cauchy–Binet and θ_k is integrable on compact subsets of B, so θ_kξ_k(ω) is integrable for every test form ω), and through it the functional τ(M_k ∩ {d<γ}, θ_k, ξ_k) is a restriction of Y_k to {d<γ}; by (R1) it equals Y_k⌞{d<γ}. Hence S_k(ω) = ∫_{M_k∩{d<γ}} θ_k ξ_k(ζ_ωω) dHⁿ = ∫_{M_k∩{d<γ}∩Ω} θ_k ξ_k(ω) dHⁿ (ζ_ω = 1 wherever {d < γ} meets tsupport ω, and ω = 0 off Ω), i.e. S_k = τ(M_k ∩ {d<γ} ∩ Ω, θ_k, ξ_k). This is a rectifiable triple in Ω with natural-valued θ_k: the set is null-measurable and countably n-rectifiable (subset of M_k); for compact K ⊆ Ω, M_k ∩ {d<γ} ∩ K ⊆ M_k ∩ (K ∩ {d ≤ γ}) with K ∩ {d ≤ γ} a compact subset of W′ ⊆ B, so θ_k is integrable there; ξ_k is measurable; and since {d < γ} ∩ Ω ∩ B is open, near each of its points the indicator of M_k ∩ {d<γ} ∩ Ω coincides with that of M_k, so by `iwl_weighted_tangent_locality` (both sets null-measurable) the weighted tangent spaces (hence the orients property) are those of (M_k,θ_k).
   (b) M_Ω(S_k) ≤ M_{W′}(Y_k⌞{d<γ}) ≤ M_B(Y_k) ≤ C_0 (for admissible ω, ζ_ωω is admissible for W′; mass identity).
   (c) ∂S_k(ω) = S_k(dω) = (Y_k⌞{d<γ})(ζ dω) = ∂(Y_k⌞{d<γ})(ζω) − (Y_k⌞{d<γ})(dζ ∧ ω) = ⟨Y_k,d,γ⟩(ζω) with ζ := ζ_ω (= ζ_{dω}), because dζ ∧ ω vanishes on a neighbourhood of tsupport ω ∩ {d ≤ γ}. Hence M_Ω(∂S_k) ≤ M_{W′}(⟨Y_k,d,γ⟩) and sup_k (M_Ω(S_k) + M_Ω(∂S_k)) < ∞.
   (d) S_k ⇀ Y_Ω in Ω, where Y_Ω(ω) := σθ(x)∫_{L_0∩Ω} ω(e_1,…,e_n) dHⁿ: by step 5, S_k(ω) = (Y_k⌞{d<γ})(ζ_ωω) → Y(ζ_ωω) = Y_Ω(ω), since ζ_ω = 1 on L_0 ∩ tsupport ω.
   (e) spt S_k ⊆ B̄_1ⁿ(0) × B̄_γ^{P−n}(0) (relatively in Ω).
7. (Projection; printed (10).) Let p : ℝ^P → ℝⁿ = Eucl n be the orthogonal projection onto the first n coordinates (linear, ‖Dp‖ = 1). p maps Ω onto B_1ⁿ(0), and p⁻¹(K) ∩ spt S_k ⊆ K × B̄_γ^{P−n}(0) is compact for compact K ⊆ B_1ⁿ(0). By `iwl_smooth_pushforward` (U := Ω, V := B_1ⁿ(0), k := m, c := 1) there are i.m. currents p_#S_k ∈ D_n(B_1ⁿ(0)) with p_#S_k(ω) = S_k(η) for η agreeing with p^#ω near spt S_k, M(p_#S_k) ≤ M_Ω(S_k) and M(∂p_#S_k) ≤ M_Ω(∂S_k); so sup_k (M_W(p_#S_k) + M_W(∂p_#S_k)) < ∞ for every W. For fixed ω ∈ D^n(B_1ⁿ(0)) choose ζ ∈ C_c^∞(Ω) with ζ = 1 near p⁻¹(tsupport ω) ∩ (ℝⁿ × B̄_γ^{P−n}(0)) (a compact subset of Ω containing spt S_k ∩ p⁻¹(tsupport ω) for every k) and η := ζ p^#ω; then p_#S_k(ω) = S_k(η) → Y_Ω(η) = σθ(x)∫_{B_1ⁿ(0)} ω(e_1,…,e_n) dLⁿ, since p|_{L_0} is the identity of ℝⁿ and ζ = 1 on L_0 ∩ p⁻¹(tsupport ω). Thus p_#S_k ⇀ c[[B_1ⁿ(0)]] with c := σθ(x) ≠ 0, where c[[B_1ⁿ(0)]](ω) := c∫_{B_1ⁿ(0)} ω(e_1,…,e_n) dLⁿ (a current on B_1ⁿ(0)).
8. (Integrality of θ(x).) By `iwl_top_dim_integrality` (with U := B_1ⁿ(0) ⊆ Eucl (m+1)), c[[B_1ⁿ(0)]] is i.m.: c[[B_1ⁿ(0)]] = τ(M″,θ″,ξ″) with θ″ ∈ {1,2,…} on M″. For Hⁿ-a.e. y ∈ M″, ξ″(y) = ±simpleNVector τ with τ an orthonormal n-frame of ℝⁿ, and simpleNVector τ = det[τ]·E with det[τ] = ±1 (E = e_1∧⋯∧e_n); so ξ″ = σ″E Hⁿ-a.e. on M″ with σ″ ∈ {±1}. Testing with ω = a·dx, a ∈ C_c^∞(B_1ⁿ(0)): c∫ a dLⁿ = ∫_{M″} a θ″σ″ dLⁿ. Hence the locally integrable functions c·1_{B_1ⁿ(0)} and θ″σ″1_{M″} agree Lⁿ-a.e. on B_1ⁿ(0) (fundamental lemma of the calculus of variations). Since c ≠ 0, Lⁿ(B_1ⁿ(0) ∖ M″) = 0, so there is y ∈ M″ with c = θ″(y)σ″(y) ∈ ℤ. Therefore θ(x) = |c| ∈ ℤ, and θ(x) ≥ 1 because θ(x) > 0.
9. (Conclusion.) By step 2, the set N := {x ∈ M : θ(x) ∉ ℕ} ⊆ M ∖ G is Hⁿ-null. Let M′ := M ∖ N. Then τ(M′,θ,ξ) = τ(M,θ,ξ) = T (the integrals ignore null sets), θ ∈ ℕ on M′, and (M′,θ,ξ) is a rectifiable triple: M′ ⊆ M is null-measurable and countably n-rectifiable, θ > 0 and integrable on compact sets, ξ is AE-strongly measurable for Hⁿ⌞M′ (= Hⁿ⌞M), and the orients property holds at a.e. x ∈ M′ because, by `iwl_weighted_tangent_locality` (M and M′ = M ∖ N are null-measurable, N being Hⁿ-null, and the difference 1_Mθ − 1_{M′}θ vanishes Hⁿ-a.e.), (M′,θ) and (M,θ) have the same weighted tangent spaces at every point. Hence T is integer multiplicity. ∎

## Key steps

1. Pass to a subsequence with mass measures μ_j → ν weakly (Simon Ch. 1, 4.16).
2. For Hⁿ-a.e. x ∈ M: tangent plane, Lebesgue point of ξ, and Θ*ⁿ(ν,x) < ∞.
3. Blow-up (7): g_{λ#}T ⇀ σθ(x)[[L_0]]; choose λ_k, j(k) so that Y_k := g_{λ_k#}T_{j(k)} have bounded mass in B_2(0) and Y_k ⇀ σθ(x)[[L_0]].
4. Slice by the distance to L_0 (SlicingTheorem, iwl_restriction_weak_limit) and localize to Ω: S_k are integer multiplicity with bounded mass and boundary mass, and S_k ⇀ σθ(x)[[L_0 ∩ Ω]].
5. Project to ℝⁿ (iwl_smooth_pushforward): p_#S_k ⇀ ±θ(x)[[B_1ⁿ]]; iwl_top_dim_integrality forces θ(x) ∈ ℤ.
6. Remove the Hⁿ-null set where θ ∉ ℕ; T is integer multiplicity.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Contract.lean (identical); Submission.lean byte-identical to Contract.lean`
- `python3: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on all 12 statements`
- `python3 listing of dag.json lean_name fields (45 nodes, no iwl_* names)`
- `rg -n 'theorem exists_disjoint_closedBall_covering_ae' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `rg -n 'theorem ae_tendsto_average|theorem ae_tendsto_lintegral_div' mathlib/Mathlib/MeasureTheory/Covering/{Differentiation,DensityTheorem}.lean`
- `rg -n 'theorem hausdorffMeasure_smul|hausdorffMeasure_smul_right_image' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'ext_of_integral_eq_on_compactlySupported' mathlib/Mathlib`
- `rg -n 'theorem map_linearDependent' mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `rg -n 'countable_not_continuousAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem lintegral_liminf_le' mathlib/Mathlib`
- `sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure, euclideanHausdorffMeasure_zero)`
- `rg -il 'BoundedVariation|Rellich|Helly' mathlib/Mathlib (only 1-D bounded variation and convex Helly; no BV compactness or Helly selection)`
- `rg -n 'theorem simon_theorem_4_14|vectorFunctionalEnvelopeMeasure|theorem simon_theorem_3_3|hasSymmetricVitaliProperty_euclidean|def IsLocallyBV|isLocallyBV_of_locallyL1_of_uniform_bound' simongmt/Poincare/SimonGMT/Chapter0{1,2}`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable|countablyRectifiable_of_measure_zero|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'nVectorPushforward_simple|def simpleNVector|def covectorEuclideanNorm|massOn_le_liminf|boundary_boundary|WeaklyConvergesOn.boundary|def GeometricCurrentOn.support|restrictDomain' simongmt/Poincare/SimonGMT/Chapter06`
- `grep -n '3.3|3.6|3.11|4.14|4.16' book/chapter-01.txt; grep -n '2.6 Theorem' book/chapter-02.txt; sed -n 2290,2480p book/chapter-06.txt (printed 8.2 proof)`
- `lake build GMT.Ch06.Submission (scratch /tmp/iwl-decomp-scratch, pinned packages)`
- `lake env lean Scratch/Stmts.lean (12 child statements; only intended sorries)`
- `lake env lean Scratch/Final.lean (12 exact Submission.<name> checks + parent assembly IwlAssemblyCheck.parent + #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/iwl-decomp-scratch/Scratch/Stmts.lean`
- `/tmp/iwl-decomp-scratch/Scratch/Final.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 Contract and a byte-identical Submission with no Submission.* declarations.

Scratch Lean checks of the frozen project:
- All 12 child statements elaborate in the comparator's child scope.
- `exact Submission.<name>` resolves for each child.
- IntegralityOfWeakLimits follows from the 12 children plus SlicingTheorem, IsoperimetricTheorem, LipschitzPushforwardIntegerMultiplicity and RectifiabilityTheorem. The helper lemmas use only propext, Classical.choice and Quot.sound.
- The smoothness exponent ((⊤ : ℕ∞) : WithTop ℕ∞) was checked to mean C^∞, not analytic.

Mathlib supplies the tools the child proofs cite:
- the Besicovitch disjoint covering (`Besicovitch.exists_disjoint_closedBall_covering_ae`);
- Lebesgue–Besicovitch differentiation (`VitaliFamily.ae_tendsto_average`);
- Hausdorff scaling (`hausdorffMeasure_smul`);
- Riesz uniqueness (`Measure.ext_of_integral_eq_on_compactlySupported`);
- monotone-derivative integral bounds (`MonotoneOn.intervalIntegral_deriv_mem_uIcc`);
- Fatou (`lintegral_liminf_le`);
- `AlternatingMap.map_linearDependent`;
- μHE[0] = μH[0] (counting measure).

SimonGMT supplies the vector Riesz theorem (`simon_theorem_4_14`, `vectorFunctionalEnvelopeMeasure`), the density comparison (`simon_theorem_3_3`), `HasWeightedApproximateTangentSpaceAt.unique`, `nVectorPushforward_simple`, `WeaklyConvergesOn.massOn_le_liminf`, `GeometricCurrentOn.boundary_boundary` and `restrictDomain`.

No match was found for BV compactness, Helly's selection theorem or the product formula for Hausdorff measure. These are cited from Simon Ch. 2, 2.6, the parent's (P6), and Simon 3.2(2) / Federer 3.2.23.

The DAG (45 nodes) reserves no iwl_* name. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
