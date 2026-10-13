<!-- theorem-id: gmt-ch06/root.flat_iff_weak-a1.total_boundedness-a1.extend-a1 -->

## Theorem `Submission.fiw_tb_extend_to_univ`

Assume MF (as in support_null). Let P, m ∈ ℕ, U ⊆ ℝ^P open, K ⊆ U compact and X ∈ D_{m+1}(U) with spt X ⊆ K and M(X) < ∞. Then there is Y ∈ D_{m+1}(ℝ^P) (a current on univ) with Y.restrictDomain (subset_univ U) = X, spt Y ⊆ K, M(Y) ≤ M(X) and M(∂Y) ≤ M(∂X) (M is the mass on the domain of each current), such that Y is integer multiplicity whenever X is, and ∂Y is integer multiplicity whenever ∂X is.

Node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/826

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2338, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2343

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3227, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3232, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3238, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3248, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3262, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1188, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1914, https://github.com/ZhengyangZhang06/gmt-formalize/issues/720, https://github.com/ZhengyangZhang06/gmt-formalize/issues/847, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3291, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3303, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3312

## Lean problem

Declaration: `Submission.fiw_tb_extend_to_univ`

```lean
(∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (T : GeometricCurrentOn U n) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple U n M θ ξ → (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) → ∀ W : Set (Eucl P), IsOpen W → T.massOn W = ∫⁻ x in M ∩ W, ENNReal.ofReal (θ x) ∂(μHE[n] : Measure (Eucl P))) → ∀ (P m : ℕ) (U K : Set (Eucl P)), IsOpen U → IsCompact K → K ⊆ U → ∀ X : GeometricCurrentOn U (m + 1), X.support ⊆ K → X.mass ≠ ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1), Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y) ∧ (IsIntegerMultiplicity X.boundary → IsIntegerMultiplicity Y.boundary)
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

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.extend-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, preliminaries (G1), (G2), (G3)(i)–(vi) (extension to ℝ^P, parent (P3)). MF is the frozen statement of the parent's sibling fiw_im_mass_formula. Uses the siblings vanish_off_support and support_null. Instead of proving (G3)(iii) through the Leibniz formula for d(χω), the boundary is handled by the restriction identity of step 7 together with Lemmas A and B, which are proved for an arbitrary degree q. Sequential continuity of the extension (step 4) uses the hypothesis M(X) < ∞ through the parent's mass bound (F3), so only zeroth derivatives of test forms enter and no Leibniz bound for derivatives of χω is needed. Every library fact cited below is available under the imports of GMT.Ch06.Submission.

Notation. Currents on ℝ^P are currents on univ. ι := testFormOnInclusion (subset_univ U) q : D^q(U) → D^q(ℝ^P) (same underlying form). For Z ∈ D_q(ℝ^P), Z|_U := Z.restrictDomain (subset_univ U), so Z|_U(ω) = Z(ιω). |α| := covectorEuclideanNorm α; directly from its definition (square root of the sum of the squares of the coefficients α(e_I), I strictly increasing), |cα| = |c|·|α| for c ∈ ℝ. H^q := μHE[q]. M(·) is the mass on the domain of the current.

1. Cutoff. K is compact, U open, and ℝ^P is locally compact Hausdorff, so there is a compact L with K ⊆ interior L and L ⊆ U (exists_compact_between). K is closed. Smooth Urysohn (exists_contMDiffMap_one_nhds_of_subset_interior with model 𝓘(ℝ, ℝ^P), smoothness ∞, s := K (closed), t := L, using K ⊆ interior L) gives a smooth χ : ℝ^P → ℝ together with, in this order: (∀ᶠ x in 𝓝ˢ K, χ x = 1), (∀ x ∉ L, χ x = 0) and (∀ x, χ x ∈ [0, 1]). By mem_nhdsSet_iff_exists, the first gives an open set N ⊇ K with χ = 1 on N. (ContMDiff for the model 𝓘(ℝ, ℝ^P) is ContDiff ℝ ∞; in Lean write the smoothness exponent as ((⊤ : ℕ∞) : WithTop ℕ∞).) Since L is closed and contains support χ, tsupport χ ⊆ L, so tsupport χ is compact and contained in U. Also {x : χ(x) ≠ 1} ⊆ ℝ^P ∖ N, a closed set; hence tsupport(1 − χ) ⊆ ℝ^P ∖ N, which is disjoint from K.
2. Products with χ. For every test q-form ω on ℝ^P, χ•ω (x ↦ χ(x)ω(x)) is smooth and tsupport(χ•ω) ⊆ tsupport χ ∩ tsupport ω; hence χ•ω ∈ D^q(U), and m_χ : D^q(ℝ^P) → D^q(U), ω ↦ χ•ω, is linear. For a test form ω on ℝ^P or on U, (1 − χ)•ω = ω − χ•ω is a test form on the same domain with tsupport((1 − χ)•ω) ⊆ tsupport(1 − χ) ⊆ ℝ^P ∖ N, which is disjoint from K. Finally |χ(x)ω(x)| = χ(x)|ω(x)| ≤ |ω(x)|. (Compact support of x ↦ g(x) • ω(x) is best obtained from IsCompact.of_isClosed_subset with tsupport_smul_subset_right rather than HasCompactSupport.smul_left.)
3. Vanishing fact (V). If Z is a q-current on ℝ^P (resp. on U) with spt Z ⊆ K and ω is a test q-form on ℝ^P (resp. on U), then Z((1 − χ)•ω) = 0 by the sibling vanish_off_support, because tsupport((1 − χ)•ω) is disjoint from K ⊇ spt Z. Hence Z(ω) = Z(χ•ω) by linearity.
4. Definition of Y and its continuity. For ω ∈ D^{m+1}(ℝ^P) put Y(ω) := X(m_χ ω); Y is linear because m_χ and X are. Put μ_X := M(X).toReal, a real number because M(X) < ∞. Sequential continuity (as required by GeometricCurrentOn) follows from the finite mass of X:
   (a) Evaluation bound (parent fact F3). If η ∈ D^{m+1}(U), c > 0 and |η(x)| ≤ c for every x, then |X(η)| ≤ c·μ_X. Indeed |tα| = |t|·|α| for t ∈ ℝ (each squared coefficient α(e_I)² in the definition of covectorEuclideanNorm is multiplied by t², and √(t²s) = |t|√s), so c⁻¹η and −c⁻¹η lie in massAdmissibleOn U (m+1) U (tsupport ⊆ U, coefficient norm ≤ 1). By GeometricCurrentOn.le_massOn, ofReal(c⁻¹X(η)) ≤ M(X) and ofReal(−c⁻¹X(η)) = ofReal(X(−c⁻¹η)) ≤ M(X); since M(X) ≠ ∞, ENNReal.ofReal_le_iff_le_toReal gives ±c⁻¹X(η) ≤ μ_X, i.e. |X(η)| ≤ c·μ_X.
   (b) Coefficient norm versus operator norm. Every α ∈ Covector(ℝ^P)(m+1) satisfies |α| ≤ A₀‖α‖, where ‖α‖ is the operator norm of the continuous alternating map α and A₀ := √(P^{m+1}). Indeed, for I : Fin (m+1) → Fin P, ContinuousAlternatingMap.le_opNorm and ‖EuclideanSpace.basisFun (Fin P) ℝ i‖ = 1 give |α(e_{I(0)}, …, e_{I(m)})| ≤ ‖α‖; the sum defining |α|² has card(Fin (m+1) → Fin P) = P^{m+1} terms, each ≤ ‖α‖², so |α| ≤ √(P^{m+1}·‖α‖²) = A₀‖α‖.
   (c) Let ω_j → 0 in the sense of TestFormOnConverges on univ: there is a compact K' with tsupport ω_j ⊆ K' for every j, and (taking k = 0) iteratedFDeriv ℝ 0 ω_j → iteratedFDeriv ℝ 0 0 = 0 uniformly on K'. As ‖iteratedFDeriv ℝ 0 f x‖ = ‖f x‖ (norm_iteratedFDeriv_zero), for every ε > 0 there is j₀ with ‖ω_j(x)‖ < ε for all j ≥ j₀ and x ∈ K'; for x ∉ K', ω_j(x) = 0. Hence, for j ≥ j₀ and every x, |χ(x)ω_j(x)| = χ(x)|ω_j(x)| ≤ A₀ε, by (b) and 0 ≤ χ ≤ 1.
   (d) By (a) with η := m_χ ω_j ∈ D^{m+1}(U) and c := (A₀ + 1)ε > 0, |Y(ω_j)| = |X(m_χ ω_j)| ≤ (A₀ + 1)ε·μ_X for all j ≥ j₀. As ε > 0 is arbitrary, Y(ω_j) → 0. Thus Y ∈ D_{m+1}(ℝ^P).
5. Y|_U = X. For ω ∈ D^{m+1}(U): Y(ιω) = X(χ•ω) (the χ•ω's agree as elements of D^{m+1}(U)), and X(ω) = X(χ•ω) by (V) applied to X (spt X ⊆ K). By GeometricCurrentOn.ext, Y.restrictDomain (subset_univ U) = X.
6. spt Y ⊆ K. Let x ∉ K. As K is closed there is r > 0 with closedBall(x, r) ∩ K = ∅. W := ball(x, r) is open, its closure lies in the compact set closedBall(x, r) (so it is compact) and in ℝ^P. If ω ∈ D^{m+1}(ℝ^P) and tsupport ω ⊆ W, then tsupport(χ•ω) ⊆ W is disjoint from K ⊇ spt X, so Y(ω) = X(χ•ω) = 0 by vanish_off_support. Hence Y vanishes on W, x ∈ zeroRegion(Y) and x ∉ spt Y = ℝ^P ∖ zeroRegion(Y).
7. Boundary relations. (a) (∂Y)|_U = ∂X: for ω ∈ D^m(U), (∂Y)(ιω) = Y(d(ιω)), and d(ιω) = ι(dω) (both have the underlying form dω), so (∂Y)(ιω) = Y(ι(dω)) = X(dω) = (∂X)(ω) by step 5; conclude with GeometricCurrentOn.ext. (b) spt ∂Y ⊆ spt Y ⊆ K: if Y vanishes on an open W then so does ∂Y, since tsupport(dω) ⊆ tsupport ω (tsupport_exteriorDerivative_subset) gives ∂Y(ω) = Y(dω) = 0 whenever tsupport ω ⊆ W; hence zeroRegion(Y) ⊆ zeroRegion(∂Y).
8. Lemma A (mass). If Z ∈ D_q(ℝ^P) and spt Z ⊆ K, then M(Z) ≤ M(Z|_U). Proof: let ω be admissible for M(Z) = Z.massOn univ (ω ∈ D^q(ℝ^P) with |ω(x)| ≤ 1 for all x). By (V), Z(ω) = Z(χ•ω) = Z(ι(m_χ ω)) = Z|_U(m_χ ω), and m_χ ω is admissible for M(Z|_U) = (Z|_U).massOn U (tsupport ⊆ tsupport χ ⊆ U, and |χ(x)ω(x)| ≤ 1). So ofReal(Z(ω)) ≤ M(Z|_U) by le_massOn; take the supremum.
   Lemma A for Z := Y (q = m + 1) and step 5 give M(Y) ≤ M(X). Lemma A for Z := ∂Y (q = m; spt ∂Y ⊆ K by 7(b)) and 7(a) give M(∂Y) ≤ M(∂X).
9. Lemma B (integrality). If Z ∈ D_q(ℝ^P), spt Z ⊆ K and Z|_U is integer multiplicity in U, then Z is integer multiplicity in ℝ^P. Proof:
   (B1) spt(Z|_U) ⊆ K. By definition spt(Z|_U) ⊆ U. Let x ∈ U ∖ K. U ∖ K is open, so there is r > 0 with closedBall(x, r) ⊆ U ∖ K, and W := ball(x, r) is open with compact closure contained in U. If ω ∈ D^q(U) and tsupport ω ⊆ W, then tsupport(ιω) ⊆ W is disjoint from K ⊇ spt Z, so Z|_U(ω) = Z(ιω) = 0 (vanish_off_support). So x ∈ zeroRegion(Z|_U) and x ∉ spt(Z|_U).
   (B2) Write Z|_U = τ(M, θ, ξ) with IsRectifiableTriple U q M θ ξ and θ ∈ ℕ on M. By the sibling support_null (with MF; U open), H^q(M ∖ spt(Z|_U)) = 0, hence H^q(M ∖ K) = 0 by (B1). Put M' := M ∩ K. Then M' ⊆ M and H^q(M ∖ M') = 0, so M and M' are H^q-a.e. equal and H^q⌞M = H^q⌞M' (Measure.restrict_congr_set).
   (B3) Blow-ups preserve null sets. For x ∈ ℝ^P, r > 0 and any set E, blowUpMap x r '' E = r⁻¹ • (E − x): translation by −x is an isometry and multiplication by r⁻¹ multiplies H^q by r^{−q} (Isometry.euclideanHausdorffMeasure_image, Measure.euclideanHausdorffMeasure_smul₀). So H^q(blowUpMap x r '' (M ∖ M')) = 0, and since blowUpMap x r '' M' ⊆ blowUpMap x r '' M ⊆ blowUpMap x r '' M' ∪ blowUpMap x r '' (M ∖ M'), the two blown-up sets are H^q-a.e. equal; their restricted measures agree. Hence for every x, every linear subspace L and every f ∈ C_c, the blow-up integrals of (M, θ) and (M', θ) at x coincide for every r > 0, and HasWeightedApproximateTangentSpaceAt q M θ x L holds iff HasWeightedApproximateTangentSpaceAt q M' θ x L holds.
   (B4) (M', θ, ξ) is an integer multiplicity rectifiable triple in ℝ^P (= univ): M' ⊆ univ; M' is null-measurable (M is, K is closed); M' is countably q-rectifiable (subset of M); θ > 0 and θ ∈ ℕ on M'; for every compact K'', M' ∩ K'' ⊆ M ∩ K and θ is integrable on M ∩ K because K is a compact subset of U, so θ is integrable on M' ∩ K''; ξ is a.e.-strongly measurable for H^q⌞M' = H^q⌞M; the orientation condition holds H^q⌞M'-a.e. because it holds H^q⌞M-a.e. for (M, θ) and, by (B3), the same orthonormal τ works for (M', θ).
   (B5) Representation. For ω ∈ D^q(ℝ^P), by (V), Z(ω) = Z(χ•ω) = Z|_U(m_χ ω) = ∫_M θ(x) ξ(x)(χ(x)ω(x)) dH^q = ∫_{M'} θ(x) ξ(x)(χ(x)ω(x)) dH^q (as H^q⌞M = H^q⌞M') = ∫_{M'} θ(x) ξ(x)(ω(x)) dH^q (χ = 1 on K ⊇ M' and ξ(x) is linear; since M' is only null-measurable use setIntegral_congr_fun₀). So Z = τ(M', θ, ξ) on D^q(ℝ^P), and Z is integer multiplicity.
   Lemma B for Z := Y (Y|_U = X): if X is integer multiplicity, so is Y. Lemma B for Z := ∂Y (spt ∂Y ⊆ K and (∂Y)|_U = ∂X by step 7): if ∂X is integer multiplicity, so is ∂Y.
10. Steps 5, 6, 8 and 9 give all the asserted properties of Y. ∎

Remark (adaptable accepted Lean proof; not needed for the argument above). The conclusion of (B3) is the special case V := ℝ^P, M' := M ∩ K, θ' := θ of the comparator-accepted Submission.br_weightedTangent_congr (commit def607d836e2e6071aa1efb85ad37d0ca1d1ac19). Its hypothesis μHE[q](symmDiff M M' ∩ ℝ^P) = μHE[q](M ∖ K) = 0 is (B2). Its Lean proof may be copied under a fresh name.
Further adaptable accepted Lean proof (optional). Step 4(a) is exactly the comparator-accepted Submission.br_la_abs_apply_le_mul_mass (DAG node root.boundary_rectifiability-a1.lattice_approximation-a1.mass_estimate-a1, commit d771ac3ae563701d45563ad2e197624b3f42977f), whose type is: ∀ (P n : ℕ) (U : Set (Eucl P)) (Y : GeometricCurrentOn U n) (ω : TestFormOn U n) (C : ℝ), 0 < C → (∀ x : Eucl P, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) x) ≤ C) → Y.mass ≠ ∞ → |Y ω| ≤ C * Y.mass.toReal. Apply it with Y := X, ω := η and C := c. Its Lean proof may be copied under a fresh name.

## Key steps

1. Smooth cutoff χ ∈ C_c^∞(U), 0 ≤ χ ≤ 1, χ = 1 on an open N ⊇ K; then tsupport((1 − χ)ω) is disjoint from K.
2. Y(ω) := X(χω) is a current on ℝ^P: since M(X) < ∞, |X(η)| ≤ sup|η|·M(X), and ω_j → 0 in D^{m+1}(ℝ^P) forces sup|χω_j| → 0.
3. By vanish_off_support, Y|_U = X and spt Y ⊆ K; also (∂Y)|_U = ∂X and spt ∂Y ⊆ spt Y.
4. Lemma A: spt Z ⊆ K implies M(Z) ≤ M(Z|_U) (test with χω); applied to Y and ∂Y.
5. Lemma B: spt Z ⊆ K and Z|_U = τ(M, θ, ξ) integer multiplicity imply Z = τ(M ∩ K, θ, ξ) integer multiplicity (support_null + null sets preserved by blow-ups); applied to Y and ∂Y.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, Mathlib 25730c7c)`
- `python3 scan of dag.json (235 nodes): no lean_name containing fiw_tb; frozen lean_statement of root.flat_iff_weak-a1.im_mass_formula-a1 (accepted) and im_lincomb-a1 compared textually with the MF/LC premises`
- `git log --all --oneline -S fiw_tb_ (687 refs, no match); grep -rl fiw_tb_ .humanize/math-wiki (no match)`
- `git show <commit>:GMT/Ch06/Submission.lean | grep -c 'theorem Submission.<name>' for the 12 cited accepted declarations (all present), including br_la_abs_apply_le_mul_mass @ d771ac3a and fiw_ims_frame_sign @ c90a4050`
- `grep -n max_nodes /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py; read _decompose, _solve_children, _existing_lean_name_problem; swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json (max_nodes 1000, max_children 12, max_depth 6)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def TestFormOnConverges|structure GeometricCurrentOn|zero_apply|boundary_apply|restrictDomain_apply|def testFormOnInclusion|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|abbrev SimonMultiIndex|def CountablyRectifiable|countablyRectifiable_of_measure_zero|def blowUpMap|def HasWeightedApproximateTangentSpaceAt' in SimonGMT Chapter06/Chapter03`
- `grep Mathlib: theorem exists_nnreal_pos_mul_lt, Finite.exists_infinite_fiber, Infinite.exists_ne_map_eq_of_mapsTo, thickening_subset_of_subset, cthickening_subset_of_subset, thickening_subset_cthickening, mul_le_mul_right`
- `lake build GMT.Ch06.Submission in /tmp/tb5-Hq3Nws (git archive d8d46c9, packages linked)`
- `python3 -I /tmp/tb5_tools/gen_challenges.py (verifier/gmt-compare.py child_modules mode contract + lean_contract.validate_lean_statement); lake env lean Scratch/V4/Ch_*.lean and Scratch/V4/Remaining3.lean (0 errors)`
- `lake env lean Scratch/V4/Assembly.lean and Scratch/V4/FiniteNet.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 2028,2090p book/chapter-06.txt (Simon 7.2 and its proof, (1)–(3))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-br-la-abs-apply-le-mul-mass.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-frame-sign.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-im-mass-formula.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Assembly.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/FiniteNet.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Remaining3.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract (IsIntegerMultiplicity, IsRectifiableTriple, tauAction, latticeFace, latticeFaceAction, IsLatticeChain, DeformationTheorem). Neither the project nor SimonGMT has an integer-multiplicity calculus, a flat-norm lemma or a lattice-chain coefficient bound, so these become the 10 children.

SimonGMT supplies the API used in the child proofs:
- massOn and mass via massAdmissibleOn and covectorEuclideanNorm, and le_massOn / massOn_mono;
- restrictDomain(_apply), testFormOnInclusion, zero_apply, boundary_apply and GeometricCurrentOn.ext;
- zeroRegion and support = U \ zeroRegion;
- SimonMultiIndex = Fin n ↪o Fin p, CountablyRectifiable (with countablyRectifiable_of_measure_zero and .mono), blowUpMap and HasWeightedApproximateTangentSpaceAt.
Mathlib supplies ENNReal.exists_nnreal_pos_mul_lt and the thickening lemmas.

Accepted Submission declarations, cited in the remarks as optional reuse pointers, were checked at their commits. The two new pointers are:
- br_la_abs_apply_le_mul_mass (d771ac3a), the evaluation bound;
- fiw_ims_frame_sign (c90a4050), the frame sign.

Scratch checks:
- all 10 child types elaborate in the comparator's exact challenge scope;
- the parent type follows from MF, LC, fiw_tb_finite_net and fiw_tb_flat_sub;
- fiw_tb_finite_net follows from its five siblings;
- both derivations use only [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
