<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1 -->

## Theorem `Submission.deformation_onto_skeleton`

Deformation onto the n-skeleton (the main step of Simon 5.1, printed displays (6)–(26)), conditional on the Slicing Theorem and on Lemma 3.9. Assume SlicingTheorem and LipschitzPushforwardIntegerMultiplicity. For all m, ℓ ∈ ℕ with ℓ ≥ 1 (n := m + 1, d := n + ℓ) there is C = C(m,ℓ) ∈ [0,∞) such that for every T ∈ D_n(ℝ^d) with M(T) + M(∂T) < ∞ there are Q ∈ D_n(ℝ^d), R ∈ D_{n+1}(ℝ^d), S ∈ D_n(ℝ^d) with: T(ω) − Q(ω) = ∂R(ω) + S(ω) for all ω; spt Q ⊆ L_n := ⋃_F latticeFace 1 F; the tangential property: for every face index F = (z, α), every open ball B with B ∩ L_n ⊆ latticeFace 1 F and every test n-form ω with tsupport ω ⊆ B and ω(x)(e_{α₁},…,e_{α_n}) = 0 for all x, Q(ω) = 0; M(Q) ≤ C M(T), M(∂Q) ≤ C M(∂T), M(R) ≤ C M(T), M(S) ≤ C M(∂T); spt Q ∪ spt R ⊆ {x : dist(x, spt T) ≤ √d} and spt ∂Q ∪ spt S ⊆ {x : dist(x, spt ∂T) ≤ √d} (closed thickenings, Metric.cthickening); if T is integer multiplicity then so are Q and R; if T and ∂T are integer multiplicity then so is S.

Node: `root.deformation-a1.onto_skeleton-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1102, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1103, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1104, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1106, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1111

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/755, https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2732, https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/720, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1069, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1070, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4553, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4561, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4576, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4586

## Lean problem

Declaration: `Submission.deformation_onto_skeleton`

```lean
SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), T.mass + T.boundary.mass < ∞ → ∃ (Q : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)) (R : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 2)) (S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)), (∀ ω, T ω - Q ω = R.boundary ω + S ω) ∧ Q.support ⊆ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F ∧ (∀ (F : LatticeFaceIndex (m + 1) (m + 1 + ℓ)) (y : Eucl (m + 1 + ℓ)) (r : ℝ), ball y r ∩ (⋃ G : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 G) ⊆ latticeFace 1 F → ∀ ω : TestFormOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) ⊆ ball y r → (∀ x, (ω : DifferentialForm (Eucl (m + 1 + ℓ)) (m + 1)) x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ)) = 0) → Q ω = 0) ∧ Q.mass ≤ C * T.mass ∧ Q.boundary.mass ≤ C * T.boundary.mass ∧ R.mass ≤ C * T.mass ∧ S.mass ≤ C * T.boundary.mass ∧ Q.support ∪ R.support ⊆ cthickening (Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ)) T.support ∧ Q.boundary.support ∪ S.support ⊆ cthickening (Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ)) T.boundary.support ∧ (IsIntegerMultiplicity T → IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity R) ∧ (IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → IsIntegerMultiplicity S)
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

- Parent DAG node: `root.deformation-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, §5, printed “Proof of the Deformation Theorem”, displays (6)–(26) (pp. 164–167): the choice of the centre a, the truncations (8)–(9), the good radii (10), the estimates (11)–(18), the limits (19)–(21), the supports and masses (22)–(25), and the first part of the discussion of (26) (the deformed current is tangential to the open n-faces); together with the tools it cites, products with [[(0,1)]] (2.17–2.21), push-forward and homotopy formula (2.23–2.29), 3.2(2), 3.9, 3.13, 4.5 and 4.10. This is the material of A2, A4(a),(d) and C2–C7 of the parent proof, copied below; the steps that the parent proof performs with Lemma 5.4, with the choice of a (C1–C2) and with the representation/restriction facts A1 are cited from the sibling theorems deformation_retraction, deformation_good_center and deformation_mass_restriction, the completeness lemma 3.13 (A4(f)) from the sibling theorem deformation_im_completeness, and the consistency step A3 (integrality of Lipschitz push-forwards of integer multiplicity currents) from the sibling theorem deformation_im_pushforward_limit (statements quoted in Part 0). Errata applied (as in the parent): book k = ℓ; (iii) the sign in (20) is corrected (homotopy formula 2.25 with f = id, g = ψ gives X − ψ_#X = −∂h_#([[(0,1)]]×X) − h_#([[(0,1)]]×∂X)), and the signs of R₁, S₁ are chosen accordingly; (iv) the printed bounds “≤ cM(T)” in (11)–(16) are replaced by the sharper bounds actually computed; (v) in (23) “<” is replaced by “≤” (this statement asserts the closed thickening of radius √d); (vii) the printed estimates (11)–(18), applied in the book to T_ρ − T_{ρ/2}, are stated for differences between consecutive good radii σ_ν, at which the slices of T and of ∂T have finite mass, and (17)–(18) are obtained by telescoping.

Part 0 — setting and the results used.
Setting. n := m + 1 ≥ 1, ℓ ≥ 1, d := n + ℓ, ℝ^d = Eucl(m+1+ℓ), all currents in U = ℝ^d (univ); C = [0,1]^d; L_n := ⋃_F latticeFace 1 F (F ∈ LatticeFaceIndex (m+1) (m+1+ℓ)), the n-skeleton (a point lies in L_n iff at least ℓ of its coordinates are integers); for a face F = (z, α), e_α := (e_{α₁},…,e_{α_n}) and Π_F := {x : x_i = z_i for i ∉ range α} ⊇ latticeFace 1 F. M = mass, spt = support, D_k = GeometricCurrentOn univ k, H^k = μHE[k]. Assume the two premises of the statement, SlicingTheorem and LipschitzPushforwardIntegerMultiplicity (see (Sl), (Lp) below), and fix m, ℓ with ℓ ≥ 1; the constant C produced below depends only on (m, ℓ), and then T ∈ D_n(ℝ^d) is arbitrary with M(T) + M(∂T) < ∞.

Conventions (stated here so that this proof is self-contained). For an ambient dimension D, e₁,…,e_D is the standard basis of ℝ^D, I(k,D) the set of strictly increasing multi-indices γ = (γ₁ < ⋯ < γ_k) in {1,…,D}, e_γ := (e_{γ₁},…,e_{γ_k}) and dx^γ := dx^{γ₁}∧⋯∧dx^{γ_k}. For a k-covector α (`Covector (Eucl D) k`), |α| := (Σ_γ α(e_γ)²)^{1/2} (`covectorEuclideanNorm`); for a k-form ω, ‖ω‖ := sup_x |ω(x)|; for a k-vector w (`NVector (Eucl D) k`, a linear functional on k-covectors), ⟨α, w⟩ := w(α), w^γ := w(dx^γ) and |w| := (Σ_γ (w^γ)²)^{1/2}; ‖A‖ is the operator norm of a linear map A. Coordinate fact: every k-covector satisfies α = Σ_γ α(e_γ)dx^γ (an alternating k-linear map is determined by its values on increasing tuples of basis vectors, and dx^γ(e_δ) = δ_{γδ}); hence w(α) = Σ_γ α(e_γ)w^γ and |w(α)| ≤ |α|·|w| (Cauchy–Schwarz). Push-forward of k-vectors: for a linear map A : ℝ^D → ℝ^{D′}, A_# = Λ_kA := `nVectorPushforward k A` is characterized by ⟨α, A_#w⟩ = ⟨A^#α, w⟩ with A^#α := α(A·,…,A·) (Simon 1.8–1.9); it is linear and A_#(simpleNVector τ) = simpleNVector(Aτ₁,…,Aτ_k) (Simon 1.10; SimonGMT `nVectorPushforward_simple`). Unit fact: if τ₁,…,τ_k ∈ ℝ^D are orthonormal then |simpleNVector τ| = 1, because its coordinates (simpleNVector τ)^γ = det(τ_i·e_{γ_j}) are the k×k minors of the D×k matrix with columns τ₁,…,τ_k and, by the Cauchy–Binet formula, Σ_γ det(τ_i·e_{γ_j})² = det(τ_i·τ_j) = 1; consequently, whenever `IsRectifiableTriple U k M θ ξ` holds, |ξ| = 1 H^k-a.e. on M (orientation clause). Mass M = `mass`, spt = `support`.

Results used.
 (S1) deformation_retraction (sibling): there is c_A = c_A(m,ℓ) such that for every a with Σ_i(a_i − 1/2)² < 1/16 and La := L_{ℓ−1}(a) := {y : ∃ J, |J| = n + 1, y_i − a_i ∈ ℤ ∀ i ∈ J} there is ψ : ℝ^d → ℝ^d with (i) ψ(x) ∈ L_n for x ∉ La, (ii) ψ(x) ∈ z + C whenever x ∈ (z + C) ∖ La, z ∈ ℤ^d, (iii) ψ is (c_A/σ)-Lipschitz on {d_a ≥ σ} for 0 < σ ≤ 1/4, where d_a := dist(·, La).
 (S2) deformation_good_center (sibling): there is c_B = c_B(m,ℓ) such that for any two finite Borel measures μ₁, μ₂ on ℝ^d there is a with Σ_i(a_i − 1/2)² < 1/16 and μ_i({d_a < σ}) ≤ c_Bσ^{n+1}μ_i(ℝ^d) for i = 1,2 and σ ∈ (0,1/4).
 (S3) deformation_mass_restriction (sibling): for every X ∈ D_k(ℝ^N) with M(X) < ∞ there are a finite Borel measure μ_X and a k-vector field v_X with IsMeasureRepresentation X μ_X v_X, μ_X(ℝ^N ∖ spt X) = 0, uniqueness of the representing vector measure on bounded Borel sets, and for every Borel A a current X⌞A with IsRestriction X A (X⌞A), (X⌞A)(ω) = ∫_A v_X(ω)dμ_X, M_W(X⌞A) = μ_X(W ∩ A) for open W, uniqueness among all Y′ with IsRestriction X A Y′, and X⌞A integer multiplicity if X is. Consequences used below: (a) X⌞ℝ^N = X (uniqueness, since IsRestriction X univ X holds with the representation (μ_X, v_X)), so μ_X(W) = M_W(X) for open W and μ_X(ℝ^N) = M(X); (b) X⌞A + X⌞(ℝ^N ∖ A) = X and, for disjoint Borel A, B, X⌞(A ∪ B) = X⌞A + X⌞B (additivity of the integral); (c) spt(X⌞A) ⊆ spt X ∩ closure(A): an open W disjoint from spt X ∩ closure(A) has M_W(X⌞A) = μ_X(W ∩ A) = 0 because μ_X(W ∩ A) ≤ μ_X(ℝ^N ∖ spt X) = 0, and a current Y with M_W(Y) = 0 vanishes on W (|Y(ω)| ≤ M_W(Y)‖ω‖); (d) M(X⌞A) = μ_X(A) ≤ M(X); (e) a current with M_W(Y) = 0 for an open W vanishes on W; in particular a test form supported in the complement of spt X is annihilated by X (cover its support by finitely many relatively compact open sets of the zero region and use a partition of unity).
 (S4) deformation_im_completeness (sibling): if T′, T′_j ∈ D_k(ℝ^N), every T′_j is integer multiplicity and for every ε > 0 there is J such that M(D) < ε for all j ≥ J and all currents D with D(ω) = T′(ω) − T′_j(ω) ∀ω, then T′ is integer multiplicity (Simon 3.13).
 (Sl) SlicingTheorem — the first premise of the statement (it is the headline theorem of the node root.slicing-a1): for T′ ∈ D_{k+1}(U) with locally finite mass and boundary mass and f L-Lipschitz on U there are slices S_t with IsSlice T′ f t S_t for every t, spt S_t ⊆ spt T′ ∩ {f = t}, S_t integer multiplicity for a.e. t if T′ is, and, for open W ⊆ U, L_W ≥ ess sup_W|Df|, a < b and R = T′⌞{a < f < b}, a measurable g with M_W(S_t) ≤ g(t) on (a,b) and ∫_a^b g ≤ L_W M_W(R).
 (S5) deformation_im_pushforward_limit (sibling; its premise is LipschitzPushforwardIntegerMultiplicity): for X ∈ D_k(ℝ^D) with X = τ(M,θ,ξ) (IsRectifiableTriple univ k M θ ξ, θ natural-valued on M) and g : ℝ^D → ℝ^{D′} Λ-Lipschitz with g⁻¹(K) ∩ spt X compact for compact K, there is an integer multiplicity S ∈ D_k(ℝ^{D′}) with IsLipschitzPushforward X g S such that, for every sequence (g_j) of C¹ maps with a common Lipschitz bound and g_j → g uniformly, and every test form ω, ∫_Mθ(x)·nVectorPushforward k (Dg_j(x)) (ξ(x)) (ω(g_j(x))) dH^k → S(ω).
 (Lp) LipschitzPushforwardIntegerMultiplicity — the second premise of the statement (the headline theorem of the node root.lipschitz_pushforward_im-a1); it is used only to discharge the premise of (S5).

Part I — tools (A2 and A4(a),(d) of the parent proof, copied; “A1” there refers to the facts (S3)(a)–(e) above; A3 is replaced by I.7 below, which uses (S5)).

A2 (Products and push-forwards; 2.17–2.29). (a) For X ∈ D_k(ℝ^d) of locally finite mass, [[(0,1)]]×X ∈ D_{k+1}(ℝ × ℝ^d) is represented by e₁∧X⃗ and L¹⌞(0,1) × μ_X; ∂([[(0,1)]]×X) = {1}×X − {0}×X − [[(0,1)]]×∂X (2.19, 2.21, 2.22). (b) For C¹ (resp. smooth) f with f|spt X proper, f_#X(ω) := X(ζ f^#ω) (2.23, ζ ∈ C_c^∞ equal to 1 near spt X ∩ spt f^#ω), ∂f_# = f_#∂, and f_#X(ω) = ∫⟨ω(f(x)), Df(x)_#X⃗(x)⟩dμ_X (2.24(2)); hence M_W(f_#X) ≤ sup_{f⁻¹(W)∩spt X}‖Df‖^k·M_{f⁻¹(W)}(X), using |Λ_kA w| ≤ ‖A‖^k|w| (the singular values of Λ_kA are products of k singular values of A). (c) Homotopy formula (2.25): if h(0,·) = f, h(1,·) = g and h|[0,1]×spt X is proper, then g_#X − f_#X = ∂h_#([[(0,1)]]×X) + h_#([[(0,1)]]×∂X). (d) Affine homotopy estimate (2.27): for h(t,x) = f(x) + t(g(x) − f(x)), M_W(h_#([[(0,1)]]×X)) ≤ sup_{spt X∩W_h}|f−g|·sup_{spt X∩W_h}(‖Df‖+‖Dg‖)^k·M_{W_h}(X), W_h := pr(h⁻¹(W)). (e) Lemma 2.28–2.29: if M_W(X), M_W(∂X) < ∞ for all W and f is Lipschitz with f|spt X proper, then f_#X(ω) := lim_{ε↓0}(f_ε)_#X(ω) exists (f_ε = ϕ_ε*f mollified; by (c),(d) |(f_ε)_#X(ω) − (f_{ε′})_#X(ω)| ≤ C sup_{f⁻¹(K)∩spt X}|f_ε − f_{ε′}|(Lip f)^k (‖dω‖ + ‖ω‖)·(M(X)+M(∂X)) locally), spt f_#X ⊆ closure f(spt X), M_W(f_#X) ≤ (ess sup_{f⁻¹(W)}‖Df‖)^k M_{f⁻¹(W)}(X), ∂f_# = f_#∂, f_#X depends only on f on a neighbourhood of spt X — indeed only on f|spt X: if f = g on spt X then f_#X = g_#X (2.28: by the homotopy formula and 2.27 applied to the mollified maps, |(f_ε)_#X(ω) − (g_ε)_#X(ω)| ≤ c·sup_{spt X ∩ K′}|f_ε − g_ε|·(Lip f + Lip g)^k·(M(X)‖dω‖ + M(∂X)‖ω‖) for a compact K′ depending on ω, and the right side tends to c·sup_{spt X ∩ K′}|f − g|·(…) = 0 as ε ↓ 0) — and (c),(d) remain valid for Lipschitz maps (pass to the limit ε ↓ 0). A locally Lipschitz map defined on an open set containing a neighbourhood of spt X on which it is Lipschitz is used through any Lipschitz extension (componentwise McShane, `LipschitzOnWith.extend_real`); the result does not depend on the extension. For k = 0 (X a signed Radon measure) f_#X(φ) := X(φ∘f) for continuous f with f|spt X proper; no boundary condition is needed.

A4 (integer multiplicity calculus used here; Simon 3.2(2), 3.13). (a) 0 is integer multiplicity (M = ∅). (d) Products (3.2(2)): if X = τ(M,θ,ξ) ∈ D_k(ℝ^D) is integer multiplicity (IsRectifiableTriple univ k M θ ξ, θ natural-valued on M), then [[(0,1)]]×X = τ((0,1)×M, θ∘pr, e₀∧(ξ∘pr)) in ℝ×ℝ^D ≅ Eucl(1+D), where pr(t,x) := x, e₀ is the unit vector of the ℝ-factor and e₀∧w denotes the (k+1)-vector α ↦ w(α(e₀, ·)). Proof: by A2(a) (2.17–2.20), ([[(0,1)]]×X)(φ) = ∫_0^1 X(φ^{(t)})dt, where φ^{(t)} := φ(t,·)(e₀, ·) is the dt-coefficient form of φ (a test k-form on ℝ^D); hence ([[(0,1)]]×X)(φ) = ∫_0^1∫_Mθ(x)⟨φ(t,x), e₀∧ξ(x)⟩dH^k(x)dt. For the H^k-measurable countably k-rectifiable M with H^k⌞M locally finite, H^{k+1}⌞((0,1)×M) = L¹⌞(0,1) × H^k⌞M: on each piece M_j ⊆ N_j (embedded C¹ k-submanifolds, Simon Ch. 3, Remark 1.3) this is the area formula for the C¹ product manifold (0,1)×N_j (the Jacobian of a product chart is the product of the Jacobians), and the exceptional set (0,1)×M₀ is H^{k+1}-null because H^{k+1}(I × A) ≤ c·L¹(I)·H^k(A) (Federer 2.10.45). So ([[(0,1)]]×X)(φ) = ∫_{(0,1)×M}(θ∘pr)⟨φ, e₀∧(ξ∘pr)⟩dH^{k+1}. Triple conditions: (0,1)×M is H^{k+1}-null-measurable and countably (k+1)-rectifiable ((0,1)×F_j(ℝ^k) is the image of the Lipschitz map (s,u) ↦ (s, F_j(u)) of ℝ^{k+1}, and (0,1)×M₀ is null); θ∘pr is natural-valued and positive on (0,1)×M and integrable on compact sets (Fubini); e₀∧(ξ∘pr) is measurable; at (t,x) with t ∈ (0,1) and x a point where ξ(x) = ±simpleNVector τ with τ orthonormal and HasWeightedApproximateTangentSpaceAt k M θ x (span τ), the blow-up of (0,1)×M at (t,x) with ratio r is (−t/r, (1−t)/r) × η_{x,r}(M) with weight θ(x + r·), so by Fubini, dominated convergence in the ℝ-variable (the inner integrals are bounded uniformly for small r, by testing with a continuous function ≥ 1 on a ball) and the hypothesis at x, ((0,1)×M, θ∘pr) has weighted approximate tangent space ℝe₀ ⊕ span τ = span(e₀, τ) at (t,x), (e₀, τ) is orthonormal, and e₀∧ξ(x) = ±simpleNVector(e₀, τ). The exceptional set (0,1)×(null set) is H^{k+1}-null. (f) Completeness (3.13): this is the sibling theorem (S4) of Part 0.

I.5 (M-limits; printed (19)). If (Y_j) are currents in D_k(ℝ^D) with M(Y_j) < ∞ and M(Y_i − Y_j) → 0 as i, j → ∞ (Y_i − Y_j denoting the difference current), then there is Y ∈ D_k(ℝ^D) with M(Y − Y_j) → 0. Indeed |Y_i(ω) − Y_j(ω)| ≤ M(Y_i − Y_j)‖ω‖, so Y(ω) := lim Y_j(ω) exists, is linear, satisfies |Y(ω)| ≤ (sup_j M(Y_j))‖ω‖ (hence is sequentially continuous: ω_i → 0 in the test-form topology implies ‖ω_i‖ → 0), and by lower semicontinuity of mass under weak convergence (2.14) M(Y − Y_j) ≤ liminf_i M(Y_i − Y_j) → 0. Then M(Y) = lim M(Y_j), Y(ω) = lim Y_j(ω) for every ω, and ∂Y_j ⇀ ∂Y. If all Y_j vanish on an open set W, so does Y; hence spt Y_j ⊆ E for all j with E closed implies spt Y ⊆ E. If all Y_j are integer multiplicity, so is Y, by (S4) (for ε > 0 choose J with M(Y − Y_j) < ε for j ≥ J; every D with D(ω) = Y(ω) − Y_j(ω) ∀ω equals the current Y − Y_j).

I.6 (the maps ψ and h on a region {d_a ≥ σ}). Let a and ψ be as in (S1), 0 < σ ≤ 1/8. By (S1)(iii) (with σ/2 ≤ 1/4), ψ is (2c_A/σ)-Lipschitz on the closed set {d_a ≥ σ/2}; extending each coordinate by McShane's formula gives ψ̄_σ : ℝ^d → ℝ^d, Lipschitz with constant Λ_σ := 2√d·c_A/σ, equal to ψ on {d_a ≥ σ/2}, which is a neighbourhood ({d_a > σ/2} is open) of {d_a ≥ σ}. By (S1)(ii), |ψ(x) − x| ≤ diam C = √d for x ∉ La; hence ψ̄_σ|_E is proper for every closed E ⊆ {d_a ≥ σ} (preimages of bounded sets are bounded). Put h_σ(t, x) := x + t(ψ(x) − x) for (t, x) ∈ [0,1] × {d_a ≥ σ/2}; there |ψ(x) − x| ≤ √d, so h_σ is Lipschitz with constant ≤ 1 + 2c_A/σ + √d, and h_σ(t, x) ∈ z + C for x ∈ (z + C) ∩ {d_a ≥ σ/2}, t ∈ [0,1] (convexity). Let h̄_σ : ℝ × ℝ^d ≅ Eucl(1+d) → ℝ^d (coordinate isometry) be a componentwise McShane extension of h_σ, Lipschitz with constant ≤ √d(1 + 2c_A/σ + √d); h̄_σ is proper on [0,1] × E for closed E ⊆ {d_a ≥ σ}. For a current X of finite mass and finite boundary mass (no boundary condition in degree 0) with spt X ⊆ {d_a ≥ σ}, define ψ_#X := (ψ̄_σ)_#X and h_#([[(0,1)]]×X) := (h̄_σ)_#([[(0,1)]]×X) in the sense of A2(e). Since ψ̄_σ, ψ̄_{σ′} agree on {d_a ≥ max(σ,σ′)/2} ⊇ spt X and h̄_σ, h̄_{σ′} agree on [0,1] × {d_a ≥ max(σ,σ′)/2} ⊇ [0,1] × spt X = spt([[(0,1)]]×X), the support clause of A2(e) (2.28) shows that ψ_#X and h_#([[(0,1)]]×X) do not depend on σ; for a fixed σ they are linear in X. By A2 they satisfy: ∂ψ_#X = ψ_#∂X; spt ψ_#X ⊆ closure ψ(spt X); M(ψ_#X) ≤ Λ_σ^kM(X) (k = deg X); the homotopy formula ψ_#X − X = ∂h_#([[(0,1)]]×X) + h_#([[(0,1)]]×∂X) (A2(c) with f = id, g = ψ̄_σ); M(h_#([[(0,1)]]×X)) ≤ √d(1 + Λ_σ)^kM(X) (h̄_σ coincides with the affine homotopy H(t,x) := x + t(ψ̄_σ(x) − x) on [0,1] × {d_a ≥ σ/2} ⊇ [0,1] × spt X = spt([[(0,1)]]×X), so by the support clause of A2(e) (2.28), (h̄_σ)_#([[(0,1)]]×X) = H_#([[(0,1)]]×X) — H being Lipschitz on the neighbourhood (−1,2) × ℝ^d of the support, because ψ̄_σ − id is Lipschitz and bounded (it is ≤ √d on {d_a ≥ σ/2}, which contains L_n ⊇ ℤ^d since dist(La, L_n) > 1/4 ≥ σ/2, and every point of ℝ^d is within √d of ℤ^d) — and A2(d) applies to H: |ψ̄_σ − id| ≤ √d on spt X and ‖D id‖ + ‖Dψ̄_σ‖ ≤ 1 + Λ_σ a.e.); spt h_#([[(0,1)]]×X) ⊆ closure h̄_σ([0,1] × spt X).

I.7 (integrality of push-forwards; replaces A3). Let X ∈ D_k(ℝ^D) be integer multiplicity, X = τ(M,θ,ξ), with locally finite boundary mass if k ≥ 1, and let g : ℝ^D → ℝ^{D′} be Λ-Lipschitz with g|spt X proper. Then the push-forward g_#X of A2(e) is integer multiplicity. Proof: let g_ε := ϕ_ε * g (C^∞, Λ-Lipschitz, |g_ε − g| ≤ Λε; g_ε|spt X is proper because g_ε⁻¹(K₁) ∩ spt X ⊆ g⁻¹({dist(·, K₁) ≤ Λε}) ∩ spt X). For k ≥ 1, by A2(e), g_#X(ω) = lim_{ε↓0}(g_ε)_#X(ω), and by A2(b), using that (H^k⌞M, θξ) represents X (unit fact; X(φ) = ∫_Mθ⟨φ, ξ⟩dH^k), (g_ε)_#X(ω) = X(ζg_ε^#ω) = ∫_Mθζ⟨g_ε^#ω, ξ⟩dH^k = ∫_Mθ⟨ω(g_ε(x)), Dg_ε(x)_#ξ(x)⟩dH^k(x), where ζ ∈ C_c^∞ equals 1 near spt X ∩ spt g_ε^#ω and we used the duality ⟨Dg_ε(x)^#α, w⟩ = ⟨α, Dg_ε(x)_#w⟩ (Simon 1.9) and H^k(M ∖ spt X) = 0 [X(φ) = 0 for test forms φ supported in the open set ℝ^D ∖ spt X (partition of unity over the zero region), so the vector measure θξH^k⌞M vanishes on Borel subsets of ℝ^D ∖ spt X (finite signed measures on a ball agreeing on C_c^∞ agree on Borel sets: mollification, monotone limits, Dynkin's π–λ theorem), hence θξ = 0 a.e. there, and |ξ| = 1 a.e., θ > 0 on M]. By (S5) (its premise is the premise (Lp) of the statement), applied to X, (M,θ,ξ), g, Λ, and the sequence g_{ε_j} for any ε_j ↓ 0 (C^∞ ⊆ C¹, Λ-Lipschitz, uniformly convergent to g), these integrals converge to S(ω) for an integer multiplicity S; hence g_#X = S is integer multiplicity. For k = 0, A2(e) defines g_#X(φ) := X(φ∘g) = ∫_Mθξ(φ(g(x)))dH^0, which is the limit of the same integrals with the g_{ε_j} (dominated convergence), so again g_#X = S.

Part II — the deformation onto the skeleton.

1. Mass measures and the centre a (printed (6), (7); parent C1–C2). Apply (S3) to T and to ∂T (finite masses): μ_T := μ_X for X = T, μ_∂ := μ_X for X = ∂T (finite Borel measures with μ_T(ℝ^d) = M(T), μ_∂(ℝ^d) = M(∂T)). Apply (S2) to μ₁ := μ_T, μ₂ := μ_∂: there is a with Σ_i(a_i − 1/2)² < 1/16 such that, writing La := L_{ℓ−1}(a), d_a := dist(·, La) and L_{ℓ−1}(a;σ) := {d_a < σ} (open),
 (6)–(7) μ_T(L_{ℓ−1}(a;σ)) ≤ c_Bσ^{n+1}M(T), μ_∂(L_{ℓ−1}(a;σ)) ≤ c_Bσ^{n+1}M(∂T) for σ ∈ (0,1/4).
 Let ψ be given by (S1) for this a. d_a is 1-Lipschitz, so its distributional gradient satisfies |Dd_a| ≤ 1 a.e.

2. Truncations and slices (printed (8)–(10); parent C3). For σ > 0 let T_σ := T⌞L_{ℓ−1}(a;σ) and (∂T)_σ := (∂T)⌞L_{ℓ−1}(a;σ) ((S3)); by (S3)(d) and (6)–(7):
 (9) M(T_σ) = μ_T({d_a < σ}) ≤ c_Bσ^{n+1}M(T), M((∂T)_σ) ≤ c_Bσ^{n+1}M(∂T) for σ ∈ (0,1/4).
 Apply (Sl) to T (degree n = m + 1, U = ℝ^d, f = d_a, L = 1, W = ℝ^d, L_W = 1): it gives S_t with IsSlice T d_a t S_t, spt S_t ⊆ spt T ∩ {d_a = t}, S_t integer multiplicity for a.e. t if T is, and for every interval (a′, b′) a measurable g with M(S_t) ≤ g(t) on (a′,b′) and ∫_{a′}^{b′}g ≤ M(T⌞{a′ < d_a < b′}). By the uniqueness in (S3), the restrictions in IsSlice are T_t and (∂T)_t, so S_t = ∂T_t − (∂T)_t (4.6), i.e. ∂T_t = (∂T)_t + S_t. If n ≥ 2, apply (Sl) also to ∂T (degree n − 1 = (m − 1) + 1 ≥ 1, finite mass, ∂∂T = 0): slices S′_t = ∂((∂T)_t) (the restriction of ∂∂T = 0 is 0), with a majorant g′ satisfying ∫_{a′}^{b′}g′ ≤ M(∂T) < ∞ on bounded intervals, so M(S′_t) < ∞ for a.e. t; and ∂S_t = ∂∂T_t − ∂(∂T)_t = −S′_t. If n = 1, ∂T and the S_t are 0-currents (finite signed measures) and no boundary condition is needed in A2(e).
 Good radii. For ν ≥ 3 choose σ_ν ∈ (2^{−ν−1}, 2^{−ν}) such that
 (10) M(S_{σ_ν}) ≤ 2^{ν+3}M(T⌞{2^{−ν−1} < d_a < 2^{−ν}}) ≤ 2^{ν+3}c_B2^{−ν(n+1)}M(T) = 8c_B2^{−νn}M(T),
 S_{σ_ν} is integer multiplicity if T is, and (if n ≥ 2) M(S′_{σ_ν}) < ∞. This is possible: with g the majorant on (2^{−ν−1}, 2^{−ν}) (an interval of length 2^{−ν−1}), Chebyshev's inequality shows that the set of t where g(t) > 4·2^{ν+1}∫g has measure < 1/4 of the interval, while the other two conditions fail only on null sets. Then σ_{ν+1} < 2^{−ν−1} < σ_ν, σ_ν ↓ 0 and σ₃ > 1/16.
 Pieces. With (S3) put X_ν := T⌞{d_a ≥ σ_ν}, Z′_ν := (∂T)⌞{d_a ≥ σ_ν}, Y_ν := T⌞{σ_{ν+1} ≤ d_a < σ_ν}, Z_ν := (∂T)⌞{σ_{ν+1} ≤ d_a < σ_ν}. By (S3)(b): X_ν = T − T_{σ_ν}, Z′_ν = ∂T − (∂T)_{σ_ν}, X_{ν+1} = X_ν + Y_ν, Z′_{ν+1} = Z′_ν + Z_ν; so X_ν = X₃ + Σ_{3≤μ<ν}Y_μ and Z′_ν = Z′₃ + Σ_{3≤μ<ν}Z_μ. Boundaries: ∂X_ν = ∂T − ∂T_{σ_ν} = Z′_ν − S_{σ_ν}; if n ≥ 2, ∂Z′_ν = −∂((∂T)_{σ_ν}) = −S′_{σ_ν}, ∂Y_ν = ∂X_{ν+1} − ∂X_ν = Z_ν + S_{σ_ν} − S_{σ_{ν+1}}, ∂Z_ν = S′_{σ_ν} − S′_{σ_{ν+1}}, ∂S_{σ_ν} = −S′_{σ_ν}: all the currents to which ψ_#, h_# are applied below have finite mass and finite boundary mass (or are 0-currents). Masses and supports ((S3)(c),(d), (9)): M(X_ν) ≤ M(T), M(Z′_ν) ≤ M(∂T), M(Y_ν) ≤ μ_T({d_a < σ_ν}) ≤ c_B2^{−ν(n+1)}M(T), M(Z_ν) ≤ c_B2^{−ν(n+1)}M(∂T); spt X_ν ⊆ spt T ∩ {d_a ≥ σ_ν}, spt Z′_ν ⊆ spt ∂T ∩ {d_a ≥ σ_ν}, spt Y_ν ⊆ spt T ∩ {d_a ≥ σ_{ν+1}} ⊆ {d_a ≥ 2^{−ν−2}}, spt Z_ν ⊆ spt ∂T ∩ {d_a ≥ 2^{−ν−2}}, spt S_{σ_ν} ⊆ spt T ∩ {d_a = σ_ν}. All of these supports lie in {d_a ≥ σ_ν′} for ν′ ≥ ν + 1, so ψ_#, h_# (I.6) are defined on them and linear on the span of X₃, Y₃, …, Y_{ν′−1}, Z′₃, Z₃, …, S_{σ_ν}.

3. Estimates (printed (11)–(18), corrected per (iv), (vii); parent C4). By I.6 with σ := σ_{ν+1} ≥ 2^{−ν−2} (so Λ_σ ≤ c₂2^ν with c₂ := 8√d·c_A) and the bounds of Step 2, with constants c depending only on (m, ℓ):
 (11) M(ψ_#Y_ν) ≤ (c₂2^ν)^nc_B2^{−ν(n+1)}M(T) ≤ c2^{−ν}M(T); (12) M(ψ_#Z_ν) ≤ (c₂2^ν)^{n−1}c_B2^{−ν(n+1)}M(∂T) ≤ c2^{−2ν}M(∂T);
 (13) M(h_#([[(0,1)]]×Y_ν)) ≤ √d(1 + c₂2^ν)^nc_B2^{−ν(n+1)}M(T) ≤ c2^{−ν}M(T); (14) M(h_#([[(0,1)]]×Z_ν)) ≤ √d(1 + c₂2^ν)^{n−1}c_B2^{−ν(n+1)}M(∂T) ≤ c2^{−2ν}M(∂T);
 (15) M(ψ_#S_{σ_ν}) ≤ (c₂2^ν)^{n−1}·8c_B2^{−νn}M(T) ≤ c2^{−ν}M(T); (16) M(h_#([[(0,1)]]×S_{σ_ν})) ≤ √d(1 + c₂2^ν)^{n−1}·8c_B2^{−νn}M(T) ≤ c2^{−ν}M(T).
 Initial pieces (supports in {d_a ≥ σ₃}, σ₃ > 1/16, Λ ≤ 32√d·c_A): M(ψ_#X₃) + M(h_#([[(0,1)]]×X₃)) ≤ cM(T) and M(ψ_#Z′₃) + M(h_#([[(0,1)]]×Z′₃)) ≤ cM(∂T). By linearity and the decompositions of Step 2, (11)–(14) give the telescoped bounds
 (17)–(18) M(ψ_#X_ν) + M(h_#([[(0,1)]]×X_ν)) ≤ cM(T), M(ψ_#Z′_ν) + M(h_#([[(0,1)]]×Z′_ν)) ≤ cM(∂T), with c independent of ν.

4. Limits and the homotopy identity (printed (19)–(21) with the corrected sign (iii); parent C5). By linearity, ψ_#X_{ν+1} − ψ_#X_ν = ψ_#Y_ν, h_#([[(0,1)]]×X_{ν+1}) − h_#([[(0,1)]]×X_ν) = h_#([[(0,1)]]×Y_ν), and similarly for Z′_ν with Z_ν; by (11)–(14) these four sequences are M-Cauchy, while M(S_{σ_ν}) + M(ψ_#S_{σ_ν}) + M(h_#([[(0,1)]]×S_{σ_ν})) → 0 by (10), (15), (16), and M(T − X_ν) = M(T_{σ_ν}) → 0 by (9). By I.5 define
 (19) Q := M-lim ψ_#X_ν, R₁ := −M-lim h_#([[(0,1)]]×X_ν), S₁ := −M-lim h_#([[(0,1)]]×Z′_ν).
 By the homotopy formula of I.6 and ∂X_ν = Z′_ν − S_{σ_ν} (with linearity of h_#):
 (20) X_ν − ψ_#X_ν = −∂h_#([[(0,1)]]×X_ν) − h_#([[(0,1)]]×Z′_ν) + h_#([[(0,1)]]×S_{σ_ν}).
 Letting ν → ∞ and evaluating on a fixed test form ω (all terms converge in mass, hence on ω; ∂ is weakly continuous): (21) T(ω) − Q(ω) = ∂R₁(ω) + S₁(ω) for every test form ω.

5. Integrality (printed remark after (21); parent C5). Suppose T is integer multiplicity. Then X_ν = T⌞{d_a ≥ σ_ν} is integer multiplicity ((S3)), with ∂X_ν of finite mass, so ψ_#X_ν = (ψ̄_{σ_ν})_#X_ν is integer multiplicity by I.7 (ψ̄_{σ_ν} is Lipschitz and proper on spt X_ν); [[(0,1)]]×X_ν is integer multiplicity by A4(d), with boundary {1}×X_ν − {0}×X_ν − [[(0,1)]]×∂X_ν of finite mass, so h_#([[(0,1)]]×X_ν) is integer multiplicity by I.7 applied to h̄_{σ_ν} on Eucl(1+d) (the coordinate isometry ℝ×ℝ^d ≅ Eucl(1+d) transports currents, masses and integer multiplicity). By I.5 (i.e. (S4)), Q and −R₁ are integer multiplicity, hence so is R₁ (if −R₁ = τ(M,θ,ξ) then R₁ = τ(M,θ,−ξ), and −ξ satisfies the orientation clause with the same frames and the opposite sign). If moreover ∂T is integer multiplicity, Z′_ν = (∂T)⌞{d_a ≥ σ_ν} is integer multiplicity ((S3)) with finite boundary mass M(S′_{σ_ν}) < ∞ (for n = 1 no boundary condition is needed), so as above h_#([[(0,1)]]×Z′_ν) is integer multiplicity and so is S₁.

6. Supports and masses (printed (22)–(25), with (v); parent C6). By (S1)(i), ψ maps ℝ^d ∖ La into the closed set L_n, so by I.6 spt ψ_#X_ν ⊆ closure ψ(spt X_ν) ⊆ L_n and, by I.5, (22) spt Q ⊆ L_n. By (S1)(ii), for x ∈ spt X_ν ⊆ spt T ∩ {d_a ≥ σ_ν} we have |ψ(x) − x| ≤ √d and |h̄(t,x) − x| ≤ √d for t ∈ [0,1] (convexity of z + C); hence spt ψ_#X_ν and spt h_#([[(0,1)]]×X_ν) lie in the closed set cthickening √d (spt T), and spt h_#([[(0,1)]]×Z′_ν) ⊆ cthickening √d (spt ∂T). By I.5:
 (23) spt Q ∪ spt R₁ ⊆ cthickening √d (spt T), spt S₁ ⊆ cthickening √d (spt ∂T).
 Moreover ∂ψ_#X_ν = ψ_#∂X_ν = ψ_#Z′_ν − ψ_#S_{σ_ν} ⇀ ∂Q, spt ψ_#Z′_ν ⊆ cthickening √d (spt ∂T) and M(ψ_#S_{σ_ν}) → 0; so for every test form ω supported in the open complement of cthickening √d (spt ∂T), ∂Q(ω) = lim(0 − ψ_#S_{σ_ν}(ω)) = 0, i.e. spt ∂Q ⊆ cthickening √d (spt ∂T). By (17)–(19) (mass is continuous under M-convergence):
 (24) M(Q) ≤ cM(T), M(R₁) ≤ cM(T), M(S₁) ≤ cM(∂T);
 and by lower semicontinuity of mass (2.14),
 (25) M(∂Q) ≤ liminf M(ψ_#∂X_ν) ≤ liminf[M(ψ_#Z′_ν) + M(ψ_#S_{σ_ν})] ≤ cM(∂T).

7. Tangential property (first part of printed (26); parent C7). Let F = (z, α) be a face index, B := ball y r with B ∩ L_n ⊆ latticeFace 1 F ⊆ Π_F, and ω a test n-form with tsupport ω ⊆ B and ω(x)(e_α) = 0 for all x. We show ψ_#X_ν(ω) = 0 for every ν; then Q(ω) = lim ψ_#X_ν(ω) = 0. Fix ν, σ := σ_ν, f := ψ̄_σ, Λ := Λ_σ. By A2(e), ψ_#X_ν(ω) = lim_{ε↓0}(f_ε)_#X_ν(ω) with f_ε := ϕ_ε * f smooth, |f_ε − f| ≤ Λε, and by A2(b) (f_ε)_#X_ν(ω) = X_ν(ζ f_ε^#ω) = ∫⟨f_ε^#ω, X⃗_ν⟩dμ_{X_ν}, where μ_{X_ν} is concentrated on spt X_ν ⊆ {d_a ≥ σ}. Let δ₀ := dist(tsupport ω, ℝ^d ∖ B) > 0 and take ε < min{σ/8, δ₀/(4Λ + 4)}. Let x ∈ spt X_ν. If f_ε(x) ∉ tsupport ω then f_ε^#ω(x) = 0. Otherwise, for every x′ with |x′ − x| < 2ε: x′ ∈ {d_a > σ/2}, so f(x′) = ψ(x′), and |ψ(x′) − f_ε(x)| ≤ |f(x′) − f(x)| + |f(x) − f_ε(x)| ≤ 3Λε < δ₀, so ψ(x′) ∈ B; since x′ ∉ La, ψ(x′) ∈ B ∩ L_n ⊆ Π_F by (S1)(i), i.e. the coordinates ψ(x′)_i, i ∉ range α, equal z_i. Hence for |x″ − x| < ε the normal coordinates of f_ε(x″) = ∫f(x″ − w)ϕ_ε(w)dw are the constants z_i, so Df_ε(x) maps ℝ^d into span{e_{α_j}}, and f_ε^#ω(x)(v₁,…,v_n) = ω(f_ε(x))(Df_ε(x)v₁,…,Df_ε(x)v_n) = det(⋯)·ω(f_ε(x))(e_α) = 0. Thus f_ε^#ω vanishes on spt X_ν and (f_ε)_#X_ν(ω) = 0 for all small ε, so ψ_#X_ν(ω) = 0. Therefore Q satisfies the tangential property of the statement.

8. Conclusion. Put R := R₁ ∈ D_{m+2}(ℝ^d) and S := S₁ ∈ D_{m+1}(ℝ^d). By (21), T(ω) − Q(ω) = R.boundary(ω) + S(ω) for all ω; spt Q ⊆ L_n by (22); the tangential property by Step 7; the four mass bounds by (24)–(25); the support inclusions spt Q ∪ spt R ⊆ cthickening √d (spt T) and spt ∂Q ∪ spt S ⊆ cthickening √d (spt ∂T) by Step 6; and the integrality statements by Step 5. All constants (c_A, c_B and those of Steps 3–6) depend only on (m, ℓ); C is their maximum. ∎

## Key steps

1. Tools: products with [[(0,1)]], smooth and Lipschitz push-forwards, homotopy formula and estimates (2.17–2.29), products of integer multiplicity currents (3.2(2)), M-limits with completeness (sibling im_completeness), integrality of Lipschitz push-forwards (sibling im_pushforward_limit, using the premise LipschitzPushforwardIntegerMultiplicity).
2. Mass measures μ_T, μ_∂T (sibling mass_restriction) and a good centre a (sibling good_center): μ(L_{ℓ−1}(a;σ)) ≤ cσ^{n+1}M (printed (6),(7)); retraction ψ (sibling retraction).
3. Truncations T_σ, slices via SlicingTheorem identified by restriction uniqueness, good radii σ_ν ∈ (2^{−ν−1}, 2^{−ν}) with small slices of T and finite slices of ∂T (printed (8)–(10)).
4. Estimates (11)–(16) for the pieces between consecutive good radii and telescoped bounds (17)–(18).
5. M-limits Q, R₁, S₁ and the corrected homotopy identity (20) give T − Q = ∂R₁ + S₁ (21); integrality via I.7 (sibling im_pushforward_limit), products (3.2(2)) and completeness (sibling im_completeness).
6. Supports and masses (22)–(25): spt Q ⊆ L_n, closed √d-thickenings, M(∂Q) ≤ cM(∂T).
7. Tangential property: mollified ψ has locally constant normal coordinates near the open faces, so Q kills forms without tangential component (first part of (26)).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp project/GMT/Ch06/Contract.lean project/GMT/Ch06/Submission.lean (all byte-identical)`
- `rg -n '^def (latticeFace|latticeFaceAction|IsLatticeChain|DeformationTheorem|IsRestriction|IsMeasureRepresentation)' project/GMT/Ch06/Contract.lean (lines 107, 115, 164, 171, 177, 274)`
- `python3 over dag.json: lean_name of all 86 nodes vs the nine proposed deformation_* names (no collision; only deformation_theorem, the selected node, is reserved)`
- `rg -n 'deformation_(retraction|good_center|mass_restriction|im_completeness|im_pushforward_limit|onto_skeleton|skeleton_polyhedral|im_combination|dilation)' project lake-packages-25730c7c/simongmt (no match)`
- `python3 over nodes/root-deformation-a1/decomposition-audit-v1.json (only skeleton_polyhedral natural_proof_acceptable = false; required change: R = √n/2, δ = 1/(2√n))`
- `rg -il 'poincar' mathlib/Mathlib (curve integrals, Lie algebras, dynamics, Poincaré conjecture only: no BV Poincaré inequality on convex domains)`
- `rg -l 'BoundedVariationOn|eVariationOn' mathlib/Mathlib (one-dimensional bounded variation only)`
- `rg -l 'Sobolev|GagliardoNirenberg|gagliardo' mathlib/Mathlib; rg -n '^theorem [a-zA-Z_.]*(lintegral_pow_le|eLpNorm_le_eLpNorm_fderiv)' mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean (Gagliardo–Nirenberg–Sobolev for compactly supported C¹ maps only)`
- `rg -n 'theorem (cthickening_subset_thickening'|cthickening_cthickening_subset|mem_thickening_iff) ' mathlib/Mathlib/Topology/MetricSpace/Thickening.lean (lines 143, 261, 638)`
- `rg -n 'theorem LipschitzOnWith.extend_real' mathlib/Mathlib (Topology/MetricSpace/Lipschitz.lean:308, McShane extension)`
- `sed -n '440,780p' book/chapter-02.txt (Simon Ch. 2, 2.1–2.9: 2.7 assumes δ ∈ (0,1) and B_{δR}(ξ) ⊂ U ⊂ B_R(ξ); the proof of 2.8 uses display (1) only where d(x) < dist(B_δ(0), ∂U))`
- `sed -n '560,720p;1780,1920p' book/chapter-06.txt (2.34–2.37 and printed displays (18)–(37) of the proof of 5.1)`
- `python3 -I: validate_lean_statement (verifier/lean_contract.py) on the nine lean_statements (all valid and unchanged)`
- `lake env lean Scratch/V2_NC_<key>.lean for the nine keys: `theorem _root_.HumanizeNodeComparator.target : (stmt) := by sorry` in the contract scope (all exit 0; only the expected sorry warning)`
- `lake env lean Scratch/V2_Assembly.lean (assembly : SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → Stmt_onto_skeleton → Stmt_skeleton_polyhedral → Stmt_im_combination → Stmt_dilation → DeformationTheorem; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/BoundedVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/deform_check/Scratch/V2_Assembly.lean`
- `/tmp/deform_check/Scratch/V2_NC_skeleton_polyhedral.lean`
- `/tmp/deform_v2/logs/assembly.log`
- `/tmp/deform_v2/logs/nc_skeleton_polyhedral.log`

Pinned revisions confirmed and the frozen contract is byte-identical to the snapshot (Submission = Contract), so the nine v1 interfaces remain valid. None of the nine bare names collides with a DAG reservation or with a declaration in the project or SimonGMT sources. All nine statements pass validate_lean_statement and elaborate in the exact comparator NodeChallenge scope. The parent assembly re-derives DeformationTheorem from onto_skeleton, skeleton_polyhedral, im_combination and dilation plus SlicingTheorem and LipschitzPushforwardIntegerMultiplicity, with axioms [propext, Classical.choice, Quot.sound]. No Matrix/IsUnit construction occurs. The pinned Mathlib has no multi-dimensional BV Poincaré inequality or BV cut-off/extension lemma (only one-dimensional BoundedVariationOn and the compact-support Gagliardo–Nirenberg–Sobolev inequality), so (T4) of deformation_skeleton_polyhedral is proved from Simon Ch. 2, 2.7–2.9 and [GT01, (7.45)]. Simon's printed 2.7 requires δ ∈ (0,1), and his proof of 2.8 needs the inner ball at positive distance from ∂U. The corrected parameters R = √n/2, δ = 1/(2√n) (δR = 1/4, distance 1/4) meet both requirements for every n ≥ 1, as the revised (T4) verifies explicitly.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: https://github.com/ZhengyangZhang06/gmt-formalize/pull/7347

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
