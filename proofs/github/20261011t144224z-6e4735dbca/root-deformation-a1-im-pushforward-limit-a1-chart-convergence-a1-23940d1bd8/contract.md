<!-- theorem-id: gmt-ch06/root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1 -->

## Theorem `Submission.deformation_ipl_chart_convergence`

Let P, Q, k ∈ ℕ, H^k := μHE[k] on ℝ^P, and let (M, θ, ξ) satisfy IsRectifiableTriple univ k M θ ξ. Let g : ℝ^P → ℝ^Q be Λ-Lipschitz and L : ℝ^P → L(ℝ^P, ℝ^Q) such that for H^k-a.e. x ∈ M, for every linear subspace T_x that is a weighted approximate tangent space of (M, θ) at x (HasWeightedApproximateTangentSpaceAt k M θ x T_x) and every v ∈ T_x, the map t ↦ g(x + t v) has derivative L(x)v at t = 0. Assume θ is H^k-integrable on M ∩ g⁻¹(K) for every compact K ⊆ ℝ^Q. Let g_j : ℝ^P → ℝ^Q (j ∈ ℕ) be C¹ maps, Λ′-Lipschitz for one common Λ′, converging uniformly to g on ℝ^P, and let ω : ℝ^Q → Covector (Eucl Q) k be continuous with compact support. Then ∫_M θ(x)·(Dg_j(x)_#ξ(x))(ω(g_j(x))) dH^k(x) → ∫_M θ(x)·(L(x)_#ξ(x))(ω(g(x))) dH^k(x) as j → ∞, where A_# = nVectorPushforward k A and Dg_j(x) = fderiv ℝ (g_j) x.

Node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1111

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/735, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1073, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4382, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4388

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/731, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2422, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1073, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2028, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1266, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4915, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4918, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4923, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4925, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4930, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4937

## Lean problem

Declaration: `Submission.deformation_ipl_chart_convergence`

```lean
∀ (P Q k : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (g : Eucl P → Eucl Q) (Λ : ℝ≥0) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → LipschitzWith Λ g → (∀ᵐ x ∂((μHE[k] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt k M θ x Tx → ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => g (x + t • v)) (L x v) 0) → (∀ K : Set (Eucl Q), IsCompact K → IntegrableOn θ (M ∩ g ⁻¹' K) (μHE[k] : Measure (Eucl P))) → ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : Eucl Q → Covector (Eucl Q) k, Continuous ω → HasCompactSupport ω → Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) (ω (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (∫ x in M, θ x * nVectorPushforward k (L x) (ξ x) (ω (g x)) ∂(μHE[k] : Measure (Eucl P))))
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

- Parent DAG node: `root.deformation-a1.im_pushforward_limit-a1`
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: part (I) of the parent proof (steps (a)–(g)), with these specializations, each of which only removes data that (I) does not use: (1) the tangential differential L(x) = d^Mg_x∘π_{T_xM} of the parent is replaced by an arbitrary map L having the directional-derivative property on the weighted approximate tangent spaces of (M,θ) — this property is the only one of d^Mg used in (c) and (f) (in the parent assembly L is the map L′ of IsLipschitzPushforward, transferred to (M,θ) by tangent locality; the parent's (II.7b–c) shows that L′ and d^Mg agree on T_xM); (2) the compactness of g⁻¹(K) ∩ spt X and H^k(M ∖ spt X) = 0 of step (b) are replaced by their only consequence used, the integrability of θ on M ∩ g⁻¹(K) for compact K; (3) the test form is only required to be continuous with compact support; (4) the ingredients of (c), (e) and (f) are the siblings: c1_cover (the chart cover of (e)), chart_chain_rule (tangent identification and chain rule of (f)), chart_change_of_variables (the area formula for the injective chart in (f)), simple_nvector_algebra (unit and change-of-frame facts), pushforward_measurable (the measurability of F claimed in (c)) and minor_weak_continuity (the weak continuity of minors and the final estimate of (f)).

Conventions. H := μHE[k] on ℝ^P; on ℝ^k, μHE[k] = L^k = volume. For a linear A : ℝ^P → ℝ^Q, A_# := nVectorPushforward k A, (A_#w)(β) = w(covectorPullback k A β) with covectorPullback k A β = β(A·,…,A·); A_# is linear in w and A_#(simpleNVector v) = simpleNVector(A∘v) (SimonGMT nVectorPushforward_simple); simpleNVector v (β) = β(v). Covectors and k-vectors carry operator norms, |β(v_0,…,v_{k−1})| ≤ ‖β‖·Π|v_b|, and ‖ω‖_∞ := sup_y‖ω(y)‖ < ∞ (ω is continuous with compact support). F_j(x) := θ(x)·(Dg_j(x)_#ξ(x))(ω(g_j(x))) with Dg_j(x) := fderiv ℝ (gj j) x, and F(x) := θ(x)·(L(x)_#ξ(x))(ω(g(x))), are the integrands of the statement. e_b := EuclideanSpace.single b 1, ∂_bφ(w) := fderiv ℝ φ w e_b, ∂φ(w) := (∂_0φ(w),…,∂_{k−1}φ(w)), and JΦ(w) := (det(⟨∂_aΦ(w), ∂_bΦ(w)⟩)_{a,b})^{1/2}. A map Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

0. (Degenerate dimension.) If k > P then H = 0 on ℝ^P (μHE[k] is a constant multiple of μH[k], and μH[k](ℝ^P) = 0 because k exceeds the Hausdorff dimension P of ℝ^P), so both sides are 0. The argument below is valid for every k; for k = 0 all families are empty, simpleNVector of the empty family has norm 1, and JΦ ≡ 1.

1. (A fixed compact target set; parent (a).) Let K₀ := tsupport ω (compact) and K := {y : dist(y, K₀) ≤ 1} (compact; empty if K₀ = ∅). By uniform convergence choose j₀ with |g_j(x) − g(x)| < 1 for all x ∈ ℝ^P and all j ≥ j₀. For such j: if ω(g_j(x)) ≠ 0 then g_j(x) ∈ K₀, so g(x) ∈ K; and if ω(g(x)) ≠ 0 then g(x) ∈ K₀ ⊆ K. Hence F_j(x) = 0 and F(x) = 0 whenever g(x) ∉ K (j ≥ j₀). Only the tail j ≥ j₀ matters for the limit.

2. (One dominator; parent (c).) For H⌞M-a.e. x: (i) by the orientation clause of the triple, ξ(x) = ε·simpleNVector τ with ε ∈ {1, −1}, τ orthonormal and span τ a weighted approximate tangent space of (M,θ) at x; (ii) by the hypothesis on L, for each a the map t ↦ g(x + tτ_a) has derivative L(x)τ_a at t = 0, so |L(x)τ_a| ≤ Λ (g is Λ-Lipschitz and |τ_a| = 1). At such x, (A_#ξ(x))(β) = ε·β(Aτ_0,…,Aτ_{k−1}) for every linear A and covector β. Since g_j is differentiable and Λ′-Lipschitz, ‖Dg_j(x)‖ ≤ Λ′. With step 1, for j ≥ j₀: |F_j(x)| ≤ G(x) and |F(x)| ≤ G(x), where G := ‖ω‖_∞·Λ″^k·θ·1_{g⁻¹(K)} and Λ″ := max(Λ, Λ′). G is H⌞M-integrable, because θ is H-integrable on M ∩ g⁻¹(K) by hypothesis.

3. (Measurability and integrability.) θ is H⌞M-a.e. strongly measurable: it is H-integrable on M ∩ B̄_q(0) for each q ∈ ℕ (field integrableOn of the triple with U = ℝ^P), and M = ⋃_q(M ∩ B̄_q(0)). F_j: the covector field x ↦ covectorPullback k (Dg_j(x)) (ω(g_j(x))) is continuous (g_j is C¹, so Dg_j is continuous; A ↦ covectorPullback k A is continuous, Mathlib ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM; ω∘g_j is continuous), ξ is H⌞M-a.e. strongly measurable and the evaluation (w, β) ↦ w(β) is continuous; so F_j(x) = θ(x)·ξ(x)(covectorPullback k (Dg_j(x)) (ω(g_j(x)))) is H⌞M-a.e. strongly measurable. F: by the sibling pushforward_measurable (with U := ℝ^P, which is open, the given triple, f := g, which is locally Lipschitz on ℝ^P because it is Lipschitz, and the hypothesis on L), x ↦ L(x)_#ξ(x) is H⌞M-a.e. strongly measurable, and ω∘g is continuous; so F is H⌞M-a.e. strongly measurable. Together with step 2, F_j (j ≥ j₀) and F are H⌞M-integrable.

4. (Chart pieces; parent (e).) M is countably k-rectifiable, so the sibling c1_cover gives C¹ maps Φ_i : ℝ^k → ℝ^P and open Ω_i ⊆ ℝ^k (i ∈ ℕ), Φ_i K_i-Lipschitz and c_i-antilipschitz (c_i > 0) on Ω_i, with H(M ∖ ⋃_iΦ_i(Ω_i)) = 0. Each Φ_i(Ω_i) is σ-compact (Ω_i is a countable union of compact sets and Φ_i is continuous), hence Borel. Put G_i := (M ∩ Φ_i(Ω_i)) ∖ ⋃_{i′<i}Φ_{i′}(Ω_{i′}). The G_i are pairwise disjoint and H-null-measurable (M is), G_i ⊆ M ∩ Φ_i(Ω_i), and M ∖ ⋃_iG_i = M ∖ ⋃_iΦ_i(Ω_i) is H-null; hence M and ⋃_iG_i are H-a.e. equal.

5. (Countable additivity.) For j ≥ j₀, F_j and F are H-integrable on M (step 3), so by countable additivity of the integral over pairwise disjoint null-measurable sets (Mathlib integral_iUnion_ae, together with M =ᵃᵉ ⋃_iG_i): ∫_M F_j dH = Σ_i a_i(j) and ∫_M F dH = Σ_i a_i, where a_i(j) := ∫_{G_i} F_j dH and a_i := ∫_{G_i} F dH. Moreover |a_i(j)|, |a_i| ≤ b_i := ∫_{G_i} G dH (step 2), and Σ_i b_i = ∫_{⋃_iG_i} G dH ≤ ∫_M G dH < ∞.

6. (One chart; parent (f).) Fix i and write Φ, Ω, K_Φ, c for Φ_i, Ω_i, K_i, c_i. Let G_K := G_i ∩ g⁻¹(K) (H-null-measurable, since g⁻¹(K) is closed), D := Ω ∩ Φ⁻¹(G_K), u_j := g_j∘Φ and u := g∘Φ. By step 1, for j ≥ j₀, a_i(j) = ∫_{G_K} F_j dH and a_i = ∫_{G_K} F dH.
 (6a) [Jacobian bound.] For w ∈ Ω and v ∈ ℝ^k, |DΦ(w)v| ≥ c|v|: for small t ≠ 0 we have w + tv ∈ Ω and c|t||v| ≤ |Φ(w + tv) − Φ(w)| = |t·DΦ(w)v + o(t)|; divide by |t| and let t → 0. Hence the Gram matrix (⟨∂_aΦ(w), ∂_bΦ(w)⟩)_{a,b} is ≥ c²·I, so JΦ(w) ≥ c^k > 0. JΦ is continuous on Ω (Φ is C¹).
 (6b) [Change of variables.] The sibling chart_change_of_variables applies to Φ and Ω (Φ is Lipschitz and antilipschitz on the open Ω) and to A := G_K ⊆ Φ(Ω): D is L^k-null-measurable, and for every h : ℝ^P → [0, ∞] that is a.e.-measurable for H⌞G_K, h∘Φ is a.e.-measurable for L^k⌞D and ∫_{G_K} h dH = ∫_D h(Φ(w))·JΦ(w) dw. Two consequences: (α) if Z ⊆ ℝ^P is H-null, then h := 1_Z vanishes H⌞G_K-a.e., so ∫_D 1_Z(Φ(w))·JΦ(w) dw = 0 and, by (6a), Φ(w) ∉ Z for L^k-a.e. w ∈ D; (β) applying the formula to the positive and negative parts of θ, of F_j (j ≥ j₀) and of F — all H-integrable on G_K ⊆ M ∩ g⁻¹(K) by step 3 and the hypothesis on θ — gives: θ∘Φ is a.e.-measurable for L^k⌞D and ∫_D θ(Φ(w))·JΦ(w) dw = ∫_{G_K} θ dH < ∞; and for φ ∈ {F_j (j ≥ j₀), F}, w ↦ φ(Φ(w))·JΦ(w) is L^k⌞D-integrable with ∫_{G_K} φ dH = ∫_D φ(Φ(w))·JΦ(w) dw.
 (6c) [Good parameters and the pointwise formula.] Fix a strongly measurable ξ̃ with ξ = ξ̃ H⌞M-a.e. For L^k-a.e. w ∈ D, with x := Φ(w) ∈ M: (i) range DΦ(w) is a weighted approximate tangent space of (M,θ) at x and u has Fréchet derivative L(x)∘DΦ(w) at w (sibling chart_chain_rule with U := ℝ^P and f := g; it holds for L^k-a.e. w ∈ Ω ∩ Φ⁻¹(M) ⊇ D); (ii) the orientation clause holds at x and ξ(x) = ξ̃(x) (the set of points of M where this fails is H-null; use (6b)(α)). At such w: ξ(x) = ε·simpleNVector τ with ε = ±1, τ orthonormal and span τ a weighted approximate tangent space at x; since θ(x) > 0, span τ = range DΦ(w) (SimonGMT HasWeightedApproximateTangentSpaceAt.unique). Write ∂_bΦ(w) = Σ_a B_{ba}τ_a with B_{ba} := ⟨∂_bΦ(w), τ_a⟩. By the second identity of the sibling simple_nvector_algebra, simpleNVector(∂Φ(w)) = det B·simpleNVector τ; by its first identity, ‖simpleNVector τ‖² = det I = 1 and ‖simpleNVector(∂Φ(w))‖² = det(⟨∂_aΦ(w), ∂_bΦ(w)⟩) = JΦ(w)², so |det B| = JΦ(w) > 0. Let β_w be the covector v ↦ det(⟨∂_aΦ(w), v_b⟩)_{a,b}, i.e. wedgeCovectors k (fun a => ⟨∂_aΦ(w), ·⟩) (SimonGMT wedgeCovectors_apply_det); then simpleNVector(∂Φ(w))(β_w) = JΦ(w)², and s(w) := ξ̃(x)(β_w)/JΦ(w) = ε·JΦ(w)/det B ∈ {1, −1} satisfies ξ(x) = s(w)·JΦ(w)⁻¹·simpleNVector(∂Φ(w)). Using A_#(simpleNVector v) = simpleNVector(A∘v), Dg_j(x)∂_bΦ(w) = ∂_bu_j(w) (chain rule for the C¹ maps g_j and Φ) and L(x)∂_bΦ(w) = ∂_bu(w) (by (i)), we get
 F_j(x)·JΦ(w) = s(w)·θ(x)·ω(u_j(w))(∂u_j(w)),  F(x)·JΦ(w) = s(w)·θ(x)·ω(u(w))(∂u(w)).
 (6d) [The weight.] Put ψ(w) := 1_D(w)·θ(Φ(w))·ξ̃(Φ(w))(β_w)/JΦ(w) for w ∈ Ω and ψ := 0 off Ω. It is a.e.-strongly measurable for L^k⌞Ω (D is null-measurable; θ∘Φ is a.e.-measurable on L^k⌞D by (6b)(β); ξ̃∘Φ is strongly measurable; w ↦ β_w and JΦ are continuous on Ω and JΦ > 0). By (6c), |ψ| = 1_D·(θ∘Φ) L^k-a.e., so by (6a) and (6b)(β), ∫_Ω|ψ| dw = ∫_D θ(Φ(w)) dw ≤ c^{−k}∫_D θ(Φ(w))·JΦ(w) dw = c^{−k}∫_{G_K} θ dH < ∞. Thus ψ is Lebesgue integrable on Ω, and by (6b)(β) and (6c), for j ≥ j₀:
 a_i(j) = ∫_D F_j(Φ(w))·JΦ(w) dw = ∫_Ω ψ(w)·ω(u_j(w))(∂u_j(w)) dw,  a_i = ∫_D F(Φ(w))·JΦ(w) dw = ∫_Ω ψ(w)·ω(u(w))(∂u(w)) dw.
 (6e) [Weak continuity of minors.] u_j is (Λ′K_Φ)-Lipschitz and u is (ΛK_Φ)-Lipschitz on Ω, and sup_Ω|u_j − u| ≤ sup_{ℝ^P}|g_j − g| → 0, so u_j → u uniformly on Ω. The sibling minor_weak_continuity, applied with this Ω and ψ, α := ω (continuous with compact support), C := K_Φ·max(Λ, Λ′), u_j and u₀ := u, gives a_i(j) → a_i as j → ∞.

7. (Summation; parent (g).) By step 5, |a_i(j)| ≤ b_i for every i and every j ≥ j₀, with Σ_i b_i < ∞, and a_i(j) → a_i for every i by step 6. Dominated convergence for series (Tannery's theorem, Mathlib tendsto_tsum_of_dominated_convergence) gives Σ_i a_i(j) → Σ_i a_i, i.e., by step 5, ∫_M F_j dH → ∫_M F dH, which is the assertion. ∎

Implementation remarks. NVector (Eucl P) k = Covector (Eucl P) k →L[ℝ] ℝ does not synthesize ContinuousENorm in this environment and the generic norm lemmas do not unify with its operator norm: avoid NVector-valued integrals, work with the real integrands F_j, F, and use the ContinuousLinearMap.opNorm_* lemmas. Continuity of (A, w) ↦ A_#w is ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM composed with ContinuousLinearMap composition (as in the accepted Submission.lpf_pi_measurability). The signed change of variables in (6b)(β) is obtained from the lintegral identity of chart_change_of_variables applied to ENNReal.ofReal of the positive and negative parts.

## Key steps

1. Fixed compact target K = closed 1-neighbourhood of tsupport ω: for j ≥ j₀ both integrands vanish off g⁻¹(K); the orientation clause, ‖Dg_j‖ ≤ Λ′ and |L(x)τ_a| ≤ Λ give the dominator ‖ω‖_∞max(Λ,Λ′)^kθ1_{g⁻¹(K)}, integrable by hypothesis.
2. Measurability: F_j directly (continuous pulled-back covector field), F by the sibling pushforward_measurable; hence F_j (j ≥ j₀) and F are integrable on M.
3. Sibling c1_cover: disjoint null-measurable pieces G_i ⊆ Φ_i(Ω_i) covering M up to an H^k-null set; countable additivity splits both integrals into series dominated by Σ_i∫_{G_i}G < ∞.
4. On one chart: JΦ ≥ c^k; the sibling chart_change_of_variables transfers integrals and null sets to Ω; the siblings chart_chain_rule and simple_nvector_algebra give ξ(Φ(w)) = s(w)JΦ(w)⁻¹·simpleNVector(∂Φ(w)), |s| = 1, so both chart integrals equal ∫_Ω ψ·ω(u)(∂u) with u = g_j∘Φ resp. g∘Φ and ψ ∈ L¹(Ω).
5. The sibling minor_weak_continuity gives convergence on each chart; Tannery's theorem sums the charts.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I over dag.json: node root.deformation-a1.im_pushforward_limit-a1 has status decomposing, 'subproblem decomposition attempt 3', children [] (attempts 1-2 accepted by review but never activated)`
- `python3 -I over dag.json: status/candidate_commit/lean_statement of ltg_tau_unique_on_open, lpf_rectifiable_support_null, br_weightedTangent_congr, lpf_simple_nvector_algebra, cmb_covector_eq_sum_coord_smul_wedge, lpf_countably_rectifiable_c1_cover, lpf_chart_chain_rule, lpf_raf_chart_change_of_variables, lpf_tde_measurable_chart_differential (all accepted with candidate commits; types byte-identical to their handoffs and, for tau_unique/support_null, to the v2 children)`
- `python3 -I over dag.json: lean_name collisions for deformation_ipl_minor_weak_continuity, deformation_ipl_tangential_pushforward_aestronglyMeasurable, deformation_ipl_chart_convergence (none)`
- `rg -l 'deformation_ipl_' snapshot project, snapshot mathlib/Mathlib, lake-packages-25730c7c/simongmt/Poincare, GMT (no match)`
- `rg -n 'theorem HasWeightedApproximateTangentSpaceAt.unique|def nVectorPushforward|theorem nVectorPushforward_simple|def simpleNVector|theorem wedgeCovectors_apply_det|def covectorPullback' simongmt/Poincare/SimonGMT`
- `sed -n '205,260p' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (euclideanHausdorffMeasure_image_le_of_lipschitzOn)`
- `rg -n 'lemma locallyLipschitzOn_univ|LipschitzWith.locallyLipschitz|theorem IntegrableOn.mono_set_ae|theorem ae_le_set |theorem continuous_compContinuousLinearMapCLM|lemma tendsto_tsum_of_dominated_convergence|theorem integral_iUnion_ae|euclideanHausdorffMeasure_eq_volume|theorem measurable_fderiv |aestronglyMeasurable_iUnion_iff|LipschitzOnWith.extend_real|ae_convolution_tendsto_right_of_locallyIntegrable' snapshot mathlib/Mathlib`
- `git show a2a69a08f815abcf63c2e24fa1b57c6c02fdd1eb:GMT/Ch06/Submission.lean (accepted lpf_pi_measurability: continuity of (A, w) ↦ A_#w via ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM)`
- `python3 -I /tmp/ipl3/gen_types.py: verifier/lean_contract.py validate_lean_statement and gmt-compare.py contract_scope/child_modules for the twelve types`
- `lake env lean /tmp/ipl3/build/AllTypes.lean (exit 0, twelve sorry warnings); lake env lean /tmp/ipl3/build/Assembly.lean (exit 0, axioms propext, Classical.choice, Quot.sound); lake env lean /tmp/ipl3/build/ProtoPM.lean (exit 0, same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-unique-on-open-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-support-null-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-countably-rectifiable-c1-cover-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/ipl3/build/AllTypes.lean`
- `/tmp/ipl3/build/Assembly.lean`
- `/tmp/ipl3/build/ProtoPM.lean`

Pinned revisions are confirmed, and the frozen contract is byte-identical to the snapshot (Submission = Contract).
Reuse:
- The nine reused declarations are comparator-accepted with candidate commits.
- Their titles, statements and Lean types are copied byte-for-byte from dag.json.
- ltg_tau_unique_on_open and lpf_rectifiable_support_null are byte-identical to the v2 children tau_unique and support_null, which were then unaccepted.
New names: the three new names collide with nothing in dag.json, the project, SimonGMT or the pinned Mathlib.
Library support (all present in the snapshot, the SimonGMT names in the pinned package):
- SimonGMT: HasWeightedApproximateTangentSpaceAt.unique (needs θ x ≠ 0), nVectorPushforward_simple, wedgeCovectors_apply_det, euclideanHausdorffMeasure_image_le_of_lipschitzOn.
- Mathlib: integral_iUnion_ae, tendsto_tsum_of_dominated_convergence, measurable_fderiv, aestronglyMeasurable_iUnion_iff, continuous_compContinuousLinearMapCLM, LipschitzOnWith.extend_real, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable.
- No general weak-continuity-of-minors theorem exists in Mathlib or SimonGMT, and no accepted DAG node provides one (slicing_im_ll_gradient_weak_star, the first-order case, is still decomposing). minor_weak_continuity therefore stays a new child.
Lean checks:
- All twelve statements validate and elaborate in the exact comparator scope.
- The parent assembly compiles from four child types with only propext, Classical.choice and Quot.sound.
- The new measurability child compiles from its three sibling types with the same axioms.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
