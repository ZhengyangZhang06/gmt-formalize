<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1 -->

## Theorem `Submission.slicing_im_ll_tangential_weak_limit`

Let P, n ∈ ℕ, U ⊆ ℝ^P open and (M, θ, ξ) with IsRectifiableTriple U n M θ ξ (M ⊆ U Hⁿ-null-measurable and countably n-rectifiable, θ > 0 on M and Hⁿ-integrable on M ∩ K for every compact K ⊆ U, ξ Hⁿ⌞M-a.e. strongly measurable with ξ(x) = ±τ₁∧…∧τ_n for an orthonormal basis τ of a weighted approximate tangent plane at Hⁿ-a.e. x ∈ M). Let h : ℝ^P → ℝ be L-Lipschitz and G : ℝ^P → ℝ^P Borel with |G| ≤ L everywhere and the tangential-gradient property (for Hⁿ-a.e. x ∈ M and every weighted approximate tangent plane Q of (M, θ) at x: G(x) ∈ Q and s ↦ h(x + su) has derivative ⟨G(x), u⟩ at s = 0 for every u ∈ Q). Let Y : ℝ^P → ℝ^P be Hⁿ⌞M-integrable with Y(x) ∈ Q for Hⁿ-a.e. x ∈ M and every weighted approximate tangent plane Q of (M, θ) at x. Let g_k : ℝ^P → ℝ (k ∈ ℕ) be differentiable and L-Lipschitz with g_k → h uniformly on ℝ^P. Then ∫_M Dg_k(x)(Y(x)) dHⁿ(x) → ∫_M ⟨G(x), Y(x)⟩ dHⁿ(x) as k → ∞.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2506

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3657

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/731, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1073, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2422, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2444, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2028, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4552, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4559, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4575, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4585, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4592

## Lean problem

Declaration: `Submission.slicing_im_ll_tangential_weak_limit`

```lean
∀ (P n : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsOpen U → IsRectifiableTriple U n M θ ξ → ∀ (h : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P), LipschitzWith L h → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (G x) u) 0) → ∀ Y : Eucl P → Eucl P, Integrable Y ((μHE[n] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt n M θ x Q → Y x ∈ Q) → ∀ g : ℕ → Eucl P → ℝ, (∀ k, Differentiable ℝ (g k)) → (∀ k, LipschitzWith L (g k)) → TendstoUniformly g h atTop → Tendsto (fun k => ∫ x in M, fderiv ℝ (g k) x (Y x) ∂(μHE[n] : Measure (Eucl P))) atTop (𝓝 (∫ x in M, inner ℝ (G x) (Y x) ∂(μHE[n] : Measure (Eucl P))))
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P = Eucl P, ℝⁿ = Eucl n; Hᵏ := μHE[k] (Mathlib's Euclidean Hausdorff measure, equal to Lebesgue measure Lᵏ = volume on ℝᵏ); |·| is the Euclidean norm and ⟨·,·⟩ the inner product; Df(x) := fderiv ℝ f x (the Fréchet derivative where it exists and 0 otherwise). Source: parent proof, Steps 7–9 (Simon Ch. 6, proof of Lemma 4.5(2), equation (1) and its justification: 'since N_j is C¹ this follows fairly easily by approximating v by smooth functions and using the fact that h_σ converges to h uniformly'), for an arbitrary uniformly convergent sequence g_k of differentiable L-Lipschitz functions. For a map Φ : ℝⁿ → ℝ^P differentiable at w write A(w) := DΦ(w) and JΦ(w) := √det(⟨A(w)e_i, A(w)e_j⟩)_{i,j<n} (e_i = EuclideanSpace.single i 1). TG denotes the hypothesis on (h, G): for Hⁿ-a.e. x ∈ M and every subspace Q with HasWeightedApproximateTangentSpaceAt n M θ x Q, G(x) ∈ Q and s ↦ h(x + su) has derivative ⟨G(x), u⟩ at s = 0 for every u ∈ Q. Put F_k(x) := Dg_k(x)(Y(x)) and F_∞(x) := ⟨G(x), Y(x)⟩; the claim is ∫_M F_k dHⁿ → ∫_M F_∞ dHⁿ. The field produced in step 8 is called c (as in the sibling gradient_weak_star); lower Lipschitz constants of charts are called κ.
1. (Integrability.) Each g_k is L-Lipschitz on ℝ^P, so ‖Dg_k(x)‖ ≤ L for all x (`norm_fderiv_le_of_lipschitz`); x ↦ Dg_k(x) is Borel (`measurable_fderiv`) and Y is Hⁿ⌞M-a.e. strongly measurable, so F_k is Hⁿ⌞M-a.e. strongly measurable with |F_k| ≤ L|Y|, hence F_k ∈ L¹(Hⁿ⌞M). G is Borel with |G| ≤ L, so likewise F_∞ ∈ L¹(Hⁿ⌞M) and |F_∞| ≤ L|Y|.
2. (Degenerate cases.) (i) If n > P, then Hⁿ = 0 on ℝ^P: ℝ^P has Hausdorff dimension P < n (`Real.dimH_univ_eq_finrank`, `hausdorffMeasure_of_dimH_lt`, and μHE[n] is a multiple of the n-dimensional Hausdorff measure). So Hⁿ⌞M = 0, all integrals vanish and the claim is trivial. (ii) If n = 0, the orientation clause of IsRectifiableTriple gives for Hⁿ-a.e. x ∈ M an (empty) orthonormal family τ with HasWeightedApproximateTangentSpaceAt 0 M θ x (span ∅); span ∅ = {0}, so the tangency hypothesis gives Y(x) = 0. Thus F_k = F_∞ = 0 Hⁿ⌞M-a.e., all integrals vanish and the claim is trivial. From now on 1 ≤ n ≤ P.
3. (C¹ charts; Simon Ch. 3, Lemma 1.2 and Remark 1.3.) M is countably n-rectifiable, so by Simon Ch. 3, Lemma 1.2 (whose 'only if' part rests on the C¹ approximation theorem, Simon Ch. 2, 1.5) M ⊆ N₀ ∪ ⋃_{j≥1} N_j with Hⁿ(N₀) = 0 and each N_j an embedded n-dimensional C¹ submanifold of ℝ^P. By the local graph representation (Simon Ch. 2, 4.4) every y ∈ N_j has an open neighbourhood W with N_j ∩ W = ψ(V), where V ⊆ ℝⁿ is open, u : V → ℝ^{P−n} is C¹, Q_y is a coordinate permutation (an orthogonal map) and ψ(v) := Q_y(v, u(v)); ψ is a homeomorphism of V onto N_j ∩ W. Choose an open ball B ⊆ ℝⁿ with ψ⁻¹(y) ∈ B and closure B̄ ⊆ V, a C^∞ cutoff χ with χ = 1 on B̄ and compact support in V, and put Φ(v) := Q_y(v, χ(v)u(v)) (with χu extended by 0 outside V). Then Φ : ℝⁿ → ℝ^P is C¹, Φ = ψ on B, Φ is Lipschitz on the convex set B (DΦ is bounded on B̄), |Φ(v) − Φ(v')| ≥ |v − v'| for all v, v' (the first n coordinates of Q_y⁻¹Φ(v) are v), and ψ(B) is relatively open in N_j. As N_j is second countable, countably many such ψ(B) cover N_j. Enumerating all of them (and padding with Ω_j := ∅, for which all chart properties hold vacuously, if there are only finitely many) we obtain open sets Ω_j ⊆ ℝⁿ, C¹ maps Φ_j : ℝⁿ → ℝ^P and constants K_j ≥ 0, κ_j > 0 (j ∈ ℕ) such that Φ_j is K_j-Lipschitz on Ω_j, κ_j|w − w'| ≤ |Φ_j(w) − Φ_j(w')| for w, w' ∈ Ω_j, and Hⁿ(M ∖ ⋃_jΦ_j(Ω_j)) ≤ Hⁿ(N₀) = 0. (This is the statement of the reserved, not yet accepted, lipschitz-pushforward lemma lpf_countably_rectifiable_c1_cover.) Consequences, for each j: (i) Φ_j is injective on Ω_j and (Φ_j|Ω_j)⁻¹ is (1/κ_j)-Lipschitz; (ii) for w ∈ Ω_j, |DΦ_j(w)s| ≥ κ_j|s| for all s (divide κ_j|ts| ≤ |Φ_j(w + ts) − Φ_j(w)| by t ↓ 0), so DΦ_j(w) is injective, and ‖DΦ_j(w)‖ ≤ K_j; (iii) Φ_j(Ω_j) is σ-compact, hence Borel, and more generally Φ_j maps Borel subsets of Ω_j to Borel sets (`MeasurableSet.image_of_continuousOn_injOn`); (iv) if Hⁿ(Z) = 0 then Lⁿ(Ω_j ∩ Φ_j⁻¹(Z)) = 0, since this set is the image of Z ∩ Φ_j(Ω_j) under the Lipschitz map (Φ_j|Ω_j)⁻¹ and Lipschitz maps multiply Hⁿ by at most Lipⁿ (Hⁿ = Lⁿ on ℝⁿ); (v) Φ_j maps Lⁿ-null subsets of Ω_j to Hⁿ-null sets (K_j-Lipschitz on Ω_j).
4. (Disjoint pieces; reduction to one chart.) Put V_j := Φ_j(Ω_j) ∖ ⋃_{i<j}Φ_i(Ω_i) (Borel, pairwise disjoint, ⋃_jV_j = ⋃_jΦ_j(Ω_j)) and M_j := M ∩ V_j (Hⁿ-null-measurable). Since M ∖ ⋃_jM_j is Hⁿ-null, countable additivity of the integral (`integral_iUnion_ae`) gives, for every F ∈ L¹(Hⁿ⌞M), ∫_M F dHⁿ = Σ_j∫_{M_j}F dHⁿ with Σ_j∫_{M_j}|F| dHⁿ = ∫_M|F| dHⁿ. Apply this to F_k and F_∞. With b_j := L∫_{M_j}|Y| dHⁿ we have |∫_{M_j}F_k dHⁿ| ≤ b_j for all k, j (step 1) and Σ_jb_j = L∫_M|Y| dHⁿ < ∞. By dominated convergence for series (Tannery's theorem, `tendsto_tsum_of_dominated_convergence`) it suffices to prove, for each fixed j, (★_j) ∫_{M_j}F_k dHⁿ → ∫_{M_j}F_∞ dHⁿ as k → ∞. Fix j and write Φ, Ω, K, κ for Φ_j, Ω_j, K_j, κ_j.
5. (Area formula on the chart.) For every Lⁿ-null-measurable E₁ ⊆ Ω and every g : ℝ^P → [0, ∞] which is Hⁿ⌞Φ(E₁)-a.e. measurable: Φ(E₁) is Hⁿ-null-measurable (by 3(iii) and 3(v)) and ∫_{Φ(E₁)} g dHⁿ = ∫_{E₁} g(Φ(w))JΦ(w) dw. This is the area formula for the injective Lipschitz map Φ|Ω (Simon Ch. 2, 4.13; Federer 3.2.3, 3.2.5). With exactly these chart hypotheses and the Gram Jacobian JΦ it is the statement of the accepted lemma lpf_raf_chart_change_of_variables, applied to A := Φ(E₁) ⊆ Φ(Ω) (note Ω ∩ Φ⁻¹(A) = E₁ by injectivity). It also follows from SimonGMT `Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn` applied to a globally Lipschitz extension Φ̃ of Φ|Ω (componentwise McShane extension; DΦ̃ = DΦ on the open set Ω) and a Borel E₀ ⊆ E₁ with Lⁿ(E₁ ∖ E₀) = 0; its Jacobian, the normDet of DΦ̃, equals the Gram Jacobian (`LinearMap.normDet_sq_eq_det_gram`). JΦ is continuous (Φ is C¹) and κⁿ ≤ JΦ ≤ Kⁿ on Ω (by 3(ii)). Splitting real functions into positive and negative parts: for F ∈ L¹(Hⁿ⌞Φ(E₁)), w ↦ F(Φ(w))JΦ(w) is Lⁿ⌞E₁-integrable and ∫_{Φ(E₁)}F dHⁿ = ∫_{E₁}F(Φ(w))JΦ(w) dw.
6. (Tangent planes on the chart; Simon Ch. 3, Remark 1.5(2), proof of Theorem 1.6 '⟹', Remark 1.8(1).) Claim: for Hⁿ-a.e. x ∈ M ∩ Φ(Ω), writing x = Φ(w) with w ∈ Ω, T := range DΦ(w) (an n-dimensional subspace by 3(ii)) satisfies HasWeightedApproximateTangentSpaceAt n M θ x T. Proof: Put N := Φ(Ω). (6.0) Hⁿ⌞N is locally finite: for y ∈ ℝ^P and ρ > 0, Ω ∩ Φ⁻¹(B̄_ρ(y)) has diameter ≤ 2ρ/κ by 3(i), so by step 5 (or 3(v)) Hⁿ(N ∩ B̄_ρ(y)) ≤ Kⁿ·Lⁿ(Ω ∩ Φ⁻¹(B̄_ρ(y))) ≤ Kⁿω_n(2ρ/κ)ⁿ. Fix x ∈ M ∩ N and ρ_x > 0 with B̄_{ρ_x}(x) ⊆ U (U is open, M ⊆ U); θ is Hⁿ-integrable on M ∩ B̄_{ρ_x}(x). Let f ∈ C_c(ℝ^P) with spt f ⊆ B_R(0), R ∈ ℕ, R ≥ 1, and 0 < r < ρ_x/R. The substitution z = x + ry (Hⁿ scales by rⁿ under dilations; this identity of Bochner integrals holds for every r > 0) gives I_r(f) := ∫_{η_{x,r}(M)} f(y)θ(x + ry) dHⁿ(y) = r^{−n}∫_M f((z − x)/r)θ(z) dHⁿ(z). All integrands below vanish outside B̄_{Rr}(x) ⊆ B̄_{ρ_x}(x), where θ is integrable on M and Hⁿ⌞N is finite, so all of them are integrable and by linearity I_r(f) = θ(x)a_r − θ(x)b_r + c_r + d_r with a_r := r^{−n}∫_N f((z − x)/r) dHⁿ, b_r := r^{−n}∫_{N∖M} f((z − x)/r) dHⁿ, c_r := r^{−n}∫_{M∩N} f((z − x)/r)(θ(z) − θ(x)) dHⁿ(z), d_r := r^{−n}∫_{M∖N} f((z − x)/r)θ(z) dHⁿ(z). (6a) a_r → ∫_T f dHⁿ for every x = Φ(w), w ∈ Ω: by step 5, a_r = r^{−n}∫_Ω f((Φ(v) − Φ(w))/r)JΦ(v) dv = ∫_{(Ω−w)/r} f((Φ(w + rs) − Φ(w))/r)JΦ(w + rs) ds; the integrand vanishes unless |s| ≤ R/κ (as |Φ(w + rs) − Φ(w)| ≥ κr|s| for w + rs ∈ Ω), is bounded by sup|f|·Kⁿ, and converges pointwise to f(DΦ(w)s)JΦ(w) as r ↓ 0 (Ω open, Φ differentiable at w, JΦ continuous); by dominated convergence a_r → JΦ(w)∫_{ℝⁿ}f(DΦ(w)s) ds = ∫_T f dHⁿ (area formula for the injective linear map DΦ(w)). (6b) |b_r| ≤ sup|f|·r^{−n}Hⁿ((N ∖ M) ∩ B̄_{Rr}(x)). By (6.0) and the Upper Density Theorem (Simon Ch. 1, 3.6 with Remark 3.7(2)), the n-dimensional upper density of Hⁿ⌞(N ∖ M) vanishes at Hⁿ-a.e. point outside N ∖ M, in particular at Hⁿ-a.e. x ∈ M ∩ N; there b_r → 0. (6c) |d_r| ≤ sup|f|·r^{−n}∫_{(M∖N)∩B̄_{Rr}(x)}θ dHⁿ. The measure λ := θHⁿ⌞(M ∖ N) (θ > 0 on M) is locally finite on U by the integrability hypothesis on compact subsets of U, and λ(M ∩ N) = 0; the Upper Density Theorem (Simon Ch. 1, 3.6, 3.7(2), applied on an exhaustion of U by open sets of finite λ-measure) shows that its upper density vanishes at Hⁿ-a.e. x ∈ M ∩ N; there d_r → 0. (6d) Let ν := Hⁿ⌞(M ∩ N); by (6.0), ν(B̄_{Rr}(x)) ≤ Kⁿω_n(2Rr/κ)ⁿ. Let K_1 ⊆ K_2 ⊆ ⋯ be compact sets with K_q ⊆ int K_{q+1} and ⋃_qK_q = U. For each q, ν_q := Hⁿ⌞(M ∩ N ∩ K_q) is a finite Borel measure and θ ∈ L¹(ν_q), so by the Lebesgue differentiation theorem for the Besicovitch Vitali family of closed balls (Simon Ch. 1, 3.23; Federer 2.9.8; Mathlib `Besicovitch.vitaliFamily`, `Besicovitch.tendsto_filterAt`, `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div`), ν_q(B̄_ρ(x))⁻¹∫_{B̄_ρ(x)}|θ − θ(x)| dν_q → 0 as ρ ↓ 0 for ν_q-a.e. x. For x ∈ int K_q and small ρ, B̄_ρ(x) ⊆ K_q, so ν_q and ν agree on subsets of B̄_ρ(x); as every x ∈ M ∩ N lies in some int K_q, ν(B̄_ρ(x))⁻¹∫_{B̄_ρ(x)}|θ − θ(x)| dν → 0 for Hⁿ-a.e. x ∈ M ∩ N. At such x, |c_r| ≤ sup|f|·r^{−n}ν(B̄_{Rr}(x))·ν(B̄_{Rr}(x))⁻¹∫_{B̄_{Rr}(x)}|θ − θ(x)| dν ≤ sup|f|·Kⁿω_n(2R/κ)ⁿ·ν(B̄_{Rr}(x))⁻¹∫_{B̄_{Rr}(x)}|θ − θ(x)| dν → 0 (and c_r = 0 when ν(B̄_{Rr}(x)) = 0). Let X ⊆ M ∩ N be the set where (6b), (6c), (6d) hold for every R ∈ ℕ; Hⁿ((M ∩ N) ∖ X) = 0 (countably many null sets). For x ∈ X and every f ∈ C_c(ℝ^P), I_r(f) → θ(x)∫_T f dHⁿ as r ↓ 0, and finrank T = n; this proves the claim. (The claim is the conclusion of the reserved, not yet accepted, lemma lpf_weighted_tangent_on_c1_chart, which needs only part of the present hypotheses.) Since θ(x) > 0 on M, T is the only weighted approximate tangent plane at such x (SimonGMT `HasWeightedApproximateTangentSpaceAt.unique`).
7. (Good parameter points.) Let E := Ω ∩ Φ⁻¹(M_j); since M_j ⊆ Φ(Ω), Φ maps E bijectively onto M_j. E is Lⁿ-null-measurable: M_j = B ∪ Z₀ with B Borel and Z₀ contained in an Hⁿ-null Borel set, so E = (Ω ∩ Φ⁻¹(B)) ∪ (Ω ∩ Φ⁻¹(Z₀)) with the first set Borel and the second Lⁿ-null by 3(iv). Let E' be the set of w ∈ E such that, with x := Φ(w): (a) range DΦ(w) is a weighted approximate tangent plane of (M, θ) at x; (b) Y(x) ∈ Q for every weighted approximate tangent plane Q of (M, θ) at x; (c) the TG property holds at x; (d) h∘Φ is differentiable at w. The points x ∈ M_j at which (a), (b) or (c) fails form an Hⁿ-null set (step 6 and the two hypotheses), whose preimage in Ω is Lⁿ-null by 3(iv). h∘Φ is (LK)-Lipschitz on the open set Ω, so by Rademacher's theorem (applied to a Lipschitz extension of (h∘Φ)|Ω to ℝⁿ, `LipschitzOnWith.extend_real`, `LipschitzWith.ae_differentiableAt`; the extension agrees with h∘Φ on the open set Ω) (d) fails only on an Lⁿ-null subset of Ω. Hence Lⁿ(E ∖ E') = 0.
8. (Coefficient field.) For w ∈ Ω let A(w) := DΦ(w); the Gram matrix A(w)ᵀA(w) is invertible (3(ii)) and depends continuously on w. For w ∈ E' put a(w) := (A(w)ᵀA(w))⁻¹A(w)ᵀY(Φ(w)). By (a), (b) Y(Φ(w)) ∈ range A(w), say Y(Φ(w)) = A(w)s; then a(w) = s, i.e. A(w)a(w) = Y(Φ(w)), and κ|a(w)| ≤ |A(w)a(w)| = |Y(Φ(w))|. Define c(w) := JΦ(w)a(w) for w ∈ E' and c(w) := 0 for w ∉ E'. Measurability: Y = Ỹ Hⁿ⌞M-a.e. for some Borel Ỹ; then Y∘Φ = Ỹ∘Φ on E outside Ω ∩ Φ⁻¹(an Hⁿ-null set), which is Lⁿ-null by 3(iv); so Y∘Φ is Lⁿ⌞E-a.e. strongly measurable, and as (A(w)ᵀA(w))⁻¹A(w)ᵀ and JΦ(w) are continuous on Ω and E' is Lⁿ-null-measurable, c is Lⁿ⌞Ω-a.e. strongly measurable. Integrability: by step 5 with E₁ := E and g := |Y|, ∫_Ω|c(w)| dw ≤ κ⁻¹∫_E JΦ(w)|Y(Φ(w))| dw = κ⁻¹∫_{M_j}|Y| dHⁿ < ∞. So c is Lⁿ-integrable on Ω.
9. (Rewriting both integrals.) Put u_k := g_k∘Φ and u := h∘Φ. (9a) g_k is differentiable everywhere and Φ is C¹, so by the chain rule Du_k(w) = Dg_k(Φ(w))∘A(w) for every w. For w ∈ E', Du_k(w)(c(w)) = JΦ(w)·Dg_k(Φ(w))(A(w)a(w)) = JΦ(w)F_k(Φ(w)); for w ∈ Ω ∖ E', c(w) = 0 and Du_k(w)(c(w)) = 0. By step 5 (F_k ∈ L¹(Hⁿ⌞M_j)) and Lⁿ(E ∖ E') = 0, ∫_Ω Du_k(w)(c(w)) dw = ∫_E F_k(Φ(w))JΦ(w) dw = ∫_{M_j}F_k dHⁿ. (9b) Let w ∈ E', x := Φ(w) and i < n; v_i := A(w)e_i ∈ range A(w). By (a) and (c), s ↦ h(x + sv_i) has derivative ⟨G(x), v_i⟩ at s = 0. On the other hand (directional-derivative fact, Simon Ch. 2, 4.10; also the statements of the accepted lemmas lpf_ccr_hasDerivAt_line_of_comp and lpf_tde_chart_directional_deriv), since h is L-Lipschitz, Φ is differentiable at w and h∘Φ is differentiable at w by (d), s ↦ h(x + sv_i) has derivative D(h∘Φ)(w)e_i at s = 0: indeed h(x + sv_i) − h(x) = [h(Φ(w + se_i)) − h(Φ(w))] + [h(x + sA(w)e_i) − h(Φ(w + se_i))], the first bracket is s·D(h∘Φ)(w)e_i + o(s), and the second is at most L|Φ(w) + sA(w)e_i − Φ(w + se_i)| = o(s) in absolute value. By uniqueness of derivatives Du(w)e_i = ⟨G(x), A(w)e_i⟩ for every i, so by linearity Du(w)s = ⟨G(x), A(w)s⟩ for all s ∈ ℝⁿ. Hence Du(w)(c(w)) = JΦ(w)⟨G(x), A(w)a(w)⟩ = JΦ(w)F_∞(Φ(w)) for w ∈ E', and Du(w)(c(w)) = 0 for w ∈ Ω ∖ E'. By step 5, ∫_Ω Du(w)(c(w)) dw = ∫_E F_∞(Φ(w))JΦ(w) dw = ∫_{M_j}F_∞ dHⁿ.
10. (Weak-* convergence; sibling gradient_weak_star.) u_k and u are (LK)-Lipschitz on Ω (g_k and h are L-Lipschitz on ℝ^P and Φ is K-Lipschitz on Ω), sup_{w∈Ω}|u_k(w) − u(w)| ≤ sup_{ℝ^P}|g_k − h| → 0, so u_k → u uniformly on Ω, Ω is open, and c is integrable on Ω (step 8). By the sibling theorem gradient_weak_star (slicing_im_ll_gradient_weak_star) with C := LK, ∫_Ω Du_k(w)(c(w)) dw → ∫_Ω Du(w)(c(w)) dw. By step 9 this is (★_j), and by step 4 the theorem follows. ∎
(Only gradient_weak_star is a Lean dependency; the lpf lemmas named above are cited as statements that this proof establishes or that are classical, and the decomposition of this node may reuse the accepted ones with identical types.)

## Key steps

1. Integrands F_k = Dg_k(Y) and F_∞ = ⟨G, Y⟩ are dominated by L|Y| ∈ L¹(Hⁿ⌞M); the cases n > P and n = 0 are trivial.
2. C¹ charts (Simon Ch. 3, 1.2–1.3): Φ_j C¹, Lipschitz and antilipschitz on open Ω_j, covering M up to an Hⁿ-null set; disjointify and reduce by Tannery's theorem to one chart piece M_j.
3. Area formula on the chart; for a.e. chart point range DΦ(w) is the weighted tangent plane (Simon Ch. 3, 1.5(2), 1.6, 1.8(1)).
4. Coefficients a = (AᵀA)⁻¹AᵀY∘Φ, c = 1_{E'}JΦ·a ∈ L¹(Ω); chain rule and the directional-derivative fact (Simon Ch. 2, 4.10) give ∫_{M_j}F_k = ∫_Ω D(g_k∘Φ)(c) and ∫_{M_j}F_∞ = ∫_Ω D(h∘Φ)(c).
5. gradient_weak_star with u_k = g_k∘Φ → u = h∘Φ uniformly on Ω, all LK-Lipschitz on Ω.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read GMT/Ch06/Contract.lean (IsRectifiableTriple, tauAction, IsMeasureRepresentation) and replay its scope with verifier/gmt-compare.py contract_scope(…, 'GMT.Ch06.main_theorem')`
- `python3 scan of dag.json (458 nodes at submission): statuses/lean_statements of slicing_mb_lb_extDeriv_smul, slicing_mb_lb_smul_testForm, slicing_mb_lb_wedge_testForm (accepted), slicing_mb_sa_* (accepted), lpf_raf_chart_change_of_variables, lpf_ccr_hasDerivAt_line_of_comp, lpf_tde_chart_directional_deriv, lpf_ccr_ae_pullback, lpf_raf_chart_preimage_null (accepted), lpf_countably_rectifiable_c1_cover, lpf_weighted_tangent_on_c1_chart (speculative-ready), rectifiability_weighted_tangent_ae (accepted); collision check for slicing_im_ll_* (none)`
- `rg 'slicing_im_ll' local-references/197bdd4b88278494 and lake-packages-25730c7c/simongmt (no match)`
- `git show <candidate>:GMT/Ch06/Submission.lean for the 203 accepted candidates: 8 add Mathlib/SimonGMT imports (allowed by the comparator)`
- `grep Mathlib: LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt (Rademacher.lean), measurable_fderiv, norm_fderiv_le_of_lipschitzOn, LipschitzOnWith.extend_real, MemLp.exist_eLpNorm_sub_le (Normed/Lp/SmoothApprox.lean), exists_contDiff_support_eq_eq_one_iff, tendsto_tsum_of_dominated_convergence (Normed/Group/Tannery.lean), integral_iUnion_ae, HasCompactSupport.contDiff_convolution_left, ContDiffBump.normed/dist_normed_convolution_le, alternatizeUncurryFin_apply, norm_alternatizeUncurryFin_le, InnerProductSpace.toDual_symm_apply, Submodule.orthogonal_orthogonal, VitaliFamily.ae_tendsto_lintegral_enorm_sub_div, Besicovitch.vitaliFamily`
- `read SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt(.unique)), Chapter06/{Forms,Currents,FormsDuality}.lean (exteriorDerivative, TestFormOn, GeometricCurrentOn.boundary_apply, exteriorDerivativeTestOn, simpleNVector_apply), Chapter02/AreaLipschitz.lean (weighted_area_formula_lipschitz_injOn)`
- `sed book/chapter-06.txt Lemma 4.5 printed proof (eqs (1)–(3)); chapter-03.txt 1.1–1.6; chapter-02.txt 4.5–4.14; chapter-01.txt 3.6–3.7, 3.15, 3.23`
- `lake env lean /tmp/lleib_split/check/Stmts.lean (six child types in the exact comparator scope: no errors)`
- `lake env lean /tmp/lleib_split/check/Assembly.lean (parent type from five child types; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/lleib_split/check/C3.lean (smooth_identity from the three reused frozen types; same axioms)`
- `lake env lean /tmp/lleib_split/check/{C1,C2}.lean (full proofs of mollify and multiplier_limit; same axioms)`
- `lake env lean /tmp/lleib_split/check/C4.lean (full proof of tangent_field, type byte-identical; same axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-extderiv-leibniz-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-smul-test-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-wedge-test-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Tannery.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/lleib_split/check/Stmts.lean`
- `/tmp/lleib_split/check/Assembly.lean`
- `/tmp/lleib_split/check/C3.lean`
- `/tmp/lleib_split/check/C1.lean`
- `/tmp/lleib_split/check/C2.lean`
- `/tmp/lleib_split/check/C4.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 Contract. Child types therefore use only contract, SimonGMT and Mathlib names; all six new types elaborate in the exact comparator scope. Three accepted declarations of the slice-mass-bound branch have exactly the types the smooth Leibniz identity needs (slicing_mb_lb_extDeriv_smul, slicing_mb_lb_smul_testForm, slicing_mb_lb_wedge_testForm), so they are reused with byte-identical types. The C¹-chart cover and the C¹-chart tangent identification exist only as speculative-ready lpf nodes, so they are not reused; tangential_weak_limit proves them inside its natural proof. The chart change of variables and the directional-derivative lemmas are accepted (lpf_raf_chart_change_of_variables, lpf_ccr_hasDerivAt_line_of_comp) and are cited. Mathlib supplies Rademacher, integration by parts for Lipschitz functions, density of C_c^∞ in L¹, a smooth Urysohn function, Tannery's theorem, convolution smoothness, normalized bumps and Besicovitch differentiation. SimonGMT supplies the injective Lipschitz area formula and the uniqueness of weighted tangent planes. Neither library has a weak-convergence lemma for tangential gradients on rectifiable sets. Accepted candidates show that extra imports in Submission.lean pass the comparator. Scratch Lean checks prove: the parent type from five child types, smooth_identity from the three reused types, and mollify, multiplier_limit and tangent_field in full; all print axioms propext, Classical.choice, Quot.sound. No proposed new name occurs in the snapshot, SimonGMT or the DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
