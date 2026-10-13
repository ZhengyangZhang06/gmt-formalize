<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1 -->

## Theorem `Submission.slicing_im_si_cutoff_tangential_gradient`

Let P ∈ ℕ, let μ be a measure on ℝ^P, and let Tan(x, Q) be an arbitrary predicate on points x ∈ ℝ^P and linear subspaces Q ⊆ ℝ^P. Let f : ℝ^P → ℝ be L-Lipschitz (L ≥ 0), let G : ℝ^P → ℝ^P be Borel with |G(x)| ≤ L for every x, and let t ∈ ℝ and ε > 0. Assume (TG): for μ-a.e. x and every Q with Tan(x, Q), G(x) ∈ Q and, for every u ∈ Q, s ↦ f(x + su) has derivative ⟨G(x), u⟩ at s = 0. Assume also that for μ-a.e. x, f(x) = t − ε implies G(x) = 0, and that for μ-a.e. x, f(x) = t implies G(x) = 0. Put h_ε(x) := max(0, min(1, (t − f(x))/ε)) and G_ε := 1_{f⁻¹((t−ε,t))}·(−ε⁻¹G). Then there is K ≥ 0 with four properties: h_ε is K-Lipschitz; G_ε is Borel; |G_ε(x)| ≤ K for every x; and for μ-a.e. x and every Q with Tan(x, Q), G_ε(x) ∈ Q and, for every u ∈ Q, s ↦ h_ε(x + su) has derivative ⟨G_ε(x), u⟩ at s = 0.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2519

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.slicing_im_si_cutoff_tangential_gradient`

```lean
∀ (P : ℕ) (μ : Measure (Eucl P)) (Tan : Eucl P → Submodule ℝ (Eucl P) → Prop) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P) (t ε : ℝ), 0 < ε → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → (∀ᵐ x ∂μ, f x = t - ε → G x = 0) → (∀ᵐ x ∂μ, f x = t → G x = 0) → ∃ K : ℝ≥0, LipschitzWith K (fun x => max 0 (min 1 ((t - f x) / ε))) ∧ Measurable ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) ∧ (∀ x, ‖(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x‖ ≤ K) ∧ ∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → (f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => max 0 (min 1 ((t - f (x + s • u)) / ε))) (inner ℝ ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x) u) 0
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.cutoff_gradient-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 7 (Simon Ch. 6, proof of Lemma 4.5(2): the piecewise-linear cut-off ψ applied to h = ψ∘f, the chain rule (4), and the remark that ∇^M f = 0 Hⁿ-a.e. on every level set {f = c}). It is stated here for an arbitrary measure μ and an arbitrary predicate Tan. In the parent, μ = H^{m+1}⌞M, Tan x Q = HasWeightedApproximateTangentSpaceAt (m+1) M θ x Q, and the two level-set hypotheses come from the sibling coarea_null (i) with c = t − ε and c = t.

Notation. For s ∈ ℝ put ψ(s) := max(0, min(1, (t − s)/ε)), so that h_ε = ψ∘f. Put E := f⁻¹((t − ε, t)) and G_ε := 1_E·(−ε⁻¹G), i.e. G_ε(x) = −ε⁻¹G(x) for x ∈ E and G_ε(x) = 0 for x ∉ E. In Lean, h_ε is `fun x => max 0 (min 1 ((t - f x) / ε))` and G_ε is `(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)`. (TG) denotes the tangential-gradient hypothesis: for μ-a.e. x and every subspace Q with Tan x Q, G(x) ∈ Q and s ↦ f(x + su) has derivative ⟨G(x), u⟩ at 0 for every u ∈ Q.

1. (Properties of ψ.) The map s ↦ (t − s)/ε is ε⁻¹-Lipschitz, and a ↦ min(1, a) and a ↦ max(0, a) are 1-Lipschitz. Hence |ψ(a) − ψ(b)| ≤ ε⁻¹|a − b| for all a, b. Moreover:
 - ψ(s) = 1 if s ≤ t − ε, because then (t − s)/ε ≥ 1;
 - ψ(s) = (t − s)/ε if t − ε ≤ s ≤ t, because then (t − s)/ε ∈ [0, 1];
 - ψ(s) = 0 if s ≥ t, because then (t − s)/ε ≤ 0.
2. (The constant.) Put K := ε⁻¹L ≥ 0. Since f is L-Lipschitz and ψ is ε⁻¹-Lipschitz, h_ε = ψ∘f is (ε⁻¹L)-Lipschitz, i.e. K-Lipschitz.
3. (G_ε is Borel and bounded by K.) f is Lipschitz, hence continuous, so E is open and therefore Borel. The map x ↦ −ε⁻¹G(x) is Borel because G is, so G_ε = 1_E·(−ε⁻¹G) is Borel. If x ∈ E then |G_ε(x)| = ε⁻¹|G(x)| ≤ ε⁻¹L = K. If x ∉ E then |G_ε(x)| = 0 ≤ K.
4. (Good points.) Each of (TG), "f(x) = t − ε ⟹ G(x) = 0" and "f(x) = t ⟹ G(x) = 0" holds for μ-a.e. x, so all three hold at μ-a.e. x. Fix such an x, a subspace Q with Tan x Q, and u ∈ Q. By (TG), G(x) ∈ Q and φ(s) := f(x + su) has φ'(0) = ⟨G(x), u⟩. In particular φ is continuous at 0, and φ(0) = f(x).
5. (G_ε(x) ∈ Q.) If x ∈ E then G_ε(x) = −ε⁻¹G(x) ∈ Q, because Q is a linear subspace containing G(x). If x ∉ E then G_ε(x) = 0 ∈ Q.
It remains to show that s ↦ h_ε(x + su) = ψ(φ(s)) has derivative ⟨G_ε(x), u⟩ at s = 0. We split according to the position of f(x) relative to t − ε and t.
6. (Case f(x) < t − ε.) Then x ∉ E, so ⟨G_ε(x), u⟩ = ⟨0, u⟩ = 0. Since φ is continuous at 0 and φ(0) < t − ε, there is a neighbourhood of 0 on which φ(s) < t − ε. There ψ(φ(s)) = 1 by step 1. A function that is constant near 0 has derivative 0 at 0.
7. (Case f(x) = t − ε.) Then x ∉ E, so ⟨G_ε(x), u⟩ = 0. By the choice of x, G(x) = 0, so φ'(0) = ⟨0, u⟩ = 0, i.e. φ(s) − φ(0) = o(s) as s → 0. By step 1, |ψ(φ(s)) − ψ(φ(0))| ≤ ε⁻¹|φ(s) − φ(0)| = o(s). Hence ψ∘φ has derivative 0 at 0.
8. (Case t − ε < f(x) < t.) Then x ∈ E and ⟨G_ε(x), u⟩ = ⟨−ε⁻¹G(x), u⟩ = −ε⁻¹⟨G(x), u⟩. By continuity of φ at 0 there is a neighbourhood of 0 on which t − ε < φ(s) < t, and there ψ(φ(s)) = (t − φ(s))/ε by step 1. The function s ↦ (t − φ(s))/ε has derivative −φ'(0)/ε = −ε⁻¹⟨G(x), u⟩ at 0. Since ψ∘φ agrees with it near 0, ψ∘φ has the same derivative at 0.
9. (Case f(x) = t.) As in step 7, now using "f(x) = t ⟹ G(x) = 0": x ∉ E, ⟨G_ε(x), u⟩ = 0, and ψ∘φ has derivative 0 at 0.
10. (Case f(x) > t.) Then x ∉ E and ⟨G_ε(x), u⟩ = 0. Near 0 we have φ(s) > t, so ψ(φ(s)) = 0 by step 1, and the derivative at 0 is 0.
11. (Conclusion.) Steps 6–10 cover every case: compare f(x) with t − ε, and if f(x) > t − ε, compare it with t. So for μ-a.e. x, every Q with Tan x Q and every u ∈ Q: G_ε(x) ∈ Q (step 5), and s ↦ h_ε(x + su) has derivative ⟨G_ε(x), u⟩ at 0. Together with steps 2 and 3, K = ε⁻¹L satisfies all four conclusions. ∎

Formalization notes (a complete Lean proof of exactly this statement was checked in a scratch build of the frozen commit d8d46c9: written as `theorem Submission.<lean_name>` inside `namespace GMT.Ch06` of a file importing GMT.Ch06.Submission, with the comparator-form restatement `theorem _root_.X : (<lean_statement>) := by exact Submission.<lean_name>` also checked; axioms propext, Classical.choice, Quot.sound; the verified proof is appended at the end):
- K := Kψ * L with Kψ : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.2 hε.le⟩. Prove ψ Lipschitz by `LipschitzWith.of_dist_le_mul` for s ↦ (t − s)/ε, then `.const_min 1` and `.const_max 0`. Then `hψL.comp hf` gives the Lipschitz conclusion.
- Measurability: `(hG.const_smul (-ε⁻¹)).indicator (hf.continuous.measurable measurableSet_Ioo)`. Do not use `measurable_const.smul hG`: it produces a non-matching form.
- Neighbourhoods: `hd.continuousAt` with `ContinuousAt.eventually_lt` against `continuousAt_const (y := t - ε)` (resp. `y := t`), closed by `simpa`.
- Derivatives: use `HasDerivAt.congr_of_eventuallyEq` with `hasDerivAt_const`, or with `(hd.const_sub t).div_const ε` and `field_simp`. Also `real_inner_smul_left` and `inner_zero_left`.
- Edge cases: `hasDerivAt_iff_isLittleO`, `simp only [sub_zero, smul_zero]`, then `Asymptotics.IsBigO.trans_isLittleO` with `Asymptotics.IsBigO.of_bound (Kψ : ℝ)` and `hψL.dist_le_mul`. In the auxiliary statement write `fun s : ℝ => …` and `(0 : ℝ)`; otherwise ℕ is inferred.
- Case split: `lt_trichotomy (f x) (t - ε)`, then `lt_trichotomy (f x) t`.

Verified Lean proof (scratch build of d8d46c9; place it in GMT/Ch06/Submission.lean after the contract's closing `end` of the noncomputable section and before `theorem main_theorem`, inside `namespace GMT.Ch06`; it uses only the frozen imports):
```lean
theorem Submission.slicing_im_si_cutoff_tangential_gradient :
    ∀ (P : ℕ) (μ : Measure (Eucl P)) (Tan : Eucl P → Submodule ℝ (Eucl P) → Prop) (f : Eucl P → ℝ) (L : ℝ≥0) (G : Eucl P → Eucl P) (t ε : ℝ), 0 < ε → LipschitzWith L f → Measurable G → (∀ x, ‖G x‖ ≤ L) → (∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → G x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => f (x + s • u)) (inner ℝ (G x) u) 0) → (∀ᵐ x ∂μ, f x = t - ε → G x = 0) → (∀ᵐ x ∂μ, f x = t → G x = 0) → ∃ K : ℝ≥0, LipschitzWith K (fun x => max 0 (min 1 ((t - f x) / ε))) ∧ Measurable ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y)) ∧ (∀ x, ‖(f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x‖ ≤ K) ∧ ∀ᵐ x ∂μ, ∀ Q : Submodule ℝ (Eucl P), Tan x Q → (f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => max 0 (min 1 ((t - f (x + s • u)) / ε))) (inner ℝ ((f ⁻¹' Ioo (t - ε) t).indicator (fun y => (-ε⁻¹) • G y) x) u) 0 := by
  intro P μ Tan f L G t ε hε hf hG hGL hTG h1 h2
  set ψ : ℝ → ℝ := fun s => max 0 (min 1 ((t - s) / ε)) with hψdef
  set Kψ : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.2 hε.le⟩ with hKψ
  have hψL : LipschitzWith Kψ ψ := by
    have hlin : LipschitzWith Kψ (fun s : ℝ => (t - s) / ε) := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [Real.dist_eq, Real.dist_eq, show (t - a) / ε - (t - b) / ε = ε⁻¹ * (b - a) by ring,
        abs_mul, abs_of_pos (inv_pos.2 hε), abs_sub_comm]
      rfl
    exact (hlin.const_min 1).const_max 0
  have hfm : Measurable f := hf.continuous.measurable
  set E : Set (Eucl P) := f ⁻¹' Ioo (t - ε) t with hEdef
  have hE : MeasurableSet E := hfm measurableSet_Ioo
  refine ⟨Kψ * L, hψL.comp hf, (hG.const_smul (-ε⁻¹)).indicator hE, fun x => ?_, ?_⟩
  · by_cases hx : x ∈ E
    · rw [indicator_of_mem hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.2 hε)]
      simp only [hKψ]
      exact mul_le_mul_of_nonneg_left (hGL x) (inv_nonneg.2 hε.le)
    · rw [indicator_of_notMem hx, norm_zero]
      exact NNReal.coe_nonneg _
  · filter_upwards [hTG, h1, h2] with x hx hx1 hx2
    intro Q hQ
    obtain ⟨hGQ, hder⟩ := hx Q hQ
    constructor
    · by_cases hxE : x ∈ E
      · rw [indicator_of_mem hxE]; exact Q.smul_mem _ hGQ
      · rw [indicator_of_notMem hxE]; exact Q.zero_mem
    intro u hu
    have hd := hder u hu
    have hc : ContinuousAt (fun s : ℝ => f (x + s • u)) 0 := hd.continuousAt
    have hc0 : (fun s : ℝ => f (x + s • u)) 0 = f x := by simp
    -- the cut-off composed with the line
    change HasDerivAt (fun s => ψ (f (x + s • u))) _ 0
    -- at points where `G x = 0` the Lipschitz bound gives derivative `0`
    have edge : G x = 0 → HasDerivAt (fun s : ℝ => ψ (f (x + s • u))) 0 (0 : ℝ) := by
      intro hG0
      rw [hG0, inner_zero_left] at hd
      rw [hasDerivAt_iff_isLittleO] at hd ⊢
      simp only [sub_zero, smul_zero] at hd ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
      refine Asymptotics.IsBigO.of_bound (Kψ : ℝ) (Eventually.of_forall fun s => ?_)
      have := hψL.dist_le_mul (f (x + s • u)) (f (x + (0 : ℝ) • u))
      simpa [Real.dist_eq, Real.norm_eq_abs] using this
    -- case analysis on the position of `f x`
    rcases lt_trichotomy (f x) (t - ε) with hlt | heq | hgt
    · -- below the band: locally constant `1`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t - ε := by
        have := hc.eventually_lt (continuousAt_const (y := t - ε)) (by simpa using hlt)
        simpa using this
      apply (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [hev] with s hs
      have : 1 ≤ (t - f (x + s • u)) / ε := by rw [le_div_iff₀ hε]; linarith
      simp only [hψdef, min_eq_left this, max_eq_right zero_le_one]
    · -- lower edge: `G x = 0`
      have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.1]
      rw [indicator_of_notMem hxE, inner_zero_left]
      exact edge (hx1 heq)
    · rcases lt_trichotomy (f x) t with hlt' | heq' | hgt'
      · -- inside the band: affine with slope `-1/ε`
        have hxE : x ∈ E := by simp [hEdef]; exact ⟨hgt, hlt'⟩
        rw [indicator_of_mem hxE, real_inner_smul_left]
        have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), t - ε < f (x + s • u) := by
          have := (continuousAt_const (y := t - ε)).eventually_lt hc (by simpa using hgt)
          simpa using this
        have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), f (x + s • u) < t := by
          have := hc.eventually_lt (continuousAt_const (y := t)) (by simpa using hlt')
          simpa using this
        have hlin : HasDerivAt (fun s : ℝ => (t - f (x + s • u)) / ε) (-ε⁻¹ * inner ℝ (G x) u) 0 := by
          have := (hd.const_sub t).div_const ε
          convert this using 1
          field_simp
        apply hlin.congr_of_eventuallyEq
        filter_upwards [hev1, hev2] with s hs1 hs2
        have ha : (t - f (x + s • u)) / ε ≤ 1 := by rw [div_le_iff₀ hε]; linarith
        have hb : 0 ≤ (t - f (x + s • u)) / ε := div_nonneg (by linarith) hε.le
        simp only [hψdef, min_eq_right ha, max_eq_right hb]
      · -- upper edge: `G x = 0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        exact edge (hx2 heq')
      · -- above the band: locally constant `0`
        have hxE : x ∉ E := fun h => by simp [hEdef] at h; linarith [h.2]
        rw [indicator_of_notMem hxE, inner_zero_left]
        have hev : ∀ᶠ s in 𝓝 (0 : ℝ), t < f (x + s • u) := by
          have := (continuousAt_const (y := t)).eventually_lt hc (by simpa using hgt')
          simpa using this
        apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [hev] with s hs
        have : (t - f (x + s • u)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
        simp only [hψdef, max_eq_left ((min_le_right _ _).trans this)]
```

## Key steps

1. ψ(s) = max(0, min(1, (t−s)/ε)) is ε⁻¹-Lipschitz and equals 1 on s ≤ t−ε, (t−s)/ε on [t−ε, t], 0 on s ≥ t; hence h_ε = ψ∘f is (ε⁻¹L)-Lipschitz
2. G_ε = 1_{f⁻¹(t−ε,t)}·(−ε⁻¹G) is Borel (open band, Borel G) with |G_ε| ≤ ε⁻¹L
3. at μ-a.e. x, (TG) and the two level-set vanishing hypotheses hold; G_ε(x) ∈ Q since Q is a subspace containing G(x)
4. off the closed band, ψ∘φ is locally constant (derivative 0 = ⟨G_ε(x), u⟩); inside the open band ψ∘φ = (t − φ)/ε near 0, derivative −ε⁻¹⟨G(x), u⟩ = ⟨G_ε(x), u⟩
5. at f(x) ∈ {t−ε, t}, G(x) = 0 gives φ(s) − φ(0) = o(s), and the ε⁻¹-Lipschitz bound gives ψ∘φ(s) − ψ∘φ(0) = o(s), derivative 0 = ⟨G_ε(x), u⟩

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical); read Contract.lean: IsRectifiableTriple, tauAction, IsMeasureRepresentation, IsRestriction, IsSlice`
- `grep -n 'def testFormOnSubmodule|def exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|boundary_apply' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents}.lean`
- `python3 scan of dag.json: decomposition of root.slicing-a1.slice_integer_multiplicity-a1 (sibling types slicing_im_coarea, slicing_im_lipschitz_leibniz, statuses decomposing); accepted nodes matching 'f ⁻¹' {t}|HasDerivAt (fun s|max 0|𝓝[>] 0|toMeasurable|simpleNVector|innerSL|alternatizeUncurryFin|IsSlice' -> reusable slicing_mb_pointwise_cutoff_tendsto (012eb78d) and fiw_ims_tt_unit_bound (27af9b19)`
- `git show 012eb78d57e01b1e54de6b8f0e5cf786950b91c0:GMT/Ch06/Submission.lean; git show 27af9b191b732eae73e3d693d8903e52f89962ce:GMT/Ch06/Submission.lean (accepted proofs, isolated-comparator-result.json passed)`
- `grep -rn 'theorem ae_tendsto_average|ae_hasDerivAt_integral|tendsto_Icc_vitaliFamily_left' mathlib/Mathlib; read MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `lake env lean Avail*.lean: availability under `import GMT.Ch06.Submission` of LocallyIntegrable.ae_hasDerivAt_integral (unknown constant), VitaliFamily.ae_tendsto_average, Real.tendsto_Icc_vitaliFamily_left, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_congr_set, Measure.le_restrict_apply, lintegral_eq_zero_iff', integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integrable_toReal_of_lintegral_ne_top, integral_toReal, ae_lt_top', ContinuousAlternatingMap.norm_alternatizeUncurryFin_le, isBoundedBilinearMap_smulRight, Integrable.bdd_mul`
- `lake env lean /tmp/sid_split_scratch/Stmts.lean (eight child types in the exact comparator scope; #print checked)`
- `lake env lean /tmp/sid_split_scratch/Assembly.lean (parent type from child and sibling types; #print axioms)`
- `lake env lean /tmp/sid_split_scratch/Full.lean (#print axioms ParentFromUncles: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/sid_split_scratch/E2Echildren.lean (embedded child proofs verbatim + comparator-form exact; no errors, no warnings)`
- `rg 'slicing_im_si_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project (no match); grep -rn 'slicing_im_si_' simongmt/Poincare (no match); dag.json lean_name scan for slicing_im_si_* (no match among 464 nodes)`
- `sed -n 1150,1345p book/chapter-06.txt (Simon Ch. 6, 4.1, Remark 4.2, 4.4, Lemma 4.5 and its proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/OneDim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/isolated-comparator-result.json`
- `/tmp/sid_split_scratch/Stmts.lean`
- `/tmp/sid_split_scratch/Assembly.lean`
- `/tmp/sid_split_scratch/Full.lean`
- `/tmp/sid_split_scratch/E2Echildren.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission is byte-identical, so child types may use only contract, SimonGMT and Mathlib names in the comparator scope. SimonGMT provides TestFormOn (smooth, compact support, tsupport ⊆ U), exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset and GeometricCurrentOn.boundary_apply. Neither SimonGMT nor Mathlib has co-area, slicing or cut-off tangential-gradient results; the six new children isolate exactly those steps of the supplied proof (Simon Ch. 6, Remark 4.2 and proof of 4.5(2)). Mathlib's interval Lebesgue differentiation lemma is not importable from Submission, but VitaliFamily.ae_tendsto_average and Real.tendsto_Icc_vitaliFamily_left are, so the one-sided version is proved from them. Two accepted DAG declarations are reused with byte-identical types: slicing_mb_pointwise_cutoff_tendsto (Step 9) and fiw_ims_tt_unit_bound (Fact U). All eight child types elaborate in the exact comparator scope. In scratch Lean the six new children are fully proved, and the parent's frozen type follows from the children plus the two declared sibling types slicing_im_coarea and slicing_im_lipschitz_leibniz, using only propext, Classical.choice and Quot.sound. No new name collides with the snapshot, SimonGMT or the 464 DAG nodes. These checks do not cover the proofs of the two sibling dependencies, which remain their own nodes.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
