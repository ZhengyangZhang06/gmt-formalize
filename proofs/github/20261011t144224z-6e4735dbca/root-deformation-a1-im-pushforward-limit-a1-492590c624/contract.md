<!-- theorem-id: gmt-ch06/root.deformation-a1.im_pushforward_limit-a1 -->

## Theorem `Submission.deformation_im_pushforward_limit`

Lipschitz push-forward of an integer multiplicity current as the limit of C¹ push-forwards (the consistency step A3 behind the printed remark after display (21) of the proof of 5.1), conditional on Lemma 3.9. Assume LipschitzPushforwardIntegerMultiplicity. Let P, Q, k ∈ ℕ, X ∈ D_k(ℝ^P) with X(ω) = tauAction k M θ ξ ω for all ω, where IsRectifiableTriple univ k M θ ξ and θ is natural-valued on M, and let g : ℝ^P → ℝ^Q be Λ-Lipschitz with g⁻¹(K) ∩ spt X compact for every compact K. Then there is an integer multiplicity S ∈ D_k(ℝ^Q) with IsLipschitzPushforward X g S such that, for every sequence (g_j) of C¹ maps ℝ^P → ℝ^Q that are Λ′-Lipschitz for a common Λ′ and converge uniformly to g, and every test form ω on ℝ^Q, ∫_M θ(x)·⟨ω(g_j(x)), Dg_j(x)_#ξ(x)⟩ dH^k(x) → S(ω) (the integrand written as θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) (ω (gj j x))).

Node: `root.deformation-a1.im_pushforward_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/691, https://github.com/ZhengyangZhang06/gmt-formalize/issues/728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/735, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1073, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2451, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1365, https://github.com/ZhengyangZhang06/gmt-formalize/issues/720, https://github.com/ZhengyangZhang06/gmt-formalize/issues/847, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4382, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4388, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4399

## Lean problem

Declaration: `Submission.deformation_im_pushforward_limit`

```lean
LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) k) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k), IsRectifiableTriple (univ : Set (Eucl P)) k M θ ξ → (∀ x ∈ M, ∃ j : ℕ, θ x = j) → (∀ ω : TestFormOn (univ : Set (Eucl P)) k, X ω = tauAction k M θ ξ ω) → ∀ (g : Eucl P → Eucl Q) (Λ : ℝ≥0), LipschitzWith Λ g → (∀ K : Set (Eucl Q), IsCompact K → IsCompact (g ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn (univ : Set (Eucl Q)) k, IsLipschitzPushforward X g S ∧ IsIntegerMultiplicity S ∧ ∀ (gj : ℕ → Eucl P → Eucl Q) (Λ' : ℝ≥0), (∀ j, ContDiff ℝ 1 (gj j)) → (∀ j, LipschitzWith Λ' (gj j)) → TendstoUniformly gj g atTop → ∀ ω : TestFormOn (univ : Set (Eucl Q)) k, Tendsto (fun j => ∫ x in M, θ x * nVectorPushforward k (fderiv ℝ (gj j) x) (ξ x) ((ω : DifferentialForm (Eucl Q) k) (gj j x)) ∂(μHE[k] : Measure (Eucl P))) atTop (𝓝 (S ω))
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
- Child DAG node: `root.deformation-a1.im_pushforward_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the consistency step behind Simon's printed remark “Q, R₁ are integer multiplicity by (19), 4.4, 4.5 and 3.13” in the proof of the Deformation Theorem (Ch. 6, §5, p. 166), i.e. A3 of the parent proof (parts (I) and (II)), copied below with the mollified maps g_ε = ϕ_ε * g of the parent replaced by an arbitrary sequence (g_j) of C¹ maps with a common Lipschitz bound converging uniformly to g (the argument of (I) uses only these properties of g_ε). The tools are Simon Ch. 3, §§1–2 (approximate tangent spaces, tangential differential d^Mg, C¹ decomposition of rectifiable sets, Lemma 1.2, Remarks 1.3, 1.5, 1.8), Ch. 2, 3.4 (area formula for injective C¹ maps), Ch. 1, 3.6 (Upper Density Theorem) and Lemma 3.9 of Ch. 6 in the form of the premise LipschitzPushforwardIntegerMultiplicity.

Setting. Write D := P, D′ := Q, H^k = μHE[k]. Assume the premise LipschitzPushforwardIntegerMultiplicity. Let X ∈ D_k(ℝ^D) (GeometricCurrentOn univ k), (M, θ, ξ) with IsRectifiableTriple univ k M θ ξ, θ(x) ∈ ℕ for x ∈ M (hence θ ≥ 1 on M, as θ > 0), and X(ω) = tauAction k M θ ξ ω for all ω, so X = τ(M,θ,ξ) is integer multiplicity. Let g : ℝ^D → ℝ^{D′} be Λ-Lipschitz with g⁻¹(K) ∩ spt X compact for every compact K. For the definition of S below let L(x) := d^Mg_x∘π_{T_xM}, where T_xM is the weighted approximate tangent space of (M,θ) at x and d^Mg_x the tangential differential of Simon Ch. 3, §2 (both defined H^k-a.e. on M; ‖L(x)‖ ≤ Λ), and S(ω) := ∫_Mθ⟨ω(g(x)), L(x)_#ξ(x)⟩dH^k for ω ∈ D^k(ℝ^{D′}). Let (g_j) be any sequence with g_j C¹, Λ′-Lipschitz, and g_j → g uniformly on ℝ^D, and F_j(x) := θ(x)⟨ω(g_j(x)), Dg_j(x)_#ξ(x)⟩ the integrand of the statement. We prove: (I) for every ω, ∫_MF_j dH^k → S(ω); (II) S(ω) = S̃(ω) for all ω, where S̃ is an integer multiplicity current with IsLipschitzPushforward X g S̃ supplied by the premise. Then S̃ is the current required by the statement. Degenerate dimensions: if k > D then μHE[k] = 0 on ℝ^D, X = 0 and every integral vanishes; if k > D′ every k-covector on ℝ^{D′} vanishes, so ω = 0; in both cases (I) and (II) hold trivially (all quantities are 0); for k = 0 see the end of (g); D = 0 or D′ = 0 need no change.

Conventions (stated here so that this proof is self-contained). For an ambient dimension D, e₁,…,e_D is the standard basis of ℝ^D, I(k,D) the set of strictly increasing multi-indices γ = (γ₁ < ⋯ < γ_k) in {1,…,D}, e_γ := (e_{γ₁},…,e_{γ_k}) and dx^γ := dx^{γ₁}∧⋯∧dx^{γ_k}. For a k-covector α (`Covector (Eucl D) k`), |α| := (Σ_γ α(e_γ)²)^{1/2} (`covectorEuclideanNorm`); for a k-form ω, ‖ω‖ := sup_x |ω(x)|; for a k-vector w (`NVector (Eucl D) k`, a linear functional on k-covectors), ⟨α, w⟩ := w(α), w^γ := w(dx^γ) and |w| := (Σ_γ (w^γ)²)^{1/2}; ‖A‖ is the operator norm of a linear map A. Coordinate fact: every k-covector satisfies α = Σ_γ α(e_γ)dx^γ (an alternating k-linear map is determined by its values on increasing tuples of basis vectors, and dx^γ(e_δ) = δ_{γδ}); hence w(α) = Σ_γ α(e_γ)w^γ and |w(α)| ≤ |α|·|w| (Cauchy–Schwarz). Push-forward of k-vectors: for a linear map A : ℝ^D → ℝ^{D′}, A_# = Λ_kA := `nVectorPushforward k A` is characterized by ⟨α, A_#w⟩ = ⟨A^#α, w⟩ with A^#α := α(A·,…,A·) (Simon 1.8–1.9); it is linear and A_#(simpleNVector τ) = simpleNVector(Aτ₁,…,Aτ_k) (Simon 1.10; SimonGMT `nVectorPushforward_simple`). Unit fact: if τ₁,…,τ_k ∈ ℝ^D are orthonormal then |simpleNVector τ| = 1, because its coordinates (simpleNVector τ)^γ = det(τ_i·e_{γ_j}) are the k×k minors of the D×k matrix with columns τ₁,…,τ_k and, by the Cauchy–Binet formula, Σ_γ det(τ_i·e_{γ_j})² = det(τ_i·τ_j) = 1; consequently, whenever `IsRectifiableTriple U k M θ ξ` holds, |ξ| = 1 H^k-a.e. on M (orientation clause). Mass M = `mass`, spt = `support`. Norm of push-forwards: |Λ_kA w| ≤ ‖A‖^k|w| for a linear map A and a k-vector w (the singular values of Λ_kA are products of k singular values of A); hence |⟨α, A_#w⟩| ≤ |α|‖A‖^k|w|.

Proof of (I): ∫_M F_j dH^k → S(ω). Fix ω ∈ D^k(ℝ^{D′}) and the sequence (g_j); put δ_j := sup_x |g_j(x) − g(x)| (→ 0 by uniform convergence) and Λ″ := max{Λ, Λ′}.
 (a) (A fixed compact target neighbourhood.) Let K₀ := tsupport ω and K := {y : dist(y, K₀) ≤ 1}, a compact set. Choose j₀ with δ_j ≤ 1 for j ≥ j₀; g_j is C¹ and Λ′-Lipschitz, so ‖Dg_j‖ ≤ Λ′ everywhere. For j ≥ j₀ we have: g_j(x) ∈ K₀ ⇒ g(x) ∈ K. Hence for all such j, ω(g_j(x)) = 0 unless x ∈ g⁻¹(K), and likewise ω(g(x)) = 0 unless x ∈ g⁻¹(K).
 (b) (The contributing source points lie in one compact set.) K″ := g⁻¹(K) ∩ spt X is compact (properness of g|spt X). Moreover H^k(M ∖ spt X) = 0: X(φ) = 0 for every test form φ supported in the open set ℝ^D ∖ spt X (tsupport φ is a compact subset of the zero region, so it is covered by finitely many relatively compact open sets on which X vanishes, and a smooth partition of unity subordinate to them splits φ into forms annihilated by X); hence, for every γ ∈ I(k,D) and every ball B_R(0), the finite signed measures B ↦ ∫_{B∩M}θξ^γ dH^k on the Borel subsets of the open set B_R(0) ∖ spt X vanish on C_c^∞ functions (test forms φdx^γ), therefore on C_c functions (mollification and dominated convergence), on compact sets (decreasing continuous approximations) and on all Borel sets (Dynkin's π–λ theorem); so θξ = 0 H^k-a.e. on M ∖ spt X, and since |ξ| = 1 H^k-a.e. on M (unit fact) and θ ≥ 1 on M, H^k(M ∖ spt X) = 0. Consequently, for j ≥ j₀, H^k-almost every x ∈ M at which ω(g_j(x)) ≠ 0 or ω(g(x)) ≠ 0 lies in K″.
 (c) (Integrable dominator.) For j ≥ j₀ put F_j(x) := θ(x)⟨ω(g_j(x)), Dg_j(x)_#ξ(x)⟩ = θ(x)·nVectorPushforward k (fderiv ℝ g_j x) (ξ x) (ω(g_j x)) — the integrand of the statement — and F(x) := θ(x)⟨ω(g(x)), L(x)_#ξ(x)⟩. Using |⟨α, A_#w⟩| ≤ |α|‖A‖^k|w| (Conventions), |ξ| = 1 H^k-a.e. on M, ‖Dg_j‖ ≤ Λ′, ‖L(x)‖ ≤ Λ and (a)–(b): |F_j(x)| ≤ G(x) and |F(x)| ≤ G(x) for H^k-a.e. x ∈ M, where G := ‖ω‖Λ″^kθ1_{K″}. G is H^k⌞M-integrable because K″ is compact and θ is integrable on M ∩ K″ (`integrableOn` of the triple, U = ℝ^D). F_j is H^k⌞M-measurable (g_j is C¹, θ and ξ are measurable), and F is H^k⌞M-measurable: on each chart piece G_i of (e), F∘Φ_i is given by the formula of (f) below in terms of θ∘Φ_i, the measurable coefficient c and the minors of Du (Du is Borel, as an a.e. limit of difference quotients), and Φ_i⁻¹ maps H^k-null sets to L^k-null sets (Φ_i⁻¹ is the restriction of a 1-Lipschitz affine map). Hence F_j (j ≥ j₀) and F are H^k⌞M-integrable.
 (d) (The integrals of the statement.) For j ≥ j₀ the integral in the statement equals ∫_M F_j dH^k by definition (⟨α, w⟩ = w(α); nVectorPushforward k A = A_#), and S(ω) = ∫_M F dH^k. For j < j₀ the integrals play no role (only the tail of the sequence matters for the limit).
 (e) (Chart pieces.) Write M = M₀ ∪ ⋃_{p≥1}M_p (disjoint, H^k-measurable), H^k(M₀) = 0, M_p ⊆ N_p embedded k-dimensional C¹ submanifolds (Simon Ch. 3, Lemma 1.2 and Remark 1.3, which use the C¹ approximation theorem Ch. 2, 1.5; embedded C¹ submanifolds are locally closed, hence Borel). Each point of N_p has a graph chart Φ : Ω → N_p, Ω ⊆ ℝ^k an open ball, Φ(w) = x₀ + O(w, h(w)) with O an orthogonal map and h C¹ with ‖Dh‖ ≤ 1 on Ω; then |DΦ(w)v| ≥ |v|, ‖DΦ‖ ≤ 2 and the Jacobian satisfies JΦ = det(DΦᵀDΦ)^{1/2} ≥ 1. By Lindelöf countably many such charts cover each N_p; disjointifying gives pairwise disjoint H^k-measurable sets G_i (i ∈ ℕ) with M ∖ M₀ = ⋃_iG_i and G_i ⊆ Φ_i(Ω_i) ∩ M_{p(i)}. By (c), F_j and F are H^k⌞M-integrable, so by countable additivity ∫_MF_j dH^k = Σ_ia_i(j) and S(ω) = ∫_MF dH^k = Σ_ia_i, where a_i(j) := ∫_{G_i}F_j dH^k, a_i := ∫_{G_i}F dH^k; and |a_i(j)|, |a_i| ≤ b_i := ∫_{G_i}G dH^k with Σ_ib_i = ∫_MG dH^k < ∞, for all j ≥ j₀.
 (f) (Convergence on one piece: weak continuity of minors.) Fix i; write Φ = Φ_i, Ω = Ω_i, N = N_{p(i)}, u_j := g_j∘Φ (C¹ on Ω, ‖Du_j‖ ≤ 2Λ′) and u := g∘Φ (Lipschitz on Ω; by Rademacher's theorem and the definition of d^Mg via C¹ charts, u is differentiable at Lᵏ-a.e. w ∈ Φ⁻¹(G_i) with Du(w) = d^Mg_{Φ(w)}∘DΦ(w) — only such w are used). Then |u_j − u| ≤ δ_j on Ω. For H^k-a.e. x = Φ(w) ∈ G_i, ξ(x) is a unit simple k-vector orienting T_xM = T_xN = DΦ(w)(ℝ^k) (orientation property of the triple, Ch. 3, Remark 1.5(2) and Remark 1.8(1) together with the Upper Density Theorem Ch. 1, 3.6, which identify the weighted tangent space of (M,θ) with T_xN at H^k-a.e. x ∈ M_p), so ξ(Φ(w)) = c(w)·∂₁Φ(w)∧⋯∧∂_kΦ(w) with c(w) := ⟨ξ(Φ(w)), ∂₁Φ∧⋯∧∂_kΦ⟩/|∂₁Φ∧⋯∧∂_kΦ|² measurable and |c(w)| = 1/JΦ(w) (|∂₁Φ∧⋯∧∂_kΦ| = JΦ). By the chain rule Dg_j(Φ(w))∂_bΦ(w) = ∂_bu_j(w), hence Dg_j(x)_#ξ(x) = c(w)·∂₁u_j(w)∧⋯∧∂_ku_j(w), whose coordinates are the k×k minors M_γ(Du_j(w)) (γ ∈ I(k,D′)); likewise L(x)_#ξ(x) = c(w)·∂₁u(w)∧⋯∧∂_ku(w) at a.e. w. By the area formula for the injective C¹ map Φ (change of variables, Simon Ch. 2, 3.4) and (a)–(b) (which allow inserting 1_{K″}), for j ≥ j₀:
 a_i(j) = Σ_γ∫_Ωψ(w)·ω_γ(u_j(w))·M_γ(Du_j(w)) dw,  a_i = Σ_γ∫_Ωψ(w)·ω_γ(u(w))·M_γ(Du(w)) dw,
 where ω_γ := ω(e_γ) and ψ(w) := 1_{Φ⁻¹(G_i∩K″)}(w)·θ(Φ(w))·c(w)·JΦ(w). Here |ψ| = θ∘Φ·1_{Φ⁻¹(G_i∩K″)}, so ∫_Ω|ψ|dw ≤ ∫_{Φ⁻¹(G_i∩K″)}θ(Φ(w))JΦ(w)dw = ∫_{G_i∩K″}θ dH^k < ∞ (JΦ ≥ 1): ψ ∈ L¹(Ω).
 Weak continuity of minors. Claim: if v_j, v : Ω → ℝ^{D′} are Lipschitz, sup_j‖Dv_j‖_∞ < ∞ and v_j → v uniformly, then every r×r minor M(Dv_j) (rows a₁,…,a_r, columns b₁,…,b_r) converges to M(Dv) weakly-* in L^∞(Ω), i.e. ∫ηM(Dv_j) → ∫ηM(Dv) for every η ∈ L¹(Ω). Proof by induction on r. Since the minors are bounded in L^∞ uniformly in j and C_c^∞(Ω) is dense in L¹(Ω), it suffices to take η = φ ∈ C_c^∞(Ω). r = 1: ∫φ∂_bv_j^a = −∫v_j^a∂_bφ → −∫v^a∂_bφ = ∫φ∂_bv^a. r ≥ 2: let C_q (q = 1,…,r) be the cofactors of the first row, i.e. ± the (r−1)×(r−1) minors with rows a₂,…,a_r and columns {b₁,…,b_r}∖{b_q}. For smooth maps the Piola identity Σ_q∂_{b_q}C_q = 0 holds (the second derivatives cancel in pairs by symmetry), so M(Dv) = Σ_q∂_{b_q}v^{a₁}C_q = Σ_q∂_{b_q}(v^{a₁}C_q); for Lipschitz maps this identity holds in the sense of distributions (mollify v: v^δ → v locally uniformly, Dv^δ → Dv a.e. and boundedly, so all products converge in L¹_loc). Hence ∫φM(Dv_j) = −Σ_q∫v_j^{a₁}C_q(Dv_j)∂_{b_q}φ. Now ∫v_j^{a₁}C_q(Dv_j)∂_{b_q}φ − ∫v^{a₁}C_q(Dv)∂_{b_q}φ = ∫(v_j^{a₁} − v^{a₁})C_q(Dv_j)∂_{b_q}φ + ∫v^{a₁}(C_q(Dv_j) − C_q(Dv))∂_{b_q}φ → 0 (the first term by uniform convergence and the L^∞ bound, the second by the induction hypothesis tested against v^{a₁}∂_{b_q}φ ∈ L¹). So ∫φM(Dv_j) → −Σ_q∫v^{a₁}C_q(Dv)∂_{b_q}φ = ∫φM(Dv).
 Apply this with v_j := u_j, v := u, r = k. Then ∫ψ(ω_γ∘u_j)M_γ(Du_j) − ∫ψ(ω_γ∘u)M_γ(Du) = ∫ψ(ω_γ∘u_j − ω_γ∘u)M_γ(Du_j) + ∫ψ(ω_γ∘u)(M_γ(Du_j) − M_γ(Du)) → 0: the first term is ≤ ‖ψ‖_{L¹}·sup_Ω|ω_γ∘u_j − ω_γ∘u|·k!(2Λ′)^k → 0 (ω_γ is uniformly continuous and |u_j − u| ≤ δ_j → 0), the second → 0 by weak-* convergence tested against ψ·(ω_γ∘u) ∈ L¹(Ω). Hence a_i(j) → a_i as j → ∞.
 (g) (Summation over the pieces.) By (e), (f) and dominated convergence for series (Tannery's theorem: |a_i(j)| ≤ b_i, Σ_ib_i < ∞, a_i(j) → a_i), ∫_MF_j dH^k = Σ_ia_i(j) → Σ_ia_i = S(ω). (For k = 0, nVectorPushforward 0 A is the identity on 0-vectors, F_j(x) = θ(x)ξ(x)(ω(g_j(x))) and F(x) = θ(x)ξ(x)(ω(g(x))), and the convergence is directly dominated convergence: ω is continuous, g_j → g uniformly and |F_j| ≤ G for j ≥ j₀.)
Proof of (II): S̃ = S.
 (II.1) (The push-forward supplied by the premise.) Apply the premise `LipschitzPushforwardIntegerMultiplicity` of the statement, its ambient dimensions and degree instantiated as D, D′ and k, with U := ℝ^D, V := ℝ^{D′} (both open), T := X and f := g. Its hypotheses hold: X is integer multiplicity; g is Lipschitz, hence locally Lipschitz on U; g maps U into V; and for every compact K ⊆ V the set g⁻¹(K) ∩ spt X is compact (properness of g|spt X). It yields an integer multiplicity current S̃ ∈ D_k(ℝ^{D′}) with `IsLipschitzPushforward X g S̃`, i.e. there are M′, θ′, ξ′, L′ such that
  (II.1a) `IsRectifiableTriple univ k M′ θ′ ξ′` (U = ℝ^D): M′ is H^k-measurable and countably k-rectifiable, θ′(x) > 0 for x ∈ M′, θ′ is H^k-integrable on M′ ∩ K for every compact K, ξ′ is H^k⌞M′-measurable, and for H^k-a.e. x ∈ M′, ξ′(x) = ±simpleNVector τ′ for an orthonormal k-frame τ′ spanning a weighted approximate tangent space of (M′,θ′) at x. Nothing more is known about θ′: it is real valued, and it need not be integer valued or ≥ 1;
  (II.1b) X(ω) = ∫_{M′}θ′⟨ω, ξ′⟩dH^k for every ω ∈ D^k(ℝ^D);
  (II.1c) for H^k-a.e. x ∈ M′, every subspace Π with `HasWeightedApproximateTangentSpaceAt k M′ θ′ x Π` and every v ∈ Π, the map t ↦ g(x + tv) has derivative L′(x)v at t = 0;
  (II.1d) S̃(ω) = ∫_{M′}θ′⟨ω(g(x)), L′(x)_#ξ′(x)⟩dH^k for every ω ∈ D^k(ℝ^{D′}).
 It suffices to prove S̃(ω) = S(ω) for every test form ω: then, by (I), ∫_MF_j dH^k → S̃(ω) for every admissible sequence (g_j) and every ω, while IsLipschitzPushforward X g S̃ and IsIntegerMultiplicity S̃ hold by (II.1); so S̃ is the current required by the statement. Steps (II.2)–(II.7) compare the two representations (M,θ,ξ) (from `IsIntegerMultiplicity X`) and (M′,θ′,ξ′) (from (II.1a)–(II.1b)) of X; of θ′ only its positivity on M′ and its integrability on compact sets are used.
 (II.2) (Unit orienting k-vectors.) By the unit fact of the Conventions, |ξ| = 1 H^k-a.e. on M and |ξ′| = 1 H^k-a.e. on M′.
 (II.3) (The two vector measures agree on bounded Borel sets.) For γ ∈ I(k,D) and bounded Borel B ⊆ ℝ^D put Ξ^γ(B) := ∫_{B∩M}θξ^γ dH^k and Ξ′^γ(B) := ∫_{B∩M′}θ′ξ′^γ dH^k. These integrals converge absolutely (|ξ^γ| ≤ |ξ| = 1 H^k-a.e. on M and θ is integrable on M ∩ B̄; likewise for θ′, ξ′ by (II.1a)), and for each R > 0, Ξ^γ and Ξ′^γ are finite signed (countably additive) measures on the Borel subsets of the open ball B_R(0). (1) For φ ∈ C_c^∞(ℝ^D) the form φdx^γ is a test form and ⟨φ(x)dx^γ, ξ(x)⟩ = φ(x)ξ^γ(x), so by the two representations of X (`IsIntegerMultiplicity X` and (II.1b)), ∫φ dΞ^γ = X(φdx^γ) = ∫φ dΞ′^γ. (2) For φ ∈ C_c(ℝ^D) the mollifications φ_ε := ϕ_ε * φ ∈ C_c^∞(ℝ^D) (0 < ε ≤ 1) converge uniformly to φ, satisfy |φ_ε| ≤ sup|φ| and are supported in the fixed compact set K := {dist(·, spt φ) ≤ 1}; dominated convergence (dominators sup|φ|·θ1_{M∩K} and sup|φ|·θ′1_{M′∩K}) gives ∫φ dΞ^γ = ∫φ dΞ′^γ. (3) For a compact set K_c ⊆ B_R(0) the functions φ_i(x) := max{0, 1 − i·dist(x, K_c)} are continuous with compact supports {dist(·, K_c) ≤ 1/i}, which lie in a fixed compact subset of B_R(0) for i ≥ i₀; 0 ≤ φ_i ≤ 1 and φ_i decreases pointwise to 1_{K_c}, so dominated convergence gives Ξ^γ(K_c) = Ξ′^γ(K_c). (4) The compact subsets of B_R(0) form a π-system generating the Borel σ-algebra of B_R(0) (every open subset of B_R(0) is a countable union of compact sets), and the Borel sets B ⊆ B_R(0) with Ξ^γ(B) = Ξ′^γ(B) form a Dynkin system: it contains B_R(0) (an increasing union of compact sets, by countable additivity) and is closed under relative complements and countable disjoint unions, Ξ^γ and Ξ′^γ being finite signed measures on B_R(0). By Dynkin's π-system theorem, Ξ^γ(B) = Ξ′^γ(B) for every Borel B ⊆ B_R(0), every R > 0 and every γ ∈ I(k,D).
 (II.4) (σ-finiteness of λ := H^k⌞(M ∪ M′), using only θ′ > 0 and the local integrability of θ′.) Let K_q := B̄_q(0) (q = 1, 2, …), compact with ⋃_qK_q = ℝ^D. Since θ is integrable on M ∩ K_q and θ′ is integrable on M′ ∩ K_q (II.1a), θ and θ′ are H^k-measurable on M ∩ K_q and M′ ∩ K_q respectively, and M, M′ are H^k-measurable; so for q, r ≥ 1 the sets
  A_{q,r} := M ∩ K_q ∩ {θ ≥ 1/r},  A′_{q,r} := M′ ∩ K_q ∩ {θ′ ≥ 1/r}
 are H^k-measurable, and by Chebyshev's (Markov's) inequality
  H^k(A′_{q,r}) ≤ r∫_{A′_{q,r}}θ′ dH^k ≤ r∫_{M′∩K_q}θ′ dH^k < ∞,  H^k(A_{q,r}) ≤ r∫_{M∩K_q}θ dH^k < ∞.
 Every x ∈ M ∪ M′ belongs to some A_{q,r} or A′_{q,r}: choose q ≥ |x|, and r ≥ 1/θ(x) if x ∈ M (θ(x) > 0), resp. r ≥ 1/θ′(x) if x ∈ M′ (θ′(x) > 0). Hence M ∪ M′ = ⋃_{q,r}(A_{q,r} ∪ A′_{q,r}) is a countable union of H^k-measurable sets of finite H^k-measure, and λ(ℝ^D ∖ (M ∪ M′)) = 0: λ is σ-finite. (No lower bound θ′ ≥ 1 is used; for the integer valued θ the sets A_{q,1} = M ∩ K_q alone would do.)
 (II.5) (Radon–Nikodym uniqueness.) The vector measures Ξ = (Ξ^γ)_γ and Ξ′ = (Ξ′^γ)_γ of (II.3) are absolutely continuous with respect to λ, with densities κ := θξ1_M and κ′ := θ′ξ′1_{M′}: Ξ^γ(B) = ∫_Bκ^γ dλ and Ξ′^γ(B) = ∫_Bκ′^γ dλ for bounded Borel B. The densities are λ-measurable (by the measurability of θ, θ′ in (II.4) and of ξ, ξ′ in the triple conditions) and λ-integrable on bounded sets (|κ| ≤ θ1_M and |κ′| ≤ θ′1_{M′} λ-a.e.). Since λ is σ-finite by (II.4) and H^k is Borel regular (Simon Ch. 1, 2.6), every λ-measurable set is the union of a Borel set and a λ-null set (Simon Ch. 1, 1.12 and 1.15(2), applied to the finite Borel regular measures H^k⌞A_{q,r} and H^k⌞A′_{q,r}, together with λ(ℝ^D ∖ (M ∪ M′)) = 0); hence κ^γ and κ′^γ agree λ-a.e. with Borel functions, and we may assume them Borel. For each q, the bounded Borel sets E_q^± := B_q(0) ∩ {±(κ^γ − κ′^γ) > 0} satisfy, by (II.3), ∫_{E_q^±}±(κ^γ − κ′^γ)dλ = ±(Ξ^γ(E_q^±) − Ξ′^γ(E_q^±)) = 0 with an integrand that is strictly positive on E_q^±, so λ(E_q^±) = 0. As {κ^γ ≠ κ′^γ} = ⋃_q(E_q^+ ∪ E_q^−), κ^γ = κ′^γ λ-a.e. for each of the finitely many γ ∈ I(k,D). This is the uniqueness of the Radon–Nikodym derivative of Ξ = Ξ′ with respect to the σ-finite measure λ: θξ1_M = θ′ξ′1_{M′} λ-a.e.
 (II.6) (Carriers, multiplicities and orientations.) Taking Euclidean lengths in (II.5) and using (II.2): θ1_M = θ′1_{M′} λ-a.e., i.e. outside an H^k-null set Z ⊆ M ∪ M′ (λ-null subsets of M ∪ M′ are H^k-null). If x ∈ M ∖ M′ then θ(x)1_M(x) = θ(x) > 0 = θ′(x)1_{M′}(x), so M ∖ M′ ⊆ Z; likewise M′ ∖ M ⊆ Z because θ′ > 0 on M′. Hence:
  • carriers: H^k(M Δ M′) = 0;
  • multiplicities: θ = θ′ H^k-a.e. on M ∩ M′;
  • orientations: dividing θξ = θ′ξ′ (valid H^k-a.e. on M ∩ M′ by (II.5)) by θ = θ′ > 0 gives ξ = ξ′ H^k-a.e. on M ∩ M′.
 (II.7) (Tangent spaces, differentials and S̃ = S.) Let Γ be the set of x ∈ M ∩ M′ such that: θ(x) = θ′(x) and ξ(x) = ξ′(x); the orientation clause of (M,θ,ξ) holds at x with an orthonormal frame τ = (τ₁,…,τ_k), i.e. ξ(x) = ±simpleNVector τ and `HasWeightedApproximateTangentSpaceAt k M θ x (span τ)`, so that T_xM = span τ (the weighted approximate tangent space is unique where θ(x) ≠ 0: SimonGMT `HasWeightedApproximateTangentSpaceAt.unique`); (II.1c) holds at x; and for every v ∈ T_xM the map t ↦ g(x + tv) has derivative d^Mg_x(v) = L(x)v at t = 0 (Simon Ch. 3, §2, p. 76; concretely, at H^k-a.e. x ∈ G_i of (e), x = Φ(w) with T_xM = DΦ(w)(ℝ^k) by (f), w a point of differentiability of u = g∘Φ, and |g(x + tDΦ(w)v) − g(Φ(w + tv))| ≤ Λ|Φ(w) + tDΦ(w)v − Φ(w + tv)| = o(t), so this derivative is Du(w)v = d^Mg_x(DΦ(w)v)). By (II.6), the a.e. clauses of the two triples, (II.1c) and (e)–(f), H^k(M ∖ Γ) = H^k(M′ ∖ Γ) = 0. Fix x ∈ Γ.
  (II.7a) (Same weighted tangent spaces.) For r > 0 the blow-up η_{x,r} := `blowUpMap x r`, η_{x,r}(y) = r⁻¹(y − x), is a bijective similarity of ratio 1/r, so H^k(η_{x,r}(Z)) = r^{−k}H^k(Z) and η_{x,r} maps H^k-null sets to H^k-null sets. Hence η_{x,r}(M) and η_{x,r}(M′) differ by the null set η_{x,r}(M Δ M′), and for φ ∈ C_c(ℝ^D) the integrands y ↦ φ(y)θ(x + ry) and y ↦ φ(y)θ′(x + ry) agree on η_{x,r}(M) outside the null set η_{x,r}({z ∈ M : z ∉ M′ or θ(z) ≠ θ′(z)}) (note x + r·η_{x,r}(z) = z). Therefore ∫_{η_{x,r}(M)}φ(y)θ(x + ry)dH^k(y) = ∫_{η_{x,r}(M′)}φ(y)θ′(x + ry)dH^k(y) for every r > 0, and since θ(x) = θ′(x) the limits required in `HasWeightedApproximateTangentSpaceAt` coincide: for every subspace Π, `HasWeightedApproximateTangentSpaceAt k M θ x Π` ⟺ `HasWeightedApproximateTangentSpaceAt k M′ θ′ x Π`. In particular T_xM = span τ is a weighted approximate tangent space of (M′,θ′) at x.
  (II.7b) (Same differentials on T_xM.) By (II.1c) with Π = span τ and v = τ_i, the map t ↦ g(x + tτ_i) has derivative L′(x)τ_i at t = 0; by the choice of Γ it also has derivative d^Mg_x(τ_i) = L(x)τ_i there. By uniqueness of derivatives, L′(x)τ_i = L(x)τ_i for i = 1,…,k.
  (II.7c) (Same pushed-forward k-vectors.) By the push-forward rule of the Conventions, L′(x)_#ξ′(x) = L′(x)_#ξ(x) = ±simpleNVector(L′(x)τ₁,…,L′(x)τ_k) = ±simpleNVector(L(x)τ₁,…,L(x)τ_k) = L(x)_#ξ(x).
 Consequently θ′(x)⟨ω(g(x)), L′(x)_#ξ′(x)⟩ = θ(x)⟨ω(g(x)), L(x)_#ξ(x)⟩ for every x ∈ Γ, i.e. the integrands of (II.1d) and of S coincide on Γ. Since M and M′ both differ from Γ by H^k-null sets, S̃(ω) = ∫_{M′}θ′⟨ω(g), L′_#ξ′⟩dH^k = ∫_Γθ⟨ω(g), L_#ξ⟩dH^k = ∫_Mθ⟨ω(g), L_#ξ⟩dH^k = S(ω) for every ω ∈ D^k(ℝ^{D′}). Thus S̃(ω) = S(ω) for every ω, which completes the proof.

## Key steps

1. Fixed compact target neighbourhood of spt ω; for large j all contributing source points lie (H^k-a.e.) in the compact set g⁻¹(K) ∩ spt X, using H^k(M ∖ spt X) = 0.
2. One integrable dominator ‖ω‖max(Λ,Λ′)^kθ1_{g⁻¹(K)∩spt X} for all integrands; measurability of the limit integrand via C¹ charts.
3. Decomposition of M into C¹ chart pieces; on each piece the integrands are ψ·(ω_γ∘u_j)·minors of Du_j by the area formula.
4. Weak-* continuity of minors of uniformly converging, uniformly Lipschitz maps (Piola identity, induction on the order) gives convergence on each piece; Tannery's theorem sums the pieces: ∫F_j → S(ω).
5. Identification S = S̃ with the integer multiplicity push-forward S̃ supplied by the premise: equal vector measures, σ-finiteness of H^k⌞(M ∪ M′) from positivity and local integrability, Radon–Nikodym uniqueness, equal weighted tangent spaces and differentials.

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

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
