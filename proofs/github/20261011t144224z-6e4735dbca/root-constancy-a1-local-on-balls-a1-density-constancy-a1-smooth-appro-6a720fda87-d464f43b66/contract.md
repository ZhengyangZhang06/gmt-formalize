<!-- theorem-id: gmt-ch06/root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1 -->

## Theorem `Submission.constancy_mdc_smooth_approx_identity_ae_tendsto`

Let n ∈ ℕ. There are functions ψ_k : ℝⁿ → ℝ (k ∈ ℕ) such that for every k: ψ_k is C^∞; ψ_k has compact support; spt ψ_k ⊆ B̄_{1/(k+1)}(0), where spt is the closed support (Lean: tsupport); ψ_k ≥ 0; and ∫ ψ_k dLⁿ = 1. Moreover, for every locally Lⁿ-integrable g : ℝⁿ → ℝ, (g ∗ ψ_k)(x) := ∫ g(t) ψ_k(x − t) dLⁿ(t) → g(x) as k → ∞, for Lⁿ-a.e. x ∈ ℝⁿ. Here ℝⁿ = EuclideanSpace ℝ (Fin n), Lⁿ is Lebesgue measure (volume), and (g ∗ ψ_k)(x) is Lean's convolution g (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x.

Node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2595

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.constancy_mdc_smooth_approx_identity_ae_tendsto`

```lean
∀ n : ℕ, ∃ ψ : ℕ → Eucl n → ℝ, (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k)) ∧ (∀ k, HasCompactSupport (ψ k)) ∧ (∀ k : ℕ, tsupport (ψ k) ⊆ closedBall 0 (1 / ((k : ℝ) + 1))) ∧ (∀ k y, 0 ≤ ψ k y) ∧ (∀ k, ∫ y, ψ k y ∂volume = 1) ∧ ∀ g : Eucl n → ℝ, LocallyIntegrable g volume → ∀ᵐ x ∂volume, Tendsto (fun k => convolution g (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop (𝓝 (g x))
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

- Parent DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1.smooth_approx_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Introduction to Geometric Measure Theory, Ch. 6, Theorem 2.34, printed proof p. 143: the mollifier ϕ_(σ)(x) = σ^{−n} ϕ(σ^{−1}x), with ϕ a mollifier as in §2 of Ch. 2 (printed p. 49: ϕ ∈ C_c^∞(ℝⁿ), ϕ ≥ 0, spt ϕ ⊆ B_1(0), ∫ϕ = 1). The printed proof concludes that θ_ε is constant on B_ρ(x₀) “letting σ ↓ 0”; this limiting fact is quoted in the bracket of Step 5 of the parent proof (“letting σ ↓ 0 (Lebesgue differentiation)”). Here σ = 1/(k+1). The a.e. convergence is derived from the Lebesgue differentiation theorem (Simon Ch. 1, Corollary 3.17) in its Lebesgue-point form.

Notation. ℝⁿ = Eucl n; Lⁿ = Lebesgue measure (volume); |·| is the Euclidean norm; B_s(x) = ball x s, B̄_s(x) = closedBall x s; spt = tsupport; ⨍_K f := Lⁿ(K)⁻¹ ∫_K f; (g ∗ ψ)(x) = ∫ g(t) ψ(x − t) dLⁿ(t) = convolution g ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume x.

Proof.

1. (A fixed mollifier.) B_1(0) is a neighbourhood of 0, so there is a C^∞ function h : ℝⁿ → ℝ with compact support, spt h ⊆ B_1(0), 0 ≤ h ≤ 1 and h(0) = 1 (a smooth bump function).
- h is continuous with compact support, hence integrable. Put I := ∫ h dLⁿ.
- The set {h ≠ 0} is open (h is continuous) and contains 0, so it has positive Lebesgue measure. Since h ≥ 0 is integrable, I > 0.
- If |y| ≥ 1 then y ∉ B_1(0) ⊇ spt h, so h(y) = 0.

2. (The kernels.) For k ∈ ℕ let s_k := k + 1 > 0, r_k := 1/s_k and ψ_k(y) := s_kⁿ · I⁻¹ · h(s_k y).
(a) ψ_k is C^∞: it is a constant multiple of h composed with the linear map y ↦ s_k y.
(b) If |y| ≥ r_k then |s_k y| = s_k|y| ≥ 1, so h(s_k y) = 0 and ψ_k(y) = 0. Hence {ψ_k ≠ 0} ⊆ B̄_{r_k}(0). Since this ball is closed, spt ψ_k ⊆ B̄_{r_k}(0) = B̄_{1/(k+1)}(0).
(c) spt ψ_k is a closed subset of the compact ball B̄_{r_k}(0), so ψ_k has compact support.
(d) 0 ≤ ψ_k(y) ≤ s_kⁿ I⁻¹ for every y, since 0 ≤ h ≤ 1 and I > 0.
(e) ∫ ψ_k dLⁿ = s_kⁿ I⁻¹ ∫ h(s_k y) dy = s_kⁿ I⁻¹ · s_k^{−n} ∫ h dLⁿ = 1. This uses the linear change of variables ∫ f(R y) dy = |R|^{−n} ∫ f for R ≠ 0 (the dimension of ℝⁿ is n).
(f) ψ_k is continuous with compact support, hence integrable. Since Lⁿ is invariant under translations and under y ↦ −y, for every x the function t ↦ ψ_k(x − t) is integrable and ∫ ψ_k(x − t) dt = ∫ ψ_k = 1.
(a)–(e) prove the first five assertions.

3. (Lebesgue points.) Let g be locally integrable. By the Lebesgue differentiation theorem in Lebesgue-point form, for Lⁿ-a.e. x:
 (∗) ⨍_{B̄_r(x)} |g(t) − g(x)| dt → 0 as r ↓ 0.
[Derivation from Simon 1.3.17. For each rational q, apply 3.17 to the locally integrable function |g − q|: ⨍_{B_r(x)} |g − q| → |g(x) − q| for x outside an Lⁿ-null set N_q. Let x ∉ ⋃_{q∈ℚ} N_q and q ∈ ℚ. Then ⨍_{B_r(x)} |g − g(x)| ≤ ⨍_{B_r(x)} |g − q| + |q − g(x)|, so limsup_{r↓0} ⨍_{B_r(x)} |g − g(x)| ≤ 2|g(x) − q|, which can be made arbitrarily small. Open and closed balls differ by a null sphere. Mathlib states (∗) directly as IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, since Lebesgue measure on ℝⁿ is uniformly locally doubling.]
Fix x satisfying (∗). Since r_k > 0 and r_k → 0, A_k := ⨍_{B̄_{r_k}(x)} |g(t) − g(x)| dt → 0 as k → ∞.

4. (The basic estimate.) Fix k and put K := B̄_{r_k}(x), a compact set.
(a) t ↦ g(t) ψ_k(x − t) is integrable. It vanishes off K, because ψ_k(x − t) = 0 when |x − t| ≥ r_k (2(b)). On K it is the product of g, which is integrable on the compact set K, with the bounded continuous function t ↦ ψ_k(x − t). (Mathlib: HasCompactSupport.convolutionExists_right.)
(b) By 2(f), t ↦ g(x) ψ_k(x − t) is integrable with integral g(x).
(c) Hence (g ∗ ψ_k)(x) − g(x) = ∫ g(t) ψ_k(x − t) dt − ∫ g(x) ψ_k(x − t) dt = ∫ (g(t) − g(x)) ψ_k(x − t) dt.
(d) Since ψ_k ≥ 0: |∫ (g(t) − g(x)) ψ_k(x − t) dt| ≤ ∫ |g(t) − g(x)| ψ_k(x − t) dt.
(e) If t ∉ K then |x − t| > r_k, so ψ_k(x − t) = 0 by 2(b). Hence ∫ |g(t) − g(x)| ψ_k(x − t) dt = ∫_K |g(t) − g(x)| ψ_k(x − t) dt.
(f) t ↦ |g(t) − g(x)| is integrable on K, because g is integrable on K and constants are integrable on the finite-measure set K. By 2(d), 0 ≤ |g(t) − g(x)| ψ_k(x − t) ≤ s_kⁿ I⁻¹ |g(t) − g(x)|. Hence ∫_K |g(t) − g(x)| ψ_k(x − t) dt ≤ s_kⁿ I⁻¹ ∫_K |g(t) − g(x)| dt.
(g) By the scaling of Lebesgue measure, Lⁿ(K) = r_kⁿ ω with ω := Lⁿ(B_1(0)) ∈ (0, ∞). Since s_kⁿ r_kⁿ = 1, s_kⁿ = ω/Lⁿ(K). So s_kⁿ I⁻¹ ∫_K |g(t) − g(x)| dt = I⁻¹ ω ⨍_K |g(t) − g(x)| dt = C A_k, where C := I⁻¹ ω does not depend on k or x.
Altogether, |(g ∗ ψ_k)(x) − g(x)| ≤ C A_k for every k.

5. (Conclusion.) 0 ≤ |(g ∗ ψ_k)(x) − g(x)| ≤ C A_k, and C A_k → 0 by Step 3, so (g ∗ ψ_k)(x) → g(x) as k → ∞ (squeeze). This holds for every x satisfying (∗), i.e. for Lⁿ-a.e. x. This proves the last assertion. ∎
(For n = 0 every step holds verbatim: ℝ⁰ is a point carrying the unit point mass, B_1(0) = ℝ⁰ and ω = 1.)

Formalization notes (no new mathematics). Every name is available under the frozen `import GMT.Ch06.Submission`; do NOT add any import (in particular ContDiffBump.normed and the Mathlib file BumpFunction/Convolution are NOT available):
- Step 1: exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ball_mem_nhds (0 : Eucl n) one_pos); integral_pos_iff_support_of_nonneg with Continuous.isOpen_support and IsOpen.measure_pos.
- Step 2: contDiff_const.mul (contDiff_const.mul (hhs.comp (contDiff_const_smul _))); HasCompactSupport.of_support_subset_isCompact; Measure.integral_comp_smul with finrank_euclideanSpace_fin.
- Step 3: IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hg 1, with w := fun _ => x and δ := r, using tendsto_nhdsWithin_iff and tendsto_one_div_add_atTop_nhds_zero_nat.
- Step 4: HasCompactSupport.convolutionExists_right, Integrable.comp_sub_left, integral_sub_left_eq_self, integral_sub, norm_integral_le_integral_norm, setIntegral_eq_integral_of_forall_compl_eq_zero, integral_mono_of_nonneg, integral_mul_const, setAverage_eq, Measure.addHaar_closedBall, measureReal_def.
- Step 5: squeeze_zero with tendsto_iff_norm_sub_tendsto_zero.
The following complete single-theorem proof of exactly this frozen type was compiled against the frozen Submission. It needs no new import, produces no warning, and #print axioms gives propext, Classical.choice, Quot.sound. It also passes a simulation of the leaf Git gate. It is a reference implementation; the prose proof above governs.

theorem constancy_mdc_smooth_approx_identity_ae_tendsto : <frozen type> := by
  intro n
  obtain ⟨h, hts, hhc, hhs, hrange, h0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (ball_mem_nhds (0 : Eucl n) one_pos)
  have hh0 : ∀ y, 0 ≤ h y := fun y => (hrange ⟨y, rfl⟩).1
  have hh1 : ∀ y, h y ≤ 1 := fun y => (hrange ⟨y, rfl⟩).2
  have hhcont : Continuous h := hhs.continuous
  have hhint : Integrable h volume := hhcont.integrable_of_hasCompactSupport hhc
  have hIpos : 0 < ∫ y, h y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => hh0 y) hhint]
    exact hhcont.isOpen_support.measure_pos volume ⟨0, by simp [Function.mem_support, h0]⟩
  set I := ∫ y, h y with hI
  have hzero : ∀ y : Eucl n, 1 ≤ ‖y‖ → h y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hy'
    have := hts hy'
    rw [mem_ball, dist_zero_right] at this
    linarith
  have hs : ∀ k : ℕ, (0:ℝ) < (k:ℝ) + 1 := fun k => by positivity
  set Ψ : ℕ → Eucl n → ℝ := fun k y => ((k:ℝ) + 1) ^ n * (I⁻¹ * h (((k:ℝ) + 1) • y)) with hΨ
  have hΨsmooth : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ k) := fun k =>
    contDiff_const.mul (contDiff_const.mul (hhs.comp (contDiff_const_smul _)))
  have hΨzero : ∀ (k : ℕ) (y : Eucl n), 1 / ((k:ℝ) + 1) ≤ ‖y‖ → Ψ k y = 0 := by
    intro k y hy
    have h1 : 1 ≤ ‖((k:ℝ) + 1) • y‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hs k).le]
      rw [div_le_iff₀ (hs k)] at hy
      linarith
    simp only [hΨ, hzero _ h1, mul_zero]
  have hΨsupp : ∀ k : ℕ, tsupport (Ψ k) ⊆ closedBall 0 (1 / ((k:ℝ) + 1)) := by
    intro k
    refine closure_minimal ?_ isClosed_closedBall
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    exact hy (hΨzero k y hlt.le)
  have hΨc : ∀ k, HasCompactSupport (Ψ k) := fun k =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport _).trans (hΨsupp k))
  have hΨnn : ∀ k y, 0 ≤ Ψ k y := fun k y => by
    have := hh0 (((k:ℝ) + 1) • y)
    have := (hs k).le
    have := inv_nonneg.2 hIpos.le
    simp only [hΨ]; positivity
  have hΨle : ∀ k y, Ψ k y ≤ ((k:ℝ) + 1) ^ n * I⁻¹ := fun k y => by
    simp only [hΨ]
    have hp : 0 ≤ ((k:ℝ) + 1) ^ n := by positivity
    have hIi : 0 ≤ I⁻¹ := inv_nonneg.2 hIpos.le
    have := hh1 (((k:ℝ) + 1) • y)
    calc ((k:ℝ) + 1) ^ n * (I⁻¹ * h (((k:ℝ) + 1) • y)) ≤ ((k:ℝ) + 1) ^ n * (I⁻¹ * 1) := by gcongr
      _ = _ := by ring
  have hΨint : ∀ k, Integrable (Ψ k) volume := fun k =>
    (hΨsmooth k).continuous.integrable_of_hasCompactSupport (hΨc k)
  have hΨone : ∀ k, ∫ y, Ψ k y = 1 := by
    intro k
    simp only [hΨ]
    rw [integral_const_mul, integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin]
    rw [smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < (((k:ℝ) + 1) ^ n)⁻¹), ← hI]
    field_simp
  refine ⟨Ψ, hΨsmooth, hΨc, hΨsupp, hΨnn, hΨone, ?_⟩
  intro g hg
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Eucl n)) hg 1
  filter_upwards [hleb] with x hx
  set r : ℕ → ℝ := fun k => 1 / ((k:ℝ) + 1) with hr
  have hrpos : ∀ k, 0 < r k := fun k => by simp only [hr]; positivity
  have hrlim : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => hrpos k⟩
  have havg := hx (fun _ => x) r hrlim (Eventually.of_forall fun k => by
    rw [one_mul]; exact mem_closedBall_self (hrpos k).le)
  set ω := (volume : Measure (Eucl n)).real (ball 0 1) with hω
  have hωpos : 0 < ω := by
    rw [hω, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  set C := I⁻¹ * ω with hC
  have hbound : ∀ k, ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖ ≤
      C * ⨍ y in closedBall x (r k), ‖g y - g x‖ := by
    intro k
    set K := closedBall x (r k) with hK
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hconv : Integrable (fun t => g t * Ψ k (x - t)) volume := by
      have := (hΨc k).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hg
        (hΨsmooth k).continuous x
      simpa [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using this
    have hconst : Integrable (fun t => g x * Ψ k (x - t)) volume :=
      ((hΨint k).comp_sub_left x).const_mul (g x)
    have hgx : g x = ∫ t, g x * Ψ k (x - t) := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun y => Ψ k y) volume x, hΨone k, mul_one]
    have hdiff : convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x =
        ∫ t, (g t - g x) * Ψ k (x - t) := by
      rw [convolution_def]
      conv_lhs => rw [hgx]
      rw [← integral_sub _ hconst]
      · congr 1; funext t; simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]; ring
      · simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hconv
    have hoff : ∀ t, t ∉ K → ‖g t - g x‖ * Ψ k (x - t) = 0 := by
      intro t ht
      rw [hK, mem_closedBall, not_le, dist_eq_norm, ← norm_neg, neg_sub] at ht
      rw [hΨzero k (x - t) ht.le, mul_zero]
    have hgK : IntegrableOn g K volume := hg.integrableOn_isCompact hKc
    have hgxK : IntegrableOn (fun t => ‖g t - g x‖) K volume :=
      (hgK.sub (integrableOn_const (hKc.measure_lt_top.ne))).norm
    calc ‖convolution g (Ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x - g x‖
        = ‖∫ t, (g t - g x) * Ψ k (x - t)‖ := by rw [hdiff]
      _ ≤ ∫ t, ‖(g t - g x) * Ψ k (x - t)‖ := norm_integral_le_integral_norm _
      _ = ∫ t, ‖g t - g x‖ * Ψ k (x - t) := by
          congr 1; funext t; rw [norm_mul, Real.norm_of_nonneg (hΨnn k _)]
      _ = ∫ t in K, ‖g t - g x‖ * Ψ k (x - t) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
      _ ≤ ∫ t in K, ‖g t - g x‖ * (((k:ℝ) + 1) ^ n * I⁻¹) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hgxK.mul_const _)
            (Eventually.of_forall fun t => ?_)
          · exact mul_nonneg (norm_nonneg _) (hΨnn k _)
          · exact mul_le_mul_of_nonneg_left (hΨle k _) (norm_nonneg _)
      _ = (∫ t in K, ‖g t - g x‖) * (((k:ℝ) + 1) ^ n * I⁻¹) := integral_mul_const _ _
      _ = C * ⨍ y in K, ‖g y - g x‖ := by
          rw [setAverage_eq, smul_eq_mul, hC]
          have hKvol : (volume : Measure (Eucl n)).real K = r k ^ n * ω := by
            rw [measureReal_def, hK, Measure.addHaar_closedBall _ _ (hrpos k).le,
              finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
              hω, measureReal_def]
          rw [hKvol]
          simp only [hr]
          field_simp
          rw [mul_assoc, ← mul_pow, mul_one_div_cancel (hs k).ne', one_pow, mul_one]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  simpa using havg.const_mul C

## Key steps

1. Choose a smooth bump h with 0 ≤ h ≤ 1, h(0) = 1 and spt h ⊆ B_1(0); then I = ∫h > 0.
2. Define ψ_k(y) = (k+1)ⁿ I⁻¹ h((k+1)y). It is C^∞, vanishes for |y| ≥ 1/(k+1) (so spt ψ_k ⊆ B̄_{1/(k+1)}(0) and ψ_k has compact support), satisfies 0 ≤ ψ_k ≤ (k+1)ⁿ I⁻¹, and has ∫ψ_k = 1 by a linear change of variables.
3. Lebesgue points: for a.e. x, ⨍_{B̄_r(x)} |g − g(x)| → 0 as r ↓ 0 (IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub; Simon 1.3.17).
4. |(g ∗ ψ_k)(x) − g(x)| = |∫ (g(t) − g(x)) ψ_k(x − t) dt| ≤ (k+1)ⁿ I⁻¹ ∫_{B̄_{1/(k+1)}(x)} |g − g(x)| = I⁻¹ Lⁿ(B_1(0)) ⨍_{B̄_{1/(k+1)}(x)} |g − g(x)|.
5. By the squeeze theorem, (g ∗ ψ_k)(x) → g(x) for a.e. x.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); ls project/GMT/Ch06 in the snapshot`
- `rg -n 'theorem ae_tendsto_average_norm_sub|theorem exists_contDiff_tsupport_subset|theorem integral_comp_smul |theorem addHaar_closedBall |theorem _root_.HasCompactSupport.convolutionExists_right|theorem _root_.HasCompactSupport.hasFDerivAt_convolution_right|theorem convolution_precompR_apply|theorem integral_pos_iff_support_of_nonneg|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem exists_mem_of_measure_ne_zero_of_ae|theorem tsupport_fderiv_apply_subset|theorem support_convolution_subset' mathlib/Mathlib`
- `rg -n 'integral_div_left_eq_self|integral_sub_left_eq_self' mathlib/Mathlib/MeasureTheory/Group/Integral.lean; rg -n 'isUnifLocDoublingMeasure' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|ae_convolution_tendsto_right_of_locallyIntegrable|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem _root_.IsOpen.is_const_of_fderiv_eq_zero' mathlib/Mathlib`
- `rg -n 'ae_eq_const_of_weak|DistributionalConstancy|constancy_mdc' project (no match)`
- `grep -n 'theorem ae_eq_const_of_weak_coordinate_derivatives_zero' -B5 -A30 simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; sed -n 1,304p of that file (fderiv_convolution_eq_zero, constancyMollifier via ContDiffBump.normed, ae_constancyMollifier_convolution_tendsto, ae_eq_const_on_ball); grep abbrev Euclidean Chapter08/Varifold.lean`
- `lake env lean #check files after `import GMT.Ch06.Submission` (Check1–Check4.lean): unknown = Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero, ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.convolution_tendsto_right, MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero, Integrable.exists_hasCompactSupport_integral_sub_le; available = IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (instance for volume on Eucl n infers), VitaliFamily.ae_tendsto_average, exists_contDiff_tsupport_subset, Measure.integral_comp_smul, Measure.addHaar_closedBall, integral_sub_left_eq_self, Integrable.comp_sub_left, HasCompactSupport.convolutionExists_right/contDiff_convolution_left/right/hasFDerivAt_convolution_right, convolution_precompR_apply, IsOpen.is_const_of_fderiv_eq_zero, finrank_euclideanSpace_fin`
- `sed of /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py (check_source_delta), prompts.py (RLCR_LEAN_TASK: preserve imports), runtime.py (_existing_lean_name_problem, reuse); git show cdfc95d (leaf candidate rejected for adding an import)`
- `python3 -I: lean_contract.validate_lean_statement on the 3 child types and the parent type; gmt-compare.contract_scope replay; lake env lean on generated challenge modules ChallengeA/B/C.lean`
- `lake env lean /tmp/dc-split-check/{Compose,ProveAC,ProveB,EndToEnd,EndToEnd2}.lean with #print axioms; python3 -I simulation of check_source_delta on each child insertion into the frozen Submission`
- `python3 -I scan of dag.json lean_name values (453 nodes) for the 3 proposed names (no match)`
- `book sources: chapter-06-source.txt lines 569–600 (2.34 printed proof), chapter-02-source.txt lines 530–545 (mollifier ϕ_σ), chapter-01-source.txt lines 927–935 (Corollary 3.17)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/tmp/dc-split-check/ProveAC.lean`
- `/tmp/dc-split-check/ProveB.lean`
- `/tmp/dc-split-check/EndToEnd2.lean`

Snapshot pins project d8d46c95 and Mathlib 25730c7c. The frozen Submission.lean is byte-identical to Contract.lean.

Not available under the frozen `import GMT.Ch06.Submission`:
- the SimonGMT weak-constancy lemma ae_eq_const_of_weak_coordinate_derivatives_zero (DistributionalConstancy.lean:294), which the supplied Step 5 cites;
- ContDiffBump.normed;
- ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:103);
- ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:186).
The leaf gate forbids adding the import: check_source_delta rejects import, set_option and extra declarations, and commit cdfc95d shows an import-adding leaf rejected.

Available, and enough for an in-closure proof:
- Lebesgue points: IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (DensityTheorem.lean:150), with instance isUnifLocDoublingMeasureOfIsAddHaarMeasure (EqHaar.lean:550);
- exists_contDiff_tsupport_subset (FiniteDimension.lean:45);
- Measure.integral_comp_smul (Haar/NormedSpace.lean:92) and Measure.addHaar_closedBall (EqHaar.lean:500);
- integral_sub_left_eq_self, the additive form of Group/Integral.lean:163;
- the convolution API: convolutionExists_right (Convolution.lean:316), support_convolution_subset (:670), convolution_precompR_apply (:970), hasFDerivAt_convolution_right (ContDiff/Convolution.lean:61), contDiff_convolution_right/left (:420, :427);
- IsOpen.is_const_of_fderiv_eq_zero (MeanValue.lean:617).
The SimonGMT proof (fderiv_convolution_eq_zero, ae_eq_const_on_ball) served as the model for weak_constancy_ball.

Results:
- The 3 child types validate and elaborate in the comparator scope.
- Each child has a complete single-theorem Lean proof that compiles warning-free with no new import and passes the leaf-gate simulation.
- An end-to-end file proves the parent's exact frozen type from the children, with axioms propext, Classical.choice, Quot.sound only.
- The proposed names collide with nothing in the DAG (453 nodes), the project snapshot or simongmt.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
