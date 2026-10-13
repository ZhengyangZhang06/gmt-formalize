<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.smooth_pushforward-a1 -->

## Theorem `Submission.iwl_smooth_pushforward`

Assume LipschitzPushforwardIntegerMultiplicity (Simon 3.9). Let U ⊆ ℝ^P, V ⊆ ℝ^Q be open, X ∈ D_{k+1}(U) integer multiplicity, and f : ℝ^P → ℝ^Q of class C^∞ with f(U) ⊆ V and f⁻¹(K) ∩ spt X compact for every compact K ⊆ V. Then there is an integer multiplicity S ∈ D_{k+1}(V) (the push-forward f_#X) such that: (1) S(ω) = X(η) whenever η ∈ D^{k+1}(U) agrees with the pull-back f^#ω on an open set containing spt X; (2) ∂S(ω) = ∂X(η) whenever ω ∈ D^k(V) and η ∈ D^k(U) agrees with f^#ω on an open set containing spt X; (3) if c ≥ 0 and ‖Df(x)‖ ≤ c for all x, then M_W(S) ≤ c^{k+1} M_{f⁻¹(W)∩U}(X) and M_W(∂S) ≤ c^k M_{f⁻¹(W)∩U}(∂X) for every W ⊆ ℝ^Q.

Node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/341

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2463, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2471, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2481, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2507, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2521

## Lean problem

Declaration: `Submission.iwl_smooth_pushforward`

```lean
LipschitzPushforwardIntegerMultiplicity → ∀ (P Q k : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V → ∀ (X : GeometricCurrentOn U (k + 1)) (f : Eucl P → Eucl Q), IsIntegerMultiplicity X → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → MapsTo f U V → (∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ X.support)) → ∃ S : GeometricCurrentOn V (k + 1), IsIntegerMultiplicity S ∧ (∀ (ω : TestFormOn V (k + 1)) (η : TestFormOn U (k + 1)), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) (k + 1)) x = ((ω : DifferentialForm (Eucl Q) (k + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S ω = X η) ∧ (∀ (ω : TestFormOn V k) (η : TestFormOn U k), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η : DifferentialForm (Eucl P) k) x = ((ω : DifferentialForm (Eucl Q) k) (f x)).compContinuousLinearMap (fderiv ℝ f x)) → S.boundary ω = X.boundary η) ∧ ∀ c : ℝ, 0 ≤ c → (∀ x, ‖fderiv ℝ f x‖ ≤ c) → ∀ W : Set (Eucl Q), S.massOn W ≤ ENNReal.ofReal (c ^ (k + 1)) * X.massOn (f ⁻¹' W ∩ U) ∧ S.boundary.massOn W ≤ ENNReal.ofReal (c ^ k) * X.boundary.massOn (f ⁻¹' W ∩ U)
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
- Child DAG node: `root.integrality_weak_limits-a1.smooth_pushforward-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (fixed for this proof). ℝ^P := Eucl P with standard orthonormal basis e_1,…,e_P. Hᵏ := μHE[k], the normalized k-dimensional Hausdorff measure (a positive constant multiple of μH[k]; it equals Lebesgue measure on a k-dimensional Euclidean space, and μHE[0] = μH[0] is the counting measure). D_k(U) := GeometricCurrentOn U k; D^k(U) := TestFormOn U k (C^∞ k-forms on ℝ^P with compact tsupport contained in U). I(k,P) := the strictly increasing maps {1,…,k} → {1,…,P}; for I ∈ I(k,P), e_I := (e_{I(1)},…,e_{I(k)}) and dx^I is the constant k-covector with dx^I(e_J) = δ_{IJ} (J ∈ I(k,P)); every k-covector is α = Σ_I α(e_I) dx^I. |α| := covectorEuclideanNorm α = (Σ_I α(e_I)²)^{1/2} (the norm used in the definition of mass), and ‖ω‖ := sup_x |ω(x)| for a form ω. For a k-vector w (an element of NVector = the dual of the k-covectors) put w^I := w(dx^I) and |w|_* := (Σ_I (w^I)²)^{1/2}; then w(α) = Σ_I α(e_I) w^I, so |w(α)| ≤ |α| |w|_* (Cauchy–Schwarz). M_W(X) := X.massOn W, M(X) := X.mass = M_U(X), spt X := X.support, X_j ⇀ X := WeaklyConvergesOn, ∂ := boundary. τ(M,θ,ξ)(ω) := tauAction = ∫_M θ ⟨ω,ξ⟩ dHᵏ with ⟨ω,ξ⟩(x) := ξ(x)(ω(x)); "i.m." := IsIntegerMultiplicity; "X⌞A" denotes a current S with IsRestriction X A S; W ⊂⊂ U := CompactlyContainedOpen W U. B_r(x), B̄_r(x) denote open and closed balls.

Source: (P3) of the parent proof (Simon Ch. 6, 2.23–2.24 for smooth maps, and 3.9 via the sibling `LipschitzPushforwardIntegerMultiplicity`), including its detailed identification of the Lipschitz push-forward with the classical smooth push-forward f_#X(ω) = X(ζ f^#ω); copied and filled in. Degree n := k + 1 ≥ 1.

Notation and facts.
- For a linear L : ℝ^P → ℝ^Q and a j-covector α on ℝ^Q, L^#α := α∘(L,…,L) (`ContinuousAlternatingMap.compContinuousLinearMap α L`); (f^#ω)(x) := Df(x)^# ω(f(x)) with Df(x) := fderiv ℝ f x.
(F1) |Y(ω)| ≤ ‖ω‖ M_W(Y) if tsupport ω ⊆ W.
(F2) (Support.) If η, η′ ∈ D^j(U) agree on an open set N ⊇ spt Y (Y ∈ D_j(U)), then Y(η) = Y(η′): K := tsupport(η − η′) ⊆ ℝ^P ∖ N is a compact subset of U ∖ spt Y, which is the union of the open sets W (closure W compact ⊆ U) on which Y vanishes; finitely many such W_1,…,W_l cover K, and with a smooth partition of unity χ_i ∈ C_c^∞(W_i), Σχ_i = 1 near K, Y(η − η′) = Σ_i Y(χ_i(η − η′)) = 0.
(F3) (Pull-back norm.) |L^#α| ≤ ‖L‖^j |α| for j-covectors α. [In the Euclidean structures on j-covectors for which {dx^I} are orthonormal, L^# is the j-th exterior power of the adjoint of L; by the singular value decomposition L = Σ_i σ_i u_i⊗v_i (orthonormal u, v), Λ^j is diagonal in the bases {v_I}, {u_I} with entries ∏_{i∈I}σ_i ≤ ‖L‖^j.]
(F4) (Naturality.) For C^∞ f and a smooth j-form ω on ℝ^Q, d(f^#ω) = f^#(dω) (chain rule and symmetry of second derivatives; standard).
(F5) (Compatible test forms exist.) For ω ∈ D^j(V), K_ω := spt X ∩ f⁻¹(tsupport ω) is compact (properness hypothesis); take ζ ∈ C_c^∞(U), 0 ≤ ζ ≤ 1, ζ = 1 on an open O ⊇ K_ω; then η := ζ·f^#ω ∈ D^j(U) and η = f^#ω on the open set N := O ∪ f⁻¹(ℝ^Q ∖ tsupport ω) ⊇ spt X, with tsupport η ⊆ tsupport ζ ∩ f⁻¹(tsupport ω).

Proof.
1. (The sibling push-forward.) f is C^∞, hence locally Lipschitz on U; f maps U into V; X is i.m.; and f⁻¹(K) ∩ spt X is compact for compact K ⊆ V. By the hypothesis `LipschitzPushforwardIntegerMultiplicity` there is an i.m. S ∈ D_n(V) with IsLipschitzPushforward X f S: there are a rectifiable triple (M,θ,ξ) in U (θ > 0 real and integrable on compact subsets of U — not necessarily integer valued or ≥ 1) with X = τ(M,θ,ξ), and linear maps L(x) such that for Hⁿ-a.e. x ∈ M, every weighted tangent space T of (M,θ) at x and every v ∈ T, the derivative of t ↦ f(x + tv) at 0 is L(x)v; and S(ω) = ∫_M θ ⟨ω(f(x)), L(x)_#ξ(x)⟩ dHⁿ for ω ∈ D^n(V) (L(x)_# = nVectorPushforward n (L x)).
2. (L(x) = Df(x) on the tangent plane.) For Hⁿ-a.e. x ∈ M the orients property gives an orthonormal τ spanning a weighted tangent space T_x with ξ(x) = ±simpleNVector τ. For v = τ_i ∈ T_x, t ↦ f(x + tv) has derivative Df(x)τ_i at 0 (f is differentiable), so L(x)τ_i = Df(x)τ_i by uniqueness of derivatives. Hence (`nVectorPushforward_simple`) L(x)_#ξ(x) = ±simpleNVector(L(x)∘τ) = ±simpleNVector(Df(x)∘τ) = Df(x)_#ξ(x), and by duality (nVectorPushforward is precomposition with the covector pull-back, (1.9)) ⟨ω(f(x)), Df(x)_#ξ(x)⟩ = ⟨(f^#ω)(x), ξ(x)⟩. Therefore
   S(ω) = ∫_M θ ⟨(f^#ω)(x), ξ(x)⟩ dHⁿ(x) for all ω ∈ D^n(V).
3. (Hⁿ(M ∖ spt X) = 0.) Let O′ := U ∖ spt X (open). By (F2) (with η′ = 0), X vanishes on every test form supported in O′. The coefficient measures θξ^I Hⁿ⌞M (locally finite total variation on U: |ξ^I| ≤ |ξ|_* = 1 a.e. since ξ = ±simpleNVector τ with τ orthonormal (Cauchy–Binet), and θ is integrable on compacts) thus annihilate every φ ∈ C_c^∞(O′) (test X with φ dx^I), hence every φ ∈ C_c(O′) (uniform approximation with supports in a fixed compact subset of O′, dominated convergence), hence they vanish on Borel subsets of O′ (Riesz uniqueness for locally finite signed measures on O′, via Jordan decompositions). So θξ = 0 Hⁿ-a.e. on M ∩ O′; since θ > 0 on M and |ξ|_* = 1 a.e. on M, Hⁿ(M ∩ O′) = 0.
4. (Formula for S.) Let ω ∈ D^n(V) and η ∈ D^n(U) with η = f^#ω on an open N ⊇ spt X. By step 2, S(ω) = ∫_M θ⟨f^#ω, ξ⟩ dHⁿ, and X(η) = ∫_M θ⟨η, ξ⟩ dHⁿ. The integrands coincide on M ∩ N ⊇ M ∩ spt X, and M ∖ spt X is Hⁿ-null (step 3). [Both are integrable: on M ∩ spt X the first integrand vanishes off the compact set K_ω of (F5) and is bounded there by (sup_{K_ω}‖Df‖)^n ‖ω‖ θ.] Hence S(ω) = X(η).
5. (Formula for ∂S.) Let ω ∈ D^k(V) and η ∈ D^k(U) with η = f^#ω on an open N ⊇ spt X. Since d is local, dη = d(f^#ω) = f^#(dω) on N (F4). By (F5) choose η′ ∈ D^n(U) with η′ = f^#(dω) on an open N′ ⊇ spt X. Then ∂S(ω) = S(dω) = X(η′) by step 4, and X(η′) = X(dη) by (F2) (η′ and dη agree on N ∩ N′ ⊇ spt X). Hence ∂S(ω) = X(dη) = ∂X(η).
6. (Mass bounds.) Let c ≥ 0 with ‖Df(x)‖ ≤ c for all x, and W ⊆ ℝ^Q. Let ω ∈ D^n(V) be admissible for M_W(S) (tsupport ω ⊆ W, |ω| ≤ 1) and let η := ζ f^#ω be as in (F5). Then tsupport η ⊆ U ∩ f⁻¹(W) and |η(x)| ≤ |Df(x)^#ω(f(x))| ≤ cⁿ by (F3). By step 4 and (F1), S(ω) = X(η) ≤ cⁿ M_{f⁻¹(W)∩U}(X) (if c = 0 then η = 0 since n ≥ 1, and S(ω) = 0). Taking the supremum over ω: M_W(S) ≤ ofReal(c^{k+1}) · M_{f⁻¹(W)∩U}(X) (the case c = 0 gives M_W(S) = 0, so the ENNReal convention 0·∞ = 0 is harmless). Likewise, for admissible ω ∈ D^k(V) and η := ζ f^#ω, step 5 gives ∂S(ω) = ∂X(η) with |η| ≤ c^k and tsupport η ⊆ U ∩ f⁻¹(W), so M_W(∂S) ≤ ofReal(c^k) · M_{f⁻¹(W)∩U}(∂X) (for k ≥ 1 and c = 0, η = 0 and ∂S(ω) = 0; for k = 0, c^0 = 1 and |η| = |ζ ω∘f| ≤ 1).
7. Steps 1, 4, 5, 6 give all assertions, with S integer multiplicity by step 1. ∎

## Key steps

1. The sibling Lipschitz push-forward gives an integer multiplicity S defined by the 3.6 formula over a rectifiable representation of X.
2. For smooth f the linear maps L(x) equal Df(x) on the weighted tangent planes a.e., so S(ω) = ∫θ⟨f^#ω, ξ⟩dHⁿ.
3. Hⁿ(M ∖ spt X) = 0 because the vector measure θξHⁿ⌞M vanishes off spt X.
4. Hence S(ω) = X(η) for every η agreeing with f^#ω near spt X; ∂S = f_#∂X by naturality of d.
5. Mass bounds from |L^#α| ≤ ‖L‖^j|α| for the Euclidean coefficient norm.

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
