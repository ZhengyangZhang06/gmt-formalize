<!-- theorem-id: gmt-ch06/root.constancy-a1.local_on_balls-a1.scalar_reduction-a1 -->

## Theorem `Submission.constancy_topForm_scalar_reduction`

Let m ∈ ℕ, n := m + 1, U ⊆ ℝⁿ an arbitrary set and T ∈ D_n(U) (Lean: T : GeometricCurrentOn U (m + 1), a linear functional on the test n-forms Dⁿ(U) = TestFormOn U (m + 1) satisfying the continuity axiom GeometricCurrentOn.continuous': T(ω_k) → 0 whenever ω_k → 0 in the sense of TestFormOnConverges). Call b : ℝⁿ → ℝ admissible if b is C^∞, has compact support and spt b ⊆ U (spt g denotes the closed support of g, the closure of {g ≠ 0}; Lean: tsupport g). Let e = (e_1,…,e_n) be the standard basis of ℝⁿ (e_i = EuclideanSpace.single i 1). Then there is a function u : (ℝⁿ → ℝ) → ℝ such that: (i) T(ω) = u(x ↦ ω(x)(e_1,…,e_n)) for every ω ∈ Dⁿ(U); (ii) for every admissible b there is ω ∈ Dⁿ(U) with ω(x)(e_1,…,e_n) = b(x) for all x ∈ ℝⁿ; (iii) u(a + b) = u(a) + u(b) for all admissible a, b; (iv) u(c·a) = c·u(a) for all c ∈ ℝ and admissible a; (v) whenever K ⊆ U is compact, a_k (k ∈ ℕ) and b are C^∞ functions ℝⁿ → ℝ with spt a_k ⊆ K for all k and spt b ⊆ K, and for every q ∈ ℕ, D^q a_k → D^q b uniformly on ℝⁿ, then u(a_k) → u(b).

Node: `root.constancy-a1.local_on_balls-a1.scalar_reduction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/968

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.constancy_topForm_scalar_reduction`

```lean
∀ (m : ℕ) (U : Set (Eucl (m + 1))) (T : GeometricCurrentOn U (m + 1)), ∃ u : (Eucl (m + 1) → ℝ) → ℝ, (∀ ω : TestFormOn U (m + 1), T ω = u (fun x => (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)))) ∧ (∀ b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∃ ω : TestFormOn U (m + 1), ∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) = b x) ∧ (∀ a b : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → u (a + b) = u a + u b) ∧ (∀ (c : ℝ) (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → u (c • a) = c * u a) ∧ (∀ (a : ℕ → Eucl (m + 1) → ℝ) (b : Eucl (m + 1) → ℝ) (K : Set (Eucl (m + 1))), IsCompact K → K ⊆ U → (∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a k)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → (∀ k, tsupport (a k) ⊆ K) → tsupport b ⊆ K → (∀ q : ℕ, TendstoUniformly (fun k x => iteratedFDeriv ℝ q (a k) x) (fun x => iteratedFDeriv ℝ q b x) atTop) → Tendsto (fun k => u (a k)) atTop (𝓝 (u b)))
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

- Parent DAG node: `root.constancy-a1.local_on_balls-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1.scalar_reduction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to Geometric Measure Theory, Ch. 6, Theorem 2.34 (Constancy Theorem) and its printed proof, pp. 142–143, as expanded in the accepted proof of the parent node root.constancy-a1.local_on_balls-a1 (book n = m + 1; erratum applied there: the garbled printed display (1) reads T(a_ε dx¹∧⋯∧dxⁿ) = ∫ a θ_ε dLⁿ for a ∈ L¹(B_ρ(x₀)), with a_ε = ϕ_ε ∗ a). This child is Step 1, items (1a)–(1e), of that proof: every top-degree form is a·dx¹∧⋯∧dxⁿ, and T(ω) = u(a_ω) with u(a) = T(a dx¹∧⋯∧dxⁿ) and a_ω(x) = ω(x)(e).
Notation. n := m + 1; ℝⁿ = Eucl n = EuclideanSpace ℝ (Fin n); e_i = EuclideanSpace.single i 1 is the i-th standard basis vector and e = (e_1,…,e_n); spt g = tsupport g (closure of {g ≠ 0}); D^q g = iteratedFDeriv ℝ q g; “C^∞” means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞). Λⁿ(ℝⁿ) = Covector (Eucl n) n is the space of continuous alternating n-linear forms on ℝⁿ, and Dⁿ(U) = TestFormOn U n consists of the C^∞ maps ω : ℝⁿ → Λⁿ(ℝⁿ) with compact support and spt ω ⊆ U. T : Dⁿ(U) → ℝ is linear (T.toCurrent is a linear map) and satisfies the continuity axiom GeometricCurrentOn.continuous': T(ω_k) → 0 whenever ω_k → 0 in the sense of TestFormOnConverges, i.e. there is a compact K ⊆ U with spt ω_k ⊆ K for all k (and spt 0 ⊆ K) and, for every q, D^q ω_k → D^q 0 = 0 uniformly on K. A function b : ℝⁿ → ℝ is called admissible if b is C^∞, has compact support and spt b ⊆ U. No hypothesis on U is used.

Proof.

1. (The n-covector dx.) Let dx := dx¹∧⋯∧dxⁿ be the n-covector v = (v_1,…,v_n) ↦ det[(v_j)_i]_{i,j}, the determinant of the n×n matrix whose (i, j) entry is the i-th coordinate of v_j. It is the wedge product of the n coordinate functionals x ↦ x_i, hence a continuous alternating n-linear form: dx ∈ Λⁿ(ℝⁿ). The coordinate matrix of e is the identity matrix, so dx(e) = det I = 1. Every α ∈ Λⁿ(ℝⁿ) satisfies α = α(e)·dx: the alternating n-linear forms on the n-dimensional space ℝⁿ are the scalar multiples of the determinant with respect to the basis e, namely α = α(e)·det_e (AlternatingMap.eq_smul_basis_det, for the basis EuclideanSpace.basisFun (Fin n) ℝ whose i-th vector is e_i), and det_e(v) is the determinant of the coordinate matrix of v, i.e. det_e(v) = dx(v); two continuous alternating maps that agree at every v are equal.

2. (The forms [b].) For b : ℝⁿ → ℝ put [b](x) := b(x)·dx. Let Λ : ℝ → Λⁿ(ℝⁿ), t ↦ t·dx; Λ is continuous linear, Λ(0) = 0 and [b] = Λ ∘ b. Hence:
 (a) if b is C^∞ then [b] is C^∞ (composition with a continuous linear map);
 (b) spt [b] ⊆ spt b (because Λ(0) = 0), and if b has compact support then so has [b];
 (c) [b](x)(e) = b(x)·dx(e) = b(x) for all x, by Step 1;
 (d) [a + b] = [a] + [b] and [c·a] = c·[a] (linearity of Λ);
 (e) if b is C^∞ then D^q[b](x) = Λ ∘ D^q b(x) for every q and x (the q-th derivative of a continuous linear map composed with b), hence ‖D^q[b](x)‖ ≤ ‖Λ‖·‖D^q b(x)‖.
 In particular, for admissible b the form [b] is C^∞ with compact support and spt [b] ⊆ spt b ⊆ U, i.e. [b] ∈ Dⁿ(U).

3. (Definition of u.) Put u(b) := T([b]) if b is admissible and u(b) := 0 otherwise (classical case distinction; the values on non-admissible functions are never used).

4. (Proof of (ii).) For admissible b, ω := [b] ∈ Dⁿ(U) by Step 2, and ω(x)(e) = b(x) for all x by 2(c).

5. (Proof of (i).) Let ω ∈ Dⁿ(U) and a_ω(x) := ω(x)(e). The evaluation ev_e : α ↦ α(e) is a continuous linear map Λⁿ(ℝⁿ) → ℝ with ev_e(0) = 0, and a_ω = ev_e ∘ ω. Since ω is C^∞ with compact support and spt ω ⊆ U, the function a_ω is C^∞, has compact support and spt a_ω ⊆ spt ω ⊆ U; so a_ω is admissible and u(a_ω) = T([a_ω]). By Step 1, for every x, ω(x) = ω(x)(e)·dx = a_ω(x)·dx = [a_ω](x); hence [a_ω] = ω as elements of Dⁿ(U) (same underlying form), and T(ω) = T([a_ω]) = u(a_ω).

6. (Proof of (iii) and (iv).) Let a, b be admissible and c ∈ ℝ. Then a + b and c·a are admissible (sums and scalar multiples of C^∞ compactly supported functions are C^∞ and compactly supported; spt(a + b) ⊆ spt a ∪ spt b ⊆ U and spt(c·a) ⊆ spt a ⊆ U). By 2(d) and the linearity of T on Dⁿ(U): u(a + b) = T([a + b]) = T([a] + [b]) = T([a]) + T([b]) = u(a) + u(b), and u(c·a) = T([c·a]) = T(c·[a]) = c·T([a]) = c·u(a).

7. (Proof of (v).) Let K, a_k, b be as in (v). A closed subset of the compact set K is compact, so every a_k and b has compact support; as spt a_k, spt b ⊆ K ⊆ U, all of them are admissible, and u(a_k) = T([a_k]), u(b) = T([b]). Put ω_k := [a_k] − [b] = [a_k − b] ∈ Dⁿ(U). Then:
 – spt ω_k ⊆ spt(a_k − b) ⊆ spt a_k ∪ spt b ⊆ K, and spt 0 = ∅ ⊆ K;
 – for every q and x, by 2(e) and the linearity of D^q on C^∞ functions, D^q ω_k(x) = Λ ∘ (D^q a_k(x) − D^q b(x)), so ‖D^q ω_k(x) − D^q 0(x)‖ = ‖D^q ω_k(x)‖ ≤ ‖Λ‖·‖D^q a_k(x) − D^q b(x)‖ (D^q of the zero form is 0). Given δ > 0, uniform convergence gives k₀ with ‖D^q a_k(x) − D^q b(x)‖ < δ/(‖Λ‖ + 1) for all k ≥ k₀ and all x, hence ‖D^q ω_k(x)‖ ≤ ‖Λ‖·δ/(‖Λ‖ + 1) < δ for all k ≥ k₀ and all x. Thus D^q ω_k → 0 uniformly on ℝⁿ, in particular uniformly on K.
 Hence ω_k → 0 in the sense of TestFormOnConverges (with this K). The continuity axiom of T gives T(ω_k) → 0. By linearity T(ω_k) = T([a_k]) − T([b]) = u(a_k) − u(b), so u(a_k) − u(b) → 0, i.e. u(a_k) → u(b).

8. Steps 4–7 prove (i)–(v) for the function u of Step 3. ∎

Formalization notes (no new mathematics; no import beyond the frozen GMT.Ch06.Submission is needed). (a) Take dx := wedgeCovectors (m + 1) (fun i => EuclideanSpace.proj i) from Poincare.SimonGMT.Chapter06.FormsDuality (already imported by the frozen file): it is a continuous alternating map by construction, and wedgeCovectors_apply_det with EuclideanSpace.coe_proj gives dx v = Matrix.det (Matrix.of fun i j => v j i); this avoids proving continuity of the determinant by hand. It helps to `generalize` the family (fun i => EuclideanSpace.single i (1 : ℝ)) to a variable e first. dx e = 1: show the matrix is 1 (ext; simp [Matrix.one_apply, PiLp.single_apply]) and use Matrix.det_one. α = α e • dx: apply AlternatingMap.eq_smul_basis_det to α.toAlternatingMap and (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis (its coercion is e, EuclideanSpace.basisFun_apply), evaluate at v, unfold Module.Basis.det_apply, then `congr 2` (the two matrices agree definitionally). (b) Λ := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) dx, with Λ t = t • dx by rfl; the test form [b] is fun x => Λ (b x) with membership proof ⟨⟨Λ.contDiff.comp hb, hcb.comp_left (map_zero Λ)⟩, (tsupport_comp_subset (map_zero Λ) b).trans hsb⟩ in testFormOnSubmodule U (m + 1). (c) Define u by a classical `if h : (ContDiff ℝ _ b ∧ HasCompactSupport b ∧ tsupport b ⊆ U) then T ⟨fun x => Λ (b x), _⟩ else 0` and evaluate it with dite_eq_left; linearity of T is map_add, map_smul, map_sub applied to T.toCurrent. (d) In (i), ev_e is ContinuousAlternatingMap.apply ℝ (Eucl (m + 1)) ℝ e; prove [a_ω] = ω by Subtype.ext and funext. (e) In (v), use ContinuousLinearMap.iteratedFDeriv_comp_left, iteratedFDeriv_sub_apply (ContDiffAt of order q via `.of_le (by simp)`), ContinuousLinearMap.norm_compContinuousMultilinearMap_le, Metric.tendstoUniformly_iff, TendstoUniformly.tendstoUniformlyOn, IsCompact.of_isClosed_subset with isClosed_tsupport, tsupport_sub, then T.continuous' and tendsto_sub_nhds_zero_iff.

## Key steps

1. dx := the determinant of the coordinate matrix (wedge of the coordinate functionals) is a continuous alternating n-form with dx(e) = 1, and every n-covector α equals α(e)·dx (AlternatingMap.eq_smul_basis_det).
2. [b] := b·dx = Λ ∘ b with Λ(t) = t·dx continuous linear: C^∞, spt [b] ⊆ spt b, [b](·)(e) = b, linear in b, D^q[b] = Λ ∘ D^q b.
3. Define u(b) := T([b]) for admissible b (0 otherwise); (ii) holds with ω = [b].
4. (i): a_ω = ω(·)(e) is admissible and [a_ω] = ω, so T(ω) = u(a_ω).
5. (iii)–(iv) follow from the linearity of b ↦ [b] and of T.
6. (v): ω_k = [a_k] − [b] → 0 in TestFormOnConverges (supports in K, ‖D^q ω_k‖ ≤ ‖Λ‖·‖D^q a_k − D^q b‖ → 0 uniformly), so T.continuous' gives u(a_k) − u(b) = T(ω_k) → 0.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean with the workspace GMT/Ch06/Contract.lean and with project/GMT/Ch06/Submission.lean (all identical); grep -n 'ConstancyTheorem' -A 25 GMT/Ch06/Contract.lean`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|hasFDerivAt_convolution_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `rg -n 'convolutionExists_left|HasCompactSupport.convolution |theorem support_convolution_subset|theorem ConvolutionExists.distrib_add|theorem convolution_smul|theorem convolution_precompR_apply' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem (contDiff_normed|integral_normed|tsupport_normed_eq|hasCompactSupport_normed|nonneg_normed|continuous_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'theorem AlternatingMap.eq_smul_basis_det|theorem det_self' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `rg -n 'iteratedFDeriv_comp_left|norm_compContinuousMultilinearMap_le|tsupport_fderiv_apply_subset|HasCompactSupport.fderiv_apply|setIntegral_eq_integral_of_forall_compl_eq_zero|ae_convolution_tendsto_right_of_locallyIntegrable' mathlib/Mathlib; rg -n '^def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `grep -n 'structure GeometricCurrentOn|def TestFormOnConverges|abbrev TestFormOn|abbrev DifferentialForm|def IsTestForm' simongmt/Poincare/SimonGMT/Chapter06/Currents.lean simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `grep -n 'def wedgeCovectors|theorem wedgeCovectors_apply_det' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; grep -n 'theorem ae_eq_const_of_weak_coordinate_derivatives_zero' -A 8 simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; grep -n 'exists_compact_derivative_bound' simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `#check after the frozen `import GMT.Ch06.Submission`: convolution API present; ContDiffBump.normed, Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero and GeometricCurrentOn.exists_compact_derivative_bound unknown`
- `lake build GMT.Ch06.Submission for the frozen commit (/tmp/lob2_check), for a variant adding only `import Poincare.SimonGMT.Chapter08.DistributionalConstancy` (/tmp/lob2_imp2: no new Lake warning; exposes ContDiffBump.normed and the SimonGMT lemma) and for a variant adding Mathlib imports (/tmp/lob2_imports: new Lake 'module system' warnings)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py child_modules (contract scope) on the 4 statements; lake env lean on the generated NodeChallenge modules against the frozen Submission and the variant`
- `lean Scratch/Child_{scalar_reduction,mollified_l1_bound,density_constancy,mollifier_limit}.lean (complete proofs, #print axioms) against the frozen Submission and with the single extra import; lean Scratch/Assembly.lean and Scratch/EndToEnd.lean (exact frozen parent type from the 4 children and the 3 dependency types; accepted mollifier proofs taken from commits d6285a3 and 933d7e8; Riesz stubbed)`
- `python3 -I scan of dag.json lean_name values (266 nodes) for the 4 proposed names and child ids; grep of simongmt/Poincare and the snapshot project for the names (no match)`
- `git show 56f7ba4 (speculative draft of root.constancy-a1 calling Submission.constancy_local_on_balls m U hU T (Submission.constancy_closed_kills_partial_derivatives m U T hT))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1/decomposition-v1.json`
- `/tmp/lob2_imp2/Scratch/Child_scalar_reduction.lean`
- `/tmp/lob2_imp2/Scratch/Child_mollified_l1_bound.lean`
- `/tmp/lob2_imp2/Scratch/Child_density_constancy.lean`
- `/tmp/lob2_imp2/Scratch/Child_mollifier_limit.lean`
- `/tmp/lob2_imp2/Scratch/Assembly.lean`
- `/tmp/lob2_imp2/Scratch/EndToEnd.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen Contract.lean and Submission.lean are byte-identical. ConstancyTheorem quantifies over GeometricCurrentOn U (m+1): linear functionals on C^∞ compactly supported TestFormOn U (m+1) with T(ω_k) → 0 whenever TestFormOnConverges ω 0.

Available through the frozen import: Mathlib's first-derivative convolution API (HasCompactSupport.contDiff_convolution_left/right, hasFDerivAt_convolution_right, convolutionExists_left, ConvolutionExists.distrib_add, convolution_smul, support_convolution_subset, convolution_precompR_apply), AlternatingMap.eq_smul_basis_det, ContinuousLinearMap.iteratedFDeriv_comp_left, tsupport_fderiv_apply_subset, ContinuousAlternatingMap.apply, and SimonGMT wedgeCovectors/wedgeCovectors_apply_det (a ready-made continuous dx¹∧⋯∧dxⁿ).

Not available through the frozen import: ContDiffBump.normed, the SimonGMT weak-constancy lemma ae_eq_const_of_weak_coordinate_derivatives_zero and GeometricCurrentOn.exists_compact_derivative_bound. Adding `import Poincare.SimonGMT.Chapter08.DistributionalConstancy` to Submission.lean provides the first two, adds no new Lake warning, and leaves all 56 GMT.Ch06 declarations hash-identical; direct Mathlib imports add Lake 'module system' warnings.

Checks on the four children (constancy_topForm_scalar_reduction, constancy_mollified_functional_l1_bounded, constancy_mollified_density_const, constancy_local_of_mollified_const):
- Every statement passes the validator and elaborates in the exact comparator contract scope.
- Each has a complete Lean proof with axioms propext, Classical.choice, Quot.sound only. The first two need no new import; the last two need the single SimonGMT import above.
- An end-to-end file proves the parent's exact frozen type from the four children and the three dependencies; its only sorry is the still-decomposing Riesz dependency.
- An independent audit accepted all four children.
- The names collide with no DAG node or library declaration.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
