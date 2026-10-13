<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1 -->

## Theorem `Submission.iwl_cr_ro_integrand_iteratedFDeriv_le`

Let P, k, a ∈ ℕ and let ω : ℝ^P → Λ_{k+1} be a C^∞ (k+1)-form. Let j ∈ ℕ and R, D ∈ ℝ with D ≥ 0, and assume ‖D^iω(y)‖ ≤ D for every i ≤ j and every y with ‖y‖ ≤ R. Then for every t ∈ [0,1] and every x with ‖x‖ ≤ R, the j-th iterated Fréchet derivative at x of z ↦ t^a • (ω(t•z)).curryLeft z has operator norm at most (R + j)·D.

Node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2723

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.iwl_cr_ro_integrand_iteratedFDeriv_le`

```lean
∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D
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

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1.integrand_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 7 of the parent proof (bound (iii)), stated for the integrand at a fixed t ∈ [0,1] and filled in. A Lean rendering of exactly this argument was compiled against the pinned snapshot, using only the standard axioms.

Conventions. E := Eucl P, Λ_l := Covector E l, D^i := iteratedFDeriv ℝ i, and ‖·‖ is the operator norm.

0. Fix j, R and D ≥ 0 with ‖D^iω(y)‖ ≤ D for all i ≤ j and all y with ‖y‖ ≤ R. Fix t ∈ [0,1] and x with ‖x‖ ≤ R. Then R ≥ 0, since ‖x‖ ≥ 0.

1. (Interior product.) Let 𝔅 := (ContinuousAlternatingMap.curryLeftLI).toContinuousLinearMap : Λ_{k+1} →L[ℝ] (E →L[ℝ] Λ_k). Then 𝔅(α) = α.curryLeft, and ‖𝔅‖ ≤ 1 because the continuous linear map underlying a linear isometry has norm at most 1 (LinearIsometry.norm_toContinuousLinearMap_le). So the function in the statement is f_t(z) = t^a • 𝔅(g_t(z))(id z), where g_t(z) := ω(t • z).

2. (Derivatives of g_t.) Let L := t • id_E ∈ E →L[ℝ] E. Then ‖L‖ = |t|·‖id_E‖ ≤ 1·1 = 1 (norm_smul, ContinuousLinearMap.norm_id_le, 0 ≤ t ≤ 1). So g_t = ω ∘ L is C^∞. For i ≤ j:
 - ContinuousLinearMap.iteratedFDeriv_comp_right gives D^ig_t(x) = (D^iω(Lx)).compContinuousLinearMap (fun _ => L);
 - so ‖D^ig_t(x)‖ ≤ ‖D^iω(Lx)‖·∏_{Fin i}‖L‖ ≤ ‖D^iω(Lx)‖ (ContinuousMultilinearMap.norm_compContinuousLinearMap_le and Finset.prod_le_one₀);
 - since ‖Lx‖ ≤ ‖L‖‖x‖ ≤ R, we have Lx ∈ closedBall 0 R, and the hypothesis gives ‖D^ig_t(x)‖ ≤ D.

3. (Removing the scalar t^a.) H(z) := 𝔅(g_t(z))(id z) is C^∞, since a bounded bilinear map composed with C^∞ maps is C^∞ (B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)). Hence D^jf_t(x) = t^a • D^jH(x) (iteratedFDeriv_const_smul_apply'), so ‖D^jf_t(x)‖ = |t^a|·‖D^jH(x)‖ with 0 ≤ t^a ≤ 1 (pow_le_one₀).

4. (Leibniz bound.) Apply ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one with the bilinear map 𝔅 (norm ≤ 1), f = g_t and g = id, both C^∞:
 ‖D^jH(x)‖ ≤ Σ_{i=0}^{j} C(j,i)·‖D^ig_t(x)‖·‖D^{j−i}id(x)‖.

5. (Derivatives of the identity.)
 - ‖D^0 id(x)‖ = ‖x‖ ≤ R (norm_iteratedFDeriv_zero).
 - ‖D^1 id(x)‖ = ‖fderiv ℝ id x‖ = ‖id_E‖ ≤ 1 (norm_iteratedFDeriv_one, fderiv_id, ContinuousLinearMap.norm_id_le).
 - D^l id(x) = 0 for l ≥ 2. Write l = n + 1 with n ≥ 1. By iteratedFDeriv_succ_eq_comp_right, D^{n+1}id(x) = Ψ(D^n(y ↦ fderiv ℝ id y)(x)) for the linear isometry Ψ := (continuousMultilinearCurryRightEquiv' ℝ n E E).symm. The map y ↦ fderiv ℝ id y is the constant y ↦ id_E (fderiv_id), so its n-th iterated derivative vanishes because n ≠ 0 (iteratedFDeriv_const_of_ne). Finally Ψ(0) = 0.

6. (Evaluating the sum.)
 - If j = 0, the sum has the single term C(0,0)·‖D^0g_t(x)‖·‖D^0id(x)‖ = ‖ω(t•x)‖·‖x‖ ≤ D·R = (R + 0)·D.
 - If j = m + 1, split off the last two terms (Finset.sum_range_succ twice):
 · for i < m, j − i ≥ 2, so these terms vanish by Step 5;
 · the term i = m is C(m+1,m)·‖D^mg_t(x)‖·‖D^1id(x)‖ ≤ (m+1)·D·1 (Nat.choose_succ_self_right, Step 2 with m ≤ j, and Step 5);
 · the term i = m+1 is C(m+1,m+1)·‖D^{m+1}g_t(x)‖·‖D^0id(x)‖ ≤ 1·D·R.
 Hence the sum is at most (m+1)·D + D·R = (R + j)·D.

7. (Conclusion.) By Steps 3, 4 and 6, ‖D^jf_t(x)‖ ≤ |t^a|·(R + j)·D ≤ 1·(R + j)·D = (R + j)·D, using (R + j)·D ≥ 0. ∎

Implementation notes (all checked in a scratch build against the snapshot):
- Add `import Mathlib.Analysis.Calculus.ContDiff.Bounds` to Submission.lean, and put `set_option maxSynthPendingDepth 3 in` before the theorem.
- Introduce 𝔅 opaquely: `obtain ⟨B, hB, hBnorm⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k), (∀ α, B α = α.curryLeft) ∧ ‖B‖ ≤ 1 := ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ) (n := k)).toContinuousLinearMap, fun α => rfl, LinearIsometry.norm_toContinuousLinearMap_le _⟩`. Then rewrite the function to `fun z => t ^ a • B (ω (t • z)) (id z)` with `funext z; rw [hB]; rfl`.
- The vanishing of D^l id is a six-line auxiliary lemma, `Submission.iwl_cr_ro_ib_iteratedFDeriv_id_eq_zero`.
- Use `Finset.prod_le_one₀`; the unprimed `Finset.prod_le_one` is the ordered-monoid version.
- In the case j = 0, a `simp only` with `Finset.range_one`, `Finset.sum_singleton`, `Nat.choose_self`, `Nat.sub_zero` and `norm_iteratedFDeriv_zero` reduces the sum.
- In the case j = m+1, use `rw [hzero, zero_add, Nat.sub_self, Nat.choose_self, Nat.choose_succ_self_right, show m + 1 - m = 1 by omega, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]`, then `push_cast`, then `nlinarith` from the two term bounds.

Appendix — verified Lean rendering of the proof above. It was compiled against the pinned snapshot in the Submission.lean layout, i.e. inside `namespace GMT.Ch06` after the contract's section, with the contract's `open`s. A comparator-style check `theorem … : (frozen type) := by exact Submission.<name>`, run in the replayed contract scope, also passes. `#print axioms` reports only propext, Classical.choice and Quot.sound. Required import: `import Mathlib.Analysis.Calculus.ContDiff.Bounds`.

```lean
theorem Submission.iwl_cr_ro_ib_iteratedFDeriv_id_eq_zero (P : ℕ) (l : ℕ) (hl : 2 ≤ l)
    (x : Eucl P) : iteratedFDeriv ℝ l (id : Eucl P → Eucl P) x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  have hconst : (fun y : Eucl P => fderiv ℝ (id : Eucl P → Eucl P) y) =
      fun _ => ContinuousLinearMap.id ℝ (Eucl P) := by
    funext y; exact fderiv_id
  rw [hconst, iteratedFDeriv_const_of_ne (by omega)]
  simp

set_option maxSynthPendingDepth 3 in
theorem Submission.iwl_cr_ro_integrand_iteratedFDeriv_le :
    (∀ (P k a : ℕ) (ω : DifferentialForm (Eucl P) (k + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) x‖ ≤ (R + j) * D) := by
  intro P k a ω hω j R D hD hbound t ht x hx
  obtain ⟨B, hB, hBnorm⟩ : ∃ B : Covector (Eucl P) (k + 1) →L[ℝ] (Eucl P →L[ℝ] Covector (Eucl P) k),
      (∀ α, B α = α.curryLeft) ∧ ‖B‖ ≤ 1 :=
    ⟨(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Eucl P) (F := ℝ) (n := k)).toContinuousLinearMap,
      fun α => rfl, LinearIsometry.norm_toContinuousLinearMap_le _⟩
  have hx' : ‖x‖ ≤ R := by simpa using hx
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hfun : (fun z : Eucl P => t ^ a • (ω (t • z)).curryLeft z) =
      fun z => t ^ a • B (ω (t • z)) (id z) := by
    funext z; rw [hB]; rfl
  rw [hfun]
  set L : Eucl P →L[ℝ] Eucl P := t • ContinuousLinearMap.id ℝ (Eucl P) with hL
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hL, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc t * ‖ContinuousLinearMap.id ℝ (Eucl P)‖ ≤ 1 * 1 :=
          mul_le_mul ht1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hgfun : (fun z : Eucl P => ω (t • z)) = ω ∘ L := by
    funext z; simp [hL]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => ω (t • z)) := by
    rw [hgfun]; exact hω.comp L.contDiff
  have hgnorm : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ ≤ D := by
    intro i hi
    rw [hgfun, L.iteratedFDeriv_comp_right hω x (by exact_mod_cast le_top)]
    have hLx : L x ∈ closedBall (0 : Eucl P) R := by
      rw [mem_closedBall, dist_zero_right]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ 1 * R := mul_le_mul hLnorm hx' (norm_nonneg x) zero_le_one
        _ = R := one_mul R
    calc ‖(iteratedFDeriv ℝ i ω (L x)).compContinuousLinearMap fun _ => L‖
        ≤ ‖iteratedFDeriv ℝ i ω (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ D * 1 := by
          apply mul_le_mul (hbound i hi _ hLx) _ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hD
          exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLnorm)
      _ = D := mul_one D
  have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Eucl P => B (ω (t • z)) (id z)) :=
    B.isBoundedBilinearMap.contDiff.comp (hg.prodMk contDiff_id)
  have hsmul : iteratedFDeriv ℝ j (fun z : Eucl P => t ^ a • B (ω (t • z)) (id z)) x =
      t ^ a • iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) (id z)) x :=
    iteratedFDeriv_const_smul_apply' (hH.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [hsmul, norm_smul]
  have hta : ‖t ^ a‖ ≤ 1 := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact pow_le_one₀ ht0 ht1
  have key := B.norm_iteratedFDeriv_le_of_bilinear_of_le_one hg contDiff_id x
    (n := j) (by exact_mod_cast le_top) hBnorm
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ *
      ‖iteratedFDeriv ℝ (j - i) (id : Eucl P → Eucl P) x‖ ≤ (R + j) * D := by
    rcases j with _ | m
    · simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self, Nat.cast_one,
        one_mul, Nat.sub_zero, norm_iteratedFDeriv_zero, id_eq, CharP.cast_eq_zero, add_zero]
      calc ‖ω (t • x)‖ * ‖x‖ ≤ D * R := by
            apply mul_le_mul _ hx' (norm_nonneg _) hD
            have := hgnorm 0 le_rfl
            simpa using this
        _ = R * D := mul_comm D R
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hzero : ∑ i ∈ Finset.range m, ((m + 1).choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun z : Eucl P => ω (t • z)) x‖ *
          ‖iteratedFDeriv ℝ (m + 1 - i) (id : Eucl P → Eucl P) x‖ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [Submission.iwl_cr_ro_ib_iteratedFDeriv_id_eq_zero P (m + 1 - i) (by omega) x,
          norm_zero, mul_zero]
      rw [hzero, zero_add, Nat.sub_self, Nat.choose_self, Nat.choose_succ_self_right,
        show m + 1 - m = 1 by omega, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one]
      have h1 : ‖fderiv ℝ (id : Eucl P → Eucl P) x‖ ≤ 1 := by
        rw [fderiv_id]; exact ContinuousLinearMap.norm_id_le
      have hm := hgnorm m (by omega)
      have hm1 := hgnorm (m + 1) le_rfl
      push_cast
      have e1 : ((m : ℝ) + 1) * ‖iteratedFDeriv ℝ m (fun z : Eucl P => ω (t • z)) x‖ *
          ‖fderiv ℝ (id : Eucl P → Eucl P) x‖ ≤ ((m : ℝ) + 1) * D * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) h1 (norm_nonneg _)
          (by positivity)
      have e2 : 1 * ‖iteratedFDeriv ℝ (m + 1) (fun z : Eucl P => ω (t • z)) x‖ * ‖id x‖ ≤
          1 * D * R := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hm1 zero_le_one) hx' (norm_nonneg _)
          (by positivity)
      nlinarith
  calc ‖t ^ a‖ * ‖iteratedFDeriv ℝ j (fun z : Eucl P => B (ω (t • z)) (id z)) x‖
      ≤ 1 * ((R + j) * D) := by
        apply mul_le_mul hta (key.trans hsum) (norm_nonneg _) zero_le_one
    _ = (R + j) * D := one_mul _
```

## Key steps

1. Write the integrand as t^a • 𝔅(ω(t•z))(id z), with ‖𝔅‖ ≤ 1 (curryLeftLI) and 0 ≤ t^a ≤ 1.
2. For i ≤ j, ‖D^i(ω∘(t•id))(x)‖ ≤ ∏‖t•id‖·‖D^iω(tx)‖ ≤ D, via iteratedFDeriv_comp_right and ‖tx‖ ≤ R.
3. Leibniz bound for a bounded bilinear map of norm ≤ 1: ‖D^jH(x)‖ ≤ Σ C(j,i)‖D^ig_t(x)‖‖D^{j−i}id(x)‖.
4. ‖D^0id(x)‖ = ‖x‖ ≤ R, ‖D^1id‖ ≤ 1 and D^l id = 0 for l ≥ 2. Only i = j and i = j−1 contribute, giving ≤ RD + jD = (R+j)D.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (project_commit d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; sha256sum GMT/Ch06/Contract.lean`
- `rg -n "(theorem|lemma|def|abbrev) [A-Za-z_.']*<name>\b" mathlib/Mathlib for <name> in hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, curryLeftLI, norm_curryLeft, curryLeft_apply_apply, iteratedFDeriv_comp_right, continuous_iteratedFDeriv, iteratedFDeriv_succ_eq_comp_left, continuous_parametric_intervalIntegral_of_continuous, contDiff_of_differentiable_iteratedFDeriv, intervalIntegral_comp_comm, norm_compContinuousLinearMap_le, norm_integral_le_of_norm_le_const, contDiff_parametric_integral_of_contDiff, contDiff_parametric_primitive_of_contDiff`
- `rg -n 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral|iteratedFDeriv_integral|integral_iteratedFDeriv|contDiffOn_parametric|fderiv_integral|hasFDerivAt_integral\b' mathlib/Mathlib`
- `rg -n 'parametric_primitive|parametric_integral|ParametricIntegral' mathlib/Mathlib`
- `rg -n 'norm_iteratedFDeriv_le_of_bilinear_of_le_one|norm_iteratedFDeriv_clm_apply|iteratedFDeriv_const_smul_apply|iteratedFDeriv_const_of_ne|theorem fderiv_id|prod_le_one₀|iteratedFDeriv_succ_eq_comp_right|contDiff_succ_iff_fderiv|contDiff_infty|iteratedFDeriv_one_apply|norm_iteratedFDeriv_one|intervalIntegral_comp_comm' mathlib/Mathlib`
- `rg -n 'def apply' mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `rg -n 'iteratedFDeriv_fixedSupportParameterSlice|intervalIntegral|∫ t in' simongmt/Poincare/SimonGMT; grep -n 'abbrev|^def' simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3: dag.json node metadata and lean_name scan (iwl_cr_*, radial, lean_statements containing ∫ together with fderiv/iteratedFDeriv/ContDiff); grep -rl iwl_cr_ro_ over dag.json, nodes/ and GMT/; git grep -l iwl_cr_ro_ over all 619 ref tips`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (imports and Submission.X declaration layout of an accepted candidate)`
- `python3 -I /tmp/ro_split/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/ro_split/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/ro_split/scratch/{Assembly,Full,InstCheck,ImportCheck}.lean and /tmp/ro_split/snip/Snip{A,B1,B2}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-radial-operator-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/ParametricCurrentContinuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ro_split/scripts/gen.py`
- `/tmp/ro_split/scratch/Assembly.lean`
- `/tmp/ro_split/scratch/Full.lean`
- `/tmp/ro_split/scratch/InstCheck.lean`
- `/tmp/ro_split/scratch/ImportCheck.lean`
- `/tmp/ro_split/snip/SnipA.lean`
- `/tmp/ro_split/snip/SnipB1.lean`
- `/tmp/ro_split/snip/SnipB2.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean (sha256 ea3ee0dd…).

Missing obligation. The snapshot Mathlib has only first-order differentiation under an interval integral (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`, Analysis/Calculus/ParametricIntervalIntegral.lean:55) and continuity of parametric integrals (`continuous_parametric_intervalIntegral_of_continuous'`, DominatedConvergence.lean:619). There is no lemma for C^∞ smoothness of x ↦ ∫ G(t,x) dt or for iterated derivatives under the integral: the searches for contDiff_parametric*, ContDiff.*intervalIntegral and iteratedFDeriv_integral found nothing. So the all-order statement is a genuinely missing, reusable obligation, which becomes child parametric_integral.

Available Mathlib tools:
- Leibniz bounds `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear(_of_le_one)` (ContDiff/Bounds.lean:202/226);
- curryLeft, curryLeftLI, norm_curryLeft and curryLeft_apply_apply (Normed/Module/Alternating/Curry.lean);
- `ContinuousLinearMap.iteratedFDeriv_comp_right` (ContDiff/Basic.lean:461);
- `iteratedFDeriv_succ_eq_comp_right` and `iteratedFDeriv_one_apply` (FTaylorSeries.lean);
- `contDiff_succ_iff_fderiv` and `contDiff_infty` (ContDiff/Defs.lean);
- `ContinuousAlternatingMap.apply` and `ContinuousMultilinearMap.apply` (Topology/Algebra/Module/{Alternating,Multilinear}/Topology.lean).

Imports. ParametricIntervalIntegral and ContDiff.Bounds are not imported by GMT.Ch06.Submission (an #check reports unknown constants), so children 1 and 3 add those imports. The accepted candidate at commit 2f36576 also adds imports to Submission.lean and declares `theorem Submission.X` inside namespace GMT.Ch06.

SimonGMT. Covector and DifferentialForm are abbrevs (Chapter06/Forms.lean:31/37). `iteratedFDeriv_fixedSupportParameterSlice` (Chapter06/ParametricCurrentContinuity.lean:76) uses the same partial-derivative-by-inclusion pattern, but SimonGMT has no smoothness result for parametric integrals.

DAG and names. No DAG node supplies a parametric-integral smoothness lemma or the radial integrand facts. The names iwl_cr_ro_* and the helper prefixes iwl_cr_ro_pi_ / iwl_cr_ro_ib_ occur nowhere in dag.json, nodes/, GMT/ or any of the 619 git ref tips.

Lean checks:
- The three frozen child types, generated through the verifier's own child_modules / validate_lean_statement path, elaborate in the replayed contract scope.
- Assembly.lean proves the parent's exact frozen type from the three children, which are sorried there.
- Full.lean and Snip{A,B1,B2}.lean prove all three children and the parent; #print axioms gives [propext, Classical.choice, Quot.sound], and the comparator-style `exact Submission.<name>` targets pass.
- An independent reviewer agent re-ran these builds and accepted the split.

Public citations for the standard mathematics: differentiation under the integral sign (Dieudonné, Foundations of Modern Analysis, §8.11) and the radial homotopy operator of the Poincaré lemma (Spivak, Calculus on Manifolds, Thm 4-11).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
