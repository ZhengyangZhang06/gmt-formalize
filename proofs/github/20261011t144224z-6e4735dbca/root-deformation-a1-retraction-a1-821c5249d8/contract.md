<!-- theorem-id: gmt-ch06/root.deformation-a1.retraction-a1 -->

## Theorem `Submission.deformation_retraction`

Lemma 5.4 (periodic retraction onto the n-skeleton). Let m, ℓ ∈ ℕ with ℓ ≥ 1, n := m + 1, d := n + ℓ, C := [0,1]^d, q := (1/2,…,1/2). There is c = c(m,ℓ) ∈ [0,∞) such that for every a ∈ ℝ^d with Σ_i(a_i − 1/2)² < 1/16 (i.e. a ∈ B_{1/4}(q)), writing La := L_{ℓ−1}(a) := {y ∈ ℝ^d : there is a set J of m + 2 coordinate indices with y_i − a_i ∈ ℤ for all i ∈ J}, there is a map ψ : ℝ^d → ℝ^d such that (i) ψ(x) ∈ L_n := ⋃_F latticeFace 1 F (the union of the closed n-faces of the unit cubical lattice, F ∈ LatticeFaceIndex (m+1) (m+1+ℓ)) for every x ∉ La; (ii) for every z ∈ ℤ^d and every x ∉ La with z_i ≤ x_i ≤ z_i + 1 for all i, also z_i ≤ ψ(x)_i ≤ z_i + 1 for all i; (iii) for every σ with 0 < σ ≤ 1/4, ψ is Lipschitz with constant c/σ on {x : dist(x, La) ≥ σ}.

Node: `root.deformation-a1.retraction-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/325

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2488, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2501, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2515, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2530, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2542

## Lean problem

Declaration: `Submission.deformation_retraction`

```lean
∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ a : Eucl (m + 1 + ℓ), ∑ i, (a i - 1 / 2) ^ 2 < 1 / 16 → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → ∃ ψ : Eucl (m + 1 + ℓ) → Eucl (m + 1 + ℓ), (∀ x, x ∉ La → ψ x ∈ ⋃ F : LatticeFaceIndex (m + 1) (m + 1 + ℓ), latticeFace 1 F) ∧ (∀ (z : Fin (m + 1 + ℓ) → ℤ) (x : Eucl (m + 1 + ℓ)), x ∉ La → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → ∀ i, (z i : ℝ) ≤ ψ x i ∧ ψ x i ≤ z i + 1) ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 / 4 → LipschitzOnWith (c / Real.toNNReal σ) ψ {x | σ ≤ infDist x La}
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
- Child DAG node: `root.deformation-a1.retraction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Lemma 5.4 (p. 160) and its printed proof (displays (1)–(8), pp. 161–163), as reproduced in Part B (B1–B3) of the parent proof. Errata applied: the book's “k” is ℓ (so L_{k−1}(a) is L_{ℓ−1}(a)); the printed bound “|y − a| ≥ 3/4” before (6) is replaced by the correct “|y − a| > 1/4”; the a.e. derivative bound of the printed statement is replaced by the pointwise upper Lipschitz constant |D̄ψ(x)| := limsup_{x′→x}|ψ(x′) − ψ(x)|/|x′ − x| that the printed proof actually estimates in (7)–(8), and Step 6 converts it into the Lipschitz bound (iii) exactly as in the last sentence of B3. Only the properties (i)–(iii) of the statement are proved (they are what the deformation argument uses); the values of ψ on L_{ℓ−1}(a) are irrelevant and ψ := id there.

Notation. n := m + 1 ≥ 1, d := n + ℓ ≥ 2, ℝ^d = Eucl(m+1+ℓ) with coordinates x = (x_1,…,x_d), C := [0,1]^d, q := (1/2,…,1/2). Fix a with Σ_i (a_i − 1/2)² < 1/16, i.e. |a − q| < 1/4; then |a_i − 1/2| < 1/4, so a_i ∈ (1/4, 3/4) for every i. L := L_{ℓ−1}(a) := {y : there is J ⊆ {1,…,d}, |J| = n + 1 = m + 2, with y_i − a_i ∈ ℤ for all i ∈ J} (this is the set La of the statement), d_a(x) := dist(x, L), and L_n := ⋃_{F} latticeFace 1 F (F ∈ LatticeFaceIndex (m+1) (m+1+ℓ)). For a set A ⊆ ℝ^d and a map f defined on A, Lip_A f(x) := limsup_{x′→x, x′∈A} |f(x′) − f(x)|/|x′ − x| (pointwise upper Lipschitz constant at x ∈ A).

1. Elementary facts.
 (a) L is closed (finite union over J of the closed sets {y : y_i − a_i ∈ ℤ ∀ i ∈ J}, each a locally finite union of affine planes), ℤ^d-periodic (y ∈ L ⟺ y + z ∈ L for z ∈ ℤ^d), and a ∈ L. Hence d_a is 1-Lipschitz, ℤ^d-periodic, d_a(x) > 0 for x ∉ L, and d_a(x) ≤ |x − a|.
 (b) x ∈ L_n ⟺ at least ℓ coordinates of x are integers. Indeed latticeFace 1 (z,α) = {x : z_i ≤ x_i ≤ z_i + 1 (i ∈ range α), x_i = z_i (i ∉ range α)} and |range α| = n, so its points have the d − n = ℓ coordinates outside range α integral; conversely, if x_i ∈ ℤ for i in a set I with |I| = ℓ, let α enumerate the complement of I increasingly, z_i := x_i (i ∈ I), z_i := ⌊x_i⌋ (i ∉ I); then x ∈ latticeFace 1 (z, α). In particular L_n is ℤ^d-invariant, and C ∩ L_n = {x ∈ C : at least ℓ coordinates lie in {0,1}} is the union of the n-faces of C.
 (c) Faces of C. For disjoint I₀, I₁ ⊆ {1,…,d} the set F = {x ∈ C : x_i = 0 (i ∈ I₀), x_i = 1 (i ∈ I₁)} is a face of dimension j = d − |I₀ ∪ I₁|, with free coordinates J_F := {1,…,d} ∖ (I₀ ∪ I₁), affine hull Π_F, relative interior {x ∈ F : x_i ∈ (0,1) ∀ i ∈ J_F} and relative boundary ∂F := F ∖ relint F. Every x ∈ C lies in the relative interior of exactly one face (free coordinates = {i : x_i ∈ (0,1)}). Two distinct faces of the same dimension meet in a face of lower dimension, contained in the relative boundary of both. For a j-face F (j ≥ n + 1) let a_F be the orthogonal projection of a onto Π_F: (a_F)_i = a_i (i ∈ J_F), (a_F)_i ∈ {0,1} the fixed value (i ∉ J_F). Since a_i ∈ (1/4,3/4), a_F ∈ relint F, and |y − a_F| > 1/4 for y ∈ ∂F; likewise |y − a| > 1/4 for y ∈ ∂C.
 (d) (Printed (1),(2).) The segment from a to a_F lies in L: its points have the |J_F| ≥ n + 1 coordinates i ∈ J_F equal to a_i. Moreover, for x ∈ F the fixed coordinates x_i ∈ {0,1} (i ∉ J_F) are not in a_i + ℤ, and for i ∈ J_F, x_i ∈ [0,1] lies in a_i + ℤ iff x_i = a_i. Hence L ∩ F = {x ∈ F : #{i ∈ J_F : x_i = a_i} ≥ n + 1}, a finite union of the sets F ∩ {x : x_i = a_i (i ∈ J)}, J ⊆ J_F, |J| = n + 1, each of which is F intersected with an affine plane through a_F. Consequently L ∩ F is a cone with vertex a_F inside F: if x ∈ F ∖ {a_F}, λ > 0 and a_F + λ(x − a_F) ∈ F, then x ∈ L ⟺ a_F + λ(x − a_F) ∈ L.

2. Radial retraction of one face. Let F be a j-face of C, n + 1 ≤ j ≤ d. For v ∈ Π_F − a_F (coordinates v_i, i ∈ J_F, the others 0) let N_F(v) := max_{i∈J_F} max{v_i/(1 − a_i), −v_i/a_i} (the gauge of F − a_F in Π_F − a_F). N_F is positively homogeneous, N_F(v) > 0 for v ≠ 0, F = a_F + {N_F ≤ 1}, ∂F = a_F + {N_F = 1}, and |N_F(v) − N_F(w)| ≤ 4|v − w| because a_i, 1 − a_i > 1/4. Define ψ_F : F ∖ {a_F} → ∂F, ψ_F(x) := a_F + (x − a_F)/N_F(x − a_F): this is the radial retraction of the printed proof (x ∈ {a_F + λ(ψ_F(x) − a_F) : λ ∈ (0,1]}), ψ_F = id on ∂F, and by 1(d), ψ_F(F ∖ L) ⊆ ∂F ∖ L (a_F ∈ L, so F ∖ L ⊆ F ∖ {a_F}).
 Estimate (printed (8)). Let x ∈ F ∖ {a_F}, v := x − a_F, y := ψ_F(x), t := |y − a_F|/|x − a_F| = 1/N_F(v) ≥ 1. For w ∈ Π_F − a_F near v,
 |w/N_F(w) − v/N_F(v)| ≤ |w − v|/N_F(w) + |v|·|N_F(v) − N_F(w)|/(N_F(v)N_F(w)),
 and |v|/N_F(v) = |y − a_F| ≤ diam F ≤ √d, N_F(w) → N_F(v). Hence
 (2.1) Lip_F ψ_F(x) ≤ (1 + 4√d)·t = (1 + 4√d)|ψ_F(x) − a_F|/|x − a_F| ≤ (1 + 4√d)√d/|x − a_F|.

3. The retraction ψ₀ of C ∖ L and the periodic map ψ (printed construction; parent B2). For n + 1 ≤ j ≤ d let ψ^{(j)} be defined on ⋃{F ∖ {a_F} : F a j-face of C} by ψ^{(j)} := ψ_F on F ∖ {a_F}; it is well defined because distinct j-faces meet only in their relative boundaries, where the ψ_F are the identity, and it is continuous (pasting finitely many continuous maps on closed sets agreeing on overlaps). By 2, ψ^{(j)} maps (⋃ j-faces) ∖ L into (⋃ (j−1)-faces) ∖ L. Hence ψ₀ := ψ^{(n+1)} ∘ ψ^{(n+2)} ∘ ⋯ ∘ ψ^{(d)} is defined and continuous on C ∖ L (ψ^{(d)} = ψ_C, a_C = a) and maps C ∖ L into the union of the n-faces of C, i.e. into C ∩ L_n (1(b)). If x lies in the relative interior of a j-face F₁ (j ≥ n + 1), the maps ψ^{(j′)}, j′ > j, fix x (x lies in the relative boundary of every j′-face containing it), so ψ₀(x) = ψ^{(n+1)}∘⋯∘ψ^{(j)}(x), the first map applied being ψ_{F₁}; if j ≤ n then x ∈ C ∩ L_n and ψ₀(x) = x.
 Translation compatibility (printed). Let z ∈ ℤ^d, x ∈ C ∖ L, z + x ∈ C. Let F₁ be the face with x ∈ relint F₁. For i ∈ J_{F₁}, x_i ∈ (0,1) and x_i + z_i ∈ [0,1] force z_i = 0; for i ∉ J_{F₁}, x_i + z_i ∈ {0,1}. So F₂ := z + F₁ is a face of C with the same free coordinates, z + x ∈ relint F₂, a_{F₂} = z + a_{F₁} and N_{F₂} = N_{F₁}; hence ψ_{F₂}(z + x) = z + ψ_{F₁}(x), and ψ_{F₁}(x), z + ψ_{F₁}(x) are again points of C differing by z. Induction on the dimension of the face (the case j ≤ n being trivial) gives ψ₀(z + x) = z + ψ₀(x).
 Therefore ψ(x) := z + ψ₀(x − z) for x ∈ (z + C) ∖ L (z ∈ ℤ^d) and ψ(x) := x for x ∈ L defines a map ψ : ℝ^d → ℝ^d: if x ∈ ((z + C) ∩ (z′ + C)) ∖ L then x − z′ = (z − z′) + (x − z) with x − z, x − z′ ∈ C ∖ L (L is periodic), so z′ + ψ₀(x − z′) = z′ + (z − z′) + ψ₀(x − z) = z + ψ₀(x − z).
 (i) For x ∉ L, choosing z with x ∈ z + C: ψ(x) = z + ψ₀(x − z) ∈ z + (C ∩ L_n) ⊆ L_n (L_n is ℤ^d-invariant). This is conclusion (i).
 (ii) For every z ∈ ℤ^d and x ∉ L with z_i ≤ x_i ≤ z_i + 1 for all i, ψ(x) = z + ψ₀(x − z) ∈ z + C, i.e. z_i ≤ ψ(x)_i ≤ z_i + 1 for all i. This is conclusion (ii). In particular |ψ(x) − x| ≤ diam C = √d for x ∉ L.

4. Claim (3) of the printed proof, pointwise form: there is c₁ = c₁(n, ℓ) such that, for every a with |a − q| < 1/4 and every x ∈ C ∖ L,
 (4.1) Lip_{C∖L} ψ₀(x) ≤ c₁/d_a(x).
 Proof by induction on ℓ ≥ 1 (n fixed), following the printed proof.
 Base ℓ = 1. Then d = n + 1, a point of C with n + 1 = d coordinates in a_i + ℤ equals a, so C ∩ L = {a} and ψ₀ = ψ_C. By (2.1) with t = |ψ_C(x) − a|/|x − a| ≤ √d/|x − a| and 1(a): Lip ψ₀(x) ≤ (1 + 4√d)√d/|x − a| ≤ (1 + 4√d)√d/d_a(x).
 Step ℓ − 1 → ℓ (ℓ ≥ 2). Let x ∈ C ∖ L (so x ≠ a), y := ψ_C(x) ∈ ∂C ∖ L and t := |y − a|/|x − a| ≥ 1; by (2.1), Lip ψ_C(x) ≤ (1 + 4√d)t. Let F be a (d−1)-face of C containing y, say F = C ∩ {x_{i₀} = ε}, ε ∈ {0,1}. The restriction ψ̃_F := ψ^{(n+1)}∘⋯∘ψ^{(d−1)} on F ∖ L is exactly the map ψ₀ of Step 3 built for the (n + (ℓ − 1))-dimensional cube F (coordinates J_F = {1,…,d} ∖ {i₀}) with centre point a_F — for every face G ⊆ F the projection of a_F onto Π_G is a_G — and with dual skeleton L̃ := {w ∈ Π_F : #{i ∈ J_F : w_i − a_i ∈ ℤ} ≥ n + 1}, the set L_{(ℓ−1)−1}(a_F) of the lower-dimensional construction in Π_F ≅ ℝ^{d−1}; moreover |a_F − q_F| ≤ |a − q| < 1/4 for the centre q_F of F, and F ∩ L = F ∩ L̃ by 1(d). By the induction hypothesis (applied in Π_F),
 (4.2) Lip_{F∖L} ψ̃_F(y) ≤ c₁(n, ℓ−1)/dist(y, L̃).
 Lower bound for dist(y, L̃) (printed (4)–(7), “similarity”). L̃ is the union of the planes Λ̃_{J,k} := {w ∈ Π_F : w_i = a_i + k_i (i ∈ J)}, J ⊆ J_F, |J| = n + 1, k ∈ ℤ^J. If some k_i ≠ 0 then |y_i − a_i − k_i| ≥ dist(a_i + k_i, [0,1]) > 1/4 (a_i ∈ (1/4,3/4), y_i ∈ [0,1]), so dist(y, Λ̃_{J,k}) > 1/4. If k = 0, then for y ∈ Π_F, dist(y, Λ̃_{J,0}) = (Σ_{i∈J}(y_i − a_i)²)^{1/2} = dist(y, Λ_J) with Λ_J := {w ∈ ℝ^d : w_i = a_i (i ∈ J)}, an affine plane through a contained in L. Since y − a = t(x − a) and Λ_J is invariant under the dilation w ↦ a + t(w − a), dist(y, Λ_J) = t·dist(x, Λ_J) ≥ t·d_a(x). Hence
 (4.3) dist(y, L̃) ≥ min{1/4, t·d_a(x)}.
 Chain rule. For x′ ∈ C ∖ L close to x, y′ := ψ_C(x′) is close to y and lies in some (d−1)-face F′ of C; for x′ close enough every such face contains y (faces not containing y have positive distance from y). Then ψ₀(x′) − ψ₀(x) = ψ̃_{F′}(y′) − ψ̃_{F′}(y), and from the definitions of the upper Lipschitz constants,
 Lip ψ₀(x) ≤ max_{F ∋ y} Lip_{F∖L} ψ̃_F(y) · Lip ψ_C(x) ≤ c₁(n,ℓ−1)(1 + 4√d) t / min{1/4, t d_a(x)}
 by (4.2), (4.3) (applied to each of the finitely many (d−1)-faces F ∋ y). If t d_a(x) ≤ 1/4 the right side is c₁(n,ℓ−1)(1 + 4√d)/d_a(x). Otherwise it is 4c₁(n,ℓ−1)(1 + 4√d)t ≤ 4c₁(n,ℓ−1)(1 + 4√d)√d/d_a(x), since t = |y − a|/|x − a| ≤ √d/|x − a| ≤ √d/d_a(x). So (4.1) holds with c₁(n,ℓ) := 4√d(1 + 4√d)c₁(n,ℓ−1), where d = n + ℓ and c₁(n,1) := (1 + 4√(n+1))√(n+1) is the base constant. This proves (4.1) for all ℓ ≥ 1.

5. From pointwise bounds to bounds along segments. Let γ : [0,1] → ℝ^d be continuous, p, p′ ∈ ℝ^d, and suppose that for every s ∈ [0,1], limsup_{s′→s, s′∈[0,1]} |γ(s′) − γ(s)|/(|s′ − s|·|p′ − p|) ≤ K. Then |γ(1) − γ(0)| ≤ K|p′ − p|. Indeed, for ε > 0 the set S := {s ∈ [0,1] : |γ(s) − γ(0)| ≤ (K + ε)s|p′ − p|} is closed and contains 0; if s* := max S < 1, the hypothesis at s* yields s′ ∈ (s*, 1] with |γ(s′) − γ(s*)| ≤ (K + ε)(s′ − s*)|p′ − p|, whence s′ ∈ S, a contradiction; so 1 ∈ S, and ε ↓ 0 gives the claim.

6. The Lipschitz bound (iii) (last sentence of the parent's B3). Let 0 < σ ≤ 1/4 and x, x′ ∈ {d_a ≥ σ}; put x_s := x + s(x′ − x).
 (a) |x − x′| < σ/2. Every x_s satisfies d_a(x_s) ≥ σ − |x − x′| > σ/2 (d_a is 1-Lipschitz), so the segment misses L. For each z ∈ ℤ^d the set {s ∈ [0,1] : x_s ∈ z + C} is a closed interval (convexity), only finitely many of them are nonempty, and they cover [0,1]; hence there are 0 = s₀ < s₁ < ⋯ < s_r = 1 and z_1,…,z_r with x_s ∈ z_i + C for s ∈ [s_{i−1}, s_i]. On (z_i + C) ∖ L, ψ = z_i + ψ₀(· − z_i), and d_a is ℤ^d-periodic, so by (4.1) the hypothesis of Step 5 holds for γ(s) := ψ(x_{s_{i−1} + s(s_i − s_{i−1})}) with K = c₁/(σ/2); thus |ψ(x_{s_i}) − ψ(x_{s_{i−1}})| ≤ (2c₁/σ)|x_{s_i} − x_{s_{i−1}}|, and summing, |ψ(x′) − ψ(x)| ≤ (2c₁/σ)|x′ − x|.
 (b) |x − x′| ≥ σ/2. By 3(ii), |ψ(x) − x|, |ψ(x′) − x′| ≤ √d, so |ψ(x) − ψ(x′)| ≤ |x − x′| + 2√d ≤ (1 + 4√d/σ)|x − x′| ≤ ((1/4 + 4√d)/σ)|x − x′|, using 1 ≤ 1/(4σ).
 Hence, with c := max{2c₁(n,ℓ), 1/4 + 4√d} ∈ [0,∞), depending only on (m, ℓ) (not on a), ψ is Lipschitz with constant c/σ on {x : σ ≤ dist(x, L)}, which is conclusion (iii) (with the constant c/σ = c / Real.toNNReal σ).

7. Conclusion. For every a with Σ_i(a_i − 1/2)² < 1/16 and La = L_{ℓ−1}(a), the map ψ of Step 3 satisfies (i) (Step 3), (ii) (Step 3) and (iii) (Step 6) with the constant c of Step 6, which depends only on m and ℓ. ∎

## Key steps

1. Elementary facts: a_i ∈ (1/4,3/4); La is closed, ℤ^d-periodic, contains a; x ∈ L_n iff ≥ ℓ integer coordinates; inside a face F of C, La ∩ F is a cone with vertex a_F (printed (1),(2)).
2. Radial retraction ψ_F of each j-face (j ≥ n+1) from a_F onto ∂F, mapping F∖La into ∂F∖La, with Lip ψ_F(x) ≤ (1+4√d)|ψ_F(x) − a_F|/|x − a_F| (printed (8)).
3. Composite ψ₀ = ψ^{(n+1)}∘⋯∘ψ^{(d)} on C∖La into C ∩ L_n; translation compatibility; periodic extension ψ, giving (i) and (ii).
4. Claim (3) by induction on ℓ: Lip ψ₀(x) ≤ c₁/d_a(x), via ψ₀ = ψ̃∘ψ_C, the induction hypothesis on (d−1)-faces and dist(y, L̃) ≥ min{1/4, t·d_a(x)} (printed (4)–(7), similarity).
5. Pointwise bounds integrate along segments; near points (|x−x′| < σ/2) via segments split by cubes, far points via |ψ − id| ≤ √d; Lipschitz constant c/σ on {d_a ≥ σ} (iii).

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
