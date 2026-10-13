<!-- theorem-id: gmt-ch06/root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1 -->

## Theorem `Submission.fiw_tb_translation_estimate`

Let m ∈ ℕ, n := m + 1, X ∈ D_n(ℝ^n) a current on univ, and u : ℝ^n → ℝ Lebesgue-integrable with X(ω) = ∫ u(x) ω(x)(e_1, …, e_n) dx for every ω ∈ D^n(ℝ^n), where e_i = EuclideanSpace.single i 1. Then for every h ∈ ℝ^n, ∫⁻ |u(x + h) − u(x)| dx ≤ |h| · M(∂X) in [0, ∞], M(∂X) = mass of the m-current ∂X on ℝ^n.

Node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/826

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3221, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3226, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3231, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3237

## Lean problem

Declaration: `Submission.fiw_tb_translation_estimate`

```lean
∀ (m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (u : Eucl (m + 1) → ℝ), Integrable u → (∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), X ω = ∫ x, u x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))) → ∀ h : Eucl (m + 1), ∫⁻ x, ENNReal.ofReal |u (x + h) - u x| ≤ ENNReal.ofReal ‖h‖ * X.boundary.mass
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

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2(b) (translation estimate, used for the summed form of Simon 5.1 (32)).

Notation. L := volume (Lebesgue measure) on ℝ^n; e := (e_0, …, e_m) the standard frame; for an n-form η, η_e(x) := η(x)(e). |α| := covectorEuclideanNorm α. Λ := M(∂X) = (∂X).massOn univ ∈ [0, ∞].

0. Trivial cases. If h = 0 the left side is ∫⁻ 0 = 0. If h ≠ 0 and Λ = ∞ the right side is ∞. Assume from now on Λ < ∞; write Λ also for its real value. Put w(x) := u(x + h) − u(x); w ∈ L¹(L) (translation invariance of L) and the goal is ∫|w| dL ≤ |h| Λ.
1. Mass bound for a test form (F3). If Z ∈ D_m(ℝ^n), η ∈ D^m(ℝ^n), c > 0 and |η(x)| ≤ c for all x, then |Z(η)| ≤ c·M(Z) (when M(Z) < ∞). First, homogeneity: for t ∈ ℝ and a covector α, covectorEuclideanNorm(t•α) = |t|·covectorEuclideanNorm(α), because (t•α)(e_I)² = t²·α(e_I)² for every I, so the sum under the square root is multiplied by t², and √(t²·s) = |t|·√s (this identity is not in the library and must be proved, which takes two lines). Then c⁻¹η and −c⁻¹η are admissible for M(Z) = Z.massOn univ (tsupport ⊆ univ, |±c⁻¹η(x)| = c⁻¹|η(x)| ≤ 1). By le_massOn, ofReal(c⁻¹Z(η)) ≤ M(Z) and ofReal(−c⁻¹Z(η)) ≤ M(Z), hence |Z(η)| ≤ c M(Z).
2. Divergence forms. For a smooth compactly supported vector field G = (G^0, …, G^m) : ℝ^n → ℝ^n (G^i := ⟨G, e_i⟩), let dx^{(i)} := wedgeCovectors m (fun j => EuclideanSpace.proj (i.succAbove j)) ∈ Λ^m(ℝ^n), the coordinate covector omitting direction i, and ω_G(x) := Σ_{i=0}^{m} (−1)^i G^i(x) · dx^{(i)}.
   (a) By wedgeCovectors_apply_det, dx^{(k)}(e_{i.succAbove 0}, …, e_{i.succAbove (m−1)}) = det[δ_{k.succAbove a, i.succAbove b}]_{a,b}, which is 1 if k = i and 0 if k ≠ i (then the row a with k.succAbove a = i is zero, as i is not in the range of i.succAbove). Hence ω_G(x)(e ∘ i.succAbove) = (−1)^i G^i(x).
   (b) The strictly increasing maps Fin m → Fin n are exactly the maps i.succAbove (i ∈ Fin n), each obtained once. Indeed, a strictly increasing I : Fin m → Fin (m+1) is not surjective (cardinality), so pick k ∉ range I; then range I ⊆ {k}ᶜ = range k.succAbove (Fin.range_succAbove), both ranges have m elements (injectivity), so they are equal, and two strictly increasing maps with the same range are equal (StrictMono.range_inj_of_wellFoundedLT). Conversely each k.succAbove is strictly increasing (Fin.strictMono_succAbove), and k ↦ k.succAbove is injective (Fin.succAbove_left_injective). So, by the definition of covectorEuclideanNorm, |ω_G(x)| = (Σ_i G^i(x)²)^{1/2} = ‖G(x)‖.
   (c) ω_G is smooth with compact support, so ω_G ∈ D^m(ℝ^n).
   (d) By exteriorDerivative_apply (extDeriv_apply), dω_G(x)(e) = Σ_{i=0}^{m} (−1)^i D[y ↦ ω_G(y)(i.removeNth e)](x)(e_i), and i.removeNth e = e ∘ i.succAbove. By (a), ω_G(y)(i.removeNth e) = (−1)^i G^i(y), so dω_G(x)(e) = Σ_i ∂_i G^i(x) = div G(x).
   (e) By the hypothesis applied to the test form dω_G (= exteriorDerivativeTestOn univ m ω_G), and by GeometricCurrentOn.boundary_apply: ∫ u div G dL = X(dω_G) = (∂X)(ω_G). By step 1 and (b): if c > 0 and ‖G(x)‖ ≤ c for all x, then |ω_G(x)| ≤ c for all x and |∫ u div G dL| ≤ c Λ.
3. Weak estimate. Let g ∈ C_c^∞(ℝ^n) with |g| ≤ 1. Then |∫ w g dL| ≤ |h| Λ. Proof: by translation invariance, ∫ u(x + h) g(x) dx = ∫ u(y) g(y − h) dy, so ∫ w g = ∫ u(y)(g(y − h) − g(y)) dy. For each y, t ↦ g(y − th) is C¹ with derivative −Dg(y − th)(h), so g(y − h) − g(y) = −∫_0^1 Dg(y − th)(h) dt (fundamental theorem of calculus). The function (y, t) ↦ u(y) Dg(y − th)(h) is measurable and bounded by |u(y)| sup‖Dg‖ ‖h‖, hence integrable on ℝ^n × [0, 1]; by Fubini, ∫ w g = −∫_0^1 (∫ u(y) Dg(y − th)(h) dy) dt. For fixed t put G_t(y) := g(y − th) h, a smooth compactly supported vector field with div G_t(y) = Σ_i h_i ∂_i g(y − th) = Dg(y − th)(h) and ‖G_t(y)‖ = |g(y − th)| ‖h‖ ≤ ‖h‖. By step 2(e) with c := ‖h‖ > 0 (h ≠ 0 by step 0), |∫ u(y) Dg(y − th)(h) dy| ≤ ‖h‖ Λ for every t, so |∫ w g| ≤ ∫_0^1 ‖h‖ Λ dt = ‖h‖ Λ.
4. From smooth g to |w| (inner/outer regularity and smooth Urysohn functions). Let w̃ be a Borel (strongly measurable) function with w̃ = w L-a.e. (AEStronglyMeasurable.mk), and ν := L.withDensity(x ↦ ofReal|w̃(x)|). Then ν(E) = ∫_E |w| dL for every Borel set E (withDensity_apply), and ν is a finite measure with ν(ℝ^n) = ∫ |w| dL (isFiniteMeasure_withDensity_ofReal). For a finite measure on Eucl n the instances InnerRegularCompactLTTop and OuterRegular are inferred automatically, so MeasurableSet.exists_isCompact_diff_lt and MeasurableSet.exists_isOpen_diff_lt apply to ν. Fix ε > 0 and put A⁺ := {w̃ > 0}, A⁻ := {w̃ < 0}, disjoint Borel sets.
   (a) Choose compact K^± ⊆ A^± with ν(A^± ∖ K^±) < ε. Then K⁺ and K⁻ are disjoint.
   (b) Choose open O^± ⊇ K^± with ν(O^± ∖ K^±) < ε. As K⁺ and K⁻ are disjoint compact sets, there is δ > 0 with thickening(δ, K⁺) ∩ thickening(δ, K⁻) = ∅ (Disjoint.exists_thickenings). Replacing O^± by O^± ∩ thickening(δ, K^±), which is still open, contains K^± and satisfies ν(O^± ∖ K^±) < ε, we may assume O⁺ ∩ O⁻ = ∅.
   (c) By IsCompact.exists_cthickening_subset_open there is r > 0 with L^± := cthickening(r, K^±) ⊆ O^±. L^± is compact (closed and bounded in Eucl n), and K^± ⊆ thickening(r, K^±) ⊆ interior L^±. Smooth Urysohn (exists_contMDiffMap_one_nhds_of_subset_interior with model 𝓘(ℝ, Eucl n), s := K^± (closed), t := L^±; ContMDiff for this model is ContDiff ℝ ∞) gives smooth g^± with values in [0, 1], g^± = 1 on K^± and g^± = 0 outside L^±. Hence tsupport g^± ⊆ L^± (L^± is closed) and g^± has compact support.
   (d) Put g := g⁺ − g⁻, smooth with compact support. Since L⁺ ⊆ O⁺ and L⁻ ⊆ O⁻ are disjoint, at every point at most one of g⁺, g⁻ is nonzero, so |g| ≤ 1; moreover g = 1 on K⁺, g = −1 on K⁻ and g = 0 outside O⁺ ∪ O⁻.
   (e) Since w = w̃ a.e., ∫ w g dL = ∫ w̃ g dL (all integrals here are finite: w ∈ L¹ and |g| ≤ 1). Split ℝ^n into the disjoint Borel sets K⁺, K⁻, O⁺ ∖ K⁺, O⁻ ∖ K⁻ and the remaining set, on which g = 0. On K⁺, w̃g = w̃ = |w̃|; on K⁻, w̃g = −w̃ = |w̃|; on O^± ∖ K^±, w̃g ≥ −|w̃|. Hence ∫ w g dL ≥ ν(K⁺) + ν(K⁻) − ν(O⁺ ∖ K⁺) − ν(O⁻ ∖ K⁻) > ν(A⁺) + ν(A⁻) − 4ε = ν(ℝ^n) − 4ε = ∫ |w| dL − 4ε, where ν(A⁺) + ν(A⁻) = ν(ℝ^n) because the density of ν vanishes on {w̃ = 0}.
   (f) By step 3, ∫ w g dL ≤ ‖h‖Λ. Hence ∫ |w| dL < ‖h‖Λ + 4ε for every ε > 0, so ∫ |w| dL ≤ ‖h‖Λ. Since w is integrable, ∫⁻ ofReal|w| dL = ofReal(∫ |w| dL) (ofReal_integral_eq_lintegral_ofReal), and therefore ∫⁻ ofReal|u(x + h) − u(x)| dx ≤ ofReal(‖h‖Λ) = ofReal‖h‖ · M(∂X). ∎

Library note. Every fact cited above is available under the imports of GMT.Ch06.Submission (intervalIntegral.integral_eq_sub_of_hasDerivAt, MeasureTheory.integral_integral_swap, integral_add_right_eq_self, exists_contMDiffMap_one_nhds_of_subset_interior, Disjoint.exists_thickenings, IsCompact.exists_cthickening_subset_open and the regularity instances were checked); no mollifier (ContDiffBump.normed and its a.e. convergence lemma are not imported) is used.

Remark (adaptable accepted Lean proofs; not needed for the argument above).
- Step 1 is the comparator-accepted Submission.cmb_abs_apply_le_of_massOn_le (commit ba202ac0407b6e93210594416fcd0729874b2eff): |T ω| ≤ B·C whenever 0 ≤ B, T.massOn W ≤ ENNReal.ofReal B, tsupport ω ⊆ W and covectorEuclideanNorm(ω(x)) ≤ C for all x.
- With dx := wedgeCovectors n (fun j => EuclideanSpace.proj j), the form Σ_j G^j • (dx.curryLeft e_j) coincides with ω_G of step 2: both take the value (−1)^i G^i on e ∘ i.succAbove. The Lean computation d(a • dx.curryLeft e_j)(x)(e) = D_j a(x), via exteriorDerivative_apply, Fin.cons_removeNth_eq_comp_cycleRange_symm and Fin.sign_cycleRange, is in the comparator-accepted Submission.constancy_closed_kills_partial_derivatives (commit 469f013363eae50dbd864d795703cdc6930d8086).
- Step 1 is also exactly the comparator-accepted Submission.br_la_abs_apply_le_mul_mass (commit d771ac3ae563701d45563ad2e197624b3f42977f): for Y : GeometricCurrentOn U n, ω : TestFormOn U n and C > 0 with covectorEuclideanNorm (ω x) ≤ C for all x and Y.mass ≠ ∞, |Y ω| ≤ C * Y.mass.toReal. Apply it with U := univ, Y := Z, ω := η and C := c.
All these proofs may be adapted under fresh names.

## Key steps

1. |Z(η)| ≤ sup|η| · M(Z) by rescaling to admissible forms.
2. For a vector field G, the m-form ω_G = Σ(−1)^i G^i dx^{(i)} has |ω_G| = |G| and dω_G(e) = div G, so |∫ u div G| = |∂X(ω_G)| ≤ sup|G| M(∂X).
3. With G_t(y) = g(y − th)h, FTC and Fubini give |∫ (u(·+h) − u) g| ≤ |h| M(∂X) for smooth g with |g| ≤ 1.
4. Inner/outer regularity of the finite measure |w| dL and smooth Urysohn functions give g ∈ C_c^∞ with |g| ≤ 1 and ∫ w g ≥ ∫ |w| − 4ε, so ∫ |u(·+h) − u| ≤ |h| M(∂X).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c95, Mathlib 25730c7c)`
- `python3 scan of dag.json (235 nodes): no lean_name containing fiw_tb; frozen lean_statement of root.flat_iff_weak-a1.im_mass_formula-a1 (accepted) and im_lincomb-a1 compared textually with the MF/LC premises`
- `git log --all --oneline -S fiw_tb_ (687 refs, no match); grep -rl fiw_tb_ .humanize/math-wiki (no match)`
- `git show <commit>:GMT/Ch06/Submission.lean | grep -c 'theorem Submission.<name>' for the 12 cited accepted declarations (all present), including br_la_abs_apply_le_mul_mass @ d771ac3a and fiw_ims_frame_sign @ c90a4050`
- `grep -n max_nodes /runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py; read _decompose, _solve_children, _existing_lean_name_problem; swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json (max_nodes 1000, max_children 12, max_depth 6)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def TestFormOnConverges|structure GeometricCurrentOn|zero_apply|boundary_apply|restrictDomain_apply|def testFormOnInclusion|def GeometricCurrentOn.zeroRegion|def GeometricCurrentOn.support|abbrev SimonMultiIndex|def CountablyRectifiable|countablyRectifiable_of_measure_zero|def blowUpMap|def HasWeightedApproximateTangentSpaceAt' in SimonGMT Chapter06/Chapter03`
- `grep Mathlib: theorem exists_nnreal_pos_mul_lt, Finite.exists_infinite_fiber, Infinite.exists_ne_map_eq_of_mapsTo, thickening_subset_of_subset, cthickening_subset_of_subset, thickening_subset_cthickening, mul_le_mul_right`
- `lake build GMT.Ch06.Submission in /tmp/tb5-Hq3Nws (git archive d8d46c9, packages linked)`
- `python3 -I /tmp/tb5_tools/gen_challenges.py (verifier/gmt-compare.py child_modules mode contract + lean_contract.validate_lean_statement); lake env lean Scratch/V4/Ch_*.lean and Scratch/V4/Remaining3.lean (0 errors)`
- `lake env lean Scratch/V4/Assembly.lean and Scratch/V4/FiniteNet.lean (#print axioms: propext, Classical.choice, Quot.sound)`
- `sed -n 2028,2090p book/chapter-06.txt (Simon 7.2 and its proof, (1)–(3))`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/8d6f8e1fdf494359a56bc7f71c57d439.json`
- `/runtime/flows/gmt-claude-40bcd6e5b78a/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-br-la-abs-apply-le-mul-mass.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-frame-sign.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-im-mass-formula.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Data/Fintype/Pigeonhole.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Assembly.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/FiniteNet.lean`
- `/tmp/tb5-Hq3Nws/Scratch/V4/Remaining3.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract (IsIntegerMultiplicity, IsRectifiableTriple, tauAction, latticeFace, latticeFaceAction, IsLatticeChain, DeformationTheorem). Neither the project nor SimonGMT has an integer-multiplicity calculus, a flat-norm lemma or a lattice-chain coefficient bound, so these become the 10 children.

SimonGMT supplies the API used in the child proofs:
- massOn and mass via massAdmissibleOn and covectorEuclideanNorm, and le_massOn / massOn_mono;
- restrictDomain(_apply), testFormOnInclusion, zero_apply, boundary_apply and GeometricCurrentOn.ext;
- zeroRegion and support = U \ zeroRegion;
- SimonMultiIndex = Fin n ↪o Fin p, CountablyRectifiable (with countablyRectifiable_of_measure_zero and .mono), blowUpMap and HasWeightedApproximateTangentSpaceAt.
Mathlib supplies ENNReal.exists_nnreal_pos_mul_lt and the thickening lemmas.

Accepted Submission declarations, cited in the remarks as optional reuse pointers, were checked at their commits. The two new pointers are:
- br_la_abs_apply_le_mul_mass (d771ac3a), the evaluation bound;
- fiw_ims_frame_sign (c90a4050), the frame sign.

Scratch checks:
- all 10 child types elaborate in the comparator's exact challenge scope;
- the parent type follows from MF, LC, fiw_tb_finite_net and fiw_tb_flat_sub;
- fiw_tb_finite_net follows from its five siblings;
- both derivations use only [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
