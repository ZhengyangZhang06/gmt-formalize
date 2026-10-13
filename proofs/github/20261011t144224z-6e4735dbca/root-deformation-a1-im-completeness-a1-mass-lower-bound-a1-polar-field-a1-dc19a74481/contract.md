<!-- theorem-id: gmt-ch06/root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_field-a1 -->

## Theorem `Submission.imc_mlb_exists_unit_field_integral_ge`

Let N ∈ ℕ, let E be a real inner product space (E : Type with NormedAddCommGroup E and InnerProductSpace ℝ E), let μ be a measure on ℝ^N = Eucl N, let R ∈ ℝ, B := ball(0, R) (the open ball), and let g : ℝ^N → E be μ-integrable on B (IntegrableOn g B μ). Then for every real ε > 0 there is F : ℝ^N → E such that F is continuous, tsupport F ⊆ B, ‖F(x)‖ ≤ 1 for every x, the function x ↦ ⟨F(x), g(x)⟩ (inner ℝ) is μ-integrable on ℝ^N, and ∫_B ‖g(x)‖ dμ(x) ≤ ∫ ⟨F(x), g(x)⟩ dμ(x) + ε.

Node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_field-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3244

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4229

Decomposition children: None

## Lean problem

Declaration: `Submission.imc_mlb_exists_unit_field_integral_ge`

```lean
∀ (N : ℕ) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure (Eucl N)) (R : ℝ) (g : Eucl N → E), IntegrableOn g (ball (0 : Eucl N) R) μ → ∀ ε : ℝ, 0 < ε → ∃ F : Eucl N → E, Continuous F ∧ tsupport F ⊆ ball (0 : Eucl N) R ∧ (∀ x, ‖F x‖ ≤ 1) ∧ Integrable (fun x => inner ℝ (F x) (g x)) μ ∧ ∫ x in ball (0 : Eucl N) R, ‖g x‖ ∂μ ≤ ∫ x, inner ℝ (F x) (g x) ∂μ + ε
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

- Parent DAG node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1`
- Child DAG node: `root.deformation-a1.im_completeness-a1.mass_lower_bound-a1.polar_field-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 3, 5 and 6 of the supplied proof of imc_lintegral_coordNorm_le_mass (the finite measure ν = |κ|μ⌞B_R and the polar field u = κ/|κ|; the cut-off χ near ∂B_R and the radial retraction π; the estimate ∫χ⟨π(g₀), u⟩ dν ≥ ν(ℝ^N) − O(ε)), written for a vector field g with values in a real inner product space E (in the parent, g = c(κ) ∈ ℝ^I). Step 4 of the supplied proof (the L¹ approximation g₀) is the sibling l1_density.

Notation. B := ball(0, R) (open), B̄_r := closedBall(0, r), μ⌞B := μ.restrict B. ⟨·,·⟩ is the real inner product of E and ‖·‖ its norm. For a set S and a function φ, ∫_S φ dμ is the Bochner integral over S.

0. (Pairing with admissible fields.) Let F : ℝ^N → E be continuous with ‖F(x)‖ ≤ 1 for all x and F(x) = 0 for x ∉ B. Then x ↦ ⟨F(x), g(x)⟩ is μ-integrable and ∫ ⟨F, g⟩ dμ = ∫_B ⟨F, g⟩ dμ.
 - It is a.e. strongly measurable for μ⌞B: x ↦ (F(x), g(x)) is a.e. strongly measurable (F continuous, g a.e. strongly measurable for μ⌞B since g is μ⌞B-integrable; AEStronglyMeasurable.prodMk), and (a, b) ↦ ⟨a, b⟩ is continuous (continuous_inner.comp_aestronglyMeasurable).
 - |⟨F(x), g(x)⟩| ≤ ‖F(x)‖‖g(x)‖ ≤ ‖g(x)‖ (Cauchy–Schwarz, norm_inner_le_norm), and ‖g‖ is μ⌞B-integrable. So ⟨F, g⟩ is μ-integrable on B (Integrable.mono').
 - ⟨F(x), g(x)⟩ = ⟨0, g(x)⟩ = 0 for x ∉ B. A function integrable on B whose support lies in B is integrable (integrableOn_iff_integrable_of_support_subset), and its integral equals the integral over B (setIntegral_eq_integral_of_forall_compl_eq_zero).

1. (The case R ≤ 0.) Then B = ∅ (ball_eq_empty). F := 0 is continuous, tsupport 0 = ∅ ⊆ B, ‖0‖ = 0 ≤ 1, ⟨0, g(x)⟩ = 0 is integrable, and ∫_∅ ‖g‖ dμ = 0 ≤ 0 + ε = ∫⟨0, g⟩ dμ + ε. From now on R > 0.

2. (Measurable modification and polar decomposition.) g is μ⌞B-integrable, hence a.e. strongly measurable for μ⌞B; choose a strongly measurable g̃ : ℝ^N → E with g = g̃ μ⌞B-a.e. (AEStronglyMeasurable.mk, stronglyMeasurable_mk, ae_eq_mk). Put ρ(x) := ‖g̃(x)‖ ≥ 0 and u(x) := ρ(x)⁻¹·g̃(x), with the convention 0⁻¹ = 0 (so u(x) = 0 when g̃(x) = 0).
 - ρ is strongly measurable (norm), u is strongly measurable (the measurable real function ρ⁻¹ times the strongly measurable g̃).
 - For every x: ‖u(x)‖ ≤ 1; ‖u(x)‖ = 1 if g̃(x) ≠ 0 (then ‖u(x)‖ = ρ(x)⁻¹ρ(x) = 1); and g̃(x) = ρ(x)·u(x) (both sides are 0 if g̃(x) = 0, and ρρ⁻¹g̃ = g̃ otherwise).
 - ρ = ‖g‖ μ⌞B-a.e., so ρ is μ⌞B-integrable and ∫_B ‖g‖ dμ = ∫_B ρ dμ.

3. (The finite measure ν.) Let ν := (μ⌞B).withDensity (x ↦ ofReal ρ(x)), i.e. ν(S) = ∫⁻_{S ∩ B} ofReal ρ dμ for measurable S.
 - ν(ℝ^N) = ∫⁻_B ofReal ρ dμ = ofReal(∫_B ρ dμ) < ∞ (ofReal_integral_eq_lintegral_ofReal, ρ ≥ 0 integrable), so ν is a finite measure (isFiniteMeasure_withDensity).
 - For measurable S ⊆ B: ν(S) = ∫⁻_S ofReal ρ dμ = ofReal(∫_S ρ dμ) (withDensity_apply, Measure.restrict_restrict, S ∩ B = S, and ρ integrable on S ⊆ B).
 - u ∈ L¹(ν): u is strongly measurable, ‖u‖ ≤ 1 and ν is finite (MemLp.of_bound).

4. (Inner radius R'.) Claim: there is R' with 0 < R' < R and ν(B ∖ B̄_{R'}) < ofReal(ε/4).
 - For n ∈ ℕ let r_n := R − R/(n + 2) and s_n := B ∖ B̄_{r_n}. Since R > 0, r_n is increasing in n, so (s_n) is decreasing; each s_n is measurable (open minus closed); ν(s_0) < ∞.
 - ⋂_n s_n = ∅: if x ∈ B then ‖x‖ < R; choose n ∈ ℕ with n > R/(R − ‖x‖) (Archimedes); then R/(n + 2) < R − ‖x‖, i.e. ‖x‖ < r_n, so x ∈ B̄_{r_n} and x ∉ s_n. Points outside B lie in no s_n.
 - By continuity from above of the finite measure ν (tendsto_measure_iInter_atTop), ν(s_n) → ν(∅) = 0. As ofReal(ε/4) > 0, some n has ν(s_n) < ofReal(ε/4). Take R' := r_n; then 0 < R' (because R/(n+2) < R) and R' < R (because R/(n+2) > 0).

5. (L¹ approximation, sibling l1_density.) Apply l1_density to N, E, the finite measure ν, f := u ∈ L¹(ν) and the nonzero ε' := ofReal(ε/4): there is g₀ : ℝ^N → E with compact support, continuous (and in L¹(ν)), such that eLpNorm (u − g₀) 1 ν ≤ ofReal(ε/4). Since eLpNorm (u − g₀) 1 ν = ∫⁻ ‖u − g₀‖ₑ dν (eLpNorm_one_eq_lintegral_enorm; u − g₀ is strongly measurable) and, by the integral formula for a measure with a measurable density (lintegral_withDensity_eq_lintegral_mul; x ↦ ofReal ρ(x) and x ↦ ‖u(x) − g₀(x)‖ₑ are measurable), ∫⁻ ‖u − g₀‖ₑ dν = ∫⁻_B ofReal(ρ(x))·‖u(x) − g₀(x)‖ₑ dμ = ∫⁻_B ofReal(ρ(x)‖g₀(x) − u(x)‖) dμ, we get
  ∫⁻_B ofReal(ρ(x)‖g₀(x) − u(x)‖) dμ(x) ≤ ofReal(ε/4).   (5.1)
 Since g₀ is continuous with compact support it is bounded: ‖g₀(x)‖ ≤ C₀ for all x (Continuous.bounded_above_of_compact_support).

6. (Cut-off.) Let R'' := (R + R')/2, so R' < R'' < R, and χ(x) := min{1, max{0, (R'' − ‖x‖)/(R'' − R')}}.
 - χ is continuous and 0 ≤ χ ≤ 1.
 - If ‖x‖ ≤ R' then (R'' − ‖x‖)/(R'' − R') ≥ 1, so χ(x) = 1. If ‖x‖ ≥ R'' then (R'' − ‖x‖)/(R'' − R') ≤ 0, so χ(x) = 0.
 - Hence support χ ⊆ ball(0, R''), and tsupport χ ⊆ closure(ball(0, R'')) ⊆ B̄_{R''} ⊆ B (closure_ball_subset_closedBall, closedBall_subset_ball since R'' < R).

7. (Radial retraction.) For a ∈ E let π(a) := max{1, ‖a‖}⁻¹·a. Since max{1, ‖a‖} ≥ 1 > 0 depends continuously on a, π is continuous. ‖π(a)‖ = ‖a‖/max{1, ‖a‖} ≤ 1. Claim: ‖π(a) − b‖ ≤ 2‖a − b‖ whenever ‖b‖ ≤ 1. If ‖a‖ ≤ 1 then π(a) = a and the claim is trivial. If t := ‖a‖ > 1 then π(a) − a = (1/t − 1)a has norm (1 − 1/t)t = t − 1 ≤ ‖a‖ − ‖b‖ ≤ ‖a − b‖, so ‖π(a) − b‖ ≤ ‖π(a) − a‖ + ‖a − b‖ ≤ 2‖a − b‖. (Step 0(f) of the supplied proof shows the sharper ‖π(a) − b‖ ≤ ‖a − b‖ in an inner product space: ‖a − b‖² − ‖a/t − b‖² = t² − 1 − 2(1 − 1/t)⟨a, b⟩ ≥ (t − 1)² ≥ 0; either bound suffices below, the ε-budget is chosen for the factor 2.)

8. (The competitor F.) F(x) := χ(x)·π(g₀(x)).
 - F is continuous (χ, π and g₀ are continuous).
 - tsupport F ⊆ tsupport χ ⊆ B (tsupport_smul_subset_left and Step 6); in particular F(x) = 0 for x ∉ B (image_eq_zero_of_notMem_tsupport).
 - ‖F(x)‖ = χ(x)‖π(g₀(x))‖ ≤ 1·1 = 1.
 By Step 0, x ↦ ⟨F(x), g(x)⟩ is μ-integrable (this is the fourth conclusion) and ∫ ⟨F, g⟩ dμ = ∫_B ⟨F, g⟩ dμ = ∫_B ⟨F, g̃⟩ dμ, the last because g = g̃ μ⌞B-a.e.

9. (Pointwise estimate.) For every x ∈ ℝ^N:
  ρ(x) − ρ(x)(1 − χ(x)) − 2ρ(x)‖g₀(x) − u(x)‖ ≤ ⟨F(x), g̃(x)⟩.   (9.1)
 By Step 2, ⟨F(x), g̃(x)⟩ = ⟨χ(x)π(g₀(x)), ρ(x)u(x)⟩ = χ(x)ρ(x)⟨π(g₀(x)), u(x)⟩ (real_inner_smul_left, real_inner_smul_right).
 - If g̃(x) = 0, then ρ(x) = 0 and both sides of (9.1) are 0.
 - Otherwise ‖u(x)‖ = 1. Write ⟨π(g₀(x)), u(x)⟩ = ⟨u(x), u(x)⟩ + ⟨π(g₀(x)) − u(x), u(x)⟩ = 1 + ⟨π(g₀(x)) − u(x), u(x)⟩ ≥ 1 − ‖π(g₀(x)) − u(x)‖·‖u(x)‖ ≥ 1 − 2‖g₀(x) − u(x)‖ (Cauchy–Schwarz, abs_real_inner_le_norm, and Step 7 with b := u(x), ‖u(x)‖ ≤ 1). Multiplying by χ(x)ρ(x) ≥ 0: χρ⟨π(g₀), u⟩ ≥ χρ − 2χρ‖g₀ − u‖ ≥ χρ − 2ρ‖g₀ − u‖, using 0 ≤ χ ≤ 1 and ρ‖g₀ − u‖ ≥ 0. Finally χρ = ρ − ρ(1 − χ).

10. (Integrability on B.) With respect to μ⌞B the following are integrable: ρ (Step 2); ρ(1 − χ), which is ρ times the continuous function 1 − χ with values in [0, 1] (Integrable.mul_bdd); ρ‖g₀ − u‖, which is ρ times the strongly measurable function ‖g₀ − u‖ bounded by C₀ + 1 (Step 5 and ‖u‖ ≤ 1); and ⟨F, g̃⟩, which is a.e. strongly measurable with |⟨F, g̃⟩| ≤ ‖F‖‖g̃‖ ≤ ρ (Integrable.mono').

11. (The two error terms.)
 (a) ∫_B ρ(1 − χ) dμ ≤ ε/4. For x ∈ B: if ‖x‖ ≤ R' then χ(x) = 1 and ρ(x)(1 − χ(x)) = 0 ≤ 1_{B∖B̄_{R'}}(x)ρ(x); if ‖x‖ > R' then x ∈ B ∖ B̄_{R'} and ρ(x)(1 − χ(x)) ≤ ρ(x) because 0 ≤ 1 − χ ≤ 1. Hence (setIntegral_mono_on, then setIntegral_indicator with B ∩ (B ∖ B̄_{R'}) = B ∖ B̄_{R'}) ∫_B ρ(1 − χ) dμ ≤ ∫_{B∖B̄_{R'}} ρ dμ. By Step 3 (S := B ∖ B̄_{R'} ⊆ B measurable) and Step 4, ofReal(∫_{B∖B̄_{R'}} ρ dμ) = ν(B ∖ B̄_{R'}) < ofReal(ε/4), hence ∫_{B∖B̄_{R'}} ρ dμ < ε/4 (ENNReal.ofReal_lt_ofReal_iff, ε/4 > 0).
 (b) ∫_B ρ‖g₀ − u‖ dμ ≤ ε/4. By Step 10 and nonnegativity, ofReal(∫_B ρ‖g₀ − u‖ dμ) = ∫⁻_B ofReal(ρ‖g₀ − u‖) dμ (ofReal_integral_eq_lintegral_ofReal), which is ≤ ofReal(ε/4) by (5.1); hence ∫_B ρ‖g₀ − u‖ dμ ≤ ε/4 (ENNReal.ofReal_le_ofReal_iff, ε/4 ≥ 0).

12. (Conclusion.) Integrating (9.1) over B with respect to μ (integral_mono; all functions are μ⌞B-integrable by Step 10; integral_sub, integral_const_mul):
  ∫_B ρ dμ − ∫_B ρ(1 − χ) dμ − 2∫_B ρ‖g₀ − u‖ dμ ≤ ∫_B ⟨F, g̃⟩ dμ.
 By Steps 2, 8 and 11: ∫_B ‖g‖ dμ = ∫_B ρ dμ ≤ ∫_B ⟨F, g̃⟩ dμ + ε/4 + 2·(ε/4) = ∫ ⟨F, g⟩ dμ + 3ε/4 ≤ ∫ ⟨F, g⟩ dμ + ε. Together with Step 8 (continuity, tsupport F ⊆ B, ‖F‖ ≤ 1, integrability) this proves the statement. ∎

Formalization note: a complete Lean proof of exactly this frozen statement following Steps 0–12 (with l1_density as a hypothesis) was compiled during the decomposition review in the comparator scope at default heartbeats, with axioms propext, Classical.choice, Quot.sound only (scratch copy /tmp/mlb_split/lean/ChildB.lean on the decomposition host; it is not a persistent artifact, and Steps 0–12 above are self-sufficient). Lemma names that worked at this Mathlib pin: le_or_gt, ball_eq_empty, AEStronglyMeasurable.mk/stronglyMeasurable_mk/ae_eq_mk, Measurable.inv(.stronglyMeasurable).smul, isFiniteMeasure_withDensity, withDensity_apply, MemLp.of_bound, tendsto_measure_iInter_atTop, lintegral_withDensity_eq_lintegral_mul, StronglyMeasurable.enorm, eLpNorm_one_eq_lintegral_enorm, ofReal_norm, Continuous.bounded_above_of_compact_support, continuous_inner.comp_aestronglyMeasurable with AEStronglyMeasurable.prodMk (MeasureTheory.AEStronglyMeasurable.inner is not in the import closure), Integrable.mul_bdd, setIntegral_mono_on, setIntegral_indicator, integral_mono, integral_sub (state the integrability facts for the explicit lambdas before rewriting).

## Key steps

1. Any continuous F with ‖F‖ ≤ 1 vanishing off B pairs integrably with g (|⟨F, g⟩| ≤ ‖g‖ on B, zero off B), and ∫⟨F, g⟩ dμ = ∫_B ⟨F, g⟩ dμ; for R ≤ 0, F = 0 works.
2. Replace g on B by a strongly measurable g̃ = g μ⌞B-a.e.; ρ := ‖g̃‖, u := ρ⁻¹g̃ (u = 0 where g̃ = 0), so ‖u‖ ≤ 1, ‖u‖ = 1 where g̃ ≠ 0 and g̃ = ρu; ν := (μ⌞B).withDensity ρ is finite and u ∈ L¹(ν).
3. Continuity from above for the finite ν gives R' ∈ (0, R) with ν(B ∖ B̄_{R'}) < ε/4; the sibling l1_density gives continuous compactly supported g₀ with ∫⁻_B ρ‖g₀ − u‖ dμ = ‖u − g₀‖_{L¹(ν)} ≤ ε/4.
4. F := χ·π(g₀) with the radial cut-off χ (1 on B̄_{R'}, 0 off ball(0, (R+R')/2)) and the radial retraction π(a) = a/max{1,‖a‖} (‖π(a) − b‖ ≤ 2‖a − b‖ for ‖b‖ ≤ 1): F is continuous, ‖F‖ ≤ 1, tsupport F ⊆ B.
5. Pointwise ⟨F, g̃⟩ = χρ⟨π(g₀), u⟩ ≥ ρ − ρ(1 − χ) − 2ρ‖g₀ − u‖; integrating over B and bounding ∫_B ρ(1 − χ) ≤ ν(B ∖ B̄_{R'}) and ∫_B ρ‖g₀ − u‖ by ε/4 gives ∫_B ‖g‖ ≤ ∫⟨F, g⟩ + 3ε/4.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp <snapshot>/project/GMT/Ch06/Submission.lean GMT/Ch06/Submission.lean (both byte-identical)`
- `python3 -I over dag.json: all accepted nodes and lean_statements (cmb_*, smr_ci_*, smr_ufd_*, polyhedral_approx_pairing_*, fiw_*), status/candidate_commit of the four reused nodes, collision check for imc_mlb_exists_hasCompactSupport_eLpNorm_sub_le, imc_mlb_exists_unit_field_integral_ge, imc_mlb_exists_form_lintegral_coordNorm_le (none), node count (531)`
- `isolated-comparator-result.json and parent-child-handoff.json of root.compactness_mass_bounds-a1.repr_bound-a1, root.compactness_mass_bounds-a1.repr_bound-a1.coeff_integrable-a1, root.slicing-a1.mass_representation-a1.covector_isometry-a1.coord_sum_wedge-a1, root.slicing-a1.mass_representation-a1.covector_isometry-a1.norm_coord-a1 (all passed; accepted natural proofs copied verbatim)`
- `git show <commit>:GMT/Ch06/Submission.lean | grep 'theorem Submission.<name>' for 5caba500 (cmb_measureRepresentation_continuous_bound), 3cd72266 (cmb_rb_measureRepresentation_integrableOn_coeff), 1b431e81 (smr_ci_coord_sum_smul_wedge), a1716c42 (smr_ci_norm_eq_sqrt_sum_coord_sq)`
- `git show 83e1f61809c1:GMT/Ch06/Submission.lean | sed -n 374,560p (accepted hdense, hmoll, hretr helpers of fiw_im_mass_formula)`
- `grep -n 'theorem\|lemma' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean (GeometricCurrentOn.massOn_mono, GeometricCurrentOn.le_massOn; definitions of covectorEuclideanNorm, massAdmissibleOn, massOn, mass)`
- `rg -n 'theorem lintegral_iUnion|theorem setLIntegral_iUnion|iSup_restrict|theorem lintegral_iSup_directed' <snapshot>/mathlib/Mathlib (setLIntegral_iUnion_of_directed at MeasureTheory/Integral/Lebesgue/Basic.lean:668, no measurability hypothesis)`
- `rg -n 'theorem MemLp.induction_dense|theorem exists_Lp_half|theorem exists_eLpNorm_indicator_le' <snapshot>/mathlib/Mathlib`
- `rg -n 'AEStronglyMeasurable.inner|bounded_above_of_compact_support|theorem lintegral_withDensity_eq_lintegral_mul|isFiniteMeasure_withDensity|theorem tendsto_measure_iInter_atTop|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem integrableOn_iff_integrable_of_support_subset|theorem eLpNorm_one_eq_lintegral_enorm|theorem MemLp.of_bound|theorem withDensity_apply|ofReal_norm|theorem Integrable.bdd_mul' <snapshot>/mathlib/Mathlib`
- `rg -n imc_mlb <snapshot>/project lake-packages-25730c7c/simongmt/Poincare; grep -rl --include=*.json imc_mlb runs/20261011T144224Z-6e4735dbca/nodes; git log --all --oneline -S imc_mlb (no match anywhere)`
- `python3 -I: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') for the child challenge scope; runtime lean_contract.validate_lean_statement on all seven types; key/name regexes and topological order`
- `sed -n 6532,6575p /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (cross-branch reuse rule), store.py ensure (existing nodes reused unchanged), decomposition_scope.py, prompts.py DECOMPOSE/DECOMPOSITION_AUDIT, swarm-project.json (max_depth 6, max_children 12, max_nodes 1000)`
- `lake env lean /tmp/mlb_split/lean/{Probe0,ApiC,Api2,Stmts,FinalStmts,Parent,ChildA,ChildB,ChildC,All,AllFull}.lean (FinalStmts: all seven child types elaborate in the comparator scope; AllFull: parent and all children sorry-free, #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-mass-lower-bound-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1-coeff-integrable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-repr-bound-a1-coeff-integrable-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-covector-isometry-a1-coord-sum-wedge-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-covector-isometry-a1-coord-sum-wedge-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-covector-isometry-a1-norm-coord-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-covector-isometry-a1-norm-coord-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/decomposition_scope.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/tmp/mlb_split/lean/FinalStmts.lean`
- `/tmp/mlb_split/lean/Parent.lean`
- `/tmp/mlb_split/lean/ChildA.lean`
- `/tmp/mlb_split/lean/ChildB.lean`
- `/tmp/mlb_split/lean/ChildC.lean`
- `/tmp/mlb_split/lean/AllFull.lean`

Pinned revisions confirmed; the frozen contract is byte-identical to the snapshot. Four comparator-accepted declarations cover Steps 1, 2 and the linear algebra of Step 0 of the supplied proof with exactly the needed types and are reused by name with byte-identical frozen types: cmb_rb_measureRepresentation_integrableOn_coeff (3cd72266), cmb_measureRepresentation_continuous_bound (5caba500; Remark (iii) of the supplied proof), smr_ci_coord_sum_smul_wedge (1b431e81) and smr_ci_norm_eq_sqrt_sum_coord_sq (a1716c42); all are accepted with passing isolated comparators. Mathlib's C_c-density file ContinuousMapDense.lean is outside the frozen closure, so the new child l1_density re-proves its p = 1 case; the accepted hdense of fiw_im_mass_formula (83e1f618) proves it verbatim. setLIntegral_iUnion_of_directed gives the exhaustion of Step 7 without measurability; GeometricCurrentOn.massOn_mono gives the mass comparison. MeasureTheory.AEStronglyMeasurable.inner is not in the closure (continuous_inner.comp_aestronglyMeasurable is). The three new names occur nowhere (DAG, project, SimonGMT, Mathlib, node files, git history). In the comparator scope all seven child types elaborate, and a scratch file with the reused accepted proofs, complete proofs of the three new children and the parent assembled from the children compiles sorry-free at default heartbeats with axioms propext, Classical.choice and Quot.sound only.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
