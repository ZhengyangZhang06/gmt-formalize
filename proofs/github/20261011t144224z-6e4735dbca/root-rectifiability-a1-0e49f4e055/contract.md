<!-- theorem-id: gmt-ch06/root.rectifiability-a1 -->

## Theorem `Submission.rectifiability_theorem`

For all P, m ∈ ℕ, every open U ⊆ ℝ^P and every T ∈ D_{m+1}(U) with M_W(T) + M_W(∂T) < ∞ for all W ⊂⊂ U: if some measure μ with IsMassMeasure T μ has upper density Θ*^{m+1}(μ, x) > 0 for μ-a.e. x, then T = τ(M, θ, ξ) is rectifiable (IsRectifiableCurrent T: M countably (m+1)-rectifiable and Hⁿ-measurable in U, θ > 0 locally integrable, ξ orienting the weighted approximate tangent spaces).

Node: `root.rectifiability-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1019, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1021, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1023, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1025, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1027, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1029, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1031, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1033, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1034, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1036, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1039, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1041

## Lean problem

Declaration: `Submission.rectifiability_theorem`

```lean
RectifiabilityTheorem
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

- Parent DAG node: `root`
- Child DAG node: `root.rectifiability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, 8.1 (Rectifiability Theorem) and its printed proof (pp. 173–175), displays (1)–(13), which use 3.3 and 3.6 of Ch. 1 (density comparison, upper density theorem), Remark 2.37(1),(2) (hence Lemma 2.36 and Remark 2.35 of Ch. 6), the Structure Theorem 3.6 of Ch. 3 (Besicovitch–Federer; Simon gives no proof and refers to [Fed69, 3.3.13] and [Ros84]; see also Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Thm. 18.1), Lemma 3.2 of Ch. 3, the Radon–Nikodym theorem 3.24 of Ch. 1, the Riesz representation 4.14 of Ch. 1 and the approximate tangent space theory of Ch. 3 §1. Book n = m + 1. The printed proof is copied below in numbered form, with the identification of the measure μ in the Lean hypothesis with μ_T and the verification of `IsRectifiableTriple` (weighted tangent spaces, Ch. 3, 1.7–1.9) filled in. Erratum/notation: Θⁿ in the printed hypothesis is the upper density Θ*ⁿ (as used in (1)–(3) and in the Lean statement); “Structure Theorem 3.8 of Ch. 3” in the preamble of §8 refers to the Rectifiability Theorem for sets, which Simon derives from the Structure Theorem 3.6 and Lemma 3.2 of Ch. 3, and the proof uses 3.6 and 3.2 directly; “1.15 of Ch. 1” (in 2.37) is the inner regularity of Radon measures. Correction of the previous draft: the frozen contract allows every ambient dimension P, including P < m+1 and P = m+1. Step 0 below proves the case P < m+1 directly (all (m+1)-forms on ℝ^P vanish, so T = 0 = τ(∅,1,0) with the empty rectifiable triple) before any dimension-dependent result is invoked, and justifies, for the top-dimensional case P = m+1, each geometric result cited in Steps 1–8 (or replaces it by an elementary argument); no dimension hypothesis is added.

Setting. U ⊆ ℝ^P open, T ∈ D_n(U) (n = m+1) with M_W(T) + M_W(∂T) < ∞ for all W ⊂⊂ U; μ is a measure with `IsMassMeasure T μ` (μ(ℝ^P∖U) = 0 and μ(W) = M_W(T) for every open W ⊂⊂ U) and Θ*ⁿ(μ,x) := `dimensionalUpperDensity μ n univ x` = limsup_{r↓0} μ(B̄_r(x))/(ω_n rⁿ) > 0 for μ-a.e. x. Hⁿ = μHE[n].

Preliminaries.
(P1) Representation (2.7) and identification of μ. By the vector Riesz theorem (Ch. 1, 4.14) applied to the ‖·‖-continuous extension of T to continuous compactly supported forms, T(ω) = ∫⟨ω,T⃗⟩dμ_T with μ_T a Radon measure on the locally compact space U (finite on compact subsets of U), extended by zero to ℝ^P (μ_T(ℝ^P∖U) = 0; μ_T need not be finite on compact subsets of ℝ^P meeting ∂U, and this is never used), |T⃗| = 1 μ_T-a.e. (|·| the Euclidean coefficient norm of n-vectors, w ↦ (Σ_β (w^β)²)^{1/2} with w^β = w(dx^β), dual to `covectorEuclideanNorm`), μ_T(W) = M_W(T) for open W ⊆ U (mollification shows that the suprema over continuous and over smooth forms agree). μ and μ_T agree on the π-system of open sets W ⊂⊂ U, which generates the Borel σ-algebra of U, and U is a countable union of such W with finite measure; hence μ⌞U = μ_T⌞U, and μ(ℝ^P∖U) = 0 = μ_T(ℝ^P∖U), so μ = μ_T. The same applies to ∂T: ∂T(ω) = ∫⟨ω,∂T⃗⟩dμ_{∂T}.
(P2) Remark 2.35, Lemma 2.36, Remark 2.37 (printed). (a) 2.35: a top-dimensional current Y ∈ D_n(V), V ⊆ ℝⁿ open, with M_W(Y), M_W(∂Y) < ∞ is Y(a dx) = ∫aθ dLⁿ with θ ∈ BV_loc(V). (b) 2.36: if E ⊆ U is closed and Lⁿ(p_α(E)) = 0 for every coordinate projection p_α : ℝ^P → ℝⁿ (α ∈ I(n,P)), then T⌞E = 0 whenever M_W(T), M_W(∂T) < ∞ for all W ⊂⊂ U. Printed proof: write ω = Σ_αω_αdx^α, so T(ω) = Σ_α(p_{α#}(T⌞ω_α))(dy) (1), where M(∂(T⌞ω_α)) ≤ M_W(∂T)|ω_α| + M_W(T)|dω_α| < ∞; by (a) p_{α#}(T⌞ω_α) = θ_α[[p_α(U)]] with θ_α ∈ BV, hence p_{α#}(T⌞ω_α)⌞p_α(E) = 0 and (2) M(p_{α#}(T⌞ω_α)) ≤ M_W(T⌞(ℝ^P∖E))|ω_α|; so (3) M_W(T) ≤ CM_W(T⌞(ℝ^P∖E)), i.e. (4) μ_T(W∩E) ≤ Cμ_T(W∖E); taking W_q ↓ K for compact K ⊆ E gives μ_T(K) = 0, and inner regularity gives μ_T(E) = 0. (c) 2.37(1): if C ⊆ U is Borel with Hⁿ(C) = 0 then μ_T(C) = 0 (closed subsets E of C have Lⁿ(p_α(E)) ≤ Hⁿ(E) = 0; inner regularity), i.e. μ_T ≪ Hⁿ. (d) 2.37(2): if Q is an orthogonal transformation of ℝ^P and E ⊆ U with Lⁿ(p_α(Q(E))) = 0 for all α, then μ_T(E) = 0 (apply (b) to Q_#T, whose mass measure is the image of μ_T; inner regularity reduces to closed E).
(P3) Ch. 1, 3.3 (density comparison; SimonGMT `simon_theorem_3_3`, stated there for Simon's Hausdorff outer measure, which is a fixed positive multiple of μH[n] as is μHE[n]; all uses below are qualitative — null sets and finiteness — or absorb the constant): for a Radon measure ν on U, A ⊆ U and t > 0, Hⁿ({x ∈ A : Θ*ⁿ(ν,x) > t}) ≤ t⁻¹ν(A) (outer measures). Simon's 3.3 is stated with the density relative to a set A₂ ⊇ A₁, Θ*ⁿ(ν,A₂,x); to obtain the displayed form for an arbitrary A, use outer regularity: for ε > 0 choose an open V with A ⊆ V ⊆ U and ν(V) ≤ ν(A) + ε, apply 3.3 with A₁ := {x ∈ A : Θ*ⁿ(ν,x) > t} and A₂ := V (for x ∈ V open, Θ*ⁿ(ν,V,x) = Θ*ⁿ(ν,x)), and let ε ↓ 0.

Proof.

0. (Dimension cases. The frozen contract allows every ambient dimension P; no dimension hypothesis is added.)
 (a) Case P < n (= m+1): T = 0 and the empty triple. Every n-covector on ℝ^P is 0: for v₁,…,v_n ∈ ℝ^P with n > P the family is linearly dependent, and an alternating multilinear map vanishes on linearly dependent families (Mathlib `AlternatingMap.map_linearDependent`; `Covector (Eucl P) n` consists of continuous alternating maps). Hence every test form ω ∈ Dⁿ(U) is the zero form, and T(ω) = T(0) = 0 by linearity. Take M := ∅, θ :≡ 1, ξ :≡ 0. Then `IsRectifiableTriple U n ∅ θ ξ` holds: ∅ ⊆ U; ∅ is measurable, in particular `NullMeasurableSet ∅ μHE[n]`; ∅ is countably n-rectifiable (`countablyRectifiable_of_measure_zero`, or M₀ := ∅ in Simon Ch. 3, 1.1); positivity of θ on M is vacuous; for every compact K ⊆ U, θ is integrable on ∅ ∩ K = ∅; and the measure Hⁿ⌞∅ is the zero measure, so ξ is a.e. strongly measurable for it and the orientation clause (an “∀ᵐ x ∂(Hⁿ⌞∅)” statement) holds trivially. Finally tauAction n ∅ θ ξ ω = ∫_∅ θ⟨ω,ξ⟩dHⁿ = 0 = T(ω) for every ω. So T = τ(∅,1,0) is rectifiable, i.e. `IsRectifiableCurrent T`; the hypotheses on T are not needed in this case. (Steps 1–8 below are not used for P < n; they involve n-planes in ℝ^P, which do not exist then.)
 (b) Case P = n (top dimension). Steps 1–8 below apply, with the following justifications of the cited geometric results in this case (Hⁿ = μHE[n] is Lebesgue measure Lⁿ on ℝⁿ):
  • (P2)(b),(c) [Lemma 2.36, Remark 2.37(1)]: for P = n the only multi-index is α = (1,…,n) and p_α = id, so the printed proof of 2.36 reduces to Remark 2.35 (P2)(a): T(a dx¹∧⋯∧dxⁿ) = ∫aθ_T dLⁿ with θ_T ∈ BV_loc(U), whence μ_T = |θ_T|Lⁿ⌞U; in particular μ_T(E) = 0 whenever Lⁿ(E) = 0, i.e. μ_T ≪ Hⁿ. (P2)(d) is not needed.
  • Step 3 [Structure Theorem, Lemma 3.2 of Ch. 3]: not needed. Every subset of ℝⁿ is countably n-rectifiable in the sense of Ch. 3, 1.1 (M ⊆ id(ℝⁿ), and the identity is Lipschitz), so the set M of Step 3 is countably n-rectifiable directly (and, consistently, a purely n-unrectifiable subset of ℝⁿ is Hⁿ-null, so (6) holds trivially).
  • Step 5 [Ch. 3, Theorem 1.9]: replaced by the Lebesgue differentiation theorem. Let θ̄ := θ1_M (θ from Step 4, extended by 0), which is in L¹_loc(U). For Lⁿ-a.e. x ∈ M, x is a Lebesgue point of θ̄ with θ̄(x) = θ(x) > 0. For such x, f ∈ C_c(ℝⁿ) with spt f ⊆ B_R(0) and λ < dist(x, ℝⁿ∖U)/R, we have η_{x,λ}(M) = {z : x+λz ∈ M}, so ∫_{η_{x,λ}M}f(z)θ(x+λz)dHⁿ(z) = ∫_{ℝⁿ}f(z)θ̄(x+λz)dz and |∫f(z)θ̄(x+λz)dz − θ(x)∫_{ℝⁿ}f| ≤ sup|f|·λ^{−n}∫_{B_{λR}(x)}|θ̄(y) − θ̄(x)|dy → 0. Hence `HasWeightedApproximateTangentSpaceAt n M θ x ℝⁿ` (finrank ℝⁿ = n), i.e. T_xM = ℝⁿ, for Hⁿ-a.e. x ∈ M. The rest of Step 5 (Lebesgue points of ξ, the blow-up formula (11)) is dimension-free.
  • Step 7 [orientation]: there is no index j ≥ n+1; instead use that Λ_n(ℝⁿ) is one-dimensional. Every n-covector on ℝⁿ equals α(e₁,…,e_n)·dx with dx := dx¹∧⋯∧dxⁿ (an alternating n-form on an n-dimensional space is a multiple of the determinant), so every n-vector w satisfies w(α) = α(e₁,…,e_n)w(dx), i.e. w = w(dx)·simpleNVector(e₁,…,e_n), and |w| = |w(dx)| in the Euclidean coefficient norm of (P1) (the only multi-index is (1,…,n)); the operator norm of `NVector` gives the same value, since ‖dx‖ = 1 by Hadamard's inequality. Since |ξ(x)| = 1, ξ(x) = ±simpleNVector(e₁,…,e_n), and (e₁,…,e_n) is an orthonormal basis of T_xM = ℝⁿ. (Step 6 is then not needed.)
  • Steps 1, 2, 4, 6, 8 and the preliminaries (P1), (P3) (Riesz representation, density comparison, Radon–Nikodym, Besicovitch differentiation) are valid in every dimension, in particular for P = n.
 (c) Case P > n. Then ℓ := P − n ≥ 1 and ℝ^P = ℝ^{n+ℓ} is the setting of Simon Ch. 3 (codimension ℓ ≥ 1), so the Structure Theorem 3.6 of Ch. 3, Lemma 3.2 and Theorem 1.9 apply verbatim, and Steps 1–8 are used as written.
 From now on assume P ≥ n.

1. (Printed (1)–(3).) By (P3), for every A ⊆ W, W ⊂⊂ U open, and t > 0: (1) Hⁿ{x ∈ A : Θ*ⁿ(μ_T,x) > t} ≤ t⁻¹μ_T(A) ≤ t⁻¹μ_T(W). Letting t → ∞ and exhausting U: (2) Hⁿ{x ∈ U : Θ*ⁿ(μ_T,x) = ∞} = 0. The same argument with ∂T: (3) Hⁿ{x ∈ U : Θ*ⁿ(μ_{∂T},x) = ∞} = 0.

2. (Printed (4)–(5).) The sets in (2), (3) are Borel (Θ*ⁿ of a Radon measure is Borel, Ch. 1, 3.2) and Hⁿ-null, so by (P2)(c): (4) μ_T{x ∈ U : Θ*ⁿ(μ_T,x) = ∞} = 0 and (5) μ_T{x ∈ U : Θ*ⁿ(μ_{∂T},x) = ∞} = 0.

3. (The carrier and its rectifiability — printed (6), (7).) [The structure-theorem argument of this step is for P > n; for P = n, M below is countably n-rectifiable trivially, Step 0(b).] Let M := {x ∈ U : Θ*ⁿ(μ_T,x) > 0} (Borel), M_j := {x ∈ M : Θ*ⁿ(μ_T,x) > 1/j}. By (1), Hⁿ(M_j ∩ W) ≤ jμ_T(W) < ∞ for W ⊂⊂ U, so M is a countable union of sets of finite Hⁿ-measure. Let P′ ⊆ M be purely n-unrectifiable (Ch. 3, 3.1) and Hⁿ-measurable; P′ is a countable union of sets of finite Hⁿ-measure because M is. By the Structure Theorem (Ch. 3, 3.6; Besicovitch–Federer), Hⁿ(p(P′)) = 0 for γ-almost every orthogonal projection p onto n-planes, γ the invariant measure on the Grassmannian. For each α ∈ I(n,P), the map Q ↦ Q⁻¹(span{e_i : i ∈ α}) carries Haar measure on O(P) to γ, and p_α∘Q is the projection onto Q⁻¹(span{e_i : i ∈ α}) followed by an isometry onto ℝⁿ; hence {Q : Hⁿ(p_α(Q(P′))) > 0} is Haar-null for each α, and so is the union over the finitely many α. Thus there is an orthogonal Q with Hⁿ(p_α(Q(P′))) = 0 for all α. Since Hⁿ⌞M is σ-finite, P′ = B ∪ N with B Borel and N contained in a Borel Hⁿ-null set; μ_T(N) = 0 by (P2)(c), and (P2)(d) applies to B (Lⁿ(p_α(Q(B))) ≤ Hⁿ(p_α(Q(P′))) = 0), so μ_T(P′) = 0, and since Θ*ⁿ(μ_T,·) > 1/j on P′ ∩ M_j, (P3) gives Hⁿ(P′ ∩ M_j) ≤ jμ_T(P′) = 0 for all j: (6) Hⁿ(P′) = 0 for every purely unrectifiable P′ ⊆ M. By Lemma 3.2 of Ch. 3 (SimonGMT `simon_lemma_3_2`: an Hⁿ-σ-finite set is the union of a countably n-rectifiable set and a purely n-unrectifiable set), M is countably n-rectifiable. By hypothesis and (P1), μ_T(U∖M) = μ(U∖M) = 0, so (7) μ_T = μ_T⌞M.

4. (Density — printed (8), (9).) By (P2)(c), μ_T ≪ Hⁿ⌞M, and Hⁿ⌞M is σ-finite (Step 3). By the Radon–Nikodym theorem for σ-finite measures (the abstract form recalled before Ch. 1, 3.24; Hⁿ⌞M need not be Radon), (8) μ_T = θHⁿ⌞M with θ ≥ 0 Hⁿ-measurable (choose a Borel version of the [0,∞]-valued density; it is finite Hⁿ⌞M-a.e. by local integrability, and we take θ := its real value, removing the null set where it is ∞ from M below together with {θ = 0}), locally Hⁿ-integrable on M (∫_{M∩K}θ dHⁿ = μ_T(K) < ∞ for compact K ⊆ U). Removing from M the Hⁿ-measurable set {θ = 0} ∩ M (which is μ_T-null) we may assume θ > 0 on M; M stays countably rectifiable and (7),(8) persist. By (P1), (9) T(ω) = ∫_M θ⟨ω,ξ⟩dHⁿ with ξ := T⃗ (μ_T-measurable, |ξ| = 1 Hⁿ-a.e. on M), i.e. T(ω) = `tauAction n M θ ξ ω` for all ω ∈ Dⁿ(U) (the integrand is integrable: |θ⟨ω,ξ⟩| ≤ θ‖ω‖1_{tsupport ω}).

5. (Weighted approximate tangent spaces — Ch. 3, 1.7–1.9 and printed (10)–(11); for P = n the use of Ch. 3, 1.9 is replaced by the Lebesgue-point argument of Step 0(b).) Since M is countably n-rectifiable and θ is positive and locally integrable on M, by Ch. 3, Theorem 1.9 (with Remark 1.8(1); applied to M ∩ B for balls B ⊂⊂ U, since θ is integrable only on compact subsets of U — tangent spaces at points of B do not change) the weighted approximate tangent space T_xM (`HasWeightedApproximateTangentSpaceAt n M θ x (T_xM)`) exists for Hⁿ-a.e. x ∈ M: for f ∈ C_c(ℝ^P), lim_{λ↓0}∫_{η_{x,λ}M}f(z)θ(x+λz)dHⁿ(z) = θ(x)∫_{T_xM}f dHⁿ. Moreover, by Lebesgue's differentiation theorem for the Radon measure μ_T = θHⁿ⌞M (Besicovitch differentiation, cf. Ch. 1 §3), for μ_T-a.e. (equivalently Hⁿ-a.e.) x ∈ M: μ_T(B_{λR}(x))⁻¹∫_{B_{λR}(x)}|ξ − ξ(x)|dμ_T → 0 for every R > 0; combined with Θ*ⁿ(μ_T,x) < ∞ (by (4)), i.e. μ_T(B_{λR}(x)) ≤ C_x(λR)ⁿ for small λ, this gives λ⁻ⁿ∫_{M∩B_{λR}(x)}θ|ξ − ξ(x)|dHⁿ → 0 for every R. (The printed argument (10)–(11) obtains the same via the decomposition M = ⋃M_j, M_j ⊆ N_j ∈ C¹, and Θⁿ(μ_T⌞((N_j∖M_j) ∪ ⋃_{k≠j}M_k), x) = 0 for Hⁿ-a.e. x ∈ M_j.) For such x and ω ∈ Dⁿ(ℝ^P), with η_{x,λ}(y) := (y − x)/λ and λ small enough that η_{x,λ}⁻¹(spt ω) ⊆ U: (η_{x,λ#}T)(ω) = ∫_Mθ(y)⟨ω((y−x)/λ), ξ(y)⟩λ⁻ⁿdHⁿ(y) = ∫_{η_{x,λ}M}θ(x+λz)⟨ω(z), ξ(x+λz)⟩dHⁿ(z), hence (11) lim_{λ↓0}η_{x,λ#}T(ω) = θ(x)∫_{T_xM}⟨ω(z), ξ(x)⟩dHⁿ(z) =: S_x(ω) (13), for all ω, at Hⁿ-a.e. x ∈ M (independent of ω).

6. (Boundary of the blow-up — printed (12).) For x ∈ M with Θ*ⁿ(μ_{∂T},x) < ∞ (μ_T-a.e., hence Hⁿ-a.e. on M by (5) and μ_T = θHⁿ⌞M with θ > 0), and spt ω ⊆ B_R(0): |∂η_{x,λ#}T(ω)| = |η_{x,λ#}∂T(ω)| ≤ ‖ω‖λ^{1−n}μ_{∂T}(B_{λR}(x)) ≤ ‖ω‖λRⁿω_n·sup_{r≤λR}μ_{∂T}(B_r(x))/(ω_nrⁿ) → 0 as λ ↓ 0. Hence S_x = lim η_{x,λ#}T has ∂S_x = 0.

7. (Orientation — printed after (13); this step is for P > n, the case P = n being Step 0(b).) Fix x as in Steps 5–6 with ξ(x) of unit length. Choose coordinates with L := T_xM = ℝⁿ×{0}. For j ≥ n+1, an (n−1)-tuple i₁ < ⋯ < i_{n−1} and ϕ ∈ C_c^∞(ℝ^P), let ω := y^jϕ dy^{i₁}∧⋯∧dy^{i_{n−1}}; then dω = ϕ dy^j∧dy^{i₁}∧⋯∧dy^{i_{n−1}} + y^j dϕ∧dy^{i₁}∧⋯, and y^j = 0 on L, so 0 = ∂S_x(ω) = S_x(dω) = θ(x)∫_Lϕ⟨dy^j∧dy^{i₁}∧⋯∧dy^{i_{n−1}}, ξ(x)⟩dHⁿ. Since ϕ is arbitrary and θ(x) > 0, ⟨e_j∧e_{i₁}∧⋯∧e_{i_{n−1}}, ξ(x)⟩ = 0, i.e. every coordinate ξ(x)^β with β ⊄ {1,…,n} vanishes. Hence ξ(x) = ±e₁∧⋯∧e_n (|ξ(x)| = 1) = ±`simpleNVector τ` for the orthonormal basis τ = (e₁,…,e_n) of T_xM.

8. (Conclusion: `IsRectifiableTriple U n M θ ξ`.) M ⊆ U; M is Hⁿ-measurable (the Borel set of Step 3 minus the set {θ = 0} for a Borel version of θ), hence `NullMeasurableSet` for Hⁿ; countably n-rectifiable (Step 3); θ > 0 on M; θ integrable on M ∩ K for compact K ⊆ U (Step 4); ξ is Hⁿ⌞M-a.e. strongly measurable (it is μ_T-measurable and μ_T = θHⁿ⌞M with θ > 0); and for Hⁿ-a.e. x ∈ M there is an orthonormal τ spanning the weighted approximate tangent space with ξ(x) = ±simpleNVector τ (Steps 5–7; for P = n, Step 0(b)). Together with T = τ(M,θ,ξ) (Step 4) this shows `IsRectifiableCurrent T`, proving `RectifiabilityTheorem`.

## Key steps

1. Dimension cases: for P < m+1 all (m+1)-covectors vanish, so T = 0 = τ(∅,1,0) with the empty rectifiable triple; for P = m+1 the structure theorem is unnecessary (every subset of ℝⁿ is rectifiable), 2.36 reduces to 2.35, tangent spaces come from Lebesgue points and Λ_n(ℝⁿ) is one-dimensional; for P > m+1 the Ch. 3 results apply with codimension ℓ = P − m − 1 ≥ 1.
2. Identify μ with the Riesz mass measure μ_T (agreement on open W ⊂⊂ U).
3. Density comparison (Ch. 1, 3.3): Hⁿ-null sets where Θ*ⁿ(μ_T) or Θ*ⁿ(μ_∂T) is infinite; μ_T ≪ Hⁿ by 2.36–2.37.
4. M := {Θ*ⁿ(μ_T) > 0} is Hⁿ-σ-finite; purely unrectifiable subsets are null by the Besicovitch–Federer structure theorem and 2.37(2); Lemma 3.2 of Ch. 3 gives M countably rectifiable.
5. Radon–Nikodym: μ_T = θHⁿ⌞M with θ > 0 locally integrable; T = τ(M,θ,ξ) with ξ = T⃗.
6. Weighted tangent spaces exist a.e. (Ch. 3, 1.9); blow-ups η_{x,λ#}T converge to θ(x)[[T_xM]] oriented by ξ(x).
7. ∂ of the blow-up vanishes because Θ*ⁿ(μ_∂T, x) < ∞; testing with y^jϕdy^I shows ξ(x) = ±e(T_xM).
8. Verify all fields of IsRectifiableTriple.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^theorem main_theorem' project/GMT/Ch06/Contract.lean`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all byte-identical)`
- `python3 listing of dag.json nodes (only 'root'; no reserved child lean_name)`
- `python3 audit of nodes/root/decomposition-audit-v2.json and decomposition-v2.json (only deformation A3 rejected; search of all 12 proofs for 'θ′ ≥ 1', 'σ-finite', 'Radon–Nikodym', 'IsLipschitzPushforward', 'LipschitzPushforwardIntegerMultiplicity', 'as in the conventions')`
- `rg -n 'theorem sigmaFinite_of_countable' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `rg -n 'theorem mul_meas_ge_le_lintegral₀' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/`
- `rg -n 'theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite|theorem Integrable.ae_eq_of_forall_setIntegral_eq' mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `rg -n 'theorem hausdorffMeasure_image_le (h : LipschitzWith' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'theorem restrict_congr_set|theorem restrict_restrict [(]|theorem ae_restrict_iff.₀|theorem ae_restrict_mem₀' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -il 'coarea|co-area' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -il 'Besicovitch.Federer|purely unrectifiable' mathlib/Mathlib/MeasureTheory (no match)`
- `rg -n 'def HasWeightedApproximateTangentSpaceAt|def blowUpMap|theorem HasWeightedApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `rg -n 'abbrev NVector|def simpleNVector|def nVectorPushforward|theorem nVectorPushforward_simple|def covectorEuclideanNorm' simongmt/Poincare/SimonGMT/Chapter06/`
- `#print MeasureTheory.Measure.euclideanHausdorffMeasure (μHE[d] = volume.addHaarScalarFactor μH[d] • μH[d])`
- `grep -n '1.12|1.15|Borel-regular|3.19|3.24' book/chapter-01.txt`
- `lake build GMT.Ch06.Submission (scratch /tmp/gmt_ch06_v3_check, frozen commit d8d46c9, pinned packages)`
- `lake env lean Scratch/V3_Stmts.lean (12 child statements in gmt-compare.py contract_scope; 0 errors)`
- `lake env lean Scratch/V3_Assembly.lean (exact Submission.<name>; 12-way assembly vs type_of% GMT.Ch06.main_theorem; ff_from_siblings; parent_from_children; #print axioms)`
- `lake env lean Scratch/V3_SigmaFinite.lean (v3_sigmaFinite_restrict; #print axioms)`
- `lake env lean Scratch/V3_Tangent.lean (v3_weightedTangent_congr; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Stmts.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Assembly.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_SigmaFinite.lean`
- `/tmp/gmt_ch06_v3_check/Scratch/V3_Tangent.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract, a byte-identical Submission with no Submission.* declarations, and the README. The DAG contains only root, so the 12 bare child names are unreserved. All 12 conjuncts are `def … : Prop` in namespace GMT.Ch06. In a scratch build of the frozen project, every child statement elaborates in the comparator's child scope, `exact Submission.<name>` resolves for all 12 children, and the 12-way assembly typechecks against `type_of% GMT.Ch06.main_theorem`. FedererFlemingCompactness follows from its three declared siblings and the parent from the other 11 children, with axioms [propext, Classical.choice, Quot.sound]. The contract's `IsLipschitzPushforward` supplies only an `IsRectifiableTriple` representation (θ′ > 0 real, integrable on compacts), confirming the v2 defect. The repaired deformation A3 uses only that. Its σ-finiteness step is kernel-checked as `v3_sigmaFinite_restrict` (via Mathlib `Measure.sigmaFinite_of_countable`, `mul_meas_ge_le_lintegral₀`, `Measure.restrict_restrict`, `ae_restrict_mem₀`), and its tangent-space step as `v3_weightedTangent_congr`, against the actual SimonGMT `HasWeightedApproximateTangentSpaceAt`/`blowUpMap` definitions (via `LipschitzWith.hausdorffMeasure_image_le`, `Measure.restrict_congr_set`, `ae_restrict_iff'₀`; μHE[d] is a scalar multiple of μH[d]), both with standard axioms only. Mathlib provides Radon–Nikodym-type uniqueness (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`, `Integrable.ae_eq_of_forall_setIntegral_eq`). SimonGMT provides `nVectorPushforward_simple`, `covectorEuclideanNorm` and `HasWeightedApproximateTangentSpaceAt.unique`. Simon Ch. 1 gives 1.12 (μ⌞Y is Borel regular for measurable Y of finite measure), 1.15(2) (inner regularity) and 2.6 (H^m is Borel regular), as cited. There is no Mathlib match for co-area or for Besicovitch–Federer/purely unrectifiable; these are cited from Simon Ch. 3, as SimonGMT omits them. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
