<!-- theorem-id: gmt-ch06/root.compactness_mass_bounds-a1 -->

## Theorem `Submission.compactness_under_mass_bounds`

For all P, n ∈ ℕ, every open U ⊆ ℝ^P and every sequence T_q ∈ D_n(U) (GeometricCurrentOn U n) with sup_q M_W(T_q) < ∞ for every open W ⊂⊂ U (CompactlyContainedOpen W U), there are a strictly increasing φ : ℕ → ℕ and T₀ ∈ D_n(U) such that T_{φ(q)} ⇀ T₀ weakly in U and, for every continuous compactly supported n-form ω with tsupport ω ⊆ U and all measure representations (μ_q, v_q) of T_{φ(q)} and (μ₀, v₀) of T₀ (IsMeasureRepresentation), ∫ v_q(x)(ω(x)) dμ_q → ∫ v₀(x)(ω(x)) dμ₀.

Node: `root.compactness_mass_bounds-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/687, https://github.com/ZhengyangZhang06/gmt-formalize/issues/689, https://github.com/ZhengyangZhang06/gmt-formalize/issues/691, https://github.com/ZhengyangZhang06/gmt-formalize/issues/693, https://github.com/ZhengyangZhang06/gmt-formalize/issues/695, https://github.com/ZhengyangZhang06/gmt-formalize/issues/697, https://github.com/ZhengyangZhang06/gmt-formalize/issues/699, https://github.com/ZhengyangZhang06/gmt-formalize/issues/701

## Lean problem

Declaration: `Submission.compactness_under_mass_bounds`

```lean
CompactnessUnderMassBounds
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
- Child DAG node: `root.compactness_mass_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Lemma 2.15 (p. 137) together with the paragraph printed immediately before it (“We also observe that if sup_q M_W(T_q) < ∞ for each open W ⊂⊂ U then by 2.7 the distribution convergence 2.13 is equivalent to weak convergence with respect to continuous forms with compact support ..., and hence by applying the standard Banach–Alaoglu theorem (in the Banach spaces M_n(W) = {T ∈ D_n(W) : M_W(T) < ∞}, W ⊂⊂ U) we deduce 2.15”). The printed argument is: uniform local mass bounds + separability give a weakly convergent subsequence (Banach–Alaoglu / diagonal argument), and the integral representation (2.7) turns convergence on smooth forms into convergence on continuous compactly supported forms. Below the printed argument is written out in numbered steps for the exact Lean statement (in which the conclusion about continuous forms is required for every measure representation in the sense of `IsMeasureRepresentation`). No erratum applies.

Conventions. ℝ^P = `Eucl P`, e_1,…,e_P the standard basis. D^n(U) = `TestFormOn U n` (smooth n-forms on ℝ^P with compact tsupport ⊆ U), D_n(U) = `GeometricCurrentOn U n`. For an n-covector α let |α| := `covectorEuclideanNorm α` = (Σ_{β∈I(n,P)} α(e_β)²)^{1/2} (I(n,P) = strictly increasing multi-indices, e_β = (e_{β_1},…,e_{β_n})), and for a form ω let ‖ω‖ := sup_x |ω(x)|. For an n-vector w ∈ `NVector (Eucl P) n` (a continuous linear functional on n-covectors) put w^β := w(dx^β), where dx^β = dx^{β_1}∧⋯∧dx^{β_n}, and |w| := (Σ_β (w^β)²)^{1/2}.
Fact A (coordinates). Every n-covector satisfies α = Σ_β α(e_β) dx^β (an alternating n-linear map is determined by its values on increasing tuples of basis vectors, and dx^β(e_γ) = δ_{βγ}). Hence w(α) = Σ_β α(e_β) w^β and, by Cauchy–Schwarz, |w(α)| ≤ |α|·|w|.

Proof.

1. (Exhaustion.) For i ≥ 1 let W_i := {x ∈ U : |x| < i and B̄_{1/i}(x) ⊆ U} (this avoids any convention for dist(x, ∅); if U = ℝ^P it is just the open ball of radius i). Each W_i is open; if x ∈ closure(W_i) then |x| ≤ i and B_{1/i}(x) ⊆ U (every y with |y−x| < 1/i satisfies |y − x_k| < 1/i for points x_k ∈ W_i close to x), so closure(W_i) is closed and bounded, hence compact, and closure(W_i) ⊆ W_{i+1} ⊆ U (B̄_{1/(i+1)}(x) ⊆ B_{1/i}(x)). Thus `CompactlyContainedOpen W_i U`; the W_i increase and ⋃_i W_i = U (U is open). Every compact K ⊆ U is contained in some W_i (open cover of K by an increasing sequence). Put C_i := sup_q M_{W_i}(T_q) < ∞ (hypothesis).

2. (Basic mass estimate.) If T ∈ D_n(U), W is any set and ω ∈ D^n(U) with tsupport ω ⊆ W, then |T(ω)| ≤ M_W(T)·‖ω‖. Indeed ‖ω‖ < ∞ (ω continuous with compact support). If ‖ω‖ = 0 then ω = 0 and T(ω) = 0. Otherwise ±ω/‖ω‖ lies in `massAdmissibleOn U n W`, so ENNReal.ofReal(±T(ω)/‖ω‖) ≤ M_W(T) by `GeometricCurrentOn.le_massOn`, which gives the claim (trivial if M_W(T) = ∞).

3. (Countable dense families.) Fix i. The set D_i := {ω ∈ D^n(U) : tsupport ω ⊆ W_i} is a subset of the separable metric space C(closure W_i ; Λ^n(ℝ^P)) with the sup norm built from |·| (continuous functions on a compact metric space with values in a finite-dimensional space form a separable Banach space), hence D_i is separable for ‖·‖. Choose a countable E_i ⊆ D_i which is ‖·‖-dense in D_i and put E := ⋃_i E_i, enumerated as η_1, η_2, … .

4. (Diagonal subsequence; Banach–Alaoglu step.) For η ∈ E_i, Step 2 gives |T_q(η)| ≤ C_i‖η‖ for all q, so (T_q(η_k))_q is a bounded real sequence for every k. By Bolzano–Weierstrass and Cantor's diagonal procedure there is a strictly increasing φ : ℕ → ℕ such that lim_q T_{φ(q)}(η_k) exists for every k.

5. (Convergence on every test form.) Let ω ∈ D^n(U). tsupport ω is compact and ⊆ U, so ω ∈ D_i for some i. Given ε > 0 pick η ∈ E_i with ‖ω − η‖ < ε; ω − η ∈ D_i. For all q, q′, by Step 2,
|T_{φ(q)}(ω) − T_{φ(q′)}(ω)| ≤ |T_{φ(q)}(ω−η)| + |T_{φ(q)}(η) − T_{φ(q′)}(η)| + |T_{φ(q′)}(η−ω)| ≤ 2C_iε + |T_{φ(q)}(η) − T_{φ(q′)}(η)|.
Hence (T_{φ(q)}(ω))_q is Cauchy; define T₀(ω) := lim_q T_{φ(q)}(ω).

6. (T₀ ∈ D_n(U) and T_{φ(q)} ⇀ T₀.) T₀ is linear as a pointwise limit of linear maps. Continuity: let ω_j → 0 in the sense of `TestFormOnConverges` (tsupports in one compact K ⊆ U, every iterated derivative → 0 uniformly on K). Choose i with K ⊆ W_i. By Step 2, |T_{φ(q)}(ω_j)| ≤ C_i‖ω_j‖ for all q, hence |T₀(ω_j)| ≤ C_i‖ω_j‖. Since ω_j → 0 uniformly on K and vanishes off K, and |α| ≤ (#I(n,P))^{1/2}·max_β|α(e_β)| ≤ (#I(n,P))^{1/2}·‖α‖_op, we get ‖ω_j‖ → 0, so T₀(ω_j) → 0. Thus T₀ is a `GeometricCurrentOn U n`, and `WeaklyConvergesOn (fun q => T (φ q)) T₀` holds by construction. By lower semicontinuity of mass (Simon 2.14; `WeaklyConvergesOn.massOn_le_liminf`), for every W ⊂⊂ U: M_W(T₀) ≤ liminf_q M_W(T_{φ(q)}) ≤ sup_q M_W(T_q) < ∞; in particular M_{W_i}(T₀) ≤ C_i.

7. (Representation lemma; this is the content of “by 2.7” in the printed text.) Let T ∈ D_n(U) with M_W(T) < ∞ for every W ⊂⊂ U and let (μ, v) satisfy `IsMeasureRepresentation T μ v`, i.e. for every ω ∈ D^n(U) the function x ↦ v(x)(ω(x)) is μ-integrable and T(ω) = ∫ v(x)(ω(x)) dμ(x).
 (a) For every compact K ⊆ U, x ↦ |v(x)| is μ-integrable on K and each v^β is a.e.-strongly measurable on K. Proof: take χ ∈ C_c^∞(ℝ^P) with 0 ≤ χ ≤ 1, χ = 1 on K, tsupport χ ⊆ U. For each β the form ω_β := χ·dx^β (constant covector times χ) lies in D^n(U) and v(x)(ω_β(x)) = χ(x)v^β(x) (Fact A). By hypothesis χv^β is μ-integrable, hence v^β is μ-integrable on K, and |v| ≤ Σ_β|v^β| is μ-integrable on K.
 (b) Let ω be a continuous n-form with compact support, tsupport ω ⊆ W where W is open with closure(W) compact ⊆ U. Then x ↦ v(x)(ω(x)) is μ-integrable and |∫ v(ω) dμ| ≤ M_W(T)‖ω‖. Proof: measurability and integrability follow from v(x)(ω(x)) = Σ_β ω(x)(e_β)v^β(x) and |v(ω)| ≤ ‖ω‖|v|1_{tsupport ω} with (a). Choose δ > 0 such that the closed δ-neighbourhood K′ of tsupport ω lies in W. Let ϕ be a smooth mollifier (ϕ ≥ 0, ∫ϕ = 1, spt ϕ ⊆ B_1(0)), ϕ_ε(x) = ε^{−P}ϕ(x/ε), and for 0 < ε < δ let ω_ε := ϕ_ε * ω (convolution of each coefficient function x ↦ ω(x)(e_β), equivalently of the covector-valued function). Then ω_ε is smooth, tsupport ω_ε ⊆ K′ ⊆ W (so ω_ε ∈ D^n(U)), |ω_ε(x)| ≤ ∫|ω(x−y)|ϕ_ε(y)dy ≤ ‖ω‖ (convexity of the Euclidean norm on coefficient vectors), and ω_ε → ω uniformly as ε ↓ 0 (uniform continuity of ω). By Step 2, |∫ v(ω_ε)dμ| = |T(ω_ε)| ≤ M_W(T)‖ω‖. By dominated convergence (dominating function ‖ω‖·|v|·1_{K′}, integrable by (a)), ∫v(ω_ε)dμ → ∫v(ω)dμ. Hence |∫ v(ω)dμ| ≤ M_W(T)‖ω‖.
 The same mollification shows: every such ω is a uniform limit of test forms ω_ε ∈ D^n(U) with tsupport ω_ε ⊆ W.

8. (Convergence on continuous compactly supported forms.) Let ω : ℝ^P → Λ^n(ℝ^P) be continuous with compact support and tsupport ω ⊆ U, and let (μ_q, v_q), (μ₀, v₀) be representations of T_{φ(q)} and T₀. Choose i with tsupport ω ⊆ W_i and put W := W_{i+1} (so closure(W_i) ⊆ W ⊂⊂ U). Let ε > 0. By Step 7 there is a test form η ∈ D^n(U) with tsupport η ⊆ W and ‖ω − η‖ ≤ ε; ω − η is continuous with compact tsupport ⊆ W. Since all integrands are integrable (Step 7(b)) the integrals are linear, and by Step 7(b) together with T_{φ(q)}(η) = ∫v_q(η)dμ_q and T₀(η) = ∫v₀(η)dμ₀:
|∫v_q(ω)dμ_q − ∫v₀(ω)dμ₀| ≤ |∫v_q(ω−η)dμ_q| + |T_{φ(q)}(η) − T₀(η)| + |∫v₀(η−ω)dμ₀| ≤ C_{i+1}ε + |T_{φ(q)}(η) − T₀(η)| + M_W(T₀)ε.
Here M_W(T_{φ(q)}) ≤ C_{i+1} and M_W(T₀) ≤ C_{i+1} (Step 6). Since T_{φ(q)}(η) → T₀(η), limsup_q |∫v_q(ω)dμ_q − ∫v₀(ω)dμ₀| ≤ 2C_{i+1}ε; ε being arbitrary, ∫ v_q(ω) dμ_q → ∫ v₀(ω) dμ₀.

9. (Degenerate cases.) If U = ∅ every test form and every ω with tsupport ω ⊆ ∅ is 0; then any strictly increasing φ and T₀ := 0 satisfy all conclusions (all integrals vanish). Steps 1–8 also cover this case formally. This proves `CompactnessUnderMassBounds`.

## Key steps

1. Exhaust U by open W_i ⊂⊂ U with closure W_i ⊆ W_{i+1}; C_i := sup_q M_{W_i}(T_q) < ∞.
2. Mass estimate |T(ω)| ≤ M_W(T)‖ω‖ for tsupport ω ⊆ W (±ω/‖ω‖ is mass-admissible).
3. Choose countable sup-norm-dense families E_i of test forms supported in W_i (separability).
4. Diagonal (Bolzano–Weierstrass / Banach–Alaoglu) subsequence converging on all of E = ⋃E_i.
5. Cauchy argument extends convergence to every test form; define T₀ as the limit.
6. T₀ is linear and sequentially continuous (|T₀(ω)| ≤ C_i‖ω‖), and M_W(T₀) ≤ sup_q M_W(T_q) by 2.14.
7. Any IsMeasureRepresentation (μ,v) has |v| locally μ-integrable and |∫v(ω)dμ| ≤ M_W(T)‖ω‖ for continuous ω (mollification + dominated convergence).
8. Approximate continuous ω uniformly by test forms supported in W_{i+1} to get convergence of ∫v_q(ω)dμ_q to ∫v₀(ω)dμ₀.

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
