<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1 -->

## Theorem `Submission.slicing_integer_multiplicity_ae`

For all P, m, every open U ⊆ ℝ^P, every T ∈ D_{m+1}(U) with M_W(T) < ∞ and M_W(∂T) < ∞ for all open W ⊂⊂ U and every f : ℝ^P → ℝ which is L-Lipschitz on U: if T is integer multiplicity, then for L¹-almost every t ∈ ℝ every S ∈ D_m(U) with IsSlice T f t S is integer multiplicity.

Node: `root.slicing-a1.slice_integer_multiplicity-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/322

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2474, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2483, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2492, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2506, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2519, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2532, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2543

## Lean problem

Declaration: `Submission.slicing_integer_multiplicity_ae`

```lean
∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) → ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U → IsIntegerMultiplicity T → ∀ᵐ t ∂(volume : Measure ℝ), ∀ S : GeometricCurrentOn U m, IsSlice T f t S → IsIntegerMultiplicity S
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

- Parent DAG node: `root.slicing-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions (as in the parent proof). D^k(U) is the space of test k-forms on U (smooth, compact support, tsupport ⊆ U; `TestFormOn U k`), D_k(U) the currents (`GeometricCurrentOn U k`: linear, and X(ω_j) → 0 whenever ω_j → 0 in D^k(U), i.e. all tsupports lie in one compact K ⊆ U and every iterated derivative of ω_j tends to 0 uniformly on K). I(k,P) is the set of strictly increasing β : {1,…,k} → {1,…,P}; e_β := (e_{β_1},…,e_{β_k}); dx^β is the coordinate k-covector, dx^β(e_γ) = δ_{βγ} for β, γ ∈ I(k,P). Fact A: every k-covector α equals Σ_β α(e_β) dx^β, and |α|² = Σ_β α(e_β)², where |α| := covectorEuclideanNorm α. A k-vector is a continuous linear functional w on k-covectors (`NVector`); put w^β := w(dx^β), so w(α) = Σ_β α(e_β) w^β and |w(α)| ≤ |α|·|w| with |w| := (Σ_β (w^β)²)^{1/2} (Cauchy–Schwarz). For a form ω, ‖ω‖ := sup_x |ω(x)|. M_W(X) = X.massOn W is the supremum of X(ω) over ω ∈ D^k(U) with tsupport ω ⊆ W and |ω(x)| ≤ 1 for all x. ρ_ε is a standard mollifier (smooth, ≥ 0, supported in the closed ε-ball, ∫ρ_ε = 1); for a continuous compactly supported form φ, ρ_ε*φ (componentwise convolution) is smooth, supported in the closed ε-neighbourhood of tsupport φ, satisfies |ρ_ε*φ(x)| ≤ ‖φ‖ (|·| is a norm, hence convex) and ρ_ε*φ → φ uniformly as ε ↓ 0. All measures are Borel measures on ℝ^P = Eucl P.

Source: Simon Ch. 6, Lemma 4.1, Remark 4.2, 4.3, Definition 4.4 and Lemma 4.5(2) with its printed proof (pp. 154–157), i.e. the parent proof's Steps 5–7, adapted so that the conclusion holds for every S with IsSlice T f t S: the restriction terms are evaluated in the representations supplied by IsSlice, and the exceptional null set depends only on (M, θ, ξ), f and a fixed countable family of forms. Book n = m+1. The Ch. 3 results used (1.6, 1.8, 1.9, 2.10 and the co-area formula of §2) are applied on M ∩ U_i for open U_i ⊂⊂ U exhausting U, since θ is integrable only on compact subsets of U; weighted tangent spaces are local. Hⁿ = μHE[n].

Setting. P, m, U open, n := m+1, T ∈ D_n(U) with M_W(T), M_W(∂T) < ∞ for W ⊂⊂ U, f : ℝ^P → ℝ L-Lipschitz on U, and T integer multiplicity: there are M, θ, ξ with IsRectifiableTriple U n M θ ξ (M ⊆ U Hⁿ-measurable and countably n-rectifiable; θ > 0 on M and integrable on M ∩ K for compact K ⊆ U; ξ Hⁿ-measurable on M and, for Hⁿ-a.e. x ∈ M, ξ(x) = ±τ₁∧⋯∧τ_n for an orthonormal basis τ of the weighted approximate tangent space T_xM of (M, θ)), θ(x) ∈ {1,2,…} for x ∈ M, and T(η) = ∫_M θ⟨η, ξ⟩ dHⁿ for η ∈ D^n(U), where ⟨η, ξ⟩(x) := ξ(x)(η(x)).

1. (Lipschitz extension.) By McShane (`LipschitzOnWith.extend_real`) there is an L-Lipschitz f̃ : ℝ^P → ℝ with f̃ = f on U. Since A_t := {x | x ∈ U ∧ f x < t} = {x | x ∈ U ∧ f̃ x < t}, IsSlice T f t S ⟺ IsSlice T f̃ t S for all t and S, and M ⊆ U; so it suffices to prove the claim for f̃, and we write f for f̃ (Lipschitz on all of ℝ^P).

2. (Slicing of M, Lemma 4.1 and Remark 4.2.) Let ∇^Mf be the tangential gradient (Simon Ch. 3, 2.1; defined Hⁿ-a.e. on M via the C¹ decomposition M = M₀ ∪ ⋃_{j≥1} M_j, pairwise disjoint, Hⁿ(M₀) = 0, M_j ⊆ N_j embedded C¹ n-submanifolds; |∇^Mf| ≤ L), M₊ := {x ∈ M : ∇^Mf(x) ≠ 0} and M_t := f⁻¹(t) ∩ M₊. Lemma 4.1 (printed proof: (1) is Ch. 3, 2.10(2); (2) follows from Ch. 3, 1.6 together with ∇^Mf(x) ∈ T_xM and ⟨∇^Mf(x), τ⟩ = 0 for τ ∈ T_xM_t; the last part is the co-area formula of Ch. 3, §2): for L¹-a.e. t, M_t is countably (n−1)-rectifiable and Hⁿ⁻¹-measurable, and for Hⁿ⁻¹-a.e. x ∈ M_t both T_xM_t and T_xM exist, T_xM_t ⊆ T_xM is (n−1)-dimensional and T_xM = T_xM_t ⊕ ℝ∇^Mf(x); and for every nonnegative Hⁿ-measurable g on M, ∫_{−∞}^{∞}∫_{M_t} g dHⁿ⁻¹ dt = ∫_M |∇^Mf| g dHⁿ. Remark 4.2: applying this to g·1_{f<s} shows that s ↦ ∫_{M∩{f<s}} |∇^Mf| g dHⁿ = ∫_{−∞}^{s} (∫_{M_r} g dHⁿ⁻¹) dr is absolutely continuous with derivative ∫_{M_s} g dHⁿ⁻¹ for L¹-a.e. s; for Hⁿ-integrable signed g on M split g = g⁺ − g⁻. Also ∫_{M∩{f=c}} |∇^Mf| dHⁿ = ∫ Hⁿ⁻¹(M_r ∩ {f = c}) dr = 0, so ∇^Mf = 0 Hⁿ-a.e. on each level set M ∩ {f = c}.

3. (The integer multiplicity slice, 4.3–4.4.) For the L¹-a.e. t of step 2 define, for x ∈ M_t, ξ_t(x) := ξ(x)⌞(∇^Mf(x)/|∇^Mf(x)|) (interior product: ⟨ξ⌞w, α⟩ := ⟨ξ, w*∧α⟩ for (n−1)-covectors α, w* the 1-covector dual to w), ξ_t := 0 off M_t, and θ_t := θ. By 4.3, ξ_t(x) is a unit simple (n−1)-vector orienting T_xM_t for Hⁿ⁻¹-a.e. x ∈ M_t: if ξ(x) = ±τ₁∧⋯∧τ_n with τ_n = ∇^Mf/|∇^Mf| and τ₁,…,τ_{n−1} an orthonormal basis of T_xM_t, then ξ_t(x) = ±(−1)^{n−1}τ₁∧⋯∧τ_{n−1}. Define ⟨T,f,t⟩(ω) := ∫_{M_t} θ_t⟨ω, ξ_t⟩ dHⁿ⁻¹ = tauAction m M_t θ_t ξ_t ω (Definition 4.4). There is an L¹-null set F₀ such that for t ∉ F₀ the triple satisfies IsRectifiableTriple U m M_t θ_t ξ_t and θ_t ∈ {1,2,…} on M_t:
 (i) M_t ⊆ M ⊆ U is Hⁿ⁻¹-measurable and countably (n−1)-rectifiable (step 2); moreover, since θ ≥ 1 on M_t and, by (iii) below, Hⁿ⁻¹(M_t ∩ K_i) ≤ ∫_{M_t∩K_i} θ dHⁿ⁻¹ < ∞ for every i, M_t is σ-finite for Hⁿ⁻¹, and an Hⁿ⁻¹-measurable σ-finite set differs from a Borel set by an Hⁿ⁻¹-null set (Borel regularity of Hausdorff measure), i.e. NullMeasurableSet M_t μHE[m];
 (ii) θ_t = θ ∈ {1,2,…} on M_t, in particular > 0;
 (iii) local integrability: choose compacts K_i ⊆ U with K_i ⊆ int K_{i+1}, ⋃K_i = U; by the co-area formula ∫∫_{M_t∩K_i} θ dHⁿ⁻¹ dt = ∫_{M∩K_i} |∇^Mf| θ dHⁿ ≤ L∫_{M∩K_i} θ dHⁿ < ∞, so for a.e. t every ∫_{M_t∩K_i} θ dHⁿ⁻¹ is finite, hence θ_t is integrable on M_t ∩ K for every compact K ⊆ U;
 (iv) measurability of ξ_t and of θ_t on M_t for a.e. t (needed for `aestronglyMeasurable` and `integrableOn`): ∇^Mf, ξ and θ are Hⁿ-measurable on M; restrictions of Hⁿ-measurable functions on M to the slices M_t are Hⁿ⁻¹-measurable for a.e. t, by the co-area formula applied to the indicator functions of the Hⁿ-null sets where measurable modifications differ;
 (v) orientation: the properties “T_xM exists and ξ(x) = ±(orthonormal frame of T_xM)” hold outside an Hⁿ-null set Z ⊆ M; by the co-area formula ∫ Hⁿ⁻¹(Z ∩ M_t) dt = ∫_Z |∇^Mf| dHⁿ = 0, so for a.e. t they hold Hⁿ⁻¹-a.e. on M_t, and then 4.3 applies Hⁿ⁻¹-a.e. on M_t. Since θ_t is a positive integer-valued locally integrable function on the countably (n−1)-rectifiable M_t, by Ch. 3, Theorem 1.9 and Remark 1.8(1) the weighted approximate tangent space of (M_t, θ_t) exists Hⁿ⁻¹-a.e. on M_t and equals T_xM_t, which ξ_t orients (ξ_t(x) = ±simpleNVector of an orthonormal basis of it). (For n = 1, M_t is countable and locally finite, the weighted tangent space at each of its points is {0}, and ξ_t = ±1.)
 Moreover, for t ∉ F₀ and every compact K ⊆ U, |⟨T,f,t⟩(ω)| ≤ ‖ω‖·∫_{M_t∩K} θ dHⁿ⁻¹ whenever tsupport ω ⊆ K (|⟨ω, ξ_t⟩| ≤ |ω| since ξ_t(x) is a unit simple vector).

4. (Lemma 4.5(2) for an arbitrary S.) First the printed (1): for Lipschitz h on ℝ^P with mollifications h^{(σ)} := ρ_σ*h and any bounded Hⁿ-measurable vector field Y on M vanishing outside a compact subset of U,
 (1) ∫_M θ Y·∇^M h^{(σ)} dHⁿ → ∫_M θ Y·∇^M h dHⁿ as σ ↓ 0
(the printed “weak convergence in L²(μ_T)”, localized because θ is only locally integrable). Proof: |∇^M h^{(σ)}| ≤ Lip(h) and θ is integrable on the compact set outside which Y vanishes, so by dominated convergence over j it suffices to treat Y vanishing off M_j ⊆ N_j, where ∇^M = ∇^{N_j} Hⁿ-a.e. Cover N_j by countably many C¹ charts φ : Ω → N_j and split M_j accordingly. In a chart, h^{(σ)}∘φ → h∘φ uniformly with Lipschitz constants bounded on compact subsets of Ω, hence D(h^{(σ)}∘φ) → D(h∘φ) weakly-* in L^∞ (test against C_c^∞(Ω) functions and integrate by parts, then use density in L¹ and the uniform L^∞ bound); ∇^{N_j}(·)∘φ is a linear expression in D(·∘φ) with continuous coefficients, and by the area formula the integral in (1) becomes ∫_Ω ⟨c_Y, D(h^{(σ)}∘φ)⟩ dy with c_Y ∈ L¹ (θ integrable, Y bounded, Jacobian continuous), which converges.
 Now fix t ∈ ℝ, ε > 0, let ψ(s) := 1 for s < t−ε, ψ linear on [t−ε, t], ψ(s) := 0 for s > t, and h := ψ∘f (Lipschitz on ℝ^P, 0 ≤ h ≤ 1). Let S ∈ D_m(U) satisfy IsSlice T f t S: there are currents A, B, a representation (μ, v) of T and a representation (μ′, v′) of ∂T with A(η) = ∫_{A_t} v(η) dμ, B(ω) = ∫_{A_t} v′(ω) dμ′ and S(ω) = A(dω) − B(ω). For bounded Borel k on ℝ^P put T⌞k(η) := ∫ k v(η) dμ and (∂T)⌞k(ω) := ∫ k v′(ω) dμ′ (integrable since v(η), v′(ω) are). Fix ω ∈ D^m(U).
 (2) h^{(σ)} is smooth with 0 ≤ h^{(σ)} ≤ 1, so h^{(σ)}ω ∈ D^m(U) and d(h^{(σ)}ω) = dh^{(σ)}∧ω + h^{(σ)}dω with both terms in D^n(U). Hence ∂T(h^{(σ)}ω) = T(dh^{(σ)}∧ω) + T(h^{(σ)}dω). By the representations, ∂T(h^{(σ)}ω) = ∫ h^{(σ)}v′(ω) dμ′ → (∂T)⌞h(ω) and T(h^{(σ)}dω) = ∫ h^{(σ)}v(dω) dμ → T⌞h(dω) as σ ↓ 0 (h^{(σ)} → h uniformly; dominated convergence with |v′(ω)|, |v(dω)|). Therefore lim_{σ↓0} T(dh^{(σ)}∧ω) exists and (∂T)⌞h(ω) = lim_{σ↓0} T(dh^{(σ)}∧ω) + T⌞h(dω).
 (3) Since ξ(x) orients T_xM for Hⁿ-a.e. x ∈ M, only the tangential part of dh^{(σ)} contributes: ⟨ξ, dh^{(σ)}∧ω⟩ = ⟨ξ⌞∇^M h^{(σ)}, ω⟩ = Y·∇^M h^{(σ)} with the bounded measurable field Y(x) := Σ_i ⟨ξ(x), e_i*∧ω(x)⟩ e_i, which vanishes off tsupport ω. Hence T(dh^{(σ)}∧ω) = ∫_M θ⟨ξ⌞∇^M h^{(σ)}, ω⟩ dHⁿ, and by (1), lim_{σ↓0} T(dh^{(σ)}∧ω) = ∫_M θ⟨ξ⌞∇^M h, ω⟩ dHⁿ.
 (4) By the chain rule, ∇^M h = ψ′(f)∇^M f Hⁿ-a.e. on M (with ψ′(f) := 0 where f ∈ {t−ε, t}; there ∇^M f = 0 Hⁿ-a.e. by step 2, and then ∇^M h = 0 too since |h(y) − h(x)| ≤ ε⁻¹|f(y) − f(x)|). Hence
 (∂T)⌞h(ω) = −ε⁻¹∫_{M∩{t−ε<f<t}} θ⟨ξ⌞∇^M f, ω⟩ dHⁿ + T⌞h(dω).
 (5) Let ε ↓ 0. g_ω := θ⟨ξ⌞(∇^M f/|∇^M f|), ω⟩1_{M₊} is Hⁿ-integrable on M (|g_ω| ≤ θ‖ω‖ on M ∩ tsupport ω, 0 elsewhere), and θ⟨ξ⌞∇^M f, ω⟩ = |∇^M f|g_ω on M. By Remark 4.2 (step 2), with φ_ω(r) := ∫_{M_r} g_ω dHⁿ⁻¹ ∈ L¹(ℝ), ε⁻¹∫_{M∩{t−ε<f<t}} |∇^M f| g_ω dHⁿ = ε⁻¹∫_{t−ε}^{t} φ_ω(r) dr → φ_ω(t) at every Lebesgue point t of φ_ω, i.e. for t outside an L¹-null set F_ω (Lebesgue differentiation theorem), and φ_ω(t) = ∫_{M_t} θ⟨ξ_t, ω⟩ dHⁿ⁻¹ = ⟨T,f,t⟩(ω) for t ∉ F₀. On the other hand h = h_ε → 1_{A_t} pointwise on U (if f(x) < t then h_ε(x) = 1 once ε < t − f(x); if f(x) ≥ t then h_ε(x) = 0), and v′(ω), v(dω) vanish off tsupport ω ⊆ U, so by dominated convergence (∂T)⌞h_ε(ω) → B(ω) and T⌞h_ε(dω) → A(dω), for every t. Hence for t ∉ F₀ ∪ F_ω: B(ω) = −⟨T,f,t⟩(ω) + A(dω), i.e. S(ω) = ⟨T,f,t⟩(ω). The set F_ω depends only on (M, θ, ξ), f and ω, not on S or on its representations.
 (6) (A null set independent of ω.) Choose compacts K_j ⊆ U with K_j ⊆ int K_{j+1}, ⋃K_j = U. For each j, D_j := {ω ∈ D^m(U) : tsupport ω ⊆ K_j} is a subset of the separable normed space of C¹ forms supported in K_j with norm ‖ω‖_{C¹} := sup|ω| + sup‖Dω‖ (it embeds isometrically in C(K_j; Λ^m × L(ℝ^P, Λ^m)), separable since K_j is a compact metric space); hence D_j has a countable ‖·‖_{C¹}-dense subset Q_j. Let {ω_k} := ⋃_j Q_j and F := F₀ ∪ ⋃_k F_{ω_k}, an L¹-null set. Let t ∉ F and S with IsSlice T f t S (with A, B, (μ, v), (μ′, v′) as above). Then S(ω_k) = ⟨T,f,t⟩(ω_k) for all k. Given ω ∈ D^m(U), tsupport ω ⊆ K_j for some j, and there are ω_{k_i} ∈ Q_j with ‖ω_{k_i} − ω‖_{C¹} → 0. Continuity of S: for a compact K ⊆ U, testing with χdx^β (χ smooth, compactly supported in U, χ = 1 on K) shows that v^β := v(dx^β) and v′^γ := v′(dx^γ) are integrable on K, so c_K := Σ_β ∫_K |v^β| dμ + Σ_γ ∫_K |v′^γ| dμ′ < ∞, and by Fact A, |S(ϖ)| ≤ ∫_K |v(dϖ)| dμ + ∫_K |v′(ϖ)| dμ′ ≤ c_K(‖dϖ‖ + ‖ϖ‖) ≤ c_K·C·‖ϖ‖_{C¹} whenever tsupport ϖ ⊆ K (C depends only on m, P, since dϖ is a fixed linear image of Dϖ). Continuity of ⟨T,f,t⟩: step 3 (last sentence). Hence S(ω) = lim_i S(ω_{k_i}) = lim_i ⟨T,f,t⟩(ω_{k_i}) = ⟨T,f,t⟩(ω).

5. (Conclusion.) For every t outside the L¹-null set F and every S ∈ D_m(U) with IsSlice T f t S, S(ω) = tauAction m M_t θ_t ξ_t ω for all ω ∈ D^m(U), where IsRectifiableTriple U m M_t θ_t ξ_t holds and θ_t takes values in ℕ on M_t (step 3). Hence ∀ᵐ t, ∀ S, IsSlice T f t S → IsIntegerMultiplicity S. ∎

## Key steps

1. Replace f by its McShane extension (IsSlice only sees f on U).
2. Lemma 4.1 / Remark 4.2: co-area slicing of the rectifiable carrier M by f (Simon Ch. 3, 1.6, 2.10, co-area formula), applied on compact exhaustions of U.
3. 4.3–4.4: for a.e. t, ⟨T,f,t⟩ = τ(M_t, θ, ξ⌞∇^Mf/|∇^Mf|) is an integer multiplicity rectifiable triple in U (measurability, local integrability, orientation via co-area and Ch. 3, 1.8–1.9).
4. 4.5(2) printed proof with the IsSlice representations: mollify h = ψ∘f, identity (∂T)⌞h(ω) = lim T(dh^{(σ)}∧ω) + T⌞h(dω), tangential gradients (weak convergence (1)), chain rule.
5. ε ↓ 0: Remark 4.2 and Lebesgue points give S(ω) = ⟨T,f,t⟩(ω) for t outside a null set F_ω depending only on (M,θ,ξ), f, ω.
6. Countable C¹-dense family of forms and C¹-continuity of S (local integrability of the representation coefficients) and C⁰-continuity of ⟨T,f,t⟩ give S = ⟨T,f,t⟩ for all t off one null set.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean against GMT/Ch06/Submission.lean and against snapshot project/GMT/Ch06/Contract.lean (all identical)`
- `read project/GMT/Ch06/Contract.lean: IsMeasureRepresentation, IsRestriction, IsSlice, IsIntegerMultiplicity, IsRectifiableTriple, CompactlyContainedOpen, SlicingTheorem`
- `read simongmt Chapter06/{Currents,Mass,FormsDuality,CurrentLocalEquality,Forms,Representation}.lean: GeometricCurrentOn, TestFormOnConverges, GeometricCurrentOn.boundary, tsupport_exteriorDerivative_subset, massOn, massAdmissibleOn, covectorEuclideanNorm, zeroRegion, support, NVector`
- `grep -rn 'theorem simon_theorem_4_14' simongmt/Poincare/SimonGMT/Chapter01 (RadonPolarRepresentation.lean; IsLocallyBoundedCcFunctional in VectorFunctionalEnvelope.lean; IsRadonOuterMeasure in RadonOuterMeasure.lean)`
- `grep -rln 'coarea|co-area' simongmt/Poincare/SimonGMT (only linear co-area: Chapter02/CoareaLinear.lean, CoareaProjection.lean; no co-area formula for rectifiable sets)`
- `grep -n '^def |^theorem ' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (CountablyRectifiable, HasWeightedApproximateTangentSpaceAt)`
- `grep -rn 'Monotone.ae_differentiableAt|MonotoneOn.intervalIntegral_deriv_mem_uIcc|MonotoneOn.intervalIntegrable_deriv' mathlib/Mathlib`
- `grep -rn 'LipschitzOnWith.extend_real|LipschitzOnWith.ae_differentiableWithinAt_of_mem|theorem measurable_deriv|theorem ext_of_generate_finite' mathlib/Mathlib`
- `grep -rln 'Lusin' mathlib/Mathlib/MeasureTheory (only Lusin–Souslin; Lusin's continuity theorem is cited from Simon Ch. 1, 1.17)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: namespace GMT.Ch06 + opens)`
- `lake build GMT.Ch06.Submission (scratch /tmp/slicing_split_check_r1, frozen d8d46c9, pinned shared packages)`
- `lake env lean Scratch/Stmts.lean and Scratch/FinalChallenge.lean (6 child statements as _root_ comparator targets in the contract scope; 0 errors)`
- `lake env lean Scratch/Assembly.lean (SlicingTheorem from slicing_exists, slicing_support_subset, slicing_mass_bound, slicing_integer_multiplicity_ae; #print axioms)`
- `lake env lean Scratch/Glue.lean (slicing_exists from slicing_mass_representation; slicing_support_subset from slicing_representation_unique; restriction-mass identification from both; #print axioms)`
- `python3 listing of dag.json lean_name values (20 nodes) and grep of the run's nodes/ for the six proposed names (no matches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonPolarRepresentation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/VectorFunctionalEnvelope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/RadonOuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/parent-child-handoff.json`
- `/tmp/slicing_split_check_r1/Scratch/Stmts.lean`
- `/tmp/slicing_split_check_r1/Scratch/FinalChallenge.lean`
- `/tmp/slicing_split_check_r1/Scratch/Assembly.lean`
- `/tmp/slicing_split_check_r1/Scratch/Glue.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 Contract; Submission is byte-identical, so child statements may use only contract, SimonGMT and Mathlib names. SimonGMT provides currents with sequential continuity, boundary, massOn (Euclidean coefficient norm), support/zeroRegion and the vector Riesz theorem `simon_theorem_4_14` on any locally compact Hausdorff space (Radon outer measure, unit field a.e.). It has only linear co-area and no co-area for rectifiable sets, and Mathlib has neither (nor Lusin's continuity theorem), so these are cited from Simon Ch. 3 §2 and Ch. 1, 1.17. Mathlib provides McShane (`LipschitzOnWith.extend_real`), Rademacher (`LipschitzOnWith.ae_differentiableWithinAt_of_mem`), Lebesgue's theorem for monotone functions (`Monotone.ae_differentiableAt`, `MonotoneOn.intervalIntegral_deriv_mem_uIcc`) and π-system uniqueness of finite measures (`ext_of_generate_finite`). In a scratch build of the frozen project, all six child statements elaborate in the comparator's child scope. `SlicingTheorem` follows from the four property children by `choose` plus assembly. `slicing_exists` follows from `slicing_mass_representation`, `slicing_support_subset` from `slicing_representation_unique`, and the restriction-mass identification used by `slicing_mass_bound` from both. All of these are kernel-checked with axioms [propext, Classical.choice, Quot.sound]. The DAG (20 nodes) reserves none of the six proposed names; the concurrently added polyhedral children have different names and types. These checks do not certify the analytic proofs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
