<!-- theorem-id: gmt-ch06/root.lipschitz_pushforward_im-a1 -->

## Theorem `Submission.lipschitz_pushforward_integer_multiplicity`

For all P, Q, n, open U ⊆ ℝ^P and V ⊆ ℝ^Q, every integer multiplicity T ∈ D_n(U) and every f : ℝ^P → ℝ^Q that is locally Lipschitz on U with f(U) ⊆ V and f⁻¹(K) ∩ spt T compact for every compact K ⊆ V, there is S ∈ D_n(V) such that S = f_#T in the sense of (3.6) (IsLipschitzPushforward T f S, i.e. S(ω) = ∫_M θ⟨ω(f(x)), L(x)_#ξ(x)⟩dHⁿ for a representation T = τ(M,θ,ξ) and linear maps L(x) giving the directional derivatives of f along the weighted approximate tangent space), and S is integer multiplicity.

Node: `root.lipschitz_pushforward_im-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/718, https://github.com/ZhengyangZhang06/gmt-formalize/issues/720, https://github.com/ZhengyangZhang06/gmt-formalize/issues/723, https://github.com/ZhengyangZhang06/gmt-formalize/issues/726, https://github.com/ZhengyangZhang06/gmt-formalize/issues/728, https://github.com/ZhengyangZhang06/gmt-formalize/issues/731, https://github.com/ZhengyangZhang06/gmt-formalize/issues/732, https://github.com/ZhengyangZhang06/gmt-formalize/issues/735, https://github.com/ZhengyangZhang06/gmt-formalize/issues/738, https://github.com/ZhengyangZhang06/gmt-formalize/issues/740, https://github.com/ZhengyangZhang06/gmt-formalize/issues/741

## Lean problem

Declaration: `Submission.lipschitz_pushforward_integer_multiplicity`

```lean
LipschitzPushforwardIntegerMultiplicity
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
- Child DAG node: `root.lipschitz_pushforward_im-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, 3.3–3.9 (pp. 146–148): the definition (3.6) of f_#T for an integer multiplicity T = τ(M,θ,ξ) and a Lipschitz f with f|spt T proper, the computations 3.4–3.5, the area-formula rewriting 3.6–3.8 and the conclusion Lemma 3.9 (f_#T = τ(f(M), N, ζ)). The printed argument is copied below in numbered form; the points it leaves implicit for the exact Lean statement (the choice of the linear maps L(x) required by `IsLipschitzPushforward`, the integrability that makes S a current, the printed assertion that for Hⁿ-a.e. y the approximate tangent space T_y(f(M)) exists and is the image d^Mf_x(T_xM) for every x ∈ f⁻¹(y) ∩ M₊ (needed for 3.7), and the verification of every field of `IsRectifiableTriple`) are filled in. No erratum applies (the printed “Hence (a) gives” refers to 3.6). Correction of the previous draft (Step 5): the images f(A_k) of different source pieces may overlap with positive density (two sheets may project onto the same plane region), so no claim is made that one image piece has zero density at the points of another. Instead, Step 5.3 compares every piece with the whole image Y = f(M₊): the complement Y ∖ f(A_k) has zero density at almost every point of f(A_k), which gives T_yY = T_y f(A_k) = T_yN′_k there (so overlapping sheets automatically have the same pushed-forward tangent plane), and the exceptional image sets are pulled back to Hⁿ-null source sets through the area formula, so that the agreement holds for every contributing preimage at Hⁿ-almost every image point.

Setting. U ⊆ ℝ^P, V ⊆ ℝ^Q open; T ∈ D_n(U) integer multiplicity: T(ω) = ∫_M θ⟨ω,ξ⟩dHⁿ for all ω ∈ Dⁿ(U), with `IsRectifiableTriple U n M θ ξ` and θ(x) ∈ {1,2,…} on M; f : ℝ^P → ℝ^Q locally Lipschitz on U, f(U) ⊆ V, and f⁻¹(K) ∩ spt T compact for every compact K ⊆ V. Hⁿ = μHE[n]. Notation |α|, ‖ω‖, w^β, |w| and Fact A (w(α) = Σ_β α(e_β)w^β, |w(α)| ≤ |α||w|) are as in the conventions: |α| = `covectorEuclideanNorm α`, w^β = w(dx^β).

Preliminary facts.
(P1) If τ₁,…,τ_n are orthonormal then |simpleNVector τ| = 1 (coordinates are the n×n minors det(τ_i·e_{β_j}); by Cauchy–Binet Σ_β det(τ_i·e_{β_j})² = det(τ_i·τ_j) = 1). For a linear map A, A_#(simpleNVector τ) = simpleNVector(Aτ) (`nVectorPushforward_simple`) and |A_#(simpleNVector τ)| = det(Aτ_i·Aτ_j)^{1/2} =: J_A(span τ), the Jacobian of A on span τ; it is ≤ ‖A‖ⁿ and it is 0 iff A|span τ has rank < n. Hence |⟨α, A_#ξ⟩| ≤ |α|·J_A ≤ |α|‖A‖ⁿ when ξ = ±simpleNVector τ.
(P2) Hⁿ(M ∖ spt T) = 0. Proof: U ∖ spt T is the union of the open sets W (closure W compact ⊆ U) on which T vanishes; by Lindelöf countably many W_k suffice. Fix k. For φ ∈ C_c^∞(W_k) and β ∈ I(n,P), the test form φ dx^β gives 0 = T(φ dx^β) = ∫_{M} φ θ ξ^β dHⁿ. The signed measures ν_β := θξ^β Hⁿ⌞M are Radon on U (θ is Hⁿ-integrable on M ∩ K for compact K ⊆ U, |ξ^β| ≤ |ξ| = 1 Hⁿ-a.e. on M by P1 and the orientation property). A signed Radon measure on W_k annihilating C_c^∞(W_k) vanishes on W_k, so θ|ξ| = 0 Hⁿ-a.e. on M ∩ W_k; since θ > 0 on M and |ξ| = 1 a.e. on M, Hⁿ(M ∩ W_k) = 0. Summing over k gives the claim (M ⊆ U).
(P3) (Null sets and measurability under f.) (i) If Z ⊆ U and Hⁿ(Z) = 0 then Hⁿ(f(Z)) = 0: since f is locally Lipschitz on the open set U, U is the union of countably many open balls B (closure in U) on each of which f is Lipschitz (Lindelöf), and Hⁿ(f(Z ∩ B)) ≤ (Lip f|_B)ⁿHⁿ(Z ∩ B) = 0. (ii) If A ⊆ U is Hⁿ-measurable with Hⁿ⌞A σ-finite, then f(A) is Hⁿ-measurable: by inner regularity of the Borel regular measure Hⁿ on sets of finite measure (Simon Ch. 1, 1.15: closed inner approximants, intersected with closed balls B̄_R to make them compact) A = ⋃_iC_i ∪ Z with C_i compact and Hⁿ(Z) = 0; each f(C_i) is compact (f is continuous on U) and Hⁿ(f(Z)) = 0 by (i).
(P4) (Locality of approximate tangent spaces; Simon Ch. 3, Definition 1.4, the proof of 1.6 “⇒”, Remark 1.5(2), and the Upper Density Theorem Ch. 1, 3.6 with Remark 3.7(2).) Let V₀ ⊆ ℝ^Q be open and Y ⊆ V₀ Hⁿ-measurable with Hⁿ(Y ∩ K) < ∞ for every compact K ⊆ V₀; approximate tangent spaces T_yY (Definition 1.4) at y ∈ V₀ only involve Y ∩ B for an arbitrarily small ball B ∋ y, so Definition 1.4 and Ch. 3, 1.6 are applied to Y ∩ V₀^{(i)} for open V₀^{(i)} ⊂⊂ V₀ exhausting V₀. (a) (Subsets.) If Y′ ⊆ Y is Hⁿ-measurable, then for Hⁿ-a.e. y ∈ Y′ the upper density Θ*ⁿ(Hⁿ⌞(Y ∖ Y′), y) is 0 (Upper Density Theorem applied to the set (Y ∖ Y′) ∩ V₀^{(i)} of finite measure, at points of Y′ ∩ V₀^{(i)}, which lie outside it), and at every such y: T_yY exists ⇔ T_yY′ exists, and then T_yY = T_yY′. Indeed for φ ∈ C_c^0(ℝ^Q) with spt φ ⊆ B_R(0) and small λ, |∫_{η_{y,λ}(Y)}φ dHⁿ − ∫_{η_{y,λ}(Y′)}φ dHⁿ| ≤ sup|φ|·λ^{−n}Hⁿ((Y∖Y′) ∩ B_{λR}(y)) → 0. (b) (Subsets of C¹ manifolds.) If N ⊆ ℝ^Q is an embedded n-dimensional C¹ submanifold and Y′ ⊆ N is Hⁿ-measurable, then T_yY′ exists and equals the classical tangent space T_yN for Hⁿ-a.e. y ∈ Y′: every y ∈ N has a ball B with N ∩ B a single C¹ graph of finite Hⁿ-measure, T_y(N ∩ B) = T_yN at every point of N ∩ B (C¹ blow-up, as in the proof of Ch. 3, 1.6 “⇒”), and (a) applies to Y′ ∩ B ⊆ N ∩ B; countably many such balls cover N. (c) (Existence.) If Y is moreover countably n-rectifiable then T_yY exists for Hⁿ-a.e. y ∈ Y (Ch. 3, Theorem 1.6 applied to Y ∩ V₀^{(i)}).

Proof.

1. (Structure of M; Simon Ch. 3, 1.2–1.3, 1.8–1.9. These results assume ∫_{M∩K}θ < ∞ for all compact K ⊆ ℝ^P; here this holds for compact K ⊆ U, so they are applied to M ∩ U_i for open U_i ⊂⊂ U exhausting U — weighted tangent spaces at points of U_i only depend on M ∩ U_i and θ there.) M is countably n-rectifiable and Hⁿ-measurable, so M = ⋃_{j≥0} M_j (disjoint, Hⁿ-measurable) with Hⁿ(M₀) = 0 and M_j ⊆ N_j, N_j embedded n-dimensional C¹ submanifolds of ℝ^P. Since θ ≥ 1 and θ is integrable on M ∩ K for compact K ⊆ U, Hⁿ⌞M is locally finite in U. By Ch. 3, Theorem 1.9 and Remark 1.8(1), for Hⁿ-a.e. x ∈ M the weighted approximate tangent space T_xM of M with respect to θ exists (`HasWeightedApproximateTangentSpaceAt n M θ x (T_xM)`), and T_xM = T_xN_j for Hⁿ-a.e. x ∈ M_j (Remark 1.8(1) identifies the weighted tangent space with the approximate tangent space of a Lusin piece of M, and P4(a),(b) below — applied to that piece intersected with M_j ⊆ N_j — identify the latter with T_xN_j a.e.). By the `orients` field, for Hⁿ-a.e. x ∈ M, ξ(x) = ±simpleNVector(τ(x)) with τ(x) an orthonormal basis of T_xM; the weighted tangent space is unique when θ(x) > 0 (`HasWeightedApproximateTangentSpaceAt.unique`).

2. (The tangential differential d^M f and the maps L(x); Simon Ch. 3 §2, p. 76.) Fix j ≥ 1 and x ∈ N_j. Writing ℝ^P = T_xN_j ⊕ (T_xN_j)^⊥, a neighbourhood of x in N_j is {x + w + g(w)} for a C¹ map g defined near 0 ∈ T_xN_j with g(0) = 0, Dg(0) = 0; Φ_x(w) := x + w + g(w) is a C¹ chart. f∘Φ_x is Lipschitz near 0. Covering N_j ∩ U by countably many such charts (Lindelöf: N_j is second countable) and using Rademacher's theorem in each chart together with the fact that C¹ charts map Lⁿ-null sets to Hⁿ-null sets, we get: for Hⁿ-a.e. x ∈ M_j the map f|N_j is differentiable at x, i.e. there is a linear map d^M f_x : T_xN_j → ℝ^Q with f(Φ_x(w)) = f(x) + d^Mf_x(w) + o(|w|). For v ∈ T_xN_j and t → 0, x + tv = Φ_x(tv) − g(tv) with |g(tv)| = o(t), so |f(x+tv) − f(Φ_x(tv))| ≤ Lip·o(t) (f is Lipschitz near x because x ∈ U and f is locally Lipschitz on U); hence t ↦ f(x + tv) is differentiable at t = 0 with derivative d^Mf_x(v), for every v ∈ T_xN_j simultaneously. Define L(x) := d^Mf_x ∘ π_{T_xM} (π = orthogonal projection) at the Hⁿ-a.e. points x ∈ M where all of the above holds and T_xM = T_xN_j, and L(x) := 0 otherwise. L is Hⁿ⌞M-measurable: the orthogonal projection onto T_xM is a continuous function of ξ(x) invariant under ξ ↦ −ξ (so it is measurable), Gram–Schmidt with measurable case distinctions gives a measurable orthonormal frame τ(x) of T_xM, and L(x)τ_i(x) = lim_{k→∞}1_{{dist(·,ℝ^P∖U) > 1/k}}(x)·k(f(x + τ_i(x)/k) − f(x)) a.e. (the cut-off keeps x + τ_i(x)/k in U, where f is continuous, so each term is measurable); thus L agrees Hⁿ⌞M-a.e. with a measurable map, which is all that is needed for the measurability of the integrands below; and for every compact K ⊆ U, Λ_K := sup_{x∈K∩M} ‖L(x)‖ < ∞ (cover K by finitely many open sets on which f is Lipschitz; ‖d^Mf_x‖ is bounded by the Lipschitz constant there). Consequently: for Hⁿ⌞M-a.e. x, for every T_x with `HasWeightedApproximateTangentSpaceAt n M θ x T_x` we have T_x = T_xM (uniqueness, θ(x) > 0) and `HasDerivAt (fun t => f (x + t • v)) (L x v) 0` for all v ∈ T_x. This is the third clause of `IsLipschitzPushforward`.

3. (Definition of S = f_#T, printed 3.6, and well-definedness.) For ω ∈ Dⁿ(V) set
S(ω) := ∫_M θ(x)⟨ω(f(x)), L(x)_#ξ(x)⟩ dHⁿ(x) = ∫_M θ(x)·`nVectorPushforward n (L x) (ξ x)`(ω(f(x))) dHⁿ(x).
Let K := tsupport ω (compact ⊆ V) and K′ := f⁻¹(K) ∩ spt T, compact ⊆ U by hypothesis. The integrand vanishes unless f(x) ∈ K, and by (P2) Hⁿ-a.e. such x ∈ M lies in K′. On M ∩ K′ the integrand is measurable and bounded by θ(x)‖ω‖Λ_{K′}ⁿ (P1, Step 2), and θ is integrable on M ∩ K′ (`integrableOn` of the triple). So S(ω) is an absolutely convergent integral, S is linear, and if ω_k → 0 in Dⁿ(V) with tsupports in one compact K, dominated convergence (same dominating function with ‖ω_k‖ → 0) gives S(ω_k) → 0. Hence S ∈ `GeometricCurrentOn V n`, and `IsLipschitzPushforward T f S` holds with the data (M, θ, ξ, L) (the first two clauses are the given i.m. representation of T, the third is Step 2, the fourth is the definition of S).

4. (Printed 3.4–3.5: where the Jacobian vanishes and the induced orientation.) Let J^Mf(x) := |L(x)_#ξ(x)| = Jacobian of d^Mf_x on T_xM (P1) and M₊ := {x ∈ M : J^Mf(x) > 0}. On M ∖ M₊, L(x)_#ξ(x) = 0 (rank d^Mf_x < n), so S(ω) = ∫_{M₊} θ⟨ω∘f, L_#ξ⟩dHⁿ. For x ∈ M₊ put η_x := L(x)_#ξ(x)/J^Mf(x); since L(x)_#ξ(x) = ±(d^Mf_xτ₁)∧⋯∧(d^Mf_xτ_n), η_x is a unit simple n-vector orienting the n-plane d^Mf_x(T_xM) (printed 3.5: d f_{x#} ξ = J^Mf(x)·η). (This holds at every x ∈ M₊ where L(x) is defined by Step 2, not only where the orientation property holds: L(x) = d^Mf_x∘π_{T_xM} has range d^Mf_x(T_xM), so L(x)_# maps every n-vector into the one-dimensional space Λ_n(d^Mf_x(T_xM)), and a nonzero element of it, normalized, is a unit simple n-vector orienting that plane.)

5. (Printed 3.6–3.8: area formula, tangent agreement, multiplicities.)
 5.1 (Consequences of the area formula; Simon Ch. 3, 2.4–2.5.) For every Hⁿ-measurable A ⊆ M and every Hⁿ-measurable h ≥ 0 on M, ∫_A hJ^Mf dHⁿ = ∫_{ℝ^Q}Σ_{x∈A∩f⁻¹(y)}h(x) dHⁿ(y) (Simon states 2.4–2.5 for f locally Lipschitz on an open set containing M, which is the present situation; for integrable signed h split h = h⁺ − h⁻). Consequences:
  (a) If E ⊆ ℝ^Q is Hⁿ-null, then Hⁿ(M₊ ∩ f⁻¹(E)) = 0. Indeed choose a Borel Hⁿ-null E′ ⊇ E; A := M₊ ∩ f⁻¹(E′) is Hⁿ-measurable (f is continuous on U), ∫_AJ^Mf dHⁿ = ∫_{E′}#(A ∩ f⁻¹(y)) dHⁿ(y) = 0 and J^Mf > 0 on A, so Hⁿ(A) = 0.
  (b) For compact K ⊆ V let K′ := f⁻¹(K) ∩ spt T (compact ⊆ U by hypothesis). Then ∫_K Σ_{x∈M₊∩K′∩f⁻¹(y)}θ(x) dHⁿ(y) = ∫_{M₊∩K′}θJ^Mf dHⁿ ≤ Λ_{K′}ⁿ∫_{M∩K′}θ dHⁿ < ∞ (P1, Step 2), and Hⁿ(f(M₊ ∩ K′)) ≤ ∫#(M₊ ∩ K′ ∩ f⁻¹(y)) dHⁿ(y) = ∫_{M₊∩K′}J^Mf dHⁿ < ∞ (θ ≥ 1).
  (c) Hⁿ(f(M ∖ M₊)) ≤ ∫#((M∖M₊) ∩ f⁻¹(y)) dHⁿ(y) = ∫_{M∖M₊}J^Mf dHⁿ = 0, and Hⁿ(f(M ∖ spt T)) = 0 (P2, P3(i)).
 Put Y := f(M₊). Then: Y ⊆ f(U) ⊆ V; Y is Hⁿ-measurable (P3(ii); Hⁿ⌞M is locally finite in U, so M₊ is Hⁿ-σ-finite); Y is countably n-rectifiable (M ⊆ M₀′ ∪ ⋃_jF_j(ℝⁿ) with Hⁿ(M₀′) = 0 and F_j Lipschitz; for each of the countably many balls B of P3(i), f∘F_j restricted to F_j⁻¹(B) is Lipschitz and extends to a Lipschitz map ℝⁿ → ℝ^Q, and f(M₀′ ∩ U) is null by P3(i)); and for every compact K ⊆ V, Y ∩ K ⊆ f(M₊ ∩ K′) ∪ f(M ∖ spt T), so Hⁿ(Y ∩ K) < ∞ by (b), (c). By P4(c) (with V₀ := V), T_yY exists for Hⁿ-a.e. y ∈ Y.
 5.2 (Source pieces on which f is an injective C¹ immersion; Simon Ch. 2, 1.5 (C¹ approximation) and the inverse function theorem.) Fix j ≥ 1 and a C¹ chart Φ : Ω → N_j (Ω ⊆ ℝⁿ open, Φ a C¹ diffeomorphism onto a relatively open subset of N_j contained in one of the balls B of P3(i), so f is Lipschitz on Φ(Ω)); countably many such charts cover M_j ⊆ N_j ∩ U. The map u := f∘Φ is locally Lipschitz on Ω; at every w with x := Φ(w) in the full-measure set of Step 2 (where f∘Φ_x is differentiable at 0 with derivative d^Mf_x), the chain rule applied to u = (f∘Φ_x)∘(Φ_x⁻¹∘Φ) near w gives that u is differentiable at w with Du(w) = d^Mf_x∘DΦ(w) (D(Φ_x⁻¹∘Φ)(w) = DΦ(w), whose range is T_xN_j). Shrinking the charts we may assume Φ is Lipschitz on Ω; then u is Lipschitz on Ω and extends (componentwise McShane) to a Lipschitz map ℝⁿ → ℝ^Q. By Ch. 2, 1.5 (componentwise), for each i ≥ 1 there is G_i ∈ C¹(ℝⁿ;ℝ^Q) with Lⁿ({u ≠ G_i} ∪ {Du ≠ DG_i}) < 1/i; so Ω = Z ∪ ⋃_iΩ_i with Lⁿ(Z) = 0 and Ω_i := {w : u(w) = G_i(w), u differentiable at w, Du(w) = DG_i(w)} (Lebesgue measurable). If w ∈ Ω_i and x = Φ(w) ∈ M₊ is a point of Step 2 with T_xM = T_xN_j, then DG_i(w) = d^Mf_x∘DΦ(w) has rank n (J^Mf(x) > 0), so by the inverse function theorem (local immersion theorem) w has an open neighbourhood O ⊆ Ω such that G_i|O is injective and N′ := G_i(O) is an embedded n-dimensional C¹ submanifold of ℝ^Q with T_{G_i(w′)}N′ = DG_i(w′)(ℝⁿ) for w′ ∈ O; at such points, f(x) = G_i(w) and d^Mf_x(T_xM) = d^Mf_x(DΦ(w)(ℝⁿ)) = DG_i(w)(ℝⁿ) = T_{f(x)}N′. By Lindelöf, countably many such O cover these points of Ω_i. Since Φ is locally Lipschitz, Φ maps Lⁿ-null sets to Hⁿ-null sets, and Φ⁻¹ (locally Lipschitz on Φ(Ω)) maps Hⁿ-null sets to Lⁿ-null sets. Collecting over all j, charts, i and neighbourhoods O (countably many), intersecting each piece Φ(O ∩ Ω_i) with M₊ ∩ M_j for the chart's own j, and disjointifying, we obtain pairwise disjoint Hⁿ-measurable sets A_k ⊆ M₊ (k ∈ ℕ) with Hⁿ(M₊ ∖ ⋃_kA_k) = 0, and for each k an embedded n-dimensional C¹ submanifold N′_k ⊆ ℝ^Q and an Hⁿ-null set Z⁰_k ⊆ A_k such that: f|A_k is injective (f = G_i∘Φ⁻¹ on A_k with G_i|O injective), f(A_k) ⊆ N′_k, the inverse (f|A_k)⁻¹ is the restriction to f(A_k) of the continuous map Φ∘(G_i|O)⁻¹ on N′_k, and for every x ∈ A_k ∖ Z⁰_k: T_xM exists and equals T_xN_j, the orientation property ξ(x) = ±simpleNVector τ(x) holds, Step 2 holds at x, and d^Mf_x(T_xM) = T_{f(x)}N′_k (Z⁰_k collects the Hⁿ-null sets where one of these fails, together with the image under Φ of the Lⁿ-null exceptional sets of the chart). Put Y_k := f(A_k) ⊆ Y ∩ N′_k (Hⁿ-measurable by P3(ii)).
 5.3 (Tangent agreement for every contributing preimage at Hⁿ-a.e. image point.) Claim: there is an Hⁿ-null set E ⊆ ℝ^Q such that for every y ∈ Y ∖ E the approximate tangent space T_yY exists and d^Mf_x(T_xM) = T_yY for every x ∈ f⁻¹(y) ∩ M₊ (in particular each such x is a point where T_xM and d^Mf_x exist). Proof.
  (i) E₁ := {y ∈ Y : T_yY does not exist} is Hⁿ-null (5.1).
  (ii) For each k apply P4(a) to Y_k ⊆ Y (V₀ := V; this uses the local finiteness of Hⁿ⌞Y proved in 5.1: the image complement Y ∖ Y_k has upper density 0 at Hⁿ-a.e. point of Y_k, whether or not other images Y_{k′} overlap Y_k), and P4(b) to Y_k ⊆ N′_k: there is an Hⁿ-null set E_{2,k} ⊆ Y_k such that T_yY = T_yY_k = T_yN′_k for every y ∈ Y_k ∖ (E₁ ∪ E_{2,k}). (On an overlap Y_k ∩ Y_{k′}, outside E₁ ∪ E_{2,k} ∪ E_{2,k′}, this gives T_yN′_k = T_yY = T_yN′_{k′}: different sheets through the same image point have the same pushed-forward tangent plane.)
  (iii) Pull back the exceptional sets through the area formula: Z_k := A_k ∩ f⁻¹(E₁ ∪ E_{2,k}) is Hⁿ-null by 5.1(a). For x ∈ A_k ∖ (Z_k ∪ Z⁰_k) and y := f(x) ∈ Y_k ∖ (E₁ ∪ E_{2,k}): d^Mf_x(T_xM) = T_yN′_k = T_yY.
  (iv) B := (M₊ ∖ ⋃_kA_k) ∪ ⋃_k(Z_k ∪ Z⁰_k) is an Hⁿ-null subset of M₊, so E := E₁ ∪ f(B) is Hⁿ-null (P3(i)). If y ∈ Y ∖ E and x ∈ f⁻¹(y) ∩ M₊, then x ∉ B (otherwise y ∈ f(B)), so x ∈ A_k ∖ (Z_k ∪ Z⁰_k) for the unique k with x ∈ A_k, and (iii) gives d^Mf_x(T_xM) = T_yY. This proves the claim.
 5.4 (Printed 3.7–3.8: the induced orientation and the multiplicity.) Enlarge E by the Hⁿ-null set f(M ∖ spt T) (5.1(c)) and, for each K = K_i of a compact exhaustion K_1 ⊆ K_2 ⊆ ⋯ of V, by the Hⁿ-null set of y ∈ K_i with Σ_{x∈M₊∩K_i′∩f⁻¹(y)}θ(x) = ∞ (5.1(b)); E stays Hⁿ-null and the claim of 5.3 still holds off E. For y ∈ Y ∖ E let F_y := f⁻¹(y) ∩ M₊. Then F_y ⊆ spt T (as y ∉ f(M ∖ spt T)), hence F_y ⊆ K_i′ for every i with y ∈ K_i, so Σ_{x∈F_y}θ(x) < ∞, and since θ ≥ 1 the fibre F_y is finite (and nonempty, as y ∈ f(M₊)). By Step 4 and 5.3, every η_x (x ∈ F_y) is a unit simple n-vector orienting the same n-plane T_yY. For a unit simple n-vector w let s(w) := w if the first nonzero coordinate w^γ (γ ∈ I(n,Q) in lexicographic order) is positive and s(w) := −w otherwise; two unit simple n-vectors orienting the same n-plane are equal up to sign, so s(η_x) depends only on T_yY. Define ζ(y) := s(η_x) for any x ∈ F_y (y ∈ Y ∖ E), and ζ := 0 elsewhere. ζ is Hⁿ-measurable: on Y_k ∖ E, ζ = s∘η∘(f|A_k)⁻¹ with (f|A_k)⁻¹ continuous (5.2), s Borel, and η agreeing with a Borel function off an Hⁿ-null subset of A_k, whose image is Hⁿ-null (P3(i)); and Y ∖ E ⊆ ⋃_kY_k. Hence (printed 3.7) η_x = ε_xζ(y) with ε_x ∈ {1,−1} for every x ∈ F_y, and (printed 3.8)
 Σ_{x∈F_y}θ(x)η_x = c(y)ζ(y),  c(y) := Σ_{x∈F_y}ε_xθ(x) ∈ ℤ,  |c(y)| ≤ Σ_{x∈F_y}θ(x),  |c(y)| ≡ Σ_{x∈F_y}θ(x) (mod 2).
 c is Hⁿ-measurable on Y ∖ E: c(y) = ⟨Σ_kΣ_{x∈F_y∩A_k}θ(x)η_x, ζ(y)⟩ (Euclidean inner product of n-vectors, |ζ(y)| = 1), and y ↦ 1_{Y_k}(y)(θη)((f|A_k)⁻¹(y)) is Hⁿ-measurable for each k by the same argument.
 5.5 (Printed 3.6.) Let ω ∈ Dⁿ(V) and K := tsupport ω. On M₊, L(x)_#ξ(x) = J^Mf(x)η_x; off M₊ it is 0 (Step 4). The function h := θ⟨ω∘f, η⟩ on M₊ satisfies |h|J^Mf ≤ ‖ω‖θJ^Mf1_{K′} Hⁿ-a.e. on M₊ (P2), which is integrable by 5.1(b). By 5.1 (applied to h⁺, h⁻) and 5.4,
 S(ω) = ∫_{M₊}θ⟨ω∘f, η⟩J^Mf dHⁿ = ∫_{ℝ^Q}Σ_{x∈F_y}θ(x)⟨ω(y), η_x⟩ dHⁿ(y) = ∫_{Y∖E}c(y)⟨ω(y), ζ(y)⟩ dHⁿ(y),   (3.6)
 using that Hⁿ-a.e. y with F_y ≠ ∅ lies in Y ∖ E.

6. (The integer multiplicity representation of S.) Let M′ := {y ∈ Y ∖ E : c(y) ≠ 0}, and on M′ put θ′(y) := |c(y)| ∈ {1,2,…} and ξ′(y) := sign(c(y))ζ(y) (off M′ put θ′ := 1, ξ′ := 0). By (3.6), S(ω) = ∫_{M′}θ′⟨ω, ξ′⟩ dHⁿ = `tauAction n M′ θ′ ξ′ ω` for all ω ∈ Dⁿ(V).

7. (Verification of `IsRectifiableTriple V n M′ θ′ ξ′` and integrality — Lemma 3.9.)
 • M′ ⊆ Y ⊆ f(U) ⊆ V.
 • M′ is Hⁿ-measurable (Y is Hⁿ-measurable, E is Hⁿ-null and c is Hⁿ-measurable; 5.1, 5.4), so `NullMeasurableSet M′ μHE[n]`.
 • M′ ⊆ Y is countably n-rectifiable (5.1; `CountablyRectifiable.mono`).
 • θ′ > 0 on M′ and θ′(y) = |c(y)| ∈ ℕ.
 • For compact K ⊆ V: if y ∈ (Y ∖ E) ∩ K then F_y ⊆ K′ = f⁻¹(K) ∩ spt T, so ∫_{M′∩K}θ′ dHⁿ ≤ ∫_KΣ_{x∈M₊∩K′∩f⁻¹(y)}θ(x) dHⁿ(y) = ∫_{M₊∩K′}θJ^Mf dHⁿ < ∞ (5.1(b)); hence θ′ is integrable on M′ ∩ K.
 • ξ′ is Hⁿ⌞M′-measurable (ζ and c are), hence a.e. strongly measurable (values in a finite-dimensional space).
 • Orientation: θ′ is positive, integer valued and locally Hⁿ-integrable on the countably n-rectifiable set M′ ⊆ V, so by Ch. 3, Theorem 1.9 and Remark 1.8(1) (applied to M′ ∩ V_i for open V_i ⊂⊂ V exhausting V; P4) the weighted approximate tangent space of M′ with respect to θ′ exists at Hⁿ-a.e. y ∈ M′ and equals the approximate tangent space T_yM′ (Remark 1.8(1): up to an Hⁿ-null set M′ is covered by compact pieces M′_j on which θ′ is continuous, and at Hⁿ-a.e. y ∈ M′_j the weighted tangent space of (M′,θ′) exists iff T_yM′_j exists, and then they coincide; T_yM′_j = T_yM′ at Hⁿ-a.e. y ∈ M′_j by P4(a)); by P4(a) applied to M′ ⊆ Y (V₀ := V), T_yM′ = T_yY at Hⁿ-a.e. y ∈ M′; and ξ′(y) = ±ζ(y) orients T_yY (5.4). Hence for Hⁿ-a.e. y ∈ M′ there is an orthonormal basis τ of the weighted approximate tangent space of (M′, θ′) at y with ξ′(y) = simpleNVector τ or ξ′(y) = −simpleNVector τ.
 Therefore S is integer multiplicity, S = τ(M′, θ′, ξ′). Together with Step 3 this proves `LipschitzPushforwardIntegerMultiplicity`.

8. (Degenerate dimensions.) If n > P, no orthonormal n-frame exists in ℝ^P, so the orientation property forces Hⁿ(M) = 0, T = 0 and S = 0 (with M′ = ∅). If n > Q then every n-vector of ℝ^Q is 0 (all n-covectors on ℝ^Q vanish), so L(x)_#ξ(x) = 0, J^Mf ≡ 0, M₊ = ∅, S = 0 and M′ = ∅. If n = 0, simple 0-vectors are ±1, J^Mf ≡ 1, M is countable and locally finite in U (θ ≥ 1 is locally H⁰-integrable), S(ω) = Σ_{y} c(y)ω(y) with c(y) = Σ_{x∈f⁻¹(y)∩M} θ(x)ξ(x) ∈ ℤ, and the weighted tangent space at each point of the locally finite set M′ is {0}; Steps 1–7 apply verbatim with these simplifications.

## Key steps

1. Hⁿ(M ∖ spt T) = 0 for T = τ(M,θ,ξ) integer multiplicity; locally Lipschitz f maps Hⁿ-null sets to null sets and σ-finite measurable sets to measurable sets; approximate tangent spaces are local (subsets, C¹ manifolds, existence on rectifiable sets).
2. Decompose M into C¹ pieces; weighted tangent spaces exist a.e. and equal T_xN_j; ξ orients them.
3. Tangential differential d^Mf_x via C¹ charts and Rademacher; L(x) := d^Mf_x∘π_{T_xM} satisfies the HasDerivAt clause.
4. Define S(ω) by (3.6); integrability on f⁻¹(spt ω) ∩ spt T (compact) gives S ∈ D_n(V) and IsLipschitzPushforward T f S.
5. Jacobian and induced orientation η_x (3.4–3.5); area formula: preimages in M₊ of Hⁿ-null image sets are null, Y = f(M₊) is countably n-rectifiable, Hⁿ-measurable and locally Hⁿ-finite in V.
6. C¹ approximation + inverse function theorem: up to a null set M₊ is a disjoint union of pieces A_k on which f is an injective C¹ immersion into an embedded manifold N′_k with d^Mf_x(T_xM) = T_{f(x)}N′_k.
7. Tangent agreement: the image complement Y ∖ f(A_k) has zero density a.e. on f(A_k), so T_yY = T_y f(A_k) = T_yN′_k there (overlapping sheets agree); pulling the exceptional image sets back through the area formula gives d^Mf_x(T_xM) = T_yY for every x ∈ f⁻¹(y) ∩ M₊ at Hⁿ-a.e. y.
8. Measurable orientation ζ(y) of T_yY, finite fibres, integer multiplicity c(y) = Σ_x ±θ(x) (3.7–3.8), and S(ω) = ∫_Y c⟨ω,ζ⟩dHⁿ (3.6).
9. Verify IsRectifiableTriple for (M′ = {c ≠ 0}, |c|, sign(c)ζ): measurability, rectifiability, local integrability by the area formula, orientation by Ch. 3, 1.9 and locality of tangent spaces; degenerate dimensions n > P, n > Q, n = 0.

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
