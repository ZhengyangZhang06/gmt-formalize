<!-- theorem-id: gmt-ch06/root.boundary_rectifiability-a1.localization-a1.tau_current-a1 -->

## Theorem `Submission.br_loc_tauAction_current`

Let P, n ∈ ℕ, V, M ⊆ ℝ^P (V arbitrary, not necessarily open), θ : ℝ^P → ℝ and ξ : ℝ^P → Λₙ(ℝ^P) (n-vectors, NVector (Eucl P) n = continuous linear functionals on n-covectors). Assume (M, θ, ξ) satisfies the triple conditions of Simon Ch. 6, 3.1 relative to V (IsRectifiableTriple V n M θ ξ): M ⊆ V is Hⁿ-null-measurable and countably n-rectifiable, θ > 0 on M, θ is Hⁿ-integrable on M ∩ K for every compact K ⊆ V, ξ is Hⁿ⌞M-a.e. strongly measurable, and for Hⁿ⌞M-a.e. x, ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ for an orthonormal τ spanning a weighted approximate tangent space of (M, θ) at x (Hⁿ = μHE[n]). Then τ(M, θ, ξ)(ω) = ∫_M θ(x)⟨ω(x), ξ(x)⟩ dHⁿ(x) (tauAction n M θ ξ ω) defines a current: there is X ∈ Dₙ(V) (GeometricCurrentOn V n: an ℝ-linear functional on the test forms Dⁿ(V) that is sequentially continuous in Simon's test-form topology) with X(ω) = τ(M, θ, ξ)(ω) for every ω ∈ Dⁿ(V).

Node: `root.boundary_rectifiability-a1.localization-a1.tau_current-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/880

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1341, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1482

Decomposition children: None

## Lean problem

Declaration: `Submission.br_loc_tauAction_current`

```lean
∀ (P n : ℕ) (V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple V n M θ ξ → ∃ X : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, X ω = tauAction n M θ ξ ω
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

- Parent DAG node: `root.boundary_rectifiability-a1.localization-a1`
- Child DAG node: `root.boundary_rectifiability-a1.localization-a1.tau_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: (H0) and (H2) of the parent proof ("T_A is linear and sequentially continuous, since test-form convergence implies uniform convergence", with the pointwise bound |⟨α, ξ(x)⟩| ≤ c|α|), stated for an arbitrary rectifiable triple. In the parent it is applied with V = ℝ^P and the triple (M ∩ B_r(x₀), θ, ξ) supplied by the sibling triple_inter_open; this gives the current X = τ(M ∩ B_r(x₀), θ, ξ) of steps 5–6, and the domain restriction of X to U is the parent's T_{B_r} (step 4). Here the bound (H0) is used in the sharper operator-norm form of the sibling unit_bound, so no comparison constant c is needed.

Notation. H := Hⁿ = μHE[n]. For an n-covector α (a continuous alternating map), ‖α‖ is its operator norm. For ω ∈ Dⁿ(V) (a C^∞ n-form with compact support and tsupport ω ⊆ V; TestFormOn V n) put F_ω(x) := θ(x)·ξ(x)(ω(x)) and τ(ω) := tauAction n M θ ξ ω = ∫_M F_ω dH. Openness of V is never used.

1. (Integrability.) Let ω ∈ Dⁿ(V). Then ω is continuous (being C^∞), has compact support, and tsupport ω ⊆ V. By the sibling tau_integrable (ltg_tau_integrable, second conjunct (b)), applied to IsRectifiableTriple V n M θ ξ and ω, the function F_ω is H-integrable on M.
2. (Pointwise bound.) By the orientation field of the triple, for H⌞M-a.e. x there is an orthonormal τ : Fin n → ℝ^P with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ. For every such x the sibling unit_bound (fiw_ims_tt_unit_bound) gives |ξ(x)(α)| ≤ ‖α‖ for every n-covector α. Moreover H⌞M-a.e. x lies in M (M is H-null-measurable, so ae_restrict_mem₀ applies), and θ(x) > 0 for every x ∈ M (field pos). Let G be the set of x ∈ M at which the bound of this step holds; H⌞M-a.e. x lies in G.
3. (Linearity.) Let ω, η ∈ Dⁿ(V) and c ∈ ℝ. The underlying forms satisfy (ω + η)(x) = ω(x) + η(x) and (cω)(x) = c·ω(x), and each ξ(x) is linear, so F_{ω+η}(x) = F_ω(x) + F_η(x) and F_{cω}(x) = c·F_ω(x) for every x. Since F_ω and F_η are integrable on M (step 1), τ(ω + η) = ∫_M (F_ω + F_η) dH = τ(ω) + τ(η) (additivity of the Bochner integral, integral_add), and τ(cω) = ∫_M c·F_ω dH = c·τ(ω) (integral_const_mul, which needs no integrability). Hence L(ω) := τ(ω) is an ℝ-linear map Dⁿ(V) → ℝ.
4. (Uniform smallness.) Let (ω_j) be a sequence in Dⁿ(V) converging to 0 in Simon's test-form topology (TestFormOnConverges ω_j 0). By definition there is a compact K ⊆ V with tsupport ω_j ⊆ K for all j, and for every k ∈ ℕ the k-th iterated derivatives of ω_j converge uniformly on K to those of the zero form. For k = 0 the iterated derivative has the same norm as the form itself, ‖D⁰ω_j(x)‖ = ‖ω_j(x)‖ (norm_iteratedFDeriv_zero), and D⁰0 = 0. Hence for every δ > 0 there is j₀ such that ‖ω_j(x)‖ < δ for all j ≥ j₀ and all x ∈ K.
5. (Majorant.) K is compact and K ⊆ V, so θ is H-integrable on M ∩ K (field integrableOn). K is closed, hence Borel; therefore 1_K·θ is H⌞M-integrable (integrable_indicator_iff together with (H⌞M)⌞K = H⌞(K ∩ M), Measure.restrict_restrict) and ∫_M 1_K θ dH = ∫_{M∩K} θ dH =: C (integral_indicator).
6. (Estimate.) Let ε > 0, put δ := ε/(|C| + 1) > 0, and let j ≥ j₀ with j₀ from step 4 for this δ. For every x ∈ G (step 2):
   - if x ∈ K: |F_{ω_j}(x)| = θ(x)·|ξ(x)(ω_j(x))| ≤ θ(x)·‖ω_j(x)‖ ≤ δ·θ(x) = δ·1_K(x)θ(x), using θ(x) > 0, step 2 and step 4;
   - if x ∉ K: x ∉ tsupport ω_j (as tsupport ω_j ⊆ K), so ω_j(x) = 0 and F_{ω_j}(x) = θ(x)·ξ(x)(0) = 0 = δ·1_K(x)θ(x).
   Thus |F_{ω_j}| ≤ δ·1_Kθ holds H⌞M-a.e. The right side is H⌞M-integrable (step 5), so |L(ω_j)| = |∫_M F_{ω_j} dH| ≤ ∫_M δ·1_Kθ dH = δ·C ≤ δ·|C| < ε (norm_integral_le_of_norm_le; the last inequality is ε|C| < ε(|C| + 1)).
7. (Continuity.) Step 6 shows L(ω_j) → 0 for every sequence ω_j → 0 in Dⁿ(V). This is exactly the continuity field continuous' of GeometricCurrentOn V n.
8. (Conclusion.) X := ⟨L, step 7⟩ ∈ Dₙ(V), and X(ω) = L(ω) = tauAction n M θ ξ ω for every ω ∈ Dⁿ(V), by definition of L. ∎

Formalization notes. The current is built as ⟨{ toFun := fun ω => tauAction n M θ ξ ω, map_add', map_smul' }, continuous'⟩. Lemmas used: integral_add, integral_const_mul, integral_congr_ae, Metric.tendstoUniformlyOn_iff, norm_iteratedFDeriv_zero, integrable_indicator_iff, integral_indicator, Measure.restrict_restrict, ae_restrict_mem₀, image_eq_zero_of_notMem_tsupport, norm_integral_le_of_norm_le, Metric.tendsto_nhds. The Lean proof below was kernel-checked in a scratch build of the frozen commit d8d46c9 (pinned toolchain and packages), first with the two sibling declarations as stubs of their exact frozen types and then with their real accepted proofs (candidate commits 1d327e46, 27af9b19); #print axioms = [propext, Classical.choice, Quot.sound].

Appendix (formalization aid; kernel-checked Lean proof of exactly the frozen type, in the contract scope `namespace GMT.Ch06` with the contract's `open`s):

theorem Submission.br_loc_tauAction_current : ∀ (P n : ℕ) (V M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n), IsRectifiableTriple V n M θ ξ → ∃ X : GeometricCurrentOn V n, ∀ ω : TestFormOn V n, X ω = tauAction n M θ ξ ω := by
  intro P n V M θ ξ hTr
  have hint : ∀ ω : TestFormOn V n, IntegrableOn
      (fun x => θ x * ξ x ((ω : DifferentialForm (Eucl P) n) x)) M (μHE[n] : Measure (Eucl P)) :=
    fun ω => (Submission.ltg_tau_integrable P n V M θ ξ hTr).2 _
      ω.property.1.1.continuous ω.property.1.2 ω.property.2
  have hub : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) n, |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hTr.orients] with x hx
    obtain ⟨τ, hτ, -, hξ⟩ := hx
    exact Submission.fiw_ims_tt_unit_bound P n τ (ξ x) hτ hξ
  let L : CurrentOn V n :=
    { toFun := fun ω => tauAction n M θ ξ ω
      map_add' := by
        intro ω η
        simp only [tauAction]
        rw [← integral_add (hint ω) (hint η)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add]
      map_smul' := by
        intro c ω
        simp only [tauAction, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  intro ωs hconv
  obtain ⟨K, hK, hKV, hsupp, -, hderiv⟩ := hconv
  have hIK : IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P)) :=
    hTr.integrableOn K hK hKV
  set C : ℝ := ∫ x in M ∩ K, θ x ∂(μHE[n] : Measure (Eucl P)) with hC
  have hgint : Integrable (K.indicator θ) ((μHE[n] : Measure (Eucl P)).restrict M) := by
    rw [integrable_indicator_iff hK.measurableSet, IntegrableOn,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact hIK
  have hgC : ∫ x, K.indicator θ x ∂((μHE[n] : Measure (Eucl P)).restrict M) = C := by
    rw [integral_indicator hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_comm]
  -- uniform smallness of the forms on `K`
  have hsmall : ∀ δ > 0, ∀ᶠ j in atTop, ∀ x ∈ K,
      ‖(ωs j : DifferentialForm (Eucl P) n) x‖ < δ := by
    intro δ hδ
    have h0 := (Metric.tendstoUniformlyOn_iff.mp (hderiv 0)) δ hδ
    filter_upwards [h0] with j hj x hx
    have := hj x hx
    rw [dist_comm, dist_eq_norm] at this
    simpa [norm_iteratedFDeriv_zero] using this
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (|C| + 1) := by positivity
  filter_upwards [hsmall _ hδ] with j hj
  rw [Real.dist_eq, sub_zero]
  have hbound : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M),
      ‖θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)‖ ≤
        (ε / (|C| + 1)) * K.indicator θ x := by
    filter_upwards [hub, ae_restrict_mem₀ hTr.nullMeasurableSet] with x hx hxM
    have hθ := hTr.pos x hxM
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs, abs_mul, abs_of_pos hθ]
      calc θ x * |ξ x ((ωs j : DifferentialForm (Eucl P) n) x)|
          ≤ θ x * ‖(ωs j : DifferentialForm (Eucl P) n) x‖ :=
            mul_le_mul_of_nonneg_left (hx _) hθ.le
        _ ≤ θ x * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left (hj x hxK).le hθ.le
        _ = ε / (|C| + 1) * θ x := mul_comm _ _
    · have hz : (ωs j : DifferentialForm (Eucl P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      rw [indicator_of_notMem hxK, hz, map_zero, mul_zero, norm_zero, mul_zero]
  have hle := norm_integral_le_of_norm_le (hgint.const_mul (ε / (|C| + 1))) hbound
  rw [integral_const_mul, hgC, Real.norm_eq_abs] at hle
  change |∫ x in M, θ x * ξ x ((ωs j : DifferentialForm (Eucl P) n) x)
    ∂(μHE[n] : Measure (Eucl P))| < ε
  calc _ ≤ ε / (|C| + 1) * C := hle
    _ ≤ ε / (|C| + 1) * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hδ.le
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]

## Key steps

1. For ω ∈ Dⁿ(V), x ↦ θ(x)ξ(x)(ω(x)) is Hⁿ-integrable on M (sibling tau_integrable), so ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ is ℝ-linear.
2. By the orientation condition and the sibling unit_bound, |ξ(x)(α)| ≤ ‖α‖ for Hⁿ⌞M-a.e. x and all α; θ > 0 on M.
3. If ω_j → 0 in Dⁿ(V), all supports lie in one compact K ⊆ V and sup_K ‖ω_j‖ → 0 (order-0 uniform convergence, ‖D⁰ω‖ = ‖ω‖).
4. Hence |τ(ω_j)| ≤ (sup_K ‖ω_j‖)·∫_{M∩K} θ dHⁿ → 0, the integral being finite by the triple's local integrability on the compact K ⊆ V.
5. The linear, sequentially continuous functional τ(M, θ, ξ) is a current X ∈ Dₙ(V) with X(ω) = tauAction n M θ ξ ω.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean with git show d8d46c9:GMT/Ch06/Contract.lean and :GMT/Ch06/Submission.lean (byte-identical)`
- `python3 scan of dag.json: accepted nodes whose statements mention tauAction/massOn/IsRestriction/IsMeasureRepresentation/simpleNVector (iwl_restriction_theory, polyhedral_approx_boundary_mass_cutoff, fiw_im_mass_formula, ltg_tau_integrable, ltg_tau_congr_on_open, br_weightedTangent_congr, fiw_ims_tt_unit_bound, polyhedral_approx_restriction_exists, cmb_abs_apply_le_of_massOn_le, isoperimetric_abs_covector_apply_le, smr_restriction_isCurrent)`
- `python3 lean_name collision scan of dag.json and grep -rl 'br_loc_' nodes/ and the snapshot project (no match)`
- `grep -n '_existing_lean_name_problem|existing_by_name|_accepted_checkpoint|_overlay_accepted_children' /runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py (identical-type reuse of accepted nodes creates no new node; Lean-union overlay of candidate commits)`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz|protected theorem dist_left' mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `rg -n 'theorem setLIntegral_congr_fun|theorem setIntegral_congr_fun₀|theorem norm_integral_le_of_norm_le|theorem ae_restrict_mem₀|theorem restrict_restrict|theorem Integrable.lintegral_lt_top|theorem closure_ball|theorem norm_iteratedFDeriv_zero|theorem tendstoUniformlyOn_iff' mathlib/Mathlib`
- `grep -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|def HasWeightedApproximateTangentSpaceAt' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `inspect simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,FormsDuality}.lean (GeometricCurrentOn, TestFormOnConverges, massOn, le_massOn, restrictDomain_apply, testFormOnInclusion_coe, NVector = Covector →L[ℝ] ℝ)`
- `grep -rn 'def .*: GeometricCurrentOn|: GeometricCurrentOn .* where|tauAction' simongmt/Poincare/SimonGMT (only point currents, products and the distribution equivalence; no constructor of τ(M,θ,ξ) as a current)`
- `python3 lean_contract.validate_lean_statement on the 9 child statements and the parent (unchanged)`
- `python3 gmt-compare.py contract_scope/child_modules (contract mode) -> Scratch/AllChallenges.lean (pristine Submission) and Scratch/AllSolutions.lean (stub Submission): 0 errors`
- `lake build GMT.Ch06.Submission Scratch.Stubs; lake env lean Scratch/Assembly.lean, Scratch/TrialN1.lean, Scratch/TrialN2.lean (0 errors; sorryAx only from child stubs)`
- `git show b9f9acdc 220d968d 83e1f618 1d327e46 bf2b2765 def607d8 27af9b19 :GMT/Ch06/Submission.lean -> Scratch/FullChain.lean; lake env lean (0 errors; #print axioms = [propext, Classical.choice, Quot.sound])`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/RCLike/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-theory-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-truncation-sequence-a1-boundary-mass-cutoff-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-mass-formula-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-congr-on-open-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-tangent-locality-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-patching-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py`
- `/tmp/loc_decomp/proj/Scratch/Stubs.lean`
- `/tmp/loc_decomp/proj/Scratch/Assembly.lean`
- `/tmp/loc_decomp/proj/Scratch/TrialN1.lean`
- `/tmp/loc_decomp/proj/Scratch/TrialN2.lean`
- `/tmp/loc_decomp/proj/Scratch/AllChallenges.lean`
- `/tmp/loc_decomp/proj/Scratch/AllSolutions.lean`
- `/tmp/loc_decomp/proj/Scratch/FullChain.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission.lean is byte-identical to it. Mathlib supplies every analytic step of the assembly and of the two new children: LipschitzWith.dist_left, norm_fderiv_le_of_lipschitz, closure_ball, setLIntegral_congr_fun, setIntegral_congr_fun₀, Measure.restrict_restrict, ae_restrict_mem₀, Integrable.lintegral_lt_top, norm_integral_le_of_norm_le, norm_iteratedFDeriv_zero and Metric.tendstoUniformlyOn_iff. SimonGMT supplies CountablyRectifiable.mono, GeometricCurrentOn.le_massOn, restrictDomain_apply and testFormOnInclusion_coe. No Mathlib or SimonGMT declaration states that τ(M,θ,ξ) is a current or that a triple restricts to an open set; these are the two new children. Seven accepted DAG declarations already cover the restriction theory, the boundary-mass cut-off, the mass identity, τ-integrability, τ-locality, tangent locality and the unit bound; they are reused with byte-identical types. In the scratch build of the frozen commit: all statements validate and elaborate in the comparator scope; the parent's exact type is proved from the nine child types; and the full chain built from the real accepted proofs plus the trial proofs has axioms [propext, Classical.choice, Quot.sound].


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
