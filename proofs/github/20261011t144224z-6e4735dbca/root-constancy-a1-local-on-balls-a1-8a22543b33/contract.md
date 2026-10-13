<!-- theorem-id: gmt-ch06/root.constancy-a1.local_on_balls-a1 -->

## Theorem `Submission.constancy_local_on_balls`

Let m ∈ ℕ, n = m + 1, U ⊆ ℝⁿ open and T ∈ D_n(U), and assume T(ω) = 0 whenever ω ∈ Dⁿ(U) satisfies ω(x)(e_1,…,e_n) = D_j a(x) for all x ∈ ℝⁿ, for some j ∈ {1,…,n} and some C^∞ compactly supported a : ℝⁿ → ℝ with spt a ⊆ U. Then for every x₀ ∈ U there are r > 0 with B_r(x₀) ⊆ U and c ∈ ℝ such that T(ω) = c ∫ ω(x)(e_1,…,e_n) dLⁿ(x) for every ω ∈ Dⁿ(U) with spt ω ⊆ B_r(x₀).

Node: `root.constancy-a1.local_on_balls-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/316

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/965, https://github.com/ZhengyangZhang06/gmt-formalize/issues/966, https://github.com/ZhengyangZhang06/gmt-formalize/issues/967

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2564, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2582, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2595, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2604

## Lean problem

Declaration: `Submission.constancy_local_on_balls`

```lean
∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ (a : Eucl (m + 1) → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ U → ∀ (j : Fin (m + 1)) (ω : TestFormOn U (m + 1)), (∀ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ))) → T ω = 0) → ∀ x₀ ∈ U, ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) ⊆ ball x₀ r → T ω = c * ∫ x, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume
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

- Parent DAG node: `root.constancy-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, Theorem 2.34 and its printed proof (p. 142–143), the part ending with “T = c_{ρ,x₀}[[B_ρ(x₀)]] (c_{ρ,x₀} constant) on each ball B_ρ(x₀) with B̄_ρ(x₀) ⊂ U”; this is Steps 1, 3, 4 and 5 of the parent proof, with the conclusion of its Step 2 (u(D_j a) = 0, i.e. T(dω_j) = ∂T(ω_j) = 0) taken as the hypothesis (H). As in the printed proof, the ball B_ρ(x₀) is fixed, R > ρ with B_R(x₀) ⊂ U, and the mollification parameter satisfies ε < R − ρ. Book n = m + 1. Erratum applied: the printed display (1) is garbled; it must read T(a_ε dx¹∧⋯∧dxⁿ) = ∫ a θ_ε dLⁿ for a ∈ L¹(B_ρ(x₀)) (the left side involves the mollified function a_ε = ϕ_ε ∗ a, as the preceding sentence of the printed proof defines F(a) = T(a_ε dx¹∧⋯∧dxⁿ)).

Setting and notation. m ∈ ℕ, n := m + 1, U ⊆ ℝⁿ open, T ∈ D_n(U) (Lean: GeometricCurrentOn U (m+1)). e = (e_1,…,e_n) is the standard basis (Lean: e_i = EuclideanSpace.single i 1), Lⁿ = Lebesgue measure (Lean: volume), D_j a(x) := Da(x)(e_j) (Lean: fderiv ℝ a x (EuclideanSpace.single j 1)), D^q the q-th derivative (Lean: iteratedFDeriv ℝ q), B_s(x) the open ball, B̄_s(x) the closed ball, “spt” the topological support (closure of {≠ 0}; Lean: tsupport). C_c^∞ denotes C^∞ functions ℝⁿ → ℝ with compact support, C¹_c the C¹ functions with compact support. f ∗ g denotes the convolution (f ∗ g)(x) = ∫ f(t) g(x − t) dt (Lean: convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) volume). Hypothesis:
(H) T(ω) = 0 whenever ω ∈ Dⁿ(U), a ∈ C_c^∞ with spt a ⊆ U, j ∈ {1,…,n}, and ω(x)(e) = D_j a(x) for all x ∈ ℝⁿ.
Claim: for every x₀ ∈ U there are r > 0 with B_r(x₀) ⊆ U and c ∈ ℝ such that T(ω) = c ∫ ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U) with spt ω ⊆ B_r(x₀).
Sibling lemmas used: constancy_riesz_l1_dual_bounded_density (Riesz representation (L¹)* = L^∞ for a finite measure), constancy_mollifier_iteratedFDeriv_norm_le_integral (for φ ∈ C_c^∞ and each q there is C_q with |D^q(φ ∗ g)(x)| ≤ C_q ∫|g| for all integrable g and all x), constancy_approx_identity_iteratedFDeriv_tendstoUniformly (for b ∈ C_c^∞ and continuous ψ_k ≥ 0 with ∫ψ_k = 1, spt ψ_k ⊆ B̄_{r_k}(0), r_k → 0: D^q(ψ_k ∗ b) → D^q b uniformly on ℝⁿ for each q).

Proof.

0. (Radii.) Fix x₀ ∈ U. U is open, so B_{R₀}(x₀) ⊆ U for some R₀ > 0. Put R := R₀/2 and ρ := r := R/2. Then K := B̄_R(x₀) ⊆ B_{R₀}(x₀) ⊆ U is compact, r > 0, and B := B_ρ(x₀) = B_r(x₀) ⊆ U. For 0 < ε < R − ρ = R/2 we have ρ + ε < R.

1. (Reduction to a distribution — parent Step 1.)
 (1a) Let dx := dx¹∧⋯∧dxⁿ be the n-covector v ↦ det[v_1 … v_n] (Lean: the continuous alternating map whose underlying alternating map is (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det; continuity: the determinant of the coordinate matrix depends continuously on v, `Continuous.matrix_det`). dx(e) = 1 (`Module.Basis.det_self`), and every α ∈ Λⁿ(ℝⁿ) equals α(e)·dx, because the alternating n-linear forms on an n-dimensional space are the multiples of the determinant (`AlternatingMap.eq_smul_basis_det`).
 (1b) For a ∈ C_c^∞ with spt a ⊆ U let [a] := a·dx, the form x ↦ a(x)·dx; it is C^∞, spt [a] ⊆ spt a, so [a] ∈ Dⁿ(U), and [a](x)(e) = a(x). Put u(a) := T([a]). Since [a + b] = [a] + [b] and [ca] = c[a], u is linear.
 (1c) For ω ∈ Dⁿ(U) put a_ω(x) := ω(x)(e). Then a_ω is C^∞ (ω composed with the continuous linear evaluation at e), spt a_ω ⊆ spt ω (compact, ⊆ U), and ω = [a_ω] by (1a). Hence T(ω) = u(a_ω).
 (1d) (Derivatives of [a].) D^q[a](x) is the image of D^q a(x) under the fixed continuous linear map t ↦ t·dx (`ContinuousLinearMap.iteratedFDeriv_comp_left`), so ‖D^q[a](x)‖ ≤ ‖dx‖·‖D^q a(x)‖ and D^q[a_k] → D^q[a] uniformly whenever D^q a_k → D^q a uniformly.
 (1e) (Continuity of u.) If a_k, a ∈ C_c^∞ have spt ⊆ K' for one compact K' ⊆ U and D^q a_k → D^q a uniformly on ℝⁿ for every q ∈ ℕ, then u(a_k) → u(a): by (1d), [a_k − a] → 0 in the sense of `TestFormOnConverges` (all supports in K', every derivative uniformly), and the continuity axiom of T (`GeometricCurrentOn.continuous'`) gives u(a_k) − u(a) = T([a_k − a]) → 0.
 (1f) (Hypothesis (H) in terms of u.) If a ∈ C_c^∞ with spt a ⊆ U and j ∈ {1,…,n}, then D_j a ∈ C_c^∞, spt D_j a ⊆ spt a ⊆ U, and [D_j a](x)(e) = D_j a(x); so (H) gives u(D_j a) = T([D_j a]) = 0. [This is the printed identity T(dω_j) = ∂T(ω_j) = 0, encoded in (H).]
 (1g) It therefore suffices to find c with u(b) = c ∫ b dLⁿ for every b ∈ C_c^∞ with spt b ⊆ B: then for ω ∈ Dⁿ(U) with spt ω ⊆ B = B_r(x₀), a_ω ∈ C_c^∞ with spt a_ω ⊆ B, and T(ω) = u(a_ω) = c ∫ a_ω dLⁿ = c ∫ ω(x)(e) dLⁿ(x).

2. (Mollifiers, as in §2 of Ch. 2.) For ε > 0 let ϕ_ε ∈ C_c^∞ with ϕ_ε ≥ 0, ϕ_ε(−x) = ϕ_ε(x), ∫ ϕ_ε dLⁿ = 1 and spt ϕ_ε = B̄_ε(0) (e.g. ϕ_ε(x) = ε^{−n}ϕ(x/ε) for a fixed mollifier ϕ; Lean: the normalized `ContDiffBump` centred at 0 with rIn = ε/2, rOut = ε, from Mathlib.Analysis.Calculus.BumpFunction.Normed: `contDiff_normed`, `continuous_normed`, `nonneg_normed`, `normed_neg`, `integral_normed`, `tsupport_normed_eq`). For g ∈ L¹(ℝⁿ) let g_ε := ϕ_ε ∗ g. Facts:
 (M1) g_ε ∈ C^∞ (`HasCompactSupport.contDiff_convolution_left`, differentiation under the integral sign).
 (M2) If g = 0 outside a set S, then g_ε = 0 outside S + B̄_ε(0) (`MeasureTheory.support_convolution_subset`).
 (M3) For each q there is C_q(ε) ≥ 0 with |D^q g_ε(x)| ≤ C_q(ε) ∫|g| dLⁿ for all x and all g ∈ L¹(ℝⁿ) — sibling lemma constancy_mollifier_iteratedFDeriv_norm_le_integral with φ = ϕ_ε (replace C_q by max(C_q, 0)).
 (M4) If g ∈ C¹_c then D_j(g_ε) = (D_j g)_ε (the derivative falls on g: `HasCompactSupport.hasFDerivAt_convolution_right`, evaluated at e_j).
 (M5) If g ∈ C_c^∞ and ε_k ↓ 0 then D^q(g_{ε_k}) → D^q g uniformly on ℝⁿ for every q — sibling lemma constancy_approx_identity_iteratedFDeriv_tendstoUniformly with ψ_k = ϕ_{ε_k}, r_k = ε_k.

3. (Printed display (1), corrected.) Fix ε with 0 < ε < R/2. For a function a integrable on B put ã := 1_B·a ∈ L¹(ℝⁿ) (a extended by zero). By (M1), (M2), ã_ε ∈ C^∞ and ã_ε = 0 outside B + B̄_ε(0) ⊆ B_{ρ+ε}(x₀), so spt ã_ε ⊆ B̄_{ρ+ε}(x₀) ⊆ K ⊆ U and ã_ε ∈ C_c^∞. Define F(a) := u(ã_ε) for a integrable on B (and F(a) := 0 otherwise; these values play no role). Since a ↦ ã ↦ ã_ε and u are linear, F(a + b) = F(a) + F(b) and F(c a) = c F(a) for a, b integrable on B and c ∈ ℝ.
 F is bounded on L¹(B). The printed proof argues: if a_j → a in L¹(B) then, by (M3), every derivative of (ã_j)_ε converges uniformly to that of ã_ε with all supports in K, so T((ã_j)_ε dx) → T(ã_ε dx) by (1e); “thus the functional F is a bounded linear functional on L¹(B_ρ(x₀))”. Explicitly: by the finite-order estimate for currents (SimonGMT `GeometricCurrentOn.exists_compact_derivative_bound`, module Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology, applied to T and the compact K ⊆ U) there are N ∈ ℕ and C₀ > 0 with |T(ω)| ≤ C₀·D whenever ω ∈ Dⁿ(U), spt ω ⊆ K, D ≥ 0 and ‖D^q ω(x)‖ ≤ D for all q ≤ N and x ∈ K. For ω = [ã_ε], (1d) and (M3) give ‖D^q[ã_ε](x)‖ ≤ ‖dx‖·C_q(ε)·∫|ã| = ‖dx‖·C_q(ε)·∫_B|a|, so with C := C₀‖dx‖·max_{q≤N} C_q(ε):
 |F(a)| ≤ C ∫_B |a| dLⁿ for every a integrable on B.
 [Equivalently, without the finite-order estimate: if no such C existed, choose a_k with |F(a_k)| > k²∫_B|a_k|; then ∫_B|a_k| > 0 (otherwise ã_k = 0 a.e., (ã_k)_ε ≡ 0 and F(a_k) = 0) and b_k := a_k/(k∫_B|a_k|) has ∫_B|b_k| = 1/k → 0 but |F(b_k)| > k, contradicting the sequential continuity just shown.]
 Now apply the Riesz representation theorem for L¹(B_ρ(x₀)), i.e. the sibling lemma constancy_riesz_l1_dual_bounded_density, with the finite measure μ := Lⁿ⌞B (Lean: volume.restrict (ball x₀ ρ), finite by `measure_ball_lt_top`; “μ-integrable” = “integrable on B”) and this F and C. It yields a measurable θ_ε : ℝⁿ → ℝ, bounded by some M everywhere, with
 (1) u(ã_ε) = F(a) = ∫_B a θ_ε dLⁿ for every a integrable on B.
 This is the corrected printed display (1).

4. (Printed display (2); θ_ε is constant.) Let a ∈ C¹_c with spt a ⊆ B and j ∈ {1,…,n}. Then ã = a; D_j a is continuous with spt D_j a ⊆ spt a ⊆ B, hence integrable on B with (D_j a)~ = D_j a; a_ε ∈ C_c^∞ with spt a_ε ⊆ K ⊆ U (Step 3); and (D_j a)_ε = D_j(a_ε) by (M4). Using (1) for D_j a and (1f) for the C_c^∞ function a_ε:
 (2) ∫_B (D_j a) θ_ε dLⁿ = u((D_j a)_ε) = u(D_j(a_ε)) = 0, j = 1,…,n.
 [In the printed notation: with ω_j = (−1)^{j−1} a_ε dx¹∧⋯∧dx^{j−1}∧dx^{j+1}∧⋯∧dxⁿ one has dω_j = (D_j a)_ε dx, and (2) reads T(dω_j) = ∂T(ω_j) = 0.]
 Thus the bounded measurable (hence locally integrable on B) function θ_ε has vanishing weak partial derivatives in the ball B, tested against all C¹_c functions supported in B. As in the printed proof, θ_ε is Lⁿ-a.e. constant on B: for 0 < σ < ρ and x ∈ B_{ρ−σ}(x₀), the function y ↦ ϕ_σ(x − y) is C_c^∞ with spt ⊆ B̄_σ(x) ⊆ B and D_{y_j}[ϕ_σ(x − y)] = −(D_jϕ_σ)(x − y); so with θ̃_ε := 1_B θ_ε, differentiation under the integral sign and (2) give D_j(ϕ_σ ∗ θ̃_ε)(x) = ∫ (D_jϕ_σ)(x − y) θ_ε(y) dy = −∫_B D_j[ϕ_σ(x − ·)] θ_ε dLⁿ = 0. Hence the C^∞ function ϕ_σ ∗ θ̃_ε has zero derivative on the convex open ball B_{ρ−σ}(x₀) and is constant there, say = k_σ (`IsOpen.is_const_of_fderiv_eq_zero`). As σ ↓ 0 along a sequence, ϕ_σ ∗ θ̃_ε → θ̃_ε Lⁿ-a.e. (Lebesgue differentiation theorem for the approximate identity ϕ_σ; `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`). Pick x₁ ∈ B where this convergence holds (possible since Lⁿ(B) > 0); for small σ, x₁ ∈ B_{ρ−σ}(x₀), so k_σ = (ϕ_σ ∗ θ̃_ε)(x₁) → θ_ε(x₁) =: c_ε. Every x ∈ B lies in B_{ρ−σ}(x₀) for small σ, so θ_ε(x) = lim k_σ = c_ε for a.e. x ∈ B. Hence θ_ε = c_ε Lⁿ-a.e. on B. [This exact argument is available, kernel-checked with the standard axioms only, as `Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero` (module Poincare.SimonGMT.Chapter08.DistributionalConstancy). Its hypotheses are: θ_ε locally integrable on B, B open and preconnected (convex), and ∫ θ_ε(x)·Da(x)(e_j) dx = 0 for every C¹ compactly supported a with spt a ⊆ B and every j. This is (2), because D_j a vanishes outside B so the whole-space integral equals the integral over B.]
 Consequently, by (1): u(ã_ε) = c_ε ∫_B a dLⁿ for every a integrable on B.

5. (Letting ε ↓ 0.) Let ε_k := R/(k + 3), so 0 < ε_k < R/2 and ε_k → 0, and let c_k := c_{ε_k} be the constant of Step 4 for ε = ε_k.
 Let b ∈ C_c^∞ with spt b ⊆ B. Then b is integrable on B, b̃ = b and ∫_B b = ∫ b, so Step 4 gives u(b_{ε_k}) = c_k ∫ b dLⁿ. By Step 3, spt b_{ε_k} ⊆ K for all k, and by (M5) every derivative of b_{ε_k} converges uniformly to the corresponding derivative of b. By (1e), u(b_{ε_k}) → u(b).
 Fix b₀ ∈ C_c^∞ with spt b₀ ⊆ B and ∫ b₀ dLⁿ = 1 (e.g. the normalized `ContDiffBump` centred at x₀ with outer radius r/2). Then c_k = c_k ∫ b₀ = u((b₀)_{ε_k}) → u(b₀) =: c. Hence for every b ∈ C_c^∞ with spt b ⊆ B: u(b) = lim_k u(b_{ε_k}) = lim_k c_k ∫ b = c ∫ b dLⁿ.

6. (Conclusion.) By (1g), T(ω) = c ∫ ω(x)(e) dLⁿ(x) for every ω ∈ Dⁿ(U) with spt ω ⊆ B_r(x₀), where r > 0 and B_r(x₀) ⊆ U (Step 0). This is the printed conclusion “T = c_{ρ,x₀}[[B_ρ(x₀)]] on each ball B_ρ(x₀)” for ρ = r. ∎

Formalization note: besides `GMT.Ch06.Submission`, a Lean proof of this statement may import `Mathlib.Analysis.Calculus.BumpFunction.Normed`, `Mathlib.Analysis.Calculus.ContDiff.Convolution`, `Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology` and `Poincare.SimonGMT.Chapter08.DistributionalConstancy` (all in the pinned packages; the cited SimonGMT lemmas use only propext, Classical.choice, Quot.sound).

## Key steps

1. Fix x₀, R with B̄_R(x₀) ⊆ U and the ball B = B_ρ(x₀), ρ = r = R/2; write ω = a_ω dx and set u(a) := T(a dx), a continuous linear functional on C_c^∞(U) with u(D_j a) = 0 by the hypothesis.
2. For 0 < ε < R/2, F(a) := u(ϕ_ε ∗ (1_B a)) is linear and bounded on L¹(B) (finite-order estimate for T plus the mollifier derivative bound).
3. The sibling Riesz lemma gives a bounded measurable θ_ε with u((1_B a)_ε) = ∫_B a θ_ε (corrected printed display (1)).
4. For a ∈ C¹_c(B): ∫_B (D_j a)θ_ε = u(D_j(a_ε)) = 0 (printed (2)); hence θ_ε = c_ε a.e. on B (mollification argument = SimonGMT ae_eq_const_of_weak_coordinate_derivatives_zero).
5. Along ε_k = R/(k+3) ↓ 0: u(b_{ε_k}) = c_k∫b and b_{ε_k} → b in the test-function sense (sibling convergence lemma), so c_k → c := u(b₀) and u(b) = c∫b for spt b ⊆ B.
6. T(ω) = u(a_ω) = c∫ω(x)(e)dLⁿ for every ω with spt ω ⊆ B_r(x₀).

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean and vs project/GMT/Ch06/Submission.lean (byte-identical)`
- `grep -n 'ConstancyTheorem' -A 25 GMT/Ch06/Contract.lean`
- `rg -n 'theorem AlternatingMap.eq_smul_basis_det|theorem det_self' mathlib/Mathlib/LinearAlgebra`
- `rg -n 'theorem extDeriv_apply' mathlib/Mathlib/Analysis/Calculus/DifferentialForm/`
- `rg -n 'curryLeft|removeNth' mathlib/Mathlib/Analysis/Normed/Module/Alternating/ ; rg -n 'theorem sign_cycleRange|cons_removeNth' mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `rg -n 'L1.*[Dd]ual|[Dd]ual.*L1|LpDual|Lp.dual|toDual|dualLp|Linfty' mathlib/Mathlib/MeasureTheory -l ; rg -n 'StrongDual|Dual' mathlib/Mathlib/MeasureTheory/Function/Holder.lean`
- `rg -n 'contDiff_convolution|hasFDerivAt_convolution|fderiv_convolution' mathlib/Mathlib/Analysis/ (first derivatives only; no iteratedFDeriv-of-convolution lemma)`
- `rg -n 'ae_convolution_tendsto_right_of_locallyIntegrable|integral_normed|tsupport_normed_eq|normed_neg|nonneg_normed|contDiff_normed' mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n 'withDensityᵥ_rnDeriv_eq|def rnDeriv|integrable_rnDeriv' mathlib/Mathlib/MeasureTheory/Measure/Decomposition/ mathlib/Mathlib/MeasureTheory/VectorMeasure/`
- `rg -n 'theorem exists_isSubordinate' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `rg -n 'is_const_of_fderiv|IsPreconnected.constant|setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/Analysis/Calculus/MeanValue.lean mathlib/Mathlib/Topology/Connected/ mathlib/Mathlib/MeasureTheory/Integral/`
- `rg -n 'dist_convolution_le|norm_iteratedFDeriv_fderiv|iteratedFDeriv_succ_eq_comp_left|def precompL|norm_precompL_le' mathlib/Mathlib/Analysis`
- `rg -n -i 'constancy|mollif' simongmt/Poincare/SimonGMT ; rg -n '^theorem|^def' simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean simongmt/Poincare/SimonGMT/Chapter01/FiniteL1Dual.lean`
- `#print axioms Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero ; #print axioms Poincare.SimonGMT.Chapter06.GeometricCurrentOn.exists_compact_derivative_bound`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the 6 child statements`
- `verifier/gmt-compare.py contract_scope + child_modules: generate and compile NodeChallenge/NodeSolution for all 6 children against stub Submission.<lean_name> (scratch /tmp/constancy_decomp_check, frozen commit d8d46c9, pinned packages)`
- `lean Scratch/ParentFromChildren.lean and Scratch/C2Usage.lean (parent assembly vs ConstancyTheorem; instantiation of the Riesz, bound and convergence siblings, normalized bumps, SimonGMT weak constancy)`
- `lean Scratch/ExtDerivCheck.lean, Scratch/DetForm.lean, Scratch/Review_C1.lean, Scratch/Review2_M1.lean, Scratch/Review2_M2.lean, Scratch/Review_API.lean (#print axioms)`
- `python3 listing of dag.json lean_name values (50 nodes; none equal to the 6 proposed names)`
- `grep -n 'Constancy' book/chapter-06.txt (printed proof of 2.34, p. 142-143)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/GroupTheory/Perm/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Holder.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/VectorMeasure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Bilinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Connected/TotallyDisconnected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FixedSupportCurrentTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentDistributionEquivalence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/FiniteL1Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/tmp/constancy_decomp_check/Scratch/ParentFromChildren.lean`
- `/tmp/constancy_decomp_check/Scratch/C2Usage.lean`
- `/tmp/constancy_decomp_check/Scratch/ExtDerivCheck.lean`
- `/tmp/constancy_decomp_check/Scratch/Review_C1.lean`
- `/tmp/constancy_decomp_check/Scratch/Review2_M1.lean`
- `/tmp/constancy_decomp_check/Scratch/Review2_M2.lean`
- `/tmp/constancy_decomp_check/Scratch/Review_API.lean`

Snapshot context: project d8d46c95 with Mathlib 25730c7c. The frozen Contract and Submission are byte-identical. `ConstancyTheorem` quantifies over `GeometricCurrentOn U (m+1)`, which consists of linear functionals on C^∞ (not analytic) compactly supported `TestFormOn` that are sequentially continuous in the `TestFormOnConverges` sense.

What Mathlib provides: `AlternatingMap.eq_smul_basis_det` (top-degree forms are multiples of det), `extDeriv_apply`, `ContinuousAlternatingMap.curryLeft`, `Fin.cons_removeNth_eq_comp_cycleRange_symm` and `Fin.sign_cycleRange`. These give C1's identity d(a·ι_{e_j}dx)(e) = D_j a, which was kernel-checked. Mathlib also has first-derivative convolution lemmas (`HasCompactSupport.hasFDerivAt_convolution_left/right`, `contDiff_convolution_left`), normalized bumps (`ContDiffBump.normed`), Lebesgue-differentiation a.e. convergence (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`), `dist_convolution_le`, signed Radon–Nikodym (`SignedMeasure.withDensityᵥ_rnDeriv_eq`), `SmoothPartitionOfUnity.exists_isSubordinate` and `IsLocallyConstant.exists_eq_const`.

What Mathlib lacks: no iterated-derivative-of-convolution lemma, and no (L¹)* = L^∞ theorem (Holder.lean only has the pairing map). These motivate the three analytic siblings.

Reusable SimonGMT lemmas, all with only propext, Classical.choice and Quot.sound: `ae_eq_const_of_weak_coordinate_derivatives_zero` (Chapter08/DistributionalConstancy.lean: zero weak gradient with C¹ tests implies a.e. constant), `GeometricCurrentOn.exists_compact_derivative_bound` (the finite-order estimate) and `finiteL1DualField` (Chapter01/FiniteL1Dual.lean, an alternative route for the Riesz lemma).

Statement checks: all six child statements pass the comparator validator and compile as generated NodeChallenge/NodeSolution modules in the exact contract scope. `ContDiffBump.normed` is not importable through the frozen Submission, which is why it is avoided in the frozen statements. The parent assembly typechecks against `ConstancyTheorem`. Full proofs of C1, M1 and M2 compile against the verbatim statements with standard axioms.

Names: none of the six names collides with the 50 DAG nodes.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
