<!-- theorem-id: gmt-ch06/root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_constancy_ball-a1 -->

## Theorem `Submission.constancy_mdc_ae_const_of_weak_partials_vanish`

Let n ∈ ℕ, let θ : ℝⁿ → ℝ be locally Lⁿ-integrable, x₀ ∈ ℝⁿ and ρ > 0. Assume ∫_{ℝⁿ} θ(x) D_j a(x) dLⁿ(x) = 0 for every C^∞ compactly supported a : ℝⁿ → ℝ with spt a ⊆ B_ρ(x₀) and every j ∈ {1,…,n}. Here D_j a(x) := Da(x)(e_j), e_j = EuclideanSpace.single j 1 is the j-th standard basis vector, and spt a is the closed support, the closure of {a ≠ 0} (Lean: tsupport a). Then there is c ∈ ℝ with θ(x) = c for Lⁿ-a.e. x ∈ B_ρ(x₀).

Node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_constancy_ball-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2595

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3577

Decomposition children: None

## Lean problem

Declaration: `Submission.constancy_mdc_ae_const_of_weak_partials_vanish`

```lean
∀ (n : ℕ) (θ : Eucl n → ℝ), LocallyIntegrable θ volume → ∀ (x₀ : Eucl n) (ρ : ℝ), 0 < ρ → (∀ a : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → tsupport a ⊆ ball x₀ ρ → ∀ j : Fin n, ∫ x, θ x * fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ)) ∂volume = 0) → ∃ c : ℝ, ∀ᵐ x ∂volume.restrict (ball x₀ ρ), θ x = c
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

- Parent DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1`
- Child DAG node: `root.constancy-a1.local_on_balls-a1.density_constancy-a1.weak_constancy_ball-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon, Introduction to Geometric Measure Theory, Ch. 6, Theorem 2.34, printed proof p. 143: “If σ < … and x ∈ B_{ρ−σ}(x₀), then ϕ_(σ)(x − ·) is a C_c^∞(B_ρ(x₀)) function and hence a legitimate choice for a in (2), so in fact (2) says D_j((θ_ε)_(σ)) = 0 on B_{ρ−σ}(x₀), hence (θ_ε)_(σ) is constant on B_{ρ−σ}(x₀), hence (letting σ ↓ 0) θ_ε is constant c on B_ρ(x₀).” Some symbols are lost in the text extraction; this reading follows the bracket of Step 5 of the parent proof. Correspondences:
- the locally integrable θ plays the role of θ_ε, and the hypothesis is (2);
- the mollifiers ϕ_(σ), σ = 1/(k+1), and the limit σ ↓ 0 come from the sibling theorem smooth_approx_identity.
We mollify θ itself rather than 1_B θ. On B_{ρ−σ}(x₀) the two mollifications coincide, and since θ is locally integrable on all of ℝⁿ, θ ∗ ψ_k is defined everywhere.

Notation. ℝⁿ = Eucl n; Lⁿ = Lebesgue measure (volume); |·| = Euclidean norm; B_s(x) = ball x s, B̄_s(x) = closedBall x s; spt = tsupport; e_j = EuclideanSpace.single j 1; (θ ∗ ψ)(x) = ∫ θ(t) ψ(x − t) dLⁿ(t) = convolution θ ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume x.

Proof.

1. (Mollifiers.) By the sibling theorem smooth_approx_identity (constancy_mdc_smooth_approx_identity_ae_tendsto) there are ψ_k : ℝⁿ → ℝ (k ∈ ℕ), each C^∞ with compact support and spt ψ_k ⊆ B̄_{r_k}(0), where r_k := 1/(k+1). Since θ is locally integrable, θ_k(x) := (θ ∗ ψ_k)(x) = ∫ θ(t) ψ_k(x − t) dt → θ(x) for Lⁿ-a.e. x. (The other two properties, ψ_k ≥ 0 and ∫ψ_k = 1, are not needed.)

2. (Smoothness and derivative of θ_k.) ψ_k is C^∞, in particular C¹, with compact support, and θ is locally integrable. Hence θ_k is C^∞, in particular differentiable everywhere. Differentiating under the integral sign gives Dθ_k(x) = ∫ θ(t) Dψ_k(x − t) dt. Evaluation at a fixed v commutes with this integral, since Dψ_k is continuous with compact support. So for every x and v ∈ ℝⁿ: Dθ_k(x)(v) = ∫ θ(t) Dψ_k(x − t)(v) dt.

3. (The derivative vanishes where the reflected kernel fits in the ball.) Fix k and x with B̄_{r_k}(x) ⊆ B_ρ(x₀), and let a(t) := ψ_k(x − t).
(a) a is C^∞ (ψ_k composed with the affine map t ↦ x − t), and by the chain rule Da(t) = −Dψ_k(x − t) for every t.
(b) a has compact support: t ↦ x − t is a homeomorphism of ℝⁿ onto itself, so spt a is the image of the compact set spt ψ_k under its inverse.
(c) The closed support of a composition with a continuous map lies in the preimage of the closed support. Hence spt a ⊆ {t : x − t ∈ spt ψ_k} ⊆ {t : |x − t| ≤ r_k} = B̄_{r_k}(x) ⊆ B_ρ(x₀).
So a is an admissible test function. By the hypothesis and Step 2, for every j: 0 = ∫ θ(t) Da(t)(e_j) dt = −∫ θ(t) Dψ_k(x − t)(e_j) dt = −Dθ_k(x)(e_j). Thus the linear map Dθ_k(x) vanishes on the basis e_1,…,e_n of ℝⁿ, so Dθ_k(x) = 0. (For n = 0 there is nothing to check: ℝ⁰ = {0}.)

4. (θ_k is constant on B_{ρ−r_k}(x₀).) Let W_k := B_{ρ−r_k}(x₀); it is empty if ρ ≤ r_k.
- For z ∈ W_k and w ∈ B̄_{r_k}(z): |w − x₀| ≤ |w − z| + |z − x₀| < r_k + (ρ − r_k) = ρ. So B̄_{r_k}(z) ⊆ B_ρ(x₀), and Dθ_k(z) = 0 by Step 3.
- W_k is open and convex, hence preconnected, and θ_k is differentiable on W_k with vanishing derivative. By the mean value theorem, θ_k(x) = θ_k(y) for all x, y ∈ W_k.

5. (A good base point.) Let G be the set of x with θ_k(x) → θ(x) as k → ∞; by Step 1, ℝⁿ ∖ G is Lⁿ-null. Since ρ > 0, Lⁿ(B_ρ(x₀)) > 0, so B_ρ(x₀) ∩ G ≠ ∅. Choose x₁ in it and put c := θ(x₁).

6. (Conclusion.) Let x ∈ B_ρ(x₀) ∩ G.
- Since |x₁ − x₀| < ρ, |x − x₀| < ρ and r_k → 0, there is k₀ with r_k < ρ − |x₁ − x₀| and r_k < ρ − |x − x₀| for all k ≥ k₀. That is, x₁, x ∈ W_k, so θ_k(x) = θ_k(x₁) for all k ≥ k₀ by Step 4.
- Since x₁ ∈ G, θ_k(x₁) → θ(x₁) = c; hence θ_k(x) → c. Since x ∈ G, also θ_k(x) → θ(x). By uniqueness of limits, θ(x) = c.
Because B_ρ(x₀) ∖ G is null, θ(x) = c for Lⁿ-a.e. x ∈ B_ρ(x₀). ∎

Formalization notes (no new mathematics). Every name is available under the frozen `import GMT.Ch06.Submission`; do NOT add any import. With L := ContinuousLinearMap.lsmul ℝ ℝ:
- Step 1: obtain ⟨ψ, hψs, hψc, hψt, -, -, hψlim⟩ := constancy_mdc_smooth_approx_identity_ae_tendsto n.
- Step 2: (hψc k).hasFDerivAt_convolution_right L hθ hψ1 x; convolution_precompR_apply L hθ ((hψc k).fderiv ℝ) (hψ1.continuous_fderiv one_ne_zero); (hψc k).contDiff_convolution_right L hθ (hψs k).
- Step 3: (hψc k).comp_homeomorph (Homeomorph.subLeft x); tsupport_comp_subset_preimage; HasFDerivAt.comp with (hasFDerivAt_id y).const_sub x; ContinuousLinearMap.coe_injective with (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext and EuclideanSpace.basisFun_apply.
- Step 4: IsOpen.is_const_of_fderiv_eq_zero with (convex_ball _ _).isPreconnected.
- Steps 5–6: Measure.exists_mem_of_measure_ne_zero_of_ae with measure_ball_pos; ae_restrict_of_ae; ae_restrict_mem; tendsto_nhds_unique; Tendsto.congr'; tendsto_one_div_add_atTop_nhds_zero_nat.
The following complete single-theorem proof of exactly this frozen type was compiled against the frozen Submission together with the sibling theorem. It needs no new import, produces no warning, and #print axioms gives propext, Classical.choice, Quot.sound. It also passes a simulation of the leaf Git gate. It is a reference implementation; the prose proof above governs.

theorem constancy_mdc_ae_const_of_weak_partials_vanish : <frozen type> := by
  intro n θ hθ x₀ ρ hρ hw
  obtain ⟨ψ, hψs, hψc, hψt, -, -, hψlim⟩ := constancy_mdc_smooth_approx_identity_ae_tendsto n
  have hd : ∀ (k : ℕ) (x : Eucl n), closedBall x (1 / ((k : ℝ) + 1)) ⊆ ball x₀ ρ →
      fderiv ℝ (convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0 := by
    intro k x hx
    have hψ1 : ContDiff ℝ 1 (ψ k) := (hψs k).of_le (by exact_mod_cast le_top)
    let a : Eucl n → ℝ := fun y => ψ k (x - y)
    have ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := (hψs k).comp (contDiff_const.sub contDiff_id)
    have hac : HasCompactSupport a := (hψc k).comp_homeomorph (Homeomorph.subLeft x)
    have has : tsupport a ⊆ ball x₀ ρ := by
      refine (tsupport_comp_subset_preimage (ψ k) (continuous_const.sub continuous_id)).trans ?_
      intro y hy
      apply hx
      have hy' := hψt k hy
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hy'
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      exact hy'
    have hda : ∀ y, fderiv ℝ a y = -(fderiv ℝ (ψ k) (x - y)) := by
      intro y
      have h1 : HasFDerivAt (ψ k) (fderiv ℝ (ψ k) (x - y)) (x - y) :=
        ((hψ1.differentiable one_ne_zero) (x - y)).hasFDerivAt
      have h2 : HasFDerivAt (fun y : Eucl n => x - y) (-ContinuousLinearMap.id ℝ (Eucl n)) y :=
        (hasFDerivAt_id y).const_sub x
      have h3 := h1.comp y h2
      simpa [a, Function.comp_def] using h3.fderiv
    rw [((hψc k).hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hθ hψ1 x).fderiv]
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun j => ?_
    rw [ContinuousLinearMap.coe_coe, convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hθ
      ((hψc k).fderiv ℝ) (hψ1.continuous_fderiv one_ne_zero)]
    have hz := hw a ha hac has j
    simp only [hda, neg_apply, mul_neg, integral_neg, neg_eq_zero] at hz
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, LinearMap.zero_apply,
      ContinuousLinearMap.toLinearMap_zero]
    simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hz
  have hconst : ∀ (k : ℕ) (x y : Eucl n), x ∈ ball x₀ (ρ - 1 / ((k : ℝ) + 1)) →
      y ∈ ball x₀ (ρ - 1 / ((k : ℝ) + 1)) →
      convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
        convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
    intro k x y hx hy
    have hdiff : Differentiable ℝ (convolution θ (ψ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
      ((hψc k).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hθ (hψs k)).differentiable
        (by simp)
    refine isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
      hdiff.differentiableOn ?_ hx hy
    intro z hz
    apply hd k z
    intro w hw'
    rw [mem_ball] at hz ⊢
    rw [mem_closedBall] at hw'
    calc dist w x₀ ≤ dist w z + dist z x₀ := dist_triangle _ _ _
      _ < ρ := by linarith
  have hlim := hψlim θ hθ
  have hpos : volume (ball x₀ ρ) ≠ 0 := (measure_ball_pos volume x₀ hρ).ne'
  obtain ⟨x₁, hx₁, hlim₁⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hlim)
  refine ⟨θ x₁, ?_⟩
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_ball] with x hx hxb
  apply tendsto_nhds_unique hx
  apply hlim₁.congr'
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have e1 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ρ - dist x₁ x₀ :=
    hr.eventually (gt_mem_nhds (by have := mem_ball.mp hx₁; linarith))
  have e2 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ρ - dist x x₀ :=
    hr.eventually (gt_mem_nhds (by have := mem_ball.mp hxb; linarith))
  filter_upwards [e1, e2] with k hk1 hk2
  exact hconst k x₁ x (by rw [mem_ball]; linarith) (by rw [mem_ball]; linarith)

## Key steps

1. Take ψ_k from smooth_approx_identity (C^∞, compact support, spt ψ_k ⊆ B̄_{1/(k+1)}(0)); then θ_k := θ ∗ ψ_k → θ a.e.
2. θ_k is C^∞ and Dθ_k(x)(v) = ∫ θ(t) Dψ_k(x − t)(v) dt (hasFDerivAt_convolution_right, convolution_precompR_apply).
3. If B̄_{1/(k+1)}(x) ⊆ B_ρ(x₀), then a = ψ_k(x − ·) is an admissible test function with Da = −Dψ_k(x − ·); the hypothesis gives Dθ_k(x)(e_j) = 0 for all j, so Dθ_k(x) = 0.
4. θ_k has zero derivative on the convex open ball B_{ρ − 1/(k+1)}(x₀), so it is constant there.
5. Pick x₁ ∈ B_ρ(x₀) with θ_k(x₁) → θ(x₁) =: c (the ball has positive measure).
6. For a.e. x ∈ B_ρ(x₀), θ_k(x) = θ_k(x₁) for all large k, so θ(x) = lim θ_k(x) = c.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (identical); ls project/GMT/Ch06 in the snapshot`
- `rg -n 'theorem ae_tendsto_average_norm_sub|theorem exists_contDiff_tsupport_subset|theorem integral_comp_smul |theorem addHaar_closedBall |theorem _root_.HasCompactSupport.convolutionExists_right|theorem _root_.HasCompactSupport.hasFDerivAt_convolution_right|theorem convolution_precompR_apply|theorem integral_pos_iff_support_of_nonneg|theorem setIntegral_eq_integral_of_forall_compl_eq_zero|theorem exists_mem_of_measure_ne_zero_of_ae|theorem tsupport_fderiv_apply_subset|theorem support_convolution_subset' mathlib/Mathlib`
- `rg -n 'integral_div_left_eq_self|integral_sub_left_eq_self' mathlib/Mathlib/MeasureTheory/Group/Integral.lean; rg -n 'isUnifLocDoublingMeasure' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|ae_convolution_tendsto_right_of_locallyIntegrable|theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero|theorem _root_.IsOpen.is_const_of_fderiv_eq_zero' mathlib/Mathlib`
- `rg -n 'ae_eq_const_of_weak|DistributionalConstancy|constancy_mdc' project (no match)`
- `grep -n 'theorem ae_eq_const_of_weak_coordinate_derivatives_zero' -B5 -A30 simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean; sed -n 1,304p of that file (fderiv_convolution_eq_zero, constancyMollifier via ContDiffBump.normed, ae_constancyMollifier_convolution_tendsto, ae_eq_const_on_ball); grep abbrev Euclidean Chapter08/Varifold.lean`
- `lake env lean #check files after `import GMT.Ch06.Submission` (Check1–Check4.lean): unknown = Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero, ContDiffBump.normed, ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable, ContDiffBump.convolution_tendsto_right, MeasureTheory.ae_eq_zero_of_integral_contDiff_smul_eq_zero, Integrable.exists_hasCompactSupport_integral_sub_le; available = IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (instance for volume on Eucl n infers), VitaliFamily.ae_tendsto_average, exists_contDiff_tsupport_subset, Measure.integral_comp_smul, Measure.addHaar_closedBall, integral_sub_left_eq_self, Integrable.comp_sub_left, HasCompactSupport.convolutionExists_right/contDiff_convolution_left/right/hasFDerivAt_convolution_right, convolution_precompR_apply, IsOpen.is_const_of_fderiv_eq_zero, finrank_euclideanSpace_fin`
- `sed of /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py (check_source_delta), prompts.py (RLCR_LEAN_TASK: preserve imports), runtime.py (_existing_lean_name_problem, reuse); git show cdfc95d (leaf candidate rejected for adding an import)`
- `python3 -I: lean_contract.validate_lean_statement on the 3 child types and the parent type; gmt-compare.contract_scope replay; lake env lean on generated challenge modules ChallengeA/B/C.lean`
- `lake env lean /tmp/dc-split-check/{Compose,ProveAC,ProveB,EndToEnd,EndToEnd2}.lean with #print axioms; python3 -I simulation of check_source_delta on each child insertion into the frozen Submission`
- `python3 -I scan of dag.json lean_name values (453 nodes) for the 3 proposed names (no match)`
- `book sources: chapter-06-source.txt lines 569–600 (2.34 printed proof), chapter-02-source.txt lines 530–545 (mollifier ϕ_σ), chapter-01-source.txt lines 927–935 (Corollary 3.17)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-local-on-balls-a1-density-constancy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/tmp/dc-split-check/ProveAC.lean`
- `/tmp/dc-split-check/ProveB.lean`
- `/tmp/dc-split-check/EndToEnd2.lean`

Snapshot pins project d8d46c95 and Mathlib 25730c7c. The frozen Submission.lean is byte-identical to Contract.lean.

Not available under the frozen `import GMT.Ch06.Submission`:
- the SimonGMT weak-constancy lemma ae_eq_const_of_weak_coordinate_derivatives_zero (DistributionalConstancy.lean:294), which the supplied Step 5 cites;
- ContDiffBump.normed;
- ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (BumpFunction/Convolution.lean:103);
- ae_eq_zero_of_integral_contDiff_smul_eq_zero (AEEqOfIntegralContDiff.lean:186).
The leaf gate forbids adding the import: check_source_delta rejects import, set_option and extra declarations, and commit cdfc95d shows an import-adding leaf rejected.

Available, and enough for an in-closure proof:
- Lebesgue points: IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (DensityTheorem.lean:150), with instance isUnifLocDoublingMeasureOfIsAddHaarMeasure (EqHaar.lean:550);
- exists_contDiff_tsupport_subset (FiniteDimension.lean:45);
- Measure.integral_comp_smul (Haar/NormedSpace.lean:92) and Measure.addHaar_closedBall (EqHaar.lean:500);
- integral_sub_left_eq_self, the additive form of Group/Integral.lean:163;
- the convolution API: convolutionExists_right (Convolution.lean:316), support_convolution_subset (:670), convolution_precompR_apply (:970), hasFDerivAt_convolution_right (ContDiff/Convolution.lean:61), contDiff_convolution_right/left (:420, :427);
- IsOpen.is_const_of_fderiv_eq_zero (MeanValue.lean:617).
The SimonGMT proof (fderiv_convolution_eq_zero, ae_eq_const_on_ball) served as the model for weak_constancy_ball.

Results:
- The 3 child types validate and elaborate in the comparator scope.
- Each child has a complete single-theorem Lean proof that compiles warning-free with no new import and passes the leaf-gate simulation.
- An end-to-end file proves the parent's exact frozen type from the children, with axioms propext, Classical.choice, Quot.sound only.
- The proposed names collide with nothing in the DAG (453 nodes), the project snapshot or simongmt.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
