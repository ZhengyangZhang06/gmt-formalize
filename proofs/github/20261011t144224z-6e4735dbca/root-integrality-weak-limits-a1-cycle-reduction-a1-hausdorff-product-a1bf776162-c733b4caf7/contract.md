<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.injective_pieces-a1 -->

## Theorem `Submission.iwl_cr_hp_injective_pieces`

Let P, m ∈ ℕ and let A ⊆ ℝ^P be a Borel set (MeasurableSet A) that is countably m-rectifiable (Simon Ch. 3, 1.1 as in SimonGMT CountablyRectifiable: A ⊆ M₀ ∪ ⋃_j F_j(ℝ^m) with H^m(M₀) = 0 and each F_j : ℝ^m → ℝ^P Lipschitz), where H^k := μHE[k]. Then there are maps G_p : ℝ^m → ℝ^P and sets B_p ⊆ ℝ^m (p ∈ ℕ) with the following properties:
- each G_p is Lipschitz and each B_p is Borel;
- G_p is injective on B_p and differentiable at every point of B_p;
- each image G_p(B_p) is a Borel subset of A, and the images are pairwise disjoint;
- H^m(A ∖ ⋃_p G_p(B_p)) = 0.

Node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.injective_pieces-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2764

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.iwl_cr_hp_injective_pieces`

```lean
∀ (P m : ℕ) (A : Set (Eucl P)), MeasurableSet A → CountablyRectifiable m A → ∃ (G : ℕ → Eucl m → Eucl P) (B : ℕ → Set (Eucl m)), (∀ p, ∃ K : ℝ≥0, LipschitzWith K (G p)) ∧ (∀ p, MeasurableSet (B p)) ∧ (∀ p, InjOn (G p) (B p)) ∧ (∀ p, ∀ b ∈ B p, DifferentiableAt ℝ (G p) b) ∧ (∀ p, G p '' B p ⊆ A) ∧ (∀ p, MeasurableSet (G p '' B p)) ∧ Pairwise (Function.onFun Disjoint fun p => G p '' B p) ∧ (μHE[m] : Measure (Eucl P)) (A \ ⋃ p, G p '' B p) = 0
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

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.injective_pieces-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source and scope. This is Steps 6–7 of the parent proof of iwl_cr_hausdorff_product_formula (node root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1).
- It reuses the piece construction of the comparator-accepted proof of rectifiability_weighted_tangent_ae (node root.rectifiability-a1.weighted_tangent_ae-a1, Lean code `hparam`/`hpart` in commit 2f36576), with dimension m + 1 replaced by m.
- It then disjointifies the pieces.
- No DAG declaration is used, and the case m = 0 needs no special treatment.

Library inputs (pinned Mathlib 25730c7c, SimonGMT 2b36630):
- (L2) Poincare.SimonGMT.Chapter02 (AreaLipschitz.lean): areaRegularSet f := {x | DifferentiableAt ℝ f x ∧ Function.Injective (fderiv ℝ f x)}.
  - measurableSet_areaRegularSet: this set is Borel.
  - area_image_compl_regularSet_eq_zero: if LipschitzWith K f, then for every s, μHE[finrank ℝ E] (f '' (s ∖ areaRegularSet f)) = 0. This is Rademacher plus the null critical image.
- (L4) exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Mathlib/MeasureTheory/Function/Jacobian.lean:255).
  - Input: f, s, f′ with HasFDerivWithinAt f (f′ x) s x for x ∈ s, and r : (E →L[ℝ] F) → ℝ≥0 with r A ≠ 0 for all A.
  - Output: pairwise disjoint Borel t_n with s ⊆ ⋃_n t_n, and A_n with ApproximatesLinearOn f (A_n) (s ∩ t_n) (r(A_n)), i.e. ‖f x − f y − A_n(x − y)‖ ≤ r(A_n)‖x − y‖ on s ∩ t_n.
  - Moreover, if s is nonempty then ∀ n, ∃ y ∈ s, A_n = f′ y.
- (L5) MeasurableSet.image_of_continuousOn_injOn (Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:821): a Borel set in a Polish space has Borel image under a map that is continuous and injective on it.
- (L6) LinearMap.exists_antilipschitzWith: an injective linear map L on a finite-dimensional space admits K > 0 with ‖v‖ ≤ K‖L v‖.
- Also used: finrank_euclideanSpace_fin (finrank ℝ (Eucl m) = m), and disjointed, disjoint_disjointed, disjointed_subset, iUnion_disjointed, MeasurableSet.disjointed.

1. (Data.) Unfold CountablyRectifiable m A. There are M₀ ⊆ E := Eucl P with μHE[m](M₀) = 0 and maps F_j : Eucl m → E (j ∈ ℕ) with LipschitzWith K_j F_j, such that A ⊆ M₀ ∪ ⋃_j range F_j.

2. (Lower-bound constants.) For every continuous linear L : Eucl m →L[ℝ] E choose δ(L) ∈ ℝ≥0 with δ(L) > 0, and κ(L) > 0:
- If L is injective, (L6) gives K_L > 0 with ‖v‖ ≤ K_L‖L v‖ for all v. Put δ(L) := κ(L) := (2K_L)⁻¹.
- Otherwise put δ(L) := κ(L) := 1.
Claim: let L be injective, t ⊆ Eucl m and g : Eucl m → E, and suppose ‖g(b) − g(b′) − L(b − b′)‖ ≤ δ(L)‖b − b′‖ for b, b′ ∈ t. Then κ(L)‖b − b′‖ ≤ ‖g(b) − g(b′)‖ for b, b′ ∈ t. Indeed,
  ‖b − b′‖/K_L ≤ ‖L(b − b′)‖ ≤ ‖g(b) − g(b′)‖ + ‖g(b) − g(b′) − L(b − b′)‖ ≤ ‖g(b) − g(b′)‖ + (2K_L)⁻¹‖b − b′‖,
so ‖g(b) − g(b′)‖ ≥ (2K_L)⁻¹‖b − b′‖.

3. (Partition of the regular set.) Fix j and put R_j := areaRegularSet F_j, which is Borel by (L2).
- If R_j = ∅, put t_{j,l} := ∅ for all l.
- Otherwise, F_j is differentiable at each b ∈ R_j, so HasFDerivWithinAt F_j (fderiv ℝ F_j b) R_j b. Apply (L4) with f := F_j, s := R_j, f′ := fderiv ℝ F_j and r := δ; this is allowed since δ(L) ≠ 0 for all L. It gives Borel sets t′_l and continuous linear maps A_l (l ∈ ℕ) with:
  - R_j ⊆ ⋃_l t′_l;
  - ApproximatesLinearOn F_j A_l (R_j ∩ t′_l) δ(A_l);
  - since R_j ≠ ∅, A_l = fderiv ℝ F_j y_l for some y_l ∈ R_j.
  Put t_{j,l} := R_j ∩ t′_l.
- In both cases: t_{j,l} is Borel, t_{j,l} ⊆ R_j, and R_j ⊆ ⋃_l t_{j,l}.
- F_j is injective on t_{j,l}. In the nonempty case, A_l is injective because y_l ∈ R_j. Step 2 then gives κ(A_l)‖b − b′‖ ≤ ‖F_j b − F_j b′‖ on t_{j,l}, so F_j b = F_j b′ forces ‖b − b′‖ ≤ 0, i.e. b = b′.

4. (Enumeration.) For p ∈ ℕ with (j, l) := Nat.unpair p, put G_p := F_j and S_p := t_{j,l}. Then:
- G_p is LipschitzWith K_j, hence continuous;
- S_p is Borel, and G_p is injective on S_p;
- G_p is differentiable at every b ∈ S_p, because S_p ⊆ R_j;
- G_p '' S_p is Borel by (L5), since Eucl m is Polish and G_p is continuous and injective on S_p.

5. (The exceptional set.) Put N := M₀ ∪ ⋃_j F_j '' (univ ∖ R_j). By (L2) with s := univ and finrank ℝ (Eucl m) = m, μHE[m](F_j '' (univ ∖ R_j)) = 0 for every j. Together with μHE[m](M₀) = 0 and countable subadditivity, μHE[m](N) = 0.

6. (Covering.) We show A ⊆ N ∪ ⋃_p G_p '' S_p. Let x ∈ A.
- If x ∈ M₀, then x ∈ N.
- Otherwise x = F_j(b) for some j and b.
  - If b ∉ R_j, then x ∈ F_j '' (univ ∖ R_j) ⊆ N.
  - If b ∈ R_j, then b ∈ t_{j,l} for some l. With p := Nat.pair j l we have Nat.unpair p = (j, l), so x = G_p(b) ∈ G_p '' S_p.

7. (Disjointification.) Let A_p := disjointed (fun p => A ∩ G_p '' S_p) p, i.e. A_p = (A ∩ G_p '' S_p) ∖ ⋃_{q<p} (A ∩ G_q '' S_q), and B_p := S_p ∩ G_p⁻¹(A_p).
(i) A_p is Borel (MeasurableSet.disjointed; A and every G_q '' S_q are Borel), A_p ⊆ A ∩ G_p '' S_p (disjointed_subset), and the A_p are pairwise disjoint (disjoint_disjointed).
(ii) B_p is Borel, since S_p is Borel, G_p is continuous (hence measurable) and A_p is Borel. Also B_p ⊆ S_p, so G_p is injective on B_p and differentiable at each point of B_p.
(iii) G_p '' B_p = A_p. If b ∈ B_p then G_p(b) ∈ A_p by definition. Conversely, if x ∈ A_p then x ∈ G_p '' S_p, so x = G_p(b) with b ∈ S_p; then b ∈ G_p⁻¹(A_p), i.e. b ∈ B_p.
Consequently each G_p '' B_p = A_p is a Borel subset of A, and the sets G_p '' B_p are pairwise disjoint.

8. (Null remainder.) ⋃_p A_p = ⋃_p (A ∩ G_p '' S_p) by iUnion_disjointed. If x ∈ A ∖ ⋃_p A_p, then x ∉ G_p '' S_p for every p; otherwise x ∈ A ∩ G_p '' S_p ⊆ ⋃_p A_p. So x ∈ N by Step 6. Hence A ∖ ⋃_p G_p '' B_p ⊆ N, and μHE[m](A ∖ ⋃_p G_p '' B_p) = 0.

9. The family (G_p, B_p)_{p∈ℕ} has all the required properties. ∎

Appendix (Lean, verified). The declaration below proves exactly this frozen statement. It was compiled against the frozen project:
- environment: commit d8d46c9, Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b36630;
- placement: inside GMT/Ch06/Submission.lean, in `namespace GMT.Ch06` after the contract's `noncomputable section … end`, where accepted `theorem Submission.…` declarations go (the check used a scratch file that imports GMT.Ch06.Submission and replays the contract's namespace and `open` commands);
- `#print axioms` reports [propext, Classical.choice, Quot.sound].
Extra imports to add at the top of GMT/Ch06/Submission.lean: Poincare.SimonGMT.Chapter02.AreaLipschitz, Mathlib.MeasureTheory.Function.Jacobian, Mathlib.MeasureTheory.Constructions.Polish.Basic. The proof uses no auxiliary top-level declarations.

theorem Submission.iwl_cr_hp_injective_pieces : ∀ (P m : ℕ) (A : Set (Eucl P)), MeasurableSet A → CountablyRectifiable m A → ∃ (G : ℕ → Eucl m → Eucl P) (B : ℕ → Set (Eucl m)), (∀ p, ∃ K : ℝ≥0, LipschitzWith K (G p)) ∧ (∀ p, MeasurableSet (B p)) ∧ (∀ p, InjOn (G p) (B p)) ∧ (∀ p, ∀ b ∈ B p, DifferentiableAt ℝ (G p) b) ∧ (∀ p, G p '' B p ⊆ A) ∧ (∀ p, MeasurableSet (G p '' B p)) ∧ Pairwise (Function.onFun Disjoint fun p => G p '' B p) ∧ (μHE[m] : Measure (Eucl P)) (A \ ⋃ p, G p '' B p) = 0 := by
  intro P m A hA hM
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 2: lower-bound constants for injective linear maps
  have hchoice : ∀ L : Eucl m →L[ℝ] Eucl P, ∃ δ : ℝ≥0, 0 < δ ∧ ∃ k : ℝ, 0 < k ∧
      (Function.Injective L → ∀ (t : Set (Eucl m)) (g : Eucl m → Eucl P),
        ApproximatesLinearOn g L t δ → ∀ b ∈ t, ∀ b' ∈ t, k * ‖b - b'‖ ≤ ‖g b - g b'‖) := by
    intro L
    by_cases hL : Function.Injective L
    · obtain ⟨K, hKpos, hK⟩ := (L : Eucl m →ₗ[ℝ] Eucl P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hL)
      have hK0 : (0 : ℝ) < K := hKpos
      refine ⟨(2 * K)⁻¹, by positivity, (2 * (K : ℝ))⁻¹, by positivity,
        fun _ t g hg b hb b' hb' => ?_⟩
      have h1 : ‖b - b'‖ ≤ K * ‖L (b - b')‖ := by
        have := hK.le_mul_dist b b'
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe, map_sub] using this
      have h2 : ‖g b - g b' - L (b - b')‖ ≤ ((2 * K)⁻¹ : ℝ≥0) * ‖b - b'‖ := hg b hb b' hb'
      have h3 : ‖L (b - b')‖ ≤ ‖g b - g b'‖ + ‖g b - g b' - L (b - b')‖ := by
        have := norm_sub_le (g b - g b') (g b - g b' - L (b - b'))
        simpa using this
      push_cast at h2
      have h4 : ‖b - b'‖ / K ≤ ‖L (b - b')‖ := by
        rw [div_le_iff₀ hK0]; linarith
      have h5 : (2 * (K : ℝ))⁻¹ * ‖b - b'‖ = ‖b - b'‖ / K - (2 * (K : ℝ))⁻¹ * ‖b - b'‖ := by
        field_simp; ring
      linarith
    · exact ⟨1, one_pos, 1, one_pos, fun h => (hL h).elim⟩
  choose δ hδpos k hkpos hk using hchoice
  -- Step 3: partition of the regular set into injective pieces
  have hpart : ∀ j, ∃ (t : ℕ → Set (Eucl m)),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)) ∧
      Poincare.SimonGMT.Chapter02.areaRegularSet (F j) ⊆ ⋃ i, t i ∧
      ∀ i, InjOn (F j) (t i) := by
    intro j
    set R := Poincare.SimonGMT.Chapter02.areaRegularSet (F j) with hRdef
    have hRmeas : MeasurableSet R := Poincare.SimonGMT.Chapter02.measurableSet_areaRegularSet _
    rcases eq_empty_or_nonempty R with hR | hR
    · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun _ => empty_subset _,
        by rw [hR]; exact empty_subset _, fun i => injOn_empty _⟩
    obtain ⟨t, Al, -, ht, hcov, happrox, hactual⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F j) R (fderiv ℝ (F j))
        (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) δ (fun L => (hδpos L).ne')
    refine ⟨fun i => R ∩ t i, fun i => hRmeas.inter (ht i), fun i => inter_subset_left, ?_, ?_⟩
    · intro b hb
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hb)
      exact mem_iUnion.2 ⟨i, hb, hi⟩
    · intro i b hb b' hb' hbb
      obtain ⟨y, hy, hAy⟩ := hactual hR i
      have hlow := hk (Al i) (hAy ▸ hy.2) (R ∩ t i) (F j) (happrox i) b hb b' hb'
      rw [hbb, sub_self, norm_zero] at hlow
      have h0 : ‖b - b'‖ ≤ 0 := by
        have := hkpos (Al i)
        nlinarith [norm_nonneg (b - b')]
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)
  choose t ht_meas ht_sub ht_cov ht_inj using hpart
  have hfin : Module.finrank ℝ (Eucl m) = m := finrank_euclideanSpace_fin
  -- Step 4: enumeration
  set Gp : ℕ → Eucl m → Eucl P := fun p => F p.unpair.1 with hGpdef
  set Sp : ℕ → Set (Eucl m) := fun p => t p.unpair.1 p.unpair.2 with hSpdef
  have hGpL : ∀ p, ∃ K : ℝ≥0, LipschitzWith K (Gp p) := fun p => hF _
  have hSpm : ∀ p, MeasurableSet (Sp p) := fun p => ht_meas _ _
  have hSpinj : ∀ p, InjOn (Gp p) (Sp p) := fun p => ht_inj _ _
  have hSpdiff : ∀ p, ∀ b ∈ Sp p, DifferentiableAt ℝ (Gp p) b := fun p b hb => (ht_sub _ _ hb).1
  have hGpc : ∀ p, Continuous (Gp p) := fun p => by
    obtain ⟨K, hK⟩ := hGpL p; exact hK.continuous
  have himgm : ∀ p, MeasurableSet (Gp p '' Sp p) := fun p =>
    (hSpm p).image_of_continuousOn_injOn (hGpc p).continuousOn (hSpinj p)
  -- Step 5: the exceptional null set
  set N := M₀ ∪ ⋃ j, F j '' (univ \ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)) with hNdef
  have hN : (μHE[m] : Measure (Eucl P)) N = 0 := by
    refine measure_union_null hM₀ (measure_iUnion_null fun j => ?_)
    obtain ⟨K, hK⟩ := hF j
    have := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero hK univ
    rwa [hfin] at this
  -- Step 6: covering
  have hcov2 : A ⊆ N ∪ ⋃ p, Gp p '' Sp p := by
    intro x hx
    rcases hcover hx with h0 | h1
    · exact Or.inl (Or.inl h0)
    · obtain ⟨j, b, rfl⟩ := mem_iUnion.1 h1
      by_cases hb : b ∈ Poincare.SimonGMT.Chapter02.areaRegularSet (F j)
      · obtain ⟨i, hi⟩ := mem_iUnion.1 (ht_cov j hb)
        refine Or.inr (mem_iUnion.2 ⟨Nat.pair j i, ?_⟩)
        simp only [hGpdef, hSpdef, Nat.unpair_pair]
        exact ⟨b, hi, rfl⟩
      · exact Or.inl (Or.inr (mem_iUnion.2 ⟨j, b, ⟨mem_univ _, hb⟩, rfl⟩))
  -- Steps 7–8: disjointification and null remainder
  set Ap : ℕ → Set (Eucl P) := disjointed fun p => A ∩ Gp p '' Sp p with hApdef
  set Bp : ℕ → Set (Eucl m) := fun p => Sp p ∩ Gp p ⁻¹' Ap p with hBpdef
  have hApm : ∀ p, MeasurableSet (Ap p) :=
    MeasurableSet.disjointed fun p => hA.inter (himgm p)
  have hApsub : ∀ p, Ap p ⊆ A ∩ Gp p '' Sp p := fun p => disjointed_subset _ p
  have himgB : ∀ p, Gp p '' Bp p = Ap p := by
    intro p
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩; exact hb.2
    · intro hx
      obtain ⟨b, hb, rfl⟩ := ((hApsub p) hx).2
      exact ⟨b, ⟨hb, hx⟩, rfl⟩
  refine ⟨Gp, Bp, hGpL, fun p => (hSpm p).inter ((hApm p).preimage (hGpc p).measurable),
    fun p => (hSpinj p).mono inter_subset_left,
    fun p b hb => hSpdiff p b hb.1, fun p => by rw [himgB p]; exact fun x hx => ((hApsub p) hx).1,
    fun p => by rw [himgB p]; exact hApm p, ?_, ?_⟩
  · intro p q hpq
    simp only [Function.onFun, himgB]
    exact disjoint_disjointed _ hpq
  · simp only [himgB]
    rw [hApdef, iUnion_disjointed]
    refine measure_mono_null ?_ hN
    intro x ⟨hxA, hxU⟩
    rcases hcov2 hxA with hxN | hxG
    · exact hxN
    · exfalso
      obtain ⟨p, hp⟩ := mem_iUnion.1 hxG
      exact hxU (mem_iUnion.2 ⟨p, hxA, hp⟩)

## Key steps

1. Unfold CountablyRectifiable m A: Lipschitz F_j : ℝ^m → ℝ^P cover A up to the H^m-null set M₀.
2. For injective linear L with ‖v‖ ≤ K_L‖Lv‖, approximation within (2K_L)⁻¹ forces ‖g b − g b′‖ ≥ (2K_L)⁻¹‖b − b′‖.
3. Partition areaRegularSet F_j with Mathlib's exists_partition_approximatesLinearOn_of_hasFDerivWithinAt. The approximating maps are actual (injective) derivatives, so each Borel piece t_{j,l} carries F_j injectively.
4. Enumerate the pieces by Nat.unpair; the images are Borel (Lusin–Souslin). The non-regular images F_j(ℝ^m ∖ R_j) are null (area_image_compl_regularSet_eq_zero); together with M₀ they form an H^m-null set N with A ⊆ N ∪ ⋃_p G_p(S_p).
5. Disjointify: A_p := disjointed(A ∩ G_p(S_p)), B_p := S_p ∩ G_p⁻¹(A_p). Then G_p(B_p) = A_p are disjoint Borel subsets of A, and A ∖ ⋃_p A_p ⊆ N.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json  (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3: read /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/{parent-child-handoff.json, parent-supplied-natural-proof.json, parent-supplied-natural-proof.md, parent-supplied-plan.md}`
- `python3: dag.json node statuses and lean_names (lpf_raf_*, lpf_countably_rectifiable_c1_cover, rectifiability_weighted_tangent_ae, iwl_cr_*); grep -r 'iwl_cr_hp_' over the run directory (no match)`
- `grep -n 'theorem hausdorffMeasure_apply|hausdorffMeasure_le_liminf_tsum|hausdorffMeasure_zero_singleton' Mathlib/MeasureTheory/Measure/Hausdorff.lean; grep 'euclideanHausdorffMeasure_def|euclideanHausdorffMeasure_zero|addHaarScalarFactor_volume_hausdorffMeasure_ne_zero' Mathlib/Geometry/Euclidean/Volume/Measure.lean (snapshot)`
- `sed -n 250,275p Mathlib/MeasureTheory/Function/Jacobian.lean (exists_partition_approximatesLinearOn_of_hasFDerivWithinAt); grep measurePreserving_piFinSuccAbove Mathlib/MeasureTheory/Constructions/Pi.lean; grep 'PiLp.volume_preserving_ofLp|PiLp.volume_preserving_toLp' Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean; grep det_succ_row_zero Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; grep exists_measurable_subset_ae_eq Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `sed -n 290,320p Mathlib/Analysis/InnerProductSpace/NormDet.lean (LinearMap.normDet_sq_eq_det_gram, any Fintype index)`
- `grep -rn 'setLIntegral_comp_preimage|theorem prod_restrict|theorem lintegral_prod |Measurable.lintegral_prod_right'|MeasurePreserving.prod|LipschitzWith.prodMk' Mathlib/ (snapshot)`
- `grep -rn 'ediam_le|edist_le_ediam_of_mem|ediam_empty|ediam_le_of_forall_dist_le' Mathlib/Topology/EMetricSpace/Diam.lean Mathlib/Topology/MetricSpace/Bounded.lean (snapshot)`
- `simongmt: cat Chapter02/AreaLipschitz.lean; sed Chapter02/Area.lean, Chapter02/AreaParametrization.lean, Chapter02/AreaApproximation.lean; grep -rn 'theorem areaJacobianAt'; sed -n 28,80p Chapter03/Rectifiable.lean (CountablyRectifiable, CountablyRectifiable.mono)`
- `git show 2f36576:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, hparam/hpart piece construction); git show a46aa05:GMT/Ch06/Submission.lean and accepted candidate diffs (declaration conventions)`
- `verifier: gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement; python3 -I /tmp/hp_decomp/scripts/gen.py children_v1.json -> NodeChallenge files; lake env lean on each (all elaborate)`
- `lake env lean /tmp/hp_decomp/T0.lean (areaJacobianAt, weighted_area_formula_lipschitz_injOn and LinearMap.normDet_sq_eq_det_gram unknown under frozen imports; MeasurableSet.image_of_continuousOn_injOn, measurePreserving_piFinSuccAbove available)`
- `lake env lean /tmp/hp_decomp/scratch/{Assembly,JacBridge,LiftGram,PieceProduct,Pieces,Cyl}.lean and /tmp/hp_decomp/final/{All,Check_iwl_cr_hp_*}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/speculative-prompt-v3.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/EMetricSpace/Diam.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaParametrization.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/hp_decomp/T0.lean`
- `/tmp/hp_decomp/scratch/Assembly.lean`
- `/tmp/hp_decomp/scratch/JacBridge.lean`
- `/tmp/hp_decomp/scratch/LiftGram.lean`
- `/tmp/hp_decomp/scratch/PieceProduct.lean`
- `/tmp/hp_decomp/scratch/Pieces.lean`
- `/tmp/hp_decomp/scratch/Cyl.lean`
- `/tmp/hp_decomp/final/All.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_cylinder_null.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_injective_pieces.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_lift_gram_det.lean`
- `/tmp/hp_decomp/final/Check_iwl_cr_hp_piece_product.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c; the frozen contract is Contract.lean, and Submission.lean is identical to it at the dispatch base.

Library inputs found (all with standard axioms):
- Mathlib supplies:
  - Hausdorff measure: hausdorffMeasure_apply (ediam form), hausdorffMeasure_zero_singleton, euclideanHausdorffMeasure_def/_zero, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero;
  - pieces: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (root namespace), MeasurableSet.image_of_continuousOn_injOn;
  - linear algebra: LinearMap.normDet_sq_eq_det_gram (any Fintype index, so EuclideanSpace.basisFun works), Matrix.det_succ_row_zero;
  - integration: measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, MeasurePreserving.setLIntegral_comp_preimage, Measure.prod_restrict, lintegral_prod, Measurable.lintegral_prod_right', NullMeasurableSet.exists_measurable_subset_ae_eq;
  - diameters: Metric.ediam_le_of_forall_dist_le, edist_le_ediam_of_mem.
- SimonGMT 2b36630 supplies weighted_area_formula_lipschitz_injOn, area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet, measurable_areaJacobianAt, areaJacobianAt_eq_normDet/_nonneg, CountablyRectifiable (F_j : EuclideanSpace ℝ (Fin n) → E) and CountablyRectifiable.mono.
- Neither library has a Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real/prod_real exist.
- No DAG node supplies the needed lemmas with compatible types:
  - the lpf_raf_* area lemmas are chart/fibre-sum forms;
  - lpf_countably_rectifiable_c1_cover is only speculative-ready.
  So the split relies on library theorems only.

Scope check: areaJacobianAt, the SimonGMT area formula and LinearMap.normDet are NOT visible after `import GMT.Ch06.Submission` with the frozen imports. Hence lift_gram_det is stated with Gram determinants (Matrix.of … inner ℝ … EuclideanSpace.single). All four child statements elaborate in verifier-generated challenge modules.

Lean results:
- Scratch proofs of all four children with exactly the proposed types, and of the parent's exact frozen type from them, compile with only propext, Classical.choice and Quot.sound, and with zero warnings.
- Per-child compiles succeed with the minimal imports listed in each appendix.
- The accepted hparam/hpart code (commit 2f36576) was reused for injective_pieces.
- No name collisions with dag.json.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
