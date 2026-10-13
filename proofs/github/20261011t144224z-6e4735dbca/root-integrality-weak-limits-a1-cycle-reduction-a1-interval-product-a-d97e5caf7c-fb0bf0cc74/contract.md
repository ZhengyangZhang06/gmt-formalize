<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.blowup_mass_bound-a1 -->

## Theorem `Submission.iwl_cr_ip_wt_blowup_mass_bound`

Let P, m ∈ ℕ, Hᵐ := μHE[m], M ⊆ ℝ^P Hᵐ-null-measurable, θ : ℝ^P → ℝ with θ ≥ 0 on M and θ Hᵐ-integrable on M ∩ K for every compact K, x ∈ ℝ^P and T a linear subspace of ℝ^P with HasWeightedApproximateTangentSpaceAt m M θ x T (Simon Ch. 3, 1.7). Then for every R ∈ ℝ there is B ∈ ℝ such that for all sufficiently small r > 0 (eventually in 𝓝[>] 0), every C ∈ ℝ and every g : ℝ^P → ℝ with |g(w)| ≤ C for all w and g(w) = 0 whenever ‖w‖ > R satisfy |∫_{η_r(M)} g(w)·θ(x + r·w) dHᵐ(w)| ≤ C·B, where η_r := blowUpMap x r, η_r(z) = r⁻¹·(z − x).

Node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.blowup_mass_bound-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3643

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2157

Decomposition children: None

## Lean problem

Declaration: `Submission.iwl_cr_ip_wt_blowup_mass_bound`

```lean
∀ (P m : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (T : Submodule ℝ (Eucl P)), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → HasWeightedApproximateTangentSpaceAt m M θ x T → ∀ R : ℝ, ∃ B : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ (C : ℝ) (g : Eucl P → ℝ), (∀ w, |g w| ≤ C) → (∀ w, R < ‖w‖ → g w = 0) → |∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, g w * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P))| ≤ C * B
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

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.blowup_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 12 of the parent proof (uniform domination of the blown-up slices via the cut-off g₀ and the tangent hypothesis applied to g₀), stated for an arbitrary integrand g bounded by C and vanishing outside B̄(0, R).

Notation. E := ℝ^P = Eucl P, Hᵐ := μHE[m], ν := Hᵐ⌞M. For r > 0, η_r := blowUpMap x r, η_r(z) = r⁻¹·(z − x). The sibling blowup_cov (the accepted declaration fiw_tl_blowup_setIntegral) states: for every n, centre c, r > 0, set S and function h, ∫_{blowUpMap c r '' S} h dHⁿ = (rⁿ)⁻¹·∫_S h(blowUpMap c r z) dHⁿ(z), with no measurability or integrability assumption. The tangent hypothesis HasWeightedApproximateTangentSpaceAt m M θ x T says in particular (second component): for every φ ∈ C_c(E), ∫_{η_r(M)} φ(w)·θ(x + r·w) dHᵐ(w) → θ(x)·∫_T φ dHᵐ as r → 0⁺.

1. (Cut-off.) Let g₀(w) := max(0, min(1, R + 1 − ‖w‖)). It is continuous (continuous_const.max, .min, .sub continuous_norm). It satisfies 0 ≤ g₀ ≤ 1; g₀(w) = 1 when ‖w‖ ≤ R (then R + 1 − ‖w‖ ≥ 1); and g₀(w) = 0 when ‖w‖ > R + 1 (then min(1, R + 1 − ‖w‖) < 0). So the support of g₀ lies in the compact ball B̄(0, R + 1) (HasCompactSupport.intro) and g₀ defines an element G₀ ∈ C_c(E) (CompactlySupportedContinuousMap built from g₀).
2. (Choice of B.) By the tangent hypothesis applied to G₀, b(r) := ∫_{η_r(M)} g₀(w)·θ(x + r·w) dHᵐ(w) tends to L₀ := θ(x)·∫_T g₀ dHᵐ as r → 0⁺. Put B := L₀ + 1 > L₀. Then eventually in 𝓝[>] 0 we have b(r) < B (Filter.Tendsto.eventually_lt_const), and eventually r > 0 (self_mem_nhdsWithin). Fix such an r, and fix C ∈ ℝ and g : E → ℝ with |g(w)| ≤ C for all w and g(w) = 0 whenever R < ‖w‖. It remains to show |∫_{η_r(M)} g(w)·θ(x + r·w) dHᵐ(w)| ≤ C·B.
3. (θ is measurable and ν-a.e. nonnegative.) M = ⋃_{n∈ℕ} (M ∩ B̄(0, n)) (each u satisfies ‖u‖ ≤ ⌈‖u‖⌉₊). On each M ∩ B̄(0, n), θ is Hᵐ-integrable (the hypothesis on θ with the compact set K = B̄(0, n)), hence a.e. strongly measurable; so θ is a.e. strongly measurable for ν (aestronglyMeasurable_iUnion_iff). Since M is Hᵐ-null-measurable, ν-a.e. u lies in M (ae_restrict_mem₀), hence θ(u) ≥ 0 for ν-a.e. u.
4. (Undoing the blow-up.) For every h : E → ℝ, blowup_cov (n = m, centre x, set M, function w ↦ h(w)·θ(x + r·w), r > 0) gives ∫_{η_r(M)} h(w)·θ(x + r·w) dHᵐ(w) = (r^m)⁻¹·∫_M h(η_r(u))·θ(x + r·η_r(u)) dHᵐ(u) = (r^m)⁻¹·∫_M h(η_r(u))·θ(u) dHᵐ(u), because x + r·(r⁻¹·(u − x)) = u (smul_smul, mul_inv_cancel₀, one_smul, add_sub_cancel).
5. (Integrability of u ↦ g₀(η_r(u))·θ(u) on M.) It is a.e. strongly measurable for ν (g₀∘η_r is continuous; times θ, step 3). ‖η_r(u)‖ = r⁻¹·‖u − x‖, so if u ∉ B̄(x, r(R+1)) then ‖η_r(u)‖ > R + 1 and g₀(η_r(u)) = 0. With 0 ≤ g₀ ≤ 1 this gives |g₀(η_r(u))·θ(u)| ≤ 1_{B̄(x, r(R+1))}(u)·|θ(u)| for every u. The right side is ν-integrable: by integrable_indicator_iff and Measure.restrict_restrict this is integrability of |θ| on M ∩ B̄(x, r(R+1)), which holds since this ball is compact. Hence u ↦ g₀(η_r(u))·θ(u) is ν-integrable (Integrable.mono').
6. (Pointwise comparison.) C ≥ 0, because 0 ≤ |g(0)| ≤ C. For every w, |g(w)| ≤ C·g₀(w): if ‖w‖ ≤ R then g₀(w) = 1 and |g(w)| ≤ C; otherwise g(w) = 0 and C·g₀(w) ≥ 0. Consequently, for ν-a.e. u (those with θ(u) ≥ 0), |g(η_r(u))·θ(u)| = |g(η_r(u))|·θ(u) ≤ C·g₀(η_r(u))·θ(u).
7. (Integral estimate.) |∫_M g(η_r(u))·θ(u) dHᵐ| ≤ ∫_M |g(η_r(u))·θ(u)| dHᵐ (norm_integral_le_integral_norm; no integrability needed) ≤ ∫_M C·g₀(η_r(u))·θ(u) dHᵐ (integral_mono_of_nonneg: the left integrand is nonnegative, the right one is ν-integrable by step 5, and step 6 gives the ν-a.e. inequality) = C·∫_M g₀(η_r(u))·θ(u) dHᵐ (integral_const_mul).
8. (Conclusion.) By step 4 with h = g and (r^m)⁻¹ > 0: |∫_{η_r(M)} g(w)·θ(x + r·w) dHᵐ| = (r^m)⁻¹·|∫_M g(η_r(u))·θ(u) dHᵐ| ≤ (r^m)⁻¹·C·∫_M g₀(η_r(u))·θ(u) dHᵐ (step 7) = C·b(r) (step 4 with h = g₀) ≤ C·B (C ≥ 0 and b(r) < B). This holds for every r in the eventual set of step 2 and all C, g as stated. ∎

Formalization aid. The following tactic proof, placed after `theorem Submission.iwl_cr_ip_wt_blowup_mass_bound : <the frozen Lean type of this child, verbatim> := by`, was kernel-checked in the contract scope (namespace GMT.Ch06 with the contract's opens) after import GMT.Ch06.Submission at the frozen commit d8d46c9 with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c), together with the accepted proof of Submission.fiw_tl_blowup_setIntegral (sibling blowup_cov, the only declaration it uses); #print axioms = [propext, Classical.choice, Quot.sound].

  intro P m M θ x T hMmeas hθnn hθint hTan R
  -- The cut-off `g₀ = max 0 (min 1 (R + 1 - ‖w‖))`.
  let g₀ : Eucl P → ℝ := fun w => max 0 (min 1 (R + 1 - ‖w‖))
  have hg₀c : Continuous g₀ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hg₀0 : ∀ w, R + 1 < ‖w‖ → g₀ w = 0 := by
    intro w hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  have hg₀cs : HasCompactSupport g₀ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Eucl P) (R + 1)) (fun w hw => ?_)
    rw [mem_closedBall, dist_zero_right, not_le] at hw
    exact hg₀0 w hw
  have hg₀nn : ∀ w, 0 ≤ g₀ w := fun w => le_max_left _ _
  have hg₀le : ∀ w, g₀ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hg₀1 : ∀ w, ‖w‖ ≤ R → g₀ w = 1 := by
    intro w hw
    show max 0 (min 1 (R + 1 - ‖w‖)) = 1
    rw [min_eq_left (by linarith)]
    exact max_eq_right zero_le_one
  let G₀ : CompactlySupportedContinuousMap (Eucl P) ℝ := ⟨⟨g₀, hg₀c⟩, hg₀cs⟩
  have hlim := hTan.2 G₀
  refine ⟨θ x * ∫ y in (T : Set (Eucl P)), g₀ y ∂(μHE[m] : Measure (Eucl P)) + 1, ?_⟩
  filter_upwards [hlim.eventually_lt_const (lt_add_one _), self_mem_nhdsWithin] with r hrB hr C g hgC hg0
  have hr0 : (0 : ℝ) < r := hr
  -- `θ` is a.e. strongly measurable and a.e. nonnegative for `Hᵐ ⌞ M`.
  have hθae : AEStronglyMeasurable θ ((μHE[m] : Measure (Eucl P)).restrict M) := by
    have hM : M = ⋃ n : ℕ, M ∩ closedBall (0 : Eucl P) n := by
      ext u
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      exact ⟨fun hu => ⟨⌈‖u‖⌉₊, hu, Nat.le_ceil _⟩, fun ⟨_, hu, _⟩ => hu⟩
    rw [hM, aestronglyMeasurable_iUnion_iff]
    intro n
    exact (hθint _ (isCompact_closedBall _ _)).aestronglyMeasurable
  have hθpos : ∀ᵐ u ∂((μHE[m] : Measure (Eucl P)).restrict M), 0 ≤ θ u :=
    (ae_restrict_mem₀ hMmeas).mono fun u hu => hθnn u hu
  -- Undo the blow-up for any integrand.
  have hcov : ∀ h : Eucl P → ℝ, ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      h w * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)) = (r ^ m)⁻¹ * ∫ u in M,
        h (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u ∂(μHE[m] : Measure (Eucl P)) := by
    intro h
    rw [Submission.fiw_tl_blowup_setIntegral P m x r M (fun w => h w * θ (x + r • w)) hr0]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul,
      add_sub_cancel]
  have hηc : Continuous (Poincare.SimonGMT.Chapter03.blowUpMap x r) := by
    show Continuous fun u : Eucl P => r⁻¹ • (u - x)
    fun_prop
  have hηnorm : ∀ u, ‖Poincare.SimonGMT.Chapter03.blowUpMap x r u‖ = r⁻¹ * ‖u - x‖ := by
    intro u
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr0]
  -- Integrability of `u ↦ g₀(η u) θ(u)` on `M`.
  have hint₀ : Integrable (fun u => g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u)
      ((μHE[m] : Measure (Eucl P)).restrict M) := by
    refine Integrable.mono' (g := (closedBall x (r * (R + 1))).indicator fun u => |θ u|) ?_
      ((hg₀c.comp hηc).aestronglyMeasurable.mul hθae) (Filter.Eventually.of_forall fun u => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall, IntegrableOn,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact (hθint _ (isCompact_closedBall x (r * (R + 1)))).norm.congr
        (Filter.Eventually.of_forall fun u => by simp [Real.norm_eq_abs])
    · by_cases hu : u ∈ closedBall x (r * (R + 1))
      · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs (θ u), Real.norm_eq_abs]
        exact mul_le_of_le_one_left (abs_nonneg _)
          ((abs_of_nonneg (hg₀nn _)).trans_le (hg₀le _))
      · rw [indicator_of_notMem hu, hg₀0, zero_mul, norm_zero]
        rw [mem_closedBall, dist_eq_norm, not_le] at hu
        rw [hηnorm, lt_inv_mul_iff₀ hr0]
        exact hu
  -- `C ≥ 0`, and `|g(η u)| θ(u) ≤ C g₀(η u) θ(u)` on `M`.
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  have hpt : ∀ w, |g w| ≤ C * g₀ w := by
    intro w
    by_cases hw : ‖w‖ ≤ R
    · rw [hg₀1 w hw, mul_one]
      exact hgC w
    · rw [hg0 w (not_le.1 hw), abs_zero]
      exact mul_nonneg hC (hg₀nn w)
  have hkey : |∫ u in M, g (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
      ∂(μHE[m] : Measure (Eucl P))| ≤
      C * ∫ u in M, g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P)) := by
    rw [← integral_const_mul]
    refine (Real.norm_eq_abs _ ▸ norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
      (hint₀.const_mul C) ?_
    filter_upwards [hθpos] with u hu
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hpt _) hu
  rw [hcov g, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr0 m))]
  have hb := hcov g₀
  calc (r ^ m)⁻¹ * |∫ u in M, g (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P))|
      ≤ (r ^ m)⁻¹ * (C * ∫ u in M, g₀ (Poincare.SimonGMT.Chapter03.blowUpMap x r u) * θ u
        ∂(μHE[m] : Measure (Eucl P))) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 (pow_nonneg hr0.le m))
    _ = C * ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, g₀ w * θ (x + r • w)
        ∂(μHE[m] : Measure (Eucl P)) := by rw [hb]; ring
    _ ≤ C * (θ x * ∫ y in (T : Set (Eucl P)), g₀ y ∂(μHE[m] : Measure (Eucl P)) + 1) :=
        mul_le_mul_of_nonneg_left hrB.le hC

## Key steps

1. Cut-off g₀ = max(0, min(1, R+1−‖w‖)) ∈ C_c(ℝ^P): 0 ≤ g₀ ≤ 1, g₀ = 1 on B̄(0,R), g₀ = 0 off B̄(0,R+1).
2. The tangent hypothesis for g₀ gives b(r) → θ(x)∫_T g₀, so eventually b(r) < B := θ(x)∫_T g₀ + 1.
3. blowup_cov: every blown-up integral ∫_{η_r M} h(w)θ(x+r·w) equals (r^m)⁻¹∫_M h(η_r u)θ(u).
4. |g| ≤ C·g₀ pointwise and θ ≥ 0 a.e. on M; u ↦ g₀(η_r u)θ(u) is integrable on M (supported in B̄(x, r(R+1))).
5. |∫_{η_r M} g θ(x+r·)| ≤ (r^m)⁻¹·C·∫_M g₀(η_r u)θ(u) = C·b(r) ≤ C·B.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum (ea3ee0dd…853d)`
- `python3 -I: dag.json status/lean_name/lean_statement of root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1* and of root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1; its accepted-candidate.json contract.lean_statement == dag lean_statement and audit.comparator_passed`
- `git show 91a22d1bfc9063820dd1583526d3d097beffd0ec:GMT/Ch06/Submission.lean (accepted proof and declaration layout of Submission.fiw_tl_blowup_setIntegral)`
- `grep -rhoE "iwl_cr_ip_[A-Za-z0-9_']+" nodes dag.json (finds the sibling product_triple proposals iwl_cr_ip_pt_slab_restrict_eq_map, iwl_cr_ip_pt_slab_transfer, iwl_cr_ip_pt_cylinder_nullMeasurableSet, iwl_cr_ip_pt_cylinder_countablyRectifiable, iwl_cr_ip_pt_frame_orthonormal); grep -rhoE 'iwl_cr_ip_wt[A-Za-z0-9_]*' nodes dag.json (no match)`
- `python3 -I: nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json (parent split, blowup_cov entry) and sibling decomposition-v1.json files (measure_identity, slice_formula: no split; product_triple: split with the names above)`
- `grep -n "theorem\|def\|abbrev" in simongmt Poincare/SimonGMT/Chapter03/Rectifiable.lean: CountablyRectifiable (l.34), countablyRectifiable_range (l.64), blowUpMap (l.96), regular_euclideanHausdorffMeasure_restrict_submodule (l.187), HasWeightedApproximateTangentSpaceAt (l.330)`
- `grep -rn in local-references mathlib/Mathlib: tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated, intervalIntegral.integral_comp_mul_add, integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le, Integrable.comp_snd, MeasureTheory.AEStronglyMeasurable.comp_snd, aestronglyMeasurable_iUnion_iff, integrable_indicator_iff, integral_mono_of_nonneg, norm_integral_le_integral_norm, setIntegral_indicator, Continuous.integrable_of_hasCompactSupport, Measure.prod.instIsFiniteMeasureOnCompacts, integral_prod, MeasurableEmbedding.integral_map, HasCompactMulSupport.comp_homeomorph, Fintype.range_linearCombination, LinearMap.coe_toContinuousLinearMap', EuclideanSpace.real_norm_sq_eq, EuclideanSpace.equiv, abs_le_of_sq_le_sq, le_of_sq_le_sq, Filter.Tendsto.const_mul_atTop, Filter.Tendsto.const_mul_atTop_of_neg, tendsto_inv_nhdsGT_zero, Filter.Tendsto.eventually_lt_const, Continuous.bounded_above_of_compact_support, Continuous.finCons`
- `python3 -I /tmp/ptdec/scripts/gen.py and final.py (lean_contract.validate_lean_statement on all 7 child types; key/name regexes; dependency acyclicity)`
- `python3 -I /tmp/ptdec/scripts/layout.py (gmt-compare.py child_modules, contract mode) and lake env lean /tmp/ptdec/layout/AllChallenges.lean (7 exact comparator challenge targets)`
- `lake env lean /tmp/ptdec/Asm.lean (parent assembly from the 7 child stubs; sorryAx only from stubs)`
- `lake env lean /tmp/ptdec/C1.lean … C6.lean and /tmp/ptdec/Full.lean (complete child proofs + accepted blowup_cov proof + parent assembly + solution-side exact checks; #print axioms = [propext, Classical.choice, Quot.sound])`
- `independent reviewer subagent: re-ran Full.lean and AllChallenges.lean, compared payload statements byte-for-byte with the checked Lean files (scripts under /tmp/ptrev); verdict ACCEPT, minor wording fixes applied`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-6184ff8144/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-930be90ff5/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-blowup-change-of-variables-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Order/OrderClosed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/AtTopBot/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ptdec/scripts/gen.py`
- `/tmp/ptdec/scripts/layout.py`
- `/tmp/ptdec/scripts/full.py`
- `/tmp/ptdec/scripts/final.py`
- `/tmp/ptdec/Check.lean`
- `/tmp/ptdec/layout/AllChallenges.lean`
- `/tmp/ptdec/Asm.lean`
- `/tmp/ptdec/Full.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. The snapshot's GMT/Ch06/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

DAG and naming:
- No accepted declaration states any of the six new child statements, so nothing new is reused.
- The only reuse is fiw_tl_blowup_setIntegral: accepted, comparator_passed, with an identical frozen type.
- The sibling product_triple is concurrently proposing iwl_cr_ip_pt_* names (not accepted), two of which overlap product_measure and product_plane (a) mathematically. This node therefore uses the unreserved prefix iwl_cr_ip_wt_, with no match anywhere in the run directory.

SimonGMT Chapter03/Rectifiable.lean supplies blowUpMap, HasWeightedApproximateTangentSpaceAt (Simon Ch. 3, 1.7), countablyRectifiable_range and regular_euclideanHausdorffMeasure_restrict_submodule.

Mathlib supplies every tool used:
- dominated convergence along 𝓝[>] 0 and continuity of parametric integrals (tendsto_integral_filter_of_dominated_convergence, continuous_of_dominated);
- interval substitution (intervalIntegral.integral_comp_mul_add);
- Fubini (integral_prod, Integrable.comp_snd, AEStronglyMeasurable.comp_snd);
- change of variables along the homeomorphism Φ′ (MeasurableEmbedding.integral_map);
- integrability of compactly supported continuous functions (Continuous.integrable_of_hasCompactSupport, Measure.prod.instIsFiniteMeasureOnCompacts);
- the integral estimates integral_mono_of_nonneg and norm_integral_le_integral_norm.

Lean checks:
- All 7 child types elaborate in the exact comparator layout.
- All 6 new children are fully proved with axioms [propext, Classical.choice, Quot.sound].
- The frozen parent type is proved from them and the accepted blow-up lemma with the same axioms.
- An independent reviewer re-ran these checks and accepted the split.

Public sources for the mathematics: L. Simon, Introduction to Geometric Measure Theory, Ch. 3 §1 (Def. 1.7, weighted approximate tangent spaces) and Ch. 6, 3.2(2) (product with an interval); Federer, Geometric Measure Theory, 3.2.23 (product formula behind (MP)).


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
