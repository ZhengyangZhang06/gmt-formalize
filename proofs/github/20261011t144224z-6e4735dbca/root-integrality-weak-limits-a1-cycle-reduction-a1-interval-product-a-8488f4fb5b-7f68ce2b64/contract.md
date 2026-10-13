<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_plane-a1 -->

## Theorem `Submission.iwl_cr_ip_wt_product_plane`

Let P, m ∈ ℕ and let τ = (τ_1, …, τ_m) be an orthonormal family in ℝ^P. Write Φ(s, u) := (s, u_1, …, u_P) ∈ ℝ^{P+1} (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))), π(y) := (y_1, …, y_P) ∈ ℝ^P (Lean: (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ y))), e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{P+1} and τ̃ := (e₀, Φ(0, τ_1), …, Φ(0, τ_m)) : Fin (m+1) → ℝ^{P+1} (Lean: Fin.cons e₀ (fun i => Φ(0, τ i))). Then (a) τ̃ is orthonormal; (b) finrank ℝ (span ℝ (range τ̃)) = m + 1; (c) as subsets of ℝ^{P+1}, span ℝ (range τ̃) = {z : π(z) ∈ span ℝ (range τ)}.

Node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_plane-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3643

Prerequisites: None

Decomposition children: None

## Lean problem

Declaration: `Submission.iwl_cr_ip_wt_product_plane`

```lean
∀ (P m : ℕ) (τ : Fin m → Eucl P), Orthonormal ℝ τ → Orthonormal ℝ (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) ∧ Module.finrank ℝ (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)))) = m + 1 ∧ ((Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1))) : Submodule ℝ (Eucl (P + 1))) : Set (Eucl (P + 1))) = {z : Eucl (P + 1) | ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z))) ∈ Submodule.span ℝ (range τ)}
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
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_plane-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1 and 2 of the parent proof (orthonormality of τ̃ = (e₀, ιτ), dim Q = m + 1, and Q = π⁻¹(T) as sets), with the coordinate facts (F1)–(F3).

Notation. E := ℝ^P = Eucl P, E′ := ℝ^{P+1} = Eucl (P+1). Φ(s, u) := (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u)) = (s, u_1, …, u_P); π(z) := (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P+1)) ℝ z)) = (z_1, …, z_P); z₀ := (EuclideanSpace.equiv (Fin (P+1)) ℝ z) 0; e₀ := EuclideanSpace.single 0 1; τ̃ := Fin.cons e₀ (fun i => Φ(0, τ_i)) : Fin (m+1) → E′, so τ̃_0 = e₀ and τ̃_{i+1} = Φ(0, τ_i) (Fin.cons_zero, Fin.cons_succ); T := span ℝ (range τ); Q := span ℝ (range τ̃).

1. (Coordinates.) The coordinates of Φ(s, u) are Φ(s, u)₀ = s and Φ(s, u)_{j+1} = u_j (ContinuousLinearEquiv.apply_symm_apply, Fin.cons_zero, Fin.cons_succ). Hence π(Φ(s, u)) = u (Fin.tail_cons, ContinuousLinearEquiv.symm_apply_apply). Moreover every z ∈ E′ satisfies z = Φ(z₀, π(z)): both sides have the same image under the injective map EuclideanSpace.equiv, because Fin.cons (q 0) (Fin.tail q) = q (Fin.cons_self_tail).
2. (e₀ = Φ(1, 0).) Compare coordinates by Fin.cases: at index 0 both equal 1; at index j+1, e₀ has coordinate 0 (j+1 ≠ 0, Fin.succ_ne_zero) and Φ(1, 0) has coordinate 0. Hence τ̃_0 = Φ(1, 0).
3. (Inner products.) For a, b ∈ ℝ and u, w ∈ E: ⟨Φ(a, u), Φ(b, w)⟩ = Σ_{i : Fin (P+1)} Φ(a, u)_i·Φ(b, w)_i (PiLp.inner_apply) = a·b + Σ_{j : Fin P} u_j·w_j (Fin.sum_univ_succ and step 1) = a·b + ⟨u, w⟩.
4. (τ̃ is orthonormal.) By orthonormal_iff_ite it suffices to show ⟨τ̃_i, τ̃_j⟩ = (1 if i = j else 0) for all i, j : Fin (m+1). Split i and j with Fin.cases and use steps 2, 3:
   - i = j = 0: ⟨Φ(1,0), Φ(1,0)⟩ = 1·1 + ⟨0, 0⟩ = 1.
   - i = 0, j = j′+1: ⟨Φ(1,0), Φ(0,τ_{j′})⟩ = 1·0 + ⟨0, τ_{j′}⟩ = 0, and 0 ≠ j′+1.
   - i = i′+1, j = 0: symmetric, value 0, and i′+1 ≠ 0.
   - i = i′+1, j = j′+1: ⟨Φ(0,τ_{i′}), Φ(0,τ_{j′})⟩ = 0 + ⟨τ_{i′}, τ_{j′}⟩ = (1 if i′ = j′ else 0) because τ is orthonormal, and i′+1 = j′+1 iff i′ = j′ (Fin.succ_inj).
5. (finrank Q = m + 1.) An orthonormal family is linearly independent (Orthonormal.linearIndependent), so finrank ℝ Q = card (Fin (m+1)) = m + 1 (finrank_span_eq_card, Fintype.card_fin).
6. (π is linear.) Fin.tail q = q ∘ Fin.succ, so π is the composite linear map πₗ := (EuclideanSpace.equiv (Fin P) ℝ).symm ∘ₗ LinearMap.funLeft ℝ ℝ Fin.succ ∘ₗ (EuclideanSpace.equiv (Fin (P+1)) ℝ), and πₗ z = π(z) holds by definition (rfl). Let Z := T.comap πₗ, a submodule of E′ whose underlying set is {z : π(z) ∈ T}.
7. (Φ is linear.) For a, b, c ∈ ℝ and u, w ∈ E: Φ(a, u) + Φ(b, w) = Φ(a + b, u + w) and c·Φ(a, u) = Φ(c·a, c·u) (pull the sum/scalar inside the linear equivalences with map_add/map_smul and compare coordinates by Fin.cases), and Φ(0, 0) = 0. By induction over finite sets (Finset.induction_on), Σ_{i∈s} Φ(a_i, u_i) = Φ(Σ_{i∈s} a_i, Σ_{i∈s} u_i).
8. (Q ≤ Z.) By Submodule.span_le it suffices that every τ̃_i lies in Z. By Fin.cases: π(τ̃_0) = π(Φ(1, 0)) = 0 ∈ T (zero_mem), and π(τ̃_{i+1}) = π(Φ(0, τ_i)) = τ_i ∈ T (Submodule.subset_span), using step 1.
9. (Z ≤ Q.) Let z ∈ Z, i.e. π(z) ∈ T. By Submodule.mem_span_range_iff_exists_fun there is c : Fin m → ℝ with Σ_i c_i·τ_i = π(z). By steps 2 and 7, z₀·τ̃_0 + Σ_i c_i·τ̃_{i+1} = Φ(z₀·1, z₀·0) + Σ_i Φ(c_i·0, c_i·τ_i) = Φ(z₀, Σ_i c_i·τ_i) = Φ(z₀, π(z)) = z (step 1). Each summand lies in Q (subset_span, smul_mem, sum_mem, add_mem), hence z ∈ Q.
10. (Conclusion.) Steps 8 and 9 give Q = Z, hence (Q : Set E′) = (Z : Set E′) = {z : π(z) ∈ T}. Together with steps 4 and 5 this proves all three claims. ∎

Formalization aid. The following tactic proof, placed after `theorem Submission.iwl_cr_ip_wt_product_plane : <the frozen Lean type of this child, verbatim> := by`, was kernel-checked in the contract scope (namespace GMT.Ch06 with the contract's opens) after import GMT.Ch06.Submission at the frozen commit d8d46c9 with the pinned toolchain (Lean v4.35.0-rc3, Mathlib 25730c7c); #print axioms = [propext, Classical.choice, Quot.sound]. It uses no helper declarations and no sibling.

  intro P m τ hτ
  -- Coordinates.
  let Φ : ℝ → Eucl P → Eucl (P + 1) := fun s u =>
    (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ u))
  have he₀ : (EuclideanSpace.single 0 1 : Eucl (P + 1)) = Φ 1 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Φ]
    · simp [Φ, Fin.succ_ne_zero]
  have hinner : ∀ (a b : ℝ) (u w : Eucl P), inner ℝ (Φ a u) (Φ b w) = a * b + inner ℝ u w := by
    intro a b u w
    simp only [Φ, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  set v : Fin (m + 1) → Eucl (P + 1) := (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1))
    (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1)) with hv
  have hv0 : v 0 = Φ 1 0 := by rw [hv, Fin.cons_zero, he₀]
  have hvs : ∀ i : Fin m, v i.succ = Φ 0 (τ i) := fun i => by rw [hv, Fin.cons_succ]
  have hon : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · rw [hv0, hinner]; simp
    · rw [hv0, hvs, hinner]; simp [(Fin.succ_ne_zero j').symm]
    · rw [hv0, hvs, hinner]; simp [Fin.succ_ne_zero i']
    · rw [hvs, hvs, hinner, (orthonormal_iff_ite.1 hτ) i' j']
      simp [Fin.succ_inj]
  refine ⟨hon, ?_, ?_⟩
  · rw [finrank_span_eq_card hon.linearIndependent, Fintype.card_fin]
  · -- The projection `π` as a linear map.
    let πₗ : Eucl (P + 1) →ₗ[ℝ] Eucl P :=
      (EuclideanSpace.equiv (Fin P) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.funLeft ℝ ℝ Fin.succ ∘ₗ (EuclideanSpace.equiv (Fin (P + 1)) ℝ).toLinearMap)
    have hπ : ∀ z, πₗ z = (EuclideanSpace.equiv (Fin P) ℝ).symm
        (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ z)) := fun z => rfl
    have hπΦ : ∀ s u, πₗ (Φ s u) = u := by
      intro s u
      rw [hπ]
      simp only [Φ, ContinuousLinearEquiv.apply_symm_apply, Fin.tail_cons,
        ContinuousLinearEquiv.symm_apply_apply]
    have hspan : Submodule.span ℝ (range v) = (Submodule.span ℝ (range τ)).comap πₗ := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases ?_ (fun i' => ?_) i
        · simp only [SetLike.mem_coe, Submodule.mem_comap, hv0, hπΦ]
          exact Submodule.zero_mem _
        · simp only [SetLike.mem_coe, Submodule.mem_comap, hvs, hπΦ]
          exact Submodule.subset_span ⟨i', rfl⟩
      · intro z hz
        rw [Submodule.mem_comap, Submodule.mem_span_range_iff_exists_fun] at hz
        obtain ⟨c, hc⟩ := hz
        have hz' : z = (EuclideanSpace.equiv (Fin (P + 1)) ℝ z 0) • v 0 +
            ∑ i, c i • v i.succ := by
          have hdecomp : z = Φ (EuclideanSpace.equiv (Fin (P + 1)) ℝ z 0) (πₗ z) := by
            apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
            simp only [Φ, hπ, ContinuousLinearEquiv.apply_symm_apply]
            exact (Fin.cons_self_tail _).symm
          have hlin : ∀ (a b : ℝ) (u w : Eucl P), Φ a u + Φ b w = Φ (a + b) (u + w) := by
            intro a b u w
            simp only [Φ, ← map_add]
            congr 1
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsmul : ∀ (c : ℝ) (a : ℝ) (u : Eucl P), c • Φ a u = Φ (c * a) (c • u) := by
            intro c a u
            simp only [Φ, ← map_smul]
            congr 1
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsum : ∀ (s : Finset (Fin m)) (a : Fin m → ℝ) (u : Fin m → Eucl P),
              ∑ i ∈ s, Φ (a i) (u i) = Φ (∑ i ∈ s, a i) (∑ i ∈ s, u i) := by
            intro s a u
            induction s using Finset.induction_on with
            | empty =>
              have h00 : Φ 0 0 = 0 := by
                apply (EuclideanSpace.equiv (Fin (P + 1)) ℝ).injective
                simp only [Φ, ContinuousLinearEquiv.apply_symm_apply, map_zero]
                ext i
                refine Fin.cases ?_ (fun j => ?_) i <;> simp
              simp [h00]
            | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj,
                Finset.sum_insert hj, ih, hlin]
          rw [hv0]
          simp_rw [hvs, hsmul, hsum, hlin, mul_zero, Finset.sum_const_zero, mul_one, smul_zero,
            zero_add, add_zero, hc]
          exact hdecomp
        rw [hz']
        refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.succ, rfl⟩))
    rw [hspan]
    rfl

## Key steps

1. Coordinates: Φ(s,u)₀ = s, π(Φ(s,u)) = u, z = Φ(z₀, π z), e₀ = Φ(1,0), and ⟨Φ(a,u), Φ(b,w)⟩ = ab + ⟨u,w⟩.
2. τ̃ is orthonormal by orthonormal_iff_ite with Fin.cases on both indices.
3. finrank span τ̃ = card (Fin (m+1)) = m + 1 by linear independence (finrank_span_eq_card).
4. span τ̃ = (span τ).comap πₗ: the generators map into span τ; conversely z = z₀·e₀ + Σ c_i·Φ(0,τ_i) when π z = Σ c_i τ_i.

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
