<!-- theorem-id: gmt-ch06/root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1 -->

## Theorem `Submission.iwl_cr_interval_product_im`

Let P, m ∈ ℕ and let X ∈ D_m(ℝ^P) be integer multiplicity. Then there is an integer multiplicity Z ∈ D_{m+1}(ℝ^{P+1}) (the product [[(0,1)]] × X) such that Z(η) = ∫_0^1 X(φ(s)) ds for every η ∈ D^{m+1}(ℝ^{P+1}) and every family φ : ℝ → D^m(ℝ^P) with φ(s)(x)(v) = η(Φ(s, x))(e_0, Φ(0, v_1), …, Φ(0, v_m)) for all s ∈ [0,1], x ∈ ℝ^P, v ∈ (ℝ^P)^m, where Φ(s, x) := (s, x_1, …, x_P) ∈ ℝ^{P+1} (Lean: (EuclideanSpace.equiv (Fin (P+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) and e_0 := Φ(1, 0) = EuclideanSpace.single 0 1.

Node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/953

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2764

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3637, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3643, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3649, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3658, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2475, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1341, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2157

## Lean problem

Declaration: `Submission.iwl_cr_interval_product_im`

```lean
∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m), IsIntegerMultiplicity X → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (P + 1))) (m + 1), IsIntegerMultiplicity Z ∧ ∀ (η : TestFormOn (univ : Set (Eucl (P + 1))) (m + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl P)) m), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl P) (v : Fin m → Eucl P), (φ s : DifferentialForm (Eucl P) m) x v = (η : DifferentialForm (Eucl (P + 1)) (m + 1)) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)
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

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part I, item 5, first paragraph of the parent proof (“the product current Π := [[(0,1)]] × X … If X = τ(M,θ,ξ) is i.m., then Π = τ((0,1) × M, θ∘π_2, e_0 ∧ ξ∘π_2) is i.m. (Simon 3.2(2)) … product formula for Hausdorff measure on rectifiable sets, Federer 3.2.23 … blow-ups of the product are products of blow-ups”), filled in. Here Π is defined directly as the τ-current of the product triple, and the parent's defining formula Π(η) = ∫_0^1 X(α_η(t,·)) dt is the slice formula proved in Step 5.

Conventions. E := ℝ^P, E′ := ℝ^{P+1}, Hᵏ := μHE[k] on the relevant space. Φ : ℝ × E → E′ as in the statement is a linear isometric isomorphism (‖Φ(s,x)‖² = s² + ‖x‖²), so it maps Hausdorff measures to Hausdorff measures (`Isometry.euclideanHausdorffMeasure_image`). e_0 := Φ(1,0), ι(v) := Φ(0,v) (a linear isometric embedding E → E′), π : E′ → E the linear 1-Lipschitz map with π(Φ(s,x)) = x. ℒ : Λ_{m+1}(E′) → Λ_m(E), ℒ(α)(v) := α(e_0, ιv_1, …, ιv_m), i.e. ℒ(α) = (α.curryLeft e_0).compContinuousLinearMap ι, is continuous linear with ‖ℒ‖ ≤ 1. The hypothesis on φ says φ(s)(x) = ℒ(η(Φ(s,x))) for s ∈ [0,1].
Write X = τ(M, θ, ξ): IsRectifiableTriple univ m M θ ξ, θ(x) ∈ ℕ for x ∈ M (so θ ≥ 1 on M), and X(φ) = ∫_M θ ξ(φ) dH^m for all φ ∈ D^m(E). As θ ≥ 1 on M and θ is integrable on M ∩ K for compact K, H^m(M ∩ K) < ∞; so H^m⌞M is locally finite (σ-finite). Let G ⊆ M be the set of x for which there is an orthonormal τ = τ(x) ∈ E^m with HasWeightedApproximateTangentSpaceAt m M θ x (span τ) and ξ(x) = ±simpleNVector τ; H^m(M ∖ G) = 0. For x ∈ G and α ∈ Λ_m(E), |ξ(x)(α)| = |α(τ)| ≤ ‖α‖.

1. (Product formula.) By iwl_cr_hausdorff_product_formula: (PF-null) if N ⊆ E and H^m(N) = 0 then H^{m+1}(Φ(ℝ × N)) = 0 (note {y : π(y) ∈ N} = Φ(ℝ × N)); (PF) if A ⊆ E is H^m-null-measurable, countably m-rectifiable and H^m(A ∩ K) < ∞ for every compact K, then ∫_{Φ(ℝ×A)} g dH^{m+1} = ∫_ℝ ∫_A g(Φ(s, x)) dH^m(x) ds for every Borel g : E′ → [0, ∞]. (PF) extends to every g that is integrable on Φ(ℝ × A) (split g = g⁺ − g⁻) and to functions of the form g = (g₁ ∘ π)·g₂ with g₂ Borel and g₁ equal H^m⌞A-a.e. to a Borel function: changing g₁ on an H^m-null set N changes g only on Φ(ℝ × N), which is H^{m+1}-null by (PF-null) and does not affect the right-hand side. All sets to which (PF) is applied below (M, the blow-ups M_r, the plane T) satisfy its hypotheses.
2. (The product triple.) Put M̃ := Φ((0,1) × M), θ̃ := θ ∘ π and ξ̃(y) := ξ(π y) ∘L ℒ ∈ NVector E′ (m+1), so ξ̃(Φ(s,x))(α) = ξ(x)(ℒα). We verify IsRectifiableTriple univ (m+1) M̃ θ̃ ξ̃:
 (a) M̃ ⊆ univ.
 (b) Null-measurability: there is a Borel M_B with H^m(M Δ M_B) = 0; Φ((0,1) × M_B) is Borel (Φ is a homeomorphism) and M̃ Δ Φ((0,1) × M_B) ⊆ Φ(ℝ × (M Δ M_B)), which is H^{m+1}-null by (PF-null).
 (c) Countable (m+1)-rectifiability: M ⊆ M_0 ∪ ⋃_j range F_j with H^m(M_0) = 0 and F_j : Eucl m → E Lipschitz; hence M̃ ⊆ Φ(ℝ × M_0) ∪ ⋃_j range G_j with G_j : Eucl (m+1) → E′, G_j(u) := Φ(u_0, F_j(u_1, …, u_m)) Lipschitz, and H^{m+1}(Φ(ℝ × M_0)) = 0 by (PF-null).
 (d) For y = Φ(s,x) ∈ M̃: θ̃(y) = θ(x) > 0 and θ̃(y) ∈ ℕ.
 (e) Local integrability: a compact K′ ⊆ E′ satisfies M̃ ∩ K′ ⊆ Φ((0,1) × (M ∩ π(K′))) with π(K′) compact; by (PF) for A := M, ∫_{M̃ ∩ K′} θ̃ dH^{m+1} ≤ ∫_0^1 ∫_{M ∩ π(K′)} θ dH^m ds < ∞ (θ̃ is H^{m+1}⌞M̃-measurable after modification on the null set of (f)).
 (f) Measurability of ξ̃: ξ = ξ′ H^m-a.e. on M for a strongly measurable ξ′; ξ̃′(y) := ξ′(π y) ∘L ℒ is strongly measurable, and ξ̃ = ξ̃′ off Φ(ℝ × (M ∩ {ξ ≠ ξ′})), an H^{m+1}-null set by (PF-null). The same argument applies to θ̃.
 (g) Orientation: for y = Φ(s,x) with s ∈ (0,1), x ∈ G, let τ̃ := (e_0, ιτ_1, …, ιτ_m): it is orthonormal and Q := span τ̃ = Φ(ℝ × span τ). For α ∈ Λ_{m+1}(E′), ξ̃(y)(α) = ξ(x)(ℒα) = ±(ℒα)(τ) = ±α(τ̃), so ξ̃(y) = ±simpleNVector τ̃; the weighted tangent condition at y is Step 3. The exceptional set M̃ ∖ Φ((0,1) × G) ⊆ Φ(ℝ × (M ∖ G)) is H^{m+1}-null by (PF-null).
3. (Tangent planes of the product.) Fix y = Φ(s₀, x) with s₀ ∈ (0,1) and x ∈ G; T := span τ(x), Q := Φ(ℝ × T), finrank Q = m + 1. Let f ∈ C_c(E′) with spt f ⊆ Φ([−ρ, ρ] × B̄_ρ(0)). For r > 0: blowUpMap y r '' M̃ = Φ(I_r × M_r) with I_r := ((0,1) − s₀)/r and M_r := blowUpMap x r '' M (Φ is linear), and θ̃(y + rΦ(σ, w)) = θ(x + rw). M_r is H^m-null-measurable and countably m-rectifiable with H^m⌞M_r locally finite (M_r is the image of M under a similarity; `euclideanHausdorffMeasure_homothety_image`). By (PF) for A := M_r (applied to the positive and negative parts of the integrand). All integrals here are finite: f is bounded with compact support, and ∫_{M_r ∩ B̄_ρ(0)} θ(x + rw) dH^m(w) = r^{−m}∫_{M ∩ B̄_{rρ}(x)} θ dH^m < ∞ by the scaling of Hausdorff measure under the homothety w ↦ x + rw (`euclideanHausdorffMeasure_homothety_image`) and the local integrability of θ. Thus:
 A(r) := ∫_{blowUpMap y r '' M̃} f(z) θ̃(y + rz) dH^{m+1}(z) = ∫_{I_r} a_r(σ) dσ, a_r(σ) := ∫_{M_r} f(Φ(σ, w)) θ(x + rw) dH^m(w).
 For each σ, f_σ := f(Φ(σ, ·)) ∈ C_c(E), so by the tangent property of (M, θ) at x, a_r(σ) → θ(x)∫_T f_σ dH^m as r → 0⁺. Fix g₀ ∈ C_c(E) with 0 ≤ g₀ ≤ 1 and g₀ = 1 on B̄_ρ(0); then |a_r(σ)| ≤ ‖f‖_∞ ∫_{M_r} g₀(w)θ(x + rw) dH^m(w) → ‖f‖_∞ θ(x)∫_T g₀, so there are r₀ > 0 and K₀ with |a_r(σ)| ≤ K₀ for 0 < r < r₀ and all σ, while a_r(σ) = 0 for |σ| > ρ. Since 0 < s₀ < 1, 1_{I_r}(σ) → 1 for every σ. Dominated convergence along r → 0⁺ (dominating function K₀·1_{[−ρ,ρ]}; `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`) gives A(r) → θ(x)∫_ℝ ∫_T f(Φ(σ, w)) dH^m(w) dσ = θ(x)∫_Q f dH^{m+1}, the last equality by (PF) for A := T (equivalently: μHE[m+1] restricted to the (m+1)-plane Q is its Lebesgue measure, `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`, and Φ|ℝ×T is a linear isometry onto Q). Since θ̃(y) = θ(x), this is HasWeightedApproximateTangentSpaceAt (m+1) M̃ θ̃ y Q.
4. (The current Z.) For η ∈ D^{m+1}(E′) put Z(η) := tauAction (m+1) M̃ θ̃ ξ̃ η = ∫_{M̃} θ̃ ξ̃(η) dH^{m+1}. For H^{m+1}-a.e. y ∈ M̃ (by 2(g)), |ξ̃(y)(η(y))| = |η(y)(τ̃)| ≤ ‖η(y)‖ ≤ (sup‖η‖)·1_{tsupport η}(y), and θ̃ is integrable on M̃ ∩ tsupport η by 2(e); so the integrand is integrable and Z is ℝ-linear. If TestFormOnConverges η_l 0 (common compact support K′, sup‖η_l‖ → 0 by uniform convergence of the 0-th derivatives), then |Z(η_l)| ≤ (sup‖η_l‖)·∫_{M̃∩K′} θ̃ dH^{m+1} → 0. Hence Z ∈ GeometricCurrentOn univ (m+1) on E′, and by Step 2 and 2(d), IsIntegerMultiplicity Z (triple (M̃, θ̃, ξ̃), θ̃ natural-valued on M̃, Z = tauAction).
5. (Slice formula.) Let η ∈ D^{m+1}(E′) and φ : ℝ → D^m(E) with φ(s)(x) = ℒ(η(Φ(s,x))) for s ∈ [0,1]. The integrand g := 1_{Φ((0,1)×ℝ^P)}·θ̃·ξ̃(η) is integrable on M̃ (Step 4) and is a finite sum of functions of the form covered by Step 1: fix a basis (b_l) of the finite-dimensional space Λ_m(E) with coordinate functionals (b*_l), so that α = Σ_l b*_l(α)·b_l for every α; then θ̃(y)ξ̃(y)(η(y)) = Σ_l (θ·ξ(·)(b_l))(π y)·b*_l(ℒη(y)), where each g₁ := θ·ξ(·)(b_l) is H^m⌞M-a.e. equal to a Borel function (θ and ξ are a.e.-measurable) and each g₂(y) := 1_{(0,1)}(y_0)·b*_l(ℒη(y)) is Borel (η is continuous). So, by (PF) for A := M applied to g (term by term, positive and negative parts), and Fubini for L¹⌞(0,1) ⊗ H^m⌞M (σ-finite): Z(η) = ∫_0^1 ∫_M θ(x) ξ(x)(ℒ(η(Φ(s,x)))) dH^m(x) ds = ∫_0^1 ∫_M θ(x) ξ(x)(φ(s)(x)) dH^m(x) ds = ∫_0^1 X(φ(s)) ds, because X(φ(s)) = tauAction m M θ ξ (φ(s)) for every s and the interval integral over [0,1] equals the integral over (0,1). ∎

## Key steps

1. Use the product formula H^{m+1}⌞Φ(ℝ × A) = L¹ ⊗ H^m⌞A and its null-set version from iwl_cr_hausdorff_product_formula (extended to a.e.-Borel integrands by (PF-null)).
2. The product triple (Φ((0,1)×M), θ∘π, ξ(π·)∘ℒ) is null-measurable, countably (m+1)-rectifiable, positive integer valued and locally integrable, with ξ̃ = ±simpleNVector(e_0, ιτ).
3. Blow-ups of the product are products of blow-ups: dominated convergence in the interval variable gives the weighted tangent plane ℝe_0 ⊕ ιT_x at a.e. point.
4. Z := τ(M̃, θ̃, ξ̃) is a current (integrable, sequentially continuous) and integer multiplicity; the product formula and Fubini give Z(η) = ∫_0^1 X(φ(s)) ds.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3: read nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/{parent-child-handoff,decomposition-v1,decomposition-audit-v1,decomposition-review-receipt-v1}.json`
- `python3: dag.json statuses and frozen lean_statements of iwl_im_closure, iwl_smooth_pushforward, iwl_cycle_reduction, isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le, isoperimetric_abs_covector_apply_le, lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula; scan of dag.json and nodes/*/decomposition-v*.json for iwl_cr_* names`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem LinearMap.injective_iff_antilipschitz|theorem normDet_sq_eq_det_gram|theorem measurePreserving_piFinSuccAbove|theorem PiLp.volume_preserving_ofLp|theorem PiLp.volume_preserving_toLp|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero|theorem hausdorffMeasure_zero_singleton|theorem hausdorffMeasure_apply|theorem exists_measurable_subset_ae_eq|theorem lintegral_prod |theorem Measurable.lintegral_prod_right'|theorem lintegral_iUnion |theorem lintegral_tsum' mathlib/Mathlib (snapshot)`
- `rg -n 'hausdorffMeasure.*prod|area_formula|areaJacobian' mathlib/Mathlib (snapshot)`
- `grep -rln for hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, norm_iteratedFDeriv_smul_le, alternatizeUncurryFin_curryLeft, extDeriv_extDeriv, tendsto_integral_filter_of_dominated_convergence, integral_integral_swap, euclideanHausdorffMeasure_homothety_image, det_succ_row_zero in snapshot Mathlib`
- `grep -n '^theorem|^def' simongmt Chapter02/{AreaLipschitz,WeightedArea,Area,AreaApproximation,AreaNoninjective}.lean, Chapter03/{Rectifiable,DisjointCover,SubmanifoldCover}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean; rg 'pointSlice_isTestForm|iteratedFDeriv_fixedSupportParameterSlice' simongmt`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, piece construction hpart)`
- `python3 -I /tmp/cr2/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/cr2/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/cr2/Scratch/Assembly.lean, SolutionCheck.lean, LibCheck.lean, JacCheck.lean, SplitCheck.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cr2/scripts/gen.py`
- `/tmp/cr2/Scratch/Assembly.lean`
- `/tmp/cr2/Scratch/SolutionCheck.lean`
- `/tmp/cr2/Scratch/LibCheck.lean`
- `/tmp/cr2/Scratch/JacCheck.lean`
- `/tmp/cr2/Scratch/SplitCheck.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

Findings in dag.json:
- The chart-cover and rectifiable-area-formula nodes (lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula) are still speculative-ready, so they cannot be reused.
- No other DAG node supplies a product formula.
- iwl_im_closure and iwl_smooth_pushforward are the parent's frozen sibling dependencies, with the types used in the assembly.
- The reused isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le and isoperimetric_abs_covector_apply_le are accepted, with identical types.

Libraries:
- rg in the snapshot Mathlib finds no area formula and no Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real and hausdorffMeasure_prod_real exist.
- The pinned SimonGMT package (lake-packages-25730c7c/simongmt, rev 2b36630) supplies the injective Lipschitz area formula weighted_area_formula_lipschitz_injOn (Chapter02/AreaLipschitz.lean:101). It takes an arbitrary weight, with μHE[finrank E] on the target, volume on the source and J = areaJacobianAt = normDet. It is derived from WeightedArea.lean:76/120. SimonGMT also supplies area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet and measurable_areaJacobianAt.
- Mathlib supplies exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LinearMap.injective_iff_antilipschitz, LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303), measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, lintegral_prod, lintegral_iUnion and lintegral_tsum.
- All of these print only propext, Classical.choice and Quot.sound.
- The accepted rectifiability_weighted_tangent_ae (commit 2f36576) already formalizes the same bi-Lipschitz piece construction (`hpart`).
- These inputs give a complete chart-free proof of the product formula.

Lean checks:
- 12 challenge modules and 12 solution resolutions.
- The parent assembly.
- The lift Jacobian identity and the measure-preserving split (standard axioms only).

These checks certify statements, assembly and library inputs, not the remaining analytic proofs. Those were reviewed in natural language; the v1 audit accepted 11 of them, and an independent reviewer accepted the repaired one in this session.

Public citation: Federer, GMT (1969) 3.2.23, cited for this product formula in arXiv:2505.11279.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
