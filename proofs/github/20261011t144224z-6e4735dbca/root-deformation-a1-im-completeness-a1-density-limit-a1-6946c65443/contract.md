<!-- theorem-id: gmt-ch06/root.deformation-a1.im_completeness-a1.density_limit-a1 -->

## Theorem `Submission.imc_im_density_limit`

Let N, k ∈ ℕ and H := μHE[k] on ℝ^N. For p ∈ ℕ let (M_p, θ_p, ξ_p) satisfy IsRectifiableTriple ℝ^N k M_p θ_p ξ_p, with θ_p natural-valued on M_p (∀ x ∈ M_p, ∃ m ∈ ℕ, θ_p(x) = m), and put κ_p := M_p.indicator(θ_p • ξ_p) : ℝ^N → Λ_k(ℝ^N) (NVector (Eucl N) k). Assume Σ_p ∫ |κ_{p+1} − κ_p| dH < ∞, where |w| := (Σ_γ w(dx^γ)²)^{1/2} for a k-vector w, the sum running over the strictly increasing multi-indices γ ∈ SimonMultiIndex k N (dx^γ = wedgeCovectors k (proj ∘ γ), w(dx^γ) = euclideanNVectorCoordinate w γ). Precisely: the [0, ∞]-valued series Σ_p ∫⁻ ENNReal.ofReal(|κ_{p+1}(x) − κ_p(x)|) dH(x) is ≠ ∞. Then there are M₀ ⊆ ℝ^N, θ₀ : ℝ^N → ℝ and ξ₀ : ℝ^N → Λ_k(ℝ^N) such that IsRectifiableTriple ℝ^N k M₀ θ₀ ξ₀ holds, θ₀ is natural-valued on M₀, and for every continuous compactly supported k-form ω : ℝ^N → Λ^k(ℝ^N), tauAction k M_p θ_p ξ_p ω → tauAction k M₀ θ₀ ξ₀ ω as p → ∞.

Node: `root.deformation-a1.im_completeness-a1.density_limit-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1106

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3254, https://github.com/ZhengyangZhang06/gmt-formalize/issues/3296, https://github.com/ZhengyangZhang06/gmt-formalize/issues/527, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1341

Decomposition children: None

## Lean problem

Declaration: `Submission.imc_im_density_limit`

```lean
∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k), (∀ p, IsRectifiableTriple (univ : Set (Eucl N)) k (M p) (θ p) (ξ p)) → (∀ p, ∀ x ∈ M p, ∃ m : ℕ, θ p x = m) → (∑' p, ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate ((M (p + 1)).indicator (fun y => θ (p + 1) y • ξ (p + 1) y) x - (M p).indicator (fun y => θ p y • ξ p y) x) γ) ^ 2)) ∂(μHE[k] : Measure (Eucl N))) ≠ ∞ → ∃ (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ m : ℕ, θ₀ x = m) ∧ ∀ ω : Eucl N → Covector (Eucl N) k, Continuous ω → HasCompactSupport ω → Tendsto (fun p => tauAction k (M p) (θ p) (ξ p) ω) atTop (𝓝 (tauAction k M₀ θ₀ ξ₀ ω))
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

- Parent DAG node: `root.deformation-a1.im_completeness-a1`
- Child DAG node: `root.deformation-a1.im_completeness-a1.density_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof (printed (2), (3) of Simon Ch. 6, Lemma 3.13: a.e. and L¹ convergence of the densities and integrality of the limit multiplicity), the Setting's unit fact (|τ₁ ∧ ⋯ ∧ τ_k| = 1 by Cauchy–Binet), the pointwise part of Step 6 ("θ_j(x) = θ(x) for j ≥ j(x); then x ∈ M_j and ξ_j(x) → ξ(x)") and the density half of Step 4 (∫⟨ω, κ_j⟩ dλ → ∫⟨ω, κ⟩ dλ). It uses the siblings l1_cauchy_limit (imc_ae_tendsto_of_summable_lintegral), limit_triple (imc_isRectifiableTriple_of_eventually_mem), pairing_expansion (polyhedral_approx_pairing_expansion, comparator-accepted) and tau_integrable (ltg_tau_integrable, comparator-accepted).

Notation. H := μHE[k]. I := SimonMultiIndex k N (strictly increasing γ : Fin k → Fin N), m := #I. e_i := EuclideanSpace.single i 1. For γ ∈ I: e_γ := (e_{γ(0)}, …, e_{γ(k−1)}), dx^γ := wedgeCovectors k (fun j ↦ EuclideanSpace.proj (γ j)), and e^γ := simpleNVector e_γ ∈ Λ_k. For a k-covector α: α_γ := euclideanCovectorCoordinate α γ = α(e_γ) and |α| := covectorEuclideanNorm α. ℝ^I := EuclideanSpace ℝ I with Euclidean norm ‖·‖. For a k-vector w: c(w) := (w(dx^γ))_γ ∈ ℝ^I, so ‖c(w)‖ = |w|. For a ∈ ℝ^I: L(a) := Σ_γ a_γ • e^γ ∈ Λ_k. κ_p := M_p.indicator(θ_p • ξ_p) and f_p := c ∘ κ_p : ℝ^N → ℝ^I.

0. Linear algebra.
 (a) c and L are ℝ-linear and continuous. Each coordinate of c is evaluation at the fixed covector dx^γ, and L is a finite sum of the continuous maps a ↦ a_γ • e^γ.
 (b) L(c(w)) = w for every k-vector w. For a covector α, L(c(w))(α) = Σ_γ w(dx^γ)·e^γ(α) = Σ_γ α(e_γ)·w(dx^γ) = Σ_γ α_γ·w(dx^γ) = w(α), by simpleNVector_apply and the first part of pairing_expansion. Two continuous linear functionals that agree everywhere are equal.
 (c) |L(a)(α)| ≤ m·‖a‖·|α| for a ∈ ℝ^I and every covector α. Indeed L(a)(α) = Σ_γ a_γ α_γ, with |a_γ| ≤ ‖a‖ (PiLp.norm_apply_le) and |α_γ| ≤ |α| (second part of pairing_expansion).
 (d) (Unit fact.) If τ : Fin k → ℝ^N is orthonormal, then Σ_γ c_γ(simpleNVector τ)² = 1, hence ‖c(simpleNVector τ)‖ = ‖c(−simpleNVector τ)‖ = 1. Proof. Let α₀ := wedgeCovectors k (fun i ↦ innerSL ℝ (τ i)), the k-covector ⟨τ₁, ·⟩ ∧ ⋯ ∧ ⟨τ_k, ·⟩. By wedgeCovectors_apply_det, α₀(v) = det[⟨τ_i, v_j⟩]_{i,j}. Hence α₀(τ) = det[⟨τ_i, τ_j⟩] = det 1 = 1 by orthonormality, and α₀(e_γ) = det[⟨τ_i, e_{γ(j)}⟩] = det[(τ_i)_{γ(j)}]. On the other side, c_γ(simpleNVector τ) = dx^γ(τ) = det[proj_{γ(i)}(τ_j)] = det[(τ_j)_{γ(i)}], the determinant of the transpose; so α₀(e_γ) = c_γ(simpleNVector τ) (Matrix.det_transpose). The pairing expansion with w := simpleNVector τ and α := α₀ gives 1 = α₀(τ) = (simpleNVector τ)(α₀) = Σ_γ α₀(e_γ)·c_γ(simpleNVector τ) = Σ_γ c_γ(simpleNVector τ)². Finally c(−s) = −c(s) has the same norm as c(s).

1. (The coordinate sequence.)
 (a) θ_p ≥ 1 on M_p: θ_p(x) is a natural number (hypothesis) and is positive (field pos of the triple).
 (b) f_p is H-a.e. strongly measurable. Its γ-coordinate is x ↦ κ_p(x)(dx^γ) = M_p.indicator(x ↦ θ_p(x)·ξ_p(x)(dx^γ)). By tau_integrable (a) (U := univ, b := dx^γ, K := B̄_n(0)), the map x ↦ θ_p(x)ξ_p(x)(dx^γ) is H-integrable on M_p ∩ B̄_n(0) for every n ∈ ℕ. Hence it is H⌞M_p-a.e. strongly measurable, since M_p = ⋃_n (M_p ∩ B̄_n(0)) (aestronglyMeasurable_iUnion_iff). As M_p is H-null-measurable, the indicator is H-a.e. strongly measurable (aestronglyMeasurable_indicator_iff₀). A map into the finite-dimensional space ℝ^I with a.e.-measurable coordinates is a.e. strongly measurable (aemeasurable_pi_iff, then compose with the continuous map WithLp.toLp).
 (c) ‖f_{p+1}(x) − f_p(x)‖ = ‖c(κ_{p+1}(x) − κ_p(x))‖ = |κ_{p+1}(x) − κ_p(x)|, by linearity of c and EuclideanSpace.norm_eq. Hence Σ_p ∫⁻ ‖f_{p+1} − f_p‖ₑ dH is the series of the hypothesis and is finite.
 (d) For H-a.e. x and every p, ‖f_p(x)‖ = M_p.indicator θ_p(x). If x ∉ M_p then κ_p(x) = 0 and both sides vanish. By the field orients of the triple (M_p, θ_p, ξ_p), for H⌞M_p-a.e. x there is an orthonormal τ with ξ_p(x) = ±simpleNVector τ. For such x ∈ M_p, f_p(x) = θ_p(x)·c(ξ_p(x)) and ‖f_p(x)‖ = |θ_p(x)|·1 = θ_p(x), by 0(d) and θ_p(x) > 0. Convert the H⌞M_p-a.e. statement into an H-a.e. statement guarded by x ∈ M_p (ae_restrict_iff'₀), and intersect over the countably many p (ae_all_iff).

2. (L¹ limit.) By l1_cauchy_limit (X := ℝ^N, μ := H, E := ℝ^I, f := (f_p)_p; hypotheses 1(b) and 1(c)) there is an H-a.e. strongly measurable g : ℝ^N → ℝ^I with f_p(x) → g(x) for H-a.e. x and ∫⁻ ‖f_p − g‖ₑ dH → 0.

3. (Integer limit.) Let G be the set of x such that f_p(x) → g(x) and the identity of 1(d) holds for every p; then H(ℝ^N ∖ G) = 0. Fix x ∈ G and put a_p := ‖f_p(x)‖ = M_p.indicator θ_p(x). Each a_p is a natural number n_p (θ_p is natural on M_p and the indicator is 0 off M_p), and a_p → ‖g(x)‖. Choose P with |a_p − ‖g(x)‖| < 1/2 for all p ≥ P. Then |n_p − n_P| < 1, so n_p = n_P for every p ≥ P (Int.abs_lt_one_iff). Hence M_p.indicator θ_p(x) = n_P for all p ≥ P, and ‖g(x)‖ = lim a_p = n_P. Define θ₀(x) := ⌊‖g(x)‖ + 1/2⌋₊ for every x, a natural number. For x ∈ G, θ₀(x) = n_P = ‖g(x)‖ (as ⌊n + 1/2⌋₊ = n), and M_p.indicator θ_p(x) = θ₀(x) for all p ≥ P.

4. (The limit data.) Let M₀ := {x : θ₀(x) ≥ 1} and ξ₀(x) := θ₀(x)⁻¹ • L(g(x)).
 (a) θ₀ is natural-valued everywhere, in particular on M₀, and θ₀ ≥ 1 on M₀.
 (b) θ₀ is H-a.e. measurable: g is a.e. strongly measurable, the norm is continuous, and t ↦ (⌊t⌋₊ : ℝ) is monotone, hence Borel (Monotone.measurable). So M₀ = θ₀⁻¹([1, ∞)) is H-null-measurable.
 (c) θ₀ is H-integrable on M₀ ∩ K for every compact K. Choose p with ∫⁻ ‖f_p − g‖ₑ dH < ∞ (possible by Step 2). By 1(d), ∫⁻_K ‖f_p‖ₑ dH = ∫⁻_K M_p.indicator(‖θ_p‖ₑ) dH = ∫⁻_{M_p∩K} ‖θ_p‖ₑ dH < ∞, because θ_p is integrable on M_p ∩ K (field integrableOn of the triple). Since θ₀ = ‖g‖ H-a.e. (Step 3) and ‖g‖ ≤ ‖f_p‖ + ‖f_p − g‖, we get ∫⁻_{M₀∩K} ‖θ₀‖ₑ ≤ ∫⁻_K ‖g‖ₑ ≤ ∫⁻_K ‖f_p‖ₑ + ∫⁻ ‖f_p − g‖ₑ < ∞. Together with 4(b) this is integrability.
 (d) For H⌞M₀-a.e. x: x ∈ M_p for all large p, and ξ_p(x) → ξ₀(x). Indeed, H⌞M₀-a.e. x lies in M₀ (ae_restrict_mem₀) and in G. For such x, θ₀(x) = n ≥ 1, and M_p.indicator θ_p(x) = n ≠ 0 for p ≥ P; this forces x ∈ M_p and θ_p(x) = n = θ₀(x). For such p, κ_p(x) = θ₀(x) • ξ_p(x), so ξ_p(x) = θ₀(x)⁻¹ • κ_p(x) = θ₀(x)⁻¹ • L(c(κ_p(x))) = θ₀(x)⁻¹ • L(f_p(x)) by 0(b). This tends to θ₀(x)⁻¹ • L(g(x)) = ξ₀(x), because f_p(x) → g(x) and L is continuous.

5. (Rectifiable limit triple.) Apply limit_triple to (M_p, θ_p, ξ_p)_p and (M₀, θ₀, ξ₀). Its hypotheses hold: the triples by assumption, θ_p ≥ 1 on M_p (1(a)), M₀ null-measurable (4(b)), θ₀ ≥ 1 on M₀ (4(a)), local integrability (4(c)), and the pointwise convergence (4(d)). It gives IsRectifiableTriple ℝ^N k M₀ θ₀ ξ₀, and by 4(a) the multiplicity θ₀ is natural-valued on M₀.

6. (Convergence of the τ-actions.) Let ω : ℝ^N → Λ^k be continuous with compact support, and let C := sup_x |ω(x)| < ∞. The map x ↦ |ω(x)| is continuous (covectorEuclideanNorm is the square root of a finite sum of squares of evaluations at fixed tuples, continuous_eval_const), and it has compact support since |0| = 0.
 (a) For every p, κ_p(x)(ω(x)) = M_p.indicator(θ_p·ξ_p(ω))(x). By tau_integrable (b) (U := univ) this is H-integrable, and tauAction k M_p θ_p ξ_p ω = ∫_{M_p} θ_pξ_p(ω) dH = ∫ κ_p(ω) dH (integral_indicator₀).
 (b) Likewise, with κ₀ := M₀.indicator(θ₀ • ξ₀), tau_integrable (b) for the triple of Step 5 shows that x ↦ κ₀(x)(ω(x)) is H-integrable and tauAction k M₀ θ₀ ξ₀ ω = ∫ κ₀(ω) dH.
 (c) κ₀(x) = L(g(x)) for H-a.e. x (namely x ∈ G). If x ∈ M₀ then θ₀(x) ≠ 0 and κ₀(x) = θ₀(x) • θ₀(x)⁻¹ • L(g(x)) = L(g(x)). If x ∉ M₀ then θ₀(x) < 1 is a natural number, so θ₀(x) = 0 = ‖g(x)‖; hence g(x) = 0 and κ₀(x) = 0 = L(0).
 (d) For H-a.e. x, κ_p(x)(ω(x)) − κ₀(x)(ω(x)) = L(f_p(x))(ω(x)) − L(g(x))(ω(x)) = L(f_p(x) − g(x))(ω(x)), by 0(b), (c) and linearity of L. Its absolute value is ≤ m·C·‖f_p(x) − g(x)‖ by 0(c).
 (e) Hence ∫⁻ ‖κ_p(ω) − κ₀(ω)‖ₑ dH ≤ ENNReal.ofReal(mC)·∫⁻ ‖f_p − g‖ₑ dH → 0 by Step 2. The L¹ convergence theorem for Bochner integrals (tendsto_integral_of_L1, with 6(a) and 6(b)) then gives ∫ κ_p(ω) dH → ∫ κ₀(ω) dH, i.e. tauAction k M_p θ_p ξ_p ω → tauAction k M₀ θ₀ ξ₀ ω. ∎

No dimension case split is needed. For k > N the index set I is empty, every k-vector and every k-covector is 0, and the formulas above hold verbatim; k = 0 is also covered verbatim.


Formalization note. The following Lean proof of exactly this declaration compiles against the frozen commit d8d46c9 (default maxHeartbeats, no set_option, no sorry), with the four sibling declarations as its only non-standard inputs (#print axioms: propext, Classical.choice, Quot.sound and the siblings). It follows Steps 0–6 (hunitfact is 0(d), hLc is 0(b), hLbound is 0(c), hnatlim is Step 3). Two instance details: ContinuousAdd (NVector (Eucl N) k) is not synthesized and is supplied from IsTopologicalAddGroup; and the compact support of x ↦ covectorEuclideanNorm (ω x) is proved with HasCompactSupport.mono, because HasCompactSupport.comp_left elaborates so slowly here that the default heartbeat budget is exceeded.
```lean
theorem Submission.imc_im_density_limit :
    ∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k), (∀ p, IsRectifiableTriple (univ : Set (Eucl N)) k (M p) (θ p) (ξ p)) → (∀ p, ∀ x ∈ M p, ∃ m : ℕ, θ p x = m) → (∑' p, ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate ((M (p + 1)).indicator (fun y => θ (p + 1) y • ξ (p + 1) y) x - (M p).indicator (fun y => θ p y • ξ p y) x) γ) ^ 2)) ∂(μHE[k] : Measure (Eucl N))) ≠ ∞ → ∃ (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ m : ℕ, θ₀ x = m) ∧ ∀ ω : Eucl N → Covector (Eucl N) k, Continuous ω → HasCompactSupport ω → Tendsto (fun p => tauAction k (M p) (θ p) (ξ p) ω) atTop (𝓝 (tauAction k M₀ θ₀ ξ₀ ω)) := by
  have hC2 := Submission.imc_ae_tendsto_of_summable_lintegral
  have hOrient := Submission.imc_isRectifiableTriple_of_eventually_mem
  have hPair := Submission.polyhedral_approx_pairing_expansion
  have hTau := Submission.ltg_tau_integrable
  intro N k M θ ξ hTri hNat hsum
  set H : Measure (Eucl N) := (μHE[k] : Measure (Eucl N)) with hH
  -- multiplicities are ≥ 1 on the carriers
  have hθ1 : ∀ p, ∀ x ∈ M p, 1 ≤ θ p x := by
    intro p x hx
    obtain ⟨m, hm⟩ := hNat p x hx
    have hpos := (hTri p).pos x hx
    rw [hm] at hpos ⊢
    have : m ≠ 0 := by rintro rfl; simp at hpos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  -- densities, coordinates
  set κ : ℕ → Eucl N → NVector (Eucl N) k :=
    fun p => (M p).indicator (fun y => θ p y • ξ p y) with hκ
  set c : NVector (Eucl N) k → EuclideanSpace ℝ (SimonMultiIndex k N) :=
    fun w => WithLp.toLp 2 (fun γ => euclideanNVectorCoordinate w γ) with hc
  set f : ℕ → Eucl N → EuclideanSpace ℝ (SimonMultiIndex k N) := fun p x => c (κ p x) with hf
  have hnormc : ∀ w : NVector (Eucl N) k,
      ‖c w‖ₑ = ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate w γ) ^ 2)) := by
    intro w
    rw [← ofReal_norm, EuclideanSpace.norm_eq]
    simp [hc, Real.norm_eq_abs, sq_abs]
  have hcsub : ∀ w w' : NVector (Eucl N) k, c (w - w') = c w - c w' := by
    intro w w'
    ext γ
    simp [hc, euclideanNVectorCoordinate]
  have hcoord : ∀ p (γ : SimonMultiIndex k N),
      AEStronglyMeasurable (fun x => euclideanNVectorCoordinate (κ p x) γ) H := by
    intro p γ
    have heq : (fun x => euclideanNVectorCoordinate (κ p x) γ) =
        (M p).indicator (fun x => θ p x * ξ p x (wedgeCovectors k (fun j => EuclideanSpace.proj (γ j)))) := by
      funext x
      by_cases hx : x ∈ M p
      · simp [hκ, hx, euclideanNVectorCoordinate]
      · simp [hκ, hx, euclideanNVectorCoordinate]
    rw [heq, aestronglyMeasurable_indicator_iff₀ (hTri p).nullMeasurableSet]
    have hU : (⋃ n : ℕ, M p ∩ closedBall (0 : Eucl N) n) = M p := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · rintro ⟨n, hx, -⟩
        exact hx
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
        exact ⟨n, hx, hn⟩
    rw [← hU, aestronglyMeasurable_iUnion_iff]
    intro n
    exact ((hTau N k univ (M p) (θ p) (ξ p) (hTri p)).1 _ _ (isCompact_closedBall 0 n)
      (subset_univ _)).aestronglyMeasurable
  have hfmeas : ∀ p, AEStronglyMeasurable (f p) H := by
    intro p
    have hpi : AEStronglyMeasurable
        (fun x => (fun γ => euclideanNVectorCoordinate (κ p x) γ : SimonMultiIndex k N → ℝ)) H :=
      (aemeasurable_pi_iff.2 fun γ => (hcoord p γ).aemeasurable).aestronglyMeasurable
    exact (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable hpi
  have hsum' : (∑' p, ∫⁻ x, ‖f (p + 1) x - f p x‖ₑ ∂H) ≠ ∞ := by
    convert hsum using 4 with p x
    simp only [hf, ← hcsub, hnormc]
    rfl
  obtain ⟨g, hgmeas, hgae, hgL1⟩ :=
    hC2 (Eucl N) H (EuclideanSpace ℝ (SimonMultiIndex k N)) f hfmeas hsum'
  -- the unit fact: ‖f p x‖ = 1_{M p} θ p x a.e.
  have hunitfact : ∀ τ : Fin k → Eucl N, Orthonormal ℝ τ →
      ∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate (simpleNVector τ) γ) ^ 2 = 1 := by
    intro τ hτ
    set α₀ : Covector (Eucl N) k := wedgeCovectors k (fun i => innerSL ℝ (τ i)) with hα₀
    have h1 : simpleNVector τ α₀ = 1 := by
      rw [simpleNVector_apply, hα₀, wedgeCovectors_apply_det]
      have : (Matrix.of fun i j => (innerSL ℝ (τ i)) (τ j)) = 1 := by
        ext i j
        rw [Matrix.of_apply, innerSL_apply_apply, Matrix.one_apply]
        exact orthonormal_iff_ite.mp hτ i j
      rw [this, Matrix.det_one]
    have h2 : ∀ γ : SimonMultiIndex k N, euclideanCovectorCoordinate α₀ γ =
        euclideanNVectorCoordinate (simpleNVector τ) γ := by
      intro γ
      simp only [euclideanCovectorCoordinate, euclideanNVectorCoordinate, simpleNVector_apply, hα₀]
      rw [wedgeCovectors_apply_det, wedgeCovectors_apply_det, ← Matrix.det_transpose]
      congr 1
      ext i j
      simp [Matrix.transpose_apply, EuclideanSpace.inner_single_right]
    have h3 := (hPair N k (simpleNVector τ) α₀).1
    rw [h1] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [h2, sq]
    rfl
  have hunit : ∀ p, ∀ᵐ x ∂H, ‖f p x‖ = (M p).indicator (θ p) x := by
    intro p
    have hor := (hTri p).orients
    rw [ae_restrict_iff'₀ (hTri p).nullMeasurableSet] at hor
    filter_upwards [hor] with x hx
    by_cases hxM : x ∈ M p
    · obtain ⟨τ, hτ, -, hξ⟩ := hx hxM
      rw [indicator_of_mem hxM]
      have hθpos := (hTri p).pos x hxM
      have hfx : f p x = θ p x • c (ξ p x) := by
        ext γ
        simp [hf, hc, hκ, hxM, euclideanNVectorCoordinate]
      rw [hfx, norm_smul, Real.norm_eq_abs, abs_of_pos hθpos]
      have hc1 : ‖c (ξ p x)‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        have hs : ∑ γ : SimonMultiIndex k N, ‖(c (ξ p x)) γ‖ ^ 2 = 1 := by
          rw [← hunitfact τ hτ]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rcases hξ with h | h
          · simp [hc, h, Real.norm_eq_abs, sq_abs]
          · simp [hc, h, Real.norm_eq_abs, sq_abs, euclideanNVectorCoordinate]
        rw [hs, Real.sqrt_one]
      rw [hc1, mul_one]
    · rw [indicator_of_notMem hxM]
      have : κ p x = 0 := by simp [hκ, hxM]
      simp [hf, this, hc, euclideanNVectorCoordinate]
      rfl
  -- limits of naturals
  have hnatlim : ∀ᵐ x ∂H, ∃ m : ℕ, ‖g x‖ = m ∧ ∀ᶠ p in atTop, (M p).indicator (θ p) x = m := by
    filter_upwards [hgae, ae_all_iff.2 hunit] with x hx hu
    have hnat : ∀ p, ∃ n : ℕ, (M p).indicator (θ p) x = n := by
      intro p
      by_cases hxM : x ∈ M p
      · rw [indicator_of_mem hxM]
        exact hNat p x hxM
      · exact ⟨0, by simp [indicator_of_notMem hxM]⟩
    choose n hn using hnat
    have hlim : Tendsto (fun p => (n p : ℝ)) atTop (𝓝 ‖g x‖) := by
      refine hx.norm.congr fun p => ?_
      rw [hu p, hn p]
    obtain ⟨P, hP⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)
    have hconst : ∀ p ≥ P, n p = n P := by
      intro p hp
      have h1 := hP p hp
      have h2 := hP P le_rfl
      rw [Real.dist_eq] at h1 h2
      have hlt : |(n p : ℝ) - n P| < 1 := by
        have := abs_sub_le (n p : ℝ) ‖g x‖ (n P)
        rw [abs_sub_comm ‖g x‖ (n P : ℝ)] at this
        linarith
      have hlt' : |((n p : ℤ) - n P : ℤ)| < 1 := by exact_mod_cast hlt
      have : ((n p : ℤ) - n P : ℤ) = 0 := Int.abs_lt_one_iff.mp hlt'
      omega
    refine ⟨n P, ?_, ?_⟩
    · refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
      exact eventually_atTop.2 ⟨P, fun p hp => by
        show (n P : ℝ) = n p
        rw [hconst p hp]⟩
    · exact eventually_atTop.2 ⟨P, fun p hp => by rw [hn p, hconst p hp]⟩
  -- the limit triple
  set θ₀ : Eucl N → ℝ := fun x => ((Nat.floor (‖g x‖ + 1 / 2) : ℕ) : ℝ) with hθ₀
  set M₀ : Set (Eucl N) := {x | 1 ≤ θ₀ x} with hM₀
  set e : SimonMultiIndex k N → NVector (Eucl N) k :=
    fun γ => simpleNVector (fun j => EuclideanSpace.single (γ j) (1 : ℝ)) with he
  set L : EuclideanSpace ℝ (SimonMultiIndex k N) → NVector (Eucl N) k :=
    fun a => ∑ γ, a γ • e γ with hL
  set ξ₀ : Eucl N → NVector (Eucl N) k := fun x => (θ₀ x)⁻¹ • L (g x) with hξ₀
  have hLc : ∀ w : NVector (Eucl N) k, L (c w) = w := by
    intro w
    ext α
    have h := (hPair N k w α).1
    rw [h]
    simp only [hL, hc, he, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, simpleNVector_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp [euclideanCovectorCoordinate, mul_comm]
    left; rfl
  have hθ₀g : ∀ᵐ x ∂H, θ₀ x = ‖g x‖ := by
    filter_upwards [hnatlim] with x hx
    obtain ⟨m, hm, -⟩ := hx
    simp only [hθ₀, hm]
    have : Nat.floor ((m : ℝ) + 1 / 2) = m := by
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> norm_num
    rw [this]
  have hfloor : Measurable (fun t : ℝ => ((Nat.floor t : ℕ) : ℝ)) := by
    have hm : Monotone (fun t : ℝ => ((Nat.floor t : ℕ) : ℝ)) := fun a b hab => by
      show ((Nat.floor a : ℕ) : ℝ) ≤ ((Nat.floor b : ℕ) : ℝ)
      exact_mod_cast Nat.floor_mono hab
    exact hm.measurable
  have hθ₀meas : AEMeasurable θ₀ H :=
    hfloor.comp_aemeasurable (hgmeas.norm.aemeasurable.add_const _)
  have hM₀meas : NullMeasurableSet M₀ H :=
    hθ₀meas.nullMeasurableSet_preimage measurableSet_Ici
  have hθ₀1 : ∀ x ∈ M₀, 1 ≤ θ₀ x := fun x hx => hx
  have hθ₀int : ∀ K : Set (Eucl N), IsCompact K → IntegrableOn θ₀ (M₀ ∩ K) H := by
    intro K hK
    obtain ⟨p, hp⟩ : ∃ p, ∫⁻ x, ‖f p x - g x‖ₑ ∂H < ∞ := by
      obtain ⟨p, hp⟩ := (hgL1.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
      exact ⟨p, hp.trans ENNReal.one_lt_top⟩
    have hfpK : ∫⁻ x in K, ‖f p x‖ₑ ∂H < ∞ := by
      have hint : IntegrableOn (θ p) (M p ∩ K) H := (hTri p).integrableOn K hK (subset_univ K)
      have hae : ∀ᵐ x ∂(H.restrict K), ‖f p x‖ₑ = (M p).indicator (fun y => ‖θ p y‖ₑ) x := by
        filter_upwards [ae_restrict_of_ae (hunit p)] with x hx
        rw [← ofReal_norm, hx, ← enorm_indicator_eq_indicator_enorm, ← ofReal_norm]
        congr 1
        rw [Real.norm_eq_abs, abs_of_nonneg]
        by_cases hxM : x ∈ M p
        · rw [indicator_of_mem hxM]
          exact ((hTri p).pos x hxM).le
        · rw [indicator_of_notMem hxM]
      rw [lintegral_congr_ae hae, lintegral_indicator₀
        ((hTri p).nullMeasurableSet.mono Measure.restrict_le_self),
        Measure.restrict_restrict₀ ((hTri p).nullMeasurableSet.mono Measure.restrict_le_self)]
      exact hint.hasFiniteIntegral
    have hθ₀ae : ∀ᵐ x ∂(H.restrict (M₀ ∩ K)), ‖θ₀ x‖ₑ ≤ ‖g x‖ₑ := by
      filter_upwards [ae_restrict_of_ae hθ₀g] with x hx
      rw [hx]
      simp
    refine ⟨hθ₀meas.aestronglyMeasurable.restrict, ?_⟩
    calc ∫⁻ x in M₀ ∩ K, ‖θ₀ x‖ₑ ∂H ≤ ∫⁻ x in M₀ ∩ K, ‖g x‖ₑ ∂H := lintegral_mono_ae hθ₀ae
      _ ≤ ∫⁻ x in K, ‖g x‖ₑ ∂H := lintegral_mono_set inter_subset_right
      _ ≤ ∫⁻ x in K, (‖f p x‖ₑ + ‖f p x - g x‖ₑ) ∂H := lintegral_mono fun x => by
            calc ‖g x‖ₑ = ‖f p x - (f p x - g x)‖ₑ := by rw [sub_sub_cancel]
              _ ≤ ‖f p x‖ₑ + ‖f p x - g x‖ₑ := enorm_sub_le
      _ = ∫⁻ x in K, ‖f p x‖ₑ ∂H + ∫⁻ x in K, ‖f p x - g x‖ₑ ∂H :=
            lintegral_add_left' (hfmeas p).enorm.restrict _
      _ < ∞ := ENNReal.add_lt_top.2 ⟨hfpK, (setLIntegral_le_lintegral _ _).trans_lt hp⟩
  have hLcont : Continuous L := by
    have : ContinuousAdd (NVector (Eucl N) k) :=
      ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl N) k)).continuous_add⟩
    simp only [hL]
    fun_prop
  have hpt : ∀ᵐ x ∂(H.restrict M₀), (∀ᶠ p in atTop, x ∈ M p) ∧
      Tendsto (fun p => ξ p x) atTop (𝓝 (ξ₀ x)) := by
    have hmem : ∀ᵐ x ∂(H.restrict M₀), x ∈ M₀ := ae_restrict_mem₀ hM₀meas
    filter_upwards [hmem, ae_restrict_of_ae hnatlim, ae_restrict_of_ae hgae,
      ae_restrict_of_ae hθ₀g] with x hxM₀ hnx hgx hθx
    obtain ⟨m, hm, hev⟩ := hnx
    have hθ₀m : θ₀ x = m := by rw [hθx, hm]
    have hm1 : (1 : ℝ) ≤ m := hθ₀m ▸ hxM₀
    have hev' : ∀ᶠ p in atTop, x ∈ M p ∧ θ p x = θ₀ x := by
      filter_upwards [hev] with p hp
      have hne : (M p).indicator (θ p) x ≠ 0 := by
        rw [hp]
        exact (lt_of_lt_of_le one_pos hm1).ne'
      have hxp : x ∈ M p := by
        by_contra h
        exact hne (indicator_of_notMem h _)
      exact ⟨hxp, by rw [← indicator_of_mem hxp (θ p), hp, hθ₀m]⟩
    refine ⟨hev'.mono fun p hp => hp.1, ?_⟩
    have hθ₀ne : θ₀ x ≠ 0 := by
      rw [hθ₀m]
      exact (lt_of_lt_of_le one_pos hm1).ne'
    have hconv : Tendsto (fun p => (θ₀ x)⁻¹ • L (f p x)) atTop (𝓝 ((θ₀ x)⁻¹ • L (g x))) :=
      ((hLcont.tendsto _).comp hgx).const_smul _
    refine hconv.congr' ?_
    filter_upwards [hev'] with p hp
    have hκx : κ p x = θ₀ x • ξ p x := by
      simp only [hκ, indicator_of_mem hp.1, hp.2]
    show (θ₀ x)⁻¹ • L (c (κ p x)) = ξ p x
    rw [hLc, hκx, smul_smul, inv_mul_cancel₀ hθ₀ne, one_smul]
  have hTri₀ : IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ :=
    hOrient N k M θ ξ M₀ θ₀ ξ₀ hTri hθ1 hM₀meas hθ₀1 hθ₀int hpt
  refine ⟨M₀, θ₀, ξ₀, hTri₀, fun x _ => ⟨_, rfl⟩, fun ω hωc hωs => ?_⟩
  -- convergence of the τ-actions
  have hint : ∀ p, IntegrableOn (fun x => θ p x * ξ p x (ω x)) (M p) H := fun p =>
    (hTau N k univ (M p) (θ p) (ξ p) (hTri p)).2 ω hωc hωs (subset_univ _)
  have hint₀ : IntegrableOn (fun x => θ₀ x * ξ₀ x (ω x)) M₀ H :=
    (hTau N k univ M₀ θ₀ ξ₀ hTri₀).2 ω hωc hωs (subset_univ _)
  -- a uniform bound for |ω|
  have hnormc : Continuous fun x => covectorEuclideanNorm (ω x) := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((continuous_eval_const _).comp hωc).pow 2
    · exact continuous_const
  have hsupp : HasCompactSupport (fun x => covectorEuclideanNorm (ω x)) := by
    refine hωs.mono fun x hx => ?_
    rw [Function.mem_support] at hx ⊢
    intro h
    apply hx
    rw [h]
    exact covectorEuclideanNorm_zero N k
  obtain ⟨C₀, hC₀⟩ := hnormc.bddAbove_range_of_hasCompactSupport hsupp
  set C : ℝ := max C₀ 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCb : ∀ x, covectorEuclideanNorm (ω x) ≤ C := fun x =>
    (hC₀ ⟨x, rfl⟩).trans (le_max_left _ _)
  -- the τ-actions as integrals of the densities
  have hκapp : ∀ p x, κ p x (ω x) = (M p).indicator (fun y => θ p y * ξ p y (ω y)) x := by
    intro p x
    by_cases hx : x ∈ M p
    · simp [hκ, hx]
    · simp [hκ, hx]
  set κ₀ : Eucl N → NVector (Eucl N) k := M₀.indicator (fun y => θ₀ y • ξ₀ y) with hκ₀
  have hκ₀app : ∀ x, κ₀ x (ω x) = M₀.indicator (fun y => θ₀ y * ξ₀ y (ω y)) x := by
    intro x
    by_cases hx : x ∈ M₀
    · simp [hκ₀, hx]
    · simp [hκ₀, hx]
  have htau : ∀ p, tauAction k (M p) (θ p) (ξ p) ω = ∫ x, κ p x (ω x) ∂H := by
    intro p
    simp_rw [hκapp]
    rw [integral_indicator₀ (hTri p).nullMeasurableSet]
    rfl
  have htau₀ : tauAction k M₀ θ₀ ξ₀ ω = ∫ x, κ₀ x (ω x) ∂H := by
    simp_rw [hκ₀app]
    rw [integral_indicator₀ hM₀meas]
    rfl
  have hintp : ∀ p, Integrable (fun x => κ p x (ω x)) H := by
    intro p
    simp_rw [hκapp]
    exact (hint p).integrable_indicator₀ (hTri p).nullMeasurableSet
  have hint₀' : Integrable (fun x => κ₀ x (ω x)) H := by
    simp_rw [hκ₀app]
    exact hint₀.integrable_indicator₀ hM₀meas
  -- κ₀ = L ∘ g almost everywhere
  have hκ₀L : ∀ᵐ x ∂H, κ₀ x = L (g x) := by
    filter_upwards [hθ₀g] with x hx
    by_cases hxM : x ∈ M₀
    · have hne : θ₀ x ≠ 0 := (lt_of_lt_of_le one_pos (show (1 : ℝ) ≤ θ₀ x from hxM)).ne'
      simp only [hκ₀, indicator_of_mem hxM, hξ₀, smul_smul, mul_inv_cancel₀ hne, one_smul]
    · have hlt : θ₀ x < 1 := not_le.mp hxM
      have h0 : θ₀ x = 0 := by
        have hfl : Nat.floor (‖g x‖ + 1 / 2) < 1 := by
          have : ((Nat.floor (‖g x‖ + 1 / 2) : ℕ) : ℝ) < 1 := hlt
          exact_mod_cast this
        simp only [hθ₀, Nat.lt_one_iff.mp hfl, Nat.cast_zero]
      have hg0 : g x = 0 := by
        rw [h0] at hx
        exact norm_eq_zero.mp hx.symm
      simp only [hκ₀, indicator_of_notMem hxM, hg0, hL]
      simp
  have hLsub : ∀ a b : EuclideanSpace ℝ (SimonMultiIndex k N), L (a - b) = L a - L b := by
    intro a b
    ext α
    simp [hL, sub_mul, Finset.sum_sub_distrib]
  have hLbound : ∀ (a : EuclideanSpace ℝ (SimonMultiIndex k N)) (α : Covector (Eucl N) k),
      |L a α| ≤ (Fintype.card (SimonMultiIndex k N) : ℝ) * ‖a‖ * covectorEuclideanNorm α := by
    intro a α
    have hexp : L a α = ∑ γ, a γ * euclideanCovectorCoordinate α γ := by
      simp [hL, he, euclideanCovectorCoordinate]
    rw [hexp]
    calc |∑ γ, a γ * euclideanCovectorCoordinate α γ|
        ≤ ∑ γ, |a γ * euclideanCovectorCoordinate α γ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _γ : SimonMultiIndex k N, ‖a‖ * covectorEuclideanNorm α := by
          refine Finset.sum_le_sum fun γ _ => ?_
          rw [abs_mul]
          exact mul_le_mul (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le a γ)
            ((hPair N k 0 α).2 γ) (abs_nonneg _) (norm_nonneg _)
      _ = (Fintype.card (SimonMultiIndex k N) : ℝ) * ‖a‖ * covectorEuclideanNorm α := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  set m : ℝ := (Fintype.card (SimonMultiIndex k N) : ℝ) with hm
  have hL1 : Tendsto (fun p => ∫⁻ x, ‖κ p x (ω x) - κ₀ x (ω x)‖ₑ ∂H) atTop (𝓝 0) := by
    have hb : ∀ p, ∫⁻ x, ‖κ p x (ω x) - κ₀ x (ω x)‖ₑ ∂H ≤
        ENNReal.ofReal (m * C) * ∫⁻ x, ‖f p x - g x‖ₑ ∂H := by
      intro p
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [hκ₀L] with x hx
      have hdiff : κ p x (ω x) - κ₀ x (ω x) = L (f p x - g x) (ω x) := by
        rw [hx, hLsub]
        show κ p x (ω x) - L (g x) (ω x) = (L (c (κ p x)) - L (g x)) (ω x)
        rw [hLc]
        rfl
      rw [hdiff, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.norm_eq_abs]
      calc |L (f p x - g x) (ω x)| ≤ m * ‖f p x - g x‖ * covectorEuclideanNorm (ω x) :=
            hLbound _ _
        _ ≤ m * ‖f p x - g x‖ * C := by
            gcongr
            exact hCb x
        _ = m * C * ‖f p x - g x‖ := by ring
    have hlim : Tendsto (fun p => ENNReal.ofReal (m * C) * ∫⁻ x, ‖f p x - g x‖ₑ ∂H) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hgL1 (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun p => bot_le) hb
  rw [htau₀]
  simp_rw [htau]
  exact tendsto_integral_of_L1 _ hint₀'.aestronglyMeasurable (Eventually.of_forall hintp) hL1
```

## Key steps

1. Coordinates f_p := c∘κ_p ∈ ℝ^I are a.e. strongly measurable (tau_integrable (a)); Σ∫‖f_{p+1} − f_p‖ < ∞ is the hypothesis; ‖f_p‖ = 1_{M_p}θ_p a.e. by orientation and the Cauchy–Binet unit fact (pairing expansion).
2. l1_cauchy_limit gives g with f_p → g a.e. and in L¹.
3. ‖g(x)‖ is a.e. a limit of natural numbers, hence the sequence is eventually constant: θ₀ := ⌊‖g‖ + 1/2⌋₊ = ‖g‖ a.e. and 1_{M_p}θ_p(x) = θ₀(x) for large p.
4. M₀ := {θ₀ ≥ 1}, ξ₀ := θ₀⁻¹L(g): null-measurability, local integrability (‖g‖ ≤ ‖f_p‖ + ‖f_p − g‖), and for a.e. x ∈ M₀ eventually x ∈ M_p with ξ_p(x) = θ₀(x)⁻¹L(f_p(x)) → ξ₀(x), using L∘c = id (pairing expansion).
5. limit_triple makes (M₀, θ₀, ξ₀) a rectifiable triple with natural multiplicity.
6. κ₀ = L(g) a.e. and |L(a)(α)| ≤ m‖a‖|α| give ∫⁻|κ_p(ω) − κ₀(ω)| ≤ mC∫⁻‖f_p − g‖ → 0; tau_integrable (b) and tendsto_integral_of_L1 give convergence of the τ-actions.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp workspaces/gmt-ch06/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean; cmp <snapshot>/project/GMT/Ch06/Contract.lean <snapshot>/project/GMT/Ch06/Submission.lean (all byte-identical)`
- `grep '^import' <snapshot>/project/GMT/Ch06/Contract.lean (8 imports) and a transitive SimonGMT import-closure walk (13 modules; Chapter01.Lusin not included)`
- `rg -n 'theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le|exists_hasCompactSupport_integral_sub_le' <snapshot>/mathlib/Mathlib (ContinuousMapDense.lean:141, :226); rg -n 'theorem ContinuousMap.exists_extension' <snapshot>/mathlib/Mathlib (TietzeExtension.lean:77): both files are outside the frozen closure`
- `rg -n 'theorem cauchySeq_of_edist_le_of_tsum_ne_top|theorem edist_le_tsum_of_edist_le_of_tendsto|theorem tendsto_integral_of_L1|theorem lintegral_tsum|theorem integral_indicator₀|theorem dist_convolution_le|theorem exists_continuous_zero_one_of_isClosed' <snapshot>/mathlib/Mathlib`
- `rg -n 'imc_' <snapshot>/project <snapshot>/mathlib and lake-packages-25730c7c/simongmt (no match); git log --all -S <each new imc_ name> (no commit); grep of the new names over runs/*/nodes (no match)`
- `python3 -I over dag.json: status, candidate commit, parent and lean_statement of the five reused names and of lpf_wtc_ae_zero_density_off_set; comparison of every new child type against all DAG node types (no duplicate); simulation of runtime.py _existing_lean_name_problem/_accepted_checkpoint and _topological on the current DAG (no problem; acyclic)`
- `sed -n 6532,6575p /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py (reuse rule), leaf_verification.py check_source_delta (no set_option in a leaf delta), decomposition_scope.py (recomputed parent_contract_digest 94deade2…)`
- `git show 12d217bba2a4:GMT/Ch06/Submission.lean (accepted zero-density proof) and git show 83e1f61809c1:GMT/Ch06/Submission.lean (accepted fiw_im_mass_formula: inline L¹ density and mollification)`
- `lake env lean /tmp/imc_v2/lean/Avail2.lean, Api3–Api7.lean (closure probes: Tietze, ContinuousMapDense, UniformContinuous.exists_contDiff_dist_le and Measurable.nat_floor absent; ContDiffBump, HasCompactSupport.contDiff_convolution_left and Lp.ae_tendsto_of_cauchy_eLpNorm present; NVector ContinuousAdd/PseudoMetrizableSpace workarounds)`
- `python3 -I /tmp/imc_v2/scripts/build_stmts.py (validate_lean_statement on all 13 types) and lake env lean /tmp/imc_v2/lean/Stmts.lean (all elaborate; only sorry warnings)`
- `lake env lean /tmp/imc_v2/lean/Test_deformation_im_completeness.lean, Test_imc_im_density_limit.lean, Test_imc_isRectifiableTriple_of_eventually_mem.lean, Test_imc_ae_tendsto_of_summable_lintegral.lean, Test_imc_ae_zero_density_off_set.lean (all compile at default heartbeats; standard axioms plus the stand-in sibling axioms)`
- `sed -n 560,735p book/sources/chapter-01-source.txt (Simon Ch. 1, 3.3–3.7 and the 5-times covering lemma)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/TietzeExtension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-zero-3299c8304e/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-pairing-expansion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-local-to-global-im-a1-tau-integrable-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-lusi-5c440af24d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-frame-sign-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-blow-7c8d1035a6/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-mass-formula-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-01-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/decomposition_scope.py`
- `/tmp/imc_v2/lean/Stmts.lean`
- `/tmp/imc_v2/lean/Test_deformation_im_completeness.lean`
- `/tmp/imc_v2/lean/Test_imc_im_density_limit.lean`
- `/tmp/imc_v2/lean/Test_imc_isRectifiableTriple_of_eventually_mem.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_tendsto_of_summable_lintegral.lean`
- `/tmp/imc_v2/lean/Test_imc_ae_zero_density_off_set.lean`

Pinned revisions confirmed: the frozen contract is byte-identical to the snapshot (Submission = Contract). The frozen import closure lacks Tietze (TietzeExtension.lean), L¹ density of C_c (ContinuousMapDense.lean) and SimonGMT Lusin. So mass_lower_bound's approximation step is proved inline from regularity, Urysohn and MemLp.induction_dense, as the accepted fiw_im_mass_formula does. Mathlib supplies the Riesz–Fischer and limit tools used by l1_cauchy_limit and density_limit (cauchySeq_of_edist_le_of_tsum_ne_top, edist_le_tsum_of_edist_le_of_tendsto, tendsto_integral_of_L1). Following the correction, the zero-density child uses the fresh name imc_ae_zero_density_off_set and is the W = ℝ^Q case of the accepted lpf_wtc_ae_zero_density_off_set; its Lean proof embeds that accepted proof (commit 12d217bb) and compiles. The five reused names are accepted checkpoints with identical types, and the controller's name check simulated on the current DAG passes. All 13 types validate and elaborate in the comparator scope. The parent compiles from mass_lower_bound, density_limit and tau_integrable; density_limit, limit_triple and l1_cauchy_limit also compile from their siblings; all at default heartbeats with axioms propext, Classical.choice and Quot.sound only. No imc_ name occurs in the project, SimonGMT, Mathlib, git history or the DAG.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
