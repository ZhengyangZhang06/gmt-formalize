<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.local_graph-a1 -->

## Theorem `Submission.slicing_im_st_lsc_local_graph`

Let m ∈ ℕ, h : ℝ^{m+1} → ℝ of class C¹, U ⊆ ℝ^{m+1} open and w₀ ∈ U with Dh(w₀) ≠ 0 (ℝ^k = EuclideanSpace ℝ (Fin k), Dh(w) = fderiv ℝ h w, B(0, r) the open ball in ℝ^m). Then there are a C¹ map ψ : ℝ^m → ℝ^{m+1}, a radius r > 0 and an open set W ⊆ ℝ^{m+1} with w₀ ∈ W such that: (i) |v − v′| ≤ |ψ(v) − ψ(v′)| for all v, v′ ∈ ℝ^m; (ii) for every v ∈ B(0, r): ψ(v) ∈ U, h(ψ(v)) = h(w₀) and Dh(ψ(v)) ≠ 0; (iii) for every w ∈ W with h(w) = h(w₀) there is v ∈ B(0, r) with ψ(v) = w.

Node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.local_graph-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3419

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4118, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4123

Decomposition children: None

## Lean problem

Declaration: `Submission.slicing_im_st_lsc_local_graph`

```lean
∀ (m : ℕ) (h : Eucl (m + 1) → ℝ) (U : Set (Eucl (m + 1))) (w₀ : Eucl (m + 1)), ContDiff ℝ 1 h → IsOpen U → w₀ ∈ U → fderiv ℝ h w₀ ≠ 0 → ∃ (ψ : Eucl m → Eucl (m + 1)) (r : ℝ) (W : Set (Eucl (m + 1))), ContDiff ℝ 1 ψ ∧ 0 < r ∧ IsOpen W ∧ w₀ ∈ W ∧ (∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖) ∧ (∀ v ∈ ball (0 : Eucl m) r, ψ v ∈ U ∧ h (ψ v) = h w₀ ∧ fderiv ℝ h (ψ v) ≠ 0) ∧ ∀ w ∈ W, h w = h w₀ → ∃ v ∈ ball (0 : Eucl m) r, ψ v = w
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.local_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1–5 of the parent proof (slicing_im_st_level_set_charts): local graph parametrization at a regular point w₀ by the implicit function theorem for H(v, s) = h(w₀ + ι₀v + se), globalization of the implicit function g by a bump function, the Pythagorean lower bound, the choice of the chart domain, and the identification of the level set inside W with ψ(V). The open set U plays the role of Ω, and the frame (ι₀, e) together with the inverse of (v, s) ↦ ι₀v + se is supplied by the sibling kernel_frame; the bump-function globalization is the sibling c1_extension.

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩ (inner ℝ) and Euclidean norm |·|; B(x, r) = ball x r is the open ball; Df(x) := fderiv ℝ f x for a map f. On ℝ^m × ℝ we use the product (max) norm, so the ball of radius ε about (0, 0) is B(0, ε) × (−ε, ε) (ball_prod_same).

1. (Frame.) Put ℓ := Dh(w₀) ≠ 0. By the sibling kernel_frame (slicing_im_st_lsc_kernel_frame applied to m and ℓ) there are continuous linear maps ι : ℝ^m → ℝ^{m+1}, p : ℝ^{m+1} → ℝ^m and a vector e ∈ ℝ^{m+1} with
   (F1) ℓ(e) = 1; (F2) |ι(v)| = |v| for all v; (F3) ⟨ι(v), e⟩ = 0 for all v; (F4) ι(p(u)) + ℓ(u)e = u for all u.

2. (The implicit equation.) Let L : ℝ^m × ℝ → ℝ^{m+1} be the continuous linear map L(v, s) := ι(v) + s·e (ι ∘ fst + snd.smulRight e), let A(q) := w₀ + L(q), so A(v, s) = w₀ + ι(v) + s·e, and let H := h ∘ A : ℝ^m × ℝ → ℝ.
   - A is affine with derivative L at every point, and A(0, 0) = w₀.
   - H is C¹ as the composition of the C¹ map h with the C¹ (affine) map A, and H(0, 0) = h(w₀).
   - By the chain rule DH(0, 0) = Dh(A(0, 0)) ∘ L = ℓ ∘ L. Its restriction to the second factor, DH(0, 0) ∘ inr : ℝ → ℝ, is s ↦ ℓ(L(0, s)) = ℓ(ι(0) + s·e) = s·ℓ(e) = s by (F1); it is the identity of ℝ, which is invertible (it is the continuous linear equivalence ContinuousLinearEquiv.refl ℝ ℝ).

3. (Implicit function theorem.) Apply the C¹ implicit function theorem of Mathlib (ContDiffAt.implicitFunction from Mathlib.Analysis.Calculus.ImplicitContDiff) to H, which is C¹ at u := (0, 0), with n := 1 ≠ 0 and the invertible partial derivative of step 2. It provides a function g : ℝ^m → ℝ such that
   (I1) g(0) = 0 (ContDiffAt.implicitFunction_apply_self: g(u.1) = u.2);
   (I2) g is C¹ at 0 (ContDiffAt.contDiffAt_implicitFunction);
   (I3) for all (v, s) in some neighbourhood N₀ of (0, 0): H(v, s) = H(0, 0) ⟺ g(v) = s (ContDiffAt.eventually_apply_eq_iff_implicitFunction).
   Choose ε > 0 with B((0, 0), ε) = B(0, ε) × (−ε, ε) ⊆ N₀ (Metric.mem_nhds_iff).

4. (Globalization of g and definition of ψ.) By (I2) and the sibling c1_extension (slicing_im_st_lsc_c1_extension applied to m, g and x := 0) there are ρ > 0 and a function g̃ : ℝ^m → ℝ of class C¹ on ℝ^m with g̃(v) = g(v) for all v ∈ B(0, ρ). Define ψ(v) := w₀ + ι(v) + g̃(v)·e. ψ is C¹ (a constant plus a continuous linear map plus the C¹ scalar function g̃ times the constant vector e). Since 0 ∈ B(0, ρ), g̃(0) = g(0) = 0 by (I1), so ψ(0) = w₀.

5. (Conclusion (i): ψ is 1-antilipschitz on ℝ^m.) Let v, v′ ∈ ℝ^m and put d := g̃(v) − g̃(v′). By linearity of ι, ψ(v) − ψ(v′) = ι(v − v′) + d·e, and ⟨ι(v − v′), d·e⟩ = d·⟨ι(v − v′), e⟩ = 0 by (F3). By the Pythagorean identity (norm_add_sq_real) and (F2),
   |ψ(v) − ψ(v′)|² = |ι(v − v′)|² + 2·0 + |d·e|² = |v − v′|² + |d·e|² ≥ |v − v′|².
   As |ψ(v) − ψ(v′)| ≥ 0, taking square roots gives |v − v′| ≤ |ψ(v) − ψ(v′)| (le_of_sq_le_sq).

6. (Choice of r.) Let O := U ∩ {w : Dh(w) ≠ 0}. Since h is C¹, Dh is continuous (ContDiff.continuous_fderiv), so {w : Dh(w) ≠ 0} is open, and O is open; w₀ ∈ O because w₀ ∈ U and Dh(w₀) ≠ 0. As ψ is continuous with ψ(0) = w₀ ∈ O, we have ψ(v) ∈ O for all v in a neighbourhood of 0. As g is continuous at 0 (by (I2)) with g(0) = 0, we have |g(v)| < ε for all v in a neighbourhood of 0. Choose r₀ > 0 such that both properties hold for all v ∈ B(0, r₀), and put r := min(r₀, ρ, ε) > 0. So r ≤ r₀, r ≤ ρ and r ≤ ε.

7. (Conclusion (ii).) Let v ∈ B(0, r).
   - Since v ∈ B(0, r₀): ψ(v) ∈ U, Dh(ψ(v)) ≠ 0 and |g(v)| < ε.
   - Since |v| < r ≤ ε and |g(v)| < ε, (v, g(v)) ∈ B(0, ε) × (−ε, ε) ⊆ N₀. Trivially g(v) = g(v), so (I3) gives H(v, g(v)) = H(0, 0) = h(w₀).
   - Since |v| < r ≤ ρ, g̃(v) = g(v), hence ψ(v) = w₀ + ι(v) + g(v)·e = A(v, g(v)) and h(ψ(v)) = H(v, g(v)) = h(w₀).

8. (The open set W.) Let W := {w ∈ ℝ^{m+1} : p(w − w₀) ∈ B(0, r) and ℓ(w − w₀) ∈ (−ε, ε)}. W is the intersection of the preimages of the open balls B(0, r) ⊆ ℝ^m and B(0, ε) ⊆ ℝ under the continuous maps w ↦ p(w − w₀) and w ↦ ℓ(w − w₀); hence W is open. Since p(0) = 0, ℓ(0) = 0 and r, ε > 0, w₀ ∈ W. (By (F4), w = A(p(w − w₀), ℓ(w − w₀)) for every w, so W = A(B(0, r) × (−ε, ε)), the open neighbourhood called W in Step 4 of the parent proof; only the identity (F4) is used below.)

9. (Conclusion (iii).) Let w ∈ W with h(w) = h(w₀). Put v := p(w − w₀) ∈ B(0, r) and s := ℓ(w − w₀) ∈ (−ε, ε).
   - By (F4) applied to u := w − w₀, ι(v) + s·e = w − w₀, so A(v, s) = w₀ + ι(v) + s·e = w.
   - Since |v| < r ≤ ε, (v, s) ∈ B(0, ε) × (−ε, ε) ⊆ N₀, and H(v, s) = h(A(v, s)) = h(w) = h(w₀) = H(0, 0). By (I3), g(v) = s.
   - Since |v| < r ≤ ρ, g̃(v) = g(v) = s, so ψ(v) = w₀ + ι(v) + s·e = A(v, s) = w.
   Thus v ∈ B(0, r) and ψ(v) = w.

10. (Conclusion.) ψ is C¹ (step 4), r > 0 (step 6), W is open with w₀ ∈ W (step 8), and (i), (ii), (iii) hold by steps 5, 7 and 9. For m = 0 every step holds verbatim: ℝ⁰ = {0}, ι = 0, p = 0, ψ is the constant w₀, W = {w : |ℓ(w − w₀)| < ε}, and (iii) says that w₀ is the only point of W on the level set {h = h(w₀)}. ∎

Lean remark. Mathlib's C¹ implicit function theorem (ContDiffAt.implicitFunction and its API) lives in Mathlib.Analysis.Calculus.ImplicitContDiff, which is NOT reachable from the frozen imports of GMT/Ch06/Submission.lean; add the line `import Mathlib.Analysis.Calculus.ImplicitContDiff` to the import block of GMT/Ch06/Submission.lean. This is allowed: gmt-compare.py byte-checks every frozen input except GMT/Ch06/Submission.lean (frozen_inputs removes it from the expected set) and places no restriction on its imports; earlier accepted candidates added Poincare.* imports, this is the first Mathlib import, and the pinned package tree contains its olean. A full gmt-compare.py run on a simulated DAG entry for this child accepted it ("Your solution is okay!"). Adding the import changes none of the frozen GMT.Ch06 declarations (type/value hashes were compared with and without it). Keep this import line when the Submission.lean of this child is merged with other branches; the other children of this decomposition compile with the frozen imports alone. With that import, the following proof was verified (Lean v4.35.0-rc3, Mathlib 25730c7c) as the declaration `theorem Submission.slicing_im_st_lsc_local_graph : (<frozen statement>) := by` placed after the `end` of the `noncomputable section` and before `main_theorem` inside `namespace GMT.Ch06`, after the sibling declarations Submission.slicing_im_st_lsc_kernel_frame and Submission.slicing_im_st_lsc_c1_extension. Axioms: propext, Classical.choice, Quot.sound. The comparator-style check `exact Submission.slicing_im_st_lsc_local_graph` against the frozen type in the contract scope also passed.
  have hKF := Submission.slicing_im_st_lsc_kernel_frame
  have hC1E := Submission.slicing_im_st_lsc_c1_extension
  intro m h U w₀ hh hU hw₀ hdh
  obtain ⟨ι, p, e, hℓe, hιn, hιe, hdec⟩ := hKF m (fderiv ℝ h w₀) hdh
  set ℓ := fderiv ℝ h w₀ with hℓdef
  let L : Eucl m × ℝ →L[ℝ] Eucl (m + 1) :=
    ι.comp (ContinuousLinearMap.fst ℝ (Eucl m) ℝ) + (ContinuousLinearMap.snd ℝ (Eucl m) ℝ).smulRight e
  let A : Eucl m × ℝ → Eucl (m + 1) := fun q => w₀ + L q
  have hAapp : ∀ q : Eucl m × ℝ, A q = w₀ + ι q.1 + q.2 • e := by
    intro q
    simp [A, L, add_assoc]
  let H : Eucl m × ℝ → ℝ := fun q => h (A q)
  have hAd : ∀ q, HasFDerivAt A L q := fun q => (L.hasFDerivAt).const_add w₀
  have hA0 : A (0, 0) = w₀ := by
    rw [hAapp]
    simp
  have hH : ContDiff ℝ 1 H := hh.comp (contDiff_const.add L.contDiff)
  have hHd : HasFDerivAt H (ℓ.comp L) ((0 : Eucl m), (0 : ℝ)) := by
    have h1 := (hh.differentiable one_ne_zero (A (0, 0))).hasFDerivAt.comp ((0 : Eucl m), (0 : ℝ)) (hAd (0, 0))
    rw [hA0] at h1
    exact h1
  have hcomp : fderiv ℝ H ((0 : Eucl m), (0 : ℝ)) ∘L ContinuousLinearMap.inr ℝ (Eucl m) ℝ =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [hHd.fderiv]
    ext
    simp [L, hℓe]
  have hinv : (fderiv ℝ H ((0 : Eucl m), (0 : ℝ)) ∘L ContinuousLinearMap.inr ℝ (Eucl m) ℝ).IsInvertible := by
    rw [hcomp]
    exact ⟨ContinuousLinearEquiv.refl ℝ ℝ, rfl⟩
  have hHat : ContDiffAt ℝ 1 H ((0 : Eucl m), (0 : ℝ)) := hH.contDiffAt
  set g := hHat.implicitFunction one_ne_zero hinv with hgdef
  have hg0 : g 0 = 0 := hHat.implicitFunction_apply_self one_ne_zero hinv
  have hgC1 : ContDiffAt ℝ 1 g 0 := hHat.contDiffAt_implicitFunction one_ne_zero hinv
  have hiff := hHat.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 hiff
  obtain ⟨ρ, hρ, g', hg'C, hg'eq⟩ := hC1E m g 0 hgC1
  let ψ : Eucl m → Eucl (m + 1) := fun v => w₀ + ι v + g' v • e
  have hψC : ContDiff ℝ 1 ψ := (contDiff_const.add ι.contDiff).add (hg'C.smul contDiff_const)
  have hψ0 : ψ 0 = w₀ := by
    simp [ψ, hg'eq 0 (mem_ball_self hρ), hg0]
  have hanti : ∀ v v' : Eucl m, ‖v - v'‖ ≤ ‖ψ v - ψ v'‖ := by
    intro v v'
    have hdiff : ψ v - ψ v' = ι (v - v') + (g' v - g' v') • e := by
      simp only [ψ, map_sub, sub_smul]
      abel
    have horth : inner ℝ (ι (v - v')) ((g' v - g' v') • e) = 0 := by
      rw [inner_smul_right, hιe, mul_zero]
    have hsq : ‖ψ v - ψ v'‖ ^ 2 = ‖v - v'‖ ^ 2 + ‖(g' v - g' v') • e‖ ^ 2 := by
      rw [hdiff, norm_add_sq_real, horth, hιn]
      ring
    have hle : ‖v - v'‖ ^ 2 ≤ ‖ψ v - ψ v'‖ ^ 2 := by
      rw [hsq]
      nlinarith [sq_nonneg ‖(g' v - g' v') • e‖]
    exact le_of_sq_le_sq hle (norm_nonneg _)
  have hopen : IsOpen (U ∩ {w | fderiv ℝ h w ≠ 0}) :=
    hU.inter (isOpen_ne_fun (hh.continuous_fderiv one_ne_zero) continuous_const)
  have h1 : ∀ᶠ v in 𝓝 (0 : Eucl m), ψ v ∈ U ∩ {w | fderiv ℝ h w ≠ 0} := by
    apply hψC.continuous.continuousAt.preimage_mem_nhds
    rw [hψ0]
    exact hopen.mem_nhds ⟨hw₀, hdh⟩
  have h2 : ∀ᶠ v in 𝓝 (0 : Eucl m), g v ∈ ball (0 : ℝ) ε := by
    apply hgC1.continuousAt.preimage_mem_nhds
    rw [hg0]
    exact ball_mem_nhds _ hε
  obtain ⟨r₀, hr₀, hr₀ball⟩ := Metric.mem_nhds_iff.1 (h1.and h2)
  set r := min r₀ (min ρ ε) with hrdef
  have hr : 0 < r := lt_min hr₀ (lt_min hρ hε)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrρ : r ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  let W : Set (Eucl (m + 1)) := {w | p (w - w₀) ∈ ball (0 : Eucl m) r ∧ ℓ (w - w₀) ∈ ball (0 : ℝ) ε}
  have hWo : IsOpen W := by
    apply IsOpen.inter
    · exact isOpen_ball.preimage (p.continuous.comp (continuous_id.sub continuous_const))
    · exact isOpen_ball.preimage (ℓ.continuous.comp (continuous_id.sub continuous_const))
  have hw₀W : w₀ ∈ W := by
    simp [W, hr, hε]
  refine ⟨ψ, r, W, hψC, hr, hWo, hw₀W, hanti, ?_, ?_⟩
  · intro v hv
    have hvr₀ : v ∈ ball (0 : Eucl m) r₀ := ball_subset_ball hrr₀ hv
    obtain ⟨⟨hU', hd'⟩, hgv⟩ := hr₀ball hvr₀
    refine ⟨hU', ?_, hd'⟩
    have hvρ : v ∈ ball (0 : Eucl m) ρ := ball_subset_ball hrρ hv
    have hvε : v ∈ ball (0 : Eucl m) ε := ball_subset_ball hrε hv
    have hq : ((v, g v) : Eucl m × ℝ) ∈ ball ((0 : Eucl m), (0 : ℝ)) ε := by
      rw [← ball_prod_same]
      exact ⟨hvε, hgv⟩
    have hHq : H (v, g v) = H ((0 : Eucl m), (0 : ℝ)) := (hεball hq).2 rfl
    have hψv : ψ v = A (v, g v) := by
      rw [hAapp]
      simp [ψ, hg'eq v hvρ]
    rw [hψv]
    simpa [H, hA0] using hHq
  · intro w hw hhw
    obtain ⟨hpw, hℓw⟩ := hw
    have hAw : A (p (w - w₀), ℓ (w - w₀)) = w := by
      rw [hAapp]
      have := hdec (w - w₀)
      simp only at this ⊢
      rw [add_assoc, this]
      abel
    have hvε : p (w - w₀) ∈ ball (0 : Eucl m) ε := ball_subset_ball hrε hpw
    have hq : ((p (w - w₀), ℓ (w - w₀)) : Eucl m × ℝ) ∈ ball ((0 : Eucl m), (0 : ℝ)) ε := by
      rw [← ball_prod_same]
      exact ⟨hvε, hℓw⟩
    have hHq : H (p (w - w₀), ℓ (w - w₀)) = H ((0 : Eucl m), (0 : ℝ)) := by
      simp only [H]
      rw [hAw, hA0]
      exact hhw
    have hgs : g (p (w - w₀)) = ℓ (w - w₀) := (hεball hq).1 hHq
    refine ⟨p (w - w₀), hpw, ?_⟩
    have hvρ : p (w - w₀) ∈ ball (0 : Eucl m) ρ := ball_subset_ball hrρ hpw
    calc ψ (p (w - w₀)) = w₀ + ι (p (w - w₀)) + g' (p (w - w₀)) • e := rfl
      _ = w₀ + ι (p (w - w₀)) + ℓ (w - w₀) • e := by rw [hg'eq _ hvρ, hgs]
      _ = A (p (w - w₀), ℓ (w - w₀)) := (hAapp (p (w - w₀), ℓ (w - w₀))).symm
      _ = w := hAw

## Key steps

1. Frame (ι, p, e) for ℓ = Dh(w₀) from kernel_frame: ℓ(e) = 1, ι isometric, ι(·) ⟂ e, ι(p(u)) + ℓ(u)e = u.
2. H(v, s) := h(w₀ + ι(v) + s·e) is C¹ with ∂ₛH(0, 0) = s ↦ s·ℓ(e) = id, invertible.
3. C¹ implicit function theorem: g(0) = 0, g C¹ at 0, and H(v, s) = h(w₀) ⟺ g(v) = s on B(0, ε) × (−ε, ε).
4. c1_extension: globally C¹ g̃ = g on B(0, ρ); ψ(v) := w₀ + ι(v) + g̃(v)e is C¹ with ψ(0) = w₀ and 1-antilipschitz by Pythagoras.
5. r := min(r₀, ρ, ε) with ψ(B(0, r)) ⊆ U ∩ {Dh ≠ 0} and |g| < ε on B(0, r); then h(ψ(v)) = h(w₀) on B(0, r).
6. W := {p(w − w₀) ∈ B(0, r), |ℓ(w − w₀)| < ε} is an open neighbourhood of w₀; for w ∈ W on the level set, w = A(p(w − w₀), ℓ(w − w₀)) and the implicit-function equivalence give w = ψ(p(w − w₀)).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch06/Contract.lean with the workspace Contract.lean (identical) and Contract.lean with Submission.lean (identical)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.json} (frozen type, Steps 0-9 of the supplied proof)`
- `python3 over dag.json: id/lean_name/status/lean_statement of all 476 nodes; grep -iE 'antilip|implicit|level|chart|graph|bump|c1_|immersion|orthonormal|isometry|kernel' over the name list; lean_statement scan for 'implicit', 'level set', 'LinearMap.ker'`
- `grep -c 'slicing_im_st_lsc_' (and each full new name) in dag.json DAG.md issue-workers.json dag.mmd; grep -rl 'slicing_im_st_lsc' nodes/ local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt/Poincare (no match)`
- `read decomposition-v1.json of root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1 (fiw_ims_frame_sign reuse convention) and of root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655 (earlier reuse of lpf_wtc_cat_fderiv_lower_bound, resolved to the accepted node in dag.json)`
- `read parent-supplied-natural-proof.{md,json} of root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9 (accepted proof and key steps of lpf_wtc_cat_fderiv_lower_bound); git show 8cfbc487a3d10545b0ea005ad58122242bbcc072 -- GMT/Ch06/Submission.lean (placement of accepted Submission.* declarations)`
- `rg in the Mathlib snapshot: ContDiffAt.implicitFunction, implicitFunction_apply_self, eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction, ContDiffAt.eventually, ContDiffBump (one_of_mem_closedBall, zero_of_le_dist, contDiffAt), hasContDiffBump_of_innerProductSpace, ContDiffOn.exists_lipschitzOnWith, TopologicalSpace.isOpen_iUnion_countable, Set.Countable.exists_eq_range, ContinuousLinearMap.IsInvertible, InnerProductSpace.toDual_symm_apply, stdOrthonormalBasis, OrthonormalBasis.reindex, ContinuousLinearMap.codRestrict, LinearMap.range_eq_top_of_ne_zero, LinearMap.finrank_range_of_inj, LinearMap.finrank_range_add_finrank_ker, Submodule.eq_of_le_of_finrank_eq, norm_add_sq_real, ball_prod_same, fderiv_comp, LinearMap.range_comp, Filter.EventuallyEq.fderiv_eq, ContDiff.continuous_fderiv, le_of_sq_le_sq, sq_le_sq₀`
- `lake env lean Check.lean: #check of the above after `import GMT.Ch06.Submission` (all available except ContDiffAt.implicitFunction* and LinearMap.range_eq_top_of_ne_zero; the former needs `import Mathlib.Analysis.Calculus.ImplicitContDiff`, whose olean is in lake-packages-25730c7c)`
- `gmt-compare.py contract_scope/child_modules (child scope: namespace GMT.Ch06 + contract opens, noncomputable section/end) and frozen_inputs/candidate_inputs (only GMT/Ch06/Submission.lean is not byte-frozen; imports unrestricted); import lines of 398 branch heads (earlier accepted candidates added Poincare.* imports)`
- `python3 -I validate.py: lean_contract.validate_lean_statement on the parent and the 5 child statements (all returned unchanged)`
- `lake env lean Stmts.lean (all child types elaborate in the comparator child scope); Assembly.lean (frozen parent type from the local_graph and tangent_range types as hypotheses: axioms propext, Classical.choice, Quot.sound); KernelFrame.lean, C1Extension.lean, LocalGraph.lean (from kernel_frame and c1_extension), TangentRange.lean (from fderiv_lower_bound): each standard axioms only`
- `lean -R sim -o sim/out/GMT/Ch06/Submission.olean sim/GMT/Ch06/Submission.lean (frozen Submission + import Mathlib.Analysis.Calculus.ImplicitContDiff + the 6 Submission.* declarations); LEAN_PATH=sim/out:$LEAN_PATH lean sim/Solutions.lean (comparator-style `exact Submission.X` for all 6 frozen types, #print axioms: propext, Classical.choice, Quot.sound)`
- `independent reviewer subagent: rebuilt the simulation from the JSON Lean remarks, compared reuse fields byte-for-byte, hashed the 56 frozen GMT.Ch06 declarations with/without the extra import (identical), ran gmt-compare.py with a simulated DAG for local_graph and the parent ('Your solution is okay!'); verdict ACCEPT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/DAG.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.mmd`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-interio-e2ad70d40d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ImplicitContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/ImplicitContDiff.olean`
- `/tmp/lsc-split-7731/Stmts.lean`
- `/tmp/lsc-split-7731/Assembly.lean`
- `/tmp/lsc-split-7731/KernelFrame.lean`
- `/tmp/lsc-split-7731/C1Extension.lean`
- `/tmp/lsc-split-7731/LocalGraph.lean`
- `/tmp/lsc-split-7731/TangentRange.lean`
- `/tmp/lsc-split-7731/sim/GMT/Ch06/Submission.lean`
- `/tmp/lsc-split-7731/sim/Solutions.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and the workspace Submission is byte-identical to it. No SimonGMT or project declaration and no DAG node provides local graph charts of regular level sets, an adapted kernel frame, a C¹ germ extension or the tangent-range identity. The names slicing_im_st_lsc_* occur nowhere in dag.json, DAG.md, issue-workers.json, dag.mmd, nodes/ or the snapshot. The only reusable accepted declaration is lpf_wtc_cat_fderiv_lower_bound (accepted, commit 8cfbc487), reused with its byte-identical type and accepted proof, as already done in the measurable_chart_differential decomposition. Mathlib supplies everything else: the C¹ implicit function theorem (ContDiffAt.implicitFunction with implicitFunction_apply_self, eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction), ContDiffBump on inner product spaces, ContDiffAt.eventually, ContDiffOn.exists_lipschitzOnWith, isOpen_iUnion_countable, Riesz duality, stdOrthonormalBasis and the finrank API. ImplicitContDiff is not imported by the frozen Submission. The comparator lets Submission.lean add imports, so only local_graph needs the extra import line. All 5 child types validate and elaborate in the comparator scope. Every new child is fully proved in Lean from its sibling dependencies, and the frozen parent type is proved from local_graph and tangent_range. Everything was kernel-checked in a simulated Submission module with comparator-style checks and standard axioms only, and independently re-verified, including by full gmt-compare.py runs.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
