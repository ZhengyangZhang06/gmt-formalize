<!-- theorem-id: gmt-ch06/root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1 -->

## Theorem `Submission.slicing_im_creg_box_coarea`

Let P, m ∈ ℕ, n := m+1, Ω ⊆ ℝⁿ open, Φ : ℝⁿ → ℝ^P of class C¹, K-Lipschitz on Ω and c-antilipschitz on Ω (c > 0), h : ℝⁿ → ℝ of class C¹, f : ℝ^P → ℝ arbitrary, G : ℝ^P → ℝ^P Borel, B ⊆ ℝⁿ open and χ : ℝⁿ → ℝⁿ of class C¹ on B with χ(B) ⊆ Ω, χ Lipschitz on B, h(χ(y)) = y_0 for y ∈ B, and |v − v′| ≤ |χ([t,v]) − χ([t,v′])| whenever [t,v], [t,v′] ∈ B ([t,v] = (t, v_0, …, v_{m−1})). Let S ⊆ χ(B) be Borel with f(Φ(w)) = h(w), G(Φ(w)) ∈ range DΦ(w) and ⟨G(Φ(w)), DΦ(w)u⟩ = Dh(w)u (all u) for every w ∈ S. Then for every Borel g : ℝ^P → [0, ∞], t ↦ ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m is Lebesgue-a.e.-measurable and ∫_ℝ ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m dt = ∫_{Φ(S)} |G| g dH^{m+1} (Hᵏ := μHE[k]).

Node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/3444

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1073, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4115, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4121

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1073, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4859, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4866, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4870

## Lean problem

Declaration: `Submission.slicing_im_creg_box_coarea`

```lean
∀ (P m : ℕ) (Φ : Eucl (m + 1) → Eucl P) (Ω : Set (Eucl (m + 1))) (h : Eucl (m + 1) → ℝ) (f : Eucl P → ℝ) (G : Eucl P → Eucl P) (B : Set (Eucl (m + 1))) (χ : Eucl (m + 1) → Eucl (m + 1)) (S : Set (Eucl (m + 1))), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ContDiff ℝ 1 h → Measurable G → IsOpen B → ContDiffOn ℝ 1 χ B → χ '' B ⊆ Ω → (∃ Λ : ℝ≥0, LipschitzOnWith Λ χ B) → (∀ y ∈ B, h (χ y) = y 0) → (∀ (t : ℝ) (v v' : Eucl m), (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) ∈ B → (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')) ∈ B → ‖v - v'‖ ≤ ‖χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v))) - χ ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v')))‖) → MeasurableSet S → S ⊆ χ '' B → (∀ w ∈ S, f (Φ w) = h w ∧ G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap ∧ ∀ u, inner ℝ (G (Φ w)) (fderiv ℝ Φ w u) = fderiv ℝ h w u) → ∀ g : Eucl P → ℝ≥0∞, Measurable g → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) (volume : Measure ℝ) ∧ ∫⁻ t, (∫⁻ x in Φ '' S ∩ f ⁻¹' {t}, g x ∂(μHE[m] : Measure (Eucl P))) ∂(volume : Measure ℝ) = ∫⁻ x in Φ '' S, ‖G x‖ₑ * g x ∂(μHE[m + 1] : Measure (Eucl P))
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

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.coarea-a1.chart_regular-a1.box-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. n := m+1. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩ and norm |·|; Lᵏ = volume on ℝᵏ; Hᵏ := μHE[k] on ℝ^P. e_i := EuclideanSpace.single i 1. For t ∈ ℝ and v ∈ ℝ^m, [t,v] := (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons t (EuclideanSpace.equiv (Fin m) ℝ v)) is the point (t, v_0, …, v_{m−1}) of ℝ^{m+1}; for y ∈ ℝ^{m+1}, tail y := (y_1, …, y_m) ∈ ℝ^m, so that y = [y_0, tail y]. D := fderiv ℝ. For F : ℝᵏ → ℝ^Q and x ∈ ℝᵏ, J_kF(x) := √det(⟨DF(x)e_i, DF(x)e_j⟩)_{i,j<k} (Gram-determinant Jacobian; the determinant of the empty matrix is 1).

This is steps 1, 3, 4 and 5 of the parent proof on one straightened box. The chart (B, χ) is now a hypothesis; the parent proof constructs it in step 2. Sibling lemmas used: area_formula (Submission.lpf_raf_chart_change_of_variables), jacobian (Submission.slicing_im_creg_jacobian_identity) and tonelli (Submission.slicing_im_creg_lintegral_cons). Mathlib results used: change of variables MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul, and Lusin–Souslin MeasurableSet.image_of_continuousOn_injOn. Fix K, c > 0 and Λ from the hypotheses.

1. (Coordinates.) [t,v]_0 = t and [t,v]_{i+1} = v_i; [y_0, tail y] = y. With ι : ℝ^m → ℝⁿ, ι(z) := [0,z], a linear map with |ι z| = |z|, [t,v] = [t,0] + ι(v). So v ↦ [t,v] is affine with derivative ι, 1-Lipschitz and continuous, |[t,v] − [t,v′]| = |v − v′|, and ι(e_i) = e_{i+1} for i < m.
2. (Injectivity.) Φ is injective on Ω: if w, w′ ∈ Ω and Φ(w) = Φ(w′), then c|w − w′| ≤ 0 with c > 0. χ is injective on B: if y, y′ ∈ B and χ(y) = χ(y′), then y_0 = h(χ y) = h(χ y′) = y′_0 =: t. With v := tail y and v′ := tail y′ we have y = [t,v] and y′ = [t,v′] in B, so the slice hypothesis gives |v − v′| ≤ |χ y − χ y′| = 0, hence y = y′.
3. (Derivatives.) B is open and χ is C¹ on B, so χ has derivative Dχ(y) at each y ∈ B (HasFDerivAt). Φ and h are differentiable. Since h(χ(y′)) = y′_0 for all y′ in the neighbourhood B of y, the chain rule and uniqueness of derivatives give Dh(χ y)(Dχ(y) z) = z_0 for all z (the derivative of y′ ↦ y′_0 is EuclideanSpace.proj 0). For [t,v] ∈ B, the slice map σ_t(v) := Φ(χ([t,v])) has derivative DΦ(χ[t,v]) ∘ Dχ([t,v]) ∘ ι at v. So Dσ_t(v)e_i = DΦ(χ y)(Dχ(y) e_{i+1}) with y = [t,v], and J_mσ_t(v) = 𝒥(y), where 𝒥(y) := √det(⟨DΦ(χ y)(Dχ(y)e_{i+1}), DΦ(χ y)(Dχ(y)e_{j+1})⟩)_{i,j<m}.
4. (Sets.) Let S′ := B ∩ χ⁻¹(S). It is Borel: χ̃ := B.piecewise χ 0 is Borel measurable (ContinuousOn.measurable_piecewise; χ is continuous on the open set B), and S′ = B ∩ χ̃⁻¹(S). χ(S′) = S because S ⊆ χ(B). Also S ⊆ χ(B) ⊆ Ω. Φ(S) is Borel by Lusin–Souslin, since Φ is continuous and injective on the Borel set S. Ω ∩ Φ⁻¹(Φ(S)) = S by injectivity of Φ on Ω.
5. (Area formula for Φ.) Apply area_formula with n := m+1, the chart Φ on the open set Ω (K-Lipschitz and c-antilipschitz), A := Φ(S) ⊆ Φ(Ω) (Borel, so null-measurable) and the Borel weight x ↦ ‖G x‖ₑ·g(x). By step 4, Ω ∩ Φ⁻¹(Φ(S)) = S, so ∫_{Φ(S)} ‖G‖ₑ g dH^{m+1} = ∫_S F dLⁿ, where F(w) := ‖G(Φ w)‖ₑ · g(Φ w) · ofReal(J_{m+1}Φ(w)).
6. (Change of variables along χ.) Apply lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume on ℝⁿ) to the Borel set S′. Its hypotheses are HasFDerivWithinAt χ (Dχ y) S′ y for y ∈ S′ (step 3) and χ injective on S′ ⊆ B (step 2). Applied to F, and using χ(S′) = S: ∫_S F dLⁿ = ∫_{S′} ofReal|det Dχ(y)| · F(χ y) dLⁿ(y).
7. (Jacobian identity.) Let y ∈ S′ and w := χ(y) ∈ S. By the pointwise hypothesis, γ := G(Φ w) ∈ range DΦ(w) and ⟨γ, DΦ(w)u⟩ = Dh(w)u for all u. With u := Dχ(y)z and step 3, ⟨γ, DΦ(w)(Dχ(y)z)⟩ = z_0 for all z. Apply jacobian with A := DΦ(w) and D := Dχ(y): 𝒥(y) = |G(Φ w)| · J_{m+1}Φ(w) · |det Dχ(y)|. Using ENNReal.ofReal_mul (all factors ≥ 0) and ‖·‖ₑ = ofReal ‖·‖ (ofReal_norm), ofReal|det Dχ(y)| · F(χ y) = g(Φ(χ y)) · ofReal(𝒥(y)) on S′. Hence, by setLIntegral_congr_fun and lintegral_indicator (S′ Borel), ∫_{S′} ofReal|det Dχ| · F∘χ dLⁿ = ∫_{ℝⁿ} F̃ dLⁿ, where F̃ := S′.indicator (y ↦ g(Φ(χ y)) · ofReal(𝒥(y))).
8. (F̃ is Borel.) On S′ ⊆ B, χ = χ̃, so F̃ = S′.indicator (y ↦ g(Φ(χ̃ y)) · ofReal √det M(y)) with M(y)_{ij} := ⟨DΦ(χ̃ y)(Dχ(y)e_{i+1}), DΦ(χ̃ y)(Dχ(y)e_{j+1})⟩. Each piece is measurable: χ̃ (step 4); y ↦ Dχ(y)e_k (measurable_fderiv_apply_const); (x,u) ↦ DΦ(x)u, which is continuous because Φ is C¹ (Continuous.measurable2); inner products (Measurable.inner); the matrix (Measurable.of_eval_matrix); det and √, which are continuous; and g∘Φ∘χ̃. So F̃ is measurable (Measurable.indicator).
9. (Tonelli.) Apply tonelli to F̃: τ(t) := ∫_{ℝ^m} F̃([t,v]) dv is measurable in t, and ∫_{ℝⁿ} F̃ dLⁿ = ∫_ℝ τ(t) dt.
10. (Slices: area formula for σ_t.) Fix t ∈ ℝ. B_t := {v : [t,v] ∈ B} is open (preimage of the open B under the continuous v ↦ [t,v]). S′_t := {v : [t,v] ∈ S′} ⊆ B_t is Borel. On B_t, σ_t is K·Λ-Lipschitz by LipschitzOnWith.comp: v ↦ [t,v] is 1-Lipschitz and maps B_t into B, χ is Λ-Lipschitz on B with χ(B) ⊆ Ω, and Φ is K-Lipschitz on Ω. σ_t is also c-antilipschitz on B_t: c|v − v′| ≤ c|χ[t,v] − χ[t,v′]| ≤ |σ_t v − σ_t v′|, by the slice hypothesis and the antilipschitz bound of Φ on Ω ⊇ χ(B). So σ_t is continuous and injective on B_t; A_t := σ_t(S′_t) is Borel (Lusin–Souslin) and B_t ∩ σ_t⁻¹(A_t) = S′_t. Apply area_formula with n := m, the chart σ_t on the open set B_t, A := A_t ⊆ σ_t(B_t) and the weight g: ∫_{A_t} g dH^m = ∫_{S′_t} g(σ_t v) · ofReal(J_mσ_t(v)) dv. For v ∈ S′_t, J_mσ_t(v) = 𝒥([t,v]) (step 3) and g(σ_t v) = g(Φ(χ[t,v])); for v ∉ S′_t, F̃([t,v]) = 0. Hence ∫_{A_t} g dH^m = ∫_{ℝ^m} F̃([t,v]) dv = τ(t) (lintegral_indicator and lintegral_congr). If B_t = ∅, all terms are 0. For m = 0 this is the counting-measure case of area_formula, with J_0 = 1.
11. (Slice sets.) A_t = Φ(S) ∩ f⁻¹{t}.
(⊇) Let w ∈ S with f(Φ w) = t. Then w = χ(y) with y ∈ B (S ⊆ χ(B)), so y ∈ S′, and y_0 = h(χ y) = h(w) = f(Φ w) = t. Thus y = [t, tail y], tail y ∈ S′_t and σ_t(tail y) = Φ(w).
(⊆) If v ∈ S′_t, then χ[t,v] ∈ S, so σ_t(v) = Φ(χ[t,v]) ∈ Φ(S), and f(σ_t v) = h(χ[t,v]) = [t,v]_0 = t.
12. (Conclusion.) By steps 10–11, ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m = τ(t) for every t ∈ ℝ. So the slice function equals the measurable τ and is AEMeasurable (Measurable.aemeasurable, AEMeasurable.congr). Chaining steps 5, 6, 7, 9 and 10–11 gives ∫_{Φ(S)} ‖G‖ₑ g dH^{m+1} = ∫_S F = ∫_{S′} ofReal|det Dχ|·F∘χ = ∫ F̃ = ∫_ℝ τ(t) dt = ∫_ℝ ∫_{Φ(S) ∩ f⁻¹{t}} g dH^m dt. ∎

## Key steps

1. Φ injective on Ω; χ injective on B (h∘χ = y_0 plus the slice bound); S′ := B ∩ χ⁻¹S Borel with χ(S′) = S; Φ(S) Borel (Lusin–Souslin).
2. Chain rule: Dh(χy)∘Dχ(y) = proj_0 on B; Dσ_t(v)e_i = DΦ(χy)(Dχ(y)e_{i+1}).
3. Area formula (lpf_raf_chart_change_of_variables) for Φ on Ω turns ∫_{Φ(S)} ‖G‖ₑ g dH^{m+1} into ∫_S ‖G∘Φ‖ₑ g∘Φ JΦ.
4. Change of variables along χ on S′ (lintegral_image_eq_lintegral_abs_det_fderiv_mul).
5. Jacobian identity (slicing_im_creg_jacobian_identity) with A = DΦ(χy), D = Dχ(y), γ = G(Φχy) rewrites the integrand as g∘Φ∘χ·𝒥, giving a Borel F̃ on ℝⁿ.
6. Tonelli (slicing_im_creg_lintegral_cons) splits ∫F̃ into ∫_t τ(t), τ measurable.
7. For each t, the area formula for the Lipschitz, antilipschitz slice map σ_t on the open B_t gives τ(t) = ∫_{σ_t(S′_t)} g dH^m, and σ_t(S′_t) = Φ(S) ∩ f⁻¹{t}.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/{parent-child-handoff.json,parent-supplied-plan.md} and nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `python3 scans of dag.json: coarea siblings and the glue type; statements of accepted lpf_raf_*, lpf_wtc_*, lpf_c1_* nodes; search for Fin.cons/toLp/piFinSuccAbove/toOpenPartialHomeomorph statements (no reusable Tonelli or IFT lemma); name-collision and identical-type scan of the six child types against all 508 nodes (only the intended reuse matches)`
- `read nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json (precedent for reusing accepted declarations by name) and nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/{parent-supplied-natural-proof.md,parent-child-handoff.json}`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e:GMT/Ch06/Submission.lean (accepted lpf_raf_chart_change_of_variables and its accepted prerequisites lpf_raf_local_lipschitz_area, lpf_raf_chart_preimage_null)`
- `grep -rn 'slicing_im_creg|slicing_im_coarea_chart_regular' local-references/197bdd4b88278494/project (no match)`
- `grep in pinned Mathlib: def normDet / normDet_* (Analysis/InnerProductSpace/NormDet.lean), volume_preserving_symm_measurableEquiv_toLp / PiLp.volume_preserving_ofLp / toLp (MeasureTheory/Measure/Haar/InnerProductSpace.lean), ContDiffAt.toOpenPartialHomeomorph (Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean), isOpen_image_symm_of_subset_target (Topology/OpenPartialHomeomorph/Basic.lean), lipschitzOnWith_of_nnnorm_fderiv_le (Analysis/Calculus/MeanValue.lean), μHE API (Geometry/Euclidean/Volume/Measure.lean)`
- `#check probes after import GMT.Ch06.Submission: lintegral_image_eq_lintegral_abs_det_fderiv_mul, measurePreserving_piFinSuccAbove, OpenPartialHomeomorph.contDiffAt_symm, HasStrictFDerivAt.toOpenPartialHomeomorph, MeasurableSet.image_of_continuousOn_injOn, TopologicalSpace.isOpen_iUnion_countable (present); LinearMap.normDet (not in the frozen import closure, hence Gram-determinant statements)`
- `python3: contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py; lean_contract.validate_lean_statement on the six child types and the parent type`
- `lake env lean /tmp/chartreg-decomp/Assembly.lean (six child stubs, parent proved from them; sorryAx only from the stubs)`
- `lake env lean /tmp/chartreg-decomp/{jac,tonelli,straight,l2g}/Proof.lean (complete; propext, Classical.choice, Quot.sound) and /tmp/chartreg-decomp/box/Check.lean (box from the three sibling types declared as axioms)`
- `lake env lean /tmp/chartreg-decomp/integrated/Integrated.lean (accepted block of 9fc44225 + five child proofs + parent assembly; all standard axioms)`
- `python3 -I /tmp/chartreg-scripts/jac_check.py (exact rational check of the Jacobian identity: 1552 cases, 0 mismatches)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1-chart-regular-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-chart-chain-rule-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-chart-ch-1ba1e0b708/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/chartreg-decomp/Assembly.lean`
- `/tmp/chartreg-decomp/jac/Proof.lean`
- `/tmp/chartreg-decomp/tonelli/Proof.lean`
- `/tmp/chartreg-decomp/straight/Proof.lean`
- `/tmp/chartreg-decomp/l2g/Proof.lean`
- `/tmp/chartreg-decomp/box/Proof.lean`
- `/tmp/chartreg-decomp/box/Check.lean`
- `/tmp/chartreg-decomp/integrated/Integrated.lean`
- `/tmp/chartreg-scripts/jac_check.py`

The snapshot (project d8d46c95, Mathlib 25730c7c) has no slicing_im_creg_* or chart_regular declaration, and the frozen import closure lacks LinearMap.normDet, so child statements use Gram-determinant Jacobians. The DAG holds the comparator-accepted lpf_raf_chart_change_of_variables (the area formula for Lipschitz, antilipschitz charts), reused here by name with a byte-identical type. It has no Tonelli split along Fin.cons and no inverse-function straightening lemma, so those become new children. Mathlib supplies the inverse function theorem (ContDiffAt.toOpenPartialHomeomorph, contDiffAt_symm), change of variables (lintegral_image_eq_lintegral_abs_det_fderiv_mul), Lusin–Souslin, Lindelöf, piFinSuccAbove/PiLp volume-preservation and Cramer's rule. Lean checks in the exact comparator scope: all six child types elaborate, and the parent's type follows from them. The five new children are fully proved in scratch files. The integrated file (accepted block + children + parent assembly) uses only propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
