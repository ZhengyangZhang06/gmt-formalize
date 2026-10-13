<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.orientation_glue-a1 -->

## Theorem `Submission.codim1_ovr_orientation_glue`

Let P, m ∈ ℕ, C ∈ 𝒟_m(ℝ^P) (GeometricCurrentOn univ m), M ⊆ ℝ^P a Borel embedded C¹ m-dimensional submanifold, ρ : ℝ^P → ℝ, and ξ_y : ℝ^P → Λ_m(ℝ^P) (ξs y) for each y ∈ ℝ^P. Write B_y := B_{ρ(y)}(y). Assume for every y ∈ M: ρ(y) > 0; ξ_y is an orientation of M ∩ B_y (IsOrientation m (M ∩ B_y) ξ_y); H^m(M ∩ B_y) < ∞; and C(ω) = ∫_{M ∩ B_y} ⟨ω(x), ξ_y(x)⟩ dH^m(x) for every ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ B_y (H^m = μHE[m]). Then there is ξ : ℝ^P → Λ_m(ℝ^P) such that: ξ is an orientation of M (IsOrientation m M ξ); ξ = ξ_y on M ∩ B_y for every y ∈ M; and C(ω) = ∫_M ⟨ω(x), ξ(x)⟩ dH^m(x) for every y ∈ M and every ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ B_y.

Node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.orientation_glue-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5217

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5722, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1285, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1081, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4210

Decomposition children: None

## Lean problem

Declaration: `Submission.codim1_ovr_orientation_glue`

```lean
∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M : Set (Euclid P)) (ρ : Euclid P → ℝ) (ξs : Euclid P → Euclid P → MultiVector P m), IsEmbeddedSubmanifold 1 m M → MeasurableSet M → (∀ y ∈ M, 0 < ρ y ∧ IsOrientation m (M ∩ ball y (ρ y)) (ξs y) ∧ μHE[m] (M ∩ ball y (ρ y)) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M ∩ ball y (ρ y), ξs y x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ ∧ (∀ y ∈ M, ∀ x ∈ M ∩ ball y (ρ y), ξ x = ξs y x) ∧ ∀ y ∈ M, ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]
```

### Frozen project context

`GMT/Ch07/Contract.lean` at `b4d606db1da5da8fa2c0292ad4924d97de8b3c4b` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 7 "Area Minimizing Currents"
(printed pp. 181–204)

Frozen contract.  Currents, boundary, mass, support and weak convergence are the clean SimonGMT
objects of `Poincare.SimonGMT.Chapter06`: `GeometricCurrentOn U n` (Simon 6.2.1), `T.boundary`
(6.2.3), `T.massOn W` = `M_W(T)` (6.2.5, Euclidean coefficient norm), `T.mass` (6.2.4),
`T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13), and the proper affine push-forward
`GeometricCurrentOn.affinePushforward` (6.2.23).  Everything else (integer multiplicity currents,
minimizing currents, densities, blow-ups, tangent cones, `reg T`, `sing T`, the associated
varifold) is defined below from primitive data.  `Hⁿ` is Mathlib's normalized `μHE[n]`; null-set
statements use Mathlib's `μH[s]` (same null sets as Simon's `Hˢ`).

**Conventions.**  The ambient space is `ℝ^{n+k}` (`Euclid (n + k)`); when a submanifold `N` is
present it has dimension `n + ℓ`, `ℓ ≤ k` (Simon writes `N^{n+ℓ} ⊂ ℝ^{n+ℓ}`, `ℓ ≤ k`, a
misprint for `ℝ^{n+k}`; `N = ℝ^{n+k}` is the case `ℓ = k`).  For an `n`-current, `∂T = 0`,
`∂S = ∂T`, `spt ∂T`, `M_W(∂T)` are read with Simon's convention `∂T = 0` if `n = 0` (6.2.3).
-/

open Filter Function Set MeasureTheory Metric
open scoped ENNReal Topology

namespace GMT.Ch07

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)

noncomputable section

/-- Euclidean space `ℝᴾ`. -/
abbrev Euclid (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Multivectors and integer multiplicity currents (Simon Ch. 6, §1 and 3.1) -/

/-- `n`-vectors `Λₙ(ℝᴾ)`, realized as the dual of `n`-covectors (Simon 6.1, `Λₙ ≅ (Λⁿ)*`);
`ξ α` is the pairing `⟨α, ξ⟩` of Simon (6.1.7). -/
abbrev MultiVector (P n : ℕ) := Covector (Euclid P) n →L[ℝ] ℝ

/-- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the subspace `Q`, i.e.
`⟨α, ξ⟩ = ±α(τ₁, …, τₙ)` (Simon 6.1.1, 6.1.7; 6.2.2).  The sign matters only for `n = 0`. -/
def IsUnitOrientationOf {n : ℕ} (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) : Prop :=
  ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = Q ∧
    ((∀ α : Covector (Euclid P) n, ξ α = α τ) ∨ ∀ α : Covector (Euclid P) n, ξ α = -α τ)

/-- Simon Ch. 6, Definition 3.1 (p. 146): a triple `(M, θ, ξ)` in `U`.  `M ⊆ U` is
`Hⁿ`-measurable (taken Borel; this loses nothing, `Hⁿ⌞M` being σ-finite) and countably
`n`-rectifiable; `θ` is positive integer-valued on `M` and locally `Hⁿ`-integrable in `U`; `ξ` is
`Hⁿ`-measurable and, `Hⁿ`-a.e. on `M`, orients the approximate tangent space `TₓM`
(Ch. 3, 1.4). -/
structure IMRep (U : Set (Euclid P)) (n : ℕ) where
  carrier : Set (Euclid P)
  mult : Euclid P → ℕ
  orient : Euclid P → MultiVector P n
  measurableSet_carrier : MeasurableSet carrier
  carrier_subset : carrier ⊆ U
  rectifiable : CountablyRectifiable n carrier
  measurable_mult : Measurable mult
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  locallyIntegrable_mult : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
    ∫⁻ x in carrier ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞
  aestronglyMeasurable_orient : AEStronglyMeasurable orient (μHE[n].restrict carrier)
  orients : ∀ᵐ x ∂(μHE[n].restrict carrier), ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n carrier x Q ∧ IsUnitOrientationOf (orient x) Q

variable {U : Set (Euclid P)} {n : ℕ}

/-- `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)` (Simon 6.3.1 (‡)). -/
def IMRep.action (R : IMRep U n) (ω : DifferentialForm (Euclid P) n) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]

/-- `T = τ(M, θ, ξ)` in `U`. -/
def IMRep.Represents (R : IMRep U n) (T : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, T ω = R.action (ω : DifferentialForm (Euclid P) n)

/-- The weight `μ_V = θ Hⁿ⌞M` of the associated varifold `V = v(M, θ)`; it equals the mass
measure `μ_T` of `T = τ(M, θ, ξ)` (Simon 6.3.2(3), 4.1.1). -/
def IMRep.measure (R : IMRep U n) : Measure (Euclid P) :=
  (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)

/-- Simon 6.3.1: `T` is an integer multiplicity (rectifiable) current. -/
def IsIntegerMultiplicity (T : GeometricCurrentOn U n) : Prop :=
  ∃ R : IMRep U n, R.Represents T

/-- Difference of currents (needed for `spt(S − T)` in 7.1.1). -/
instance : Sub (GeometricCurrentOn U n) where
  sub S T :=
    { toCurrent := S.toCurrent - T.toCurrent
      continuous' := fun ωs h => by
        simpa using (S.continuous' ωs h).sub (T.continuous' ωs h) }

/-! ## Boundary conventions in arbitrary degree -/

/-- `∂S = ∂T` in `U` (vacuous for `n = 0`, where `∂ = 0`). -/
def SameBoundary : {n : ℕ} → GeometricCurrentOn U n → GeometricCurrentOn U n → Prop
  | 0, _, _ => True
  | _ + 1, S, T => S.boundary = T.boundary

/-- `∂T = 0` in `U`. -/
def BoundaryVanishes : {n : ℕ} → GeometricCurrentOn U n → Prop
  | 0, _ => True
  | _ + 1, T => T.boundary = 0

/-- `spt ∂T` (empty for `n = 0`). -/
def boundarySupport : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P)
  | 0, _ => ∅
  | _ + 1, T => T.boundary.support

/-- `M_W(∂T)` (zero for `n = 0`). -/
def boundaryMassOn : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P) → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, T, W => T.boundary.massOn W

/-! ## Minimizing currents (Simon 7.1.1) -/

/-- `W ⊂⊂ U`: `closure W` is a compact subset of `U`. -/
def CompactlyContained (W U : Set (Euclid P)) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- **Simon 7.1.1 (p. 181).**  The integer multiplicity `T ∈ 𝒟ₙ(U)` is *minimizing in `A`*
(`A ⊆ U`): `M_W(T) ≤ M_W(S)` whenever `W ⊂⊂ U` is open, `S ∈ 𝒟ₙ(U)` is integer multiplicity,
`∂S = ∂T` in `U` and `spt(S − T)` is a compact subset of `A ∩ W`.  Competitors are integer
multiplicity, as required by Remark 7.2.2(1) and the proofs of 7.1.4 and 7.2.4. -/
def IsMinimizingIn (T : GeometricCurrentOn U n) (A : Set (Euclid P)) : Prop :=
  IsIntegerMultiplicity T ∧
    ∀ (W : Set (Euclid P)) (S : GeometricCurrentOn U n), IsOpen W → CompactlyContained W U →
      IsIntegerMultiplicity S → SameBoundary S T → IsCompact (S - T).support →
        (S - T).support ⊆ A ∩ W → T.massOn W ≤ S.massOn W

/-! ## Densities, blow-ups, tangent cones (Simon 7.3) -/

/-- `ωₙ`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ := volume (ball (0 : Euclid n) 1)

/-- `Θⁿ(μ_T, x) = θ`: `(ωₙρⁿ)⁻¹ μ_T(B_ρ(x)) → θ` as `ρ ↓ 0`, with `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)`
for small `ρ` (Simon 6.2.8; open and closed balls give the same limit). -/
def HasMassDensity (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ Tendsto (fun ρ : ℝ => T.massOn (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))

/-- Value of a current in `U` on an ambient form: `T(ω)` if `ω ∈ 𝒟ⁿ(U)`, else `0`.  Used for
convergence of currents on varying domains (Simon: "`η_{x,λⱼ#}T ⇀ C` in `ℝ^{n+ℓ}`"). -/
def currentEval (T : GeometricCurrentOn U n) (ω : DifferentialForm (Euclid P) n) : ℝ := by
  classical
  exact if h : IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0

/-- `Tⱼ ⇀ T` in `V`, for currents `Tⱼ ∈ 𝒟ₙ(Uⱼ)` whose domains eventually contain every compact
subset of `V` (as for blow-ups): `Tⱼ(ω) → T(ω)` for every `ω ∈ 𝒟ⁿ(V)` (Simon 6.2.13). -/
def ConvergesWeakly {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ ω : TestFormOn V n,
    Tendsto (fun j => currentEval (Ts j) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (T ω))

/-- `μ_{Tⱼ} → μ_T` as Radon measures in `V` (Simon 7.2.4, Remark 7.2.5(1)): for all integer
multiplicity representations of the `Tⱼ` and of `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for every
continuous `f` with compact support in `V`. -/
def MassMeasuresConverge {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ts j)) →
    ∀ R : IMRep V n, R.Represents T →
      ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
        Tendsto (fun j => ∫ x, f x ∂(Rs j).measure) atTop (𝓝 (∫ x, f x ∂R.measure))

/-- The linear part `y ↦ λ⁻¹y` of the dilation `η_{x,λ}`. -/
def dilationCLM (P : ℕ) (lam : ℝ) : Euclid P →L[ℝ] Euclid P :=
  lam⁻¹ • ContinuousLinearMap.id ℝ (Euclid P)

/-- Simon's dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, written `y ↦ −λ⁻¹x + λ⁻¹y`. -/
def dilation (x : Euclid P) (lam : ℝ) : Euclid P → Euclid P :=
  fun y => -(lam⁻¹ • x) + dilationCLM P lam y

/-- The blow-up `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))`, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` (Simon 6.2.23 for
the proper affine diffeomorphism `η_{x,λ}`, `λ ≠ 0`). -/
def blowUp (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : lam ≠ 0) :
    GeometricCurrentOn (dilation x lam '' U) n :=
  (T.restrictDomain (show (fun y => -(lam⁻¹ • x) + dilationCLM P lam y) ⁻¹'
      (dilation x lam '' U) ⊆ U by
    rintro y ⟨z, hz, hzy⟩
    have hzy' : lam⁻¹ • z = lam⁻¹ • y := by
      simpa [dilation, dilationCLM] using hzy
    rwa [← smul_right_injective (Euclid P) (inv_ne_zero hlam) hzy'])).affinePushforward
    (dilationCLM P lam) (-(lam⁻¹ • x)) (by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • x)))).isProperMap using 1
      funext y
      simp [dilationCLM])

/-- `C ∈ 𝒟ₙ(ℝᴾ)` is a cone: `η_{0,λ#}C = C` for every `λ > 0` (Simon 7.3.1(2)). -/
def IsConeCurrent (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam) (ω : TestFormOn (univ : Set (Euclid P)) n),
    currentEval (blowUp C 0 lam hlam.ne') (ω : DifferentialForm (Euclid P) n) = C ω

/-- Simon 7.3.2(1): `C` is a tangent cone of `T` at `x`, i.e. `η_{x,λⱼ#}T ⇀ C` in `ℝᴾ` for some
sequence `λⱼ > 0`, `λⱼ → 0`. -/
def IsTangentConeAt (T : GeometricCurrentOn U n) (x : Euclid P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∃ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) ∧
    ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C

/-- Simon 7.3.2(1): `T` has a (multiplicity `m`) tangent plane at `x`: some tangent cone has
support an `n`-dimensional subspace. -/
def HasTangentPlaneAt (T : GeometricCurrentOn U n) (x : Euclid P) : Prop :=
  ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, IsTangentConeAt T x C ∧
    ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ C.support = (Q : Set (Euclid P))

/-! ## Submanifolds, `reg T`, `sing T` (Simon Ch. 2, §4 and 7.4.1) -/

/-- Simon Ch. 2, §4, (4.1) (p. 55): `M ⊂ ℝᴾ` is a `d`-dimensional (embedded) `Cʳ` submanifold:
each `y ∈ M` has an open `W ∋ y` and a 1:1 `Cʳ` map `ψ : V → W`, `V ⊆ ℝᵈ` open, with
`ψ(V) = W ∩ M`, `ψ` proper, and `Dψ` of rank `d` on `V`. -/
def IsEmbeddedSubmanifold (r d : ℕ) (M : Set (Euclid P)) : Prop :=
  ∀ y ∈ M, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ z ∈ V, Injective (fderiv ℝ ψ z)

/-- Simon Ch. 2, §4 (p. 55): `T_yM = {γ'(0) : γ ∈ C¹((−1,1); ℝᴾ), γ((−1,1)) ⊆ M, γ(0) = y}`. -/
def tangentSpace (M : Set (Euclid P)) (y : Euclid P) : Set (Euclid P) :=
  {v | ∃ γ : ℝ → Euclid P, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ v 0}

/-- An orientation of the `d`-dimensional submanifold `M` (Simon 6.2.2): `ξ` is continuous on
`M` and `ξ(y) = ±τ₁ ∧ ⋯ ∧ τ_d` for an orthonormal basis `τ` of `T_yM`, for every `y ∈ M`. -/
def IsOrientation (d : ℕ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P d) : Prop :=
  ContinuousOn ξ M ∧ ∀ y ∈ M, ∃ Q : Submodule ℝ (Euclid P),
    (Q : Set (Euclid P)) = tangentSpace M y ∧ IsUnitOrientationOf (ξ y) Q

/-- **Simon 7.4.1 (p. 193)**: `reg T` is the set of `y ∈ spt T` such that, for some `ρ > 0`
(with `B_ρ(y) ⊆ U`), `m ∈ ℤ \ {0}` and embedded `n`-dimensional oriented `C¹` submanifold `M`
(of locally finite `Hⁿ`-measure in `B_ρ(y)`, as `[[M]]` requires, 6.2.2), `T = m[[M]]` in
`B_ρ(y)` (6.2.16), i.e. `T(ω) = m ∫_M ⟨ω, ξ_M⟩ dHⁿ` whenever `spt ω ⊆ B_ρ(y)`.
The point `y` itself must lie on `M` (as in 4.4(8) and the proof of 5.8): otherwise a singular
point could be declared regular by deleting it from `M`, e.g. the vertex of the Simons cone. -/
def regularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  {y | y ∈ T.support ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball y ρ ⊆ U ∧
    ∃ (m : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P n), m ≠ 0 ∧ y ∈ M ∧
      IsEmbeddedSubmanifold 1 n M ∧ IsOrientation n M ξ ∧
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[n] (M ∩ K) ≠ ∞) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y ρ →
        T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]}

/-- **Simon 7.4.1**: `sing T = spt T \ reg T`. -/
def singularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  T.support \ regularSet T

/-! ## The associated varifold `V = v(M, θ)` (Simon Ch. 4, 2.3–2.7 and 3.14) -/

/-- The approximate tangent plane `TₓM` (Ch. 3, 1.4; unique when it exists), `⊥` otherwise. -/
def approxTangentPlane (n : ℕ) (M : Set (Euclid P)) (x : Euclid P) :
    Submodule ℝ (Euclid P) := by
  classical
  exact if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥

/-- `div_M X(x) = Σⱼ eⱼ · ∇^M Xʲ = trace(p_{TₓM} ∘ DX(x))` (Simon Ch. 4, 2.3). -/
def tangentialDivergence (n : ℕ) (M : Set (Euclid P)) (X : Euclid P → Euclid P)
    (x : Euclid P) : ℝ :=
  LinearMap.trace ℝ (Euclid P)
    ((approxTangentPlane n M x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

/-- First variation `δV(X) = ∫_M div_M X dμ_V` of `V = v(M, θ)` (Simon Ch. 4, 2.2). -/
def IMRep.firstVariation (R : IMRep U n) (X : Euclid P → Euclid P) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x ∂μHE[n]

/-- Simon Ch. 4, 2.6 (computed form, p. 88): `V` is stationary in `U ∩ N`: `δV(X) = 0` for all
`X ∈ C¹_c(U; ℝᴾ)` with `X(x) ∈ TₓN` for every `x ∈ N ∩ U`. -/
def IMRep.IsStationaryAlong (R : IMRep U n) (N : Set (Euclid P)) : Prop :=
  ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → R.firstVariation X = 0

/-- Simon Ch. 4, 3.14: `V` has generalized mean curvature `H` in `U`
(`∫ div_M X dμ_V = −∫ X · H dμ_V`, `X ∈ C¹_c(U; ℝᴾ)`), with `H` bounded on compact subsets. -/
def IMRep.HasLocallyBoundedMeanCurvature (R : IMRep U n) : Prop :=
  ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧
    (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ᵐ x ∂R.measure, x ∈ K → ‖H x‖ ≤ Λ) ∧
    ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure

/-! ## Codimension one (Simon 7.5) -/

/-- Simon 7.5 (p. 197): `N ∈ 𝒪`, an oriented embedded `C²` submanifold of dimension `n + 1` with
`(N̄ \ N) ∩ U = ∅` and `N ∩ U ≠ ∅`, with chosen orientation `ξN`. -/
def InClassO (n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  IsEmbeddedSubmanifold 2 (n + 1) N ∧ IsOrientation (n + 1) N ξN ∧ (closure N \ N) ∩ U = ∅ ∧
    (N ∩ U).Nonempty

/-- Simon 7.5.1: `T = ∂[[E]]` in `U`, where `[[E]](ω) = ∫_E ⟨ω, ξ_N⟩ dH^{n+1}`. -/
def IsBoundaryOfRegion (T : GeometricCurrentOn U n) (E : Set (Euclid P))
    (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  ∀ ω : TestFormOn U n,
    T ω = ∫ x in E, ξN x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]

/-! ## Headline results -/

/-- **Simon 7.1.2 (Lemma, pp. 181–182).**  Let `N` be an embedded `C²` `(n+ℓ)`-dimensional
submanifold of `ℝ^{n+k}`, `(N̄ \ N) ∩ U = ∅`.  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`,
`spt T ⊆ N` and `∂T = 0` in `U`, then the associated varifold `V = v(M, θ)` (for any
representation `T = τ(M, θ, ξ)`) is stationary in `N ∩ U` (Ch. 4, 2.6) and has locally bounded
generalized mean curvature in `U` (Ch. 4, 3.14).
*Correction*: `spt T ⊆ N` and `(N̄ \ N) ∩ U = ∅` are implicit in the book (they are part of the
setting of Ch. 4, 2.5–2.6 and of §3); without `spt T ⊆ N` the lemma is false. -/
def MinimizingImpliesStationary : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    T.support ⊆ N → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T →
    ∀ R : IMRep U n, R.Represents T → R.IsStationaryAlong N ∧ R.HasLocallyBoundedMeanCurvature

/-- **Simon 7.2.1 (Lemma, p. 183).**  Let `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` be integer multiplicity with
`spt S` compact and `∂S = 0`.  Then there is an integer multiplicity `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`spt T` compact, `∂T = S`, and `M(T) ≤ M(R)` for every integer multiplicity `R` with `spt R`
compact and `∂R = S`.  Here `n = m + 2`: integer multiplicity currents have dimension `≥ 1`
(Ch. 6, §3).  *Correction*: the printed statement omits the conclusion `∂T = S` (proved: `T ∈ 𝓘_S`);
without it `T = 0` would do. -/
def ExistenceOfMinimizingFilling : Prop :=
  ∀ (m ℓ : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 1)),
    IsIntegerMultiplicity S → IsCompact S.support → S.boundary = 0 →
    ∃ T : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity T ∧ IsCompact T.support ∧ T.boundary = S ∧
      ∀ R : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R → IsCompact R.support → R.boundary = S → T.mass ≤ R.mass

/-- **Simon 7.2.4 (Theorem, p. 184).**  If `Tⱼ` are minimizing in `U`,
`supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for each open `W ⊂⊂ U`, and `Tⱼ ⇀ T ∈ 𝒟ₙ(U)`, then `T` is
(integer multiplicity, Remark 7.2.5(1), and) minimizing in `U`, and `μ_{Tⱼ} → μ_T` as Radon
measures in `U`. -/
def CompactnessOfMinimizingCurrents : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n),
    IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U →
      ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) →
    WeaklyConvergesOn Ts T → IsMinimizingIn T U ∧ MassMeasuresConverge (Us := fun _ => U) Ts T

/-- **Simon 7.3.1 (Theorem, p. 187).**  `N` as in 7.1.2 (`C²`).  If `T ∈ 𝒟ₙ(U)` is minimizing in
`U ∩ N` and `spt T ⊆ U ∩ N`, then (1) `Θⁿ(μ_T, x)` exists at every `x ∈ U \ spt ∂T` and is upper
semicontinuous there; (2) for `x ∈ spt T \ spt ∂T` and `λⱼ ↓ 0` (any `λⱼ > 0`, `λⱼ → 0`) there
are a subsequence `λⱼ'` and an integer multiplicity `C ∈ 𝒟ₙ(ℝ^{n+k})`, minimizing in `ℝ^{n+k}`,
with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η_{x,λⱼ'#}T} → μ_C`, `η_{0,λ#}C = C` (`λ > 0`) and
`Θⁿ(μ_C, 0) = Θⁿ(μ_T, x)`.
*Correction*: the printed hypothesis "`x ∈ spt T \ spt ∂T`" and "(1) … everywhere in `U`" are
garbled; the monotonicity proof gives (1) on `U \ spt ∂T`, which is what is stated. -/
def DensityAndTangentCones : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N →
    (∃ Θ : Euclid (n + k) → ℝ, (∀ x ∈ U \ boundarySupport T, HasMassDensity T x (Θ x)) ∧
        UpperSemicontinuousOn Θ (U \ boundarySupport T)) ∧
    ∀ x ∈ T.support \ boundarySupport T, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j),
      Tendsto lams atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧
        ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        IsMinimizingIn C univ ∧ IsConeCurrent C ∧
        ∃ θ : ℝ, HasMassDensity T x θ ∧ HasMassDensity C 0 θ

/-- **Simon 7.3.3 (Theorem, p. 189).**  `N` as in 7.3.1.  If `T` is minimizing in `U ∩ N`,
`spt T ⊆ U ∩ N` and `∂T = 0` in `U`, then (1) `Θⁿ(μ_T, x) ∈ ℤ` for all `x ∈ U \ E`, where
`H^{n−3+α}(E) = 0` for all `α > 0`; (2) there is `F ⊇ E` with `H^{n−2+α}(F) = 0` for all `α > 0`
such that `T` has a tangent plane at each `x ∈ spt T \ F`.
*Correction*: printed "`F ⊂ E`" must read `F ⊃ E` (non-integer density excludes tangent planes). -/
def IntegerDensityAndTangentPlanes : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∃ E F : Set (Euclid (n + k)), E ⊆ F ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧
      (∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m) ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧
      ∀ x ∈ T.support \ F, HasTangentPlaneAt T x

/-- **Simon 7.4.2 (Theorem, p. 194).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and minimizing in
`U ∩ N` (`N` an embedded `C²` `(n+ℓ)`-submanifold, `(N̄ \ N) ∩ U = ∅`), `spt T ⊆ U ∩ N` and
`∂T = 0` in `U`, then `reg T` is dense in `spt T`. -/
def RegularSetDense : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    T.support ⊆ closure (regularSet T)

/-- **Simon 7.4.3 (Theorem, p. 194)**, for a fixed `N` (`Nᵢ = N`).  Let `Tᵢ, T` be minimizing in
`U ∩ N`, `spt Tᵢ, spt T ⊆ N`, `∂Tᵢ = ∂T = 0` in `U`, `Tᵢ ⇀ T`, with
`supᵢ M_W(Tᵢ) < ∞` for `W ⊂⊂ U`.  If `y ∈ N ∩ U`, `Θⁿ(μ_T, y) = 1`, `y = lim yⱼ`, `yⱼ ∈ spt Tⱼ`,
then `y ∈ reg T` and `yⱼ ∈ reg Tⱼ` for all large `j`.
*Deviations*: the book allows `Nᵢ → N` "in the `C²` sense" (not defined at this point of the
book); we take `Nᵢ = N`.  The local mass bound is the hypothesis of 7.2.4, which the proof uses
for `μ_{Tⱼ} → μ_T`; it is added explicitly. -/
def DensityOneImpliesRegular : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n) (ys : ℕ → Euclid (n + k)) (y : Euclid (n + k)),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsMinimizingIn T (U ∩ N) →
    (∀ j, (Ts j).support ⊆ N) → T.support ⊆ N →
    (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) →
    WeaklyConvergesOn Ts T → y ∈ N ∩ U → HasMassDensity T y 1 →
    Tendsto ys atTop (𝓝 y) → (∀ j, ys j ∈ (Ts j).support) →
    y ∈ regularSet T ∧ ∀ᶠ j in atTop, ys j ∈ regularSet (Ts j)

/-- **Simon 7.4.4 (Theorem, p. 194).**  If `T` is as in 7.4.2 and `ξ ∈ spt T` has
`Θⁿ(μ_T, ξ) < 2`, then there is `ρ > 0` with `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0` for all `α > 0`. -/
def SingularSetSmallWhereDensityBelowTwo : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∀ ξ ∈ T.support, ∀ θ : ℝ, HasMassDensity T ξ θ → θ < 2 →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] (singularSet T ∩ ball ξ ρ) = 0

/-- **Simon 7.4.5 (Theorem, p. 195).**  If `C ∈ 𝒟ₙ(ℝ^{n+k})` is minimizing in `ℝ^{n+k}`, `∂C = 0`,
`C` is a cone, and `spt C ⊆ H̄` for an open half-space `H = {x : v · x > 0}` (`v ≠ 0`, so
`0 ∈ ∂H`), then `spt C ⊆ ∂H`. -/
def HalfSpaceConeLiesInBoundary : Prop :=
  ∀ (n k : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (v : Euclid (n + k)),
    IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → v ≠ 0 →
    C.support ⊆ closure {x | 0 < inner ℝ v x} → C.support ⊆ frontier {x | 0 < inner ℝ v x}

/-- **Simon 7.5.8 (Theorem, p. 200).**  Let `N ∈ 𝒪` (oriented by `ξN`), `E ⊆ N ∩ U`
`H^{n+1}`-measurable, `T = ∂[[E]] ∈ 𝒟ₙ(U)` integer multiplicity and minimizing in `N ∩ U`.  Then
`sing T = ∅` if `n ≤ 6`; `sing T` is locally finite in `U` (finite on compact subsets of `U`) if
`n = 7`; `H^{n−7+α}(sing T) = 0` for all `α > 0` if `n > 7`.  (`N = ℝ^{n+1}` is the case `k = 1`.)
-/
def CodimensionOneRegularity : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    (n ≤ 6 → singularSet T = ∅) ∧
    (n = 7 → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ U → (singularSet T ∩ K).Finite) ∧
    (7 < n → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 7 + α] (singularSet T) = 0)

/-- **Simon 7.5.11 (Corollary, p. 202).**  If `T` is as in 7.5.8, `T = τ(M, θ, ξ)`, and
`T₁ ∈ 𝒟ₙ(U)` is obtained by equipping a connected component `M₁` of `reg T` with multiplicity
`1` and the orientation `ξ` of `T`, then `∂T₁ = 0` in `U` and `T₁` is minimizing in `U ∩ N`. -/
def RegularComponentsAreMinimizing : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    ∀ R : IMRep U n, R.Represents T → ∀ y ∈ regularSet T, ∀ T₁ : GeometricCurrentOn U n,
      (∀ ω : TestFormOn U n, T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
        R.orient x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]) →
      BoundaryVanishes T₁ ∧ IsMinimizingIn T₁ (U ∩ N)

end

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.offvertex_rep-a1.orientation_glue-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Steps 4 and 5 and fact (F3) of the supplied parent proof (parent B3a–B3b).
Departures from the parent text, stated explicitly.
(i) (F3) is derived from the accepted declaration submanifold_density_one (H^m(M ∩ B_s(w))/(ω_m s^m) → 1 as s ↓ 0). The parent used the mean value inequality and bilipschitz_measure. The conclusion is the same and the proof is shorter.
(ii) In the sign test the parent shows ξ_{y'} = −ξ_y on a whole neighbourhood. Here both representations of C are compared on one bump form: one integral is > 0 and the other < 0, using only continuity of the two pairings at w. The idea is the same (orientation_sign plus a positive bump-form test).
Notation.
- H^m := μHE[m], B_s(w) := ball w s, and B_y := B_{ρ(y)}(y).
- ⟨α, η⟩ := η(α), and |α| := covectorEuclideanNorm α.
- ξ_y := ξs y.

1. (Tangent spaces of the pieces.) M is an embedded C¹ m-submanifold, so the hypothesis of submanifold_local holds with O := ℝ^P at every point (M ∩ ℝ^P = M). Part (b) of submanifold_local with O := B_y gives tangentSpace(M ∩ B_y, w) = tangentSpace(M, w) for every y ∈ M and w ∈ M ∩ B_y.
2. (Positivity, F3.) Let w ∈ M and s > 0. Then H^m(M ∩ B_s(w)) ≠ 0. Otherwise H^m(M ∩ B_{s'}(w)) ≤ H^m(M ∩ B_s(w)) = 0 for 0 < s' < s. So the ratio H^m(M ∩ B_{s'}(w))/(ω_m s'^m) is 0 on (0, s) and tends to 0 as s' ↓ 0. By submanifold_density_one it tends to 1. Limits in [0, ∞] are unique, a contradiction.
3. (Agreement on overlaps.) Let y, y' ∈ M and w ∈ M ∩ B_y ∩ B_{y'}. We show ξ_{y'}(w) = ξ_y(w).
 (a) By the orientation hypotheses there are subspaces Q and Q' such that:
  - Q has carrier tangentSpace(M ∩ B_y, w), and ξ_y(w) is a unit orientation of Q;
  - Q' has carrier tangentSpace(M ∩ B_{y'}, w), and ξ_{y'}(w) is a unit orientation of Q'.
  By step 1 both carriers equal tangentSpace(M, w), so Q = Q' (a submodule is determined by its carrier). By orientation_sign, ξ_{y'}(w) = ξ_y(w) or ξ_{y'}(w) = −ξ_y(w). Assume the latter; we derive a contradiction.
 (b) Let L be given by unit_orientation_dual, and put β := L(ξ_y(w)). Part (c) of that lemma gives ξ_y(w)(β) = 1, hence ξ_{y'}(w)(β) = −1.
 (c) Put f(x) := ξ_y(x)(β) and g(x) := ξ_{y'}(x)(β).
  - Orientations are continuous on their sets, and evaluation at β is continuous. So f is continuous on M ∩ B_y and g on M ∩ B_{y'}.
  - Both sets are neighbourhoods of w relative to M, and f(w) = 1, g(w) = −1.
  - B_y ∩ B_{y'} is an open set containing w.
  Hence there is r > 0 with B_r(w) ⊆ B_y ∩ B_{y'} such that f(x) > 1/2 and g(x) < −1/2 for every x ∈ M ∩ B_r(w).
 (d) Let φ : ℝ^P → [0, 1] be the smooth bump ContDiffBump centred at w with inner radius r/4 and outer radius r/2.
  - φ = 1 on closedBall(w, r/4), and tsupport φ = closedBall(w, r/2) ⊆ B_r(w) is compact.
  - For a covector γ put ω_γ(x) := φ(x)γ. It is smooth with compact support, so ω_γ ∈ 𝒟^m(ℝ^P), and tsupport ω_γ ⊆ B_r(w).
  - ω_{−β} = −ω_β.
 (e) Claim. Let z ∈ M with B_r(w) ⊆ B_z, and let γ be a covector with ξ_z(x)(γ) ≥ 1/2 for all x ∈ M ∩ B_r(w). Then C(ω_γ) > 0.
  Proof. tsupport ω_γ ⊆ B_z, so by hypothesis C(ω_γ) = ∫_{M ∩ B_z} F dH^m, where F(x) := ξ_z(x)(φ(x)γ) = φ(x)·ξ_z(x)(γ).
  - F is integrable on M ∩ B_z. It is continuous on the Borel set M ∩ B_z, hence a.e. strongly measurable for H^m restricted to it. Also |F(x)| ≤ |ξ_z(x)(γ)| ≤ |γ| by unit_orientation_dual (a), since ξ_z(x) is a unit orientation of a subspace. And H^m(M ∩ B_z) < ∞.
  - F ≥ 0 on M ∩ B_z. On B_r(w), φ ≥ 0 and ξ_z(x)(γ) ≥ 1/2. Off B_r(w), φ(x) = 0 because tsupport φ ⊆ B_r(w).
  - F ≥ 1/2 on M ∩ B_{r/4}(w), where φ = 1.
  - Put E := M ∩ B_{r/4}(w) ⊆ M ∩ B_z. E is Borel, H^m(E) > 0 by step 2, and H^m(E) ≤ H^m(M ∩ B_z) < ∞.
  - Hence C(ω_γ) = ∫_{M ∩ B_z} F ≥ ∫_E F ≥ (1/2)·H^m(E) > 0. The first inequality is monotonicity in the domain for a nonnegative integrable function; the second is the lower bound on E.
 (f) Apply (e) twice.
  - With z := y and γ := β, using f > 1/2 on M ∩ B_r(w): C(ω_β) > 0.
  - With z := y' and γ := −β, using ξ_{y'}(x)(−β) = −g(x) > 1/2: C(ω_{−β}) > 0.
  But C(ω_{−β}) = C(−ω_β) = −C(ω_β) < 0 by linearity of C, a contradiction. Hence ξ_{y'}(w) = ξ_y(w).
4. (Global orientation.) Define ξ(x) := ξ_x(x) for every x ∈ ℝ^P.
 (a) Let y ∈ M and x ∈ M ∩ B_y. Then x ∈ B_x since ρ(x) > 0. Step 3 for the pair (y, x) at the point x gives ξ(x) = ξ_x(x) = ξ_y(x). So ξ = ξ_y on M ∩ B_y, the second conclusion.
 (b) ξ is continuous on M. Let y ∈ M.
  - ξ_y is continuous within M ∩ B_y at y, and M ∩ B_y is a neighbourhood of y relative to M. So ξ_y is continuous within M at y.
  - ξ agrees with ξ_y on that neighbourhood, by (a). So ξ is continuous within M at y.
 (c) Let x ∈ M. Then ξ(x) = ξ_x(x) is a unit orientation of a subspace Q with carrier tangentSpace(M ∩ B_x, x) = tangentSpace(M, x), by step 1.
 Hence IsOrientation m M ξ.
5. (Representation.) Let y ∈ M and ω ∈ 𝒟^m(ℝ^P) with tsupport ω ⊆ B_y.
 - By hypothesis, C(ω) = ∫_{M ∩ B_y} ⟨ω, ξ_y⟩ dH^m.
 - This equals ∫_{M ∩ B_y} ⟨ω, ξ⟩ dH^m, since ξ = ξ_y on the Borel set M ∩ B_y (step 4(a)).
 - For x ∈ M ∖ B_y we have x ∉ tsupport ω, so ω(x) = 0 and ⟨ω(x), ξ(x)⟩ = 0. As M is Borel and M ∩ B_y ⊆ M, this gives ∫_{M ∩ B_y} ⟨ω, ξ⟩ dH^m = ∫_M ⟨ω, ξ⟩ dH^m. ∎

Lean reference proof (verified). The declaration below was compiled with Lean v4.35.0-rc3 and Mathlib 25730c7c, after `import GMT.Ch07.Submission`, in namespace GMT.Ch07 with the contract `open`s. It was compiled twice: in a standalone file, and spliced into a copy of GMT/Ch07/Submission.lean just before main_theorem. Each listed dependency was present under its exact frozen type, as an axiom standing in for the accepted or sibling declaration. `#print axioms` reports propext, Classical.choice and Quot.sound, plus exactly the declarations listed in depends_on (for reused children: their Submission names). It follows the numbered proof above.

```lean
theorem Submission.codim1_ovr_orientation_glue : ∀ (P m : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) m) (M : Set (Euclid P)) (ρ : Euclid P → ℝ) (ξs : Euclid P → Euclid P → MultiVector P m), IsEmbeddedSubmanifold 1 m M → MeasurableSet M → (∀ y ∈ M, 0 < ρ y ∧ IsOrientation m (M ∩ ball y (ρ y)) (ξs y) ∧ μHE[m] (M ∩ ball y (ρ y)) ≠ ∞ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M ∩ ball y (ρ y), ξs y x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m]) → ∃ ξ : Euclid P → MultiVector P m, IsOrientation m M ξ ∧ (∀ y ∈ M, ∀ x ∈ M ∩ ball y (ρ y), ξ x = ξs y x) ∧ ∀ y ∈ M, ∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball y (ρ y) → C ω = ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] := by
  intro P m C M ρ ξs hM hMm hloc
  -- step 1: tangent spaces of the pieces are those of M
  have hloc2 := (Submission.codim1_ovr_embedded_submanifold_local P 1 m M le_rfl
    (fun y _ => ⟨univ, isOpen_univ, mem_univ y, by rwa [inter_univ]⟩)).2
  have htan : ∀ y ∈ M, ∀ w ∈ M ∩ ball y (ρ y),
      tangentSpace (M ∩ ball y (ρ y)) w = tangentSpace M w :=
    fun y _ w hw => (hloc2 (ball y (ρ y)) isOpen_ball).2 w hw
  -- step 2 (F3): positivity of H^m(M ∩ B_s(w))
  have hpos : ∀ w ∈ M, ∀ s : ℝ, 0 < s → μHE[m] (M ∩ ball w s) ≠ 0 := by
    intro w hw s hs h0
    have hlim := Submission.dimred_rpd_submanifold_density_one P m M w hM hw
    have hev : (fun _ : ℝ => (0 : ℝ≥0∞)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun s' : ℝ => μHE[m] (M ∩ ball w s') / (unitBallVolume m * ENNReal.ofReal (s' ^ m)) := by
      filter_upwards [Ioo_mem_nhdsGT hs] with s' hs'
      have h' : μHE[m] (M ∩ ball w s') = 0 :=
        measure_mono_null (inter_subset_inter_right _ (ball_subset_ball hs'.2.le)) h0
      rw [h', ENNReal.zero_div]
    have h01 := tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim
    exact zero_ne_one h01
  -- step 3: agreement on overlaps (analytic core: bump-form test)
  have hagree : ∀ y ∈ M, ∀ y' ∈ M, ∀ w ∈ M ∩ ball y (ρ y), w ∈ ball y' (ρ y') →
      ξs y' w = ξs y w := by
    intro y hy y' hy' w hw hw'
    obtain ⟨Q, hQ, hQξ⟩ := (hloc y hy).2.1.2 w hw
    obtain ⟨Q', hQ', hQξ'⟩ := (hloc y' hy').2.1.2 w ⟨hw.1, hw'⟩
    have hQQ : Q' = Q := by
      apply SetLike.coe_injective
      rw [hQ, hQ', htan y hy w hw, htan y' hy' w ⟨hw.1, hw'⟩]
    subst hQQ
    rcases Submission.rsdic_unitOrientation_eq_or_eq_neg P m (ξs y w) (ξs y' w) Q' hQξ hQξ' with h | h
    · exact h
    · exfalso
      obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P m
      have hβ1 : ξs y w (L (ξs y w)) = 1 := (hL (ξs y w) Q' hQξ).2.2
      have hβ2 : ξs y' w (L (ξs y w)) = -1 := by
        rw [h, neg_apply, hβ1]
      set β := L (ξs y w) with hβdef
      have hwM : w ∈ M := hw.1
      -- continuity of the two pairings at w within M
      have hny : M ∩ ball y (ρ y) ∈ 𝓝[M] w :=
        inter_mem_nhdsWithin M (isOpen_ball.mem_nhds hw.2)
      have hny' : M ∩ ball y' (ρ y') ∈ 𝓝[M] w :=
        inter_mem_nhdsWithin M (isOpen_ball.mem_nhds hw')
      have hcy : ContinuousWithinAt (fun x => ξs y x β) M w :=
        (((hloc y hy).2.1.1 w hw).mono_of_mem_nhdsWithin hny).clm_apply continuousWithinAt_const
      have hcy' : ContinuousWithinAt (fun x => ξs y' x β) M w :=
        (((hloc y' hy').2.1.1 w ⟨hwM, hw'⟩).mono_of_mem_nhdsWithin hny').clm_apply
          continuousWithinAt_const
      have hev1 : ∀ᶠ x in 𝓝[M] w, (1 / 2 : ℝ) < ξs y x β :=
        hcy.eventually (lt_mem_nhds (by show (1 / 2 : ℝ) < ξs y w β; rw [hβ1]; norm_num))
      have hev2 : ∀ᶠ x in 𝓝[M] w, ξs y' x β < -(1 / 2 : ℝ) :=
        hcy'.eventually (gt_mem_nhds (by show ξs y' w β < -(1 / 2 : ℝ); rw [hβ2]; norm_num))
      obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.mem_nhdsWithin_iff.1 (hev1.and hev2)
      obtain ⟨r₂, hr₂, hr₂sub⟩ := Metric.isOpen_iff.1 (isOpen_ball.inter (isOpen_ball (x := y') (ε := ρ y')))
        w ⟨hw.2, hw'⟩
      set r := min r₁ r₂ with hrdef
      have hr : 0 < r := lt_min hr₁ hr₂
      have hrB : ball w r ⊆ ball y (ρ y) ∩ ball y' (ρ y') :=
        (ball_subset_ball (min_le_right _ _)).trans hr₂sub
      have hrM : ∀ x ∈ M ∩ ball w r, (1 / 2 : ℝ) < ξs y x β ∧ ξs y' x β < -(1 / 2 : ℝ) :=
        fun x hx => hr₁sub ⟨ball_subset_ball (min_le_left _ _) hx.2, hx.1⟩
      -- the bump function
      let φ : ContDiffBump w := ⟨r / 4, r / 2, by positivity, by linarith⟩
      have hφsupp : tsupport φ ⊆ ball w r := by
        rw [φ.tsupport_eq]; exact closedBall_subset_ball (by simp [φ]; linarith)
      have hform : ∀ γ : Covector (Euclid P) m,
          (fun x => φ x • γ) ∈ TestFormOn (univ : Set (Euclid P)) m := by
        intro γ
        refine ⟨⟨?_, ?_⟩, subset_univ _⟩
        · exact (φ.contDiff (n := ⊤)).smul contDiff_const
        · exact φ.hasCompactSupport.smul_right
      have htsupp : ∀ γ : Covector (Euclid P) m,
          tsupport (fun x => φ x • γ) ⊆ ball w r :=
        fun γ => (tsupport_smul_subset_left _ _).trans hφsupp
      -- positivity of C on a bump times a covector that pairs ≥ 1/2 near w
      have hposC : ∀ z ∈ M, ball w r ⊆ ball z (ρ z) → ∀ γ : Covector (Euclid P) m,
          (∀ x ∈ M ∩ ball w r, (1 / 2 : ℝ) ≤ ξs z x γ) →
          0 < C ⟨fun x => φ x • γ, hform γ⟩ := by
        intro z hz hrz γ hγ
        rw [(hloc z hz).2.2.2 ⟨fun x => φ x • γ, hform γ⟩ ((htsupp γ).trans hrz)]
        simp only [map_smul, smul_eq_mul]
        have hmeasB : MeasurableSet (M ∩ ball z (ρ z)) := hMm.inter measurableSet_ball
        have hmeas4 : MeasurableSet (M ∩ ball w (r / 4)) := hMm.inter measurableSet_ball
        have hsub4 : M ∩ ball w (r / 4) ⊆ M ∩ ball z (ρ z) :=
          inter_subset_inter_right _ ((ball_subset_ball (by linarith)).trans hrz)
        have hfinB := (hloc z hz).2.2.1
        have hfin4 : μHE[m] (M ∩ ball w (r / 4)) ≠ ∞ :=
          ne_top_of_le_ne_top hfinB (measure_mono hsub4)
        have hpos4 : 0 < μHE[m].real (M ∩ ball w (r / 4)) :=
          ENNReal.toReal_pos (hpos w hwM (r / 4) (by positivity)) hfin4
        -- integrability on M ∩ B_z
        have hint : IntegrableOn (fun x => φ x * ξs z x γ) (M ∩ ball z (ρ z)) μHE[m] := by
          refine IntegrableOn.of_bound (lt_top_iff_ne_top.2 hfinB) ?_ (covectorEuclideanNorm γ) ?_
          · exact (((φ.continuous.continuousOn).mul
              (((hloc z hz).2.1.1).clm_apply continuousOn_const))).aestronglyMeasurable hmeasB
          · refine (ae_restrict_iff' hmeasB).2 (Eventually.of_forall fun x hx => ?_)
            obtain ⟨Q, -, hQ⟩ := (hloc z hz).2.1.2 x hx
            have hb := (hL (ξs z x) Q hQ).1 γ
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg φ.nonneg]
            calc φ x * |ξs z x γ| ≤ 1 * |ξs z x γ| :=
                  mul_le_mul_of_nonneg_right φ.le_one (abs_nonneg _)
              _ ≤ covectorEuclideanNorm γ := by rw [one_mul]; exact hb
        have hnonneg : ∀ x ∈ M ∩ ball z (ρ z), 0 ≤ φ x * ξs z x γ := by
          intro x hx
          by_cases hxr : x ∈ ball w r
          · exact mul_nonneg φ.nonneg (le_trans (by norm_num) (hγ x ⟨hx.1, hxr⟩))
          · rw [image_eq_zero_of_notMem_tsupport (fun h => hxr (hφsupp h)), zero_mul]
        have hge : ∀ x ∈ M ∩ ball w (r / 4), (1 / 2 : ℝ) ≤ φ x * ξs z x γ := by
          intro x hx
          have hx1 : φ x = 1 := φ.one_of_mem_closedBall (by
            show x ∈ closedBall w (r / 4); exact ball_subset_closedBall hx.2)
          rw [hx1, one_mul]
          exact hγ x ⟨hx.1, ball_subset_ball (by linarith) hx.2⟩
        calc (0 : ℝ) < 1 / 2 * μHE[m].real (M ∩ ball w (r / 4)) := by positivity
          _ ≤ ∫ x in M ∩ ball w (r / 4), φ x * ξs z x γ ∂μHE[m] :=
              setIntegral_ge_of_const_le_real hmeas4 hfin4 hge (hint.mono_set hsub4)
          _ ≤ ∫ x in M ∩ ball z (ρ z), φ x * ξs z x γ ∂μHE[m] :=
              setIntegral_mono_set hint
                ((ae_restrict_iff' hmeasB).2 (Eventually.of_forall hnonneg))
                (Eventually.of_forall hsub4)
      have h1 := hposC y hy (hrB.trans inter_subset_left) β
        (fun x hx => (hrM x hx).1.le)
      have h2 := hposC y' hy' (hrB.trans inter_subset_right) (-β)
        (fun x hx => by rw [map_neg]; linarith [(hrM x hx).2])
      have hneg : (⟨fun x => φ x • (-β), hform (-β)⟩ : TestFormOn (univ : Set (Euclid P)) m) =
          -⟨fun x => φ x • β, hform β⟩ := by
        apply Subtype.ext
        funext x
        simp [smul_neg]
      have hC : C ⟨fun x => φ x • (-β), hform (-β)⟩ = -C ⟨fun x => φ x • β, hform β⟩ := by
        rw [hneg]; exact map_neg (C.toCurrent : TestFormOn (univ : Set (Euclid P)) m →ₗ[ℝ] ℝ) _
      rw [hC] at h2
      linarith
  -- step 4: the global orientation
  refine ⟨fun x => ξs x x, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    have hcont : ContinuousWithinAt (ξs y) (M ∩ ball y (ρ y)) y :=
      (hloc y hy).2.1.1 y ⟨hy, mem_ball_self (hloc y hy).1⟩
    have hnhds : M ∩ ball y (ρ y) ∈ 𝓝[M] y :=
      inter_mem_nhdsWithin M (isOpen_ball.mem_nhds (mem_ball_self (hloc y hy).1))
    have hc2 : ContinuousWithinAt (ξs y) M y := hcont.mono_of_mem_nhdsWithin hnhds
    refine hc2.congr_of_eventuallyEq ?_ rfl
    filter_upwards [hnhds] with x hx
    exact hagree y hy x hx.1 x hx (mem_ball_self (hloc x hx.1).1)
  · intro x hx
    obtain ⟨Q, hQ, hQξ⟩ := (hloc x hx).2.1.2 x ⟨hx, mem_ball_self (hloc x hx).1⟩
    exact ⟨Q, by rw [hQ, htan x hx x ⟨hx, mem_ball_self (hloc x hx).1⟩], hQξ⟩
  · intro y hy x hx
    exact hagree y hy x hx.1 x hx (mem_ball_self (hloc x hx.1).1)
  · intro y hy ω hω
    rw [(hloc y hy).2.2.2 ω hω]
    have hmeas : MeasurableSet (M ∩ ball y (ρ y)) := hMm.inter measurableSet_ball
    have h1 : ∫ x in M ∩ ball y (ρ y), ξs y x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] =
        ∫ x in M ∩ ball y (ρ y), ξs x x ((ω : DifferentialForm (Euclid P) m) x) ∂μHE[m] :=
      setIntegral_congr_fun hmeas (fun x hx => by
        simp only [hagree y hy x hx.1 x hx (mem_ball_self (hloc x hx.1).1)])
    rw [h1]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMm inter_subset_left
    intro x hx
    have hxω : x ∉ tsupport (ω : DifferentialForm (Euclid P) m) := fun h => hx.2 ⟨hx.1, hω h⟩
    rw [image_eq_zero_of_notMem_tsupport hxω, map_zero]
```

## Key steps

1. submanifold_local: the pieces M ∩ B_y have the tangent spaces of M, so two local orientations at a common point orient the same subspace.
2. submanifold_density_one gives H^m(M ∩ B_s(w)) > 0 for w ∈ M and s > 0.
3. orientation_sign gives ξ_{y'} = ±ξ_y at a common point. The − case fails: the bump form φ·L(ξ_y(w)) would receive a positive value of C from the y-representation and a negative one from the y'-representation.
4. ξ(x) := ξ_x(x) agrees with every ξ_y on M ∩ B_y. Hence it is a continuous orientation of M and represents C on each B_y.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; sha256sum <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `cat GMT/Ch07/Contract.lean (IMRep, IsIntegerMultiplicity, IsConeCurrent, blowUp, dilation, IsEmbeddedSubmanifold, tangentSpace, IsOrientation, IsUnitOrientationOf, regularSet, HasMassDensity)`
- `grep -n 'VanishesOn|def zeroRegion|def support|isOpen_zeroRegion|structure GeometricCurrentOn|abbrev TestFormOn|IsTestForm|IsSmoothForm|covectorEuclideanNorm|testFormEuclideanSupNorm' simongmt/Poincare/SimonGMT/Chapter06/{CurrentLocalEquality,Currents,Forms,Mass,FormSupNorm}.lean`
- `rg -n 'euclideanHausdorffMeasure_smul₀|nullSingletonClass_hausdorff|exists_isSubordinate|one_of_mem_closedBall|support_eq|tsupport_eq|tendsto_integral_of_dominated_convergence|setIntegral_ge_of_const_le_real|setIntegral_mono_set|IntegrableOn.of_bound|ENNReal.tsum_geometric|exists_nat_pow_near|Tendsto.bddAbove_range|ContinuousAlternatingMap.apply' <snapshot>/mathlib/Mathlib`
- `rg -c 'codim1_ovr_' <snapshot> (no match); grep each of the 7 new lean_names in dag.json (no match); git grep -l 'codim1_ovr_' over all 1662 distinct ref objects (no match)`
- `python3 over dag.json: accepted nodes whose lean_statement mentions IsEmbeddedSubmanifold, tangentSpace or IsOrientation; nodes with IsConeCurrent and support; IMRep/IsIntegerMultiplicity with Tendsto; status, frozen type, candidate commit and parent handoff of the 5 reused names; children of simons_regular_cone-a1`
- `git show <commit> -- GMT/Ch07/Submission.lean for 44ef61f79e21 (dtc_vanish_off_support: smooth partition of unity), 52115c22ec2d (cone_current_apply_dilation_pullback), d626082a69a0 (chart_tangentSpace_eq_range_fderiv), a5ceace526bc (dpf_pb_imrep_pullback_integral_tendsto: IMRep dominated convergence)`
- `runtime.py (_decompose, _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff) and speculation.py contract (a parent's prerequisites are its children plus its depends_on)`
- `lean -DautoImplicit=false /tmp/ovr-split-check/{Types,Assembly,SkelC3,C1C2,C4,C5,C6,C7,Full,SubmissionCopy}.lean with LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecificLimits/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Archimedean/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b7ab3fcecc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-7577af74dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-cone-measure-homogeneous-a1-27e5a07a68/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-chart-tangent-space-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1-unit-or-24edf309fb/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/speculation.py`
- `/tmp/ovr-split-check/Full.lean`
- `/tmp/ovr-split-check/SubmissionCopy.lean`

Pins match. The manifest records project b4d606db and Mathlib 25730c7c, equal to workspace HEAD and .lake/packages/mathlib. The snapshot Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f…).
Library.
- SimonGMT Chapter06 supplies GeometricCurrentOn, TestFormOn, VanishesOn, the open zeroRegion, support = U ∖ zeroRegion, and covectorEuclideanNorm.
- SimonGMT has no continuity or homogeneity lemma for covectorEuclideanNorm, and no local-to-global gluing lemma for currents. The children prove these inline.
- The snapshot Mathlib has every library lemma the children use:
  - Measure.euclideanHausdorffMeasure_smul₀ (Geometry/Euclidean/Volume/Measure.lean:152);
  - nullSingletonClass_hausdorff (MeasureTheory/Measure/Hausdorff.lean:615);
  - SmoothPartitionOfUnity.exists_isSubordinate (Geometry/Manifold/PartitionOfUnity.lean:555);
  - ContDiffBump.one_of_mem_closedBall, support_eq and tsupport_eq (Analysis/Calculus/BumpFunction/Basic.lean:137–157);
  - tendsto_integral_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:57);
  - setIntegral_mono_set and setIntegral_ge_of_const_le_real (MeasureTheory/Integral/Bochner/Set.lean:737, 798);
  - IntegrableOn.of_bound (MeasureTheory/Integral/IntegrableOn.lean:174);
  - ENNReal.tsum_geometric (Analysis/SpecificLimits/Basic.lean:402);
  - exists_nat_pow_near (Algebra/Order/Archimedean/Basic.lean:195).
DAG.
- Five accepted declarations are reused with byte-identical frozen types: cone_current_apply_dilation_pullback (52115c22ec2d), chart_tangentSpace_eq_range_fderiv (d626082a69a0), dor_ims_unitOrientation_dual (9c8432cb0101), rsdic_unitOrientation_eq_or_eq_neg (fe95347baaed) and dimred_rpd_submanifold_density_one (e8842d90b78f).
- Unaccepted nodes owned by other parents cannot be shared: idtp_tpf_cone_support_smul and idtp_ccd_cone_support_smul (decomposing) have the content of cone_support_smul. So that child gets the fresh name codim1_ovr_cone_support_smul.
- The 7 new codim1_ovr_ names are free in dag.json, the snapshot, SimonGMT and all git refs.
- This node's own prerequisites stay available to its glue (speculation.contract = children + depends_on): codim1_density_one_regular_local_rep, dtc_vanish_off_support and dor_ims_unitOrientation_dual.
Lean.
- Types.lean elaborates all 12 child types.
- Assembly.lean proves the selected frozen type from the frozen child types and this node's prerequisites, all given as axioms.
- Each new child has a complete Lean proof that uses exactly its listed dependencies. These proofs are attached to the child proofs.
- Full.lean, and SubmissionCopy.lean (the same block spliced into a copy of Submission.lean before main_theorem), compile without errors.
- #print axioms of the selected theorem lists propext, Classical.choice and Quot.sound, plus the 7 frozen prerequisites: the 5 reused declarations, codim1_density_one_regular_local_rep and dtc_vanish_off_support.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
