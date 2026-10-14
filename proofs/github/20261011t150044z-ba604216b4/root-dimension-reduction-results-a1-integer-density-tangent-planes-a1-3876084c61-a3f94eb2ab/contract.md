<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1 -->

## Theorem `Submission.idtp_ccd_stationary_cone_sheet_planar`

For every P ∈ ℕ, every M ⊆ ℝ^P that is an embedded C¹ 2-dimensional submanifold (IsEmbeddedSubmanifold 1 2 M), every p ∈ M with p ≠ 0 and every ρ > 0 such that (i) t·x ∈ M whenever x ∈ M ∩ B_ρ(p), t > 0 and t·x ∈ B_ρ(p), and (ii) M is stationary in B_ρ(p): ∫_{M ∩ B_ρ(p)} tr(P_x ∘ DX(x)) dH²(x) = 0 for every C¹ vector field X : ℝ^P → ℝ^P with compact support and tsupport X ⊆ B_ρ(p), where P_x is the orthogonal projection onto span(tangentSpace M x) and H² := μHE[2]: there are δ > 0 and a 2-dimensional linear subspace Q of ℝ^P with p ∈ Q and M ∩ B_δ(p) = Q ∩ B_δ(p).

Node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4810

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6006, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6010, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6017, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6026, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6038, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6054, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6066, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6077, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6087, https://github.com/ZhengyangZhang06/gmt-formalize/issues/6093

## Lean problem

Declaration: `Submission.idtp_ccd_stationary_cone_sheet_planar`

```lean
∀ (P : ℕ) (M : Set (Euclid P)) (p : Euclid P) (ρ : ℝ), IsEmbeddedSubmanifold 1 2 M → p ∈ M → p ≠ 0 → 0 < ρ → (∀ x ∈ M ∩ ball p ρ, ∀ t : ℝ, 0 < t → t • x ∈ ball p ρ → t • x ∈ M) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball p ρ → ∫ x in M ∩ ball p ρ, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[2] = 0) → ∃ (δ : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q = 2 ∧ p ∈ Q ∧ M ∩ ball p δ = (Q : Set (Euclid P)) ∩ ball p δ
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

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, steps 7–11 (the rotation-field conservation law; Simon Ch. 4, 2.2–2.6 for the first variation, Ch. 2 §3 for the area formula), stated for the surface M itself and without the normalization |p| = 1 of parent step 1 (u := p/|p| and r₀ := |p| replace p and 1). Conventions: H² := μHE[2], B_r(x) := ball x r, ⟨·,·⟩ the inner product; T_xM := span(tangentSpace M x) with orthogonal projection P_{T_xM}; for v, w ∈ ℝ^P, v ⊗ w is the linear map h ↦ ⟨w, h⟩v.
1. (Chart at p.) Let (V₀, W₀, ψ) be a chart of M at p (IsEmbeddedSubmanifold 1 2 M) and v₀ ∈ V₀ with ψ(v₀) = p. For v ∈ V₀, tangentSpace M ψ(v) = range Dψ(v) (accepted `Submission.chart_tangentSpace_eq_range_fderiv`, r = 1), a 2-dimensional subspace since Dψ(v) is injective on ℝ². Put Q := span(tangentSpace M p) = range Dψ(v₀), so finrank Q = 2. By the accepted lemma `Submission.dsmc_chart_inverse_continuity`, for v ∈ V₀ and ε > 0 there is δ_v > 0 with |v' − v| < ε whenever v' ∈ V₀ and |ψ(v') − ψ(v)| < δ_v. Let r₀ := |p| > 0, u := p/r₀, and fix ρ₁ with 0 < ρ₁ ≤ min(ρ, r₀/2) and B_{ρ₁}(p) ⊆ W₀.
2. (p ∈ Q.) Let ε₀ := min(1/2, ρ₁/(2r₀)) and c(t) := (1 + ε₀t)p. For t ∈ (−1, 1): 1 + ε₀t > 0 and |c(t) − p| = ε₀|t|r₀ < ρ₁ ≤ ρ, so c(t) ∈ M by hypothesis (i) applied to x := p ∈ M ∩ B_ρ(p). c is affine, hence C¹, c(0) = p and c'(0) = ε₀p; by the definition of tangentSpace, ε₀p ∈ tangentSpace M p ⊆ Q. Hence p ∈ Q and u ∈ Q.
3. (Coordinates.) Choose a unit vector e ∈ Q with ⟨e, u⟩ = 0 (normalize w − ⟨w,u⟩u for some w ∈ Q ∖ ℝu, which exists since finrank Q = 2); (u, e) is an orthonormal basis of Q. Put πx := ⟨x,u⟩u + ⟨x,e⟩e (orthogonal projection onto Q) and Ax := ⟨x,u⟩e − ⟨x,e⟩u. A is linear, ⟨Ax, y⟩ = −⟨x, Ay⟩ (so ⟨Ax, x⟩ = 0), |Ax| = |πx|, and Au = e. Let Ω := {x : ⟨x,u⟩ > 0} (open); B_{ρ₁}(p) ⊆ Ω because ⟨x,u⟩ ≥ r₀ − |x − p| > r₀/2 there. On Ω let f(x) := arctan(⟨x,e⟩/⟨x,u⟩) ∈ (−π/2, π/2). f is smooth on Ω, f(tx) = f(x) for t > 0, ∇f(x) = Ax/|πx|² (so ⟨∇f(x), x⟩ = 0), f(p) = 0 and ∇f(p) = e/r₀. Let F(x) := (|x|, f(x)) ∈ ℝ², smooth on Ω (0 ∉ Ω). DF(p)v = (⟨u,v⟩, ⟨e,v⟩/r₀), which maps Q = span{u, e} bijectively onto ℝ².
4. (Inverse function theorem.) Φ := F ∘ ψ is C¹ near v₀ (ψ is C¹ on the open set V₀ and maps a neighbourhood of v₀ into B_{ρ₁}(p) ⊆ Ω), and DΦ(v₀) = DF(p) ∘ Dψ(v₀) is a bijection of ℝ² (Dψ(v₀) maps ℝ² bijectively onto Q and DF(p)|_Q is bijective). By the inverse function theorem (Mathlib `ContDiffAt.toOpenPartialHomeomorph`) there are open sets V₁' ∋ v₀ with V₁' ⊆ V₀ ∩ ψ⁻¹(B_{ρ₁}(p)) and O' ∋ Φ(v₀) = (r₀, 0) such that Φ maps V₁' homeomorphically onto O'. Since DΦ is continuous at v₀ and invertibility is an open condition, we may shrink V₁' (and replace O' by Φ(V₁')) so that DΦ(v) is invertible for every v ∈ V₁'; then the inverse Φ⁻¹ : O' → V₁' is C¹ at every point of O' with invertible derivative DΦ⁻¹(w) = DΦ(Φ⁻¹(w))⁻¹ (`OpenPartialHomeomorph.contDiffAt_symm` applied at each point of O'). G₀ := ψ ∘ Φ⁻¹ : O' → M is continuous with G₀(r₀, 0) = p. Choose s with 0 < s < min(r₀/2, π/4) such that O := (r₀ − s, r₀ + s) × (−s, s) ⊆ O' and G₀(O) ⊆ B_{ρ₁/2}(p); put G := G₀ on O and V₁ := Φ⁻¹(O) ∩ V₁' (open, ⊆ V₀). Then G is C¹ on O and injective there; F ∘ G = id_O, so F is injective on G(O) with inverse G; DG(w) = Dψ(Φ⁻¹(w)) ∘ DΦ⁻¹(w) is injective with range DG(w) = range Dψ(Φ⁻¹(w)) = tangentSpace M (G(w)) (step 1); and G(O) = ψ(V₁).
5. (G(O) is relatively open in M.) For v ∈ V₁ choose ε_v > 0 with B_{ε_v}(v) ⊆ V₁ and δ_v as in step 1 for this ε_v; then M ∩ W₀ ∩ B_{δ_v}(ψ(v)) ⊆ ψ(V₁), because every point of M ∩ W₀ = ψ(V₀) is ψ(v') with v' ∈ V₀, and |ψ(v') − ψ(v)| < δ_v forces v' ∈ B_{ε_v}(v) ⊆ V₁. So N₀ := ⋃_{v∈V₁} (W₀ ∩ B_{δ_v}(ψ(v))) is open with M ∩ N₀ = ψ(V₁). Put N := N₀ ∩ B_{ρ₁}(p): N is open, N ⊆ B_{ρ₁}(p) ⊆ B_ρ(p) ∩ Ω, M ∩ N = G(O) (as G(O) ⊆ B_{ρ₁/2}(p)), and p = G(r₀, 0) ∈ N.
6. (Radial structure.) Define γ(α) := r₀⁻¹G(r₀, α) for α ∈ (−s, s). γ is C¹, |γ(α)| = 1 (the first coordinate of F(G(r₀, α)) = (r₀, α) is |G(r₀, α)| = r₀), f(γ(α)) = f(G(r₀, α)) = α (homogeneity of f), and γ(0) = u. Claim: G(t, α) = tγ(α) on O. Fix α and let I_α := {t ∈ (r₀ − s, r₀ + s) : G(t, α) = tγ(α)}; it contains r₀ and is relatively closed by continuity. It is open: if t ∈ I_α, then tγ(α) = G(t, α) ∈ G(O) ⊆ N, so t'γ(α) ∈ N for t' near t; for such t', t'γ(α) = (t'/t)G(t, α) with G(t, α) ∈ M ∩ B_ρ(p), t'/t > 0 and t'γ(α) ∈ N ⊆ B_ρ(p), so t'γ(α) ∈ M by hypothesis (i); hence t'γ(α) ∈ M ∩ N = G(O), say t'γ(α) = G(w), and w = F(G(w)) = F(t'γ(α)) = (t', α), i.e. t' ∈ I_α. By connectedness I_α = (r₀ − s, r₀ + s). Consequently ∂_tG(t, α) = γ(α), ∂_αG(t, α) = tγ'(α), and T_{G(t,α)}M = range DG(t, α) = span{γ(α), γ'(α)}. Since |γ| ≡ 1, ⟨γ, γ'⟩ = 0; differentiating f(γ(α)) = α gives ⟨∇f(γ(α)), γ'(α)⟩ = 1, i.e. ⟨Aγ(α), γ'(α)⟩ = |πγ(α)|²; in particular γ'(α) ≠ 0, and (γ(α), τ(α)) with τ := γ'/|γ'| is an orthonormal basis of T_{G(t,α)}M.
7. (Test field.) Fix λ ∈ C^∞_c((r₀ − s, r₀ + s)) with λ ≥ 0 and λ ≢ 0, and let ψ₀ : ℝ → ℝ be an arbitrary C¹ function with compact support in (−s, s). K₀ := G(tsupport λ × tsupport ψ₀) is compact and contained in G(O) ⊆ N. Choose a smooth ζ : ℝ^P → [0, 1] with compact support, tsupport ζ ⊆ N, and ζ = 1 on an open neighbourhood of K₀: since K₀ is compact and N is open, there is ε > 0 such that the closed 3ε-neighbourhood of K₀ lies in N; take ζ := (indicator of the open 2ε-neighbourhood of K₀) convolved with a smooth nonnegative bump of integral 1 supported in B_ε(0) (or apply the smooth Urysohn lemma to the disjoint closed sets 'closed ε-neighbourhood of K₀' and 'complement of the open 2ε-neighbourhood'); then ζ = 1 on the open ε-neighbourhood of K₀ and tsupport ζ is contained in the closed 3ε-neighbourhood, a compact subset of N. Let g(x) := ψ₀(f(x))·λ(|x|)·ζ(x) and X(x) := g(x)·Ax. g is C¹ on ℝ^P (on N ⊆ Ω ∖ {0} every factor is C¹, and g vanishes on the open set (tsupport ζ)ᶜ), so X is C¹ with compact support and tsupport X ⊆ tsupport ζ ⊆ N ⊆ B_ρ(p). By hypothesis (ii), ∫_{M∩B_ρ(p)} tr(P_{T_xM} ∘ DX(x)) dH²(x) = 0.
8. (Integrand.) DX(x) = g(x)A + (Ax) ⊗ ∇g(x). For a 2-plane T with orthonormal basis (t₁, t₂), tr(P_T ∘ A) = Σᵢ⟨At_i, t_i⟩ = 0 and tr(P_T ∘ (v ⊗ w)) = ⟨P_T w, v⟩; hence h(x) := tr(P_{T_xM} ∘ DX(x)) = ⟨P_{T_xM}∇g(x), Ax⟩. If x ∈ (M ∩ B_ρ(p)) ∖ N, then x ∉ tsupport X, DX(x) = 0 and h(x) = 0. Let x ∈ M ∩ N = G(O), x = G(t, α) = tγ(α) with (t, α) = F(x). Here ∇g = λζψ₀'(f)∇f + ψ₀(f)ζλ'(|x|)x/|x| + ψ₀(f)λ(|x|)∇ζ. The second term contributes ⟨P_{T_xM}γ(α), Ax⟩ = ⟨γ(α), Ax⟩ = 0, because γ(α) = x/|x| ∈ T_xM and ⟨x, Ax⟩ = 0. The third term vanishes: if ψ₀(α)λ(t) ≠ 0 then x ∈ K₀, where ∇ζ = 0. In the first term ζ(x) = 1 whenever λ(t)ψ₀'(α) ≠ 0 (then x ∈ K₀). Hence h(x) = λ(t)ψ₀'(α)⟨P_{T_xM}Ax, Ax⟩/|πx|² = λ(t)ψ₀'(α)|P_{T_xM}Ax|²/|πx|². With Ax = tAγ, ⟨Aγ, γ⟩ = 0 and the basis (γ, τ): |P_{T_xM}Ax|² = t²⟨Aγ, τ⟩² = t²|πγ|⁴/|γ'|² and |πx|² = t²|πγ|². So h(G(t, α)) = λ(t)ψ₀'(α)|πγ(α)|²/|γ'(α)|².
9. (Area formula.) M is a Borel set: by Lindelöf countably many chart sets W_i cover M, and each M ∩ W_i = ψ_i(V_i) is a continuous image of a σ-compact open set, so M is σ-compact; hence M ∩ B_ρ(p) and G(O) = M ∩ N are Borel. Since h = 0 on (M ∩ B_ρ(p)) ∖ G(O) and G(O) = M ∩ N ⊆ M ∩ B_ρ(p), the indicator identity gives ∫_{M∩B_ρ(p)} h dH² = ∫_{G(O)} h dH². By the area formula for the injective C¹ map G with injective derivative on the open set O (SimonGMT `integral_area_formula_of_injective_derivative`, Chapter02/WeightedArea.lean, with μHE[2] = Lebesgue measure on ℝ² by `EuclideanSpace.euclideanHausdorffMeasure_eq_volume`), ∫_{G(O)} h dH² = ∫_O J_G(t, α)·h(G(t, α)) d(t, α), where J_G = areaJacobianAt G = sqrt(det(DGᵀDG)) (`areaJacobianAt_eq_sqrt_det_gram`). DG(t, α) has the orthogonal columns γ(α) (unit) and tγ'(α), so J_G(t, α) = t|γ'(α)|. Hence 0 = ∫_O λ(t)·t·ψ₀'(α)·κ(α) d(t, α) with κ := |πγ|²/|γ'|, continuous on (−s, s). The integrand is continuous with compact support in O, so by Fubini 0 = (∫λ(t)t dt)·(∫ψ₀'(α)κ(α) dα), and ∫λ(t)t dt > 0. Therefore ∫_{−s}^{s} ψ₀'(α)κ(α) dα = 0 for every C¹ function ψ₀ with compact support in (−s, s). (Lean note: the proof file needs the imports Poincare.SimonGMT.Chapter02.WeightedArea, Poincare.SimonGMT.Chapter02.AreaParametrization (which contains `areaJacobianAt_eq_sqrt_det_gram`; alternatively compute normDet directly) and Poincare.SimonGMT.Chapter08.DistributionalConstancy, all built in the pinned package; finrank ℝ (Euclid 2) = 2 is `finrank_euclideanSpace_fin`.)
10. (κ ≡ 1.) κ is continuous on (−s, s) and has vanishing distributional derivative there, hence it is constant: transport along the volume-preserving linear isometry ℝ ≅ Euclid 1 and apply SimonGMT `ae_eq_const_of_weak_coordinate_derivatives_zero` (Chapter08/DistributionalConstancy.lean, n = 1, U := the image of (−s, s), open and preconnected, f := κ extended by 0, locally integrable on U; its hypothesis is exactly step 9 for the C¹ compactly supported test functions with support in U) to get κ = c a.e. on (−s, s), hence everywhere on (−s, s) by continuity. At α = 0: γ(0) = u and |πu| = 1; γ'(0) ⊥ u and γ'(0) ∈ T_pM = span{γ(0), γ'(0)} = Q, so γ'(0) ∈ ℝe; and ⟨Au, γ'(0)⟩ = |πu|² = 1 with Au = e gives γ'(0) = e. Hence κ ≡ κ(0) = 1, i.e. |γ'| = |πγ|² on (−s, s).
11. (Planarity.) By Cauchy–Schwarz, |πγ|² = ⟨Aγ, γ'⟩ ≤ |Aγ||γ'| = |πγ|·|πγ|²; and |πγ| ≥ ⟨γ, u⟩ > 0 (γ(α) = r₀⁻¹G(r₀, α) ∈ Ω since G(r₀, α) ∈ N ⊆ Ω), so |πγ| ≥ 1. Also |πγ| ≤ |γ| = 1. Hence |γ − πγ|² = |γ|² − |πγ|² = 0 and γ(α) ∈ Q. As ⟨γ,u⟩ > 0, ⟨γ,u⟩² + ⟨γ,e⟩² = 1 and arctan(⟨γ,e⟩/⟨γ,u⟩) = α ∈ (−π/2, π/2), we get γ(α) = cos α·u + sin α·e. Therefore G(O) = {t(cos α·u + sin α·e) : |t − r₀| < s, |α| < s} ⊆ Q.
12. (Conclusion.) Choose δ with 0 < δ ≤ min(s, ρ₁), B_δ(p) ⊆ N, and |f(y)| < s for y ∈ B_δ(p) (N is an open set containing p, and f is continuous at p with f(p) = 0). If y ∈ Q ∩ B_δ(p), then ⟨y,u⟩ > 0, y = |y|(cos f(y)·u + sin f(y)·e) (polar form in Q), ||y| − r₀| ≤ |y − p| < s and |f(y)| < s, so y = G(|y|, f(y)) ∈ G(O) ⊆ M. Conversely M ∩ B_δ(p) ⊆ M ∩ N = G(O) ⊆ Q. Hence M ∩ B_δ(p) = Q ∩ B_δ(p), where finrank Q = 2 (step 1) and p ∈ Q (step 2). ∎

## Key steps

1. Q := T_pM is 2-dimensional (chart) and contains p (radial curve t ↦ (1 + ε₀t)p in M); fix u = p/|p|, e ∈ Q ⊥ u, the rotation A of Q, the angle f and F = (|x|, f).
2. Inverse function theorem for F∘ψ gives G : O = (r₀−s, r₀+s)×(−s, s) → M, injective C¹ with injective derivative, F∘G = id, and an open N with M ∩ N = G(O).
3. Radial invariance and injectivity of F on G(O) give G(t, α) = tγ(α) with |γ| = 1, f(γ(α)) = α, T_{G(t,α)}M = span{γ, γ'} and ⟨Aγ, γ'⟩ = |πγ|².
4. Stationarity tested with X = ψ₀(f)λ(|x|)ζ·Ax reduces, by the trace identities, to the integrand λψ₀'|πγ|²/|γ'|² on G(O); the area formula (J_G = t|γ'|) and Fubini give ∫ψ₀'κ = 0 with κ = |πγ|²/|γ'|.
5. κ has zero distributional derivative, so κ ≡ κ(0) = 1; Cauchy–Schwarz gives |πγ| = 1, so γ(α) = cos α·u + sin α·e ∈ Q and M ∩ B_δ(p) = Q ∩ B_δ(p) for small δ.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `python3 -I scans of dag.json (lean_name, lean_statement, status): lemmas mentioning regularSet; IsConeCurrent together with support; IsStationaryAlong or firstVariation together with IsMinimizingIn; HasApproximateTangentSpaceAt together with IsEmbeddedSubmanifold or ContDiff; names matching support_null|density_zero|vanish|null_off; restrictDomain together with boundary; subspace ball measure; statuses of the 29 cited lemma names`
- `grep -n 'def restrictDomain|def VanishesOn|def zeroRegion|def support|def IsTestForm|def testFormOnSubmodule|def GeometricCurrentOn.boundary|def WeaklyConvergesOn|abbrev Covector' simongmt Chapter06/{CurrentLocalEquality,Currents,Forms}.lean`
- `grep -n 'def HasApproximateTangentSpaceAt|HasApproximateTangentSpaceAt.unique|def CountablyRectifiable' simongmt Chapter03/Rectifiable.lean`
- `grep -n 'theorem integral_area_formula_of_injective_derivative|def areaJacobianAt|areaJacobianAt_eq_sqrt_det_gram|theorem ae_eq_const_of_weak_coordinate_derivatives_zero' simongmt Chapter02/{WeightedArea,Area,AreaParametrization}.lean Chapter08/DistributionalConstancy.lean`
- `grep -rn 'euclideanHausdorffMeasure' mathlib Geometry/Euclidean/Volume/Measure.lean (zero_or_top, eq_volume, Isometry.euclideanHausdorffMeasure_image); grep -n 'addHaar_ball_of_pos|addHaar_ball ' mathlib MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `grep -c idtp_ccd dag.json; grep -rl idtp_ccd run nodes/*.json|*.md and .swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); grep -n 'Whi82' book/chapter-07.txt, book/simon-gmt.txt; sed -n 490,515p book/chapter-07.txt`
- `lake env lean /tmp/ccdp_check/Children.lean (7 child types elaborate); lake env lean /tmp/ccdp_check/Assembly.lean (#print axioms assembly_check: propext, Classical.choice, Quot.sound); lake env lean /tmp/ccdp_check/FromJson.lean (frozen child types as Submission.* stubs plus accepted-lemma stubs prove the parent type, exit 0)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3597486845/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/ccdp_check/Children.lean`
- `/tmp/ccdp_check/Assembly.lean`
- `/tmp/ccdp_check/FromJson.lean`

Pins match the manifest. The snapshot project commit equals workspace HEAD, b4d606d. Mathlib is 25730c7c and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

Accepted DAG lemmas used by the children, all with status `accepted`: rsd_constant_multiplicity_reduction, rsd_ae_hasMassDensity_mult, rsd_mem_support_iff_measure_ball_pos, rsd_massOn_eq_measure, rsd_cmr_support_eq_inter, imrep_carrier_sdiff_support_null, regcomp_atl_local_density_zero, approxTangent_le_submanifold_tangentSpace, dtc_approxTangent_of_null_diff, chart_tangentSpace_eq_range_fderiv, dsmc_chart_inverse_continuity, dimred_rpd_submanifold_density_one, imsupp_unit_orientation_ne_zero_norm_le_one, cone_current_imrep_measure_smul_image, dtc_restrictDomain_isIntegerMultiplicity, dtc_massOn_eq_of_agreeOn, dimred_cs_mi_hasMassDensity_unique, dimred_regular_point_density.

Non-accepted results used, all ancestor or parent prerequisites as in the supplied proof:
- density_one_implies_regular (speculative-ready)
- minimizing_implies_stationary (speculative-ready)
- idtp_planar_cycle_eq_const_mul (planar_constancy, this node's prerequisite)

No accepted lemma already states any child. In particular:
- No accepted lemma states cone-support dilation invariance or the regular-point support identity.
- No accepted lemma gives existence of approximate tangent planes for C¹ submanifolds. This is why sheet_first_variation uses the density argument plus approxTangent_le_submanifold_tangentSpace.
- The decomposing node codim1_density_one_regular_local_rep covers only density 1 and is not accepted.

SimonGMT supplies the area formula integral_area_formula_of_injective_derivative (areaJacobianAt = normDet; areaJacobianAt_eq_sqrt_det_gram is in AreaParametrization.lean) and ae_eq_const_of_weak_coordinate_derivatives_zero, which takes C¹ test functions. These modules are outside the base import closure, so only proofs, never the frozen statements, use them; other worktrees already add these imports. The SimonGMT definitions of support, zeroRegion and test forms (ContDiff ∞ with compact support) match the arguments in the proofs.

Mathlib supplies euclideanHausdorffMeasure_zero_or_top, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Isometry.euclideanHausdorffMeasure_image and addHaar_ball_of_pos.

The proposed names idtp_ccd_* are unreserved: there is no match in dag.json, the run nodes, or any worktree Submission.

Lean check: all 7 child types elaborate after import GMT.Ch07.Submission in namespace GMT.Ch07. The hypothesis-only assembly proves the frozen parent type with axioms propext, Classical.choice and Quot.sound.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
