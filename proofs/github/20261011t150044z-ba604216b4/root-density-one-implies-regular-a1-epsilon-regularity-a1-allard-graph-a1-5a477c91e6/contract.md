<!-- theorem-id: gmt-ch07/root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1 -->

## Theorem `Submission.dor_allard_bounded_curvature_graph`

Let n ≥ 1 and k ≥ 0. For every ε > 0 there are δ₀ > 0 and γ ∈ (0, 1] with the following property. Let U ⊆ ℝ^{n+k} be any set, R = (M, θ, ξ) an integer multiplicity triple in U (IMRep) with weight μ_R = θHⁿ⌞M (R.measure), W ⊆ U open, κ ∈ ℝ, ρ > 0, z ∈ ℝ^{n+k}, and H : ℝ^{n+k} → ℝ^{n+k} μ_R-a.e. strongly measurable with |H(x)| ≤ κ for all x, such that v(M, θ) has generalized mean curvature H in W: R.firstVariation X = ∫_M θ div_M X dHⁿ = −∫⟨X, H⟩ dμ_R for every C¹ compactly supported vector field X with tsupport X ⊆ W (div_M X(x) = trace(p_{T_xM}∘DX(x)), T_xM the approximate tangent plane of M). If the closed ball B̄_ρ(z) ⊆ W, z ∈ spt μ_R, μ_R(B̄_ρ(z)) ≤ (1 + δ₀)ω_nρⁿ and κρ ≤ δ₀, then there are linear isometries ι : ℝⁿ → ℝ^{n+k} and ι' : ℝ^k → ℝ^{n+k} with ⟨ιv, ι'w⟩ = 0 for all v, w, and u : ℝⁿ → ℝ^k with u(0) = 0, u of class C¹ on the open ball B_{γρ}(0) ⊆ ℝⁿ with ‖Du(v)‖ ≤ ε there, such that spt μ_R ∩ B_{γρ}(z) = {z + ιv + ι'u(v) : |v| < γρ} ∩ B_{γρ}(z) (open balls). This is Allard's Regularity Theorem (Simon Ch. 5, 5.2 with Remark 5.3) for integer multiplicity varifolds with bounded generalized mean curvature, i.e. the case p = 2n of hypotheses 5.1.

Node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/679

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/1952, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1954, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1957, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1983, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1990, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2008, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2015, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2022, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2027, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2043, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2055, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2087

## Lean problem

Declaration: `Submission.dor_allard_bounded_curvature_graph`

```lean
∀ (n k : ℕ), 0 < n → ∀ ε : ℝ, 0 < ε → ∃ δ₀ γ : ℝ, 0 < δ₀ ∧ 0 < γ ∧ γ ≤ 1 ∧ ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ₀) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ₀ → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ u 0 = 0 ∧ ContDiffOn ℝ 1 u (ball 0 (γ * ρ)) ∧ (∀ v ∈ ball (0 : Euclid n) (γ * ρ), ‖fderiv ℝ u v‖ ≤ ε) ∧ R.measure.support ∩ ball z (γ * ρ) = ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) (γ * ρ)) ∩ ball z (γ * ρ)
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

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 5 §§2–5, the proof of the Allard Regularity Theorem 5.2 (chapter-05.txt lines 1008–1032 for 5.1–5.2; Lemma 2.1, Remark 2.2, (2.3)–(2.4), Affine Approximation 2.5, Lipschitz Approximation 2.6, Corollary 2.7, Harmonic Approximation 3.1–3.4, Tilt-excess Decay 4.5–4.6 and the proof of 5.2, printed pp. 106–124), with the monotonicity identity of Ch. 4, 3.3–3.17 (chapter-04.txt lines 215–455). The printed proof is copied with p := 2n and bounded mean curvature: since |H| ≤ κ, each term ρ^{1−n/p}(∫_{B_ρ}|H|^p dμ)^{1/p} of Simon is at most C(n)κρ, so Simon's smallness hypothesis on H is replaced by κρ ≤ δ, Simon's E_* by E_*(ξ, r, S) := max{E(ξ, r, S), δ^{−1}κ²r²}, Simon's decay exponent 2(1 − n/p) equals 1, and the bounded-H monotonicity 3.17 replaces 4.7. Departures from the printed text are marked Correction.

Notation. E := ℝ^{n+k}; B_t(x) is the closed ball, B̆_t(x) the open ball (Lean ball); Bⁿ, B̆ⁿ denote balls in ℝⁿ or in an n-plane; ω_n := unitBallVolume n. M := R.carrier, θ := R.mult (a positive integer on M), μ := R.measure = θHⁿ⌞M with Hⁿ := μHE[n]. Since W ⊆ U is open and IMRep.locallyIntegrable_mult holds on compact subsets of U, μ and Hⁿ⌞M are finite on compact subsets of W. For Hⁿ-a.e. (hence μ-a.e.) x ∈ M the approximate tangent plane T_xM := approxTangentPlane n M x exists and is n-dimensional (IMRep.orients); p_x is the orthogonal projection onto T_xM and p_x^⊥ := I − p_x. For an n-plane S, p_S and p_S^⊥ := I − p_S. |A| is the Hilbert–Schmidt norm and ‖A‖ ≤ |A| the operator norm. div_M X(x) := trace(p_x∘DX(x)), so R.firstVariation X = ∫ div_M X dμ. The hypothesis is (MC): ∫ div_M X dμ = −∫ X·H dμ for every C¹ compactly supported X : E → E with tsupport X ⊆ W; and |H| ≤ κ everywhere (so κ ≥ 0). Tilt-excess (Simon 4.1): E(ξ, r, S) := r^{−n}∫_{B_r(ξ)}|p_x − p_S|² dμ(x). α := 1/(2n+2). No translation, dilation or rotation of R is used: balls have arbitrary centres and rotations are only choices of orthonormal coordinates. For readability we write z = 0 (read B_t(y) as B_t(z + y)).

Part 0. Constants.
0.1 Fix c₀ = c₀(n, k) ∈ (0, 1/4] as in 8.6 and put L₀ := min{ε, c₀}.
0.2 Parts 2–8 introduce finitely many smallness thresholds for δ, each depending only on n, k and L₀; δ_A ∈ (0, 1/8] denotes their minimum. We prove (★): if δ := δ_A and (SA) below holds for some ρ > 0, then there are an n-plane T₀ and a map f : T₀ → T₀^⊥, C¹ on A := {v ∈ T₀ : |v| < δρ/16} with ‖Df‖ ≤ L₀ there and f(0) = 0, such that spt μ ∩ B̆_{δρ/16}(0) = {v + f(v) : v ∈ A} ∩ B̆_{δρ/16}(0). Part 9 derives the Lean statement with δ₀ := δ_A and γ := δ_A/16.

Part 1. Monotonicity and densities (Simon Ch. 4, 3.3–3.17, 4.10; Ch. 3, 1.5).
1.1 Let y ∈ E, R > 0 with B_R(y) ⊆ W, r := |x − y|, D^⊥r(x) := p_x^⊥((x − y)/r). Then for 0 < s < t < R:
 (M1) ∫_{B_t(y)∖B_s(y)} r^{−n}|D^⊥r|² dμ ≤ e^{κt}t^{−n}μ(B_t(y)) − e^{κs}s^{−n}μ(B_s(y));
 (M2) e^{−κt}t^{−n}μ(B_t(y)) − e^{−κs}s^{−n}μ(B_s(y)) ≤ ∫_{B_t(y)∖B_s(y)} r^{−n}|D^⊥r|² dμ.
 Here r^{−n}|D^⊥r|² = |x − y|^{−n−2}|p_x^⊥(x − y)|².
 Proof (Simon 3.2–3.6, 3.16–3.17). Let ε' ∈ (0, 1) with (1+ε')t < R and φ ∈ C¹(ℝ) with 0 ≤ φ ≤ 1, φ' ≤ 0, φ ≡ 1 on (−∞, 1], φ ≡ 0 on [1+ε', ∞). For τ ∈ (0, t] let X_τ(x) := φ(r/τ)(x − y); it is C¹ (it equals x − y near y) with tsupport in B_{(1+ε')τ}(y) ⊆ W. At μ-a.e. x, DX_τ = φ(r/τ)I + τ^{−1}φ'(r/τ)(x − y)⊗∇r, so div_M X_τ = nφ(r/τ) + (r/τ)φ'(r/τ)(1 − |D^⊥r|²), because trace p_x = n and p_x∇r·∇r = 1 − |D^⊥r|². With I(τ) := ∫φ(r/τ)dμ and J(τ) := ∫φ(r/τ)|D^⊥r|²dμ (C¹ in τ by differentiation under the integral) and (r/τ)φ'(r/τ) = −τ∂_τ[φ(r/τ)], (MC) gives nI(τ) − τI'(τ) + τJ'(τ) = −h(τ), where h(τ) := ∫φ(r/τ)(x − y)·H dμ and |h(τ)| ≤ (1+ε')κτI(τ). Thus g(τ) := τ^{−n}I(τ) satisfies g' = τ^{−n}J' + e with |e| ≤ cg, c := (1+ε')κ; as J' ≥ 0, (e^{cτ}g)' ≥ τ^{−n}J' and (e^{−cτ}g)' ≤ τ^{−n}J'. Integrating over [s, t]: ∫_s^t τ^{−n}J' dτ ≤ e^{ct}g(t) − e^{cs}g(s) and e^{−ct}g(t) − e^{−cs}g(s) ≤ ∫_s^t τ^{−n}J' dτ. By Fubini (Simon 3.5), ∫_s^t τ^{−n}J'(τ)dτ = ∫|D^⊥r|²(∫_s^t τ^{−n}∂_τφ(r/τ)dτ)dμ, and the inner integral lies between r^{−n}(φ(r/t) − φ(r/s)) and (1+ε')ⁿr^{−n}(φ(r/t) − φ(r/s)); moreover 1_{B_t∖B_{(1+ε')s}} ≤ φ(r/t) − φ(r/s) ≤ 1_{B_{(1+ε')t}∖B_s} and μ(B_τ(y)) ≤ I(τ) ≤ μ(B_{(1+ε')τ}(y)). Letting ε' ↓ 0 (closed balls decrease to closed balls) gives (M1) and (M2).
1.2 Consequences. (a) τ ↦ e^{κτ}τ^{−n}μ(B_τ(y)) is nondecreasing on (0, R) (cf. library HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn). (b) Θ(μ, y) := lim_{τ↓0} μ(B_τ(y))/(ω_nτⁿ) exists in [0, ∞) for every y ∈ W. (c) For 0 < t < R: ∫_{B_t(y)} |x − y|^{−n−2}|p_x^⊥(x − y)|² dμ ≤ e^{κt}t^{−n}μ(B_t(y)) − ω_nΘ(μ, y) (let s ↓ 0 in (M1); μ({y}) = 0 as n ≥ 1). (d) If μ(B_s(y)) = 0 then μ(B_t(y)) ≤ e^{κt}tⁿ∫_{B_t(y)∖B_s(y)} |x − y|^{−n−2}|p_x^⊥(x − y)|² dμ (by (M2)).
1.3 Θ(μ, y) ≥ 1 for y ∈ spt μ ∩ W (Simon Ch. 4, 4.10(1)). (i) If x ∈ M and T_xM exists, then Hⁿ(M ∩ B_τ(x))/(ω_nτⁿ) → 1 (Simon Ch. 3, 1.5(3): test the definition of the approximate tangent plane with continuous compactly supported functions squeezed between the indicators of B_{1−ε''}(0) and B_{1+ε''}(0)); as μ ≥ Hⁿ⌞M, Θ(μ, x) ≥ 1. So Θ(μ, ·) ≥ 1 μ-a.e. in W. (ii) Θ(μ, ·) is upper semicontinuous on W: if y_j → y ∈ W and B_{τ+ε''}(y) ⊆ W, then B_τ(y_j) ⊆ B_{τ+ε''}(y) for large j and 1.2(a) gives Θ(μ, y_j) ≤ ω_n^{−1}e^{κτ}τ^{−n}μ(B_{τ+ε''}(y)); let j → ∞, then ε'' ↓ 0, then τ ↓ 0. (iii) If y ∈ spt μ ∩ W, every B̆_{1/j}(y) has positive μ-measure, hence contains x_j with Θ(μ, x_j) ≥ 1; by (ii), Θ(μ, y) ≥ 1.
1.4 Hⁿ((spt μ ∩ W) ∖ M) = 0. Let A' := (spt μ ∩ W) ∖ M, so μ(A') = 0. Given ε'' > 0 choose an open O with A' ⊆ O ⊆ W and μ(O) < ε'' (outer regularity of the Radon measure μ⌞W). For x ∈ A' the upper n-density of μ⌞O at x equals Θ(μ, x) ≥ 1, so the comparison theorem (Simon Ch. 1, 3.3; library simon_theorem_3_3) gives Hⁿ(A') ≤ μ(O) < ε''.
1.5 θ(x) ≤ Θ(μ, x) for Hⁿ-a.e. x ∈ M ∩ W. For an integer m ≥ 1 let M_m := {x ∈ M : θ(x) = m}. By the Upper Density Theorem (Simon Ch. 1, 3.6 and Remark 3.7(2) for the locally finite measure Hⁿ⌞(M ∩ W); library simon_theorem_3_6), the upper density of Hⁿ⌞(M ∖ M_m) vanishes at Hⁿ-a.e. x ∈ M_m ∩ W; with 1.3(i), Hⁿ(M_m ∩ B_τ(x))/(ω_nτⁿ) → 1 there, and μ ≥ m·Hⁿ⌞M_m gives Θ(μ, x) ≥ m = θ(x).
1.6 Tangent planes on a Lipschitz graph (Simon Ch. 3, 1.5(2) and the proof of 1.6). Let S be an n-plane, a ∈ E, f : S → S^⊥ Lipschitz, Φ_f(v) := a + v + f(v), F := Φ_f(S). Then for Hⁿ-a.e. x ∈ M ∩ F ∩ W, writing x = Φ_f(v): f is differentiable at v and T_xM = graph Df(v) := {w + Df(v)w : w ∈ S}.
 Proof. (i) By Rademacher's theorem (Mathlib LipschitzWith.ae_differentiableAt) and Lebesgue's differentiation theorem, Lⁿ-a.e. v ∈ S is a differentiability point of f and a Lebesgue point of Df; the exceptional set N satisfies Hⁿ(Φ_f(N)) = 0 because Φ_f is Lipschitz. (ii) For v ∉ N, F has approximate tangent plane graph Df(v) at x = Φ_f(v): for ψ₀ ∈ C_c(E) with spt ψ₀ ⊆ B_{R'}(0), the area formula gives ∫_{η_{x,λ}(F)} ψ₀ dHⁿ = ∫_S ψ₀(w + f_λ(w)) J_f(v + λw) dw, where f_λ(w) := (f(v + λw) − f(v))/λ and J_f is the area Jacobian of Φ_f; the integrand vanishes for |w| > R' and is uniformly bounded; f_λ → Df(v) locally uniformly and J_f(v + λ·) → J_f(v) in L¹_loc (Lebesgue point of Df; the Jacobian is a locally Lipschitz function of Df), so the integral tends to ∫_S ψ₀(w + Df(v)w) J_f(v) dw = ∫_{graph Df(v)} ψ₀ dHⁿ. (iii) By the Upper Density Theorem, for Hⁿ-a.e. x ∈ M ∩ F ∩ W the upper densities of Hⁿ⌞(F ∖ M) and of Hⁿ⌞(M ∖ F) at x vanish (both sets have locally finite Hⁿ-measure in W). (iv) At such x with v ∉ N, |∫_{η_{x,λ}(M)} ψ₀ dHⁿ − ∫_{η_{x,λ}(F)} ψ₀ dHⁿ| ≤ sup|ψ₀|·λ^{−n}Hⁿ(((M ∖ F) ∪ (F ∖ M)) ∩ B_{λR'}(x)) → 0, so M has approximate tangent plane graph Df(v) at x, and by uniqueness (HasApproximateTangentSpaceAt.unique) T_xM = graph Df(v).

Part 2. Standing assumption and density bounds (Simon 2.3–2.4).
(SA) δ ∈ (0, 1/8], ρ > 0, 0 ∈ spt μ, B_ρ(0) ⊆ W, μ(B_ρ(0)) ≤ (1 + δ)ω_nρⁿ and κρ ≤ δ. Put r₁ := δρ. As B_ρ(0) is compact and W open, fix ρ⁺ ∈ (ρ, 2ρ) with B_{ρ⁺}(0) ⊆ W. For y ∈ B_{4r₁}(0) we have B_{ρ⁺−4r₁}(y) ⊆ W and ρ⁺ − 4r₁ > (1 − 4δ)ρ ≥ ρ/2 ≥ 4r₁; so 1.1–1.2 apply at y for all radii ≤ (1 − 4δ)ρ.
2.1 For every y ∈ B_{4r₁}(0) and 0 < t ≤ (1 − 4δ)ρ: μ(B_t(y)) ≤ (1 + c(δ))ω_ntⁿ with c(δ) := e^{δ}(1 − 4δ)^{−n}(1 + δ) − 1 ≤ C₁δ. Indeed by 1.2(a) with t' := (1 − 4δ)ρ and B_{t'}(y) ⊆ B_ρ(0): t^{−n}μ(B_t(y)) ≤ e^{κt'}t'^{−n}μ(B_ρ(0)) ≤ e^{δ}(1 − 4δ)^{−n}(1 + δ)ω_n.
2.2 For every y ∈ spt μ ∩ B_{4r₁}(0) and 0 < t ≤ (1 − 4δ)ρ: μ(B_t(y)) ≥ e^{−δ}ω_ntⁿ, by 1.2(a) and 1.3: e^{κt}t^{−n}μ(B_t(y)) ≥ ω_nΘ(μ, y) ≥ ω_n. Fix δ₁ = δ₁(n) ∈ (0, 1/8] with C₁δ₁ ≤ 1/2; for δ ≤ δ₁ we get ½ω_ntⁿ ≤ μ(B_t(y)) ≤ 2ω_ntⁿ (Simon 2.4). Correction: Simon states 2.4 for y ∈ B_{δρ}(0) and t ≤ (1 − δ)ρ but uses it at points of B_{3δρ}(0); the enlarged range is proved identically.
2.3 For every y ∈ spt μ ∩ B_{4r₁}(0) and 0 < t ≤ (1 − 4δ)ρ: ∫_{B_t(y)} |x − y|^{−n−2}|p_x^⊥(x − y)|² dμ ≤ ω_n(e^{δ}(1 + c(δ)) − 1) ≤ C₂δ, by 1.2(c), 2.1 and Θ(μ, y) ≥ 1.
2.4 For δ ≤ δ₁, θ = 1 at μ-a.e. point of B_{4r₁}(0): by 1.5 and 2.1, θ(x) ≤ Θ(μ, x) ≤ 1 + c(δ) < 2 there, and θ is a positive integer. Correction: this replaces Simon's '1 ≤ θ ≤ 1 + Cδ (by 2.5)' in the proof of 4.5.

Part 3. Tilt controlled by height (Simon 2.1–2.2).
3.1 If B_r(ξ) ⊆ W and S is an n-plane, then E(ξ, r/2, S) ≤ C₃'[r^{−n}∫_{B_r(ξ)} (dist(x − ξ, S)/r)² dμ + κ²r²·r^{−n}μ(B_r(ξ))], with C₃' = C₃'(n).
 Proof (Simon 2.1). Let q := p_S^⊥ and ζ ∈ C¹_c(B̆_r(ξ)) with 0 ≤ ζ ≤ 1, ζ ≡ 1 on B_{r/2}(ξ), |∇ζ| ≤ 3/r. X(x) := ζ(x)²q(x − ξ) is C¹ with compact support in W. At μ-a.e. x, div_M X = ζ² trace(p_x q) + 2ζ ∇ζ·p_x q(x − ξ), where trace(p_x q) = n − trace(p_x p_S) = ½|p_x − p_S|² and p_x q(x − ξ) = (p_x − p_S)q(x − ξ) (as p_S q = 0), so |∇ζ·p_x q(x − ξ)| ≤ |∇ζ||p_x − p_S||q(x − ξ)|. By (MC) and 2ab ≤ ¼a² + 4b²: ½∫ζ²|p_x − p_S|² ≤ ¼∫ζ²|p_x − p_S|² + 4∫|∇ζ|²|q(x − ξ)|² + ∫ζ²|q(x − ξ)||H|. With |q(x − ξ)||H| ≤ ½r^{−2}|q(x − ξ)|² + ½r²|H|², |q(x − ξ)| = dist(x − ξ, S) and |H| ≤ κ: ∫_{B_{r/2}(ξ)} |p_x − p_S|² dμ ≤ C r^{−2}∫_{B_r(ξ)} dist(x − ξ, S)² dμ + C r²κ²μ(B_r(ξ)). Multiply by (r/2)^{−n}.

Part 4. Affine approximation (Simon 2.5).
Assume (SA) with δ ≤ δ₁. For every ξ ∈ spt μ ∩ B_{2r₁}(0) and r ∈ (0, 2r₁] there is an n-plane S = S(ξ, r) with
 (4a) dist(x − ξ, S) ≤ C₃δ^α r for all x ∈ spt μ ∩ B_r(ξ), and (4b) E(ξ, r/2, S) ≤ C₃δ^{2α}.
Correction: Simon's (‡) writes the two quantities as a chain of inequalities; what is proved and used is that each is bounded as in (4a), (4b).
 Proof. Every point y used below lies in spt μ ∩ B_r(ξ) ⊆ B_{4r₁}(0) and every radius is ≤ 2r ≤ 4r₁ ≤ (1 − 4δ)ρ, so 2.1–2.3 apply. (i) Choose a maximal family y₁, …, y_N in K := spt μ ∩ B_r(ξ) with |y_i − y_j| > δ^αr for i ≠ j. The balls B_{δ^αr/2}(y_j) are disjoint, lie in B_{2r}(ξ), and have μ-measure ≥ ½ω_n(δ^αr/2)ⁿ, while μ(B_{2r}(ξ)) ≤ 2ω_n(2r)ⁿ; hence N ≤ 2^{2n+2}δ^{−αn}. By maximality K ⊆ ∪_j B_{δ^αr}(y_j). (ii) For each j, B_r(ξ) ⊆ B_{2r}(y_j), so by 2.3, ∫_{B_r(ξ)} |p_x^⊥(x − y_j)|² dμ ≤ (2r)^{n+2}C₂δ. (iii) Hence Ψ(x) := Σ_j |p_x^⊥(x − y_j)|² satisfies ∫_{B_r(ξ)} Ψ dμ ≤ Cδ^{1−αn}r^{n+2}. (iv) With λ := (4/ω_n)Cδ^{1−2αn}r², Chebyshev's inequality gives μ({x ∈ B_r(ξ) : Ψ(x) > λ}) ≤ ¼ω_nδ^{αn}rⁿ < ½ω_n(δ^αr)ⁿ ≤ μ(B_{δ^αr}(ξ)). So there is x₀ ∈ spt μ ∩ M ∩ B_{δ^αr}(ξ) at which T_{x₀}M exists and Ψ(x₀) ≤ λ. (v) Then |p_{x₀}^⊥(y_j − x₀)| ≤ λ^{1/2} = Cδ^{1/2−αn}r = Cδ^αr (as ½ − αn = α), and since |x₀ − ξ| ≤ δ^αr, |p_{x₀}^⊥(y_j − ξ)| ≤ (C + 1)δ^αr for all j. (vi) Let S := T_{x₀}M. For x ∈ K choose j with |x − y_j| ≤ δ^αr; then dist(x − ξ, S) = |p_{x₀}^⊥(x − ξ)| ≤ (C + 2)δ^αr, which is (4a). (vii) By 3.1 at (ξ, r) (B_r(ξ) ⊆ B_ρ(0) ⊆ W), (4a), μ(B_r(ξ)) ≤ 2ω_nrⁿ and κr ≤ κρ ≤ δ: E(ξ, r/2, S) ≤ C₃'(2ω_n(C + 2)²δ^{2α} + 2ω_nδ²) ≤ C₃δ^{2α}.

Part 5. Lipschitz approximation and graph criterion (Simon 2.6–2.7).
Setting: (SA) with δ ≤ δ₁; ξ ∈ spt μ ∩ B_{r₁}(0); σ₀ ∈ (0, r₁]; a constant C₆ ≥ 1; an n-plane T₀ with (i) E(ξ, σ₀, T₀) ≤ C₆δ^{2α} and (ii) dist(x − ξ, T₀) ≤ C₆δ^ασ₀ for all x ∈ spt μ ∩ B_{σ₀}(ξ). Let P := p_{T₀}, Q := p_{T₀}^⊥, and for g : T₀ → T₀^⊥ let Φ_g(v) := ξ + v + g(v) and graph_ξ g := Φ_g(T₀). Let L ∈ (0, 1].
5A. There are β = β(n, k, C₆) ∈ (0, 1/4] and C₇ = C₇(n, k, C₆) such that if δ^α ≤ βL there is a Lipschitz f : T₀ → T₀^⊥ with Lip f ≤ L, sup|f| ≤ C₇δ^ασ₀ and, for F := graph_ξ f,
 μ(B_{σ₀/2}(ξ) ∖ F) + Hⁿ((F ∖ spt μ) ∩ B_{σ₀/4}(ξ)) ≤ C₇L^{−2}σ₀ⁿE(ξ, σ₀, T₀).
5B. There is β' = β'(n, k, C₆) ∈ (0, β] such that if in addition E(y, t, T₀) ≤ β'²L² for all y ∈ spt μ ∩ B_{σ₀/2}(ξ) and t ∈ (0, σ₀/2], then spt μ ∩ B_{σ₀/8}(ξ) = F ∩ B_{σ₀/8}(ξ).
Correction: Simon states the Hⁿ-estimate on B_{σ₀/2} and 2.7 on B_{σ₀/4}, and omits the factor σ₀ in sup|f|; with the covering radii below the argument gives B_{σ₀/4} and B_{σ₀/8}.
Proof. Points used below are y ∈ B_{3σ₀/4}(ξ) ⊆ B_{2r₁}(0) and η ∈ B_{σ₀/4}(ξ); all radii are ≤ 5σ₀/4 ≤ (1 − 4δ)ρ; so 1.2, 2.1–2.3 and Part 4 apply.
(a) G := {y ∈ spt μ ∩ B_{3σ₀/4}(ξ) : t^{−n}∫_{B_{t/2}(y)} |p_x − p_{T₀}|² dμ ≤ β²L² for all t ∈ (0, σ₀/2]}.
(b) μ(B_{3σ₀/4}(ξ) ∖ G) ≤ Cβ^{−2}L^{−2}σ₀ⁿE(ξ, σ₀, T₀). For y ∈ (spt μ ∩ B_{3σ₀/4}(ξ)) ∖ G pick t_y ∈ (0, σ₀/2] with β²L²t_yⁿ < ∫_{B_{t_y/2}(y)} |p_x − p_{T₀}|² dμ. By the 5-times covering lemma (Simon Ch. 1, 3.4; Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall) there are countably many disjoint B_{t_j/2}(y_j) from this family with (spt μ ∩ B_{3σ₀/4}(ξ)) ∖ G ⊆ ∪_j B_{5t_j/2}(y_j). Using μ(E ∖ spt μ) = 0, μ(B_{5t_j/2}(y_j)) ≤ 2ω_n(5t_j/2)ⁿ and that the disjoint balls lie in B_{σ₀}(ξ): μ(B_{3σ₀/4}(ξ) ∖ G) ≤ CΣ_j t_jⁿ ≤ Cβ^{−2}L^{−2}Σ_j ∫_{B_{t_j/2}(y_j)} |p_x − p_{T₀}|² ≤ Cβ^{−2}L^{−2}∫_{B_{σ₀}(ξ)} |p_x − p_{T₀}|² dμ.
(c) There is C₈ = C₈(n, k, C₆) with |Q(y₂ − y₁)| ≤ C₈βL|y₂ − y₁| for y₁, y₂ ∈ G. Let t := |y₁ − y₂| ≤ 3σ₀/2. If t ≤ σ₀/2: Part 4 at (y₁, t) gives S₁ with dist(y₂ − y₁, S₁) ≤ C₃δ^αt and ∫_{B_{t/2}(y₁)} |p_x − p_{S₁}|² ≤ C₃δ^{2α}(t/2)ⁿ, while y₁ ∈ G gives ∫_{B_{t/2}(y₁)} |p_x − p_{T₀}|² ≤ β²L²tⁿ; since |p_{S₁} − p_{T₀}|² ≤ 2|p_x − p_{S₁}|² + 2|p_x − p_{T₀}|² and μ(B_{t/2}(y₁)) ≥ ½ω_n(t/2)ⁿ, |p_{S₁} − p_{T₀}| ≤ C(βL + δ^α) ≤ CβL, hence |Q(y₂ − y₁)| ≤ dist(y₂ − y₁, S₁) + ‖p_{S₁} − p_{T₀}‖t ≤ C₈βLt. If t > σ₀/2: by (ii), |Q(y₂ − y₁)| ≤ 2C₆δ^ασ₀ < 4C₆δ^αt ≤ 4C₆βLt. Correction: Simon treats only the first case. With C₈β ≤ ½ this gives |Q(y₂ − y₁)| ≤ 2C₈βL|P(y₂ − y₁)|; so P is injective on G and g₀(P(y − ξ)) := Q(y − ξ), y ∈ G, is Lipschitz with constant 2C₈βL.
(d) Extend each coordinate of g₀ (with respect to an orthonormal basis of T₀^⊥) to all of T₀ with the same Lipschitz constant (Simon Ch. 2, 1.2; Mathlib LipschitzOnWith.extend_real) and truncate it to [−C₆δ^ασ₀, C₆δ^ασ₀]; by (ii) this does not change it on P(G − ξ). The resulting f satisfies f = g₀ on P(G − ξ), Lip f ≤ 2√k C₈βL ≤ L (we require 2√k C₈β ≤ 1), sup|f| ≤ √k C₆δ^ασ₀, and G ⊆ F.
(e) μ(B_{σ₀/2}(ξ) ∖ F) ≤ μ(B_{3σ₀/4}(ξ) ∖ G), bounded by (b).
(f) Let η ∈ (F ∖ spt μ) ∩ B_{σ₀/4}(ξ). Then d := dist(η, spt μ) ∈ (0, |η − ξ|] and s_η := d/2 ≤ σ₀/8; B_{s_η}(η) ∩ spt μ = ∅, so μ(B_{s_η}(η)) = 0, and some y ∈ spt μ has |y − η| = 2s_η, whence y ∈ B_{σ₀/2}(ξ). By 2.1–2.2 at y: ½ω_ns_ηⁿ ≤ μ(B_{s_η}(y)) ≤ μ(B_{3s_η}(η)) ≤ μ(B_{5s_η}(y)) ≤ 2·5ⁿω_ns_ηⁿ. By 1.2(d) at η: μ(B_{3s_η}(η)) ≤ e^{δ}3ⁿs_η^{−2}∫_{B_{3s_η}(η)} |p_x^⊥(x − η)|² dμ. Now p_x^⊥ − Q = p_{T₀} − p_x; for x ∈ F ∩ B_{3s_η}(η), |Q(x − η)| = |f(P(x − ξ)) − f(P(η − ξ))| ≤ 2√k C₈β·3s_η; for x ∉ F, |Q(x − η)| ≤ 3s_η. Hence ½ω_ns_ηⁿ ≤ C[β²μ(B_{3s_η}(η)) + μ(B_{3s_η}(η) ∖ F) + ∫_{B_{3s_η}(η)} |p_x − p_{T₀}|² dμ], and choosing β so small that Cβ²·2·5ⁿω_n ≤ ¼ω_n:
 (10') s_ηⁿ ≤ C₉[μ(B_{3s_η}(η) ∖ F) + ∫_{B_{3s_η}(η)} |p_x − p_{T₀}|² dμ].
 Correction: Simon's (9)–(11) write B_σ(η) where B_{3σ}(η) is meant; with bounded H the additive error Cδσⁿ in (9) does not occur.
 The closed balls B_{3s_η}(η) cover (F ∖ spt μ) ∩ B_{σ₀/4}(ξ); by the 5-times covering lemma choose disjoint B_{3s_j}(η_j) with (F ∖ spt μ) ∩ B_{σ₀/4}(ξ) ⊆ ∪_j B_{15s_j}(η_j). As F is the graph of a 1-Lipschitz map, Hⁿ(F ∩ B_{15s_j}(η_j)) ≤ 2^{n/2}ω_n(15s_j)ⁿ (LipschitzOnWith.hausdorffMeasure_image_le for Φ_f). The disjoint balls B_{3s_j}(η_j) lie in B_{5σ₀/8}(ξ) ⊆ B_{3σ₀/4}(ξ); so by (10'), G ⊆ F and (b): Hⁿ((F ∖ spt μ) ∩ B_{σ₀/4}(ξ)) ≤ CΣ_j s_jⁿ ≤ C[μ(B_{3σ₀/4}(ξ) ∖ G) + ∫_{B_{σ₀}(ξ)} |p_x − p_{T₀}|²] ≤ Cβ^{−2}L^{−2}σ₀ⁿE(ξ, σ₀, T₀). With (e) this proves 5A.
(g) Proof of 5B. For y ∈ spt μ ∩ B_{σ₀/2}(ξ) and t ∈ (0, σ₀/2], t^{−n}∫_{B_{t/2}(y)} |p_x − p_{T₀}|² ≤ E(y, t, T₀) ≤ β'²L² ≤ β²L², so y ∈ G ⊆ F; thus spt μ ∩ B_{σ₀/2}(ξ) ⊆ F. Suppose η ∈ (F ∖ spt μ) ∩ B_{σ₀/8}(ξ) and let s_η, y be as in (f). Then s_η ≤ σ₀/16 and B_{3s_η}(η) ⊆ B_{σ₀/2}(ξ), so μ(B_{3s_η}(η) ∖ F) = 0; also y ∈ spt μ ∩ B_{σ₀/4}(ξ), B_{3s_η}(η) ⊆ B_{5s_η}(y) and 5s_η ≤ σ₀/2, so ∫_{B_{3s_η}(η)} |p_x − p_{T₀}|² ≤ (5s_η)ⁿβ'²L². Then (10') gives s_ηⁿ ≤ C₉5ⁿβ'²s_ηⁿ, impossible if C₉5ⁿβ'² < 1. Hence F ∩ B_{σ₀/8}(ξ) ⊆ spt μ and spt μ ∩ B_{σ₀/8}(ξ) = F ∩ B_{σ₀/8}(ξ).

Part 6. Harmonic approximation (Simon 3.1–3.4).
6.1 For every ε' > 0 there is δ_h = δ_h(n, ε') > 0 such that: if R₀ > 0 and w ∈ W^{1,2}(B̆ⁿ_{R₀}(0)) satisfy R₀^{−n}∫|∇w|² ≤ 1 and |∫∇w·∇ζ| ≤ δ_hR₀ⁿ sup|∇ζ| for every ζ ∈ C¹_c(B̆ⁿ_{R₀}(0)), then there is a harmonic h on B̆ⁿ_{R₀}(0) with R₀^{−n}∫|∇h|² ≤ 1 and R₀^{−n−2}∫(h − w)² ≤ ε'.
 Proof. The substitution w(x) = R₀w₁(x/R₀) reduces to R₀ = 1. If the claim fails, there are ε' > 0 and w_j ∈ W^{1,2}(B), B := B̆ⁿ₁(0), with ∫_B|∇w_j|² ≤ 1, |∫_B∇w_j·∇ζ| ≤ j^{−1}sup|∇ζ| for all ζ ∈ C¹_c(B), and ∫_B(w_j − h)² > ε' for every harmonic h on B with ∫_B|∇h|² ≤ 1. Let λ_j be the mean of w_j over B. By the Poincaré inequality ∫_B|w_j − λ_j|² ≤ C, so by Rellich's theorem a subsequence satisfies w_j − λ_j → w in L²(B) and ∇w_j ⇀ ∇w weakly in L²(B), with w ∈ W^{1,2}(B), ∫_B|∇w|² ≤ 1 and ∫_B∇w·∇ζ = lim ∫_B∇w_j·∇ζ = 0 for all ζ ∈ C¹_c(B). By Weyl's lemma w is harmonic; then h_j := w + λ_j is harmonic with ∫_B|∇h_j|² ≤ 1 and ∫_B(w_j − h_j)² → 0 along the subsequence, a contradiction.
6.2 If h is harmonic on B̆ⁿ_{R₀}(0), λ(x) := h(0) + ∇h(0)·x and θ' ∈ (0, ¼], then |h(0)| ≤ CR₀^{−n/2}‖h‖_{L²(B_{R₀})}, |∇h(0)| ≤ CR₀^{−n/2}‖∇h‖_{L²(B_{R₀})} and sup over Bⁿ_{θ'R₀}(0) of |h − λ| ≤ Cθ'²R₀^{1−n/2}‖∇h‖_{L²(B_{R₀})}, with C = C(n) (mean value property and second-order Taylor expansion; Simon 3.2–3.4).

Part 7. Tilt-excess decay (Simon 4.5–4.6) with p = 2n.
Let E_*(ξ, r, S) := max{E(ξ, r, S), δ^{−1}κ²r²}.
7A. There are θ₀ ∈ (0, 1/4] and δ₂ ∈ (0, δ₁], depending only on n and k, such that under (SA) with δ ≤ δ₂: for every ξ ∈ spt μ ∩ B_{r₁}(0), σ ∈ (0, r₁] and n-plane T there is an n-plane S with E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T).
7B. Any such S satisfies |p_S − p_T|² ≤ C₁₀θ₀^{−n}E_*(ξ, σ, T).
Proof of 7B (Simon 4.6). (θ₀σ)^{−n}∫_{B_{θ₀σ}(ξ)} |p_x − p_T|² ≤ θ₀^{−n}E(ξ, σ, T) and (θ₀σ)^{−n}∫_{B_{θ₀σ}(ξ)} |p_x − p_S|² ≤ E_*(ξ, θ₀σ, S) ≤ E_*(ξ, σ, T); add, using |p_S − p_T|² ≤ 2|p_x − p_T|² + 2|p_x − p_S|² and μ(B_{θ₀σ}(ξ)) ≥ ½ω_n(θ₀σ)ⁿ.
Proof of 7A. C denotes constants depending only on n, k; θ' and ε' are parameters fixed in Step 10 before δ₂.
Step 1 (reduction; Simon (1)–(2)). Part 4 at (ξ, 2σ) gives T̃ with E(ξ, σ, T̃) ≤ C₃δ^{2α} and dist(x − ξ, T̃) ≤ 2C₃δ^ασ on spt μ ∩ B_{2σ}(ξ). If E(ξ, σ, T) > C₃δ^{2α} then E_*(ξ, σ, T̃) ≤ E_*(ξ, σ, T), so it suffices to prove 7A with T̃ in place of T; hence we may assume E(ξ, σ, T) ≤ C₃δ^{2α}. Then |p_T − p_{T̃}|²μ(B_σ(ξ)) ≤ 4C₃δ^{2α}σⁿ gives ‖p_T − p_{T̃}‖ ≤ Cδ^α, and
 (2') dist(x − ξ, T) ≤ C₁₁δ^ασ for all x ∈ spt μ ∩ B_σ(ξ).
 Let E₀ := E_*(ξ, σ, T). Since κσ ≤ κr₁ ≤ δ², δ^{−1}κ²σ² ≤ δ³; so E₀ ≤ C₃δ^{2α}. If E₀ = 0 then E(ξ, σ, T) = 0 and κ = 0, and S := T works (E_*(ξ, θ₀σ, T) ≤ θ₀^{−n}E(ξ, σ, T) = 0). Assume E₀ > 0. Fix orthonormal bases of T and T^⊥ and write x − ξ = (x', x'') ∈ ℝⁿ × ℝ^k; e_{n+j} is the j-th basis vector of T^⊥.
Step 2 (Lipschitz approximation; Simon (3)–(4)). Part 5A at (ξ, σ₀ := σ, T₀ := T, L := 1, C₆ := max{C₃, C₁₁}), which needs δ^α ≤ β, gives f : ℝⁿ → ℝ^k with Lip f ≤ 1, |f| ≤ C₇δ^ασ, F := graph_ξ f and
 (4') μ(B_{σ/2}(ξ) ∖ F) + Hⁿ((F ∖ spt μ) ∩ B_{σ/4}(ξ)) ≤ C₇σⁿE₀.
 Put r := σ/4 and R₀ := r/2 = σ/8. Correction: Simon works on B_σ; since 5A controls F ∖ spt μ only on B_{σ/4}, the harmonic approximation is done on Bⁿ_{σ/8}.
Step 3 (height; Simon (5)). Require C₁₁δ^α ≤ 1/16 and C₇δ^α ≤ 1/16. Then every x ∈ spt μ ∩ B_σ(ξ) with |x'| < r/2 has |x''| ≤ r/4, hence |x − ξ| < 3r/4; and Φ_f(v) := ξ + (v, f(v)) ∈ B̆_{3r/4}(ξ) for |v| < r/2.
Step 4 (equation for fʲ; Simon (6)–(9)). Fix j ∈ {1, …, k}, let f̃ʲ(x) := fʲ(x') and M₁ := M ∩ F. For ζ ∈ C¹_c(B̆_r(ξ)), (MC) with X := ζe_{n+j} gives (6): ∫(p_xe_{n+j})·∇ζ dμ = −∫ζ e_{n+j}·H dμ. By 1.6, for μ-a.e. x = Φ_f(v) ∈ M₁, T_xM = graph Df(v); since τ'·e_{n+j} = τ'·(∇fʲ(v), 0) for τ' ∈ graph Df(v), we get (7): p_xe_{n+j} = p_x(∇fʲ(v), 0) =: ∇^Mf̃ʲ(x). Hence ∫_{M₁}∇^Mf̃ʲ·∇ζ dμ = −∫_{M∖M₁}(p_xe_{n+j})·∇ζ dμ − ∫ζ e_{n+j}·H dμ, and with μ(B_r(ξ) ∖ F) ≤ CrⁿE₀ (4'), sup|ζ| ≤ r sup|∇ζ|, μ(B_r(ξ)) ≤ 2ω_nrⁿ and κr ≤ κσ ≤ (δE₀)^{1/2}:
 (8') |r^{−n}∫_{M₁∩B_r(ξ)} ∇^Mf̃ʲ·∇ζ dμ| ≤ C sup|∇ζ|(δ^{1/2}E₀^{1/2} + E₀).
 Also |∇^Mf̃ʲ| = |p_xe_{n+j}| = |(p_x − p_T)e_{n+j}| ≤ |p_x − p_T| μ-a.e. on M₁, so
 (9') r^{−n}∫_{M₁∩B_r(ξ)} |∇^Mf̃ʲ|² dμ ≤ 4ⁿE(ξ, σ, T) ≤ CE₀.
Step 5 (tests independent of x''; Simon (10)–(13)). Let ζ₀ ∈ C¹_c(B̆ⁿ_{r/2}(0)), ζ̃₀(x) := ζ₀(x'), and h₀ ∈ C¹_c(B̆_r(ξ)) with h₀ ≡ 1 on B_{7r/8}(ξ); put ζ := ζ̃₀h₀ ∈ C¹_c(B̆_r(ξ)). At x ∈ spt μ: if x ∈ B_σ(ξ) and |x'| < r/2, then x ∈ B̆_{3r/4}(ξ) (Step 3) and ζ = ζ̃₀ near x; if x ∈ B_σ(ξ) and |x'| ≥ r/2, then ζ̃₀ and ζ vanish near x (spt ζ₀ is a compact subset of B̆ⁿ_{r/2}(0)); if x ∉ B_σ(ξ), ζ vanishes near x. Hence (8') holds with ∇ζ replaced by ∇ζ̃₀ = (∇ζ₀(x'), 0) and sup|∇ζ| by sup|∇ζ₀|. At μ-a.e. x ∈ M₁, with a := (∇fʲ(x'), 0) and b := ∇ζ̃₀(x) in T: ∇^Mf̃ʲ·∇ζ̃₀ = (p_xa)·b = a·b − (p_Tp_x^⊥p_Ta)·b and p_Tp_x^⊥p_T = (p_T − p_x)p_x^⊥(p_T − p_x), so (11): |∇^Mf̃ʲ·∇ζ̃₀ − ∇fʲ(x')·∇ζ₀(x')| ≤ |p_x − p_T|²|∇fʲ(x')||∇ζ₀(x')|. With |∇fʲ| ≤ 1 and (4'):
 (12') |r^{−n}∫_{M₁∩B_r(ξ)} ∇fʲ(x')·∇ζ₀(x') dμ| ≤ C sup|∇ζ₀|(δ^{1/2}E₀^{1/2} + E₀),
 and applying (11) with b := a and (9'):
 (13') r^{−n}∫_{M₁∩B_r(ξ)} |∇fʲ(x')|² dμ ≤ CE₀.
Step 6 (transfer to ℝⁿ; Simon (14)–(16)). Let J_f(v) := (det(I + Df(v)ᵀDf(v)))^{1/2} ∈ [1, 2^{n/2}], so |J_f − 1| ≤ C|Df|², and θ_F(v) := θ(Φ_f(v)) if Φ_f(v) ∈ M, θ_F(v) := 0 otherwise. By the area formula for the injective Lipschitz map Φ_f (Simon Ch. 2, 3.5) and Step 3, for every Borel g on ℝⁿ supported in B̆ⁿ_{r/2}(0) and nonnegative or integrable: ∫_{M₁∩B_r(ξ)} g(x') dμ = ∫_{Bⁿ_{r/2}(0)} g(v)θ_F(v)J_f(v) dv. Let Z₀ := {v ∈ B̆ⁿ_{r/2}(0) : Φ_f(v) ∉ M} and Z₂ := {v ∈ B̆ⁿ_{r/2}(0) : θ_F(v) ≥ 2}. By 1.4, (4') and J_f ≥ 1: Lⁿ(Z₀) ≤ Hⁿ((F ∖ spt μ) ∩ B_r(ξ)) + Hⁿ((spt μ ∩ W) ∖ M) ≤ C₇σⁿE₀ ≤ CrⁿE₀; by 2.4, Lⁿ(Z₂) = 0. Off Z₀ ∪ Z₂ we have θ_F = 1. Hence from (12'), (13'):
 (16') r^{−n}∫_{Bⁿ_{r/2}(0)} |∇fʲ|² dv ≤ CE₀,
 (15') |r^{−n}∫_{Bⁿ_{r/2}(0)} ∇fʲ·∇ζ₀ dv| ≤ C sup|∇ζ₀|(δ^{1/2}E₀^{1/2} + E₀) ≤ C₁₂δ^αE₀^{1/2} sup|∇ζ₀|,
 using ∫_{Z₀}|∇fʲ||∇ζ₀| ≤ sup|∇ζ₀|Lⁿ(Z₀), |θ_FJ_f − 1| ≤ C|Df|² off Z₀ ∪ Z₂ together with (16'), and E₀ ≤ (C₃δ^{2α})^{1/2}E₀^{1/2}, δ^{1/2} ≤ δ^α. Correction: Simon's (15) has the factor δ^{1/2}E₀^{1/2}; since only E₀ ≤ Cδ^{1/(n+1)} is available, the factor is δ^{1/(2n+2)}E₀^{1/2}, which suffices.
Step 7 (harmonic approximation; Simon (17)). By (16') choose C₁₃ with R₀^{−n}∫_{Bⁿ_{R₀}(0)} |∇fʲ|² ≤ C₁₃E₀. Then w := (C₁₃E₀)^{−1/2}fʲ satisfies the hypotheses of 6.1 on B̆ⁿ_{R₀}(0) provided C₁₄δ^α ≤ δ_h(n, ε'), where C₁₄ := 2ⁿC₁₂C₁₃^{−1/2}. So there are harmonic functions uʲ on B̆ⁿ_{R₀}(0), j = 1, …, k, and u := (u¹, …, uᵏ) satisfies
 (17') R₀^{−n}∫_{Bⁿ_{R₀}(0)} |Du|² ≤ CE₀ and R₀^{−n−2}∫_{Bⁿ_{R₀}(0)} |f − u|² ≤ Cε'E₀.
Step 8 (affine approximation of u; Simon (18)–(19)). Let λ(v) := u(0) + Du(0)v. By 6.2, (17') and |f| ≤ C₇δ^ασ = 8C₇δ^αR₀: |Du(0)| ≤ CE₀^{1/2}, and (18') |u(0)| ≤ CR₀^{−n/2}(‖u − f‖_{L²} + ‖f‖_{L²}) ≤ C₁₅R₀δ^α; and for θ' ∈ (0, ¼], sup over Bⁿ_{θ'R₀}(0) of |u − λ| ≤ Cθ'²R₀E₀^{1/2}. Hence
 (19') (θ'R₀)^{−n−2}∫_{Bⁿ_{θ'R₀}(0)} |f − λ|² dv ≤ C(θ'^{−n−2}ε' + θ'²)E₀.
Step 9 (the new plane; Simon (20)–(22)). Let S := {(w, Du(0)w) : w ∈ ℝⁿ}, an n-plane, and τ := ξ + (0, u(0)). Require C₁₅δ^α ≤ θ'/4; then |τ − ξ| ≤ θ'R₀/4 and B_{θ'R₀}(τ) ⊆ B_{σ/2}(ξ). For x = Φ_f(v) with |v| ≤ θ'R₀, dist(x − τ, S) ≤ |f(v) − λ(v)|, and F ∩ B_{θ'R₀}(τ) ⊆ Φ_f(Bⁿ_{θ'R₀}(0)). Split ∫_{B_{θ'R₀}(τ)} dist(x − τ, S)² dμ into the parts on F and off F. On F, μ⌞F ≤ Hⁿ⌞F (θ = 1 μ-a.e. there by 2.4) and the area formula with J_f ≤ 2^{n/2} bound it by 2^{n/2}∫_{Bⁿ_{θ'R₀}(0)} |f − λ|². Off F, each x ∈ spt μ ∩ B_{θ'R₀}(τ) has dist(x − τ, S) ≤ |x''| + |u(0)| + |Du(0)||x'| ≤ Cδ^ασ by (2') and (18'), and μ(B_{θ'R₀}(τ) ∖ F) ≤ C₇σⁿE₀ by (4'). With σ = 8R₀ this gives
 (θ'R₀)^{−n−2}∫_{B_{θ'R₀}(τ)} dist(x − τ, S)² dμ ≤ C(θ'^{−n−2}ε' + θ'^{−n−2}δ^{2α} + θ'²)E₀.
 Correction: Simon's middle term Cδ^{1/(n+1)}E₀ omits the factor θ'^{−n−2}; this is harmless because θ' is fixed before δ. Now 3.1 at (τ, θ'R₀) (B_{θ'R₀}(τ) ⊆ W, μ(B_{θ'R₀}(τ)) ≤ 2ω_n(θ'R₀)ⁿ by 2.1, κ²(θ'R₀)² ≤ κ²σ² ≤ δE₀) gives
 (20') E(τ, θ'R₀/2, S) ≤ C(θ'^{−n−2}(ε' + δ^{2α}) + θ'² + δ)E₀,
 and since B_{θ'R₀/4}(ξ) ⊆ B_{θ'R₀/2}(τ) (21'),
 (22') E(ξ, θ'R₀/4, S) ≤ 2ⁿE(τ, θ'R₀/2, S) ≤ C₁₆(θ'^{−n−2}(ε' + δ^{2α}) + θ'² + δ)E₀.
Step 10 (choice of constants; Simon (23)). Put θ₀ := θ'R₀/(4σ) = θ'/32. Choose θ' ∈ (0, ¼] with C₁₆θ'² ≤ θ'/128, then ε' > 0 with C₁₆θ'^{−n−2}ε' ≤ θ'/128, then δ₂ ∈ (0, δ₁] so small that for δ ≤ δ₂: δ^α ≤ β (Step 2), C₁₁δ^α ≤ 1/16 and C₇δ^α ≤ 1/16 (Step 3), C₁₄δ^α ≤ δ_h(n, ε') (Step 7), C₁₅δ^α ≤ θ'/4 (Step 9), C₁₆θ'^{−n−2}δ^{2α} ≤ θ'/128 and C₁₆δ ≤ θ'/128. Then E(ξ, θ₀σ, S) ≤ (θ'/32)E₀ = θ₀E₀ and δ^{−1}κ²(θ₀σ)² = θ₀²δ^{−1}κ²σ² ≤ θ₀E₀, so E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T).

Part 8. Iteration and the graph (proof of Simon 5.2).
Assume (SA) with δ ≤ δ₂ and the smallness conditions of 8.4. Put σ₀ := r₁ = δρ.
8.1 Base plane. Part 4 at (0, 2σ₀) gives T₀ with E(0, σ₀, T₀) ≤ C₃δ^{2α} and dist(x, T₀) ≤ 2C₃δ^ασ₀ for x ∈ spt μ ∩ B_{2σ₀}(0). For ξ ∈ spt μ ∩ B_{σ₀/2}(0), B_{σ₀/2}(ξ) ⊆ B_{σ₀}(0), so E_*(ξ, σ₀/2, T₀) ≤ max{2ⁿC₃δ^{2α}, δ³} ≤ E₀ := 2ⁿC₃δ^{2α} (C₃ ≥ 1).
8.2 Iteration. Fix ξ ∈ spt μ ∩ B_{σ₀/2}(0) and put σ_j := θ₀^jσ₀/2 ∈ (0, r₁]. Applying 7A inductively at (ξ, σ_j, S_j) gives n-planes S₀ := T₀, S₁, S₂, … with E_*(ξ, σ_{j+1}, S_{j+1}) ≤ θ₀E_*(ξ, σ_j, S_j), so E_*(ξ, σ_j, S_j) ≤ θ₀^jE₀, and by 7B |p_{S_{j+1}} − p_{S_j}| ≤ (C₁₀θ₀^{−n}θ₀^jE₀)^{1/2}. Summing the geometric series, p_{S_j} converges to an orthogonal projection of rank n (the set of such projections is closed); its range is called S(ξ). Then |p_{S(ξ)} − p_{S_j}| ≤ Cθ₀^{j/2}E₀^{1/2} and |p_{S(ξ)} − p_{T₀}| ≤ CE₀^{1/2}. Correction: Simon's (2) writes η^jσ₀ for η^jσ₀/2.
8.3 Decay at all scales (Simon (7)–(8)). For 0 < s ≤ σ₀/2 choose j with σ_{j+1} < s ≤ σ_j. Then E(ξ, s, S(ξ)) ≤ 2(σ_j/s)ⁿE(ξ, σ_j, S_j) + 2s^{−n}μ(B_s(ξ))|p_{S_j} − p_{S(ξ)}|² ≤ Cθ₀^jE₀ ≤ C(s/σ₀)E₀ (as θ₀^j = 2σ_j/σ₀ < 2s/(θ₀σ₀)). Thus for ξ ∈ spt μ ∩ B_{σ₀/2}(0) and 0 < s ≤ σ₀/2:
 (7'') E(ξ, s, S(ξ)) ≤ C₁₇(s/σ₀)E₀, and (8'') E(ξ, s, T₀) ≤ 2E(ξ, s, S(ξ)) + 4ω_n|p_{S(ξ)} − p_{T₀}|² ≤ C₁₈E₀.
8.4 The graph (Simon (9)). Apply 5B at (0, σ₀, T₀, L := L₀, C₆ := 2C₃): (i) and (ii) hold by 8.1; the extra hypothesis holds by (8'') provided C₁₈2ⁿC₃δ^{2α} ≤ β'²L₀²; and 5A needs δ^α ≤ βL₀. Also require C₇δ^α ≤ 1/32. These are the smallness conditions of this part (they depend on L₀). We obtain a Lipschitz f : T₀ → T₀^⊥ with Lip f ≤ L₀, sup|f| ≤ C₇δ^ασ₀ ≤ σ₀/32 and
 (9'') spt μ ∩ B_{σ₀/8}(0) = F ∩ B_{σ₀/8}(0), F := graph_0 f = {v + f(v) : v ∈ T₀}.
 Since 0 ∈ spt μ, 0 = Φ_f(v) for some v, so v = 0 and f(0) = 0.
8.5 Tangent planes (Simon (10)). Let A := {v ∈ T₀ : |v| < σ₀/16}. For v ∈ A, |Φ_f(v)| < σ₀/16 + σ₀/32, so Φ_f(v) ∈ spt μ ∩ B_{σ₀/8}(0) by (9''). By (9''), 1.4 and θ ≥ 1, Hⁿ⌞(F ∩ B_{σ₀/8}(0)) ≤ μ; hence, using J_f ≥ 1, every μ-null set has Lⁿ-null Φ_f-preimage in A. So by 1.6, 1.4 and Lebesgue's differentiation theorem for the Radon measure μ (Mathlib ae_tendsto_average_norm_sub), for Lⁿ-a.e. v ∈ A the point ξ_v := Φ_f(v) satisfies: f is differentiable at v, ξ_v ∈ M, T_{ξ_v}M = graph Df(v), and ξ_v is a μ-Lebesgue point of x ↦ p_x. At such v, (7'') gives p_{S(ξ_v)} = p_{graph Df(v)}: indeed |p_{ξ_v} − p_{S(ξ_v)}|²·s^{−n}μ(B_s(ξ_v)) ≤ 2s^{−n}∫_{B_s(ξ_v)} |p_x − p_{ξ_v}|² dμ + 2E(ξ_v, s, S(ξ_v)) → 0 as s ↓ 0, while s^{−n}μ(B_s(ξ_v)) ≥ ω_n/2.
8.6 Projections of graphs. For linear A₁, A₂ : T₀ → T₀^⊥ with ‖A₁‖, ‖A₂‖ ≤ c₀: the T₀^⊥←T₀ block of p_{graph A} is A(I + AᵀA)^{−1}, so the corresponding block of p_{graph A₁} − p_{graph A₂} equals (A₁ − A₂)(I + A₁ᵀA₁)^{−1} + A₂(I + A₁ᵀA₁)^{−1}(A₂ᵀA₂ − A₁ᵀA₁)(I + A₂ᵀA₂)^{−1}, whose Hilbert–Schmidt norm is at least (1 + c₀²)^{−1}|A₁ − A₂| − 2c₀²√(n+k)|A₁ − A₂| ≥ ½|A₁ − A₂| when c₀ = c₀(n, k) is small (this fixes c₀ in 0.1). Hence |A₁ − A₂| ≤ 2|p_{graph A₁} − p_{graph A₂}|.
8.7 Campanato estimate (Simon (11)). Let v ∈ A be as in 8.5 and 0 < s ≤ σ₀/64. For v' ∈ Bⁿ_s(v): |Φ_f(v') − ξ_v| ≤ √2|v' − v| < 2s, and B_{2s}(ξ_v) ⊆ B_{σ₀/8}(0) since |ξ_v| < 3σ₀/32. For a.e. such v', p_{Φ_f(v')} = p_{graph Df(v')} (8.5). By 8.6 (Lip f ≤ L₀ ≤ c₀), the area formula (J_f ≥ 1), Hⁿ⌞(F ∩ B_{σ₀/8}(0)) ≤ μ and (7'') with 2s ≤ σ₀/2:
 ∫_{Bⁿ_s(v)} |Df(v') − Df(v)|² dv' ≤ 4∫_{F∩B_{2s}(ξ_v)} |p_x − p_{S(ξ_v)}|² dHⁿ ≤ 4∫_{B_{2s}(ξ_v)} |p_x − p_{S(ξ_v)}|² dμ ≤ 4(2s)ⁿC₁₇(2s/σ₀)E₀.
 For a.e. v₁, v₂ ∈ A with s := |v₁ − v₂| ≤ σ₀/64, averaging |Df(v₁) − Df(v₂)|² ≤ 2|Df(v') − Df(v₁)|² + 2|Df(v') − Df(v₂)|² over v' ∈ Bⁿ_{s/2}((v₁ + v₂)/2) ⊆ Bⁿ_s(v₁) ∩ Bⁿ_s(v₂) gives |Df(v₁) − Df(v₂)| ≤ C₁₉(|v₁ − v₂|/σ₀)^{1/2}E₀^{1/2}.
8.8 C¹ regularity. Hence Df coincides Lⁿ-a.e. on A with a uniformly continuous map g (the continuous extension of Df restricted to the full-measure set of good points). As f is Lipschitz, its distributional derivative is Df; so the mollifications f_t := f ∗ ϱ_t satisfy Df_t = g ∗ ϱ_t → g locally uniformly on A and f_t → f uniformly. Therefore f is C¹ on A with Df = g, and ‖Df‖ ≤ Lip f ≤ L₀ ≤ ε on A.
8.9 Conclusion of (★). With δ = δ_A and γρ := σ₀/16 = δρ/16: by (9''), spt μ ∩ B̆_{γρ}(0) = F ∩ B̆_{γρ}(0); every x = Φ_f(v) ∈ F ∩ B̆_{γρ}(0) has |v| = |P x| < γρ, i.e. v ∈ A. Hence spt μ ∩ B̆_{γρ}(0) = Φ_f(A) ∩ B̆_{γρ}(0), with f(0) = 0, f C¹ on A and ‖Df‖ ≤ ε on A.

Part 9. The Lean statement.
Let δ_A ∈ (0, 1/8] be the minimum of δ₂ and the smallness conditions of 8.4; it depends only on n, k and ε (through L₀). Put δ₀ := δ_A and γ := δ_A/16 ∈ (0, 1]. Let U, W, R, H, κ, ρ, z satisfy the hypotheses. Then (SA) holds at the centre z with δ := δ₀: z ∈ spt μ, B_ρ(z) ⊆ W, μ(B_ρ(z)) ≤ (1 + δ₀)ω_nρⁿ, κρ ≤ δ₀ (and κ ≥ 0 since ‖H x‖ ≤ κ). Parts 2–8, centred at z, give T₀ and f. Let (a₁, …, aₙ) and (b₁, …, b_k) be orthonormal bases of T₀ and T₀^⊥, ι(v) := Σᵢ vᵢaᵢ, ι'(w) := Σ_j w_jb_j (linear isometries with ⟨ιv, ι'w⟩ = 0), and u(v) := (⟨f(ιv), b_j⟩)_{j=1..k}, so ι'(u(v)) = f(ιv). Then z + ιv + ι'(u v) = z + Φ_f(ιv), u(0) = 0, u is C¹ on ball 0 (γρ) with ‖fderiv ℝ u v‖ = ‖Df(ιv)‖ ≤ ε there, and by 8.9, R.measure.support ∩ ball z (γρ) = ((fun v => z + ι v + ι' (u v)) '' ball 0 (γρ)) ∩ ball z (γρ).

## Key steps

1. Monotonicity inequalities (M1)/(M2) from the first variation with |H| ≤ κ (Simon Ch. 4, 3.17); hence Θ(μ, ·) exists, is upper semicontinuous and ≥ 1 on spt μ, Hⁿ(spt μ ∖ M) = 0 and θ ≤ Θ(μ, ·).
2. Density bounds ½ ≤ μ(B_t(y))/(ω_n tⁿ) ≤ 1 + Cδ and the radial tilt bound ∫|x−y|^{−n−2}|p_x^⊥(x−y)|² dμ ≤ Cδ at support points near z (Simon 2.4, enlarged range); θ = 1 a.e. near z.
3. Tilt bounded by height (Simon 2.1) and affine approximation (Simon 2.5) by a packing, Chebyshev and choice of a good tangent plane.
4. Lipschitz approximation and graph criterion (Simon 2.6–2.7) via the 5-times covering lemma, Lipschitz extension, and the monotonicity bound at points off the support (corrected radii).
5. Harmonic approximation (Simon 3.1–3.4) and tilt-excess decay E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T) with E_* = max{E, δ^{−1}κ²r²} (Simon 4.5–4.6, p = 2n).
6. Iteration of the decay at every point of spt μ near z gives E(ξ, s, S(ξ)) ≤ C(s/σ₀)E₀; the graph criterion makes spt μ ∩ B_{σ₀/8} the graph of f with Lip f ≤ L₀ ≤ ε.
7. Campanato estimate for Df gives f ∈ C^{1,1/2}; choosing orthonormal bases of T₀, T₀^⊥ yields ι, ι', u with u(0) = 0 and the graph identity on B_{γρ}(z), γ = δ₀/16.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `grep -n '^(theorem|lemma|def|structure)' simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,Forms}.lean Chapter03/Rectifiable.lean Chapter05/Basic.lean`
- `grep -n '^(theorem|def)' simongmt Chapter08/{DistributionalConstancy,ConstancyTangentGraph,ConstancyCorrected,ConstancyProjection}.lean`
- `grep -n '^theorem' simongmt Chapter02/{AreaFormula,AreaLipschitz,Area}.lean Chapter04/{MeanCurvature,LpMeanCurvature,MultiplicityBridge}.lean Chapter01/{DensityComparison,Densities,HausdorffDensityBounds}.lean`
- `grep measure_compl_support / mem_support_iff in mathlib MeasureTheory/Measure/Support.lean; exists_disjoint_subfamily_covering_enlargement_closedBall in MeasureTheory/Covering/Vitali.lean; LipschitzWith.ae_differentiableAt in Analysis/Calculus/Rademacher.lean; LipschitzOnWith.extend_real in Topology/MetricSpace/Lipschitz.lean; hausdorffMeasure_image_le in MeasureTheory/Measure/Hausdorff.lean; ae_tendsto_average_norm_sub in MeasureTheory/Covering/Differentiation.lean`
- `grep -rl 'dor_allard_bounded_curvature_graph|dor_graph_supported_cycle_regular' dag.json GMT simongmt (no match); lean_name listing of dag.json and of every nodes/*/decomposition-v*.json`
- `python3 lean_contract.validate_lean_statement on both strings; gmt-compare.child_modules (contract mode) then lean NodeA.lean NodeB.lean`
- `lean -o build/DorerContract.olean DorerContract.lean (byte copy of Contract.lean); lean AssemblyExact.lean (#print axioms dorer_assembly_exact)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DistributionalConstancy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LpMeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/simon-gmt.pdf`
- `/tmp/ch07-dorer-decomp/NodeA.lean`
- `/tmp/ch07-dorer-decomp/NodeB.lean`
- `/tmp/ch07-dorer-decomp/AssemblyExact.lean`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean.
Reusable facts found:
- Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero and WeakDerivativesZero.ae_eq_const give distributional constancy on a connected open set (child B, step 14).
- Chapter02.weighted_area_formula_lipschitz_injOn and injective_area_formula_lipschitz give the injective Lipschitz area formula (both children).
- Chapter03.HasApproximateTangentSpaceAt (unweighted blow-up definition) and HasApproximateTangentSpaceAt.unique.
- Chapter01.simon_theorem_3_3 and simon_theorem_3_6 / simon_remark_3_7_*: comparison and upper density theorems.
- Chapter04.HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn: bounded-H monotonicity for the library RectifiableVarifold.
- Chapter06.affinePullbackForm and exteriorDerivative_affinePullbackForm (child B, step 13), GeometricCurrentOn.zeroRegion and support.
- Mathlib: Measure.measure_compl_support, Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall, LipschitzWith.ae_differentiableAt, LipschitzOnWith.extend_real, LipschitzOnWith.hausdorffMeasure_image_le, ae_tendsto_average_norm_sub.
Not available, hence the split:
- Allard regularity: Chapter05/Basic.lean defines only the vocabulary and states that Lipschitz approximation, excess decay and Allard are not formalized.
- The current Constancy Theorem and C¹ push-forward of currents: only the proper affine push-forward exists.
Lean checks:
- Both child strings pass validate_lean_statement and elaborate in comparator-generated contract-scope modules.
- The conditional assembly of the exact parent type from the exact C1, C3 and child types uses only propext, Classical.choice and Quot.sound.
- No name collisions.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
