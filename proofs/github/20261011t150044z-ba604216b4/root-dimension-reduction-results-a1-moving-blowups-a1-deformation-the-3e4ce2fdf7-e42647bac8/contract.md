<!-- theorem-id: gmt-ch07/root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_smooth_approx-a1 -->

## Theorem `Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx`

Let k ∈ ℕ, L ∈ ℝ≥0 and f : ℝᵏ → ℝ L-Lipschitz (ℝᵏ = Euclid k with Lebesgue measure). Then there are functions f_n : ℝᵏ → ℝ (n ∈ ℕ) such that every f_n is C^∞ (ContDiff ℝ (⊤ : ℕ∞)), every f_n is L-Lipschitz, f_n → f uniformly on ℝᵏ, and Df_n(x) → Df(x) in operator norm for Lebesgue-a.e. x ∈ ℝᵏ, where D = fderiv ℝ (Df(x) = 0 where f is not differentiable).

Node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_smooth_approx-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7020

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/7827, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4980

Decomposition children: None

## Lean problem

Declaration: `Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx`

```lean
∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x))
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

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.jacobian_continuity-a1.lipschitz_smooth_approx-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6(i): 'For Lipschitz functions mollify g and all u_i simultaneously: for each Lipschitz h, h∗ϕ_δ → h uniformly, D(h∗ϕ_δ) = (Dh)∗ϕ_δ → Dh a.e. and |D(h∗ϕ_δ)| ≤ Lip(h)'. The parent cites Mathlib ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable for the a.e. convergence; that lemma lies outside the Submission's import closure, so the same Lebesgue-differentiation step is done below with IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub and tendsto_integral_smul_of_tendsto_average_norm_sub, which are available. Uses the siblings mollify_fderiv and mollify_lipschitz. (The frozen type is identical to that of the not yet accepted node dor_lmb_fcd_jwc_lipschitz_smooth_approx of another branch, so a fresh name is used.)

Notation: λ = Lebesgue measure on ℝᵏ = Euclid k; D = fderiv ℝ; e_i := EuclideanSpace.single i 1 (i ∈ Fin k); d := finrank ℝ (Euclid k); c := λ(closedBall(0, 1)) ∈ (0, ∞) as a real number.

1. (Bumps.) For n ∈ ℕ let φ_n be the smooth bump function at 0 (ContDiffBump (0 : Euclid k)) with inner radius r_n := 1/(n+2) and outer radius R_n := 2/(n+2) = 2r_n. Then φ_n is C^∞, 0 ≤ φ_n ≤ 1, φ_n = 1 on closedBall(0, r_n), support φ_n = ball(0, R_n), and φ_n has compact support.

2. (Normalization.) For every x and every ρ ≥ 0, λ(closedBall(x, ρ)) = ρ^d·c (Measure.addHaar_real_closedBall'), and c > 0. Since φ_n ≥ 0 is integrable and equals 1 on closedBall(0, r_n), I_n := ∫ φ_n ≥ λ(closedBall(0, r_n)) = r_n^d·c > 0. Put ρ_n := φ_n / I_n. Then ρ_n is C^∞ (in particular C¹), continuous, has compact support, ρ_n ≥ 0, ∫ ρ_n = 1, support ρ_n ⊆ ball(0, R_n), and ρ_n ≤ 1/I_n ≤ 1/(r_n^d·c) everywhere (φ_n ≤ 1).

3. (Definition and smoothness.) Put f_n(x) := ∫ ρ_n(t)·f(x − t) dt = (ρ_n ⋆ f)(x) (convolution with the multiplication pairing). ρ_n is C^∞ with compact support and f is continuous, hence locally integrable, so f_n is C^∞ (HasCompactSupport.contDiff_convolution_left).

4. (Lipschitz constant.) ρ_n is continuous, compactly supported, nonnegative with ∫ ρ_n = 1 and f is L-Lipschitz, so by the sibling mollify_lipschitz, f_n = (x ↦ ∫ ρ_n(y)·f(x − y) dy) is L-Lipschitz.

5. (Uniform convergence.) Fix n and x. For y ∈ ball(x, R_n), |f(y) − f(x)| ≤ L·|y − x| ≤ L·R_n. Since ρ_n ≥ 0, ∫ρ_n = 1 and support ρ_n ⊆ ball(0, R_n), dist_convolution_le gives |f_n(x) − f(x)| ≤ L·R_n. As L·R_n → 0 and the bound does not depend on x, f_n → f uniformly on ℝᵏ: for ε > 0, eventually L·R_n < ε, and then dist(f(x), f_n(x)) < ε for all x.

6. (Derivatives of f_n.) By the sibling mollify_fderiv (ρ_n is C¹ with compact support), for all n, x, v: Df_n(x)v = ∫ ρ_n(t)·Df(x − t)v dt.

7. (A.e. convergence in each basis direction.) Fix i and put g_i(s) := Df(s)e_i. g_i is measurable (measurable_fderiv_apply_const) and |g_i(s)| ≤ ‖Df(s)‖·‖e_i‖ ≤ L‖e_i‖ (norm_fderiv_le_of_lipschitz), so g_i is locally integrable (dominated by a constant). Lebesgue measure is uniformly locally doubling, so by the Lebesgue differentiation theorem (IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub) there is a λ-null set outside of which, for every sequence of radii R_n → 0+ and centres in closedBall(x, R_n) (here the centre x itself), the averages ⨍_{closedBall(x, R_n)} |g_i − g_i(x)| dλ tend to 0. Fix such x and apply tendsto_integral_smul_of_tendsto_average_norm_sub with the constant 2^d to the kernels K_n(y) := ρ_n(x − y). Its hypotheses hold: g_i is integrable on every closed ball; ∫ K_n = ∫ ρ_n = 1 (translation and reflection invariance, integral_sub_left_eq_self); support K_n ⊆ closedBall(x, R_n) (if K_n(y) ≠ 0 then x − y ∈ ball(0, R_n)); and 0 ≤ K_n(y) ≤ 1/(r_n^d·c) = 2^d/((2r_n)^d·c) = 2^d/λ(closedBall(x, R_n)). Hence ∫ K_n(y)·g_i(y) dy → g_i(x). By the change of variables t = x − y and step 6, ∫ K_n(y)·g_i(y) dy = ∫ ρ_n(t)·g_i(x − t) dt = Df_n(x)e_i. So Df_n(x)e_i → Df(x)e_i for λ-a.e. x.

8. (All directions and the operator norm.) The k exceptional null sets of step 7 have a null union (ae_all_iff), so for λ-a.e. x, Df_n(x)e_i → Df(x)e_i for every i ∈ Fin k. For a continuous linear T : ℝᵏ → ℝ and w ∈ ℝᵏ, w = Σ_i w(i)e_i and |w(i)| ≤ ‖w‖ (PiLp.norm_apply_le), so |Tw| ≤ Σ_i |w(i)|·|Te_i| ≤ (Σ_i |Te_i|)·‖w‖, i.e. ‖T‖ ≤ Σ_i |Te_i| (ContinuousLinearMap.opNorm_le_bound). With T = Df_n(x) − Df(x) at such a point x, 0 ≤ ‖Df_n(x) − Df(x)‖ ≤ Σ_i |Df_n(x)e_i − Df(x)e_i| → 0, so Df_n(x) → Df(x) (squeeze).

Steps 3, 4, 5 and 8 are the four required properties of the sequence (f_n).

Lean realization (compiled during this decomposition with the pinned toolchain against GMT.Ch07.Submission at b4d606db, Mathlib 25730c7c, in the Submission layout: inside namespace GMT.Ch07 after the contract's open commands, together with the proofs of the sibling declarations it uses; no extra import, no sorry; #print axioms: propext, Classical.choice, Quot.sound):
```lean
/-- **Smooth approximation of a Lipschitz function** (step 4 of the weak continuity of Jacobians):
an `L`-Lipschitz `f : ℝᵏ → ℝ` is the uniform limit of `C^∞`, `L`-Lipschitz functions `f_n` with
`Df_n(x) → Df(x)` in operator norm for a.e. `x`.  Take `f_n = ρ_n ⋆ f`, where `ρ_n = φ_n / ∫ φ_n`
normalizes a bump `φ_n` equal to `1` on `B(0, 1/(n+2))` and supported in `B(0, 2/(n+2))`.  Then
`f_n` is smooth, `L`-Lipschitz (`cmcs_ls_mollify_lipschitz`) and `|f_n - f| ≤ 2L/(n+2)`.  By
`dimred_mbl_dt_lp_jc_mollify_fderiv_eq`, `Df_n(x) eᵢ = (ρ_n ⋆ Df(·) eᵢ)(x)`; as `∫ φ_n ≥ |B(0, 1/(n+2))|`
gives `0 ≤ ρ_n ≤ 2ᵈ / |B(0, 2/(n+2))|`, this tends to `Df(x) eᵢ` at every Lebesgue point of the
bounded function `Df(·) eᵢ`, and `‖T‖ ≤ ∑ᵢ |T eᵢ|` gives convergence in operator norm. -/
theorem Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  intro k L f hf
  -- step 1: bumps `φ n` with `rIn = 1/(n+2)`, `rOut = 2/(n+2)`, normalized to `ρ n = φ n / ∫ φ n`
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : Euclid k) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by have := hpos n; positivity,
      div_lt_div_of_pos_right (by norm_num) (hpos n)⟩
  have hrOut : ∀ n, (φ n).rOut = 2 * (φ n).rIn := fun n => by
    show 2 / ((n : ℝ) + 2) = 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div]
  -- `|B(x, r)| = r ^ d * c` with `c = |B(0, 1)| > 0`
  set d := Module.finrank ℝ (Euclid k)
  set c := (volume : Measure (Euclid k)).real (closedBall 0 1)
  have hcpos : 0 < c := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
    measure_closedBall_lt_top.ne
  have hvol : ∀ (x : Euclid k) (r : ℝ), 0 ≤ r →
      (volume : Measure (Euclid k)).real (closedBall x r) = r ^ d * c :=
    fun x r hr => Measure.addHaar_real_closedBall' _ x hr
  -- `φ n = 1` on `B(0, rIn)` and `φ n ≥ 0`, so `∫ φ n ≥ |B(0, rIn)| = rIn ^ d * c > 0`
  have hφint : ∀ n, Integrable (φ n) (volume : Measure (Euclid k)) := fun n =>
    (φ n).continuous.integrable_of_hasCompactSupport (φ n).hasCompactSupport
  have hIge : ∀ n, (φ n).rIn ^ d * c ≤ ∫ x, φ n x := by
    intro n
    rw [← hvol 0 _ (φ n).rIn_pos.le]
    calc (volume : Measure (Euclid k)).real (closedBall 0 (φ n).rIn)
        = ∫ x in closedBall (0 : Euclid k) (φ n).rIn, φ n x := by
          rw [setIntegral_congr_fun measurableSet_closedBall
            (fun x hx => (φ n).one_of_mem_closedBall hx), setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ ∫ x, φ n x :=
          setIntegral_le_integral (hφint n) (Eventually.of_forall fun x => (φ n).nonneg)
  have hIpos : ∀ n, 0 < ∫ x, φ n x := fun n =>
    (mul_pos (pow_pos (φ n).rIn_pos d) hcpos).trans_le (hIge n)
  set ρ : ℕ → Euclid k → ℝ := fun n x => φ n x / ∫ y, φ n y with hρ
  have hρc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρc1 : ∀ n, ContDiff ℝ 1 (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (φ n).continuous.div_const _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    (φ n).hasCompactSupport.comp_left (g := fun t : ℝ => t / ∫ y, φ n y) (zero_div _)
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n x => div_nonneg (φ n).nonneg (hIpos n).le
  have hρint : ∀ n, ∫ x, ρ n x = 1 := fun n => by
    show ∫ x, φ n x / ∫ y, φ n y = 1
    rw [integral_div, div_self (hIpos n).ne']
  have hρsupp : ∀ n, support (ρ n) ⊆ ball 0 (φ n).rOut := fun n x hx => by
    rw [← (φ n).support_eq, mem_support]
    intro h0
    exact (mem_support.1 hx) (by simp [hρ, h0])
  have hρle : ∀ n x, ρ n x ≤ 1 / ((φ n).rIn ^ d * c) := fun n x =>
    calc ρ n x = φ n x / ∫ y, φ n y := rfl
      _ ≤ 1 / ∫ y, φ n y := div_le_div_of_nonneg_right (φ n).le_one (hIpos n).le
      _ ≤ 1 / ((φ n).rIn ^ d * c) :=
          one_div_le_one_div_of_le (mul_pos (pow_pos (φ n).rIn_pos d) hcpos) (hIge n)
  -- `f_n = ρ n ⋆ f`
  set fs : ℕ → Euclid k → ℝ := fun n x => ∫ t, ρ n t * f (x - t) with hfs
  have hconv : ∀ n, fs n = convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro n; funext x; simp [hfs, convolution_def]
  have hrOut0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [φ] using this
  refine ⟨fs, fun n => ?_, fun n => ?_, ?_, ?_⟩
  · -- step 2: `ρ n ⋆ f` is smooth
    rw [hconv]
    exact (hρs n).contDiff_convolution_left _ (hρc n) hf.continuous.locallyIntegrable
  · -- step 3: `ρ n ⋆ f` is `L`-Lipschitz
    exact Submission.cmcs_ls_mollify_lipschitz k (ρ n) f L (hρcont n) (hρs n) (hρ0 n) (hρint n) hf
  · -- step 4: `|f_n x - f x| ≤ L * rOut` for all `x`, and `rOut → 0`
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(hrOut0.const_mul (L : ℝ)).eventually (gt_mem_nhds (by simpa using hε))]
      with n hn x
    have hdist := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := f x) (g := f)
      (by positivity : (0 : ℝ) ≤ L * (φ n).rOut) (hρsupp n) (hρ0 n) (hρint n)
      hf.continuous.aestronglyMeasurable (fun y hy => by
        calc dist (f y) (f x) ≤ L * dist y x := hf.dist_le_mul y x
          _ ≤ L * (φ n).rOut := by gcongr; exact (mem_ball.1 hy).le)
    rw [← hconv] at hdist
    rw [dist_comm]
    exact lt_of_le_of_lt hdist hn
  · -- step 5: `Df_n(x) v = ∫ ρ n t * Df(x - t) v dt`
    have hB1 : ∀ n x v, fderiv ℝ (fs n) x v = ∫ t, ρ n t * fderiv ℝ f (x - t) v := fun n x v =>
      Submission.dimred_mbl_dt_lp_jc_mollify_fderiv_eq k L f (ρ n) hf (hρc1 n) (hρs n) x v
    have hδ : Tendsto (fun n => (φ n).rOut) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hrOut0, Eventually.of_forall fun n => (φ n).rOut_pos⟩
    -- steps 6-7: for each basis vector `e_i`, `Df_n(x) e_i → Df(x) e_i` for a.e. `x`
    have hDi : ∀ i : Fin k, ∀ᵐ x ∂(volume : Measure (Euclid k)),
        Tendsto (fun n => fderiv ℝ (fs n) x (EuclideanSpace.single i (1 : ℝ))) atTop
          (𝓝 (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) := by
      intro i
      set g : Euclid k → ℝ := fun s => fderiv ℝ f s (EuclideanSpace.single i (1 : ℝ)) with hg
      have hloc : LocallyIntegrable g (volume : Measure (Euclid k)) := by
        refine (locallyIntegrable_const ((L : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)).mono
          ((measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs (_ * _), abs_of_nonneg (by positivity)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      -- Lebesgue differentiation: `⨍_{B(x, r)} |g - g x| → 0` as `r → 0`, for a.e. `x`
      filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1]
        with x hx
      have havg := hx (fun _ => x) (fun n => (φ n).rOut) hδ
        (Eventually.of_forall fun n => mem_closedBall_self (by simpa using (φ n).rOut_pos.le))
      -- `0 ≤ ρ n (x - ·) ≤ 2 ^ d / |B(x, rOut)|`, supported in `B(x, rOut)`, with integral `1`
      have key := tendsto_integral_smul_of_tendsto_average_norm_sub ((2 : ℝ) ^ d) havg
        (g := fun n y => ρ n (x - y))
        (Eventually.of_forall fun n => hloc.integrableOn_isCompact (isCompact_closedBall _ _))
        (tendsto_const_nhds.congr fun n => by
          rw [integral_sub_left_eq_self (ρ n) volume x, hρint n])
        (Eventually.of_forall fun n y hy => by
          have hy' : x - y ∈ ball (0 : Euclid k) (φ n).rOut := hρsupp n hy
          rw [mem_ball, dist_zero_right] at hy'
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact hy'.le)
        (Eventually.of_forall fun n y => by
          rw [abs_of_nonneg (hρ0 n _), hvol x _ (φ n).rOut_pos.le, hrOut n]
          calc ρ n (x - y) ≤ 1 / ((φ n).rIn ^ d * c) := hρle n _
            _ = 2 ^ d / ((2 * (φ n).rIn) ^ d * c) := by
              rw [mul_pow]
              field_simp)
      refine key.congr fun n => ?_
      rw [hB1, ← integral_sub_left_eq_self (fun y => ρ n (x - y) • g y) volume x]
      simp only [sub_sub_cancel, smul_eq_mul, hg]
    filter_upwards [ae_all_iff.2 hDi] with x hx
    -- step 8: `‖T‖ ≤ ∑ᵢ |T eᵢ|`, so convergence on the basis gives convergence in norm
    have hbound : ∀ T : Euclid k →L[ℝ] ℝ, ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound T (Finset.sum_nonneg fun i _ => norm_nonneg _)
        fun w => ?_
      have hw : w = ∑ i, w i • EuclideanSpace.single i (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w]
        simp
      calc ‖T w‖ = ‖∑ i, w i • T (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hw]
            simp [map_sum, map_smul]
        _ ≤ ∑ i, ‖w i • T (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
        _ = ∑ i, ‖w i‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by simp
        _ ≤ ∑ i, ‖w‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
            gcongr with i
            exact PiLp.norm_apply_le w i
        _ = (∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖) * ‖w‖ := by
            rw [Finset.sum_mul]; simp [mul_comm]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hbound _) ?_
    have : Tendsto (fun n => ∑ i : Fin k, ‖(fderiv ℝ (fs n) x - fderiv ℝ f x)
        (EuclideanSpace.single i (1 : ℝ))‖) atTop (𝓝 (∑ i : Fin k, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hx i)
      simpa using this
    simpa using this
```

## Key steps

1. Normalized bumps ρ_n = φ_n/∫φ_n supported in B(0, 2/(n+2)) with 0 ≤ ρ_n ≤ 2^d/λ(B(x, 2/(n+2))) and ∫ρ_n = 1; f_n := ρ_n ⋆ f.
2. f_n is C^∞ (contDiff_convolution_left), L-Lipschitz (sibling mollify_lipschitz) and |f_n − f| ≤ 2L/(n+2) (dist_convolution_le).
3. Df_n(x)e_i = ∫ρ_n(t)Df(x − t)e_i dt (sibling mollify_fderiv) → Df(x)e_i a.e. by Lebesgue differentiation for the doubling Lebesgue measure.
4. ‖T‖ ≤ Σ_i |Te_i| upgrades convergence on the basis to operator-norm convergence a.e.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git -C SNAPSHOT/mathlib rev-parse HEAD (25730c7c); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean workspace GMT/Ch07/Submission.lean (identical); git log -1 of the workspace (b4d606db)`
- `rg -n -i 'piola|mollif|weak.?contin|null.?lagrang|minor' SNAPSHOT/project -g '*.lean' (no relevant match: only LpSeminorm imports and a Hölder-seminorm comment in Ch04/Ch05); rg -n -i jacobian SNAPSHOT/project/GMT/Ch02/Contract.lean SNAPSHOT/project/GMT/Ch03/Contract.lean SNAPSHOT/project/GMT/Ch07/Contract.lean (only the areaJacobian/coareaJacobian definitions of Ch02/Ch03 and the area/coarea formulas; nothing in Ch07)`
- `rg -l 'dimred_mbl_dt_lp_jc|dor_lmb_fcd_jwc|cmcs_ls_mollify|cmr_cc_det' SNAPSHOT/project (no match; these declarations exist only in DAG candidate commits)`
- `rg -n '^(theorem|lemma) [A-Za-z_.]*NAME' SNAPSHOT/mathlib/Mathlib for NAME in integral_lineDeriv_mul_eq, norm_fderiv_le_of_lipschitz, measurable_fderiv_apply_const, contDiff_convolution_left, hasFDerivAt_convolution_left, convolutionExists_left, ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, dist_convolution_le, extDeriv_pullback, extDeriv_apply, det_succ_row_zero, tendsto_integral_filter_of_dominated_convergence, ae_differentiableAt, induction_dense, exists_contDiff_support_eq_eq_one_iff, lipschitzWith_of_hasCompactSupport, exists_isCompact_sdiff_lt, exists_isOpen_sdiff_lt, bdd_mul, addHaar_real_closedBall' (all found); ae_convolution_tendsto_right_of_locallyIntegrable and det_le (found in the snapshot, see next query)`
- `lake env lean /tmp/jc-decomp2/probe/Probe.lean importing only GMT.Ch07.Submission: #check ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le (Unknown constant: outside the frozen import closure); #check IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub, tendsto_integral_smul_of_tendsto_average_norm_sub, LipschitzWith.integral_lineDeriv_mul_eq, MemLp.induction_dense, HasCompactSupport.hasFDerivAt_convolution_left, extDeriv_pullback (available)`
- `python3 scans of RUN/dag.json: nodes whose id/title/statement mention Jacobian weak continuity; status, candidate_commit, updated_at and lean_statement of the eleven child names under the runtime rule _accepted_checkpoint (six reused names accepted with byte-identical types; twin mollify_fderiv accepted at 01:41:31Z, the four other twins comparing/speculative-ready); collision scan for dimred_mbl_dt_lp_jc_* (unused); RUN/issue-workers.json (mode broker-owned-issue-polling; worker for issue 7020 started 2026-10-14T00:19:09Z)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose depth guard and name checks, _existing_lean_name_problem, _accepted_checkpoint, _solve_children reuse by lean_name), store.py (refresh, update: accepted is permanent), parallel.py (enabled, RefreshLock), scripts/swarm-run-issue.py, and workspace .humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json (github_shared_issue_runtime true, max_depth 6, max_children 12, max_nodes 5000, decomposition_attempts 5)`
- `git show <commit>:GMT/Ch07/Submission.lean for accepted candidates fee01ff86c, 2c87728a, 7ba02a03, c6153c4c, 52b9c39c, 13966862 (reused proofs byte-identical to the compiled chain) and ebbe3de7 (accepted twin of mollify_fderiv; proof body identical to the embedded realization)`
- `lake env lean /tmp/jc-decomp2/lean/FinalCheck.lean (eleven child proofs, assembly_from_children, Submission.dimred_mbl_dt_lp_jacobian_weak_continuity with its frozen type, exact-type checks; exit 0, no sorry, axioms propext/Classical.choice/Quot.sound); lake env lean /tmp/jc-decomp2/challenges/AllChallenges.lean (prefix from verifier contract_scope; exit 0, only sorry warnings); both validate_lean_statement implementations on all eleven types; dependency cross-check of Submission.* references against depends_on`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Average.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/AbsoluteValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-b372f37aac/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/swarm-configs/c8e45649089f4d62adf9de1e95c664c3.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/parallel.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/scripts/swarm-run-issue.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/jc-decomp2/lean/FinalCheck.lean`
- `/tmp/jc-decomp2/challenges/AllChallenges.lean`
- `/tmp/jc-decomp2/probe/Probe.lean`

Pins match: project b4d606db and Mathlib 25730c7c, and the workspace Submission is byte-identical to the frozen Ch07 contract. The snapshot project contains no weak-continuity, Piola, mollification or minor-expansion lemma. Its only Jacobians are the Ch02/Ch03 area/coarea Jacobian definitions, so the needed obligations come from the DAG. Six comparator-accepted DAG declarations with exactly the needed types are reused verbatim: cmr_cc_det_covector_exists, dor_lmb_fcd_jwc_covector_det_expansion, dor_lmb_fcd_jwc_weak_star_l1_upgrade, dor_lmb_fcd_jwc_piola_identity, cmcs_ls_mollify_lipschitz and dor_lmb_fcd_jwc_minor_measurable_bound. All six were accepted before this attempt's shared-DAG refresh (01:30:20Z), so the earlier 'reserved by active DAG node' rejection no longer applies. The five remaining links get fresh, unused dimred_mbl_dt_lp_jc_* names, because their twins were unaccepted at that refresh. Every Mathlib lemma cited by the child proofs exists in the snapshot and is available after import GMT.Ch07.Submission. ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable and Matrix.det_le exist in the snapshot but are outside the import closure, so the child proofs use in-closure substitutes. All eleven child proofs plus the parent, stated with its exact frozen type, compile together with no sorry and only the standard axioms. Every type elaborates in the comparator's challenge scope.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
