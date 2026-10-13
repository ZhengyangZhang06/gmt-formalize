<!-- theorem-id: gmt-ch07/root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1 -->

## Theorem `Submission.ptd_piece_image_approxTangent_ae`

Let F : ℝ^n → ℝ^P be L-Lipschitz, B ⊆ ℝ^n Borel and m > 0 with m|a − a'| ≤ |F(a) − F(a')| for a, a' ∈ B. Suppose F is differentiable with injective derivative at every point of B. Then for Lebesgue-a.e. b ∈ B, F(B) has approximate tangent space range DF(b) at F(b): HasApproximateTangentSpaceAt n (F '' B) (F b) (range DF(b)).

Node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4147

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4990, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4997, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5003, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5010, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5019, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5030

## Lean problem

Declaration: `Submission.ptd_piece_image_approxTangent_ae`

```lean
∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n (F '' B) (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P))
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

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1.piece_image_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 3 (growth bound), 4, 5 and 7 of the parent proof. Here the conclusion is stated for F(B) itself; the comparison with Y in steps 1–3 and 6 is a separate child. Definition used: HasApproximateTangentSpaceAt n S y Q means finrank Q = n and ∫_{η_{y,r}(S)} f dH^n → ∫_Q f dH^n as r → 0⁺ (filter 𝓝[>] 0) for every f ∈ C_c(E). Notation:
- E := ℝ^P; H^n := μHE[n] on E or on ℝ^n; λ := volume on ℝ^n (= μHE[n] there, EuclideanSpace.euclideanHausdorffMeasure_eq_volume);
- A := F(B); B̄_r(z) and B_r(z) are the closed and open balls; η_{y,r}(z) := r^{-1}(z − y) (SimonGMT blowUpMap y r);
- J(a) := normDet(DF(a)) (= SimonGMT areaJacobianAt F a); L_b := DF(b); ‖f‖_∞ := sup|f|;
- ω_n := λ(B̄_1(0)) ∈ (0, ∞), so λ(B̄_t(z)) = ω_n t^n for t ≥ 0 (Measure.addHaar_closedBall', finrank ℝ ℝ^n = n).
0. Preliminaries.
(a) F is injective on B: if F(a) = F(a') with a, a' ∈ B then m|a − a'| ≤ 0, and m > 0. F is also continuous. So A is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn; ℝ^n is Polish).
(b) Lipschitz images: H^n(F(S)) ≤ L^n H^n(S) = L^n λ(S) for every S ⊆ ℝ^n (SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn).
(c) Growth: let b ∈ B and s > 0. If a ∈ B and F(a) ∈ B̄_s(F(b)), then m|a − b| ≤ |F(a) − F(b)| ≤ s. So A ∩ B̄_s(F(b)) ⊆ F(B̄_{s/m}(b)), and by (b), H^n(A ∩ B̄_s(F(b))) ≤ L^n ω_n m^{-n} s^n.
(d) Scaling: let r > 0. η_{y,r} is the homothety with centre y and ratio r^{-1} followed by the translation z ↦ z − y. So H^n(η_{y,r}(S)) = r^{-n} H^n(S) for every S ⊆ E (MeasureTheory.euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image).
- η_{y,r} is a homeomorphism (inverse w ↦ y + rw), hence a measurable embedding that maps Borel sets to Borel sets, and |η_{y,r}(z)| < R ⇔ |z − y| < rR.
- For Borel S, the image of H^n⌞S under η_{y,r} is r^n·H^n⌞η_{y,r}(S): for Borel T, H^n(S ∩ η_{y,r}^{-1}(T)) = r^n H^n(η_{y,r}(S) ∩ T).
- In Lean form: Measure.map η_{y,r} (μHE[n].restrict S) = ENNReal.ofReal (r^n) • μHE[n].restrict (η_{y,r} '' S). Hence ∫_{η_{y,r}(S)} g dH^n = r^{-n} ∫_S g(η_{y,r}(z)) dH^n(z) for every Borel g : E → ℝ (MeasurableEmbedding.integral_map, integral_smul_measure). No integrability is needed: if one side is not integrable, neither is the other, and both integrals are 0.
(e) Jacobian: J is Borel (SimonGMT measurable_areaJacobianAt) and 0 ≤ J(a) ≤ L^n for every a.
- ‖DF(a)‖ ≤ L by norm_fderiv_le_of_lipschitz; DF(a) = 0 where F is not differentiable.
- For every linear T : ℝ^n → E, normDet(T)·ω_n = H^n(T(B̄_1(0))) ≤ ‖T‖^n ω_n. The equality is LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume. The inequality is euclideanHausdorffMeasure_image_le_of_lipschitzOn for the ‖T‖-Lipschitz map T (T.lipschitz), together with μHE[n] = λ on ℝ^n.
- Since ω_n ∈ (0, ∞), normDet(T) ≤ ‖T‖^n.
(f) Area formula: ∫⁻_A g dH^n = ∫⁻_B J(a) g(F(a)) dλ(a) for every g : E → [0, ∞]. This is SimonGMT weighted_area_formula_lipschitz_injOn with s = B, using (a) and finrank ℝ ℝ^n = n.
1. Good parameters. Two theorems apply to λ:
- the Lebesgue density theorem (Besicovitch.ae_tendsto_measure_inter_div for λ and B);
- the Lebesgue differentiation theorem, applied to J, which is bounded and Borel, hence locally integrable. Use IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub with μ := volume (doubling by the instance isUnifLocDoublingMeasureOfIsAddHaarMeasure), K := 1, ι := ℝ, l := 𝓝[>] 0, w := fun _ ↦ b and δ := id; the side condition b ∈ B̄_ρ(b) is trivial, and the radii tend to 0⁺ by self_mem_nhdsWithin.
So λ-a.e. b ∈ B satisfies:
(α) λ(B ∩ B̄_ρ(b))/λ(B̄_ρ(b)) → 1 as ρ → 0⁺. Since λ(B̄_ρ(b)) = ω_n ρ^n ∈ (0, ∞), equivalently ρ^{-n} λ(B̄_ρ(b) ∖ B) → 0.
(β) ⨍_{B̄_ρ(b)} |J(a) − J(b)| dλ(a) → 0 as ρ → 0⁺, equivalently ρ^{-n} ∫_{B̄_ρ(b)} |J(a) − J(b)| dλ(a) → 0.
The set of b ∈ B satisfying (α) and (β) is (volume.restrict B)-conull and does not depend on any test function. Fix such b. F is differentiable at b by hypothesis. Put y := F(b) and L_b := DF(b).
2. Lower bound (γ): m|c| ≤ |L_b c| for every c ∈ ℝ^n.
- This is trivial for c = 0. Let c ≠ 0, so n ≥ 1 and ℝ^n is nontrivial, and let δ ∈ (0, |c|).
- For r > 0 the open ball W_r := B_{rδ}(b + rc) satisfies W_r ⊆ B̄_{r(|c|+δ)}(b) and λ(W_r) = ω_n (rδ)^n (open and closed balls have equal measure, Measure.addHaar_closedBall_eq_addHaar_ball).
- If W_r ∩ B = ∅, then with ρ := r(|c| + δ), λ(B̄_ρ(b) ∖ B)/λ(B̄_ρ(b)) ≥ (δ/(|c| + δ))^n > 0. By (α) this ratio tends to 0, so there is r_δ > 0 with W_r ∩ B ≠ ∅ for all r ∈ (0, r_δ).
- Let θ > 0. Differentiability at b gives ρ_θ > 0 with |F(b + h) − F(b) − L_b h| ≤ θ|h| whenever |h| < ρ_θ.
- Choose r ∈ (0, r_δ) with r(|c| + δ) < ρ_θ, and c' with |c' − c| < δ and b + rc' ∈ B. Since b and b + rc' lie in B, m r|c'| ≤ |F(b + rc') − F(b)| ≤ r|L_b c'| + θ r|c'|. So m|c'| ≤ |L_b c'| + θ|c'|.
- Using |c| − δ ≤ |c'| ≤ |c| + δ and |L_b c'| ≤ |L_b c| + ‖L_b‖δ gives m(|c| − δ) ≤ |L_b c| + ‖L_b‖δ + θ(|c| + δ).
- This holds for every θ > 0 and δ ∈ (0, |c|). Letting θ → 0 and then δ → 0 gives m|c| ≤ |L_b c|.
Consequently L_b is injective and finrank(range L_b) = n (LinearMap.finrank_range_of_inj).
3. Setup. Fix f ∈ C_c(E). Choose R > 0 with f(w) = 0 whenever |w| ≥ R (tsupport f is compact, hence bounded). Let M := ‖f‖_∞ < ∞ and D := B̄_{R/m}(0) ⊆ ℝ^n. For r > 0 and c ∈ ℝ^n let Φ_r(c) := (F(b + rc) − F(b))/r.
4. Rescaled area formula. For every r > 0, f is H^n-integrable on η_{y,r}(A) and
∫_{η_{y,r}(A)} f dH^n = ∫_{ℝ^n} 1_B(b + rc) J(b + rc) f(Φ_r(c)) dλ(c).
(i) η_{y,r}(A) is Borel. Also η_{y,r}(A) ∩ B_R(0) = η_{y,r}(A ∩ B_{rR}(y)), which has H^n-measure r^{-n} H^n(A ∩ B_{rR}(y)) ≤ L^n ω_n (R/m)^n < ∞ by 0(c) and 0(d). Since f is Borel, |f| ≤ M and f = 0 off B_R(0), f is integrable on η_{y,r}(A).
(ii) By 0(d), ∫_{η_{y,r}(A)} f dH^n = r^{-n} ∫_A g dH^n with g := f∘η_{y,r}. g is Borel, |g| ≤ M and g = 0 off B_{rR}(y).
(iii) Apply 0(f) to the weights g⁺ := max(g, 0), g⁻ := max(−g, 0) and |g|.
- ∫⁻_A g^± dH^n = ∫⁻_B J(a) g^±(F(a)) dλ(a), and ∫⁻_B J(a)|g(F(a))| dλ(a) = ∫⁻_A |g| dH^n ≤ M H^n(A ∩ B_{rR}(y)) < ∞.
- So a ↦ 1_B(a) J(a) g(F(a)) is Borel and λ-integrable. As J ≥ 0, its positive and negative parts are a ↦ 1_B(a) J(a) g^±(F(a)).
- Write both Bochner integrals as differences of the lintegrals of their positive and negative parts (integral_eq_lintegral_pos_part_sub_lintegral_neg_part). This gives ∫_A g dH^n = ∫_B J(a) g(F(a)) dλ(a).
(iv) Substitute a = b + rc. λ is translation invariant and ∫ h(rc) dλ(c) = r^{-n} ∫ h dλ for r > 0 (Measure.integral_comp_smul). Using (F(b + rc) − y)/r = Φ_r(c), this gives ∫_{ℝ^n} 1_B(a) J(a) f((F(a) − y)/r) dλ(a) = r^n ∫_{ℝ^n} 1_B(b + rc) J(b + rc) f(Φ_r(c)) dλ(c). Combining (ii)–(iv) proves the formula.
5. Localisation.
- If b + rc ∈ B and f(Φ_r(c)) ≠ 0, then |Φ_r(c)| < R. So m r|c| ≤ |F(b + rc) − F(b)| < rR, and |c| < R/m.
- If f(L_b c) ≠ 0 then |L_b c| < R, and by (γ), |c| < R/m.
Hence the integrand of step 4 and c ↦ J(b) f(L_b c) both vanish outside D, and I_∞ := ∫_{ℝ^n} J(b) f(L_b c) dλ(c) = ∫_D J(b) f(L_b c) dλ(c).
6. Convergence: ∫_{η_{y,r}(A)} f dH^n → I_∞ as r → 0⁺.
- Let c ∈ D. Add and subtract J(b + rc) f(Φ_r(c)) and J(b) f(Φ_r(c)), and use 0 ≤ J ≤ L^n and |f| ≤ M:
|1_B(b + rc) J(b + rc) f(Φ_r(c)) − J(b) f(L_b c)| ≤ L^n M 1_{ℝ^n∖B}(b + rc) + M|J(b + rc) − J(b)| + J(b)|f(Φ_r(c)) − f(L_b c)|.
- All three terms are bounded Borel functions of c, D has finite measure ω_n (R/m)^n, and both integrands vanish off D by step 5. So |∫_{η_{y,r}(A)} f dH^n − I_∞| is at most the integral over D of the right-hand side.
(i) ∫_D 1_{ℝ^n∖B}(b + rc) dλ(c) = r^{-n} λ(B̄_{rR/m}(b) ∖ B) = (R/m)^n · s^{-n} λ(B̄_s(b) ∖ B) with s := rR/m → 0⁺. This tends to 0 by (α).
(ii) ∫_D |J(b + rc) − J(b)| dλ(c) = r^{-n} ∫_{B̄_{rR/m}(b)} |J(a) − J(b)| dλ(a) = (R/m)^n · s^{-n} ∫_{B̄_s(b)} |J − J(b)| dλ. This tends to 0 by (β).
(iii) Given θ > 0, let ρ_θ be as in step 2. For 0 < r < ρ_θ m/R and c ∈ D we have |rc| < ρ_θ, so |Φ_r(c) − L_b c| = r^{-1}|F(b + rc) − F(b) − L_b(rc)| ≤ θ|c| ≤ θR/m. Thus Φ_r → L_b uniformly on D. Since f is uniformly continuous (CompactlySupportedContinuousMapClass.uniformContinuous), sup_{c ∈ D} |f(Φ_r(c)) − f(L_b c)| → 0. Hence ∫_D J(b)|f(Φ_r(c)) − f(L_b c)| dλ(c) ≤ J(b) λ(D) sup_D |…| → 0.
Hence ∫_{η_{y,r}(A)} f dH^n → I_∞.
7. Identification: I_∞ = ∫_{range L_b} f dH^n.
- By LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume (finrank ℝ ℝ^n = n), H^n(L_b(S)) = normDet(L_b) λ(S) = J(b) λ(S) for every S ⊆ ℝ^n.
- For Borel T ⊆ E, L_b(L_b^{-1}(T)) = range L_b ∩ T, so H^n(range L_b ∩ T) = J(b) λ(L_b^{-1}(T)). That is, H^n⌞range L_b is the image measure of J(b)·λ under L_b (range L_b is closed, hence Borel).
- L_b is an injective linear map between finite-dimensional spaces, hence a closed embedding (LinearMap.isClosedEmbedding_of_injective) and a measurable embedding. So MeasurableEmbedding.integral_map and integral_smul_measure give ∫_{range L_b} f dH^n = J(b) ∫_{ℝ^n} f(L_b c) dλ(c) = I_∞.
8. Conclusion. By steps 4, 6 and 7, ∫_{η_{F(b),r}(F(B))} f dH^n → ∫_{range DF(b)} f dH^n as r → 0⁺ for every f ∈ C_c(E), and finrank(range DF(b)) = n by step 2. So HasApproximateTangentSpaceAt n (F '' B) (F b) (range DF(b)) holds at every b ∈ B satisfying (α) and (β), that is, for (volume.restrict B)-a.e. b.
9. Dimension zero. For n = 0 the argument runs as written:
- ℝ^0 = {0} = D, B ⊆ {0}, ω_0 ∈ (0, ∞) and r^{±0} = 1;
- J ≡ 1 (LinearMap.normDet_of_subsingleton);
- (α) and (β) hold at b = 0 when 0 ∈ B, and (γ) concerns only c = 0;
- range L_b = {0} has finrank 0.
(Optional observation, not used: if n > P, no injective DF(a) exists, so B = ∅. Steps 0–8 need no case split, since (γ) already yields injectivity at good points.)
Imports: the Lean proof needs Poincare.SimonGMT.Chapter02.AreaLipschitz and Poincare.SimonGMT.Chapter02.AreaApproximation (area formula, measurable_areaJacobianAt) and Mathlib.Analysis.InnerProductSpace.NormDet. The submission may add these imports; the frozen statement does not use them. The statement mentions no Jacobian because LinearMap.normDet and areaJacobianAt are not in scope after import GMT.Ch07.Submission.

## Key steps

1. Preliminaries: F(B) is Borel; H^n(F(B) ∩ B̄_s(F b)) ≤ L^n ω_n m^{-n} s^n; H^n scales by r^{-n} under η_{y,r}; J = normDet DF is Borel with 0 ≤ J ≤ L^n; injective Lipschitz area formula on B.
2. For λ-a.e. b ∈ B: (α) b is a Lebesgue density point of B and (β) b is a Lebesgue point of J.
3. At such b, density plus differentiability give m|c| ≤ |DF(b)c| for all c.
4. Rescaled area formula: ∫_{η_{F b,r}(F(B))} f dH^n = ∫ 1_B(b+rc) J(b+rc) f(Φ_r(c)) dλ(c), with every integrand supported in B̄_{R/m}(0).
5. A three-term estimate using (α), (β) and the uniform convergence Φ_r → DF(b) on B̄_{R/m}(0) gives the limit J(b)∫ f(DF(b)c) dλ(c).
6. H^n(DF(b)S) = J(b)λ(S) identifies the limit with ∫_{range DF(b)} f dH^n, and finrank(range DF(b)) = n.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n 'HasApproximateTangentSpaceAt|bilipschitz|Antilipschitz|ae_tendsto_measure_inter_div|blowUpMap|tangent_iff|approxTangent' project --glob '*.lean'`
- `rg -n 'ptd_|rsdic_|dpf_' project --glob '*.lean' (no match)`
- `rg -n 'theorem ae_tendsto_measure_inter_div \(|instHasBesicovitchCovering|isUnifLocDoublingMeasureOfIsAddHaarMeasure|theorem ae_tendsto_average_norm_sub|MeasurableSet.image_of_continuousOn_injOn|euclideanHausdorffMeasure_image_eq_normDet_mul_volume|addHaar_closedBall'|integral_comp_smul|norm_fderiv_le_of_lipschitz|euclideanHausdorffMeasure_homothety_image|Isometry.euclideanHausdorffMeasure_image|EuclideanSpace.euclideanHausdorffMeasure_eq_volume|MeasurableEmbedding.integral_map|addHaar_closedBall_eq_addHaar_ball|normDet_of_subsingleton|integral_eq_lintegral_pos_part_sub_lintegral_neg_part|ae_restrict_iff'' mathlib/Mathlib`
- `rg -n 'finrank_range_of_inj|invFunOn_pos|LipschitzWith.ae_differentiableAt|uniformContinuous|isClosedEmbedding_of_injective' mathlib/Mathlib`
- `grep -rn 'euclideanHausdorffMeasure_image_le_of_lipschitzOn|weighted_area_formula_lipschitz_injOn|measurable_areaJacobianAt|def HasApproximateTangentSpaceAt|def blowUpMap|def areaJacobianAt' lake-packages-25730c7c/simongmt/Poincare/SimonGMT`
- `python3 -I dag.json scans: lean_statements containing HasApproximateTangentSpaceAt, LipschitzWith or volume.restrict; exact-string comparison with rsdic_ae_tangent_iff_of_subset and regcomp_approx_tangent_locality; duplicate lean_name scan over all eight chapter DAGs (2,397 nodes, none); 'ptd_' scan over 509 dag.json names and 716 stored proposal names (none)`
- `git show a157a5f4f62ba1c354a3b0cc070d947560abf2e6:GMT/Ch07/Submission.lean; git show 048ff2b9b9037a03e4daa8d5ce0db106c1f592a3:GMT/Ch07/Submission.lean; git log --graph a157a5f4; git merge-base a157a5f4 problems/ch07`
- `git for-each-ref refs/heads | xargs git grep -l 'ptd_' -- GMT (1,178 heads, no match); git grep '^import' -- GMT/Ch07/Submission.lean over all heads`
- `lake env lean /tmp/ptd-a1-review/Avail.lean`
- `lake env lean /tmp/ptd-a1-review/Types.lean`
- `lake env lean /tmp/ptd-a1-review/Assembly.lean (#print axioms ptd_assembly_conditional)`
- `lake env lean /tmp/ptd-a1-review/FinalAssembly.lean, NodeChallenge_K1.lean, NodeChallenge_K2.lean, NodeChallenge_K3.lean`
- `lake env lean /tmp/ptd-a1-review/K2Proof.lean (#print axioms)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the three child types and the parent type`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/ContinuousMap/CompactlySupported.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-piece-tan-680a7024c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/ptd-a1-review/Avail.lean`
- `/tmp/ptd-a1-review/Types.lean`
- `/tmp/ptd-a1-review/Assembly.lean`
- `/tmp/ptd-a1-review/FinalAssembly.lean`
- `/tmp/ptd-a1-review/NodeChallenge_K1.lean`
- `/tmp/ptd-a1-review/NodeChallenge_K2.lean`
- `/tmp/ptd-a1-review/NodeChallenge_K3.lean`
- `/tmp/ptd-a1-review/K2Proof.lean`

The snapshot contains no proof of this statement or of any child. The project's GMT/Ch03/Contract.lean lists Simon 3.1.6 (ApproximateTangentCharacterization) only as an unproved contract Prop, and GMT/Ch07/Contract.lean supplies only the definitions (HasApproximateTangentSpaceAt via SimonGMT, approxTangentPlane).

Every library fact the child proofs cite exists in the pinned Mathlib 25730c7c with compatible hypotheses:
- Besicovitch.ae_tendsto_measure_inter_div and instHasBesicovitchCovering;
- IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub with isUnifLocDoublingMeasureOfIsAddHaarMeasure;
- MeasurableSet.image_of_continuousOn_injOn;
- euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image and EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume and normDet_of_subsingleton;
- addHaar_closedBall', addHaar_closedBall_eq_addHaar_ball and Measure.integral_comp_smul;
- MeasurableEmbedding.integral_map, integral_eq_lintegral_pos_part_sub_lintegral_neg_part and ae_restrict_iff';
- norm_fderiv_le_of_lipschitz, LinearMap.finrank_range_of_inj, Function.invFunOn_pos, CompactlySupportedContinuousMapClass.uniformContinuous and LinearMap.isClosedEmbedding_of_injective.
SimonGMT 2b36630 supplies euclideanHausdorffMeasure_image_le_of_lipschitzOn, weighted_area_formula_lipschitz_injOn (arbitrary weight, no rank hypothesis) and measurable_areaJacobianAt.

LinearMap.normDet and areaJacobianAt are not in scope after import GMT.Ch07.Submission, so no frozen child type mentions them. gmt-compare.py freezes every input except Submission.lean, so the K3 proof may add the needed imports.

In the DAG, tangent_locality's type is character-identical to the accepted rsdic_ae_tangent_iff_of_subset and regcomp_approx_tangent_locality. It is deliberately given a fresh name: both copies sit under depth-1 nodes that depend on this node's ancestor root.minimizing_implies_stationary-a1, and no DAG has ever shared a lean_name.

Lean checks: all three child types and the parent type elaborate in the comparator's replayed contract scope. The conditional assembly uses only propext, Classical.choice and Quot.sound, and piece_pullback is fully proved in scratch with the same axioms. The proposed ptd_ names collide with nothing in dag.json, stored proposals or any branch.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
