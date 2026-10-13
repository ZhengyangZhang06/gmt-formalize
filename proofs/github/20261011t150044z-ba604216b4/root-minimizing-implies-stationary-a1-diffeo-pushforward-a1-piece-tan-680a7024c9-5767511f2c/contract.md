<!-- theorem-id: gmt-ch07/root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1 -->

## Theorem `Submission.dpf_approxTangent_ae_bilipschitz_piece`

Let U ⊆ ℝ^P be open and Y ⊆ U Borel with H^n(Y ∩ C) < ∞ for every compact C ⊆ U. Let F : ℝ^n → ℝ^P be L-Lipschitz, B ⊆ ℝ^n Borel and m > 0 with m|a − a'| ≤ |F(a) − F(a')| for a, a' ∈ B, F differentiable with injective derivative at every point of B, and F(B) ⊆ Y. Then for Lebesgue-a.e. b ∈ B, Y has the approximate tangent space range DF(b) at F(b) (HasApproximateTangentSpaceAt n Y (F b) (range DF(b))).

Node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/8

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/988

Prerequisites: None

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/4581, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4589, https://github.com/ZhengyangZhang06/gmt-formalize/issues/4595

## Lean problem

Declaration: `Submission.dpf_approxTangent_ae_bilipschitz_piece`

```lean
∀ (P n : ℕ) (U Y : Set (Euclid P)) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → MeasurableSet Y → Y ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (Y ∩ C) ≠ ∞) → LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → F '' B ⊆ Y → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n Y (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P))
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

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.piece_tangent_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the parent proof (density lemma). It is the bi-Lipschitz analogue of Simon's proof of Theorem 1.6 "⇒" of Ch. 3 (chapter-03.txt lines 109–143), which compares M with a C¹ manifold N_j and controls M ∖ N_j by the upper density theorem; here the C¹ piece is replaced by the bi-Lipschitz image F(B), the blow-up of F(B) is computed by the area formula, and the upper-density bound of the parent's step 5(i) is replaced by the elementary bi-Lipschitz estimate of step 3 below (a valid simplification: it uses only m|a − a'| ≤ |F(a) − F(a')| on B). Definition used: HasApproximateTangentSpaceAt n Y y Q means finrank Q = n and ∫_{η_{y,r}(Y)} f dH^n → ∫_Q f dH^n as r → 0⁺ for every f ∈ C_c(E) (Simon Ch. 3 1.4, chapter-03.txt lines 77–85). Notation: E := ℝ^P; H^n := μHE[n] on E or on ℝ^n; λ := Lebesgue measure on ℝ^n (= μHE[n] there, EuclideanSpace.euclideanHausdorffMeasure_eq_volume); A := F(B); B̄_r(z), B_r(z) closed and open balls; η_{y,r}(z) := r^{-1}(z − y) (= SimonGMT blowUpMap y r); J_F(a) := normDet(DF(a)) (= SimonGMT areaJacobianAt F a); L_b := DF(b); ω_n := λ(B̄_1(0)) ∈ (0, ∞); ‖f‖_∞ := sup|f|.
0. Preliminaries. (a) F is continuous and injective on B (m > 0), so A is Borel (Lusin–Souslin, MeasurableSet.image_of_continuousOn_injOn), and A ⊆ Y ⊆ U. (b) The inverse G : A → B of F|_B satisfies |G(y) − G(y')| ≤ m^{-1}|y − y'|, so H^n(G(N)) ≤ m^{-n}H^n(N) for N ⊆ A (LipschitzOnWith.hausdorffMeasure_image_le; μHE[n] = c_n·μH[n] with a constant c_n ∈ (0, ∞) depending only on n, Measure.euclideanHausdorffMeasure_def). Hence if a property holds at every point of A outside an H^n-null set N, then it holds at F(b) for every b ∈ B ∖ G(N), and λ(G(N)) = 0. (c) Lipschitz images: H^n(F(S)) ≤ L^n H^n(S) = L^n λ(S) for S ⊆ ℝ^n (LipschitzWith.hausdorffMeasure_image_le, same normalization). (d) Scaling: for r > 0, η_{y,r} is the homothety of ratio r^{-1} about y followed by the translation z ↦ z − y, so H^n(η_{y,r}(S)) = r^{-n}H^n(S) for all S ⊆ E (MeasureTheory.euclideanHausdorffMeasure_homothety_image, and invariance of μHE[n] under the isometry z ↦ z − y, Isometry.euclideanHausdorffMeasure_image); η_{y,r} is a homeomorphism, so η_{y,r}(S) is Borel for Borel S. Hence for Borel S the image of H^n⌞S under the measurable embedding η_{y,r} is r^n·H^n⌞η_{y,r}(S), and ∫_{η_{y,r}(S)} f dH^n = r^{-n}∫_S f(η_{y,r}(z)) dH^n(z) whenever either side is an integral of an integrable function (MeasurableEmbedding.integral_map, integral_smul_measure). (e) 0 ≤ J_F(a) ≤ L^n for every a, and J_F is Borel (SimonGMT measurable_areaJacobianAt): ‖DF(a)‖ ≤ L (norm_fderiv_le_of_lipschitz; DF(a) = 0 where F is not differentiable), and normDet(T) ≤ ‖T‖^n for every linear T : ℝ^n → E, because normDet(T)·ω_n = H^n(T(B̄_1(0))) ≤ ‖T‖^n H^n(B̄_1(0)) = ‖T‖^n ω_n (Mathlib LinearMap.euclideanHausdorffMeasure_image and the Lipschitz image bound).
1. Countable compact cover. If U = ∅ then Y = ∅, so F(B) ⊆ ∅ forces B = ∅ and the claim is trivial (volume.restrict ∅ = 0); assume U ≠ ∅. U is open in the separable space E, so there are closed balls C_k = B̄_{s_k}(q_k) ⊆ U (k ∈ ℕ, s_k > 0) whose open balls B_{s_k}(q_k) cover U (centres in a countable dense set, positive rational radii, closures inside U). Each C_k is compact and ⊆ U, so H^n(Y ∩ C_k) < ∞.
2. Density of A in Y. Fix k and let ν_k := H^n⌞(Y ∩ C_k), a finite (hence locally finite) Borel measure (IsFiniteMeasure from H^n(Y ∩ C_k) < ∞, isFiniteMeasure_restrict). By the Besicovitch density theorem (Mathlib Besicovitch.ae_tendsto_measure_inter_div applied to ν_k and A; E is finite-dimensional), for ν_k⌞A-a.e. y: ν_k(A ∩ B̄_r(y))/ν_k(B̄_r(y)) → 1 as r → 0⁺. Since A ⊆ Y and A, Y, C_k are Borel, ν_k⌞A = H^n⌞(A ∩ C_k), so this holds for H^n-a.e. y ∈ A ∩ C_k. Discarding the countable union N₁ of the exceptional sets (H^n(N₁) = 0), every y ∈ A ∖ N₁ is density-good: the convergence holds for every k with y ∈ C_k.
3. Smallness of Y ∖ A. Let y = F(b) (b ∈ B) be density-good and choose k with y ∈ B_{s_k}(q_k); put r₀ := s_k − |y − q_k| > 0. For 0 < r < r₀, B̄_r(y) ⊆ C_k, so with a(r) := H^n(A ∩ B̄_r(y)) and z(r) := H^n((Y ∖ A) ∩ B̄_r(y)) we get ν_k(A ∩ B̄_r(y)) = a(r) and ν_k(B̄_r(y)) = a(r) + z(r) < ∞; by step 2, a(r)/(a(r) + z(r)) → 1, so for each ε ∈ (0, 1/2) there is r_ε ∈ (0, r₀) with z(r) ≤ ε(a(r) + z(r)), hence z(r) ≤ 2ε a(r), for 0 < r < r_ε. If a ∈ B and F(a) ∈ B̄_r(y) then m|a − b| ≤ |F(a) − F(b)| ≤ r, so A ∩ B̄_r(y) ⊆ F(B ∩ B̄_{r/m}(b)) and, by 0(c), a(r) ≤ L^n λ(B̄_{r/m}(b)) = L^n ω_n m^{-n} r^n (this bound holds for every b ∈ B and r > 0). Thus z(r) ≤ 2ε L^n ω_n m^{-n} r^n for r < r_ε, i.e. r^{-n} z(r) → 0 as r → 0⁺.
4. Good parameters. By Lebesgue's density and differentiation theorems for λ on ℝ^n (Besicovitch.ae_tendsto_measure_inter_div for λ and B; IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub for λ, an additive Haar measure, and J_F, which is bounded and Borel, hence locally integrable), λ-a.e. b ∈ B satisfies (α) b is a density point of B: λ(B̄_ρ(b) ∖ B)/λ(B̄_ρ(b)) → 0 as ρ → 0⁺, and (β) b is a Lebesgue point of J_F: ρ^{-n} ∫_{B̄_ρ(b)} |J_F(a) − J_F(b)| dλ(a) → 0 as ρ → 0⁺ (= ω_n times the average). Every b ∈ B with (α) also satisfies (γ) |L_b c| ≥ m|c| for all c ∈ ℝ^n. Proof of (γ): it is trivial for c = 0; let c ≠ 0 (so n ≥ 1). There are r_l → 0⁺ and c_l → c with b + r_l c_l ∈ B: otherwise there are ε ∈ (0, |c|) and r₁ > 0 with B ∩ (b + r B_ε(c)) = ∅ for all r ∈ (0, r₁); but b + r B_ε(c) ⊆ B̄_{r(|c|+ε)}(b) has measure r^n λ(B_ε(0)) = (ε/(|c|+ε))^n λ(B̄_{r(|c|+ε)}(b)) (open and closed balls have the same Lebesgue measure, Measure.addHaar_closedBall_eq_addHaar_ball, which needs ℝ^n nontrivial: true since c ≠ 0; λ scales by r^n under dilation by r), a fixed positive fraction of λ(B̄_ρ(b)) for every ρ = r(|c|+ε) < r₁(|c|+ε), contradicting (α). Then m r_l|c_l| ≤ |F(b + r_l c_l) − F(b)| = |r_l L_b c_l + o(r_l)| (differentiability at b, |c_l| bounded); divide by r_l and let l → ∞ to get m|c| ≤ |L_b c|.
5. Blow-up of A. Let b ∈ B satisfy (α) and (β), y := F(b), f ∈ C_c(E) and R > 0 with f = 0 outside B_R(0). Put Φ_r(c) := (F(b + rc) − F(b))/r for r > 0, c ∈ ℝ^n.
 (a) Formula: η_{y,r}(A) ∩ B_R(0) = η_{y,r}(A ∩ B_{rR}(y)) has H^n-measure ≤ r^{-n} a(rR) ≤ L^n ω_n (R/m)^n < ∞ (0(d) and step 3's bound for a), so f is integrable on η_{y,r}(A). By 0(d), the weighted area formula for the injective Lipschitz map F on B (SimonGMT weighted_area_formula_lipschitz_injOn, finrank ℝ ℝ^n = n, applied to the weights (f∘η_{y,r})⁺ and (f∘η_{y,r})⁻ and subtracted; all terms are finite since f is bounded and only B ∩ B̄_{rR/m}(b) contributes) and the substitution a = b + rc (λ scales by r^n): ∫_{η_{y,r}(A)} f dH^n = r^{-n}∫_B J_F(a) f((F(a) − y)/r) dλ(a) = ∫_{ℝ^n} 1_B(b + rc) J_F(b + rc) f(Φ_r(c)) dλ(c).
 (b) Localisation: if b + rc ∈ B and f(Φ_r(c)) ≠ 0 then m r|c| ≤ |F(b + rc) − F(b)| < rR, so |c| < R/m; and by (γ), f(L_b c) = 0 for |c| ≥ R/m. So, with D := B̄_{R/m}(0) ⊆ ℝ^n, the integral in (a) is an integral over D, and I_∞ := ∫_{ℝ^n} J_F(b) f(L_b c) dλ(c) = ∫_D J_F(b) f(L_b c) dλ(c).
 (c) Convergence: for c ∈ D, |1_B(b + rc) J_F(b + rc) f(Φ_r(c)) − J_F(b) f(L_b c)| ≤ L^n‖f‖_∞ 1_{D ∖ r^{-1}(B − b)}(c) + ‖f‖_∞ |J_F(b + rc) − J_F(b)| + J_F(b)|f(Φ_r(c)) − f(L_b c)| (add and subtract J_F(b + rc) f(Φ_r(c)) and J_F(b) f(Φ_r(c)); 0(e)). Integrating over D: the first term gives L^n‖f‖_∞ r^{-n} λ(B̄_{rR/m}(b) ∖ B) → 0 by (α) (λ(B̄_{rR/m}(b)) = ω_n(R/m)^n r^n); the second gives ‖f‖_∞ r^{-n} ∫_{B̄_{rR/m}(b)} |J_F − J_F(b)| dλ → 0 by (β); the third is ≤ J_F(b) λ(D) sup_{c∈D} |f(Φ_r(c)) − f(L_b c)| → 0 because Φ_r → L_b uniformly on D (F is differentiable at b) and f is uniformly continuous. Hence ∫_{η_{y,r}(A)} f dH^n → I_∞ as r → 0⁺.
 (d) Identification: L_b is injective and linear with normDet(L_b) = J_F(b), and H^n(L_b(S)) = J_F(b) λ(S) for all S ⊆ ℝ^n (Mathlib LinearMap.euclideanHausdorffMeasure_image, LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume). For Borel T ⊆ E, L_b(L_b^{-1}(T)) = range L_b ∩ T, so H^n(range L_b ∩ T) = J_F(b) λ(L_b^{-1}(T)), i.e. H^n⌞range L_b is the image measure of J_F(b)·λ under L_b; as an injective linear map between finite-dimensional spaces is a closed (hence measurable) embedding, MeasurableEmbedding.integral_map gives I_∞ = J_F(b)∫_{ℝ^n} f(L_b c) dλ(c) = ∫_{range L_b} f dH^n.
6. Conclusion. Let N₂ ⊆ B be the λ-null set of b ∈ B where (α) or (β) fails, and N₃ := G(N₁ ∩ A), λ-null by 0(b) and step 2. Let b ∈ B ∖ (N₂ ∪ N₃) (a (volume.restrict B)-conull set); then F(b) is density-good. Let y := F(b), f and R as in step 5, k and r₀ as in step 3. For 0 < r < r₀/R, B̄_{rR}(y) ⊆ C_k, so H^n(η_{y,r}(Y) ∩ B_R(0)) = r^{-n}H^n(Y ∩ B_{rR}(y)) ≤ r^{-n}H^n(Y ∩ C_k) < ∞ and f is integrable on η_{y,r}(Y); η_{y,r}(Y) is the disjoint union of the Borel sets η_{y,r}(A) and η_{y,r}(Y ∖ A), so |∫_{η_{y,r}(Y)} f dH^n − ∫_{η_{y,r}(A)} f dH^n| ≤ ‖f‖_∞ H^n(η_{y,r}(Y ∖ A) ∩ B_R(0)) ≤ ‖f‖_∞ r^{-n} z(rR) = ‖f‖_∞ R^n (rR)^{-n} z(rR) → 0 by step 3. With step 5, ∫_{η_{y,r}(Y)} f dH^n → ∫_{range L_b} f dH^n as r → 0⁺ (filter 𝓝[>] 0), for every f ∈ C_c(E). Since L_b is injective on ℝ^n, finrank(range L_b) = n. This is HasApproximateTangentSpaceAt n Y (F b) (range DF(b)), for (volume.restrict B)-a.e. b.
7. Dimension zero. The argument is valid for n = 0 as written: ℝ^0 = {0}, λ is the unit point mass, B ⊆ {0}, ω_0 = 1 and r^{±0} = 1, J_F ≡ 1 (normDet of a map out of ℝ^0, LinearMap.normDet_of_subsingleton), (γ) is vacuous, D = {0}, integrals over ℝ^0 are evaluations at 0, and range L_b = {0} has finrank 0. (Imports: the Lean proof needs Poincare.SimonGMT.Chapter02.AreaLipschitz and Poincare.SimonGMT.Chapter02.AreaApproximation for the area formula and measurable_areaJacobianAt, and Mathlib.Analysis.InnerProductSpace.NormDet; the submission may add these imports, the frozen statement does not use them.)

## Key steps

1. F|_B is bi-Lipschitz, so H^n-null subsets of F(B) pull back to λ-null subsets of B, and F(B) is Borel.
2. Besicovitch density of F(B) inside H^n⌞(Y ∩ C_k) on a countable cover of U by compact balls.
3. H^n(F(B) ∩ B̄_r(F b)) = O(r^n) by the bi-Lipschitz bound, hence H^n((Y ∖ F(B)) ∩ B̄_r(F b)) = o(r^n).
4. At density points of B that are Lebesgue points of J_F, |DF(b)c| ≥ m|c|, and the area formula plus rescaling give ∫_{η(F(B))} f → J_F(b)∫ f(DF(b)c) dc = ∫_{range DF(b)} f dH^n.
5. The o(r^n) estimate transfers the blow-up limit from F(B) to Y; finrank range DF(b) = n.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606d, mathlib 25730c7c)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/{parent-child-handoff.json,decomposition-scope-v1.json,decomposition-scope-v2.json,decomposition-v2.json,decomposition-audit-v1.json,decomposition-audit-v2.json,decomposition-review-receipt-v1.json,decomposition-review-receipt-v2.json}; sha256(handoff natural_proof) = edb40234e38681383059766fc8fce5de4e38aeb8b70b1da74d3e2f3509f688a2`
- `python3 -I: dag.json scan of all 451 nodes for the 11 dpf_ lean_names (no hits) and for approxTangent/pushforward/area_formula/bilipschitz lean_names`
- `grep -l '"<each dpf_ name>"' nodes/*/decomposition-v*.json (hits only in this node's own v1/v2)`
- `grep -n diffeo-pushforward issue-workers.json; git branch -a | grep diffeo; git grep -n 'dpf_\|imrep_c1_diffeo' <node proof branch> -- GMT (no matches)`
- `rg -n 'pushforward|Pushforward' project/GMT --glob '*.lean'`
- `rg -n 'dpf_|imrep_c1_diffeo|approxTangent.*map|area_formula' project/GMT --glob '*.lean' (no match)`
- `grep -rn in mathlib/Mathlib: exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, ae_tendsto_measure_inter_div, ae_tendsto_average_norm_sub, image_of_continuousOn_injOn, hausdorffMeasure_image_le, contDiff_symm, extDerivWithin_pullback, det_isEmpty, theorem lintegral_iUnion, normDet_comp, normDet_sq_eq_det_gram, euclideanHausdorffMeasure_image, normDet_of_subsingleton, euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_singleton, exists_antilipschitzWith, analyticOnNhd_compContinuousLinearMapCLM, continuous_compContinuousLinearMapCLM, norm_compContinuousLinearMap_le, convolution_tendsto_right_of_continuous, hasFDerivAt_convolution_right, contDiff_convolution_left, lipschitzWith_of_nnnorm_fderiv_le, toHomeomorphOfContinuousClosed, ofInjectiveEndo, eq_smul_basis_det, comp_quasiMeasurePreserving, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, euclideanHausdorffMeasure_homothety_image, euclideanHausdorffMeasure_eq_volume, lintegral_withDensity_eq_lintegral_mul_non_measurable, norm_fderiv_le_of_lipschitz, addHaar_closedBall_eq_addHaar_ball, exists_cthickening_subset_open, continuous_det, det_fromBlocks_zero₂₁, gramSchmidtOrthonormalBasis`
- `grep -n -A12 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt' Mathlib/MeasureTheory/Function/Jacobian.lean; grep -A6 'Homeomorph.contDiff_symm' Mathlib/Analysis/Calculus/ContDiff/Operations.lean; grep -A8 euclideanHausdorffMeasure_homothety_image Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep -A5 'normDet_comp\|normDet_sq_eq_det_gram\|euclideanHausdorffMeasure_image' Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn in simongmt/Poincare/SimonGMT: def areaRegularSet, measurableSet_areaRegularSet, area_image_compl_regularSet_eq_zero, weighted_area_formula_lipschitz_injOn, measurable_areaJacobianAt, def HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique, def blowUpMap, exteriorDerivativeOn_pullbackFormWithin, def pullbackFormWithin, exteriorDerivativeTestOn, boundary_apply, def TestFormOnConverges, def IsTestForm, def IsSmoothForm, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset, def CountablyRectifiable, def areaJacobianAt, structure GeometricCurrentOn`
- `grep -n '^theorem\|^lemma' simongmt/Poincare/SimonGMT/Chapter03/*.lean`
- `lake env lean /tmp/dpf-a3-review/Types.lean`
- `lake env lean /tmp/dpf-a3-review/Assembly.lean (#print axioms assembly_conditional)`
- `lake env lean /tmp/dpf-a3-review/Wiring.lean`
- `lake env lean /tmp/dpf-a3-review/Instances.lean (#print axioms gram_eq_normDet_check)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Analytic/CPolynomial.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/tmp/dpf-a3-review/Types.lean`
- `/tmp/dpf-a3-review/Assembly.lean`
- `/tmp/dpf-a3-review/Wiring.lean`
- `/tmp/dpf-a3-review/Instances.lean`

No declaration in the local snapshot proves this push-forward statement or any of the 11 children, so the children are new. The only related project item is the Ch06 contract's LipschitzPushforwardIntegerMultiplicity, a different Prop about IsLipschitzPushforward that is still unproved (its main_theorem is sorry). SimonGMT Chapter03 asserts no theorem that rectifiable sets have approximate tangent planes almost everywhere. Every library fact the child proofs rely on exists in the pinned Mathlib (25730c7c) and SimonGMT (2b36630) with compatible hypotheses:
- the partition theorem, with rpos : ∀ A, r A ≠ 0;
- Homeomorph.contDiff_symm and the homothety scaling of μHE;
- Besicovitch density and Lebesgue differentiation;
- normDet_comp, normDet_sq_eq_det_gram and euclideanHausdorffMeasure_image;
- SimonGMT's weighted injective Lipschitz area formula, which takes an arbitrary weight and has no rank hypothesis;
- HasApproximateTangentSpaceAt (finrank plus C_c blow-up convergence) and its uniqueness.
All 11 frozen child types and the parent type elaborate in the comparator's replayed contract scope. The parent assembly compiles, and its conditional form uses only propext, Classical.choice and Quot.sound. Sibling wiring and the inferred instances were confirmed in Lean: the Matrix.of Gram expression equals normDet of the restricted map, ‖L‖ is the operator norm, and HasOrthogonalProjection is found. No name collides with the 451 DAG nodes or with other nodes' stored proposals.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
