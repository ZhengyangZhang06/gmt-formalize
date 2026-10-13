import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

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

/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]

/-- **Simon 6.3.2(3)** (with 6.2.4–6.2.8): for `T = τ(M, θ, ξ)` in `U` and open `W ⊆ U`,
`M_W(T) = μ_T(W) = ∫_{M ∩ W} θ dHⁿ`.  Upper bound: for admissible `ω`, `|⟨ω, ξ⟩| ≤ |ω| ≤ 1_W`
`Hⁿ`-a.e. on `M`, so `T(ω) ≤ μ_T(W)`.  Lower bound on a compact `K ⊆ W`, then exhaust `W`: with
`L` the dual of `dor_ims_unitOrientation_dual` (`|L(ξ)| ≤ 1`, `⟨L(ξ), ξ⟩ = 1`), approximate
`f = 1_K L(ξ)` in `L¹(μ_T⌞K_δ)` by a continuous compactly supported `g`, truncate to
`β = g / max(1, |g|)` (so `|β - f| ≤ 2|g - f|`), smooth to `h` with `‖h - β‖ < δ`, and take
`ω = χ h / (1 + Cδ)`, `χ ∈ C^∞`, `χ = 1` on `K`, `spt χ ⊆ K_δ`: `ω` is admissible and
`T(ω) ≥ μ_T(K) - ε`. -/
theorem Submission.dtc_mass_eq_measure : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → W ⊆ U → R.Represents T → T.massOn W = R.measure W := by
  intro P n U W T R _ hW hWU hRT
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `L` is bounded on the unit ball (continuity at `0`)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ ξ : MultiVector P n, ‖ξ‖ ≤ 1 → ‖L ξ‖ ≤ B := by
    have hcont : ∀ ε > 0, ∃ δ > 0, ∀ {x : MultiVector P n}, dist x 0 < δ →
        dist (L x) (L 0) < ε :=
      Metric.continuousAt_iff.1 (L.continuous.continuousAt (x := 0))
    obtain ⟨δ, hδ, hδL⟩ := hcont 1 one_pos
    refine ⟨2 / δ, fun ξ hξ => ?_⟩
    have hsm : ‖(δ / 2) • ξ‖ ≤ δ / 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
      rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
      gcongr
      calc ‖ξ α‖ ≤ ‖ξ‖ * ‖α‖ := ξ.le_opNorm α
        _ ≤ 1 * ‖α‖ := by gcongr
        _ = ‖α‖ := one_mul _
    have h1 : dist ((δ / 2) • ξ) 0 < δ := by
      rw [dist_zero_right (E := MultiVector P n) _]
      linarith
    have h3 : dist (L ((δ / 2) • ξ)) (L 0) < 1 := hδL h1
    rw [map_smul, map_zero, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)] at h3
    rw [le_div_iff₀ hδ]
    nlinarith [norm_nonneg (L ξ)]
  -- `|α| = ‖c α‖` for the linear coefficient map `c α = (α(e_I))_I` (`I` strictly increasing)
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : Covector (Euclid P) n →ₗ[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    { toFun := fun α => WithLp.toLp 2 fun I => if StrictMono I then α (fun i => e (I i)) else 0
      map_add' := fun α β => by
        ext I
        simp only [ContinuousAlternatingMap.add_apply, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := fun a α => by
        ext I
        simp only [ContinuousAlternatingMap.smul_apply, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  have hc : ∀ α, covectorEuclideanNorm α = ‖c α‖ := by
    intro α
    rw [← Real.sqrt_sq (norm_nonneg (c α)), EuclideanSpace.real_norm_sq_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [c, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp [e]
  -- `|α| ≤ C ‖α‖`, since each coefficient is bounded by the operator norm
  set C : ℝ := √(Fintype.card (Fin n → Fin P)) + 1
  have hCpos : 0 < C := by positivity
  have hN3 : ∀ α, ‖c α‖ ≤ C * ‖α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    calc √(∑ I, ‖(c α) I‖ ^ 2) ≤ √(∑ _I : Fin n → Fin P, ‖α‖ ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun I _ => ?_)
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          simp only [c, LinearMap.coe_mk, AddHom.coe_mk]
          split_ifs
          · calc ‖α (fun i => e (I i))‖ ≤ ‖α‖ * ∏ i, ‖e (I i)‖ := α.le_opNorm _
              _ = ‖α‖ := by
                rw [Finset.prod_eq_one (fun i _ => e.orthonormal.norm_eq_one (I i)), mul_one]
          · simp
      _ = √(Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
            Real.sqrt_sq (norm_nonneg _)]
      _ ≤ C * ‖α‖ := by
          gcongr
          linarith
  have hcc : Continuous c := AddMonoidHomClass.continuous_of_bound c C hN3
  have hNc : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simp only [hc]
    exact hcc.norm
  have hNtri : ∀ α β : Covector (Euclid P) n,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hc, hc, hc, map_add]
    exact norm_add_le _ _
  have hNsmul : ∀ (r : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (r • α) = |r| * covectorEuclideanNorm α := by
    intro r α
    rw [hc, hc, map_smul, norm_smul, Real.norm_eq_abs]
  -- truncation `v ↦ v / max(1, |v|)` moves `v` by at most `|v - w|` towards any `|w| ≤ 1`
  have htrunc : ∀ v w : Covector (Euclid P) n, covectorEuclideanNorm w ≤ 1 →
      covectorEuclideanNorm ((max 1 (covectorEuclideanNorm v))⁻¹ • v - w) ≤
        2 * covectorEuclideanNorm (v - w) := by
    intro v w hw
    rcases le_total (covectorEuclideanNorm v) 1 with hv | hv
    · rw [max_eq_left hv, inv_one, one_smul]
      linarith [covectorEuclideanNorm_nonneg (v - w)]
    · rw [max_eq_right hv]
      have hvpos : 0 < covectorEuclideanNorm v := one_pos.trans_le hv
      have e1 : covectorEuclideanNorm ((covectorEuclideanNorm v)⁻¹ • v - v) =
          covectorEuclideanNorm v - 1 := by
        rw [show (covectorEuclideanNorm v)⁻¹ • v - v = ((covectorEuclideanNorm v)⁻¹ - 1) • v by
          module, hNsmul,
          abs_of_nonpos (sub_nonpos.2 (inv_le_one_of_one_le₀ hv)), neg_sub, sub_mul, one_mul,
          inv_mul_cancel₀ hvpos.ne']
      have e2 : covectorEuclideanNorm v ≤
          covectorEuclideanNorm (v - w) + covectorEuclideanNorm w := by
        calc covectorEuclideanNorm v = covectorEuclideanNorm ((v - w) + w) := by
              rw [sub_add_cancel]
          _ ≤ _ := hNtri _ _
      calc covectorEuclideanNorm ((covectorEuclideanNorm v)⁻¹ • v - w)
          = covectorEuclideanNorm (((covectorEuclideanNorm v)⁻¹ • v - v) + (v - w)) := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := hNtri _ _
        _ ≤ 2 * covectorEuclideanNorm (v - w) := by rw [e1]; linarith
  -- good points: `ξ(x)` is a unit orientation of the approximate tangent plane
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      (∀ α, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
      covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 ∧
      ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    obtain ⟨h1, h2, h3⟩ := hL _ Q hQ
    exact ⟨h1, h2, h3, (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2⟩
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgoodμ := hac.ae_le hgood
  -- `T(ω) = ∫ ⟨ω, ξ⟩ dμ` for `μ = θ Hⁿ⌞M`
  have hθ : Measurable fun x => (R.mult x : NNReal) :=
    measurable_from_nat.comp R.measurable_mult
  have hT : ∀ ω : TestFormOn U n,
      T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
    intro ω
    rw [hRT ω, IMRep.action, IMRep.measure]
    have : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    rw [this, integral_withDensity_eq_integral_smul hθ]
    congr 1
  apply le_antisymm
  · -- upper bound: `T(ω) ≤ ∫ |ω| dμ ≤ μ(W)` for admissible `ω`
    apply sSup_le
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    dsimp only
    rw [hT ω]
    calc ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure)
        ≤ ‖∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂R.measure :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, W.indicator 1 x ∂R.measure := by
          apply lintegral_mono_ae
          filter_upwards [hgoodμ] with x hx
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW, Pi.one_apply, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.2 ((hx.1 _).trans (hω1 x))
          · have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
              image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h)
            rw [this, map_zero, enorm_zero]
            exact zero_le
      _ = R.measure W := lintegral_indicator_one hW.measurableSet
  · -- lower bound on a compact `K ⊆ W`: an admissible `ω ≈ 1_K L(ξ)` with `T(ω) ≥ μ(K) - ε`
    have hcompact : ∀ K : Set (Euclid P), IsCompact K → K ⊆ W → R.measure K ≤ T.massOn W := by
      intro K hK hKW
      obtain ⟨δ₀, hδ₀, hδ₀W⟩ := hK.exists_cthickening_subset_open hW hKW
      have hKV : K ⊆ thickening δ₀ K := self_subset_thickening hδ₀ K
      have hμC : R.measure (cthickening δ₀ K) < ∞ := by
        rw [IMRep.measure, withDensity_apply _ isClosed_cthickening.measurableSet,
          Measure.restrict_restrict isClosed_cthickening.measurableSet, inter_comm]
        exact lt_top_iff_ne_top.2
          (R.locallyIntegrable_mult _ hK.cthickening (hδ₀W.trans hWU))
      have hμV : R.measure (thickening δ₀ K) < ∞ :=
        (measure_mono (thickening_subset_cthickening δ₀ K)).trans_lt hμC
      have hμK : R.measure K < ∞ := (measure_mono hKV).trans_lt hμV
      -- `ν = μ⌞V`, `V = K_{δ₀}`, is finite
      set V := thickening δ₀ K
      set ν := R.measure.restrict V with hν
      have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμV.ne
      have hgoodν := ae_restrict_of_ae (s := V) hgoodμ
      have hacν : ν ≪ μHE[n].restrict R.carrier :=
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac
      have hξν : AEStronglyMeasurable R.orient ν := R.aestronglyMeasurable_orient.mono_ac hacν
      have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
        isBoundedBilinearMap_apply.continuous
      have hevalm : ∀ v : Euclid P → Covector (Euclid P) n, AEStronglyMeasurable v ν →
          AEStronglyMeasurable (fun x => R.orient x (v x)) ν := fun v hv =>
        (hev.comp_aestronglyMeasurable (hξν.prodMk hv) :)
      -- the target `f = 1_K L(ξ)`: `|f| ≤ 1` and `ξ(f) = 1_K` a.e.
      set f : Euclid P → Covector (Euclid P) n := K.indicator fun x => L (R.orient x) with hf
      have hfm : AEStronglyMeasurable f ν :=
        (L.continuous.comp_aestronglyMeasurable hξν).indicator hK.measurableSet
      have hfi : Integrable f ν := by
        refine Integrable.of_bound hfm (max B 0) ?_
        filter_upwards [hgoodν] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK]
          exact (hB _ hx.2.2.2).trans (le_max_left _ _)
        · rw [hf, indicator_of_notMem hxK, norm_zero]
          exact le_max_right _ _
      have hf1 : ∀ᵐ x ∂ν, covectorEuclideanNorm (f x) ≤ 1 := by
        filter_upwards [hgoodν] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK]
          exact hx.2.1
        · rw [hf, indicator_of_notMem hxK, covectorEuclideanNorm_zero]
          exact zero_le_one
      have hfξi : Integrable (fun x => R.orient x (f x)) ν := by
        refine Integrable.of_bound (hevalm _ hfm) 1 ?_
        filter_upwards [hgoodν, hf1] with x hx hx1
        rw [Real.norm_eq_abs]
        exact (hx.1 _).trans hx1
      have hμKf : (R.measure K).toReal = ∫ x, R.orient x (f x) ∂ν := by
        have : (fun x => R.orient x (f x)) =ᵐ[ν] K.indicator 1 := by
          filter_upwards [hgoodν] with x hx
          by_cases hxK : x ∈ K
          · rw [hf, indicator_of_mem hxK, indicator_of_mem hxK, Pi.one_apply, hx.2.2.1]
          · rw [hf, indicator_of_notMem hxK, indicator_of_notMem hxK, map_zero]
        rw [integral_congr_ae this, integral_indicator_one hK.measurableSet, Measure.real, hν,
          Measure.restrict_apply hK.measurableSet, inter_eq_left.2 hKV]
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      -- tolerance `δ`
      set δ : ℝ := (ε : ℝ) / (4 * C * (ν.real univ + 1)) with hδ
      have hδpos : 0 < δ := by
        have : (0 : ℝ) < ε := hε
        positivity
      -- `g` continuous with compact support, `∫ ‖f - g‖ dν ≤ δ`
      obtain ⟨g, hgcs, hgf, hgc, hgi⟩ := hfi.exists_hasCompactSupport_integral_sub_le hδpos
      -- truncation `β = g / max(1, |g|)`, so `|β| ≤ 1`
      set β : Euclid P → Covector (Euclid P) n :=
        fun x => (max 1 (covectorEuclideanNorm (g x)))⁻¹ • g x with hβ
      have hmax : ∀ x, 0 < max 1 (covectorEuclideanNorm (g x)) :=
        fun x => one_pos.trans_le (le_max_left _ _)
      have hβc : Continuous β :=
        ((continuous_const.max (hNc.comp hgc)).inv₀ fun x => (hmax x).ne').smul hgc
      have hβs : HasCompactSupport β := hgcs.mono fun x hx hgx => hx (by
        rw [hβ]
        dsimp only
        rw [hgx, smul_zero])
      have hβ1 : ∀ x, covectorEuclideanNorm (β x) ≤ 1 := by
        intro x
        rw [hβ]
        dsimp only
        rw [hNsmul, abs_of_pos (inv_pos.2 (hmax x)), inv_mul_le_iff₀ (hmax x), mul_one]
        exact le_max_right _ _
      have hβg : ∀ x, covectorEuclideanNorm (β x) ≤ covectorEuclideanNorm (g x) := by
        intro x
        rw [hβ]
        dsimp only
        rw [hNsmul, abs_of_pos (inv_pos.2 (hmax x)), inv_mul_le_iff₀ (hmax x)]
        exact le_mul_of_one_le_left (covectorEuclideanNorm_nonneg _) (le_max_left _ _)
      -- smoothing: `h` smooth, `‖h - β‖ < δ`
      obtain ⟨h, hhs, hhβ⟩ :=
        (hβs.uniformContinuous_of_continuous hβc).exists_contDiff_dist_le hδpos
      have hhβE : ∀ x, covectorEuclideanNorm (h x - β x) ≤ C * δ := by
        intro x
        rw [hc]
        refine (hN3 _).trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
        rw [← dist_eq_norm]
        exact (hhβ x).le
      -- cutoff `χ ∈ C^∞`, `0 ≤ χ ≤ 1`, `support χ = V`, `χ = 1` on `K`
      obtain ⟨χ, hχs, hχr, hχsupp, hχ1⟩ :=
        exists_contDiff_support_eq_eq_one_iff (n := ⊤) isOpen_thickening hK.isClosed hKV
      have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => hχr (mem_range_self x)
      have hχ0 : ∀ x, x ∉ V → χ x = 0 := fun x hx => by
        rw [← Function.notMem_support, hχsupp]
        exact hx
      -- the form `ω = a χ h`, `a = (1 + Cδ)⁻¹`
      set a : ℝ := (1 + C * δ)⁻¹ with ha
      have hCδ : 0 < C * δ := mul_pos hCpos hδpos
      have haC : a * (1 + C * δ) = 1 := inv_mul_cancel₀ (by positivity)
      have hapos : 0 < a := inv_pos.2 (by positivity)
      have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      set ω₀ : DifferentialForm (Euclid P) n := fun x => (a * χ x) • h x with hω₀
      have hω₀0 : ∀ x, x ∉ V → ω₀ x = 0 := fun x hx => by
        rw [hω₀]
        dsimp only
        rw [hχ0 x hx, mul_zero, zero_smul]
      have hω₀s : IsSmoothForm ω₀ := (contDiff_const.mul hχs).smul hhs
      have hω₀c : HasCompactSupport ω₀ :=
        HasCompactSupport.intro hK.cthickening fun x hx =>
          hω₀0 x fun hxV => hx (thickening_subset_cthickening δ₀ K hxV)
      have hω₀W : tsupport ω₀ ⊆ W := by
        refine (closure_minimal (fun x hx => ?_) isClosed_cthickening).trans hδ₀W
        by_contra hxC
        exact hx (hω₀0 x fun hxV => hxC (thickening_subset_cthickening δ₀ K hxV))
      have hω₀1 : ∀ x, covectorEuclideanNorm (ω₀ x) ≤ 1 := by
        intro x
        rw [hω₀]
        dsimp only
        rw [hNsmul, abs_of_nonneg (mul_nonneg hapos.le (hχ01 x).1)]
        have hhx : covectorEuclideanNorm (h x) ≤ 1 + C * δ := by
          calc covectorEuclideanNorm (h x) = covectorEuclideanNorm (β x + (h x - β x)) := by
                rw [add_sub_cancel]
            _ ≤ _ := hNtri _ _
            _ ≤ 1 + C * δ := add_le_add (hβ1 x) (hhβE x)
        calc a * χ x * covectorEuclideanNorm (h x) ≤ a * 1 * (1 + C * δ) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hχ01 x).2 hapos.le) hhx
                (covectorEuclideanNorm_nonneg _) (by rw [mul_one]; exact hapos.le)
          _ = 1 := by rw [mul_one, haC]
      let ω : TestFormOn U n := ⟨ω₀, ⟨hω₀s, hω₀c⟩, hω₀W.trans hWU⟩
      have hωadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀W, hω₀1⟩
      -- `T(ω) = ∫ ξ(ω) dν`
      have hTω : T ω = ∫ x, R.orient x (ω₀ x) ∂ν := by
        rw [hT ω, hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        change R.orient x (ω₀ x) = 0
        rw [hω₀0 x hx, map_zero]
      have hω₀i : Integrable (fun x => R.orient x (ω₀ x)) ν := by
        refine Integrable.of_bound (hevalm _ hω₀s.continuous.aestronglyMeasurable) 1 ?_
        filter_upwards [hgoodν] with x hx
        rw [Real.norm_eq_abs]
        exact (hx.1 _).trans (hω₀1 x)
      -- pointwise: `|ξ(ω - f)| ≤ |ω - f| ≤ 2Cδ + 2C‖f - g‖`
      have hpt : ∀ᵐ x ∂ν, ‖R.orient x (ω₀ x) - R.orient x (f x)‖ ≤
          2 * C * δ + 2 * C * ‖f x - g x‖ := by
        filter_upwards [hgoodν, hf1] with x hx hx1
        rw [← map_sub, Real.norm_eq_abs]
        refine (hx.1 _).trans ?_
        have h1 : covectorEuclideanNorm (ω₀ x - χ x • β x) ≤ 2 * C * δ := by
          have e : ω₀ x - χ x • β x = χ x • (a • (h x - β x) + (-(1 - a)) • β x) := by
            rw [hω₀]
            dsimp only
            module
          rw [e, hNsmul, abs_of_nonneg (hχ01 x).1]
          have e2 : covectorEuclideanNorm (a • (h x - β x) + (-(1 - a)) • β x) ≤
              a * (C * δ) + (1 - a) * 1 := by
            refine (hNtri _ _).trans ?_
            rw [hNsmul, hNsmul, abs_of_pos hapos, abs_neg, abs_of_nonneg (sub_nonneg.2 ha1)]
            exact add_le_add (mul_le_mul_of_nonneg_left (hhβE x) hapos.le)
              (mul_le_mul_of_nonneg_left (hβ1 x) (sub_nonneg.2 ha1))
          calc χ x * covectorEuclideanNorm (a • (h x - β x) + (-(1 - a)) • β x)
              ≤ 1 * (a * (C * δ) + (1 - a) * 1) :=
                mul_le_mul (hχ01 x).2 e2 (covectorEuclideanNorm_nonneg _) zero_le_one
            _ ≤ 2 * C * δ := by
                have h1a : 1 - a = a * (C * δ) := by
                  rw [mul_add, mul_one] at haC
                  linarith
                have h2a : a * (C * δ) ≤ C * δ := mul_le_of_le_one_left hCδ.le ha1
                rw [h1a]
                linarith
        have h2 : covectorEuclideanNorm (χ x • β x - f x) ≤ 2 * C * ‖f x - g x‖ := by
          have hgfE : covectorEuclideanNorm (g x - f x) ≤ C * ‖f x - g x‖ := by
            rw [hc, norm_sub_rev (f x)]
            exact hN3 _
          by_cases hxK : x ∈ K
          · rw [(hχ1 x).1 hxK, one_smul]
            refine (htrunc (g x) (f x) hx1).trans ?_
            linarith
          · have hfx : f x = 0 := by rw [hf, indicator_of_notMem hxK]
            rw [show χ x • β x - f x = χ x • β x by rw [hfx, sub_zero], hNsmul,
              abs_of_nonneg (hχ01 x).1]
            have hgf0 : covectorEuclideanNorm (g x) ≤ C * ‖f x - g x‖ := by
              rw [hfx, zero_sub, norm_neg, hc]
              exact hN3 _
            have hn : 0 ≤ C * ‖f x - g x‖ := by positivity
            calc χ x * covectorEuclideanNorm (β x) ≤ 1 * covectorEuclideanNorm (g x) := by
                  gcongr
                  · exact covectorEuclideanNorm_nonneg _
                  · exact (hχ01 x).2
                  · exact hβg x
              _ ≤ 2 * C * ‖f x - g x‖ := by linarith
        calc covectorEuclideanNorm (ω₀ x - f x)
            = covectorEuclideanNorm ((ω₀ x - χ x • β x) + (χ x • β x - f x)) := by
              rw [sub_add_sub_cancel]
          _ ≤ _ := hNtri _ _
          _ ≤ 2 * C * δ + 2 * C * ‖f x - g x‖ := add_le_add h1 h2
      -- integrate: `|T(ω) - μ(K)| ≤ 2Cδ ν(V) + 2Cδ = ε/2`
      have hfgi : Integrable (fun x => ‖f x - g x‖) ν := (hfi.sub hgi).norm
      have hbi : Integrable (fun x => 2 * C * δ + 2 * C * ‖f x - g x‖) ν :=
        (integrable_const _).add (hfgi.const_mul _)
      have hest : |T ω - (R.measure K).toReal| ≤ ε / 2 := by
        rw [hTω, hμKf, ← integral_sub hω₀i hfξi, ← Real.norm_eq_abs]
        refine (norm_integral_le_of_norm_le hbi hpt).trans ?_
        rw [integral_add (integrable_const _) (hfgi.const_mul _), integral_const,
          integral_const_mul, smul_eq_mul]
        have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
        calc ν.real univ * (2 * C * δ) + 2 * C * ∫ x, ‖f x - g x‖ ∂ν
            ≤ ν.real univ * (2 * C * δ) + 2 * C * δ := by gcongr
          _ = 2 * C * δ * (ν.real univ + 1) := by ring
          _ = ε / 2 := by
            rw [hδ]
            field_simp
            ring
      have hTω' : (R.measure K).toReal ≤ T ω + ε := by
        have := (abs_le.1 hest).1
        have : (0 : ℝ) ≤ ε := ε.coe_nonneg
        linarith
      calc R.measure K = ENNReal.ofReal (R.measure K).toReal :=
            (ENNReal.ofReal_toReal hμK.ne).symm
        _ ≤ ENNReal.ofReal (T ω + ε) := ENNReal.ofReal_le_ofReal hTω'
        _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (T ω) + ε := by rw [ENNReal.ofReal_coe_nnreal]
        _ ≤ T.massOn W + ε := by gcongr; exact T.le_massOn hωadm
    -- exhaust `W` by the increasing compact sets `F m ∩ B̄_m(0)`
    obtain ⟨F, hFc, hFW, hFU, hFm⟩ := hW.exists_iUnion_isClosed
    have hKm : Monotone fun m : ℕ => F m ∩ closedBall (0 : Euclid P) m := fun a b hab =>
      inter_subset_inter (hFm hab) (closedBall_subset_closedBall (Nat.cast_le.2 hab))
    have hKU : ⋃ m : ℕ, F m ∩ closedBall (0 : Euclid P) m = W := by
      refine Subset.antisymm (iUnion_subset fun m => inter_subset_left.trans (hFW m))
        fun x hx => ?_
      rw [← hFU] at hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := exists_nat_ge (dist x 0)
      exact mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha,
        mem_closedBall.2 (hb.trans (Nat.cast_le.2 (le_max_right a b)))⟩
    calc R.measure W = R.measure (⋃ m : ℕ, F m ∩ closedBall (0 : Euclid P) m) := by rw [hKU]
      _ = ⨆ m : ℕ, R.measure (F m ∩ closedBall (0 : Euclid P) m) := hKm.measure_iUnion
      _ ≤ T.massOn W := iSup_le fun m => hcompact _
          ((isCompact_closedBall 0 m).inter_left (hFc m)) (inter_subset_left.trans (hFW m))

/-- **Existence and upper semicontinuity of the density** (Simon 7.3.1(1), first sentence of its
proof; Ch. 4, 3.16–3.17 and 3.11).  Let `n ≥ 1`, `U` open and `T = τ(M, θ, ξ)` in `U`, where
`V = v(M, θ)` has locally bounded generalized mean curvature in `U`, `μ = θHⁿ⌞M`.  Then
`Θⁿ(μ_T, x)` exists at every `x ∈ U` and is upper semicontinuous on `U`.

Step 0: `TᵧM` is read off the orientation `ξ(y) = ±τ₁ ∧ ⋯ ∧ τₙ`.  For the coordinate covectors
`e^K` (`K : Fin n → Fin P`), Hadamard's inequality and an orthonormal completion give
`|p_{TᵧM} w| = max_{|vᵢ| ≤ 1} |∑_K (∏ᵢ (w, v)ᵢ^{Kᵢ}) ⟨e^K, ξ(y)⟩|`, a continuous function of
`(⟨e^K, ξ(y)⟩)_K` and `w`; so `div_M X` is `μ`-measurable and the first variation is a genuine
integral.  Steps 1–2: testing with `X = Φ_a(|y - x|²/t²)(y - x)`, where `Φ_a` is a `C¹`
nonincreasing profile equal to `1` on `(-∞, 1]` and `0` on `[a, ∞)`, gives
`n I - t I' ≤ Λ t I` for `I(t) = ∫ Φ_a(|y - x|²/t²) dμ` (`div_M X = nΦ + 2Φ'|p(y - x)|²/t²`,
`|X · H| ≤ 2tΛ₀Φ`), so `e^{Λt} t⁻ⁿ I(t)` is nondecreasing; letting `a ↓ 1`, so is
`e^{Λt} t⁻ⁿ μ(B_t(x))`, with the same `Λ` for all `x` near a given point.  Steps 3–5: the density
is the limit (infimum) of these monotone quantities; `M_{B_ρ(x)}(T) = μ(B_ρ(x))`
(`dtc_mass_eq_measure`) gives `HasMassDensity`, and comparing balls at nearby centres gives upper
semicontinuity. -/
theorem Submission.dtc_density_usc : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → 0 < n → R.Represents T → R.HasLocallyBoundedMeanCurvature → ∃ Θ : Euclid P → ℝ, (∀ x ∈ U, HasMassDensity T x (Θ x)) ∧ UpperSemicontinuousOn Θ U := by
  intro P n U T R hU hn hrep hH
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  obtain ⟨H, -, hHb, hfv⟩ := hH
  -- Step 0: `y ↦ |p_y w|` is `Hⁿ⌞M`-measurable, read off the orientation `ξ`
  have hpm : ∀ x : Euclid P, AEStronglyMeasurable
      (fun y => ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖) R.measure := by
    obtain ⟨F, hF, c, hc, hFc⟩ : ∃ F : ((Fin (m + 1) → Fin P) → ℝ) × Euclid P → ℝ, Continuous F ∧
        ∃ c : Euclid P → ((Fin (m + 1) → Fin P) → ℝ),
          AEStronglyMeasurable c (μHE[m + 1].restrict R.carrier) ∧
          ∀ᵐ y ∂(μHE[m + 1].restrict R.carrier), ∀ w,
            ‖(approxTangentPlane (m + 1) R.carrier y).starProjection w‖ = F (c y, w) := by
      -- coordinate `n`-covectors `e K`, `e K w = det (w j (K i))`
      have hfact : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
      let b₀ := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
      let o₀ : Orientation ℝ (Euclid (m + 1)) (Fin (m + 1)) := b₀.toBasis.orientation
      let L : (Fin (m + 1) → Fin P) → (Euclid P →L[ℝ] Euclid (m + 1)) := fun K =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.pi fun j => EuclideanSpace.proj (K j))
      let e : (Fin (m + 1) → Fin P) → Covector (Euclid P) (m + 1) := fun K =>
        (b₀.toBasis.det.compLinearMap (L K).toLinearMap).mkContinuous (‖L K‖ ^ (m + 1)) fun w => by
          rw [Real.norm_eq_abs]
          calc |b₀.toBasis.det.compLinearMap (L K).toLinearMap w|
              = |o₀.volumeForm fun i => L K (w i)| := (o₀.volumeForm_robust' b₀ _).symm
            _ ≤ ∏ i, ‖L K (w i)‖ := o₀.abs_volumeForm_apply_le _
            _ ≤ ∏ i, (‖L K‖ * ‖w i‖) :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => (L K).le_opNorm _
            _ = ‖L K‖ ^ (m + 1) * ∏ i, ‖w i‖ := by
                rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have he : ∀ K (w : Fin (m + 1) → Euclid P), e K w = Matrix.det (Matrix.of fun i j => w j (K i)) := by
        intro K w
        show b₀.toBasis.det (fun i => L K (w i)) = _
        rw [Module.Basis.det_apply]
        rfl
      -- expansion of `det ⟪aᵢ, τⱼ⟫` in the coordinate covectors
      have hexp : ∀ a τ : Fin (m + 1) → Euclid P,
          Matrix.det (Matrix.of fun i j => inner ℝ (a i) (τ j)) =
            ∑ K : Fin (m + 1) → Fin P, (∏ i, a i (K i)) * e K τ := by
        intro a τ
        have hrow : (Matrix.of fun i j => inner ℝ (a i) (τ j)) =
            fun i => ∑ k, a i k • fun j => τ j k := by
          ext i j
          simp [PiLp.inner_apply, Finset.sum_apply, mul_comm]
        rw [hrow]
        have h1 := (Matrix.detRowAlternating (n := Fin (m + 1)) (R := ℝ)).toMultilinearMap.map_sum
          (fun i k => a i k • fun j => τ j k)
        simp only [AlternatingMap.coe_multilinearMap] at h1
        refine h1.trans (Finset.sum_congr rfl fun K _ => ?_)
        rw [he, ← AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ]
        rfl
      -- the sup formula
      let f : (((Fin (m + 1) → Fin P) → ℝ) × Euclid P) → (Fin m → Euclid P) → ℝ := fun p v =>
        |∑ K : Fin (m + 1) → Fin P, (∏ i, (Fin.cons p.2 v : Fin (m + 1) → Euclid P) i (K i)) * p.1 K|
      refine ⟨fun p => sSup (f p '' closedBall 0 1),
        IsCompact.continuous_sSup (isCompact_closedBall _ _) (by fun_prop),
        fun y K => R.orient y (e K),
        (continuous_pi fun K => (ContinuousLinearMap.apply ℝ ℝ (e K)).continuous).comp_aestronglyMeasurable
          R.aestronglyMeasurable_orient, ?_⟩
      filter_upwards [R.orients] with y hy
      obtain ⟨Q, hQ, τ, hτ, hspan, hsign⟩ := hy
      have hT : approxTangentPlane (m + 1) R.carrier y = Q := by
        have h : ∃ Q, HasApproximateTangentSpaceAt (m + 1) R.carrier y Q := ⟨Q, hQ⟩
        rw [approxTangentPlane, dite_eq_left h]
        exact h.choose_spec.unique hQ
      rw [hT]
      -- an orthonormal basis of `Q` from the frame `τ`
      have hmem : ∀ i, τ i ∈ Q := fun i => hspan ▸ Submodule.subset_span (mem_range_self i)
      let w₀ : Fin (m + 1) → Q := fun i => ⟨τ i, hmem i⟩
      have hw₀ : Orthonormal ℝ w₀ := by
        rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w₀)]
        exact hτ
      have hw₀span : ⊤ ≤ Submodule.span ℝ (range w₀) := by
        rintro ⟨z, hz⟩ -
        rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hz
        obtain ⟨c, hc⟩ := hz
        rw [Submodule.mem_span_range_iff_exists_fun]
        exact ⟨c, Subtype.ext (by simp only [Submodule.coe_sum, Submodule.coe_smul]; exact hc)⟩
      let b := OrthonormalBasis.mk hw₀ hw₀span
      have hb : ∀ i, (b i : Euclid P) = τ i := fun i =>
        congrArg Subtype.val (congrFun (OrthonormalBasis.coe_mk hw₀ hw₀span) i)
      have hQdim : Module.finrank ℝ Q = m + 1 :=
        (Module.finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _)
      have : Fact (Module.finrank ℝ Q = m + 1) := ⟨hQdim⟩
      let o : Orientation ℝ Q (Fin (m + 1)) := b.toBasis.orientation
      let π := Q.orthogonalProjectionOnto
      have hbdet : ∀ a : Fin (m + 1) → Euclid P,
          b.toBasis.det (fun j => π (a j)) = Matrix.det (Matrix.of fun i j => inner ℝ (a i) (τ j)) := by
        intro a
        rw [Module.Basis.det_apply, ← Matrix.det_transpose]
        congr 1
        ext i j
        rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, hb,
          real_inner_comm]
        rfl
      have hD : ∀ a : Fin (m + 1) → Euclid P,
          |∑ K : Fin (m + 1) → Fin P, (∏ i, a i (K i)) * R.orient y (e K)| =
            |b.toBasis.det (fun j => π (a j))| := by
        intro a
        rw [hbdet, hexp]
        rcases hsign with h | h
        · simp only [h]
        · simp only [h, mul_neg, Finset.sum_neg_distrib, abs_neg]
      have hHad : ∀ a : Fin (m + 1) → Euclid P, |b.toBasis.det (fun j => π (a j))| ≤ ∏ j, ‖π (a j)‖ :=
        fun a => by rw [← o.volumeForm_robust' b]; exact o.abs_volumeForm_apply_le _
      have hnorm : ∀ w, ‖Q.starProjection w‖ = ‖π w‖ := fun w => by
        rw [Submodule.starProjection_apply]; rfl
      have hup : ∀ w (v : Fin m → Euclid P), ‖v‖ ≤ 1 →
          |b.toBasis.det (fun j => π ((Fin.cons w v : Fin (m + 1) → Euclid P) j))| ≤ ‖π w‖ := by
        intro w v hv
        refine (hHad _).trans ?_
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
          fun i _ => ?_)
        rw [Fin.cons_succ]
        exact (Q.norm_orthogonalProjectionOnto_apply_le _).trans ((norm_le_pi_norm v i).trans hv)
      intro w
      refine (IsGreatest.csSup_eq ⟨?_, ?_⟩).symm
      · by_cases h0 : π w = 0
        · refine ⟨0, mem_closedBall_self zero_le_one, ?_⟩
          show |_| = _
          rw [hD, hnorm, h0, norm_zero]
          exact le_antisymm ((hup w 0 (by rw [norm_zero]; exact zero_le_one)).trans_eq
            (by rw [h0, norm_zero])) (abs_nonneg _)
        · have hu : ‖(‖π w‖⁻¹ • π w)‖ = 1 := by
            rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
          obtain ⟨c', hc'⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := Q)
            (ι := Fin (m + 1)) (hQdim.trans (Fintype.card_fin _).symm)
            (v := fun _ => ‖π w‖⁻¹ • π w) (s := {0})
            ⟨fun i => hu, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
          have hc0 : c' 0 = ‖π w‖⁻¹ • π w := hc' 0 rfl
          refine ⟨fun i => (c' i.succ : Euclid P), ?_, ?_⟩
          · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
            intro i
            exact le_of_eq (c'.orthonormal.1 i.succ)
          · show |_| = _
            rw [hD, hnorm]
            have hcomp : (fun j => π ((Fin.cons w (fun i => (c' i.succ : Euclid P)) :
                Fin (m + 1) → Euclid P) j)) =
                fun j => (Fin.cons ‖π w‖ (fun _ => 1) : Fin (m + 1) → ℝ) j • c' j := by
              funext j
              refine Fin.cases ?_ (fun i => ?_) j
              · simp only [Fin.cons_zero, hc0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
              · simp only [Fin.cons_succ, one_smul]
                exact Q.orthogonalProjectionOnto_mem_subspace_eq_self _
            rw [hcomp, ← AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ,
              AlternatingMap.coe_multilinearMap, Fin.prod_univ_succ, Fin.cons_zero, smul_eq_mul, abs_mul,
              ← o.volumeForm_robust' b, o.abs_volumeForm_apply_of_orthonormal]
            simp only [Fin.cons_succ, Finset.prod_const_one, mul_one, abs_norm]
      · rintro _ ⟨v, hv, rfl⟩
        show |_| ≤ _
        rw [hD, hnorm]
        exact hup w v (by simpa using hv)
    intro x
    exact ((hF.comp_aestronglyMeasurable (hc.prodMk
      (continuous_id.sub continuous_const).aestronglyMeasurable)).congr
        (hFc.mono fun y hy => (hy (y - x)).symm)).mono_ac (withDensity_absolutelyContinuous _ _)
  set μ := R.measure with hμ
  -- `μ = θHⁿ⌞M` is finite on compact subsets of `U`
  have hfin : ∀ K, IsCompact K → K ⊆ U → μ K ≠ ∞ := by
    intro K hK hKU
    rw [hμ, IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Steps 1–2: locally uniform monotonicity of `e^{Λt} t⁻ⁿ μ(B_t(x))` (Simon 4.3.16–3.17)
  have hmono : ∀ x₀ ∈ U, ∃ R₀ > 0, ∃ Λ : ℝ, closedBall x₀ (4 * R₀) ⊆ U ∧
      ∀ x ∈ ball x₀ R₀, MonotoneOn
        (fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal / t ^ (m + 1)) (Ioo 0 R₀) := by
    -- cutoff profiles `Φ a`: `1` on `(-∞, 1]`, `0` on `[a, ∞)`, `C¹`, nonincreasing
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ → ℝ, Φ = fun a s => Real.smoothTransition ((a - s) / (a - 1)) :=
      ⟨_, rfl⟩
    have hΦ1 : ∀ a s, 1 < a → s ≤ 1 → Φ a s = 1 := fun a s ha hs => by
      rw [hΦdef]
      exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hΦ0 : ∀ a s, 1 < a → a ≤ s → Φ a s = 0 := fun a s ha hs => by
      rw [hΦdef]
      exact Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    have hΦnn : ∀ a s, 0 ≤ Φ a s := fun a s => by rw [hΦdef]; exact Real.smoothTransition.nonneg _
    have hΦle : ∀ a s, Φ a s ≤ 1 := fun a s => by rw [hΦdef]; exact Real.smoothTransition.le_one _
    have hΦC1 : ∀ a, ContDiff ℝ 1 (Φ a) := fun a => by
      rw [hΦdef]
      exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
    have hΦc : ∀ a, Continuous (Φ a) := fun a => (hΦC1 a).continuous
    have hΦd : ∀ a s, HasDerivAt (Φ a) (deriv (Φ a) s) s := fun a s =>
      ((hΦC1 a).differentiable one_ne_zero s).hasDerivAt
    have hΦdc : ∀ a, Continuous (deriv (Φ a)) := fun a => (hΦC1 a).continuous_deriv le_rfl
    have hΦdnp : ∀ a s, 1 < a → deriv (Φ a) s ≤ 0 := fun a s ha => by
      refine Antitone.deriv_nonpos fun s₁ s₂ h => ?_
      rw [hΦdef]
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))
    have hΦd0 : ∀ a s, 1 < a → (s < 1 ∨ a < s) → deriv (Φ a) s = 0 := fun a s ha hs => by
      rcases hs with hs | hs
      · rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (1 : ℝ))
          ((eventually_lt_nhds hs).mono fun s' hs' => hΦ1 a s' ha hs'.le), deriv_const]
      · rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
          ((eventually_gt_nhds hs).mono fun s' hs' => hΦ0 a s' ha hs'.le), deriv_const]
    have hΦbd : ∀ a, 1 < a → ∃ C, ∀ s, |s * deriv (Φ a) s| ≤ C := fun a ha =>
      Continuous.bounded_above_of_compact_support (continuous_id.mul (hΦdc a))
        (HasCompactSupport.intro (isCompact_Icc (a := 1) (b := a)) fun s hs => by
          show s * deriv (Φ a) s = 0
          rw [hΦd0 a s ha (by simp only [mem_Icc, not_and_or, not_le] at hs; exact hs), mul_zero])
    have hdt : ∀ a r2 t : ℝ, t ≠ 0 → HasDerivAt (fun t => Φ a (r2 / t ^ 2))
        (deriv (Φ a) (r2 / t ^ 2) * (-2 * (r2 / t ^ 2) / t)) t := by
      intro a r2 t ht
      have h1 : HasDerivAt (fun t : ℝ => r2 / t ^ 2) (-2 * (r2 / t ^ 2) / t) t := by
        convert (hasDerivAt_const t r2).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht) using 1
        norm_num
        field_simp
      exact (hΦd a _).comp t h1
    have hcancel : ∀ D q t : ℝ, t ≠ 0 → -t * (D * (-2 * q / t)) = 2 * (q * D) := by
      intro D q t ht
      field_simp
    have hr1 : ∀ D q r2 N u : ℝ, D ≤ 0 → 0 ≤ u → 0 ≤ N → N ≤ r2 → q = r2 * u →
        q * D ≤ D * u * N ∧ D * u * N ≤ 0 := by
      intro D q r2 N u hD hu hN hNr hq
      have h1 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hD hu) (sub_nonneg.2 hNr)
      have h2 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hD hu) hN
      have e : q * D - D * u * N = D * u * (r2 - N) := by rw [hq]; ring
      exact ⟨by linarith, h2⟩
    have hr2 : ∀ k φ D q N u C : ℝ, 0 ≤ k → 0 ≤ φ → φ ≤ 1 → |q * D| ≤ C → q * D ≤ D * u * N →
        D * u * N ≤ 0 → |k * φ + 2 * (D * u) * N| ≤ k + 2 * C := by
      intro k φ D q N u C hk hφ hφ1 hC h1 h2
      have h3 := abs_le.1 hC
      have h4 := mul_nonneg hk hφ
      have h5 := mul_le_of_le_one_right hk hφ1
      have e : 2 * (D * u) * N = 2 * (D * u * N) := by ring
      exact abs_le.2 ⟨by linarith, by linarith⟩
    intro x₀ hx₀
    -- `dim Tᵧ = n` for `μ`-a.e. `y`
    have hrank : ∀ᵐ y ∂μ, Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier y) = m + 1 := by
      refine (withDensity_absolutelyContinuous _ _).ae_le ?_
      filter_upwards [R.orients] with y hy
      obtain ⟨Q, hQ, -⟩ := hy
      have h : ∃ Q, HasApproximateTangentSpaceAt (m + 1) R.carrier y Q := ⟨Q, hQ⟩
      rw [approxTangentPlane, dite_eq_left h]
      exact h.choose_spec.finrank_eq
    -- Simon 4.3.2: `div_M X = n η(|y - x|²) + 2 η'(|y - x|²) |p_y(y - x)|²`
    have hdiv : ∀ (η η' : ℝ → ℝ) (x y : Euclid P), (∀ s, HasDerivAt η (η' s) s) →
        Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier y) = m + 1 →
        tangentialDivergence (m + 1) R.carrier (fun z => η (‖z - x‖ ^ 2) • (z - x)) y =
          ((m : ℝ) + 1) * η (‖y - x‖ ^ 2) + 2 * η' (‖y - x‖ ^ 2) *
            ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 := by
      intro η η' x y hη hy
      set T := approxTangentPlane (m + 1) R.carrier y
      have hsub : HasFDerivAt (fun z : Euclid P => z - x) (ContinuousLinearMap.id ℝ (Euclid P)) y :=
        (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
      have hc : HasFDerivAt (fun z : Euclid P => η (‖z - x‖ ^ 2))
          (η' (‖y - x‖ ^ 2) • (2 • (innerSL ℝ (y - x)).comp (ContinuousLinearMap.id ℝ (Euclid P)))) y :=
        (hη _).comp_hasFDerivAt y hsub.norm_sq
      have htr : LinearMap.trace ℝ (Euclid P) T.starProjection.toLinearMap = (m : ℝ) + 1 := by
        rw [LinearMap.IsProj.trace (p := T) ⟨fun z => T.starProjection_apply_mem z,
          fun z hz => Submodule.starProjection_eq_self_iff.2 hz⟩, hy, Nat.cast_succ]
      have hinner : inner ℝ (y - x) (T.starProjection (y - x)) = ‖T.starProjection (y - x)‖ ^ 2 := by
        have h := T.re_inner_starProjection_eq_normSq (y - x)
        rw [RCLike.re_to_real, real_inner_comm] at h
        exact h
      have hcomp : T.starProjection.toLinearMap ∘ₗ
          (fderiv ℝ (fun z : Euclid P => η (‖z - x‖ ^ 2) • (z - x)) y).toLinearMap =
          η (‖y - x‖ ^ 2) • T.starProjection.toLinearMap +
            (η' (‖y - x‖ ^ 2) • (2 • (innerSL ℝ (y - x)).comp
              (ContinuousLinearMap.id ℝ (Euclid P)))).toLinearMap.smulRight (T.starProjection (y - x)) := by
        rw [show fderiv ℝ (fun z : Euclid P => η (‖z - x‖ ^ 2) • (z - x)) y = _ from
          (hc.smul hsub).fderiv]
        refine LinearMap.ext fun w => ?_
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, add_apply,
          smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
          map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply]
      rw [tangentialDivergence, hcomp, map_add, map_smul, LinearMap.trace_smulRight, htr]
      simp only [ContinuousLinearMap.coe_coe, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, innerSL_apply_apply, hinner, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat]
      ring
    -- the first-variation hypothesis as an identity of `μ`-integrals
    have hfvμ : ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
        ∫ y, tangentialDivergence (m + 1) R.carrier X y ∂μ = -∫ y, inner ℝ (X y) (H y) ∂μ := by
      intro X h1 h2 h3
      have hden : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
        funext x
        simp
      have hmeas : Measurable fun x => (R.mult x : NNReal) := measurable_from_nat.comp R.measurable_mult
      rw [← hfv X h1 h2 h3, hμ, IMRep.measure, hden, integral_withDensity_eq_integral_smul hmeas,
        IMRep.firstVariation]
      congr 1
    -- localization
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    have hR₀ : 0 < δ / 5 := by positivity
    have hK₀U : closedBall x₀ (4 * (δ / 5)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hδU
    have hK₀fin : μ (closedBall x₀ (4 * (δ / 5))) ≠ ∞ := hfin _ (isCompact_closedBall _ _) hK₀U
    obtain ⟨Λ₀, hΛ₀⟩ := hHb _ (isCompact_closedBall _ _) hK₀U
    refine ⟨δ / 5, hR₀, 2 * max Λ₀ 0, hK₀U, fun x hx => ?_⟩
    set R₀ := δ / 5 with hR₀def
    set K₀ := closedBall x₀ (4 * R₀) with hK₀def
    set Λ := 2 * max Λ₀ 0 with hΛdef
    have hxx₀ : ‖x - x₀‖ < R₀ := by rwa [mem_ball, dist_eq_norm] at hx
    have hfar : ∀ y, y ∉ K₀ → 3 * R₀ < ‖y - x‖ := by
      intro y hy
      rw [hK₀def, mem_closedBall, dist_eq_norm, not_le] at hy
      linarith [norm_sub_le_norm_sub_add_norm_sub y x x₀]
    have hnear : ∀ y, ‖y - x‖ < 3 * R₀ → y ∈ K₀ := by
      intro y hy
      rw [hK₀def, mem_closedBall, dist_eq_norm]
      linarith [norm_sub_le_norm_sub_add_norm_sub y x x₀]
    have hout : ∀ a t, a ≤ 2 → 0 < t → t < R₀ → ∀ y, y ∉ K₀ → a < ‖y - x‖ ^ 2 / t ^ 2 := by
      intro a t ha ht htR y hy
      rw [lt_div_iff₀ (pow_pos ht 2)]
      have h1 := pow_lt_pow_left₀ (hfar y hy) (by positivity) two_ne_zero
      have h2 := pow_lt_pow_left₀ htR ht.le two_ne_zero
      have h3 := mul_le_mul_of_nonneg_right ha (sq_nonneg t)
      have h4 : (3 * R₀) ^ 2 = 9 * R₀ ^ 2 := by ring
      linarith [sq_nonneg R₀]
    -- bounded functions vanishing off `K₀` are integrable
    have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f μ → ∀ C : ℝ, (∀ y, |f y| ≤ C) →
        (∀ y, y ∉ K₀ → f y = 0) → Integrable f μ := by
      intro f hf C hC h0
      refine Integrable.mono'
        ((integrableOn_const (C := C) hK₀fin).integrable_indicator measurableSet_closedBall)
        hf (ae_of_all _ fun y => ?_)
      by_cases hy : y ∈ K₀
      · rw [indicator_of_mem hy, Real.norm_eq_abs]
        exact hC y
      · rw [indicator_of_notMem hy, h0 y hy, norm_zero]
    have hΦint : ∀ a, 1 < a → a ≤ 2 → ∀ t, 0 < t → t < R₀ →
        Integrable (fun y => Φ a (‖y - x‖ ^ 2 / t ^ 2)) μ := fun a ha1 ha2 t ht htR =>
      hint _ ((hΦc a).comp (by fun_prop)).aestronglyMeasurable 1
        (fun y => by rw [abs_of_nonneg (hΦnn _ _)]; exact hΦle _ _)
        fun y hy => hΦ0 a _ ha1 (hout a t ha2 ht htR y hy).le
    -- monotonicity of `e^{Λt} t⁻ⁿ ∫ Φ_a(|y - x|²/t²) dμ` (Simon 4.3.16–3.17)
    have hGmono : ∀ a, 1 < a → a ≤ 2 → MonotoneOn
        (fun t => Real.exp (Λ * t) * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) / t ^ (m + 1))
          (Ioo 0 R₀) := by
      intro a ha1 ha2
      obtain ⟨C, hC⟩ := hΦbd a ha1
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
      have hstep : ∀ t ∈ Ioo 0 R₀,
          HasDerivAt (fun t => ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ)
            (∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ) t ∧
          ((m : ℝ) + 1) * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) -
              t * (∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ) ≤
            Λ * t * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) := by
        rintro t ⟨ht0, htR⟩
        have hq : Continuous fun y : Euclid P => ‖y - x‖ ^ 2 / t ^ 2 := by fun_prop
        have hI_int := hΦint a ha1 ha2 t ht0 htR
        -- `|Φ'(q) · (-2q/s)| = (2/s) |q Φ'(q)| ≤ 2C/s`
        have hF' : ∀ q s : ℝ, 0 < s → |deriv (Φ a) q * (-2 * q / s)| ≤ 2 / s * C := by
          intro q s hs
          rw [show deriv (Φ a) q * (-2 * q / s) = -(2 / s * (q * deriv (Φ a) q)) by ring, abs_neg,
            abs_mul, abs_of_pos (div_pos two_pos hs)]
          exact mul_le_mul_of_nonneg_left (hC q) (div_pos two_pos hs).le
        have hJ_int : Integrable
            (fun y => deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t)) μ :=
          hint _ (((hΦdc a).comp hq).mul (by fun_prop)).aestronglyMeasurable (2 / t * C)
            (fun y => hF' _ t ht0) fun y hy => by
              rw [hΦd0 a _ ha1 (Or.inr (hout a t ha2 ht0 htR y hy)), zero_mul]
        refine ⟨?_, ?_⟩
        · -- differentiation under the integral sign
          refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo (t / 2) R₀)
            (F := fun t y => Φ a (‖y - x‖ ^ 2 / t ^ 2))
            (F' := fun t y => deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t))
            (bound := K₀.indicator fun _ => 2 / (t / 2) * C) (Ioo_mem_nhds (by linarith) htR)
            (Eventually.of_forall fun t' => ((hΦc a).comp (by fun_prop)).aestronglyMeasurable)
            hI_int hJ_int.aestronglyMeasurable (ae_of_all _ fun y t' ht' => ?_)
            ((integrableOn_const (C := 2 / (t / 2) * C) hK₀fin).integrable_indicator
              measurableSet_closedBall)
            (ae_of_all _ fun y t' ht' => hdt a _ t' (by linarith [ht'.1]))).2
          have ht'0 : 0 < t' := by linarith [ht'.1]
          by_cases hy : y ∈ K₀
          · rw [indicator_of_mem hy, Real.norm_eq_abs]
            exact (hF' _ t' ht'0).trans (mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_left zero_le_two (by linarith) ht'.1.le) hC0)
          · rw [indicator_of_notMem hy, hΦd0 a _ ha1 (Or.inr (hout a t' ha2 ht'0 ht'.2 y hy)),
              zero_mul, norm_zero]
        · -- the first variation of the radial field `X = Φ_a(|y - x|²/t²)(y - x)`
          have hη : ∀ s, HasDerivAt (fun s => Φ a (s / t ^ 2))
              (deriv (Φ a) (s / t ^ 2) * (1 / t ^ 2)) s := fun s =>
            (hΦd a (s / t ^ 2)).comp s ((hasDerivAt_id s).div_const (t ^ 2))
          have hXsupp : ∀ z : Euclid P, 2 * t ≤ ‖z - x‖ →
              Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x) = 0 := by
            intro z hz
            refine (congrArg (· • (z - x)) (hΦ0 a _ ha1 ?_)).trans (zero_smul ℝ _)
            rw [le_div_iff₀ (pow_pos ht0 2)]
            have h1 := pow_le_pow_left₀ (by positivity) hz 2
            have h3 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg t)
            have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
            linarith [sq_nonneg t]
          have hXts : tsupport (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x)) ⊆
              closedBall x (2 * t) := by
            refine closure_minimal (fun z hz => ?_) isClosed_closedBall
            by_contra h
            rw [mem_closedBall, dist_eq_norm, not_le] at h
            exact hz (hXsupp z h.le)
          have hfvX := hfvμ (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x))
            (((hΦC1 a).comp (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const
              _)).smul (contDiff_id.sub contDiff_const))
            ((isCompact_closedBall x (2 * t)).of_isClosed_subset (isClosed_tsupport _) hXts)
            (hXts.trans fun z hz => hK₀U (hnear z (by
              rw [mem_closedBall, dist_eq_norm] at hz
              linarith)))
          have hdivX : ∀ᵐ y ∂μ, tangentialDivergence (m + 1) R.carrier
              (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x)) y =
              ((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
                2 * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) *
                  ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 :=
            hrank.mono fun y hy => hdiv (fun s => Φ a (s / t ^ 2)) _ x y hη hy
          -- pointwise: `q Φ'(q) ≤ Φ'(q) t⁻² |p_y(y - x)|² ≤ 0`
          have hpt : ∀ y : Euclid P,
              (‖y - x‖ ^ 2 / t ^ 2) * deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) ≤
                deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2) *
                  ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 ∧
              deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2) *
                  ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 ≤ 0 := fun y =>
            hr1 _ _ _ _ _ (hΦdnp a _ ha1) (one_div_nonneg.2 (sq_nonneg t)) (sq_nonneg _)
              (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2)
              (div_eq_mul_one_div _ _)
          have hB_int : Integrable (fun y => ((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
              2 * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) *
                ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2) μ := by
            refine hint _ ((((hΦc a).comp hq).aestronglyMeasurable.const_mul _).add
              ((((hΦdc a).comp hq).aestronglyMeasurable.mul_const _).const_mul _ |>.mul
                ((continuous_pow 2).comp_aestronglyMeasurable (hpm x))))
              ((m : ℝ) + 1 + 2 * C) (fun y => ?_) fun y hy => ?_
            · exact hr2 _ _ _ _ _ _ _ (by positivity) (hΦnn _ _) (hΦle _ _) (hC _) (hpt y).1 (hpt y).2
            · rw [hΦ0 a _ ha1 (hout a t ha2 ht0 htR y hy).le,
                hΦd0 a _ ha1 (Or.inr (hout a t ha2 ht0 htR y hy))]
              ring
          have hA_int := (hI_int.const_mul ((m : ℝ) + 1)).add (hJ_int.const_mul (-t))
          have h1 : ((m : ℝ) + 1) * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) -
              t * (∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ) =
              ∫ y, (((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
                -t * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t))) ∂μ := by
            rw [integral_add (hI_int.const_mul _) (hJ_int.const_mul _), integral_const_mul,
              integral_const_mul]
            ring
          have h2 : ∫ y, (((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
                -t * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t))) ∂μ ≤
              ∫ y, tangentialDivergence (m + 1) R.carrier
                (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x)) y ∂μ := by
            rw [integral_congr_ae hdivX]
            refine integral_mono hA_int hB_int fun y => (add_le_add_iff_left _).2 ?_
            rw [hcancel _ _ t ht0.ne', mul_assoc]
            exact mul_le_mul_of_nonneg_left (hpt y).1 zero_le_two
          have h3 : -∫ y, inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y) ∂μ ≤
              Λ * t * ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ := by
            have hbd : ∀ᵐ y ∂μ, |inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y)| ≤
                Λ * t * Φ a (‖y - x‖ ^ 2 / t ^ 2) := by
              filter_upwards [hΛ₀] with y hy
              by_cases hyx : ‖y - x‖ < 2 * t
              · have hH := (hy (hnear y (by linarith))).trans (le_max_left Λ₀ 0)
                calc |inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y)|
                    ≤ ‖Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)‖ * ‖H y‖ := abs_real_inner_le_norm _ _
                  _ = Φ a (‖y - x‖ ^ 2 / t ^ 2) * ‖y - x‖ * ‖H y‖ := by
                    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦnn _ _)]
                  _ ≤ Φ a (‖y - x‖ ^ 2 / t ^ 2) * (2 * t) * max Λ₀ 0 :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hyx.le (hΦnn _ _)) hH (norm_nonneg _)
                      (mul_nonneg (hΦnn _ _) (by linarith))
                  _ = Λ * t * Φ a (‖y - x‖ ^ 2 / t ^ 2) := by rw [hΛdef]; ring
              · rw [hXsupp y (not_lt.1 hyx), inner_zero_left, abs_zero]
                exact mul_nonneg (mul_nonneg (by positivity) ht0.le) (hΦnn _ _)
            calc -∫ y, inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y) ∂μ
                ≤ |∫ y, inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y) ∂μ| := neg_le_abs _
              _ ≤ ∫ y, |inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y)| ∂μ :=
                abs_integral_le_integral_abs
              _ ≤ ∫ y, Λ * t * Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ :=
                integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (hI_int.const_mul _) hbd
              _ = Λ * t * ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ := integral_const_mul _ _
          linarith
      have hG : ∀ t ∈ Ioo 0 R₀, ∃ d, 0 ≤ d ∧ HasDerivAt (fun t => Real.exp (Λ * t) *
          (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) / t ^ (m + 1)) d t := by
        intro t ht
        obtain ⟨hI, hineq⟩ := hstep t ht
        set I := ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ
        set J := ∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ
        have he : HasDerivAt (fun t => Real.exp (Λ * t)) (Real.exp (Λ * t) * Λ) t := by
          simpa using ((hasDerivAt_id t).const_mul Λ).exp
        refine ⟨Real.exp (Λ * t) * t ^ m * (Λ * t * I - (((m : ℝ) + 1) * I - t * J)) /
            (t ^ (m + 1)) ^ 2, div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
              (pow_nonneg ht.1.le _)) (by linarith)) (sq_nonneg _),
          ((he.mul hI).div (hasDerivAt_pow (m + 1) t) (pow_ne_zero _ ht.1.ne')).congr_deriv ?_⟩
        have alg : ∀ e I J : ℝ, (e * Λ * I + e * J) * t ^ (m + 1) -
            e * I * (((m + 1 : ℕ) : ℝ) * t ^ (m + 1 - 1)) =
            e * t ^ m * (Λ * t * I - (((m : ℝ) + 1) * I - t * J)) := by
          intro e I J
          rw [Nat.add_sub_cancel]
          push_cast
          ring
        simp only [Pi.mul_apply]
        rw [alg]
      refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 R₀)
        (fun t ht => (hG t ht).choose_spec.2.continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Ioo]
        exact fun t ht => (hG t ht).choose_spec.2.differentiableAt.differentiableWithinAt
      · rw [interior_Ioo]
        exact fun t ht => (hG t ht).choose_spec.2.deriv ▸ (hG t ht).choose_spec.1
    -- let `ρ ↑ ρ₁` with `a = (ρ₁/ρ)²`: `e^{Λt} t⁻ⁿ μ(B_t(x))` is nondecreasing (Simon 4.3.17)
    intro σ hσ ρ₁ hρ₁ hσρ₁
    obtain ⟨hσ0, hσR⟩ := hσ
    obtain ⟨hρ₁0, hρ₁R⟩ := hρ₁
    have hind : ∀ r, r < R₀ → Integrable ((ball x r).indicator (1 : Euclid P → ℝ)) μ := fun r hr =>
      (integrableOn_const (C := (1 : ℝ)) (ne_top_of_le_ne_top hK₀fin (measure_mono fun z hz =>
        hnear z (by rw [mem_ball, dist_eq_norm] at hz; linarith)))).integrable_indicator
        measurableSet_ball
    have hkey : ∀ ρ ∈ Ioo (max σ (3 * ρ₁ / 4)) ρ₁,
        Real.exp (Λ * σ) * (μ (ball x σ)).toReal / σ ^ (m + 1) ≤
          Real.exp (Λ * ρ) * (μ (ball x ρ₁)).toReal / ρ ^ (m + 1) := by
      rintro ρ ⟨hρ1, hρ2⟩
      have hσρ : σ < ρ := (le_max_left _ _).trans_lt hρ1
      have hρ0 : 0 < ρ := hσ0.trans hσρ
      have ha1 : 1 < (ρ₁ / ρ) ^ 2 := one_lt_pow₀ ((one_lt_div hρ0).2 hρ2) two_ne_zero
      have ha2 : (ρ₁ / ρ) ^ 2 ≤ 2 := by
        have h43 : ρ₁ / ρ ≤ 4 / 3 := by
          rw [div_le_iff₀ hρ0]
          linarith [(le_max_right σ (3 * ρ₁ / 4)).trans_lt hρ1]
        calc (ρ₁ / ρ) ^ 2 ≤ (4 / 3) ^ 2 := pow_le_pow_left₀ (by positivity) h43 2
          _ ≤ 2 := by norm_num
      have hlow : (μ (ball x σ)).toReal ≤ ∫ y, Φ ((ρ₁ / ρ) ^ 2) (‖y - x‖ ^ 2 / σ ^ 2) ∂μ := by
        refine (integral_indicator_one measurableSet_ball).symm.trans_le
          (integral_mono (hind σ hσR) (hΦint _ ha1 ha2 σ hσ0 hσR) fun y => ?_)
        by_cases hy : y ∈ ball x σ
        · rw [indicator_of_mem hy, Pi.one_apply, hΦ1 _ _ ha1]
          rw [mem_ball, dist_eq_norm] at hy
          exact (div_le_one (pow_pos hσ0 2)).2 (pow_le_pow_left₀ (norm_nonneg _) hy.le 2)
        · rw [indicator_of_notMem hy]
          exact hΦnn _ _
      have hup : ∫ y, Φ ((ρ₁ / ρ) ^ 2) (‖y - x‖ ^ 2 / ρ ^ 2) ∂μ ≤ (μ (ball x ρ₁)).toReal := by
        refine (integral_mono (hΦint _ ha1 ha2 ρ hρ0 (hρ2.trans hρ₁R)) (hind ρ₁ hρ₁R)
          fun y => ?_).trans_eq (integral_indicator_one measurableSet_ball)
        by_cases hy : y ∈ ball x ρ₁
        · rw [indicator_of_mem hy, Pi.one_apply]
          exact hΦle _ _
        · rw [indicator_of_notMem hy, hΦ0 _ _ ha1]
          rw [mem_ball, dist_eq_norm, not_lt] at hy
          rw [div_pow]
          exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ₁0.le hy 2) (sq_nonneg ρ)
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le)
        (pow_nonneg hσ0.le _)).trans ((hGmono _ ha1 ha2 ⟨hσ0, hσR⟩ ⟨hρ0, hρ2.trans hρ₁R⟩ hσρ.le).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)
            (pow_nonneg hρ0.le _)))
    have hlim : Tendsto (fun ρ => Real.exp (Λ * ρ) * (μ (ball x ρ₁)).toReal / ρ ^ (m + 1)) (𝓝[<] ρ₁)
        (𝓝 (Real.exp (Λ * ρ₁) * (μ (ball x ρ₁)).toReal / ρ₁ ^ (m + 1))) :=
      (((by fun_prop : Continuous fun ρ => Real.exp (Λ * ρ) * (μ (ball x ρ₁)).toReal).continuousAt).div
        (continuous_pow (m + 1)).continuousAt (pow_ne_zero _ hρ₁0.ne')).tendsto.mono_left
        nhdsWithin_le_nhds
    rcases hσρ₁.lt_or_eq with hlt | heq
    · exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT (max_lt hlt (by linarith)))
        fun ρ hρ => hkey ρ hρ)
    · rw [heq]
  -- `M_W(T) = μ(W)` for open `W ⊆ U`
  have hmass : ∀ W, IsOpen W → W ⊆ U → T.massOn W = μ W := fun W hW hWU =>
    Submission.dtc_mass_eq_measure P (m + 1) U W T R hU hW hWU hrep
  -- Steps 3–5: existence of the density, `HasMassDensity`, upper semicontinuity (Simon 4.3.11)
  have hω0 : unitBallVolume (m + 1) ≠ 0 := (measure_ball_pos volume (0 : Euclid (m + 1)) one_pos).ne'
  have hωtop : unitBallVolume (m + 1) ≠ ∞ := measure_ball_lt_top.ne
  -- the density quotient converges to `L/ωₙ`, `L = inf_{0<t<R₀} e^{Λt} t⁻ⁿ μ(B_t(x))`
  have hlim : ∀ (x : Euclid P) (Λ R₀ : ℝ), 0 < R₀ → (∀ t ∈ Ioo 0 R₀, μ (ball x t) ≠ ∞) →
      MonotoneOn (fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal / t ^ (m + 1)) (Ioo 0 R₀) →
      Tendsto (fun ρ => μ (ball x ρ) / (unitBallVolume (m + 1) * ENNReal.ofReal (ρ ^ (m + 1))))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (sInf ((fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal /
          t ^ (m + 1)) '' Ioo 0 R₀)) / unitBallVolume (m + 1))) := by
    intro x Λ R₀ hR₀ hfinx hmon
    have h1 := hmon.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hR₀) ⟨0, by
      rintro _ ⟨t, ht, rfl⟩
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (pow_nonneg ht.1.le _)⟩
    have h2 := ((((by fun_prop : Continuous fun t : ℝ => Real.exp (-(Λ * t))).tendsto 0).mono_left
      nhdsWithin_le_nhds).mul h1)
    rw [mul_zero, neg_zero, Real.exp_zero, one_mul] at h2
    refine (ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal h2) (Or.inr hω0)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR₀] with t ht
    rw [mul_div_assoc', ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul,
      ENNReal.ofReal_div_of_pos (pow_pos ht.1 _), ENNReal.ofReal_toReal (hfinx t ht),
      div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop)]
    ring
  -- the chosen density
  refine ⟨fun x => (limUnder (𝓝[>] (0 : ℝ)) fun ρ =>
    μ (ball x ρ) / (unitBallVolume (m + 1) * ENNReal.ofReal (ρ ^ (m + 1)))).toReal, ?_, ?_⟩
  · intro x hx
    dsimp only
    obtain ⟨R₀, hR₀, Λ, hK, hmon⟩ := hmono x hx
    have hfinx : ∀ t ∈ Ioo 0 R₀, μ (ball x t) ≠ ∞ := fun t ht =>
      ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) hK)
        (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [ht.2]))))
    have hl := hlim x Λ R₀ hR₀ hfinx (hmon x (mem_ball_self hR₀))
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    rw [hl.limUnder_eq, ENNReal.ofReal_toReal (ENNReal.div_ne_top ENNReal.ofReal_ne_top hω0)]
    refine hl.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR₀] with ρ hρ
    rw [hmass _ isOpen_ball ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [hρ.2]))).trans hK)]
  · intro x hx c hc
    obtain ⟨R₀, hR₀, Λ, hK, hmon⟩ := hmono x hx
    have hω : 0 < (unitBallVolume (m + 1)).toReal := ENNReal.toReal_pos hω0 hωtop
    -- `Θ(x') = L(x')/ωₙ` near `x`
    have hΘ : ∀ x' ∈ ball x R₀, (limUnder (𝓝[>] (0 : ℝ)) fun ρ =>
        μ (ball x' ρ) / (unitBallVolume (m + 1) * ENNReal.ofReal (ρ ^ (m + 1)))).toReal =
        sInf ((fun t => Real.exp (Λ * t) * (μ (ball x' t)).toReal / t ^ (m + 1)) '' Ioo 0 R₀) /
          (unitBallVolume (m + 1)).toReal := by
      intro x' hx'
      have hfinx : ∀ t ∈ Ioo 0 R₀, μ (ball x' t) ≠ ∞ := fun t ht =>
        ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) hK)
          (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall' (by
            rw [mem_ball] at hx'
            linarith [ht.2]))))
      rw [(hlim x' Λ R₀ hR₀ hfinx (hmon x' hx')).limUnder_eq, ENNReal.toReal_div,
        ENNReal.toReal_ofReal (Real.sInf_nonneg (by
          rintro _ ⟨t, ht, rfl⟩
          exact div_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
            (pow_nonneg ht.1.le _)))]
    have hc' : sInf ((fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal / t ^ (m + 1)) '' Ioo 0 R₀) <
        c * (unitBallVolume (m + 1)).toReal := by
      rw [← div_lt_iff₀ hω, ← hΘ x (mem_ball_self hR₀)]
      exact hc
    obtain ⟨_, ⟨t₁, ht₁, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((nonempty_Ioo.2 hR₀).image _) hc'
    -- shrink the radius slightly: `e^{Λt} t⁻ⁿ μ(B_{t₁}(x)) < cωₙ` for some `t < t₁`
    have hcont : ContinuousAt (fun t => Real.exp (Λ * t) * (μ (ball x t₁)).toReal / t ^ (m + 1)) t₁ :=
      ((by fun_prop : Continuous fun t => Real.exp (Λ * t) * (μ (ball x t₁)).toReal).continuousAt).div
        (continuous_pow (m + 1)).continuousAt (pow_ne_zero _ ht₁.1.ne')
    obtain ⟨t₂, ht₂lt, ht₂⟩ := ((hcont.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds |>.and
      (Ioo_mem_nhdsLT ht₁.1)).exists (f := 𝓝[<] t₁)
    have hfin₁ : μ (ball x t₁) ≠ ∞ := ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) hK)
      (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [ht₁.2]))))
    refine eventually_nhdsWithin_of_eventually_nhds (Filter.mem_of_superset
      (ball_mem_nhds x (lt_min hR₀ (sub_pos.2 ht₂.2))) fun x' hx' => ?_)
    have hx'1 : x' ∈ ball x R₀ := ball_subset_ball (min_le_left _ _) hx'
    simp only [Set.mem_ofPred_eq]
    rw [hΘ x' hx'1, div_lt_iff₀ hω]
    have hbdd : BddBelow ((fun t => Real.exp (Λ * t) * (μ (ball x' t)).toReal / t ^ (m + 1)) ''
        Ioo 0 R₀) := ⟨0, by
      rintro _ ⟨t, ht, rfl⟩
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (pow_nonneg ht.1.le _)⟩
    refine (csInf_le hbdd ⟨t₂, ⟨ht₂.1, ht₂.2.trans ht₁.2⟩, rfl⟩).trans_lt (lt_of_le_of_lt ?_ ht₂lt)
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ((ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top hfin₁ (measure_mono ?_)) hfin₁).2 (measure_mono ?_)) (Real.exp_pos _).le)
        (pow_nonneg ht₂.1.le _) <;>
      · intro z hz
        rw [mem_ball] at hz hx' ⊢
        have := dist_triangle z x' x
        have := min_le_right R₀ (t₁ - t₂)
        linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
