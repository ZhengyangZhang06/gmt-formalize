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
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion

/-- **Simon Ch. 6, 4.9 with `f = |x|`** (localisation at a good radius in the proof of 7.2): if
`μ(B_r) < ∞` for every `r`, the left Dini derivative `D(t) = liminf_{h ↓ 0} h⁻¹ μ{t - h < |x| < t}`
of `t ↦ μ(B_t)` is Borel.  For `h > 0`, `μ{t - h < |x| < t} = μ(B_t) - μ(B̄_{t-h})` is a
difference of monotone functions of `t`.  Along the basis `(0, ε)` of `𝓝[>] 0`,
`D(t) = ⨆ₖ ⨅_{0 < h < 1/(k+1)} h⁻¹ μ{t - h < |x| < t}`; the annulus measure increases with `h`
and `x ↦ x⁻¹ μ{t - h < |x| < t}` is continuous at `h`, so each infimum may run over rational
`h`, and `D` is a countable supremum of countable infima of measurable functions. -/
theorem Submission.dtc_bc_lc_fd_lz_dini_measurable : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ r : ℝ, μ (ball (0 : Euclid P) r) < ∞) → Measurable (fun t : ℝ => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x : Euclid P | t - h < ‖x‖ ∧ ‖x‖ < t}) (𝓝[>] 0)) := by
  intro P μ hμ
  -- `A(t, h) = μ{t - h < |x| < t}` and `f(t, h) = h⁻¹ A(t, h)`
  let A : ℝ → ℝ → ℝ≥0∞ := fun t h => μ {x : Euclid P | t - h < ‖x‖ ∧ ‖x‖ < t}
  let f : ℝ → ℝ → ℝ≥0∞ := fun t h => ENNReal.ofReal h⁻¹ * A t h
  -- Step 4: `A(t, ·)` is monotone, and `A(t, h) ≤ μ(B_t) < ∞`
  have hAmono : ∀ t h' h : ℝ, h' ≤ h → A t h' ≤ A t h := fun t h' h hle =>
    measure_mono fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hAfin : ∀ t h : ℝ, A t h ≠ ∞ := fun t h =>
    ne_top_of_le_ne_top (hμ t).ne (measure_mono fun x hx => mem_ball_zero_iff.2 hx.2)
  -- Steps 1–3: for `h > 0`, `A(t, h) = μ(B_t) - μ(B̄_{t-h})`, a difference of monotone
  -- functions of `t`
  have hfm : ∀ h : ℝ, 0 < h → Measurable fun t => f t h := by
    intro h hh
    have hF : Monotone fun s : ℝ => μ (ball (0 : Euclid P) s) :=
      fun a b hab => measure_mono (ball_subset_ball hab)
    have hG : Monotone fun s : ℝ => μ (closedBall (0 : Euclid P) s) :=
      fun a b hab => measure_mono (closedBall_subset_closedBall hab)
    have hAeq : ∀ t, A t h = μ (ball (0 : Euclid P) t) - μ (closedBall (0 : Euclid P) (t - h)) := by
      intro t
      have hsub : closedBall (0 : Euclid P) (t - h) ⊆ ball 0 t :=
        closedBall_subset_ball (by linarith)
      have hset : {x : Euclid P | t - h < ‖x‖ ∧ ‖x‖ < t} = ball 0 t \ closedBall 0 (t - h) :=
        Set.ext fun x => ⟨fun hx => ⟨mem_ball_zero_iff.2 hx.2,
            fun hx' => not_lt.2 (mem_closedBall_zero_iff.1 hx') hx.1⟩,
          fun hx => ⟨not_le.1 fun hx' => hx.2 (mem_closedBall_zero_iff.2 hx'),
            mem_ball_zero_iff.1 hx.1⟩⟩
      show μ _ = _
      rw [hset, measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet
        (ne_top_of_le_ne_top (hμ t).ne (measure_mono hsub))]
    have : (fun t => f t h) = fun t => ENNReal.ofReal h⁻¹ *
        (μ (ball (0 : Euclid P) t) - μ (closedBall (0 : Euclid P) (t - h))) := by
      funext t
      show ENNReal.ofReal h⁻¹ * A t h = _
      rw [hAeq]
    rw [this]
    exact (hF.measurable.sub (hG.measurable.comp (measurable_id.sub_const h))).const_mul _
  -- Steps 5–6: `D(t) = ⨆ₖ ⨅_{q ∈ ℚ, 0 < q < 1/(k+1)} f(t, q)`
  have key : ∀ t, liminf (fun h => f t h) (𝓝[>] 0) =
      ⨆ k : ℕ, ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / (k + 1)}, f t ((q : ℚ) : ℝ) := by
    intro t
    rw [(nhdsGT_basis (0 : ℝ)).liminf_eq_iSup_iInf]
    refine le_antisymm (iSup₂_le fun ε hε => ?_) (iSup_le fun k => ?_)
    · -- `I_ε(t) ≤ J_k(t)` once `1/(k+1) < ε`
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine le_iSup_of_le k (le_iInf fun q => ?_)
      exact iInf₂_le ((q : ℚ) : ℝ) ⟨by exact_mod_cast q.2.1, q.2.2.trans hk⟩
    · -- `J_k(t) ≤ I_{1/(k+1)}(t)`: approximate `h` from below by rationals
      refine le_iSup₂_of_le (1 / ((k : ℝ) + 1)) (by positivity) (le_iInf₂ fun h hh => ?_)
      refine le_of_forall_gt fun c hc => ?_
      -- `x ↦ x⁻¹ A(t, h)` is continuous at `h`
      have htend : Tendsto (fun x : ℝ => ENNReal.ofReal x⁻¹ * A t h) (𝓝[<] h) (𝓝 (f t h)) :=
        (ENNReal.Tendsto.mul_const ((ENNReal.continuous_ofReal.tendsto _).comp
          (tendsto_inv₀ hh.1.ne')) (Or.inr (hAfin t h))).mono_left nhdsWithin_le_nhds
      obtain ⟨l, hl, hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (htend.eventually_lt_const hc)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hl hh.1)
      have hq0 : (0 : ℝ) < q := (le_max_right l 0).trans_lt hq1
      calc ⨅ q : {q : ℚ // 0 < q ∧ (q : ℝ) < 1 / (k + 1)}, f t ((q : ℚ) : ℝ)
          ≤ f t q := iInf_le_of_le ⟨q, by exact_mod_cast hq0, hq2.trans hh.2⟩ le_rfl
        _ ≤ ENNReal.ofReal (q : ℝ)⁻¹ * A t h := mul_le_mul_right (hAmono t q h hq2.le) _
        _ < c := hlsub ⟨(le_max_left l 0).trans_lt hq1, hq2⟩
  -- Step 7: a countable supremum of countable infima of measurable functions
  show Measurable fun t => liminf (fun h => f t h) (𝓝[>] 0)
  rw [show (fun t => liminf (fun h => f t h) (𝓝[>] 0)) = _ from funext key]
  exact Measurable.iSup fun k => Measurable.iInf fun q => hfm _ (by exact_mod_cast q.2.1)
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Simon Ch. 6, remark before 4.10** (integrated lower left Dini derivative).  For monotone
`F : ℝ → ℝ`, the lower integral over `(a, b)` of `D(t) = liminf_{h → 0+} (F(t) - F(t - h)) / h`
is at most `F(b) - F(a)`.  `F` is differentiable a.e. (Lebesgue), and at a point of
differentiability the left difference quotients tend to `F'(t)`, so `D = F'` a.e.  Changing the
integrand on a null set needs no measurability of `D`, and `∫_(a,b) F' ≤ F(b) - F(a)` is
`cmcs_smi_lintegral_ofReal_deriv_le`. -/
theorem Submission.cmcs_smi_lintegral_left_dini_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  -- `D = ofReal ∘ deriv F` at every point of differentiability, hence a.e.
  have hae : ∀ᵐ t, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) =
      ENNReal.ofReal (deriv F t) := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    have hlim : Tendsto (fun h : ℝ => (F t - F (t - h)) / h) (𝓝[>] 0) (𝓝 (deriv F t)) := by
      refine (ht.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]
      ring
    exact (ENNReal.tendsto_ofReal hlim).liminf_eq
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) := lintegral_congr_ae (ae_restrict_of_ae hae)
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_ofReal_deriv_le F a b hF

/-- **Simon Ch. 6, the remark deriving 4.10 from 4.9, for a measure on `ℝ`.**  For any measure
`ν` on `ℝ`, `∫⁻_{(a,b)} liminf_{h → 0+} h⁻¹ ν((t − h, t)) dt ≤ ν((a, b))` (Simon applies this to
`ν((s, t)) = M_W(T ⌞ {s < f < t})`).  When `ν((a, b)) < ∞`, `F(s) = ν((a, min s b))` is finite
and monotone, with `F a = 0` and `F b = ν((a, b))`.  For `0 < h < t − a`, additivity on
`(a, t − h) ∪ (t − h, t) ⊆ (a, t)` gives `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`, so the left
density is at most the lower left Dini derivative of `F`, whose integral
`cmcs_smi_lintegral_left_dini_le` bounds by `F b − F a`. -/
theorem Submission.cmcs_smi_lintegral_left_density_le : ∀ (ν : Measure ℝ) (a b : ℝ), ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤ ν (Ioo a b) := by
  intro ν a b
  by_cases hN : ν (Ioo a b) = ∞
  · rw [hN]
    exact le_top
  -- the distribution function `F(s) = ν((a, min s b))` of `ν` on `(a, b)`
  set F : ℝ → ℝ := fun s => (ν (Ioo a (min s b))).toReal with hFdef
  have hfin : ∀ s, ν (Ioo a (min s b)) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hN (measure_mono (Ioo_subset_Ioo_right (min_le_right s b)))
  have hFmono : Monotone F := fun s s' hss' =>
    ENNReal.toReal_mono (hfin s') (measure_mono (Ioo_subset_Ioo_right (min_le_min_right b hss')))
  have hofF : ∀ s, ENNReal.ofReal (F s) = ν (Ioo a (min s b)) := fun s =>
    ENNReal.ofReal_toReal (hfin s)
  have hFa : F a = 0 := by
    simp only [hFdef]
    rw [Ioo_eq_empty (not_lt.2 (min_le_left a b)), measure_empty, ENNReal.toReal_zero]
  have hFb : F b = (ν (Ioo a b)).toReal := by
    simp only [hFdef, min_self]
  -- the strip estimate: for `0 < h < t − a`, `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`
  have hstrip : ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a),
      ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t) ≤ ENNReal.ofReal ((F t - F (t - h)) / h) := by
    intro t ht h hh
    have hmt : min t b = t := min_eq_left ht.2.le
    have hmth : min (t - h) b = t - h := min_eq_left (by linarith [hh.1, ht.2])
    have hunion : ν (Ioo a (t - h)) + ν (Ioo (t - h) t) ≤ ν (Ioo a t) := by
      rw [← measure_union _ measurableSet_Ioo]
      · refine measure_mono (union_subset ?_ ?_)
        · exact Ioo_subset_Ioo_right (by linarith [hh.1])
        · exact Ioo_subset_Ioo_left (by linarith [hh.2])
      · rw [Set.disjoint_left]
        intro x hx1 hx2
        linarith [hx1.2, hx2.1]
    have hle : ν (Ioo (t - h) t) ≤ ENNReal.ofReal (F t - F (t - h)) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hofF, hofF, hmt, hmth]
      refine ENNReal.le_sub_of_add_le_left ?_ hunion
      rw [← hmth]
      exact hfin (t - h)
    calc ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)
        ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)) := mul_le_mul_right hle _
      _ = ENNReal.ofReal ((F t - F (t - h)) / h) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hh.1.le), div_eq_inv_mul]
  -- `(0, t − a) ∈ 𝓝[>] 0`, so the strip estimate compares the two liminfs on `(a, b)`
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤
        liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) := by
    intro t ht
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact hstrip t ht h hh
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_left_dini_le F a b hFmono
    _ = ν (Ioo a b) := by rw [hFb, hFa, sub_zero, ENNReal.ofReal_toReal hN]

/-- **Simon Ch. 6, 4.10** (integrated slice-mass bound, with `μ(W ∩ {a < f < s})` in place of
`M_W(T⌞{a < f < s})`): if `m(t) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})` for every
`t ∈ (a, b)`, then `∫⁻_{(a,b)} m ≤ L · μ(W ∩ {a < f < b})`.  The push-forward `ν = f_#(μ⌞W)` has
`ν((s, t)) = μ(W ∩ {s < f < t})`, so the hypothesis reads
`m(t) ≤ L · liminf_{h↓0} h⁻¹ ν((t − h, t))`; pull `L` out of the lower integral (`L ≠ ∞`) and bound
the integrated lower left density of `ν` by `ν((a, b))` (`cmcs_smi_lintegral_left_density_le`).
No measurability of `m` is needed. -/
theorem Submission.cmcs_slice_mass_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (W : Set (Euclid P)) (L : NNReal) (m : ℝ → ℝ≥0∞) (a b : ℝ), Measurable f → MeasurableSet W → (∀ t ∈ Ioo a b, m t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∫⁻ t in Ioo a b, m t ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by
  intro P μ f W L m a b hf _hW hm
  -- `ν = f_#(μ⌞W)`, so `ν((s, t)) = μ(f⁻¹(s, t) ∩ W) = μ(W ∩ {s < f < t})`
  set ν : Measure ℝ := (μ.restrict W).map f with hν
  have hνI : ∀ s t : ℝ, ν (Ioo s t) = μ (W ∩ {x | s < f x ∧ f x < t}) := by
    intro s t
    rw [hν, Measure.map_apply hf measurableSet_Ioo,
      Measure.restrict_apply (hf measurableSet_Ioo), Set.inter_comm]
    rfl
  calc ∫⁻ t in Ioo a b, m t
      ≤ ∫⁻ t in Ioo a b, (L : ℝ≥0∞) *
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => by simpa only [hνI] using hm t ht
    _ = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b,
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (L : ℝ≥0∞) * ν (Ioo a b) :=
        mul_le_mul_right (Submission.cmcs_smi_lintegral_left_density_le ν a b) _
    _ = (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by rw [hνI]

/-- **A good slicing radius** (Simon Ch. 6, proof of 7.2, via 4.10 and the argument of Ch. 2,
6.7(2)).  Let `μ_j(B_r) < ∞` and `μ_j(B_{r₀+1}) ≤ Λ₀`, and put
`D_j(t) = liminf_{h↓0} h⁻¹ μ_j({t − h < |x| < t})`.  Each `D_j` is measurable
(`dtc_bc_lc_fd_lz_dini_measurable`), and 4.10 (`cmcs_slice_mass_integral` with `f = |·|`,
`W = ℝᴾ`, `L = 1`) gives `∫_{(r₀, r₀+1)} D_j ≤ μ_j(B_{r₀+1}) ≤ Λ₀`.  By Fatou,
`G = liminf_j D_j` has `∫_{(r₀, r₀+1)} G ≤ Λ₀ < ∞`, so `G(t₀) < ∞` for some `t₀ ∈ (r₀, r₀ + 1)`.
With `C = G(t₀) + 1`, `D_j(t₀) < C` for infinitely many `j`; extract these as `φ`. -/
theorem Submission.dtc_bc_lc_fd_lz_good_radius : ∀ (P : ℕ) (μ : ℕ → Measure (Euclid P)) (r₀ : ℝ) (Λ₀ : NNReal), (∀ (j : ℕ) (r : ℝ), μ j (ball (0 : Euclid P) r) < ∞) → (∀ j, μ j (ball (0 : Euclid P) (r₀ + 1)) ≤ (Λ₀ : ℝ≥0∞)) → ∃ t₀ ∈ Ioo r₀ (r₀ + 1), ∃ (φ : ℕ → ℕ) (C : NNReal), StrictMono φ ∧ ∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (φ j) {x : Euclid P | t₀ - h < ‖x‖ ∧ ‖x‖ < t₀}) (𝓝[>] 0) ≤ (C : ℝ≥0∞) := by
  intro P μ r₀ Λ₀ hfin hΛ
  -- `D j t = liminf_{h → 0+} h⁻¹ μ_j({t − h < |x| < t})`, measurable in `t`
  set D : ℕ → ℝ → ℝ≥0∞ := fun j t =>
    liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ j {x : Euclid P | t - h < ‖x‖ ∧ ‖x‖ < t})
      (𝓝[>] 0)
  have hDm : ∀ j, Measurable (D j) := fun j =>
    Submission.dtc_bc_lc_fd_lz_dini_measurable P (μ j) (hfin j)
  -- 4.10 with `f = |·|`, `W = ℝᴾ`, `L = 1`: `∫_{(r₀, r₀+1)} D j ≤ μ_j(B_{r₀+1}) ≤ Λ₀`
  have hint : ∀ j, ∫⁻ t in Ioo r₀ (r₀ + 1), D j t ≤ Λ₀ := by
    intro j
    calc ∫⁻ t in Ioo r₀ (r₀ + 1), D j t
        ≤ ((1 : NNReal) : ℝ≥0∞) * μ j (univ ∩ {x | r₀ < ‖x‖ ∧ ‖x‖ < r₀ + 1}) :=
          Submission.cmcs_slice_mass_integral P (μ j) (fun x => ‖x‖) univ 1 (D j) r₀ (r₀ + 1)
            measurable_norm MeasurableSet.univ fun t _ => by
              rw [ENNReal.coe_one, one_mul]
              simp only [univ_inter]
              exact le_rfl
      _ ≤ μ j (ball (0 : Euclid P) (r₀ + 1)) := by
          rw [ENNReal.coe_one, one_mul, univ_inter]
          exact measure_mono fun x hx => mem_ball_zero_iff.2 hx.2
      _ ≤ Λ₀ := hΛ j
  -- Fatou: `G = liminf_j D j` has `∫_{(r₀, r₀+1)} G ≤ liminf_j ∫_{(r₀, r₀+1)} D j ≤ Λ₀`
  set G : ℝ → ℝ≥0∞ := fun t => liminf (fun j => D j t) atTop
  have hGm : Measurable G := Measurable.liminf hDm
  have hGint : ∫⁻ t in Ioo r₀ (r₀ + 1), G t ≤ Λ₀ :=
    (lintegral_liminf_le hDm).trans (liminf_le_of_frequently_le' (Frequently.of_forall hint))
  -- `G < ∞` a.e. on `(r₀, r₀ + 1)`, which is not null, so `G(t₀) < ∞` for some `t₀` there
  obtain ⟨t₀, ht₀, hGt₀⟩ : ∃ t₀ ∈ Ioo r₀ (r₀ + 1), G t₀ < ∞ := by
    have hae := ae_lt_top hGm (ne_top_of_le_ne_top ENNReal.coe_ne_top hGint)
    rw [ae_restrict_iff' measurableSet_Ioo] at hae
    by_contra! hcon
    have hnull : volume (Ioo r₀ (r₀ + 1)) = 0 := by
      refine measure_mono_null (fun t ht => ?_) (ae_iff.1 hae)
      intro hlt
      exact not_lt.2 (hcon t ht) (hlt ht)
    simp [Real.volume_Ioo] at hnull
  -- `C = G(t₀) + 1`: `D j t₀ < C` for infinitely many `j`, which we extract
  have hGC : G t₀ < ((G t₀).toNNReal + 1 : NNReal) :=
    calc G t₀ = ((G t₀).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hGt₀.ne).symm
      _ < ((G t₀).toNNReal + 1 : NNReal) := ENNReal.coe_lt_coe.2 (lt_add_one _)
  obtain ⟨φ, hφ, hφC⟩ :=
    extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hGC)
  exact ⟨t₀, ht₀, φ, (G t₀).toNNReal + 1, hφ, fun j => (hφC j).le⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
