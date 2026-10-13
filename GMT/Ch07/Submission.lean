import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

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

/-- **Rescaled Gauss–Green identity** (Simon Ch. 3, 4.3 (8), for a general field and centre).
Let `F ⊆ ℝ^{m+1}` be Borel and suppose `∫_F div φ = −∫ ⟨φ, ν⟩ dμ` for every `C¹` compactly
supported `φ` with `tsupport φ ⊆ D`.  If `r > 0` and `B̄_{rR}(y) ⊆ D`, then for every `C¹`
compactly supported `g` with `tsupport g ⊆ B_R(0)` the blow-up `F_{y,r} = {w : y + rw ∈ F}`
satisfies `∫_{F_{y,r}} div g = −(r^m)⁻¹ ∫ ⟨g(r⁻¹(z − y)), ν(z)⟩ dμ(z)`.  Apply the hypothesis to
`φ = g ∘ S`, `S z = r⁻¹(z − y)`: `div φ = r⁻¹ (div g) ∘ S` by the chain rule,
`tsupport φ ⊆ S⁻¹(tsupport g) ⊆ B̄_{rR}(y)`, and the substitution `z = y + rw` (Jacobian
`r^{m+1}`) gives `∫_F div φ = r^m ∫_{F_{y,r}} div g`. -/
theorem Submission.codim1_rdo_dg_bh_rescaled_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r R : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → closedBall y (r * R) ⊆ D → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → ∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -(r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ := by
  intro m D F μ ν y r R hF hGG hr hball g hg hgc hgs
  have hr0 : r ≠ 0 := hr.ne'
  -- Step 1: the affine map `S z = r⁻¹(z − y)`, inverse to `w ↦ y + rw`.
  set S : Euclid (m + 1) → Euclid (m + 1) := fun z => r⁻¹ • (z - y) with hS_def
  have hS_cont : Continuous S := (continuous_id.sub continuous_const).const_smul r⁻¹
  have hS_deriv : ∀ z, HasFDerivAt S (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) z :=
    fun z => ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const y).const_smul r⁻¹
  -- Step 2: `φ = g ∘ S` is `C¹` and `div φ = r⁻¹ (div g) ∘ S`.
  have hφ : ContDiff ℝ 1 (fun z => g (S z)) :=
    hg.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hdiv : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => g (S z)) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
      r⁻¹ * LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (S z) : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by
    intro z
    have hgd : HasFDerivAt g (fderiv ℝ g (S z)) (S z) :=
      ((hg.differentiable one_ne_zero) (S z)).hasFDerivAt
    rw [show (fun z => g (S z)) = g ∘ S from rfl, (hgd.comp z (hS_deriv z)).fderiv]
    have : (fderiv ℝ g (S z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) =
        r⁻¹ • fderiv ℝ g (S z) := by
      ext x; simp
    rw [this, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
  -- Step 3: `φ` has compact support and `tsupport φ ⊆ S⁻¹(tsupport g) ⊆ B̄_{rR}(y) ⊆ D`.
  let e : Euclid (m + 1) ≃ₜ Euclid (m + 1) :=
    (Homeomorph.subRight y).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr0))
  have he : ⇑e = S := by funext z; rfl
  have hφc : HasCompactSupport (fun z => g (S z)) := by
    have := hgc.comp_homeomorph e
    rwa [he] at this
  have hφs : tsupport (fun z => g (S z)) ⊆ D := by
    intro z hz
    have hmem := hgs (tsupport_comp_subset_preimage g hS_cont hz)
    rw [mem_ball_zero_iff, hS_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    apply hball
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  -- Step 4: the Gauss–Green hypothesis for `φ`.
  have hGGφ := hGG (fun z => g (S z)) hφ hφc hφs
  -- Step 5: the substitution `z = y + rw`: `∫_F div φ = r^m ∫_{F_{y,r}} div g`.
  set Tg : Euclid (m + 1) → ℝ := fun w => LinearMap.trace ℝ (Euclid (m + 1))
    (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
  have hpre : MeasurableSet ((fun w => y + r • w) ⁻¹' F) :=
    (measurable_const.add (measurable_id.const_smul r)) hF
  have hcv : ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => g (S z)) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
      r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, Tg w := by
    simp_rw [hdiv]
    rw [← integral_indicator hF, ← integral_indicator hpre]
    have h1 : ∫ z, F.indicator (fun z => r⁻¹ * Tg (S z)) z =
        ∫ u, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + u) :=
      (integral_add_left_eq_self _ y).symm
    have h2 := Measure.integral_comp_smul (μ := volume)
      (fun u => F.indicator (fun z => r⁻¹ * Tg (S z)) (y + u)) r
    rw [finrank_euclideanSpace_fin] at h2
    have h3 : ∫ u, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + u) =
        r ^ (m + 1) * ∫ x, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + r • x) := by
      rw [h2, smul_eq_mul, ← mul_assoc, abs_inv, abs_of_pos (pow_pos hr _),
        mul_inv_cancel₀ (pow_ne_zero _ hr0), one_mul]
    rw [h1, h3]
    have h4 : ∀ x, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + r • x) =
        r⁻¹ * ((fun w => y + r • w) ⁻¹' F).indicator Tg x := by
      intro x
      by_cases hx : y + r • x ∈ F
      · have hx' : x ∈ (fun w => y + r • w) ⁻¹' F := hx
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
        simp [hS_def, smul_smul, inv_mul_cancel₀ hr0]
      · have hx' : x ∉ (fun w => y + r • w) ⁻¹' F := hx
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]
    simp_rw [h4]
    rw [integral_const_mul, ← mul_assoc, pow_succ, mul_assoc (r ^ m), mul_inv_cancel₀ hr0, mul_one]
  -- Step 6: divide by `r^m > 0`.
  rw [hcv] at hGGφ
  calc ∫ w in (fun w => y + r • w) ⁻¹' F, Tg w
      = (r ^ m)⁻¹ * (r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, Tg w) := by field_simp
    _ = -(r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ := by rw [hGGφ]; ring

/-- **Directional rescaled Gauss–Green identity** (Simon Ch. 3, 4.3, (8), for an arbitrary
direction `w` in place of `eᵢ`).  Let `(μ, ν)` satisfy the Gauss–Green identity
`∫_F div φ dL^{m+1} = −∫ ⟨φ, ν⟩ dμ` for `φ ∈ C¹_c` with `spt φ ⊆ D`, and let `r > 0`,
`B̄_{rR}(y) ⊆ D`.  For `ζ ∈ C¹_c` with `spt ζ ⊆ B_R(0)` and `w ∈ ℝ^{m+1}`, the field `g = ζ w` is
`C¹` with `spt g ⊆ spt ζ ⊆ B_R(0)`, `div g = Dζ(·)(w)` (the trace of the rank-one map
`h ↦ Dζ(h) w` is `Dζ(w)`) and `⟨g, ν⟩ = ζ ⟨w, ν⟩`.  The rescaled Gauss–Green identity for `g`
thus reads `∫_{F_{y,r}} Dζ(w) dL^{m+1} = −r⁻ᵐ ∫ ζ(r⁻¹(z − y)) ⟨w, ν(z)⟩ dμ(z)`, where
`F_{y,r} = {x : y + r x ∈ F}`. -/
theorem Submission.codim1_rdo_dg_bh_directional_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r R : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → closedBall y (r * R) ⊆ D → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R → ∀ w : Euclid (m + 1), ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z w = -(r ^ m)⁻¹ * ∫ z, ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ := by
  intro m D F μ ν y r R hF hGG hr hball ζ hζ hζc hζs w
  -- Step 1: `g = ζ w` is `C¹` with compact support and `spt g ⊆ spt ζ ⊆ B_R(0)`
  have hg : ContDiff ℝ 1 (fun z => ζ z • w) := hζ.smul contDiff_const
  have hgc : HasCompactSupport (fun z => ζ z • w) := hζc.smul_right (f' := fun _ => w)
  have hgs : tsupport (fun z => ζ z • w) ⊆ ball (0 : Euclid (m + 1)) R :=
    (tsupport_smul_subset_left ζ (fun _ => w)).trans hζs
  -- Step 2: `div g = Dζ(·)(w)`, the trace of the rank-one map `h ↦ Dζ(h) w`
  have h1 : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => ζ z • w) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = fderiv ℝ ζ z w := by
    intro z
    rw [fderiv_smul_const ((hζ.differentiable one_ne_zero) z) w]
    have : ((fderiv ℝ ζ z).smulRight w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
        (fderiv ℝ ζ z : Euclid (m + 1) →ₗ[ℝ] ℝ).smulRight w := by
      ext x; simp
    rw [this, LinearMap.trace_smulRight]
    rfl
  -- Step 3: `⟨g(r⁻¹(z − y)), ν(z)⟩ = ζ(r⁻¹(z − y)) ⟨w, ν(z)⟩`
  have h2 : ∀ z, inner ℝ (ζ (r⁻¹ • (z - y)) • w) (ν z) = ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) :=
    fun z => real_inner_smul_left _ _ _
  -- Step 4: the rescaled Gauss–Green identity for `g`, with both integrands rewritten
  have key := Submission.codim1_rdo_dg_bh_rescaled_gauss_green m D F μ ν y r R hF hGG hr hball
    (fun z => ζ z • w) hg hgc hgs
  simp_rw [h1, h2] at key
  exact key
/-- **Small normal defect** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi), printed (1)–(2),
chapter-03.txt lines 609–619).  Let `ν` be a measurable unit vector field and `v` a unit vector,
let `μ(B̄_ρ₀(y)) < ∞` for some `ρ₀ > 0`, and let the averages `A(ρ) = μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ`
tend to `v` as `ρ ↓ 0`.  Then for every `δ > 0` and all small `ρ > 0`,
`∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ ≤ δ μ(B̄_ρ(y))` and `∫_{B̄_ρ(y)} |⟨ν, w⟩| dμ ≤ δ |w| μ(B̄_ρ(y))` for
every `w ⊥ v`.  The first bound is `∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ = μ(B̄_ρ(y)) (1 - ⟨A(ρ), v⟩)`; the
second integrates `|⟨ν, w⟩| ≤ |w| |ν - v| ≤ |w| (δ/2 + (1 - ⟨ν, v⟩)/δ)`, where
`|ν - v|² = 2 (1 - ⟨ν, v⟩)`. -/
theorem Submission.codim1_rdo_dg_bh_normal_defect_small : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ δ : ℝ, 0 < δ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ z in closedBall y ρ, (1 - inner ℝ (ν z) v) ∂μ ≤ δ * (μ (closedBall y ρ)).toReal ∧ ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in closedBall y ρ, |inner ℝ (ν z) w| ∂μ ≤ δ * ‖w‖ * (μ (closedBall y ρ)).toReal := by
  intro m μ ν y v hν hν1 hv ⟨ρ₀, hρ₀, hfin⟩ hA δ hδ
  -- `⟨A(ρ), v⟩ → ⟨v, v⟩ = 1`
  have hε : Tendsto (fun ρ : ℝ => inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun x : Euclid (m + 1) => inner ℝ x v) :=
      continuous_id.inner continuous_const
    have := (hcont.tendsto v).comp hA
    rwa [real_inner_self_eq_norm_sq, hv, one_pow] at this
  -- eventually `ρ < ρ₀` and `1 - ⟨A(ρ), v⟩ < η = min δ (δ² / 2)`
  set η := min δ (δ ^ 2 / 2) with hη_def
  have hη : 0 < η := lt_min hδ (by positivity)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηδ2 : η ≤ δ ^ 2 / 2 := min_le_right _ _
  have hev1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 1 - η < inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v :=
    hε.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 ρ₀ := Ioo_mem_nhdsGT hρ₀
  filter_upwards [hev1, hev2] with ρ h1 h2
  -- `μ(B̄_ρ(y)) < ∞`, so the bounded measurable integrands are integrable
  set B := closedBall y ρ with hB
  have hfinρ : μ B ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall h2.2.le))
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr hfinρ
  set M := (μ B).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hνint : Integrable ν (μ.restrict B) :=
    Integrable.of_bound hν.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hν1 z).le)
  have hνv_meas : Measurable (fun z => inner ℝ (ν z) v) :=
    (continuous_id.inner continuous_const).measurable.comp hν
  have hνv : Integrable (fun z => inner ℝ (ν z) v) (μ.restrict B) := by
    refine Integrable.of_bound hνv_meas.aestronglyMeasurable 1 (Eventually.of_forall fun z => ?_)
    calc ‖inner ℝ (ν z) v‖ = |inner ℝ (ν z) v| := Real.norm_eq_abs _
      _ ≤ ‖ν z‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hν1, hv, one_mul]
  have hdefint : Integrable (fun z => 1 - inner ℝ (ν z) v) (μ.restrict B) :=
    (integrable_const 1).sub hνv
  -- `∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ = M (1 - ⟨A(ρ), v⟩) ≤ M η`
  have hdef : ∫ z in B, (1 - inner ℝ (ν z) v) ∂μ ≤ M * η := by
    rcases eq_or_ne M 0 with hM0' | hMne
    · have hμB : μ B = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hM0' with h | h
        · exact h
        · exact absurd h hfinρ
      rw [Measure.restrict_eq_zero.mpr hμB, integral_zero_measure, hM0', zero_mul]
    · have hinner : ∫ z in B, inner ℝ (ν z) v ∂μ = inner ℝ (∫ z in B, ν z ∂μ) v := by
        simp_rw [real_inner_comm v]
        have := (innerSL ℝ v).integral_comp_comm hνint
        simpa using this
      rw [integral_sub (integrable_const 1) hνv, hinner, integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.restrict_apply_univ]
      have hA' : inner ℝ (∫ z in B, ν z ∂μ) v = M * inner ℝ (M⁻¹ • ∫ z in B, ν z ∂μ) v := by
        rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
      rw [hA']
      have : 1 - inner ℝ (M⁻¹ • ∫ z in B, ν z ∂μ) v ≤ η := by linarith
      nlinarith
  refine ⟨?_, ?_⟩
  · calc ∫ z in B, (1 - inner ℝ (ν z) v) ∂μ ≤ M * η := hdef
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hηδ hM0
      _ = δ * M := mul_comm _ _
  · intro w hw
    -- pointwise `|⟨ν, w⟩| ≤ |w| |ν - v| ≤ |w| (δ/2 + (1 - ⟨ν, v⟩)/δ)` for `w ⊥ v`
    have hpt : ∀ z, |inner ℝ (ν z) w| ≤ ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ) := by
      intro z
      have e1 : inner ℝ (ν z) w = inner ℝ (ν z - v) w := by
        rw [inner_sub_left, real_inner_comm w v, hw, sub_zero]
      have e2 : ‖ν z - v‖ ^ 2 = 2 - 2 * inner ℝ (ν z) v := by
        rw [norm_sub_sq_real, hν1, hv]; ring
      have e3 : ‖ν z - v‖ ≤ δ / 2 + (1 - inner ℝ (ν z) v) / δ := by
        have ht := sq_nonneg (‖ν z - v‖ - δ)
        have : (1 - inner ℝ (ν z) v) / δ = ‖ν z - v‖ ^ 2 / (2 * δ) := by
          rw [e2]; field_simp
        rw [this, div_add_div _ _ (two_ne_zero) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith
      rw [e1]
      calc |inner ℝ (ν z - v) w| ≤ ‖ν z - v‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ ≤ (δ / 2 + (1 - inner ℝ (ν z) v) / δ) * ‖w‖ :=
            mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
        _ = _ := mul_comm _ _
    have hint1 : Integrable (fun z => |inner ℝ (ν z) w|) (μ.restrict B) := by
      refine Integrable.of_bound
        ((continuous_abs.comp (continuous_id.inner continuous_const)).measurable.comp
          hν).aestronglyMeasurable ‖w‖
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      calc |inner ℝ (ν z) w| ≤ ‖ν z‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ‖w‖ := by rw [hν1, one_mul]
    have hint2 : Integrable (fun z => ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ)) (μ.restrict B) :=
      ((integrable_const (δ / 2)).add (hdefint.div_const δ)).const_mul ‖w‖
    -- integrate, then use `∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ ≤ M η ≤ M δ² / 2`
    calc ∫ z in B, |inner ℝ (ν z) w| ∂μ
        ≤ ∫ z in B, ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ) ∂μ :=
          integral_mono hint1 hint2 hpt
      _ = ‖w‖ * (δ / 2 * M + (∫ z in B, (1 - inner ℝ (ν z) v) ∂μ) / δ) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hdefint.div_const δ),
            integral_const, integral_div, smul_eq_mul]
          simp only [Measure.real, Measure.restrict_apply_univ]
          ring
      _ ≤ ‖w‖ * (δ / 2 * M + M * η / δ) := by
          gcongr
      _ ≤ ‖w‖ * (δ / 2 * M + M * (δ ^ 2 / 2) / δ) := by
          gcongr
      _ = δ * ‖w‖ * M := by
          field_simp
          ring
/-- **Uniform perimeter bound for the blow-ups** (Simon Ch. 3, 4.3 (6)–(8): the bound that lets
the compactness theorem Ch. 2, 2.6 select an `L¹_loc`-convergent sequence of blow-ups).  Let
`∫_F div φ = -∫ ⟨φ, ν⟩ dμ` for `φ ∈ C¹_c` with `spt φ ⊆ D`, where `|ν| = 1`, and let
`B̄_{ρ₁}(y) ⊆ D` and `μ(B̄_ρ(y)) ≤ C₁ρᵐ` for `0 < ρ < ρ₁`.  If `rR < ρ₁`, `g ∈ C¹_c(B_R(0))` and
`|g| ≤ 1`, then `∫_{F_{y,r}} div g ≤ C₁Rᵐ`, where `F_{y,r} = {w : y + rw ∈ F}`.  As
`B̄_{rR}(y) ⊆ D`, the rescaled Gauss–Green identity gives `∫_{F_{y,r}} div g = -r⁻ᵐ ∫ h dμ` with
`h(z) = ⟨g(r⁻¹(z - y)), ν(z)⟩`; `|h| ≤ 1` and `h` vanishes off `K = B̄_{rR}(y)`, so
`|∫ h dμ| ≤ μ(K) ≤ C₁(rR)ᵐ` and `-r⁻ᵐ ∫ h dμ ≤ C₁Rᵐ`. -/
theorem Submission.codim1_rdo_dg_bh_perimeter_bound : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ R r : ℝ, 0 < R → 0 < r → r * R < ρ₁ → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → (∀ z, ‖g z‖ ≤ 1) → ∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C₁ * R ^ m := by
  intro m D F μ ν y ρ₁ C₁ hF hν hν1 hGG hρ₁ hC₁ hball hmass R r hR hr hrR g hg hgc hgs hg1
  -- Step 1: `B̄_{rR}(y) ⊆ B̄_{ρ₁}(y) ⊆ D`, so the rescaled Gauss–Green identity applies to `g`
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall hrR.le).trans hball
  rw [Submission.codim1_rdo_dg_bh_rescaled_gauss_green m D F μ ν y r R hF hGG hr hsub g hg hgc hgs]
  -- Step 2: `h(z) = ⟨g(r⁻¹(z - y)), ν(z)⟩` vanishes off `B̄_{rR}(y)`, as `spt g ⊆ B_R(0)`
  have hzero : ∀ z, z ∉ closedBall y (r * R) → inner ℝ (g (r⁻¹ • (z - y))) (ν z) = 0 := by
    intro z hz
    have hgz : g (r⁻¹ • (z - y)) = 0 := by
      by_contra hne
      apply hz
      have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hgs (subset_tsupport _ hne)
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_lt_iff₀ hr] at hmem
      rw [mem_closedBall, dist_eq_norm]
      exact hmem.le
    rw [hgz, inner_zero_left]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- Step 3: `μ(B̄_{rR}(y)) ≤ C₁(rR)ᵐ < ∞` and `|h| ≤ |g| |ν| ≤ 1`, so `|∫ h dμ| ≤ C₁(rR)ᵐ`
  have hK : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) :=
    hmass _ (mul_pos hr hR) hrR
  have hbound : ‖∫ z in closedBall y (r * R), inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ‖ ≤
      1 * μ.real (closedBall y (r * R)) := by
    refine norm_setIntegral_le_of_norm_le_const (hK.trans_lt ENNReal.ofReal_lt_top) fun z _ => ?_
    calc ‖inner ℝ (g (r⁻¹ • (z - y))) (ν z)‖ = |inner ℝ (g (r⁻¹ • (z - y))) (ν z)| :=
          Real.norm_eq_abs _
      _ ≤ ‖g (r⁻¹ • (z - y))‖ * ‖ν z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [hν1, mul_one]; exact hg1 _
  have hμK : μ.real (closedBall y (r * R)) ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hK
  rw [Real.norm_eq_abs, one_mul] at hbound
  have hneg := (abs_le.mp hbound).1
  -- Step 4: `-r⁻ᵐ ∫ h dμ ≤ r⁻ᵐ C₁(rR)ᵐ = C₁Rᵐ`
  have hrm : 0 < r ^ m := pow_pos hr m
  calc -(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ
      = (r ^ m)⁻¹ * -∫ z in closedBall y (r * R), inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ := by
        ring
    _ ≤ (r ^ m)⁻¹ * (C₁ * (r * R) ^ m) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hrm.le)
    _ = C₁ * R ^ m := by rw [mul_pow]; field_simp

/-- **Simon Ch. 3, proof of 4.3, (8)** ("so that `∫_{λ_k⁻¹E} Dᵢζ dL^{n+1} → 0` by (2) for
`i = 1, …, n`"): derivatives of `ζ ∈ C¹_c(ℝ^{m+1})` in directions `w ⊥ v` integrate to `0` over
the blow-ups `F_{y,r} = {x : y + rx ∈ F}` as `r ↓ 0`.  Take `R > 0` with `spt ζ ⊆ B_R(0)` and
`M = sup |ζ|`.  For small `r`, `ρ = rR < ρ₁`, so `B̄_ρ(y) ⊆ D` and the directional Gauss–Green
identity (`codim1_rdo_dg_bh_directional_gauss_green`) gives
`∫_{F_{y,r}} Dζ(w) = −r⁻ᵐ ∫ ζ(r⁻¹(z − y)) ⟨w, ν(z)⟩ dμ(z)`, whose integrand vanishes off `B̄_ρ(y)`
and is bounded by `M |⟨ν, w⟩|`.  The normal-defect estimate (2)
(`codim1_rdo_dg_bh_normal_defect_small`, applicable as `μ(B̄_{ρ₁/2}(y)) ≤ C₁(ρ₁/2)ᵐ < ∞`) gives
`∫_{B̄_ρ(y)} |⟨ν, w⟩| dμ ≤ δ|w| μ(B̄_ρ(y)) ≤ δ|w|C₁ρᵐ` for small `ρ`, hence
`|∫_{F_{y,r}} Dζ(w)| ≤ δM|w|C₁Rᵐ`, which is `< η` for `δ = η/(1 + M|w|C₁Rᵐ)`. -/
theorem Submission.codim1_rdo_dg_bh_tangential_vanish : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∀ w : Euclid (m + 1), inner ℝ w v = 0 → Tendsto (fun r : ℝ => ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z w) (𝓝[>] 0) (𝓝 0) := by
  intro m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA hρ₁ hC₁ hball hmass ζ hζ hζc w hw
  -- Step 1: `spt ζ ⊆ B_R(0)` with `R > 0`, and `|ζ| ≤ M`
  obtain ⟨R₀, hR₀⟩ := hζc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
  set R := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R :=
    hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖ζ z‖ ≤ M := hζ.continuous.bounded_above_of_compact_support hζc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM' : ∀ z, |ζ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  -- Step 2: `μ(B̄_{ρ₁/2}(y)) < ∞`, and `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`
  have hfin : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞ :=
    ⟨ρ₁ / 2, half_pos hρ₁, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass _ (half_pos hρ₁) (half_lt_self hρ₁))⟩
  have htend : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * R < ρ₁ :=
    (htend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hρ₁)
  -- Step 3: given `η > 0`, apply (2) with `δ = η/(1 + K)`, `K = M|w|C₁Rᵐ`, at `ρ = rR`
  set K := M * ‖w‖ * C₁ * R ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ := η / (1 + K) with hδ_def
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hnd := htend.eventually
    (Submission.codim1_rdo_dg_bh_normal_defect_small m μ ν y v hν hν1 hv hfin hA δ hδ)
  filter_upwards [hnd, hsmall, self_mem_nhdsWithin] with r h1 h2 h3
  have hr : 0 < r := h3
  have hrR : 0 < r * R := mul_pos hr hRpos
  -- Step 4: `B̄_{rR}(y) ⊆ D` and `μ(B̄_{rR}(y)) ≤ C₁(rR)ᵐ < ∞`
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall h2.le).trans hball
  have hBfin : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) := hmass _ hrR h2
  have hBlt : μ (closedBall y (r * R)) < ∞ := hBfin.trans_lt ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (μ.restrict (closedBall y (r * R))) :=
    isFiniteMeasure_restrict.mpr hBlt.ne
  have hμB : (μ (closedBall y (r * R))).toReal ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hBfin
  -- Step 5: the directional Gauss–Green identity; its integrand vanishes off `B̄_{rR}(y)`
  have hζz : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hR (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  have hrm : 0 < r ^ m := pow_pos hr m
  rw [dist_zero_right, Submission.codim1_rdo_dg_bh_directional_gauss_green m D F μ ν y r R hF hGG hr
    hsub ζ hζ hζc hR w]
  have hzero : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) = 0 := by
    intro z hz
    rw [hζz z hz, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- Step 6: `|∫ ζ(r⁻¹(z − y)) ⟨w, ν⟩ dμ| ≤ M ∫_{B̄_{rR}(y)} |⟨ν, w⟩| dμ ≤ Mδ|w|C₁(rR)ᵐ`
  have hνw : Measurable (fun z => |inner ℝ (ν z) w|) :=
    (continuous_abs.comp (continuous_id.inner continuous_const)).measurable.comp hν
  have hint : Integrable (fun z => M * |inner ℝ (ν z) w|) (μ.restrict (closedBall y (r * R))) := by
    refine (Integrable.of_bound hνw.aestronglyMeasurable ‖w‖
      (Eventually.of_forall fun z => ?_)).const_mul M
    rw [Real.norm_eq_abs, abs_abs]
    calc |inner ℝ (ν z) w| ≤ ‖ν z‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ = ‖w‖ := by rw [hν1, one_mul]
  have hb1 : ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ ≤
      ∫ z in closedBall y (r * R), M * |inner ℝ (ν z) w| ∂μ := by
    apply norm_integral_le_of_norm_le hint
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, real_inner_comm]
    exact mul_le_mul_of_nonneg_right (hM' _) (abs_nonneg _)
  have hb2 : ∫ z in closedBall y (r * R), M * |inner ℝ (ν z) w| ∂μ ≤
      M * (δ * ‖w‖ * (C₁ * (r * R) ^ m)) := by
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hM0
    calc ∫ z in closedBall y (r * R), |inner ℝ (ν z) w| ∂μ
        ≤ δ * ‖w‖ * (μ (closedBall y (r * R))).toReal := h1.2 w hw
      _ ≤ δ * ‖w‖ * (C₁ * (r * R) ^ m) := by gcongr
  -- Step 7: `r⁻ᵐ · Mδ|w|C₁(rR)ᵐ = δK < η`
  have hnorm : ‖-(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ =
      (r ^ m)⁻¹ * ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ := by
    rw [norm_mul, norm_neg, norm_inv, Real.norm_eq_abs (r ^ m), abs_of_pos hrm]
  rw [hnorm]
  calc (r ^ m)⁻¹ * ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖
      ≤ (r ^ m)⁻¹ * (M * (δ * ‖w‖ * (C₁ * (r * R) ^ m))) := by
        gcongr
        exact hb1.trans hb2
    _ = δ * K := by rw [hK, mul_pow]; field_simp
    _ < η := by
        rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Simon Ch. 3, 4.3, proof of (9): the normal derivatives of the blow-ups `F_{y,r}` are
asymptotically nonpositive.  Take `tsupport ζ ⊆ B_R(0)`, `M ≥ sup ζ` and `δ' = δ / (1 + M C₁ Rᵐ)`.
For small `r`, `directional_gauss_green` (with `w = v`, `ρ = rR`) and the pointwise bound
`-ζ⟨v, ν⟩ ≤ M (1 - ⟨ν, v⟩)` on `B̄_ρ(y)` give
`∫_{F_{y,r}} Dζ(v) ≤ r⁻ᵐ M ∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ ≤ r⁻ᵐ M δ' μ(B̄_ρ(y)) ≤ M δ' C₁ Rᵐ ≤ δ`,
by `normal_defect_small` and `μ(B̄_ρ(y)) ≤ C₁ρᵐ`. -/
theorem Submission.codim1_rdo_dg_bh_normal_limsup : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z v ≤ δ := by
  intro m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA hρ₁ hC₁ hball hmass ζ hζ hζc hζ0 δ hδ
  -- Step 1: `tsupport ζ ⊆ B_R(0)` with `R ≥ 1`, `|ζ| ≤ M`, and `δ' = δ / (1 + M C₁ Rᵐ)`
  obtain ⟨R₀, hR₀⟩ := hζc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
  set R := max R₀ 1 with hR_def
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R :=
    hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖ζ z‖ ≤ M := hζ.continuous.bounded_above_of_compact_support hζc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM' : ∀ z, |ζ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  set K := M * C₁ * R ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  set δ' := δ / (1 + K) with hδ'_def
  have hδ' : 0 < δ' := div_pos hδ (by linarith)
  -- Step 2: the normal defect on `B̄_ρ(y)` is at most `δ' μ(B̄_ρ(y))` for small `ρ = rR`
  have hfin : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞ :=
    ⟨ρ₁ / 2, half_pos hρ₁, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass _ (half_pos hρ₁) (half_lt_self hρ₁))⟩
  have htend : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * R < ρ₁ :=
    (htend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hρ₁)
  have hnd := htend.eventually
    (Submission.codim1_rdo_dg_bh_normal_defect_small m μ ν y v hν hν1 hv hfin hA δ' hδ')
  filter_upwards [hnd, hsmall, self_mem_nhdsWithin] with r h1 h2 h3
  have hr : 0 < r := h3
  have hrR : 0 < r * R := mul_pos hr hRpos
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall h2.le).trans hball
  have hBfin : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) := hmass _ hrR h2
  have hBlt : μ (closedBall y (r * R)) < ∞ := hBfin.trans_lt ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (μ.restrict (closedBall y (r * R))) :=
    isFiniteMeasure_restrict.mpr hBlt.ne
  have hμB : (μ (closedBall y (r * R))).toReal ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hBfin
  -- Step 3: the rescaled identity, with `s(z) = ζ(r⁻¹(z - y))` vanishing off `B̄_ρ(y)`
  have hζz : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hR (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  have hζmeas : Measurable (fun z : Euclid (m + 1) => ζ (r⁻¹ • (z - y))) :=
    (hζ.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)).measurable
  have hrm : 0 < r ^ m := pow_pos hr m
  rw [Submission.codim1_rdo_dg_bh_directional_gauss_green m D F μ ν y r R hF hGG hr
    hsub ζ hζ hζc hR v]
  have hzero : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) = 0 := by
    intro z hz
    rw [hζz z hz, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- Step 4: `-s⟨v, ν⟩ ≤ M (1 - ⟨ν, v⟩)`, both sides bounded on the finite ball
  have hνv : Measurable (fun z => inner ℝ (ν z) v) :=
    (continuous_id.inner continuous_const).measurable.comp hν
  have hνv' : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hν
  have hint_l : Integrable (fun z => ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z))
      (μ.restrict (closedBall y (r * R))) := by
    refine Integrable.of_bound (hζmeas.mul hνv').aestronglyMeasurable M
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have : |inner ℝ v (ν z)| ≤ 1 :=
      (abs_real_inner_le_norm _ _).trans (by rw [hν1, hv, one_mul])
    calc |ζ (r⁻¹ • (z - y))| * |inner ℝ v (ν z)| ≤ M * 1 := by
          gcongr
          exact hM' _
      _ = M := mul_one M
  have hint_d : Integrable (fun z => 1 - inner ℝ (ν z) v) (μ.restrict (closedBall y (r * R))) := by
    refine (integrable_const 1).sub (Integrable.of_bound hνv.aestronglyMeasurable 1
      (Eventually.of_forall fun z => ?_))
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by rw [hν1, hv, one_mul])
  have hpt : ∀ z, -(ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z)) ≤ M * (1 - inner ℝ (ν z) v) := by
    intro z
    have hs0 := hζ0 (r⁻¹ • (z - y))
    have hsM : ζ (r⁻¹ • (z - y)) ≤ M := (le_abs_self _).trans (hM' _)
    have hin : inner ℝ (ν z) v ≤ 1 :=
      (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (by rw [hν1, hv, one_mul]))
    rw [real_inner_comm]
    nlinarith
  -- Step 5: integrate and use `μ(B̄_ρ(y)) ≤ C₁ρᵐ`
  have hmain : -∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ ≤
      M * ∫ z in closedBall y (r * R), (1 - inner ℝ (ν z) v) ∂μ := by
    rw [← integral_neg, ← integral_const_mul]
    exact integral_mono hint_l.neg (hint_d.const_mul M) hpt
  have hdef : ∫ z in closedBall y (r * R), (1 - inner ℝ (ν z) v) ∂μ ≤ δ' * (C₁ * (r * R) ^ m) :=
    h1.1.trans (by gcongr)
  -- Step 6: `r⁻ᵐ M δ' C₁ (rR)ᵐ = δ' M C₁ Rᵐ ≤ δ`
  calc -(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ
      = (r ^ m)⁻¹ * (-∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) := by
        ring
    _ ≤ (r ^ m)⁻¹ * (M * (δ' * (C₁ * (r * R) ^ m))) := by
        gcongr
        exact hmain.trans (mul_le_mul_of_nonneg_left hdef hM0)
    _ = δ' * K := by rw [hK, mul_pow]; field_simp
    _ ≤ δ := by
        rw [hδ'_def, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
/-- **Scale invariance of the two-sided volume density bounds** (Simon Ch. 3, 4.3 (10)–(11)): if
`L(F ∩ B_ρ(y)) ≥ c₂ρ^{m+1}` and `L(B_ρ(y) \ F) ≥ c₂ρ^{m+1}` for `0 < ρ < ρ₂`, then the rescaled set
`F_{y,r} = {w : y + rw ∈ F}` satisfies the same bounds on `B_s(0)` whenever `rs < ρ₂`.  The map
`w ↦ y + rw` scales Lebesgue measure by `r^{m+1}` and pulls `B_{rs}(y)` back to `B_s(0)`. -/
theorem Submission.codim1_rdo_dg_bh_rescaled_volume_lower : ∀ (m : ℕ) (F : Set (Euclid (m + 1))) (y : Euclid (m + 1)) (c₂ ρ₂ : ℝ), MeasurableSet F → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₂ → ENNReal.ofReal (c₂ * ρ ^ (m + 1)) ≤ volume (F ∩ ball y ρ) ∧ ENNReal.ofReal (c₂ * ρ ^ (m + 1)) ≤ volume (ball y ρ \ F)) → ∀ s r : ℝ, 0 < s → 0 < r → r * s < ρ₂ → ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume ((fun w => y + r • w) ⁻¹' F ∩ ball (0 : Euclid (m + 1)) s) ∧ ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume (ball (0 : Euclid (m + 1)) s \ (fun w => y + r • w) ⁻¹' F) := by
  intro m F y c₂ ρ₂ _ hvol s r hs hr hrs
  -- `L((y + r ·)⁻¹' S) = r^{-(m+1)} L(S)`: Haar scaling, then translation invariance
  have hscale : ∀ S : Set (Euclid (m + 1)), volume ((fun w => y + r • w) ⁻¹' S) =
      ENNReal.ofReal (|r ^ (m + 1)|⁻¹) * volume S := by
    intro S
    have : (fun w => y + r • w) ⁻¹' S = (r • ·) ⁻¹' ((fun u => y + u) ⁻¹' S) := rfl
    rw [this, Measure.addHaar_preimage_smul volume hr.ne', finrank_euclideanSpace_fin,
      measure_preimage_add, abs_inv]
  -- `|(y + rw) − y| = r|w|`, so `(y + r ·)⁻¹' B_{rs}(y) = B_s(0)`
  have hball : (fun w => y + r • w) ⁻¹' ball y (r * s) = ball (0 : Euclid (m + 1)) s := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_mul_iff_right₀ hr
  -- the hypothesis at `ρ = rs`, and both sets as preimages of the unscaled ones
  obtain ⟨h1, h2⟩ := hvol (r * s) (mul_pos hr hs) hrs
  have e1 : (fun w => y + r • w) ⁻¹' F ∩ ball (0 : Euclid (m + 1)) s =
      (fun w => y + r • w) ⁻¹' (F ∩ ball y (r * s)) := by rw [Set.preimage_inter, hball]
  have e2 : ball (0 : Euclid (m + 1)) s \ (fun w => y + r • w) ⁻¹' F =
      (fun w => y + r • w) ⁻¹' (ball y (r * s) \ F) := by rw [Set.preimage_sdiff, hball]
  -- `r^{-(m+1)} · c₂(rs)^{m+1} = c₂s^{m+1}` in `[0, ∞]` (both sides `0` if `c₂ ≤ 0`)
  have hfac : ENNReal.ofReal (c₂ * s ^ (m + 1)) =
      ENNReal.ofReal (|r ^ (m + 1)|⁻¹) * ENNReal.ofReal (c₂ * (r * s) ^ (m + 1)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [abs_of_pos (pow_pos hr _), mul_pow]
    field_simp
  rw [e1, e2, hscale, hscale, hfac]
  exact ⟨by gcongr, by gcongr⟩
/-- **`L¹_loc` transfer** (the passage to the blow-up limit in Simon Ch. 3, 4.3 (7), and in the
volume bounds fixing `λ = 0` after (9)): if `L^{m+1}((F_k Δ F₀) ∩ B_R(0)) → 0` for every `R`,
then `∫_{F_k} f → ∫_{F₀} f` for continuous compactly supported `f`
(`|∫_{F_k} f − ∫_{F₀} f| ≤ sup |f| · L^{m+1}((F_k Δ F₀) ∩ B_R(0))` once `spt f ⊆ B_R(0)`), and
`L^{m+1}(F_k ∩ B_s(0))`, `L^{m+1}(B_s(0) \ F_k)` converge to the values for `F₀`, each differing
from its limit by at most `L^{m+1}((F_k Δ F₀) ∩ B_s(0))`. -/
theorem Submission.codim1_rdo_dg_bh_l1loc_transfer : ∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))) (F₀ : Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → MeasurableSet F₀ → (∀ R : ℝ, Tendsto (fun k => volume (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R)) atTop (𝓝 0)) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z in Fs k, f z) atTop (𝓝 (∫ z in F₀, f z))) ∧ (∀ s : ℝ, Tendsto (fun k => volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)) atTop (𝓝 (volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)))) ∧ ∀ s : ℝ, Tendsto (fun k => volume (ball (0 : Euclid (m + 1)) s \ Fs k)) atTop (𝓝 (volume (ball (0 : Euclid (m + 1)) s \ F₀))) := by
  intro m Fs F₀ hFs hF₀ hconv
  -- `a k → b` in `[0, ∞]` once `b < ∞` and `a k ≤ b + e k`, `b ≤ a k + e k` with `e k → 0`
  have key : ∀ (a : ℕ → ℝ≥0∞) (b : ℝ≥0∞) (e : ℕ → ℝ≥0∞), b ≠ ∞ → Tendsto e atTop (𝓝 0) →
      (∀ k, a k ≤ b + e k) → (∀ k, b ≤ a k + e k) → Tendsto a atTop (𝓝 b) := by
    intro a b e hb he h1 h2
    rw [ENNReal.tendsto_nhds hb]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with k hk
    constructor
    · rw [tsub_le_iff_right]
      exact (h2 k).trans (by gcongr)
    · exact (h1 k).trans (by gcongr)
  refine ⟨?_, ?_, ?_⟩
  · intro f hf hfc
    obtain ⟨R, hR⟩ : ∃ R, tsupport f ⊆ ball (0 : Euclid (m + 1)) R :=
      hfc.isCompact.isBounded.subset_ball 0
    obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖f z‖ ≤ M := hf.bounded_above_of_compact_support hfc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hM' : ∀ z, |f z| ≤ M := fun z => by rw [← Real.norm_eq_abs]; exact hM z
    have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
    set E : ℕ → Set (Euclid (m + 1)) := fun k => symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R
    have hEm : ∀ k, MeasurableSet (E k) := fun k =>
      ((hFs k).symmDiff hF₀).inter measurableSet_ball
    have hEfin : ∀ k, volume (E k) ≠ ∞ := fun k =>
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
    -- `|1_{F_k} f − 1_{F₀} f| ≤ M · 1_{E k}`, as `f = 0` off `B_R(0)`
    have hbound : ∀ k, ‖(∫ z in Fs k, f z) - ∫ z in F₀, f z‖ ≤ M * (volume (E k)).toReal := by
      intro k
      rw [← integral_indicator (hFs k), ← integral_indicator hF₀,
        ← integral_sub (hfi.indicator (hFs k)) (hfi.indicator hF₀)]
      have hgi : Integrable ((E k).indicator (fun _ => M)) :=
        (integrableOn_const (hEfin k)).integrable_indicator (hEm k)
      calc ‖∫ z, ((Fs k).indicator f z - F₀.indicator f z)‖
          ≤ ∫ z, (E k).indicator (fun _ => M) z := by
            refine norm_integral_le_of_norm_le hgi (Eventually.of_forall fun z => ?_)
            by_cases hz : z ∈ E k
            · rw [Set.indicator_of_mem hz]
              by_cases h1 : z ∈ Fs k <;> by_cases h2 : z ∈ F₀ <;>
                simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, hM0, hM' z]
            · rw [Set.indicator_of_notMem hz, norm_le_zero_iff, sub_eq_zero]
              by_cases hzR : z ∈ ball (0 : Euclid (m + 1)) R
              · -- `z ∉ F_k Δ F₀`, so `z ∈ F_k ↔ z ∈ F₀`
                have hzs : z ∉ symmDiff (Fs k) F₀ := fun h => hz ⟨h, hzR⟩
                rw [Set.mem_symmDiff, not_or, not_and_not_right, not_and_not_right] at hzs
                by_cases h1 : z ∈ Fs k
                · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hzs.1 h1)]
                · rw [Set.indicator_of_notMem h1,
                    Set.indicator_of_notMem fun h2 => h1 (hzs.2 h2)]
              · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzR (hR h)
                rw [Set.indicator_apply_eq_zero.2 fun _ => hfz,
                  Set.indicator_apply_eq_zero.2 fun _ => hfz]
        _ = M * (volume (E k)).toReal := by
            rw [integral_indicator_const _ (hEm k), smul_eq_mul, mul_comm, measureReal_def]
    have hlim : Tendsto (fun k => M * (volume (E k)).toReal) atTop (𝓝 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hconv R)).const_mul M
    rw [← tendsto_sub_nhds_zero_iff]
    exact squeeze_zero_norm hbound hlim
  · intro s
    have hb : volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
    refine key _ _ _ hb (hconv s) (fun k => ?_) (fun k => ?_)
    · calc volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)
          ≤ volume ((F₀ ∩ ball (0 : Euclid (m + 1)) s) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ F₀
            · exact Or.inl ⟨h, hz.2⟩
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inl ⟨hz.1, h⟩), hz.2⟩
        _ ≤ _ := measure_union_le _ _
    · calc volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)
          ≤ volume ((Fs k ∩ ball (0 : Euclid (m + 1)) s) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ Fs k
            · exact Or.inl ⟨h, hz.2⟩
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inr ⟨hz.1, h⟩), hz.2⟩
        _ ≤ _ := measure_union_le _ _
  · intro s
    have hb : volume (ball (0 : Euclid (m + 1)) s \ F₀) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.sdiff_subset)
    refine key _ _ _ hb (hconv s) (fun k => ?_) (fun k => ?_)
    · calc volume (ball (0 : Euclid (m + 1)) s \ Fs k)
          ≤ volume ((ball (0 : Euclid (m + 1)) s \ F₀) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ F₀
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inr ⟨h, hz.2⟩), hz.1⟩
            · exact Or.inl ⟨hz.1, h⟩
        _ ≤ _ := measure_union_le _ _
    · calc volume (ball (0 : Euclid (m + 1)) s \ F₀)
          ≤ volume ((ball (0 : Euclid (m + 1)) s \ Fs k) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ Fs k
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inl ⟨h, hz.2⟩), hz.1⟩
            · exact Or.inl ⟨hz.1, h⟩
        _ ≤ _ := measure_union_le _ _
/-- **The blow-up half-space passes through the origin** (Simon Ch. 3, 4.3: "(10) and (11)
evidently tell us that `λ = 0` in (9)").  If `F₀` and its complement have positive measure in
every `B_s(0)`, and `F₀` is null, conull, or a.e. equal to `{⟨z, v⟩ > c}` with `|v| = 1`, then
`F₀ = {⟨z, v⟩ > 0}` a.e.  Since `|⟨z, v⟩| ≤ |z|`, `B_c(0)` misses `{⟨z, v⟩ > c}` if `c > 0`, and
`B_{−c}(0)` lies inside it if `c < 0`. -/
theorem Submission.codim1_rdo_dg_bh_offset_zero : ∀ (m : ℕ) (F₀ : Set (Euclid (m + 1))) (v : Euclid (m + 1)), ‖v‖ = 1 → (∀ s : ℝ, 0 < s → 0 < volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ∧ 0 < volume (ball (0 : Euclid (m + 1)) s \ F₀)) → (volume F₀ = 0 ∨ volume F₀ᶜ = 0 ∨ ∃ c : ℝ, volume (symmDiff F₀ {z | c < inner ℝ z v}) = 0) → volume (symmDiff F₀ {z | 0 < inner ℝ z v}) = 0 := by
  intro m F₀ v hv hpos htri
  rcases htri with h | h | ⟨c, hc⟩
  -- `L(F₀) = 0` would give `L(F₀ ∩ B_1(0)) = 0`
  · exact ((hpos 1 one_pos).1.ne' (measure_mono_null Set.inter_subset_left h)).elim
  -- `L(F₀ᶜ) = 0` would give `L(B_1(0) \ F₀) = 0`
  · exact ((hpos 1 one_pos).2.ne' (measure_mono_null (fun x hx => hx.2) h)).elim
  · rcases lt_trichotomy c 0 with hneg | rfl | hcpos
    -- `c < 0`: `⟨z, v⟩ ≥ −|z| > c` on `B_{−c}(0)`, so `B_{−c}(0) \ F₀ ⊆ F₀ Δ {⟨z, v⟩ > c}`
    · have hsub : ball (0 : Euclid (m + 1)) (-c) \ F₀ ⊆ symmDiff F₀ {z | c < inner ℝ z v} := by
        intro z hz
        refine Set.mem_symmDiff.mpr (Or.inr ⟨?_, hz.2⟩)
        have h1 : |inner ℝ z v| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
        have h2 := mem_ball_zero_iff.mp hz.1
        rw [hv, mul_one] at h1
        show c < inner ℝ z v
        linarith [neg_abs_le (inner ℝ z v)]
      exact ((hpos (-c) (neg_pos.mpr hneg)).2.ne' (measure_mono_null hsub hc)).elim
    · exact hc
    -- `c > 0`: `⟨z, v⟩ ≤ |z| < c` on `B_c(0)`, so `F₀ ∩ B_c(0) ⊆ F₀ Δ {⟨z, v⟩ > c}`
    · have hsub : F₀ ∩ ball (0 : Euclid (m + 1)) c ⊆ symmDiff F₀ {z | c < inner ℝ z v} := by
        intro z hz
        refine Set.mem_symmDiff.mpr (Or.inl ⟨hz.1, ?_⟩)
        have h1 : |inner ℝ z v| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
        have h2 := mem_ball_zero_iff.mp hz.2
        rw [hv, mul_one] at h1
        show ¬ c < inner ℝ z v
        linarith [le_abs_self (inner ℝ z v)]
      exact ((hpos c hcpos).1.ne' (measure_mono_null hsub hc)).elim
/-- **Discrete growth** (Simon Ch. 3, 4.3, (10), integrated in discrete steps).  If `V > 0` on
`(0, ρ₁)` and `V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ+δ) − V(ρ))` whenever `ρ, δ > 0`, `ρ + δ < ρ₁`, then
`(ρ/(2K(m+1)))^{m+1} ≤ V(ρ)` for `0 < ρ < ρ₁`.  With `W = V^{1/(m+1)}` and the Bernoulli bound
`xⁿ(x + n(y − x)) ≤ x yⁿ` (`x, y ≥ 0`), one step of length `δ` gives
`δw ≤ (W(r+δ) − W(r))(K(m+1)w + mδ)` for `0 ≤ w ≤ W(r)`.  Summing `N` such steps with
`δ = ρ/(2N)` from `ρ/2`, `w = W(ρ/2)` and `N > mρ²/(4K²(m+1)²W(ρ/2)²)` gives
`W(ρ) ≥ ρ/(2K(m+1))`. -/
theorem Submission.codim1_rdo_dg_vdl_discrete_growth : ∀ (m : ℕ) (K ρ₁ : ℝ) (V : ℝ → ℝ), 0 < K → (∀ r : ℝ, 0 < r → r < ρ₁ → 0 < V r) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → V ρ ^ ((m : ℝ) / (m + 1)) ≤ K / δ * (V (ρ + δ) - V ρ)) → ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ V ρ := by
  intro m K ρ₁ V hK hV hdiff ρ hρ hρ₁
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hKm : 0 < K * (m + 1) := by positivity
  -- Bernoulli's inequality `xⁿ (x + n (y − x)) ≤ x yⁿ` for `x, y ≥ 0`
  have bern : ∀ n : ℕ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ n * (x + n * (y - x)) ≤ x * y ^ n := by
    intro n
    induction n with
    | zero => intro x y _ _; simp
    | succ n ih =>
      intro x y hx hy
      have h1 := mul_le_mul_of_nonneg_left (ih x y hx hy) hy
      have h2 : 0 ≤ x ^ n * (n * (y - x) ^ 2) :=
        mul_nonneg (pow_nonneg hx n) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (y - x)))
      rw [pow_succ, pow_succ]
      push_cast
      linarith
  -- Step 2: `W = V^{1/(m+1)}`, so `W > 0`, `W^{m+1} = V` and `W^m = V^{m/(m+1)}`
  obtain ⟨W, hWpos, hWpow, hWpowm⟩ : ∃ W : ℝ → ℝ, (∀ r, 0 < r → r < ρ₁ → 0 < W r) ∧
      (∀ r, 0 < r → r < ρ₁ → W r ^ (m + 1) = V r) ∧
      (∀ r, 0 < r → r < ρ₁ → W r ^ m = V r ^ ((m : ℝ) / (m + 1))) := by
    refine ⟨fun r => V r ^ ((1 : ℝ) / (m + 1)), fun r h1 h2 => Real.rpow_pos_of_pos (hV r h1 h2) _,
      fun r h1 h2 => ?_, fun r h1 h2 => ?_⟩
    · show (V r ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = V r
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hV r h1 h2).le, Nat.cast_add_one,
        one_div_mul_cancel hm1, Real.rpow_one]
    · show (V r ^ ((1 : ℝ) / (m + 1))) ^ m = V r ^ ((m : ℝ) / (m + 1))
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hV r h1 h2).le, one_div_mul_eq_div]
  -- Step 3, algebra: `δ bᵐ ≤ K (a^{m+1} − b^{m+1})` and `0 ≤ w ≤ b` give
  -- `δ w ≤ (a − b) (K (m+1) w + m δ)`
  have alg : ∀ a b δ w : ℝ, 0 < a → 0 < b → 0 < δ → 0 ≤ w → w ≤ b →
      δ * b ^ m ≤ K * (a ^ (m + 1) - b ^ (m + 1)) →
      δ * w ≤ (a - b) * (K * (m + 1) * w + m * δ) := by
    intro a b δ w ha hb hδ hw0 hwb hd
    rw [pow_succ, pow_succ] at hd
    have hP : 0 < a ^ m := pow_pos ha m
    have hQ : 0 < b ^ m := pow_pos hb m
    have hB1 := bern (m + 1) a b ha.le hb.le
    rw [pow_succ, pow_succ] at hB1
    push_cast at hB1
    have hB0 := bern m a b ha.le hb.le
    -- `a^{m+1} − b^{m+1} ≤ (m+1) aᵐ (a − b)`
    have h1 : a ^ m * a - b ^ m * b ≤ (m + 1) * a ^ m * (a - b) := by
      have h : a * (a ^ m * a - b ^ m * b) ≤ a * ((m + 1) * a ^ m * (a - b)) := by linarith
      exact le_of_mul_le_mul_left h ha
    have h2 : δ * b ^ m ≤ K * (m + 1) * a ^ m * (a - b) := by
      have := mul_le_mul_of_nonneg_left h1 hK.le
      linarith
    have hab : 0 ≤ a - b := by
      by_contra hcon
      have : K * (m + 1) * a ^ m * (a - b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hKm.le hP.le) (not_le.mp hcon).le
      have : 0 < δ * b ^ m := mul_pos hδ hQ
      linarith
    -- `δ (a − m (a − b)) ≤ K (m+1) a (a − b)`
    have h3 : δ * (a + m * (b - a)) ≤ K * (m + 1) * a * (a - b) := by
      have e1 := mul_le_mul_of_nonneg_left hB0 hδ.le
      have e2 := mul_le_mul_of_nonneg_left h2 ha.le
      have h4 : a ^ m * (δ * (a + m * (b - a))) ≤ a ^ m * (K * (m + 1) * a * (a - b)) := by
        linarith
      exact le_of_mul_le_mul_left h4 hP
    have h5 : a * (δ * w) ≤ a * ((a - b) * (K * (m + 1) * w + m * δ)) := by
      have e1 := mul_le_mul_of_nonneg_left h3 hw0
      have e2 : 0 ≤ (a - b) * m * δ * (a - w) :=
        mul_nonneg (mul_nonneg (mul_nonneg hab hm0) hδ.le) (by linarith)
      linarith
    exact le_of_mul_le_mul_left h5 ha
  -- Step 3: one step of length `δ`
  have step : ∀ r δ w : ℝ, 0 < r → 0 < δ → r + δ < ρ₁ → 0 ≤ w → w ≤ W r →
      δ * w ≤ (W (r + δ) - W r) * (K * (m + 1) * w + m * δ) := by
    intro r δ w hr hδ hrδ hw0 hwb
    have hr1 : r < ρ₁ := by linarith
    have hrδ0 : 0 < r + δ := by linarith
    have hd := hdiff r δ hr hδ hrδ
    rw [← hWpowm r hr hr1, ← hWpow r hr hr1, ← hWpow (r + δ) hrδ0 hrδ] at hd
    refine alg _ _ δ w (hWpos _ hrδ0 hrδ) (hWpos r hr hr1) hδ hw0 hwb ?_
    have hδne : δ ≠ 0 := hδ.ne'
    calc δ * W r ^ m ≤ δ * (K / δ * (W (r + δ) ^ (m + 1) - W r ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left hd hδ.le
      _ = K * (W (r + δ) ^ (m + 1) - W r ^ (m + 1)) := by field_simp
  -- Step 4′: `N` steps of length `δ = ρ/(2N)` from `ρ/2`
  have hρ2 : 0 < ρ / 2 := by linarith
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ = W (ρ / 2) := ⟨_, rfl⟩
  have hw₀pos : 0 < w₀ := by rw [hw₀]; exact hWpos _ hρ2 (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) * ρ ^ 2 / (4 * (K * (m + 1)) ^ 2 * w₀ ^ 2))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ρ / (2 * N) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hNδ : (N : ℝ) * δ = ρ / 2 := by
    rw [hδ]
    field_simp
  have ind : ∀ j : ℕ, j ≤ N →
      (j : ℝ) * δ * w₀ ≤ (K * (m + 1) * w₀ + m * δ) * (W (ρ / 2 + j * δ) - w₀) := by
    intro j
    induction j with
    | zero => intro _; simp [hw₀]
    | succ j ih =>
      intro hj
      have ih' := ih (Nat.le_of_succ_le hj)
      have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      have hr : 0 < ρ / 2 + j * δ := by positivity
      have hrδ : ρ / 2 + j * δ + δ < ρ₁ := by
        have := mul_le_mul_of_nonneg_right hjN hδpos.le
        linarith
      have hcoef : 0 < K * (m + 1) * w₀ + m * δ := by positivity
      have hwb : w₀ ≤ W (ρ / 2 + j * δ) := by
        by_contra hcon
        have h1 : (K * (m + 1) * w₀ + m * δ) * (W (ρ / 2 + j * δ) - w₀) < 0 :=
          mul_neg_of_pos_of_neg hcoef (by linarith [not_le.mp hcon])
        have h2 : 0 ≤ (j : ℝ) * δ * w₀ := by positivity
        linarith
      have hs := step (ρ / 2 + j * δ) δ w₀ hr hδpos hrδ hw₀pos.le hwb
      have heq : ρ / 2 + ((j + 1 : ℕ) : ℝ) * δ = ρ / 2 + j * δ + δ := by push_cast; ring
      rw [heq]
      push_cast
      linarith
  have hfin := ind N le_rfl
  have hρN : ρ / 2 + (N : ℝ) * δ = ρ := by rw [hNδ]; ring
  rw [hρN, hNδ] at hfin
  -- `N` is large: `m δ ρ < 2 (K (m+1))² w₀²`
  have hmδ : (m : ℝ) * δ * ρ < 2 * (K * (m + 1)) ^ 2 * w₀ ^ 2 := by
    have h1 : (m : ℝ) * ρ ^ 2 < N * (4 * (K * (m + 1)) ^ 2 * w₀ ^ 2) := by
      rwa [div_lt_iff₀ (by positivity)] at hN
    have h2 : (2 * N) * ((m : ℝ) * δ * ρ) = m * ρ ^ 2 := by
      have : (2 * N) * ((m : ℝ) * δ * ρ) = 2 * m * ρ * (N * δ) := by ring
      rw [this, hNδ]; ring
    have h3 : (2 * N) * ((m : ℝ) * δ * ρ) < (2 * N) * (2 * (K * (m + 1)) ^ 2 * w₀ ^ 2) := by
      rw [h2]; linarith
    exact lt_of_mul_lt_mul_left h3 (by positivity)
  -- Steps 4′(c) and 6: `ρ/(2K(m+1)) ≤ W(ρ)`, so `(ρ/(2K(m+1)))^{m+1} ≤ W(ρ)^{m+1} = V(ρ)`
  have hA : ρ / (2 * K * (m + 1)) ≤ W ρ := by
    rw [div_le_iff₀ (by positivity)]
    by_contra hcon
    have hcoef : 0 < K * (m + 1) * w₀ + m * δ := by positivity
    have e1 := mul_lt_mul_of_pos_left (not_le.mp hcon) hcoef
    have e2 := mul_le_mul_of_nonneg_left hfin hKm.le
    have e3 : 0 ≤ K * (m + 1) * m * δ * w₀ := by positivity
    linarith
  calc (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ W ρ ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) hA (m + 1)
    _ = V ρ := hWpow ρ hρ hρ₁
/-- **Annular cut-off** (step 3 of the lower volume-density bound in De Giorgi's theorem, Simon
Ch. 3, 4.3, proof of (10)–(11)).  There is `C₀ > 0` such that for all `ρ, δ > 0` some `C¹`
function `ζ` on `ℝᴾ` has compact support in `B̄_{ρ+δ}(y)`, `0 ≤ ζ ≤ 1`, `ζ = 1` on `B̄_ρ(y)`,
`‖Dζ‖ ≤ C₀/δ`, and `Dζ = 0` off the open annulus `B_{ρ+δ}(y) \ B̄_ρ(y)`.  Take `C₀ = 3/2` and
`ζ(z) = h((‖z − y‖ − ρ)/δ)` with `h(t) = 1 − ∫₀ᵗ 6 max(0, s(1 − s)) ds` (`= 1 − 3t² + 2t³` on
`[0, 1]`): `h` is `C¹`, `1` on `(−∞, 0]`, `0` on `[1, ∞)`, `h' = 0` there and `|h'| ≤ 3/2`.  Then
`ζ` is constant near `y`, `h ∘ u` with `u` smooth away from `y`, and `(3/(2δ))`-Lipschitz by the
reverse triangle inequality. -/
theorem Submission.codim1_rdo_dg_vdl_annular_cutoff : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ C₀ / δ) ∧ ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
  -- Step 1: the profile `h(t) = 1 − ∫₀ᵗ g`, `g(s) = 6 max(0, s(1 − s))`
  obtain ⟨h, hh_C1, hh_flat, hh_bounds, hh_one, hh_zero, hh_lip⟩ : ∃ h : ℝ → ℝ,
      ContDiff ℝ 1 h ∧ (∀ t, t ≤ 0 ∨ 1 ≤ t → HasDerivAt h 0 t) ∧ (∀ t, 0 ≤ h t ∧ h t ≤ 1) ∧
      (∀ t, t ≤ 0 → h t = 1) ∧ (∀ t, 1 ≤ t → h t = 0) ∧
      ∀ a b, ‖h b - h a‖ ≤ 3 / 2 * ‖b - a‖ := by
    set g : ℝ → ℝ := fun s => 6 * max 0 (s * (1 - s)) with hg_eq
    have hg_cont : Continuous g := by fun_prop
    have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hg_cont.intervalIntegrable a b
    have hg_nonneg : ∀ s, 0 ≤ g s := fun s => mul_nonneg (by norm_num) (le_max_left _ _)
    have hg_le : ∀ s, g s ≤ 3 / 2 := fun s => by
      have h : max 0 (s * (1 - s)) ≤ 1 / 4 :=
        max_le (by norm_num) (by nlinarith [sq_nonneg (s - 1 / 2)])
      simp only [hg_eq]
      linarith
    have hg_left : ∀ s, s ≤ 0 → g s = 0 := fun s hs => by
      simp only [hg_eq]
      rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg hs (by linarith)), mul_zero]
    have hg_right : ∀ s, 1 ≤ s → g s = 0 := fun s hs => by
      simp only [hg_eq]
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)), mul_zero]
    -- `∫₀¹ g = 1`: on `[0, 1]`, `g(s) = 6s(1 − s)` is the derivative of `3s² − 2s³`
    have hg_one : ∫ s in (0 : ℝ)..1, g s = 1 := by
      have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 * s ^ 2 - 2 * s ^ 3)
          (6 * (s * (1 - s))) s := fun s => by
        convert ((hasDerivAt_pow 2 s).const_mul 3).sub ((hasDerivAt_pow 3 s).const_mul 2) using 1
        norm_num
        ring
      rw [intervalIntegral.integral_congr (g := fun s => 6 * (s * (1 - s))) ?_,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
          ((by fun_prop : Continuous fun s : ℝ => 6 * (s * (1 - s))).intervalIntegrable _ _)]
      · norm_num
      · intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        simp only [hg_eq]
        rw [max_eq_right (mul_nonneg hs.1 (by linarith [hs.2]))]
    -- the primitive `F(t) = ∫₀ᵗ g`, with `F' = g`
    set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hF_eq
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
      (hg_cont.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hF_left : ∀ t, t ≤ 0 → F t = 0 := fun t ht => by
      simp only [hF_eq]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_ge ht] at hs
        exact hg_left s hs.2
    have hF_right : ∀ t, 1 ≤ t → F t = 1 := fun t ht => by
      simp only [hF_eq]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int 0 1) (hg_int 1 t), hg_one]
      have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro s hs
          rw [uIcc_of_le ht] at hs
          exact hg_right s hs.1
      rw [h, add_zero]
    have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ 1 := fun t => by
      rcases le_total t 0 with ht | ht
      · rw [hF_left t ht]
        exact ⟨le_rfl, zero_le_one⟩
      rcases le_total 1 t with ht' | ht'
      · rw [hF_right t ht']
        exact ⟨zero_le_one, le_rfl⟩
      refine ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u, ?_⟩
      rw [← hg_one]
      exact intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg)
        (hg_int _ _)
    -- `h = 1 − F`, with `h' = −g`
    have hh_deriv : ∀ t, HasDerivAt (fun t => 1 - F t) (-g t) t := fun t =>
      (hF_deriv t).const_sub 1
    refine ⟨fun t => 1 - F t, ?_, fun t ht => ?_, fun t => ?_, fun t ht => ?_, fun t ht => ?_,
      fun a b => ?_⟩
    · rw [contDiff_one_iff_deriv]
      refine ⟨fun t => (hh_deriv t).differentiableAt, ?_⟩
      rw [show deriv (fun t => 1 - F t) = fun t => -g t from funext fun t => (hh_deriv t).deriv]
      exact hg_cont.neg
    · have hg0 : g t = 0 := ht.elim (hg_left t) (hg_right t)
      simpa [hg0] using hh_deriv t
    · obtain ⟨h₀, h₁⟩ := hF_bounds t
      exact ⟨by linarith, by linarith⟩
    · simp only [hF_left t ht, sub_zero]
    · simp only [hF_right t ht, sub_self]
    · refine convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hh_deriv t).hasDerivWithinAt) (fun t _ => ?_) (mem_univ a) (mem_univ b)
      rw [norm_neg, Real.norm_of_nonneg (hg_nonneg t)]
      exact hg_le t
  -- Step 2: `C₀ = 3/2` and `ζ(z) = h(u(z))`, `u(z) = (‖z − y‖ − ρ)/δ`
  refine ⟨3 / 2, by norm_num, fun P y ρ δ hρ hδ => ?_⟩
  -- Step 3: `ζ ≡ 1` on `B_ρ(y)`, a neighbourhood of `y`
  have hζ_near : (fun z : Euclid P => h ((‖z - y‖ - ρ) / δ)) =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds y hρ] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hh_one _ ((div_le_iff₀ hδ).2 (by linarith))
  -- `u` is smooth away from `y`
  have hu : ∀ z : Euclid P, z ≠ y → ContDiffAt ℝ 1 (fun w : Euclid P => (‖w - y‖ - ρ) / δ) z :=
    fun z hz => (((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hz)).sub
      contDiffAt_const).div_const δ
  -- Step 4: `ζ = 0` off `B_{ρ+δ}(y)`, so `tsupport ζ ⊆ closure B_{ρ+δ}(y) ⊆ B̄_{ρ+δ}(y)`
  have htsupp : tsupport (fun z : Euclid P => h ((‖z - y‖ - ρ) / δ)) ⊆ closedBall y (ρ + δ) := by
    refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro z hz
    by_contra hzb
    apply hz
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hzb
    exact hh_zero _ ((le_div_iff₀ hδ).2 (by linarith))
  refine ⟨fun z => h ((‖z - y‖ - ρ) / δ), ?_,
    (isCompact_closedBall y (ρ + δ)).of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp,
    fun z => hh_bounds _, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  -- Step 5: `ζ` is `C¹` — constant near `y`, and `h ∘ u` with `u` smooth away from `y`
  · rw [contDiff_iff_contDiffAt]
    intro z
    rcases eq_or_ne z y with rfl | hz
    · exact contDiffAt_const.congr_of_eventuallyEq hζ_near
    · exact hh_C1.contDiffAt.comp z (hu z hz)
  -- Step 3: `ζ = 1` on `B̄_ρ(y)`
  · rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hh_one _ ((div_le_iff₀ hδ).2 (by linarith))
  -- Step 6: `ζ` is `(3/(2δ))`-Lipschitz (reverse triangle inequality), so `‖Dζ(z)‖ ≤ 3/(2δ)`
  · refine norm_fderiv_le_of_lip' ℝ (by positivity) (Eventually.of_forall fun w => ?_)
    calc ‖h ((‖w - y‖ - ρ) / δ) - h ((‖z - y‖ - ρ) / δ)‖
        ≤ 3 / 2 * ‖(‖w - y‖ - ρ) / δ - (‖z - y‖ - ρ) / δ‖ := hh_lip _ _
      _ = 3 / 2 / δ * |‖w - y‖ - ‖z - y‖| := by
          rw [Real.norm_eq_abs, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ]
          ring
      _ ≤ 3 / 2 / δ * ‖(w - y) - (z - y)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = 3 / 2 / δ * ‖w - z‖ := by rw [sub_sub_sub_cancel_right]
  -- Step 7: `Dζ(z) = 0` off the open annulus
  · rcases eq_or_ne z y with rfl | hzy
    · rw [hζ_near.fderiv_eq, fderiv_const_apply]
    · -- `u(z) ≤ 0` or `u(z) ≥ 1`, where `h' = 0`; chain rule
      have hu_out : (‖z - y‖ - ρ) / δ ≤ 0 ∨ 1 ≤ (‖z - y‖ - ρ) / δ := by
        rcases le_or_gt ‖z - y‖ ρ with h₁ | h₁
        · exact Or.inl ((div_le_iff₀ hδ).2 (by linarith))
        · refine Or.inr ((le_div_iff₀ hδ).2 ?_)
          have h₂ : z ∉ ball y (ρ + δ) := fun hb => hz ⟨hb, by
            rw [Metric.mem_closedBall, dist_eq_norm, not_le]
            exact h₁⟩
          rw [Metric.mem_ball, dist_eq_norm, not_lt] at h₂
          linarith
      have hD := (hh_flat _ hu_out).comp_hasFDerivAt z
        ((hu z hzy).differentiableAt one_ne_zero).hasFDerivAt
      rw [zero_smul] at hD
      exact hD.fderiv

/-- **Finite-difference form of De Giorgi's volume estimate** (Simon Ch. 3, 4.3, the first
displays of (10); used for 7.5.8).  Let `G ⊆ ℝ^{m+1}` (`m ≥ 1`) be Borel and
`V(r) = L^{m+1}(G ∩ B̄_r(y))`.  Suppose `(∫_G ζ^{(m+1)/m})^{m/(m+1)} ≤ c (∫ ζ dμ + ∫_G |Dζ|)`
for every `C¹` function `ζ ≥ 0` with compact support in `D ⊇ B̄_{ρ₁}(y)` (`μ(B̄_{ρ₁}(y)) < ∞`), and
`δ μ(B̄_ρ(y)) ≤ C₁ L^{m+1}(G ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` whenever `ρ, δ > 0`, `ρ + δ < ρ₁`.  Then
`V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ+δ) − V(ρ))` for such `ρ, δ`, with `K = 2c(C₁ + C₀)`, `C₀` the constant
of `Submission.codim1_rdo_dg_vdl_annular_cutoff`.  Test the Sobolev inequality with that cut-off
`ζ` for the radii `ρ` and `η = δ/2`: the left side is at least `V(ρ)^{m/(m+1)}`, since `ζ = 1` on
`B̄_ρ(y)`; `∫ ζ dμ ≤ μ(B̄_{ρ+η}(y)) ≤ (C₁/η) L^{m+1}(G ∩ A₂)`, `A₂ = B_{ρ+δ}(y) \ B̄_{ρ+η}(y)`, by
the second hypothesis at radius `ρ + η`; and `∫_G |Dζ| ≤ (C₀/η) L^{m+1}(G ∩ A₁)`,
`A₁ = B_{ρ+η}(y) \ B̄_ρ(y)`.  The sets `G ∩ B̄_ρ(y)`, `G ∩ A₁` and `G ∩ A₂` are disjoint subsets of
`G ∩ B̄_{ρ+δ}(y)`. -/
theorem Submission.codim1_rdo_dg_vdl_finite_difference : ∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ K : ℝ, 0 < K ∧ ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤ K / δ * ((volume (G ∩ closedBall y (ρ + δ))).toReal - (volume (G ∩ closedBall y ρ)).toReal) := by
  intro m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ hS hA
  obtain ⟨C₀, hC₀, hcut⟩ := Submission.codim1_rdo_dg_vdl_annular_cutoff
  refine ⟨2 * c * (C₁ + C₀), mul_pos (mul_pos two_pos hc) (by linarith), ?_⟩
  intro ρ δ hρ hδ hρδ
  -- Step 0: the exponents, the half width `η = δ/2` and the two annuli `A₁`, `A₂`.
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hp : (0 : ℝ) < (m + 1 : ℝ) / m := div_pos (by positivity) hm0
  have hq : (0 : ℝ) ≤ (m : ℝ) / (m + 1) := by positivity
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = δ / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; exact half_pos hδ
  set A₁ := ball y (ρ + η) \ closedBall y ρ
  set A₂ := ball y (ρ + δ) \ closedBall y (ρ + η)
  have hA₁m : MeasurableSet A₁ := measurableSet_ball.diff measurableSet_closedBall
  have hA₂m : MeasurableSet A₂ := measurableSet_ball.diff measurableSet_closedBall
  have hA₁fin : volume A₁ ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hA₂fin : volume A₂ ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hGA₁fin : volume (G ∩ A₁) ≠ ∞ := ne_top_of_le_ne_top hA₁fin (measure_mono inter_subset_right)
  have hGA₂fin : volume (G ∩ A₂) ≠ ∞ := ne_top_of_le_ne_top hA₂fin (measure_mono inter_subset_right)
  have hGB : ∀ r : ℝ, volume (G ∩ closedBall y r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right)
  -- `∫_G 𝟙_s a dL^{m+1} = a L^{m+1}(G ∩ s)`
  have hind : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → ∀ a : ℝ,
      ∫ z in G, s.indicator (fun _ => a) z = a * (volume (G ∩ s)).toReal := by
    intro s hs a
    rw [integral_indicator_const a hs, measureReal_restrict_apply hs, smul_eq_mul, mul_comm,
      inter_comm s G, measureReal_def]
  -- Step 1: the cut-off `ζ` for the radii `ρ` and `η`; it is admissible in the Sobolev inequality.
  obtain ⟨ζ, hζC, hζc, hζsupp, hζ01, hζ1, hζgrad, hζzero⟩ := hcut (m + 1) y ρ η hρ hη
  have hsub : closedBall y (ρ + η) ⊆ closedBall y ρ₁ := closedBall_subset_closedBall (by linarith)
  have hSob := hS ζ hζC hζc (hζsupp.trans (hsub.trans hD)) fun z => (hζ01 z).1
  -- Step 2: `V(ρ) ≤ ∫_G ζ^{(m+1)/m}`, as `ζ^{(m+1)/m} ≥ 𝟙_{B̄_ρ}`.
  have hleft : (volume (G ∩ closedBall y ρ)).toReal ≤ ∫ z in G, ζ z ^ ((m + 1 : ℝ) / m) := by
    have hcont : Continuous fun z => ζ z ^ ((m + 1 : ℝ) / m) :=
      hζC.continuous.rpow_const fun _ => Or.inr hp.le
    have hcpt : HasCompactSupport fun z => ζ z ^ ((m + 1 : ℝ) / m) :=
      hζc.comp_left (g := fun t : ℝ => t ^ ((m + 1 : ℝ) / m)) (Real.zero_rpow hp.ne')
    have hint : Integrable (fun z => ζ z ^ ((m + 1 : ℝ) / m)) (volume.restrict G) :=
      (hcont.integrable_of_hasCompactSupport hcpt).integrableOn
    calc (volume (G ∩ closedBall y ρ)).toReal
        = ∫ z in G, (closedBall y ρ).indicator (fun _ => (1 : ℝ)) z := by
          rw [hind _ measurableSet_closedBall, one_mul]
      _ ≤ ∫ z in G, ζ z ^ ((m + 1 : ℝ) / m) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) hint
            (Eventually.of_forall fun z => ?_)
          · exact indicator_nonneg (fun _ _ => zero_le_one) z
          · dsimp only
            by_cases hz : z ∈ closedBall y ρ
            · rw [indicator_of_mem hz, hζ1 z hz, Real.one_rpow]
            · rw [indicator_of_notMem hz]
              exact Real.rpow_nonneg (hζ01 z).1 _
  -- Step 3: `η ∫ ζ dμ ≤ η μ(B̄_{ρ+η}) ≤ C₁ L^{m+1}(G ∩ A₂)`, by the annular bound at `ρ + η`.
  have hμfin : μ (closedBall y (ρ + η)) ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono hsub)
  have hIμ : ∫ z, ζ z ∂μ ≤ (μ (closedBall y (ρ + η))).toReal := by
    have hint : Integrable ((closedBall y (ρ + η)).indicator fun _ => (1 : ℝ)) μ :=
      (integrableOn_const hμfin).integrable_indicator measurableSet_closedBall
    calc ∫ z, ζ z ∂μ ≤ ∫ z, (closedBall y (ρ + η)).indicator (fun _ => (1 : ℝ)) z ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => (hζ01 z).1) hint
            (Eventually.of_forall fun z => ?_)
          by_cases hz : z ∈ closedBall y (ρ + η)
          · rw [indicator_of_mem hz]
            exact (hζ01 z).2
          · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport fun h => hz (hζsupp h)]
      _ = (μ (closedBall y (ρ + η))).toReal := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
            measureReal_def]
  have hAη : ENNReal.ofReal η * μ (closedBall y (ρ + η)) ≤
      ENNReal.ofReal C₁ * volume (G ∩ A₂) := by
    have h := hA (ρ + η) η (by linarith) hη (by linarith)
    rwa [show ρ + η + η = ρ + δ by linarith] at h
  have hμterm : η * ∫ z, ζ z ∂μ ≤ C₁ * (volume (G ∩ A₂)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGA₂fin) hAη
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le,
      ENNReal.toReal_ofReal hC₁] at h
    exact (mul_le_mul_of_nonneg_left hIμ hη.le).trans h
  -- Step 4: `η ∫_G |Dζ| ≤ C₀ L^{m+1}(G ∩ A₁)`, as `|Dζ| ≤ (C₀/η) 𝟙_{A₁}`.
  have hgrad : ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ C₀ / η * (volume (G ∩ A₁)).toReal := by
    have hint : Integrable (A₁.indicator fun _ => C₀ / η) (volume.restrict G) :=
      ((integrableOn_const hA₁fin).integrable_indicator hA₁m).integrableOn
    calc ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ ∫ z in G, A₁.indicator (fun _ => C₀ / η) z := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
            (Eventually.of_forall fun z => ?_)
          dsimp only
          by_cases hz : z ∈ A₁
          · rw [indicator_of_mem hz]
            exact hζgrad z
          · rw [indicator_of_notMem hz, hζzero z hz, norm_zero]
      _ = C₀ / η * (volume (G ∩ A₁)).toReal := hind A₁ hA₁m _
  have hgradterm : η * ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ C₀ * (volume (G ∩ A₁)).toReal := by
    calc η * ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ η * (C₀ / η * (volume (G ∩ A₁)).toReal) :=
          mul_le_mul_of_nonneg_left hgrad hη.le
      _ = C₀ * (volume (G ∩ A₁)).toReal := by field_simp
  -- Step 5: `G ∩ B̄_ρ`, `G ∩ A₁`, `G ∩ A₂` are disjoint subsets of `G ∩ B̄_{ρ+δ}`.
  have hpieces : (volume (G ∩ closedBall y ρ)).toReal + (volume (G ∩ A₁)).toReal +
      (volume (G ∩ A₂)).toReal ≤ (volume (G ∩ closedBall y (ρ + δ))).toReal := by
    have hd₁ : Disjoint (G ∩ closedBall y ρ) (G ∩ A₁) := by
      rw [Set.disjoint_left]
      rintro z ⟨-, hz⟩ ⟨-, -, hz'⟩
      exact hz' hz
    have hd₂ : Disjoint (G ∩ closedBall y ρ ∪ G ∩ A₁) (G ∩ A₂) := by
      rw [Set.disjoint_left]
      rintro z hz ⟨-, -, hz'⟩
      apply hz'
      rcases hz with ⟨-, hz⟩ | ⟨-, hz, -⟩
      · exact closedBall_subset_closedBall (by linarith) hz
      · exact ball_subset_closedBall hz
    have hsub' : G ∩ closedBall y ρ ∪ G ∩ A₁ ∪ G ∩ A₂ ⊆ G ∩ closedBall y (ρ + δ) := by
      rintro z ((⟨hzG, hz⟩ | ⟨hzG, hz, -⟩) | ⟨hzG, hz, -⟩)
      · exact ⟨hzG, closedBall_subset_closedBall (by linarith) hz⟩
      · exact ⟨hzG, closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)⟩
      · exact ⟨hzG, ball_subset_closedBall hz⟩
    have hle : volume (G ∩ closedBall y ρ) + volume (G ∩ A₁) + volume (G ∩ A₂) ≤
        volume (G ∩ closedBall y (ρ + δ)) := by
      rw [← measure_union hd₁ (hG.inter hA₁m), ← measure_union hd₂ (hG.inter hA₂m)]
      exact measure_mono hsub'
    rw [← ENNReal.toReal_add (hGB ρ) hGA₁fin,
      ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hGB ρ, hGA₁fin⟩) hGA₂fin]
    exact ENNReal.toReal_mono (hGB (ρ + δ)) hle
  -- Step 6: combine, with `δ = 2η` and `K = 2c(C₁ + C₀)`.
  have ha₁ : 0 ≤ (volume (G ∩ A₁)).toReal := ENNReal.toReal_nonneg
  have ha₂ : 0 ≤ (volume (G ∩ A₂)).toReal := ENNReal.toReal_nonneg
  have hlhs : (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤
      c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖) :=
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hleft hq).trans hSob
  have hann : C₁ * (volume (G ∩ A₂)).toReal + C₀ * (volume (G ∩ A₁)).toReal ≤
      (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
        (volume (G ∩ closedBall y ρ)).toReal) := by
    nlinarith [mul_nonneg hC₁ ha₁, mul_nonneg hC₀.le ha₂]
  have key : η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤
      c * (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
        (volume (G ∩ closedBall y ρ)).toReal) := by
    calc η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1))
        ≤ η * (c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) :=
          mul_le_mul_of_nonneg_left hlhs hη.le
      _ = c * (η * ∫ z, ζ z ∂μ + η * ∫ z in G, ‖fderiv ℝ ζ z‖) := by ring
      _ ≤ c * (C₁ * (volume (G ∩ A₂)).toReal + C₀ * (volume (G ∩ A₁)).toReal) :=
          mul_le_mul_of_nonneg_left (add_le_add hμterm hgradterm) hc.le
      _ ≤ c * ((C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
            (volume (G ∩ closedBall y ρ)).toReal)) :=
          mul_le_mul_of_nonneg_left hann hc.le
      _ = c * (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
            (volume (G ∩ closedBall y ρ)).toReal) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  have hδη : (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) * δ =
      2 * (η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1))) := by
    rw [hη_def]
    ring
  rw [hδη]
  linarith

/-- **One-sided volume density bound** (the lower bound (10) of Simon Ch. 3, 4.3, for a general
Borel `G`).  Under the Sobolev inequality (S) on `D ⊇ B̄_{ρ₁}(y)` and the annular bound (A), with
`μ(B̄_r(y)) ≠ 0` for `r > 0`, there is `c' > 0` with `c'ρ^{m+1} ≤ L(G ∩ B_ρ(y))` for
`0 < ρ < ρ₁`.  With `V(r) = L(G ∩ B̄_r(y))`, `finite_difference` gives
`V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ + δ) − V(ρ))`; (A) at `ρ = δ = r/2` and `μ(B̄_{r/2}(y)) ≠ 0` give
`V(r) > 0` on `(0, ρ₁)`; `discrete_growth` then gives `V(r) ≥ (r/(2K(m+1)))^{m+1}`, and
`B̄_{ρ/2}(y) ⊆ B_ρ(y)` gives the bound with `c' = (1/(4K(m+1)))^{m+1}`. -/
theorem Submission.codim1_rdo_dg_vdl_one_sided_density : ∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0) → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ c' : ℝ, 0 < c' ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ENNReal.ofReal (c' * ρ ^ (m + 1)) ≤ volume (G ∩ ball y ρ) := by
  intro m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ_fin hμ_pos hS hA
  -- Step 1: the finite-difference inequality for `V(r) = L(G ∩ B̄_r(y))`
  obtain ⟨K, hK, hdiff⟩ :=
    Submission.codim1_rdo_dg_vdl_finite_difference m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ_fin hS hA
  -- Step 2: `L(G ∩ B̄_r(y)) ≤ L(B̄_r(y)) < ∞`
  have hfin : ∀ r : ℝ, volume (G ∩ closedBall y r) ≠ ∞ := fun r =>
    ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  -- Step 3: `V > 0` on `(0, ρ₁)`, from (A) at `ρ = δ = r/2`
  have hV_pos : ∀ r : ℝ, 0 < r → r < ρ₁ → 0 < (volume (G ∩ closedBall y r)).toReal := by
    intro r hr hrρ₁
    have hA' := hA (r / 2) (r / 2) (half_pos hr) (half_pos hr) (by linarith)
    have hlhs : ENNReal.ofReal (r / 2) * μ (closedBall y (r / 2)) ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.2 (half_pos hr)) (hμ_pos _ (half_pos hr))
    have hann : volume (G ∩ (ball y (r / 2 + r / 2) \ closedBall y (r / 2))) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hA'
      exact hlhs (le_zero_iff.1 hA')
    have hsub : G ∩ (ball y (r / 2 + r / 2) \ closedBall y (r / 2)) ⊆ G ∩ closedBall y r := by
      rw [add_halves]
      exact inter_subset_inter_right _ (sdiff_subset.trans ball_subset_closedBall)
    exact ENNReal.toReal_pos (fun h0 => hann (measure_mono_null hsub h0)) (hfin r)
  -- Step 4: discrete growth, `V(r) ≥ (r/(2K(m+1)))^{m+1}` on `(0, ρ₁)`
  have hgrowth := Submission.codim1_rdo_dg_vdl_discrete_growth m K ρ₁
    (fun r => (volume (G ∩ closedBall y r)).toReal) hK hV_pos hdiff
  -- Step 5: evaluate at `ρ/2`, with `c' = (1/(4K(m+1)))^{m+1}` and `B̄_{ρ/2}(y) ⊆ B_ρ(y)`
  refine ⟨(1 / (4 * K * (m + 1))) ^ (m + 1), by positivity, fun ρ hρ hρρ₁ => ?_⟩
  have hc' : (1 / (4 * K * (m + 1))) ^ (m + 1) * ρ ^ (m + 1) =
      (ρ / 2 / (2 * K * (m + 1))) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((1 / (4 * K * (m + 1))) ^ (m + 1) * ρ ^ (m + 1))
      ≤ ENNReal.ofReal (volume (G ∩ closedBall y (ρ / 2))).toReal := by
        rw [hc']
        exact ENNReal.ofReal_le_ofReal (hgrowth (ρ / 2) (half_pos hρ) (by linarith))
    _ = volume (G ∩ closedBall y (ρ / 2)) := ENNReal.ofReal_toReal (hfin _)
    _ ≤ volume (G ∩ ball y ρ) :=
        measure_mono (inter_subset_inter_right _ (closedBall_subset_ball (half_lt_self hρ)))
/-- **The divergence of a compactly supported `C¹` vector field integrates to zero** (used for the
complement in Simon Ch. 3, 4.3 (11)): `∫ trace Dφ(z) dLᴾ(z) = 0` for `φ ∈ C¹_c(ℝᴾ; ℝᴾ)`.
For fixed `w`, the difference quotients `g_t = t⁻¹(φ(· + tw) − φ)` have integral `0` by
translation invariance of `Lᴾ`, tend to `Dφ(·)w` pointwise as `t → 0`, and for `0 < |t| ≤ 1` are
bounded by `M‖w‖ 1_{K'}`, where `M = sup ‖Dφ‖` (mean value inequality) and
`K' = cthickening ‖w‖ (spt φ)` is compact; dominated convergence gives `∫ Dφ(z)w dz = 0`.
Finally `trace Dφ(z) = Σᵢ ⟨eᵢ, Dφ(z)eᵢ⟩`, and the integral commutes with the sum and `⟨eᵢ, ·⟩`. -/
theorem Submission.codim1_rdo_dg_vdl_integral_divergence_eq_zero : ∀ (P : ℕ) (φ : Euclid P → Euclid P), ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 := by
  intro P φ hφ hsupp
  -- step 1: `Dφ` is continuous with compact support, `φ` is `M`-Lipschitz and integrable
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφc : Continuous φ := hφ.continuous
  have hDc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖fderiv ℝ φ z‖ ≤ M :=
    hDc.bounded_above_of_compact_support (hsupp.fderiv ℝ)
  have hlip : ∀ x y : Euclid P, ‖φ y - φ x‖ ≤ M * ‖y - x‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hM z)
      (mem_univ x) (mem_univ y)
  have hint : Integrable φ := hφc.integrable_of_hasCompactSupport hsupp
  -- step 2: `∫ Dφ(z) w dz = 0` for every `w`
  have key : ∀ w : Euclid P, ∫ z, fderiv ℝ φ z w = 0 := by
    intro w
    -- (a) the difference quotients `g_t` have integral zero, by translation invariance
    have ha : ∀ t : ℝ, ∫ z, t⁻¹ • (φ (z + t • w) - φ z) = 0 := fun t => by
      rw [integral_smul, integral_sub (hint.comp_add_right (t • w)) hint,
        integral_add_right_eq_self, sub_self, smul_zero]
    -- (b) `g_t(z) → Dφ(z) w` as `t → 0`, `t ≠ 0`
    have hb : ∀ z, Tendsto (fun t : ℝ => t⁻¹ • (φ (z + t • w) - φ z)) (𝓝[≠] 0)
        (𝓝 (fderiv ℝ φ z w)) := fun z => by
      have h : HasDerivAt (fun t : ℝ => φ (z + t • w)) (fderiv ℝ φ z w) 0 :=
        (hdiff z).hasFDerivAt.hasLineDerivAt w
      simpa only [zero_add, zero_smul, add_zero] using hasDerivAt_iff_tendsto_slope_zero.mp h
    -- (c) for `0 < |t| ≤ 1`, `‖g_t‖ ≤ M‖w‖ 1_{K'}` with `K' = cthickening ‖w‖ (tsupport φ)`
    have hK' : IsCompact (cthickening ‖w‖ (tsupport φ)) := hsupp.cthickening
    have h1 : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ 1 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
      simpa using ht
    have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ z, ‖t⁻¹ • (φ (z + t • w) - φ z)‖ ≤
        (cthickening ‖w‖ (tsupport φ)).indicator (fun _ => M * ‖w‖) z := by
      filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
      have ht0' : t ≠ 0 := ht0
      refine ae_of_all _ fun z => ?_
      by_cases hz : z ∈ cthickening ‖w‖ (tsupport φ)
      · rw [indicator_of_mem hz, norm_smul, norm_inv, Real.norm_eq_abs]
        calc |t|⁻¹ * ‖φ (z + t • w) - φ z‖ ≤ |t|⁻¹ * (M * ‖z + t • w - z‖) :=
              mul_le_mul_of_nonneg_left (hlip z (z + t • w)) (inv_nonneg.mpr (abs_nonneg t))
          _ = M * ‖w‖ := by
              rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_left_comm,
                inv_mul_cancel_left₀ (abs_ne_zero.mpr ht0')]
      · -- outside `K'`, both `z` and `z + t • w` lie outside `tsupport φ`, so `g_t(z) = 0`
        have hz1 : z ∉ tsupport φ := fun h => hz (self_subset_cthickening _ h)
        have hz2 : z + t • w ∉ tsupport φ := fun h => hz <|
          mem_cthickening_of_dist_le z (z + t • w) ‖w‖ _ h <| by
            rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
            exact mul_le_of_le_one_left (norm_nonneg w) ht
        rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz1,
          image_eq_zero_of_notMem_tsupport hz2, sub_self, smul_zero, norm_zero]
    have hbound_int : Integrable ((cthickening ‖w‖ (tsupport φ)).indicator fun _ => M * ‖w‖) :=
      (integrableOn_const hK'.measure_lt_top.ne).integrable_indicator hK'.measurableSet
    -- (d) dominated convergence along `t → 0`, `t ≠ 0`; all the integrals vanish by (a)
    have hd := tendsto_integral_filter_of_dominated_convergence
      (F := fun (t : ℝ) (z : Euclid P) => t⁻¹ • (φ (z + t • w) - φ z)) _
      (Eventually.of_forall fun t =>
        (show Continuous fun z => t⁻¹ • (φ (z + t • w) - φ z) by fun_prop).aestronglyMeasurable)
      hbound hbound_int (ae_of_all _ hb)
    simp only [ha] at hd
    exact tendsto_nhds_unique hd tendsto_const_nhds
  -- step 3: `trace Dφ(z) = Σᵢ ⟨eᵢ, Dφ(z) eᵢ⟩`; integrate termwise
  have htr : ∀ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) =
      ∑ i, inner ℝ (EuclideanSpace.basisFun (Fin P) ℝ i)
        (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin P) ℝ i)) := fun z => by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    rfl
  have hcomp : ∀ v : Euclid P, Integrable (fun z => fderiv ℝ φ z v) := fun v =>
    (hDc.clm_apply continuous_const).integrable_of_hasCompactSupport (hsupp.fderiv_apply ℝ v)
  simp_rw [htr]
  rw [integral_finsetSum _ fun i _ => by
    simpa only [innerSL_apply_apply] using
      (innerSL ℝ (EuclideanSpace.basisFun (Fin P) ℝ i)).integrable_comp (hcomp _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := (innerSL ℝ (EuclideanSpace.basisFun (Fin P) ℝ i)).integral_comp_comm
    (hcomp (EuclideanSpace.basisFun (Fin P) ℝ i))
  simp only [innerSL_apply_apply] at h
  rw [h, key, inner_zero_right]

/-- **Simon Ch. 3, proof of 4.3, (11)** ("repeating the same argument with `U ∖ E` in place of
`E`", l. 729–732 of the chapter text): the Gauss–Green identity for `F` with normal `ν` gives the
one for `Fᶜ` with normal `−ν`.  The divergence `trace Dφ` of a `C¹` field with compact support is
continuous with compact support, hence integrable, and has integral `0`
(`codim1_rdo_dg_vdl_integral_divergence_eq_zero`).  So
`∫_{Fᶜ} trace Dφ = −∫_F trace Dφ = ∫ ⟨φ, ν⟩ dμ = −∫ ⟨φ, −ν⟩ dμ`. -/
theorem Submission.codim1_rdo_dg_vdl_gauss_green_compl : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P), MeasurableSet F → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in Fᶜ, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (-ν z) ∂μ := by
  intro P D F μ ν hF hGG φ hφ hφc hφD
  -- Step 2: `z ↦ trace Dφ(z)` is continuous with compact support, hence integrable
  have hf_int : Integrable fun z =>
      LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) := by
    -- `A ↦ trace A` is linear on the finite-dimensional space `ℝᴾ →L[ℝ] ℝᴾ`, hence continuous
    have htr : Continuous fun A : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) :=
      (LinearMap.trace ℝ (Euclid P) ∘ₗ
        ContinuousLinearMap.coeLM ℝ).continuous_of_finiteDimensional
    exact (htr.comp (hφ.continuous_fderiv one_ne_zero)).integrable_of_hasCompactSupport
      ((hφc.fderiv ℝ).comp_left (by simp))
  -- Step 3: `∫_F trace Dφ + ∫_{Fᶜ} trace Dφ = ∫ trace Dφ = 0`
  have hsplit := integral_add_compl hF hf_int
  have hdiv : ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 :=
    Submission.codim1_rdo_dg_vdl_integral_divergence_eq_zero P φ hφ hφc
  have hF_GG := hGG φ hφ hφc hφD
  -- Step 4: `⟨φ, −ν⟩ = −⟨φ, ν⟩` and `∫ −g dμ = −∫ g dμ`
  simp only [inner_neg_right, integral_neg, neg_neg]
  linarith
/-- **Converging normal averages force positive mass on every ball** (step 2 of the lower volume
density bound in De Giorgi's argument for 7.5.8).  Let `A(ρ) = μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ`
(with `0⁻¹ = 0`).  If `A(ρ) → v ≠ 0` as `ρ ↓ 0`, then `μ(B̄_r(y)) ≠ 0` for every `r > 0`: some
`ρ ∈ (0, r)` has `A(ρ) ≠ 0`, while `μ(B̄_r(y)) = 0` would give `μ(B̄_ρ(y)) = 0` and so `A(ρ) = 0`. -/
theorem Submission.codim1_rdo_dg_vdl_measure_closedBall_ne_zero : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P), v ≠ 0 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0 := by
  intro P μ ν y v hv hlim r hr hμr
  -- Step 1: `A(ρ) → v ≠ 0`, so `A(ρ) ≠ 0` for all small `ρ > 0`
  have hA : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ ≠ 0 :=
    hlim.eventually_ne hv
  -- Step 2: pick `ρ ∈ (0, r)` with `A(ρ) ≠ 0`
  obtain ⟨ρ, hAρ, hρ⟩ := (hA.and (Ioo_mem_nhdsGT hr)).exists
  -- Step 3: `μ(B̄_ρ(y)) ≤ μ(B̄_r(y)) = 0` would force `A(ρ) = 0`
  have hμρ : μ (closedBall y ρ) = 0 := measure_mono_null (closedBall_subset_closedBall hρ.2.le) hμr
  rw [hμρ, ENNReal.toReal_zero, inv_zero, zero_smul] at hAρ
  exact hAρ rfl
/-- The `C¹` radial cut-off between `B̄_ρ(y)` and `B̄_{ρ+δ}(y)` (it replaces Simon's Lipschitz
cut-offs in Ch. 3, 4.3 (3)–(4)): `ζ = h ∘ a` with `a(z) = (|z - y| - ρ)/δ` and the clamped
smoothstep `h = p ∘ clamp_{[0,1]}`, `p(s) = 1 - 3s² + 2s³`.  As `p'(0) = p'(1) = 0`, `h` is `C¹`,
nonincreasing and `3/2`-Lipschitz, so `ζ` is `C¹`, `ζ = 1` on `B̄_ρ`, `tsupport ζ ⊆ B̄_{ρ+δ}`,
`‖Dζ‖ ≤ 3/(2δ)`, `Dζ = 0` off the open annulus (Fermat at the extrema `ζ = 0, 1`), and
`{t ≤ ζ} = B̄_{ρ+δ s_t}` with `s_t = max {s ∈ [0, 1] | t ≤ h s} < 1`. -/
theorem Submission.codim1_rdo_dg_ce_radial_cutoff : ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ)) ∧ (∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
  intro P y ρ δ hρ hδ
  -- Steps 1–3: the profile `h = p ∘ cl`, `p(s) = 1 - 3s² + 2s³`, `cl(s) = max 0 (min s 1)`
  have profile : ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Antitone h ∧ (∀ s, 0 ≤ h s ∧ h s ≤ 1) ∧
      (∀ s, s ≤ 0 → h s = 1) ∧ (∀ s, 1 ≤ s → h s = 0) ∧ LipschitzWith (3 / 2 : NNReal) h := by
    set p : ℝ → ℝ := fun s => 1 - 3 * s ^ 2 + 2 * s ^ 3 with hp_def
    set cl : ℝ → ℝ := fun s => max 0 (min s 1) with hcl_def
    set h : ℝ → ℝ := fun s => p (cl s) with hh_def
    set q : ℝ → ℝ := fun s => -6 * cl s + 6 * cl s ^ 2 with hq_def
    have hp : ∀ s, HasDerivAt p (-6 * s + 6 * s ^ 2) s := by
      intro s
      have h1 := ((hasDerivAt_pow 2 s).const_mul 3).const_sub 1
      have h2 := (hasDerivAt_pow 3 s).const_mul 2
      convert h1.add h2 using 1
      push_cast
      ring
    have hcl0 : ∀ s, s ≤ 0 → cl s = 0 := fun s hs => by
      simp only [hcl_def]; exact max_eq_left (min_le_of_left_le hs)
    have hcl1 : ∀ s, 1 ≤ s → cl s = 1 := fun s hs => by
      simp only [hcl_def]; rw [min_eq_right hs]; exact max_eq_right zero_le_one
    have hclmid : ∀ s, 0 ≤ s → s ≤ 1 → cl s = s := fun s h0 h1 => by
      simp only [hcl_def]; rw [min_eq_left h1]; exact max_eq_right h0
    have hcl01 : ∀ s, 0 ≤ cl s ∧ cl s ≤ 1 := fun s =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    -- Step 2: `h' = q = p' ∘ cl` everywhere; at `0` and `1` the one-sided derivatives agree
    have hderiv : ∀ s, HasDerivAt h (q s) s := by
      intro s
      rcases lt_trichotomy s 0 with hs | hs | hs
      · have heq : h =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
          filter_upwards [Iio_mem_nhds hs] with u hu
          simp only [hh_def, hcl0 u (le_of_lt hu), hp_def]; norm_num
        have hq0 : q s = 0 := by simp only [hq_def, hcl0 s hs.le]; norm_num
        rw [hq0]; exact (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq heq
      · subst hs
        have hq0 : q 0 = 0 := by simp only [hq_def, hcl0 0 le_rfl]; norm_num
        rw [hq0]
        have hL : HasDerivWithinAt h 0 (Iic 0) 0 := by
          refine (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (1 : ℝ)).congr (fun u hu => ?_) ?_
          · simp only [hh_def, hcl0 u hu, hp_def]; norm_num
          · simp only [hh_def, hcl0 0 le_rfl, hp_def]; norm_num
        have hR : HasDerivWithinAt h 0 (Ici 0) 0 := by
          have := (hp 0).hasDerivWithinAt (s := Ici 0)
          simp only [mul_zero, zero_pow two_ne_zero, add_zero] at this
          refine this.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ))
                (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
            simp only [hh_def, hclmid u hu.1 (le_of_lt hu.2)]
          · simp only [hh_def, hclmid 0 le_rfl zero_le_one]
        have := hL.union hR
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · rcases lt_trichotomy s 1 with hs1 | hs1 | hs1
        · have heq : h =ᶠ[𝓝 s] p := by
            filter_upwards [Ioo_mem_nhds hs hs1] with u hu
            simp only [hh_def, hclmid u hu.1.le hu.2.le]
          have hqs : q s = -6 * s + 6 * s ^ 2 := by simp only [hq_def, hclmid s hs.le hs1.le]
          rw [hqs]; exact (hp s).congr_of_eventuallyEq heq
        · subst hs1
          have hq0 : q 1 = 0 := by simp only [hq_def, hcl1 1 le_rfl]; norm_num
          rw [hq0]
          have hR : HasDerivWithinAt h 0 (Ici 1) 1 := by
            refine (hasDerivWithinAt_const (1 : ℝ) (Ici 1) (0 : ℝ)).congr (fun u hu => ?_) ?_
            · simp only [hh_def, hcl1 u hu, hp_def]; norm_num
            · simp only [hh_def, hcl1 1 le_rfl, hp_def]; norm_num
          have hL : HasDerivWithinAt h 0 (Iic 1) 1 := by
            have := (hp 1).hasDerivWithinAt (s := Iic 1)
            norm_num at this
            refine this.congr_of_eventuallyEq ?_ ?_
            · filter_upwards [inter_mem_nhdsWithin (Iic (1 : ℝ))
                  (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
              simp only [hh_def, hclmid u (le_of_lt hu.2) hu.1]
            · simp only [hh_def, hclmid 1 zero_le_one le_rfl]
          have := hL.union hR
          rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
        · have heq : h =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
            filter_upwards [Ioi_mem_nhds hs1] with u hu
            simp only [hh_def, hcl1 u (le_of_lt hu), hp_def]; norm_num
          have hq0 : q s = 0 := by simp only [hq_def, hcl1 s hs1.le]; norm_num
          rw [hq0]; exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
    -- Step 3: `h ∈ C¹`, `-3/2 ≤ h' ≤ 0`, so `h` is antitone and `3/2`-Lipschitz; `0 ≤ h ≤ 1`
    have hdiff : Differentiable ℝ h := fun s => (hderiv s).differentiableAt
    have hderiv_eq : deriv h = q := funext fun s => (hderiv s).deriv
    have hclcont : Continuous cl := by
      simp only [hcl_def]; fun_prop
    have hqcont : Continuous q := by
      simp only [hq_def]; fun_prop
    have hC1 : ContDiff ℝ 1 h := contDiff_one_iff_deriv.2 ⟨hdiff, hderiv_eq ▸ hqcont⟩
    have hq_nonpos : ∀ s, q s ≤ 0 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s; simp only [hq_def]; nlinarith
    have hq_abs : ∀ s, |q s| ≤ 3 / 2 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s
      rw [abs_of_nonpos (hq_nonpos s)]; simp only [hq_def]; nlinarith [sq_nonneg (cl s - 1 / 2)]
    have hanti : Antitone h := antitone_of_deriv_nonpos hdiff fun s => hderiv_eq ▸ hq_nonpos s
    refine ⟨h, hC1, hanti, ?_, ?_, ?_, ?_⟩
    · intro s; obtain ⟨h0, h1⟩ := hcl01 s
      simp only [hh_def, hp_def]
      have e1 : 1 - 3 * cl s ^ 2 + 2 * cl s ^ 3 = (1 - cl s) ^ 2 * (1 + 2 * cl s) := by ring
      constructor
      · rw [e1]; exact mul_nonneg (sq_nonneg _) (by linarith)
      · nlinarith [mul_nonneg (sq_nonneg (cl s)) (by linarith : (0 : ℝ) ≤ 3 - 2 * cl s)]
    · intro s hs; simp only [hh_def, hcl0 s hs, hp_def]; norm_num
    · intro s hs; simp only [hh_def, hcl1 s hs, hp_def]; norm_num
    · refine lipschitzWith_of_nnnorm_deriv_le hdiff fun s => ?_
      rw [hderiv_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
      simpa using hq_abs s
  obtain ⟨h, hC1, hanti, h01, h0, h1, hlip⟩ := profile
  -- Step 4: `ζ = h ∘ a`, `a(z) = (|z - y| - ρ)/δ`; `ζ = 1` on `B̄_ρ` and `ζ = 0` off `B_{ρ+δ}`
  set a : Euclid P → ℝ := fun z => (‖z - y‖ - ρ) / δ with ha_def
  set ζ : Euclid P → ℝ := fun z => h (a z) with hζ_def
  have hζ1 : ∀ z ∈ closedBall y ρ, ζ z = 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    exact h0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hζ0 : ∀ z, ρ + δ ≤ ‖z - y‖ → ζ z = 0 := by
    intro z hz
    refine h1 _ ?_
    rw [ha_def, le_div_iff₀ hδ]; linarith
  have hsupp : support ζ ⊆ ball y (ρ + δ) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    by_contra hcon
    exact hz (hζ0 z (not_lt.1 hcon))
  have htsupp : tsupport ζ ⊆ closedBall y (ρ + δ) :=
    closure_minimal (hsupp.trans ball_subset_closedBall) isClosed_closedBall
  have hcomp : HasCompactSupport ζ :=
    HasCompactSupport.intro (isCompact_closedBall y (ρ + δ)) fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz (htsupp h'))
  -- Step 5: `ζ` is `C¹`: constant near points of `B_ρ`, a `C¹` composite where `z ≠ y`
  have hC1ζ : ContDiff ℝ 1 ζ := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : ‖z - y‖ < ρ
    · have heq : ζ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        have hmem : ball y ρ ∈ 𝓝 z :=
          isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; exact hz)
        filter_upwards [hmem] with u hu
        exact hζ1 u (ball_subset_closedBall hu)
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · have hzy : z - y ≠ 0 := by
        intro h0'; rw [h0', norm_zero] at hz; exact hz hρ
      have hn : ContDiffAt ℝ 1 (fun u : Euclid P => ‖u - y‖) z :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ hzy
      have ha' : ContDiffAt ℝ 1 a z := (hn.sub contDiffAt_const).div_const δ
      exact hC1.contDiffAt.comp z ha'
  -- Step 6: `ζ` is `3/(2δ)`-Lipschitz, hence `‖Dζ‖ ≤ 3/(2δ)`
  have hlipζ : LipschitzWith (Real.toNNReal (3 / (2 * δ))) ζ := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    have h1' := hlip.dist_le_mul (a z) (a w)
    have h2' : dist (a z) (a w) ≤ dist z w / δ := by
      rw [Real.dist_eq, ha_def]
      simp only
      rw [← sub_div, abs_div, abs_of_pos hδ, dist_eq_norm]
      gcongr
      calc |‖z - y‖ - ρ - (‖w - y‖ - ρ)| = |‖z - y‖ - ‖w - y‖| := by ring_nf
        _ ≤ ‖(z - y) - (w - y)‖ := abs_norm_sub_norm_le _ _
        _ = ‖z - w‖ := by abel_nf
    rw [Real.coe_toNNReal _ (by positivity)]
    calc dist (ζ z) (ζ w) ≤ (3 / 2 : NNReal) * dist (a z) (a w) := h1'
      _ ≤ (3 / 2 : ℝ) * (dist z w / δ) := by
          push_cast; gcongr
      _ = 3 / (2 * δ) * dist z w := by field_simp
  have hgrad : ∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ) := by
    intro z
    have := norm_fderiv_le_of_lipschitz ℝ hlipζ (x₀ := z)
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  -- Step 7: `Dζ = 0` off the open annulus (Fermat at the extrema `ζ = 0` and `ζ = 1`)
  have hζle : ∀ z, ζ z ≤ 1 := fun z => (h01 _).2
  have hζge : ∀ z, 0 ≤ ζ z := fun z => (h01 _).1
  have hzero : ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
    intro z hz
    rw [Set.mem_sdiff, not_and_or, not_not] at hz
    rcases hz with hz | hz
    · rw [mem_ball, dist_eq_norm, not_lt] at hz
      have hmin : IsLocalMin ζ z := Eventually.of_forall fun u => by rw [hζ0 z hz]; exact hζge u
      exact hmin.fderiv_eq_zero
    · have hmax : IsLocalMax ζ z := Eventually.of_forall fun u => by rw [hζ1 z hz]; exact hζle u
      exact hmax.fderiv_eq_zero
  -- Step 8: `{t ≤ ζ} = B̄_{ρ+δ s_t}` with `s_t = sup M`, `M = {s ∈ [0, 1] | t ≤ h s}` compact
  have hlevel : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
    intro t ht0 ht1
    set M : Set ℝ := Icc 0 1 ∩ h ⁻¹' Ici t with hM
    have hMc : IsCompact M :=
      isCompact_Icc.inter_right (isClosed_Ici.preimage hC1.continuous)
    have hM0 : (0 : ℝ) ∈ M := ⟨⟨le_rfl, zero_le_one⟩, by simp [h0 0 le_rfl, ht1]⟩
    set st := sSup M with hst
    have hstM : st ∈ M := hMc.sSup_mem ⟨0, hM0⟩
    have hst0 : 0 ≤ st := hstM.1.1
    have hst1 : st < 1 := by
      rcases hstM.1.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have := hstM.2; rw [heq, mem_preimage, mem_Ici, h1 1 le_rfl] at this; linarith
    have hiff : ∀ u : ℝ, t ≤ h u ↔ u ≤ st := by
      intro u
      constructor
      · intro hu
        by_contra hcon
        push Not at hcon
        rcases le_or_gt u 1 with hu1 | hu1
        · have huM : u ∈ M := ⟨⟨hst0.trans hcon.le, hu1⟩, hu⟩
          exact absurd (le_csSup hMc.bddAbove huM) (not_le.2 hcon)
        · rw [h1 u hu1.le] at hu; linarith
      · intro hu
        exact le_trans hstM.2 (hanti hu)
    refine ⟨ρ + δ * st, by nlinarith, by nlinarith, ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq, mem_closedBall, dist_eq_norm, hζ_def]
    rw [hiff, ha_def, div_le_iff₀ hδ]
    constructor <;> intro hh <;> linarith
  exact ⟨ζ, hC1ζ, hcomp, fun z => h01 _, hζ1, htsupp, hgrad, hzero, hlevel⟩
/-- **Signed layer cake** (Simon Ch. 3, 4.3 (4)–(5), the limit procedure of the De Giorgi cut-off
estimates): let `0 ≤ ζ ≤ 1` vanish off `S`, `μ(S) < ∞`, `ζ = 1` on `B`, `|g| ≤ 1` and `c ≥ 0`.  If
`c μ({ζ ≥ t}) ≤ ∫_{ζ ≥ t} g dμ` for every `t ∈ (0, 1]`, then `c μ(B) ≤ ∫ ζ g dμ`.

Proof sketch:
* `ζ(x) g(x) = ∫_{(0,1]} H(x, t) dt` with `H(x, t) = 1{t ≤ ζ(x)} g(x)`; `H` is bounded and
  measurable on the finite product `μ⌞S ⊗ λ⌞(0, 1]`, so Fubini swaps the two integrals.
* For `t ∈ (0, 1]`, `B ⊆ {ζ ≥ t} ⊆ S`, so `∫ H(·, t) dμ⌞S = ∫_{ζ ≥ t} g dμ ≥ c μ({ζ ≥ t}) ≥ c μ(B)`;
  integrating over `(0, 1]` concludes. -/
theorem Submission.codim1_rdo_dg_ce_signed_layer_cake : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (ζ g : X → ℝ) (S B : Set X) (c : ℝ), Measurable ζ → Measurable g → (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) → (∀ x, |g x| ≤ 1) → MeasurableSet S → μ S ≠ ∞ → (∀ x, x ∉ S → ζ x = 0) → (∀ x ∈ B, ζ x = 1) → 0 ≤ c → (∀ t : ℝ, 0 < t → t ≤ 1 → c * (μ {x | t ≤ ζ x}).toReal ≤ ∫ x in {x | t ≤ ζ x}, g x ∂μ) → c * (μ B).toReal ≤ ∫ x, ζ x * g x ∂μ := by
  intro X _ μ ζ g S B c hζ hg hζ01 hg1 hS hSfin hζS hζB hc hlev
  -- the finite measures `μ⌞S` and `λ⌞(0, 1]`
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by simp)
  -- for `t ∈ (0, 1]`, `B ⊆ {ζ ≥ t} ⊆ S`
  have hLS : ∀ t : ℝ, 0 < t → {x | t ≤ ζ x} ⊆ S := fun t ht x hx => by
    by_contra hxS
    have hx' : t ≤ ζ x := hx
    rw [hζS x hxS] at hx'
    linarith
  have hBL : ∀ t : ℝ, t ≤ 1 → B ⊆ {x | t ≤ ζ x} := fun t ht x hx => by
    show t ≤ ζ x
    rw [hζB x hx]
    exact ht
  -- the layer-cake integrand `H(x, t) = 1{t ≤ ζ(x)} g(x)` is integrable on `μ⌞S ⊗ λ⌞(0, 1]`
  set H : X → ℝ → ℝ := fun x t => if t ≤ ζ x then g x else 0 with hH
  have hHmeas : Measurable (uncurry H) :=
    Measurable.ite (measurableSet_le measurable_snd (hζ.comp measurable_fst))
      (hg.comp measurable_fst) measurable_const
  have hHint : Integrable (uncurry H) ((μ.restrict S).prod ν) := by
    refine Integrable.of_bound hHmeas.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    simp only [uncurry, hH]
    split_ifs
    · simpa [Real.norm_eq_abs] using hg1 p.1
    · simp
  -- inner integral in `t`: `∫_{(0,1]} H(x, t) dt = λ((0, ζ(x)]) g(x) = ζ(x) g(x)`
  have hinner : ∀ x, ∫ t, H x t ∂ν = ζ x * g x := by
    intro x
    have : (fun t => H x t) = (Iic (ζ x)).indicator (fun _ => g x) := by
      funext t; simp [hH, indicator_apply, mem_Iic]
    rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, hν, Measure.real,
      Measure.restrict_apply measurableSet_Iic]
    have hset : Iic (ζ x) ∩ Ioc (0 : ℝ) 1 = Ioc 0 (ζ x) := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.trans (hζ01 x).2⟩
    rw [hset, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (hζ01 x).1]
  -- `ζ g` vanishes off `S`, so `∫ ζ g dμ = ∫∫ H dt dμ⌞S`
  have hleft : ∫ x, ζ x * g x ∂μ = ∫ x, ∫ t, H x t ∂ν ∂(μ.restrict S) := by
    simp_rw [hinner]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hζS x hx]
  -- for `t ∈ (0, 1]`: `∫ H(·, t) dμ⌞S = ∫_{ζ ≥ t} g dμ ≥ c μ({ζ ≥ t}) ≥ c μ(B)`
  have hlow : ∀ t ∈ Ioc (0 : ℝ) 1, c * (μ B).toReal ≤ ∫ x, H x t ∂(μ.restrict S) := by
    intro t ht
    have hLmeas : MeasurableSet {x | t ≤ ζ x} := measurableSet_le measurable_const hζ
    have : (fun x => H x t) = {x | t ≤ ζ x}.indicator g := by
      funext x; simp [hH, indicator_apply]
    rw [this, integral_indicator hLmeas, Measure.restrict_restrict hLmeas,
      inter_eq_left.2 (hLS t ht.1)]
    refine le_trans ?_ (hlev t ht.1 ht.2)
    have hLfin : μ {x | t ≤ ζ x} ≠ ∞ := ne_top_of_le_ne_top hSfin (measure_mono (hLS t ht.1))
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hLfin (measure_mono (hBL t ht.2))) hc
  have hint_t : Integrable (fun t => ∫ x, H x t ∂(μ.restrict S)) ν := hHint.integral_prod_right
  calc c * (μ B).toReal = ∫ t, c * (μ B).toReal ∂ν := by
        simp [hν, Measure.real]
    _ ≤ ∫ t, ∫ x, H x t ∂(μ.restrict S) ∂ν := by
        refine integral_mono_ae (integrable_const _) hint_t ?_
        rw [hν, EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall hlow
    _ = ∫ x, ∫ t, H x t ∂ν ∂(μ.restrict S) := (integral_integral_swap hHint).symm
    _ = ∫ x, ζ x * g x ∂μ := hleft.symm
/-- The divergence theorem for compactly supported fields (step 6 of the cut-off estimates in the
De Giorgi argument, cf. Simon Ch. 3, 4.3): if `φ : ℝᴾ → ℝᴾ` is `C¹` with compact support, then
`div φ = trace Dφ = ∑ᵢ ∂ᵢφⁱ` is integrable and `∫ div φ dLᴾ = ∑ᵢ ∫ ∂ᵢφⁱ dLᴾ = 0`. -/
theorem Submission.codim1_rdo_dg_ce_integral_div_eq_zero : ∀ (P : ℕ) (φ : Euclid P → Euclid P), ContDiff ℝ 1 φ → HasCompactSupport φ → Integrable (fun z => LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P)) ∧ ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 := by
  intro P φ hφ hφc
  set b := EuclideanSpace.basisFun (Fin P) ℝ with hb
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- the coordinate functions `φⁱ = ⟪bᵢ, φ⟫` are `C¹` with compact support
  set f : Fin P → Euclid P → ℝ := fun i w => innerSL ℝ (b i) (φ w) with hf
  have hfC : ∀ i, ContDiff ℝ 1 (f i) := fun i => (innerSL ℝ (b i)).contDiff.comp hφ
  have hfcs : ∀ i, HasCompactSupport (f i) := fun i => hφc.comp_left (map_zero _)
  have hfder : ∀ i z, fderiv ℝ (f i) z = (innerSL ℝ (b i)).comp (fderiv ℝ φ z) := by
    intro i z
    exact ((innerSL ℝ (b i)).hasFDerivAt.comp z (hdiff z).hasFDerivAt).fderiv
  -- `trace Dφ(z) = ∑ᵢ ⟪bᵢ, Dφ(z) bᵢ⟫ = ∑ᵢ ∂ᵢφⁱ(z)`
  have hcoord : ∀ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) =
      ∑ i, fderiv ℝ (f i) z (b i) := by
    intro z
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfder]
    simp [innerSL_apply_apply]
  -- each `∂ᵢφⁱ` is continuous and vanishes off `tsupport φⁱ`, hence integrable
  have hint_i : ∀ i, Integrable (fun z => fderiv ℝ (f i) z (b i)) := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hfC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    · refine (hfcs i).mono' ?_
      intro z hz
      refine support_fderiv_subset ℝ ?_
      intro h0
      exact hz (by simp [h0])
  -- `∫ ∂ᵢφⁱ = 0`: integrate by parts against the constant function `1`
  have hzero_i : ∀ i, ∫ z, fderiv ℝ (f i) z (b i) = 0 := by
    intro i
    obtain ⟨C, hC⟩ := (hfC i).lipschitzWith_of_hasCompactSupport (hfcs i) one_ne_zero
    have h1 := (LipschitzWith.const (1 : ℝ) : LipschitzWith 0 (fun _ : Euclid P => (1 : ℝ))).integral_lineDeriv_mul_eq
      (μ := (volume : Measure (Euclid P))) hC (hfcs i) (b i)
    have hl : ∀ x, lineDeriv ℝ (f i) x (-b i) = -fderiv ℝ (f i) x (b i) := by
      intro x
      rw [(((hfC i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
    have hc : ∀ x, lineDeriv ℝ (fun _ : Euclid P => (1 : ℝ)) x (b i) = 0 := by
      intro x
      simp [lineDeriv]
    simp only [hc, zero_mul, integral_zero, mul_one, hl, integral_neg] at h1
    linarith
  have hint : Integrable (fun z => LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P)) := by
    simp_rw [hcoord]
    exact integrable_finsetSum _ fun i _ => hint_i i
  refine ⟨hint, ?_⟩
  simp_rw [hcoord]
  rw [integral_finsetSum _ fun i _ => hint_i i]
  exact Finset.sum_eq_zero fun i _ => hzero_i i
/-- **Normal averages close to a unit vector** (quantitative form of Simon Ch. 3, 4.3 (1)).  Let
`μ(B̄_{ρ₀}(y)) < ∞`, `ν` be measurable with `|ν| ≤ 1`, `|v| = 1`, and
`A(ρ) := μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ → v` as `ρ ↓ 0`.  Then for some `ρ₂ ∈ (0, ρ₀]`,
`∫_{B̄_r(y)} ⟨ν, v⟩ dμ ≥ ½ μ(B̄_r(y))` whenever `0 < r < ρ₂`.  Since `⟨A(r), v⟩ → |v|² = 1`, we have
`⟨A(r), v⟩ > ½` for `r ∈ (0, ε)`; take `ρ₂ = min ε ρ₀`.  For `0 < r < ρ₂`, `ν` is integrable on
`B̄_r(y)` (bounded, finite measure), so `∫⟨ν, v⟩ = ⟨∫ν, v⟩`.  Either `μ(B̄_r(y)) = 0` and both sides
vanish, or `∫ν = μ(B̄_r(y)) A(r)` and `∫⟨ν, v⟩ = μ(B̄_r(y)) ⟨A(r), v⟩ ≥ ½ μ(B̄_r(y))`. -/
theorem Submission.codim1_rdo_dg_ce_normal_average_lower : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₀ : ℝ), 0 < ρ₀ → μ (closedBall y ρ₀) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ρ₂ ≤ ρ₀ ∧ ∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ := by
  intro P μ ν y v ρ₀ hρ₀ hfin hν hν1 hv hT
  -- step 1: `⟨A(ρ), v⟩ → ⟨v, v⟩ = 1`, so `⟨A(ρ), v⟩ > ½` for `ρ ∈ (0, ε)`
  have hT' : Tendsto (fun ρ : ℝ => inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v) (𝓝[>] 0) (𝓝 (inner ℝ v v)) :=
    hT.inner tendsto_const_nhds
  rw [real_inner_self_eq_norm_sq, hv, one_pow] at hT'
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hT'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  -- step 2: `ρ₂ = min ε ρ₀`; for `r < ρ₂`, `μ(B̄_r(y)) ≤ μ(B̄_{ρ₀}(y)) < ∞`
  refine ⟨min ε ρ₀, lt_min hε hρ₀, min_le_right _ _, fun r hr hr₂ => ?_⟩
  have hkey : (1 / 2 : ℝ) < inner ℝ ((μ (closedBall y r)).toReal⁻¹ •
      ∫ z in closedBall y r, ν z ∂μ) v :=
    hεsub ⟨hr, hr₂.trans_le (min_le_left _ _)⟩
  have hBfin : μ (closedBall y r) ≠ ∞ := ne_top_of_le_ne_top hfin
    (measure_mono (closedBall_subset_closedBall (hr₂.trans_le (min_le_right _ _)).le))
  -- step 3: `ν` is integrable on `B̄_r(y)`, and `∫⟨ν, v⟩ = ⟨∫ν, v⟩`
  have hint : IntegrableOn ν (closedBall y r) μ :=
    Measure.integrableOn_of_bounded hBfin hν.aestronglyMeasurable (Eventually.of_forall hν1)
  have hcomm : ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ =
      inner ℝ (∫ z in closedBall y r, ν z ∂μ) v := by
    simpa only [innerSL_apply_apply, real_inner_comm v] using
      (innerSL ℝ v).integral_comp_comm hint
  -- step 4: if `μ(B̄_r(y)) = 0`, both sides vanish
  by_cases hμ0 : μ (closedBall y r) = 0
  · rw [hμ0, ENNReal.toReal_zero, mul_zero, setIntegral_measure_zero _ hμ0]
  -- step 5: otherwise `∫ν = a A(r)` with `a = μ(B̄_r(y)) > 0`, so `∫⟨ν, v⟩ = a ⟨A(r), v⟩ ≥ a / 2`
  have hpos : 0 < (μ (closedBall y r)).toReal := ENNReal.toReal_pos hμ0 hBfin
  have hI : ∫ z in closedBall y r, ν z ∂μ = (μ (closedBall y r)).toReal •
      ((μ (closedBall y r)).toReal⁻¹ • ∫ z in closedBall y r, ν z ∂μ) := by
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [hcomm, hI, real_inner_smul_left]
  nlinarith

/-- Annular bound behind De Giorgi's cut-off estimates (Simon Ch. 3, 4.3 (3)–(6), in
finite-difference form, as used for 7.5.8).  Suppose `F` satisfies the Gauss–Green identity
`∫_F div φ dLᴾ = -∫ ⟨φ, ν⟩ dμ` for `C¹` fields `φ` with compact support in `D ⊇ B̄_{ρ₂}(y)`
(`|ν| ≤ 1`, `μ(B̄_{ρ₂}(y)) < ∞`), and `½ μ(B̄_r(y)) ≤ ∫_{B̄_r(y)} ⟨ν, v⟩ dμ` for `0 < r < ρ₂`
(`|v| ≤ 1`).  Then `δ μ(B̄_ρ(y)) ≤ 3 Lᴾ(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` whenever `ρ, δ > 0` and
`ρ + δ < ρ₂`.  Test the identity with `φ = ζ v`, `ζ` the radial cut-off
`Submission.codim1_rdo_dg_ce_radial_cutoff`: `div φ = Dζ v` vanishes off the annulus and is
bounded by `3/(2δ)`, while the signed layer-cake formula
`Submission.codim1_rdo_dg_ce_signed_layer_cake` over the superlevel balls `{ζ ≥ t} = B̄_r(y)`
gives `∫ ζ ⟨v, ν⟩ dμ ≥ ½ μ(B̄_ρ(y))`. -/
theorem Submission.codim1_rdo_dg_ce_annular_bound : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₂ : ℝ), MeasurableSet F → closedBall y ρ₂ ⊆ D → μ (closedBall y ρ₂) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ ≤ 1 → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → (∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ) → ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₂ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) := by
  intro P D F μ ν y v ρ₂ _hF hD hfin hν hν1 hv hGG h1' ρ δ hρ hδ hρδ
  set A := ball y (ρ + δ) \ closedBall y ρ
  -- Step 1: `μ(B̄_ρ) ≤ μ(B̄_{ρ+δ}) ≤ μ(B̄_{ρ₂}) < ∞` and `Lᴾ(F ∩ A) ≤ Lᴾ(B_{ρ+δ}) < ∞`.
  have hSsub : closedBall y (ρ + δ) ⊆ closedBall y ρ₂ := closedBall_subset_closedBall hρδ.le
  have hSfin : μ (closedBall y (ρ + δ)) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hSsub)
  have hBfin : μ (closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hSfin (measure_mono (closedBall_subset_closedBall (by linarith)))
  have hAmeas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hAfin : volume A ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hFAfin : volume (F ∩ A) ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono inter_subset_right)
  -- Step 2: the radial cut-off `ζ`, `= 1` on `B̄_ρ`, supported in `B̄_{ρ+δ}`, `|Dζ| ≤ 3/(2δ)`.
  obtain ⟨ζ, hζC, hζc, hζ01, hζ1, hζsupp, hζgrad, hζzero, hζlevel⟩ :=
    Submission.codim1_rdo_dg_ce_radial_cutoff P y ρ δ hρ hδ
  -- Step 3: Gauss–Green for `φ = ζ v`, whose divergence is the trace `Dζ v` of the rank-one
  -- map `Dφ = Dζ ⊗ v`: `∫ ζ ⟨v, ν⟩ dμ = -∫_F Dζ v dLᴾ`.
  have hφD : tsupport (fun z => ζ z • v) ⊆ D :=
    (tsupport_smul_subset_left _ _).trans (hζsupp.trans (hSsub.trans hD))
  have htrace : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (fun z => ζ z • v) z : Euclid P →ₗ[ℝ] Euclid P) = fderiv ℝ ζ z v := by
    intro z
    rw [fderiv_smul_const ((hζC.differentiable one_ne_zero) z) v]
    exact LinearMap.trace_smulRight _ _
  have hGGζ : ∫ z, ζ z * inner ℝ v (ν z) ∂μ = -∫ z in F, fderiv ℝ ζ z v := by
    have h := hGG (fun z => ζ z • v) (hζC.smul contDiff_const) hζc.smul_right hφD
    simp only [htrace, real_inner_smul_left] at h
    rw [h, neg_neg]
  -- Step 4: `|Dζ v| ≤ (3/(2δ)) 𝟙_A`, so `-∫_F Dζ v dLᴾ ≤ (3/(2δ)) Lᴾ(F ∩ A)`.
  have hpt : ∀ z, ‖fderiv ℝ ζ z v‖ ≤ A.indicator (fun _ => 3 / (2 * δ)) z := by
    intro z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      calc ‖fderiv ℝ ζ z v‖ ≤ ‖fderiv ℝ ζ z‖ * ‖v‖ := (fderiv ℝ ζ z).le_opNorm v
        _ ≤ 3 / (2 * δ) * 1 := mul_le_mul (hζgrad z) hv (norm_nonneg _) (by positivity)
        _ = 3 / (2 * δ) := mul_one _
    · rw [indicator_of_notMem hz, hζzero z hz]
      simp
  have hup : -∫ z in F, fderiv ℝ ζ z v ≤ 3 / (2 * δ) * (volume (F ∩ A)).toReal := by
    have hint : Integrable (A.indicator (fun _ => 3 / (2 * δ))) (volume.restrict F) :=
      ((integrableOn_const hAfin).integrable_indicator hAmeas).restrict
    have heq : ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z =
        3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      rw [integral_indicator_const _ hAmeas, smul_eq_mul, mul_comm]
      congr 1
      simp only [Measure.real, Measure.restrict_apply hAmeas, inter_comm]
    calc -∫ z in F, fderiv ℝ ζ z v ≤ ‖∫ z in F, fderiv ℝ ζ z v‖ := by
          rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = 3 / (2 * δ) * (volume (F ∩ A)).toReal := heq
  -- Step 5: the signed layer-cake formula with `g = ⟨v, ν⟩`, `S = B̄_{ρ+δ}`, `B = B̄_ρ`, `c = ½`;
  -- each `{ζ ≥ t} = B̄_r` has `0 < ρ ≤ r < ρ + δ < ρ₂`, where `(1′)` applies.
  have hg : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hν
  have hlow : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤ ∫ z, ζ z * inner ℝ v (ν z) ∂μ := by
    refine Submission.codim1_rdo_dg_ce_signed_layer_cake (Euclid P) μ ζ (fun z => inner ℝ v (ν z))
      (closedBall y (ρ + δ)) (closedBall y ρ) (1 / 2) hζC.continuous.measurable hg hζ01 ?_
      measurableSet_closedBall hSfin ?_ hζ1 (by norm_num) ?_
    · intro z
      calc |inner ℝ v (ν z)| ≤ ‖v‖ * ‖ν z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul hv (hν1 z) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · intro z hz
      exact image_eq_zero_of_notMem_tsupport (fun h => hz (hζsupp h))
    · intro t ht0 ht1
      obtain ⟨r, hr1, hr2, hrset⟩ := hζlevel t ht0 ht1
      rw [hrset]
      simpa only [real_inner_comm] using h1' r (by linarith) (by linarith)
  -- Step 6: `½ μ(B̄_ρ) ≤ (3/(2δ)) Lᴾ(F ∩ A)`; multiply by `2δ > 0`.
  have hreal : δ * (μ (closedBall y ρ)).toReal ≤ 3 * (volume (F ∩ A)).toReal := by
    have key : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤
        3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      linarith
    have h3 : 3 / (2 * δ) * (volume (F ∩ A)).toReal * (2 * δ) = 3 * (volume (F ∩ A)).toReal := by
      field_simp
    nlinarith [key, hδ]
  -- Step 7: back to `[0, ∞]`, both measures being finite by step 1.
  calc ENNReal.ofReal δ * μ (closedBall y ρ)
      = ENNReal.ofReal (δ * (μ (closedBall y ρ)).toReal) := by
        rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hBfin]
    _ ≤ ENNReal.ofReal (3 * (volume (F ∩ A)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 3 * volume (F ∩ A) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hFAfin]

/-- **Cut-off estimates** of Simon Ch. 3, proof of Theorem 4.3, (1) and (3)–(6), in
finite-difference form, at a point `y` where the normal averages of the Gauss–Green measure `μ`
tend to a unit vector `v`.  `codim1_rdo_dg_ce_normal_average_lower` gives `0 < ρ₂ ≤ ρ₀`, with
`B̄_{ρ₀}(y) ⊆ D`, such that `½ μ(B̄_r(y)) ≤ ∫_{B̄_r(y)} ⟨ν, v⟩ dμ` for `0 < r < ρ₂` (printed (1)).
`codim1_rdo_dg_ce_annular_bound` (the cut-off and layer-cake argument of (3)–(5)) then gives
`δ μ(B̄_ρ(y)) ≤ 3 L(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` for `ρ + δ < ρ₂`.  Since `∫ div φ = 0`
(`codim1_rdo_dg_ce_integral_div_eq_zero`), `Fᶜ` satisfies the Gauss–Green identity with `−ν`, and
`(−ν, −v)` satisfies the same lower bound, so the annular bound also holds for `Fᶜ`.  Taking
`δ = ρ` and `L(B_{2ρ}(y)) = (2ρ)^{m+1} ω_{m+1}` gives `μ(B̄_ρ(y)) ≤ 3·2^{m+1} ω_{m+1} ρ^m`
(printed (6)).  Finally `ρ₁ = ρ₂/2` and `C = max(3, 3·2^{m+1} ω_{m+1})`. -/
theorem Submission.codim1_rdo_dg_cutoff_estimates : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → y ∈ D → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ ρ₁ C : ℝ, 0 < ρ₁ ∧ 0 ≤ C ∧ closedBall y ρ₁ ⊆ D ∧ (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) ∧ ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C * volume ((ball y (ρ + δ) \ closedBall y ρ) \ F)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ m) := by
  intro m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 1: a radius `ρ₀` with `B̄_{ρ₀}(y) ⊆ D`, and `ρ₂ ≤ ρ₀` below which (1′) holds
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD y hy
  have hρ₀D : closedBall y (ε / 2) ⊆ D := (closedBall_subset_ball (half_lt_self hε)).trans hεD
  have hρ₀fin : μ (closedBall y (ε / 2)) ≠ ∞ := hμK _ (isCompact_closedBall y _) hρ₀D
  obtain ⟨ρ₂, hρ₂pos, hρ₂le, h1'⟩ := Submission.codim1_rdo_dg_ce_normal_average_lower (m + 1) μ ν
    y v (ε / 2) (half_pos hε) hρ₀fin hν (fun z => (hν1 z).le) hv hT
  have hρ₂D : closedBall y ρ₂ ⊆ D := (closedBall_subset_closedBall hρ₂le).trans hρ₀D
  have hρ₂fin : μ (closedBall y ρ₂) ≠ ∞ := hμK _ (isCompact_closedBall y _) hρ₂D
  -- steps 2–5: the annular bound for `F`
  have hA1 := Submission.codim1_rdo_dg_ce_annular_bound (m + 1) D F μ ν y v ρ₂ hF hρ₂D hρ₂fin hν
    (fun z => (hν1 z).le) hv.le hGG h1'
  -- step 6: `Fᶜ` satisfies (GG) with `−ν` because `∫ div φ = 0`, and (1′) holds for `(−ν, −v)`,
  -- so the annular bound also holds for `Fᶜ`
  have hGGc : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ D → ∫ z in Fᶜ, LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (-ν z) ∂μ := by
    intro φ hφ hφc hφD
    obtain ⟨hint, hzero⟩ := Submission.codim1_rdo_dg_ce_integral_div_eq_zero (m + 1) φ hφ hφc
    have hsplit := integral_add_compl hF hint
    rw [hzero, hGG φ hφ hφc hφD] at hsplit
    simp only [inner_neg_right, integral_neg, neg_neg]
    linarith
  have h1'c : ∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤
      ∫ z in closedBall y r, inner ℝ (-ν z) (-v) ∂μ := by
    intro r hr hr2
    simpa only [inner_neg_neg] using h1' r hr hr2
  have hA2 := Submission.codim1_rdo_dg_ce_annular_bound (m + 1) D Fᶜ μ (fun z => -ν z) y (-v) ρ₂
    hF.compl hρ₂D hρ₂fin hν.neg (fun z => by simpa using (hν1 z).le) (by simpa using hv.le) hGGc
    h1'c
  -- step 8: `ρ₁ = ρ₂/2` and `C = max(3, 3·2^{m+1} ω_{m+1})`, where `ω_{m+1} = L(B₁(0))`
  set ω : ℝ := (volume (ball (0 : Euclid (m + 1)) 1)).toReal with hω
  have hωeq : volume (ball (0 : Euclid (m + 1)) 1) = ENNReal.ofReal ω := by
    rw [hω, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  refine ⟨ρ₂ / 2, max 3 (3 * 2 ^ (m + 1) * ω), half_pos hρ₂pos, le_max_of_le_left (by norm_num),
    (closedBall_subset_closedBall (half_le_self hρ₂pos.le)).trans hρ₂D, ?_, ?_⟩
  -- the annular bounds of steps 5–6 hold below `ρ₁ < ρ₂`, and `3 ≤ C`
  · intro ρ δ hρ hδ hρδ
    have hlt : ρ + δ < ρ₂ := by linarith
    have hC : ENNReal.ofReal 3 ≤ ENNReal.ofReal (max 3 (3 * 2 ^ (m + 1) * ω)) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hset : Fᶜ ∩ (ball y (ρ + δ) \ closedBall y ρ) = (ball y (ρ + δ) \ closedBall y ρ) \ F := by
      ext z; simp [and_comm]
    have h2 := hA2 ρ δ hρ hδ hlt
    rw [hset] at h2
    exact ⟨(hA1 ρ δ hρ hδ hlt).trans (mul_le_mul_left hC _), h2.trans (mul_le_mul_left hC _)⟩
  -- step 7: `δ = ρ` and `L(B_{2ρ}(y)) = (2ρ)^{m+1} ω_{m+1}`
  · intro ρ hρ hρ1
    have hvol : volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) ≤
        ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := by
      calc volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) ≤ volume (ball y (ρ + ρ)) :=
            measure_mono (inter_subset_right.trans sdiff_subset)
        _ = ENNReal.ofReal ((ρ + ρ) ^ (m + 1)) * volume (ball (0 : Euclid (m + 1)) 1) := by
            rw [Measure.addHaar_ball _ _ (by linarith), finrank_euclideanSpace_fin]
        _ = ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := by
            rw [hωeq, ENNReal.ofReal_mul (by positivity)]
    have key : ENNReal.ofReal ρ * μ (closedBall y ρ) ≤
        ENNReal.ofReal ρ * ENNReal.ofReal (3 * 2 ^ (m + 1) * ω * ρ ^ m) := by
      calc ENNReal.ofReal ρ * μ (closedBall y ρ)
          ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) :=
            hA1 ρ ρ hρ hρ (by linarith)
        _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := mul_le_mul_right hvol _
        _ = ENNReal.ofReal ρ * ENNReal.ofReal (3 * 2 ^ (m + 1) * ω * ρ ^ m) := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hρ.le]
            congr 1
            ring
    have hρne : ENNReal.ofReal ρ ≠ 0 := by simpa using hρ
    refine ((ENNReal.mul_le_mul_iff_right hρne ENNReal.ofReal_ne_top).mp key).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
/-- **Real-integral form of a lower-integral Gagliardo–Nirenberg–Sobolev inequality** (Simon
Ch. 3, proof of Theorem 4.3 (De Giorgi), Sobolev step, chapter-03.txt lines 689–712; the bound
`(H)` below has the shape of Mathlib's `lintegral_pow_le_pow_lintegral_fderiv`).  If every `C¹`
compactly supported `w : ℝᴾ → ℝ` satisfies `∫⁻ ‖w‖ₑ^p ≤ C (∫⁻ ‖Dw‖ₑ)^p`, then with
`c = C^{1/p} + 1 > 0` every such `w` satisfies `(∫ |w|^p)^{1/p} ≤ c ∫ |Dw|`: `Dw` is continuous
with compact support, so `∫⁻ ‖Dw‖ₑ < ∞`; both Bochner integrals are the `toReal` of the lower
integrals, `(H)` passes to `toReal`, and `t ↦ t^{1/p}` is monotone on `[0, ∞)`. -/
theorem Submission.codim1_rdo_dg_sp_gns_real_of_lintegral : ∀ (P : ℕ) (p : ℝ) (C : NNReal), 0 < p → (∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → ∫⁻ x, ‖w x‖ₑ ^ p ≤ (C : ℝ≥0∞) * (∫⁻ x, ‖fderiv ℝ w x‖ₑ) ^ p) → ∃ c : ℝ, 0 < c ∧ ∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, |w z| ^ p) ^ p⁻¹ ≤ c * ∫ z, ‖fderiv ℝ w z‖ := by
  intro P p C hp hH
  -- Step 1: `c = C^{1/p} + 1 > 0`
  refine ⟨(C : ℝ) ^ p⁻¹ + 1, by positivity, ?_⟩
  intro w hw hcs
  -- Step 2: `Dw` is continuous with compact support, so `∫⁻ ‖Dw‖ₑ < ∞` and
  -- `∫ |Dw| = (∫⁻ ‖Dw‖ₑ).toReal`
  have hDcont : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hDint : Integrable (fderiv ℝ w) := hDcont.integrable_of_hasCompactSupport (hcs.fderiv ℝ)
  have hAfin : (∫⁻ x, ‖fderiv ℝ w x‖ₑ) ≠ ∞ := hDint.hasFiniteIntegral.ne
  have hA : ∫ z, ‖fderiv ℝ w z‖ = (∫⁻ x, ‖fderiv ℝ w x‖ₑ).toReal :=
    integral_norm_eq_lintegral_enorm hDcont.aestronglyMeasurable
  -- Step 3: `|w|^p` is continuous and nonnegative, and `ofReal (|w x|^p) = ‖w x‖ₑ^p`, so
  -- `∫ |w|^p = (∫⁻ ‖w‖ₑ^p).toReal`
  have hF : ∫ z, |w z| ^ p = (∫⁻ x, ‖w x‖ₑ ^ p).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg (w z)) p)
      ((hw.continuous.abs.rpow_const fun _ => Or.inr hp.le).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  -- Step 4: take `toReal` in `(H)`, whose right side `C · (∫⁻ ‖Dw‖ₑ)^p` is finite
  have h4 : ∫ z, |w z| ^ p ≤ (C : ℝ) * (∫ z, ‖fderiv ℝ w z‖) ^ p := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le hAfin))
      (hH w hw hcs)
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal, ← hF, ← hA] at h
  -- Step 5: take the `1/p` power: `(C I^p)^{1/p} = C^{1/p} I ≤ c I`
  have hI : 0 ≤ ∫ z, ‖fderiv ℝ w z‖ := integral_nonneg fun z => norm_nonneg _
  have hL : 0 ≤ ∫ z, |w z| ^ p := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg (w z)) p
  calc (∫ z, |w z| ^ p) ^ p⁻¹ ≤ ((C : ℝ) * (∫ z, ‖fderiv ℝ w z‖) ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow hL h4 (inv_nonneg.2 hp.le)
    _ = (C : ℝ) ^ p⁻¹ * ∫ z, ‖fderiv ℝ w z‖ := by
        rw [Real.mul_rpow C.coe_nonneg (Real.rpow_nonneg hI p), Real.rpow_rpow_inv hI hp.ne']
    _ ≤ ((C : ℝ) ^ p⁻¹ + 1) * ∫ z, ‖fderiv ℝ w z‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hI
/-- **Variation of `1_F ζ` from the Gauss–Green identity** (Simon Ch. 3, proof of Theorem 4.3
(De Giorgi), chapter-03.txt lines 689–712: `|D(ζ 1_F)| ≤ ζ |D1_F| + 1_F |Dζ|`, in dual form).  If
`∫_F div φ = -∫ ⟨φ, ν⟩ dμ` for every `C¹` compactly supported `φ` with `tsupport φ ⊆ D`, `|ν| = 1`
and `μ` is finite on compact subsets of `D`, then for `ζ ≥ 0` `C¹` with compact support in `D` and
`g` `C¹` compactly supported with `|g| ≤ 1`, `|∫ 1_F ζ div g| ≤ ∫ ζ dμ + ∫_F |Dζ|`.  Apply (GG) to
`φ = ζ g`: `div (ζ g) = ζ div g + Dζ(g)` (the trace of `v ↦ Dζ(v) g` is `Dζ(g)`), and bound
`|⟨ζ g, ν⟩| ≤ ζ` and `|Dζ(g)| ≤ |Dζ|`. -/
theorem Submission.codim1_rdo_dg_sp_gauss_green_variation : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → ∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, F.indicator ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ ∫ z, ζ z ∂μ + ∫ z in F, ‖fderiv ℝ ζ z‖ := by
  intro P D F μ ν _ hF _ hμK _ hν1 hGG ζ hζ hζc hζD hζ0 g hg _ hg1
  -- Step 1: the test field `φ = ζ g` satisfies the hypotheses of (GG)
  have hsupp : support (fun z => ζ z • g z) ⊆ support ζ := fun z hz h0 => hz (by simp [h0])
  have hGGφ := hGG (fun z => ζ z • g z) (hζ.smul hg) (hζc.mono hsupp)
    ((closure_mono hsupp).trans hζD)
  -- Step 2: `div (ζ g) = ζ div g + Dζ(g)`
  have hdiv : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (fun z => ζ z • g z) z : Euclid P →ₗ[ℝ] Euclid P) =
      ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) +
        fderiv ℝ ζ z (g z) := by
    intro z
    rw [fderiv_fun_smul ((hζ.differentiable one_ne_zero) z) ((hg.differentiable one_ne_zero) z),
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul,
      smul_eq_mul]
    congr 1
    exact LinearMap.trace_smulRight (fderiv ℝ ζ z : Euclid P →ₗ[ℝ] ℝ) (g z)
  -- Step 3: integrability with respect to Lebesgue measure
  have hdivg : Continuous fun z =>
      LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) :=
    ((LinearMap.trace ℝ (Euclid P)).comp
      (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional.comp
      (hg.continuous_fderiv one_ne_zero)
  have hI1 : Integrable (fun z =>
      ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)) :=
    (hζ.continuous.mul hdivg).integrable_of_hasCompactSupport hζc.mul_right
  have hI2 : Integrable (fun z => fderiv ℝ ζ z (g z)) :=
    ((hζ.continuous_fderiv one_ne_zero).clm_apply hg.continuous).integrable_of_hasCompactSupport
      ((hζc.fderiv ℝ).mono fun z hz h0 => hz (by simp [h0]))
  have hI3 : Integrable (fun z => ‖fderiv ℝ ζ z‖) :=
    (hζ.continuous_fderiv one_ne_zero).norm.integrable_of_hasCompactSupport (hζc.fderiv ℝ).norm
  -- Step 4: rewriting the left side
  have hkey : ∫ z, F.indicator ζ z *
      LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) =
      -∫ z, inner ℝ (ζ z • g z) (ν z) ∂μ - ∫ z in F, fderiv ℝ ζ z (g z) := by
    have h1 : ∫ z, F.indicator ζ z *
        LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) =
        ∫ z in F, ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_indicator hF]
      congr 1
      ext z
      by_cases hz : z ∈ F <;> simp [hz]
    have h2 := hGGφ
    simp only [hdiv] at h2
    rw [integral_add hI1.integrableOn hI2.integrableOn] at h2
    rw [h1]
    linarith
  -- Step 5: `ζ` is `μ`-integrable
  have hζμ : Integrable ζ μ := by
    have : IsFiniteMeasure (μ.restrict (tsupport ζ)) := isFiniteMeasure_restrict.2 (hμK _ hζc hζD)
    exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport ζ)).1
      (hζ.continuous.integrable_of_hasCompactSupport hζc)
  -- Step 6: pointwise bounds
  have hb1 : ∀ z, ‖inner ℝ (ζ z • g z) (ν z)‖ ≤ ζ z := by
    intro z
    calc ‖inner ℝ (ζ z • g z) (ν z)‖ ≤ ‖ζ z • g z‖ * ‖ν z‖ := norm_inner_le_norm _ _
      _ = ζ z * ‖g z‖ := by rw [hν1, mul_one, norm_smul, Real.norm_of_nonneg (hζ0 z)]
      _ ≤ ζ z * 1 := mul_le_mul_of_nonneg_left (hg1 z) (hζ0 z)
      _ = ζ z := mul_one _
  have hb2 : ∀ z, ‖fderiv ℝ ζ z (g z)‖ ≤ ‖fderiv ℝ ζ z‖ := fun z =>
    ((fderiv ℝ ζ z).le_opNorm (g z)).trans (mul_le_of_le_one_right (norm_nonneg _) (hg1 z))
  -- Step 7: conclusion
  have hA : |∫ z, inner ℝ (ζ z • g z) (ν z) ∂μ| ≤ ∫ z, ζ z ∂μ :=
    norm_integral_le_of_norm_le hζμ (Eventually.of_forall hb1)
  have hB : |∫ z in F, fderiv ℝ ζ z (g z)| ≤ ∫ z in F, ‖fderiv ℝ ζ z‖ :=
    norm_integral_le_of_norm_le hI3.integrableOn (Eventually.of_forall hb2)
  rw [hkey, show ∀ a b : ℝ, -a - b = -(a + b) from fun a b => by ring, abs_neg]
  exact (abs_add_le _ _).trans (add_le_add hA hB)
/-- **`C¹` approximation of an indicator in `L¹`**: if `P ⊆ B_R(0) ⊆ ℝⁿ` is measurable and
`η > 0`, there is a `C¹` function `ψ : ℝⁿ → [0, 1]` with compact support in `B_R(0)` and
`∫ |ψ - 1_P| < η`.  Take a compact `K ⊆ P` with `L(P \ K) < η/2` (inner regularity), an open
`U ⊇ K` with `L(U \ K) < η/2` (outer regularity at `K`) and `r' < R` with `K ⊆ B_{r'}(0)`; the
smooth Urysohn lemma for `K ⊆ s := U ∩ B_{r'}(0)` gives `ψ` with `support ψ = s` and `ψ = 1`
exactly on `K`, and `|ψ - 1_P| ≤ 1_{P \ K} + 1_{s \ K}`. -/
theorem Submission.codim1_rdo_dg_bvc_smooth_indicator_approx : ∀ (n : ℕ) (P : Set (Euclid n)) (R η : ℝ), MeasurableSet P → P ⊆ ball (0 : Euclid n) R → 0 < η → ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball (0 : Euclid n) R ∧ (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧ ∫ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z| < η := by
  intro n P R η hP hPR hη
  -- Step 1: `L(P) ≤ L(B_R) < ∞`
  have hPfin : volume P ≠ ∞ := (measure_mono hPR |>.trans_lt measure_ball_lt_top).ne
  have hη2 : ENNReal.ofReal (η / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos hη)).ne'
  -- Step 2: a compact closed `K ⊆ P` with `L(P \ K) < η/2`
  obtain ⟨K, hKP, hKc, hKcl, hPK⟩ := hP.exists_isCompact_isClosed_sdiff_lt hPfin hη2
  -- Step 3: an open `U ⊇ K` with `L(U) < L(K) + η/2`
  obtain ⟨U, hKU, hUo, hU⟩ := hKc.exists_isOpen_lt_add (μ := volume) hη2
  -- Step 4: `K ⊆ B_{r'}(0)` for some `r' < R`
  obtain ⟨r', hr'R, hKr'⟩ := exists_lt_subset_ball hKcl (hKP.trans hPR)
  -- Step 5: smooth Urysohn for `K ⊆ s := U ∩ B_{r'}(0)`
  set s := U ∩ ball (0 : Euclid n) r' with hsdef
  have hs : IsOpen s := hUo.inter isOpen_ball
  have hKs : K ⊆ s := fun x hx => ⟨hKU hx, hKr' hx⟩
  obtain ⟨ψ, hψ, hψr, hψs, hψ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1) hs hKcl hKs
  have hψ01 : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1 := fun z => hψr (mem_range_self z)
  -- Step 6: `tsupport ψ = closure s ⊆ B̄_{r'}(0) ⊆ B_R(0)`, which is compact
  have htsupp : tsupport ψ ⊆ closedBall (0 : Euclid n) r' := by
    rw [tsupport, hψs]
    exact closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨ψ, hψ, ?_, htsupp.trans (closedBall_subset_ball hr'R), hψ01, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport ψ).trans htsupp)
  -- Step 7: `|ψ - 1_P| ≤ 1_{P \ K} + 1_{s \ K}` pointwise
  have hdom : ∀ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z|
      ≤ (P \ K).indicator (fun _ => (1 : ℝ)) z + (s \ K).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h01 := hψ01 z
    by_cases hzK : z ∈ K
    · have h1 : ψ z = 1 := (hψ1 z).1 hzK
      simp [h1, hKP hzK, hzK]
    · by_cases hzP : z ∈ P
      · have : (P \ K).indicator (fun _ => (1 : ℝ)) z = 1 := by simp [hzP, hzK]
        rw [indicator_of_mem hzP, this]
        have : 0 ≤ (s \ K).indicator (fun _ => (1 : ℝ)) z :=
          indicator_nonneg (fun _ _ => zero_le_one) _
        rw [abs_le]; constructor <;> linarith
      · rw [indicator_of_notMem hzP, sub_zero, abs_of_nonneg h01.1]
        by_cases hzs : z ∈ s
        · have : (s \ K).indicator (fun _ => (1 : ℝ)) z = 1 := by simp [hzs, hzK]
          rw [this]
          have : 0 ≤ (P \ K).indicator (fun _ => (1 : ℝ)) z :=
            indicator_nonneg (fun _ _ => zero_le_one) _
          linarith [h01.2]
        · have : ψ z = 0 := by
            by_contra h
            exact hzs (hψs ▸ (mem_support.2 h))
          rw [this]
          exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
            (indicator_nonneg (fun _ _ => zero_le_one) _)
  -- Step 8: integrate, using `L(P \ K) < η/2` and `L(s \ K) ≤ L(U \ K) < η/2`
  have hPKm : MeasurableSet (P \ K) := hP.diff hKcl.measurableSet
  have hsKm : MeasurableSet (s \ K) := hs.measurableSet.diff hKcl.measurableSet
  have hPKfin : volume (P \ K) ≠ ∞ := (measure_mono sdiff_subset |>.trans_lt hPfin.lt_top).ne
  have hsKlt : volume (s \ K) < ENNReal.ofReal (η / 2) := by
    calc volume (s \ K) ≤ volume (U \ K) :=
          measure_mono (sdiff_subset_sdiff_left inter_subset_left)
      _ = volume U - volume K :=
          measure_sdiff hKU hKcl.measurableSet.nullMeasurableSet hKc.measure_lt_top.ne
      _ < ENNReal.ofReal (η / 2) := by
        rw [ENNReal.sub_lt_iff_lt_right hKc.measure_lt_top.ne (measure_mono hKU)]
        rwa [add_comm]
  have hsKfin : volume (s \ K) ≠ ∞ := (hsKlt.trans ENNReal.ofReal_lt_top).ne
  have hint1 : Integrable ((P \ K).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hPKfin).integrable_indicator hPKm
  have hint2 : Integrable ((s \ K).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hsKfin).integrable_indicator hsKm
  calc ∫ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z|
      ≤ ∫ z, ((P \ K).indicator (fun _ => (1 : ℝ)) z + (s \ K).indicator (fun _ => (1 : ℝ)) z) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (hint1.add hint2) (Filter.Eventually.of_forall hdom)
    _ = (volume (P \ K)).toReal + (volume (s \ K)).toReal := by
        rw [integral_add hint1 hint2, integral_indicator_const _ hPKm,
          integral_indicator_const _ hsKm]
        simp [Measure.real]
    _ < η / 2 + η / 2 := by
        gcongr
        · exact (ENNReal.toReal_lt_toReal hPKfin ENNReal.ofReal_ne_top).2 hPK
            |>.trans_eq (ENNReal.toReal_ofReal (half_pos hη).le)
        · exact (ENNReal.toReal_lt_toReal hsKfin ENNReal.ofReal_ne_top).2 hsKlt
            |>.trans_eq (ENNReal.toReal_ofReal (half_pos hη).le)
    _ = η := add_halves η

/-- **The `L¹` norm on a ball by duality with `C¹` test functions** (used in the mollification
estimate of the precompactness step of the BV compactness theorem, Simon Ch. 2, 2.6, which the book
delegates to [GT01, Theorem 7.22]; this serves De Giorgi's argument), for
bounded Borel `f`: if `|f| ≤ M` and `∫ f φ ≤ A` for every `C¹` function `φ` with compact support in
`B_R(0)` and `|φ| ≤ 1`, then `∫_{B_R(0)} |f| ≤ A`.  With `P = {f > 0} ∩ B_R(0)`,
`N = {f < 0} ∩ B_R(0)` and `g = 1_P − 1_N` one has `f g = 1_{B_R(0)} |f|`.  Approximating `1_P` and
`1_N` in `L¹` within `η' = η / (2(M + 1))` by `C¹` functions `ψ_P`, `ψ_N` with values in `[0, 1]`
and compact support in `B_R(0)` (`smooth_indicator_approx`) gives the admissible test
`φ = ψ_P − ψ_N`, and `∫ f g − ∫ f φ ≤ M (∫ |ψ_P − 1_P| + ∫ |ψ_N − 1_N|) < (M + 1) 2η' = η`. -/
theorem Submission.codim1_rdo_dg_bvc_l1_le_of_tests : ∀ (n : ℕ) (f : Euclid n → ℝ) (R A M : ℝ), Measurable f → (∀ z, |f z| ≤ M) → (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid n) R → (∀ z, |φ z| ≤ 1) → ∫ z, f z * φ z ≤ A) → ∫ z in ball (0 : Euclid n) R, |f z| ≤ A := by
  intro n f R A M hf hM hA
  -- Step 1: `M ≥ |f 0| ≥ 0`; `P = {f > 0} ∩ B_R` and `N = {f < 0} ∩ B_R` are Borel subsets of
  -- `B_R` (so of finite measure); `g = 1_P − 1_N`
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set P : Set (Euclid n) := {z | 0 < f z} ∩ ball 0 R
  set N : Set (Euclid n) := {z | f z < 0} ∩ ball 0 R
  have hPm : MeasurableSet P := (measurableSet_lt measurable_const hf).inter measurableSet_ball
  have hNm : MeasurableSet N := (measurableSet_lt hf measurable_const).inter measurableSet_ball
  have hPfin : volume P ≠ ∞ := (measure_mono inter_subset_right |>.trans_lt measure_ball_lt_top).ne
  have hNfin : volume N ≠ ∞ := (measure_mono inter_subset_right |>.trans_lt measure_ball_lt_top).ne
  set g : Euclid n → ℝ := fun z =>
    P.indicator (fun _ => (1 : ℝ)) z - N.indicator (fun _ => (1 : ℝ)) z with hg
  -- Step 2: `f g = 1_{B_R} |f|` pointwise, so `∫_{B_R} |f| = ∫ f g`; `f g` is integrable, being
  -- Borel, bounded by `M` and zero outside `B_R`
  have hfg : (fun z => f z * g z) = (ball (0 : Euclid n) R).indicator fun z => |f z| := by
    funext z
    by_cases hz : z ∈ ball (0 : Euclid n) R
    · rw [indicator_of_mem hz]
      rcases lt_trichotomy (f z) 0 with h | h | h
      · have hzP : z ∉ P := fun hzP => lt_asymm h hzP.1
        have hzN : z ∈ N := ⟨h, hz⟩
        simp only [hg, indicator_of_notMem hzP, indicator_of_mem hzN, abs_of_neg h]
        ring
      · simp [h]
      · have hzP : z ∈ P := ⟨h, hz⟩
        have hzN : z ∉ N := fun hzN => lt_asymm h hzN.1
        simp only [hg, indicator_of_mem hzP, indicator_of_notMem hzN, abs_of_pos h]
        ring
    · have hzP : z ∉ P := fun hzP => hz hzP.2
      have hzN : z ∉ N := fun hzN => hz hzN.2
      simp only [hg, indicator_of_notMem hzP, indicator_of_notMem hzN, indicator_of_notMem hz]
      ring
  have hrepr : ∫ z in ball (0 : Euclid n) R, |f z| = ∫ z, f z * g z := by
    rw [hfg, integral_indicator measurableSet_ball]
  have hfg_int : Integrable fun z => f z * g z := by
    rw [hfg]
    refine (Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne
      (continuous_abs.measurable.comp hf).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)).integrable_indicator measurableSet_ball
    simpa [Real.norm_eq_abs] using hM z
  -- Step 3: given `η > 0`, approximate `1_P` and `1_N` in `L¹` within `η' = η / (2(M + 1))`
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hM1 : 0 < M + 1 := by linarith
  set η' : ℝ := η / (2 * (M + 1)) with hη'
  have hη'0 : 0 < η' := div_pos hη (mul_pos two_pos hM1)
  obtain ⟨ψP, hψP, hcP, htP, h01P, hapP⟩ :=
    Submission.codim1_rdo_dg_bvc_smooth_indicator_approx n P R η' hPm inter_subset_right hη'0
  obtain ⟨ψN, hψN, hcN, htN, h01N, hapN⟩ :=
    Submission.codim1_rdo_dg_bvc_smooth_indicator_approx n N R η' hNm inter_subset_right hη'0
  -- Step 4: `φ = ψ_P − ψ_N` is an admissible test, so `∫ f φ ≤ A`; `f φ` is integrable
  set φ : Euclid n → ℝ := fun z => ψP z - ψN z with hφ
  have hφ1 : ∀ z, |φ z| ≤ 1 := fun z => by
    obtain ⟨h0P, h1P⟩ := h01P z
    obtain ⟨h0N, h1N⟩ := h01N z
    rw [hφ, abs_le]
    constructor <;> linarith
  have hφA : ∫ z, f z * φ z ≤ A :=
    hA φ (hψP.sub hψN) (hcP.sub hcN) ((tsupport_sub ψP ψN).trans (union_subset htP htN)) hφ1
  have hfφ_int : Integrable fun z => f z * φ z :=
    ((hψP.sub hψN).continuous.integrable_of_hasCompactSupport (hcP.sub hcN)).bdd_mul
      hf.aestronglyMeasurable (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM z)
  -- Step 5: `f g − f φ ≤ M (|ψ_P − 1_P| + |ψ_N − 1_N|)` pointwise, and these errors are integrable;
  -- integrate
  have hIP : Integrable fun z => |ψP z - P.indicator (fun _ => (1 : ℝ)) z| :=
    ((hψP.continuous.integrable_of_hasCompactSupport hcP).sub
      ((integrableOn_const (C := (1 : ℝ)) hPfin).integrable_indicator hPm)).abs
  have hIN : Integrable fun z => |ψN z - N.indicator (fun _ => (1 : ℝ)) z| :=
    ((hψN.continuous.integrable_of_hasCompactSupport hcN).sub
      ((integrableOn_const (C := (1 : ℝ)) hNfin).integrable_indicator hNm)).abs
  have hpt : ∀ z, f z * g z - f z * φ z ≤ M * (|ψP z - P.indicator (fun _ => (1 : ℝ)) z| +
      |ψN z - N.indicator (fun _ => (1 : ℝ)) z|) := by
    intro z
    calc f z * g z - f z * φ z
        = f z * ((P.indicator (fun _ => (1 : ℝ)) z - ψP z) -
            (N.indicator (fun _ => (1 : ℝ)) z - ψN z)) := by
          simp only [hg, hφ]
          ring
      _ ≤ |f z| * |(P.indicator (fun _ => (1 : ℝ)) z - ψP z) -
            (N.indicator (fun _ => (1 : ℝ)) z - ψN z)| := by
          rw [← abs_mul]
          exact le_abs_self _
      _ ≤ M * (|ψP z - P.indicator (fun _ => (1 : ℝ)) z| +
            |ψN z - N.indicator (fun _ => (1 : ℝ)) z|) := by
          rw [abs_sub_comm (ψP z), abs_sub_comm (ψN z)]
          exact mul_le_mul (hM z) (abs_sub _ _) (abs_nonneg _) hM0
  have hmain : (∫ z, f z * g z) - ∫ z, f z * φ z ≤
      M * ((∫ z, |ψP z - P.indicator (fun _ => (1 : ℝ)) z|) +
        ∫ z, |ψN z - N.indicator (fun _ => (1 : ℝ)) z|) := by
    rw [← integral_sub hfg_int hfφ_int, ← integral_add hIP hIN, ← integral_const_mul]
    exact integral_mono (hfg_int.sub hfφ_int) ((hIP.add hIN).const_mul M) hpt
  -- Step 6: `S = ∫ |ψ_P − 1_P| + ∫ |ψ_N − 1_N|` satisfies `0 ≤ S < 2η'`, so
  -- `M S ≤ (M + 1) S < (M + 1) 2η' = η`
  set S : ℝ := (∫ z, |ψP z - P.indicator (fun _ => (1 : ℝ)) z|) +
    ∫ z, |ψN z - N.indicator (fun _ => (1 : ℝ)) z| with hS
  have hS0 : 0 ≤ S :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hS2 : S < 2 * η' := by
    rw [hS]
    linarith
  have hMS : M * S < η :=
    calc M * S ≤ (M + 1) * S := by linarith
      _ < (M + 1) * (2 * η') := mul_lt_mul_of_pos_left hS2 hM1
      _ = η := by
        rw [hη']
        field_simp
  -- Step 7: `∫_{B_R} |f| = ∫ f g ≤ ∫ f φ + M S < A + η`; `η > 0` is arbitrary
  rw [hrepr]
  linarith
/-- **Translation against a `C¹` test function** (step 1 of the BV compactness argument, for a
single translation vector `w`): if `∫_F div g ≤ C` for every `C¹` field `g` with `|g| ≤ 1` and
compact support in `B_{R+|w|}(0)`, then `∫_F (φ(z) − φ(z + w)) dz ≤ |w| C` for every `C¹` test
function `φ` with `|φ| ≤ 1` and compact support in `B_R(0)`.  For `t ∈ [0, 1]` the field
`G_t = −|w|⁻¹ φ(· + tw) w` is admissible and `div G_t = −|w|⁻¹ Dφ(· + tw)[w]` (trace of a rank-one
map), so `Φ(t) = ∫_F φ(z + tw) dz`, differentiable under the integral sign, has
`Φ'(t) = ∫_F Dφ(z + tw)[w] dz ≥ −|w| C` on `[0, 1]`; hence `Φ(0) − Φ(1) ≤ |w| C`. -/
theorem Submission.codim1_rdo_dg_bvc_translate_test_le : ∀ (n : ℕ) (F : Set (Euclid n)) (R C : ℝ) (w : Euclid n) (φ : Euclid n → ℝ), MeasurableSet F → (∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid n) (R + ‖w‖) → (∀ z, ‖g z‖ ≤ 1) → ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid n) R → (∀ z, |φ z| ≤ 1) → ∫ z in F, (φ z - φ (z + w)) ≤ ‖w‖ * C := by
  intro n F R C w φ _hF hdiv hφ hφc hφs hφb
  -- `w = 0`: both sides vanish
  by_cases hw : w = 0
  · subst hw; simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  -- the elementary fields `G_t = (−‖w‖⁻¹ φ(· + t • w)) • w`, `0 ≤ t ≤ 1`, give
  -- `−‖w‖ C ≤ ∫_F Dφ(z + t • w)[w]`
  have hfield : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      -(‖w‖ * C) ≤ ∫ z in F, fderiv ℝ φ (z + t • w) w := by
    intro t ht0 ht1
    set c : ℝ := -(‖w‖⁻¹) with hc
    set G : Euclid n → Euclid n := fun z => (c * φ (z + t • w)) • w with hG
    have hGd : ∀ z, HasFDerivAt G ((c • fderiv ℝ φ (z + t • w)).smulRight w) z := by
      intro z
      have h1 : HasFDerivAt (fun y : Euclid n => φ (y + t • w)) (fderiv ℝ φ (z + t • w)) z :=
        (hφd (z + t • w)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const (t • w))
      exact (h1.const_mul c).smul_const w
    have hGc1 : ContDiff ℝ 1 G :=
      (contDiff_const.mul (hφ.comp (contDiff_id.add contDiff_const))).smul contDiff_const
    -- `tsupport G ⊆ tsupport φ(· + t • w) = tsupport φ − t • w`
    have hpre : tsupport (fun y : Euclid n => φ (y + t • w)) =
        (fun y => y + t • w) ⁻¹' tsupport φ :=
      tsupport_comp_eq_preimage φ (Homeomorph.addRight (t • w))
    have hGsupp : tsupport G ⊆ tsupport (fun y : Euclid n => φ (y + t • w)) :=
      (tsupport_smul_subset_left _ _).trans tsupport_mul_subset_right
    have hGcs : HasCompactSupport G :=
      (hφc.comp_homeomorph (Homeomorph.addRight (t • w))).mul_left.smul_right
    have hGball : tsupport G ⊆ ball (0 : Euclid n) (R + ‖w‖) := by
      intro z hz
      have h1 : z + t • w ∈ ball (0 : Euclid n) R := hφs (hpre.subset (hGsupp hz))
      rw [mem_ball_zero_iff] at h1 ⊢
      have h2 : ‖t • w‖ ≤ ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      calc ‖z‖ = ‖(z + t • w) - t • w‖ := by simp
        _ ≤ ‖z + t • w‖ + ‖t • w‖ := norm_sub_le _ _
        _ < R + ‖w‖ := by linarith
    have hGnorm : ∀ z, ‖G z‖ ≤ 1 := by
      intro z
      simp only [hG, hc, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_norm]
      rw [mul_comm (‖w‖⁻¹), mul_assoc, inv_mul_cancel₀ hwpos.ne', mul_one]
      exact hφb _
    -- `div G_t(z) = c Dφ(z + t • w)[w]`: the trace of the rank-one map `h ↦ c Dφ(z + t • w)[h] w`
    have htrace : ∀ z, LinearMap.trace ℝ (Euclid n) (fderiv ℝ G z : Euclid n →ₗ[ℝ] Euclid n) =
        c * fderiv ℝ φ (z + t • w) w := by
      intro z
      rw [(hGd z).fderiv]
      have : ((c • fderiv ℝ φ (z + t • w)).smulRight w : Euclid n →L[ℝ] Euclid n) =
          (((c • fderiv ℝ φ (z + t • w) : Euclid n →L[ℝ] ℝ) : Euclid n →ₗ[ℝ] ℝ).smulRight w :
            Euclid n →ₗ[ℝ] Euclid n) := by
        ext v; simp
      rw [this, LinearMap.trace_smulRight]
      simp
    have hbound := hdiv G hGc1 hGcs hGball hGnorm
    simp_rw [htrace] at hbound
    rw [integral_const_mul] at hbound
    -- `−‖w‖⁻¹ ∫_F Dφ(z + t • w)[w] ≤ C`; multiply by `‖w‖ > 0`
    have h3 := mul_le_mul_of_nonneg_left hbound hwpos.le
    rw [← mul_assoc, hc, mul_neg, mul_inv_cancel₀ hwpos.ne', neg_one_mul] at h3
    linarith
  -- `Φ(t) = ∫_F φ(z + t • w)` has derivative `∫_F Dφ(z + t • w)[w]` (dominated differentiation)
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖fderiv ℝ φ x‖ ≤ B :=
    (hφc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hφ'c
  set Φ : ℝ → ℝ := fun t => ∫ z in F, φ (z + t • w) with hΦ
  have hΦd : ∀ t₀ : ℝ, HasDerivAt Φ (∫ z in F, fderiv ℝ φ (z + t₀ • w) w) t₀ := by
    intro t₀
    set K : Set (Euclid n) := closedBall (0 : Euclid n) (R + (|t₀| + 1) * ‖w‖)
    have hKm : MeasurableSet K := measurableSet_closedBall
    have hKfin : volume K ≠ ∞ := measure_closedBall_lt_top.ne
    -- `Dφ(z + t • w) ≠ 0` forces `z + t • w ∈ tsupport φ ⊆ B_R(0)`
    have hsupp : ∀ z t, fderiv ℝ φ (z + t • w) ≠ 0 → ‖z‖ < R + |t| * ‖w‖ := by
      intro z t h
      have h1 := hφs (tsupport_fderiv_subset ℝ (subset_tsupport _ h))
      rw [mem_ball_zero_iff] at h1
      calc ‖z‖ = ‖(z + t • w) - t • w‖ := by simp
        _ ≤ ‖z + t • w‖ + ‖t • w‖ := norm_sub_le _ _
        _ < R + |t| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]; linarith
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict F)
      (F := fun t z => φ (z + t • w)) (F' := fun t z => fderiv ℝ φ (z + t • w) w)
      (bound := K.indicator (fun _ => B * ‖w‖)) (s := ball t₀ 1) (ball_mem_nhds t₀ zero_lt_one)
      ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (hφ.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · exact (hφi.comp_add_right (t₀ • w)).integrableOn
    · exact ((hφ'c.comp (continuous_id.add continuous_const)).clm_apply
        continuous_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z t ht => ?_
      by_cases hz : fderiv ℝ φ (z + t • w) = 0
      · simp only [hz, zero_apply, norm_zero]
        exact indicator_nonneg
          (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hB 0)) (norm_nonneg _)) _
      · have hzK : z ∈ K := by
          have h1 := hsupp z t hz
          have h2 : |t| ≤ |t₀| + 1 := by
            have := abs_sub_abs_le_abs_sub t t₀
            rw [mem_ball, Real.dist_eq] at ht; linarith
          rw [mem_closedBall_zero_iff]
          nlinarith [norm_nonneg w]
        rw [indicator_of_mem hzK]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    · exact ((integrableOn_const hKfin).integrable_indicator hKm).integrableOn
    · refine Filter.Eventually.of_forall fun z t _ => ?_
      have h1 : HasDerivAt (fun s : ℝ => z + s • w) w t := by
        simpa using ((hasDerivAt_id t).smul_const w).const_add z
      exact (hφd (z + t • w)).hasFDerivAt.comp_hasDerivAt t h1
  -- `Ψ(t) = Φ(t) + ‖w‖ C t` has `Ψ' ≥ 0` on `(0, 1)`, so `Ψ(0) ≤ Ψ(1)`
  set Ψ : ℝ → ℝ := fun t => Φ t + ‖w‖ * C * t with hΨ
  have hΨd : ∀ t, HasDerivAt Ψ ((∫ z in F, fderiv ℝ φ (z + t • w) w) + ‖w‖ * C) t := by
    intro t
    have := (hΦd t).add ((hasDerivAt_id t).const_mul (‖w‖ * C))
    simp only [id, mul_one] at this
    exact this
  have hmono : MonotoneOn Ψ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t _ => (hΨd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hΨd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hΨd t).deriv]
      linarith [hfield t ht.1.le ht.2.le]
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hΨ, hΦ, zero_smul, add_zero, one_smul, mul_zero, mul_one] at h01
  -- `Φ(0) − Φ(1) = ∫_F (φ z − φ (z + w))`
  rw [integral_sub hφi.integrableOn (hφi.comp_add_right w).integrableOn]
  linarith
/-- **`L¹` translation estimate** (step 1 of the BV compactness argument behind Simon Ch. 2, 2.6,
via [GT01, 7.22], for a single translation `w`).  If `∫_F div g ≤ C` for every `C¹` vector field
`g` with `|g| ≤ 1` and compact support in `B_{R+|w|}(0)`, then
`∫_{B_R(0)} |1_F(z) − 1_F(z − w)| dz ≤ |w| C`.  The difference `f = 1_F − 1_F(· − w)` is Borel with
`|f| ≤ 1`; for an admissible test `φ`, translation invariance of Lebesgue measure gives
`∫ f φ = ∫_F (φ − φ(· + w))`, which `translate_test` bounds by `|w| C`, and `l1_duality` (with
`M = 1`) turns this weak bound into the `L¹` bound. -/
theorem Submission.codim1_rdo_dg_bvc_translation_l1_le : ∀ (n : ℕ) (F : Set (Euclid n)) (R C : ℝ) (w : Euclid n), MeasurableSet F → (∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid n) (R + ‖w‖) → (∀ z, ‖g z‖ ≤ 1) → ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C) → ∫ z in ball (0 : Euclid n) R, |F.indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) (z - w)| ≤ ‖w‖ * C := by
  intro n F R C w hF hdiv
  -- Step 1: `u = 1_F` takes values in `[0, 1]`, so `f = u − u(· − w)` is Borel with `|f| ≤ 1`
  set u : Euclid n → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
  have hu01 : ∀ z, 0 ≤ u z ∧ u z ≤ 1 := fun z => by
    by_cases hz : z ∈ F <;> simp [hu, hz]
  have hu_meas : Measurable u := measurable_const.indicator hF
  have hu_shift : Measurable fun z => u (z - w) := hu_meas.comp (measurable_id.sub_const w)
  have hbd : ∀ z, |u z - u (z - w)| ≤ 1 := fun z => by
    rw [abs_le]
    constructor <;> linarith [(hu01 z).1, (hu01 z).2, (hu01 (z - w)).1, (hu01 (z - w)).2]
  -- Step 4: `l1_duality` with `M = 1` and `A = ‖w‖ C` reduces the claim to the tested bound
  refine Submission.codim1_rdo_dg_bvc_l1_le_of_tests n (fun z => u z - u (z - w)) R (‖w‖ * C) 1
    (hu_meas.sub hu_shift) hbd fun φ hφ hφc hφs hφb => ?_
  -- Step 2: `∫ f φ = ∫_F (φ − φ(· + w))`, moving the translation onto `φ` (`z = y + w`)
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hmul : ∀ ψ : Euclid n → ℝ, (fun z => u z * ψ z) = F.indicator ψ := fun ψ => by
    funext z
    by_cases hz : z ∈ F <;> simp [hu, hz]
  have h1 : Integrable fun z => u z * φ z := by
    rw [hmul]
    exact hφi.indicator hF
  have hu_shift_le : ∀ z, ‖u (z - w)‖ ≤ 1 := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hu01 (z - w)).1]
    exact (hu01 (z - w)).2
  have h2 : Integrable fun z => u (z - w) * φ z :=
    hφi.bdd_mul hu_shift.aestronglyMeasurable (Eventually.of_forall hu_shift_le)
  have h3 : Integrable fun z => u z * φ (z + w) := by
    rw [hmul]
    exact (hφi.comp_add_right w).indicator hF
  have hshift : ∫ z, u (z - w) * φ z = ∫ z, u z * φ (z + w) := by
    rw [← integral_add_right_eq_self (fun z => u (z - w) * φ z) w]
    simp
  have key : ∫ z, (u z - u (z - w)) * φ z = ∫ z in F, (φ z - φ (z + w)) := by
    simp_rw [sub_mul]
    rw [integral_sub h1 h2, hshift, ← integral_sub h1 h3, ← integral_indicator hF]
    congr 1
    funext z
    by_cases hz : z ∈ F <;> simp [hu, hz]
  -- Step 3: `translate_test` bounds `∫_F (φ − φ(· + w))` by `‖w‖ C`
  exact key.trans_le
    (Submission.codim1_rdo_dg_bvc_translate_test_le n F R C w φ hF hdiv hφ hφc hφs hφb)

/-- **Mollification estimate for a set of bounded perimeter** (Simon 2.6, chapter-02.txt
lines 598–626, the precompactness step delegated to [GT01, Theorem 7.22]: with `u = 1_F`,
`‖u − ρ * u‖_{L¹(B_R)} ≤ ε C` when `ρ ≥ 0`, `∫ ρ = 1`, `support ρ ⊆ B_ε(0)`, `ε ≤ 1` and
`∫_F div g ≤ C` for the fields `g` of the class in `B_{R+1}(0)`).  As `∫ ρ = 1`,
`|u(z) − ∫ ρ(y) u(z − y) dy| ≤ ∫ ρ(y) |u(z) − u(z − y)| dy`; the integrand is at most `ρ(y)`,
so Fubini on `B_R(0) × ℝⁿ` turns the integral over `B_R(0)` into `∫ ρ(y) I(y) dy` with
`I(y) = ∫_{B_R(0)} |u(z) − u(z − y)| dz`.  For `ρ(y) ≠ 0`, `|y| < ε ≤ 1`, so the translation
estimate `Submission.codim1_rdo_dg_bvc_translation_l1_le` applies at radius
`R + |y| ≤ R + 1` and gives `I(y) ≤ |y| C ≤ ε C`. -/
theorem Submission.codim1_rdo_dg_bvc_mollify_l1_le : ∀ (n : ℕ) (F : Set (Euclid n)) (R C ε : ℝ) (ρ : Euclid n → ℝ), MeasurableSet F → ε ≤ 1 → Continuous ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → support ρ ⊆ ball (0 : Euclid n) ε → (∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid n) (R + 1) → (∀ z, ‖g z‖ ≤ 1) → ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C) → ∫ z in ball (0 : Euclid n) R, |F.indicator (fun _ => (1 : ℝ)) z - ∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (z - y)| ≤ ε * C := by
  intro n F R C ε ρ hF hε1 hρc hρcs hρ0 hρ1 hρs hdiv
  set u : Euclid n → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
  have hu_meas : Measurable u := measurable_const.indicator hF
  have hu01 : ∀ z, 0 ≤ u z ∧ u z ≤ 1 := fun z => by
    simp only [hu, Set.indicator]; split_ifs <;> norm_num
  have hbd : ∀ z y, |u z - u (z - y)| ≤ 1 := fun z y => by
    have h1 := hu01 z
    have h2 := hu01 (z - y)
    rw [abs_le]; constructor <;> linarith
  -- Step 1: `C ≥ 0` (the field `g = 0`) and `ρ` is integrable
  have hC : 0 ≤ C := by
    simpa using hdiv (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
  have hρint : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  -- Step 2: pointwise, `|u z − ∫ ρ(y) u(z − y)| ≤ ∫ ρ(y) |u z − u(z − y)|`, since `∫ ρ = 1`
  have hpt : ∀ z, |u z - ∫ y, ρ y * u (z - y)| ≤ ∫ y, ρ y * |u z - u (z - y)| := by
    intro z
    have hint1 : Integrable (fun y => ρ y * u z) := hρint.mul_const _
    have hint2 : Integrable (fun y => ρ y * u (z - y)) :=
      hρint.mul_bdd (c := 1) (hu_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hu01 (z - y)).1]
          exact (hu01 (z - y)).2)
    have e : ∫ y, ρ y * (u z - u (z - y)) = u z - ∫ y, ρ y * u (z - y) := by
      simp_rw [mul_sub]
      rw [integral_sub hint1 hint2, integral_mul_const, hρ1, one_mul]
    rw [← e]
    refine abs_integral_le_integral_abs.trans_eq ?_
    congr 1
    funext y
    rw [abs_mul, abs_of_nonneg (hρ0 y)]
  -- Step 3: Fubini for `H(z, y) = ρ(y) |u z − u(z − y)| ≤ ρ(y)` on `B_R(0) × ℝⁿ`
  set H : Euclid n → Euclid n → ℝ := fun z y => ρ y * |u z - u (z - y)| with hH
  have hHmeas : Measurable (Function.uncurry H) :=
    (hρc.measurable.comp measurable_snd).mul (continuous_abs.measurable.comp
      ((hu_meas.comp measurable_fst).sub (hu_meas.comp (measurable_fst.sub measurable_snd))))
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hHint :
      Integrable (Function.uncurry H) ((volume.restrict (ball (0 : Euclid n) R)).prod volume) := by
    have hdom : Integrable (fun p : Euclid n × Euclid n => ρ p.2)
        ((volume.restrict (ball (0 : Euclid n) R)).prod volume) := by
      simpa using
        (integrable_const (1 : ℝ) (μ := volume.restrict (ball (0 : Euclid n) R))).mul_prod hρint
    refine hdom.mono' hHmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hH, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 p.2), abs_abs]
    exact mul_le_of_le_one_right (hρ0 p.2) (hbd _ _)
  -- Step 4: each translation; for `ρ(y) ≠ 0`, `translation_l1` with `w = y` at radius `R + |y|`
  have hinner : ∀ y, ∫ z in ball (0 : Euclid n) R, H z y ≤ ρ y * (ε * C) := by
    intro y
    simp only [hH]
    rw [integral_const_mul]
    by_cases hy : ρ y = 0
    · simp [hy]
    have hyε : ‖y‖ < ε := mem_ball_zero_iff.1 (hρs hy)
    have hdiv' : ∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g →
        tsupport g ⊆ ball (0 : Euclid n) (R + ‖y‖) → (∀ z, ‖g z‖ ≤ 1) →
        ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C :=
      fun g hg hgc hgs hgb => hdiv g hg hgc (hgs.trans (ball_subset_ball (by linarith))) hgb
    have hI : ∫ z in ball (0 : Euclid n) R, |u z - u (z - y)| ≤ ε * C :=
      (Submission.codim1_rdo_dg_bvc_translation_l1_le n F R C y hF hdiv').trans
        (mul_le_mul_of_nonneg_right hyε.le hC)
    exact mul_le_mul_of_nonneg_left hI (hρ0 y)
  -- Step 5: combine the three estimates
  calc ∫ z in ball (0 : Euclid n) R, |u z - ∫ y, ρ y * u (z - y)|
      ≤ ∫ z in ball (0 : Euclid n) R, ∫ y, H z y :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _)
          hHint.integral_prod_left (Eventually.of_forall hpt)
    _ = ∫ y, ∫ z in ball (0 : Euclid n) R, H z y := integral_integral_swap hHint
    _ ≤ ∫ y, ρ y * (ε * C) := integral_mono hHint.integral_prod_right (hρint.mul_const _) hinner
    _ = ε * C := by rw [integral_mul_const, hρ1, one_mul]
/-- **Mollified indicators are uniformly bounded and uniformly Lipschitz** (step 2 of the `BV`
compactness theorem, Simon Ch. 2, 2.6, for indicators).  Let `ρ ≥ 0` be `C¹` with compact
support and `∫ ρ = 1`, and `v_F(x) = ∫ ρ(y) 1_F(x − y) dy`.  Then `|v_F| ≤ ∫ ρ = 1`.  `ρ` is
`L_ρ`-Lipschitz; after `y ↦ x − y`, `v_F(x) − v_F(x') = ∫ (ρ(x − z) − ρ(x' − z)) 1_F(z) dz`,
whose integrand is at most `L_ρ|x − x'| (1_K(x − z) + 1_K(x' − z))` with `K = spt ρ`, so
`|v_F(x) − v_F(x')| ≤ 2L_ρ|K| |x − x'|`.  Hence `L = max 1 (2L_ρ|K|)` serves every measurable
`F`. -/
theorem Submission.codim1_rdo_dg_bvc_mollified_lipschitz : ∀ (n : ℕ) (ρ : Euclid n → ℝ), ContDiff ℝ 1 ρ → HasCompactSupport ρ → (∀ y, 0 ≤ ρ y) → ∫ y, ρ y = 1 → ∃ L : ℝ, ∀ F : Set (Euclid n), MeasurableSet F → (∀ x, |∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)| ≤ L) ∧ ∀ x x', |(∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)) - ∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x' - y)| ≤ L * ‖x - x'‖ := by
  intro n ρ hρ hρc hρ0 hρ1
  -- `ρ` is `Lρ`-Lipschitz, and `K = spt ρ` is compact with finite measure `V`
  obtain ⟨Lρ, hLρ⟩ := hρ.lipschitzWith_of_hasCompactSupport hρc (by norm_num)
  set K := tsupport ρ
  have hKc : IsCompact K := hρc
  have hKm : MeasurableSet K := (isClosed_tsupport ρ).measurableSet
  have hKfin : volume K ≠ ∞ := hKc.measure_lt_top.ne
  set V : ℝ := (volume K).toReal with hV
  have hρint : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hind : ∀ (s : Set (Euclid n)) (z : Euclid n), |s.indicator (fun _ => (1 : ℝ)) z| ≤ 1 := by
    intro s z
    simp only [Set.indicator]; split_ifs <;> norm_num
  have hK0 : ∀ w, 0 ≤ K.indicator (fun _ => (1 : ℝ)) w :=
    fun w => indicator_nonneg (fun _ _ => zero_le_one) w
  refine ⟨max 1 (2 * Lρ * V), fun F hF => ⟨fun x => ?_, fun x x' => ?_⟩⟩
  · -- `|v_F(x)| ≤ ∫ ρ = 1`
    have hu : ∀ y, |ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)| ≤ ρ y := by
      intro y
      rw [abs_mul, abs_of_nonneg (hρ0 y)]
      exact mul_le_of_le_one_right (hρ0 y) (hind F (x - y))
    calc |∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)|
        ≤ ∫ y, |ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, ρ y := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
          hρint (Filter.Eventually.of_forall hu)
      _ = 1 := hρ1
      _ ≤ max 1 (2 * Lρ * V) := le_max_left _ _
  · -- `v_F(x) = ∫ ρ(x − z) 1_F(z) dz` (Lebesgue measure is invariant under `y ↦ x − y`)
    have hsub : ∀ x : Euclid n, ∫ y, ρ y * F.indicator (fun _ => (1 : ℝ)) (x - y) =
        ∫ z, ρ (x - z) * F.indicator (fun _ => (1 : ℝ)) z := by
      intro x
      rw [← integral_sub_left_eq_self (fun z => ρ (x - z) * F.indicator (fun _ => (1 : ℝ)) z)
        volume x]
      simp
    have hi : ∀ x : Euclid n,
        Integrable (fun z => ρ (x - z) * F.indicator (fun _ => (1 : ℝ)) z) := by
      intro x
      refine Integrable.mul_bdd (c := 1) (hρint.comp_sub_left x) ?_ ?_
      · exact (measurable_const.indicator hF).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hind F z
    rw [hsub x, hsub x', ← integral_sub (hi x) (hi x')]
    -- pointwise, `|(ρ(x − z) − ρ(x' − z)) 1_F(z)| ≤ Lρ|x − x'| (1_K(x − z) + 1_K(x' − z))`
    have hpt : ∀ z, |ρ (x - z) * F.indicator (fun _ => (1 : ℝ)) z -
        ρ (x' - z) * F.indicator (fun _ => (1 : ℝ)) z| ≤
        Lρ * ‖x - x'‖ * (K.indicator (fun _ => (1 : ℝ)) (x - z) +
          K.indicator (fun _ => (1 : ℝ)) (x' - z)) := by
      intro z
      rw [← sub_mul, abs_mul]
      have hlip : |ρ (x - z) - ρ (x' - z)| ≤ Lρ * ‖x - x'‖ := by
        have := hLρ.dist_le_mul (x - z) (x' - z)
        rw [Real.dist_eq, dist_eq_norm] at this
        simpa using this
      by_cases h : x - z ∈ K ∨ x' - z ∈ K
      · have hs : 1 ≤ K.indicator (fun _ => (1 : ℝ)) (x - z) +
            K.indicator (fun _ => (1 : ℝ)) (x' - z) := by
          rcases h with h | h
          · rw [indicator_of_mem h]; linarith [hK0 (x' - z)]
          · rw [indicator_of_mem h (f := fun _ => (1 : ℝ))]; linarith [hK0 (x - z)]
        calc |ρ (x - z) - ρ (x' - z)| * |F.indicator (fun _ => (1 : ℝ)) z|
            ≤ Lρ * ‖x - x'‖ * 1 := mul_le_mul hlip (hind F z) (abs_nonneg _) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
      · push Not at h
        have h1 : ρ (x - z) = 0 := image_eq_zero_of_notMem_tsupport h.1
        have h2 : ρ (x' - z) = 0 := image_eq_zero_of_notMem_tsupport h.2
        rw [h1, h2, sub_zero, abs_zero, zero_mul]
        exact mul_nonneg (by positivity) (add_nonneg (hK0 _) (hK0 _))
    -- `∫ 1_K(x − z) dz = |K| = V`
    have hKi : ∀ x : Euclid n, Integrable (fun z => K.indicator (fun _ => (1 : ℝ)) (x - z)) :=
      fun x => ((integrableOn_const hKfin).integrable_indicator hKm).comp_sub_left x
    have hKint : ∀ x : Euclid n, ∫ z, K.indicator (fun _ => (1 : ℝ)) (x - z) = V := by
      intro x
      rw [integral_sub_left_eq_self (fun z => K.indicator (fun _ => (1 : ℝ)) z) volume x,
        integral_indicator_const _ hKm]
      simp [hV, Measure.real]
    calc |∫ z, (ρ (x - z) * F.indicator (fun _ => (1 : ℝ)) z -
          ρ (x' - z) * F.indicator (fun _ => (1 : ℝ)) z)|
        ≤ ∫ z, |ρ (x - z) * F.indicator (fun _ => (1 : ℝ)) z -
          ρ (x' - z) * F.indicator (fun _ => (1 : ℝ)) z| := abs_integral_le_integral_abs
      _ ≤ ∫ z, Lρ * ‖x - x'‖ * (K.indicator (fun _ => (1 : ℝ)) (x - z) +
          K.indicator (fun _ => (1 : ℝ)) (x' - z)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (((hKi x).add (hKi x')).const_mul _) (Filter.Eventually.of_forall hpt)
      _ = Lρ * ‖x - x'‖ * (V + V) := by
          rw [integral_const_mul, integral_add (hKi x) (hKi x'), hKint x, hKint x']
      _ = 2 * Lρ * V * ‖x - x'‖ := by ring
      _ ≤ max 1 (2 * Lρ * V) * ‖x - x'‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
/-- **Finite sup-norm nets** (the total-boundedness half of Arzelà–Ascoli, i.e. the Arzelà–Ascoli
step of the Rellich compactness argument behind the harmonic approximation lemma, Simon Ch. 5).
If the `g j` are bounded by `C` and `C`-Lipschitz on the compact set `K`, then for every `δ > 0`
there is a finite set `S` of indices such that every `g j` is `δ`-close on `K` to some `g k`,
`k ∈ S`.  With `C' = max C 0 + 1` and `r = δ / (3C')`, cover `K` by finitely many `r`-balls
centred in `T ⊆ K`; the vectors `(g j y)_{y ∈ T}` lie in a compact ball of `T → ℝ`, so finitely
many of them form a `δ/3`-net; then `|g j x − g k x| ≤ C'r + δ/3 + C'r = δ`. -/
theorem Submission.dorag_ha_rb_sup_net : ∀ (n : ℕ) (K : Set (Euclid n)) (g : ℕ → Euclid n → ℝ) (C : ℝ), IsCompact K → (∀ j, ∀ x ∈ K, |g j x| ≤ C) → (∀ j, ∀ x ∈ K, ∀ y ∈ K, |g j x - g j y| ≤ C * ‖x - y‖) → ∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∀ x ∈ K, |g j x - g k x| ≤ δ := by
  intro n K g C hK hbd hlip δ hδ
  -- Step 1: `C' = max C 0 + 1`, `r = δ / (3C')`, and finitely many `r`-balls centred in `T ⊆ K`
  -- cover `K`
  obtain ⟨C', hC'pos, hCC'⟩ : ∃ C' : ℝ, 0 < C' ∧ C ≤ C' :=
    ⟨max C 0 + 1, by linarith [le_max_right C 0], by linarith [le_max_left C 0]⟩
  have hr : 0 < δ / (3 * C') := div_pos hδ (mul_pos three_pos hC'pos)
  have hC'r : C' * (δ / (3 * C')) = δ / 3 := by
    field_simp
  obtain ⟨T, hTK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (δ / (3 * C'))) (fun x _ => ball_mem_nhds x hr)
  -- Step 2: the evaluation vectors `Φ j = (g j y)_{y ∈ T}` lie in a compact ball of `T → ℝ`
  let Φ : ℕ → T → ℝ := fun j y => g j y
  have hrange : range Φ ⊆ closedBall 0 C' := by
    rintro _ ⟨j, rfl⟩
    rw [mem_closedBall, dist_pi_le_iff hC'pos.le]
    intro y
    rw [Pi.zero_apply, Real.dist_eq, sub_zero]
    exact (hbd j y (hTK y y.2)).trans hCC'
  have htb : TotallyBounded (range Φ) :=
    (isCompact_closedBall (0 : T → ℝ) C').totallyBounded.subset hrange
  -- Step 3: a finite `δ/3`-net `t ⊆ range Φ`; each `q ∈ t` is `Φ (invFun Φ q)`
  obtain ⟨t, htΦ, htfin, htcover⟩ :=
    finite_approx_of_totallyBounded htb (δ / 3) (div_pos hδ three_pos)
  refine ⟨htfin.toFinset.image (Function.invFun Φ), fun j => ?_⟩
  -- Step 4: `Φ j` is `δ/3`-close to some `q = Φ k ∈ t`, so `|g j - g k| < δ/3` on `T`
  obtain ⟨q, hqt, hjq⟩ := mem_iUnion₂.1 (htcover (mem_range_self j))
  refine ⟨Function.invFun Φ q, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hqt), ?_⟩
  have hkq : Φ (Function.invFun Φ q) = q := Function.invFun_eq (htΦ hqt)
  have hT : ∀ y ∈ T, |g j y - g (Function.invFun Φ q) y| < δ / 3 := fun y hy =>
    calc |g j y - g (Function.invFun Φ q) y|
        = dist (Φ j ⟨y, hy⟩) (Φ (Function.invFun Φ q) ⟨y, hy⟩) := rfl
      _ ≤ dist (Φ j) (Φ (Function.invFun Φ q)) :=
        dist_le_pi_dist (Φ j) (Φ (Function.invFun Φ q)) ⟨y, hy⟩
      _ = dist (Φ j) q := by rw [hkq]
      _ < δ / 3 := hjq
  -- Step 5: the three-term estimate through a centre `y ∈ T` with `‖x - y‖ < r`
  intro x hx
  obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  have hyK : y ∈ K := hTK y hyT
  have hxy' : ‖x - y‖ < δ / (3 * C') := by
    rw [← dist_eq_norm]
    exact hxy
  have hCr : C * ‖x - y‖ ≤ δ / 3 :=
    calc C * ‖x - y‖ ≤ C' * ‖x - y‖ := mul_le_mul_of_nonneg_right hCC' (norm_nonneg _)
      _ ≤ C' * (δ / (3 * C')) := mul_le_mul_of_nonneg_left hxy'.le hC'pos.le
      _ = δ / 3 := hC'r
  have h1 := hlip j x hx y hyK
  have h2 := hT y hyT
  have h3 := hlip (Function.invFun Φ q) y hyK x hx
  rw [norm_sub_rev] at h3
  calc |g j x - g (Function.invFun Φ q) x|
      ≤ |g j x - g j y| + |g j y - g (Function.invFun Φ q) x| := abs_sub_le _ _ _
    _ ≤ |g j x - g j y| +
          (|g j y - g (Function.invFun Φ q) y| +
            |g (Function.invFun Φ q) y - g (Function.invFun Φ q) x|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ ≤ δ := by linarith
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset

/-- **Local `L¹` total boundedness of the indicators** (step 3 of the BV compactness argument
behind De Giorgi's theorem, Simon 2.6 / [GT01, 7.22]).  If the `F_k ⊆ ℝ^{m+1}` have eventually
bounded perimeter in every ball, then for `R, θ > 0` finitely many `F_i` form a `θ`-net of the
`F_k` in `L¹(B_R)`.  From the bound `C ≥ 0` at radius `R + 1`, valid for `k ≥ k₀`, choose
`ε ≤ 1` with `εC < θ/3` and a mollifier `ρ` supported in `B_ε`; then `1_{F_k}` is `εC`-close
in `L¹(B_R)` to `v_k = ρ * 1_{F_k}`, the `v_k` are uniformly bounded and Lipschitz, so a finite
sup-norm `δ`-net on `closedBall 0 R` with `δ L(B_R) < θ/3` gives the net for `k ≥ k₀`; the
indices `k < k₀` are their own centres. -/
theorem Submission.codim1_rdo_dg_bvc_indicator_totally_bounded : ∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ k in atTop, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → (∀ z, ‖g z‖ ≤ 1) → ∫ z in Fs k, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∀ R : ℝ, 0 < R → ∀ θ : ℝ, 0 < θ → ∃ S : Finset ℕ, ∀ k, ∃ i ∈ S, volume (symmDiff (Fs k) (Fs i) ∩ ball (0 : Euclid (m + 1)) R) < ENNReal.ofReal θ := by
  intro m Fs hmeas hyp R hR θ hθ
  -- Step 1: the bound `C` at radius `R + 1` holds for `k ≥ k₀`; `g = 0` shows `C ≥ 0`
  obtain ⟨C, hev⟩ := hyp (R + 1) (by linarith)
  obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1 hev
  have hC : 0 ≤ C := by
    simpa using hk0 k0 le_rfl (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp)
      (by simp)
  -- Step 2: `ε = min (1/2) (θ / (3(C + 1)))`, so `ε ≤ 1` and `εC < θ/3`, and a mollifier `ρ`
  -- supported in `B_ε`
  set ε : ℝ := min (1 / 2) (θ / (3 * (C + 1))) with hεdef
  have hεpos : 0 < ε := lt_min (by norm_num) (div_pos hθ (by positivity))
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hεC : ε * C < θ / 3 := by
    have h1 : ε ≤ θ / (3 * (C + 1)) := min_le_right _ _
    have h2 : θ / (3 * (C + 1)) * C < θ / 3 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hC).trans_lt h2
  obtain ⟨ρ, hρsmooth, hρcs, hρ0, hρ1, hρs⟩ :=
    Submission.dgcr_stc_exists_normalized_mollifier (m + 1) ε hεpos
  have hρC1 : ContDiff ℝ 1 ρ := hρsmooth.of_le (by exact_mod_cast le_top)
  -- Step 3: `u k = 1_{F_k}` is `εC`-close to `v k = ρ * 1_{F_k}` in `L¹(B_R)` for `k ≥ k₀`
  set u : ℕ → Euclid (m + 1) → ℝ := fun k => (Fs k).indicator (fun _ => (1 : ℝ)) with hu
  set v : ℕ → Euclid (m + 1) → ℝ :=
    fun k x => ∫ y, ρ y * (Fs k).indicator (fun _ => (1 : ℝ)) (x - y) with hv
  have hmoll : ∀ k, k0 ≤ k → ∫ z in ball (0 : Euclid (m + 1)) R, |u k z - v k z| ≤ ε * C :=
    fun k hk => Submission.codim1_rdo_dg_bvc_mollify_l1_le (m + 1) (Fs k) R C ε ρ (hmeas k) hε1
      hρsmooth.continuous hρcs hρ0 hρ1 hρs (hk0 k hk)
  -- Step 4: the `v k` are bounded by `L` and `L`-Lipschitz; a finite sup-norm `δ`-net of the
  -- `v (k₀ + j)` on `closedBall 0 R`, where `δ L(B_R) < θ/3`
  obtain ⟨L, hL⟩ := Submission.codim1_rdo_dg_bvc_mollified_lipschitz (m + 1) ρ hρC1 hρcs hρ0 hρ1
  set V : ℝ := (volume (ball (0 : Euclid (m + 1)) R)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set δ : ℝ := θ / (3 * (V + 1)) with hδdef
  have hδ : 0 < δ := div_pos hθ (by positivity)
  have hδV : δ * V < θ / 3 := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨S', hS'⟩ := Submission.dorag_ha_rb_sup_net (m + 1) (closedBall (0 : Euclid (m + 1)) R)
      (fun j => v (k0 + j)) L (isCompact_closedBall _ _)
      (fun j x _ => (hL (Fs (k0 + j)) (hmeas _)).1 x)
      (fun j x _ y _ => (hL (Fs (k0 + j)) (hmeas _)).2 x y) δ hδ
  -- measurability, bounds and integrability on `B_R` of everything involved
  have hu_meas : ∀ k, Measurable (u k) := fun k => measurable_const.indicator (hmeas k)
  have hu_bd : ∀ k z, |u k z| ≤ 1 := by
    intro k z
    simp only [hu, Set.indicator]
    split_ifs <;> norm_num
  have hv_cont : ∀ k, Continuous (v k) := by
    intro k
    refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
    rw [Real.dist_eq, dist_eq_norm]
    exact ((hL (Fs k) (hmeas k)).2 x y).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  have hv_bd : ∀ k z, |v k z| ≤ L := fun k z => (hL (Fs k) (hmeas k)).1 z
  have hfin : volume (ball (0 : Euclid (m + 1)) R) ≠ ⊤ := measure_ball_lt_top.ne
  have hint : ∀ f : Euclid (m + 1) → ℝ, Measurable f → ∀ M : ℝ, (∀ z, |f z| ≤ M) →
      IntegrableOn f (ball (0 : Euclid (m + 1)) R) := by
    intro f hf M hM
    exact Measure.integrableOn_of_bounded (M := M) hfin hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM z)
  -- Step 5: the centres are `0, …, k₀ - 1` and `k₀ + i'`, `i' ∈ S'`
  refine ⟨Finset.range k0 ∪ S'.image (fun i => k0 + i), fun k => ?_⟩
  by_cases hk : k < k0
  · refine ⟨k, Finset.mem_union_left _ (Finset.mem_range.2 hk), ?_⟩
    simp only [symmDiff_self, Set.bot_eq_empty, Set.empty_inter, measure_empty]
    exact ENNReal.ofReal_pos.2 hθ
  have hk : k0 ≤ k := not_lt.1 hk
  obtain ⟨i', hi'S, hi'⟩ := hS' (k - k0)
  refine ⟨k0 + i', Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi'S), ?_⟩
  have hkk : k0 + (k - k0) = k := Nat.add_sub_cancel' hk
  simp only [hkk] at hi'
  have hi : k0 ≤ k0 + i' := Nat.le_add_right _ _
  set i := k0 + i' with hidef
  -- Step 6: `|u k - u i| ≤ |u k - v k| + |v k - v i| + |u i - v i|`, integrated over `B_R`
  have htri : ∀ z, |u k z - u i z| ≤ |u k z - v k z| + |v k z - v i z| + |u i z - v i z| := by
    intro z
    calc |u k z - u i z| = |(u k z - v k z) + (v k z - v i z) - (u i z - v i z)| := by
          congr 1; ring
      _ ≤ |(u k z - v k z) + (v k z - v i z)| + |u i z - v i z| := abs_sub _ _
      _ ≤ |u k z - v k z| + |v k z - v i z| + |u i z - v i z| := by
          gcongr; exact abs_add_le _ _
  have hm1 : Measurable fun z => |u k z - v k z| :=
    continuous_abs.measurable.comp ((hu_meas k).sub (hv_cont k).measurable)
  have hm2 : Measurable fun z => |v k z - v i z| :=
    continuous_abs.measurable.comp ((hv_cont k).measurable.sub (hv_cont i).measurable)
  have hm3 : Measurable fun z => |u i z - v i z| :=
    continuous_abs.measurable.comp ((hu_meas i).sub (hv_cont i).measurable)
  have hb : ∀ a b : ℝ, |a| ≤ 1 → |b| ≤ L → |(|a - b|)| ≤ 1 + L := by
    intro a b ha hb
    rw [abs_abs]
    exact (abs_sub _ _).trans (add_le_add ha hb)
  have hI1 := hint _ hm1 (1 + L) fun z => hb _ _ (hu_bd k z) (hv_bd k z)
  have hI2 := hint _ hm2 (L + L) fun z => by
    rw [abs_abs]
    exact (abs_sub _ _).trans (add_le_add (hv_bd k z) (hv_bd i z))
  have hI3 := hint _ hm3 (1 + L) fun z => hb _ _ (hu_bd i z) (hv_bd i z)
  have h2 : ∫ z in ball (0 : Euclid (m + 1)) R, |v k z - v i z| ≤ δ * V := by
    calc ∫ z in ball (0 : Euclid (m + 1)) R, |v k z - v i z|
        ≤ ∫ z in ball (0 : Euclid (m + 1)) R, δ :=
          setIntegral_mono_on hI2 (integrableOn_const hfin) measurableSet_ball
            fun z hz => hi' z (ball_subset_closedBall hz)
      _ = δ * V := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
  have key : ∫ z in ball (0 : Euclid (m + 1)) R, |u k z - u i z| < θ := by
    have hI12 : IntegrableOn (fun z => |u k z - v k z| + |v k z - v i z|)
        (ball (0 : Euclid (m + 1)) R) := hI1.add hI2
    calc ∫ z in ball (0 : Euclid (m + 1)) R, |u k z - u i z|
        ≤ ∫ z in ball (0 : Euclid (m + 1)) R,
            (|u k z - v k z| + |v k z - v i z| + |u i z - v i z|) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
            (hI12.add hI3) (Filter.Eventually.of_forall htri)
      _ = (∫ z in ball (0 : Euclid (m + 1)) R, |u k z - v k z|) +
            (∫ z in ball (0 : Euclid (m + 1)) R, |v k z - v i z|) +
            ∫ z in ball (0 : Euclid (m + 1)) R, |u i z - v i z| := by
          rw [integral_add hI12 hI3, integral_add hI1 hI2]
      _ ≤ ε * C + δ * V + ε * C := by
          gcongr
          · exact hmoll k hk
          · exact hmoll i hi
      _ < θ := by linarith
  -- Step 7: `|u k - u i| = 1_{F_k Δ F_i}`, so the integral is `L((F_k Δ F_i) ∩ B_R)`
  have hsd : ∀ z, |u k z - u i z| = (symmDiff (Fs k) (Fs i)).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    simp only [hu, Set.indicator, Set.mem_symmDiff]
    by_cases h1 : z ∈ Fs k <;> by_cases h2 : z ∈ Fs i <;> simp [h1, h2, Set.mem_symmDiff]
  have hA : MeasurableSet (symmDiff (Fs k) (Fs i)) := (hmeas k).symmDiff (hmeas i)
  have hmeas_eq : volume (symmDiff (Fs k) (Fs i) ∩ ball (0 : Euclid (m + 1)) R)
      = ENNReal.ofReal (∫ z in ball (0 : Euclid (m + 1)) R, |u k z - u i z|) := by
    simp_rw [hsd]
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply hA, ENNReal.ofReal_toReal]
    exact (measure_mono Set.inter_subset_right |>.trans_lt measure_ball_lt_top).ne
  rw [hmeas_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hθ).2 key
/-- **Infinite pairwise close subsets** (the pigeonhole step behind "every sequence in a totally
bounded subset has a Cauchy subsequence" in the BV compactness theorem, Simon Ch. 2, 2.6, applied
to the indicators `1_{F_k}` in `L¹(B_R)`).  Suppose that for all `R, θ > 0` there is a finite set
`S` such that every `F_k` has some `i ∈ S` with `L((F_k Δ F_i) ∩ B_R) < θ`.  Then every infinite
`I ⊆ ℕ` contains an infinite `J ⊆ I` with `L((F_j Δ F_l) ∩ B_{r+1}) ≤ 2^{-r}` for all `j, l ∈ J`.
Take `R = r + 1`, `θ = 2^{-(r+1)}` and a centre map `c : ℕ → S`; then some fibre
`J = I ∩ c⁻¹{s}` is infinite, and `F_j Δ F_l ⊆ (F_j Δ F_s) ∪ (F_l Δ F_s)` gives
`2^{-(r+1)} + 2^{-(r+1)} = 2^{-r}`. -/
theorem Submission.codim1_rdo_dg_bvc_infinite_close_subset : ∀ (n : ℕ) (Fs : ℕ → Set (Euclid n)), (∀ R : ℝ, 0 < R → ∀ θ : ℝ, 0 < θ → ∃ S : Finset ℕ, ∀ k, ∃ i ∈ S, volume (symmDiff (Fs k) (Fs i) ∩ ball (0 : Euclid n) R) < ENNReal.ofReal θ) → ∀ (r : ℕ) (I : Set ℕ), I.Infinite → ∃ J ⊆ I, J.Infinite ∧ ∀ j ∈ J, ∀ l ∈ J, volume (symmDiff (Fs j) (Fs l) ∩ ball (0 : Euclid n) ((r : ℝ) + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ r := by
  intro n Fs hTB r I hI
  -- Step 1: radius `r + 1` and accuracy `2^{-(r+1)}` give `S` and a centre map `c : ℕ → S`
  obtain ⟨S, hS⟩ := hTB ((r : ℝ) + 1) (by positivity) ((1 / 2 : ℝ) ^ (r + 1)) (by positivity)
  choose c hcS hc using hS
  have hθ : ENNReal.ofReal ((1 / 2 : ℝ) ^ (r + 1)) = (2⁻¹ : ℝ≥0∞) ^ (r + 1) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  -- Step 2: `I ⊆ ⋃_{s ∈ S} (I ∩ c⁻¹{s})`, so some fibre `I ∩ c⁻¹{s}` is infinite
  obtain ⟨s, -, hJ⟩ : ∃ s ∈ S, (I ∩ c ⁻¹' {s}).Infinite := by
    by_contra! h
    exact hI ((S.finite_toSet.biUnion fun s hs => h s hs).subset
      fun k hk => mem_biUnion (hcS k) ⟨hk, rfl⟩)
  refine ⟨I ∩ c ⁻¹' {s}, inter_subset_left, hJ, fun j hj l hl => ?_⟩
  -- Step 3: `F_j Δ F_l ⊆ (F_j Δ F_s) ∪ (F_l Δ F_s)`, monotonicity and subadditivity
  set B := ball (0 : Euclid n) ((r : ℝ) + 1)
  have hjs : volume (symmDiff (Fs j) (Fs s) ∩ B) ≤ (2⁻¹ : ℝ≥0∞) ^ (r + 1) := by
    rw [← hθ, ← (hj.2 : c j = s)]
    exact (hc j).le
  have hls : volume (symmDiff (Fs l) (Fs s) ∩ B) ≤ (2⁻¹ : ℝ≥0∞) ^ (r + 1) := by
    rw [← hθ, ← (hl.2 : c l = s)]
    exact (hc l).le
  have htri : symmDiff (Fs j) (Fs l) ∩ B ⊆
      (symmDiff (Fs j) (Fs s) ∩ B) ∪ (symmDiff (Fs l) (Fs s) ∩ B) := by
    rintro x ⟨hx, hxB⟩
    rcases symmDiff_triangle (Fs j) (Fs s) (Fs l) hx with h | h
    · exact Or.inl ⟨h, hxB⟩
    · exact Or.inr ⟨by rwa [symmDiff_comm] at h, hxB⟩
  calc volume (symmDiff (Fs j) (Fs l) ∩ B)
      ≤ volume (symmDiff (Fs j) (Fs s) ∩ B) + volume (symmDiff (Fs l) (Fs s) ∩ B) :=
        (measure_mono htri).trans (measure_union_le _ _)
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (r + 1) + (2⁻¹ : ℝ≥0∞) ^ (r + 1) := add_le_add hjs hls
    _ = (2⁻¹ : ℝ≥0∞) ^ r := by rw [pow_succ, ← div_eq_mul_inv, ENNReal.add_halves]
/-- **Diagonal extraction** (Simon Ch. 6, proof of 7.2, chapter-06.txt lines 2101–2105:
"apply (1) with `ε = 1, 1/2, 1/4` etc. to extract a subsequence `{T_{j_r}}` …
`d(T_{j_{r+1}}, T_{j_r}) < 2^{-r}`", with `2^{-r}`-closeness replaced by an arbitrary relation
`C r`).  If, for each `r`, every infinite `I ⊆ ℕ` contains an infinite `J ⊆ I` all of whose pairs
are `C r`-related, then some strictly increasing `φ` has `C r (φ (r + 1)) (φ r)` for every `r`.
Refining `I₀ = ℕ` gives nested infinite sets `I_{r+1} ⊆ I_r` with `I_{r+1}` pairwise
`C r`-related; an increasing choice `φ(r) ∈ I_{r+1}` puts both `φ(r)` and `φ(r + 1)` in
`I_{r+1}`. -/
theorem Submission.cmc_fc_cs_diagonal_subseq : ∀ (C : ℕ → ℕ → ℕ → Prop), (∀ (r : ℕ) (I : Set ℕ), I.Infinite → ∃ J ⊆ I, J.Infinite ∧ ∀ j ∈ J, ∀ l ∈ J, C r j l) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ r, C r (φ (r + 1)) (φ r) := by
  intro C hC
  -- Step 1: refinements `F(r, I) ⊆ I`, infinite, with all pairs in relation `C r`
  choose F hFsub hFinf hFC using hC
  -- Step 2: nested infinite index sets `I₀ = ℕ`, `I_{r+1} = F(r, I_r)`
  let I : ℕ → {s : Set ℕ // s.Infinite} := fun r =>
    Nat.rec ⟨univ, infinite_univ⟩ (fun r s => ⟨F r s.1 s.2, hFinf r s.1 s.2⟩) r
  have hsub : ∀ r, (I (r + 1)).1 ⊆ (I r).1 := fun r => hFsub r (I r).1 (I r).2
  have hpair : ∀ r, ∀ j ∈ (I (r + 1)).1, ∀ l ∈ (I (r + 1)).1, C r j l :=
    fun r => hFC r (I r).1 (I r).2
  -- Step 3: `I_{r+1}` is unbounded: `g(r, a) ∈ I_{r+1}` and `a < g(r, a)`
  choose g hgI hglt using fun r : ℕ => (I (r + 1)).2.exists_gt
  -- Step 4: diagonal choice `φ(0) = g(0, 0)`, `φ(r + 1) = g(r + 1, φ(r)) ∈ I_{r+2}`
  let φ : ℕ → ℕ := fun r => Nat.rec (g 0 0) (fun r a => g (r + 1) a) r
  have hφI : ∀ r, φ r ∈ (I (r + 1)).1 := by
    intro r
    cases r with
    | zero => exact hgI 0 0
    | succ r => exact hgI (r + 1) (φ r)
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun r => hglt (r + 1) (φ r)
  -- Step 5: `φ(r + 1) ∈ I_{r+2} ⊆ I_{r+1}` and `φ(r) ∈ I_{r+1} = F(r, I_r)`
  exact ⟨φ, hφ, fun r => hpair r _ (hsub (r + 1) (hφI (r + 1))) _ (hφI r)⟩
/-- **Limit of a fast-Cauchy sequence of sets** (the completeness step of the BV compactness
argument in the De Giorgi proof, cf. Simon Ch. 2, 2.6; the Riesz–Fischer argument specialized to
indicators).  If the Borel sets `Gⱼ ⊆ ℝⁿ` satisfy `L((G_{i+1} Δ Gᵢ) ∩ B_{i+1}(0)) ≤ 2⁻ⁱ` for
every `i`, then the liminf `F₀ = ⋃_J ⋂_i G_{J+i}` is Borel and `L((Gⱼ Δ F₀) ∩ B_R(0)) → 0` for
every `R`: `Gⱼ Δ F₀ ⊆ ⋃_l (G_{j+l+1} Δ G_{j+l})`, and for `j ≥ ⌈R⌉₊` every ball `B_{j+l+1}(0)`
contains `B_R(0)`, so the measure is at most `∑_l 2^{-(j+l)} = 2 · 2⁻ʲ → 0`. -/
theorem Submission.codim1_rdo_dg_bvc_limit_of_fast_cauchy : ∀ (n : ℕ) (Gs : ℕ → Set (Euclid n)), (∀ j, MeasurableSet (Gs j)) → (∀ i : ℕ, volume (symmDiff (Gs (i + 1)) (Gs i) ∩ ball (0 : Euclid n) ((i : ℝ) + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ i) → ∃ F₀ : Set (Euclid n), MeasurableSet F₀ ∧ ∀ R : ℝ, Tendsto (fun j => volume (symmDiff (Gs j) F₀ ∩ ball (0 : Euclid n) R)) atTop (𝓝 0) := by
  intro n Gs hGm hG
  -- Step 1: the liminf `F₀ = ⋃_J ⋂_i G_{J+i}` is Borel
  set F₀ : Set (Euclid n) := ⋃ J : ℕ, ⋂ i : ℕ, Gs (J + i) with hF₀
  refine ⟨F₀, MeasurableSet.iUnion fun J => MeasurableSet.iInter fun i => hGm _, fun R => ?_⟩
  -- Step 2: `Gⱼ Δ F₀ ⊆ ⋃_l (G_{j+l+1} Δ G_{j+l})`
  have hincl : ∀ j, symmDiff (Gs j) F₀ ⊆ ⋃ l : ℕ, symmDiff (Gs (j + l + 1)) (Gs (j + l)) := by
    intro j x hx
    by_contra hxU
    simp only [mem_iUnion, not_exists] at hxU
    -- `x` is in no `G_{j+l+1} Δ G_{j+l}`, so by induction `x ∈ G_{j+l} ↔ x ∈ Gⱼ` for every `l`
    have hstep : ∀ l, (x ∈ Gs (j + l + 1) ↔ x ∈ Gs (j + l)) := by
      intro l
      have hl := hxU l
      rw [Set.mem_symmDiff] at hl
      tauto
    have hall : ∀ l, (x ∈ Gs (j + l) ↔ x ∈ Gs j) := by
      intro l
      induction l with
      | zero => simp
      | succ l ih => rw [← ih, ← add_assoc]; exact hstep l
    -- hence `x ∈ F₀ ↔ x ∈ Gⱼ`, contradicting `x ∈ Gⱼ Δ F₀`
    have hF : x ∈ F₀ ↔ x ∈ Gs j := by
      constructor
      · intro hx0
        rw [hF₀, mem_iUnion] at hx0
        obtain ⟨J, hJ⟩ := hx0
        have hJj := mem_iInter.1 hJ j
        rw [Nat.add_comm] at hJj
        exact (hall J).1 hJj
      · intro hxj
        rw [hF₀, mem_iUnion]
        exact ⟨j, mem_iInter.2 fun i => (hall i).2 hxj⟩
    rw [Set.mem_symmDiff] at hx
    tauto
  -- Step 3: for `j ≥ N = ⌈R⌉₊` and every `l`, `B_R(0) ⊆ B_{j+l+1}(0)`, so by countable
  -- subadditivity the measure is at most `∑_l 2^{-(j+l)} = 2⁻ʲ · ∑_l 2⁻ˡ = 2 · 2⁻ʲ`
  set N : ℕ := ⌈R⌉₊
  have hbound : ∀ j, N ≤ j →
      volume (symmDiff (Gs j) F₀ ∩ ball (0 : Euclid n) R) ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j hj
    calc volume (symmDiff (Gs j) F₀ ∩ ball (0 : Euclid n) R)
        ≤ volume (⋃ l : ℕ, symmDiff (Gs (j + l + 1)) (Gs (j + l)) ∩
            ball (0 : Euclid n) (((j + l : ℕ) : ℝ) + 1)) := by
          refine measure_mono ?_
          rintro x ⟨hx, hxR⟩
          obtain ⟨l, hl⟩ := mem_iUnion.1 (hincl j hx)
          refine mem_iUnion.2 ⟨l, hl, ball_subset_ball ?_ hxR⟩
          have h1 : R ≤ (N : ℝ) := Nat.le_ceil R
          have h2 : (N : ℝ) ≤ ((j + l : ℕ) : ℝ) := by
            exact_mod_cast hj.trans (Nat.le_add_right j l)
          linarith
      _ ≤ ∑' l : ℕ, volume (symmDiff (Gs (j + l + 1)) (Gs (j + l)) ∩
            ball (0 : Euclid n) (((j + l : ℕ) : ℝ) + 1)) := measure_iUnion_le _
      _ ≤ ∑' l : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + l) := ENNReal.tsum_le_tsum fun l => hG (j + l)
      _ = (2⁻¹ : ℝ≥0∞) ^ j * ∑' l : ℕ, (2⁻¹ : ℝ≥0∞) ^ l := by
          rw [← ENNReal.tsum_mul_left]
          simp_rw [pow_add]
      _ = 2 * (2⁻¹ : ℝ≥0∞) ^ j := by
          rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, mul_comm]
  -- Step 4: `2 · 2⁻ʲ → 0`, and the measures are squeezed between `0` and this bound for `j ≥ N`
  have hlim : Tendsto (fun j : ℕ => 2 * (2⁻¹ : ℝ≥0∞) ^ j) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two))
      (Or.inr (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨N, hbound⟩)

/-- **Compactness for sets of locally bounded perimeter** (Simon Ch. 2, 2.6, chapter-02.txt
lines 598–626, for `u_k = 1_{F_k}` on `U = ℝ^{m+1}`; the precompactness that the book cites from
[GT01, Theorem 7.22] is proved by mollification and Arzelà–Ascoli).  If for every `R > 0` there is
`C_R` with `∫_{F_k} div g ≤ C_R` for all large `k` and every `C¹` field `g` with `|g| ≤ 1` and
compact support in `B_R(0)`, then a subsequence `F_{ψ j}` converges locally in measure to a Borel
set `F₀`.  The indicators `1_{F_k}` are totally bounded in `L¹(B_R)` for every `R`; so every
infinite index set contains an infinite one whose members are pairwise `2^{-r}`-close on
`B_{r+1}`; the diagonal subsequence is `2^{-r}`-fast Cauchy on `B_{r+1}`, hence converges. -/
theorem Submission.codim1_rdo_dg_bv_set_compactness : ∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ k in atTop, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → (∀ z, ‖g z‖ ≤ 1) → ∫ z in Fs k, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (ψ : ℕ → ℕ) (F₀ : Set (Euclid (m + 1))), StrictMono ψ ∧ MeasurableSet F₀ ∧ ∀ R : ℝ, Tendsto (fun j => volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R)) atTop (𝓝 0) := by
  intro m Fs hmeas hdiv
  -- Steps 1–3: for every `R, θ > 0`, finitely many `F_i` are `θ`-close in measure on `B_R` to
  -- every `F_k` (mollification estimate and finite sup-norm nets of the mollified indicators)
  have hTB := Submission.codim1_rdo_dg_bvc_indicator_totally_bounded m Fs hmeas hdiv
  -- Step 4: every infinite `I ⊆ ℕ` contains an infinite `J` whose members are pairwise
  -- `2^{-r}`-close on `B_{r+1}`
  have hJ := Submission.codim1_rdo_dg_bvc_infinite_close_subset (m + 1) Fs hTB
  -- Step 4: diagonal extraction of a strictly increasing `ψ` with `F_{ψ(r+1)}` and `F_{ψ r}`
  -- `2^{-r}`-close on `B_{r+1}`
  obtain ⟨ψ, hψ, hclose⟩ := Submission.cmc_fc_cs_diagonal_subseq
    (fun r j l => volume (symmDiff (Fs j) (Fs l) ∩ ball (0 : Euclid (m + 1)) ((r : ℝ) + 1)) ≤
      (2⁻¹ : ℝ≥0∞) ^ r) hJ
  -- Step 5: the fast Cauchy subsequence converges locally in measure to a Borel `F₀`
  obtain ⟨F₀, hF₀, hconv⟩ := Submission.codim1_rdo_dg_bvc_limit_of_fast_cauchy (m + 1)
    (fun j => Fs (ψ j)) (fun j => hmeas (ψ j)) hclose
  exact ⟨ψ, F₀, hψ, hF₀, hconv⟩
/-- **Simon Ch. 3, 4.3 (8)–(9)** (translation identity): for a Borel set `F ⊆ ℝⁿ`,
`ζ ∈ C¹_c(ℝⁿ)`, `w ∈ ℝⁿ` and `t ∈ ℝ`,
`∫_F ζ(z − t w) dz = ∫_F ζ(z) dz − ∫₀ᵗ ∫_F Dζ(z − s w)(w) dz ds` (oriented `∫₀ᵗ`).  Integrate
the fundamental theorem of calculus for `s ↦ ζ(z − s w)` over `z ∈ F` and swap the integrals
(Fubini); `Dζ(z − s w)(w)` is bounded and, for `s` between `0` and `t`, vanishes for `z` off the
compact set `tsupport ζ + [0, t] w`. -/
theorem Submission.codim1_rdo_dg_hr_translate_integral_eq : ∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (ζ : EuclideanSpace ℝ (Fin n) → ℝ) (w : EuclideanSpace ℝ (Fin n)) (t : ℝ), MeasurableSet F → ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z in F, ζ (z - t • w) = (∫ z in F, ζ z) - ∫ s in (0 : ℝ)..t, ∫ z in F, fderiv ℝ ζ (z - s • w) w := by
  intro n F ζ w t hF hζ hcs
  -- `Dζ` is continuous and bounded by `M`
  have hDc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hDc.bounded_above_of_compact_support (hcs.fderiv ℝ)
  -- `G (s, z) = Dζ (z - s • w) w` is continuous
  have hGc : Continuous (uncurry fun (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) =>
      fderiv ℝ ζ (z - s • w) w) :=
    (hDc.comp (continuous_snd.sub (continuous_fst.smul continuous_const))).clm_apply
      continuous_const
  -- for `s ∈ uIcc 0 t`, `Dζ (z - s • w) = 0` off the compact `K' = tsupport ζ + uIcc 0 t • w`
  obtain ⟨K', hK', hvan⟩ : ∃ K' : Set (EuclideanSpace ℝ (Fin n)), IsCompact K' ∧
      ∀ s ∈ uIcc (0 : ℝ) t, ∀ z ∉ K', fderiv ℝ ζ (z - s • w) = 0 := by
    refine ⟨(fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.1 + p.2 • w) '' (tsupport ζ ×ˢ uIcc 0 t),
      (hcs.isCompact.prod isCompact_uIcc).image
        (continuous_fst.add (continuous_snd.smul continuous_const)), fun s hs z hz => ?_⟩
    by_contra h
    exact hz ⟨(z - s • w, s), ⟨support_fderiv_subset ℝ h, hs⟩, sub_add_cancel z (s • w)⟩
  -- FTC along `s ↦ ζ (z - s • w)`, whose derivative is `-G (s, z)`
  have hFTC : ∀ z, ζ (z - t • w) - ζ z = -∫ s in (0 : ℝ)..t, fderiv ℝ ζ (z - s • w) w := by
    intro z
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
        HasDerivAt (fun s => ζ (z - s • w)) (-fderiv ℝ ζ (z - s • w) w) s := by
      intro s _
      have h1 : HasDerivAt (fun s : ℝ => z - s • w) (-w) s := by
        simpa using ((hasDerivAt_id s).smul_const w).const_sub z
      have h2 := ((hζ.differentiable one_ne_zero) (z - s • w)).hasFDerivAt.comp_hasDerivAt s h1
      rw [map_neg] at h2
      exact h2
    have hint : IntervalIntegrable (fun s => -fderiv ℝ ζ (z - s • w) w) volume 0 t :=
      ((hDc.comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
        continuous_const).neg.intervalIntegrable _ _
    rw [← intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  -- `G` is integrable for `(volume|uIoc 0 t) ⊗ (volume|F)`: a.e. `|G (s, z)| ≤ M ‖w‖ 1_{K'}(z)`
  have hint : Integrable (uncurry fun (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) =>
      fderiv ℝ ζ (z - s • w) w) ((volume.restrict (uIoc 0 t)).prod (volume.restrict F)) := by
    have hbound : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (1 : ℝ) * K'.indicator (fun _ => M * ‖w‖) p.2)
        ((volume.restrict (uIoc 0 t)).prod (volume.restrict F)) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := K'.indicator fun _ => M * ‖w‖)
        (integrableOn_const (s := uIoc 0 t) measure_Ioc_lt_top.ne enorm_ne_top).integrable
        ((integrable_indicator_iff hK'.measurableSet).2
          (integrableOn_const hK'.measure_lt_top.ne enorm_ne_top))
    have hfst : ∀ᵐ p ∂((volume.restrict (uIoc (0 : ℝ) t)).prod (volume.restrict F)),
        p.1 ∈ uIoc (0 : ℝ) t :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)
    refine hbound.mono' hGc.aestronglyMeasurable ?_
    filter_upwards [hfst] with ⟨s, z⟩ hs
    simp only [uncurry_apply_pair, one_mul]
    by_cases hz : z ∈ K'
    · rw [indicator_of_mem hz]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
    · rw [indicator_of_notMem hz, hvan s (uIoc_subset_uIcc hs) z hz]
      simp
  -- `ζ (· - t • w)` and `ζ` are continuous with compact support, hence integrable
  have hi2 : Integrable ζ := hζ.continuous.integrable_of_hasCompactSupport hcs
  have hi1 : Integrable (fun z => ζ (z - t • w)) :=
    (hζ.continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hcs.comp_homeomorph (Homeomorph.subRight (t • w)))
  -- integrate the FTC identity over `F` and swap the order of integration
  have hswap : ∫ s in (0 : ℝ)..t, ∫ z in F, fderiv ℝ ζ (z - s • w) w =
      ∫ z in F, ∫ s in (0 : ℝ)..t, fderiv ℝ ζ (z - s • w) w :=
    intervalIntegral_integral_swap hint
  have hsplit : ∫ z in F, (ζ (z - t • w) - ζ z) =
      -∫ z in F, ∫ s in (0 : ℝ)..t, fderiv ℝ ζ (z - s • w) w := by
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ hFTC)
  rw [integral_sub hi1.integrableOn hi2.integrableOn] at hsplit
  rw [hswap]
  linarith
/-- **Sign version of the fundamental lemma**: if `f` is locally integrable on `ℝⁿ` and
`∫ g f ≥ 0` for every nonnegative `C¹` function `g` with compact support, then `f ≥ 0` a.e.
For compact `K`, smooth Urysohn functions `gⱼ` (`0 ≤ gⱼ ≤ 1`, `gⱼ = 1` on `K`,
`support gⱼ = K_{uⱼ}`, `uⱼ ↓ 0`) are admissible tests with `gⱼ → 1_K` pointwise and
`|gⱼ f| ≤ 1_{K¹}|f|`, so dominated convergence gives `∫_K f ≥ 0`.  If `{f < 0}` had positive
measure, inner regularity would give a compact `K ⊆ {f < 0}` of positive measure, on which
`∫_K f < 0`. -/
theorem Submission.codim1_rdo_dg_hr_ae_nonneg_of_test_nonneg : ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ), LocallyIntegrable f volume → (∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → (∀ x, 0 ≤ g x) → 0 ≤ ∫ x, g x * f x) → ∀ᵐ x ∂volume, 0 ≤ f x := by
  intro n f hf htest
  -- Steps 1–3: `0 ≤ ∫_K f` for every compact `K`
  have hcpt : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → 0 ≤ ∫ x in K, f x := by
    intro K hK
    have hK1 : IsCompact (cthickening 1 K) := hK.cthickening
    -- radii `u j ∈ (0, 1)` with `u j → 0`
    obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ j, u j ∈ Ioo 0 1) ∧
        Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' zero_lt_one
    have vK : ∀ j, thickening (u j) K ⊆ cthickening 1 K :=
      fun j => thickening_subset_cthickening_of_le (u_pos j).2.le K
    -- smooth Urysohn functions `g j` with `support (g j) = K_{u j}` and `g j = 1` on `K`
    have : ∀ j, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g ∧ range g ⊆ Icc 0 1 ∧
        support g = thickening (u j) K ∧ ∀ x ∈ K, g x = 1 := by
      intro j
      obtain ⟨g, hg, hgr, hgs, hg1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
        isOpen_thickening hK.isClosed (self_subset_thickening (u_pos j).1 K)
      exact ⟨g, hg, hgr, hgs, fun x hx => (hg1 x).1 hx⟩
    choose g g_diff g_range g_supp hg1 using this
    have hnn : ∀ j, 0 ≤ ∫ x, g j x * f x := by
      intro j
      refine htest _ (g_diff j) ?_ (fun x => (g_range j (mem_range_self x)).1)
      apply HasCompactSupport.of_support_subset_isCompact hK1
      rw [g_supp]
      exact vK j
    -- dominated convergence: `∫ g j * f → ∫_K f`
    have L : Tendsto (fun j => ∫ x, g j x * f x) atTop (𝓝 (∫ x in K, f x)) := by
      rw [← integral_indicator hK.measurableSet]
      let bound : EuclideanSpace ℝ (Fin n) → ℝ := (cthickening 1 K).indicator fun x => ‖f x‖
      have A : ∀ j, AEStronglyMeasurable (fun x => g j x * f x) volume :=
        fun j => (g_diff j).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
      have B : Integrable bound volume := by
        rw [integrable_indicator_iff hK1.measurableSet]
        exact (hf.integrableOn_isCompact hK1).norm
      have C : ∀ j, ∀ᵐ x ∂volume, ‖g j x * f x‖ ≤ bound x := by
        intro j
        filter_upwards with x
        rw [norm_mul]
        refine le_indicator_apply (fun _ => ?_) (fun hxK => ?_)
        · have h01 := g_range j (mem_range_self (f := g j) x)
          have : ‖g j x‖ ≤ 1 := by
            rw [Real.norm_of_nonneg h01.1]
            exact h01.2
          exact mul_le_of_le_one_left (norm_nonneg _) this
        · have : g j x = 0 := by
            rw [← notMem_support, g_supp]
            contrapose hxK
            exact vK j hxK
          simp [this]
      have D : ∀ᵐ x ∂volume, Tendsto (fun j => g j x * f x) atTop (𝓝 (K.indicator f x)) := by
        filter_upwards with x
        by_cases hxK : x ∈ K
        · have : ∀ j, g j x = 1 := fun j => hg1 j x hxK
          simp [this, indicator_of_mem hxK f]
        · simp_rw [indicator_of_notMem hxK f]
          apply tendsto_const_nhds.congr'
          suffices H : ∀ᶠ j in atTop, g j x = 0 by
            filter_upwards [H] with j hj using by simp [hj]
          obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε K := by
            rw [← hK.isClosed.closure_eq, closure_eq_iInter_thickening K] at hxK
            simpa using hxK
          filter_upwards [(tendsto_order.1 u_lim).2 _ εpos] with j hj
          rw [← notMem_support, g_supp]
          contrapose hε
          exact thickening_mono hj.le K hε
      exact tendsto_integral_of_dominated_convergence bound A B C D
    exact ge_of_tendsto' L hnn
  -- Steps 4–6: `{f < 0}` is null; take a measurable `T ⊆ {f < 0}` with `T =ᵐ {f < 0}`
  rw [ae_iff]
  simp only [not_le]
  by_contra hS
  obtain ⟨T, hTS, hTm, hTeq⟩ := (nullMeasurableSet_lt hf.aestronglyMeasurable.aemeasurable
    aemeasurable_const : NullMeasurableSet {x | f x < 0} volume).exists_measurable_subset_ae_eq
  have hTpos : 0 < volume T := by
    rw [measure_congr hTeq]
    exact pos_iff_ne_zero.2 hS
  -- inner regularity: a compact `K ⊆ T` of positive measure
  obtain ⟨K, hKT, hKc, hKpos⟩ := hTm.exists_lt_isCompact hTpos
  -- `∫_K f < 0` since `f < 0` on `K`
  have hneg : 0 < ∫ x in K, -f x := by
    have hfK : IntegrableOn f K volume := hf.integrableOn_isCompact hKc
    rw [setIntegral_pos_iff_support_of_nonneg_ae (f := fun x => -f x) _ hfK.neg]
    · have : support (fun x => -f x) ∩ K = K := by
        refine inter_eq_right.2 fun x hx => ?_
        have : f x < 0 := hTS (hKT hx)
        rw [mem_support]
        linarith
      rwa [this]
    · exact ae_restrict_of_forall_mem hKc.measurableSet fun x hx => by
        have : f x < 0 := hTS (hKT hx)
        simp only [Pi.zero_apply]
        linarith
  rw [integral_neg] at hneg
  linarith [hcpt K hKc]

/-- **Tangential invariance** (step 2 of the half-space rigidity behind Simon Ch. 3, 4.3: "it
follows that `F = ℝⁿ × H`").  If the Borel set `F ⊆ ℝⁿ` has `∫_F Dζ(z)(w) dz = 0` for every
compactly supported `C¹` function `ζ`, then `z + w ∈ F ↔ z ∈ F` for a.e. `z`.  The translation
identity with `t = 1` gives `∫_F ζ(z − w) dz = ∫_F ζ`, since every translate `ζ(· − s w)` is
again admissible; substituting `z = y + w` turns this into `∫ ζ 1_F(· + w) = ∫ ζ 1_F`, and the
fundamental lemma of the calculus of variations gives `1_F(· + w) = 1_F` a.e. -/
theorem Submission.codim1_rdo_dg_hr_ae_translate_invariant : ∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n)), MeasurableSet F → (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∫ z in F, fderiv ℝ ζ z w = 0) → ∀ᵐ z ∂volume, (z + w ∈ F ↔ z ∈ F) := by
  intro n F w hF hζ
  -- `ζ(· − s w)` is again admissible, with derivative `Dζ(· − s w)`: the inner integrals vanish
  have hinner : ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∀ s : ℝ, ∫ z in F, fderiv ℝ ζ (z - s • w) w = 0 := by
    intro ζ hζc hζs s
    have h := hζ (fun y => ζ (y - s • w)) (hζc.comp (contDiff_id.sub contDiff_const))
      (hζs.comp_homeomorph (Homeomorph.subRight (s • w)))
    simpa only [fderiv_comp_sub] using h
  -- the translation identity with `t = 1`
  have htrans : ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∫ z in F, ζ (z - w) = ∫ z in F, ζ z := by
    intro ζ hζc hζs
    have h := Submission.codim1_rdo_dg_hr_translate_integral_eq n F ζ w 1 hF hζc hζs
    simpa only [one_smul, hinner ζ hζc hζs, intervalIntegral.integral_zero, sub_zero] using h
  -- substituting `z = y + w`: `∫ ζ 1_F(· + w) = ∫ ζ 1_F`
  have hG : MeasurableSet ((fun y => y + w) ⁻¹' F) := hF.preimage (measurable_add_const w)
  have hint : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      ∫ y, g y • ((fun y => y + w) ⁻¹' F).indicator (fun _ => (1 : ℝ)) y
        = ∫ y, g y • F.indicator (fun _ => (1 : ℝ)) y := by
    intro g hgc hgs
    have e1 : (fun y => g y • ((fun y => y + w) ⁻¹' F).indicator (fun _ => (1 : ℝ)) y)
        = fun y => F.indicator (fun z => g (z - w)) (y + w) := by
      funext y
      by_cases hy : y + w ∈ F <;> simp [hy]
    have e2 : (fun y => g y • F.indicator (fun _ => (1 : ℝ)) y) = F.indicator g := by
      funext y
      by_cases hy : y ∈ F <;> simp [hy]
    rw [e1, e2, integral_add_right_eq_self (F.indicator fun z => g (z - w)) w,
      integral_indicator hF, integral_indicator hF]
    exact htrans g hgc hgs
  -- the fundamental lemma: `1_F(· + w) = 1_F` a.e.
  have hae : ∀ᵐ y ∂volume, ((fun y => y + w) ⁻¹' F).indicator (fun _ => (1 : ℝ)) y
      = F.indicator (fun _ => (1 : ℝ)) y :=
    ae_eq_of_integral_contDiff_smul_eq ((locallyIntegrable_const 1).indicator hG)
      ((locallyIntegrable_const 1).indicator hF)
      (fun g hgc hgs => hint g (hgc.of_le (by simp)) hgs)
  -- equal indicators: `z + w ∈ F ↔ z ∈ F`
  filter_upwards [hae] with z hz
  by_cases h1 : z + w ∈ F <;> by_cases h2 : z ∈ F <;> simp_all
/-- Normal monotonicity (Simon Ch. 3, 4.3: "`H` is non-decreasing"): if `∫_F Dζ(z)(v) dz ≤ 0`
for every nonnegative `ζ ∈ C¹_c(ℝⁿ)`, then for `t ≥ 0` and a.e. `z`, `z ∈ F` implies
`z + t v ∈ F`.  The hypothesis for the translates `ζ(· − s v)` gives
`g(s) = ∫_F Dζ(z − s v)(v) dz ≤ 0`, so the translation identity
`codim1_rdo_dg_hr_translate_integral_eq` yields `∫_F ζ ≤ ∫_F ζ(· − t v)`.  Substituting
`z = y + t v`, `f = 1_F(· + t v) − 1_F` has `∫ ζ f ≥ 0` for all such `ζ`, so `f ≥ 0` a.e. by
`codim1_rdo_dg_hr_ae_nonneg_of_test_nonneg`; and `z ∈ F`, `z + t v ∉ F` would give `f(z) = −1`. -/
theorem Submission.codim1_rdo_dg_hr_ae_translate_monotone : ∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n)), MeasurableSet F → (∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∫ z in F, fderiv ℝ ζ z v ≤ 0) → ∀ t : ℝ, 0 ≤ t → ∀ᵐ z ∂volume, z ∈ F → z + t • v ∈ F := by
  intro n F v hF hdiv t ht
  classical
  -- Steps 1–2: for every admissible `ζ`, `∫_F ζ ≤ ∫_F ζ(· − t v)`
  have hmono : ∀ ζ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      (∀ z, 0 ≤ ζ z) → ∫ z in F, ζ z ≤ ∫ z in F, ζ (z - t • v) := by
    intro ζ hζ hζc hζ0
    -- `g(s) = ∫_F Dζ(z − s v)(v) dz ≤ 0`: the hypothesis for the translate `ζ(· − s v)`
    have hg : ∀ s : ℝ, ∫ z in F, fderiv ℝ ζ (z - s • v) v ≤ 0 := fun s => by
      simpa only [fderiv_comp_sub] using hdiv (fun y => ζ (y - s • v))
        (hζ.comp (contDiff_id.sub contDiff_const))
        (hζc.comp_homeomorph (Homeomorph.subRight (s • v))) fun z => hζ0 _
    have hint : 0 ≤ ∫ s in (0 : ℝ)..t, -∫ z in F, fderiv ℝ ζ (z - s • v) v :=
      intervalIntegral.integral_nonneg_of_forall ht fun s => neg_nonneg.2 (hg s)
    rw [intervalIntegral.integral_neg] at hint
    rw [Submission.codim1_rdo_dg_hr_translate_integral_eq n F ζ v t hF hζ hζc]
    linarith
  -- Step 3: with `u = 1_F`, `f = u(· + t v) − u` has `∫ g f ≥ 0` for every admissible `g`
  set u : EuclideanSpace ℝ (Fin n) → ℝ := F.indicator fun _ => 1
  have hFt : MeasurableSet ((· + t • v) ⁻¹' F) := hF.preimage (measurable_add_const _)
  have htest : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      (∀ x, 0 ≤ g x) → 0 ≤ ∫ x, g x * (u (x + t • v) - u x) := by
    intro g hg hgc hg0
    have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
    -- `∫_F g(z − t v) dz = ∫ 1_F(y + t v) g(y) dy` by translation invariance
    have e1 : ∫ z in F, g (z - t • v) = ∫ y, ((· + t • v) ⁻¹' F).indicator g y := by
      rw [← integral_indicator hF, ← integral_add_right_eq_self _ (t • v)]
      congr 1; ext y; simp [indicator_apply]
    have e2 : ∫ z in F, g z = ∫ y, F.indicator g y := (integral_indicator hF).symm
    have e3 : (fun x => g x * (u (x + t • v) - u x)) =
        fun x => ((· + t • v) ⁻¹' F).indicator g x - F.indicator g x := by
      ext x; simp [u, indicator_apply, mul_sub]
    have := hmono g hg hgc hg0
    rw [e3, integral_sub (hgi.indicator hFt) (hgi.indicator hF)]
    linarith
  -- `f` is bounded and Borel, hence locally integrable
  have hli : LocallyIntegrable (fun x => u (x + t • v) - u x) volume := by
    have hu' : (fun x => u (x + t • v)) = ((· + t • v) ⁻¹' F).indicator fun _ => 1 := by
      ext x; simp [u, indicator_apply]
    refine LocallyIntegrable.sub ?_ ?_
    · rw [hu']; exact (locallyIntegrable_const 1).indicator hFt
    · exact (locallyIntegrable_const 1).indicator hF
  -- Steps 4–5: `f ≥ 0` a.e., while `z ∈ F`, `z + t v ∉ F` would give `f(z) = −1`
  filter_upwards [Submission.codim1_rdo_dg_hr_ae_nonneg_of_test_nonneg n _ hli htest]
    with z hz hzF
  by_contra hzt
  norm_num [u, hzF, hzt] at hz
/-- **Simon, Ch. 3, 4.3, the step to (9)** (a monotone set is null, co-null or a half-space): if a
Borel `F ⊆ ℝⁿ` has `z ∈ F ⇒ z + a ∈ F` for a.e. `z`, for each `a` with `⟨a, v⟩ ≥ 0`, then `F` is
null, co-null, or a.e. equal to `{⟨z, v⟩ > c}`.  Translating `B̄_r(z₁)` onto `B̄_r(z₀)` shows that a
point `z₁` of density `1` lies strictly further along `v` than a point `z₀` of density `0`.  With
`c = sup ⟨z₀, v⟩`, the Lebesgue density theorem puts `F Δ {⟨z, v⟩ > c}` inside a null set and the
null hyperplane `{⟨z, v⟩ = c}`. -/
theorem Submission.codim1_rdo_dg_hr_monotone_set_trichotomy : ∀ (n : ℕ) (F : Set (EuclideanSpace ℝ (Fin n))) (v : EuclideanSpace ℝ (Fin n)), MeasurableSet F → (∀ a : EuclideanSpace ℝ (Fin n), 0 ≤ inner ℝ a v → ∀ᵐ z ∂volume, z ∈ F → z + a ∈ F) → volume F = 0 ∨ volume Fᶜ = 0 ∨ ∃ c : ℝ, volume (symmDiff F {z | c < inner ℝ z v}) = 0 := by
  intro n F v hF hmono
  -- a point of density `1` lies strictly further along `v` than a point of density `0`
  have hord : ∀ z₁ z₀ : EuclideanSpace ℝ (Fin n),
      Tendsto (fun r => volume (F ∩ closedBall z₁ r) / volume (closedBall z₁ r)) (𝓝[>] 0) (𝓝 1) →
      Tendsto (fun r => volume (F ∩ closedBall z₀ r) / volume (closedBall z₀ r)) (𝓝[>] 0) (𝓝 0) →
      inner ℝ z₀ v < inner ℝ z₁ v := by
    intro z₁ z₀ h₁ h₀
    by_contra hlt
    rw [not_lt] at hlt
    -- `z ↦ z + (z₀ - z₁)` keeps `F` a.e. and maps `B̄_r(z₁)` onto `B̄_r(z₀)`
    have hnull : volume {z | ¬(z ∈ F → z + (z₀ - z₁) ∈ F)} = 0 :=
      ae_iff.mp (hmono (z₀ - z₁) (by rw [inner_sub_left]; linarith))
    have hball : ∀ r : ℝ, (fun z => z + (z₀ - z₁)) ⁻¹' closedBall z₀ r = closedBall z₁ r := by
      intro r
      ext z
      simp only [mem_preimage, mem_closedBall, dist_eq_norm]
      rw [show z + (z₀ - z₁) - z₀ = z - z₁ by abel]
    have hle : ∀ r : ℝ, volume (F ∩ closedBall z₁ r) / volume (closedBall z₁ r) ≤
        volume (F ∩ closedBall z₀ r) / volume (closedBall z₀ r) := by
      intro r
      have hsub : F ∩ closedBall z₁ r ⊆ (fun z => z + (z₀ - z₁)) ⁻¹' (F ∩ closedBall z₀ r) ∪
          {z | ¬(z ∈ F → z + (z₀ - z₁) ∈ F)} := by
        rintro z ⟨hzF, hzB⟩
        by_cases h : z + (z₀ - z₁) ∈ F
        · rw [← hball r] at hzB
          exact Or.inl (show z + (z₀ - z₁) ∈ F ∩ closedBall z₀ r from ⟨h, hzB⟩)
        · exact Or.inr fun himp => h (himp hzF)
      have hden : volume (closedBall z₁ r) = volume (closedBall z₀ r) := by
        rw [← hball r, measure_preimage_add_right]
      rw [hden]
      refine ENNReal.div_le_div_right ?_ _
      calc volume (F ∩ closedBall z₁ r)
          ≤ volume ((fun z => z + (z₀ - z₁)) ⁻¹' (F ∩ closedBall z₀ r) ∪
              {z | ¬(z ∈ F → z + (z₀ - z₁) ∈ F)}) := measure_mono hsub
        _ ≤ volume ((fun z => z + (z₀ - z₁)) ⁻¹' (F ∩ closedBall z₀ r)) +
              volume {z | ¬(z ∈ F → z + (z₀ - z₁) ∈ F)} := measure_union_le _ _
        _ = volume (F ∩ closedBall z₀ r) := by rw [hnull, add_zero, measure_preimage_add_right]
    exact absurd (le_of_tendsto_of_tendsto' h₁ h₀ hle) (by simp)
  -- Lebesgue density theorem: off a null set `N`, points of `F` have density `1` and points of
  -- `Fᶜ` have density `0`
  obtain ⟨N, hN0, hN⟩ : ∃ N : Set (EuclideanSpace ℝ (Fin n)), volume N = 0 ∧ ∀ x ∉ N,
      Tendsto (fun r => volume (F ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 (F.indicator 1 x)) :=
    ⟨_, ae_iff.mp (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hF),
      fun x hx => not_not.mp hx⟩
  have hA₁ : ∀ x ∈ F, x ∉ N →
      Tendsto (fun r => volume (F ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 1) := by
    intro x hx hxN
    simpa [indicator_of_mem hx] using hN x hxN
  have hA₀ : ∀ x ∉ F, x ∉ N →
      Tendsto (fun r => volume (F ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    intro x hx hxN
    simpa [indicator_of_notMem hx] using hN x hxN
  -- no point of density `1`: `F` is null
  by_cases h₁ : ∃ z₁, Tendsto (fun r => volume (F ∩ closedBall z₁ r) / volume (closedBall z₁ r))
      (𝓝[>] 0) (𝓝 1)
  swap
  · refine Or.inl (measure_mono_null (fun x hx => ?_) hN0)
    by_contra hxN
    exact h₁ ⟨x, hA₁ x hx hxN⟩
  -- no point of density `0`: `Fᶜ` is null
  by_cases h₀ : ∃ z₀, Tendsto (fun r => volume (F ∩ closedBall z₀ r) / volume (closedBall z₀ r))
      (𝓝[>] 0) (𝓝 0)
  swap
  · refine Or.inr (Or.inl (measure_mono_null (fun x hx => ?_) hN0))
    by_contra hxN
    exact h₀ ⟨x, hA₀ x hx hxN⟩
  obtain ⟨z₁, hz₁⟩ := h₁
  obtain ⟨z₀, hz₀⟩ := h₀
  -- `c = sup {⟨z₀, v⟩ : z₀ has density 0}` separates the two kinds of density points
  obtain ⟨c, hc₀, hc₁⟩ : ∃ c : ℝ,
      (∀ z, Tendsto (fun r => volume (F ∩ closedBall z r) / volume (closedBall z r)) (𝓝[>] 0)
        (𝓝 0) → inner ℝ z v ≤ c) ∧
      (∀ z, Tendsto (fun r => volume (F ∩ closedBall z r) / volume (closedBall z r)) (𝓝[>] 0)
        (𝓝 1) → c ≤ inner ℝ z v) := by
    refine ⟨sSup ((fun z => inner ℝ z v) '' {z | Tendsto (fun r => volume (F ∩ closedBall z r) /
      volume (closedBall z r)) (𝓝[>] 0) (𝓝 0)}), fun z hz => le_csSup ⟨inner ℝ z₁ v, ?_⟩
      ⟨z, hz, rfl⟩, fun z hz => csSup_le ⟨_, z₀, hz₀, rfl⟩ ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact (hord z₁ w hz₁ hw).le
    · rintro _ ⟨w, hw, rfl⟩
      exact (hord z w hz hw).le
  -- the hyperplane `{⟨z, v⟩ = c}` is null, since `v ≠ 0`
  have hv : v ≠ 0 := by
    rintro rfl
    simpa using hord z₁ z₀ hz₁ hz₀
  have hP : volume {z : EuclideanSpace ℝ (Fin n) | inner ℝ z v = c} = 0 := by
    have hvv : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hv
    refine measure_mono_null (t := (AffineSubspace.mk' ((c / inner ℝ v v) • v)
      (LinearMap.ker (innerₛₗ ℝ v)) : Set (EuclideanSpace ℝ (Fin n)))) (fun z hz => ?_)
      (Measure.addHaar_affineSubspace _ _ fun h => ?_)
    · replace hz : inner ℝ z v = c := hz
      rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker,
        innerₛₗ_apply_apply, inner_sub_right, real_inner_smul_right, div_mul_cancel₀ c hvv,
        real_inner_comm z v, hz, sub_self]
    · have hmem : (c / inner ℝ v v) • v + v ∈ AffineSubspace.mk' ((c / inner ℝ v v) • v)
          (LinearMap.ker (innerₛₗ ℝ v)) := by
        rw [h]
        exact AffineSubspace.mem_top _ _ _
      rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left, LinearMap.mem_ker,
        innerₛₗ_apply_apply] at hmem
      exact hvv hmem
  -- `F Δ {⟨z, v⟩ > c} ⊆ N ∪ {⟨z, v⟩ = c}`
  refine Or.inr (Or.inr ⟨c, measure_mono_null (fun z hz => ?_) (measure_union_null hN0 hP)⟩)
  rcases mem_symmDiff.mp hz with ⟨hzF, hzH⟩ | ⟨hzH, hzF⟩
  · by_cases hzN : z ∈ N
    · exact Or.inl hzN
    · exact Or.inr (le_antisymm (not_lt.mp (show ¬c < inner ℝ z v from hzH))
        (hc₁ z (hA₁ z hzF hzN)))
  · by_cases hzN : z ∈ N
    · exact Or.inl hzN
    · exact absurd (show c < inner ℝ z v from hzH) (not_lt.mpr (hc₀ z (hA₀ z hzF hzN)))

/-- **Half-space rigidity** (Simon Ch. 3, 4.3 (8)–(9); for the inward normal the limit set is
`{⟨z, v⟩ > c}`): if `D_w 1_{F₀} = 0` for every `w ⊥ v` and `D_v 1_{F₀} ≥ 0` in the sense of
distributions, then `F₀` is null, co-null, or a.e. a half-space `{⟨z, v⟩ > c}`.  Translation by
`w ⊥ v` preserves `F₀` a.e. and translation by `t • v`, `t ≥ 0`, maps `F₀` into itself a.e.; writing
`a = (a - ⟨a, v⟩ • v) + ⟨a, v⟩ • v`, translation by any `a` with `⟨a, v⟩ ≥ 0` maps `F₀` into itself
a.e., and the Lebesgue density trichotomy for such monotone sets concludes. -/
theorem Submission.codim1_rdo_dg_halfspace_rigidity : ∀ (m : ℕ) (F₀ : Set (Euclid (m + 1))) (v : Euclid (m + 1)), ‖v‖ = 1 → MeasurableSet F₀ → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in F₀, fderiv ℝ ζ z w = 0) → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∫ z in F₀, fderiv ℝ ζ z v ≤ 0) → volume F₀ = 0 ∨ volume F₀ᶜ = 0 ∨ ∃ c : ℝ, volume (symmDiff F₀ {z | c < inner ℝ z v}) = 0 := by
  intro m F₀ v hv hF htan hnor
  refine Submission.codim1_rdo_dg_hr_monotone_set_trichotomy (m + 1) F₀ v hF fun a ha => ?_
  -- `a = w + t • v` with `t = ⟨a, v⟩ ≥ 0` and `w = a - t • v ⊥ v`, as `‖v‖ = 1`
  generalize ht : inner ℝ a v = t at ha
  have hw : inner ℝ (a - t • v) v = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv, ht]
    ring
  -- a.e. `z + w ∈ F₀ ↔ z ∈ F₀`, and a.e. `z + w ∈ F₀ → z + w + t • v ∈ F₀` (translate by `w`)
  have hinv := Submission.codim1_rdo_dg_hr_ae_translate_invariant (m + 1) F₀ (a - t • v) hF
    fun ζ hζ hζc => htan ζ hζ hζc (a - t • v) hw
  have hmono := (measurePreserving_add_right volume (a - t • v)).quasiMeasurePreserving.ae
    (Submission.codim1_rdo_dg_hr_ae_translate_monotone (m + 1) F₀ v hF hnor t ha)
  filter_upwards [hinv, hmono] with z hzw hzwv hz
  simpa only [add_assoc, sub_add_cancel] using hzwv (hzw.2 hz)

/-- **Blow-up of `F` at `y` is the half-space `{⟨w, v⟩ > 0}`** (Simon Ch. 3, proof of Theorem 4.3
(De Giorgi), printed (7)–(11) and the paragraph "Now given any sequence `λ_k ↓ 0` …",
chapter-03.txt lines 652–744; for the inward normal the limit is `{⟨w, v⟩ > 0}`, the OCR's
inequality being reversed).  Given `r_k ↓ 0`, the rescaled sets `F_{y,r_k}` have locally bounded
perimeter (`μ(B̄_ρ(y)) ≤ C₁ ρ^m`), so a subsequence converges in `L¹_loc` to some `F₀`; since the
normal averages tend to `v`, `F₀` has vanishing tangential and nonpositive normal distributional
derivative, hence is (a.e.) `∅`, `ℝ^{m+1}` or `{⟨w, v⟩ > c}`; the scale-invariant two-sided volume
bounds force `c = 0`.  The limit being independent of the sequence, the whole family converges. -/
theorem Submission.codim1_rdo_dg_blowup_halfspace : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), 1 ≤ m → IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → y ∈ D → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ R : ℝ, Tendsto (fun r : ℝ => volume (symmDiff ((fun w => y + r • w) ⁻¹' F) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R)) (𝓝[>] 0) (𝓝 0) := by
  intro m D F μ ν y v hm hD hF hμD hμK hν hν1 hGG hy hv hA R
  -- step 1: `μ(B̄_ρ(y)) ≤ C₁ ρ^m` for `ρ < ρ₁`, and `L(F ∩ B_ρ(y)), L(B_ρ(y) \ F) ≥ c₂ ρ^{m+1}`
  -- for `ρ < ρ₂`
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hball, -, hupper⟩ :=
    Submission.codim1_rdo_dg_cutoff_estimates m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hA
  obtain ⟨c₂, ρ₂, hc₂, hρ₂, hlower⟩ :=
    Submission.codim1_rdo_dg_volume_density_lower m D F μ ν y v hm hD hF hμD hμK hν hν1 hGG hy
      hv hA
  -- `L((y + r ·)⁻¹ S) = r^{-(m+1)} L(S)` and `(y + r ·)⁻¹ B_{rs}(y) = B_s`
  have hscale : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid (m + 1)),
      volume ((fun w => y + r • w) ⁻¹' S) = ENNReal.ofReal ((r ^ (m + 1))⁻¹) * volume S := by
    intro r hr S
    have hcomp : (fun w : Euclid (m + 1) => y + r • w) ⁻¹' S =
        (fun w => r • w) ⁻¹' ((fun u => y + u) ⁻¹' S) := rfl
    rw [hcomp, Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add,
      finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hr _))]
  have hballpre : ∀ r : ℝ, 0 < r → ∀ s : ℝ,
      (fun w => y + r • w) ⁻¹' ball y (r * s) = ball (0 : Euclid (m + 1)) s := by
    intro r hr s
    ext w
    rw [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, mem_ball_zero_iff, mul_lt_mul_iff_of_pos_left hr]
  -- step 6, scale invariance: `L(F_r ∩ B_s), L(B_s \ F_r) ≥ c₂ s^{m+1}` for `0 < r < ρ₂ / s`
  have hdens : ∀ s : ℝ, 0 < s → ∀ r ∈ Ioo 0 (ρ₂ / s),
      ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤
          volume ((fun w => y + r • w) ⁻¹' F ∩ ball (0 : Euclid (m + 1)) s) ∧
        ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤
          volume (ball (0 : Euclid (m + 1)) s \ (fun w => y + r • w) ⁻¹' F) := by
    intro s hs r hr
    obtain ⟨h1, h2⟩ := hlower (r * s) (mul_pos hr.1 hs) ((lt_div_iff₀ hs).mp hr.2)
    have hc : ENNReal.ofReal (c₂ * s ^ (m + 1)) =
        ENNReal.ofReal ((r ^ (m + 1))⁻¹) * ENNReal.ofReal (c₂ * (r * s) ^ (m + 1)) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hr.1.le _))]
      congr 1
      have hr' : r ^ (m + 1) ≠ 0 := pow_ne_zero _ hr.1.ne'
      calc c₂ * s ^ (m + 1) = (r ^ (m + 1))⁻¹ * r ^ (m + 1) * (c₂ * s ^ (m + 1)) := by
            rw [inv_mul_cancel₀ hr', one_mul]
        _ = (r ^ (m + 1))⁻¹ * (c₂ * (r * s) ^ (m + 1)) := by ring
    rw [← hballpre r hr.1 s, ← preimage_inter, ← preimage_sdiff, hscale r hr.1, hscale r hr.1, hc]
    exact ⟨by gcongr, by gcongr⟩
  -- step 7: it suffices that every sequence `r_k → 0⁺` has a subsequence along which the
  -- quantity tends to `0`
  refine tendsto_of_subseq_tendsto fun rs hrs => ?_
  set Fs : ℕ → Set (Euclid (m + 1)) := fun k => (fun w => y + rs k • w) ⁻¹' F
  have hFs : ∀ k, MeasurableSet (Fs k) := fun k =>
    hF.preimage (continuous_const.add (continuous_const_smul (rs k))).measurable
  -- step 4: perimeter bounds `C₁ R^m` on `B_R`, hence an `L¹_loc` limit `F₀` of a subsequence
  have hBV : ∀ R' : ℝ, 0 < R' → ∃ C : ℝ, ∀ᶠ k in atTop, ∀ g : Euclid (m + 1) → Euclid (m + 1),
      ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R' →
      (∀ z, ‖g z‖ ≤ 1) → ∫ z in Fs k, LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C := by
    intro R' hR'
    refine ⟨C₁ * R' ^ m, ?_⟩
    filter_upwards [hrs.eventually_mem (Ioo_mem_nhdsGT (div_pos hρ₁ hR'))]
      with k hk g hg hgc hgs hg1
    exact Submission.codim1_rdo_dg_bh_perimeter_bound m D F μ ν y ρ₁ C₁ hF hν hν1 hGG hρ₁ hC₁
      hball hupper R' (rs k) hR' hk.1 ((lt_div_iff₀ hR').mp hk.2) g hg hgc hgs hg1
  obtain ⟨ψ, F₀, hψ, hF₀, hconv⟩ := Submission.codim1_rdo_dg_bv_set_compactness m Fs hFs hBV
  refine ⟨ψ, ?_⟩
  have hrsψ : Tendsto (fun j => rs (ψ j)) atTop (𝓝[>] 0) := hrs.comp hψ.tendsto_atTop
  obtain ⟨hint, hin, hout⟩ := Submission.codim1_rdo_dg_bh_l1loc_transfer m (fun j => Fs (ψ j))
    F₀ (fun j => hFs (ψ j)) hF₀ hconv
  -- step 5: `F₀` has vanishing tangential and nonpositive normal derivative
  have htan : ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in F₀, fderiv ℝ ζ z w = 0 := by
    intro ζ hζ hζc w hw
    exact tendsto_nhds_unique
      (hint (fun z => fderiv ℝ ζ z w)
        ((hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
        (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hζc w))
      ((Submission.codim1_rdo_dg_bh_tangential_vanish m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA
        hρ₁ hC₁ hball hupper ζ hζ hζc w hw).comp hrsψ)
  have hnor : ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      (∀ z, 0 ≤ ζ z) → ∫ z in F₀, fderiv ℝ ζ z v ≤ 0 := by
    intro ζ hζ hζc hζ0
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    rw [zero_add]
    exact le_of_tendsto
      (hint (fun z => fderiv ℝ ζ z v)
        ((hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
        (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hζc v))
      (hrsψ.eventually (Submission.codim1_rdo_dg_bh_normal_limsup m D F μ ν y v ρ₁ C₁ hF hν hν1
        hGG hv hA hρ₁ hC₁ hball hupper ζ hζ hζc hζ0 δ hδ))
  -- so `F₀` is a.e. `∅`, `ℝ^{m+1}` or `{⟨w, v⟩ > c}`
  have htri := Submission.codim1_rdo_dg_halfspace_rigidity m F₀ v hv hF₀ htan hnor
  -- step 6: the two-sided bounds pass to the limit, which forces `c = 0`
  have hpos : ∀ s : ℝ, 0 < s → 0 < volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ∧
      0 < volume (ball (0 : Euclid (m + 1)) s \ F₀) := by
    intro s hs
    have hcs : 0 < ENNReal.ofReal (c₂ * s ^ (m + 1)) := ENNReal.ofReal_pos.mpr (by positivity)
    have hev : ∀ᶠ j in atTop, rs (ψ j) ∈ Ioo 0 (ρ₂ / s) :=
      hrsψ.eventually_mem (Ioo_mem_nhdsGT (div_pos hρ₂ hs))
    exact ⟨hcs.trans_le (ge_of_tendsto (hin s) (hev.mono fun j hj => (hdens s hs _ hj).1)),
      hcs.trans_le (ge_of_tendsto (hout s) (hev.mono fun j hj => (hdens s hs _ hj).2))⟩
  have hFH := Submission.codim1_rdo_dg_bh_offset_zero m F₀ v hv hpos htri
  -- step 7: `L((F_{r_{ψ j}} Δ H) ∩ B_R) ≤ L((F_{r_{ψ j}} Δ F₀) ∩ B_R) + L(F₀ Δ H) → 0`
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv R)
    (fun j => zero_le) (fun j => ?_)
  calc volume (symmDiff (Fs (ψ j)) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R)
      ≤ volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R ∪
          symmDiff F₀ {w | 0 < inner ℝ w v}) := by
        refine measure_mono fun x hx => ?_
        rcases symmDiff_triangle _ F₀ _ hx.1 with h | h
        · exact Or.inl ⟨h, hx.2⟩
        · exact Or.inr h
    _ ≤ volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R) +
          volume (symmDiff F₀ {w | 0 < inner ℝ w v}) := measure_union_le _ _
    _ = volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R) := by
        rw [hFH, add_zero]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Mollification by an even `C¹` kernel `η` with compact support commutes with `D` and is
self-adjoint: `∫ D(η * u)(x)(s x) dx = −∫ u div(η * s)` for integrable `u`, `s` (Simon Ch. 2,
Lemma 2.5).  Both derivatives are convolutions with the odd, bounded `Dη`, and Fubini applies to
`Dη(x − z)(s x) u(z)`, which is dominated by `C ‖s x‖ |u z|`. -/
theorem codim1_rdo_dg_sp_mollifier_adjoint : ∀ (P : ℕ) (η u : Euclid P → ℝ) (s : Euclid P → Euclid P), ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, η (-z) = η z) → Integrable u → Integrable s → ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z : Euclid P →ₗ[ℝ] Euclid P) := by
  intro P η u s hη hηc heven hu hs
  -- Step 0: `Dη` is continuous with compact support, hence bounded by some `C`.
  have hDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDcs : HasCompactSupport (fderiv ℝ η) := hηc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 1: `η` is even, so `Dη` is odd (chain rule for `η = η ∘ (−id)`).
  have hodd : ∀ y, fderiv ℝ η (-y) = -fderiv ℝ η y := by
    intro y
    have h1 : HasFDerivAt (η ∘ fun z => -z)
        ((fderiv ℝ η (-y)).comp (-ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hη.differentiable one_ne_zero) (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
    rw [show (η ∘ fun z => -z) = η from funext heven] at h1
    ext v
    rw [h1.fderiv]
    simp
  -- Step 2: `D(η * u)(x) = (Dη * u)(x)`, so `D(η * u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz`.
  have hLHS : ∀ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) =
      ∫ z, fderiv ℝ η (x - z) (s x) * u z := by
    intro x
    rw [(hηc.hasFDerivAt_convolution_left _ hη hu.locallyIntegrable x).fderiv, convolution_eq_swap,
      ContinuousLinearMap.integral_apply
        ((hDcs.convolutionExists_left _ hDc hu.locallyIntegrable x).integrable_swap)]
    simp
  -- Step 3: `div(η * s)(z) = trace D(η * s)(z) = ∫ Dη(z − x)(s x) dx`: the trace `T` is a
  -- continuous linear functional, and the trace of the rank-one map `v ↦ a(v) w` is `a(w)`.
  have hRHS : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
        Euclid P →ₗ[ℝ] Euclid P) = ∫ x, fderiv ℝ η (z - x) (s x) := by
    let T : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid P) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have hTA : ∀ A : Euclid P →L[ℝ] Euclid P,
        T A = LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) := fun A => rfl
    have hrk : ∀ (a : Euclid P →L[ℝ] ℝ) (w : Euclid P), T (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w) = a w := by
      intro a w
      have h : ((ContinuousLinearMap.precompL (Euclid P)
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w :
            Euclid P →L[ℝ] Euclid P) : Euclid P →ₗ[ℝ] Euclid P) =
          (a : Euclid P →ₗ[ℝ] ℝ).smulRight w := by
        ext v
        simp
      rw [hTA, h, LinearMap.trace_smulRight]
      rfl
    intro z
    rw [(hηc.hasFDerivAt_convolution_left _ hη hs.locallyIntegrable z).fderiv, convolution_eq_swap]
    have hT := ContinuousLinearMap.integral_comp_comm T
      ((hDcs.convolutionExists_left (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P)) hDc
          hs.locallyIntegrable z).integrable_swap)
    simp_rw [hrk] at hT
    exact hT.symm
  -- Step 4: Fubini for `H(x, z) = Dη(x − z)(s x) u(z)`, dominated by `C ‖s x‖ |u z|`.
  have hint : Integrable (uncurry fun x z => fderiv ℝ η (x - z) (s x) * u z)
      ((volume : Measure (Euclid P)).prod volume) := by
    refine Integrable.mono' ((hs.norm.mul_prod hu.norm).const_mul C) ?_ (Eventually.of_forall ?_)
    · exact ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
        hs.aestronglyMeasurable.comp_fst
        (hDc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hu.aestronglyMeasurable.comp_snd
    · rintro ⟨x, z⟩
      simp only [uncurry_apply_pair, norm_mul]
      calc ‖fderiv ℝ η (x - z) (s x)‖ * ‖u z‖ ≤ (C * ‖s x‖) * ‖u z‖ := by
            gcongr
            exact ((fderiv ℝ η (x - z)).le_opNorm (s x)).trans (by gcongr; exact hC _)
        _ = C * (‖s x‖ * ‖u z‖) := by ring
  -- Step 5: combine, using `Dη(z − x) = −Dη(x − z)` to identify the swapped integral.
  calc ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x)
      = ∫ x, ∫ z, fderiv ℝ η (x - z) (s x) * u z := by simp_rw [hLHS]
    _ = ∫ z, ∫ x, fderiv ℝ η (x - z) (s x) * u z := integral_integral_swap hint
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P)
          (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
            Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_neg]
      congr 1
      funext z
      rw [hRHS z, ← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      rw [← neg_sub x z, hodd, neg_apply]
      ring
/-- Mollification does not increase the variation (Simon Ch. 2, Lemma 2.5, formula (4)): if
`|∫ u div g| ≤ M` for every `g ∈ C¹_c(ℝᴾ; ℝᴾ)` with `|g| ≤ 1`, then `∫ |D(η * u)| ≤ M` for an even
mollifier `η ≥ 0` with `∫ η = 1`.  With `w = η * u`, the field `s = 1_{spt w} |∇w|⁻¹ ∇w`
(`0⁻¹ = 0`) is Borel, bounded by `1`, compactly supported and has `Dw(s) = |Dw|`;
`codim1_rdo_dg_sp_mollifier_adjoint` moves `η` onto `s`, and `g = η * s` is admissible. -/
theorem codim1_rdo_dg_sp_mollify_variation : ∀ (P : ℕ) (u : Euclid P → ℝ) (M : ℝ), Integrable u → HasCompactSupport u → (∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ M) → ∀ η : Euclid P → ℝ, ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, 0 ≤ η z) → (∀ z, η (-z) = η z) → ∫ z, η z = 1 → ∫ z, ‖fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) z‖ ≤ M := by
  intro P u M hu huc hM η hη hηc hη0 heven hη1
  -- Step 1: `w = η * u` is `C¹` with compact support `S = spt w`.
  set w := convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwc : HasCompactSupport w := hηc.convolution _ huc
  have hDw : Continuous (fderiv ℝ w) :=
    (hηc.contDiff_convolution_left _ hη hu.locallyIntegrable).continuous_fderiv one_ne_zero
  set S := tsupport w
  have hSm : MeasurableSet S := (isClosed_tsupport w).measurableSet
  -- Step 2: the gradient `∇w = (toDual)⁻¹ Dw` is continuous, `|∇w| = |Dw|`, `Dw(∇w) = |∇w|²`.
  set grad : Euclid P → Euclid P :=
    fun x => (InnerProductSpace.toDual ℝ (Euclid P)).symm (fderiv ℝ w x)
  have hgc : Continuous grad := (InnerProductSpace.toDual ℝ (Euclid P)).symm.continuous.comp hDw
  have hgn : ∀ x, ‖grad x‖ = ‖fderiv ℝ w x‖ := fun x => LinearIsometryEquiv.norm_map _ _
  have hgg : ∀ x, fderiv ℝ w x (grad x) = ‖grad x‖ ^ 2 := by
    intro x
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := grad x) (y := fderiv ℝ w x)]
    exact real_inner_self_eq_norm_sq _
  -- Step 3: the unit field `f = |∇w|⁻¹ ∇w` (`0⁻¹ = 0`) and `s = 1_S f`.
  set f : Euclid P → Euclid P := fun x => ‖grad x‖⁻¹ • grad x with hf
  have hfm : Measurable f := hgc.norm.measurable.inv.smul hgc.measurable
  have hf1 : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    simp only [hf, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖grad x‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  set s : Euclid P → Euclid P := S.indicator f with hs
  have hs1 : ∀ x, ‖s x‖ ≤ 1 := fun x => (norm_indicator_le_norm_self f x).trans (hf1 x)
  have hsc : HasCompactSupport s :=
    HasCompactSupport.intro hwc.isCompact fun x hx => indicator_of_notMem hx f
  have hsi : Integrable s := by
    rw [hs, integrable_indicator_iff hSm]
    exact Measure.integrableOn_of_bounded hwc.isCompact.measure_lt_top.ne
      hfm.aestronglyMeasurable (Eventually.of_forall hf1)
  -- Step 4: `Dw(x)(s x) = |Dw(x)|` for all `x`.
  have hDs : ∀ x, fderiv ℝ w x (s x) = ‖fderiv ℝ w x‖ := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hs, indicator_of_mem hx, hf, map_smul, hgg, smul_eq_mul, ← hgn]
      rcases eq_or_ne ‖grad x‖ 0 with h | h
      · simp [h]
      · field_simp
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  -- Step 5: `g = η * s` is admissible: `C¹`, compact support, `|g| ≤ ∫ η = 1`.
  set g := convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume with hg
  have hgC1 : ContDiff ℝ 1 g := hηc.contDiff_convolution_left _ hη hsi.locallyIntegrable
  have hgcs : HasCompactSupport g := hηc.convolution _ hsc
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  have hg1 : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    rw [hg, convolution_def]
    refine (norm_integral_le_of_norm_le hηi (Eventually.of_forall fun t => ?_)).trans hη1.le
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hη0 t)]
    exact mul_le_of_le_one_right (hη0 t) (hs1 _)
  -- Steps 6–7: the adjoint identity, then the hypothesis for `g`.
  calc ∫ z, ‖fderiv ℝ w z‖ = ∫ z, fderiv ℝ w z (s z) :=
        integral_congr_ae (Eventually.of_forall fun z => (hDs z).symm)
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) :=
        Submission.codim1_rdo_dg_sp_mollifier_adjoint P η u s hη hηc heven hu hsi
    _ ≤ |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| :=
        neg_le_abs _
    _ ≤ M := hM g hgC1 hgcs hg1

/-- **Sobolev inequality in the limit of symmetric mollifications** (Simon Ch. 3, proof of
Theorem 4.3 (De Giorgi), Sobolev step, chapter-03.txt lines 689–712, with the mollification
Lemma Ch. 2, 2.5, chapter-02.txt lines 543–596).  Assume the Sobolev inequality
`(∫ |w|^p)^{1/p} ≤ c ∫ |Dw|` for `C¹` compactly supported `w`, let `u` be integrable with compact
support and `|∫ u div g| ≤ M` for `C¹_c` fields `|g| ≤ 1`, and let `η_k` be even, nonnegative,
`C¹`, compactly supported with `∫ η_k = 1` and `η_k * u → u` a.e.  Then `(∫ |u|^p)^{1/p} ≤ c M`:
`g = 0` gives `M ≥ 0`; each `w_k = η_k * u` is `C¹` with compact support and
`∫ |Dw_k| ≤ M` (`codim1_rdo_dg_sp_mollify_variation`), so `∫⁻ ‖w_k‖ₑ^p ≤ (cM)^p` by the Sobolev
inequality; Fatou's lemma along `w_k → u` a.e. gives `∫⁻ ‖u‖ₑ^p ≤ (cM)^p`, and taking `toReal`
and the `1/p` power concludes. -/
theorem codim1_rdo_dg_sp_sobolev_limit : ∀ (P : ℕ) (p c : ℝ), 0 < p → 0 ≤ c → (∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, |w z| ^ p) ^ p⁻¹ ≤ c * ∫ z, ‖fderiv ℝ w z‖) → ∀ (u : Euclid P → ℝ) (M : ℝ), Integrable u → HasCompactSupport u → (∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ M) → ∀ η : ℕ → Euclid P → ℝ, (∀ k, ContDiff ℝ 1 (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ᵐ x, Tendsto (fun k => convolution (η k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop (𝓝 (u x))) → (∫ z, |u z| ^ p) ^ p⁻¹ ≤ c * M := by
  intro P p c hp hc hS u M hu hcu hM η hη hηc hη0 hηs hη1 hae
  -- Step 1: testing the variation bound with `g = 0` gives `M ≥ 0`, hence `c M ≥ 0`
  have hM0 : 0 ≤ M := by
    simpa using hM (fun _ => 0) contDiff_const HasCompactSupport.zero fun _ => by simp
  have hcM : 0 ≤ c * M := mul_nonneg hc hM0
  -- Step 2: the mollifications `w_k = η_k * u` are `C¹` with compact support
  set w : ℕ → Euclid P → ℝ :=
    fun k => convolution (η k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwC : ∀ k, ContDiff ℝ 1 (w k) := fun k =>
    (hηc k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hη k) hu.locallyIntegrable
  have hwcs : ∀ k, HasCompactSupport (w k) := fun k =>
    (hηc k).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcu
  -- `ofReal (|t|^p) = ‖t‖ₑ^p`
  have henorm : ∀ t : ℝ, ENNReal.ofReal (|t| ^ p) = ‖t‖ₑ ^ p := fun t => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg t) hp.le]
  -- Step 3: `∫ |Dw_k| ≤ M` and the Sobolev inequality give `∫ |w_k|^p ≤ (c M)^p`
  have hbound : ∀ k, ∫ z, |w k z| ^ p ≤ (c * M) ^ p := by
    intro k
    have hvar : ∫ z, ‖fderiv ℝ (w k) z‖ ≤ M :=
      Submission.codim1_rdo_dg_sp_mollify_variation P u M hu hcu hM (η k) (hη k) (hηc k)
        (hη0 k) (hηs k) (hη1 k)
    have h1 : (∫ z, |w k z| ^ p) ^ p⁻¹ ≤ c * M :=
      (hS (w k) (hwC k) (hwcs k)).trans (mul_le_mul_of_nonneg_left hvar hc)
    have ha : 0 ≤ ∫ z, |w k z| ^ p :=
      integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) p
    calc ∫ z, |w k z| ^ p = ((∫ z, |w k z| ^ p) ^ p⁻¹) ^ p :=
          (Real.rpow_inv_rpow ha hp.ne').symm
      _ ≤ (c * M) ^ p := Real.rpow_le_rpow (Real.rpow_nonneg ha _) h1 hp.le
  -- Step 4: `|w_k|^p` is continuous with compact support, so `∫⁻ ‖w_k‖ₑ^p ≤ ofReal ((c M)^p)`
  have hlow : ∀ k, ∫⁻ x, ‖w k x‖ₑ ^ p ≤ ENNReal.ofReal ((c * M) ^ p) := by
    intro k
    have hint : Integrable fun z => |w k z| ^ p :=
      ((hwC k).continuous.abs.rpow_const fun _ => Or.inr hp.le).integrable_of_hasCompactSupport
        ((hwcs k).abs.rpow_const hp.ne')
    calc ∫⁻ x, ‖w k x‖ₑ ^ p = ∫⁻ x, ENNReal.ofReal (|w k x| ^ p) :=
          lintegral_congr fun x => (henorm (w k x)).symm
      _ = ENNReal.ofReal (∫ z, |w k z| ^ p) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg _) p)).symm
      _ ≤ ENNReal.ofReal ((c * M) ^ p) := ENNReal.ofReal_le_ofReal (hbound k)
  -- Step 5: Fatou's lemma along `w_k → u` a.e.
  have hfatou : ∫⁻ x, ‖u x‖ₑ ^ p ≤ ENNReal.ofReal ((c * M) ^ p) :=
    calc ∫⁻ x, ‖u x‖ₑ ^ p = ∫⁻ x, liminf (fun k => ‖w k x‖ₑ ^ p) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          exact ((hx.enorm.ennrpow_const p).liminf_eq).symm
      _ ≤ liminf (fun k => ∫⁻ x, ‖w k x‖ₑ ^ p) atTop :=
          lintegral_liminf_le fun k => (hwC k).continuous.measurable.enorm.pow_const p
      _ ≤ ENNReal.ofReal ((c * M) ^ p) := liminf_le_of_frequently_le' (Frequently.of_forall hlow)
  -- Step 6: `∫ |u|^p = (∫⁻ ‖u‖ₑ^p).toReal ≤ (c M)^p`; take the `1/p` power
  have hup : 0 ≤ ∫ z, |u z| ^ p := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) p
  have hU : ∫ z, |u z| ^ p ≤ (c * M) ^ p := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg (u z)) p)
      ((continuous_abs.rpow_const fun _ => Or.inr hp.le).comp_aestronglyMeasurable
        hu.aestronglyMeasurable)]
    refine ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hcM p) ?_
    calc ∫⁻ x, ENNReal.ofReal (|u x| ^ p) = ∫⁻ x, ‖u x‖ₑ ^ p :=
          lintegral_congr fun x => henorm (u x)
      _ ≤ ENNReal.ofReal ((c * M) ^ p) := hfatou
  calc (∫ z, |u z| ^ p) ^ p⁻¹ ≤ ((c * M) ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow hup hU (inv_nonneg.2 hp.le)
    _ = c * M := Real.rpow_rpow_inv hcM hp.ne'

/-- **The Sobolev inequality for `ζ 1_F`** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi),
chapter-03.txt lines 689–712: `(∫ (ζ 1_F)^{(n+1)/n})^{n/(n+1)} ≤ c ∫ |D(ζ 1_F)| ≤
c (∫ ζ dμ + ∫_F |Dζ|)`, with the mollification Lemma Ch. 2, 2.5).  For `m ≥ 1` the exponent
`p = (m+1)/m` is the Hölder conjugate of `dim ℝ^{m+1} = m+1`, so Mathlib's Gagliardo–Nirenberg–
Sobolev inequality gives the constant `c`.  Given the Gauss–Green identity, `u = 1_F ζ` has
variation at most `M = ∫ ζ dμ + ∫_F |Dζ|`; the normalized bump functions of radius `1/(k+1)` are
even, nonnegative, unit-mass `C¹` kernels whose mollifications converge to `u` a.e. (Lebesgue
differentiation), and the Sobolev bound passes from the mollifications to `u`. -/
theorem codim1_rdo_dg_sobolev_perimeter : ∀ (m : ℕ), 1 ≤ m → ∃ c : ℝ, 0 < c ∧ ∀ (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in F, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in F, ‖fderiv ℝ ζ z‖) := by
  intro m hm
  -- Step 0: `p = (m+1)/m` is the Hölder conjugate of `m + 1`; GNS gives the constant `c`
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m + 1 : ℝ) / m := by positivity
  have hHC : Real.HolderConjugate (Module.finrank ℝ (Euclid (m + 1)) : ℝ) ((m + 1 : ℝ) / m) := by
    rw [finrank_euclideanSpace_fin]
    refine ⟨?_, by positivity, hp⟩
    push_cast
    field_simp
    ring
  obtain ⟨c, hc, hS⟩ := Submission.codim1_rdo_dg_sp_gns_real_of_lintegral (m + 1)
    ((m + 1 : ℝ) / m) (lintegralPowLePowLIntegralFDerivConst volume ((m + 1 : ℝ) / m)) hp
    fun w hw hwc => lintegral_pow_le_pow_lintegral_fderiv volume hw hwc hHC
  refine ⟨c, hc, ?_⟩
  intro D F μ ν hD hF hμD hμK hν hν1 hGG ζ hζ hζc hζD hζ0
  -- Step 1: `u = 1_F ζ` is integrable with compact support; its variation bound `M` is
  -- `gauss_green_variation` (used below)
  have hu : Integrable (F.indicator ζ) :=
    (hζ.continuous.integrable_of_hasCompactSupport hζc).indicator hF
  have huc : HasCompactSupport (F.indicator ζ) :=
    hζc.mono fun z hz h0 => hz (by simp [h0])
  -- Step 2: even, nonnegative, unit-mass `C¹` kernels of radius `1/(k+1)`
  let φ : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    { rIn := 1 / ((k : ℝ) + 1) / 2
      rOut := 1 / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith }
  have hφ0 : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφK : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn :=
    Eventually.of_forall fun k => by
      change 1 / ((k : ℝ) + 1) ≤ 2 * (1 / ((k : ℝ) + 1) / 2)
      linarith
  -- Lebesgue differentiation: the mollifications converge to `u` almost everywhere
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hφ0 hφK hu.locallyIntegrable
  -- Steps 3–4: GNS for the mollifications and passage to the limit
  have key := Submission.codim1_rdo_dg_sp_sobolev_limit (m + 1) ((m + 1 : ℝ) / m) c hp hc.le hS
    (F.indicator ζ) (∫ z, ζ z ∂μ + ∫ z in F, ‖fderiv ℝ ζ z‖) hu huc
    (fun g hg hgc hg1 => Submission.codim1_rdo_dg_sp_gauss_green_variation (m + 1) D F μ ν hD hF
      hμD hμK hν hν1 hGG ζ hζ hζc hζD hζ0 g hg hgc hg1)
    (fun k => (φ k).normed volume) (fun k => (φ k).contDiff_normed)
    (fun k => (φ k).hasCompactSupport_normed) (fun k => (φ k).nonneg_normed)
    (fun k => (φ k).normed_neg) (fun k => (φ k).integral_normed) hae
  -- Conclusion: `∫ |1_F ζ|^p = ∫_F ζ^p` and `p⁻¹ = m/(m+1)`
  have hint : ∫ z, |F.indicator ζ z| ^ ((m + 1 : ℝ) / m) = ∫ z in F, ζ z ^ ((m + 1 : ℝ) / m) := by
    rw [← integral_indicator hF]
    congr 1
    ext z
    by_cases hz : z ∈ F
    · simp [hz, abs_of_nonneg (hζ0 z)]
    · simp [hz, Real.zero_rpow hp.ne']
  rwa [hint, inv_div] at key

/-- **Lower volume density** of `F` and of its complement (Simon Ch. 3, proof of Theorem 4.3,
(10)–(11)) at a point `y` where the normal averages of the Gauss–Green measure `μ` tend to a unit
vector `v`.  `codim1_rdo_dg_cutoff_estimates` gives `ρ₁ > 0` and `C₁ ≥ 0` with `B̄_{ρ₁}(y) ⊆ D` and
the annular bounds `δ μ(B̄_ρ(y)) ≤ C₁ L(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` and
`δ μ(B̄_ρ(y)) ≤ C₁ L((B_{ρ+δ}(y) \ B̄_ρ(y)) \ F)` for `ρ + δ < ρ₁`, and
`codim1_rdo_dg_sobolev_perimeter` gives `c_S > 0` with
`(∫_F ζ^{(m+1)/m})^{m/(m+1)} ≤ c_S (∫ ζ dμ + ∫_F |Dζ|)`.  Since `v ≠ 0`, every closed ball about
`y` has positive `μ`-measure, and `μ(B̄_{ρ₁}(y)) < ∞` by local finiteness.  The finite-difference
isoperimetric inequality and its discrete integration (`codim1_rdo_dg_vdl_one_sided_density`)
give `L(F ∩ B_ρ(y)) ≥ c₁ ρ^{m+1}` for `ρ < ρ₁` (printed (10)).  Since `∫ div φ = 0`, `Fᶜ`
satisfies the Gauss–Green identity with normal `−ν`, so the Sobolev inequality and the annular
bound hold for `Fᶜ` as well, and the same argument gives `L(B_ρ(y) \ F) ≥ c₂ ρ^{m+1}`
(printed (11)).  Take `c = min c₁ c₂` and `ρ₂ = ρ₁`. -/
theorem codim1_rdo_dg_volume_density_lower : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), 1 ≤ m → IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → y ∈ D → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ c ρ₂ : ℝ, 0 < c ∧ 0 < ρ₂ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₂ → ENNReal.ofReal (c * ρ ^ (m + 1)) ≤ volume (F ∩ ball y ρ) ∧ ENNReal.ofReal (c * ρ ^ (m + 1)) ≤ volume (ball y ρ \ F) := by
  intro m D F μ ν y v hm hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 1: `ρ₁`, `C₁` and the annular bounds (a) for `F` and (b) for its complement
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hρ₁D, hann, -⟩ :=
    Submission.codim1_rdo_dg_cutoff_estimates m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 2: the Sobolev inequality, with a constant `c_S` independent of `(D, F, μ, ν)`
  obtain ⟨cS, hcS, hS⟩ := Submission.codim1_rdo_dg_sobolev_perimeter m hm
  -- step 3: every closed ball about `y` has positive mass, and `μ(B̄_{ρ₁}(y)) < ∞`
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have hpos : ∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0 :=
    Submission.codim1_rdo_dg_vdl_measure_closedBall_ne_zero (m + 1) μ ν y v hv0 hT
  have hfin : μ (closedBall y ρ₁) ≠ ∞ := hμK _ (isCompact_closedBall y ρ₁) hρ₁D
  -- step 4: the lower bound for `F` (printed (10))
  obtain ⟨c₁, hc₁, h₁⟩ := Submission.codim1_rdo_dg_vdl_one_sided_density m D F μ y ρ₁ C₁ cS hm
    hF hcS hC₁ hρ₁D hfin hpos (hS D F μ ν hD hF hμD hμK hν hν1 hGG)
    fun ρ δ hρ hδ hρδ => (hann ρ δ hρ hδ hρδ).1
  -- step 5: `Fᶜ` satisfies the Gauss–Green identity with normal `−ν`, so the Sobolev inequality
  -- holds for `Fᶜ`; with (b) this gives the lower bound for `Fᶜ` (printed (11))
  have hGGc := Submission.codim1_rdo_dg_vdl_gauss_green_compl (m + 1) D F μ ν hF hGG
  obtain ⟨c₂, hc₂, h₂⟩ := Submission.codim1_rdo_dg_vdl_one_sided_density m D Fᶜ μ y ρ₁ C₁ cS hm
    hF.compl hcS hC₁ hρ₁D hfin hpos
    (hS D Fᶜ μ (fun z => -ν z) hD hF.compl hμD hμK hν.neg
      (fun z => (norm_neg (ν z)).trans (hν1 z)) hGGc)
    fun ρ δ hρ hδ hρδ => by
      rw [← Set.sdiff_eq_compl_inter]
      exact (hann ρ δ hρ hδ hρδ).2
  -- step 6: `c = min c₁ c₂` and `ρ₂ = ρ₁`, using `B_ρ(y) \ F = Fᶜ ∩ B_ρ(y)`
  refine ⟨min c₁ c₂, ρ₁, lt_min hc₁ hc₂, hρ₁, fun ρ hρ hρρ₁ => ⟨?_, ?_⟩⟩
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left c₁ c₂)
      (pow_nonneg hρ.le _))).trans (h₁ ρ hρ hρρ₁)
  · rw [Set.sdiff_eq_compl_inter]
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right c₁ c₂)
      (pow_nonneg hρ.le _))).trans (h₂ ρ hρ hρρ₁)

end Submission

end GMT.Ch07
