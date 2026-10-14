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

/-- **Adjoint identities of the graph chart** (Simon 7.5.2 with Ch. 6, 2.35; step 1 of the
chart perimeter estimate).  Let `ι : ℝ^{n+1} → ℝᴾ` be a linear isometry with adjoint `A = ι*`,
and let `u` be differentiable on `D = B_{δ₁}(0)` with values in `(range ι)ᗮ`; put
`G(y) = x + ιy + u(y)`.  Then `‖A‖ ≤ 1`, `Aι = id`, and for `v ∈ D`: `A(G(v) − x) = v`,
`G(v) − x − ιA(G(v) − x) = u(v)` and `A ∘ DG(v) = id`.  Indeed `‖A‖ = ‖ι‖ ≤ 1`,
`⟨Aιz, w⟩ = ⟨ιz, ιw⟩ = ⟨z, w⟩` and `⟨Au(v), w⟩ = ⟨u(v), ιw⟩ = 0`, so `Au ≡ 0` on `D`; since `D`
is open, `DG(v) = ι + Du(v)` and `A ∘ Du(v) = D(A ∘ u)(v) = 0`. -/
theorem Submission.codim1_lur_graph_chart_adjoint_identities : ∀ (P n : ℕ) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ : ℝ), DifferentiableOn ℝ u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap‖ ≤ 1 ∧ (∀ z : Euclid (n + 1), ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι z) = z) ∧ ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ContinuousLinearMap.adjoint ι.toContinuousLinearMap (x + ι v + u v - x) = v ∧ x + ι v + u v - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (x + ι v + u v - x)) = u v ∧ ∀ y : Euclid (n + 1), ContinuousLinearMap.adjoint ι.toContinuousLinearMap (fderiv ℝ (fun y => x + ι y + u y) v y) = y := by
  intro P n x ι u δ₁ hu horth
  set A := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hAdef
  -- `‖A‖ = ‖ι‖ ≤ 1`
  have hA : ‖A‖ ≤ 1 := by
    rw [hAdef, LinearIsometryEquiv.norm_map]
    exact ι.norm_toContinuousLinearMap_le
  -- `Aι = id`: `⟨Aιz, w⟩ = ⟨ιz, ιw⟩ = ⟨z, w⟩`
  have hAι : ∀ z, A (ι z) = z := by
    intro z
    apply ext_inner_right ℝ
    intro w
    rw [hAdef, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map z w
  -- `A u = 0` on `D`: `⟨Au(v), w⟩ = ⟨u(v), ιw⟩ = 0`
  have hAu : ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, A (u v) = 0 := by
    intro v hv
    apply ext_inner_right ℝ
    intro w
    rw [hAdef, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact horth v hv w
  refine ⟨hA, hAι, fun v hv => ?_⟩
  have hsub : x + ι v + u v - x = ι v + u v := by abel
  have hπ : A (x + ι v + u v - x) = v := by
    rw [hsub, map_add, hAι, hAu v hv, add_zero]
  refine ⟨hπ, ?_, fun y => ?_⟩
  · rw [hπ, hsub]; abel
  · -- `DG(v) = ι + Du(v)`, and `A ∘ Du(v) = 0` since `A ∘ u ≡ 0` on the open ball `D`
    have hvn : ball (0 : Euclid (n + 1)) δ₁ ∈ 𝓝 v := isOpen_ball.mem_nhds hv
    have hud : DifferentiableAt ℝ u v := hu.differentiableAt hvn
    have hG : fderiv ℝ (fun y => x + ι y + u y) v = ι.toContinuousLinearMap + fderiv ℝ u v :=
      ((ι.toContinuousLinearMap.hasFDerivAt).const_add x).add hud.hasFDerivAt |>.fderiv
    have hAdu : A ∘L fderiv ℝ u v = 0 := by
      have h0 : (fun y => A (u y)) =ᶠ[𝓝 v] fun _ => (0 : Euclid (n + 1)) :=
        Filter.eventually_of_mem hvn fun z hz => hAu z hz
      exact (A.hasFDerivAt.comp v hud.hasFDerivAt).unique
        ((hasFDerivAt_const (0 : Euclid (n + 1)) v).congr_of_eventuallyEq h0)
    have hAdu' : A (fderiv ℝ u v y) = 0 := by
      simpa using congrArg (fun L : Euclid (n + 1) →L[ℝ] Euclid (n + 1) => L y) hAdu
    rw [hG]
    show A (ι y + fderiv ℝ u v y) = y
    rw [map_add, hAdu', add_zero]
    exact hAι y

/-- **Geometry of the graph chart** (Simon 7.5.2, used in 7.5.8).  Let `ι : ℝ^{n+1} → ℝᴾ` be a
linear isometry with adjoint `A = ι*`, `D = B_{δ₁}(0)`, `u` be `C²` on `D` with values in
`(range ι)ᗮ`, `|u| < δ₂/2` and `G(y) = x + ιy + u(y) ∈ N` on `D`, and let `u` be the only such graph
of `N` over `D` within `δ₂` (`x + ιv + h ∈ N`, `|v| < δ₁`, `|h| < δ₂`, `h ⊥ range ι` force
`h = u(v)`).  With `Z = {w : |A(w − x)| < δ₁, |w − x − ιA(w − x)| < δ₂}`: `G` is a `C²` immersion,
`DG(v) = ι + Du(v)`, `G` is injective on `D`, `Z` is open, `D ∩ G⁻¹K` is compact for compact
`K ⊆ Z`, `S ∩ Z = G(D ∩ G⁻¹S)` for `S ⊆ N`, and `D ∩ G⁻¹S` is Borel for Borel `S`.  The key
identity is `A(G(v) − x) = v` on `D` (`Aι = id`, `A u = 0`); `Du(v) ⊥ range ι` (differentiate
`⟨ιw, u⟩ ≡ 0`) gives `|DG(v)a| ≥ |a|`. -/
theorem Submission.codim1_lur_cd_graph_chart_geometry : ∀ (P n : ℕ) (N : Set (Euclid P)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ), ContDiffOn ℝ 2 u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ‖u v‖ < δ₂ / 2) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, x + ι v + u v ∈ N) → (∀ (v : Euclid (n + 1)) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid (n + 1), inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v) → ContDiffOn ℝ 2 (fun y => x + ι y + u y) (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ a : Euclid (n + 1), fderiv ℝ (fun y => x + ι y + u y) v a = ι a + fderiv ℝ u v a) ∧ (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, Function.Injective (fderiv ℝ (fun y => x + ι y + u y) v)) ∧ InjOn (fun y => x + ι y + u y) (ball 0 δ₁) ∧ IsOpen {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} → IsCompact (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' K)) ∧ (∀ S : Set (Euclid P), S ⊆ N → S ∩ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} = (fun y => x + ι y + u y) '' (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' S)) ∧ ∀ S : Set (Euclid P), MeasurableSet S → MeasurableSet (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' S) := by
  intro P n N x ι u δ₁ δ₂ hu horth hsmall hN huniq
  set A := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hA
  -- `Aι = id`, `A` kills `(range ι)ᗮ`, and `w − x − ιA(w − x) ⊥ range ι`
  have hAι : ∀ a, A (ι a) = a := fun a => ext_inner_right ℝ fun b => by
    rw [hA, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map a b
  have hA0 : ∀ h : Euclid P, (∀ w, inner ℝ (ι w) h = 0) → A h = 0 := fun h hh =>
    ext_inner_right ℝ fun b => by
      rw [hA, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
      exact hh b
  have hperp : ∀ w : Euclid P, ∀ b, inner ℝ (ι b) (w - x - ι (A (w - x))) = 0 := fun w b => by
    rw [inner_sub_right, ι.inner_map_map, hA, ContinuousLinearMap.adjoint_inner_right]
    simp
  -- `A(G(v) − x) = v` on `D`
  have hπG : ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, A (x + ι v + u v - x) = v := fun v hv => by
    rw [show x + ι v + u v - x = ι v + u v by abel, map_add, hAι, hA0 _ (horth v hv), add_zero]
  have hG2 : ContDiffOn ℝ 2 (fun y => x + ι y + u y) (ball 0 δ₁) :=
    (contDiffOn_const.add ι.contDiff.contDiffOn).add hu
  have hGc : ContinuousOn (fun y => x + ι y + u y) (ball 0 δ₁) := hG2.continuousOn
  have hud : ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, DifferentiableAt ℝ u v := fun v hv =>
    (hu.differentiableOn (by norm_num) v hv).differentiableAt (isOpen_ball.mem_nhds hv)
  have hGd : ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁,
      HasFDerivAt (fun y => x + ι y + u y) (ι.toContinuousLinearMap + fderiv ℝ u v) v :=
    fun v hv => (ι.toContinuousLinearMap.hasFDerivAt.const_add x).add (hud v hv).hasFDerivAt
  -- `Du(v)` maps into `(range ι)ᗮ`: differentiate `⟨ιw, u⟩ ≡ 0` on the open set `D`
  have hDu : ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w a, inner ℝ (ι w) (fderiv ℝ u v a) = 0 := by
    intro v hv w a
    have h1 : HasFDerivAt (fun y => inner ℝ (ι w) (u y))
        ((innerSL ℝ (ι w)).comp (fderiv ℝ u v)) v :=
      (innerSL ℝ (ι w)).hasFDerivAt.comp v (hud v hv).hasFDerivAt
    have h2 : HasFDerivAt (fun y => inner ℝ (ι w) (u y)) (0 : Euclid (n + 1) →L[ℝ] ℝ) v :=
      (hasFDerivAt_const (0 : ℝ) v).congr_of_eventuallyEq
        (Filter.eventually_of_mem (isOpen_ball.mem_nhds hv) fun y hy => horth y hy w)
    simpa using congrArg (fun L => L a) (h1.unique h2)
  refine ⟨hG2, fun v hv a => ?_, fun v hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hGd v hv).fderiv]
    rfl
  · -- `⟨ιa, DG(v)a⟩ = |a|²`
    rw [(hGd v hv).fderiv]
    intro a b hab
    have h0 : (ι.toContinuousLinearMap + fderiv ℝ u v) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h1 : inner ℝ (ι (a - b)) ((ι.toContinuousLinearMap + fderiv ℝ u v) (a - b)) =
        ‖a - b‖ ^ 2 := by
      rw [add_apply, inner_add_right, hDu v hv, add_zero,
        LinearIsometry.coe_toContinuousLinearMap, ι.inner_map_map, real_inner_self_eq_norm_sq]
    rw [h0, inner_zero_right] at h1
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1.symm))
  · intro v hv v' hv' h
    have h' : x + ι v + u v = x + ι v' + u v' := h
    rw [← hπG v hv, ← hπG v' hv', h']
  · exact (isOpen_lt (by fun_prop) continuous_const).and (isOpen_lt (by fun_prop) continuous_const)
  · -- `D ∩ G⁻¹K = A(K − x) ∩ G⁻¹K`, a closed subset of the compact set `A(K − x) ⊆ D`
    intro K hK hKZ
    have hK' : IsCompact ((fun w => A (w - x)) '' K) := hK.image (by fun_prop)
    have hK'D : (fun w => A (w - x)) '' K ⊆ ball 0 δ₁ := by
      rintro _ ⟨w, hw, rfl⟩
      exact mem_ball_zero_iff.mpr (hKZ hw).1
    have heq : ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' K =
        (fun w => A (w - x)) '' K ∩ (fun y => x + ι y + u y) ⁻¹' K := by
      ext v
      constructor
      · rintro ⟨hv, hvK⟩
        exact ⟨⟨_, hvK, hπG v hv⟩, hvK⟩
      · rintro ⟨hv, hvK⟩
        exact ⟨hK'D hv, hvK⟩
    rw [heq]
    exact hK'.of_isClosed_subset
      ((hGc.mono hK'D).preimage_isClosed_of_isClosed hK'.isClosed hK.isClosed) inter_subset_left
  · intro S hSN
    ext w
    constructor
    · -- graph uniqueness at `v = A(w − x)`, `h = w − x − ιv`
      rintro ⟨hwS, hw1, hw2⟩
      have hx : x + ι (A (w - x)) + (w - x - ι (A (w - x))) = w := by abel
      have h := huniq (A (w - x)) (w - x - ι (A (w - x))) hw1 hw2 (hperp w)
        (by rw [hx]; exact hSN hwS)
      refine ⟨A (w - x), ⟨mem_ball_zero_iff.mpr hw1, ?_⟩, ?_⟩
      · show x + ι (A (w - x)) + u (A (w - x)) ∈ S
        rw [← h, hx]
        exact hwS
      · show x + ι (A (w - x)) + u (A (w - x)) = w
        rw [← h, hx]
    · rintro ⟨v, ⟨hv, hvS⟩, rfl⟩
      refine ⟨hvS, ?_, ?_⟩
      · show ‖A (x + ι v + u v - x)‖ < δ₁
        rw [hπG v hv]
        exact mem_ball_zero_iff.mp hv
      · show ‖x + ι v + u v - x - ι (A (x + ι v + u v - x))‖ < δ₂
        rw [hπG v hv, show x + ι v + u v - x - ι v = u v by abel]
        linarith [hsmall v hv, norm_nonneg (u v)]
  · -- on `D`, `G` agrees with the Borel map equal to `G` on `D` and to `x` off `D`
    intro S hS
    classical
    have hm : Measurable ((ball (0 : Euclid (n + 1)) δ₁).piecewise (fun y => x + ι y + u y)
        fun _ => x) :=
      hGc.measurable_piecewise continuousOn_const measurableSet_ball
    have heq : ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' S = ball 0 δ₁ ∩
        (ball (0 : Euclid (n + 1)) δ₁).piecewise (fun y => x + ι y + u y) (fun _ => x) ⁻¹' S := by
      ext v
      constructor
      · rintro ⟨hv, h⟩
        exact ⟨hv, by rwa [mem_preimage, piecewise_eq_of_mem _ _ _ hv]⟩
      · rintro ⟨hv, h⟩
        exact ⟨hv, by rwa [mem_preimage, piecewise_eq_of_mem _ _ _ hv] at h⟩
    rw [heq]
    exact measurableSet_ball.inter (hm hS)
/-- **Regularity of the pulled-back vector field** (Simon Ch. 6, 2.35, used for 7.5).  Let
`D ⊆ ℝⁿ⁺¹` be open, `G` be `C²` on `D`, `ω` be a smooth `n`-form on `ℝᴾ`, and let
`C = D ∩ G⁻¹(spt ω)` be compact.  The zero extension `Φ` of
`Ψ(v) = Σⱼ (−1)ʲ ω(G v)(DG(v)e_{j.succAbove 0}, …, DG(v)e_{j.succAbove (n−1)}) eⱼ` is `C¹` with
compact support in `D`.  Each coefficient is the smooth evaluation `(α, b) ↦ α b` (a continuous
multilinear map on the diagonal) of the `C¹` maps `v ↦ ω(G v)` and `v ↦ (DG(v)e_{j.succAbove k})ₖ`,
so `Ψ` is `C¹` on `D`; `Φ` vanishes off the compact, hence closed, set `C ⊆ D`, so `Φ` is `C¹` on
the open cover `D ∪ Cᶜ` and `spt Φ ⊆ C`. -/
theorem Submission.codim1_lur_cd_pullback_field_regularity : ∀ (P n : ℕ) (D : Set (Euclid (n + 1))) (G : Euclid (n + 1) → Euclid P) (ω : DifferentialForm (Euclid P) n) (Φ : Euclid (n + 1) → Euclid (n + 1)), IsOpen D → ContDiffOn ℝ 2 G D → ContDiff ℝ (⊤ : ℕ∞) ω → IsCompact (D ∩ G ⁻¹' tsupport ω) → Φ = D.indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * ω (G v) (fun k => fderiv ℝ G v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) → ContDiff ℝ 1 Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ D := by
  intro P n D G ω Φ hD hG hω hC hΦ
  -- joint evaluation `(α, b) ↦ α b` of continuous multilinear forms: a continuous multilinear
  -- map restricted to the diagonal, hence smooth
  have hev : ContDiff ℝ 1 (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclid P) ℝ ×
      (Fin n → Euclid P) => p.1 p.2) :=
    (ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclid P) ℝ)
      ).continuousMultilinearMapOption.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
  -- `v ↦ ω (G v)` and `v ↦ DG(v)` are `C¹` on `D`
  have hωG : ContDiffOn ℝ 1 (fun v => (ω (G v)).toContinuousMultilinearMap) D :=
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp_contDiffOn
      ((hω.of_le (by exact_mod_cast le_top)).comp_contDiffOn (hG.of_le (by norm_num)))
  have hDG : ContDiffOn ℝ 1 (fderiv ℝ G) D := hG.fderiv_of_isOpen hD (by norm_num)
  have hcoef : ∀ j : Fin (n + 1), ContDiffOn ℝ 1 (fun v => ω (G v)
      (fun k => fderiv ℝ G v (EuclideanSpace.single (j.succAbove k) 1))) D := fun j =>
    hev.comp_contDiffOn (hωG.prodMk (contDiffOn_pi.2 fun _ => hDG.clm_apply contDiffOn_const))
  have hΨ : ContDiffOn ℝ 1 (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * ω (G v)
      (fun k => fderiv ℝ G v (EuclideanSpace.single (j.succAbove k) 1))) •
        EuclideanSpace.single j (1 : ℝ)) D :=
    ContDiffOn.sum fun j _ => (contDiffOn_const.mul (hcoef j)).smul contDiffOn_const
  -- `Φ` vanishes off the compact, hence closed, set `C = D ∩ G⁻¹(spt ω)`
  have hsupp : support Φ ⊆ D ∩ G ⁻¹' tsupport ω := by
    intro v hv
    by_contra hvC
    refine hv ?_
    rw [hΦ]
    by_cases hvD : v ∈ D
    · rw [indicator_of_mem hvD]
      simp [image_eq_zero_of_notMem_tsupport fun h => hvC ⟨hvD, h⟩]
    · exact indicator_of_notMem hvD _
  have hCcl : IsClosed (D ∩ G ⁻¹' tsupport ω) := hC.isClosed
  have htsupp : tsupport Φ ⊆ D ∩ G ⁻¹' tsupport ω := closure_minimal hsupp hCcl
  refine ⟨?_, hC.of_isClosed_subset (isClosed_tsupport _) htsupp,
    htsupp.trans inter_subset_left⟩
  -- glue: `Φ = Ψ` on the open set `D`, `Φ = 0` on the open set `Cᶜ`, and `D ∪ Cᶜ = ℝⁿ⁺¹`
  refine contDiff_of_contDiffOn_union_of_isOpen (s := D) (t := (D ∩ G ⁻¹' tsupport ω)ᶜ)
    (hΨ.congr fun v hv => by rw [hΦ, indicator_of_mem hv])
    ((contDiffOn_const (c := (0 : Euclid (n + 1)))).congr
      fun v hv => notMem_support.1 fun h => hv (hsupp h)) ?_ hD hCcl.isOpen_compl
  exact eq_univ_of_forall fun v => (em (v ∈ D)).imp id fun hv h => hv h.1
/-- **Area formula for an injective immersion, Gram form** (Simon Ch. 2, 3.1–3.5; step (1b)
of the chart divergence formula in the proof of Simon 7.5.2).  Let `G : ℝᵐ → ℝᴾ` be
differentiable with injective derivative at every point of the Borel set `F` and injective on `F`.
With `eᵢ` the standard basis of `ℝᵐ`, every `h : ℝᴾ → ℝ` has
`∫_{G(F)} h dHᵐ = ∫_F √det(⟨DG(v)eᵢ, DG(v)eⱼ⟩) h(G(v)) dv`.

Linear case (Simon 3.1): an injective linear `B` factors as `ι ∘ C` with `ι` an isometry of `ℝᵐ`
onto `range B`, so `Hᵐ(B S) = |det C| Lᵐ(S)`, and the Gram matrix of `B` is `CᵀC`.  The
approximation argument for 3.2: on countably many Borel pieces of `F`, `G` and (a.e.) `DG` are
`η`-close to an injective linear map, so the Lipschitz bound for `Hᵐ` puts `Hᵐ(G t)` and `∫_t J`
within a factor `(1 + 2η)^{2m}` of each other for Borel `t ⊆ F`.  Letting `η → 0` gives
`Hᵐ(G t) = ∫_t J`, and the integral identity follows as for
`integral_image_eq_integral_abs_det_fderiv_smul`. -/
theorem Submission.codim1_lur_cd_injective_area_formula_gram : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (F : Set (Euclid m)), MeasurableSet F → (∀ v ∈ F, DifferentiableAt ℝ G v) → (∀ v ∈ F, Function.Injective (fderiv ℝ G v)) → InjOn G F → ∀ h : Euclid P → ℝ, ∫ w in G '' F, h w ∂μHE[m] = ∫ v in F, Real.sqrt (Matrix.det (Matrix.of fun i j : Fin m => inner ℝ (fderiv ℝ G v (EuclideanSpace.single i 1)) (fderiv ℝ G v (EuclideanSpace.single j 1)))) * h (G v) := by
  intro P m G F hF hG hreg hinj h
  -- `Jf B = √det(⟨B eᵢ, B eⱼ⟩)`, the Gram Jacobian of a linear map `B : ℝᵐ → ℝᴾ`
  set Jf : (Euclid m →L[ℝ] Euclid P) → ℝ := fun B => Real.sqrt (Matrix.det (Matrix.of
    fun i j : Fin m => inner ℝ (B (EuclideanSpace.single i 1)) (B (EuclideanSpace.single j 1))))
  -- (1) Linear area formula: `B = ι ∘ C` with `ι` an isometry onto `range B`, so
  -- `Hᵐ(B S) = Lᵐ(C S) = |det C| Lᵐ(S)`, and `⟨B eᵢ, B eⱼ⟩ = ⟨C eᵢ, C eⱼ⟩ = (CᵀC)ᵢⱼ`.
  have hlin : ∀ B : Euclid m →L[ℝ] Euclid P, Injective B → ∀ S : Set (Euclid m),
      μHE[m] (B '' S) = ENNReal.ofReal (Jf B) * volume S := by
    intro B hB S
    have hW : Module.finrank ℝ (LinearMap.range (B : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hB, finrank_euclideanSpace_fin]
    set b := (stdOrthonormalBasis ℝ (LinearMap.range (B : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hW)
    set C : Euclid m →ₗ[ℝ] Euclid m :=
      b.repr.toLinearMap ∘ₗ (B : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hBC : ∀ x, B x = (b.repr.symm (C x) : Euclid P) := fun x => by simp [C]
    have hι : Isometry fun y => (b.repr.symm y : Euclid P) :=
      isometry_subtype_coe.comp b.repr.symm.isometry
    have hgram : Jf B = |LinearMap.det C| := by
      set e := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      have hM : (Matrix.of fun i j : Fin m => inner ℝ (B (EuclideanSpace.single i 1))
          (B (EuclideanSpace.single j 1))) =
          (LinearMap.toMatrix e e C).transpose * LinearMap.toMatrix e e C := by
        ext i j
        rw [Matrix.of_apply, hBC, hBC, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map,
          Matrix.mul_apply]
        simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, e,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr, PiLp.inner_apply,
          RCLike.inner_apply, conj_trivial]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      show Real.sqrt _ = _
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, ← sq,
        Real.sqrt_sq_eq_abs]
    rw [show B '' S = (fun y => (b.repr.symm y : Euclid P)) '' (C '' S) by
        rw [image_image]; exact image_congr fun x _ => hBC x,
      hι.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_image_linearMap, hgram]
  -- (2) Lipschitz comparison: if `‖f x - f y‖ ≤ K ‖g x - g y‖` on `S` and `g` is injective
  -- there, then `Hᵐ(f S) ≤ Kᵐ Hᵐ(g S)` (the Lipschitz bound for `f ∘ g⁻¹` on `g S`).
  have hcmp : ∀ (f g : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn g S →
      (∀ x ∈ S, ∀ y ∈ S, ‖f x - f y‖ ≤ K * ‖g x - g y‖) →
      μHE[m] (f '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (g '' S) := by
    intro f g S K hg hfg
    have hθ : ∀ x ∈ S, f (invFunOn g S (g x)) = f x := fun x hx => by
      rw [hg.leftInvOn_invFunOn hx]
    have hlip : LipschitzOnWith K (f ∘ invFunOn g S) (g '' S) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [comp_apply, comp_apply, hθ x hx, hθ y hy, dist_eq_norm, dist_eq_norm]
      exact hfg x hx y hy
    have himg : f '' S = (f ∘ invFunOn g S) '' (g '' S) := by
      rw [image_image]; exact image_congr fun x hx => (hθ x hx).symm
    have key := hlip.hausdorffMeasure_image_le (d := (m : ℝ)) m.cast_nonneg
    rw [ENNReal.rpow_natCast] at key
    rw [himg, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]
    exact mul_le_mul_right key _
  -- (3) Jacobian comparison for injective linear maps: (1) and (2) on the unit ball.
  have hjcmp : ∀ (B₁ B₂ : Euclid m →L[ℝ] Euclid P) (K : NNReal), Injective B₁ → Injective B₂ →
      (∀ z, ‖B₁ z‖ ≤ K * ‖B₂ z‖) →
      ENNReal.ofReal (Jf B₁) ≤ (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf B₂) := by
    intro B₁ B₂ K h₁ h₂ hB
    have key := hcmp B₁ B₂ (ball 0 1) K h₂.injOn fun x _ y _ => by
      rw [← map_sub, ← map_sub]; exact hB _
    rw [hlin B₁ h₁, hlin B₂ h₂, ← mul_assoc] at key
    exact (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume 0 one_pos).ne'
      measure_ball_lt_top.ne).1 key
  -- (4) If `G` is `δ`-approximated by `A` on `S`, then `‖DG(v) - A‖ ≤ δ` at a.e. `v ∈ S`
  -- (at Lebesgue density points; the argument of `ApproximatesLinearOn.norm_fderiv_sub_le`).
  have hdcl : ∀ (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal) (S : Set (Euclid m)), S ⊆ F →
      MeasurableSet S → ApproximatesLinearOn G A S δ →
      ∀ᵐ v ∂(volume.restrict S), ‖fderiv ℝ G v - A‖ ≤ δ := by
    open scoped Pointwise in
    intro A δ S hSF hS hA
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid m)) S,
      ae_restrict_mem hS] with x hx xs
    refine ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(fderiv ℝ G x - A) z‖ ≤
        (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ε)
          (𝓝[>] 0) (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ G x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (S ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume S x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0, ball x ρ ∩ S ⊆
        {y | ‖G y - G x - (fderiv ℝ G x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1
        ((hG x (hSF xs)).hasFDerivAt.hasFDerivWithinAt (s := S)).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ :=
      nhdsWithin_le_nhds
        (eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos))
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (S ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ G x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ G x - A) a‖ = ‖(fderiv ℝ G x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖G y - G x - A (y - x) - (G y - G x - (fderiv ℝ G x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖G y - G x - A (y - x)‖ + ‖G y - G x - (fderiv ℝ G x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hA _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ G x - A) z‖ = ‖(fderiv ℝ G x - A) a + (fderiv ℝ G x - A) (z - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(fderiv ℝ G x - A) a‖ + ‖(fderiv ℝ G x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ G x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (5) A lower bound `‖z‖ ≤ c(A) ‖A z‖` for injective `A`.
  have hmod : ∀ A : Euclid m →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ z, ‖z‖ ≤ c * ‖A z‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨c, cpos, hc⟩ := (A : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.2 hA)
      exact ⟨c, cpos, fun _ z => by simpa using hc.le_mul_dist z 0⟩
    · exact ⟨1, one_pos, fun h' => absurd h' hA⟩
  choose c cpos hc using hmod
  have hcont : ContinuousOn G F := fun v hv => (hG v hv).continuousAt.continuousWithinAt
  -- (6) For `0 < η ≤ 1/2` and `K = 1 + 2η`, partition a Borel `t ⊆ F` into pieces on which `G`
  -- and (a.e.) `DG` are `η`-close to an injective `A`; then (1)–(3) give two-sided bounds.
  have hpiece : ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ t ⊆ F, MeasurableSet t →
      μHE[m] (G '' t) ≤ (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2 *
        ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) ∧
      ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) ≤
        (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2 * μHE[m] (G '' t) := by
    intro η ηpos ηle t htF ht
    set K : NNReal := (1 + 2 * η).toNNReal
    have hKr : (K : ℝ) = 1 + 2 * η := Real.coe_toNNReal _ (by linarith)
    have hrel : ∀ u w : Euclid P, ‖u - w‖ ≤ η * ‖w‖ → ‖u‖ ≤ K * ‖w‖ ∧ ‖w‖ ≤ K * ‖u‖ := by
      intro u w huw
      have h1 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := norm_le_insert' u w
      have h2 : ‖w‖ ≤ ‖u‖ + ‖u - w‖ := by simpa [norm_sub_rev] using norm_le_insert' w u
      have h3 : (1 - η) * ‖w‖ ≤ ‖u‖ := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 + 2 * η)
      have h5 : 0 ≤ η * (1 - 2 * η) * ‖w‖ :=
        mul_nonneg (mul_nonneg ηpos.le (by linarith)) (norm_nonneg w)
      rw [hKr]
      constructor <;> nlinarith [norm_nonneg u, norm_nonneg w, mul_nonneg ηpos.le (norm_nonneg w)]
    rcases t.eq_empty_or_nonempty with rfl | tne
    · simp
    obtain ⟨T, A, Tdisj, Tmeas, tT, Tappr, TA⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G t (fderiv ℝ G)
        (fun v hv => (hG v (htF hv)).hasFDerivAt.hasFDerivWithinAt)
        (fun B => η.toNNReal / c B) (fun B => (div_pos (Real.toNNReal_pos.2 ηpos) (cpos B)).ne')
    have Ainj : ∀ n, Injective (A n) := fun n => by
      obtain ⟨y, yt, hy⟩ := TA tne n
      rw [hy]; exact hreg y (htF yt)
    have hpc : ∀ n, μHE[m] (G '' (t ∩ T n)) ≤ ((K : ℝ≥0∞) ^ m) ^ 2 *
          ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v)) ∧
        ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v)) ≤
          ((K : ℝ≥0∞) ^ m) ^ 2 * μHE[m] (G '' (t ∩ T n)) := by
      intro n
      have hSF : t ∩ T n ⊆ F := inter_subset_left.trans htF
      have hS : MeasurableSet (t ∩ T n) := ht.inter (Tmeas n)
      have hcpos : (0 : ℝ) < c (A n) := cpos (A n)
      have hc0 : (c (A n) : ℝ) ≠ 0 := hcpos.ne'
      have happ : ∀ x ∈ t ∩ T n, ∀ y ∈ t ∩ T n,
          ‖(G x - G y) - (A n x - A n y)‖ ≤ η * ‖A n x - A n y‖ := by
        intro x hx y hy
        have h1 := Tappr n x hx y hy
        rw [NNReal.coe_div, Real.coe_toNNReal _ ηpos.le] at h1
        have h2 := hc (A n) (Ainj n) (x - y)
        rw [← map_sub]
        calc ‖G x - G y - A n (x - y)‖ ≤ η / c (A n) * ‖x - y‖ := h1
          _ ≤ η / c (A n) * (c (A n) * ‖A n (x - y)‖) := by gcongr
          _ = η * ‖A n (x - y)‖ := by field_simp
      have hder : ∀ᵐ v ∂(volume.restrict (t ∩ T n)), ∀ z,
          ‖fderiv ℝ G v z - A n z‖ ≤ η * ‖A n z‖ := by
        filter_upwards [hdcl (A n) _ (t ∩ T n) hSF hS (Tappr n)] with v hv z
        rw [NNReal.coe_div, Real.coe_toNNReal _ ηpos.le] at hv
        have h2 := hc (A n) (Ainj n) z
        calc ‖fderiv ℝ G v z - A n z‖ = ‖(fderiv ℝ G v - A n) z‖ := rfl
          _ ≤ ‖fderiv ℝ G v - A n‖ * ‖z‖ := (fderiv ℝ G v - A n).le_opNorm z
          _ ≤ η / c (A n) * ‖z‖ := by gcongr
          _ ≤ η / c (A n) * (c (A n) * ‖A n z‖) := by gcongr
          _ = η * ‖A n z‖ := by field_simp
      have hJ : ∀ᵐ v ∂(volume.restrict (t ∩ T n)),
          ENNReal.ofReal (Jf (fderiv ℝ G v)) ≤ (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf (A n)) ∧
          ENNReal.ofReal (Jf (A n)) ≤ (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf (fderiv ℝ G v)) := by
        filter_upwards [hder, ae_restrict_mem hS] with v hv hvS
        exact ⟨hjcmp _ _ K (hreg v (hSF hvS)) (Ainj n) fun z => (hrel _ _ (hv z)).1,
          hjcmp _ _ K (Ainj n) (hreg v (hSF hvS)) fun z => (hrel _ _ (hv z)).2⟩
      have hup := hcmp G (A n) (t ∩ T n) K (Ainj n).injOn
        fun x hx y hy => (hrel _ _ (happ x hx y hy)).1
      have hlo := hcmp (A n) G (t ∩ T n) K (hinj.mono hSF)
        fun x hx y hy => (hrel _ _ (happ x hx y hy)).2
      rw [hlin (A n) (Ainj n), ← setLIntegral_const] at hup hlo
      have hKtop : (K : ℝ≥0∞) ^ m ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
      constructor
      · calc μHE[m] (G '' (t ∩ T n))
            ≤ (K : ℝ≥0∞) ^ m * ∫⁻ _ in t ∩ T n, ENNReal.ofReal (Jf (A n)) := hup
          _ ≤ (K : ℝ≥0∞) ^ m * ∫⁻ v in t ∩ T n, (K : ℝ≥0∞) ^ m *
                ENNReal.ofReal (Jf (fderiv ℝ G v)) :=
            mul_le_mul_right (lintegral_mono_ae (hJ.mono fun v hv => hv.2)) _
          _ = _ := by rw [lintegral_const_mul' _ _ hKtop, ← mul_assoc, sq]
      · calc ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v))
            ≤ ∫⁻ _ in t ∩ T n, (K : ℝ≥0∞) ^ m * ENNReal.ofReal (Jf (A n)) :=
            lintegral_mono_ae (hJ.mono fun v hv => hv.1)
          _ = (K : ℝ≥0∞) ^ m * ∫⁻ _ in t ∩ T n, ENNReal.ofReal (Jf (A n)) :=
            lintegral_const_mul' _ _ hKtop
          _ ≤ (K : ℝ≥0∞) ^ m * ((K : ℝ≥0∞) ^ m * μHE[m] (G '' (t ∩ T n))) :=
            mul_le_mul_right hlo _
          _ = _ := by rw [← mul_assoc, sq]
    have hdisj : Pairwise (Disjoint on fun n => t ∩ T n) := fun i j hij =>
      Disjoint.mono inter_subset_right inter_subset_right (Tdisj hij)
    have hunion : t = ⋃ n, t ∩ T n := by rw [← inter_iUnion, inter_eq_left.2 tT]
    have hX : μHE[m] (G '' t) = ∑' n, μHE[m] (G '' (t ∩ T n)) := by
      rw [show G '' t = ⋃ n, G '' (t ∩ T n) by rw [← image_iUnion, ← hunion]]
      exact measure_iUnion (fun i j hij => Disjoint.image (hdisj hij) (hinj.mono htF)
          inter_subset_left inter_subset_left)
        fun n => (ht.inter (Tmeas n)).image_of_continuousOn_injOn
          (hcont.mono (inter_subset_left.trans htF)) (hinj.mono (inter_subset_left.trans htF))
    have hY : ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) =
        ∑' n, ∫⁻ v in t ∩ T n, ENNReal.ofReal (Jf (fderiv ℝ G v)) := by
      conv_lhs => rw [hunion]
      exact lintegral_iUnion (fun n => ht.inter (Tmeas n)) hdisj _
    rw [hX, hY, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    exact ⟨ENNReal.tsum_le_tsum fun n => (hpc n).1, ENNReal.tsum_le_tsum fun n => (hpc n).2⟩
  -- (7) Letting `η → 0`: `Hᵐ(G t) = ∫_t J` for every Borel `t ⊆ F`.
  have hmeas : ∀ t ⊆ F, MeasurableSet t →
      μHE[m] (G '' t) = ∫⁻ v in t, ENNReal.ofReal (Jf (fderiv ℝ G v)) := by
    intro t htF ht
    have hlim : Tendsto (fun η : ℝ => (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2) (𝓝[>] 0)
        (𝓝 1) := by
      have hc : Continuous fun η : ℝ => ((1 + 2 * η).toNNReal ^ m) ^ 2 :=
        ((continuous_real_toNNReal.comp (by fun_prop)).pow m).pow 2
      simpa using ENNReal.tendsto_coe.2 ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η ≤ 1 / 2 :=
      Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)
    have hlim' : ∀ X : ℝ≥0∞, Tendsto (fun η : ℝ => (((1 + 2 * η).toNNReal : ℝ≥0∞) ^ m) ^ 2 * X)
        (𝓝[>] 0) (𝓝 X) := fun X => by
      simpa using ENNReal.Tendsto.mul_const hlim (Or.inl one_ne_zero)
    apply le_antisymm
    · refine ge_of_tendsto (hlim' _) ?_
      filter_upwards [hev] with η hη
      exact (hpiece η hη.1 hη.2 t htF ht).1
    · refine ge_of_tendsto (hlim' _) ?_
      filter_upwards [hev] with η hη
      exact (hpiece η hη.1 hη.2 t htF ht).2
  -- (8) From the measure identity to the integral identity, as in
  -- `integral_image_eq_integral_abs_det_fderiv_smul`: `G|_F` is a measurable embedding.
  have hJm : Measurable fun v => Jf (fderiv ℝ G v) := by
    have : Continuous Jf := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det (continuous_matrix fun i j => ?_))
      exact (continuous_id.clm_apply continuous_const).inner
        (continuous_id.clm_apply continuous_const)
    exact this.measurable.comp (measurable_fderiv ℝ G)
  have hemb : MeasurableEmbedding (F.domRestrict G) :=
    { injective := injOn_iff_injective.1 hinj
      measurable := (continuousOn_iff_continuous_domRestrict.1 hcont).measurable
      measurableSet_image' := fun s hs => by
        rw [domRestrict_eq, image_comp]
        exact (hF.subtype_image hs).image_of_continuousOn_injOn
          (hcont.mono (Subtype.coe_image_subset F s)) (hinj.mono (Subtype.coe_image_subset F s)) }
  have hmap : Measure.map (F.domRestrict G) (Measure.comap Subtype.val
      (volume.withDensity fun v => ENNReal.ofReal (Jf (fderiv ℝ G v)))) =
      μHE[m].restrict (G '' F) := by
    ext u hu
    have hpre : MeasurableSet (F.domRestrict G ⁻¹' u) := hemb.measurable hu
    have hset : Subtype.val '' (F.domRestrict G ⁻¹' u) = F ∩ G ⁻¹' u :=
      Subtype.image_preimage_coe F (G ⁻¹' u)
    have htm : MeasurableSet (F ∩ G ⁻¹' u) := hset ▸ hF.subtype_image hpre
    rw [Measure.map_apply hemb.measurable hu,
      Measure.comap_apply _ Subtype.val_injective (fun _ hs => hF.subtype_image hs) _ hpre, hset,
      withDensity_apply _ htm, Measure.restrict_apply hu, ← hmeas _ inter_subset_left htm,
      image_inter_preimage, inter_comm]
  rw [← hmap, hemb.integral_map]
  simp only [domRestrict_apply, ← comp_apply (f := h), ENNReal.ofReal]
  rw [← (MeasurableEmbedding.subtype_coe hF).integral_map, map_comap_subtype_coe hF,
    setIntegral_withDensity_eq_setIntegral_smul₀ hJm.real_toNNReal.aemeasurable _ hF]
  refine setIntegral_congr_fun hF fun v _ => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  rfl
/-- **Divergence of the field of a pulled-back form** (Simon 7.5.2 with Ch. 6, 2.34–2.35).  Let
`G : ℝⁿ⁺¹ → ℝᴾ` be `C²` on the open set `D`, `ω` a smooth `n`-form on `ℝᴾ`, `e` the standard basis
and `Φ = 1_D · Σⱼ (-1)ʲ ω(G)(DG e_{j.succAbove 0}, …, DG e_{j.succAbove (n-1)}) eⱼ`.  Then
`trace DΦ(v) = dω(G v)(DG(v) e₀, …, DG(v) eₙ)` on `D`.  Near `v ∈ D`, `Φ = Σⱼ (-1)ʲ β(·)(ê_j) eⱼ`
for the pull-back `β(y) = ω(G y) ∘ DG(y)` and `ê_j = j.removeNth e`, so
`trace DΦ(v) = Σⱼ (-1)ʲ Dβ(v)(eⱼ)(ê_j) = dβ(v)(e)`; and `dβ(v) = dω(G v) ∘ DG(v)` since `G` is
`C²` (`extDeriv_pullback`). -/
theorem Submission.codim1_lur_cd_pullback_field_trace : ∀ (P n : ℕ) (D : Set (Euclid (n + 1))) (G : Euclid (n + 1) → Euclid P) (ω : DifferentialForm (Euclid P) n) (Φ : Euclid (n + 1) → Euclid (n + 1)), IsOpen D → ContDiffOn ℝ 2 G D → ContDiff ℝ (⊤ : ℕ∞) ω → Φ = D.indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * ω (G v) (fun k => fderiv ℝ G v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) → ∀ v ∈ D, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ Φ v : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) = exteriorDerivative ω (G v) (fun i => fderiv ℝ G v (EuclideanSpace.single i 1)) := by
  intro P n D G ω Φ hD hG hω hΦ v hv
  -- `e` is the standard basis and `β(y) = ω(G y) ∘ DG(y)` the pulled-back form
  let e : Fin (n + 1) → Euclid (n + 1) := fun i => EuclideanSpace.single i 1
  let β : Euclid (n + 1) → Covector (Euclid (n + 1)) n :=
    fun y => (ω (G y)).compContinuousLinearMap (fderiv ℝ G y)
  -- `G` is `C²` at `v`, so `β` is differentiable at `v`
  have hGv : ContDiffAt ℝ 2 G v := hG.contDiffAt (hD.mem_nhds hv)
  have hωd : DifferentiableAt ℝ ω (G v) := (hω.differentiable (by simp)).differentiableAt
  have hβd : DifferentiableAt ℝ β v :=
    (hωd.comp v (hGv.differentiableAt (by norm_num))).continuousAlternatingMapCompContinuousLinearMap
      ((hGv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  -- near `v`, `Φ = Σⱼ cⱼ eⱼ` with `cⱼ(y) = (-1)ʲ β(y)(j.removeNth e)`
  have hΦd : HasFDerivAt Φ (∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) •
      (ContinuousAlternatingMap.apply ℝ (Euclid (n + 1)) ℝ (j.removeNth e)).comp
        (fderiv ℝ β v)).smulRight (e j)) v := by
    refine (HasFDerivAt.fun_sum (u := Finset.univ) fun (j : Fin (n + 1)) _ =>
      ((((ContinuousAlternatingMap.apply ℝ (Euclid (n + 1)) ℝ (j.removeNth e)).hasFDerivAt.comp v
        hβd.hasFDerivAt).const_mul ((-1 : ℝ) ^ (j : ℕ))).smul_const (e j))).congr_of_eventuallyEq ?_
    filter_upwards [hD.mem_nhds hv] with y hy
    rw [hΦ, Set.indicator_of_mem hy]
    rfl
  -- pull-back commutes with `d`: `dβ(v) = dω(G v) ∘ DG(v)`
  have hR : exteriorDerivative ω (G v) (fun i => fderiv ℝ G v (EuclideanSpace.single i 1)) =
      extDeriv β v e := by
    rw [extDeriv_pullback (x := v) hωd hGv (by simp)]
    rfl
  -- `trace (Σⱼ c'ⱼ ⊗ eⱼ) = Σⱼ c'ⱼ(eⱼ)`, the coordinate formula for `dβ(v)(e)`
  rw [hR, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply, hΦd.fderiv,
    ContinuousLinearMap.toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => (LinearMap.trace_smulRight _ (e j)).trans ?_
  simp [ContinuousAlternatingMap.apply_apply, zsmul_eq_mul]
/-- **Chart divergence formula** (Simon 7.5.2, steps (1a)–(1e), with Ch. 6, 2.35).  Let
`T = ∂[[E]]` in `U` for a Borel `E ⊆ N ∩ U`, and let `N` be, near `x`, the graph
`G(y) = x + ιy + u(y)` over `D = B_{δ₁}(0)` of a `C²` map `u` into `(range ι)ᗮ` with `|u| < δ₂/2`,
unique within `δ₂`, along which `ξN(G v) · J(v) = DG(v)e₀ ∧ ⋯ ∧ DG(v)eₙ` for the Gram Jacobian
`J(v) = √det(⟨DG(v)eᵢ, DG(v)eⱼ⟩)`.  If `spt ω ⊆ Z = {w : |A(w − x)| < δ₁, |w − x − ιA(w − x)| < δ₂}`
(`A = ι*`), the field `Φ = 1_D · Σⱼ (−1)ʲ ω(G)(DG e_{j.succAbove 0}, …, DG e_{j.succAbove (n−1)}) eⱼ`
is `C¹` with compact support in `D`, and `T(ω) = ∫_{D ∩ G⁻¹E} div Φ`.  Since `spt dω ⊆ spt ω ⊆ Z`
and `E ∩ Z = G(D ∩ G⁻¹E)`, the area formula for the injective immersion `G` gives
`T(ω) = ∫_{D ∩ G⁻¹E} J · ξN(G)(dω(G))`, and the orientation identity turns the integrand into
`dω(G)(DG e₀, …, DG eₙ) = div Φ`. -/
theorem Submission.codim1_lur_chart_divergence_formula : ∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ), MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → 0 < δ₁ → 0 < δ₂ → ContDiffOn ℝ 2 u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, (∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N ∧ ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1))) → (∀ (v : Euclid (n + 1)) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid (n + 1), inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v) → ∀ (ω : TestFormOn U n) (Φ : Euclid (n + 1) → Euclid (n + 1)), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} → Φ = (ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * (ω : DifferentialForm (Euclid P) n) (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) → ContDiff ℝ 1 Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ ball 0 δ₁ ∧ T ω = ∫ v in ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ Φ v : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) := by
  intro P n U N E ξN T x ι u δ₁ δ₂ hE hEN hT _ _ hu hchart huniq ω Φ hωZ hΦ
  -- the graph chart `G` on `D = B_{δ₁}(0)`: a `C²` injective immersion with `N ∩ Z = G(D)`
  obtain ⟨hG2, hDG, hDGinj, hGinj, -, hcpt, himg, hmeas⟩ :=
    Submission.codim1_lur_cd_graph_chart_geometry P n N x ι u δ₁ δ₂ hu
      (fun v hv => (hchart v hv).1) (fun v hv => (hchart v hv).2.2.1)
      (fun v hv => (hchart v hv).2.2.2.1) huniq
  set G : Euclid (n + 1) → Euclid P := fun y => x + ι y + u y
  set Z := {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧
    ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂}
  have hωs : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  -- `Φ` is `C¹` with compact support in `D`, since `D ∩ G⁻¹(spt ω)` is compact
  obtain ⟨hΦ1, hΦc, hΦD⟩ := Submission.codim1_lur_cd_pullback_field_regularity P n _ G _ Φ
    isOpen_ball hG2 hωs (hcpt _ ω.property.1.2.isCompact hωZ) hΦ
  refine ⟨hΦ1, hΦc, hΦD, ?_⟩
  set F := ball (0 : Euclid (n + 1)) δ₁ ∩ G ⁻¹' E
  have hF : MeasurableSet F := hmeas E hE
  -- localization: `E ∩ Z = G(F)`, and `ξN(dω)` vanishes on `E \ Z` since `spt dω ⊆ spt ω ⊆ Z`
  have hEZ : E ∩ Z = G '' F := himg E fun w hw => (hEN hw).1
  have hvanish : ∀ w ∈ E \ G '' F,
      ξN w (exteriorDerivative (ω : DifferentialForm (Euclid P) n) w) = 0 := by
    rintro w ⟨hwE, hwG⟩
    have hwZ : w ∉ Z := fun hwZ => hwG (hEZ ▸ ⟨hwE, hwZ⟩)
    rw [image_eq_zero_of_notMem_tsupport
      fun h => hwZ (hωZ (tsupport_exteriorDerivative_subset _ h)), map_zero]
  calc T ω = ∫ w in E, ξN w (exteriorDerivative (ω : DifferentialForm (Euclid P) n) w)
        ∂μHE[n + 1] := hT ω
    _ = ∫ w in G '' F, ξN w (exteriorDerivative (ω : DifferentialForm (Euclid P) n) w)
        ∂μHE[n + 1] :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hE (hEZ ▸ inter_subset_left) hvanish
    -- area formula for the injective immersion `G` on `F`
    _ = ∫ v in F, Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) =>
          inner ℝ (fderiv ℝ G v (EuclideanSpace.single i 1))
            (fderiv ℝ G v (EuclideanSpace.single j 1)))) *
          ξN (G v) (exteriorDerivative (ω : DifferentialForm (Euclid P) n) (G v)) :=
      Submission.codim1_lur_cd_injective_area_formula_gram P (n + 1) G F hF
        (fun v hv => (hG2.differentiableOn (by norm_num) v hv.1).differentiableAt
          (isOpen_ball.mem_nhds hv.1))
        (fun v hv => hDGinj v hv.1) (hGinj.mono inter_subset_left) _
    -- orientation `J · ξN(G)(α) = α(DG e)` and `trace DΦ = dω(G)(DG e)` on `F ⊆ D`
    _ = ∫ v in F, LinearMap.trace ℝ (Euclid (n + 1))
          (fderiv ℝ Φ v : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) := by
      refine setIntegral_congr_fun hF fun v hv => ?_
      rw [Submission.codim1_lur_cd_pullback_field_trace P n _ G _ Φ isOpen_ball hG2 hωs hΦ v hv.1]
      simp only [hDG v hv.1]
      rw [mul_comm]
      exact (hchart v hv.1).2.2.2.2 _
/-- Orientation normal form (Simon Ch. 6, 1.1 and 2.2; step 1 of the graph chart in Ch. 7, §5):
a unit orientation `ξ = ±τ₀ ∧ ⋯ ∧ τₘ` of `Q` equals `ι(e₀) ∧ ⋯ ∧ ι(eₘ)` for a linear isometry
`ι : ℝ^{m+1} → ℝᴾ` with range `Q`.  If the sign is `−`, replace `τ₀` by `−τ₀`: the family stays
orthonormal with the same span, and `α(τ') = −α(τ)` by linearity of `α` in slot `0`.  Then `ι` is
the linear map `eᵢ ↦ τ'ᵢ`; it sends the standard orthonormal basis to an orthonormal family, so it
is an isometry, and its range is `span τ' = Q`. -/
theorem Submission.codim1_rdo_gc_unitOrientation_isometry : ∀ (P m : ℕ) (ξ : MultiVector P (m + 1)) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ∃ ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid P, Set.range ι = (Q : Set (Euclid P)) ∧ ∀ α : Covector (Euclid P) (m + 1), ξ α = α (fun i => ι (EuclideanSpace.single i 1)) := by
  intro P m ξ Q ⟨τ, hτ, hspan, hsign⟩
  -- normalize the sign: an orthonormal `τ'` spanning `Q` with `ξ(α) = α(τ')`
  obtain ⟨τ', hτ', hspan', hξ'⟩ : ∃ τ' : Fin (m + 1) → Euclid P, Orthonormal ℝ τ' ∧
      Submodule.span ℝ (Set.range τ') = Q ∧ ∀ α : Covector (Euclid P) (m + 1), ξ α = α τ' := by
    rcases hsign with h | h
    · exact ⟨τ, hτ, hspan, h⟩
    · -- `τ' = update τ 0 (−τ₀)`
      refine ⟨Function.update τ 0 ((-1 : ℝ) • τ 0), ?_, ?_, ?_⟩
      · rw [orthonormal_iff_ite] at hτ ⊢
        intro i j
        rcases eq_or_ne i 0 with rfl | hi <;> rcases eq_or_ne j 0 with rfl | hj
        · simp only [Function.update_self, inner_smul_left, inner_smul_right, hτ 0 0]
          norm_num
        · simp [Function.update_of_ne hj, hτ 0 j, hj.symm]
        · simp [hτ i 0, hi]
        · simp only [Function.update_of_ne hi, Function.update_of_ne hj, hτ i j]
      · rw [← hspan]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          rcases eq_or_ne i 0 with rfl | hi
          · simp only [Function.update_self]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
          · rw [Function.update_of_ne hi]; exact Submodule.subset_span ⟨i, rfl⟩
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          rcases eq_or_ne i 0 with rfl | hi
          · have h0 : Function.update τ 0 ((-1 : ℝ) • τ 0) 0 ∈
                Submodule.span ℝ (Set.range (Function.update τ 0 ((-1 : ℝ) • τ 0))) :=
              Submodule.subset_span ⟨0, rfl⟩
            have h1 := Submodule.smul_mem _ (-1 : ℝ) h0
            simpa using h1
          · have h0 : Function.update τ 0 ((-1 : ℝ) • τ 0) i ∈
                Submodule.span ℝ (Set.range (Function.update τ 0 ((-1 : ℝ) • τ 0))) :=
              Submodule.subset_span ⟨i, rfl⟩
            rwa [Function.update_of_ne hi] at h0
      · intro α
        rw [h α, α.map_update_smul, Function.update_eq_self]
        simp
  -- `ι` is the linear map `eᵢ ↦ τ'ᵢ`, an isometry since it maps an orthonormal basis to `τ'`
  let B := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  let f : Euclid (m + 1) →ₗ[ℝ] Euclid P := B.toBasis.constr ℝ τ'
  have hfB : ∀ i, f (B i) = τ' i := fun i => by
    have := B.toBasis.constr_basis ℝ τ' i
    rwa [OrthonormalBasis.coe_toBasis] at this
  have hf : Orthonormal ℝ (f ∘ B.toBasis) := by
    convert hτ' using 1; funext i; exact hfB i
  let ι := f.isometryOfOrthonormal (v := B.toBasis) (by simp [B.orthonormal]) hf
  refine ⟨ι, ?_, ?_⟩
  · -- `range ι = span τ' = Q`
    have : Set.range ι = Set.range f := rfl
    rw [this, ← LinearMap.coe_range, ← hspan']
    congr 1
    rw [Module.Basis.constr_range]
  · -- `ξ(α) = α(τ') = α(ι e₀, …, ι eₘ)`
    intro α
    rw [hξ' α]
    congr 1
    funext i
    have : (EuclideanSpace.single i 1 : Euclid (m + 1)) = B i := by simp [B]
    rw [this]
    exact (hfB i).symm
/-- **`C²` inverse function theorem with a `C²` inverse on a neighbourhood** (graph chart of
`N ∈ 𝒪` over its tangent plane, step 4: `φ : V₀ → O` is bijective with `C²` inverse).  If
`φ : ℝᵈ → ℝᵈ` is `C²` on an open `V ∋ z₀` and `Dφ(z₀)` is injective, there are open sets `V₀`, `O`
with `z₀ ∈ V₀ ⊆ V` such that `φ : V₀ → O` is a bijection whose inverse `g` is `C²` on `O`.
`Dφ` is continuous on `V`, so `V' = {z ∈ V : Dφ(z) injective}` is open; the strict-derivative
inverse function theorem gives an open partial homeomorphism `Φ = φ` with `z₀ ∈ Φ.source`; take
`V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀` and `g = Φ.symm`, which is `C²` at every
`y ∈ O` because `Dφ(g y)` is invertible. -/
theorem Submission.codim1_rdo_gc_local_inverse_c2 : ∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 2 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (g : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 2 g O ∧ MapsTo g O V₀ ∧ (∀ y ∈ O, φ (g y) = y) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ g (φ z) = z := by
  intro d φ V z₀ hV hz₀ hφ hinj
  -- step 1: `φ` is `C²` and differentiable at every point of `V`, and `Dφ` is continuous on `V`
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV (by norm_num)
  have hdiff : ∀ z ∈ V, HasFDerivAt φ (fderiv ℝ φ z) z := fun z hz =>
    ((hφ.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  -- step 2: an injective endomorphism of `ℝᵈ` is a continuous linear equivalence
  have equivOf : ∀ L : Euclid d →L[ℝ] Euclid d, Injective L →
      ∃ E : Euclid d ≃L[ℝ] Euclid d, (E : Euclid d →L[ℝ] Euclid d) = L := by
    intro L hL
    have hsurj : Surjective L := LinearMap.injective_iff_surjective.mp hL
    exact ⟨(LinearEquiv.ofBijective (L : Euclid d →ₗ[ℝ] Euclid d)
      ⟨hL, hsurj⟩).toContinuousLinearEquiv, by ext; rfl⟩
  -- step 3: `V' = {z ∈ V : Dφ(z) injective}` is open and contains `z₀`
  set V' := V ∩ (fderiv ℝ φ) ⁻¹' {L | Injective L} with hV'eq
  have hV' : IsOpen V' := hcont.isOpen_inter_preimage hV ContinuousLinearMap.isOpen_injective
  have hz₀' : z₀ ∈ V' := ⟨hz₀, hinj⟩
  -- step 4: the inverse function theorem at `z₀` gives `Φ = φ` with `z₀ ∈ Φ.source`
  obtain ⟨E₀, hE₀⟩ := equivOf _ hinj
  have hstrict : HasStrictFDerivAt φ (E₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hE₀]; exact (hφ.contDiffAt (hV.mem_nhds hz₀)).hasStrictFDerivAt (by norm_num)
  set Φ := hstrict.toOpenPartialHomeomorph φ with hΦeq
  have hΦcoe : ∀ z, Φ z = φ z := fun z => rfl
  -- steps 5–6: `V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀`, `g = Φ.symm`; for `y ∈ O`,
  -- `g y ∈ V₀` and `φ (g y) = y`
  have hV₀ : IsOpen (Φ.source ∩ V') := Φ.open_source.inter hV'
  refine ⟨Φ.source ∩ V', Φ.target ∩ Φ.symm ⁻¹' (Φ.source ∩ V'), Φ.symm, hV₀,
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hV₀,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀'⟩, fun z hz => hz.2.1, ?_,
    fun y hy => hy.2, fun y hy => by rw [← hΦcoe]; exact Φ.right_inv hy.1, fun z hz => ?_⟩
  -- step 7: `g` is `C²` at every `y ∈ O`, since `Dφ(g y)` is invertible
  · intro y hy
    have hz : Φ.symm y ∈ V' := hy.2.2
    obtain ⟨E, hE⟩ := equivOf _ hz.2
    apply ContDiffAt.contDiffWithinAt
    apply Φ.contDiffAt_symm hy.1
    · rw [hE]; exact hdiff _ hz.1
    · exact hφ.contDiffAt (hV.mem_nhds hz.1)
  -- step 6(b): for `z ∈ V₀`, `φ z ∈ O` and `g (φ z) = z`
  · have h1 : Φ.symm (Φ z) = z := Φ.left_inv hz.1
    rw [← hΦcoe]
    exact ⟨⟨Φ.map_source hz.1, by rw [Set.mem_preimage, h1]; exact hz⟩, h1⟩
/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm

/-- **Chart lemma** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ` be a chart of `N` as in
`IsEmbeddedSubmanifold`: `Cʳ` (`r ≥ 1`) and injective on the open `V`, `ψ(V) = W ∩ N`, proper,
with `Dψ` injective on `V`.  For `v ∈ V`, `q = ψ(v)` and `A = Dψ(v)`: (i) `T_qN = A(ℝᵈ)`;
(ii) `ψ⁻¹` is continuous at `q`; (iii) every `y ∈ N` near `q` has `|y − q − Aa| ≤ ε|y − q|` for
some `a`.  (ii) is `dsmc_chart_inverse_continuity` (properness and injectivity), (iii) is
`dsmc_chart_secant_estimate` (differentiability at `v`, injectivity of `A` and (ii)), and (i)
combines `dsmc_tangentSpace_subset_range_of_secant` (by (iii), curve velocities lie in the closed
subspace `A(ℝᵈ)`) with `dsmc_chart_range_subset_tangentSpace` (the curves `t ↦ ψ(v + h(t)a)`). -/
theorem Submission.dsmc_chart_tangentSpace_eq_range : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → ∀ v ∈ V, tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - fderiv ℝ ψ v a‖ ≤ ε * ‖y - ψ v‖) := by
  intro P r d N V W ψ hr hV hW hψ hinj himg hprop hDψ v hv
  -- (ii): properness and injectivity of `ψ` on `V` make `ψ⁻¹` continuous at `ψ v`
  have hii : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε :=
    Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj
      (himg.subset.trans inter_subset_left) hprop v hv
  -- `ψ` is `C¹` on the open set `V ∋ v`, so `A = fderiv ℝ ψ v` is its derivative at `v`
  have hA : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    (hψ.differentiableOn (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr)).hasFDerivAt
      (hV.mem_nhds hv)
  -- (iii): the secant estimate at `ψ v`, from `hA`, injectivity of `A` and (ii)
  have hiii := Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW himg hv hA
    (hDψ v hv) hii
  -- (i): `T_{ψ v}N ⊆ A(ℝᵈ)` by (iii); `A(ℝᵈ) ⊆ T_{ψ v}N` since `ψ '' V ⊆ N`
  exact ⟨Set.Subset.antisymm
      (Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v) hiii)
      (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ
        (himg.subset.trans inter_subset_right) v hv),
    hii, hiii⟩

/-- **Graph over the tangent plane** (Simon Ch. 2, §4).  Let `N` be an embedded `C²`
`d`-submanifold, `x ∈ N ∩ U` with `U` open, and `ι : ℝᵈ → ℝᴾ` a linear isometry onto `T_xN`.
Then `B̄_{δ₁+δ₂}(x) ⊆ U` and over `B_{δ₁}(0)` the set `N` is the graph `v ↦ x + ιv + u(v)` of a
`C²` map `u ⊥ ι(ℝᵈ)` with `u(0) = 0`, `Du(0) = 0`, `‖Du‖ ≤ 1` and `‖u‖ < δ₂/2`; a point
`x + ιv + h ∈ N` with `|v| < δ₁`, `|h| < δ₂` and `h ⊥ ι(ℝᵈ)` has `h = u(v)`.
For a chart `ψ` with `ψ(z₀) = x`, `Dψ(z₀)(ℝᵈ) = T_xN = ι(ℝᵈ)` and `ψ⁻¹` is continuous at `x`
(`dsmc_chart_tangentSpace_eq_range`), so `φ = ι*(ψ − x)` has injective derivative `ι*Dψ(z₀)` at
`z₀` and a `C²` local inverse `g : O → V₀` (`codim1_rdo_gc_local_inverse_c2`).  Put
`u(v) = ψ(g(v)) − x − ιv`.  Then `ι*u = 0` on `O`, and `Du(0)` maps into `ι(ℝᵈ)` and is orthogonal
to it, so `Du(0) = 0`.  Near `x`, `N` lies in `ψ(V₀)`, and `x + ιv + h = ψ(z)` gives `φ(z) = v`,
so `z = g(v)` and `h = u(v)`. -/
theorem Submission.codim1_rdo_gc_graph_over_tangent : ∀ (P d : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (ι : Euclid d →ₗᵢ[ℝ] Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → x ∈ N ∩ U → Set.range ι = tangentSpace N x → ∃ (u : Euclid d → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, (∀ w : Euclid d, inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N) ∧ ∀ (v : Euclid d) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid d, inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v := by
  intro P d U N x ι hU hN hx hι
  -- a chart `ψ` with `ψ(z₀) = x`: `Dψ(z₀)(ℝᵈ) = T_xN = ι(ℝᵈ)` and `ψ⁻¹` is continuous at `x`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hψinj, hψimg, hprop, hDψ⟩ := hN x hx.1
  obtain ⟨z₀, hz₀V, hψz₀⟩ : x ∈ ψ '' V := by rw [hψimg]; exact ⟨hxW, hx.1⟩
  obtain ⟨htan, hinvc, -⟩ := Submission.dsmc_chart_tangentSpace_eq_range P 2 d N V W ψ
    (by norm_num) hV hW hψ hψinj hψimg hprop hDψ z₀ hz₀V
  rw [hψz₀] at htan hinvc
  have hrangeψ : Set.range (fderiv ℝ ψ z₀) = Set.range ι := by rw [← htan, hι]
  have hψ2 : ContDiffOn ℝ 2 ψ V := by exact_mod_cast hψ
  -- the adjoint `ι*`: `⟨ιw, h⟩ = ⟨w, ι*h⟩`, `ι*ι = 1`, and `ι*h = 0` if `h ⊥ ι(ℝᵈ)`
  set ιs : Euclid P →L[ℝ] Euclid d := ι.toContinuousLinearMap.adjoint with hιs
  have hadj : ∀ w h, inner ℝ (ι w) h = inner ℝ w (ιs h) := fun w h => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_right]; rfl
  have hιsι : ∀ w, ιs (ι w) = w := by
    intro w
    apply ext_inner_left ℝ
    intro w'
    rw [← hadj, LinearIsometry.inner_map_map]
  have hιs0 : ∀ h, (∀ w, inner ℝ (ι w) h = 0) → ιs h = 0 := by
    intro h hh
    apply ext_inner_left ℝ
    intro w
    rw [← hadj, hh w, inner_zero_right]
  -- `φ = ι*(ψ − x)` is `C²` on `V`, with injective derivative `ι*Dψ(z₀)` at `z₀`
  have hψdiff : ∀ z ∈ V, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz =>
    ((hψ2.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  let φ : Euclid d → Euclid d := fun z => ιs (ψ z - x)
  have hφ : ContDiffOn ℝ 2 φ V := ιs.contDiff.comp_contDiffOn (hψ2.sub contDiffOn_const)
  have hφderiv : HasFDerivAt φ (ιs.comp (fderiv ℝ ψ z₀)) z₀ :=
    ιs.hasFDerivAt.comp z₀ ((hψdiff z₀ hz₀V).sub_const x)
  have hφinj : Injective (fderiv ℝ φ z₀) := by
    rw [hφderiv.fderiv]
    intro a₁ a₂ h
    have h1 : ιs (fderiv ℝ ψ z₀ (a₁ - a₂)) = 0 := by
      have h' : ιs (fderiv ℝ ψ z₀ a₁) = ιs (fderiv ℝ ψ z₀ a₂) := h
      rw [map_sub, map_sub, h', sub_self]
    obtain ⟨w, hw⟩ : fderiv ℝ ψ z₀ (a₁ - a₂) ∈ Set.range ι := hrangeψ ▸ ⟨a₁ - a₂, rfl⟩
    rw [← hw, hιsι] at h1
    have h2 : fderiv ℝ ψ z₀ (a₁ - a₂) = fderiv ℝ ψ z₀ 0 := by rw [← hw, h1, map_zero, map_zero]
    exact sub_eq_zero.mp (hDψ z₀ hz₀V h2)
  -- the `C²` local inverse `g : O → V₀` of `φ`; `φ(z₀) = 0`, so `0 ∈ O` and `g(0) = z₀`
  obtain ⟨V₀, O, g, hV₀, hO, hz₀V₀, hV₀V, hg, hgmaps, hφg, hgφ⟩ :=
    Submission.codim1_rdo_gc_local_inverse_c2 d φ V z₀ hV hz₀V hφ hφinj
  have hφz₀ : φ z₀ = 0 := by simp [φ, hψz₀]
  obtain ⟨h0O, hg0⟩ := hgφ z₀ hz₀V₀
  rw [hφz₀] at h0O hg0
  -- the graph map `u(v) = ψ(g(v)) − x − ιv`: on `O` it is `C²`, `ι*u = 0` and `x + ιv + u(v) ∈ N`
  let u : Euclid d → Euclid P := fun v => ψ (g v) - x - ι v
  have hGu : ∀ v, x + ι v + u v = ψ (g v) := fun v => by simp only [u]; abel
  have hu0 : u 0 = 0 := by simp [u, hg0, hψz₀]
  have hgV : MapsTo g O V := fun y hy => hV₀V (hgmaps hy)
  have huC2 : ContDiffOn ℝ 2 u O :=
    ((hψ2.comp hg hgV).sub contDiffOn_const).sub ι.toContinuousLinearMap.contDiff.contDiffOn
  have hιsu : ∀ v ∈ O, ιs (u v) = 0 := by
    intro v hv
    have h1 : ιs (ψ (g v) - x) = v := hφg v hv
    simp only [u, map_sub, hιsι]
    rw [← map_sub, h1, sub_self]
  have horthO : ∀ v ∈ O, ∀ w, inner ℝ (ι w) (u v) = 0 := by
    intro v hv w
    rw [hadj, hιsu v hv, inner_zero_right]
  have hmemO : ∀ v ∈ O, x + ι v + u v ∈ N := fun v hv => by
    rw [hGu]
    have h1 : ψ (g v) ∈ ψ '' V := ⟨g v, hgV hv, rfl⟩
    rw [hψimg] at h1
    exact h1.2
  have hudiff : ∀ v ∈ O, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((huC2.contDiffAt (hO.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  -- `Du(0) = 0`: every `Du(0)c` lies in `ι(ℝᵈ)` and is orthogonal to `ι(ℝᵈ)`
  have hDu0 : fderiv ℝ u 0 = 0 := by
    have hgdiff : HasFDerivAt g (fderiv ℝ g 0) 0 :=
      ((hg.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by norm_num)).hasFDerivAt
    have hψg : HasFDerivAt (fun v => ψ (g v)) ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0)) 0 := by
      have h' : HasFDerivAt ψ (fderiv ℝ ψ z₀) (g 0) := by rw [hg0]; exact hψdiff z₀ hz₀V
      exact h'.comp 0 hgdiff
    have huder : HasFDerivAt u ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0) - ι.toContinuousLinearMap) 0 :=
      (hψg.sub_const x).sub ι.toContinuousLinearMap.hasFDerivAt
    ext1 c
    -- `⟨ιw, Du(0)c⟩ = 0`: differentiate `⟨ιw, u⟩ = 0` on the neighbourhood `O` of `0`
    have horthD : ∀ w, inner ℝ (ι w) (fderiv ℝ u 0 c) = 0 := by
      intro w
      have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hO.mem_nhds h0O) (fun v' hv' => horthO v' hv' w)
      have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
          ((innerSL ℝ (ι w)).comp (fderiv ℝ u 0)) 0 :=
        (innerSL ℝ (ι w)).hasFDerivAt.comp 0 (hudiff 0 h0O)
      have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid d →L[ℝ] ℝ) 0 :=
        (hasFDerivAt_const (0 : ℝ) 0).congr_of_eventuallyEq hloc
      have h2 := congrArg (fun L => L c) (hd.unique hd0)
      simpa using h2
    -- `Du(0)c = Dψ(z₀)(Dg(0)c) − ιc = ι(w₁ − c)` with `Dψ(z₀)(Dg(0)c) = ιw₁`
    obtain ⟨w₁, hw₁⟩ : fderiv ℝ ψ z₀ (fderiv ℝ g 0 c) ∈ Set.range ι :=
      hrangeψ ▸ ⟨fderiv ℝ g 0 c, rfl⟩
    have hDuc : fderiv ℝ u 0 c = ι (w₁ - c) := by
      rw [huder.fderiv, map_sub]
      simp [hw₁]
    have h3 := horthD (w₁ - c)
    rw [← hDuc, real_inner_self_eq_norm_sq] at h3
    simpa using h3
  -- `N ∩ B_s(x) ⊆ ψ(V₀)`, by continuity of `ψ⁻¹` at `x`; also `B_s(x) ⊆ W ∩ U`
  obtain ⟨ε, hε, hballV₀⟩ := Metric.isOpen_iff.mp hV₀ z₀ hz₀V₀
  obtain ⟨δC, hδC, hδCprop⟩ := hinvc ε hε
  obtain ⟨ρW, hρW, hballW⟩ := Metric.isOpen_iff.mp hW x hxW
  obtain ⟨ρU, hρU, hballU⟩ := Metric.isOpen_iff.mp hU x hx.2
  set s := min (min ρW δC) ρU with hs
  have hspos : 0 < s := lt_min (lt_min hρW hδC) hρU
  have hNball : ∀ q ∈ N, dist q x < s → ∃ z ∈ V₀, ψ z = q := by
    intro q hq hqx
    have hqW : q ∈ W :=
      hballW (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_left _ _)))
    obtain ⟨z, hzV, rfl⟩ : q ∈ ψ '' V := by rw [hψimg]; exact ⟨hqW, hq⟩
    have h1 := hδCprop z hzV (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_right _ _)))
    exact ⟨z, hballV₀ h1, rfl⟩
  -- `δ₂ = s/4`, and `δ₁ ≤ δ₂` so small that `B_{δ₁}(0) ⊆ O`, `‖u‖ < δ₂/2`, `‖Du‖ < 1` there
  set r₁ := s / 4 with hr₁eq
  have hr₁ : 0 < r₁ := by positivity
  have hucont : ContinuousAt u 0 := huC2.continuousOn.continuousAt (hO.mem_nhds h0O)
  have hDucont : ContinuousAt (fderiv ℝ u) 0 :=
    (huC2.continuousOn_fderiv_of_isOpen hO (by norm_num)).continuousAt (hO.mem_nhds h0O)
  obtain ⟨ρ₁, hρ₁, hρ₁prop⟩ := Metric.continuousAt_iff.mp hucont (r₁ / 2) (by positivity)
  obtain ⟨ρ₂, hρ₂, hρ₂prop⟩ := Metric.continuousAt_iff.mp hDucont 1 one_pos
  obtain ⟨ρ₃, hρ₃, hρ₃O⟩ := Metric.isOpen_iff.mp hO 0 h0O
  set δ₁ := min (min (min ρ₁ ρ₂) ρ₃) r₁ with hδ₁eq
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min (lt_min hρ₁ hρ₂) hρ₃) hr₁
  have hδ₁ρ₁ : δ₁ ≤ ρ₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁ρ₂ : δ₁ ≤ ρ₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁ρ₃ : δ₁ ≤ ρ₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₁r₁ : δ₁ ≤ r₁ := min_le_right _ _
  have hballO : ball (0 : Euclid d) δ₁ ⊆ O := (ball_subset_ball hδ₁ρ₃).trans hρ₃O
  refine ⟨u, δ₁, r₁, hδ₁pos, hr₁, ?_, hu0, hDu0, huC2.mono hballO, ?_, ?_⟩
  · -- `B̄_{δ₁+δ₂}(x) ⊆ B_s(x) ⊆ U`
    intro q hq
    apply hballU
    rw [mem_closedBall] at hq
    rw [mem_ball]
    have : s ≤ ρU := min_le_right _ _
    linarith
  · intro v hv
    have hvO := hballO hv
    have hv0 : dist v 0 < δ₁ := hv
    refine ⟨horthO v hvO, ?_, ?_, hmemO v hvO⟩
    · have h1 := hρ₂prop (lt_of_lt_of_le hv0 hδ₁ρ₂)
      rw [hDu0, dist_zero_right] at h1
      exact h1.le
    · have h1 := hρ₁prop (lt_of_lt_of_le hv0 hδ₁ρ₁)
      rw [hu0, dist_zero_right] at h1
      exact h1
  · -- uniqueness: `q = x + ιv + h ∈ N ∩ B_s(x)` is `ψ(z)` with `z ∈ V₀` and `φ(z) = v`, so
    -- `z = g(v)` and `x + ιv + u(v) = ψ(g(v)) = q`
    intro v h hv hh horthh hq
    have hvO : v ∈ O := hballO (by rw [mem_ball, dist_zero_right]; exact hv)
    have hqx : dist (x + ι v + h) x < s := by
      rw [dist_eq_norm, show x + ι v + h - x = ι v + h by abel]
      calc ‖ι v + h‖ ≤ ‖ι v‖ + ‖h‖ := norm_add_le _ _
        _ = ‖v‖ + ‖h‖ := by rw [LinearIsometry.norm_map]
        _ < δ₁ + r₁ := add_lt_add hv hh
        _ ≤ r₁ + r₁ := by linarith
        _ < s := by rw [hr₁eq]; linarith
    obtain ⟨z, hzV₀, hψz⟩ := hNball _ hq hqx
    have hφz : φ z = v := by
      show ιs (ψ z - x) = v
      rw [hψz, show x + ι v + h - x = ι v + h by abel, map_add, hιsι, hιs0 h horthh, add_zero]
    have hgz : g v = z := by rw [← hφz]; exact (hgφ z hzV₀).2
    have h1 := hGu v
    rw [hgz, hψz] at h1
    exact (add_left_cancel h1).symm
/-- Steps 3–5 of the orientation push-forward (Simon 6.3.4–3.5, with the orthonormal basis of
`span v` chosen by Gram–Schmidt): a linearly independent family `v` in `ℝᴾ` has an orthonormal
frame `σ` with the same span such that `A = (⟨σᵢ, vⱼ⟩)` satisfies `det(⟨vᵢ, vⱼ⟩) = (det A)²`,
`det A ≠ 0` and `|det A| ≤ ∏ᵢ |vᵢ|`.  Gram–Schmidt in `W = span v` makes `A` the upper-triangular
matrix of `v` in an orthonormal basis of `W`, and Parseval gives `(⟨vᵢ, vⱼ⟩) = AᵀA`. -/
theorem Submission.dpf_exists_orthonormal_frame_det_gram : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Submodule.span ℝ (Set.range v) ∧ Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ^ 2 ∧ Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ≠ 0 ∧ |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| ≤ ∏ i, ‖v i‖ := by
  intro P n v hv
  set W := Submodule.span ℝ (Set.range v)
  -- `v` regarded in `W` is a linearly independent spanning family `w`
  let w : Fin n → W := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp W.subtype hv
  have hspan_w : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  -- the Gram–Schmidt orthonormal basis `b` of `W`, and `σ = b` regarded in `ℝᴾ`
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  -- `A` is the (upper-triangular) matrix of `w` in the basis `b`
  have hA : (Matrix.of fun i j => inner ℝ (σ i) (v j)) = b.toBasis.toMatrix w := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, Submodule.coe_inner]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) =
      ∏ i, inner ℝ (σ i) (v i) := by
    rw [hA, ← Module.Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    rfl
  refine ⟨σ, b.orthonormal.comp_linearIsometry W.subtypeₗᵢ, ?_, ?_, ?_, ?_⟩
  · -- `span σ = W`
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
    have hσ : Set.range σ = W.subtype '' Set.range b := Set.range_comp _ _
    rw [hσ, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
  · -- Parseval: `(⟨vᵢ, vⱼ⟩) = AᵀA`
    have hG : (Matrix.of fun i j => inner ℝ (v i) (v j)) =
        Matrix.transpose (Matrix.of fun i j => inner ℝ (σ i) (v j)) *
          Matrix.of fun i j => inner ℝ (σ i) (v j) := by
      ext i j
      have hp := b.sum_inner_mul_inner (w i) (w j)
      simp only [Submodule.coe_inner] at hp
      rw [Matrix.mul_apply, Matrix.of_apply, ← hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, real_inner_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  · -- `det A = det_b w` is a unit
    rw [hA, ← Module.Basis.det_apply]
    exact ((Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩).ne_zero
  · -- Cauchy–Schwarz on the diagonal entries
    rw [hdet, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |inner ℝ (σ i) (v i)| ≤ ‖σ i‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖v i‖ := by rw [show ‖σ i‖ = 1 from b.norm_eq_one i, one_mul]
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

/-- Step (6c) of the graph chart in the codimension-one regularity theorem (Simon 7.5.8; unit
orientations as in Simon 6.2.2): for linearly independent `b₁, …, bₘ` in `ℝᴾ` the Gram determinant
`Γ = det(⟨bᵢ, bⱼ⟩)` is positive, and an `m`-vector `ξ` with `⟨α, ξ⟩ √Γ = α(b₁, …, bₘ)` for every
`m`-covector `α` is a unit orientation of `span b`.  For the Gram–Schmidt frame `σ` of `span b` and
`A = (⟨σᵢ, bⱼ⟩)`, `Γ = (det A)²`, `√Γ = |det A|` and `α(b) = det A · α(σ)`, so
`ξ = ±σ₁ ∧ ⋯ ∧ σₘ`. -/
theorem Submission.codim1_rdo_gc_gram_unitOrientation : ∀ (P m : ℕ) (b : Fin m → Euclid P), LinearIndependent ℝ b → 0 < Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)) ∧ ∀ ξ : MultiVector P m, (∀ α : Covector (Euclid P) m, ξ α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j))) = α b) → IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range b)) := by
  intro P m b hb
  obtain ⟨σ, hσ, hspan, hgram, hA, -⟩ := Submission.dpf_exists_orthonormal_frame_det_gram P m b hb
  set A := Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (b j)) with hAeq
  have hpos : 0 < Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)) := by
    rw [hgram]; positivity
  refine ⟨hpos, fun ξ hξ => ?_⟩
  have hmem : ∀ j, b j ∈ Submodule.span ℝ (Set.range σ) := fun j => by
    rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcov := Submission.dgoj_covector_eq_det_mul_of_mem_span P m σ b hσ hmem
  have hsqrt : Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j))) = |A| := by
    rw [hgram, Real.sqrt_sq_eq_abs]
  refine ⟨σ, hσ, hspan, ?_⟩
  rcases lt_or_gt_of_ne hA with hneg | hpos'
  · right
    intro α
    have h1 := hξ α
    rw [hsqrt, abs_of_neg hneg, hcov α] at h1
    have h2 : A * ξ α = A * (-α σ) := by linarith
    exact mul_left_cancel₀ hA h2
  · left
    intro α
    have h1 := hξ α
    rw [hsqrt, abs_of_pos hpos', hcov α] at h1
    have h2 : A * ξ α = A * α σ := by linarith
    exact mul_left_cancel₀ hA h2
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
/-- **Gauss–Green measure** (Simon Ch. 2, 2.1–2.2 and Ch. 3, 4.1, with the Riesz representation
Ch. 1, 4.14): if `φ ↦ ∫_F div φ` is bounded on smooth fields with `|φ| ≤ 1` supported in each
compact `K ⊆ D`, it is `φ ↦ -∫ ⟨φ, ν⟩ dμ` on `C¹` fields compactly supported in `D`, for a measure
`μ` carried by `D`, finite on its compact subsets, and a Borel unit field `ν`.  For each coordinate
`i`, `g ↦ ±∫_F div (g eᵢ)` has positive part `f ↦ sup {±∫_F div (g eᵢ) : g smooth, 0 ≤ g ≤ f}` on
`C_c(D, ℝ≥0)` (additive by smooth approximation under a continuous ceiling), represented by
Riesz–Markov–Kakutani on the open subspace `D`; the `2(m + 1)` measures are densities against their
sum (Lebesgue decomposition), the density field is normalized and the measure pushed forward to
`ℝ^{m+1}`; `C¹` fields are reached by mollification. -/
theorem Submission.codim1_rdo_dg_gauss_green_measure : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))), IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
  intro m D F hD hF hbound
  classical
  -- the trace as a continuous linear functional and the functional `T φ = ∫_F div φ`
  obtain ⟨trc, htrc⟩ : ∃ trc : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ, ∀ A,
      trc A = LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ)), fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (Euclid (m + 1) → Euclid (m + 1)) → ℝ,
      ∀ φ, T φ = ∫ y in F, trc (fderiv ℝ φ y) := ⟨_, fun _ => rfl⟩
  have hTeq : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = T φ := by
    intro φ
    rw [hT]
    simp only [htrc]
  have hbound' : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ,
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → T φ ≤ C := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound K hK hKD
    refine ⟨C, fun φ h1 h2 h3 h4 => ?_⟩
    rw [← hTeq φ]
    exact hC φ h1 h2 h3 h4
  suffices H : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ by
    obtain ⟨μ, ν, h1, h2, h3, h4, h5⟩ := H
    exact ⟨μ, ν, h1, h2, h3, h4, fun φ hφ hφc hφD => (hTeq φ).trans (h5 φ hφ hφc hφD)⟩
  -- Step 1: `T` is linear on `C¹` compactly supported fields, and locally bounded
  have hdiv_int : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      Integrable (fun y => trc (fderiv ℝ φ y)) (volume.restrict F) := fun φ hφ hc =>
    ((trc.continuous.comp (hφ.continuous_fderiv one_ne_zero)).integrable_of_hasCompactSupport
      ((hc.fderiv ℝ).comp_left trc.map_zero)).restrict
  have hT_add : ∀ φ ψ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → T (φ + ψ) = T φ + T ψ := by
    intro φ ψ hφ hφc hψ hψc
    simp only [hT]
    rw [← integral_add (hdiv_int φ hφ hφc) (hdiv_int ψ hψ hψc)]
    congr 1; ext y
    rw [fderiv_add (hφ.differentiable one_ne_zero y) (hψ.differentiable one_ne_zero y), map_add]
  have hT_smul : ∀ (c : ℝ) (φ : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 φ →
      T (c • φ) = c * T φ := by
    intro c φ hφ
    simp only [hT]
    rw [← integral_const_mul]
    congr 1; ext y
    rw [fderiv_const_smul (hφ.differentiable one_ne_zero y),
      map_smul, smul_eq_mul]
  have hT0 : T 0 = 0 := by simp [hT]
  have hbd : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → ∀ M : ℝ, 0 ≤ M → (∀ y, ‖φ y‖ ≤ M) → |T φ| ≤ C * M := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound' K hK hKD
    have hC0 : 0 ≤ C := by
      simpa [hT0] using hC 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
    refine ⟨C, hC0, fun φ hφ hφc hφK M hM hφM => ?_⟩
    rcases hM.eq_or_lt with rfl | hMpos
    · have : φ = 0 := funext fun y => norm_le_zero_iff.1 (hφM y)
      simp [this, hT0]
    · have hsm : ContDiff ℝ (⊤ : ℕ∞) (M⁻¹ • φ) := contDiff_const.smul hφ
      have hsK : tsupport (M⁻¹ • φ) ⊆ K :=
        (tsupport_smul_subset_right (fun _ => M⁻¹) φ).trans hφK
      have hsn : ∀ y, ‖(M⁻¹ • φ) y‖ ≤ 1 := fun y => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM)]
        calc M⁻¹ * ‖φ y‖ ≤ M⁻¹ * M := by gcongr; exact hφM y
          _ = 1 := inv_mul_cancel₀ hMpos.ne'
      have h1 := hC _ hsm (hφc.smul_left) hsK hsn
      have h2 := hC (-(M⁻¹ • φ)) hsm.neg (hφc.smul_left).neg (by rwa [tsupport_neg]) (fun y => by
        rw [Pi.neg_apply, norm_neg]; exact hsn y)
      rw [hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h1
      rw [show -(M⁻¹ • φ) = (-M⁻¹) • φ by rw [neg_smul],
        hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h2
      rw [abs_le]
      constructor
      · have := mul_le_mul_of_nonneg_left h2 hM
        rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
      · have := mul_le_mul_of_nonneg_left h1 hM
        rw [← mul_assoc, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
  -- compact subsets of `D` and compact supports on the subtype `D`
  have hsubK : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D →
      IsCompact (Subtype.val ⁻¹' K : Set D) := fun K hK hKD =>
    Subtype.isCompact_iff.2 (by rwa [Subtype.image_preimage_coe, inter_eq_right.2 hKD])
  have hcs : ∀ (h : Euclid (m + 1) → ℝ) (K : Set (Euclid (m + 1))), IsCompact K →
      support h ⊆ K → HasCompactSupport h ∧ tsupport h ⊆ K := fun h K hK hhK =>
    ⟨hK.of_isClosed_subset (isClosed_tsupport h) (closure_minimal hhK hK.isClosed),
      closure_minimal hhK hK.isClosed⟩
  -- smooth approximation of `a` under a continuous ceiling `u` (smooth partitions of unity)
  have happrox : ∀ (u a : Euclid (m + 1) → ℝ), Continuous u → Continuous a →
      (∀ z, 0 ≤ a z ∧ a z ≤ u z) → ∀ ε : ℝ, 0 < ε →
      ∃ a' : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a' ∧
        ∀ z, 0 ≤ a' z ∧ a' z ≤ u z ∧ |a' z - a z| < ε := by
    intro u a hu ha hau ε hε
    have hloc : ∀ y : Euclid (m + 1), ∃ c : ℝ, ∀ᶠ z in 𝓝 y, c ∈ Icc 0 (u z) ∩ ball (a z) ε := by
      intro y
      refine ⟨max 0 (a y - ε / 2), ?_⟩
      have h1 : ∀ᶠ z in 𝓝 y, |a z - a y| < ε / 2 := by
        have := (ha.tendsto y).eventually (ball_mem_nhds (a y) (half_pos hε))
        filter_upwards [this] with z hz
        simpa [Real.dist_eq] using hz
      have h2 : ∀ᶠ z in 𝓝 y, max 0 (a y - ε / 2) ≤ u z := by
        by_cases hay : a y - ε / 2 ≤ 0
        · exact Eventually.of_forall fun z => by
            rw [max_eq_left hay]; exact (hau z).1.trans (hau z).2
        · rw [not_le] at hay
          have hlt : a y - ε / 2 < u y := by linarith [(hau y).2]
          have := (hu.tendsto y).eventually (lt_mem_nhds hlt)
          filter_upwards [this] with z hz
          rw [max_eq_right hay.le]; exact hz.le
      filter_upwards [h1, h2] with z hz1 hz2
      refine ⟨⟨le_max_left _ _, hz2⟩, ?_⟩
      rw [mem_ball, Real.dist_eq]
      have : |max 0 (a y - ε / 2) - a y| ≤ ε / 2 := by
        rcases le_total (a y - ε / 2) 0 with h | h
        · rw [max_eq_left h, zero_sub, abs_neg, abs_of_nonneg (hau y).1]; linarith
        · rw [max_eq_right h]; rw [show a y - ε / 2 - a y = -(ε / 2) by ring, abs_neg,
            abs_of_pos (half_pos hε)]
      calc |max 0 (a y - ε / 2) - a z| ≤ |max 0 (a y - ε / 2) - a y| + |a y - a z| :=
            abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by
          have : |a y - a z| < ε / 2 := by rw [abs_sub_comm]; exact hz1
          linarith
        _ = ε := by ring
    obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
      (modelWithCornersSelf ℝ (Euclid (m + 1))) (n := ⊤)
      (t := fun z => Icc 0 (u z) ∩ ball (a z) ε)
      (fun z => (convex_Icc _ _).inter (convex_ball _ _)) hloc
    refine ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z => ?_⟩
    have := hg z
    simp only [mem_inter_iff, mem_Icc, mem_ball, Real.dist_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- Step 2: the positive part of a locally bounded functional, via Riesz–Markov–Kakutani on `D`
  have hpos : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ : Measure D, IsFiniteMeasureOnCompacts μ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → (∀ y, 0 ≤ g y) →
          BddAbove (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) ∧
          ∫ x : D, g x ∂μ = sSup (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) := by
    intro S hSadd hSsmul hSbd
    have hS0 : S 0 = 0 := by simpa using hSsmul 0 0 contDiff_const
    -- `A u`: smooth `h`, `0 ≤ h ≤ u`, compactly supported in `D`; the functional is `sup S(A u)`
    obtain ⟨A, hA⟩ : ∃ A : (Euclid (m + 1) → ℝ) → Set (Euclid (m + 1) → ℝ), ∀ u h, h ∈ A u ↔
        (ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
          ∀ y, 0 ≤ h y ∧ h y ≤ u y) :=
      ⟨fun u => {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ u y}, fun _ _ => Iff.rfl⟩
    have hA0 : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → (0 : Euclid (m + 1) → ℝ) ∈ A u :=
      fun u hu => (hA u 0).2 ⟨contDiff_const, HasCompactSupport.zero, by simp,
        fun y => ⟨le_rfl, hu y⟩⟩
    have hAsupp : ∀ u h, h ∈ A u → support h ⊆ support u := by
      intro u h hh y hy huy
      obtain ⟨-, -, -, h4⟩ := (hA u h).1 hh
      have := h4 y
      rw [huy] at this
      exact hy (le_antisymm this.2 this.1)
    have hbddA : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → BddAbove (S '' A u) := by
      intro u hu hu0 K hK hKD huK
      obtain ⟨C, hC⟩ := hSbd K hK hKD
      obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support (hcs u K hK huK).1
      refine ⟨C * M, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨h1, h2, -, h4⟩ := (hA u h).1 hh
      refine hC h h1 h2 (hcs h K hK ((hAsupp u h hh).trans huK)).2 M
        ((norm_nonneg _).trans (hM 0)) fun y => ?_
      rw [abs_of_nonneg (h4 y).1]
      exact (h4 y).2.trans ((le_abs_self _).trans (hM y))
    have hle_sup : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ h ∈ A u, S h ≤ sSup (S '' A u) :=
      fun u hu hu0 K hK hKD huK h hh => le_csSup (hbddA u hu hu0 K hK hKD huK) ⟨h, hh, rfl⟩
    have hsup_le : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → ∀ c : ℝ,
        (∀ h ∈ A u, S h ≤ c) → sSup (S '' A u) ≤ c := fun u hu c hc =>
      csSup_le ⟨S 0, 0, hA0 u hu, rfl⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
    -- additivity
    have hadd : ∀ u₁ u₂ : Euclid (m + 1) → ℝ, Continuous u₁ → (∀ y, 0 ≤ u₁ y) →
        Continuous u₂ → (∀ y, 0 ≤ u₂ y) → ∀ K₁ K₂, IsCompact K₁ → K₁ ⊆ D → support u₁ ⊆ K₁ →
        IsCompact K₂ → K₂ ⊆ D → support u₂ ⊆ K₂ →
        sSup (S '' A (u₁ + u₂)) = sSup (S '' A u₁) + sSup (S '' A u₂) := by
      intro u₁ u₂ hu₁ hu₁0 hu₂ hu₂0 K₁ K₂ hK₁ hK₁D hu₁K hK₂ hK₂D hu₂K
      have hu0 : ∀ y, 0 ≤ (u₁ + u₂) y := fun y => add_nonneg (hu₁0 y) (hu₂0 y)
      have huK : support (u₁ + u₂) ⊆ K₁ ∪ K₂ := fun y hy => by
        by_contra hy'
        apply hy
        have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
        have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
        rw [Pi.add_apply, notMem_support.1 (fun h => hy1 (hu₁K h)),
          notMem_support.1 (fun h => hy2 (hu₂K h)), add_zero]
      have hKK : IsCompact (K₁ ∪ K₂) := hK₁.union hK₂
      have hKKD : K₁ ∪ K₂ ⊆ D := union_subset hK₁D hK₂D
      apply le_antisymm
      · apply hsup_le (u₁ + u₂) hu0
        intro g hg
        obtain ⟨hg1, hg2, hg3, hg4⟩ := (hA (u₁ + u₂) g).1 hg
        obtain ⟨C, hC⟩ := hSbd (K₁ ∪ K₂) hKK hKKD
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨δ, hδ0, hCδ⟩ : ∃ δ : ℝ, 0 < δ ∧ C * (2 * δ) ≤ ε := by
          refine ⟨ε / (2 * (|C| + 1)), div_pos hε (by positivity), ?_⟩
          have hpos' : (0 : ℝ) < |C| + 1 := by positivity
          have : C * (2 * (ε / (2 * (|C| + 1)))) = C * ε / (|C| + 1) := by
            field_simp
          rw [this, div_le_iff₀ hpos', mul_comm ε]
          exact mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right
            zero_le_one)) hε.le
        have ha : Continuous fun y => min (g y) (u₁ y) := hg1.continuous.min hu₁
        obtain ⟨a', ha'1, ha'2⟩ := happrox u₁ (fun y => min (g y) (u₁ y)) hu₁ ha
          (fun z => ⟨le_min (hg4 z).1 (hu₁0 z), min_le_right _ _⟩) δ hδ0
        have hb : ∀ z, 0 ≤ g z - min (g z) (u₁ z) ∧ g z - min (g z) (u₁ z) ≤ u₂ z := by
          intro z
          refine ⟨sub_nonneg.2 (min_le_left _ _), ?_⟩
          have h' : g z ≤ u₁ z + u₂ z := (hg4 z).2
          rcases le_total (g z) (u₁ z) with h | h
          · rw [min_eq_left h, sub_self]; exact hu₂0 z
          · rw [min_eq_right h]; linarith
        obtain ⟨b', hb'1, hb'2⟩ := happrox u₂ (fun y => g y - min (g y) (u₁ y)) hu₂
          (hg1.continuous.sub ha) hb δ hδ0
        have ha'K : support a' ⊆ K₁ := fun y hy => hu₁K fun h => hy (by
          have := ha'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hb'K : support b' ⊆ K₂ := fun y hy => hu₂K fun h => hy (by
          have := hb'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hcsa' := hcs a' K₁ hK₁ ha'K
        have hcsb' := hcs b' K₂ hK₂ hb'K
        have ha'A : a' ∈ A u₁ := (hA u₁ a').2 ⟨ha'1, hcsa'.1, hcsa'.2.trans hK₁D,
          fun z => ⟨(ha'2 z).1, (ha'2 z).2.1⟩⟩
        have hb'A : b' ∈ A u₂ := (hA u₂ b').2 ⟨hb'1, hcsb'.1, hcsb'.2.trans hK₂D,
          fun z => ⟨(hb'2 z).1, (hb'2 z).2.1⟩⟩
        have hgK : support g ⊆ K₁ ∪ K₂ := (hAsupp (u₁ + u₂) g hg).trans huK
        have hrK : support (g - a' - b') ⊆ K₁ ∪ K₂ := fun y hy => by
          by_contra hy'
          apply hy
          have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
          have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
          rw [Pi.sub_apply, Pi.sub_apply, notMem_support.1 (fun h => hy' (hgK h)),
            notMem_support.1 (fun h => hy1 (ha'K h)), notMem_support.1 (fun h => hy2 (hb'K h)),
            sub_zero, sub_zero]
        have hrcs := hcs (g - a' - b') (K₁ ∪ K₂) hKK hrK
        have hr1 : ContDiff ℝ (⊤ : ℕ∞) (g - a' - b') := (hg1.sub ha'1).sub hb'1
        have hrb : ∀ y, |(g - a' - b') y| ≤ 2 * δ := fun y => by
          have h1 := (ha'2 y).2.2
          have h2 := (hb'2 y).2.2
          rw [Pi.sub_apply, Pi.sub_apply]
          have e : g y - a' y - b' y =
              -((a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))) := by ring
          rw [e, abs_neg]
          calc |(a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))|
              ≤ |a' y - min (g y) (u₁ y)| + |b' y - (g y - min (g y) (u₁ y))| :=
                abs_add_le _ _
            _ ≤ 2 * δ := by linarith
        have hSr := hC (g - a' - b') hr1 hrcs.1 hrcs.2 (2 * δ) (by positivity) hrb
        have hdec : S ((a' + b') + (g - a' - b')) = S a' + S b' + S (g - a' - b') := by
          rw [hSadd (a' + b') (g - a' - b') (ha'1.add hb'1) (hcsa'.1.add hcsb'.1) hr1 hrcs.1,
            hSadd a' b' ha'1 hcsa'.1 hb'1 hcsb'.1]
        rw [show (a' + b') + (g - a' - b') = g by abel] at hdec
        have h1 := hle_sup u₁ hu₁ hu₁0 K₁ hK₁ hK₁D hu₁K a' ha'A
        have h2 := hle_sup u₂ hu₂ hu₂0 K₂ hK₂ hK₂D hu₂K b' hb'A
        linarith
      · have key : ∀ h₁ ∈ A u₁, ∀ h₂ ∈ A u₂, S h₁ + S h₂ ≤ sSup (S '' A (u₁ + u₂)) := by
          intro h₁ hh₁ h₂ hh₂
          obtain ⟨a1, a2, a3, a4⟩ := (hA u₁ h₁).1 hh₁
          obtain ⟨b1, b2, b3, b4⟩ := (hA u₂ h₂).1 hh₂
          rw [← hSadd h₁ h₂ a1 a2 b1 b2]
          have hmem : h₁ + h₂ ∈ A (u₁ + u₂) := (hA (u₁ + u₂) (h₁ + h₂)).2 ⟨a1.add b1,
            a2.add b2, (tsupport_add h₁ h₂).trans (union_subset a3 b3),
            fun y => ⟨add_nonneg (a4 y).1 (b4 y).1, add_le_add (a4 y).2 (b4 y).2⟩⟩
          exact hle_sup (u₁ + u₂) (hu₁.add hu₂) hu0 (K₁ ∪ K₂) hKK hKKD huK (h₁ + h₂) hmem
        have : sSup (S '' A u₁) ≤ sSup (S '' A (u₁ + u₂)) - sSup (S '' A u₂) := by
          apply hsup_le u₁ hu₁0
          intro h₁ hh₁
          have : sSup (S '' A u₂) ≤ sSup (S '' A (u₁ + u₂)) - S h₁ := by
            apply hsup_le u₂ hu₂0
            intro h₂ hh₂
            have := key h₁ hh₁ h₂ hh₂
            linarith
          linarith
        linarith
    -- homogeneity
    have hsmul : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ c : ℝ, 0 ≤ c →
        sSup (S '' A (c • u)) = c * sSup (S '' A u) := by
      intro u hu hu0 K hK hKD huK c hc
      have hcu0 : ∀ y, 0 ≤ (c • u) y := fun y => mul_nonneg hc (hu0 y)
      have hcuK : support (c • u) ⊆ K := (support_const_smul_subset c u).trans huK
      have hcuc : Continuous (c • u) := hu.const_smul c
      rcases hc.eq_or_lt with hc0 | hcpos
      · subst hc0
        rw [zero_mul]
        apply le_antisymm
        · apply hsup_le ((0 : ℝ) • u) hcu0
          intro h hh
          obtain ⟨-, -, -, h4⟩ := (hA ((0 : ℝ) • u) h).1 hh
          have : h = 0 := funext fun y => le_antisymm (by
            have := (h4 y).2
            rwa [Pi.smul_apply, zero_smul] at this) (h4 y).1
          rw [this, hS0]
        · have h0 := hle_sup ((0 : ℝ) • u) hcuc hcu0 K hK hKD hcuK 0 (hA0 ((0 : ℝ) • u) hcu0)
          rwa [hS0] at h0
      · apply le_antisymm
        · apply hsup_le (c • u) hcu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA (c • u) h).1 hh
          have hmem : c⁻¹ • h ∈ A u := (hA u (c⁻¹ • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c⁻¹) h2,
            (tsupport_smul_subset_right (fun _ => c⁻¹) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg (inv_nonneg.2 hc) (h4 y).1, by
                rw [Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hcpos]
                have := (h4 y).2
                rwa [Pi.smul_apply, smul_eq_mul] at this⟩⟩
          have := hle_sup u hu hu0 K hK hKD huK (c⁻¹ • h) hmem
          have e : S h = c * S (c⁻¹ • h) := by
            rw [hSsmul c⁻¹ h h1, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
          rw [e]
          exact mul_le_mul_of_nonneg_left this hc
        · rw [← le_div_iff₀' hcpos]
          apply hsup_le u hu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA u h).1 hh
          have hmem : c • h ∈ A (c • u) := (hA (c • u) (c • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c) h2,
            (tsupport_smul_subset_right (fun _ => c) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg hc (h4 y).1, by
                rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
                exact mul_le_mul_of_nonneg_left (h4 y).2 hc⟩⟩
          have := hle_sup (c • u) hcuc hcu0 K hK hKD hcuK (c • h) hmem
          rw [hSsmul c h h1] at this
          rw [le_div_iff₀' hcpos]
          exact this
    -- extension by zero of `f ∈ C_c(D, ℝ≥0)`; `f ↦ sup S(A (ext f))` is `ℝ≥0`-linear
    obtain ⟨ext, hext⟩ : ∃ ext : CompactlySupportedContinuousMap D NNReal →
        Euclid (m + 1) → ℝ, ∀ f y, ext f y = if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0 :=
      ⟨fun f y => if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0, fun _ _ => rfl⟩
    have hextK : ∀ f : CompactlySupportedContinuousMap D NNReal,
        IsCompact (Subtype.val '' tsupport f) ∧ Subtype.val '' tsupport f ⊆ D := fun f =>
      ⟨f.hasCompactSupport.image continuous_subtype_val, by rintro _ ⟨x, -, rfl⟩; exact x.2⟩
    have hext_supp : ∀ f : CompactlySupportedContinuousMap D NNReal,
        support (ext f) ⊆ Subtype.val '' tsupport f := by
      intro f y hy
      rw [mem_support, hext] at hy
      by_cases h : y ∈ D
      · rw [dite_eq_left h] at hy
        refine ⟨⟨y, h⟩, subset_tsupport _ ?_, rfl⟩
        intro h0
        apply hy
        rw [h0]
        rfl
      · rw [dite_eq_right h] at hy
        exact absurd rfl hy
    have hext_nonneg : ∀ f y, 0 ≤ ext f y := by
      intro f y
      rw [hext]
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact le_rfl
    have hext_cont : ∀ f : CompactlySupportedContinuousMap D NNReal, Continuous (ext f) := by
      intro f
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ Subtype.val '' tsupport f
      · have hyD : y ∈ D := (hextK f).2 hy
        have hcont : ContinuousOn (ext f) D := by
          rw [continuousOn_iff_continuous_domRestrict]
          have : D.domRestrict (ext f) = fun x : D => ((f x : NNReal) : ℝ) := by
            funext x
            rw [Set.domRestrict_apply, hext, dite_eq_left x.2]
          rw [this]
          exact NNReal.continuous_coe.comp f.continuous
        exact hcont.continuousAt (hD.mem_nhds hyD)
      · have : ext f =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [(hextK f).1.isClosed.isOpen_compl.mem_nhds hy] with z hz
          by_contra hne
          exact hz (hext_supp f hne)
        exact continuousAt_const.congr this.symm
    have hext_add : ∀ f g : CompactlySupportedContinuousMap D NNReal,
        ext (f + g) = ext f + ext g := by
      intro f g
      funext y
      simp only [hext, Pi.add_apply]
      split_ifs
      · simp
      · simp
    have hext_smul : ∀ (c : NNReal) (f : CompactlySupportedContinuousMap D NNReal),
        ext (c • f) = (c : ℝ) • ext f := by
      intro c f
      funext y
      simp only [hext, Pi.smul_apply]
      split_ifs
      · simp
      · simp
    have hΛ0 : ∀ f : CompactlySupportedContinuousMap D NNReal, 0 ≤ sSup (S '' A (ext f)) :=
      fun f => by
        have := hle_sup (ext f) (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2
          (hext_supp f) 0 (hA0 _ (hext_nonneg f))
        rwa [hS0] at this
    let Λn : CompactlySupportedContinuousMap D NNReal →ₗ[NNReal] NNReal :=
      { toFun := fun f => ⟨sSup (S '' A (ext f)), hΛ0 f⟩
        map_add' := fun f g => by
          apply NNReal.eq
          change sSup (S '' A (ext (f + g))) = sSup (S '' A (ext f)) + sSup (S '' A (ext g))
          rw [hext_add]
          exact hadd _ _ (hext_cont f) (hext_nonneg f) (hext_cont g) (hext_nonneg g) _ _
            (hextK f).1 (hextK f).2 (hext_supp f) (hextK g).1 (hextK g).2 (hext_supp g)
        map_smul' := fun c f => by
          apply NNReal.eq
          change sSup (S '' A (ext (c • f))) = (c : ℝ) * sSup (S '' A (ext f))
          rw [hext_smul]
          exact hsmul _ (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2 (hext_supp f)
            c c.2 }
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    refine ⟨RealRMK.rieszMeasure (CompactlySupportedContinuousMap.toRealPositiveLinear Λn),
      inferInstance, ?_⟩
    intro g hg hgc hgD hg0
    have hAg : A g = {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ g y} := by
      ext h
      exact hA g h
    rw [← hAg]
    refine ⟨hbddA g hg.continuous hg0 (tsupport g) hgc hgD (subset_tsupport g), ?_⟩
    have hgcs : HasCompactSupport (fun x : D => Real.toNNReal (g x)) := by
      refine (hsubK _ hgc hgD).of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal ?_ ((isClosed_tsupport g).preimage continuous_subtype_val))
      intro x hx
      apply subset_tsupport g
      intro h0
      apply hx
      simp [h0]
    let fg : CompactlySupportedContinuousMap D NNReal :=
      ⟨⟨fun x => Real.toNNReal (g x),
        continuous_real_toNNReal.comp (hg.continuous.comp continuous_subtype_val)⟩, hgcs⟩
    have hfg : ext fg = g := by
      funext y
      rw [hext]
      by_cases h : y ∈ D
      · rw [dite_eq_left h]
        exact Real.coe_toNNReal _ (hg0 y)
      · rw [dite_eq_right h]
        exact (image_eq_zero_of_notMem_tsupport (fun h' => h (hgD h'))).symm
    calc ∫ x : D, g x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn))
        = ∫ x : D, (CompactlySupportedContinuousMap.toReal fg) x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn)) := by
          congr 1
          funext x
          rw [CompactlySupportedContinuousMap.toReal_apply]
          exact (Real.coe_toNNReal _ (hg0 x)).symm
      _ = CompactlySupportedContinuousMap.toRealPositiveLinear Λn
          (CompactlySupportedContinuousMap.toReal fg) := RealRMK.integral_rieszMeasure _ _
      _ = (Λn fg : ℝ) := by rw [CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
      _ = sSup (S '' A (ext fg)) := rfl
      _ = sSup (S '' A g) := by rw [hfg]
  -- Step 3: Jordan decomposition of a locally bounded functional on smooth functions
  have hcsD : ∀ f : Euclid (m + 1) → ℝ, HasCompactSupport f → tsupport f ⊆ D →
      HasCompactSupport (fun x : D => f x) := by
    intro f hfc hfD
    refine (hsubK _ hfc hfD).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal ?_ ((isClosed_tsupport f).preimage continuous_subtype_val))
    intro x hx
    exact subset_tsupport f hx
  have hintD : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ → ∀ f : Euclid (m + 1) → ℝ,
      Continuous f → HasCompactSupport f → tsupport f ⊆ D → Integrable (fun x : D => f x) μ := by
    intro μ hμ f hf hfc hfD
    exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport (hcsD f hfc hfD)
  have hjordan : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧ IsFiniteMeasureOnCompacts μ₂ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
    intro S hSadd hSsmul hSbd
    obtain ⟨μ₁, hμ₁, h₁⟩ := hpos S hSadd hSsmul hSbd
    have hSneg : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → S (-g) = -S g :=
      fun g hg => by
        rw [show -g = (-1 : ℝ) • g by rw [neg_one_smul], hSsmul (-1) g hg, neg_one_mul]
    obtain ⟨μ₂, hμ₂, h₂⟩ := hpos (fun g => -S g)
      (fun g h hg hgc hh hhc => by rw [hSadd g h hg hgc hh hhc, neg_add])
      (fun c g hg => by rw [hSsmul c g hg, mul_neg])
      (fun K hK hKD => by
        obtain ⟨C, hC⟩ := hSbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (-g) hg.neg hgc.neg (by rwa [tsupport_neg]) M hM
          (fun y => by rw [Pi.neg_apply, abs_neg]; exact hgM y)
        rwa [hSneg g hg] at this)
    refine ⟨μ₁, μ₂, hμ₁, hμ₂, ?_⟩
    have hnn : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ D → (∀ y, 0 ≤ g y) → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro g hg hgc hgD hg0
      obtain ⟨hb₁, he₁⟩ := h₁ g hg hgc hgD hg0
      obtain ⟨hb₂, he₂⟩ := h₂ g hg hgc hgD hg0
      rw [he₁, he₂]
      set Ag := {h : Euclid (m + 1) → ℝ | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y} with hAg
      have hgA : g ∈ Ag := ⟨hg, hgc, hgD, fun y => ⟨hg0 y, le_rfl⟩⟩
      have hsubA : ∀ h ∈ Ag, g - h ∈ Ag := fun h hh =>
        ⟨hg.sub hh.1, hgc.sub hh.2.1, (tsupport_sub g h).trans (union_subset hgD hh.2.2.1),
          fun y => ⟨sub_nonneg.2 (hh.2.2.2 y).2, sub_le_self _ (hh.2.2.2 y).1⟩⟩
      have hdec : ∀ h ∈ Ag, S g = S (g - h) + S h := fun h hh => by
        rw [← hSadd (g - h) h (hg.sub hh.1) (hgc.sub hh.2.1) hh.1 hh.2.1, sub_add_cancel]
      have hne : Ag.Nonempty := ⟨g, hgA⟩
      have i1 : sSup ((fun g => -S g) '' Ag) ≤ sSup (S '' Ag) - S g := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₁ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      have i2 : sSup (S '' Ag) ≤ S g + sSup ((fun g => -S g) '' Ag) := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₂ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      linarith
    -- a general `g`: add `M χ`, with `|g| ≤ M` and a smooth cutoff `χ = 1` on `tsupport g`
    intro g hg hgc hgD
    obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hgc hD hgD
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ) (E := tsupport g)) (isClosed_tsupport g)
      (self_subset_thickening hδ _)
    have hχK : support χ ⊆ cthickening δ (tsupport g) :=
      hχs ▸ thickening_subset_cthickening δ _
    have hχcs := hcs χ (cthickening δ (tsupport g)) (IsCompact.cthickening hgc) hχK
    obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (M • χ) := contDiff_const.smul hχ
    have hψcs : HasCompactSupport (M • χ) := HasCompactSupport.smul_left (f := fun _ => M) hχcs.1
    have hψD : tsupport (M • χ) ⊆ D :=
      (tsupport_smul_subset_right (fun _ => M) χ).trans (hχcs.2.trans hδD)
    have hψ0 : ∀ y, 0 ≤ (M • χ) y := fun y => by
      rw [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hM0 (hχ01 y).1
    have hgψ0 : ∀ y, 0 ≤ (g + M • χ) y := fun y => by
      by_cases hy : y ∈ tsupport g
      · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (hχ1 y).1 hy, mul_one]
        have := hM y
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (g y)]
      · rw [Pi.add_apply, image_eq_zero_of_notMem_tsupport hy, zero_add]; exact hψ0 y
    have e1 := hnn (g + M • χ) (hg.add hψ) (hgc.add hψcs)
      ((tsupport_add g (M • χ)).trans (union_subset hgD hψD)) hgψ0
    have e2 := hnn (M • χ) hψ hψcs hψD hψ0
    rw [hSadd g (M • χ) hg hgc hψ hψcs] at e1
    have i1 : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ →
        ∫ x : D, (g + M • χ) x ∂μ = ∫ x : D, g x ∂μ + ∫ x : D, (M • χ) x ∂μ := by
      intro μ hμ
      simp only [Pi.add_apply]
      exact integral_add (hintD μ hμ g hg.continuous hgc hgD)
        (hintD μ hμ (M • χ) hψ.continuous hψcs hψD)
    rw [i1 μ₁ hμ₁, i1 μ₂ hμ₂] at e1
    linarith
  -- Step 4: representation of `T` on smooth fields
  have hsm_rep : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
    -- the standard basis
    obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)),
        b = EuclideanSpace.basisFun (Fin (m + 1)) ℝ := ⟨_, rfl⟩
    have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.norm_eq_one i
    have hbinner : ∀ (x : Euclid (m + 1)) (i : Fin (m + 1)), inner ℝ x (b i) = x i := by
      intro x i; rw [hb]; exact EuclideanSpace.inner_basisFun_real _ x i
    have hbsum : ∀ x : Euclid (m + 1), ∑ i, x i • b i = x := by
      intro x; rw [hb]; exact (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr x
    -- coordinate functionals
    have hcomp : ∀ i : Fin (m + 1), ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧
        IsFiniteMeasureOnCompacts μ₂ ∧ ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          HasCompactSupport g → tsupport g ⊆ D →
          T (fun y => g y • b i) = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro i
      have hsm : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          ContDiff ℝ (⊤ : ℕ∞) (fun y => g y • b i) := fun g hg => hg.smul contDiff_const
      have hcs1 : ∀ g : Euclid (m + 1) → ℝ, HasCompactSupport g →
          HasCompactSupport (fun y => g y • b i) := fun g hg =>
        hg.comp_left (g := fun r : ℝ => r • b i) (zero_smul ℝ (b i))
      apply hjordan (fun g => T (fun y => g y • b i))
      · intro g h hg hgc hh hhc
        have e : (fun y => (g + h) y • b i) = (fun y => g y • b i) + (fun y => h y • b i) := by
          funext y; rw [Pi.add_apply, Pi.add_apply, add_smul]
        change T (fun y => (g + h) y • b i) = T (fun y => g y • b i) + T (fun y => h y • b i)
        rw [e, hT_add _ _ ((hsm g hg).of_le (by exact_mod_cast le_top)) (hcs1 g hgc)
          ((hsm h hh).of_le (by exact_mod_cast le_top)) (hcs1 h hhc)]
      · intro c g hg
        have e : (fun y => (c • g) y • b i) = c • (fun y => g y • b i) := by
          funext y; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_smul]
        change T (fun y => (c • g) y • b i) = c * T (fun y => g y • b i)
        rw [e, hT_smul c _ ((hsm g hg).of_le (by exact_mod_cast le_top))]
      · intro K hK hKD
        obtain ⟨C, -, hC⟩ := hbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (fun y => g y • b i) (hsm g hg) (hcs1 g hgc)
          ((tsupport_smul_subset_left g (fun _ => b i)).trans hgK) M hM (fun y => by
            rw [norm_smul, hb1 i, mul_one, Real.norm_eq_abs]; exact hgM y)
        exact (le_abs_self _).trans this
    choose μ₁ μ₂ hμ₁ hμ₂ hrep using hcomp
    -- coordinates of a field
    have hcoord_sm : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y i) := fun φ i hφ =>
      (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hφ
    have hcoord_cs : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        HasCompactSupport φ → HasCompactSupport (fun y => φ y i) := fun φ i hφ =>
      hφ.comp_left (g := fun v : Euclid (m + 1) => v i) rfl
    have hcoord_ts : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        tsupport (fun y => φ y i) ⊆ tsupport φ := fun φ i =>
      tsupport_comp_subset (g := fun v : Euclid (m + 1) => v i) rfl φ
    have hTdecomp : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → T φ = ∑ i, T (fun y => φ y i • b i) := by
      intro φ hφ hφc
      have key : ∀ s : Finset (Fin (m + 1)),
          ContDiff ℝ 1 (∑ i ∈ s, fun y => φ y i • b i) ∧
          HasCompactSupport (∑ i ∈ s, fun y => φ y i • b i) ∧
          T (∑ i ∈ s, fun y => φ y i • b i) = ∑ i ∈ s, T (fun y => φ y i • b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          exact ⟨contDiff_const, HasCompactSupport.zero, hT0⟩
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          have h1 : ContDiff ℝ 1 (fun y => φ y j • b j) :=
            ((hcoord_sm φ j hφ).smul contDiff_const).of_le (by exact_mod_cast le_top)
          have h2 : HasCompactSupport (fun y => φ y j • b j) :=
            (hcoord_cs φ j hφc).comp_left (g := fun r : ℝ => r • b j) (zero_smul ℝ _)
          exact ⟨h1.add ih.1, h2.add ih.2.1, by rw [hT_add _ _ h1 h2 ih.1 ih.2.1, ih.2.2]⟩
      have hφeq : φ = ∑ i, fun y => φ y i • b i := by
        funext y
        rw [Finset.sum_apply]
        exact (hbsum (φ y)).symm
      conv_lhs => rw [hφeq]
      exact (key Finset.univ).2.2
    -- the dominating measure on `D`
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    obtain ⟨μD, hμD⟩ : ∃ μD : Measure D, μD = ∑ i, (μ₁ i + μ₂ i) := ⟨_, rfl⟩
    have hμDK : ∀ K : Set D, IsCompact K → μD K < ∞ := by
      intro K hK
      rw [hμD, Measure.finsetSum_apply]
      refine ENNReal.sum_lt_top.2 fun i _ => ?_
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨(hμ₁ i).lt_top_of_isCompact hK, (hμ₂ i).lt_top_of_isCompact hK⟩
    have : IsFiniteMeasureOnCompacts μD := ⟨hμDK⟩
    have hRN : ∀ ν : Measure D, IsFiniteMeasureOnCompacts ν → ν ≤ μD →
        ∃ r : D → ℝ≥0∞, Measurable r ∧ (∀ᵐ x ∂μD, r x < ∞) ∧ ν = μD.withDensity r := by
      intro ν hν hle
      have := hν
      refine ⟨ν.rnDeriv μD, Measure.measurable_rnDeriv _ _, Measure.rnDeriv_lt_top _ _, ?_⟩
      have := Measure.haveLebesgueDecomposition_add ν μD
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        zero_add] at this
    have hle₁ : ∀ i, μ₁ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_self_add
    have hle₂ : ∀ i, μ₂ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_add_self
    choose r₁ hr₁m hr₁lt hr₁ using fun i => hRN (μ₁ i) (hμ₁ i) (hle₁ i)
    choose r₂ hr₂m hr₂lt hr₂ using fun i => hRN (μ₂ i) (hμ₂ i) (hle₂ i)
    -- the density field `H`
    obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → D → ℝ, ∀ i x, c i x = (r₁ i x).toReal - (r₂ i x).toReal :=
      ⟨fun i x => (r₁ i x).toReal - (r₂ i x).toReal, fun _ _ => rfl⟩
    have hcm : ∀ i, Measurable (c i) := fun i => by
      have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
      rw [this]
      exact (hr₁m i).ennreal_toReal.sub (hr₂m i).ennreal_toReal
    obtain ⟨H, hH⟩ : ∃ H : D → Euclid (m + 1), ∀ x, H x = ∑ i, c i x • b i :=
      ⟨fun x => ∑ i, c i x • b i, fun _ => rfl⟩
    have hHm : Measurable H := by
      have : H = fun x => ∑ i, c i x • b i := funext hH
      rw [this]
      exact Finset.measurable_sum _ fun i _ => (hcm i).smul_const (b i)
    have hrepD : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = ∫ x : D, inner ℝ (φ x) (H x) ∂μD := by
      intro φ hφ hφc hφD
      rw [hTdecomp φ hφ hφc]
      have hterm : ∀ i, Integrable (fun x : D => c i x * φ x i) μD ∧
          T (fun y => φ y i • b i) = ∫ x : D, c i x * φ x i ∂μD := by
        intro i
        have hgi := hcoord_sm φ i hφ
        have hgc := hcoord_cs φ i hφc
        have hgD := (hcoord_ts φ i).trans hφD
        have I₁ := hintD (μ₁ i) (hμ₁ i) (fun y => φ y i) hgi.continuous hgc hgD
        have I₂ := hintD (μ₂ i) (hμ₂ i) (fun y => φ y i) hgi.continuous hgc hgD
        rw [hrep i (fun y => φ y i) hgi hgc hgD]
        rw [hr₁ i] at I₁ ⊢
        rw [hr₂ i] at I₂ ⊢
        have J₁ := (integrable_withDensity_iff_integrable_smul' (hr₁m i) (hr₁lt i)).1 I₁
        have J₂ := (integrable_withDensity_iff_integrable_smul' (hr₂m i) (hr₂lt i)).1 I₂
        rw [integral_withDensity_eq_integral_toReal_smul (hr₁m i) (hr₁lt i),
          integral_withDensity_eq_integral_toReal_smul (hr₂m i) (hr₂lt i), ← integral_sub J₁ J₂]
        have e : (fun x : D => c i x * φ x i) =
            fun x : D => (r₁ i x).toReal • φ x i - (r₂ i x).toReal • φ x i := by
          funext x
          rw [hc, smul_eq_mul, smul_eq_mul, sub_mul]
        rw [e]
        exact ⟨J₁.sub J₂, rfl⟩
      rw [Finset.sum_congr rfl fun i _ => (hterm i).2,
        ← integral_finsetSum _ fun i _ => (hterm i).1]
      congr 1
      funext x
      rw [hH, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, hbinner]
    -- normalization to a unit field
    obtain ⟨ν', hν'⟩ : ∃ ν' : D → Euclid (m + 1), ∀ x,
        ν' x = if H x = 0 then b 0 else ‖H x‖⁻¹ • H x :=
      ⟨fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x, fun _ => rfl⟩
    have hν'm : Measurable ν' := by
      have : ν' = fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x := funext hν'
      rw [this]
      exact Measurable.ite (measurableSet_eq_fun hHm measurable_const) measurable_const
        (hHm.norm.inv.smul hHm)
    have hν'1 : ∀ x, ‖ν' x‖ = 1 := by
      intro x
      rw [hν']
      split_ifs with h
      · exact hb1 0
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
    have hHν : ∀ (v : Euclid (m + 1)) (x : D),
        (‖H x‖₊ : ℝ) • inner ℝ v (ν' x) = inner ℝ v (H x) := by
      intro v x
      rw [hν', coe_nnnorm, smul_eq_mul]
      split_ifs with h
      · rw [h, norm_zero, zero_mul, inner_zero_right]
      · rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_mul]
    obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure D,
        μ' = μD.withDensity (fun x => ((‖H x‖₊ : NNReal) : ℝ≥0∞)) := ⟨_, rfl⟩
    have hμ'K : ∀ K : Set D, IsCompact K → μ' K < ∞ := by
      intro K hK
      have hKm : MeasurableSet K := hK.measurableSet
      have hlt : ∀ (r : D → ℝ≥0∞) (ν : Measure D), Measurable r → IsFiniteMeasureOnCompacts ν →
          ν = μD.withDensity r → IntegrableOn (fun x => (r x).toReal) K μD := by
        intro r ν hr hν hνr
        apply integrable_toReal_of_lintegral_ne_top hr.aemeasurable
        rw [← withDensity_apply _ hKm, ← hνr]
        exact (hν.lt_top_of_isCompact hK).ne
      have hci : ∀ i, IntegrableOn (c i) K μD := by
        intro i
        have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
        rw [this]
        exact (hlt _ _ (hr₁m i) (hμ₁ i) (hr₁ i)).sub (hlt _ _ (hr₂m i) (hμ₂ i) (hr₂ i))
      have hHK : IntegrableOn H K μD := by
        have : H = fun x => ∑ i, c i x • b i := funext hH
        rw [this]
        exact integrable_finsetSum _ fun i _ => (hci i).smul_const (b i)
      rw [hμ', withDensity_apply _ hKm]
      exact hHK.hasFiniteIntegral
    -- push forward to `ℝ^{m+1}`
    refine ⟨Measure.map Subtype.val μ', fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.map_apply measurable_subtype_coe hD.measurableSet.compl]
      have : (Subtype.val ⁻¹' Dᶜ : Set D) = ∅ := by
        ext x
        simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
        exact x.2
      rw [this, measure_empty]
    · intro K hK hKD
      rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
      exact (hμ'K _ (hsubK K hK hKD)).ne
    · exact Measurable.dite hν'm.neg measurable_const hD.measurableSet
    · intro y
      by_cases hy : y ∈ D
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_left hy, norm_neg, hν'1]
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_right hy, hb1]
    · intro φ hφ hφc hφD
      rw [(MeasurableEmbedding.subtype_coe hD.measurableSet).integral_map]
      have e : (fun x : D => inner ℝ (φ x) ((fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0) x))
          = fun x : D => -inner ℝ (φ x) (ν' x) := by
        funext x
        show inner ℝ (φ x) (if hy : (x : Euclid (m + 1)) ∈ D then -ν' ⟨x, hy⟩ else b 0) =
          -inner ℝ (φ x) (ν' x)
        rw [dite_eq_left x.2, Subtype.coe_eta, inner_neg_right]
      rw [e, integral_neg, neg_neg, hrepD φ hφ hφc hφD, hμ',
        integral_withDensity_eq_integral_smul hHm.nnnorm]
      congr 1
      funext x
      rw [NNReal.smul_def]
      exact (hHν (φ x) x).symm
  obtain ⟨μ, ν, hμD, hμK, hνm, hν1, hsmooth⟩ := hsm_rep
  refine ⟨μ, ν, hμD, hμK, hνm, hν1, ?_⟩
  -- Step 5: `C¹` fields, by mollification
  -- normalized mollifiers
  have hmoll : ∀ r : ℝ, 0 < r → ∃ ρ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball 0 r := by
    intro r hr
    let B : ContDiffBump (0 : Euclid (m + 1)) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    have hBs : HasCompactSupport B := B.hasCompactSupport
    have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
    have hI : 0 < ∫ x, B x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
      exact measure_ball_pos volume 0 hr
    refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
      fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
    · exact (support_mul_subset_right _ _).trans B.support_eq.subset
  have hprec : ContinuousLinearMap.precompR (Euclid (m + 1))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1)) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ]
        (Euclid (m + 1) →L[ℝ] Euclid (m + 1))) := by
    ext x A v
    simp [ContinuousLinearMap.precompR]
  intro φ hφ hφc hφD
  obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hφc hD hφD
  set K' := cthickening δ (tsupport φ) with hK'
  have hK'c : IsCompact K' := IsCompact.cthickening hφc
  have hK'm : MeasurableSet K' := isClosed_cthickening.measurableSet
  -- radii
  obtain ⟨rr, hrr0, hrrδ, hrrlim⟩ : ∃ rr : ℕ → ℝ, (∀ n, 0 < rr n) ∧ (∀ n, rr n ≤ δ) ∧
      Tendsto rr atTop (𝓝 0) := by
    refine ⟨fun n => δ / ((n : ℝ) + 1), fun n => div_pos hδ (by positivity), fun n => ?_, ?_⟩
    · exact div_le_self hδ.le (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  choose ρ hρs hρc hρ0 hρ1 hρsupp using fun n => hmoll (rr n) (hrr0 n)
  -- mollified fields
  obtain ⟨φn, hφn⟩ : ∃ φn : ℕ → Euclid (m + 1) → Euclid (m + 1),
      ∀ n, φn n = convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨fun n => convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun _ => rfl⟩
  have hφn_sm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φn n) := fun n => by
    rw [hφn]
    exact (hρc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs n)
      hφ.continuous.locallyIntegrable
  have hφn_supp : ∀ n, support (φn n) ⊆ K' := fun n => by
    rw [hφn]
    refine (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add (hρsupp n) (subset_tsupport φ)).trans ?_
    rw [ball_add_zero]
    exact (thickening_subset_cthickening _ _).trans (cthickening_mono (hrrδ n) _)
  have hφn_cs : ∀ n, HasCompactSupport (φn n) ∧ tsupport (φn n) ⊆ K' := fun n =>
    ⟨hK'c.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hφn_supp n) hK'c.isClosed),
      closure_minimal (hφn_supp n) hK'c.isClosed⟩
  -- bounds
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M', hM'⟩ := hdφc.bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  have hφn_bd : ∀ n y, ‖φn n y‖ ≤ Mφ := fun n y => by
    rw [hφn, ← dist_zero_right]
    exact dist_convolution_le hMφ0 (hρsupp n) (hρ0 n) (hρ1 n)
      hφ.continuous.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hMφ x)
  have hsmall : Tendsto (fun n => support (ρ n)) atTop (𝓝 (0 : Euclid (m + 1))).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [hrrlim.eventually (gt_mem_nhds hε)] with n hn
    exact (hρsupp n).trans ((ball_subset_ball hn.le).trans hεt)
  have hφn_lim : ∀ y, Tendsto (fun n => φn n y) atTop (𝓝 (φ y)) := fun y => by
    simp only [hφn]
    exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1) hsmall
      (Eventually.of_forall fun _ => hφ.continuous.aestronglyMeasurable)
      ((hφ.continuous.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- derivatives
  have hdφn : ∀ n y, fderiv ℝ (φn n) y =
      convolution (ρ n) (fderiv ℝ φ) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := fun n y => by
    rw [hφn, ← hprec]
    exact (hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρs n).continuous.locallyIntegrable hφ y).fderiv
  have hdφn_bd : ∀ n y, ‖fderiv ℝ (φn n) y‖ ≤ M' := fun n y => by
    rw [hdφn, ← dist_zero_right]
    exact dist_convolution_le hM'0 (hρsupp n) (hρ0 n) (hρ1 n)
      hdφc.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hM' x)
  have hdφn_lim : ∀ y, Tendsto (fun n => fderiv ℝ (φn n) y) atTop (𝓝 (fderiv ℝ φ y)) :=
    fun y => by
      simp only [hdφn]
      exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1)
        hsmall (Eventually.of_forall fun _ => hdφc.aestronglyMeasurable)
        ((hdφc.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- convergence of the left side
  have hL : Tendsto (fun n => T (φn n)) atTop (𝓝 (T φ)) := by
    simp only [hT]
    refine tendsto_integral_of_dominated_convergence (K'.indicator fun _ => ‖trc‖ * M')
      (fun n => (trc.continuous.comp ((hφn_sm n).continuous_fderiv (by simp))).aestronglyMeasurable)
      ?_ (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · exact ((integrable_indicator_iff hK'm).2
        (integrableOn_const hK'c.measure_lt_top.ne)).restrict
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        exact (trc.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hdφn_bd n y) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        have : fderiv ℝ (φn n) y = 0 :=
          notMem_support.1 fun h => hy ((hφn_cs n).2 (support_fderiv_subset ℝ h))
        rw [this, map_zero, norm_zero]
    · exact (trc.continuous.tendsto _).comp (hdφn_lim y)
  -- convergence of the right side
  have hR : Tendsto (fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ) atTop
      (𝓝 (-∫ y, inner ℝ (φ y) (ν y) ∂μ)) := by
    refine Tendsto.neg (tendsto_integral_of_dominated_convergence (K'.indicator fun _ => Mφ)
      (fun n => (Continuous.measurable2 continuous_inner (hφn_sm n).continuous.measurable
        hνm).aestronglyMeasurable) ?_ (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_))
    · exact (integrable_indicator_iff hK'm).2
        (integrableOn_const (hμK K' hK'c hδD))
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        refine (norm_inner_le_norm _ _).trans ?_
        rw [hν1, mul_one]
        exact hφn_bd n y
      · rw [indicator_of_notMem hy]
        have : φn n y = 0 := notMem_support.1 fun h => hy (hφn_supp n h)
        rw [this, inner_zero_left, norm_zero]
    · exact (hφn_lim y).inner tendsto_const_nhds
  have hLR : (fun n => T (φn n)) = fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ := by
    funext n
    exact hsmooth (φn n) (hφn_sm n) (hφn_cs n).1 ((hφn_cs n).2.trans hδD)
  rw [hLR] at hL
  exact tendsto_nhds_unique hL hR
/-- **Rescaled Gauss–Green identity** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi), the change
of variable `x → λₖ x` in (8), chapter-03.txt lines 661–665).  Suppose
`∫_F div φ dLᵐ⁺¹ = -∫ ⟨φ, ν⟩ dμ` for every `C¹` compactly supported `φ` with `tsupport φ ⊆ D`.
If `r > 0` and `g` is `C¹` with compact support and `y + r • tsupport g ⊆ D`, then with
`F_{y,r} = {w : y + r w ∈ F}`, `r⁻ᵐ ∫ ⟨g((z - y)/r), ν(z)⟩ dμ(z) = -∫_{F_{y,r}} div g dLᵐ⁺¹`:
`φ = g((· - y)/r)` is admissible with `div φ = r⁻¹ (div g)((· - y)/r)`, and the substitution
`z = y + r w` has Jacobian `rᵐ⁺¹`. -/
theorem Submission.codim1_rdo_dg_tma_rescaled_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r : ℝ) (g : Euclid (m + 1) → Euclid (m + 1)), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → ContDiff ℝ 1 g → HasCompactSupport g → (∀ w ∈ tsupport g, y + r • w ∈ D) → (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ = -∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by
  intro m D F μ ν y r g hF hGG hr hg hgc hD
  set T : Euclid (m + 1) → ℝ := fun w =>
    LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
    with hTdef
  -- the affine homeomorphism `A w = y + r • w` and its inverse
  let A : Euclid (m + 1) ≃ₜ Euclid (m + 1) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y)
  have hA : ∀ w, A w = y + r • w := fun w => rfl
  have hAsymm : ∀ z, A.symm z = r⁻¹ • (z - y) := by
    intro z
    apply A.injective
    rw [A.apply_symm_apply, hA, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  -- `φ = g ∘ A⁻¹` is admissible in the Gauss–Green identity
  set φ : Euclid (m + 1) → Euclid (m + 1) := fun z => g (r⁻¹ • (z - y)) with hφdef
  have hφA : φ = g ∘ A.symm := by
    funext z
    simp [hφdef, hAsymm]
  have hφ : ContDiff ℝ 1 φ := hg.comp (by fun_prop)
  have hφts : tsupport φ = A '' tsupport g := by
    rw [hφA, tsupport_comp_eq_preimage _ A.symm, A.preimage_symm]
  have hφc : HasCompactSupport φ := by
    rw [HasCompactSupport, hφts]
    exact hgc.isCompact.image A.continuous
  have hφD : tsupport φ ⊆ D := by
    rw [hφts]
    rintro _ ⟨w, hw, rfl⟩
    rw [hA]
    exact hD w hw
  -- chain rule: `div φ (z) = r⁻¹ (div g) (r⁻¹ • (z - y))`
  have hfd : ∀ z, fderiv ℝ φ z = r⁻¹ • fderiv ℝ g (r⁻¹ • (z - y)) := by
    intro z
    have hin : HasFDerivAt (fun z : Euclid (m + 1) => r⁻¹ • (z - y))
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) z :=
      ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const y).const_smul (r⁻¹ : ℝ)
    have hgd := ((hg.differentiable one_ne_zero) (r⁻¹ • (z - y))).hasFDerivAt
    have h2 : HasFDerivAt φ ((fderiv ℝ g (r⁻¹ • (z - y))).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1)))) z := hgd.comp z hin
    rw [h2.fderiv]
    ext x
    simp
  have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = r⁻¹ * T (r⁻¹ • (z - y)) := by
    intro z
    rw [hfd]
    simp [hTdef, map_smul]
  have hGG' := hGG φ hφ hφc hφD
  simp_rw [htr] at hGG'
  rw [integral_const_mul] at hGG'
  -- change of variables `z = y + r • w`
  have hcv : ∫ z in F, T (r⁻¹ • (z - y)) =
      r ^ (m + 1) * ∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
    have hpre : MeasurableSet ((fun w => y + r • w) ⁻¹' F) := hF.preimage (by fun_prop)
    rw [← integral_indicator hF, ← integral_indicator hpre]
    set Ψ : Euclid (m + 1) → ℝ := F.indicator (fun z => T (r⁻¹ • (z - y))) with hΨ
    have h1 : (fun w => ((fun w => y + r • w) ⁻¹' F).indicator T w) =
        fun w => Ψ (r • w + y) := by
      funext w
      rw [add_comm (r • w) y]
      by_cases hw : y + r • w ∈ F
      · rw [indicator_of_mem (show w ∈ (fun w => y + r • w) ⁻¹' F from hw), hΨ,
          indicator_of_mem hw]
        simp [smul_smul, inv_mul_cancel₀ hr.ne']
      · rw [indicator_of_notMem (show w ∉ (fun w => y + r • w) ⁻¹' F from hw), hΨ,
          indicator_of_notMem hw]
    rw [h1, Measure.integral_comp_smul volume (fun x => Ψ (x + y)) r,
      integral_add_right_eq_self Ψ y]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    rw [abs_of_pos (inv_pos.2 (pow_pos hr _))]
    field_simp
  rw [hcv] at hGG'
  -- `rᵐ ∫_{F_{y,r}} div g = -∫ ⟨g ((z - y) / r), ν⟩ dμ`; divide by `rᵐ`
  have hrm : (r ^ m) ≠ 0 := pow_ne_zero _ hr.ne'
  have key : ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ =
      -(r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, T w) := by
    have : r⁻¹ * (r ^ (m + 1) * ∫ w in (fun w => y + r • w) ⁻¹' F, T w) =
        r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
      rw [pow_succ]
      field_simp
    rw [this] at hGG'
    linarith
  rw [key]
  field_simp
/-- **Hausdorff measure on a hyperplane** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi),
chapter-03.txt lines 734–746).  For `v ≠ 0` in `ℝ^{m+1}` the hyperplane `P_v = (span{v})ᗮ` has
dimension `m`, so an orthonormal basis of `P_v` indexed by `Fin m` gives a linear isometry
`ι : ℝ^m → ℝ^{m+1}` onto `P_v`; in particular `⟨ι x, v⟩ = 0`.  `μHE[m]` is isometry invariant
(`ι_# μHE[m] = μHE[m]⌞range ι`) and equals Lebesgue measure on `ℝ^m`, hence
`μHE[m]⌞P_v = ι_# Lᵐ`. -/
theorem Submission.codim1_rdo_dg_tma_hyperplane_param : ∀ (m : ℕ) (v : Euclid (m + 1)), v ≠ 0 → ∃ ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1), (∀ x, inner ℝ (ι x) v = 0) ∧ (μHE[m] : Measure (Euclid (m + 1))).restrict ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))) = Measure.map ι volume := by
  intro m v hv
  set K : Submodule ℝ (Euclid (m + 1)) := (Submodule.span ℝ {v})ᗮ with hKdef
  -- `dim P_v = m`
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨by simp⟩
  have hK : Module.finrank ℝ K = m := Submodule.finrank_orthogonal_span_singleton hv
  -- `ι = (P_v ↪ ℝ^{m+1}) ∘ e`, `e : ℝ^m ≃ P_v` the inverse coordinates of an orthonormal basis
  let b : OrthonormalBasis (Fin m) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hK)
  let e : Euclid m ≃ₗᵢ[ℝ] K := b.repr.symm
  let ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1) := K.subtypeₗᵢ.comp e.toLinearIsometry
  have hιK : ∀ x, ι x ∈ K := fun x => (e x).2
  refine ⟨ι, ?_, ?_⟩
  · intro x
    have h := hιK x
    rw [hKdef, Submodule.mem_orthogonal_singleton_iff_inner_right] at h
    rw [real_inner_comm]
    exact h
  · have hrange : Set.range ι = (K : Set (Euclid (m + 1))) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact hιK x
      · intro hz
        refine ⟨e.symm ⟨z, hz⟩, ?_⟩
        simp [ι]
    -- `ι_# Lᵐ = ι_# μHE[m] = μHE[m]⌞range ι`
    rw [← hrange, ← ι.isometry.map_euclideanHausdorffMeasure,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
/-- **Simon Ch. 3, 4.3 (†)** (boundary-parallel directions): if `⟨u, v⟩ = 0` and `h` is `C¹` with
compact support, then `∫_H Dh(w)(u) dw = 0` on the half-space `H = {w : ⟨w, v⟩ > 0}`.  `H` is
invariant under `w ↦ w + t u`, so `Φ(t) = ∫_H h(w + t u) dw` is constant by translation
invariance of Lebesgue measure; differentiating under the integral sign at `t = 0` gives
`Φ'(0) = ∫_H Dh(w)(u) dw = 0`. -/
theorem Submission.codim1_rdo_dg_tma_tangential_halfspace : ∀ (P : ℕ) (v u : Euclid P) (h : Euclid P → ℝ), inner ℝ u v = 0 → ContDiff ℝ 1 h → HasCompactSupport h → ∫ w in {w : Euclid P | 0 < inner ℝ w v}, fderiv ℝ h w u = 0 := by
  intro P v u h huv hh hhc
  set H : Set (Euclid P) := {w | 0 < inner ℝ w v} with hHdef
  -- Step 1: `H` is open, hence measurable, and invariant under translation along `u`
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hHinv : ∀ (t : ℝ) (w : Euclid P), w + t • u ∈ H ↔ w ∈ H := by
    intro t w
    simp [hHdef, inner_add_left, real_inner_smul_left, huv]
  -- Step 2: `Φ(t) = ∫_H h(w + t u) dw` does not depend on `t`
  have hconst : ∀ t : ℝ, ∫ w in H, h (w + t • u) = ∫ w in H, h w := by
    intro t
    rw [← integral_indicator hHmeas, ← integral_indicator hHmeas]
    have hfun : (fun w => H.indicator (fun w => h (w + t • u)) w) =
        fun w => H.indicator h (w + t • u) := by
      funext w
      by_cases hw : w ∈ H
      · rw [indicator_of_mem hw, indicator_of_mem ((hHinv t w).2 hw)]
      · rw [indicator_of_notMem hw, indicator_of_notMem (fun h' => hw ((hHinv t w).1 h'))]
    rw [hfun, integral_add_right_eq_self (fun w => H.indicator h w) (t • u)]
  -- Step 3: `|Dh(w + t u)(u)| ≤ M‖u‖ 1_{B̄_{R+‖u‖}(0)}(w)` for `|t| < 1`
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support (hhc.fderiv ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set bound : Euclid P → ℝ :=
    (closedBall (0 : Euclid P) (R + ‖u‖)).indicator (fun _ => M * ‖u‖) with hbound
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  -- Step 4: differentiation under the integral sign at `t = 0`
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict H) (F := fun (t : ℝ) w => h (w + t • u))
    (F' := fun (t : ℝ) w => fderiv ℝ h (w + t • u) u) (x₀ := (0 : ℝ)) (bound := bound)
    (ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => (hh.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (by
      simp only [zero_smul, add_zero]
      exact (hh.continuous.integrable_of_hasCompactSupport hhc).integrableOn)
    ((hdc.clm_apply continuous_const).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w t ht => by
      by_cases hwt : w + t • u ∈ tsupport h
      · have h1 : ‖w + t • u‖ ≤ R := by simpa using hR hwt
        have ht1 : |t| < 1 := by simpa using ht
        have h2 : ‖w‖ ≤ R + ‖u‖ := by
          calc ‖w‖ = ‖(w + t • u) - t • u‖ := by simp
            _ ≤ ‖w + t • u‖ + ‖t • u‖ := norm_sub_le _ _
            _ ≤ R + ‖u‖ := by
                rw [norm_smul, Real.norm_eq_abs]
                nlinarith [abs_nonneg t, norm_nonneg u]
        rw [hbound, indicator_of_mem (by simpa using h2)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      · have : fderiv ℝ h (w + t • u) = 0 := by
          by_contra hne
          exact hwt (support_fderiv_subset ℝ hne)
        rw [this, zero_apply, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg hM0 (norm_nonneg _)) _)
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top).ne)).integrableOn
    (Eventually.of_forall fun w t _ => by
      have h1 : HasDerivAt (fun t : ℝ => w + t • u) u t := by
        simpa using ((hasDerivAt_id t).smul_const u).const_add w
      exact ((hhd (w + t • u)).hasFDerivAt.comp_hasDerivAt t h1))
  -- Step 5: `Φ` is constant, so `Φ'(0) = ∫_H Dh(w)(u) dw` vanishes
  have h0 : HasDerivAt (fun t : ℝ => ∫ w in H, h (w + t • u)) 0 0 := by
    have hfun : (fun t : ℝ => ∫ w in H, h (w + t • u)) = fun _ => ∫ w in H, h w :=
      funext hconst
    rw [hfun]
    exact hasDerivAt_const _ _
  have := key.2.unique h0
  simpa using this
/-- **Orthogonal Fubini: `(x, s) ↦ ι x + s v` preserves Lebesgue measure** (Simon Ch. 3, 4.3 (†),
step 2 of the proof).  Let `ι : ℝᵐ → ℝᵐ⁺¹` be a linear isometry and `v` a unit vector orthogonal
to its range.  The vectors `b_j = ι(e_j)` (`j < m`) and `b_m = v` are orthonormal, so they form an
orthonormal basis `B` of `ℝᵐ⁺¹`, and `B.repr⁻¹ : c ↦ Σⱼ cⱼ bⱼ` preserves Lebesgue measure.  The
coordinate map `S(x, s) = (x₀, …, x_{m-1}, s)` sends `Lᵐ ⊗ L¹` to `Lᵐ⁺¹` (`ofLp × id`, swap, the
inverse of `piFinSuccAbove` at the last index, `toLp`).  Finally `B.repr⁻¹ (S(x, s)) =
Σ_{j<m} xⱼ ι(eⱼ) + s v = ι x + s v`, so the map is the composition `B.repr⁻¹ ∘ S`. -/
theorem Submission.codim1_rdo_dg_tma_orthogonal_fubini : ∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → MeasurePreserving (fun p : Euclid m × ℝ => ι p.1 + p.2 • v) volume volume := by
  intro m ι v hv hιv
  -- Step 1: the adapted orthonormal basis `(ι e₀, …, ι e_{m-1}, v)`
  let b : Fin (m + 1) → Euclid (m + 1) :=
    Fin.lastCases v (fun i => ι (EuclideanSpace.single i (1 : ℝ)))
  have hb_last : b (Fin.last m) = v := by simp [b]
  have hb_cs : ∀ i : Fin m, b (Fin.castSucc i) = ι (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    simp [b]
  have hb : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hb_last, hv]
      | cast j =>
        rw [hb_last, hb_cs, real_inner_comm, hιv]
        simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        have := j.isLt
        simp
        omega
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [hb_last, hb_cs, hιv]
        simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        have := i.isLt
        simp
        omega
      | cast j =>
        rw [hb_cs, hb_cs, LinearIsometry.inner_map_map, EuclideanSpace.inner_single_left]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Fin.castSucc_inj]
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Euclid (m + 1)) := by simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rw [← coe_basisOfOrthonormalOfCardEqFinrank hb hcard,
      (basisOfOrthonormalOfCardEqFinrank hb hcard).span_eq]
  let B : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)) := OrthonormalBasis.mk hb hsp
  have hB : ∀ i, B i = b i := by
    intro i
    simp [B]
  -- Step 2: the coordinate map `S(x, s) = (x₀, …, x_{m-1}, s)` preserves Lebesgue measure
  let S : Euclid m × ℝ → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun p => WithLp.toLp 2 (Fin.snoc (WithLp.ofLp p.1) p.2)
  have hS : MeasurePreserving S volume volume := by
    have h1 : MeasurePreserving (fun p : Euclid m × ℝ => (WithLp.ofLp p.1, p.2))
        ((volume : Measure (Euclid m)).prod (volume : Measure ℝ))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) :=
      (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
    have h2 : MeasurePreserving (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      Measure.measurePreserving_swap
    have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
    have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
    have := h4.comp (h3.comp (h2.comp h1))
    convert this using 1
    funext p
    simp [S, MeasurableEquiv.piFinSuccAbove]
    rfl
  -- Step 3: `B.repr⁻¹` preserves Lebesgue measure and `B.repr⁻¹ ∘ S = (x, s) ↦ ι x + s v`
  have hΦ : MeasurePreserving (B.repr.symm : EuclideanSpace ℝ (Fin (m + 1)) → Euclid (m + 1))
      volume volume := B.measurePreserving_repr_symm
  have := hΦ.comp hS
  convert this using 1
  funext p
  simp only [comp_apply, S]
  rw [← OrthonormalBasis.sum_repr_symm, Fin.sum_univ_castSucc]
  simp only [hB, hb_last, hb_cs, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr p.1]
  simp [map_sum, map_smul]
/-- **Normal derivative over a half-space** (Simon Ch. 3, proof of Theorem 4.3, p. 82: the
integration `∫_{ℝⁿ} ∫_H ∂_{n+1} φ(x′, x^{n+1}) dx^{n+1} dx′` in the normal variable).  If
`ι : ℝ^m → ℝ^{m+1}` is a linear isometry, `v` is a unit vector normal to its range and `h` is `C¹`
with compact support, then `∫_{⟨w, v⟩ > 0} Dh(w)(v) dw = -∫_{ℝ^m} h(ι x) dx`.  The coordinates
`Θ(x, s) = ι x + s v` preserve Lebesgue measure (`codim1_rdo_dg_tma_orthogonal_fubini`) and satisfy
`⟨Θ(x, s), v⟩ = s`, so Fubini turns the left side into `∫ dx ∫_{s > 0} ∂ₛ h(ι x + s v) ds`; the
fundamental theorem of calculus on `(0, ∞)` for the compactly supported `C¹` function
`s ↦ h(ι x + s v)` gives `-h(ι x)`. -/
theorem Submission.codim1_rdo_dg_tma_normal_halfspace : ∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)) (h : Euclid (m + 1) → ℝ), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → ContDiff ℝ 1 h → HasCompactSupport h → ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v}, fderiv ℝ h w v = -∫ x, h (ι x) := by
  intro m ι v h hv hιv hh hhc
  -- `Θ(x, s) = ι x + s v` is measure preserving, and `⟨Θ(x, s), v⟩ = s`
  have hMP := Submission.codim1_rdo_dg_tma_orthogonal_fubini m ι v hv hιv
  set Θ : Euclid m × ℝ → Euclid (m + 1) := fun p => ι p.1 + p.2 • v with hΘdef
  set H : Set (Euclid (m + 1)) := {w | 0 < inner ℝ w v} with hHdef
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hΘv : ∀ p, inner ℝ (Θ p) v = p.2 := by
    intro p
    simp [hΘdef, inner_add_left, real_inner_smul_left, hιv, hv]
  -- the integrand `G = 1_H · Dh(·)(v)` is integrable
  set G : Euclid (m + 1) → ℝ := H.indicator (fun w => fderiv ℝ h w v) with hGdef
  have hdc : Continuous (fun w => fderiv ℝ h w v) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hGint : Integrable G :=
    (hdc.integrable_of_hasCompactSupport (hhc.fderiv_apply ℝ v)).indicator hHmeas
  -- change of variables `w = Θ(x, s)` and Fubini
  rw [← integral_indicator hHmeas]
  change ∫ w, G w = _
  have hGae : AEStronglyMeasurable G (Measure.map Θ volume) := by
    rw [hMP.map_eq]
    exact hGint.aestronglyMeasurable
  rw [← hMP.map_eq, integral_map hMP.measurable.aemeasurable hGae]
  have hGΘint : Integrable (fun p => G (Θ p)) ((volume : Measure (Euclid m)).prod volume) :=
    (integrable_map_measure hGae hMP.measurable.aemeasurable).1 (by rwa [hMP.map_eq])
  rw [Measure.volume_eq_prod, integral_prod _ hGΘint, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ∫ s, G (Θ (x, s)) = -h (ι x)
  -- for fixed `x`, the fundamental theorem of calculus for `k(s) = h(ι x + s v)` on `(0, ∞)`
  set k : ℝ → ℝ := fun s => h (ι x + s • v) with hkdef
  have hk : ContDiff ℝ 1 k := hh.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hiso : Isometry (fun s : ℝ => ι x + s • v) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hv, mul_one]
  have hkc : HasCompactSupport k := hhc.comp_isClosedEmbedding hiso.isClosedEmbedding
  have hderiv : ∀ s, deriv k s = fderiv ℝ h (ι x + s • v) v := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => ι x + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add (ι x)
    exact (((hh.differentiable one_ne_zero) (ι x + s • v)).hasFDerivAt.comp_hasDerivAt s h1).deriv
  have hFTC : ∫ s in Ioi 0, deriv k s = -h (ι x) := by
    rw [hkc.integral_Ioi_deriv_eq hk 0]
    simp [hkdef]
  -- compare the integrands: `Θ(x, s) ∈ H` exactly when `s > 0`
  rw [← hFTC, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [hGdef, hHdef, indicator_apply, mem_ofPred_eq, hΘv, mem_Ioi]
  split_ifs
  · rw [hderiv]
  · rfl

/-- **Gauss–Green for a half-space** (used in the proof of Simon Ch. 3, Theorem 4.3).  For
`|v| = 1` and `g ∈ C¹_c(ℝ^{m+1}; ℝ^{m+1})`,
`∫_{⟨w, v⟩ > 0} div g dL^{m+1} = −∫_{v^⊥} ⟨g, v⟩ dHᵐ`.  With `ι : ℝᵐ → v^⊥` from
`codim1_rdo_dg_tma_hyperplane_param`, `(ι e₀, …, ι e_{m−1}, v)` is an orthonormal basis `b`, so
`div g = Σⱼ D⟨bⱼ, g⟩(bⱼ)`.  The `m` tangential terms integrate to `0` over the half-space
(`codim1_rdo_dg_tma_tangential_halfspace`), the normal term is `−∫ ⟨v, g(ι x)⟩ dx`
(`codim1_rdo_dg_tma_normal_halfspace`), and `Hᵐ⌞v^⊥ = ι_# Lᵐ` turns it into the boundary
integral. -/
theorem Submission.codim1_rdo_dg_tma_halfspace_gauss_green : ∀ (m : ℕ) (v : Euclid (m + 1)) (g : Euclid (m + 1) → Euclid (m + 1)), ‖v‖ = 1 → ContDiff ℝ 1 g → HasCompactSupport g → ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v}, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), inner ℝ (g z) v ∂μHE[m] := by
  intro m v g hv hg hgc
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hιv, hmap⟩ := Submission.codim1_rdo_dg_tma_hyperplane_param m v hv0
  -- the adapted orthonormal basis `(ι e₀, …, ι e_{m-1}, v)`
  let b : Fin (m + 1) → Euclid (m + 1) :=
    Fin.lastCases v (fun i => ι (EuclideanSpace.single i (1 : ℝ)))
  have hb_last : b (Fin.last m) = v := by simp [b]
  have hb_cs : ∀ i : Fin m, b (Fin.castSucc i) = ι (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    simp [b]
  have hb : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hb_last, hv]
      | cast j =>
        rw [hb_last, hb_cs, real_inner_comm, hιv, ite_eq_right (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hb_last, hb_cs, hιv, ite_eq_right (Fin.castSucc_lt_last i).ne]
      | cast j =>
        rw [hb_cs, hb_cs, LinearIsometry.inner_map_map, EuclideanSpace.inner_single_left]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Fin.castSucc_inj]
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Euclid (m + 1)) := by simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rw [← coe_basisOfOrthonormalOfCardEqFinrank hb hcard,
      (basisOfOrthonormalOfCardEqFinrank hb hcard).span_eq]
  let B : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)) := OrthonormalBasis.mk hb hsp
  have hB : ∀ i, B i = b i := by
    intro i
    simp [B]
  -- scalar components
  set h : Fin (m + 1) → Euclid (m + 1) → ℝ := fun i w => inner ℝ (b i) (g w) with hhdef
  have hh_cd : ∀ i, ContDiff ℝ 1 (h i) := fun i => contDiff_const.inner ℝ hg
  have hh_cs : ∀ i, HasCompactSupport (h i) := by
    intro i
    exact hgc.mono' (fun w hw => by
      by_contra hgw
      exact hw (by simp [hhdef, image_eq_zero_of_notMem_tsupport hgw]))
  have hfd : ∀ i w, fderiv ℝ (h i) w (b i) =
      inner ℝ (b i) ((fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (b i)) := by
    intro i w
    have hgd : DifferentiableAt ℝ g w := (hg.differentiable one_ne_zero) w
    rw [hhdef]
    simp only
    rw [fderiv_inner_apply ℝ (differentiableAt_const (b i)) hgd]
    simp
  have htr : ∀ w, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = ∑ i, fderiv ℝ (h i) w (b i) := by
    intro w
    rw [LinearMap.trace_eq_sum_inner _ B]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfd, hB]
  have hint : ∀ i, Integrable (fun w => fderiv ℝ (h i) w (b i))
      (volume.restrict {w : Euclid (m + 1) | 0 < inner ℝ w v}) := by
    intro i
    have hc : Continuous (fun w => fderiv ℝ (h i) w (b i)) :=
      ((hh_cd i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun w => fderiv ℝ (h i) w (b i)) :=
      ((hh_cs i).fderiv ℝ).mono' (fun w hw => by
        by_contra hne
        exact hw (by simp [image_eq_zero_of_notMem_tsupport hne]))
    exact (hc.integrable_of_hasCompactSupport hcs).integrableOn
  simp_rw [htr]
  rw [integral_finsetSum _ (fun i _ => hint i), Fin.sum_univ_castSucc]
  -- the `m` tangential terms vanish
  have htan : ∀ i : Fin m, ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v},
      fderiv ℝ (h (Fin.castSucc i)) w (b (Fin.castSucc i)) = 0 := by
    intro i
    exact Submission.codim1_rdo_dg_tma_tangential_halfspace (m + 1) v (b (Fin.castSucc i))
      (h (Fin.castSucc i)) (by rw [hb_cs]; exact hιv _) (hh_cd _) (hh_cs _)
  simp_rw [htan, Finset.sum_const_zero, zero_add]
  -- the normal term, and `Hᵐ⌞v^⊥ = ι_# Lᵐ`
  rw [hb_last]
  have hnorm := Submission.codim1_rdo_dg_tma_normal_halfspace m ι v (h (Fin.last m)) hv hιv
    (hh_cd _) (hh_cs _)
  rw [hnorm, hmap]
  congr 1
  have hcont : Continuous (fun z => inner ℝ (g z) v) := hg.continuous.inner continuous_const
  rw [integral_map ι.continuous.aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [hhdef, hb_last, real_inner_comm]
/-- **Blow-up convergence of the vector measure `ν μ` on `C¹` vector fields** (Simon Ch. 3,
Theorem 4.3 (De Giorgi), chapter-03.txt lines 588–746: the closing step "by 4.1, (1) and (2)",
lines 739–746, with the change of variables (8), line 664).  Let `F` be Borel with
`∫_F div φ = −∫ ⟨φ, ν⟩ dμ` for every `C¹_c` field `φ` with `spt φ ⊆ D`, where `B̄_{ρ₁}(y) ⊆ D`,
and let the blow-ups `F_r = {w : y + r w ∈ F}` satisfy `L^{m+1}((F_r Δ H) ∩ B_R(0)) → 0` as
`r ↓ 0` for every `R`, where `H = {w : ⟨w, v⟩ > 0}`, `|v| = 1`.  Then for every `C¹_c` field `g`,
`r⁻ᵐ ∫ ⟨g(r⁻¹(z − y)), ν(z)⟩ dμ(z) → ∫_{v^⊥} ⟨g, v⟩ dHᵐ` as `r ↓ 0`.  With `spt g ⊆ B_R(0)`, the
rescaled Gauss–Green identity turns the left side into `−∫_{F_r} div g` for `r < ρ₁/R`;
`|∫_{F_r} div g − ∫_H div g| ≤ sup |div g| · L^{m+1}((F_r Δ H) ∩ B_R(0)) → 0`; and the half-space
Gauss–Green formula gives `∫_H div g = −∫_{v^⊥} ⟨g, v⟩ dHᵐ`. -/
theorem Submission.codim1_rdo_dg_tma_vector_convergence : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < ρ₁ → closedBall y ρ₁ ⊆ D → ‖v‖ = 1 → (∀ R : ℝ, Tendsto (fun r : ℝ => volume (symmDiff ((fun w => y + r • w) ⁻¹' F) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R)) (𝓝[>] 0) (𝓝 0)) → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), inner ℝ (g z) v ∂μHE[m])) := by
  intro m D F μ ν y v ρ₁ hF hGG hρ₁ hball hv hblow g hg hgc
  -- Step 1: `spt g ⊆ B_R(0)`.  `T = div g = trace Dg` is continuous and vanishes off `B_R(0)`
  -- (`Dg = 0` off `spt g`), so it is integrable and bounded by some `M`.
  obtain ⟨R, hRpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport g ⊆ ball (0 : Euclid (m + 1)) R := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  set T : Euclid (m + 1) → ℝ := fun w =>
    LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
    with hTdef
  have hTcont : Continuous T := by
    have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
    have h2 : Continuous (fun A : Euclid (m + 1) →L[ℝ] Euclid (m + 1) =>
        LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))) :=
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact h2.comp h1
  have hTzero : ∀ w, w ∉ ball (0 : Euclid (m + 1)) R → T w = 0 := by
    intro w hw
    have hw' : w ∉ tsupport g := fun h => hw (hR h)
    have : fderiv ℝ g w = 0 := by
      by_contra hne
      exact hw' (support_fderiv_subset ℝ hne)
    simp [hTdef, this]
  have hTcs : HasCompactSupport T := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) R) ?_
    intro w hw
    exact hTzero w (fun h => hw (ball_subset_closedBall h))
  obtain ⟨M, hM⟩ : ∃ M, ∀ w, ‖T w‖ ≤ M := hTcont.bounded_above_of_compact_support hTcs
  have hTint : Integrable T := hTcont.integrable_of_hasCompactSupport hTcs
  set H : Set (Euclid (m + 1)) := {w | 0 < inner ℝ w v}
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  -- Step 2: for `0 < r < ρ₁/R` and `w ∈ spt g`, `|(y + r w) − y| = r|w| < ρ₁`, so
  -- `y + r w ∈ B̄_{ρ₁}(y) ⊆ D` and the rescaled Gauss–Green identity gives
  -- `r⁻ᵐ ∫ ⟨g(r⁻¹(z − y)), ν⟩ dμ = −∫_{F_r} T`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ =
      -∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / R :=
      nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hRpos))
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    refine Submission.codim1_rdo_dg_tma_rescaled_gauss_green m D F μ ν y r g hF hGG hr hg hgc ?_
    intro w hw
    apply hball
    have hwR : ‖w‖ < R := by simpa using hR hw
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    have : r * ‖w‖ ≤ r * R := mul_le_mul_of_nonneg_left hwR.le hr.le
    have h2 : r * R < ρ₁ := by
      have := (lt_div_iff₀ hRpos).mp hrR
      linarith
    linarith
  -- Steps 3–4: `|∫_{F_r} T − ∫_H T| ≤ M · L^{m+1}((F_r Δ H) ∩ B_R(0))`, since the integrand
  -- `(1_{F_r} − 1_H) T` vanishes off `(F_r Δ H) ∩ B_R(0)` and is bounded by `M` there; the
  -- right side tends to `0` by the blow-up hypothesis.
  have hlim : Tendsto (fun r : ℝ => ∫ w in (fun w => y + r • w) ⁻¹' F, T w) (𝓝[>] 0)
      (𝓝 (∫ w in H, T w)) := by
    have hbound : ∀ r : ℝ, 0 < r → ‖(∫ w in (fun w => y + r • w) ⁻¹' F, T w) - ∫ w in H, T w‖ ≤
        M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R)).toReal := by
      intro r hr
      have hFr : MeasurableSet ((fun w => y + r • w) ⁻¹' F) :=
        hF.preimage (by fun_prop)
      rw [← integral_indicator hFr, ← integral_indicator hHmeas, ← integral_sub
        (hTint.indicator hFr) (hTint.indicator hHmeas)]
      have hS : MeasurableSet (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R) :=
        ((hFr.symmDiff hHmeas)).inter measurableSet_ball
      have hfin : volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R) ≠ ∞ :=
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top |>.ne
      calc ‖∫ w, ((fun w => y + r • w) ⁻¹' F).indicator T w - H.indicator T w‖
          ≤ ∫ w, (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
              ball (0 : Euclid (m + 1)) R).indicator (fun _ => M) w := by
            have hInt : Integrable ((symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
                ball (0 : Euclid (m + 1)) R).indicator (fun _ => M)) :=
              (integrable_indicator_iff hS).2 (integrableOn_const hfin)
            refine norm_integral_le_of_norm_le hInt (Eventually.of_forall fun w => ?_)
            have hMabs : ∀ w, |T w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
            by_cases hwB : w ∈ ball (0 : Euclid (m + 1)) R
            · by_cases h1 : w ∈ (fun w => y + r • w) ⁻¹' F <;> by_cases h2 : w ∈ H <;>
                simp [h1, h2, hwB, Set.mem_symmDiff, hMabs, norm_neg]
            · have hT0 := hTzero w hwB
              by_cases h1 : w ∈ (fun w => y + r • w) ⁻¹' F <;> by_cases h2 : w ∈ H <;>
                simp [h1, h2, hwB, hT0, Set.mem_symmDiff]
        _ = M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
              ball (0 : Euclid (m + 1)) R)).toReal := by
            rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm, Measure.real]
    have h0 : Tendsto (fun r : ℝ => M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R)).toReal) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hblow R)
      simpa using this.const_mul M
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hbound r hr
  -- Steps 5–6: `∫_H T = −∫_{v^⊥} ⟨g, v⟩ dHᵐ` by the half-space Gauss–Green formula, so
  -- `−∫_{F_r} T → ∫_{v^⊥} ⟨g, v⟩ dHᵐ`; by Step 2 the rescaled `ν μ`-integrals eventually agree.
  have hGGH := Submission.codim1_rdo_dg_tma_halfspace_gauss_green m v g hv hg hgc
  have hneg := hlim.neg
  rw [show (∫ w in H, T w) = -∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))),
      inner ℝ (g z) v ∂μHE[m] from hGGH, neg_neg] at hneg
  exact hneg.congr' (hev.mono fun r hr => hr.symm)
/-- **Normal-defect estimate** (Simon Ch. 3, 4.3 (†), "by 4.1, (1) and (2)"): weighting by
`⟨v, ν⟩` does not change blow-up limits.  Write `B_ρ = B̄_ρ(y)` and
`A(ρ) = μ(B_ρ)⁻¹ ∫_{B_ρ} ν dμ`.  Choose `R ≥ 1` with `tsupport f ⊆ B̄_R(0)` and `|f| ≤ M`; then
`f(r⁻¹(z − y)) ≠ 0` forces `z ∈ B_{rR}`, where `μ ≤ C (rR)ⁿ < ∞`.  Splitting
`f = f ⟨v, ν⟩ + f (1 − ⟨v, ν⟩)` with `0 ≤ 1 − ⟨v, ν⟩ ≤ 2` (Cauchy–Schwarz), the defect
`Δ(r) = r⁻ⁿ ∫ f(r⁻¹(z − y)) (1 − ⟨v, ν(z)⟩) dμ(z)` satisfies
`|Δ(r)| ≤ r⁻ⁿ M ∫_{B_{rR}} (1 − ⟨v, ν⟩) dμ = r⁻ⁿ M μ(B_{rR}) (1 − ⟨v, A(rR)⟩)
  ≤ M C Rⁿ |1 − ⟨v, A(rR)⟩|`, which tends to `0` because `A(rR) → v` and `⟨v, v⟩ = 1`. -/
theorem Submission.codim1_rdo_dg_tma_normal_defect : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₁ C L : ℝ) (f : Euclid P → ℝ), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 L) → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) := by
  intro P n μ ν y v ρ₁ C L f hνm hν1 hv hρ₁ hC hdens hA hf hfc hL
  -- Step 1: `tsupport f ⊆ B̄_R(0)` with `R ≥ 1`, and `|f| ≤ M`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport f ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ w, |f w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  set A : ℝ → Euclid P := fun ρ =>
    (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ with hAdef
  -- Step 2: Cauchy–Schwarz, `|⟨v, ν(z)⟩| ≤ 1`
  have hinner_le : ∀ z, inner ℝ v (ν z) ≤ 1 := by
    intro z
    have := real_inner_le_norm v (ν z)
    rwa [hv, hν1, one_mul] at this
  have hinner_abs : ∀ z, |inner ℝ v (ν z)| ≤ 1 := by
    intro z
    have := abs_real_inner_le_norm v (ν z)
    rwa [hv, hν1, one_mul] at this
  have hνinner_meas : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hνm
  -- Steps 3–6: for `0 < r` with `rR < ρ₁`, `|Δ(r)| ≤ M C Rⁿ |1 − ⟨v, A(rR)⟩|`
  have hbound : ∀ r : ℝ, 0 < r → r * R < ρ₁ →
      |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ| ≤
        M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))| := by
    intro r hr hrR
    set B := closedBall y (r * R) with hBdef
    have hBμ : μ B ≤ ENNReal.ofReal (C * (r * R) ^ n) := hdens _ (by positivity) hrR
    have hBfin : μ B ≠ ∞ := (hBμ.trans_lt ENNReal.ofReal_lt_top).ne
    have hsupp : ∀ z, z ∉ B → f (r⁻¹ • (z - y)) = 0 := by
      intro z hz
      by_contra hne
      have h1 := hR (subset_tsupport f hne)
      apply hz
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        at h1
      rw [hBdef, mem_closedBall, dist_eq_norm]
      calc ‖z - y‖ = r * (r⁻¹ * ‖z - y‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left h1 hr.le
    have hcont : Continuous (fun z => f (r⁻¹ • (z - y))) := by fun_prop
    -- Step 3: integrability
    have hint1 : Integrable (fun z => f (r⁻¹ • (z - y))) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hcont.aestronglyMeasurable (M := M)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM' _)
    have hint2 : Integrable (fun z => f (r⁻¹ • (z - y)) * inner ℝ v (ν z)) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_
        (fun z hz => by rw [hsupp z hz, zero_mul])
      refine Measure.integrableOn_of_bounded hBfin
        (hcont.aestronglyMeasurable.mul hνinner_meas.aestronglyMeasurable) (M := M)
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |f (r⁻¹ • (z - y))| * |inner ℝ v (ν z)| ≤ M * 1 :=
            mul_le_mul (hM' _) (hinner_abs z) (abs_nonneg _) hM0
        _ = M := mul_one M
    have hνint : IntegrableOn ν B μ :=
      Measure.integrableOn_of_bounded hBfin hνm.aestronglyMeasurable (M := 1)
        (Eventually.of_forall fun z => (hν1 z).le)
    -- Step 5: `∫_B (1 − ⟨v, ν⟩) dμ = μ(B) (1 − ⟨v, A(rR)⟩)`
    have hkey : ∫ z in B, (1 - inner ℝ v (ν z)) ∂μ =
        (μ B).toReal * (1 - inner ℝ v (A (r * R))) := by
      have hint3 : IntegrableOn (fun z => inner ℝ v (ν z)) B μ :=
        Measure.integrableOn_of_bounded hBfin hνinner_meas.aestronglyMeasurable (M := 1)
          (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hinner_abs z)
      rw [integral_sub (integrableOn_const (C := (1 : ℝ)) hBfin) hint3, setIntegral_const,
        smul_eq_mul, mul_one]
      have hcomm : ∫ z in B, inner ℝ v (ν z) ∂μ = inner ℝ v (∫ z in B, ν z ∂μ) := by
        have := ContinuousLinearMap.integral_comp_comm (innerSL ℝ v) hνint
        simpa using this
      rw [hcomm, Measure.real]
      by_cases h0 : (μ B).toReal = 0
      · have hμ0 : μ B = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
          · exact h
          · exact absurd h hBfin
        have : ∫ z in B, ν z ∂μ = 0 := by
          rw [Measure.restrict_eq_zero.2 hμ0, integral_zero_measure]
        rw [this, h0]
        simp
      · simp only [hAdef]
        rw [← hBdef, real_inner_smul_right]
        field_simp
    -- Step 4: splitting and the pointwise bound `|f (1 − ⟨v, ν⟩)| ≤ M (1 − ⟨v, ν⟩) 1_B`
    have hdiff : (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ =
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ := by
      rw [← mul_sub, ← integral_sub hint1 hint2]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      ring
    have hle : |∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ| ≤
        M * ∫ z in B, (1 - inner ℝ v (ν z)) ∂μ := by
      have hbint : Integrable (fun z => B.indicator (fun z => M * (1 - inner ℝ v (ν z))) z) μ := by
        refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
        refine Measure.integrableOn_of_bounded hBfin
          (aestronglyMeasurable_const.mul
            (aestronglyMeasurable_const.sub hνinner_meas.aestronglyMeasurable)) (M := M * 2)
          (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM0]
        refine mul_le_mul_of_nonneg_left ?_ hM0
        have := hinner_abs z
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hbint (Eventually.of_forall fun z => ?_)).trans ?_
      · by_cases hz : z ∈ B
        · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (sub_nonneg.2 (hinner_le z))]
          exact mul_le_mul_of_nonneg_right (hM' _) (sub_nonneg.2 (hinner_le z))
        · rw [indicator_of_notMem hz, hsupp z hz, zero_mul, norm_zero]
      · rw [integral_indicator measurableSet_closedBall, integral_const_mul]
    -- Step 6: `μ(B_{rR}) ≤ C (rR)ⁿ`
    have hμB : (μ B).toReal ≤ C * (r * R) ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hBμ
    rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr n))]
    calc (r ^ n)⁻¹ * |∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ|
        ≤ (r ^ n)⁻¹ * (M * ((μ B).toReal * |1 - inner ℝ v (A (r * R))|)) := by
          gcongr
          refine hle.trans ?_
          rw [hkey]
          gcongr
          exact le_abs_self _
      _ ≤ (r ^ n)⁻¹ * (M * ((C * (r * R) ^ n) * |1 - inner ℝ v (A (r * R))|)) := by
          gcongr
      _ = M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))| := by
          rw [mul_pow]
          field_simp
  -- Step 7: `A(rR) → v`, so the bound tends to `0`
  have hAr : Tendsto (fun r : ℝ => A (r * R)) (𝓝[>] 0) (𝓝 v) := by
    refine hA.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hin : Tendsto (fun r : ℝ => inner ℝ v (A (r * R))) (𝓝[>] 0) (𝓝 1) := by
    have hic : Continuous (fun w : Euclid P => inner ℝ v w) := continuous_const.inner continuous_id
    have := (hic.tendsto v).comp hAr
    simpa [Function.comp_def, real_inner_self_eq_norm_sq, hv] using this
  have h0 : Tendsto (fun r : ℝ => M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))|) (𝓝[>] 0)
      (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hin).abs.const_mul (M * (C * R ^ n))
    simpa using this
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / R :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hRpos))
  have hΔ : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
      (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    exact hbound r hr (by have := (lt_div_iff₀ hRpos).mp hrR; linarith)
  -- Step 8: `r⁻ⁿ ∫ f(r⁻¹(z − y)) dμ = r⁻ⁿ ∫ f(r⁻¹(z − y)) ⟨v, ν(z)⟩ dμ + Δ(r) → L`
  have := hL.add hΔ
  simpa using this
/-- **Uniform `C¹` approximation with support control** (Simon Ch. 3, proof of Theorem 4.3
(De Giorgi): "mollifying, there is `f_θ ∈ C_c^∞` with `spt f_θ ⊆ B_{R+1}(0)` and
`‖f − f_θ‖_∞ ≤ θ`").  `f` has compact support, so it is uniformly continuous; pick a modulus
`δ ≤ 1` for `θ`.  Convolving `f` with a nonnegative `C¹` bump `ψ`, `∫ ψ = 1`,
`spt ψ ⊆ B_δ(0)`, gives a `C¹` function `g` with `spt g ⊆ B_δ(0) + B̄_R(0) ⊆ B̄_{R+1}(0)` and
`|g(x) − f(x)| ≤ ∫ ψ(t) |f(x − t) − f(x)| dt ≤ θ`. -/
theorem Submission.codim1_rdo_dg_tma_smooth_approx : ∀ (P : ℕ) (f : Euclid P → ℝ) (R θ : ℝ), Continuous f → tsupport f ⊆ closedBall (0 : Euclid P) R → 0 < θ → ∃ g : Euclid P → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ tsupport g ⊆ closedBall (0 : Euclid P) (R + 1) ∧ ∀ x, |f x - g x| ≤ θ := by
  intro P f R θ hf hR hθ
  -- `f` is uniformly continuous; `δ = min δ₀ 1` is a modulus for `θ`
  have hfc : HasCompactSupport f :=
    (isCompact_closedBall (0 : Euclid P) R).of_isClosed_subset (isClosed_tsupport f) hR
  have huc : UniformContinuous f := hfc.uniformContinuous_of_continuous hf
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuous_iff.1 huc θ hθ
  set δ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ one_pos
  -- the normalized bump `ψ = c⁻¹ ψ₀`, `c = ∫ ψ₀ > 0`
  obtain ⟨ψ₀, hψ₀ts, hψ₀c, hψ₀s, hψ₀r, hψ₀0⟩ :=
    exists_contDiff_tsupport_subset (E := Euclid P) (s := ball (0 : Euclid P) δ) (x := 0)
      (n := 1) (ball_mem_nhds 0 hδpos)
  have hψ₀nn : ∀ x, 0 ≤ ψ₀ x := fun x => (hψ₀r ⟨x, rfl⟩).1
  set c := ∫ x, ψ₀ x with hcdef
  have hc : 0 < c :=
    hψ₀s.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hψ₀c hψ₀nn
      (by rw [hψ₀0]; norm_num)
  set ψ : Euclid P → ℝ := fun x => c⁻¹ * ψ₀ x with hψdef
  have hψs : ContDiff ℝ 1 ψ := contDiff_const.mul hψ₀s
  have hψc : HasCompactSupport ψ := hψ₀c.mul_left
  have hψnn : ∀ x, 0 ≤ ψ x := fun x => mul_nonneg (inv_nonneg.2 hc.le) (hψ₀nn x)
  have hψint : ∫ x, ψ x = 1 := by
    rw [hψdef, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne']
  have hψsupp : ∀ t, ψ t ≠ 0 → ‖t‖ < δ := by
    intro t ht
    have : t ∈ tsupport ψ₀ := subset_tsupport ψ₀ (fun h0 => ht (by simp [hψdef, h0]))
    simpa using hψ₀ts this
  -- `g = ψ ⋆ f` is `C¹`
  set g : Euclid P → ℝ := convolution ψ f (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgdef
  have hg : ContDiff ℝ 1 g :=
    hψc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hψs hf.locallyIntegrable
  have hgval : ∀ x, g x = ∫ t, ψ t * f (x - t) := by
    intro x
    rw [hgdef, convolution_def]
    simp
  -- `spt g ⊆ spt ψ + spt f ⊆ B̄_{R+1}(0)`
  have hgsupp : support g ⊆ closedBall (0 : Euclid P) (R + 1) := by
    refine (support_convolution_subset _).trans ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' : ‖a‖ < δ := hψsupp a ha
    have hb' : ‖b‖ ≤ R := by simpa using hR (subset_tsupport f hb)
    rw [mem_closedBall, dist_zero_right]
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ ≤ R + 1 := by
          have : δ ≤ 1 := min_le_right _ _
          linarith
  have hgts : tsupport g ⊆ closedBall (0 : Euclid P) (R + 1) :=
    closure_minimal hgsupp isClosed_closedBall
  refine ⟨g, hg, (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport g) hgts,
    hgts, fun x => ?_⟩
  -- `g x − f x = ∫ ψ(t) (f(x − t) − f(x)) dt`, and the integrand is at most `ψ(t) θ`
  have hint1 : Integrable (fun t => ψ t * f (x - t)) :=
    (hψs.continuous.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψc.mul_right
  have hint2 : Integrable (fun t => ψ t * f x) :=
    (hψs.continuous.integrable_of_hasCompactSupport hψc).mul_const _
  have hdiff : g x - f x = ∫ t, ψ t * (f (x - t) - f x) := by
    simp_rw [hgval, mul_sub]
    rw [integral_sub hint1 hint2, integral_mul_const, hψint, one_mul]
  rw [abs_sub_comm, hdiff]
  calc |∫ t, ψ t * (f (x - t) - f x)| ≤ ∫ t, ψ t * θ := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le
          ((hψs.continuous.integrable_of_hasCompactSupport hψc).mul_const _)
          (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψnn t)]
        by_cases ht : ψ t = 0
        · simp [ht]
        · refine mul_le_mul_of_nonneg_left ?_ (hψnn t)
          have h1 : dist (x - t) x < δ₀ := by
            rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
            exact (hψsupp t ht).trans_le (min_le_left _ _)
          exact (by simpa [Real.dist_eq] using (hδ h1).le)
    _ = θ := by rw [integral_mul_const, hψint, one_mul]

/-- **Blow-up convergence extends from `C¹` to continuous test functions** (Simon Ch. 3, 4.3 (†),
step 5 of the tangent-measure argument in De Giorgi's theorem; used for 7.5.8).  Let
`μ(B̄_ρ(y)) ≤ C ρⁿ` for `0 < ρ < ρ₁` and let `τ` be finite on closed balls.  If
`r⁻ⁿ ∫ g(r⁻¹(z − y)) dμ(z) → ∫ g dτ` as `r ↓ 0` for every `C¹` compactly supported `g`, the same
holds for every continuous compactly supported `f`.  With `tsupport f ⊆ B̄_R(0)`, `S = R + 1` and
`g` the `θ`-approximation of `f` given by `Submission.codim1_rdo_dg_tma_smooth_approx`,
`|r⁻ⁿ ∫ (f − g)(r⁻¹(z − y)) dμ| ≤ θ C Sⁿ` whenever `rS < ρ₁`, and `|∫ (f − g) dτ| ≤ θ τ(B̄_S(0))`;
take `θ = ε/(4K)` with `K = C Sⁿ + τ(B̄_S(0)) + 1`. -/
theorem Submission.codim1_rdo_dg_tma_continuous_extension : ∀ (P n : ℕ) (μ τ : Measure (Euclid P)) (y : Euclid P) (ρ₁ C : ℝ), 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ R : ℝ, τ (closedBall (0 : Euclid P) R) ≠ ∞) → (∀ g : Euclid P → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z ∂τ))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, f z ∂τ)) := by
  intro P n μ τ y ρ₁ C hρ₁ hC hdens hτ hsmooth f hf hfc
  -- Step 1: `tsupport f ⊆ B̄_R(0)` with `R ≥ 0`, and `S = R + 1`.
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : tsupport f ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set S := R + 1 with hSdef
  have hS : 0 < S := by positivity
  -- Step 2: if `φ` is continuous, `|φ| ≤ c`, `φ = 0` off `B̄_S(0)` and `rS < ρ₁`, then
  -- `z ↦ φ(r⁻¹(z − y))` vanishes off `B̄_{rS}(y)`, is `μ`-integrable, and
  -- `|r⁻ⁿ ∫ φ(r⁻¹(z − y)) dμ| ≤ r⁻ⁿ c μ(B̄_{rS}(y)) ≤ c C Sⁿ`.
  have key : ∀ (φ : Euclid P → ℝ) (c r : ℝ), Continuous φ → (∀ w, |φ w| ≤ c) →
      (∀ w, φ w ≠ 0 → w ∈ closedBall (0 : Euclid P) S) → 0 < r → r * S < ρ₁ →
      Integrable (fun z => φ (r⁻¹ • (z - y))) μ ∧
        |(r ^ n)⁻¹ * ∫ z, φ (r⁻¹ • (z - y)) ∂μ| ≤ c * (C * S ^ n) := by
    intro φ c r hφ hφc hφs hr hrS
    set B := closedBall y (r * S) with hBdef
    have hBfin : μ B ≠ ∞ :=
      ((hdens (r * S) (by positivity) hrS).trans_lt ENNReal.ofReal_lt_top).ne
    have hsupp : ∀ z, z ∉ B → φ (r⁻¹ • (z - y)) = 0 := by
      intro z hz
      by_contra hne
      have h1 := hφs _ hne
      apply hz
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        at h1
      rw [hBdef, mem_closedBall, dist_eq_norm]
      calc ‖z - y‖ = r * (r⁻¹ * ‖z - y‖) := by field_simp
        _ ≤ r * S := mul_le_mul_of_nonneg_left h1 hr.le
    have hcont : Continuous (fun z => φ (r⁻¹ • (z - y))) := by fun_prop
    have hint : Integrable (fun z => φ (r⁻¹ • (z - y))) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hcont.aestronglyMeasurable (M := c)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hφc _)
    refine ⟨hint, ?_⟩
    have hc0 : 0 ≤ c := (abs_nonneg _).trans (hφc 0)
    have hle : |∫ z, φ (r⁻¹ • (z - y)) ∂μ| ≤ c * (μ B).toReal := by
      have h2 : ‖∫ z, φ (r⁻¹ • (z - y)) ∂μ‖ ≤ ∫ z, B.indicator (fun _ => c) z ∂μ := by
        refine norm_integral_le_of_norm_le
          ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin))
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ B
        · rw [indicator_of_mem hz]
          simpa [Real.norm_eq_abs] using hφc _
        · rw [indicator_of_notMem hz, hsupp z hz, norm_zero]
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real] at h2
      simpa [Real.norm_eq_abs, mul_comm] using h2
    have hμ : (μ B).toReal ≤ C * (r * S) ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hdens _ (by positivity) hrS)
    rw [abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr n))]
    calc (r ^ n)⁻¹ * |∫ z, φ (r⁻¹ • (z - y)) ∂μ|
        ≤ (r ^ n)⁻¹ * (c * (C * (r * S) ^ n)) := by
          gcongr
          exact hle.trans (mul_le_mul_of_nonneg_left hμ hc0)
      _ = c * (C * S ^ n) := by
          rw [mul_pow]
          field_simp
  -- Step 3: for `φ` as in step 2, `φ` is `τ`-integrable and `|∫ φ dτ| ≤ c T`,
  -- `T = τ(B̄_S(0))`.
  set T := (τ (closedBall (0 : Euclid P) S)).toReal with hTdef
  have keyτ : ∀ (φ : Euclid P → ℝ) (c : ℝ), Continuous φ → (∀ w, |φ w| ≤ c) →
      (∀ w, φ w ≠ 0 → w ∈ closedBall (0 : Euclid P) S) →
      Integrable φ τ ∧ |∫ z, φ z ∂τ| ≤ c * T := by
    intro φ c hφ hφc hφs
    have hBfin := hτ S
    have hsupp : ∀ z, z ∉ closedBall (0 : Euclid P) S → φ z = 0 := by
      intro z hz
      by_contra hne
      exact hz (hφs z hne)
    have hint : Integrable φ τ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hφ.aestronglyMeasurable (M := c)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hφc _)
    refine ⟨hint, ?_⟩
    have h2 : ‖∫ z, φ z ∂τ‖ ≤ ∫ z, (closedBall (0 : Euclid P) S).indicator (fun _ => c) z ∂τ := by
      refine norm_integral_le_of_norm_le
        ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin))
        (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ closedBall (0 : Euclid P) S
      · rw [indicator_of_mem hz]
        simpa [Real.norm_eq_abs] using hφc _
      · rw [indicator_of_notMem hz, hsupp z hz, norm_zero]
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real] at h2
    simpa [Real.norm_eq_abs, mul_comm, hTdef] using h2
  -- `f` is bounded and vanishes off `B̄_S(0)`; `K = C Sⁿ + T + 1 > 0`.
  have hfs : ∀ w, f w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := by
    intro w hw
    have := hR (subset_tsupport f hw)
    exact closedBall_subset_closedBall (by linarith) this
  obtain ⟨Mf, hMf⟩ := hf.bounded_above_of_compact_support hfc
  have hMf' : ∀ w, |f w| ≤ Mf := fun w => by simpa [Real.norm_eq_abs] using hMf w
  set K := C * S ^ n + T + 1 with hKdef
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hK : 0 < K := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 4: `g ∈ C¹_c` with `tsupport g ⊆ B̄_S(0)` and `|f − g| ≤ θ = ε/(4K)`.
  set θ := ε / (4 * K) with hθdef
  have hθ : 0 < θ := by positivity
  obtain ⟨g, hg, hgc, hgs, hfg⟩ :=
    Submission.codim1_rdo_dg_tma_smooth_approx P f R θ hf hR hθ
  have hgs' : ∀ w, g w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := fun w hw =>
    hgs (subset_tsupport g hw)
  obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hMg' : ∀ w, |g w| ≤ Mg := fun w => by simpa [Real.norm_eq_abs] using hMg w
  -- Step 5: eventually `|r⁻ⁿ ∫ g(r⁻¹(z − y)) dμ − ∫ g dτ| < ε/2`, and `r < ρ₁/S`.
  have hlim := Metric.tendsto_nhds.1 (hsmooth g hg hgc) (ε / 2) (by positivity)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / S :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hS))
  filter_upwards [hlim, self_mem_nhdsWithin, hsmall] with r hr1 hr hrS
  have hrS' : r * S < ρ₁ := by
    have := (lt_div_iff₀ hS).mp hrS
    linarith
  -- Step 6: the `θ`-bounds for `f − g` from steps 2 and 3.
  have hdiff_s : ∀ w, (f - g) w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := by
    intro w hw
    by_cases hfw : f w = 0
    · have : g w ≠ 0 := by
        intro hgw
        apply hw
        simp [hfw, hgw]
      exact hgs' w this
    · exact hfs w hfw
  have hd : ∀ w, |(f - g) w| ≤ θ := fun w => by simpa using hfg w
  obtain ⟨hint_f, -⟩ := key f Mf r hf hMf' hfs hr hrS'
  obtain ⟨hint_g, -⟩ := key g Mg r hg.continuous hMg' hgs' hr hrS'
  obtain ⟨-, hest⟩ := key (f - g) θ r (hf.sub hg.continuous) hd hdiff_s hr hrS'
  obtain ⟨hτf, -⟩ := keyτ f Mf hf hMf' hfs
  obtain ⟨hτg, -⟩ := keyτ g Mg hg.continuous hMg' hgs'
  obtain ⟨-, hestτ⟩ := keyτ (f - g) θ (hf.sub hg.continuous) hd hdiff_s
  have e1 : (r ^ n)⁻¹ * ∫ z, (f - g) (r⁻¹ • (z - y)) ∂μ =
      (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ := by
    rw [← mul_sub, ← integral_sub hint_f hint_g]
    rfl
  have e2 : ∫ z, (f - g) z ∂τ = ∫ z, f z ∂τ - ∫ z, g z ∂τ := by
    rw [← integral_sub hτf hτg]
    rfl
  rw [e1] at hest
  rw [e2] at hestτ
  -- Step 7: the triangle inequality gives `< θ K + ε/2 = 3ε/4`.
  rw [Real.dist_eq] at hr1 ⊢
  have hθK : θ * (C * S ^ n) + θ * T ≤ ε / 2 := by
    have h1 : θ * (C * S ^ n) + θ * T ≤ θ * K := by
      rw [hKdef]
      nlinarith
    have h2 : θ * K = ε / 4 := by
      rw [hθdef]
      field_simp
    linarith
  calc |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - ∫ z, f z ∂τ|
      = |((r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ)
          + ((r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ - ∫ z, g z ∂τ)
          - (∫ z, f z ∂τ - ∫ z, g z ∂τ)| := by ring_nf
    _ ≤ |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ|
          + |(r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ - ∫ z, g z ∂τ|
          + |∫ z, f z ∂τ - ∫ z, g z ∂τ| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < θ * (C * S ^ n) + ε / 2 + θ * T := by
        have := hr1
        linarith
    _ ≤ ε := by linarith
/-- **Differentiation of the unit normal** (Simon Ch. 3, (4.2); Ch. 1, 3.23): if `μ` is carried
by the open set `D` and is finite on compact subsets of `D`, then for `μ`-a.e. `y` the averages of
the bounded Borel field `ν` over `B̄_ρ(y)` tend to `ν(y)` as `ρ ↓ 0`.  Exhaust `D` by the compact
sets `K a b = B̄_a(0) \ U_{1/(b+1)}(Dᶜ)`; for the finite measure `μ⌞K a b` this is Mathlib's
Lebesgue–Besicovitch differentiation theorem along closed balls (`ae_tendsto_average` for
`Besicovitch.vitaliFamily`, with `Besicovitch.tendsto_filterAt`), and near a point of `D` the
averages for `μ` and for `μ⌞K a b` coincide. -/
theorem Submission.codim1_rdo_dg_normal_average_ae : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → ∀ᵐ y ∂μ, y ∈ D ∧ Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 (ν y)) := by
  intro m D μ ν hD hDc hK hν hν1
  -- the compact sets `K a b = B̄_a(0) \ U_{1/(b+1)}(Dᶜ) ⊆ D`
  let K : ℕ → ℕ → Set (Euclid (m + 1)) := fun a b =>
    closedBall 0 a \ thickening (1 / ((b : ℝ) + 1)) Dᶜ
  have hKc : ∀ a b, IsCompact (K a b) := fun a b =>
    (isCompact_closedBall _ _).diff isOpen_thickening
  have hKD : ∀ a b, K a b ⊆ D := fun a b x hx => by
    by_contra hxD
    exact hx.2 (self_subset_thickening (by positivity) _ hxD)
  -- Besicovitch differentiation of `ν` for the finite measures `μ⌞K a b`
  have hdiff : ∀ a b, ∀ᵐ y ∂μ, y ∈ K a b → Tendsto
      (fun ρ : ℝ => ⨍ z in closedBall y ρ, ν z ∂(μ.restrict (K a b))) (𝓝[>] 0) (𝓝 (ν y)) := by
    intro a b
    have : IsFiniteMeasure (μ.restrict (K a b)) :=
      isFiniteMeasure_restrict.2 (hK _ (hKc a b) (hKD a b))
    have hint : Integrable ν (μ.restrict (K a b)) :=
      Integrable.of_bound hν.aestronglyMeasurable 1 (Eventually.of_forall fun y => (hν1 y).le)
    have h := (Besicovitch.vitaliFamily (μ.restrict (K a b))).ae_tendsto_average
      hint.locallyIntegrable
    rw [ae_restrict_iff' (hKc a b).isClosed.measurableSet] at h
    filter_upwards [h] with y hy hyK
    exact (hy hyK).comp (Besicovitch.tendsto_filterAt _ y)
  -- `μ`-a.e. point lies in `D`
  have hDae : ∀ᵐ y ∂μ, y ∈ D := by
    have h := compl_mem_ae_iff.2 hDc
    rwa [compl_compl] at h
  filter_upwards [hDae, ae_all_iff.2 fun a => ae_all_iff.2 (hdiff a)] with y hyD hy
  refine ⟨hyD, ?_⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD y hyD
  obtain ⟨a, ha⟩ := exists_nat_ge (‖y‖ + 1)
  obtain ⟨b, hb⟩ := exists_nat_one_div_lt (half_pos hε)
  -- `B̄_ρ(y) ⊆ K a b` for `ρ < min 1 (ε / 2)`
  have hsub : ∀ ρ : ℝ, ρ < 1 → ρ < ε / 2 → closedBall y ρ ⊆ K a b := by
    intro ρ hρ1 hρε z hz
    refine ⟨?_, fun hzt => ?_⟩
    · rw [mem_closedBall_zero_iff]
      have := norm_le_of_mem_closedBall hz
      linarith
    · obtain ⟨w, hwD, hzw⟩ := mem_thickening_iff.1 hzt
      apply hwD
      apply hεD
      rw [mem_ball]
      have hzy := mem_closedBall.1 hz
      rw [dist_comm] at hzw
      calc dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
        _ < ε := by linarith
  have hyK : y ∈ K a b := hsub 0 one_pos (half_pos hε) (mem_closedBall_self le_rfl)
  -- for small `ρ` the averages for `μ⌞K a b` and for `μ` over `B̄_ρ(y)` coincide
  refine (hy a b hyK).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (half_pos hε))] with ρ hρ
  have hρK := hsub ρ (hρ.2.trans_le (min_le_left _ _)) (hρ.2.trans_le (min_le_right _ _))
  rw [setAverage_eq, measureReal_def, Measure.restrict_apply measurableSet_closedBall,
    inter_eq_left.2 hρK, Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hρK]
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
/-- **The ball and cone masses are Borel functions of the centre.**  This is the measurability
that Simon's proof of Ch. 3, 1.6 "⇐" does not check when it applies Egoroff's theorem to `f_k`
and `q_k`, which are built from `μ(B_ρ(x))` and `μ(X_{1/2}(P_x^⊥, x) ∩ B_ρ(x))`.  For an s-finite
`μ` on `E = ℝ^{m+1}`, a Borel `ν : E → E` and `α, q ∈ ℝ`, the maps `x ↦ μ(B̄_q(x))` and
`x ↦ μ({z : α|z - x| ≤ |⟨z - x, ν(x)⟩|} ∩ B̄_q(x))` are measurable.  Each is `x ↦ μ(S_x)` for a
measurable `S ⊆ E × E`, namely `S = A = {(x, z) : |z - x| ≤ q}` or `S = B ∩ A` with
`B = {(x, z) : α|z - x| ≤ |⟨z - x, ν(x)⟩|}`, so the section lemma of Tonelli's theorem applies. -/
theorem Submission.codim1_rdo_dg_rc_ball_cone_measurable : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (α q : ℝ), SFinite μ → Measurable ν → Measurable (fun x : Euclid (m + 1) => μ (closedBall x q)) ∧ Measurable (fun x : Euclid (m + 1) => μ ({z | α * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x q)) := by
  intro m μ ν α q hμ hν
  -- `A = {(x, z) : |z - x| ≤ q}` is measurable, with sections `B̄_q(x)`
  have hA : MeasurableSet {p : Euclid (m + 1) × Euclid (m + 1) | dist p.2 p.1 ≤ q} :=
    measurableSet_le (continuous_dist.comp (continuous_snd.prodMk continuous_fst)).measurable
      measurable_const
  -- `B = {(x, z) : α|z - x| ≤ |⟨z - x, ν(x)⟩|}` is measurable since `ν` is
  have hB : MeasurableSet {p : Euclid (m + 1) × Euclid (m + 1) |
      α * ‖p.2 - p.1‖ ≤ |inner ℝ (p.2 - p.1) (ν p.1)|} := by
    refine measurableSet_le ?_ ?_
    · exact (continuous_const.mul (continuous_norm.comp
        (continuous_snd.sub continuous_fst))).measurable
    · exact continuous_abs.measurable.comp (Continuous.measurable2 continuous_inner
        (measurable_snd.sub measurable_fst) (hν.comp measurable_fst))
  -- for s-finite `μ`, `x ↦ μ(S_x)` is measurable for every measurable `S ⊆ E × E`
  refine ⟨?_, ?_⟩
  · have h := measurable_measure_prodMk_left (ν := μ) hA
    convert h using 2 with x
    rfl
  · have h := measurable_measure_prodMk_left (ν := μ) (hB.inter hA)
    convert h using 2 with x
    rfl

/-- **Uniform density and cone bounds on a large compact set** (Simon Ch. 3, proof of 1.6 "⇐",
(4) and (7)–(9), chapter-03.txt lines 162–213).  Let `μ` be a finite measure on `ℝ^{m+1}`,
`C(x) = {z : ¼|z − x| ≤ |⟨z − x, ν(x)⟩|}`, and suppose that for `μ`-a.e. `y`,
`μ(B̄_r(y))/(ωₘrᵐ) → 1` and `μ(C(y) ∩ B̄_r(y))/rᵐ → 0` as `r ↓ 0`.  Then for `ε, η > 0` there are
a compact `K` with `μ(Kᶜ) ≤ η` and `δ > 0` such that `(1 − ε)⁺ωₘρᵐ ≤ μ(B̄_ρ(x))` and
`μ(C(x) ∩ B̄_ρ(x)) ≤ εωₘρᵐ` for all `x ∈ K`, `0 < ρ < δ`.  Egoroff's theorem is replaced by the
Borel sets `G_k` of points where both bounds hold at every rational radius `0 < q < 1/(k + 1)`
(Borel by `codim1_rdo_dg_rc_ball_cone_measurable`): they increase to a set of full measure, so
`μ(G_kᶜ) < η/2` for some `k` by continuity from above, and inner regularity gives a compact
`K ⊆ G_k` with `μ(G_k \ K) < η/2`.  The bounds pass from rational to real radii by monotonicity
in the radius and continuity of `ρ ↦ cρᵐ`. -/
theorem Submission.codim1_rdo_dg_rc_uniform_compact : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (ε : ℝ) (η : ℝ≥0∞), IsFiniteMeasure μ → Measurable ν → 0 < ε → 0 < η → (∀ᵐ y ∂μ, Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) → ∃ K : Set (Euclid (m + 1)), ∃ δ : ℝ, IsCompact K ∧ 0 < δ ∧ μ Kᶜ ≤ η ∧ (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) ∧ (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) := by
  intro m μ ν ε η hfin hν hε hη hae
  have hω0 : unitBallVolume m ≠ 0 := by
    unfold unitBallVolume; exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume m ≠ ∞ := by
    unfold unitBallVolume; exact measure_ball_lt_top.ne
  -- step 2: for each radius `q` both `x ↦ μ(B̄_q(x))` and `x ↦ μ(C(x) ∩ B̄_q(x))` are Borel
  have hball : ∀ q : ℝ, Measurable (fun x : Euclid (m + 1) => μ (closedBall x q)) :=
    fun q => (Submission.codim1_rdo_dg_rc_ball_cone_measurable m μ ν (1 / 4) q inferInstance hν).1
  have hcone : ∀ q : ℝ, Measurable (fun x : Euclid (m + 1) =>
      μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x q)) :=
    fun q => (Submission.codim1_rdo_dg_rc_ball_cone_measurable m μ ν (1 / 4) q inferInstance hν).2
  -- monotonicity and continuity of `ρ ↦ c * ofReal (ρ ^ m)`
  have hmono : ∀ (c : ℝ≥0∞) (s t : ℝ), 0 ≤ s → s ≤ t →
      c * ENNReal.ofReal (s ^ m) ≤ c * ENNReal.ofReal (t ^ m) := by
    intro c s t hs hst
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hs hst m)) c
  have hcont : ∀ c : ℝ≥0∞, c ≠ ∞ → Continuous (fun s : ℝ => c * ENNReal.ofReal (s ^ m)) :=
    fun c hc => (ENNReal.continuous_const_mul hc).comp
      (ENNReal.continuous_ofReal.comp (continuous_pow m))
  -- the argument for general constants `A`, `B` and a general family of sets `C x`
  have main : ∀ (C : Euclid (m + 1) → Set (Euclid (m + 1))) (A B : ℝ≥0∞), A ≠ ∞ → B ≠ ∞ →
      (∀ q : ℝ, Measurable (fun x => μ (C x ∩ closedBall x q))) →
      (∀ᵐ y ∂μ, ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r < r₁ →
        A * ENNReal.ofReal (r ^ m) ≤ μ (closedBall y r) ∧
          μ (C y ∩ closedBall y r) ≤ B * ENNReal.ofReal (r ^ m)) →
      ∃ K : Set (Euclid (m + 1)), ∃ δ : ℝ, IsCompact K ∧ 0 < δ ∧ μ Kᶜ ≤ η ∧
        (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → A * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) ∧
        (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ →
          μ (C x ∩ closedBall x ρ) ≤ B * ENNReal.ofReal (ρ ^ m)) := by
    intro C A B hA hB hCmeas hgood
    -- step 1: the good sets `G k`, bounds at rational radii `q < 1/(k + 1)`
    let G : ℕ → Set (Euclid (m + 1)) := fun k => {x | ∀ q : ℚ, 0 < (q : ℝ) →
      (q : ℝ) < 1 / ((k : ℝ) + 1) →
      A * ENNReal.ofReal ((q : ℝ) ^ m) ≤ μ (closedBall x q) ∧
        μ (C x ∩ closedBall x q) ≤ B * ENNReal.ofReal ((q : ℝ) ^ m)}
    -- step 2: each `G k` is Borel
    have hGmeas : ∀ k, MeasurableSet (G k) := by
      intro k
      refine Measurable.setOf (Measurable.forall fun q => ?_)
      refine Measurable.imp measurable_const (Measurable.imp measurable_const
        (Measurable.and ?_ ?_))
      · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (hball q))
      · exact measurableSet_setOfPred.1 (measurableSet_le (hCmeas q) measurable_const)
    -- step 3: `G` is increasing
    have hGmono : Monotone G := by
      intro k l hkl x hx q hq0 hql
      refine hx q hq0 (lt_of_lt_of_le hql ?_)
      have hkl' : (k : ℝ) ≤ l := Nat.cast_le.mpr hkl
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    -- step 4: `μ`-a.e. point lies in some `G k`
    have hGae : ∀ᵐ x ∂μ, x ∈ ⋃ k, G k := by
      filter_upwards [hgood] with y hy
      obtain ⟨r₁, hr₁, hy⟩ := hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr₁
      exact mem_iUnion.mpr ⟨k, fun q hq0 hqk => hy q hq0 (hqk.trans hk)⟩
    have hnull : μ (⋂ k, (G k)ᶜ) = 0 := by
      rw [← compl_iUnion]
      exact mem_ae_iff.mp hGae
    -- step 5: continuity from above gives `μ (G k)ᶜ < η / 2` for some `k`
    have htend : Tendsto (fun k => μ (G k)ᶜ) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) (s := fun k => (G k)ᶜ)
        (fun k => (hGmeas k).compl.nullMeasurableSet)
        (fun k l hkl => compl_subset_compl.mpr (hGmono hkl)) ⟨0, measure_ne_top μ _⟩
      rw [hnull] at this
      exact this
    have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨k, hk⟩ := (htend.eventually_lt_const hη2).exists
    -- step 6: inner regularity gives a compact `K ⊆ G k` with `μ (G k \ K) < η / 2`
    obtain ⟨K, hKG, hKc, hKμ⟩ :=
      (hGmeas k).exists_isCompact_sdiff_lt (measure_ne_top μ _) hη2.ne'
    refine ⟨K, 1 / ((k : ℝ) + 1), hKc, by positivity, ?_, ?_, ?_⟩
    · calc μ Kᶜ ≤ μ ((G k)ᶜ ∪ (G k \ K)) := by
            apply measure_mono
            intro x hx
            by_cases h : x ∈ G k
            · exact Or.inr ⟨h, hx⟩
            · exact Or.inl h
        _ ≤ μ (G k)ᶜ + μ (G k \ K) := measure_union_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add hk.le hKμ.le
        _ = η := ENNReal.add_halves η
    -- step 7(a): lower bound at real radii, approximating `ρ` from below by rationals
    · intro x hxK ρ hρ hρδ
      have hxG := hKG hxK
      have key : ∀ s ∈ Ioo 0 ρ, A * ENNReal.ofReal (s ^ m) ≤ μ (closedBall x ρ) := by
        intro s hs
        obtain ⟨q, hsq, hqρ⟩ := exists_rat_btwn hs.2
        have hq0 : 0 < (q : ℝ) := hs.1.trans hsq
        calc A * ENNReal.ofReal (s ^ m) ≤ A * ENNReal.ofReal ((q : ℝ) ^ m) :=
              hmono A s q hs.1.le hsq.le
          _ ≤ μ (closedBall x q) := (hxG q hq0 (hqρ.trans hρδ)).1
          _ ≤ μ (closedBall x ρ) := measure_mono (closedBall_subset_closedBall hqρ.le)
      exact le_of_tendsto (((hcont A hA).tendsto ρ).mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsLT hρ) key)
    -- step 7(b): cone bound at real radii, approximating `ρ` from above by rationals
    · intro x hxK ρ hρ hρδ
      have hxG := hKG hxK
      have key : ∀ s ∈ Ioo ρ (1 / ((k : ℝ) + 1)),
          μ (C x ∩ closedBall x ρ) ≤ B * ENNReal.ofReal (s ^ m) := by
        intro s hs
        obtain ⟨q, hρq, hqs⟩ := exists_rat_btwn hs.1
        have hq0 : 0 < (q : ℝ) := hρ.trans hρq
        calc μ (C x ∩ closedBall x ρ) ≤ μ (C x ∩ closedBall x q) :=
              measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hρq.le))
          _ ≤ B * ENNReal.ofReal ((q : ℝ) ^ m) := (hxG q hq0 (hqs.trans hs.2)).2
          _ ≤ B * ENNReal.ofReal (s ^ m) := hmono B q s hq0.le hqs.le
      exact ge_of_tendsto (((hcont B hB).tendsto ρ).mono_left nhdsWithin_le_nhds)
        (eventually_of_mem (Ioo_mem_nhdsGT hρδ) key)
  -- step 4 for the actual constants: where both limits hold, the bounds hold for small `r`
  have hA1 : ENNReal.ofReal (1 - ε) < 1 := ENNReal.ofReal_lt_one.mpr (by linarith)
  have hB0 : 0 < ENNReal.ofReal ε * unitBallVolume m :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε).ne' hω0
  refine main (fun x => {z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|})
    (ENNReal.ofReal (1 - ε) * unitBallVolume m) (ENNReal.ofReal ε * unitBallVolume m)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop) hcone ?_
  filter_upwards [hae] with y hy
  obtain ⟨h1, h2⟩ := hy
  have e1 := h1.eventually_const_lt hA1
  have e2 := h2.eventually_lt_const hB0
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  refine ⟨r₁, hr₁, fun r hr0 hr1 => ?_⟩
  obtain ⟨hlow, hup⟩ := hsub ⟨hr0, hr1⟩
  have hpow0 : ENNReal.ofReal (r ^ m) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hr0 m)).ne'
  have hpowtop : ENNReal.ofReal (r ^ m) ≠ ∞ := ENNReal.ofReal_ne_top
  constructor
  · have := (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hω0 hpow0))
      (Or.inl (ENNReal.mul_ne_top hωtop hpowtop))).mp hlow.le
    rw [mul_assoc]
    exact this
  · exact (ENNReal.div_le_iff hpow0 hpowtop).mp hup.le
/-- **Simon Ch. 3, proof of 1.6 "⇐", claim (10)** (cone exclusion), in codimension one: let
`μ(B̄_ρ(y)) ≥ (1 − ε) ωₘ ρᵐ` and `μ(C(y) ∩ B̄_ρ(y)) ≤ ε ωₘ ρᵐ` for `y ∈ K`, `0 < ρ < δ`, where
`C(y) = {z : |z − y| ≤ 4 |⟨z − y, ν(y)⟩|}`, and let `(1 + 16ᵐ) ε < 1`.  Then
`|⟨x' − x, v⟩| ≤ |x' − x| / 2` for `x, x' ∈ K` with `|x' − x| < δ / 2` and `|ν(x) − v| ≤ 1/16`.
Otherwise `B̄_{ρ/8}(x') ⊆ C(x) ∩ B̄_{2ρ}(x)` for `ρ = |x' − x|`, and the two bounds give
`(1 − ε) ωₘ (ρ/8)ᵐ ≤ ε ωₘ (2ρ)ᵐ`, i.e. `1 − ε ≤ 16ᵐ ε`. -/
theorem Submission.codim1_rdo_dg_rc_cone_exclusion : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (K : Set (Euclid (m + 1))) (δ ε : ℝ), (∀ y, ‖ν y‖ = 1) → 0 ≤ ε → (1 + 16 ^ m) * ε < 1 → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) → ∀ x ∈ K, ∀ x' ∈ K, ∀ v : Euclid (m + 1), ‖ν x - v‖ ≤ 1 / 16 → ‖x' - x‖ < δ / 2 → |inner ℝ (x' - x) v| ≤ ‖x' - x‖ / 2 := by
  intro m μ ν K δ ε hν1 hε0 hε1 hlow hup x hx x' hx' v hv hxx'
  by_contra hcon
  push Not at hcon
  set w := x' - x with hw
  set ρ := ‖w‖ with hρ
  have hρ0 : 0 < ρ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · exfalso
      have hw0 : w = 0 := norm_eq_zero.1 h.symm
      rw [hw0] at hcon
      simp at hcon
      linarith [h, hρ]
  have hδ : 0 < δ := by linarith
  -- `|⟨w, ν x⟩| > 7ρ/16`, since `|⟨w, v⟩| > ρ/2` and `|ν x - v| ≤ 1/16`
  have h2 : 7 * ρ / 16 < |inner ℝ w (ν x)| := by
    have e1 : |inner ℝ w (v - ν x)| ≤ ρ * ‖ν x - v‖ := by
      calc |inner ℝ w (v - ν x)| ≤ ‖w‖ * ‖v - ν x‖ := abs_real_inner_le_norm _ _
        _ = ρ * ‖ν x - v‖ := by rw [norm_sub_rev v (ν x)]
    have e2 : inner ℝ w v = inner ℝ w (ν x) + inner ℝ w (v - ν x) := by
      rw [inner_sub_right]; ring
    have e3 : |inner ℝ w v| ≤ |inner ℝ w (ν x)| + |inner ℝ w (v - ν x)| := by
      rw [e2]; exact abs_add_le _ _
    have e4 : ρ * ‖ν x - v‖ ≤ ρ * (1 / 16) := mul_le_mul_of_nonneg_left hv hρ0.le
    linarith
  -- `B̄_{ρ/8}(x') ⊆ C(x) ∩ B̄_{2ρ}(x)`: on the small ball `|z - x| ≤ 9ρ/8` and
  -- `|⟨z - x, ν x⟩| > 7ρ/16 - ρ/8 = 5ρ/16`
  have hsub : closedBall x' (ρ / 8) ⊆
      {z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x (2 * ρ) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hzx : z - x = w + (z - x') := by rw [hw]; abel
    have hnorm : ‖z - x‖ ≤ 9 * ρ / 8 := by
      calc ‖z - x‖ = ‖w + (z - x')‖ := by rw [hzx]
        _ ≤ ‖w‖ + ‖z - x'‖ := norm_add_le _ _
        _ ≤ ρ + ρ / 8 := by linarith
        _ = 9 * ρ / 8 := by ring
    have hin : |inner ℝ (z - x') (ν x)| ≤ ρ / 8 := by
      calc |inner ℝ (z - x') (ν x)| ≤ ‖z - x'‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
        _ = ‖z - x'‖ := by rw [hν1 x, mul_one]
        _ ≤ ρ / 8 := hz
    have hinner : inner ℝ (z - x) (ν x) = inner ℝ w (ν x) + inner ℝ (z - x') (ν x) := by
      rw [hzx, inner_add_left]
    have hbig : 5 * ρ / 16 < |inner ℝ (z - x) (ν x)| := by
      rw [hinner]
      have h' : |inner ℝ w (ν x)| ≤
          |inner ℝ w (ν x) + inner ℝ (z - x') (ν x)| + |inner ℝ (z - x') (ν x)| := by
        have := abs_sub (inner ℝ w (ν x) + inner ℝ (z - x') (ν x)) (inner ℝ (z - x') (ν x))
        simpa using this
      linarith
    refine ⟨?_, ?_⟩
    · show (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|
      linarith
    · rw [mem_closedBall, dist_eq_norm]; linarith
  -- `(1 - ε) ωₘ (ρ/8)ᵐ ≤ μ(B̄_{ρ/8}(x')) ≤ μ(C(x) ∩ B̄_{2ρ}(x)) ≤ ε ωₘ (2ρ)ᵐ`
  have hlow' := hlow x' hx' (ρ / 8) (by positivity) (by linarith)
  have hup' := hup x hx (2 * ρ) (by positivity) (by linarith)
  have hchain : ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal ((ρ / 8) ^ m) ≤
      ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal ((2 * ρ) ^ m) :=
    hlow'.trans ((measure_mono hsub).trans hup')
  -- cancelling `ωₘ (ρ/8)ᵐ ∈ (0, ∞)` gives `1 - ε ≤ 16ᵐ ε`, contradicting `(1 + 16ᵐ) ε < 1`
  have hω0 : unitBallVolume m ≠ 0 := by
    unfold unitBallVolume; exact (measure_ball_pos _ _ one_pos).ne'
  have hωt : unitBallVolume m ≠ ∞ := by
    unfold unitBallVolume; exact measure_ball_lt_top.ne
  set a := (unitBallVolume m).toReal with ha_def
  have ha : 0 < a := ENNReal.toReal_pos hω0 hωt
  have hωeq : unitBallVolume m = ENNReal.ofReal a := (ENNReal.ofReal_toReal hωt).symm
  have h1ε : 0 ≤ 1 - ε := by
    have : 0 ≤ (16 : ℝ) ^ m * ε := by positivity
    nlinarith
  have hL : ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal ((ρ / 8) ^ m) =
      ENNReal.ofReal ((1 - ε) * a * (ρ / 8) ^ m) := by
    rw [hωeq, ← ENNReal.ofReal_mul h1ε, ← ENNReal.ofReal_mul (by positivity)]
  have hR : ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal ((2 * ρ) ^ m) =
      ENNReal.ofReal (ε * a * (2 * ρ) ^ m) := by
    rw [hωeq, ← ENNReal.ofReal_mul hε0, ← ENNReal.ofReal_mul (by positivity)]
  rw [hL, hR, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  have hpow : (2 * ρ) ^ m = 16 ^ m * (ρ / 8) ^ m := by
    rw [← mul_pow]; congr 1; ring
  rw [hpow] at hchain
  have hpos : 0 < a * (ρ / 8) ^ m := by positivity
  have h16 : (1 - ε) * (a * (ρ / 8) ^ m) ≤ (ε * 16 ^ m) * (a * (ρ / 8) ^ m) := by
    calc (1 - ε) * (a * (ρ / 8) ^ m) = (1 - ε) * a * (ρ / 8) ^ m := by ring
      _ ≤ ε * a * (16 ^ m * (ρ / 8) ^ m) := hchain
      _ = (ε * 16 ^ m) * (a * (ρ / 8) ^ m) := by ring
  have h17 : 1 - ε ≤ ε * 16 ^ m := le_of_mul_le_mul_right h16 hpos
  nlinarith
/-- **Simon Ch. 3, proof of 1.6 "⇐"** (Lipschitz graph step, codimension one): if `‖v‖ = 1` and
`|⟨x' − x, v⟩| ≤ ‖x' − x‖/2` on `S`, then `S` lies in a closed countably `m`-rectifiable set.
With `t(z) = ⟨z, v⟩` and `p(z) = z − t(z)v`, the hypothesis gives `|t(x') − t(x)| ≤ ‖p(x') − p(x)‖`
on `S`, so `p(x) ↦ t(x)` is 1-Lipschitz on `p(S)`; its McShane extension `τ` makes
`Γ = {z | τ(p(z)) = t(z)}` closed, and `Γ` lies in the range of the Lipschitz map
`y ↦ ι(y) + τ(ι(y))v`, where `ι : ℝᵐ ≃ v^⊥` is a linear isometry. -/
theorem Submission.codim1_rdo_dg_rc_closed_graph_cover : ∀ (m : ℕ) (v : Euclid (m + 1)) (S : Set (Euclid (m + 1))), ‖v‖ = 1 → (∀ x ∈ S, ∀ x' ∈ S, |inner ℝ (x' - x) v| ≤ ‖x' - x‖ / 2) → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ S ⊆ Γ := by
  intro m v S hv hS
  -- Step 1: height `t` and orthogonal projection `p` onto `vᗮ`.
  obtain ⟨t, ht⟩ : ∃ t : Euclid (m + 1) → ℝ, ∀ z, t z = inner ℝ z v := ⟨_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Euclid (m + 1) → Euclid (m + 1), ∀ z, p z = z - t z • v :=
    ⟨_, fun _ => rfl⟩
  have hvv : inner ℝ v v = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hpv : ∀ z, inner ℝ (p z) v = (0 : ℝ) := by
    intro z
    rw [hp, inner_sub_left, real_inner_smul_left, hvv, ht, mul_one, sub_self]
  have hpmem : ∀ z, p z ∈ (ℝ ∙ v)ᗮ := by
    intro z
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hpv z
  have hdecomp : ∀ z, p z + t z • v = z := by
    intro z
    rw [hp, sub_add_cancel]
  -- Step 2: the key inequality `|t x' - t x| ≤ ‖p x' - p x‖` on `S`.
  have key : ∀ x ∈ S, ∀ x' ∈ S, |t x' - t x| ≤ ‖p x' - p x‖ := by
    intro x hx x' hx'
    have h1 := hS x hx x' hx'
    have h2 : inner ℝ (x' - x) v = t x' - t x := by
      rw [inner_sub_left, ht, ht]
    have h3 : x' - x = (p x' - p x) + (t x' - t x) • v := by
      rw [hp, hp, sub_smul]
      abel
    have h4 : ‖x' - x‖ ≤ ‖p x' - p x‖ + |t x' - t x| := by
      calc ‖x' - x‖ = ‖(p x' - p x) + (t x' - t x) • v‖ := by rw [← h3]
        _ ≤ ‖p x' - p x‖ + ‖(t x' - t x) • v‖ := norm_add_le _ _
        _ = ‖p x' - p x‖ + |t x' - t x| := by
          rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
    rw [h2] at h1
    linarith
  -- Step 3: the height as a function of the projection, and its McShane extension.
  obtain ⟨τ, hτ⟩ : ∃ τ : Euclid (m + 1) → ℝ, ∀ x ∈ S, τ (p x) = t x := by
    refine ⟨fun y => t (Function.invFunOn p S y), ?_⟩
    intro x hx
    have hex : ∃ a ∈ S, p a = p x := ⟨x, hx, rfl⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have h := key x hx _ hmem
    rw [heq, sub_self, norm_zero] at h
    have h0 : t (Function.invFunOn p S (p x)) - t x = 0 := abs_nonpos_iff.mp h
    show t (Function.invFunOn p S (p x)) = t x
    linarith
  have hτLip : LipschitzOnWith 1 τ (p '' S) := by
    apply LipschitzOnWith.mk_one
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [hτ x hx, hτ x' hx', Real.dist_eq, dist_eq_norm]
    exact key x' hx' x hx
  obtain ⟨τ', hτ'Lip, hτ'eq⟩ := hτLip.extend_real
  -- Step 4: an isometry `ι : ℝᵐ ≃ vᗮ` and the Lipschitz graph map `F`.
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hv0 : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  let ι := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m hv0).repr.symm
  let F : Euclid m → Euclid (m + 1) := fun y => ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1)) +
    τ' ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1)) • v
  have hFLip : ∃ K, LipschitzWith K F := by
    have h1 : LipschitzWith (1 * 1)
        (fun y : Euclid m => ((ι y : (ℝ ∙ v)ᗮ) : Euclid (m + 1))) :=
      (Submodule.subtypeₗᵢ (ℝ ∙ v)ᗮ).lipschitzWith.comp ι.lipschitzWith
    have hsm : LipschitzWith 1 (fun r : ℝ => r • v) := by
      apply LipschitzWith.mk_one
      intro r s
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq, Real.norm_eq_abs]
    exact ⟨_, h1.add (hsm.comp (hτ'Lip.comp h1))⟩
  obtain ⟨K, hK⟩ := hFLip
  -- Step 5: the closed graph `Γ = {z | τ' (p z) = t z}`.
  have htc : Continuous t := by
    rw [show t = fun z => inner ℝ z v from funext ht]
    fun_prop
  have hpc : Continuous p := by
    rw [show p = fun z => z - t z • v from funext hp]
    fun_prop
  refine ⟨{z | τ' (p z) = t z}, ?_, ?_, ?_⟩
  · exact isClosed_eq (hτ'Lip.continuous.comp hpc) htc
  · apply (Poincare.SimonGMT.Chapter03.countablyRectifiable_range hK).mono
    intro z hz
    simp only [mem_ofPred_eq] at hz
    refine ⟨ι.symm ⟨p z, hpmem z⟩, ?_⟩
    simp only [F, LinearIsometryEquiv.apply_symm_apply]
    rw [hz]
    exact hdecomp z
  · intro x hx
    simp only [mem_ofPred_eq]
    rw [← hτ'eq (mem_image_of_mem p hx)]
    exact hτ x hx

/-- **Compact cover** of Simon Ch. 3, proof of Theorem 1.6 "⇐": the choice of `π₁, …, π_N` with
`E = ⋃ⱼ Eⱼ` and the selection `E ⊆ ⋃ⱼ Qⱼ(graph fⱼ)`, in codimension one, where the subspaces `πⱼ`
become unit directions `v`.  Cover the unit sphere by finitely many balls `B_{1/16}(v)` and `K` by
finitely many balls `B_{δ/4}(c)`, `c ∈ K`.  Two points of
`S_{v,c} = {x ∈ K : |ν(x) − v| < 1/16} ∩ B_{δ/4}(c)` are less than `δ/2` apart, so
`codim1_rdo_dg_rc_cone_exclusion` gives `|⟨x' − x, v⟩| ≤ ½|x' − x|` on `S_{v,c}`, and
`codim1_rdo_dg_rc_closed_graph_cover` gives a closed countably `m`-rectifiable `Γ_{v,c} ⊇ S_{v,c}`.
The finite union of the `Γ_{v,c}` contains `K`, since `|ν(x)| = 1`. -/
theorem Submission.codim1_rdo_dg_rc_compact_cover : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (K : Set (Euclid (m + 1))) (δ ε : ℝ), (∀ y, ‖ν y‖ = 1) → IsCompact K → 0 < δ → 0 ≤ ε → (1 + 16 ^ m) * ε < 1 → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ENNReal.ofReal (1 - ε) * unitBallVolume m * ENNReal.ofReal (ρ ^ m) ≤ μ (closedBall x ρ)) → (∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ < δ → μ ({z | (1 / 4 : ℝ) * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x ρ) ≤ ENNReal.ofReal ε * unitBallVolume m * ENNReal.ofReal (ρ ^ m)) → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ K ⊆ Γ := by
  intro m μ ν K δ ε hν1 hK hδ hε0 hε1 hlow hup
  -- step 1: a finite `1/16`-net `V` of the unit sphere
  obtain ⟨V, hVs, hVfin, hVcov⟩ :=
    (isCompact_sphere (0 : Euclid (m + 1)) 1).finite_cover_balls (e := 1 / 16) (by norm_num)
  -- step 2: a finite `δ/4`-net `C ⊆ K` of `K`
  obtain ⟨C, -, hCfin, hCcov⟩ := hK.finite_cover_balls (e := δ / 4) (by positivity)
  -- step 3: on `S_{v,c}` the cone condition holds in direction `v`, so `S_{v,c}` lies in a closed
  -- countably `m`-rectifiable `Γ_{v,c}`
  have hS : ∀ v ∈ V, ∀ c ∈ C, ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧
      {x | x ∈ K ∧ dist (ν x) v < 1 / 16} ∩ ball c (δ / 4) ⊆ Γ := by
    intro v hv c _
    have hv1 : ‖v‖ = 1 := by simpa using hVs hv
    apply Submission.codim1_rdo_dg_rc_closed_graph_cover m v _ hv1
    rintro x ⟨⟨hxK, hxv⟩, hxc⟩ x' ⟨⟨hx'K, -⟩, hx'c⟩
    apply Submission.codim1_rdo_dg_rc_cone_exclusion m μ ν K δ ε hν1 hε0 hε1 hlow hup
      x hxK x' hx'K v
    · rw [← dist_eq_norm]
      exact hxv.le
    · calc ‖x' - x‖ = dist x' x := (dist_eq_norm _ _).symm
        _ ≤ dist x' c + dist c x := dist_triangle _ _ _
        _ < δ / 4 + δ / 4 := add_lt_add (mem_ball.1 hx'c) (mem_ball'.1 hxc)
        _ = δ / 2 := by ring
  choose! Γ hΓc hΓr hΓS using hS
  -- step 4: `⋃_{v,c} Γ_{v,c}` is closed (a finite union) and countably `m`-rectifiable (a
  -- countable union)
  refine ⟨⋃ v ∈ V, ⋃ c ∈ C, Γ v c, ?_, ?_, ?_⟩
  · exact hVfin.isClosed_biUnion fun v hv => hCfin.isClosed_biUnion fun c hc => hΓc v hv c hc
  · rw [← sUnion_image2 Γ V C]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
      (hVfin.image2 Γ hCfin).countable (forall_mem_image2.2 hΓr)
  -- step 5: `x ∈ K` lies in `S_{v,c}` for a `v ∈ V` with `|ν(x) − v| < 1/16` and a `c ∈ C` with
  -- `x ∈ B_{δ/4}(c)`
  · intro x hxK
    have hνx : ν x ∈ sphere (0 : Euclid (m + 1)) 1 := by simpa using hν1 x
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 (hVcov hνx)
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hCcov hxK)
    exact mem_iUnion₂.2 ⟨v, hv, mem_iUnion₂.2 ⟨c, hc, hΓS v hv c hc ⟨⟨hxK, mem_ball.1 hxv⟩, hxc⟩⟩⟩

/-- **Halving step (★)** of Simon Ch. 3, proof of Theorem 1.6 "⇐":
`μ(ℝ^{n+ℓ} \ ⋃ⱼ Qⱼ(graph fⱼ)) ≤ ½ μ(ℝ^{n+ℓ})`, obtained there from (4) and (8).  If `Ū` is a
compact subset of `D`, then `λ = μ⌞U` is finite and, since `λ = μ` on closed balls inside the open
set `U`, inherits the a.e. density and cone limits.  `codim1_rdo_dg_rc_uniform_compact` with
`ε = 1/(2(1 + 16ᵐ))` and `η = μ(U)/2` gives a compact `K` with `λ(Kᶜ) ≤ μ(U)/2` and uniform bounds
on `K`, and `codim1_rdo_dg_rc_compact_cover` gives a closed countably `m`-rectifiable `Γ ⊇ K`; then
`μ(U \ Γ) = λ(U \ Γ) ≤ λ(Kᶜ) ≤ μ(U)/2`. -/
theorem Submission.codim1_rdo_dg_rc_halving_step : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0)) → ∀ U : Set (Euclid (m + 1)), IsOpen U → IsCompact (closure U) → closure U ⊆ D → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ μ (U \ Γ) ≤ μ U / 2 := by
  intro m D μ ν hfin hν hν1 hae U hU hUc hUD
  -- step 1: `μ(U) ≤ μ(Ū) < ∞`; if `μ(U) = 0`, then `Γ = ∅` works
  have hUfin : μ U ≠ ∞ := ne_top_of_le_ne_top (hfin _ hUc hUD) (measure_mono subset_closure)
  by_cases h0 : μ U = 0
  · refine ⟨∅, isClosed_empty,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero (by simp), ?_⟩
    simp [h0]
  -- step 2: `λ = μ⌞U` is finite and has the same limits as `μ` at every `y ∈ U`, because the two
  -- functions of `r` agree for `0 < r < r_y`, where `B_{r_y}(y) ⊆ U`
  set lam := μ.restrict U with hlam
  have : IsFiniteMeasure lam := isFiniteMeasure_restrict.2 hUfin
  have haeL : ∀ᵐ y ∂lam,
      Tendsto (fun r : ℝ => lam (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)))
        (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r : ℝ => lam ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩
        closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae hae] with y hyU hy
    obtain ⟨h1, h2⟩ := hy
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hyU
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r := by
      filter_upwards [Ioo_mem_nhdsGT hr] with s hs using hs.2
    constructor
    · refine h1.congr' ?_
      filter_upwards [hev] with s hs
      rw [hlam, Measure.restrict_apply' hU.measurableSet,
        inter_eq_left.2 ((closedBall_subset_ball hs).trans hrU)]
    · refine h2.congr' ?_
      filter_upwards [hev] with s hs
      rw [hlam, Measure.restrict_apply' hU.measurableSet,
        inter_eq_left.2 (inter_subset_right.trans ((closedBall_subset_ball hs).trans hrU))]
  -- step 3: `ε = 1/(2(1 + 16ᵐ)) > 0` with `(1 + 16ᵐ)ε = 1/2 < 1`, and `η = μ(U)/2 > 0`
  set ε : ℝ := 1 / (2 * (1 + 16 ^ m)) with hε
  have hεpos : 0 < ε := by positivity
  have hε1 : (1 + 16 ^ m) * ε < 1 := by
    have : (0 : ℝ) < 1 + 16 ^ m := by positivity
    rw [hε, mul_one_div, div_lt_one (by positivity)]
    linarith
  -- step 4: a compact `K` with `λ(Kᶜ) ≤ η` on which the density and cone bounds are uniform
  obtain ⟨K, δ, hK, hδ, hKc, hlow, hup⟩ := Submission.codim1_rdo_dg_rc_uniform_compact m lam ν ε
    (μ U / 2) inferInstance hν hεpos (ENNReal.half_pos h0) haeL
  -- step 5: a closed countably `m`-rectifiable `Γ ⊇ K`
  obtain ⟨Γ, hΓc, hΓr, hKΓ⟩ :=
    Submission.codim1_rdo_dg_rc_compact_cover m lam ν K δ ε hν1 hK hδ hεpos.le hε1 hlow hup
  -- step 6: `μ(U \ Γ) = λ(U \ Γ) ≤ λ(Kᶜ) ≤ μ(U)/2`, as `U \ Γ ⊆ U` and `U \ Γ ⊆ Kᶜ`
  refine ⟨Γ, hΓc, hΓr, ?_⟩
  calc μ (U \ Γ) = lam (U \ Γ) := by
        rw [hlam, Measure.restrict_apply' hU.measurableSet, inter_eq_left.2 sdiff_subset]
    _ ≤ lam Kᶜ := measure_mono fun x hx hxK => hx.2 (hKΓ hxK)
    _ ≤ μ U / 2 := hKc
/-- Iterated halving on a countable ball cover (Simon Ch. 3, proof of 1.6 "⇐", final iteration):
let `D ⊆ ℝ^{m+1}` be open, `μ(ℝ^{m+1} \ D) = 0` and `μ(K) < ∞` for compact `K ⊆ D`.  If every
open `U` with compact closure `Ū ⊆ D` has a closed countably `m`-rectifiable `Γ` with
`μ(U \ Γ) ≤ μ(U)/2`, then `μ` is carried by a Borel countably `m`-rectifiable set `R`.
For an open `W` with compact closure in `D`, applying the hypothesis to `W \ Γᵢ` gives closed
countably `m`-rectifiable sets `Γᵢ` with `μ(W \ Γᵢ) ≤ 2⁻ⁱ μ(W)`, so `μ(W \ ⋃ᵢ Γᵢ) = 0`; `D` is
covered by countably many balls `B_{r/2}(x)` with `B_r(x) ⊆ D` (Lindelöf), and `R` is the union
of the corresponding sets `⋃ᵢ Γᵢ`. -/
theorem Submission.codim1_rdo_dg_rc_of_halving : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))), IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → (∀ U : Set (Euclid (m + 1)), IsOpen U → IsCompact (closure U) → closure U ⊆ D → ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧ μ (U \ Γ) ≤ μ U / 2) → ∃ R : Set (Euclid (m + 1)), MeasurableSet R ∧ CountablyRectifiable m R ∧ μ Rᶜ = 0 := by
  intro m D μ hDo hDc hfin hhalf
  -- Steps 2–3: on an open set `W` with compact closure in `D`, iterate the halving hypothesis.
  have key : ∀ W : Set (Euclid (m + 1)), IsOpen W → IsCompact (closure W) → closure W ⊆ D →
      ∃ R' : Set (Euclid (m + 1)), MeasurableSet R' ∧ CountablyRectifiable m R' ∧
        μ (W \ R') = 0 := by
    intro W hWo hWc hWD
    have hWfin : μ W ≠ ∞ := ne_top_of_le_ne_top (hfin _ hWc hWD) (measure_mono subset_closure)
    have step : ∀ i : ℕ, ∃ Γ : Set (Euclid (m + 1)), IsClosed Γ ∧ CountablyRectifiable m Γ ∧
        μ (W \ Γ) ≤ μ W * (2⁻¹ : ℝ≥0∞) ^ i := by
      intro i
      induction i with
      | zero =>
        refine ⟨∅, isClosed_empty,
          Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty, ?_⟩
        simp
      | succ i ih =>
        obtain ⟨Γ, hΓc, hΓr, hΓμ⟩ := ih
        have hUo : IsOpen (W \ Γ) := hWo.sdiff hΓc
        have hUcl : closure (W \ Γ) ⊆ closure W := closure_mono sdiff_subset
        obtain ⟨Γ', hΓ'c, hΓ'r, hΓ'μ⟩ :=
          hhalf (W \ Γ) hUo (hWc.of_isClosed_subset isClosed_closure hUcl) (hUcl.trans hWD)
        refine ⟨Γ ∪ Γ', hΓc.union hΓ'c, ?_, ?_⟩
        · rw [← sUnion_pair]
          refine Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion
            (Set.toFinite _).countable ?_
          rintro S (rfl | rfl)
          · exact hΓr
          · exact hΓ'r
        · rw [← Set.sdiff_sdiff]
          calc μ ((W \ Γ) \ Γ') ≤ μ (W \ Γ) / 2 := hΓ'μ
            _ = μ (W \ Γ) * 2⁻¹ := div_eq_mul_inv _ _
            _ ≤ μ W * (2⁻¹ : ℝ≥0∞) ^ i * 2⁻¹ := by gcongr
            _ = μ W * (2⁻¹ : ℝ≥0∞) ^ (i + 1) := by rw [pow_succ, mul_assoc]
    choose Γ hΓc hΓr hΓμ using step
    refine ⟨⋃ i, Γ i, MeasurableSet.iUnion (fun i => (hΓc i).measurableSet),
      Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion Γ hΓr, ?_⟩
    have hlim : Tendsto (fun i : ℕ => μ W * (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i : ℕ => (2⁻¹ : ℝ≥0∞) ^ i) atTop (𝓝 0) :=
        ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hWfin)
    refine nonpos_iff_eq_zero.1 ?_
    refine ge_of_tendsto' hlim (fun i => ?_)
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion Γ i))).trans (hΓμ i)
  -- Step 1: a countable cover of `D` by balls with compact closure inside `D`.
  have hr : ∀ x : Euclid (m + 1), ∃ r : ℝ, 0 < r ∧ (x ∈ D → ball x r ⊆ D) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨r, hr0, hrD⟩ := Metric.isOpen_iff.1 hDo x hx
      exact ⟨r, hr0, fun _ => hrD⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose r hr0 hrD using hr
  let W : Euclid (m + 1) → Set (Euclid (m + 1)) := fun x => ball x (r x / 2)
  have hWcl : ∀ x ∈ D, closure (W x) ⊆ D := fun x hx =>
    closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (half_lt_self (hr0 x))).trans (hrD x hx))
  have hWcpt : ∀ x, IsCompact (closure (W x)) := fun x =>
    (isCompact_closedBall x (r x / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hR : ∀ x : Euclid (m + 1), ∃ R' : Set (Euclid (m + 1)), MeasurableSet R' ∧
      CountablyRectifiable m R' ∧ (x ∈ D → μ (W x \ R') = 0) := by
    intro x
    by_cases hx : x ∈ D
    · obtain ⟨R', h1, h2, h3⟩ := key (W x) isOpen_ball (hWcpt x) (hWcl x hx)
      exact ⟨R', h1, h2, fun _ => h3⟩
    · exact ⟨∅, MeasurableSet.empty,
        Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
        fun h => absurd h hx⟩
  choose Rx hRxm hRxr hRxμ using hR
  obtain ⟨T, hTD, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_biUnion_countable D W (fun x _ => isOpen_ball)
  have hDcov : D ⊆ ⋃ x ∈ T, W x := by
    rw [hTU]
    intro y hy
    exact mem_biUnion hy (mem_ball_self (half_pos (hr0 y)))
  -- Step 4: glue.
  refine ⟨⋃ x ∈ T, Rx x, MeasurableSet.biUnion hTc (fun x _ => hRxm x), ?_, ?_⟩
  · rw [← sUnion_image]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image Rx)
      (by rintro S ⟨x, -, rfl⟩; exact hRxr x)
  · have hsub : (⋃ x ∈ T, Rx x)ᶜ ⊆ Dᶜ ∪ ⋃ x ∈ T, (W x \ Rx x) := by
      intro y hy
      by_cases hyD : y ∈ D
      · right
        obtain ⟨x, hxT, hyW⟩ := mem_iUnion₂.1 (hDcov hyD)
        exact mem_iUnion₂.2 ⟨x, hxT, hyW, fun hyR => hy (mem_iUnion₂.2 ⟨x, hxT, hyR⟩)⟩
      · exact Or.inl hyD
    refine measure_mono_null hsub (measure_union_null hDc ?_)
    exact (measure_biUnion_null_iff hTc).2 (fun x hx => hRxμ x (hTD hx))
/-- **`Hᵐ` of a ball in an `m`-dimensional subspace** (Simon Ch. 3, Remark 1.5(3): `Hᵐ` on an
`m`-plane is `m`-dimensional Lebesgue measure): if `Q ⊆ ℝᴺ` is a linear subspace with
`dim Q = m` and `s > 0`, then `Hᵐ(Q ∩ B_s(0)) = ωₘsᵐ`.  An orthonormal basis of `Q` gives a
linear isometry `ι : ℝᵐ → ℝᴺ` with `ι(B_s(0)) = Q ∩ B_s(0)`; `μHE[m]` is preserved by isometries
and equals `volume` on `ℝᵐ`, where `volume (B_s(0)) = sᵐωₘ`. -/
theorem Submission.codim1_rdo_dg_ftd_plane_ball_measure : ∀ (N m : ℕ) (Q : Submodule ℝ (Euclid N)), Module.finrank ℝ Q = m → ∀ s : ℝ, 0 < s → μHE[m] ((Q : Set (Euclid N)) ∩ ball 0 s) = unitBallVolume m * ENNReal.ofReal (s ^ m) := by
  intro N m Q hm s hs
  -- Step 1: the coordinates of an orthonormal basis of `Q` indexed by `Fin m` give
  -- `e : Q ≃ₗᵢ ℝᵐ`, and `ι = e⁻¹` followed by `Q ↪ ℝᴺ` is a linear isometry with values in `Q`
  let e : Q ≃ₗᵢ[ℝ] Euclid m := ((stdOrthonormalBasis ℝ Q).reindex (finCongr hm)).repr
  let ι : Euclid m →ₗᵢ[ℝ] Euclid N := Q.subtypeₗᵢ.comp e.symm.toLinearIsometry
  have hι : ∀ a, ι a = (e.symm a : Euclid N) := fun a => rfl
  -- Step 2: `ι(B_s(0)) = Q ∩ B_s(0)`
  have himage : ι '' ball 0 s = (Q : Set (Euclid N)) ∩ ball 0 s := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨by rw [hι]; exact (e.symm a).2, ?_⟩
      rw [mem_ball_zero_iff] at ha ⊢
      rwa [LinearIsometry.norm_map]
    · rintro ⟨hz, hzs⟩
      refine ⟨e ⟨z, hz⟩, ?_, by rw [hι, LinearIsometryEquiv.symm_apply_apply]⟩
      rw [mem_ball_zero_iff] at hzs ⊢
      rwa [LinearIsometryEquiv.norm_map]
  -- Steps 3–5: isometry invariance of `μHE[m]`, `μHE[m] = volume` on `ℝᵐ`, Haar scaling of balls
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos (volume : Measure (Euclid m)) 0 hs, finrank_euclideanSpace_fin,
    unitBallVolume]
  -- Step 6: commute the product
  exact mul_comm _ _
/-- **Markov bound for rescaled measures** (the measure-theoretic half of the flat-tangent
density estimate): if `f ≥ 0` is continuous with compact support, `f ≥ 1` on `A`,
`μ(B̄_{r₀}(y)) < ∞`, and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → L < L'` as `r ↓ 0`, then
`μ{z : r⁻¹(z − y) ∈ A} ≤ L' rᵐ` for all small `r > 0`.  Once `r R' < r₀`, where `f = 0` off
`B̄_{R'}(0)`, the rescaled integrand is bounded and vanishes off `B̄_{r₀}(y)`, hence integrable,
and Markov's inequality at level `1` bounds the (possibly non-measurable) set by its integral. -/
theorem Submission.codim1_rdo_dg_ftd_test_upper_bound : ∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → Continuous f → HasCompactSupport f → (∀ w, 0 ≤ f w) → (∀ w ∈ A, 1 ≤ f w) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L < L' → ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {z | r⁻¹ • (z - y) ∈ A} ≤ ENNReal.ofReal (L' * r ^ m) := by
  intro N m μ y f A L L' ⟨r₀, hr₀, hfin⟩ hf hfc hf0 hA hlim hLL'
  -- a radius `R' > 0` outside of which `f` vanishes, and a bound `‖f‖ ≤ C`
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R', hR'pos, hzero⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ w : Euclid N, R' < ‖w‖ → f w = 0 := by
    refine ⟨max R 1, lt_max_of_lt_right one_pos, fun w hw => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hws => ?_
    have hwR := hR hws
    rw [mem_closedBall, dist_zero_right] at hwR
    linarith [le_max_left R 1]
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  -- eventually `r < r₀ / R'` and the rescaled integral is `< L'`
  filter_upwards [hlim (Iio_mem_nhds hLL'), Ioo_mem_nhdsGT (div_pos hr₀ hR'pos)] with r hrL hr
  have hr0 : 0 < r := hr.1
  have hrR : r * R' < r₀ := (lt_div_iff₀ hR'pos).mp hr.2
  -- `z ↦ f (r⁻¹ • (z - y))` is continuous, bounded, and vanishes off `closedBall y r₀`
  have hgc : Continuous fun z => f (r⁻¹ • (z - y)) :=
    hf.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
  have hgint : Integrable (fun z => f (r⁻¹ • (z - y))) μ := by
    have hball : IntegrableOn (fun z => f (r⁻¹ • (z - y))) (closedBall y r₀) μ :=
      Measure.integrableOn_of_bounded (M := C) hfin hgc.aestronglyMeasurable
        (Eventually.of_forall fun z => hC _)
    refine integrableOn_univ.mp (hball.of_forall_sdiff_eq_zero MeasurableSet.univ fun z hz => ?_)
    have hz' : r₀ < ‖z - y‖ := by
      have hz2 := hz.2
      rwa [mem_closedBall, dist_eq_norm, not_le] at hz2
    apply hzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, lt_inv_mul_iff₀ hr0]
    linarith
  -- Markov's inequality at level `1`
  have hmarkov : μ {z | r⁻¹ • (z - y) ∈ A} ≤ ENNReal.ofReal (∫ z, f (r⁻¹ • (z - y)) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall fun z => hf0 _)]
    calc μ {z | r⁻¹ • (z - y) ∈ A}
        ≤ μ {z | 1 ≤ ENNReal.ofReal (f (r⁻¹ • (z - y)))} :=
          measure_mono fun z hz => ENNReal.one_le_ofReal.mpr (hA _ hz)
      _ = 1 * μ {z | 1 ≤ ENNReal.ofReal (f (r⁻¹ • (z - y)))} := (one_mul _).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ :=
          mul_meas_ge_le_lintegral₀ hgc.measurable.ennreal_ofReal.aemeasurable 1
  refine hmarkov.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint := (inv_mul_lt_iff₀ (pow_pos hr0 m)).mp hrL
  rw [mul_comm L']
  exact hint.le
/-- **Lower bound for rescaled measures from a test function** (the lower half of the
flat-tangent density estimate): if `f` is continuous, `0 ≤ f ≤ 1`, `f = 0` off `A`, and
`r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → L > L'` as `r ↓ 0`, then `L' rᵐ ≤ μ{z : r⁻¹(z − y) ∈ A}` for all
small `r > 0`.  The rescaled integrand is dominated by the indicator of the (possibly
non-measurable) set, and a non-integrable integrand has Bochner integral `0`. -/
theorem Submission.codim1_rdo_dg_ftd_test_lower_bound : ∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), Continuous f → (∀ w, 0 ≤ f w) → (∀ w, f w ≤ 1) → (∀ w, w ∉ A → f w = 0) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L' < L → ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (L' * r ^ m) ≤ μ {z | r⁻¹ • (z - y) ∈ A} := by
  intro N m μ y f A L L' hf hf0 hf1 hfA hlim hLL'
  -- eventually `r > 0` and the rescaled integral exceeds `L'`
  filter_upwards [hlim (Ioi_mem_nhds hLL'), self_mem_nhdsWithin] with r hrL hr
  have hint : L' * r ^ m < ∫ z, f (r⁻¹ • (z - y)) ∂μ :=
    (lt_inv_mul_iff₀' (pow_pos hr m)).mp hrL
  -- `ofReal (∫ g) ≤ ∫⁻ ofReal g`: equality if `g` is integrable, otherwise `∫ g = 0`
  have hlint : ENNReal.ofReal (∫ z, f (r⁻¹ • (z - y)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ := by
    by_cases hg : Integrable (fun z => f (r⁻¹ • (z - y))) μ
    · exact (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall fun z => hf0 _)).le
    · rw [integral_undef hg, ENNReal.ofReal_zero]
      exact zero_le
  -- `ofReal g ≤ 1_{S_r}` pointwise, and `∫⁻ 1_{S_r} dμ ≤ μ S_r` for any set `S_r`
  have hind : ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ ≤
      ∫⁻ z, {z | r⁻¹ • (z - y) ∈ A}.indicator 1 z ∂μ := by
    refine lintegral_mono fun z => ?_
    show ENNReal.ofReal (f (r⁻¹ • (z - y))) ≤ {z | r⁻¹ • (z - y) ∈ A}.indicator 1 z
    by_cases hz : r⁻¹ • (z - y) ∈ A
    · rw [indicator_of_mem (show z ∈ {z | r⁻¹ • (z - y) ∈ A} from hz), Pi.one_apply]
      exact ENNReal.ofReal_le_one.mpr (hf1 _)
    · rw [hfA _ hz, ENNReal.ofReal_zero]
      exact zero_le
  exact (ENNReal.ofReal_le_ofReal hint.le).trans
    (hlint.trans (hind.trans (lintegral_indicator_one_le _)))

/-- **Ball densities of a measure with a flat tangent measure** (Simon Ch. 3, Remark 1.5(3),
first assertion, for `μ` in place of `Hⁿ⌞M`): if `P = v^⊥` (`‖v‖ = 1`), `μ(B̄_{r₀}(y)) < ∞`
and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → ∫_P f dHᵐ` as `r ↓ 0` for every continuous compactly
supported `f`, then `μ(B̄_r(y))/(ωₘrᵐ) → 1` and `μ(B_r(y))/(ωₘrᵐ) → 1`.  Since
`Hᵐ(P ∩ B_s(0)) = ωₘsᵐ`, the radial cutoffs `f₊ = 1` on `B̄₁(0)`, `= 0` off `B_{1+ε}(0)`, and
`f₋ = 1` on `B̄_{1−ε}(0)`, `= 0` off `B₁(0)`, have `∫_P f₊ ≤ ωₘ(1 + ε)ᵐ` and
`∫_P f₋ ≥ ωₘ(1 − ε)ᵐ`; the Markov-type bounds for rescaled measures then give
`ωₘcrᵐ ≤ μ(B_r(y)) ≤ μ(B̄_r(y)) ≤ ωₘCrᵐ` for small `r > 0`, for any `c < 1 < C`. -/
theorem Submission.codim1_rdo_dg_ftd_ball_density : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ (ball y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) := by
  intro m μ y v _hm hv hr₀ hlim
  -- Step 0(a): `P = v^⊥` is an `m`-dimensional subspace of `ℝ^{m+1}`
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hv
    exact zero_ne_one hv
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hPdim : Module.finrank ℝ (Submodule.span ℝ {v})ᗮ = m :=
    Submodule.finrank_orthogonal_span_singleton hv0
  -- Step 0(b): `ωₘ = ofReal ω` with `ω > 0`
  have hω0 : unitBallVolume m ≠ 0 := by
    rw [unitBallVolume]
    exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume m ≠ ∞ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top.ne
  obtain ⟨ω, hωpos, hωeq⟩ : ∃ ω : ℝ, 0 < ω ∧ unitBallVolume m = ENNReal.ofReal ω :=
    ⟨(unitBallVolume m).toReal, ENNReal.toReal_pos hω0 hωtop, (ENNReal.ofReal_toReal hωtop).symm⟩
  -- Step 0(c): `ν = Hᵐ⌞P` gives `B_s(0)` the measure `ω sᵐ`
  set ν : Measure (Euclid (m + 1)) :=
    μHE[m].restrict ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))) with hν
  have hνball : ∀ s : ℝ, 0 < s → ν (ball 0 s) = ENNReal.ofReal (ω * s ^ m) := by
    intro s hs
    rw [hν, Measure.restrict_apply measurableSet_ball, inter_comm,
      Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m _ hPdim s hs, hωeq,
      ENNReal.ofReal_mul hωpos.le]
  have hνint : ∀ s : ℝ, 0 < s →
      Integrable ((ball (0 : Euclid (m + 1)) s).indicator fun _ => (1 : ℝ)) ν := by
    intro s hs
    have hfin : ν (ball 0 s) ≠ ∞ := by
      rw [hνball s hs]
      exact ENNReal.ofReal_ne_top
    exact (integrableOn_const hfin).integrable_indicator measurableSet_ball
  have hνind : ∀ s : ℝ, 0 < s →
      ∫ w, (ball (0 : Euclid (m + 1)) s).indicator (fun _ => (1 : ℝ)) w ∂ν = ω * s ^ m := by
    intro s hs
    rw [integral_indicator_const _ measurableSet_ball, measureReal_def, hνball s hs,
      ENNReal.toReal_ofReal (mul_pos hωpos (pow_pos hs m)).le, smul_eq_mul, mul_one]
  -- Step 1: comparison of `I(g) = ∫_P g dHᵐ` with plane balls
  have hle_ind : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), (∀ w, g w ≤ 1) →
      (∀ w, b ≤ ‖w‖ → g w = 0) →
      ∀ w, g w ≤ (ball (0 : Euclid (m + 1)) b).indicator (fun _ => (1 : ℝ)) w := by
    intro b g hg1 hgb w
    by_cases hw : w ∈ ball (0 : Euclid (m + 1)) b
    · rw [indicator_of_mem hw]
      exact hg1 w
    · rw [indicator_of_notMem hw, hgb w (not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h))]
  have hgint : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < b → Continuous g → (∀ w, 0 ≤ g w) →
      (∀ w, g w ≤ 1) → (∀ w, b ≤ ‖w‖ → g w = 0) → Integrable g ν := by
    intro b g hb hg hg0 hg1 hgb
    refine (hνint b hb).mono' hg.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 w)]
    exact hle_ind b g hg1 hgb w
  -- (U) `I(g) ≤ ω bᵐ` if `0 ≤ g ≤ 1` vanishes off `B_b(0)`
  have hplane_le : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < b → Continuous g →
      (∀ w, 0 ≤ g w) → (∀ w, g w ≤ 1) → (∀ w, b ≤ ‖w‖ → g w = 0) →
      ∫ w, g w ∂ν ≤ ω * b ^ m := fun b g hb hg hg0 hg1 hgb =>
    (integral_mono (hgint b g hb hg hg0 hg1 hgb) (hνint b hb) (hle_ind b g hg1 hgb)).trans_eq
      (hνind b hb)
  -- (L) `ω aᵐ ≤ I(g)` if moreover `g ≥ 1` on `B_a(0)`
  have hplane_ge : ∀ (a b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < a → 0 < b → Continuous g →
      (∀ w, 0 ≤ g w) → (∀ w, g w ≤ 1) → (∀ w, ‖w‖ < a → 1 ≤ g w) →
      (∀ w, b ≤ ‖w‖ → g w = 0) → ω * a ^ m ≤ ∫ w, g w ∂ν := by
    intro a b g ha hb hg hg0 hg1 hga hgb
    refine (hνind a ha).symm.trans_le
      (integral_mono (hνint a ha) (hgint b g hb hg hg0 hg1 hgb) fun w => ?_)
    by_cases hw : w ∈ ball (0 : Euclid (m + 1)) a
    · rw [indicator_of_mem hw]
      exact hga w (mem_ball_zero_iff.mp hw)
    · rw [indicator_of_notMem hw]
      exact hg0 w
  -- Step 2: the radial cutoff `g_{a,b} = min 1 (max 0 ((b − ‖w‖)/(b − a)))`
  have hcut : ∀ a b : ℝ, a < b → ∃ g : Euclid (m + 1) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ w, 0 ≤ g w) ∧ (∀ w, g w ≤ 1) ∧ (∀ w, ‖w‖ ≤ a → g w = 1) ∧
      (∀ w, b ≤ ‖w‖ → g w = 0) := by
    intro a b hab
    have hba : 0 < b - a := sub_pos.mpr hab
    have hzero : ∀ w : Euclid (m + 1), b ≤ ‖w‖ → min 1 (max 0 ((b - ‖w‖) / (b - a))) = 0 := by
      intro w hw
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le),
        min_eq_right zero_le_one]
    refine ⟨fun w => min 1 (max 0 ((b - ‖w‖) / (b - a))), by fun_prop, ?_,
      fun w => le_min zero_le_one (le_max_left _ _), fun w => min_le_left _ _, fun w hw => ?_,
      hzero⟩
    · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) b)
        fun w hw => hzero w ?_
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw.le
    · have h1 : 1 ≤ (b - ‖w‖) / (b - a) := by
        rw [le_div_iff₀ hba]
        linarith
      show min 1 (max 0 ((b - ‖w‖) / (b - a))) = 1
      rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  -- Step 3: `{z : r⁻¹(z − y) ∈ B̄₁(0)} = B̄_r(y)` and `{z : r⁻¹(z − y) ∈ B₁(0)} = B_r(y)`
  have hset_closed : ∀ r : ℝ, 0 < r →
      {z | r⁻¹ • (z - y) ∈ closedBall (0 : Euclid (m + 1)) 1} = closedBall y r := by
    intro r hr
    ext z
    change r⁻¹ • (z - y) ∈ closedBall (0 : Euclid (m + 1)) 1 ↔ z ∈ closedBall y r
    rw [mem_closedBall_zero_iff, mem_closedBall_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_le_iff₀ hr, mul_one]
  have hset_open : ∀ r : ℝ, 0 < r →
      {z | r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) 1} = ball y r := by
    intro r hr
    ext z
    change r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) 1 ↔ z ∈ ball y r
    rw [mem_ball_zero_iff, mem_ball_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
  -- Step 4: for `C > 1`, eventually `μ(B̄_r(y)) ≤ ω C rᵐ` (test with `f₊ = g_{1,1+ε}`)
  have hupper : ∀ C : ℝ, 1 < C →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall y r) ≤ ENNReal.ofReal (ω * C * r ^ m) := by
    intro C hC
    have hcont : Continuous fun t : ℝ => (1 + t) ^ m := by fun_prop
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 + t) ^ m < C :=
      ((hcont.tendsto' 0 1 (by simp)).eventually (gt_mem_nhds hC)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨ε, hεC, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨g, hgc, hgcs, hg0, hg1, hgone, hgzero⟩ :=
      hcut 1 (1 + ε) (lt_add_of_pos_right 1 hε0)
    have hI : ∫ w, g w ∂ν < ω * C :=
      (hplane_le (1 + ε) g (by linarith) hgc hg0 hg1 hgzero).trans_lt
        (mul_lt_mul_of_pos_left hεC hωpos)
    filter_upwards [Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y g
      (closedBall 0 1) _ (ω * C) hr₀ hgc hgcs hg0
      (fun w hw => (hgone w (mem_closedBall_zero_iff.mp hw)).ge) (hlim g hgc hgcs) hI,
      self_mem_nhdsWithin] with r hr hrpos
    rwa [hset_closed r hrpos] at hr
  -- Step 5: for `c < 1`, eventually `ω c rᵐ ≤ μ(B_r(y))` (test with `f₋ = g_{1−ε,1}`)
  have hlower : ∀ c : ℝ, c < 1 →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (ω * c * r ^ m) ≤ μ (ball y r) := by
    intro c hc
    have hcont : Continuous fun t : ℝ => (1 - t) ^ m := by fun_prop
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), c < (1 - t) ^ m :=
      ((hcont.tendsto' 0 1 (by simp)).eventually (lt_mem_nhds hc)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨ε, hεc, hε⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
    have hε0 : (0 : ℝ) < ε := hε.1
    have hε1 : ε < 1 := hε.2
    obtain ⟨g, hgc, hgcs, hg0, hg1, hgone, hgzero⟩ := hcut (1 - ε) 1 (by linarith)
    have hI : ω * c < ∫ w, g w ∂ν :=
      (mul_lt_mul_of_pos_left hεc hωpos).trans_le
        (hplane_ge (1 - ε) 1 g (by linarith) one_pos hgc hg0 hg1
          (fun w hw => (hgone w hw.le).ge) hgzero)
    filter_upwards [Submission.codim1_rdo_dg_ftd_test_lower_bound (m + 1) m μ y g
      (ball 0 1) _ (ω * c) hgc hg0 hg1
      (fun w hw => hgzero w (not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h)))
      (hlim g hgc hgcs) hI, self_mem_nhdsWithin] with r hr hrpos
    rwa [hset_open r hrpos] at hr
  -- Step 6: `ofReal (ω c rᵐ) / (ωₘ rᵐ) = ofReal c`
  have hratio : ∀ c : ℝ, 0 ≤ c → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (ω * c * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) =
        ENNReal.ofReal c := by
    intro c hc r hr
    have hden0 : unitBallVolume m * ENNReal.ofReal (r ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
    have hdentop : unitBallVolume m * ENNReal.ofReal (r ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    rw [show ω * c * r ^ m = c * (ω * r ^ m) by ring, ENNReal.ofReal_mul hc,
      ENNReal.ofReal_mul hωpos.le, ← hωeq, ENNReal.mul_div_cancel_right hden0 hdentop]
  -- Step 7: squeeze between `B_r(y)` and `B̄_r(y)` in the order topology of `[0, ∞]`
  have hsqueeze : ∀ F : ℝ → Set (Euclid (m + 1)), (∀ r, ball y r ⊆ F r) →
      (∀ r, F r ⊆ closedBall y r) →
      Tendsto (fun r : ℝ => μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0)
        (𝓝 1) := by
    intro F hF1 hF2
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨c, hc0, hac, hc1⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
      filter_upwards [hlower c (ENNReal.ofReal_lt_one.mp hc1), self_mem_nhdsWithin]
        with r hr hrpos
      calc a < ENNReal.ofReal c := hac
        _ = ENNReal.ofReal (ω * c * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
          (hratio c hc0 r hrpos).symm
        _ ≤ μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
          ENNReal.div_le_div_right (hr.trans (measure_mono (hF1 r))) _
    · obtain ⟨C, hC0, h1C, hCb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
      filter_upwards [hupper C (ENNReal.one_lt_ofReal.mp h1C), self_mem_nhdsWithin]
        with r hr hrpos
      calc μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))
          ≤ ENNReal.ofReal (ω * C * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
            ENNReal.div_le_div_right ((measure_mono (hF2 r)).trans hr) _
        _ = ENNReal.ofReal C := hratio C hC0 r hrpos
        _ < b := hCb
  exact ⟨hsqueeze (closedBall y) (fun _ => ball_subset_closedBall) (fun _ => subset_rfl),
    hsqueeze (ball y) (fun _ => subset_rfl) (fun _ => ball_subset_closedBall)⟩

/-- **The double cone around the normal has density zero** (Simon Ch. 3, Remark 1.5(3), second
assertion): if `‖v‖ = 1`, `P = v^⊥`, `μ(B̄_{r₀}(y)) < ∞` and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → ∫_P f dHᵐ`
as `r ↓ 0` for every continuous compactly supported `f`, then for every `α > 0`
`μ({z : α‖z − y‖ ≤ |⟨z − y, v⟩|} ∩ B̄_r(y)) / rᵐ → 0` (`m ≥ 1`).  With
`K = {w : α‖w‖ ≤ |⟨w, v⟩|} ∩ B̄₁(0)`, the test function `g = (1 − dist(·, K)/θ)⁺` is `1` on `K` and
vanishes at points of `P` outside `B_{θ(1+1/α)}(0)`, so `∫_P g dHᵐ ≤ ωₘ(θ(1 + 1/α))ᵐ`; the Markov
bound then gives `μ(cone ∩ B̄_r(y)) ≤ (ωₘ(θ(1 + 1/α))ᵐ + θ) rᵐ` for small `r`, and `θ ↓ 0`. -/
theorem Submission.codim1_rdo_dg_ftd_cone_density : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → ∀ α : ℝ, 0 < α → Tendsto (fun r : ℝ => μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
  intro m μ y v hm hv hfin hconv α hα
  -- Step 0: `P = v^⊥` is a closed `m`-dimensional subspace, and `(Hᵐ⌞P)(B_s(0)) = ωₘ sᵐ`
  set P : Submodule ℝ (Euclid (m + 1)) := (Submodule.span ℝ {v})ᗮ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hv
    exact zero_ne_one hv
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hPdim : Module.finrank ℝ P = m := Submodule.finrank_orthogonal_span_singleton hv0
  have hPmeas : MeasurableSet (P : Set (Euclid (m + 1))) :=
    P.closed_of_finiteDimensional.measurableSet
  have hωfin : unitBallVolume m ≠ ∞ := measure_ball_lt_top.ne
  set ω : ℝ := (unitBallVolume m).toReal
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hωeq : unitBallVolume m = ENNReal.ofReal ω := (ENNReal.ofReal_toReal hωfin).symm
  have hball : ∀ s : ℝ, 0 < s →
      μHE[m].restrict (P : Set (Euclid (m + 1))) (ball 0 s) = ENNReal.ofReal (ω * s ^ m) := by
    intro s hs
    rw [Measure.restrict_apply measurableSet_ball, inter_comm,
      Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m P hPdim s hs, hωeq,
      ← ENNReal.ofReal_mul hω0]
  -- Step 8: it suffices to bound the ratio eventually by each `ε ∈ (0, ∞)`
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact Eventually.of_forall fun r => hεtop ▸ le_top
  have ht : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  -- since `m ≥ 1`, `ωₘ(θ(1 + α⁻¹))ᵐ + θ → 0` as `θ → 0`; pick `θ > 0` with this `< ε`
  have hφ : Tendsto (fun θ : ℝ => ω * (θ * (1 + α⁻¹)) ^ m + θ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun θ : ℝ => ω * (θ * (1 + α⁻¹)) ^ m + θ := by fun_prop
    have h0 := hc.tendsto 0
    rw [zero_mul, zero_pow (by omega), mul_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  obtain ⟨θ, hθt, hθmem⟩ := ((hφ.eventually (gt_mem_nhds ht)).and self_mem_nhdsWithin).exists
  have hθ : 0 < θ := hθmem
  set ρ : ℝ := θ * (1 + α⁻¹) with hρ
  have hρpos : 0 < ρ := mul_pos hθ (add_pos one_pos (inv_pos.mpr hα))
  -- Step 1: the cone `K` in the closed unit ball contains `0`
  set K : Set (Euclid (m + 1)) := {w | α * ‖w‖ ≤ |inner ℝ w v|} ∩ closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  -- Step 2: `g = (1 − dist(·, K)/θ)⁺` is continuous, `0 ≤ g ≤ 1`, `g = 1` on `K`, and `g(w) ≠ 0`
  -- forces `dist(w, k) < θ` for some `k ∈ K`
  set g : Euclid (m + 1) → ℝ := fun w => max 0 (1 - infDist w K / θ)
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const θ))
  have hg0 : ∀ w, 0 ≤ g w := fun w => le_max_left _ _
  have hg1 : ∀ w, g w ≤ 1 := fun w =>
    max_le zero_le_one (by linarith [div_nonneg (infDist_nonneg (x := w) (s := K)) hθ.le])
  have hgK : ∀ w ∈ K, 1 ≤ g w := fun w hw =>
    le_max_of_le_right (by rw [infDist_zero_of_mem hw, zero_div, sub_zero])
  have hgne : ∀ w, g w ≠ 0 → ∃ k ∈ K, dist w k < θ := by
    intro w hw
    rw [← infDist_lt_iff hKne]
    by_contra hcon
    have h1 : 1 ≤ infDist w K / θ := by
      rw [le_div_iff₀ hθ, one_mul]
      exact not_lt.mp hcon
    exact hw (max_eq_left (by linarith))
  -- Step 3: `g` vanishes outside `B̄_{1+θ}(0)`, so it has compact support
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) (1 + θ))
      fun w hw => ?_
    by_contra hne
    obtain ⟨k, hk, hwk⟩ := hgne w hne
    rw [dist_eq_norm] at hwk
    have hk1 : ‖k‖ ≤ 1 := mem_closedBall_zero_iff.mp hk.2
    apply hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ = ‖(w - k) + k‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - k‖ + ‖k‖ := norm_add_le _ _
      _ ≤ 1 + θ := by linarith
  -- Step 4: on `P`, `g(w) ≠ 0` forces `‖w‖ < ρ = θ(1 + α⁻¹)` (Cauchy–Schwarz, `⟨w, v⟩ = 0`)
  have hgP : ∀ w ∈ P, ρ ≤ ‖w‖ → g w = 0 := by
    intro w hwP hwρ
    by_contra hne
    obtain ⟨k, hk, hwk⟩ := hgne w hne
    rw [dist_eq_norm] at hwk
    have hwv : inner ℝ w v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hwP
    have hαk : α * ‖k‖ < θ :=
      calc α * ‖k‖ ≤ |inner ℝ k v| := hk.1
        _ = |inner ℝ (k - w) v| := by rw [inner_sub_left, hwv, sub_zero]
        _ ≤ ‖k - w‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖w - k‖ := by rw [hv, mul_one, norm_sub_rev]
        _ < θ := hwk
    have hkθ : ‖k‖ < θ * α⁻¹ := by
      rw [← div_eq_mul_inv, lt_div_iff₀ hα]
      linarith
    have hwρ' : ‖w‖ < ρ :=
      calc ‖w‖ = ‖(w - k) + k‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - k‖ + ‖k‖ := norm_add_le _ _
        _ < θ + θ * α⁻¹ := add_lt_add hwk hkθ
        _ = ρ := by rw [hρ]; ring
    linarith
  -- Step 5: `∫_P g dHᵐ ≤ ∫_P 1_{B_ρ(0)} dHᵐ = ωₘ ρᵐ`
  have hIg : ∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m] ≤ ω * ρ ^ m := by
    have hint : Integrable ((ball (0 : Euclid (m + 1)) ρ).indicator (1 : Euclid (m + 1) → ℝ))
        (μHE[m].restrict (P : Set (Euclid (m + 1)))) := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact integrableOn_const (by rw [hball ρ hρpos]; exact ENNReal.ofReal_ne_top)
    calc ∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m]
        ≤ ∫ z in (P : Set (Euclid (m + 1))),
            (ball (0 : Euclid (m + 1)) ρ).indicator 1 z ∂μHE[m] := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w => hg0 w) hint ?_
          rw [EventuallyLE, ae_restrict_iff' hPmeas]
          refine Eventually.of_forall fun w hwP => ?_
          by_cases hwb : w ∈ ball (0 : Euclid (m + 1)) ρ
          · rw [indicator_of_mem hwb, Pi.one_apply]
            exact hg1 w
          · rw [indicator_of_notMem hwb, hgP w hwP (by rwa [mem_ball_zero_iff, not_lt] at hwb)]
      _ = ω * ρ ^ m := by
          rw [integral_indicator_one measurableSet_ball, measureReal_def, hball ρ hρpos,
            ENNReal.toReal_ofReal (mul_nonneg hω0 (pow_nonneg hρpos.le m))]
  -- Step 6: the Markov bound for `g` and `K`, with `L' = ωₘ ρᵐ + θ`
  have hev := Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y g K
    (∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m]) (ω * ρ ^ m + θ) hfin hgc hgcs hg0 hgK
    (hconv g hgc hgcs) (by linarith)
  -- Steps 7–8: the cone in `B̄_r(y)` rescales into `K`, so the ratio is eventually `≤ ε`
  filter_upwards [hev, self_mem_nhdsWithin] with r hr hrmem
  have hr0 : 0 < r := hrmem
  have hincl : {z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r ⊆
      {z | r⁻¹ • (z - y) ∈ K} := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨?_, ?_⟩
    · show α * ‖r⁻¹ • (z - y)‖ ≤ |inner ℝ (r⁻¹ • (z - y)) v|
      rw [norm_smul, real_inner_smul_left, abs_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      calc α * (r⁻¹ * ‖z - y‖) = r⁻¹ * (α * ‖z - y‖) := by ring
        _ ≤ r⁻¹ * |inner ℝ (z - y) v| := mul_le_mul_of_nonneg_left hz1 (inv_nonneg.mpr hr0.le)
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0,
        inv_mul_le_iff₀ hr0, mul_one]
      rwa [mem_closedBall, dist_eq_norm] at hz2
  refine ENNReal.div_le_of_le_mul ?_
  calc μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r)
      ≤ μ {z | r⁻¹ • (z - y) ∈ K} := measure_mono hincl
    _ ≤ ENNReal.ofReal ((ω * ρ ^ m + θ) * r ^ m) := hr
    _ ≤ ENNReal.ofReal (ε.toReal * r ^ m) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hθt.le (pow_nonneg hr0.le m))
    _ = ε * ENNReal.ofReal (r ^ m) := by
        rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hεtop]

/-- **A flat tangent measure gives density one and the cone condition** (Simon Ch. 3,
Remark 1.5(3), applied to `μ`): if `μ(B̄_{r₀}(y)) < ∞` and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) →
∫_P f dHᵐ` as `r ↓ 0` for every continuous compactly supported `f`, where `P = (span{v})^⊥` and
`|v| = 1`, then `μ(B̄_r(y))/(ωₘrᵐ) → 1`, `μ(B_r(y))/(ωₘrᵐ) → 1`, and
`μ({z : α|z − y| ≤ |⟨z − y, v⟩|} ∩ B̄_r(y))/rᵐ → 0` for every `α > 0`.  The ball densities
sandwich `1_{B̄₁}` between continuous cut-offs; the cone test function
`(1 − dist(·, K_α)/θ)⁺` lives in `B_{θ(1+1/α)}` on `P`. -/
theorem Submission.codim1_rdo_dg_flat_tangent_density_cone : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ (ball y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ ∀ α : ℝ, 0 < α → Tendsto (fun r : ℝ => μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
  intro m μ y v hm hv hfin hconv
  -- Step 2: closed and open ball densities tend to `1`
  obtain ⟨hclosed, hopen⟩ := Submission.codim1_rdo_dg_ftd_ball_density m μ y v hm hv hfin hconv
  -- Step 3: for every `α > 0` the cone `{α|z − y| ≤ |⟨z − y, v⟩|}` has density `0`
  exact ⟨hclosed, hopen, Submission.codim1_rdo_dg_ftd_cone_density m μ y v hm hv hfin hconv⟩

/-- **Rectifiability from flat tangent measures** (Simon Ch. 3, 1.6 "⇐" in codimension one).
Let `μ` be carried by the open set `D` and finite on its compact subsets. Suppose that at
`μ`-a.e. `y` the blow-ups `r⁻ᵐ μ(y + r ·)` converge to `Hᵐ⌞ν(y)^⊥`, for a Borel unit vector
field `ν`. Then `μ` is carried by a Borel countably `m`-rectifiable set.
Almost every `y` lies in `D`, so `μ(B̄_{r/2}(y)) < ∞` for any ball `B_r(y) ⊆ D`. Hence
`flat_tangent_density` gives (5) density one and (6) `μ(X_{1/4}(ν(y), y) ∩ B̄_ρ(y)) = o(ρᵐ)`.
These are the hypotheses of the halving step (★), and iterating (★) (`of_halving`) gives `R`. -/
theorem Submission.codim1_rdo_dg_rectifiable_of_flat_tangent : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), 1 ≤ m → IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, ∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → ∃ R : Set (Euclid (m + 1)), MeasurableSet R ∧ CountablyRectifiable m R ∧ μ Rᶜ = 0 := by
  intro m D μ ν hm hD hDc hK hν hν1 hflat
  -- step 1: (5) and (6) at `μ`-a.e. `y`; such `y` lie in `D`, where `μ` is finite on small balls
  have hdens : ∀ᵐ y ∂μ,
      Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)))
        (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun r : ℝ => μ ({z | (1 / 4 : ℝ) * ‖z - y‖ ≤ |inner ℝ (z - y) (ν y)|} ∩
        closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hflat, mem_ae_iff.2 hDc] with y hy hyD
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD y hyD
    have hfin : μ (closedBall y (r / 2)) ≠ ∞ :=
      hK _ (isCompact_closedBall y (r / 2)) ((closedBall_subset_ball (half_lt_self hr)).trans hrD)
    obtain ⟨h5, -, h6⟩ := Submission.codim1_rdo_dg_flat_tangent_density_cone m μ y (ν y) hm
      (hν1 y) ⟨r / 2, half_pos hr, hfin⟩ hy
    exact ⟨h5, h6 (1 / 4) (by norm_num)⟩
  -- steps 2–6: the halving step (★) for open `U ⋐ D`; step 0: iterate (★) over balls in `D`
  exact Submission.codim1_rdo_dg_rc_of_halving m D μ hD hDc hK
    (Submission.codim1_rdo_dg_rc_halving_step m D μ ν hK hν hν1 hdens)
/-- **Simon Ch. 3, Lemma 1.2** (the inverse-function step of the "only if" part): if `G` is `C¹`
and `DG(x)` is injective, then `μ |a − b| ≤ |G(a) − G(b)|` on some ball `B_δ(x)`.  With
`|v| ≤ K |DG(x) v|` and `μ = 1/(2K)`, strict differentiability gives
`|G(a) − G(b) − DG(x)(a − b)| ≤ μ |a − b|` near `x`, so `|G(a) − G(b)| ≥ 2μ|a − b| − μ|a − b|`. -/
theorem Submission.codim1_rdo_c1cov_local_lower_lipschitz : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖ := by
  intro P n G x hG hinj
  -- `L = DG(x)` is injective on the finite-dimensional `ℝⁿ`: `‖v‖ ≤ K ‖L v‖`
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hbound : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ G x v‖ :=
    (fderiv ℝ G x).bound_of_antilipschitz hKL
  -- `μ = 1/(2K)`, so `‖L v‖ ≥ 2μ ‖v‖`
  set μ : ℝ := (2 * K)⁻¹ with hμ
  have hK' : (0 : ℝ) < K := hK
  have hμ0 : 0 < μ := by positivity
  -- `G` is `C¹`, so `L` is a strict derivative: `G` approximates `L` with constant `μ` near `x`
  obtain ⟨s, hs, hGs⟩ := (hG.contDiffAt.hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
    (c := ⟨μ, hμ0.le⟩) (Or.inr hμ0)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, μ, hδ, hμ0, fun a ha b hb => ?_⟩
  have h1 : ‖G a - G b - fderiv ℝ G x (a - b)‖ ≤ μ * ‖a - b‖ := hGs a (hδs ha) b (hδs hb)
  have h2 : 2 * μ * ‖a - b‖ ≤ ‖fderiv ℝ G x (a - b)‖ := by
    calc 2 * μ * ‖a - b‖ ≤ 2 * μ * (K * ‖fderiv ℝ G x (a - b)‖) := by
          gcongr
          exact hbound (a - b)
      _ = ‖fderiv ℝ G x (a - b)‖ := by
          rw [hμ]
          field_simp
  -- triangle inequality: `‖L (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - L (a - b)‖`
  have h3 : ‖fderiv ℝ G x (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - fderiv ℝ G x (a - b)‖ := by
    simpa using norm_sub_le (G a - G b) (G a - G b - fderiv ℝ G x (a - b))
  linarith

/-- **Simon Ch. 3, Lemma 1.2, "only if" part, final paragraph** (chapter-03.txt lines 61–65),
for one `C¹` map `G : ℝⁿ → ℝᴾ`: up to an `Hⁿ`-null set, `G(ℝⁿ)` is covered by the images
`G(B_{r_k}(c_k))` of countably many open balls (empty when `r_k ≤ 0`) carrying lower Lipschitz
bounds `m_k|a − b| ≤ |G a − G b|`, `m_k > 0`.
The critical image `G(C)`, `C = {x : DG(x) not injective}`, is `Hⁿ`-null.  Mathlib's partition
of `C ∩ B̄_R(0)` into pieces `T` on which `G` is `η`-close to some non-injective `A = DG(y)`
reduces this to `Hⁿ(G(T)) ≤ (‖A‖ + 1)ⁿ η Lⁿ(T)`: for a unit `u ∈ ker A`, the compression
`D w = w + (η − 1)⟨u, w⟩u` has `det D = η`, and `|G a − G b| ≤ (‖A‖ + 1)|D a − D b|` on `T`.
For a dense sequence `e` and `(q, p) = Nat.unpair k`, the candidate ball `B_{1/(p+1)}(e_q)` is
kept, with a witness `m_k`, when it carries a lower Lipschitz bound, and replaced by `B_0 = ∅`
otherwise.  At a regular point `x`, `codim1_rdo_c1cov_local_lower_lipschitz` gives a bound on
some `B_δ(x)`; a candidate ball with `2/(p+1) < δ` and `|x − e_q| < 1/(p+1)` contains `x`, lies
in `B_δ(x)` and is kept. -/
theorem Submission.codim1_rdo_c1cov_regular_ball_cover : ∀ (P n : ℕ) (G : Euclid n → Euclid P), ContDiff ℝ 1 G → ∃ (c : ℕ → Euclid n) (r m : ℕ → ℝ), (∀ k, 0 < m k) ∧ (∀ k, ∀ a ∈ ball (c k) (r k), ∀ b ∈ ball (c k) (r k), m k * ‖a - b‖ ≤ ‖G a - G b‖) ∧ μHE[n] (range G \ ⋃ k, G '' ball (c k) (r k)) = 0 := by
  intro P n G hG
  -- the critical image `G({x : DG(x) not injective})` is `Hⁿ`-null
  have hcrit : μHE[n] (G '' {x | ¬ Injective (fderiv ℝ G x)}) = 0 := by
    -- near a non-injective `A`, `G` shrinks `Hⁿ` by the factor `ε`
    have hloc : ∀ ε : NNReal, 0 < ε → ε ≤ 1 → ∀ A : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal,
        0 < δ ∧ (¬ Injective A → ∀ T : Set (Euclid n), ApproximatesLinearOn G A T δ →
          μHE[n] (G '' T) ≤ ε * volume T) := by
      intro ε hε hε1 A
      by_cases hA : Injective A
      · exact ⟨1, one_pos, fun h => absurd hA h⟩
      -- a unit vector `u` in the kernel of `A`
      obtain ⟨u, hu1, hAu⟩ : ∃ u : Euclid n, ‖u‖ = 1 ∧ A u = 0 := by
        rw [injective_iff_map_eq_zero] at hA
        push Not at hA
        obtain ⟨w, hw, hw0⟩ := hA
        refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
        · rw [map_smul, hw, smul_zero]
      set K : NNReal := ‖A‖₊ + 1 with hK
      have hK1 : 1 ≤ K := le_add_self
      have hKn : (0 : NNReal) < K ^ n := pow_pos (zero_lt_one.trans_le hK1) n
      set η : NNReal := ε / K ^ n with hη
      have hη0 : 0 < η := div_pos hε hKn
      have hη1 : (η : ℝ) ≤ 1 := by
        have : η ≤ ε := div_le_self (by positivity) (one_le_pow₀ hK1)
        exact_mod_cast this.trans hε1
      refine ⟨η, hη0, fun _ T hT => ?_⟩
      -- the compression `D w = w + (η - 1) ⟪u, w⟫ u` along `u`
      let D : Euclid n →ₗ[ℝ] Euclid n := LinearMap.id + ((η : ℝ) - 1) • (innerₛₗ ℝ u).smulRight u
      have hD : ∀ w, D w = w + (((η : ℝ) - 1) * inner ℝ u w) • u := by
        intro w
        simp [D, mul_smul]
      -- `det D = 1 + (η - 1) ‖u‖² = η` (matrix determinant lemma in the standard basis)
      have hdet : LinearMap.det D = η := by
        set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with hb
        have hM : LinearMap.toMatrix b b D =
            1 + Matrix.vecMulVec (fun i => u i) (fun j => ((η : ℝ) - 1) * u j) := by
          ext i j
          rw [LinearMap.toMatrix_apply, hD]
          simp [hb, Matrix.one_apply, Matrix.vecMulVec_apply, EuclideanSpace.inner_single_right]
          ring
        have hsum : ∑ j, u j * u j = 1 := by
          have h := real_inner_self_eq_norm_sq u
          rw [hu1, PiLp.inner_apply] at h
          simpa [sq] using h
        rw [← LinearMap.det_toMatrix b, hM, Matrix.vecMulVec_eq Unit,
          Matrix.det_one_add_replicateCol_mul_replicateRow]
        simp only [dotProduct, mul_assoc]
        rw [← Finset.mul_sum, hsum]
        ring
      -- `‖G y₁ - G y₂‖ ≤ ‖A (y₁ - y₂)‖ + η ‖y₁ - y₂‖ ≤ K ‖D (y₁ - y₂)‖` on `T`
      have hkey : ∀ y₁ ∈ T, ∀ y₂ ∈ T, ‖G y₁ - G y₂‖ ≤ K * ‖D y₁ - D y₂‖ := by
        intro y₁ h₁ y₂ h₂
        have happ : ‖G y₁ - G y₂ - A (y₁ - y₂)‖ ≤ η * ‖y₁ - y₂‖ := hT y₁ h₁ y₂ h₂
        rw [← map_sub]
        set w := y₁ - y₂
        have hAw : A w = A (D w) := by rw [hD, map_add, map_smul, hAu, smul_zero, add_zero]
        -- `‖D w‖² = ‖w‖² - (1 - η²) ⟪u, w⟫² ≥ η² ‖w‖²`
        have hnorm : (η : ℝ) * ‖w‖ ≤ ‖D w‖ := by
          have h1 : ‖D w‖ ^ 2 = ‖w‖ ^ 2 + ((η : ℝ) ^ 2 - 1) * inner ℝ u w ^ 2 := by
            rw [hD, norm_add_sq_real, inner_smul_right, norm_smul, real_inner_comm,
              Real.norm_eq_abs, hu1, mul_one, sq_abs]
            ring
          have h2 : inner ℝ u w ^ 2 ≤ ‖w‖ ^ 2 := by
            have h := abs_real_inner_le_norm u w
            rw [hu1, one_mul] at h
            exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
          have h3 : ((η : ℝ) * ‖w‖) ^ 2 ≤ ‖D w‖ ^ 2 := by
            rw [h1, mul_pow]
            have h4 : (η : ℝ) ^ 2 ≤ 1 := by nlinarith [η.coe_nonneg]
            nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4)]
          exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3
        have hAD : ‖A (D w)‖ ≤ ‖A‖ * ‖D w‖ := A.le_opNorm _
        calc ‖G y₁ - G y₂‖ ≤ ‖A w‖ + ‖G y₁ - G y₂ - A w‖ := norm_le_insert' _ _
          _ ≤ ‖A‖ * ‖D w‖ + ‖D w‖ := by rw [hAw] at happ ⊢; linarith
          _ = K * ‖D w‖ := by simp [K]; ring
      -- `φ = G ∘ D⁻¹` is `K`-Lipschitz on `D '' T` and `G '' T ⊆ φ '' (D '' T)`
      let φ : Euclid n → Euclid P := fun z => G (Function.invFunOn D T z)
      have hφ : ∀ y ∈ T, Function.invFunOn D T (D y) ∈ T ∧ D (Function.invFunOn D T (D y)) = D y :=
        fun y hy => Function.invFunOn_pos ⟨y, hy, rfl⟩
      have hlip : LipschitzOnWith K φ (D '' T) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨y₁, h₁, rfl⟩ _ ⟨y₂, h₂, rfl⟩
        obtain ⟨h₁', e₁⟩ := hφ y₁ h₁
        obtain ⟨h₂', e₂⟩ := hφ y₂ h₂
        have h := hkey _ h₁' _ h₂'
        rw [e₁, e₂] at h
        simpa only [dist_eq_norm] using h
      have hsub : G '' T ⊆ φ '' (D '' T) := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨D y, ⟨y, hy, rfl⟩, ?_⟩
        obtain ⟨h', e⟩ := hφ y hy
        have h := hkey _ h' _ hy
        rw [e, sub_self, norm_zero, mul_zero] at h
        exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
      -- `Hⁿ(G(T)) ≤ Kⁿ Hⁿ(D(T)) = Kⁿ |det D| Lⁿ(T) = ε Lⁿ(T)`
      calc μHE[n] (G '' T) ≤ μHE[n] (φ '' (D '' T)) := measure_mono hsub
        _ ≤ (K : ℝ≥0∞) ^ n * μHE[n] (D '' T) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
        _ = (K : ℝ≥0∞) ^ n * (ENNReal.ofReal |LinearMap.det D| * volume T) := by
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
        _ = ε * volume T := by
            rw [hdet, abs_of_nonneg η.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← mul_assoc,
              ← ENNReal.coe_pow, ← ENNReal.coe_mul, hη, mul_div_cancel₀ _ hKn.ne']
    -- on `C ∩ B̄_R(0)`: partition into pieces where `G` is close to some `DG(y)`, `y ∈ C`
    have hR : ∀ R : ℝ, μHE[n] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ closedBall 0 R)) = 0 := by
      intro R
      set s := {x | ¬ Injective (fderiv ℝ G x)} ∩ closedBall (0 : Euclid n) R with hs
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (G '' s) ≤ ε * volume (closedBall (0 : Euclid n) R) := by
        intro ε hε hε1
        rcases eq_empty_or_nonempty s with h | h
        · rw [h, image_empty, measure_empty]
          exact bot_le
        choose δ hδ using hloc ε hε hε1
        obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
            (fun x _ => (hG.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt) δ
            (fun A => (hδ A).1.ne')
        calc μHE[n] (G '' s) ≤ μHE[n] (⋃ k, G '' (s ∩ t k)) := by
              rw [← image_iUnion, ← inter_iUnion]
              exact measure_mono (image_mono (subset_inter Subset.rfl t_cover))
          _ ≤ ∑' k, μHE[n] (G '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R ∩ t k) := by
              refine ENNReal.tsum_le_tsum fun k => ?_
              obtain ⟨y, hy, hAy⟩ := Af' h k
              calc μHE[n] (G '' (s ∩ t k)) ≤ ε * volume (s ∩ t k) :=
                    (hδ (A k)).2 (by rw [hAy]; exact hy.1) _ (ht k)
                _ ≤ ε * volume (closedBall (0 : Euclid n) R ∩ t k) := by
                    gcongr
                    exact inter_subset_right
          _ = ε * volume (⋃ k, closedBall (0 : Euclid n) R ∩ t k) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion]
              · exact pairwise_disjoint_mono t_disj fun k => inter_subset_right
              · exact fun k => measurableSet_closedBall.inter (t_meas k)
          _ ≤ ε * volume (closedBall (0 : Euclid n) R) := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left
      -- let `ε → 0`
      have B : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))
          (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))
            (𝓝 0) (𝓝 (((0 : NNReal) : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))) :=
          ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
            (Or.inr measure_closedBall_lt_top.ne)
        simp only [zero_mul, ENNReal.coe_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      rw [← nonpos_iff_eq_zero]
      apply ge_of_tendsto B
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
      exact hbound ε hε.1 hε.2
    have h := measure_iUnion_null (μ := μHE[n]) fun k : ℕ => hR k
    rwa [← image_iUnion, iUnion_inter_closedBall_nat] at h
  classical
  -- candidate balls `B_{1/(p+1)}(e_q)`, `(q, p) = Nat.unpair k`, for a dense sequence `e`
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (Euclid n)
  let ctr : ℕ → Euclid n := fun k => e (Nat.unpair k).1
  let rad : ℕ → ℝ := fun k => 1 / ((Nat.unpair k).2 + 1 : ℝ)
  -- a candidate ball is good if `G` has a lower Lipschitz bound on it
  let good : ℕ → Prop := fun k => ∃ μ : ℝ, 0 < μ ∧
    ∀ a ∈ ball (ctr k) (rad k), ∀ b ∈ ball (ctr k) (rad k), μ * ‖a - b‖ ≤ ‖G a - G b‖
  refine ⟨ctr, fun k => if good k then rad k else 0,
    fun k => if h : good k then Exists.choose h else 1, fun k => ?_, fun k => ?_, ?_⟩
  · -- `m_k > 0`
    show 0 < if h : good k then Exists.choose h else 1
    split_ifs with h
    exacts [(Exists.choose_spec h).1, one_pos]
  · -- (i): the witness on a good ball; otherwise `B_0(c_k) = ∅`
    intro a ha b hb
    dsimp only at ha hb ⊢
    by_cases h : good k
    · rw [ite_eq_left h] at ha hb
      rw [dite_eq_left h]
      exact (Exists.choose_spec h).2 a ha b hb
    · rw [ite_eq_right h, ball_zero] at ha
      exact absurd ha (notMem_empty a)
  · -- (ii): each regular point lies in a good ball, so the remainder is in the critical image
    refine measure_mono_null ?_ hcrit
    rintro y ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, fun hinj => hy ?_, rfl⟩
    obtain ⟨δ, μ, hδ, hμ, hlip⟩ :=
      Submission.codim1_rdo_c1cov_local_lower_lipschitz P n G x hG hinj
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt (half_pos hδ)
    obtain ⟨q, hq⟩ := he.exists_dist_lt x (Nat.one_div_pos_of_nat : (0 : ℝ) < 1 / ((p : ℝ) + 1))
    have hk : Nat.unpair (Nat.pair q p) = (q, p) := Nat.unpair_pair q p
    -- `B_{1/(p+1)}(e_q) ⊆ B_δ(x)`, so this candidate ball is good
    have hsub : ball (ctr (Nat.pair q p)) (rad (Nat.pair q p)) ⊆ ball x δ := by
      intro a ha
      simp only [ctr, rad, hk, mem_ball] at ha ⊢
      calc dist a x ≤ dist a (e q) + dist (e q) x := dist_triangle _ _ _
        _ < 1 / ((p : ℝ) + 1) + 1 / ((p : ℝ) + 1) := add_lt_add ha (by rwa [dist_comm])
        _ < δ := by linarith
    have hgood : good (Nat.pair q p) :=
      ⟨μ, hμ, fun a ha b hb => hlip a (hsub ha) b (hsub hb)⟩
    refine mem_iUnion.2 ⟨Nat.pair q p, x, ?_, rfl⟩
    show x ∈ ball (ctr (Nat.pair q p)) (if good (Nat.pair q p) then rad (Nat.pair q p) else 0)
    rw [ite_eq_left hgood]
    simpa only [ctr, rad, hk, mem_ball] using hq
/-- **Simon Ch. 3, proof of Lemma 1.2** (properties (ii), (iii) of the pieces `g(B_r(c))`): the
image of an open ball under a `C¹` map `g : ℝⁿ → ℝᴾ` is Borel and has finite `Hⁿ`-measure.
`B_r(c) = ⋃ₜ closedBall(c, r − 1/(t+1))`, so `g(B_r(c))` is a countable union of compact sets;
`g` is Lipschitz on the compact convex `closedBall(c, r)`, so by Simon Ch. 2, 1.8(i)
`Hⁿ(g(B_r(c))) ≤ Λⁿ Lⁿ(B_r(c)) < ∞`. -/
theorem Submission.codim1_rdo_c1cov_image_ball_borel_finite : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r : ℝ), ContDiff ℝ 1 g → MeasurableSet (g '' ball c r) ∧ μHE[n] (g '' ball c r) ≠ ∞ := by
  intro P n g c r hg
  refine ⟨?_, ?_⟩
  · -- `B_r(c)` is the union of the compact balls `closedBall(c, r − 1/(t+1))`
    have hball : ball c r = ⋃ t : ℕ, closedBall c (r - 1 / ((t : ℝ) + 1)) := by
      ext y
      simp only [mem_ball, mem_iUnion, mem_closedBall]
      constructor
      · intro hy
        obtain ⟨t, ht⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
        exact ⟨t, by linarith⟩
      · rintro ⟨t, ht⟩
        have : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
        linarith
    rw [hball, image_iUnion]
    exact MeasurableSet.iUnion fun t =>
      ((isCompact_closedBall c _).image hg.continuous).isClosed.measurableSet
  · -- `g` is Lipschitz on the compact convex `closedBall c r`, hence on `ball c r`
    obtain ⟨K, hK⟩ := (hg.contDiffOn (s := closedBall c r)).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall c r) (isCompact_closedBall c r)
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hK.mono ball_subset_closedBall))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_ball_lt_top.ne
/-- Simon Ch. 3, Lemma 1.2, display (1) (corrected: `F(ℝⁿ) ⊆ E ∪ ⋃ᵢ Gᵢ(ℝⁿ)`, `Gᵢ : ℝⁿ → ℝᴾ`),
for one Lipschitz map `F : ℝⁿ → ℝᴾ`, given the scalar `C¹` approximation theorem (Simon Ch. 2,
Theorem 1.5) on `ℝⁿ` as the hypothesis.  Each coordinate `Fˡ` is `K`-Lipschitz; approximating it
with error `((i + 1)(P + 1))⁻¹` gives `C¹` maps `Gᵢ = (g_{i,l})ₗ` with `Lⁿ{F ≠ Gᵢ} ≤ (i + 1)⁻¹`, so
`Z = ⋂ᵢ {F ≠ Gᵢ}` is `Lⁿ`-null, `Hⁿ(F(Z)) ≤ Kⁿ Lⁿ(Z) = 0` (Simon 2.1.8(i), `Hⁿ = Lⁿ` on `ℝⁿ`) and
`F(ℝⁿ) \ ⋃ᵢ Gᵢ(ℝⁿ) ⊆ F(Z)`. -/
theorem Submission.codim1_rdo_c1cov_lipschitz_range_c1_cover : ∀ (P n : ℕ), (∀ (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε) → ∀ (F : Euclid n → Euclid P) (K : NNReal), LipschitzWith K F → ∃ G : ℕ → Euclid n → Euclid P, (∀ i, ContDiff ℝ 1 (G i)) ∧ μHE[n] (range F \ ⋃ i, range (G i)) = 0 := by
  intro P n hH F K hF
  -- Step 1: the coordinates `Fˡ` of `F` are `K`-Lipschitz
  have hFl : ∀ l : Fin P, LipschitzWith K fun x => F x l := fun l =>
    LipschitzWith.of_dist_le_mul fun x y =>
      (PiLp.dist_apply_le (F x) (F y) l).trans (hF.dist_le_mul x y)
  -- Step 2: `C¹` approximation of every coordinate with error `δᵢ = ((i + 1)(P + 1))⁻¹`
  have hδ : ∀ i : ℕ, (0 : ℝ≥0∞) < (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := fun i =>
    ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by simp) (by simp))
  choose g hg hgvol using fun (i : ℕ) (l : Fin P) => hH (fun x => F x l) K (hFl l) _ (hδ i)
  -- Step 3: `Gᵢ = (g_{i,1}, …, g_{i,P})` is `C¹`
  let G : ℕ → Euclid n → Euclid P := fun i x => WithLp.toLp 2 fun l => g i l x
  have hG : ∀ i, ContDiff ℝ 1 (G i) := fun i => (contDiff_piLp 2).2 fun l => hg i l
  -- Step 4: `{F ≠ Gᵢ} ⊆ ⋃ₗ {Fˡ ≠ g_{i,l} ∨ DFˡ ≠ Dg_{i,l}}`, so `Lⁿ{F ≠ Gᵢ} ≤ (i + 1)⁻¹`
  have hsub : ∀ i, {x | F x ≠ G i x} ⊆
      ⋃ l, {x | F x l ≠ g i l x ∨ fderiv ℝ (fun x => F x l) x ≠ fderiv ℝ (g i l) x} := by
    intro i x hx
    obtain ⟨l, hl⟩ : ∃ l, F x l ≠ g i l x := by
      by_contra! h
      exact hx (PiLp.ext h)
    exact mem_iUnion.2 ⟨l, Or.inl hl⟩
  have hvol : ∀ i : ℕ, volume {x | F x ≠ G i x} ≤ ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro i
    calc volume {x | F x ≠ G i x}
        ≤ ∑ l, volume {x | F x l ≠ g i l x ∨ fderiv ℝ (fun x => F x l) x ≠ fderiv ℝ (g i l) x} :=
          (measure_mono (hsub i)).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _l : Fin P, (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ :=
          Finset.sum_le_sum fun l _ => (hgvol i l).le
      _ = (P : ℝ≥0∞) * (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := by simp
      _ ≤ ((P : ℝ≥0∞) + 1) * (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := by gcongr; exact le_self_add
      _ = ((i : ℝ≥0∞) + 1)⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_left_comm,
            ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
  -- Step 5: `Z = ⋂ᵢ {F ≠ Gᵢ}` is `Lⁿ`-null
  have hZ : volume (⋂ i, {x | F x ≠ G i x}) = 0 := by
    refine le_antisymm (le_of_forall_gt fun ε hε => ?_) bot_le
    obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    calc volume (⋂ i, {x | F x ≠ G i x}) ≤ volume {x | F x ≠ G i x} := measure_mono (iInter_subset _ i)
      _ ≤ ((i : ℝ≥0∞) + 1)⁻¹ := hvol i
      _ ≤ (i : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hi
  -- Step 6: `Hⁿ(F(Z)) ≤ Kⁿ Hⁿ(Z) = Kⁿ Lⁿ(Z) = 0`
  have hFZ : μHE[n] (F '' ⋂ i, {x | F x ≠ G i x}) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μHE[n] (F '' ⋂ i, {x | F x ≠ G i x})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] (⋂ i, {x | F x ≠ G i x}) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero]
  -- Step 7: `F(ℝⁿ) \ ⋃ᵢ Gᵢ(ℝⁿ) ⊆ F(Z)`
  refine ⟨G, hG, measure_mono_null ?_ hFZ⟩
  rintro _ ⟨⟨x, rfl⟩, hy⟩
  exact ⟨x, mem_iInter.2 fun i h => hy (mem_iUnion.2 ⟨i, x, h.symm⟩), rfl⟩
/-- **Whitney's `C¹` extension theorem** (Simon Ch. 2, 1.6; proof of Evans–Gariepy §6.5).  If
`A ⊆ ℝⁿ` is closed, `h` and `D` are continuous on `A`, and the remainder
`h y - h x - D x (y - x)` is `o(|y - x|)` uniformly for `x` in compact subsets of `A`, then some
`g ∈ C¹(ℝⁿ)` has `g = h` and `Dg = D` on `A`.  With `r x = min(1, dist(x, A)) / 100`, Vitali's
lemma selects disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `ℝⁿ \ A`;
nearby radii are comparable, so the overlap is uniformly bounded.  Rescaled bumps divided by
their locally finite sum give a partition of unity `w c` on `ℝⁿ \ A` with
`∑ ‖D(w c)(x)‖ ≤ M / r x`.  Put `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`, where
`P b x = h b + D b (x - b)` and `pr c ∈ A` is a nearest point. -/
theorem Submission.codim1_rdo_c1a_whitney_extension : ∀ (n : ℕ) (A : Set (Euclid n)) (h : Euclid n → ℝ) (D : Euclid n → (Euclid n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖) → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧ ∀ a ∈ A, HasFDerivAt g (D a) a := by
  intro n A h D hA hh hD hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  -- the Whitney radius `r x = min 1 (dist x A) / 100`
  obtain ⟨r, hr⟩ : ∃ r : Euclid n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨_, fun _ => rfl⟩
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
    rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := fun x y => by
    have h₁ := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h₁
    have h₂ := (abs_sub_le_iff.mp h₁).1
    rw [hr, hr]; linarith
  -- radii of nearby centres are comparable
  have hnear : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := hrlip x c
    have h₂ := hrlip c x
    rw [dist_comm c x] at h₂
    have := hr0 x
    have := hr0 c
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Vitali: disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `Aᶜ`
  obtain ⟨Z, hZA, hZdisj, hZcov⟩ : ∃ Z ⊆ Aᶜ, Z.PairwiseDisjoint (fun c => ball c (r c)) ∧
      ∀ x ∉ A, ∃ c ∈ Z, dist x c < 4 * r c := by
    obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      Aᶜ (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
    refine ⟨s, hs, hd, fun x hx => ?_⟩
    obtain ⟨c, hcs, hxc⟩ := hc x hx
    exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
  have hsep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      simpa only [mem_ball, dist_comm] using lt_of_not_ge hlt
    exact Set.disjoint_left.mp (hZdisj hc hd hcd) hdc (mem_ball_self (hrpos d (hZA hd)))
  -- a `1/2`-separated subset of `B̄(0, 21)` has at most `N` points
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Euclid n), s ⊆ closedBall (0 : Euclid n) 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Euclid n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hssep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Euclid n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Euclid n) ≠ (y : Euclid n) := fun e => hxy' (Subtype.ext e)
      have hd := hssep x.property y.property hne'
      have htri := dist_triangle (x : Euclid n) (c x : Euclid n) (y : Euclid n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Euclid n) (c x : Euclid n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  -- bounded overlap: at most `N` centres are near any `x ∉ A`
  have hover : ∀ x ∉ A, {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := hrpos x hx
    let f : Euclid n → Euclid n := fun c => (r x)⁻¹ • (c - x)
    have hf : Injective f := by
      intro c d hcd
      have e := congrArg (fun z : Euclid n => r x • z) hcd
      simpa [f, smul_smul, hrx.ne'] using e
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖f c‖ ≤ 21 := by
      intro c hc
      have hd := (hnear x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      simp only [f]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep' : (f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun e => hcd (congrArg f e)
      have hdist := hsep c hc.1 d hd.1 hcd'
      have hrad := (hnear x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        simpa only [dist_eq_norm] using hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      simp only [f]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Euclid n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep'
    exact ⟨hfin.of_finite_image hf.injOn, by rwa [Set.ncard_image_of_injective _ hf] at hcard⟩
  -- the finite set `F x` of centres near `x ∉ A`
  have hfin : ∀ x ∉ A, {c : Z | dist x c ≤ r x + 10 * r c}.Finite := by
    intro x hx
    apply ((hover x hx).1.preimage (Subtype.val_injective (p := (· ∈ Z))).injOn).subset
    intro c hc
    exact ⟨c.property, hc⟩
  have hFex : ∀ x, ∃ s : Finset Z, x ∉ A → ∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun hx' => absurd hx hx'⟩
    · exact ⟨(hfin x hx).toFinset, fun _ c => by simp⟩
  choose F hF using hFex
  have hFcard : ∀ x ∉ A, (F x).card ≤ N := by
    intro x hx
    have hsub : (F x).map (Embedding.subtype _) ⊆ (hover x hx).1.toFinset := by
      intro c hc
      simp only [Finset.mem_map, Embedding.coe_subtype] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [Set.Finite.mem_toFinset]
      exact ⟨c'.property, (hF x hx c').mp hc'⟩
    calc (F x).card = ((F x).map (Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (hover x hx).1.toFinset.card := Finset.card_le_card hsub
      _ = {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard :=
          (Set.ncard_eq_toFinset_card _ _).symm
      _ ≤ N := (hover x hx).2
  -- a smooth bump `ψ = 1` on `B̄(0, 4)`, `ψ = 0` off `B(0, 8)`
  obtain ⟨ψ, hψc, hψ0, hψ1, hψin, hψout, L, hL⟩ : ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ 4 → ψ x = 1) ∧
      (∀ x, 8 ≤ ‖x‖ → ψ x = 0) ∧ ∃ L : NNReal, LipschitzWith L ψ := by
    let b : ContDiffBump (0 : Euclid n) := ⟨4, 8, by norm_num, by norm_num⟩
    have hb : ContDiff ℝ 1 b := b.contDiff
    obtain ⟨L, hL⟩ := hb.lipschitzWith_of_hasCompactSupport b.hasCompactSupport one_ne_zero
    refine ⟨b, hb, fun x => b.nonneg, fun x => b.le_one, fun x hx => ?_, fun x hx => ?_, L, hL⟩
    · exact b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    · apply notMem_support.mp
      rw [b.support_eq]
      exact fun hxb => absurd (mem_ball_zero_iff.mp hxb) (not_lt.mpr hx)
  -- the rescaled bumps `φ c x = ψ ((x - c) / r c)`
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid n → Euclid n → ℝ, ∀ c x, φ c x = ψ ((r c)⁻¹ • (x - c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hφfun : ∀ c, φ c = fun x => ψ ((r c)⁻¹ • (x - c)) := fun c => funext (hφ c)
  have hφc : ∀ c, ContDiff ℝ 1 (φ c) := by
    intro c
    rw [hφfun c]
    exact hψc.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hφ0 : ∀ c x, 0 ≤ φ c x := fun c x => by rw [hφ]; exact hψ0 _
  have hφin : ∀ c x, 0 < r c → dist x c ≤ 4 * r c → φ c x = 1 := by
    intro c x hc hx
    rw [hφ]
    apply hψin
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (r c)⁻¹ * dist x c ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have hφout : ∀ c x, 0 < r c → 8 * r c ≤ dist x c → φ c x = 0 := by
    intro c x hc hx
    rw [hφ]
    apply hψout
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * dist x c := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, hBb⟩ : ∃ B : ℝ, 0 < B ∧ ∀ c, 0 < r c → ∀ x, ‖fderiv ℝ (φ c) x‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c hc x => ?_⟩
    let ρ : NNReal := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Euclid n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (φ c) := by
      rw [hφfun c]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (φ c) x‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- near `x ∉ A`, only the bumps indexed by `F x` are active
  have hφzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → φ c y = 0 := by
    intro x hx y hy c hc
    apply hφout c y (hrpos c (hZA c.property))
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun e => hc ((hF x hx c).mpr e)
    have ht := dist_triangle x y (c : Euclid n)
    rw [dist_comm x y] at ht
    have := hr0 (c : Euclid n)
    linarith
  have hyA : ∀ x ∉ A, ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA'
    have hi := infDist_le_dist_of_mem (x := x) hyA'
    have hr' := hrd x
    rw [dist_comm x y] at hi
    linarith [hr0 x]
  -- the locally finite sum `S = ∑ φ c`
  obtain ⟨S, hS⟩ : ∃ S : Euclid n → ℝ, ∀ x, S x = ∑ᶠ c : Z, φ c x := ⟨_, fun _ => rfl⟩
  have hSnear : ∀ x ∉ A, ∀ y, dist y x < r x → S y = ∑ c ∈ F x, φ c y := by
    intro x hx y hy
    rw [hS]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hcF
    exact hc (hφzero x hx y hy c hcF)
  have hSev : ∀ x ∉ A, S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hSnear x hx y hy
  have hSc : ∀ x ∉ A, ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (c : Z) y => φ c y) (s := F x) fun c _ => hφc c).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hSfd : ∀ x ∉ A, fderiv ℝ S x = ∑ c ∈ F x, fderiv ℝ (φ c) x := by
    intro x hx
    rw [(hSev x hx).fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (hφc c).differentiable one_ne_zero x)
  have hS1 : ∀ x ∉ A, 1 ≤ S x := by
    intro x hx
    have hrx := hrpos x hx
    rw [hSnear x hx x (by simpa using hrx)]
    obtain ⟨c, hc, hxc⟩ := hZcov x hx
    have hi : (⟨c, hc⟩ : Z) ∈ F x := by
      rw [hF x hx]
      have := hr0 c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = φ c x := (hφin c x (hrpos c (hZA hc)) hxc.le).symm
      _ ≤ ∑ c ∈ F x, φ c x :=
          Finset.single_le_sum (f := fun c : Z => φ c x) (fun c _ => hφ0 c x) hi
  -- the partition of unity `w c = φ c / S` on `Aᶜ`
  obtain ⟨w, hw⟩ : ∃ w : Z → Euclid n → ℝ, ∀ c x, w c x = φ c x / S x := ⟨_, fun _ _ => rfl⟩
  have hwfun : ∀ c, w c = fun x => φ c x / S x := fun c => funext (hw c)
  have hwc : ∀ c : Z, ∀ x ∉ A, ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    rw [hwfun c]
    exact (hφc c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
  have hw0 : ∀ c : Z, ∀ x ∉ A, 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (hφ0 c x) (le_trans zero_le_one (hS1 x hx))
  have hwzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, hφzero x hx y hy c hc, zero_div]
  have hwsum : ∀ x ∉ A, ∀ y, dist y x < r x → ∑ c ∈ F x, w c y = 1 := by
    intro x hx y hy
    simp only [hw, ← Finset.sum_div, ← hSnear x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hyA x hx y hy))))
  have hwdsum : ∀ x ∉ A, ∑ c ∈ F x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ F x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hwsum x hx y hy
    have hh' := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh'
    rw [fderiv_fun_sum (fun c _ => (hwc c x hx).differentiableAt one_ne_zero)] at hh'
    exact hh'
  have hwd_le : ∀ x ∉ A, ∀ c : Z,
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
    intro x hx c
    have hS1x := hS1 x hx
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
    have hSi : (S x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1x
    have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ S x ^ 2 by nlinarith)
    have hb := ((hφc c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x := by
      simpa only [hwfun, div_eq_mul_inv, Function.comp_def] using hprod.fderiv
    rw [hder]
    have hb0 := hφ0 c x
    have hb1 : φ c x ≤ 1 := by rw [hφ]; exact hψ1 _
    calc ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x‖
        ≤ ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (φ c) x‖ :=
          norm_add_le _ _
      _ = φ c x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (φ c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (φ c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
  -- `∑_{c ∈ F x} ‖D w_c(x)‖ ≤ M / r x`
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∉ A, ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := hrpos x hx
    obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * B / r x := ⟨_, rfl⟩
    have hT : 0 ≤ T := by rw [hT_def]; positivity
    have hb' : ∀ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ T := by
      intro c hc
      have hcr := hrpos c (hZA c.property)
      have hlow := (hnear x c ((hF x hx c).mp hc)).1
      refine (hBb c hcr x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = T := by rw [hT_def]; ring
    have hcard : ((F x).card : ℝ) ≤ N := by exact_mod_cast hFcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSfd x hx]
      calc ‖∑ c ∈ F x, fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ F x, T := Finset.sum_le_sum hb'
        _ = ((F x).card : ℝ) * T := by simp
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ T + (N : ℝ) * T := fun c hc =>
      (hwd_le x hx c).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ ∑ _c ∈ F x, (T + (N : ℝ) * T) := Finset.sum_le_sum hw'
      _ = ((F x).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by rw [hT_def]; ring
  -- the affine jets `P b x = h b + D b (x - b)`
  obtain ⟨P, hP⟩ : ∃ P : Euclid n → Euclid n → ℝ, ∀ b x, P b x = h b + D b (x - b) :=
    ⟨_, fun _ _ => rfl⟩
  have hPfun : ∀ b, P b = fun x => h b + D b (x - b) := fun b => funext (hP b)
  have hPc : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    rw [hPfun b]
    exact contDiff_const.add ((D b).contDiff.comp (contDiff_id.sub contDiff_const))
  have hPd : ∀ b x, HasFDerivAt (P b) (D b) x := by
    intro b x
    have e := (((D b).hasFDerivAt (x := x)).sub_const (D b b)).const_add (h b)
    have hfun : (fun y => h b + D b (y - b)) = fun y => h b + (D b y - D b b) := by
      funext y
      rw [map_sub]
    rw [hPfun b, hfun]
    exact e
  have hPsub : ∀ a b x,
      ‖P b x - P a x‖ ≤ ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ := by
    intro a b x
    have heq : P b x - P a x = (h b - h a - D a (b - a)) + (D b - D a) (x - b) := by
      have hx : x - a = (x - b) + (b - a) := by abel
      simp only [hP, hx, map_add, sub_apply]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((D b - D a).le_opNorm (x - b)))
  -- nearest points `pr x ∈ A`
  choose pr hprA hprd using fun x => hA.exists_infDist_eq_dist hne x
  have hprle : ∀ x, ∀ a ∈ A, dist x (pr x) ≤ dist x a := by
    intro x a ha
    rw [← hprd x]
    exact infDist_le_dist_of_mem ha
  have hpr2 : ∀ x, ∀ a ∈ A, dist (pr x) a ≤ 2 * dist x a := by
    intro x a ha
    have ht := dist_triangle (pr x) x a
    rw [dist_comm (pr x) x] at ht
    linarith [hprle x a ha]
  have hanc1 : ∀ x ∉ A, ∀ c : Z, c ∈ F x → dist x (pr c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hd := (hnear x c ((hF x hx c).mp hc)).2.2
    have hr' := hrd x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Euclid n)) (y := x)
    have ht := dist_triangle x (c : Euclid n) (pr c)
    rw [dist_comm (c : Euclid n) x] at hi
    rw [← hprd (c : Euclid n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have hanc2 : ∀ x ∉ A, ∀ a ∈ A, ∀ c : Z, c ∈ F x → dist (pr c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := hanc1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (pr c) x a
    rw [dist_comm (pr c) x] at ht
    linarith
  -- uniform estimates near a point of `A`
  have hloc : ∀ a ∈ A, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ η) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖h c - h b - D b (c - b)‖ ≤ η * ‖c - b‖ := by
    intro a ha η hη
    obtain ⟨r₀, hr₀, hrem₀⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left η hη
    obtain ⟨η₀, hη₀, hD₀⟩ := Metric.continuousWithinAt_iff.mp (hD a ha) η hη
    have hδ1 : min 1 (min η₀ (r₀ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η₀ (r₀ / 3)) ≤ η₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hδr : min 1 (min η₀ (r₀ / 3)) ≤ r₀ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η₀ (r₀ / 3)), lt_min one_pos (lt_min hη₀ (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      simpa only [dist_eq_norm] using (hD₀ hb (hba.trans_le hδη)).le
    · intro b hb hba c hc hca
      apply hrem₀ b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- convex combinations
  have hconv : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (s : Finset Z)
      (a : Z → ℝ) (v : Z → G) (b : ℝ), (∀ i ∈ s, 0 ≤ a i) → ∑ i ∈ s, a i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, a i • v i‖ ≤ b := by
    intro G _ _ s a v b ha hs hv
    calc ‖∑ i ∈ s, a i • v i‖ ≤ ∑ i ∈ s, ‖a i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, a i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (ha i hi)]
      _ ≤ ∑ i ∈ s, a i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (ha i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- the extension: `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid n → ℝ, ∀ x,
      g x = if x ∈ A then h x else ∑ᶠ c : Z, w c x * P (pr c) x := ⟨_, fun _ => rfl⟩
  have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
  have hgnear : ∀ x ∉ A, ∀ y, dist y x < r x → g y = ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (hyA x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (pr c) y = 0
    rw [hwzero x hx y hy c hc', zero_mul]
  have hgev : ∀ x ∉ A, g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hgnear x hx y hy
  have hgc : ∀ x ∉ A, ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ F x, w c y * P (pr c) y) x :=
      ContDiffAt.sum (fun c _ => (hwc c x hx).mul (hPc _).contDiffAt)
    exact hs.congr_of_eventuallyEq (hgev x hx)
  have hgfd : ∀ x ∉ A, fderiv ℝ g x =
      ∑ c ∈ F x, (w c x • D (pr c) + P (pr c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(hgev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((hwc c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hPd _ x)
  -- `Dg = D` on `A`
  have hgd : ∀ a ∈ A, HasFDerivAt g (D a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, -, hDδ, hremδ⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by simpa using hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [hgA a ha]
    by_cases hxA : x ∈ A
    · rw [hgA x hxA]
      have hr' := hremδ a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hxx : dist x x < r x := by simpa using hrpos x hxA
      have hid : g x - h a - D a (x - a) = ∑ c ∈ F x, w c x • (P (pr c) x - P a x) := by
        rw [hgnear x hxA x hxx]
        simp only [smul_eq_mul, mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum x hxA x hxx, one_mul, hP a x]
        ring
      rw [hid]
      apply hconv (F x) (fun c => w c x) (fun c => P (pr c) x - P a x) _
        (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx)
      intro c hc
      have hbA := hprA (c : Euclid n)
      have hba := hanc2 x hxA a ha c hc
      have hxb : dist x (pr c) ≤ 2 * dist x a :=
        (hanc1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr c) hbA hbaδ
      have hr' := hremδ a ha haa (pr c) hbA hbaδ
      have hba' : ‖pr c - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
      have hxb' : ‖x - pr c‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
      calc ‖P (pr c) x - P a x‖
          ≤ ‖h (pr c) - h a - D a (pr c - a)‖ + ‖D (pr c) - D a‖ * ‖x - pr c‖ :=
            hPsub a (pr c) x
        _ ≤ (ε / 5) * ‖pr c - a‖ + (ε / 5) * ‖x - pr c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  -- `Dg` is continuous at the points of `A`
  have hgcont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by rw [hη_def]; positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by rw [hη_def]; field_simp
    have hηε : η ≤ ε / 2 := by nlinarith [mul_pos hη hM]
    obtain ⟨δ, hδ, hδ1, hDδ, hremδ⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [(hgd a ha).fderiv, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [(hgd x hxA).fderiv]
      exact (hDδ x hxA (by linarith)).trans hηε
    · have hrx := hrpos x hxA
      have hxx : dist x x < r x := by simpa using hrx
      have hbA := hprA x
      have hbaδ : dist (pr x) a < δ := by
        linarith [hpr2 x a ha, dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := by
        rw [hr x, min_eq_right hdx]
        ring
      have hD' : ∀ c ∈ F x, ‖D (pr c) - D a‖ ≤ η := by
        intro c hc
        apply hDδ _ (hprA c)
        have hi := hanc2 x hxA a ha c hc
        linarith [dist_nonneg (x := x) (y := a)]
      have hP' : ∀ c ∈ F x, ‖P (pr c) x - P (pr x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA := hprA (c : Euclid n)
        have hda := hanc2 x hxA a ha c hc
        have hdaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
        have hxd := hanc1 x hxA c hc
        have hxb : dist x (pr x) = infDist x A := (hprd x).symm
        have hdb : dist (pr c) (pr x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (pr c) x (pr x)
          rw [dist_comm (pr c) x, hxb] at ht
          linarith
        have hDd : ‖D (pr c) - D (pr x)‖ ≤ 2 * η := by
          calc ‖D (pr c) - D (pr x)‖ = ‖(D (pr c) - D a) - (D (pr x) - D a)‖ := by
                congr 1; abel
            _ ≤ ‖D (pr c) - D a‖ + ‖D (pr x) - D a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hremδ (pr x) hbA hbaδ (pr c) hdA hdaδ
        have hdb' : ‖pr c - pr x‖ ≤ 3 * infDist x A := by
          simpa only [dist_eq_norm] using hdb
        have hxd' : ‖x - pr c‖ ≤ 2 * infDist x A := by simpa only [dist_eq_norm] using hxd
        calc ‖P (pr c) x - P (pr x) x‖
            ≤ ‖h (pr c) - h (pr x) - D (pr x) (pr c - pr x)‖ +
                ‖D (pr c) - D (pr x)‖ * ‖x - pr c‖ := hPsub (pr x) (pr c) x
          _ ≤ η * ‖pr c - pr x‖ + (2 * η) * ‖x - pr c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by rw [hscale]; ring
      have hsplit : fderiv ℝ g x - D a = (∑ c ∈ F x, w c x • (D (pr c) - D a)) +
          ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x := by
        rw [hgfd x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hwsum x hxA x hxx, hwdsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hsplit]
      calc ‖(∑ c ∈ F x, w c x • (D (pr c) - D a)) +
            ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ F x, w c x • (D (pr c) - D a)‖ +
              ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact hconv (F x) (fun c => w c x) (fun c => D (pr c) - D a) η
                (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx) hD'
            · calc ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ F x, ‖(P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ c ∈ F x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ :=
                    (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by field_simp
        _ = ε / 2 := heq
  refine ⟨g, ?_, fun a ha => hgA a ha, hgd⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (hgd x hx).differentiableAt
    · exact (hgc x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact hgcont x hx
    · exact (hgc x hx).continuousAt_fderiv one_ne_zero
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
/-- Evaluation of `n`-covectors at an `n`-family `c`, `ev c = (α ↦ α c)`, is a continuous map
into `n`-vectors: `‖ev c - ev c'‖ ≤ n · max(‖c‖, ‖c'‖)ⁿ⁻¹ · ‖c - c'‖`. -/
theorem Submission.dgoj_exists_continuous_covector_eval : ∀ (P n : ℕ), ∃ ev : (Fin n → Euclid P) → MultiVector P n, Continuous ev ∧ ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := by
  intro P n
  let ev : (Fin n → Euclid P) → MultiVector P n := fun c =>
    LinearMap.mkContinuous
      { toFun := fun α => α c
        map_add' := fun α β => rfl
        map_smul' := fun r α => rfl }
      (∏ i, ‖c i‖) fun α => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        calc ‖α c‖ ≤ ‖α‖ * ∏ i, ‖c i‖ := α.le_opNorm c
          _ = (∏ i, ‖c i‖) * ‖α‖ := mul_comm _ _
  have hev : ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := fun c α => rfl
  refine ⟨ev, ?_, hev⟩
  have key : ∀ c c' : Fin n → Euclid P,
      ‖ev c - ev c'‖ ≤ (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := by
    intro c c'
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
    rw [sub_apply, hev, hev]
    have h := α.norm_image_sub_le c c'
    rw [Fintype.card_fin] at h
    calc ‖α c - α c'‖ ≤ ‖α‖ * n * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := h
      _ = (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ * ‖α‖ := by ring
  rw [continuous_iff_continuousAt]
  intro c₀
  have hcont : Continuous fun c : Fin n → Euclid P => (n : ℝ) * max ‖c‖ ‖c₀‖ ^ (n - 1) * ‖c - c₀‖ := by
    fun_prop
  have h0 := hcont.tendsto c₀
  simp only [sub_self, norm_zero, mul_zero] at h0
  have h1 : Tendsto (fun c => ‖ev c - ev c₀‖) (𝓝 c₀) (𝓝 0) :=
    squeeze_zero (fun c => norm_nonneg (ev c - ev c₀)) (fun c => key c c₀) h0
  exact (tendsto_iff_norm_sub_tendsto_zero (E := MultiVector P n) (f := ev) (b := ev c₀)).2 h1

/-- Step 6 of the graph chart in the proof of **Simon 7.5.8** (orientations as in Ch. 6, 1.1–2.2):
if `ξN` orients `N`, `ξN(x) = ιe₀ ∧ ⋯ ∧ ιeₙ`, and `u` is `C¹` on `D = B_δ(0)` with `u(0) = 0`,
`Du(0) = 0`, `u ⊥ range ι` and `G(v) = x + ιv + u(v) ∈ N`, then on `D`
`ξN(G(v)) = J(v)⁻¹ a₀(v) ∧ ⋯ ∧ aₙ(v)`, where `aᵢ(v) = ιeᵢ + Du(v)eᵢ` and
`J(v) = det(⟨aᵢ(v), aⱼ(v)⟩)^{1/2}`.  Since `Du(v) ⊥ range ι`, `a(v)` is linearly independent, so
`η(v) = J(v)⁻¹ a₀(v) ∧ ⋯ ∧ aₙ(v)` is a unit orientation of `span a(v) = T_{G(v)}N`, and
`ξN(G(v)) = ±η(v)`.  The sign `s(v) = ξN(G(v))(L(η(v))) = ±1` is continuous on the connected
set `D` and `s(0) = 1`, so `s = 1` on `D`. -/
theorem Submission.codim1_rdo_gc_orientation_along_graph : ∀ (P n : ℕ) (N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ α : Covector (Euclid P) (n + 1), ξN x α = α (fun i => ι (EuclideanSpace.single i 1))) → 0 < δ → u 0 = 0 → fderiv ℝ u 0 = 0 → ContDiffOn ℝ 1 u (ball 0 δ) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + u v ∈ N) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) := by
  intro P n N ξN x ι u δ hξ hιξ hδ hu0 hDu0 hu horth hmem
  set D := ball (0 : Euclid (n + 1)) δ with hD
  have hDopen : IsOpen D := isOpen_ball
  let e : Fin (n + 1) → Euclid (n + 1) := fun i => EuclideanSpace.single i 1
  -- the graph map `G`, its derivative `A(v) = ι + Du(v)`, the frame `a(v)` and `J(v)`
  let G : Euclid (n + 1) → Euclid P := fun v => x + ι v + u v
  let A : Euclid (n + 1) → (Euclid (n + 1) →L[ℝ] Euclid P) :=
    fun v => ι.toContinuousLinearMap + fderiv ℝ u v
  let a : Euclid (n + 1) → Fin (n + 1) → Euclid P := fun v i => ι (e i) + fderiv ℝ u v (e i)
  let gram : Euclid (n + 1) → ℝ := fun v => Matrix.det (Matrix.of fun i j => inner ℝ (a v i) (a v j))
  let J : Euclid (n + 1) → ℝ := fun v => Real.sqrt (gram v)
  -- (1) calculus on the open ball `D`
  have hudiff : ∀ v ∈ D, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((hu.contDiffAt (hDopen.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  have hGderiv : ∀ v ∈ D, HasFDerivAt G (A v) v := fun v hv => by
    have h1 : HasFDerivAt (fun v : Euclid (n + 1) => x + ι v) ι.toContinuousLinearMap v :=
      (ι.toContinuousLinearMap.hasFDerivAt).const_add x
    exact h1.add (hudiff v hv)
  have hAe : ∀ v ∈ D, ∀ i, fderiv ℝ G v (e i) = a v i := fun v hv i => by
    rw [(hGderiv v hv).fderiv]; rfl
  have hDuc : ContinuousOn (fderiv ℝ u) D := hu.continuousOn_fderiv_of_isOpen hDopen le_rfl
  have hGc : ContDiffOn ℝ 1 G D :=
    (contDiffOn_const.add ι.toContinuousLinearMap.contDiff.contDiffOn).add hu
  -- (2) `Du(v)` is orthogonal to `range ι`: `v' ↦ ⟨ιw, u(v')⟩` vanishes on `D`
  have hDorth : ∀ v ∈ D, ∀ w a', inner ℝ (ι w) (fderiv ℝ u v a') = 0 := by
    intro v hv w a'
    have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 v] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hDopen.mem_nhds hv) (fun v' hv' => horth v' hv' w)
    have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
        ((innerSL ℝ (ι w)).comp (fderiv ℝ u v)) v :=
      (innerSL ℝ (ι w)).hasFDerivAt.comp v (hudiff v hv)
    have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid (n + 1) →L[ℝ] ℝ) v :=
      (hasFDerivAt_const (0 : ℝ) v).congr_of_eventuallyEq hloc
    have h2 := congrArg (fun L => L a') (hd.unique hd0)
    simpa using h2
  -- (3) `‖A(v)c‖ ≥ ‖c‖`, so `A(v)` is injective and `a(v)` is linearly independent
  have hnorm : ∀ v ∈ D, ∀ c : Euclid (n + 1), ‖c‖ ^ 2 ≤ ‖A v c‖ ^ 2 := by
    intro v hv c
    have h1 : A v c = ι c + fderiv ℝ u v c := rfl
    rw [h1, norm_add_sq_real, hDorth v hv c c, LinearIsometry.norm_map]
    nlinarith [sq_nonneg ‖fderiv ℝ u v c‖]
  have hinj : ∀ v ∈ D, Injective (A v) := by
    intro v hv c₁ c₂ h12
    have h1 := hnorm v hv (c₁ - c₂)
    rw [map_sub, h12, sub_self, norm_zero] at h1
    have h2 : ‖c₁ - c₂‖ = 0 := by nlinarith [norm_nonneg (c₁ - c₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h2)
  have hlin : ∀ v ∈ D, LinearIndependent ℝ (a v) := by
    intro v hv
    have hb := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.linearIndependent
    have hker : LinearMap.ker (A v : Euclid (n + 1) →ₗ[ℝ] Euclid P) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (hinj v hv)
    have := hb.map' (A v : Euclid (n + 1) →ₗ[ℝ] Euclid P) hker
    convert this using 1
    funext i
    simp [a, A, e]
  -- (4) `η(v) = J(v)⁻¹ a₀(v) ∧ ⋯ ∧ aₙ(v)` is a unit orientation of `span a(v)`
  obtain ⟨ev, hevc, hev⟩ := Submission.dgoj_exists_continuous_covector_eval P (n + 1)
  let η : Euclid (n + 1) → MultiVector P (n + 1) := fun v => (J v)⁻¹ • ev (a v)
  have hgpos : ∀ v ∈ D, 0 < gram v := fun v hv =>
    (Submission.codim1_rdo_gc_gram_unitOrientation P (n + 1) (a v) (hlin v hv)).1
  have hJpos : ∀ v ∈ D, 0 < J v := fun v hv => Real.sqrt_pos.2 (hgpos v hv)
  have hηJ : ∀ v ∈ D, ∀ α, η v α * J v = α (a v) := by
    intro v hv α
    simp only [η, smul_apply, hev, smul_eq_mul]
    field_simp [(hJpos v hv).ne']
  have hηunit : ∀ v ∈ D, IsUnitOrientationOf (η v) (Submodule.span ℝ (Set.range (a v))) :=
    fun v hv => (Submission.codim1_rdo_gc_gram_unitOrientation P (n + 1) (a v) (hlin v hv)).2 _
      (hηJ v hv)
  -- (5)–(6) `span a(v) = T_{G(v)}N`, hence `ξN(G(v)) = ±η(v)`
  have hrange := Submission.dsmc_chart_range_subset_tangentSpace P 1 (n + 1) N D G le_rfl hDopen
    (by simpa using hGc) (by rintro _ ⟨v, hv, rfl⟩; exact hmem v hv)
  have hsign : ∀ v ∈ D, ξN (G v) = η v ∨ ξN (G v) = -η v := by
    intro v hv
    obtain ⟨Q, hQ, hQξ⟩ := hξ.2 (G v) (hmem v hv)
    have hle : Submodule.span ℝ (Set.range (a v)) ≤ Q := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : a v i ∈ tangentSpace N (G v) := hrange v hv ⟨e i, hAe v hv i⟩
      rw [← hQ] at h1
      exact h1
    have hfin1 : Module.finrank ℝ (Submodule.span ℝ (Set.range (a v))) = n + 1 := by
      rw [finrank_span_eq_card (hlin v hv)]; simp
    have hfin2 : Module.finrank ℝ Q = n + 1 := by
      obtain ⟨τ, hτ, hτspan, -⟩ := hQξ
      rw [← hτspan, finrank_span_eq_card hτ.linearIndependent]; simp
    have hEq := Submodule.eq_of_le_of_finrank_eq hle (hfin1.trans hfin2.symm)
    have hηQ : IsUnitOrientationOf (η v) Q := hEq ▸ hηunit v hv
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P (n + 1) (η v) (ξN (G v)) Q hηQ hQξ
  -- (7) the sign function `s(v) = ξN(G(v))(L(η(v))) ∈ {1, -1}` is continuous on `D`
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P (n + 1)
  have hηL : ∀ v ∈ D, η v (L (η v)) = 1 := fun v hv => (hL _ _ (hηunit v hv)).2.2
  let s : Euclid (n + 1) → ℝ := fun v => ξN (G v) (L (η v))
  have hs : ∀ v ∈ D, s v = 1 ∨ s v = -1 := by
    intro v hv
    rcases hsign v hv with h | h
    · left; simp only [s, h]; exact hηL v hv
    · right; simp only [s, h, neg_apply]; rw [hηL v hv]
  have hGcont : ContinuousOn G D := hGc.continuousOn
  have hξG : ContinuousOn (fun v => ξN (G v)) D := hξ.1.comp hGcont (fun v hv => hmem v hv)
  have hac : ContinuousOn a D := continuousOn_pi.2 fun i =>
    continuousOn_const.add (hDuc.clm_apply continuousOn_const)
  have hgramc : ContinuousOn gram D := by
    have hM : ContinuousOn (fun v => (Matrix.of fun i j => inner ℝ (a v i) (a v j) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)) D :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j =>
        ((continuousOn_pi.1 hac) i).inner ((continuousOn_pi.1 hac) j)
    exact (continuous_id.matrix_det).comp_continuousOn hM
  have hJc : ContinuousOn J D := Real.continuous_sqrt.comp_continuousOn hgramc
  have hηc : ContinuousOn η D :=
    (hJc.inv₀ (fun v hv => (hJpos v hv).ne')).smul (hevc.comp_continuousOn hac)
  have hsc : ContinuousOn s D := hξG.clm_apply (L.continuous.comp_continuousOn hηc)
  -- (8) at the centre: `G(0) = x`, `a(0) = ιe`, `J(0) = 1`, so `η(0) = ξN(x)` and `s(0) = 1`
  have h0D : (0 : Euclid (n + 1)) ∈ D := mem_ball_self hδ
  have hG0 : G 0 = x := by simp [G, hu0]
  have ha0 : a 0 = fun i => ι (e i) := by funext i; simp [a, hDu0]
  have hgram0 : gram 0 = 1 := by
    have hM : (Matrix.of fun i j => inner ℝ (a 0 i) (a 0 j) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) = 1 := by
      ext i j
      rw [ha0, Matrix.of_apply, LinearIsometry.inner_map_map, Matrix.one_apply]
      simp [e, EuclideanSpace.inner_single_left]
    simp only [gram, hM, Matrix.det_one]
  have hJ0 : J 0 = 1 := by simp [J, hgram0]
  have hη0 : η 0 = ξN x := by
    ext α
    simp only [η, hJ0, inv_one, one_smul, hev, ha0, hιξ]
    rfl
  have hs0 : s 0 = 1 := by
    show ξN (G 0) (L (η 0)) = 1
    rw [hG0, ← hη0]; exact hηL 0 h0D
  -- (9) `D` is connected, so the intermediate value theorem gives `s = 1` on `D`
  have hsconst : ∀ v ∈ D, s v = 1 := by
    intro v hv
    rcases hs v hv with h | h
    · exact h
    · exfalso
      have hpre : IsPreconnected D := (convex_ball (0 : Euclid (n + 1)) δ).isPreconnected
      have hivt := hpre.intermediate_value hv h0D hsc
      rw [h, hs0] at hivt
      obtain ⟨w, hw, hw0⟩ := hivt (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
      rcases hs w hw with h' | h' <;> rw [hw0] at h' <;> norm_num at h'
  -- (10) hence `ξN(G(v)) = η(v)`, which is the claim
  intro v hv α
  have hpos : ξN (G v) = η v := by
    rcases hsign v hv with h | h
    · exact h
    · exfalso
      have h1 := hsconst v hv
      simp only [s, h, neg_apply] at h1
      rw [hηL v hv] at h1
      norm_num at h1
  show ξN (G v) α * J v = α (a v)
  rw [hpos]
  exact hηJ v hv α

/-- **Oriented graph chart** (Simon Ch. 2, §4 and 6.2.2).  Let `N` be an embedded `C²`
`(n+1)`-submanifold oriented by `ξN`, and `x ∈ N ∩ U`.  Near `x`, `N` is the graph
`G(v) = x + ιv + u(v)`, `v ∈ B_{δ₁}(0)`, of a `C²` map `u ⊥ ι(ℝⁿ⁺¹)` over the tangent plane
`T_xN = ι(ℝⁿ⁺¹)` (`ι` a linear isometry), with `u(0) = 0`, `‖Du‖ ≤ 1` and `‖u‖ < δ₂/2`; a point
`x + ιv + h ∈ N` with `|v| < δ₁`, `|h| < δ₂`, `h ⊥ ι(ℝⁿ⁺¹)` has `h = u(v)`; and
`ξN(G(v)) · J(v) = DG(v)e₁ ∧ ⋯ ∧ DG(v)eₙ₊₁` with `J(v) = det(⟨DG(v)eᵢ, DG(v)eⱼ⟩)^{1/2}`.
`ξN(x)` is a unit orientation of `T_xN`, so `ξN(x) = ιe₁ ∧ ⋯ ∧ ιeₙ₊₁` for some `ι` onto `T_xN`;
the inverse function theorem gives the graph over `ι(ℝⁿ⁺¹)` with `Du(0) = 0`; and the
orientation identity, true at `v = 0`, is transported over the connected ball `B_{δ₁}(0)`. -/
theorem Submission.codim1_rdo_graph_chart : ∀ (P n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (x : Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 (n + 1) N → IsOrientation (n + 1) N ξN → x ∈ N ∩ U → ∃ (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, (∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N ∧ ∀ α : Covector (Euclid P) (n + 1), ξN (x + ι v + u v) α * Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1)) (ι (EuclideanSpace.single j 1) + fderiv ℝ u v (EuclideanSpace.single j 1)))) = α (fun i => ι (EuclideanSpace.single i 1) + fderiv ℝ u v (EuclideanSpace.single i 1))) ∧ ∀ (v : Euclid (n + 1)) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid (n + 1), inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v := by
  intro P n U N ξN x hU hN hξ hx
  -- `ξN(x)` orients `Q = T_xN`; write it as `ξN(x) = ιe₁ ∧ ⋯ ∧ ιeₙ₊₁` with `ι(ℝⁿ⁺¹) = Q`
  obtain ⟨Q, hQ, hQξ⟩ := hξ.2 x hx.1
  obtain ⟨ι, hιQ, hιξ⟩ := Submission.codim1_rdo_gc_unitOrientation_isometry P n (ξN x) Q hQξ
  -- near `x`, `N` is the `C²` graph of `u ⊥ ι(ℝⁿ⁺¹)` over `ι(ℝⁿ⁺¹) = T_xN`, and `Du(0) = 0`
  obtain ⟨u, δ₁, δ₂, hδ₁, hδ₂, hball, hu0, hDu0, hu, hgraph, huniq⟩ :=
    Submission.codim1_rdo_gc_graph_over_tangent P (n + 1) U N x ι hU hN hx (hιQ.trans hQ)
  -- the orientation identity at `v = 0` propagates over `B_{δ₁}(0)` along the graph
  have horient := Submission.codim1_rdo_gc_orientation_along_graph P n N ξN x ι u δ₁ hξ hιξ hδ₁
    hu0 hDu0 (hu.of_le (by norm_num)) (fun v hv => (hgraph v hv).1)
    (fun v hv => (hgraph v hv).2.2.2)
  exact ⟨ι, u, δ₁, δ₂, hδ₁, hδ₂, hball, hu0, hu, fun v hv =>
    ⟨(hgraph v hv).1, (hgraph v hv).2.1, (hgraph v hv).2.2.1, (hgraph v hv).2.2.2, horient v hv⟩,
    huniq⟩
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** for `Lⁿ` with a closed set, `Lⁿ(B) = ∞` allowed (Simon Ch. 2, proof of
1.5, step 2, glued as in the infinite-measure case of Simon 1.15(2)).  On the bounded Borel shells
`S_j = {j ≤ ‖x‖ < j + 1}`, the compact form `dor_ims_lusin_measurable_continuousOn` gives compact
`K_j ⊆ B ∩ S_j` with `Lⁿ((B ∩ S_j) \ K_j) < δ_j` on which `g` is continuous, where `∑ δ_j < ε`.
As `K_j ⊆ S_j`, the family `(K_j)` is locally finite, so `C = ⋃ⱼ K_j` is closed and `g` is
continuous on `C`; and `B \ C ⊆ ⋃ⱼ (B ∩ S_j) \ K_j` has measure `< ε`. -/
theorem Submission.codim1_rdo_c1a_lusin_isClosed : ∀ (n : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (g : Euclid n → Y) (B : Set (Euclid n)), Measurable g → MeasurableSet B → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Euclid n), C ⊆ B ∧ IsClosed C ∧ ContinuousOn g C ∧ volume (B \ C) < ε := by
  intro n Y _ _ _ _ g B hg hB ε hε
  -- bounded Borel shells `S_j = {j ≤ ‖x‖ < j + 1}`, each of finite measure; `x ∈ S_⌊‖x‖⌋`
  set S : ℕ → Set (Euclid n) := fun j => {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hSμ : ∀ j, volume (S j) ≠ ∞ := fun j =>
    ((measure_mono fun x hx => mem_closedBall_zero_iff.mpr hx.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hxS : ∀ x : Euclid n, x ∈ S ⌊‖x‖⌋₊ := fun x =>
    ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- weights `δ_j > 0` with `∑ δ_j < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  -- Lusin on each shell: compact `K_j ⊆ B ∩ S_j`, defect `< δ_j`, `g` continuous on `K_j`
  choose K hK hKB hKμ hKg using fun j =>
    Submission.dor_ims_lusin_measurable_continuousOn n volume (B ∩ S j) g (δ j) hg
      (hB.inter (hSm j)) (ne_top_of_le_ne_top (hSμ j) (measure_mono inter_subset_right))
      (hδ j).ne'
  -- `K_j ⊆ S_j`, so `ball x 1` meets `K_j` only for the finitely many `j < ‖x‖ + 1`
  have hlf : LocallyFinite K := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyK, hyx⟩
    refine Nat.lt_ceil.mpr ((hKB j hyK).2.1.trans_lt ?_)
    calc ‖y‖ ≤ ‖x‖ + dist y x := norm_le_norm_add_const_of_dist_le le_rfl
      _ < ‖x‖ + 1 := by linarith [mem_ball.mp hyx]
  -- hence `C = ⋃ⱼ K_j` is closed and `g` is continuous on `C`
  refine ⟨⋃ j, K j, iUnion_subset fun j => (hKB j).trans inter_subset_left,
    hlf.isClosed_iUnion fun j => (hK j).isClosed,
    hlf.continuousOn_iUnion (fun j => (hK j).isClosed) hKg, ?_⟩
  -- `x ∈ B \ C` lies in `(B ∩ S_j) \ K_j` for `j = ⌊‖x‖⌋`
  calc volume (B \ ⋃ j, K j) ≤ volume (⋃ j, (B ∩ S j) \ K j) :=
        measure_mono fun x hx => mem_iUnion.mpr
          ⟨⌊‖x‖⌋₊, ⟨hx.1, hxS x⟩, fun hxK => hx.2 (mem_iUnion_of_mem _ hxK)⟩
    _ ≤ ∑' j, volume ((B ∩ S j) \ K j) := measure_iUnion_le _
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (hKμ j).le
    _ < ε := hδε
/-- **Egoroff's theorem** on `ℝⁿ` with a closed good set (steps 5–6 of Simon's proof of Ch. 2,
1.5).  If `C` is measurable (possibly `|C| = ∞`), `η_k` and `g` are measurable and `η_k → g`
pointwise on `C`, then for every `ε > 0` there is a closed `A ⊆ C` with `|C \ A| < ε` such that
`η_k → g` uniformly on every compact `Q ⊆ A`.  For weights `δ_j > 0` with `∑ δ_j < ε`, Egoroff on
the finite-measure sets `C ∩ B_{j+1}(0)` gives `t_j` with `|t_j| ≤ δ_j / 2`; put
`A₀ = C \ ⋃ t_j`.  Outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with excess `< δ_j / 2`,
so `A = (⋃ U_j)ᶜ ⊆ A₀` is closed and `C \ A ⊆ ⋃ (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`.  A compact
`Q ⊆ A` is bounded, so `Q ⊆ (C ∩ B_{j+1}(0)) \ t_j` for large `j`. -/
theorem Submission.codim1_rdo_c1a_egorov_isClosed : ∀ (n : ℕ) (C : Set (Euclid n)) (η : ℕ → Euclid n → ℝ) (g : Euclid n → ℝ), MeasurableSet C → (∀ k, Measurable (η k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q := by
  intro n C η g hC hη hg hconv ε hε
  -- weights `δ_j > 0` with `∑ δ_j < ε`; every `s ∩ B_{j+1}(0)` has finite measure
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have hB : ∀ (j : ℕ) (s : Set (Euclid n)), volume (s ∩ ball 0 (j + 1)) ≠ ∞ := fun j s =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Egoroff on `C_j = C ∩ B_{j+1}(0)`: `η_k → g` uniformly on `C_j \ t_j`, `|t_j| ≤ δ_j / 2`
  choose t htC htm htμ htu using fun j : ℕ =>
    tendstoUniformlyOn_of_ae_tendsto (μ := volume) (fun k => (hη k).stronglyMeasurable)
      hg.stronglyMeasurable (hC.inter measurableSet_ball) (hB j C)
      (ae_of_all _ fun x hx => hconv x hx.1) (ENNReal.half_pos (hδ j).ne')
  -- `A₀ = C \ ⋃ t_j`; outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with small excess
  have hA₀ : MeasurableSet (C \ ⋃ j, t j) := hC.diff (MeasurableSet.iUnion htm)
  choose U hUD hUo hUf hUμ using fun j : ℕ =>
    (hA₀.compl.inter measurableSet_ball).exists_isOpen_sdiff_lt (hB j _)
      (ENNReal.half_pos (hδ j).ne').ne'
  -- the balls cover `A₀ᶜ`, so the closed set `A = (⋃ U_j)ᶜ` lies in `A₀`
  have hAA₀ : (⋃ j, U j)ᶜ ⊆ C \ ⋃ j, t j := by
    refine compl_subset_comm.1 fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨j, hUD j ⟨hx, mem_ball.2 (by linarith)⟩⟩
  refine ⟨(⋃ j, U j)ᶜ, hAA₀.trans sdiff_subset, (isOpen_iUnion hUo).isClosed_compl, ?_, ?_⟩
  -- `C \ A ⊆ ⋃_j (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`, and each piece has measure `≤ δ_j`
  · calc volume (C \ (⋃ j, U j)ᶜ)
        ≤ volume (⋃ j, (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1))))) := by
          refine measure_mono fun x ⟨hxC, hxU⟩ => ?_
          obtain ⟨j, hj⟩ := mem_iUnion.1 (not_not.1 hxU)
          by_cases hxt : x ∈ ⋃ i, t i
          · obtain ⟨i, hi⟩ := mem_iUnion.1 hxt
            exact mem_iUnion.2 ⟨i, Or.inl hi⟩
          · exact mem_iUnion.2 ⟨j, Or.inr ⟨hj, fun h => h.1 ⟨hxC, hxt⟩⟩⟩
      _ ≤ ∑' j, volume (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1)))) :=
          measure_iUnion_le _
      _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (measure_union_le _ _).trans <|
          (add_le_add (htμ j) (hUμ j).le).trans (ENNReal.add_halves _).le
      _ < ε := hδε
  -- a compact `Q ⊆ A` is bounded, so `Q ⊆ C_j \ t_j` for large `j`
  · intro Q hQ hQA
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball 0
    obtain ⟨j, hj⟩ := exists_nat_ge R
    refine (htu j).mono fun x hx => ⟨⟨(hAA₀ (hQA hx)).1, ?_⟩, fun hxt => ?_⟩
    · exact ball_subset_ball (by linarith) (hR hx)
    · exact (hAA₀ (hQA hx)).2 (mem_iUnion.2 ⟨j, hxt⟩)
/-- **Whitney's hypothesis 1.6(∗) on a large closed set** (Simon Ch. 2, proof of Theorem 1.5).
Let `f : ℝⁿ → ℝ` be `L`-Lipschitz and differentiable at every point of the closed set `C`, with
`Df` continuous on `C`.  The remainder quotient `R(x, y) = |f(y) − f(x) − Df(x)(y − x)| / |y − x|`
is at most `2L`, and `η_k(x) = sup {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}` (`0` off `C`)
tends to `0` on `C`.  Each `{η_k > t}`, `t ≥ 0`, is relatively open in `C`, so `η_k` is Borel,
and Egorov's theorem in closed form gives a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that
`η_k → 0` uniformly on every compact `Q ⊆ A`.  Then `R(x, y) ≤ η_k(x) < ε'` for `x ∈ Q`,
`y ∈ A`, `0 < |x − y| < 1/(k + 1)`. -/
theorem Submission.codim1_rdo_c1a_whitney_remainder : ∀ (n : ℕ) (f : Euclid n → ℝ) (L : NNReal) (C : Set (Euclid n)), LipschitzWith L f → IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ f x) → ContinuousOn (fderiv ℝ f) C → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε' * ‖y - x‖ := by
  intro n f L C hf hC hdiff hDf ε hε
  classical
  -- the remainder quotient `R(x, y)`, bounded by `2L` since `‖Df(x)‖ ≤ L`
  let R : Euclid n → Euclid n → ℝ := fun x y => ‖f y - f x - fderiv ℝ f x (y - x)‖ / ‖y - x‖
  have hR_le : ∀ x y, R x y ≤ 2 * L := by
    intro x y
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ‖f y - f x‖ + ‖fderiv ℝ f x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖y - x‖ + L * ‖y - x‖ := by
          refine add_le_add ?_ ?_
          · rw [← dist_eq_norm, ← dist_eq_norm]
            exact hf.dist_le_mul y x
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      _ = 2 * L * ‖y - x‖ := by ring
  -- `η_k(x) = sup E_k(x)`, `E_k(x) = {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}`, on `C`
  let E : ℕ → Euclid n → Set ℝ := fun k x =>
    R x '' {y | y ∈ C ∧ 0 < dist y x ∧ dist y x < 1 / ((k : ℝ) + 1)}
  let η : ℕ → Euclid n → ℝ := fun k x => if x ∈ C then sSup (E k x) else 0
  have hη_nonneg : ∀ k x, 0 ≤ η k x := by
    intro k x
    by_cases hx : x ∈ C
    · simp only [η, ite_eq_left hx]
      exact Real.sSup_nonneg (by
        rintro _ ⟨y, -, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [η, ite_eq_right hx, le_refl]
  have hR_le_η : ∀ (k : ℕ) x y, x ∈ C → y ∈ C → 0 < dist y x → dist y x < 1 / ((k : ℝ) + 1) →
      R x y ≤ η k x := by
    intro k x y hx hy h0 h1
    simp only [η, ite_eq_left hx]
    exact le_csSup ⟨2 * L, by rintro _ ⟨z, -, rfl⟩; exact hR_le x z⟩ ⟨y, ⟨hy, h0, h1⟩, rfl⟩
  -- `η_k(x) → 0` for `x ∈ C`, by differentiability of `f` at `x`
  have hη_tendsto : ∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨ρ, hρ, hρx⟩ :=
      Metric.eventually_nhds_iff.mp ((hdiff x hx).hasFDerivAt.isLittleO.bound (half_pos he))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hle : η k x ≤ e / 2 := by
      simp only [η, ite_eq_left hx]
      refine Real.sSup_le ?_ (half_pos he).le
      rintro _ ⟨y, ⟨-, -, h1⟩, rfl⟩
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos he).le
        (hρx (h1.trans_le ((Nat.one_div_le_one_div hk).trans hN.le)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hη_nonneg k x)]
    exact hle.trans_lt (half_lt_self he)
  -- `{η_k > t}` is relatively open in the closed set `C` for `t ≥ 0`, so `η_k` is Borel
  have hη_meas : ∀ k, Measurable (η k) := by
    intro k
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · convert MeasurableSet.univ
      exact eq_univ_of_forall fun x => ht.trans_le (hη_nonneg k x)
    have hUC : η k ⁻¹' Ioi t ⊆ C := by
      intro x hx
      by_contra hxC
      have hx' : t < η k x := hx
      simp only [η, ite_eq_right hxC] at hx'
      exact absurd hx' (not_lt.mpr ht)
    have hnhds : ∀ x ∈ η k ⁻¹' Ioi t, η k ⁻¹' Ioi t ∪ Cᶜ ∈ 𝓝 x := by
      intro x hx
      have hxC := hUC hx
      have hxt : t < sSup (E k x) := by
        have hx' : t < η k x := hx
        simpa only [η, ite_eq_left hxC] using hx'
      have hne : (E k x).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Real.sSup_empty] at hxt
        exact absurd hxt (not_lt.mpr ht)
      obtain ⟨_, ⟨y, ⟨hy, h0, h1⟩, rfl⟩, hty⟩ := exists_lt_of_lt_csSup hne hxt
      -- `z ↦ R(z, y)` is continuous within `C` at `x`, as `f` and `Df|_C` are continuous
      have hsub : ContinuousWithinAt (fun z => y - z) C x :=
        continuousWithinAt_const.sub continuousWithinAt_id
      have hnum : ContinuousWithinAt (fun z => ‖f y - f z - fderiv ℝ f z (y - z)‖) C x :=
        ((continuousWithinAt_const.sub hf.continuous.continuousWithinAt).sub
          ((hDf x hxC).clm_apply hsub)).norm
      have hRy : ContinuousWithinAt (fun z => R z y) C x :=
        hnum.div hsub.norm (norm_sub_pos_iff.mpr (dist_pos.mp h0)).ne'
      have hdist : Tendsto (fun z => dist y z) (𝓝 x) (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist tendsto_id
      -- near `x`, every `z ∈ C` has `η_k(z) ≥ R(z, y) > t`
      filter_upwards [eventually_nhdsWithin_iff.mp (Filter.Tendsto.eventually_const_lt hty hRy),
        hdist.eventually_const_lt h0, hdist.eventually_lt_const h1] with z hz hz0 hz1
      by_cases hzC : z ∈ C
      · exact Or.inl ((hz hzC).trans_le (hR_le_η k z y hzC hy hz0 hz1))
      · exact Or.inr hzC
    have heq : η k ⁻¹' Ioi t = C ∩ interior (η k ⁻¹' Ioi t ∪ Cᶜ) := by
      refine Subset.antisymm
        (fun x hx => ⟨hUC hx, mem_interior_iff_mem_nhds.mpr (hnhds x hx)⟩) ?_
      rintro x ⟨hxC, hxI⟩
      rcases interior_subset hxI with hx | hx
      · exact hx
      · exact absurd hxC hx
    rw [heq]
    exact hC.measurableSet.inter isOpen_interior.measurableSet
  -- Egorov on `C`: a closed `A ⊆ C`, `Lⁿ(C \ A) < ε`, with `η_k → 0` uniformly on compact `Q ⊆ A`
  obtain ⟨A, hAC, hA, hCA, hunif⟩ := Submission.codim1_rdo_c1a_egorov_isClosed n C η
    (fun _ => 0) hC.measurableSet hη_meas measurable_const hη_tendsto ε hε
  refine ⟨A, hAC, hA, hCA, fun Q hQ hQA ε' hε' => ?_⟩
  -- `η_k < ε'` on `Q` for some `k`; take `δ = 1/(k + 1)`
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp (hunif Q hQ hQA) ε' hε').exists
  refine ⟨1 / ((k : ℝ) + 1), Nat.one_div_pos_of_nat, fun x hx y hy hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have h0 : 0 < dist y x := dist_pos.mpr hyx
  have hηx : η k x < ε' := by
    have hkx := hk x hx
    rw [dist_comm, Real.dist_eq, sub_zero] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hR : R x y ≤ ε' :=
    (hR_le_η k x y (hAC (hQA hx)) (hAC hy) h0 (by rwa [dist_comm])).trans hηx.le
  exact (div_le_iff₀ (norm_sub_pos_iff.mpr hyx)).mp hR

/-- **`C¹` approximation** (Simon Ch. 2, Theorem 1.5).  If `f : ℝⁿ → ℝ` is `K`-Lipschitz and
`ε > 0`, there is `g ∈ C¹(ℝⁿ)` with `Lⁿ({f ≠ g} ∪ {Df ≠ Dg}) < ε`.  By Rademacher (1.4) `f` is
differentiable on a Borel set `B` of full measure.  Lusin gives a closed `C ⊆ B` with `Df|C`
continuous and `Lⁿ(B \ C) < ε/2`; the remainder estimate gives a closed `A ⊆ C` with
`Lⁿ(C \ A) < ε/2` on which `f, Df` satisfy Whitney's condition 1.6(∗); Whitney's extension
theorem (1.6) gives `g ∈ C¹` with `g = f` and `Dg = Df` on `A`.  The exceptional set lies in
`Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem Submission.codim1_rdo_c1_approximation : ∀ (n : ℕ) (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε := by
  intro n f K hf ε hε
  -- Rademacher: `f` is differentiable on the Borel set `B`, whose complement is null
  set B : Set (Euclid n) := {x | DifferentiableAt ℝ f x}
  have hBm : MeasurableSet B := measurableSet_of_differentiableAt ℝ f
  have hBc : volume Bᶜ = 0 := ae_iff.mp hf.ae_differentiableAt
  -- Lusin: a closed `C ⊆ B` with `Df` continuous on `C` and `Lⁿ(B \ C) < ε/2`
  obtain ⟨C, hCB, hC, hDC, hBC⟩ := Submission.codim1_rdo_c1a_lusin_isClosed n (fderiv ℝ f) B
    (measurable_fderiv ℝ f) hBm (ε / 2) (ENNReal.half_pos hε.ne')
  -- a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` on which Whitney's condition 1.6(∗) holds
  obtain ⟨A, hAC, hA, hCA, hR⟩ := Submission.codim1_rdo_c1a_whitney_remainder n f K C hf hC
    (fun x hx => hCB hx) hDC (ε / 2) (ENNReal.half_pos hε.ne')
  -- Whitney: `g ∈ C¹` with `g = f` and `Dg = Df` on `A`
  obtain ⟨g, hg, hgf, hDg⟩ := Submission.codim1_rdo_c1a_whitney_extension n A f (fderiv ℝ f) hA
    hf.continuous.continuousOn (hDC.mono hAC) hR
  refine ⟨g, hg, ?_⟩
  -- the exceptional set misses `A`, and `Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`
  calc volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x}
      ≤ volume (Bᶜ ∪ (B \ C) ∪ (C \ A)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ A
        · rcases hx with hfg | hfg
          · exact absurd (hgf hxA).symm hfg
          · exact absurd (hDg x hxA).fderiv.symm hfg
        by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
    _ ≤ volume (Bᶜ ∪ (B \ C)) + volume (C \ A) := measure_union_le _ _
    _ ≤ volume Bᶜ + volume (B \ C) + volume (C \ A) := by gcongr; exact measure_union_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [hBc, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε

/-- **Simon Ch. 3, Lemma 1.2, "only if"** (chapter-03.txt lines 39–65, in the lemma at lines
25–66), in quantitative form: a countably `n`-rectifiable `M ⊆ ℝᴾ` is covered, up to an
`Hⁿ`-null set, by countably many images `Nₖ = gₖ(B_{rₖ}(cₖ))` of open balls under C¹ maps
`gₖ : ℝⁿ → ℝᴾ` with lower Lipschitz bounds `mₖ|a − b| ≤ |gₖ(a) − gₖ(b)|` on the balls, each `Nₖ`
Borel with `Hⁿ(Nₖ) < ∞`.  By Definition 1.1, `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ`
Lipschitz.  The C¹ approximation theorem (Simon Ch. 2, 1.5) covers `Fⱼ(ℝⁿ)` by C¹ images
`Gⱼᵢ(ℝⁿ)` up to a null set, and `Gⱼᵢ(ℝⁿ)` is covered, up to its null critical image, by images of
balls carrying lower Lipschitz bounds.  The triples `(j, i, q)` are enumerated by applying
`Nat.unpair` twice. -/
theorem Submission.codim1_rdo_rectifiable_c1_cover : ∀ (P n : ℕ) (M : Set (Euclid P)), CountablyRectifiable n M → ∃ (g : ℕ → Euclid n → Euclid P) (c : ℕ → Euclid n) (r m : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (g k)) ∧ (∀ k, 0 < m k) ∧ (∀ k, ∀ a ∈ ball (c k) (r k), ∀ b ∈ ball (c k) (r k), m k * ‖a - b‖ ≤ ‖g k a - g k b‖) ∧ (∀ k, MeasurableSet (g k '' ball (c k) (r k))) ∧ (∀ k, μHE[n] (g k '' ball (c k) (r k)) ≠ ∞) ∧ μHE[n] (M \ ⋃ k, g k '' ball (c k) (r k)) = 0 := by
  intro P n M hM
  -- Step 1 (Definition 1.1): `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ` `Kⱼ`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  choose K hK using hF
  -- Steps 2–3: C¹ maps `Gⱼᵢ` with `Hⁿ(Fⱼ(ℝⁿ) ∖ ⋃ᵢ Gⱼᵢ(ℝⁿ)) = 0`, by the C¹ approximation theorem.
  choose G hG hFG using fun j => Submission.codim1_rdo_c1cov_lipschitz_range_c1_cover P n
    (Submission.codim1_rdo_c1_approximation n) (F j) (K j) (hK j)
  -- Steps 4–6: balls `B_{rⱼᵢq}(cⱼᵢq)` on which `Gⱼᵢ` has lower Lipschitz constant `mⱼᵢq > 0`,
  -- whose images cover `Gⱼᵢ(ℝⁿ)` up to an `Hⁿ`-null set.
  choose c r m hm hlow hGB using fun j i => Submission.codim1_rdo_c1cov_regular_ball_cover P n
    (G j i) (hG j i)
  -- Step 7: `k ↦ (J k, I k, Q k)` maps `ℕ` onto `ℕ³` (`Nat.unpair` applied twice).
  obtain ⟨J, I, Q, hJIQ⟩ : ∃ J I Q : ℕ → ℕ, ∀ j i q, ∃ k, J k = j ∧ I k = i ∧ Q k = q :=
    ⟨fun k => k.unpair.1, fun k => k.unpair.2.unpair.1, fun k => k.unpair.2.unpair.2,
      fun j i q => ⟨Nat.pair j (Nat.pair i q), by simp⟩⟩
  -- Step 8: the pieces `Nₖ` are Borel with finite `Hⁿ`-measure.
  have hN k := Submission.codim1_rdo_c1cov_image_ball_borel_finite P n (G (J k) (I k))
    (c (J k) (I k) (Q k)) (r (J k) (I k) (Q k)) (hG (J k) (I k))
  refine ⟨fun k => G (J k) (I k), fun k => c (J k) (I k) (Q k), fun k => r (J k) (I k) (Q k),
    fun k => m (J k) (I k) (Q k), fun k => hG _ _, fun k => hm _ _ _, fun k => hlow _ _ _,
    fun k => (hN k).1, fun k => (hN k).2, ?_⟩
  -- Step 9: `M ∖ ⋃ₖ Nₖ` lies in the countable union of `Hⁿ`-null sets
  -- `M₀ ∪ ⋃ⱼ (Fⱼ(ℝⁿ) ∖ ⋃ᵢ Gⱼᵢ(ℝⁿ)) ∪ ⋃ⱼ ⋃ᵢ (Gⱼᵢ(ℝⁿ) ∖ ⋃_q Gⱼᵢ(B_{rⱼᵢq}(cⱼᵢq)))`.
  refine measure_mono_null ?_ (measure_union_null hM₀ (measure_union_null (measure_iUnion_null hFG)
    (measure_iUnion_null fun j => measure_iUnion_null (hGB j))))
  rintro y ⟨hyM, hyN⟩
  rcases hcover hyM with hy₀ | hyF
  · exact Or.inl hy₀
  obtain ⟨j, hyj⟩ := mem_iUnion.1 hyF
  by_cases hyG : y ∈ ⋃ i, range (G j i)
  · obtain ⟨i, hyi⟩ := mem_iUnion.1 hyG
    by_cases hyB : y ∈ ⋃ q, G j i '' ball (c j i q) (r j i q)
    · obtain ⟨q, hyq⟩ := mem_iUnion.1 hyB
      obtain ⟨k, rfl, rfl, rfl⟩ := hJIQ j i q
      exact absurd (mem_iUnion.2 ⟨k, hyq⟩) hyN
    · exact Or.inr (Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨i, hyi, hyB⟩⟩))
  · exact Or.inr (Or.inl (mem_iUnion.2 ⟨j, hyj, hyG⟩))
/-- A lower Lipschitz bound at a point passes to the derivative (step 1 of the `C¹`-piece tangent
argument, Simon Ch. 3, 1.6): if `U` is open, `a ∈ U`, `g` is differentiable at `a` and
`m|x − a| ≤ |g(x) − g(a)|` on `U`, then `m|v| ≤ |Dg(a)v|`.  For small `t > 0`, `a + tv ∈ U`
gives `m|v| ≤ |t⁻¹(g(a + tv) − g(a))|`, and the quotients tend to `Dg(a)v` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_c1pt_fderiv_lower_bound : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (U : Set (Euclid n)) (a : Euclid n) (m : ℝ), IsOpen U → a ∈ U → DifferentiableAt ℝ g a → (∀ x ∈ U, m * ‖x - a‖ ≤ ‖g x - g a‖) → ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := by
  intro P n g U a m hU ha hg hm v
  -- difference quotients `q(t) = t⁻¹ • (g (a + t • v) - g a)` tend to `Dg(a) v` as `t ↓ 0`
  have hq : Tendsto (fun t : ℝ => t⁻¹ • (g (a + t • v) - g a)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ g a v)) := by
    simpa only [inv_inv] using hg.hasFDerivAt.lim v (c := fun t : ℝ => t⁻¹)
      (tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero)
  -- `a + t • v → a` as `t → 0`, so `a + t • v ∈ U` for small `t` (`U` is a neighbourhood of `a`)
  have hline : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a (by simp)
  -- for small `t > 0`: `t * (m‖v‖) ≤ ‖g (a + t • v) - g a‖`, i.e. `m‖v‖ ≤ ‖q(t)‖`
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), m * ‖v‖ ≤ ‖t⁻¹ • (g (a + t • v) - g a)‖ := by
    filter_upwards [nhdsWithin_le_nhds (hline (hU.mem_nhds ha)), self_mem_nhdsWithin]
      with t htU ht
    have ht : (0 : ℝ) < t := ht
    have h := hm _ htU
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm] at h
    rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  -- the non-strict inequality passes to the limit along the nontrivial filter `𝓝[>] 0`
  exact ge_of_tendsto hq.norm hle
/-- **Simon Ch. 2, (3.2) and (3.5)** (area formula for the blow-ups of an injective regular
image): if `g` is differentiable on the Borel set `B`, injective on `B` and `Dg(a)` is injective
for `a ∈ B`, then for `s > 0`, every `z` and every `f`,
`∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + s b) f(s⁻¹(g(z + s b) − g(z))) dLⁿ(b)`, where
`B_s = {b | z + s b ∈ B}` and `J_g = √det(Dg* ∘ Dg)`.  The rescaled map
`φ(b) = s⁻¹(g(z + s b) − g(z))` is injective on `B_s` with `Dφ(b) = Dg(z + s b)` and
`φ(B_s) = η_{g(z),s}(g(B))`, so this is the area formula for `φ`.  That formula is proved in
place: the linear case (3.1), sharp `Hⁿ` estimates for maps close to an injective linear map,
a measurable partition into such pieces, and the transport of the Jacobian-weighted measure,
following the pinned SimonGMT `Chapter02.AreaApproximation`, `AreaDerivative`, `AreaFormula`
and `WeightedArea` proofs, which lie outside this file's imports. -/
theorem Submission.codim1_rdo_c1pt_rescaled_area_formula : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (B : Set (Euclid n)) (z : Euclid n) (s : ℝ) (f : Euclid P → ℝ), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ g a) → InjOn g B → (∀ a ∈ B, Injective (fderiv ℝ g a)) → 0 < s → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B), f y ∂μHE[n] = ∫ b in {b : Euclid n | z + s • b ∈ B}, Real.sqrt (((fderiv ℝ g (z + s • b)).adjoint ∘L fderiv ℝ g (z + s • b)).det) * f (s⁻¹ • (g (z + s • b) - g z)) := by
  intro P n g B z s f hB hdiff hinj hreg hs
  classical
  -- `J(L) = √det(L* ∘ L)` is the metric Jacobian of a linear map `L : ℝⁿ → ℝᴾ`
  obtain ⟨J, hJdef⟩ : ∃ J : (Euclid n →L[ℝ] Euclid P) → ℝ,
      J = fun L => Real.sqrt ((L.adjoint ∘L L).det) := ⟨_, rfl⟩
  have hJnonneg : ∀ L, 0 ≤ J L := fun L => by rw [hJdef]; exact Real.sqrt_nonneg _
  have hJcont : Continuous J := by
    rw [hJdef]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  /- Simon (3.1), the linear area formula: an injective `L` factors as `ι ∘ M` with `ι` a
  linear isometry onto its range and `M` an endomorphism of `ℝⁿ`, so
  `Hⁿ(L(A)) = Lⁿ(M(A)) = |det M| Lⁿ(A)`, and `J(L)² = det(M* M) = (det M)² ≠ 0`. -/
  have hlin : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L →
      0 < J L ∧ ∀ A : Set (Euclid n), μHE[n] (L '' A) = ENNReal.ofReal (J L) * volume A := by
    intro L hL
    have hV : Module.finrank ℝ (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) = n := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let e : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) ≃ₗᵢ[ℝ] Euclid n :=
      ((stdOrthonormalBasis ℝ _).reindex (finCongr hV)).repr
    let ιI : Euclid n →ₗᵢ[ℝ] Euclid P :=
      (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)).subtypeₗᵢ.comp e.symm.toLinearIsometry
    let M : Euclid n →L[ℝ] Euclid n := (e : _ →L[ℝ] Euclid n) ∘L L.rangeRestrict
    have hLιM : L = ιI.toContinuousLinearMap ∘L M := by
      ext1 x
      show L x = ((e.symm (e (L.rangeRestrict x)) :
        LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) : Euclid P)
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hιadj : ιI.toContinuousLinearMap.adjoint ∘L ιI.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp ιI.norm_map
    have hdetadj : (ContinuousLinearMap.adjoint M).det = M.det := by
      have h := congrArg Matrix.det (LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ) (M : Euclid n →ₗ[ℝ] Euclid n))
      rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h
      simp only [star_trivial] at h
      exact h
    have hdet : (L.adjoint ∘L L).det = M.det ^ 2 := by
      have h1 : L.adjoint ∘L L = M.adjoint ∘L M := by
        rw [hLιM, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ _ M, hιadj, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
      have h2 : (M.adjoint ∘L M).det = M.adjoint.det * M.det :=
        LinearMap.det_comp _ _
      rw [h1, h2, hdetadj, sq]
    have hJ : J L = |M.det| := by
      rw [hJdef]
      dsimp only
      rw [hdet, Real.sqrt_sq_eq_abs]
    have hMinj : LinearMap.ker (M : Euclid n →ₗ[ℝ] Euclid n) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      have h := congrArg (fun v => ((e.symm v : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) :
        Euclid P)) hxy
      simpa [M] using h
    refine ⟨?_, fun A => ?_⟩
    · rw [hJ]
      exact abs_pos.mpr (fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hMinj)
    · rw [hJ, hLιM, ContinuousLinearMap.coe_comp, Set.image_comp,
        LinearIsometry.coe_toContinuousLinearMap, ιI.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact MeasureTheory.Measure.addHaar_image_linearMap volume (M : Euclid n →ₗ[ℝ] Euclid n) A
  -- comparison of pairwise distances gives comparison of the `Hⁿ` measures of the images
  have hdistcmp : ∀ (u v : Euclid n → Euclid P) (T : Set (Euclid n)) (K : NNReal), InjOn v T →
      (∀ x ∈ T, ∀ y ∈ T, dist (u x) (u y) ≤ K * dist (v x) (v y)) →
      μHE[n] (u '' T) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (v '' T) := by
    intro u v T K hv hK
    have hh : LipschitzOnWith K (u ∘ invFunOn v T) (v '' T) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy] using hK x hx y hy
    have himage : (u ∘ invFunOn v T) '' (v '' T) = u '' T := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  /- Near an injective `L`, one radius `δ` controls both the Jacobian of nearby linear maps and
  the `Hⁿ` measure of images under maps `δ`-approximating `L`, up to a factor `q > 1`. -/
  have hradius : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
          ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
            ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
        (∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P), ApproximatesLinearOn u L T δ →
          μHE[n] (u '' T) ≤ q * μHE[n] (L '' T) ∧ μHE[n] (L '' T) ≤ q * μHE[n] (u '' T)) := by
    intro L hL q hq
    obtain ⟨K, -, hK⟩ := (L : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hqR : (1 : ℝ) < q := hq
    have hJpos := (hlin L hL).1
    have hmul : J L < (q : ℝ) * J L := lt_mul_of_one_lt_left hJpos hqR
    have hnear : ∀ᶠ L' in 𝓝 L, J L' < (q : ℝ) * J L ∧ J L < (q : ℝ) * J L' :=
      (hJcont.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hJcont.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεev : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
      (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds,
        hεev.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    -- `‖(u x - u y) - L(x - y)‖ ≤ δ K ‖L x - L y‖` on `T`
    have herror : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P),
        ApproximatesLinearOn u L T δ → ∀ x ∈ T, ∀ y ∈ T,
          ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      intro T u hu x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      calc ‖u x - u y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hu x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    refine ⟨δ, hδ, fun L' hL' => ?_, fun T u hu => ⟨?_, ?_⟩⟩
    · have hdist : dist L' L < ε := by
        rw [dist_eq_norm]
        exact hL'.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hdist
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h1.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h2.le
    · refine (hdistcmp u L T (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖u x - u y‖ ≤ ‖u x - u y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
            add_le_add (herror T u hu x hx y hy) le_rfl
          _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
      · gcongr
        rw [← ENNReal.coe_pow]
        exact ENNReal.coe_le_coe.mpr hδupper.le
    · have hδR : (δ : ℝ) * K < 1 := hδK
      have hdist : ∀ x ∈ T, ∀ y ∈ T,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (u x) (u y) := by
        intro x hx y hy
        have h1 := herror T u hu x hx y hy
        have htriangle := norm_le_norm_add_norm_sub (u x - u y) (L x - L y)
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
        linarith only [h1, htriangle]
      have huinj : InjOn u T := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      refine (hdistcmp L u T _ huinj hdist).trans ?_
      gcongr
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlower.le
  /- On almost every point of a measurable piece where `u` is `δ`-approximated by `A`, the
  derivative is `δ`-close to `A` (the density-point argument of Mathlib's
  `ApproximatesLinearOn.norm_fderiv_sub_le`, for rectangular derivatives). -/
  have hderivbound : ∀ (u : Euclid n → Euclid P) (T : Set (Euclid n)) (A : Euclid n →L[ℝ] Euclid P)
      (δ : NNReal) (u' : Euclid n → Euclid n →L[ℝ] Euclid P), ApproximatesLinearOn u A T δ →
      MeasurableSet T → (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) →
      ∀ᵐ x ∂(volume.restrict T), ‖u' x - A‖₊ ≤ δ := by
    intro u T A δ u' hf hT hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume T, ae_restrict_mem hT]
    intro x hx xT
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun w => ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - A) w‖ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖w‖ + 0) + ‖u' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ := MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one volume T x hx
      (closedBall w ε) measurableSet_closedBall (measure_closedBall_pos volume w εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ T ⊆ {y : Euclid n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xT).isLittleO εpos)
    have B₂ := (eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := x)
      (isBounded_closedBall (x := w) (r := ε)) (ball_mem_nhds x ρpos)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    obtain ⟨r, ⟨y, ⟨yT, hy⟩⟩, rρ, rpos⟩ := (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, aw, ya⟩ : ∃ a, a ∈ closedBall w ε ∧ y = x + r • a := by
      have hy' := hy
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy'
      rcases hy' with ⟨a, aw, ha⟩
      exact ⟨a, aw, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖w‖ + ε :=
      calc ‖a‖ = ‖w + (a - w)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖w‖ + ‖a - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε := by grw [mem_closedBall_iff_norm.1 aw]
    have I : r * ‖(u' x - A) a‖ ≤ r * (δ + ε) * (‖w‖ + ε) :=
      calc r * ‖(u' x - A) a‖ = ‖(u' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - A (y - x) - (u y - u x - (u' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - A (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yT _ xT) (hρ ⟨rρ hy, yT⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖w‖ + ε) := by gcongr
    calc ‖(u' x - A) w‖ = ‖(u' x - A) a + (u' x - A) (w - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(u' x - A) a‖ + ‖(u' x - A) (w - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ‖w - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at aw
          gcongr
  /- Simon (3.2), measure form: for `u` injective on a measurable `T`, differentiable along `T`
  with injective derivative `u'`, `Hⁿ(u(T)) = ∫_T J(u'(x)) dLⁿ(x)`.  Partition `T` into
  measurable pieces on which `u` is close to linear maps `A i = u'(yᵢ)`, compare on each piece
  up to a factor `q²`, sum, and let `q ↓ 1`. -/
  have hmeasure : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet T →
      (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) → (∀ x ∈ T, Injective (u' x)) → InjOn u T →
      μHE[n] (u '' T) = ∫⁻ x in T, ENNReal.ofReal (J (u' x)) := by
    intro T u u' hT hu' hreg' hinj'
    have hcmp : ∀ q : NNReal, 1 < q →
        μHE[n] (u '' T) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' T) := by
      intro q hq
      rcases eq_empty_or_nonempty T with rfl | hTne
      · simp
      have hchoice : ∀ L : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
              ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
          (∀ (T' : Set (Euclid n)) (v : Euclid n → Euclid P), ApproximatesLinearOn v L T' δ →
            μHE[n] (v '' T') ≤ q * μHE[n] (L '' T') ∧
              μHE[n] (L '' T') ≤ q * μHE[n] (v '' T'))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, h1, h2⟩ := hradius L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨1, one_pos, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u T u' hu' δ
          (fun L => (hδpos L).ne')
      have hAreg : ∀ i, Injective (A i) := by
        intro i
        obtain ⟨x, hx, hA⟩ := hactual hTne i
        rw [hA]
        exact hreg' x hx
      have hTeq : T = ⋃ i, T ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[n] (u '' T) = ∑' i, μHE[n] (u '' (T ∩ t i)) := by
        conv_lhs => rw [hTeq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj' inter_subset_left inter_subset_left
        · intro i
          apply (hT.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hu' x hx.1).continuousWithinAt.mono inter_subset_left
          · exact hinj'.mono inter_subset_left
      have hsumintegral : ∫⁻ x in T, ENNReal.ofReal (J (u' x)) =
          ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
        conv_lhs => rw [hTeq]
        exact lintegral_iUnion (fun i => hT.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[n] (u '' (T ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by
        intro i
        have hJ := (hδ (A i) (hAreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (A i) (hAreg i)).2 (T ∩ t i) u (happrox i)
        have hlinA := (hlin (A i) (hAreg i)).2 (T ∩ t i)
        rw [hlinA] at harea_upper harea_lower
        have hderiv := hderivbound u (T ∩ t i) (A i) (δ (A i)) u' (happrox i) (hT.inter (ht i))
          (fun x hx => (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
          calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ ∫⁻ _ in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (A i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).1
            _ = q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (J (A i)) * volume (T ∩ t i) ≤
            q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
          calc ENNReal.ofReal (J (A i)) * volume (T ∩ t i)
              = ∫⁻ _ in T ∩ t i, ENNReal.ofReal (J (A i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (u' x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).2
            _ = q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[n] (u '' (T ∩ t i)) ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
                rw [pow_two, mul_assoc]
        · calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (T ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc ∑' i, μHE[n] (u '' (T ∩ t i))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_mul_left
      · calc ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, μHE[n] (u '' (T ∩ t i)) := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).2
  /- Simon (3.5), Bochner form: the Jacobian-weighted measure on `S` is transported by `u`
  to `Hⁿ ⌞ u(S)`, so `∫_{u(S)} f dHⁿ = ∫_S J(u'(x)) f(u(x)) dLⁿ(x)` for every `f`. -/
  have hbochner : ∀ (S : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet S →
      (∀ x ∈ S, HasFDerivAt u (u' x) x) → (∀ x ∈ S, Injective (u' x)) → InjOn u S →
      Measurable u' → ∫ y in u '' S, f y ∂μHE[n] = ∫ x in S, J (u' x) * f (u x) := by
    intro S u u' hS hu' hreg' hinj' hmeas'
    have hcont : ContinuousOn u S := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hS hinj'
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hJm : Measurable (fun x => J (u' x)) := hJcont.measurable.comp hmeas'
    have hmap : Measure.map (S.domRestrict u)
        ((volume.withDensity (fun x => ENNReal.ofReal (J (u' x)))).comap
          (Subtype.val : S → Euclid n)) = μHE[n].restrict (u '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((S.domRestrict u) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict u) ⁻¹' t) ⊆ S := by
        rintro x ⟨w, _, rfl⟩
        exact w.property
      rw [withDensity_apply _ hBm, ← hmeasure _ u u' hBm
        (fun x hx => (hu' x (hBS hx)).hasFDerivWithinAt) (fun x hx => hreg' x (hBS hx))
        (hinj'.mono hBS), Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨hw, ⟨w, w.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    simp only [Set.domRestrict_apply, ← Function.comp_apply (f := f), ENNReal.ofReal]
    rw [← hsub.integral_map, map_comap_subtype_coe hS,
      setIntegral_withDensity_eq_setIntegral_smul₀ (hJm.real_toNNReal.aemeasurable) _ hS]
    congr with x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hJnonneg _), smul_eq_mul, comp_apply]
  -- the rescaled map `φ(b) = s⁻¹ • (g (z + s • b) - g z)` on `B_s = {b | z + s • b ∈ B}`
  have hs0 : s ≠ 0 := hs.ne'
  have hBs : MeasurableSet {b : Euclid n | z + s • b ∈ B} :=
    hB.preimage ((measurable_const_add z).comp (measurable_const_smul s))
  have hderiv : ∀ b ∈ {b : Euclid n | z + s • b ∈ B},
      HasFDerivAt (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) (fderiv ℝ g (z + s • b)) b := by
    intro b hb
    have h1 : HasFDerivAt (fun b' : Euclid n => z + s • b')
        (s • ContinuousLinearMap.id ℝ (Euclid n)) b :=
      ((hasFDerivAt_id b).const_smul s).const_add z
    refine ((((hdiff _ hb).hasFDerivAt.comp b h1).sub_const (g z)).const_smul s⁻¹).congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ hs0]
  have hinjφ : InjOn (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z))
      {b : Euclid n | z + s • b ∈ B} := by
    intro b hb b' hb' h
    have h' : g (z + s • b) = g (z + s • b') := by
      simpa [hs0] using h
    exact smul_right_injective _ hs0 (add_left_cancel (hinj hb hb' h'))
  have himage :
      (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) '' {b : Euclid n | z + s • b ∈ B} =
        Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨g (z + s • b), ⟨z + s • b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s⁻¹ • (a - z), ?_, ?_⟩
      · show z + s • s⁻¹ • (a - z) ∈ B
        rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
      · show s⁻¹ • (g (z + s • s⁻¹ • (a - z)) - g z) = s⁻¹ • (g a - g z)
        rw [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
  have hmeasf' : Measurable (fun b : Euclid n => fderiv ℝ g (z + s • b)) :=
    (measurable_fderiv ℝ g).comp ((measurable_const_add z).comp (measurable_const_smul s))
  rw [← himage, hbochner _ _ (fun b : Euclid n => fderiv ℝ g (z + s • b)) hBs hderiv
    (fun b hb => hreg _ hb) hinjφ hmeasf', hJdef]
/-- **Simon Ch. 2, (3.1)** in integral form (area formula for an injective linear map): for an
injective linear `L : ℝⁿ → ℝᴾ` and every `f`, `∫_{L(ℝⁿ)} f dHⁿ = √det(L* ∘ L) ∫_{ℝⁿ} f(Lb) dLⁿ(b)`.
Write `L = W ∘ A` with `W` a linear isometry of `ℝⁿ` onto `L(ℝⁿ)` and `A` an automorphism of `ℝⁿ`;
then `Hⁿ⌞L(ℝⁿ) = W#Lⁿ`, `Lⁿ = |det A| A#Lⁿ` and `det(L* ∘ L) = det(A* ∘ A) = (det A)²`. -/
theorem Submission.codim1_rdo_c1pt_linear_range_integral : ∀ (P n : ℕ) (L : Euclid n →L[ℝ] Euclid P) (f : Euclid P → ℝ), Injective L → ∫ y in (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = Real.sqrt ((L.adjoint ∘L L).det) * ∫ b, f (L b) := by
  intro P n L f hL
  -- `L = W ∘ A`: `W` is a linear isometry of `ℝⁿ` onto `R = L(ℝⁿ)` (via an orthonormal basis of
  -- `R`, which has dimension `n`) and `A` is a surjective endomorphism of `ℝⁿ`
  obtain ⟨W, A, hWA, hA⟩ : ∃ (W : Euclid n →ₗᵢ[ℝ] Euclid P) (A : Euclid n →L[ℝ] Euclid n),
      (∀ x, W (A x) = L x) ∧ Surjective A := by
    let R := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)
    have hrank : Module.finrank ℝ R = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Euclid n →ₗ[ℝ] Euclid P)) hL).trans
        finrank_euclideanSpace_fin
    let bv : OrthonormalBasis (Fin n) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hrank)
    refine ⟨R.subtypeₗᵢ.comp bv.repr.symm.toLinearIsometry,
      bv.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        L.codRestrict R (fun x => LinearMap.mem_range_self _ x), fun x => by simp, fun z => ?_⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bv.repr.symm z).2
    refine ⟨x, ?_⟩
    have hx' : L.codRestrict R (fun x => LinearMap.mem_range_self _ x) x = bv.repr.symm z :=
      Subtype.ext hx
    simp [hx']
  have hAinj : Injective A := fun x y h => hL (by rw [← hWA x, ← hWA y, h])
  -- `L(ℝⁿ) = W(ℝⁿ)`
  have hrange : (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) =
      Set.range W := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hA.range_comp W]
    congr 1
    funext x
    exact (hWA x).symm
  -- `Hⁿ⌞W(ℝⁿ) = W#Hⁿ` (`W` is an isometry) and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hW : ∫ y in Set.range W, f y ∂μHE[n] = ∫ x, f (W x) := by
    rw [← W.isometry.map_euclideanHausdorffMeasure,
      W.isometry.isClosedEmbedding.measurableEmbedding.integral_map,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- change of variables `x = A b` on `ℝⁿ`
  have hAcv : ∫ x, f (W x) = |A.det| * ∫ b, f (W (A b)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) hAinj.injOn (fun x => f (W x))
    rw [Set.image_univ, hA.range_eq, Measure.restrict_univ] at h
    rw [h, ← integral_const_mul]
    simp only [smul_eq_mul]
  -- `L* ∘ L = A* ∘ W* ∘ W ∘ A = A* ∘ A`, so `det (L* ∘ L) = (det A)²`
  have hdet : (L.adjoint ∘L L).det = A.det ^ 2 := by
    have hL' : L = W.toContinuousLinearMap ∘L A := ContinuousLinearMap.ext fun x => (hWA x).symm
    have h1 : L.adjoint ∘L L = A.adjoint ∘L A := by
      rw [hL', ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _), W.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have hadj : LinearMap.det (LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n)) =
        LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
        Matrix.det_conjTranspose, LinearMap.det_toMatrix, star_trivial]
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap, hadj, sq]
  rw [hrange, hW, hAcv, hdet, Real.sqrt_sq_eq_abs]
  simp only [hWA]
/-- Rescaled integrals over a `C¹` piece converge to the integral over its tangent map (proof of
Simon Ch. 3, Theorem 1.6, with a continuous weight `h`).  With `L = Dg(z)`,
`B_s = {b : z + s b ∈ B}` and `φ_s(b) = s⁻¹ (g(z + s b) − g(z))`:
`∫_{B_s} h(z + s b) f(φ_s(b)) db → h(z) ∫ f(L b) db` as `s ↓ 0`.  Take `f = 0` off `B_R(0)` and
`B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R`, `K = B̄_{R/m}(0) ⊆ B_s`, and the integrand vanishes on
`B_s \ K` because `|φ_s(b)| ≥ m|b| > R`.  On `K` it is bounded by `sup_{B̄_ρ(z)} |h| · sup |f|` and
tends pointwise to `h(z) f(L b)`, so dominated convergence applies.  Finally `f(L b) = 0` off `K`
because `|L b| ≥ m|b| > R`. -/
theorem Submission.codim1_rdo_c1pt_rescaled_integral_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), Continuous g → DifferentiableAt ℝ g z → Continuous h → IsOpen B → z ∈ B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hg hgz hh hB hzB hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Step 3: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ closedBall z ρ := by
    intro s hs hss b hb
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 4: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hB.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hρB (hKB s hs.1 hs.2.le b hb)
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 5: uniform bounds
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 6–8: dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => Continuous.aestronglyMeasurable ?_
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      exact (hh.comp hz).mul (hf.comp (((hg.comp hz).sub continuous_const).const_smul s⁻¹))
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.tendsto z).comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 9: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc

/-- **Approximate tangent space of a `C¹` piece** (Simon Ch. 3, 1.4; the step "since `x ∈ Nⱼ` and
`Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of the proof of
1.6 "⇒", chapter-03.txt lines 113–125).  Let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on
`B = B_r(c)`, `m > 0`, and `z ∈ B`.  Then `|Dg(a)v| ≥ m|v|`, so `Dg(a)` is injective for `a ∈ B`,
`g` is injective on `B` and `T = Dg(z)(ℝⁿ)` has dimension `n`.  By the area formula (Ch. 2, 3.2,
3.3, 3.5), `∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + sb) f(s⁻¹(g(z + sb) − g(z))) db` for
`s > 0`.  The Jacobian `J_g = √det(Dg* ∘ Dg)` is continuous, so these integrals tend to
`J_g(z) ∫ f(Dg(z)b) db`, which is `∫_T f dHⁿ` by the linear area formula (Ch. 2, 3.1). -/
theorem Submission.codim1_rdo_c1_piece_approxTangent : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r m : ℝ), ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt n (g '' ball c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n g c r m hg hm hlip z hz
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- a vector `x` with `m|x| ≤ 0` vanishes, since `m > 0`
  have hzero : ∀ x : Euclid n, m * ‖x‖ ≤ 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hm)
  -- Step 1, `m|v| ≤ |Dg(a)v|` for `a ∈ B`, so `Dg(a)` is injective; `g` is injective on `B`.
  have hlow : ∀ a ∈ ball c r, ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := fun a ha =>
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P n g (ball c r) a m isOpen_ball ha (hdiff a)
      fun x hx => hlip x hx a ha
  have hinj : ∀ a ∈ ball c r, Injective (fderiv ℝ g a) := by
    intro a ha v w hvw
    have h := hlow a ha (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinjOn : InjOn g (ball c r) := by
    intro a ha b hb hab
    have h := hlip a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  -- Step 2, the Jacobian `J_g(a) = √det(Dg(a)* ∘ Dg(a))` is continuous.
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hJ : Continuous fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous.comp hcont).clm_comp hcont))
  refine ⟨?_, fun f => ?_⟩
  · -- `dim T = n`
    rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P))
      (hinj z hz), finrank_euclideanSpace_fin]
  · -- Steps 3–8, `∫_T f dHⁿ = J_g(z) ∫ f(Dg(z)b) db` is the limit of the rescaled area formulas.
    rw [Submission.codim1_rdo_c1pt_linear_range_integral P n (fderiv ℝ g z) f (hinj z hz)]
    refine (Submission.codim1_rdo_c1pt_rescaled_integral_tendsto P n g
      (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det)) (ball c r) z m f
      hdiff.continuous (hdiff z) hJ isOpen_ball hz hm (fun a ha => hlip a ha z hz) (hlow z hz)
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P n g (ball c r) z s f
      measurableSet_ball (fun a _ => hdiff a) hinjOn hinj hs).symm
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in an open set**
(Simon Ch. 1, 3.6 and Remark 3.7(2); chapter-01.txt lines 700–711).  If `U ⊆ ℝᴾ` is open and
`S ⊆ ℝᴾ` is Borel with `Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e.
`x ∈ U \ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B(y, r_y)` with
`B̄(y, r_y) ⊆ U` cover `U` (Lindelöf); the upper density theorem applies to each piece
`S ∩ B(y, r_y)`, of finite measure, and the piece agrees with `S` on small balls about
`x ∈ B(y, r_y)`. -/
theorem Submission.doraggt_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U` (Lindelöf).
  have hrad : ∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hrad
  obtain ⟨D, hDU, hDc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    (fun y hy => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (hr0 y hy)))
  -- Steps 2 and 3, the upper density theorem for each finite-measure piece `S ∩ B(y, r y)`,
  -- simultaneously for the countably many `y ∈ D`.
  have hae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] ((S ∩ ball y (r y)) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    refine Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball) ?_
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
  -- Step 4, near `x ∈ B(y, r y)` the piece and `S` agree.
  filter_upwards [hae] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcover hxU)
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεball)]
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]
/-- Changing a set by parts of vanishing `n`-density at `x` does not change its approximate
tangent spaces at `x` (Simon Ch. 3, Definition 1.4 and Remark 1.5(2); proof of 3.1.6).  For
`f ∈ C_c(ℝᴾ)` with `|f| ≤ C`, `f = 0` off `B̄_R(0)` and `0 < r < r₀/R`, comparing both blow-up
integrals with the one over `η_{x,r}(A ∩ B)` gives `|∫_{η_{x,r}(A)} f dHⁿ − ∫_{η_{x,r}(B)} f dHⁿ| ≤
C Hⁿ(η_{x,r}(A \ B) ∩ B̄_R(0)) + C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`, and
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`. -/
theorem Submission.doraggt_approxTangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → 0 < r₀ → μHE[n] (A ∩ closedBall x r₀) ≠ ∞ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((A \ B) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n A B x r₀ hA hB hr₀ hAfin hBfin hAB hBA
  -- Step 1: it suffices that `∫_{η_r(A)} f − ∫_{η_r(B)} f → 0` for every `f ∈ C_c`
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n A B x fun f => ?_
  -- Step 2: `|f| ≤ C`, and `f = 0` off `B̄_R(0)` for some `R > 0`
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R, hR, hzero⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
      f.hasCompactSupport.isCompact.isBounded
    exact ⟨max R₁ 1, lt_max_of_lt_right one_pos, fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (closedBall_subset_closedBall (le_max_left _ _) (hR₁ h))⟩
  -- Step 3: for `0 < r < r₀ / R`, `Hⁿ(η_r(S) ∩ B̄_R(0)) ≤ r⁻ⁿ Hⁿ(S ∩ B̄_{r₀}(x)) < ∞`
  have hfin : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall x r₀) ≠ ∞ → ∀ r ∈ Ioo 0 (r₀ / R),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) ≠ ∞ := by
    intro S hS r hr
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr.1).ne'))
      (ne_top_of_le_ne_top hS (measure_mono (inter_subset_inter_right _
        (closedBall_subset_closedBall ((lt_div_iff₀ hR).mp hr.2).le))))
  -- Step 4: `C Hⁿ(η_r(S) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`
  have herr : ∀ S : Set (Euclid P),
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun r : ℝ => C *
        (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
        (𝓝[>] 0) (𝓝 0) := by
    intro S hS
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ => μHE[n] (S ∩ closedBall x ρ)) R hR hS)).const_mul C
    rw [ENNReal.toReal_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Function.comp_apply, Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr]
  -- Step 5: for `0 < r < r₀ / R`, compare both integrals with the one over `η_r(A ∩ B)`
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]‖ ≤
        C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A \ B) ∩
            closedBall 0 R)).toReal +
          C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩
            closedBall 0 R)).toReal := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
    have hA' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) A x r R C f
      f.continuous (hA.inter hB) hA inter_subset_left hr.1 (hfin A hAfin r hr) hC hzero
    have hB' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) B x r R C f
      f.continuous (hA.inter hB) hB inter_subset_right hr.1 (hfin B hBfin r hr) hC hzero
    rw [Set.sdiff_self_inter] at hA'
    rw [Set.sdiff_inter_self_eq_sdiff] at hB'
    rw [← sub_sub_sub_cancel_right _ _
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ B), f y ∂μHE[n])]
    exact (norm_sub_le _ _).trans (add_le_add hA' hB')
  -- Step 6: squeeze
  have hlim := (herr _ hAB).add (herr _ hBA)
  rw [add_zero] at hlim
  exact squeeze_zero_norm' hle hlim

/-- **Approximate tangent planes of two locally finite sets agree a.e. on their overlap** (Simon
Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 "⇒", chapter-03.txt lines 86–90 and 113–146,
stated symmetrically for two sets).  Let `W ⊆ ℝᴾ` be open and `A`, `B` Borel with `Hⁿ(A ∩ K)` and
`Hⁿ(B ∩ K)` finite for every compact `K ⊆ W`.  By the upper density theorem the densities of
`A ∖ B` and `B ∖ A` vanish at `Hⁿ`-a.e. `x ∈ W ∩ A ∩ B`; a closed ball about such `x` inside `W`
has finite measure in `A` and in `B`, so `A` and `B` have the same approximate tangent planes at
`x`. -/
theorem Submission.doraggt_ae_approxTangent_transfer : ∀ (P n : ℕ) (W A B : Set (Euclid P)), IsOpen W → MeasurableSet A → MeasurableSet B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (A ∩ K) ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ W → x ∈ A → x ∈ B → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n W A B hW hA hB hAfin hBfin
  -- Step 1, the densities of `A ∖ B` and `B ∖ A` vanish `Hⁿ`-a.e. on `W` off these sets.
  have hAB := Submission.doraggt_local_density_zero P n W (A \ B) hW (hA.diff hB)
    fun K hK hKW => ne_top_of_le_ne_top (hAfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  have hBA := Submission.doraggt_local_density_zero P n W (B \ A) hW (hB.diff hA)
    fun K hK hKW => ne_top_of_le_ne_top (hBfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 2, at such `x ∈ W ∩ A ∩ B`, `x ∉ A ∖ B` and `x ∉ B ∖ A`, so both densities vanish.
  filter_upwards [hAB, hBA] with x hxAB hxBA hxW hxA hxB
  -- Step 3, `B̄(x, ε/2) ⊆ B(x, ε) ⊆ W` is compact, so `A` and `B` have finite measure in it.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  have hsub : closedBall x (ε / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Step 4, the approximate tangent planes of `A` and `B` at `x` agree.
  exact Submission.doraggt_approxTangent_iff_of_density_zero P n A B x (ε / 2) hA hB
    (half_pos hε) (hAfin _ (isCompact_closedBall x (ε / 2)) hsub)
    (hBfin _ (isCompact_closedBall x (ε / 2)) hsub) (hxAB hxW fun h => h.2 hxB)
    (hxBA hxW fun h => h.2 hxA)

/-- **A countably `n`-rectifiable set has approximate tangent planes `Hⁿ`-a.e.** (Simon Ch. 3,
Theorem 1.6 "⇒", chapter-03.txt lines 109–143, with Lemma 1.2 and Remark 1.3, lines 25–76).  Let
`M ⊆ ℝᴾ` be Borel and countably `n`-rectifiable with `Hⁿ(M ∩ K) < ∞` for every compact `K`.  Up to
an `Hⁿ`-null set, `M` is covered by Borel pieces `N_k = g_k(B_{r_k}(c_k))` of finite measure, with
`g_k` of class `C¹` and `m_k|a − b| ≤ |g_k(a) − g_k(b)|` on the ball (Lemma 1.2).  `N_k` has the
approximate tangent plane `Dg_k(z)(ℝⁿ)` at each `g_k(z)`, and by the upper density theorem `M` and
`N_k` have the same approximate tangent planes at `Hⁿ`-a.e. point of `M ∩ N_k`.  The countably many
exceptional null sets combine, so `T_w M` exists for `Hⁿ`-a.e. `w ∈ M`.  The pieces need not be
disjoint (Remark 1.3). -/
theorem Submission.codim1_rdo_rectifiable_ae_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ᵐ w ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M w Q := by
  intro P n M hM hrect hloc
  -- Step 1, `M` is covered up to an `Hⁿ`-null set by the `C¹` pieces `N_k = g_k(B_{r_k}(c_k))`.
  obtain ⟨g, c, r, m, hg, hm, hlow, hmeas, hfin, hnull⟩ :=
    Submission.codim1_rdo_rectifiable_c1_cover P n M hrect
  -- Step 2, `M` and `N_k` have the same approximate tangent planes `Hⁿ`-a.e. on `M ∩ N_k`.
  have hpiece : ∀ k, ∀ᵐ w ∂(μHE[n] : Measure (Euclid P)), w ∈ (univ : Set (Euclid P)) → w ∈ M →
      w ∈ g k '' ball (c k) (r k) → ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M w Q ↔
          HasApproximateTangentSpaceAt n (g k '' ball (c k) (r k)) w Q :=
    fun k => Submission.doraggt_ae_approxTangent_transfer P n univ M (g k '' ball (c k) (r k))
      isOpen_univ hM (hmeas k) (fun K hK _ => hloc K hK)
      (fun K _ _ => ne_top_of_le_ne_top (hfin k) (measure_mono inter_subset_left))
  -- Step 3, the exceptional sets of Steps 1 and 2 form countably many `Hⁿ`-null sets.
  have hall := ae_all_iff.2 hpiece
  have hcov : ∀ᵐ w ∂(μHE[n] : Measure (Euclid P)), w ∉ M \ ⋃ k, g k '' ball (c k) (r k) :=
    measure_eq_zero_iff_ae_notMem.1 hnull
  -- Step 4, off them, `w = g_k(z) ∈ M ∩ N_k` for some `k`, and `T_w M = T_w N_k = Dg_k(z)(ℝⁿ)`.
  rw [ae_restrict_iff' hM]
  filter_upwards [hall, hcov] with w hw hw' hwM
  have hU : w ∈ ⋃ k, g k '' ball (c k) (r k) := by
    by_contra h
    exact hw' ⟨hwM, h⟩
  obtain ⟨k, z, hz, rfl⟩ := mem_iUnion.1 hU
  exact ⟨_, (hw k (mem_univ _) hwM ⟨z, hz, rfl⟩ _).2
    (Submission.codim1_rdo_c1_piece_approxTangent P n (g k) (c k) (r k) (m k) (hg k) (hm k)
      (hlow k) z hz)⟩
/-- An approximate tangent plane forces unit `Hⁿ`-density on closed balls (Simon Ch. 3,
Remark 1.5(3), with Definition 1.4).  If `Hⁿ(M ∩ B̄_s(x)) < ∞` and `Q` is an approximate tangent
space of `M` at `x`, then `Hⁿ(M ∩ B̄_ρ(x)) / (ωₙρⁿ) → 1` as `ρ ↓ 0`.  Since
`Hⁿ(η_{x,r}(M) ∩ B̄_1(0)) = r⁻ⁿHⁿ(M ∩ B̄_r(x))` and `Hⁿ(Q ∩ B̄_t(0)) = ωₙtⁿ`, the radial cut-offs
`g_{1-ε,1} ≤ 1_{B̄_1(0)} ≤ g_{1,1+ε}` in `C_c` squeeze `r⁻ⁿHⁿ(M ∩ B̄_r(x))` between blow-up integrals
whose limits lie within `ωₙ(1 ∓ ε)ⁿ`. -/
theorem Submission.rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M x Q s hs hfin hT
  obtain ⟨hQ, hconv⟩ := hT
  -- Step 1: `ωₙ ∈ (0, ∞)`
  set ω := unitBallVolume n with hωdef
  have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set w := ω.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
  -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`, via a linear isometry `ℝⁿ ≅ Q`
  have hplane0 : ∀ t : ℝ, 0 ≤ t →
      μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(b.repr.symm v).2, ?_⟩
        rw [mem_closedBall, dist_zero_right] at hv ⊢
        have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
        simpa [ι, this] using hv
      · rintro ⟨hyQ, hy⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right] at hy ⊢
          simpa using hy
        · simp [ι]
    rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
  -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
    intro r hr A
    have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A =
        (fun y => r⁻¹ • y) '' ((fun y => y - x) '' A) := by
      rw [image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) :=
      Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
    rw [h1, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [abs_of_pos hr]
  have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
    intro r hr t
    have key : ∀ z : Euclid P,
        ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
      intro z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, dist_eq_norm]
      rw [inv_mul_le_iff₀ hr, mul_comm r t]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      rw [mem_closedBall, dist_zero_right, key] at hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_zero_right, key]
      exact hzb
  have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
        ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
    intro r hr t
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
  have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
  have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
    intro r hr t ht
    rw [hνball r hr t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
  -- Step 4: radial cut-off functions `g_{a,b}` in `C_c`
  have hbump : ∀ a b : ℝ, 0 < a → a < b →
      ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Continuous f ∧ (0 ≤ ⇑f) ∧
        (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
    intro a b ha hab
    have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
      continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
    have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
      intro y hy
      have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [max_eq_left ((min_le_right _ _).trans h1)]
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
        continuous_toFun := hcont
        hasCompactSupport' := by
          refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
          intro y hy
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hzero y hy.le }
    have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
    refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) a
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        rw [mem_closedBall, dist_zero_right] at hy
        have : 1 ≤ (b - ‖y‖) / (b - a) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) b
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        exact max_le zero_le_one (min_le_left _ _)
      · rw [indicator_of_notMem hy, hf, hzero]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le
  -- Step 5: integrability of functions dominated by the indicator of a finite-measure closed ball
  have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
      Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h)
  have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
      ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
      Integrable f ν := by
    intro ν f t hf hfin' h0 hle
    refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y
  -- Step 6: the normalised mass `a(r) = r⁻ⁿ Hⁿ(M ∩ B̄_r(x))` and the plane-ball values
  set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
  have hareal : ∀ r : ℝ, 0 < r →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
    intro r hr
    rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hplane : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
  have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
    intro t ht
    rw [hplane t ht]
    exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hplanereal : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
    intro t ht
    rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step 7: `a r → ωₙ`
  have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
      -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
      have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
        rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
          (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
      filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `∫_{η(M)} f ≤ a r`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
          (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
      exact hr1.trans_le hle
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
      -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
      have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
        rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
          (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
      filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `a r ≤ ∫_{η(M)} f`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have h2 : (1 + ε) * r ≤ s := by nlinarith [hr2.1, hr2.2, hε.2]
      have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
          (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
      exact hge.trans_lt hr1
  -- Step 8: back to the `ℝ≥0∞` quotient
  have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
    intro ρ hρ hρs
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
    congr 1
    simp only [hadef, inv_pow]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (ha.div_const w)
    rwa [div_self hw.ne', ENNReal.ofReal_one] at this
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
  exact (hconvert ρ hρ.1 hρ.2).symm
/-- **Simon Ch. 1, 3.1–3.2** (densities may be computed with closed or open balls; cf. 6.2.8 and
`HasMassDensity`): if `ν(B̄_ρ(x)) / (ωₙρⁿ) → θ ∈ [0, ∞]` as `ρ ↓ 0`, then also
`ν(B_ρ(x)) / (ωₙρⁿ) → θ`.  The upper bound follows from `B_ρ(x) ⊆ B̄_ρ(x)`.  For the lower
bound, given `a < θ` pick `t ∈ (0, 1)` with `a < tⁿθ`; then `B̄_{tρ}(x) ⊆ B_ρ(x)` and
`ωₙ(tρ)ⁿ = tⁿ ωₙρⁿ` give `ν(B_ρ(x)) / (ωₙρⁿ) ≥ tⁿ · ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) > a` for small
`ρ`. -/
theorem Submission.rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
  intro P n ν x θ hg
  set ω := unitBallVolume n
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Step 2: choose `t ∈ (0, 1)` with `a < tⁿθ`, using `tⁿθ → θ` as `t ↑ 1`
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
        (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [one_mul] at hlim
    obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
      have h1 := (tendsto_order.1 hlim).1 a ha
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
      exact ⟨t, ht, ht'.1, ht'.2⟩
    have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]
      exact hta
    -- Step 3: the rescaled closed-ball ratio `g(tρ)` still tends to `θ`
    have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact mul_pos ht0 hρ
    have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
    filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
    simp only [Function.comp] at hρ
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- Step 4: `ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) · tⁿ = ν(B̄_{tρ}(x)) / (ωₙρⁿ)`
    have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
        = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
        ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
        mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    -- Step 5: `a < tⁿ g(tρ) ≤ h(ρ)`, as `B̄_{tρ}(x) ⊆ B_ρ(x)`
    calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.div_mul_cancel hc0 hctop).symm
      _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
      _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
      _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
          exact closedBall_subset_ball (by nlinarith)
  · -- Step 1: `h(ρ) ≤ g(ρ)`, as `B_ρ(x) ⊆ B̄_ρ(x)`
    filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
    refine lt_of_le_of_lt ?_ hρ
    gcongr
    exact ball_subset_closedBall
/-- **Step 1 of Corollary 7.5.11** (`k ≥ 1`, Simon 7.5; Ch. 2, §4, (4.1)).  A nonempty embedded
`d`-dimensional `Cʳ` submanifold `M` of `ℝᴾ` has `d ≤ P`: for `y ∈ M` and a chart `ψ : V → W` at
`y`, `y ∈ W ∩ M = ψ(V)` gives `z ∈ V`, and the injective linear map `Dψ(z) : ℝᵈ → ℝᴾ` gives
`d = dim ℝᵈ ≤ dim ℝᴾ = P`. -/
theorem Submission.regcomp_cop_dim_le_of_embedded : ∀ (P d r : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → M.Nonempty → d ≤ P := by
  intro P d r M hM ⟨y, hy⟩
  -- a chart `ψ : V → W` of `M` at `y`
  obtain ⟨V, W, ψ, -, -, hyW, -, -, hψV, -, hDψ⟩ := hM y hy
  -- `y ∈ W ∩ M = ψ(V)`, so `y = ψ(z)` for some `z ∈ V`
  obtain ⟨z, hz, -⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  -- `Dψ(z) : ℝᵈ → ℝᴾ` is injective, so `d = dim ℝᵈ ≤ dim ℝᴾ = P`
  simpa using LinearMap.finrank_le_finrank_of_injective
    (f := (fderiv ℝ ψ z : Euclid d →ₗ[ℝ] Euclid P)) (hDψ z hz)
/-- **Simon 7.5** (`T = ∂[[E]]` with `E ⊆ N`): if `(N̄ \ N) ∩ U = ∅`, `E ⊆ N` and
`T(ω) = ∫_E ⟨dω, ξN⟩ dH^{n+1}` for `ω ∈ 𝒟ⁿ(U)`, then `spt T ⊆ N`.  A point `x ∈ spt T \ N` lies
outside `N̄`, so `B_ε(x) ⊆ U \ N̄` for some `ε > 0`.  `W = B_{ε/2}(x)` is open with `W̄` compact
in `U`, and every `ω` with `spt ω ⊆ W` has `spt dω ⊆ spt ω` disjoint from `E`.  So the integrand
vanishes on `E`, `T(ω) = 0`, and `x ∈ W` lies in the zero region of `T`. -/
theorem Submission.regcomp_cop_region_support_subset : ∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), IsOpen U → (closure N \ N) ∩ U = ∅ → E ⊆ N → IsBoundaryOfRegion T E ξN → T.support ⊆ N := by
  intro P n U N E ξN T hU hN hEN hT x hx
  obtain ⟨hxU, hxZ⟩ := hx
  by_contra hxN
  -- `x ∉ N̄`, since `(N̄ \ N) ∩ U = ∅`
  have hxN' : x ∉ closure N := fun h => hN.subset ⟨⟨h, hxN⟩, hxU⟩
  -- a ball `B_ε(x) ⊆ U \ N̄`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff isClosed_closure) x ⟨hxU, hxN'⟩
  -- `W = B_{ε/2}(x)` is open, and `W̄ ⊆ B̄_{ε/2}(x)` is compact and contained in `B_ε(x) ⊆ U`
  have hcl : closure (ball x (ε / 2)) ⊆ ball x ε :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))
  refine hxZ ⟨ball x (ε / 2), ⟨isOpen_ball,
    (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, hcl.trans (hball.trans sdiff_subset), ?_⟩,
    mem_ball_self (half_pos hε)⟩
  -- `T` vanishes on `W`: for `spt ω ⊆ W`, `dω = 0` on `E ⊆ N`, so the integrand vanishes on `E`
  intro ω hω
  rw [hT ω]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  have hzω : z ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Euclid P) n)) := fun h =>
    (hball (ball_subset_ball (by linarith) (hω (tsupport_exteriorDerivative_subset _ h)))).2
      (subset_closure (hEN hz))
  rw [image_eq_zero_of_notMem_tsupport hzω, map_zero]
/-- **`∂[[E]]` is a cycle**: Simon 7.5.1 (`T = ∂[[E]]`, chapter-07.txt line 752) with (6.1.12)
`d²ω = 0` (chapter-06.txt line 150) and the boundary (6.2.3) `∂T(ω) = T(dω)`, `∂T = 0` if `n = 0`
(chapter-06.txt lines 216–220).  If `T(ω) = ∫_E ⟨dω, ξ_N⟩ dH^{n+1}` for every `ω ∈ 𝒟ⁿ(U)`, then
`∂T = 0` in `U`: for `n = m + 1` and `φ ∈ 𝒟ᵐ(U)`, `∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξ_N⟩ dH^{m+2} = 0`,
since `d(dφ) = 0` for the smooth form `φ`.  No hypothesis on `U`, `E` or `ξ_N` is needed. -/
theorem Submission.regcomp_cop_region_boundary_vanishes : ∀ (P n : ℕ) (U E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), IsBoundaryOfRegion T E ξN → BoundaryVanishes T := by
  intro P n
  cases n with
  | zero =>
    -- Degree `0`: `BoundaryVanishes T` is `True` (Simon's convention `∂T = 0`, 6.2.3).
    intro U E ξN T _
    trivial
  | succ m =>
    -- Degree `m + 1`: show `∂T = 0` by testing on every `φ ∈ 𝒟ᵐ(U)`.
    intro U E ξN T hT
    show T.boundary = 0
    apply GeometricCurrentOn.ext
    intro φ
    -- `∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξ_N⟩ dH^{m+2}`: (6.2.3) and the hypothesis at `dφ ∈ 𝒟^{m+1}(U)`.
    rw [GeometricCurrentOn.boundary_apply, hT (exteriorDerivativeTestOn U m φ),
      GeometricCurrentOn.zero_apply]
    -- `d(dφ) = 0` for the smooth form `φ` (6.1.12), so the integrand is `ξ_N(x)(0) = 0`.
    have hdd : exteriorDerivative ((exteriorDerivativeTestOn U m φ : TestFormOn U (m + 1)) :
        DifferentialForm (Euclid P) (m + 1)) = 0 :=
      exteriorDerivative_sq φ.property.1.1
    simp only [hdd, Pi.zero_apply, map_zero, integral_zero]

/-- **Simon 7.5.1** (`T = ∂[[E]]` in `U`, `N ∈ 𝒪`, `E ⊆ N ∩ U`; Ch. 6, 2.3 and 2.11; Ch. 2, §4).
If `U` is open, `N ∈ 𝒪` is oriented by `ξN`, `E ⊆ N ∩ U` and `T(ω) = ∫_E ⟨dω, ξN⟩ dH^{n+1}` for
`ω ∈ 𝒟ⁿ(U)`, then `n + 1 ≤ P`, `spt T ⊆ U ∩ N` and `∂T = 0` in `U`.  A chart of `N` at a point
of `N ∩ U ≠ ∅` has injective derivative `ℝ^{n+1} → ℝᴾ`, so `n + 1 ≤ P`; `spt T ⊆ U` by
definition and `spt T ⊆ N` because `(N̄ \ N) ∩ U = ∅` and `E ⊆ N`; and
`∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξN⟩ dH^{n+1} = 0`.  Minimality of `T` is not needed. -/
theorem Submission.codim1_region_support_cycle : ∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n), IsOpen U → InClassO n U N ξN → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN → n + 1 ≤ P ∧ T.support ⊆ U ∩ N ∧ BoundaryVanishes T := by
  intro P n U N E ξN T hU hO hE hT
  obtain ⟨hN, -, hNU, hne⟩ := hO
  refine ⟨?_, fun x hx => ⟨T.support_subset_domain hx, ?_⟩, ?_⟩
  · -- `n + 1 ≤ P`: `N` is a nonempty embedded `(n + 1)`-dimensional submanifold of `ℝᴾ`
    exact Submission.regcomp_cop_dim_le_of_embedded P (n + 1) 2 N hN (hne.mono inter_subset_left)
  · -- `spt T ⊆ N`, since `(N̄ \ N) ∩ U = ∅` and `E ⊆ N`
    exact Submission.regcomp_cop_region_support_subset P n U N E ξN T hU hNU
      (hE.trans inter_subset_left) hT hx
  · -- `∂T = 0`: `∂T(φ) = T(dφ) = ∫_E ⟨d(dφ), ξN⟩ dH^{n+1} = 0`
    exact Submission.regcomp_cop_region_boundary_vanishes P n U E ξN T hT
/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 2.5 and 3.2(3)**, upper bound: if `T(ω) = ∫_{M'} θ' ⟨ω, ξ'⟩ dHᵏ` for every
`ω` supported in `V`, with `θ' ≥ 0` and `ξ'` a unit orientation `Hᵏ`-a.e. on `M'`, then
`M_W(T) ≤ ∫_{M' ∩ W} θ' dHᵏ` for measurable `W ⊆ V`.  For admissible `ω`, `|ξ'(ω)| ≤ |ω| ≤ 1`
a.e. on `M'` and `ω = 0` off `W`, so `T(ω) ≤ |∫_{M'} θ' ξ'(ω)| ≤ ∫⁻_{M'} 1_W θ'`; no
integrability or measurability of `θ'`, `ξ'` is needed. -/
theorem Submission.codim1_oriented_rep_massOn_le_lintegral : ∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), (∀ x, 0 ≤ θ' x) → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), MeasurableSet W → W ⊆ V → T.massOn W ≤ ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] := by
  intro P k U V M' T θ' ξ' hθ hξ hT W hW hWV
  obtain ⟨_, hL⟩ := Submission.dor_ims_unitOrientation_dual P k
  -- `|ξ'(x)(α)| ≤ |α|` for `Hᵏ⌞M'`-a.e. `x`
  have hgood : ∀ᵐ x ∂(μHE[k].restrict M'),
      ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α := by
    filter_upwards [hξ] with x ⟨Q, hQ⟩
    exact (hL (ξ' x) Q hQ).1
  -- it suffices to bound `T(ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  dsimp only
  rw [hT ω (hωW.trans hWV)]
  -- `|θ' ξ'(ω)| ≤ 1_W θ'` a.e. on `M'`: `ω = 0` off `W` and `|ξ'(ω)| ≤ |ω| ≤ 1`
  have hdom : ∀ᵐ x ∂(μHE[k].restrict M'),
      ‖θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ≤
        W.indicator (fun x => ENNReal.ofReal (θ' x)) x := by
    filter_upwards [hgood] with x hx
    by_cases hxW : x ∈ W
    · rw [indicator_of_mem hxW, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hθ x)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc θ' x * |ξ' x ((ω : DifferentialForm (Euclid P) k) x)|
          ≤ θ' x * 1 := mul_le_mul_of_nonneg_left ((hx _).trans (hω1 x)) (hθ x)
        _ = θ' x := mul_one _
    · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h), map_zero, mul_zero,
        enorm_zero]
      exact zero_le
  -- `T(ω) ≤ |∫ g| ≤ ∫⁻ |g| ≤ ∫⁻_{M'} 1_W θ' = ∫⁻_{M' ∩ W} θ'`
  calc ENNReal.ofReal (∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k])
      ≤ ‖∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in M', ‖θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂μHE[k] :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in M', W.indicator (fun x => ENNReal.ofReal (θ' x)) x ∂μHE[k] :=
        lintegral_mono_ae hdom
    _ = ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] := by
        rw [lintegral_indicator hW, Measure.restrict_restrict hW, inter_comm]
/-- **Lower mass bound for an oriented representation** (Simon Ch. 6, 2.5 and 3.2(3)).  If
`T(ω) = ∫_{M'} θ' ⟨ω, ξ'⟩ dHᵏ` for the test forms supported in `V`, with `θ' ≥ 0` measurable and
`ξ'` a.e. a unit orientation, then `I = ∫_{M' ∩ W} θ' dHᵏ ≤ M_W(T)` for every open `W ⊆ V` with
`I < ∞`.  Let `ν = θ' Hᵏ⌞M'` and let `L` be the dual map of `dor_ims_unitOrientation_dual`, so
`ν`-a.e. `|ξ'(α)| ≤ |α|`, `|L(ξ')| ≤ 1` and `ξ'(L(ξ')) = 1`.  Lusin gives a compact `K ⊆ W` of such
points with `ν(W \ K) < η` on which `L ∘ ξ'` is continuous, and the smooth unit approximation an
admissible `ω` with `|ω − L ∘ ξ'| ≤ δ = η/(I + 1)` on `K`.  Then `ξ'(ω) ≥ (1 − δ) 1_K − 1_{W \ K}`
`ν`-a.e., so `T(ω) = ∫ ξ'(ω) dν ≥ (1 − δ) ν(K) − ν(W \ K) > I − 3η`. -/
theorem Submission.codim1_oriented_rep_lintegral_le_massOn : ∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), V ⊆ U → Measurable θ' → (∀ x, 0 ≤ θ' x) → AEStronglyMeasurable ξ' (μHE[k].restrict M') → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≠ ∞ → ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≤ T.massOn W := by
  intro P k U V M' T θ' ξ' hVU hθm hθ0 hξm hξo hT W hW hWV hI
  -- Step 1: the dual map `L` of the unit orientations
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P k
  -- Step 2: `ν = θ' Hᵏ⌞M'`, with `ν ≪ Hᵏ⌞M'`, `ν(W) = I < ∞` and `∫ g dν = ∫_{M'} θ' g dHᵏ`
  set ν : Measure (Euclid P) :=
    (μHE[k].restrict M').withDensity fun x => ENNReal.ofReal (θ' x) with hν
  have hνμ : ν ≪ μHE[k].restrict M' := withDensity_absolutelyContinuous _ _
  have hνW : ν W = ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] := by
    rw [hν, withDensity_apply _ hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
      inter_comm]
  have hνW' : ν W ≠ ∞ := hνW ▸ hI
  -- `ν`-a.e. `x` is good, and the bad points lie in a measurable `ν`-null set `Z`
  have hgood : ∀ᵐ x ∂ν, (∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) ∧
      covectorEuclideanNorm (L (ξ' x)) ≤ 1 ∧ ξ' x (L (ξ' x)) = 1 :=
    hνμ.ae_le (hξo.mono fun x ⟨Q, hQ⟩ => hL (ξ' x) Q hQ)
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hξν : AEStronglyMeasurable ξ' ν := hξm.mono_ac hνμ
  have hdens : ∀ g : Euclid P → ℝ, ∫ x, g x ∂ν = ∫ x in M', θ' x * g x ∂μHE[k] := by
    intro g
    rw [hν, integral_withDensity_eq_integral_toReal_smul hθm.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hθ0 x), smul_eq_mul]
  set m : ℝ := ν.real W
  have hm0 : 0 ≤ m := measureReal_nonneg
  -- Steps 4–8: for every `η > 0` some admissible `ω` has `T(ω) > m - 3η`
  have key : ∀ η : ℝ, 0 < η →
      ∃ ω : TestFormOn U k, ω ∈ massAdmissibleOn U k W ∧ m - 3 * η < T ω := by
    intro η hη
    -- Step 4: Lusin on `W \ Z` gives a compact `K` of good points with `ν(W \ K) < η`
    obtain ⟨K, hKc, hKA, hKν, hLK⟩ := Submission.dor_ims_lusin_continuousOn P k ν (W \ Z)
      (fun x => L (ξ' x)) η (hW.measurableSet.diff hZm)
      (measure_ne_top_of_subset sdiff_subset hνW')
      (L.continuous.comp_aestronglyMeasurable hξν) hη
    have hKW : K ⊆ W := hKA.trans sdiff_subset
    have hKm : MeasurableSet K := hKc.measurableSet
    have hLK1 : ∀ x ∈ K, covectorEuclideanNorm (L (ξ' x)) ≤ 1 := by
      intro x hx
      by_contra h
      exact (hKA hx).2 (hZ fun hg => h hg.2.1)
    have hWK : ν.real (W \ K) < η := by
      refine ENNReal.toReal_lt_of_lt_ofReal ?_
      rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
    -- Step 5: an admissible `ω` with `|ω - L ∘ ξ'| ≤ δ` on `K`
    set δ : ℝ := η / (m + 1) with hδ
    have hδ0 : 0 < δ := div_pos hη (by linarith)
    obtain ⟨ω₀, hω₀, hω₀W, hω₀1, hω₀K⟩ := Submission.dor_ims_smooth_unit_approx P k K W
      (fun x => L (ξ' x)) δ hKc hW hKW hLK hLK1 hδ0
    let ω : TestFormOn U k := ⟨ω₀, hω₀, hω₀W.trans (hWV.trans hVU)⟩
    refine ⟨ω, ⟨hω₀W, hω₀1⟩, ?_⟩
    have hω₀0 : ∀ x, x ∉ W → ω₀ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hω₀W h)
    -- Step 6: `f = ξ'(ω₀)` is `ν`-integrable, as `|f| ≤ 1_W`, and `T(ω) = ∫ f dν`
    have hTω : T ω = ∫ x, ξ' x (ω₀ x) ∂ν := by
      rw [hdens]
      exact hT ω (hω₀W.trans hWV)
    have hfm : AEStronglyMeasurable (fun x => ξ' x (ω₀ x)) ν :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
        (hξν.prodMk (ContDiff.continuous hω₀.1).aestronglyMeasurable)
    have hWi : Integrable (W.indicator (1 : Euclid P → ℝ)) ν :=
      (integrable_indicator_iff hW.measurableSet).mpr (integrableOn_const hνW')
    have hfi : Integrable (fun x => ξ' x (ω₀ x)) ν := by
      refine hWi.mono' hfm (hgood.mono fun x hx => ?_)
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW, Pi.one_apply, Real.norm_eq_abs]
        exact (hx.1 _).trans (hω₀1 x)
      · rw [indicator_of_notMem hxW, hω₀0 x hxW, map_zero, norm_zero]
    -- Step 7: `f ≥ (1 - δ) 1_K - 1_{W \ K}` `ν`-a.e.
    have hKi : Integrable (K.indicator (1 : Euclid P → ℝ)) ν :=
      (integrable_indicator_iff hKm).mpr (integrableOn_const (measure_ne_top_of_subset hKW hνW'))
    have hWKi : Integrable ((W \ K).indicator (1 : Euclid P → ℝ)) ν :=
      (integrable_indicator_iff (hW.measurableSet.diff hKm)).mpr
        (integrableOn_const (measure_ne_top_of_subset sdiff_subset hνW'))
    have hlow : ∀ᵐ x ∂ν,
        (1 - δ) * K.indicator 1 x - (W \ K).indicator 1 x ≤ ξ' x (ω₀ x) := by
      refine hgood.mono fun x hx => ?_
      by_cases hxK : x ∈ K
      · -- `f = 1 + ξ'(ω₀ - L(ξ')) ≥ 1 - |ω₀ - L(ξ')| ≥ 1 - δ`
        rw [indicator_of_mem hxK, indicator_of_notMem fun h => h.2 hxK, Pi.one_apply, mul_one,
          sub_zero]
        have h1 : ξ' x (ω₀ x) = 1 + ξ' x (ω₀ x - L (ξ' x)) := by
          rw [map_sub, hx.2.2]
          ring
        have h2 := (hx.1 (ω₀ x - L (ξ' x))).trans (hω₀K x hxK)
        rw [h1]
        linarith [neg_abs_le (ξ' x (ω₀ x - L (ξ' x)))]
      · rw [indicator_of_notMem hxK, mul_zero, zero_sub]
        by_cases hxW : x ∈ W
        · -- `f ≥ -|ω₀| ≥ -1`
          rw [indicator_of_mem (s := W \ K) ⟨hxW, hxK⟩, Pi.one_apply]
          linarith [neg_abs_le (ξ' x (ω₀ x)), (hx.1 (ω₀ x)).trans (hω₀1 x)]
        · -- `ω₀ = 0` off `W`
          rw [indicator_of_notMem fun h => hxW h.1, hω₀0 x hxW, map_zero, neg_zero]
    -- Step 8: `T(ω) ≥ (1 - δ) ν(K) - ν(W \ K) > m - 3η`, as `δ ν(K) ≤ δ m < η`,
    -- `ν(W \ K) < η` and `ν(K) = m - ν(W \ K)`
    have hge : (1 - δ) * ν.real K - ν.real (W \ K) ≤ T ω := by
      rw [hTω, ← integral_indicator_one hKm, ← integral_indicator_one (hW.measurableSet.diff hKm),
        ← integral_const_mul, ← integral_sub (hKi.const_mul _) hWKi]
      exact integral_mono_ae ((hKi.const_mul _).sub hWKi) hfi hlow
    have hsplit : ν.real (W \ K) = m - ν.real K := measureReal_sdiff hKW hKm hνW'
    have hKle : ν.real K ≤ m := measureReal_mono hKW hνW'
    have hδm : δ * m < η := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    have hδK : δ * ν.real K ≤ δ * m := mul_le_mul_of_nonneg_left hKle hδ0.le
    have hexp : (1 - δ) * ν.real K = ν.real K - δ * ν.real K := by ring
    linarith
  -- Steps 3 and 9: every `r < I` is at most `M_W(T)`, via `key` for `η = (m - r)/3`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  rw [← hνW] at hr
  have hrm : (r : ℝ) < m := ENNReal.toReal_strict_mono hνW' hr
  obtain ⟨ω, hω, hTω⟩ := key ((m - r) / 3) (by linarith)
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ T.massOn W := T.le_massOn hω

/-- **Mass of a current given on `V` by an oriented weighted set** (Simon Ch. 6, 2.5 and 3.2(3):
`M_W(T) = ∫_{M ∩ W} θ dHᵏ` for `T = τ(M, θ, ξ)`, with a general weight `θ' ≥ 0`).  Let
`I(W) = ∫⁻_{M' ∩ W} θ' dHᵏ` for an open `W ⊆ V`.  Step 2: `|θ' ξ'(ω)| ≤ θ' 1_W` a.e. on `M'` for
every admissible `ω`, so `M_W(T) ≤ I(W)`.  Step 3: if `I(W) < ∞`, a smooth admissible form close
to `L ∘ ξ'` on a compact `K ⊆ M' ∩ W` of almost full `θ' Hᵏ`-measure gives `I(W) ≤ M_W(T)`, and
equality follows by antisymmetry. -/
theorem Submission.codim1_massOn_eq_lintegral_of_oriented_rep : ∀ (P k : ℕ) (U V M' : Set (Euclid P)) (T : GeometricCurrentOn U k) (θ' : Euclid P → ℝ) (ξ' : Euclid P → MultiVector P k), IsOpen V → V ⊆ U → MeasurableSet M' → M' ⊆ V → Measurable θ' → (∀ x, 0 ≤ θ' x) → AEStronglyMeasurable ξ' (μHE[k].restrict M') → (∀ᵐ x ∂(μHE[k].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' x) Q) → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ V → T ω = ∫ x in M', θ' x * ξ' x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) → ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → T.massOn W ≤ ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ∧ (∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k] ≠ ∞ → T.massOn W = ∫⁻ x in M' ∩ W, ENNReal.ofReal (θ' x) ∂μHE[k]) := by
  intro P k U V M' T θ' ξ' _hV hVU _hM' _hM'V hθ hθ0 hξ hξQ hT W hW hWV
  -- Step 2: `M_W(T) ≤ I(W)`; the open set `W` is Borel
  have hle := Submission.codim1_oriented_rep_massOn_le_lintegral P k U V M' T θ' ξ' hθ0 hξQ hT W
    hW.measurableSet hWV
  -- Step 3: `I(W) ≤ M_W(T)` when `I(W) < ∞`, hence `M_W(T) = I(W)`
  exact ⟨hle, fun hI => le_antisymm hle
    (Submission.codim1_oriented_rep_lintegral_le_massOn P k U V M' T θ' ξ' hVU hθ hθ0 hξ hξQ hT W hW
      hWV hI)⟩
/-- **Countably `n`-rectifiable sets of finite measure have density one a.e.** (general fact
(G7); Simon Ch. 3, Lemma 1.2, Remark 1.3, the proof of Theorem 1.6 "⇒" and Remark 1.5(3),
chapter-03.txt lines 25–144).  Let `M ⊆ ℝᴾ` be Borel and countably `n`-rectifiable with
`Hⁿ(M) < ∞`.  Then `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞` for every compact `K`, so by Theorem 1.6 "⇒" the
approximate tangent space `T_wM` exists for `Hⁿ`-a.e. `w ∈ M`.  At such `w`, `Hⁿ(M ∩ B̄_1(w))` is
finite, so `Hⁿ(M ∩ B̄_t(w)) / (ωₙtⁿ) → 1` by Remark 1.5(3); for the measure `Hⁿ⌞M` this
closed-ball limit gives the open-ball limit `Hⁿ(M ∩ B_t(w)) / (ωₙtⁿ) → 1` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_rectifiable_ae_density_one : ∀ (P n : ℕ) (M : Set (Euclid P)), 1 ≤ n → MeasurableSet M → CountablyRectifiable n M → μHE[n] M ≠ ∞ → ∀ᵐ w ∂(μHE[n].restrict M), Tendsto (fun t : ℝ => μHE[n] (M ∩ ball w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M _ hM hrect hfin
  -- Step 1: `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞` for every `K`
  have hloc : ∀ K : Set (Euclid P), μHE[n] (M ∩ K) ≠ ∞ := fun K =>
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  -- Step 2 (Lemma 1.2, Remark 1.3, Theorem 1.6 "⇒"): approximate tangent spaces `Hⁿ`-a.e. on `M`
  have htan := Submission.codim1_rdo_rectifiable_ae_approxTangent P n M hM hrect fun K _ => hloc K
  -- Step 3: `Hⁿ⌞M` evaluates as `Hⁿ(M ∩ ·)`
  have hν : ∀ s : Set (Euclid P), μHE[n].restrict M s = μHE[n] (M ∩ s) := fun s => by
    rw [Measure.restrict_apply' hM, inter_comm]
  filter_upwards [htan] with w ⟨Q, hQ⟩
  -- Step 4 (Remark 1.5(3)): closed-ball density one at `w`, as `Hⁿ(M ∩ B̄_1(w)) < ∞`
  have hclosed := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n M w Q 1 one_pos
    (hloc _) hQ
  -- Step 5: from closed to open balls, for the measure `Hⁿ⌞M`
  exact (Submission.rsd_tendsto_ball_density_of_closedBall P n (μHE[n].restrict M) w 1
    (hclosed.congr fun ρ => by rw [hν])).congr fun ρ => by rw [hν]

/-- **`μ = Hᵐ⌞B` with approximate tangent planes `ν(y)^⊥`** (Simon Ch. 3, 4.3, first part, given
the rectifiable density theorem (RD)).  Let `μ` be locally finite in the open set `D ⊆ ℝ^{m+1}`,
carried by `D`, with flat tangent measure `Hᵐ⌞ν(y)^⊥` at `μ`-a.e. `y`.  Then `μ = Hᵐ⌞B` for a
Borel countably `m`-rectifiable `B ⊆ D` whose approximate tangent space (Ch. 3, 1.4) at
`Hᵐ`-a.e. `y ∈ B` is `ν(y)^⊥`.  Take `B = (D ∩ R) \ N`, with `R` from
`codim1_rdo_dg_rectifiable_of_flat_tangent` and `N` a Borel `μ`-null set off which the flat
tangent exists, so `Θᵐ(μ, y) = 1` on `B` (`codim1_rdo_dg_flat_tangent_density_cone`).  A Vitali
`5r`-covering bounds `Hᵐ⌞B` locally by `μ`, and small covers give `μ ≪ Hᵐ⌞B`; (RD) gives
`Θᵐ(Hᵐ⌞B, w) = 1` a.e., so Besicovitch differentiation yields `dμ/d(Hᵐ⌞B) = 1` and `μ = Hᵐ⌞B`.
Finally `Hᵐ(η_{y,r}(A)) = r⁻ᵐ Hᵐ(A)` turns the flat tangent measure into Definition 1.4. -/
theorem Submission.codim1_rdo_dg_measure_eq_hausdorff : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), 1 ≤ m → IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → (∀ᵐ y ∂μ, ∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → (∀ S : Set (Euclid (m + 1)), MeasurableSet S → CountablyRectifiable m S → μHE[m] S ≠ ∞ → ∀ᵐ w ∂(μHE[m].restrict S), Tendsto (fun t : ℝ => μHE[m] (S ∩ ball w t) / (unitBallVolume m * ENNReal.ofReal (t ^ m))) (𝓝[>] 0) (𝓝 1)) → ∃ B : Set (Euclid (m + 1)), MeasurableSet B ∧ B ⊆ D ∧ CountablyRectifiable m B ∧ μ = μHE[m].restrict B ∧ ∀ᵐ y ∂(μHE[m].restrict B), HasApproximateTangentSpaceAt m B y (Submodule.span ℝ {ν y})ᗮ := by
  intro m D μ ν hm hD hμD hμK hνm hν1 hflat hRD
  -- (step 3 tool) local copy of the accepted `dorag_sn_hausdorff_le_mul_of_lower_density`
  have hcmp_gen : ∀ (N n : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ν : Measure (Euclid N)) (A O : Set (Euclid N)), IsOpen O → A ⊆ O → (∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ ν (closedBall x t)) → μHE[n] A ≤ C * ν O := by
    intro N n c hc
    -- `μHE[n] = k • μH[n]` with a finite factor `k`; take `C = k · 10ⁿ / c`
    set k : NNReal :=
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)]
    refine ⟨(k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c),
      ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
    intro ν A O hO hAO hA
    have hdiam : ∀ (y : Euclid N) (ρ : ℝ), ediam (closedBall y ρ) ≤ ENNReal.ofReal (2 * ρ) := by
      intro y ρ
      apply ediam_le_of_forall_dist_le
      intro z hz w hw
      rw [mem_closedBall] at hz hw
      linarith [dist_triangle_right z w y]
    -- scale `δ = 1 / (m + 1)`: a countable disjoint family of admissible balls whose 5-times
    -- enlargements cover `A`, of total cost at most `(10ⁿ/c) ν(O)`
    have step : ∀ m : ℕ, ∃ u : Set (Euclid N × ℝ), u.Countable ∧
        (∀ p ∈ u, ediam (closedBall p.1 (5 * p.2)) ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1))) ∧
        A ⊆ ⋃ p : u, closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2) ∧
        ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) ≤
          ENNReal.ofReal (10 ^ n / c) * ν O := by
      intro m
      set δ : ℝ := 1 / ((m : ℝ) + 1)
      have hδpos : 0 < δ := by positivity
      -- the admissible balls, as (center, radius) pairs
      set T : Set (Euclid N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ 10 * p.2 ≤ δ ∧
        closedBall p.1 p.2 ⊆ O ∧ ENNReal.ofReal (c * p.2 ^ n) ≤ ν (closedBall p.1 p.2)}
      obtain ⟨u, huT, hudisj, hucov⟩ :=
        Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T (fun p => p.1)
          (fun p => p.2) δ (fun p hp => by linarith [hp.2.2.1, hp.2.1]) 5 (by norm_num)
      -- disjoint balls with nonempty interiors in the separable space `ℝᴺ`
      have hucount : u.Countable := by
        refine hudisj.countable_of_nonempty_interior fun p hp => ?_
        exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huT hp).2.1)⟩
      refine ⟨u, hucount, fun p hp => ?_, ?_, ?_⟩
      · obtain ⟨-, -, hpδ, -, -⟩ := huT hp
        refine (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
        linarith
      · -- each `x ∈ A` is the center of a small admissible ball
        intro x hx
        obtain ⟨t₀, ht₀, hbound⟩ := hA x hx
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
        set r : ℝ := min (t₀ / 2) (min (ε / 2) (δ / 10))
        have hrpos : 0 < r := by positivity
        have hr₁ := min_le_left (t₀ / 2) (min (ε / 2) (δ / 10))
        have hr₂ := min_le_right (t₀ / 2) (min (ε / 2) (δ / 10))
        have hr₃ := min_le_left (ε / 2) (δ / 10)
        have hr₄ := min_le_right (ε / 2) (δ / 10)
        have hmem : (x, r) ∈ T :=
          ⟨hx, hrpos, by linarith, (closedBall_subset_ball (by linarith)).trans hball,
            hbound r hrpos (by linarith)⟩
        obtain ⟨b, hbu, hsub⟩ := hucov (x, r) hmem
        exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (mem_closedBall_self hrpos.le)⟩
      · calc ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
            ≤ ∑' p : u, ENNReal.ofReal (10 ^ n / c) *
                ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
              refine ENNReal.tsum_le_tsum fun p => ?_
              obtain ⟨-, hp0, -, -, hpν⟩ := huT p.2
              calc ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
                  ≤ ENNReal.ofReal (2 * (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) :=
                    ENNReal.rpow_le_rpow (hdiam _ _) (Nat.cast_nonneg n)
                _ = ENNReal.ofReal (10 ^ n / c) * ENNReal.ofReal (c * (p : Euclid N × ℝ).2 ^ n) := by
                    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
                      ← ENNReal.ofReal_mul (by positivity)]
                    congr 1
                    field_simp
                    ring
                _ ≤ ENNReal.ofReal (10 ^ n / c) *
                      ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
                    gcongr
          _ = ENNReal.ofReal (10 ^ n / c) * ν (⋃ p ∈ u, closedBall p.1 p.2) := by
              rw [ENNReal.tsum_mul_left,
                measure_biUnion hucount hudisj fun p _ => measurableSet_closedBall]
          _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
              gcongr
              exact iUnion₂_subset fun p hp => (huT hp).2.2.2.1
    choose u hucount hudiam hucov husum using step
    have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
    -- covers of mesh `1 / (m + 1) → 0`
    have main : μH[(n : ℝ)] A ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
      calc μH[(n : ℝ)] A
          ≤ liminf (fun m => ∑' p : u m,
              ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)) atTop := by
            refine Measure.hausdorffMeasure_le_liminf_tsum (ι := fun m => u m) (n : ℝ) A
              (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) ?_
              (fun m p => closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2))
              (Eventually.of_forall fun m p => hudiam m p p.2) (Eventually.of_forall hucov)
            simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O :=
            liminf_le_of_frequently_le' (Frequently.of_forall husum)
    calc μHE[n] A = (k : ℝ≥0∞) * μH[(n : ℝ)] A := by
          rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
            smul_eq_mul]
      _ ≤ (k : ℝ≥0∞) * (ENNReal.ofReal (10 ^ n / c) * ν O) := by gcongr
      _ = (k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c) * ν O := by rw [mul_assoc]
  -- (step 4 tool) `Hⁿ`-null sets of closed-ball density-one points of `μ` are `μ`-null
  have hnull_gen : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)), (∀ x ∈ A, Tendsto (fun r : ℝ => μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 1)) → μHE[n] A = 0 → μ A = 0 := by
    intro P n μ A hdens hA
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
    have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    set C : ℝ≥0∞ := 2 * unitBallVolume n with hCdef
    have hC0 : C ≠ 0 := mul_ne_zero two_ne_zero hω0
    have hCtop : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hωtop
    -- the pieces `A_k` on which `μ` has uniform growth below radius `1/(k+1)`
    set Ak : ℕ → Set (Euclid P) := fun k => {x | x ∈ A ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / ((k : ℝ) + 1) →
      μ (closedBall x r) ≤ C * ENNReal.ofReal r ^ n} with hAkdef
    have hcover : A ⊆ ⋃ k, Ak k := by
      intro x hx
      have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          μ (closedBall x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) < 2 :=
        (hdens x hx).eventually (gt_mem_nhds (by norm_num))
      obtain ⟨δ, hδ, hδsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h2
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      refine mem_iUnion.mpr ⟨k, hx, fun r hr hrk => ?_⟩
      have hq := hδsub ⟨hr, hrk.trans_lt hk⟩
      have hc0 : unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ 0 :=
        mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
      have hctop : unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ ∞ :=
        ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
      have := ((ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop)).mp hq).le
      calc μ (closedBall x r) ≤ 2 * (unitBallVolume n * ENNReal.ofReal (r ^ n)) := this
        _ = C * ENNReal.ofReal r ^ n := by rw [hCdef, ENNReal.ofReal_pow hr.le, mul_assoc]
    -- every `A_k` is `μ`-null
    have hnull : ∀ k, μ (Ak k) = 0 := by
      intro k
      set R : ℝ := 1 / ((k : ℝ) + 1) with hRdef
      have hR : 0 < R := by positivity
      have hHk : μH[(n : ℝ)] (Ak k) = 0 := by
        have h0 : μHE[n] (Ak k) = 0 := measure_mono_null (fun x hx => hx.1) hA
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul] at h0
        exact (mul_eq_zero.mp h0).resolve_left (by
          simpa using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
      have hdiam : ∀ s : Set (Euclid P), ediam s ≤ ENNReal.ofReal R →
          OuterMeasure.restrict (Ak k) μ.toOuterMeasure s ≤ C * ediam s ^ n := by
        intro s hs
        rw [OuterMeasure.restrict_apply, Measure.toOuterMeasure_apply]
        rcases (s ∩ Ak k).eq_empty_or_nonempty with he | ⟨x, hxs, hxA⟩
        · simp only [he, measure_empty, zero_le]
        have hsfin : ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
        have hdR : (ediam s).toReal ≤ R := ENNReal.toReal_le_of_le_ofReal hR.le hs
        have hsub : s ∩ Ak k ⊆ closedBall x (ediam s).toReal := by
          intro y hy
          change dist y x ≤ (ediam s).toReal
          simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using
            (ENNReal.toReal_mono hsfin (edist_le_ediam_of_mem hy.1 hxs))
        apply (measure_mono hsub).trans
        by_cases hd : 0 < (ediam s).toReal
        · simpa only [ENNReal.ofReal_toReal hsfin] using hxA.2 _ hd hdR
        · have hd0 : (ediam s).toReal = 0 := le_antisymm (not_lt.mp hd) ENNReal.toReal_nonneg
          have hed0 : ediam s = 0 := by
            rw [← ENNReal.ofReal_toReal hsfin, hd0, ENNReal.ofReal_zero]
          rw [hd0, hed0]
          -- zero radius: let the radius tend to zero in the growth bound
          have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] 0) (𝓝 0) :=
            tendsto_id.mono_left inf_le_left
          have hlim : Tendsto (fun r : ℝ ↦ C * (ENNReal.ofReal r) ^ n) (𝓝[>] 0)
              (𝓝 (C * (0 : ℝ≥0∞) ^ n)) := by
            simpa only [ENNReal.ofReal_zero, Function.comp_def] using
              ENNReal.Tendsto.const_mul
                (ENNReal.Tendsto.pow (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hid))
                (Or.inr hCtop)
          apply ge_of_tendsto hlim
          filter_upwards [Ioo_mem_nhdsGT hR] with r hr
          exact (measure_mono (closedBall_subset_closedBall hr.1.le)).trans
            (hxA.2 r hr.1 hr.2.le)
      have hm := OuterMeasure.le_mkMetric (fun d : ℝ≥0∞ ↦ C * d ^ n)
        (OuterMeasure.restrict (Ak k) μ.toOuterMeasure) (ENNReal.ofReal R)
        (ENNReal.ofReal_pos.mpr hR) hdiam
      have hcost : (fun d : ℝ≥0∞ ↦ C * d ^ n) = C • (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) := by
        funext d
        simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
      rw [hcost, OuterMeasure.mkMetric_smul _ hCtop hC0] at hm
      have hk := hm (Ak k)
      rw [OuterMeasure.restrict_apply, inter_self, Measure.toOuterMeasure_apply,
        smul_apply, smul_eq_mul] at hk
      have hH : OuterMeasure.mkMetric (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) (Ak k) = 0 := by
        have : (μH[(n : ℝ)] : Measure (Euclid P)).toOuterMeasure =
            OuterMeasure.mkMetric (fun d : ℝ≥0∞ ↦ d ^ (n : ℝ)) := by
          rw [Measure.hausdorffMeasure, Measure.mkMetric_toOuterMeasure]
        rw [← this, Measure.toOuterMeasure_apply, hHk]
      rw [hH, mul_zero] at hk
      exact le_antisymm hk zero_le
    exact measure_mono_null hcover (measure_iUnion_null hnull)
  -- (step 5 tool) (RD) on pieces `B ∩ ball` gives closed-ball density one of `Hⁿ⌞B` a.e.
  have hdens_gen : ∀ (P n : ℕ) (D B : Set (Euclid P)), IsOpen D → MeasurableSet B → B ⊆ D → CountablyRectifiable n B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → μHE[n] (B ∩ K) ≠ ∞) → (∀ S : Set (Euclid P), MeasurableSet S → CountablyRectifiable n S → μHE[n] S ≠ ∞ → ∀ᵐ w ∂(μHE[n].restrict S), Tendsto (fun t : ℝ => μHE[n] (S ∩ ball w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1)) → ∀ᵐ w ∂(μHE[n].restrict B), Tendsto (fun t : ℝ => (μHE[n].restrict B) (closedBall w t) / (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1) := by
    intro P n D B hD hBm hBD hBrect hloc hRD
    have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
    have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    -- Step 1: open-ball density one of `Hⁿ⌞B` at `Hⁿ⌞B`-a.e. point, from (RD) on pieces
    have hopen : ∀ᵐ w ∂(μHE[n].restrict B), Tendsto (fun t : ℝ => μHE[n] (B ∩ ball w t) /
        (unitBallVolume n * ENNReal.ofReal (t ^ n))) (𝓝[>] 0) (𝓝 1) := by
      have hrad : ∀ x : D, ∃ ε : ℝ, 0 < ε ∧ closedBall (x : Euclid P) ε ⊆ D := by
        intro x
        obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD x x.2
        exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεD⟩
      choose ε hε hεD using hrad
      obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
        (fun x : D => ball (x : Euclid P) (ε x)) (fun _ => isOpen_ball)
      have hcov : (⋃ x ∈ T, ball (x : Euclid P) (ε x)) = D := by
        rw [hT]
        apply subset_antisymm
        · exact iUnion_subset fun x => ball_subset_closedBall.trans (hεD x)
        · intro y hy
          exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hε ⟨y, hy⟩)⟩
      have hBae : ∀ᵐ w ∂(μHE[n].restrict B), w ∈ D :=
        (ae_restrict_mem hBm).mono fun w hw => hBD hw
      rw [← Measure.restrict_eq_self_of_ae_mem hBae, ← hcov,
        ae_restrict_biUnion_iff _ hTc]
      intro x _
      rw [Measure.restrict_restrict measurableSet_ball]
      have hSm : MeasurableSet (ball (x : Euclid P) (ε x) ∩ B) := measurableSet_ball.inter hBm
      have hSrect : CountablyRectifiable n (ball (x : Euclid P) (ε x) ∩ B) :=
        hBrect.mono inter_subset_right
      have hSfin : μHE[n] (ball (x : Euclid P) (ε x) ∩ B) ≠ ∞ :=
        ne_top_of_le_ne_top (hloc _ (isCompact_closedBall _ _) (hεD x))
          (measure_mono fun y hy => ⟨hy.2, ball_subset_closedBall hy.1⟩)
      filter_upwards [hRD _ hSm hSrect hSfin, ae_restrict_mem hSm] with w hw hwS
      refine hw.congr' ?_
      obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.mp isOpen_ball w hwS.1
      filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
      have hset : ball (x : Euclid P) (ε x) ∩ B ∩ ball w t = B ∩ ball w t := by
        ext y
        constructor
        · rintro ⟨⟨_, hyB⟩, hyt⟩
          exact ⟨hyB, hyt⟩
        · rintro ⟨hyB, hyt⟩
          exact ⟨⟨hδW (ball_subset_ball ht.2.le hyt), hyB⟩, hyt⟩
      rw [hset]
    -- Step 2: pass from open to closed balls by squeezing between radii `t` and `t + t²`
    filter_upwards [hopen] with w hw
    set c : ℝ → ℝ≥0∞ := fun t => unitBallVolume n * ENNReal.ofReal (t ^ n) with hcdef
    set q : ℝ → ℝ≥0∞ := fun t => μHE[n] (B ∩ ball w t) / c t with hqdef
    have hs : Tendsto (fun t : ℝ => t + t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun t : ℝ => t + t ^ 2) (𝓝 0) (𝓝 (0 + 0 ^ 2)) :=
          (continuous_id.add (continuous_pow 2)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact add_pos_of_pos_of_nonneg ht (sq_nonneg t)
    have hk : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ n)) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ n)) (𝓝 0)
          (𝓝 (ENNReal.ofReal ((1 + 0) ^ n))) :=
        (ENNReal.continuous_ofReal.comp
          ((continuous_const.add continuous_id).pow n)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hupper : Tendsto (fun t : ℝ => ENNReal.ofReal ((1 + t) ^ n) * q (t + t ^ 2))
        (𝓝[>] 0) (𝓝 1) := by
      have := ENNReal.Tendsto.mul hk (Or.inl one_ne_zero) (hw.comp hs) (Or.inl one_ne_zero)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hw hupper ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show μHE[n] (B ∩ ball w t) / c t ≤ (μHE[n].restrict B) (closedBall w t) / c t
      rw [Measure.restrict_apply measurableSet_closedBall]
      have hsub : B ∩ ball w t ⊆ closedBall w t ∩ B := fun y hy =>
        ⟨ball_subset_closedBall hy.2, hy.1⟩
      exact ENNReal.div_le_div_right (measure_mono hsub) _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hk0 : ENNReal.ofReal ((1 + t) ^ n) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (pow_pos (by linarith) n)).ne'
      have hktop : ENNReal.ofReal ((1 + t) ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
      have hc0 : c t ≠ 0 := mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos ht0 n)).ne'
      have hctop : c t ≠ ∞ := ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
      have hcs : c (t + t ^ 2) = c t * ENNReal.ofReal ((1 + t) ^ n) := by
        simp only [hcdef]
        rw [mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg ht0.le n), ← mul_pow]
        congr 3
        ring
      show (μHE[n].restrict B) (closedBall w t) / c t ≤
        ENNReal.ofReal ((1 + t) ^ n) * (μHE[n] (B ∩ ball w (t + t ^ 2)) / c (t + t ^ 2))
      rw [Measure.restrict_apply measurableSet_closedBall, hcs]
      have hsub : closedBall w t ∩ B ⊆ B ∩ ball w (t + t ^ 2) := fun y hy =>
        ⟨hy.2, closedBall_subset_ball (by nlinarith) hy.1⟩
      calc μHE[n] (closedBall w t ∩ B) / c t
          ≤ μHE[n] (B ∩ ball w (t + t ^ 2)) / c t := ENNReal.div_le_div_right (measure_mono hsub) _
        _ = ENNReal.ofReal ((1 + t) ^ n) *
            (μHE[n] (B ∩ ball w (t + t ^ 2)) / (c t * ENNReal.ofReal ((1 + t) ^ n))) := by
          rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), ← mul_assoc, ← mul_assoc,
            mul_comm (ENNReal.ofReal _) (c t)⁻¹, mul_assoc (c t)⁻¹,
            ENNReal.mul_inv_cancel hk0 hktop, mul_one]
  -- (step 6 tool) `μ ≪ ρ` and ball ratios `μ/ρ → 1` `ρ`-a.e. force `μ = ρ` (Besicovitch)
  have heq_gen : ∀ (P : ℕ) (D : Set (Euclid P)) (μ ρ : Measure (Euclid P)), IsOpen D → μ Dᶜ = 0 → ρ Dᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → μ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → ρ K ≠ ∞) → μ ≪ ρ → (∀ᵐ w ∂ρ, Tendsto (fun t : ℝ => μ (closedBall w t) / ρ (closedBall w t)) (𝓝[>] 0) (𝓝 1)) → μ = ρ := by
    intro P D μ ρ hD hμD hρD hμK hρK hac hratio
    -- Step 1: equality on every open ball whose closure lies in `D`
    have hlocal : ∀ c : Euclid P, ∀ s : ℝ, closedBall c s ⊆ D →
        μ.restrict (ball c s) = ρ.restrict (ball c s) := by
      intro c s hcs
      have hfinμ : μ (ball c s) ≠ ∞ := ne_top_of_le_ne_top
        (hμK _ (isCompact_closedBall c s) hcs) (measure_mono ball_subset_closedBall)
      have hfinρ : ρ (ball c s) ≠ ∞ := ne_top_of_le_ne_top
        (hρK _ (isCompact_closedBall c s) hcs) (measure_mono ball_subset_closedBall)
      have : IsFiniteMeasure (μ.restrict (ball c s)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinμ.lt_top⟩
      have : IsFiniteMeasure (ρ.restrict (ball c s)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfinρ.lt_top⟩
      have hacW : μ.restrict (ball c s) ≪ ρ.restrict (ball c s) := hac.restrict _
      have hone : (μ.restrict (ball c s)).rnDeriv (ρ.restrict (ball c s))
          =ᵐ[ρ.restrict (ball c s)] 1 := by
        filter_upwards [Besicovitch.ae_tendsto_rnDeriv (μ.restrict (ball c s))
            (ρ.restrict (ball c s)), ae_restrict_mem measurableSet_ball,
            ae_restrict_of_ae hratio] with w hw hwW hwr
        obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp isOpen_ball w hwW
        have heq : (fun t : ℝ => μ (closedBall w t) / ρ (closedBall w t)) =ᶠ[𝓝[>] 0]
            (fun t : ℝ => μ.restrict (ball c s) (closedBall w t) /
              ρ.restrict (ball c s) (closedBall w t)) := by
          filter_upwards [Ioo_mem_nhdsGT hε] with t ht
          have hsub : closedBall w t ⊆ ball c s := (closedBall_subset_ball ht.2).trans hεW
          rw [Measure.restrict_apply measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hsub]
        exact tendsto_nhds_unique hw (hwr.congr' heq)
      calc μ.restrict (ball c s)
          = (ρ.restrict (ball c s)).withDensity
              ((μ.restrict (ball c s)).rnDeriv (ρ.restrict (ball c s))) :=
            by
              have h := Measure.singularPart_add_rnDeriv (μ.restrict (ball c s)) (ρ.restrict (ball c s))
              rw [Measure.singularPart_eq_zero_of_ac hacW, zero_add] at h
              exact h.symm
        _ = (ρ.restrict (ball c s)).withDensity 1 := withDensity_congr_ae hone
        _ = ρ.restrict (ball c s) := withDensity_one
    -- Step 2: countably many such balls cover `D`
    have hrad : ∀ x : D, ∃ ε : ℝ, 0 < ε ∧ closedBall (x : Euclid P) ε ⊆ D := by
      intro x
      obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD x x.2
      exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεD⟩
    choose ε hε hεD using hrad
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : D => ball (x : Euclid P) (ε x)) (fun _ => isOpen_ball)
    have hcov : (⋃ x ∈ T, ball (x : Euclid P) (ε x)) = D := by
      rw [hT]
      apply subset_antisymm
      · exact iUnion_subset fun x => ball_subset_closedBall.trans (hεD x)
      · intro y hy
        exact mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hε ⟨y, hy⟩)⟩
    have hD' : μ.restrict D = ρ.restrict D := by
      rw [← hcov]
      exact (Measure.restrict_biUnion_congr hTc).mpr fun x _ => hlocal x (ε x) (hεD x)
    have hμae : ∀ᵐ x ∂μ, x ∈ D := by
      rw [ae_iff]
      exact hμD
    have hρae : ∀ᵐ x ∂ρ, x ∈ D := by
      rw [ae_iff]
      exact hρD
    rw [← Measure.restrict_eq_self_of_ae_mem hμae, ← Measure.restrict_eq_self_of_ae_mem hρae, hD']
  -- (step 7 tool) local copy of the accepted `setIntegral_blowUpMap_image_eq_inv_pow_mul`
  have hcov_gen : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
    intro P n M x r hr f
    -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
    obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
        ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
      ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
    -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
    have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
      intro S
      have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
        rw [image_image, he]
        rfl
      rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
    -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
    have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
      ext A hA
      rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
        Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
        e.image_preimage]
    -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
    rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
      NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hr)]
  -- Step 1: the good set `G` of flat-tangent points, of full `μ`-measure
  set G : Set (Euclid (m + 1)) := {y | ∀ f : Euclid (m + 1) → ℝ, Continuous f →
    HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ)
      (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))}
    with hGdef
  have hGc : μ Gᶜ = 0 := hflat
  -- Step 2: rectifiable carrier `B = (D ∩ R) \ N`
  obtain ⟨R, hRm, hRrect, hRc⟩ :=
    Submission.codim1_rdo_dg_rectifiable_of_flat_tangent m D μ ν hm hD hμD hμK hνm hν1 hflat
  set N : Set (Euclid (m + 1)) := toMeasurable μ Gᶜ with hNdef
  set B : Set (Euclid (m + 1)) := (D ∩ R) \ N with hBdef
  have hBm : MeasurableSet B :=
    (hD.measurableSet.inter hRm).diff (measurableSet_toMeasurable _ _)
  have hBD : B ⊆ D := fun y hy => hy.1.1
  have hBrect : CountablyRectifiable m B := hRrect.mono fun y hy => hy.1.2
  have hBG : ∀ y ∈ B, y ∈ G := by
    intro y hy
    by_contra h
    exact hy.2 (subset_toMeasurable μ Gᶜ h)
  have hN : μ N = 0 := by rw [hNdef, measure_toMeasurable]; exact hGc
  have hμBc : μ Bᶜ = 0 := by
    have hsub : Bᶜ ⊆ Dᶜ ∪ Rᶜ ∪ N := by
      intro y hy
      by_cases hyD : y ∈ D
      · by_cases hyR : y ∈ R
        · right
          by_contra hyN
          exact hy ⟨⟨hyD, hyR⟩, hyN⟩
        · left; right; exact hyR
      · left; left; exact hyD
    exact measure_mono_null hsub (measure_union_null (measure_union_null hμD hRc) hN)
  -- Step 1 (cont.): density one of `μ` at every point of `B`
  have hdens : ∀ y ∈ B, Tendsto (fun r : ℝ => μ (closedBall y r) /
      (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) := by
    intro y hy
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD y (hBD hy)
    have hfin : ∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞ :=
      ⟨ε / 2, half_pos hε, hμK _ (isCompact_closedBall y (ε / 2))
        ((closedBall_subset_ball (half_lt_self hε)).trans hεD)⟩
    exact (Submission.codim1_rdo_dg_flat_tangent_density_cone m μ y (ν y) hm (hν1 y) hfin
      (hBG y hy)).1
  have hω0 : unitBallVolume m ≠ 0 := (measure_ball_pos _ _ zero_lt_one).ne'
  have hωtop : unitBallVolume m ≠ ∞ := measure_ball_lt_top.ne
  -- Step 3: local finiteness of `Hᵐ⌞B` by the density comparison
  have hω2top : unitBallVolume m / 2 ≠ ∞ := ENNReal.div_ne_top hωtop two_ne_zero
  set c : ℝ := (unitBallVolume m / 2).toReal with hcdef
  have hc : 0 < c := ENNReal.toReal_pos (ENNReal.div_ne_zero.mpr ⟨hω0, ENNReal.ofNat_ne_top⟩)
    hω2top
  obtain ⟨C, hCtop, hcmp⟩ := hcmp_gen (m + 1) m c hc
  have hlow : ∀ x ∈ B, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ENNReal.ofReal (c * t ^ m) ≤ μ (closedBall x t) := by
    intro x hx
    have h := (hdens x hx).eventually (lt_mem_nhds (by norm_num : (2⁻¹ : ℝ≥0∞) < 1))
    obtain ⟨t₀, ht₀, hsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp h
    refine ⟨t₀, ht₀, fun t ht htt => ?_⟩
    have hq : 2⁻¹ < μ (closedBall x t) / (unitBallVolume m * ENNReal.ofReal (t ^ m)) :=
      hsub ⟨ht, htt⟩
    have hden0 : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos ht m)).ne'
    have hdentop : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    have hlt := (ENNReal.lt_div_iff_mul_lt (Or.inl hden0) (Or.inl hdentop)).mp hq
    calc ENNReal.ofReal (c * t ^ m) = unitBallVolume m / 2 * ENNReal.ofReal (t ^ m) := by
          rw [ENNReal.ofReal_mul hc.le, hcdef, ENNReal.ofReal_toReal hω2top]
      _ = 2⁻¹ * (unitBallVolume m * ENNReal.ofReal (t ^ m)) := by
          rw [ENNReal.div_eq_inv_mul, mul_assoc]
      _ ≤ μ (closedBall x t) := hlt.le
  have hloc : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μHE[m] (B ∩ K) ≠ ∞ := by
    intro K hK hKD
    obtain ⟨δ, hδ, hδD⟩ := hK.exists_cthickening_subset_open hD hKD
    have hle := hcmp μ (B ∩ K) (thickening δ K) isOpen_thickening
      (inter_subset_right.trans (self_subset_thickening hδ K)) (fun x hx => hlow x hx.1)
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hCtop (hμK _ hK.cthickening hδD))
      (hle.trans (mul_le_mul' le_rfl (measure_mono (thickening_subset_cthickening δ K))))
  set ρ : Measure (Euclid (m + 1)) := μHE[m].restrict B with hρdef
  have hρDc : ρ Dᶜ = 0 := by
    rw [hρdef, Measure.restrict_apply hD.measurableSet.compl]
    have : Dᶜ ∩ B = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hyD hyB
      exact hyD (hBD hyB)
    rw [this, measure_empty]
  have hρK : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ρ K ≠ ∞ := by
    intro K hK hKD
    rw [hρdef, Measure.restrict_apply' hBm, inter_comm]
    exact hloc K hK hKD
  -- Step 4: `μ ≪ Hᵐ⌞B`
  have hac : μ ≪ ρ := by
    intro A hA
    rw [hρdef, Measure.restrict_apply' hBm] at hA
    have h1 : μ (A ∩ B) = 0 :=
      hnull_gen (m + 1) m μ (A ∩ B)
        (fun x hx => hdens x hx.2) hA
    refine measure_mono_null (fun y hy => ?_) (measure_union_null h1 hμBc)
    by_cases hyB : y ∈ B
    · exact Or.inl ⟨hy, hyB⟩
    · exact Or.inr hyB
  -- Step 5: density one of `Hᵐ⌞B`
  have hρdens := hdens_gen (m + 1) m D B hD hBm
    hBD hBrect hloc hRD
  -- Step 6: ball ratios and identification
  have hratio : ∀ᵐ w ∂ρ, Tendsto (fun t : ℝ => μ (closedBall w t) / ρ (closedBall w t))
      (𝓝[>] 0) (𝓝 1) := by
    filter_upwards [hρdens, ae_restrict_mem hBm] with w hw hwB
    have h := ENNReal.Tendsto.div (hdens w hwB) (Or.inl one_ne_zero) hw
      (Or.inl ENNReal.one_ne_top)
    rw [ENNReal.div_self one_ne_zero ENNReal.one_ne_top] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hc0 : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos ht m)).ne'
    have hctop : unitBallVolume m * ENNReal.ofReal (t ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    show μ (closedBall w t) / (unitBallVolume m * ENNReal.ofReal (t ^ m)) /
        (ρ (closedBall w t) / (unitBallVolume m * ENNReal.ofReal (t ^ m))) =
      μ (closedBall w t) / ρ (closedBall w t)
    conv_lhs => rw [div_eq_mul_inv (μ (closedBall w t)), div_eq_mul_inv (ρ (closedBall w t))]
    exact ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.mpr hctop)
      (ENNReal.inv_ne_top.mpr hc0)
  have hμeq : μ = μHE[m].restrict B :=
    heq_gen (m + 1) D μ ρ hD hμD hρDc hμK hρK hac hratio
  refine ⟨B, hBm, hBD, hBrect, hμeq, ?_⟩
  -- Step 7: approximate tangent planes by scaling
  filter_upwards [ae_restrict_mem hBm] with y hy
  have hν0 : ν y ≠ 0 := by
    intro h
    have := hν1 y
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hflaty : y ∈ G := hBG y hy
  simp only [hGdef, mem_ofPred_eq] at hflaty
  rw [hμeq] at hflaty
  refine ⟨?_, fun f => ?_⟩
  · have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
    exact Submodule.finrank_orthogonal_span_singleton hν0
  · refine (hflaty f f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hcov_gen (m + 1) m B y r hr f, inv_pow]
    rfl
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW

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
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hball, -, hmass⟩ :=
    Submission.codim1_rdo_dg_cutoff_estimates m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hA
  obtain ⟨c₂, ρ₂, hc₂, hρ₂, hvol⟩ :=
    Submission.codim1_rdo_dg_volume_density_lower m D F μ ν y v hm hD hF hμD hμK hν hν1 hGG hy
      hv hA
  -- step 7: it suffices that every sequence `r_k → 0⁺` has a subsequence along which the
  -- quantity tends to `0`
  apply Filter.tendsto_of_subseq_tendsto
  intro rs hrs
  have hrs0 : Tendsto rs atTop (𝓝 0) := hrs.mono_right nhdsWithin_le_nhds
  have hrs_pos : ∀ᶠ k in atTop, 0 < rs k := hrs.eventually self_mem_nhdsWithin
  set Fs : ℕ → Set (Euclid (m + 1)) := fun k => (fun w => y + rs k • w) ⁻¹' F with hFs_def
  have hFs : ∀ k, MeasurableSet (Fs k) := fun k =>
    (measurable_const.add (measurable_id.const_smul (rs k))) hF
  -- step 4: perimeter bounds `C₁ R^m` on `B_R`, hence an `L¹_loc` limit `F₀` of a subsequence
  have hper : ∀ R' : ℝ, 0 < R' → ∃ C : ℝ, ∀ᶠ k in atTop, ∀ g : Euclid (m + 1) → Euclid (m + 1),
      ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R' →
      (∀ z, ‖g z‖ ≤ 1) →
      ∫ z in Fs k, LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C := by
    intro R' hR'
    refine ⟨C₁ * R' ^ m, ?_⟩
    have h1 : ∀ᶠ k in atTop, rs k * R' < ρ₁ := by
      have : Tendsto (fun k => rs k * R') atTop (𝓝 0) := by simpa using hrs0.mul_const R'
      exact this.eventually (gt_mem_nhds hρ₁)
    filter_upwards [hrs_pos, h1] with k hk1 hk2
    intro g hg hgc hgs hg1
    exact Submission.codim1_rdo_dg_bh_perimeter_bound m D F μ ν y ρ₁ C₁ hF hν hν1 hGG hρ₁ hC₁
      hball hmass R' (rs k) hR' hk1 hk2 g hg hgc hgs hg1
  obtain ⟨ψ, F₀, hψ, hF₀, hconv⟩ := Submission.codim1_rdo_dg_bv_set_compactness m Fs hFs hper
  refine ⟨ψ, ?_⟩
  have hrsψ : Tendsto (fun j => rs (ψ j)) atTop (𝓝[>] 0) := hrs.comp hψ.tendsto_atTop
  obtain ⟨hint, hin, hout⟩ :=
    Submission.codim1_rdo_dg_bh_l1loc_transfer m (fun j => Fs (ψ j)) F₀ (fun j => hFs _) hF₀ hconv
  -- step 5: `F₀` has vanishing tangential and nonpositive normal derivative
  have htan : ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in F₀, fderiv ℝ ζ z w = 0 := by
    intro ζ hζ hζc w hw
    have h1 := (Submission.codim1_rdo_dg_bh_tangential_vanish m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv
      hA hρ₁ hC₁ hball hmass ζ hζ hζc w hw).comp hrsψ
    have h2 := hint (fun z => fderiv ℝ ζ z w)
      ((hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hζc.fderiv_apply (𝕜 := ℝ) w)
    exact tendsto_nhds_unique h2 h1
  have hnor : ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      (∀ z, 0 ≤ ζ z) → ∫ z in F₀, fderiv ℝ ζ z v ≤ 0 := by
    intro ζ hζ hζc hζ0
    have h2 := hint (fun z => fderiv ℝ ζ z v)
      ((hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hζc.fderiv_apply (𝕜 := ℝ) v)
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have h1 := Submission.codim1_rdo_dg_bh_normal_limsup m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA
      hρ₁ hC₁ hball hmass ζ hζ hζc hζ0 δ hδ
    have h3 : ∀ᶠ j in atTop, ∫ z in Fs (ψ j), fderiv ℝ ζ z v ≤ δ := hrsψ.eventually h1
    simpa using le_of_tendsto h2 h3
  -- so `F₀` is a.e. `∅`, `ℝ^{m+1}` or `{⟨w, v⟩ > c}`
  have htri := Submission.codim1_rdo_dg_halfspace_rigidity m F₀ v hv hF₀ htan hnor
  -- step 6: the scale-invariant two-sided volume bounds pass to the limit, which forces `c = 0`
  have hpos : ∀ s : ℝ, 0 < s → 0 < volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ∧
      0 < volume (ball (0 : Euclid (m + 1)) s \ F₀) := by
    intro s hs
    have hpos' : ∀ᶠ j in atTop, 0 < rs (ψ j) := hrsψ.eventually self_mem_nhdsWithin
    have hsmall : ∀ᶠ j in atTop, rs (ψ j) * s < ρ₂ := by
      have : Tendsto (fun j => rs (ψ j) * s) atTop (𝓝 0) := by
        simpa using (hrsψ.mono_right nhdsWithin_le_nhds).mul_const s
      exact this.eventually (gt_mem_nhds hρ₂)
    have hlow : ∀ᶠ j in atTop,
        ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume (Fs (ψ j) ∩ ball (0 : Euclid (m + 1)) s) ∧
          ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume (ball (0 : Euclid (m + 1)) s \ Fs (ψ j)) := by
      filter_upwards [hpos', hsmall] with j h1 h2
      exact Submission.codim1_rdo_dg_bh_rescaled_volume_lower m F y c₂ ρ₂ hF hvol s (rs (ψ j)) hs
        h1 h2
    have hc : 0 < ENNReal.ofReal (c₂ * s ^ (m + 1)) :=
      ENNReal.ofReal_pos.mpr (mul_pos hc₂ (pow_pos hs _))
    exact ⟨lt_of_lt_of_le hc (ge_of_tendsto (hin s) (hlow.mono fun j h => h.1)),
      lt_of_lt_of_le hc (ge_of_tendsto (hout s) (hlow.mono fun j h => h.2))⟩
  have hH := Submission.codim1_rdo_dg_bh_offset_zero m F₀ v hv hpos htri
  -- step 7: `L((F_{r_{ψ j}} Δ H) ∩ B_R) ≤ L((F_{r_{ψ j}} Δ F₀) ∩ B_R) + L(F₀ Δ H) → 0`
  have hle : ∀ j, volume (symmDiff (Fs (ψ j)) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R) ≤
      volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R) := by
    intro j
    calc volume (symmDiff (Fs (ψ j)) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R)
        ≤ volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R ∪
            symmDiff F₀ {w | 0 < inner ℝ w v}) := by
          apply measure_mono
          intro x hx
          rcases symmDiff_triangle (Fs (ψ j)) F₀ {w | 0 < inner ℝ w v} hx.1 with h | h
          · exact Or.inl ⟨h, hx.2⟩
          · exact Or.inr h
      _ ≤ volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R) +
            volume (symmDiff F₀ {w | 0 < inner ℝ w v}) :=
          measure_union_le _ _
      _ = volume (symmDiff (Fs (ψ j)) F₀ ∩ ball (0 : Euclid (m + 1)) R) := by rw [hH, add_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv R) (fun j => by simp) hle

/-- **Blow-ups of the Gauss–Green measure converge to `Hᵐ⌞ν(y)ᗮ`** (Simon Ch. 3, proof of
Theorem 4.3 (De Giorgi), 4.3 (†), chapter-03.txt lines 734–746).  By `normal_average_ae`,
`μ`-a.e. `y` lies in `D` and has normal averages `A(ρ) → ν(y)`; fix such `y` and put
`v = ν(y)`.  `cutoff_estimates` gives `B̄_{ρ₁}(y) ⊆ D` and `μ(B̄_ρ(y)) ≤ C ρᵐ`,
`blowup_halfspace` gives `F_{y,r} → {⟨w, v⟩ > 0}` in `L¹_loc`, and `hyperplane_param` shows
that `τ = Hᵐ⌞vᗮ` is finite on balls.  By `continuous_extension` it suffices to treat `C¹`
test functions `g`; by `normal_defect` it suffices to show
`r⁻ᵐ ∫ g(r⁻¹(z − y)) ⟨v, ν(z)⟩ dμ(z) → ∫_{vᗮ} g dHᵐ`, which is the vector convergence (3a)
(`vector_convergence`) for the field `g v`, since `⟨g v, ν⟩ = g ⟨v, ν⟩` and `⟨g v, v⟩ = g`. -/
theorem Submission.codim1_rdo_dg_tangent_measure_ae : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), 1 ≤ m → IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ᵐ y ∂μ, ∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m])) := by
  intro m D F μ ν hm hD hF hDc hloc hνm hν1 hGG
  -- Step 1: good points `y` (`y ∈ D`, `A(ρ) → ν(y)`), with `v = ν(y)`
  filter_upwards [Submission.codim1_rdo_dg_normal_average_ae m D μ ν hD hDc hloc hνm hν1]
    with y hy
  obtain ⟨hyD, hA⟩ := hy
  have hv : ‖ν y‖ = 1 := hν1 y
  obtain ⟨ρ₁, C, hρ₁, hC, hball, -, hdens⟩ :=
    Submission.codim1_rdo_dg_cutoff_estimates m D F μ ν y (ν y) hD hF hDc hloc hνm hν1 hGG
      hyD hv hA
  have hblow := Submission.codim1_rdo_dg_blowup_halfspace m D F μ ν y (ν y) hm hD hF hDc hloc
    hνm hν1 hGG hyD hv hA
  -- `τ = Hᵐ⌞ν(y)ᗮ = ι_# Lᵐ` is finite on closed balls
  have hv0 : ν y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  obtain ⟨ι, -, hmap⟩ := Submission.codim1_rdo_dg_tma_hyperplane_param m (ν y) hv0
  have hfin : ∀ R : ℝ, ((μHE[m] : Measure (Euclid (m + 1))).restrict
      ((Submodule.span ℝ {ν y})ᗮ : Set (Euclid (m + 1)))) (closedBall (0 : Euclid (m + 1)) R)
      ≠ ∞ := by
    intro R
    rw [hmap, Measure.map_apply ι.continuous.measurable measurableSet_closedBall]
    have hpre : (ι : Euclid m → Euclid (m + 1)) ⁻¹' closedBall 0 R = closedBall 0 R := by
      ext x
      simp [ι.norm_map]
    rw [hpre]
    exact measure_closedBall_lt_top.ne
  -- Step 5: it suffices to treat `C¹` test functions
  intro f hf hfc
  refine Submission.codim1_rdo_dg_tma_continuous_extension (m + 1) m μ _ y ρ₁ C hρ₁ hC hdens hfin
    ?_ f hf hfc
  -- Step 4: it suffices to treat the integrals weighted by `⟨ν(y), ν⟩`
  intro g hg hgc
  refine Submission.codim1_rdo_dg_tma_normal_defect (m + 1) m μ ν y (ν y) ρ₁ C _ g hνm hν1 hv hρ₁
    hC hdens hA hg.continuous hgc ?_
  -- Step 3: the vector convergence (3a) for the field `g ν(y)`
  have key := Submission.codim1_rdo_dg_tma_vector_convergence m D F μ ν y (ν y) ρ₁ hF hGG hρ₁
    hball hv hblow (fun w => g w • ν y) (hg.smul contDiff_const) hgc.smul_right
  simpa [real_inner_smul_left, real_inner_self_eq_norm_sq, hv] using key

/-- **De Giorgi's structure theorem**, Gauss–Green form (Simon Ch. 3, 4.1–4.3).  Let `m ≥ 1`,
`D ⊆ ℝ^{m+1}` open and `F` Borel with locally finite perimeter in `D`.  Then there are a
countably `m`-rectifiable Borel set `B ⊆ D`, with `Hᵐ(B ∩ K) < ∞` for compact `K ⊆ D`, and a
Borel `ν`, with `|ν| = 1` on `B` and approximate tangent space `ν(y)^⊥` at `Hᵐ`-a.e. `y ∈ B`,
such that `∫_F div φ = −∫_B ⟨φ, ν⟩ dHᵐ` for `φ ∈ C¹_c(D; ℝ^{m+1})`.  The Riesz representation
of the perimeter functional gives a Gauss–Green pair `(μ, ν)` (4.1).  At `μ`-a.e. `y` the
blow-ups of `μ` converge to `Hᵐ⌞ν(y)^⊥` (4.3 (†)).  Since countably `m`-rectifiable sets of finite
measure have `Hᵐ`-density one a.e., this gives `μ = Hᵐ⌞B`, with approximate tangent planes
`ν^⊥`, and then (4.1) is the Gauss–Green formula over `B`. -/
theorem Submission.codim1_rdo_de_giorgi_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))), 1 ≤ m → IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (B : Set (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), MeasurableSet B ∧ B ⊆ D ∧ CountablyRectifiable m B ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μHE[m] (B ∩ K) ≠ ∞) ∧ Measurable ν ∧ (∀ y ∈ B, ‖ν y‖ = 1) ∧ (∀ᵐ y ∂(μHE[m].restrict B), HasApproximateTangentSpaceAt m B y (Submodule.span ℝ {ν y})ᗮ) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y in B, inner ℝ (φ y) (ν y) ∂μHE[m] := by
  intro m D F hm hD hF hper
  -- Steps 1–2: the Gauss–Green pair `(μ, ν)` of (4.1), `|ν| ≡ 1`
  obtain ⟨μ, ν, hμD, hμK, hν, hν1, hGG⟩ :=
    Submission.codim1_rdo_dg_gauss_green_measure m D F hD hF hper
  -- Steps 3–4: at `μ`-a.e. `y` the blow-ups of `μ` converge to `Hᵐ⌞ν(y)^⊥` (4.3 (†))
  have htan :=
    Submission.codim1_rdo_dg_tangent_measure_ae m D F μ ν hm hD hF hμD hμK hν hν1 hGG
  -- Steps 5–8: `μ = Hᵐ⌞B`, using `Hᵐ`-density one of rectifiable sets (`P = m + 1`, `n = m`)
  obtain ⟨B, hB, hBD, hBrect, rfl, hBtan⟩ :=
    Submission.codim1_rdo_dg_measure_eq_hausdorff m D μ ν hm hD hμD hμK hν hν1 htan
      fun S hS hSrect hSfin =>
        Submission.codim1_rdo_rectifiable_ae_density_one (m + 1) m S hm hS hSrect hSfin
  -- Step 9: `Hᵐ(B ∩ K) = μ(K) < ∞`, and (4.1) for `μ = Hᵐ⌞B` is the Gauss–Green formula
  refine ⟨B, ν, hB, hBD, hBrect, fun K hK hKD => ?_, hν, fun y _ => hν1 y, hBtan, hGG⟩
  rw [inter_comm, ← Measure.restrict_apply' hB]
  exact hμK K hK hKD

end GMT.Ch07
