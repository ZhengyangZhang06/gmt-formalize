import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
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

/-- **Faces of the unit cubical lattice** (Simon Ch. 6, §5: the `n`-faces `F ∈ 𝓛ₙ` used in the proof
of the deformation theorem 5.1).  Let `n = m + 1` and `p = (z, ι)` with `ι : Fin n → Fin P` strictly
increasing.  The map `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` has coordinates `z_{ι(k)} + y_k` at `ι(k)` and
`zᵢ` off `range ι`, so it is an isometric embedding `ℝⁿ → ℝᴾ` with `Φ_p⁻¹(F_p) = [0, 1]ⁿ` and
`F_p ⊆ range Φ_p`.  As `μHE[n] = volume` on `ℝⁿ`, `Φ_p#μHE[n] = μHE[n]⌞range Φ_p` and `∂[0, 1]ⁿ` is
Lebesgue-null, `Hⁿ⌞F_p = Φ_p#(Lⁿ⌞(0, 1)ⁿ)`; hence `Hⁿ(F_p) = 1` and
`∫_{F_p} f dHⁿ = ∫_{(0, 1)ⁿ} f ∘ Φ_p`.  `F_p` is closed with diameter `≤ √P`, and the non-integer
coordinates of a point of `Φ_p((0, 1)ⁿ)` determine `ι` and `z`, so it lies in no other face
`F_q`. -/
theorem Submission.dor_lmb_fcd_fr_face_geometry : ∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)), StrictMono p.2 → volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ μHE[m + 1] {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = 1 ∧ (μHE[m + 1] : Measure (Euclid P)).restrict {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = Measure.map (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∀ f : Euclid P → ℝ, ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, f x ∂μHE[m + 1] = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, f (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))) ∧ (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}) ∧ (∀ y y' : Euclid (m + 1), dist (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.2 j) (1 : ℝ)) = dist y y') ∧ (∀ x ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, ∀ x' ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, dist x x' ≤ Real.sqrt P) ∧ IsClosed {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∉ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧ (i ∉ Set.range q.2 → x i = q.1 i)} := by
  intro P m p hp
  -- the face map `Φ = Φ_p`, the closed face `F = F_p`, the open cube `Q = Q₁`, the closed cube `C`
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let F : Set (Euclid P) := {x : Euclid P | ∀ i : Fin P,
    (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}
  let Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  let C : Set (Euclid (m + 1)) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1}
  show volume Q = 1 ∧ μHE[m + 1] F = 1 ∧
    (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) ∧
    (∀ f : Euclid P → ℝ, ∫ x in F, f x ∂μHE[m + 1] = ∫ y in Q, f (Φ y)) ∧
    (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F) ∧
    (∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y') ∧
    (∀ x ∈ F, ∀ x' ∈ F, dist x x' ≤ Real.sqrt P) ∧ IsClosed F ∧
    ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p →
      ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → Φ y ∉ {x : Euclid P | ∀ i : Fin P,
        (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧
          (i ∉ Set.range q.2 → x i = q.1 i)}
  have hinj : Injective p.2 := hp.injective
  -- Step 1: coordinates of `Φ`
  have hcoord : ∀ y i, Φ y i = p.1 i + ∑ j, if i = p.2 j then y j else 0 := by
    intro y i
    simp [Φ, Pi.single_apply]
  have hcoord_mem : ∀ y k, Φ y (p.2 k) = p.1 (p.2 k) + y k := by
    intro y k
    rw [hcoord]
    simp [hinj.eq_iff]
  have hcoord_nmem : ∀ y i, i ∉ range p.2 → Φ y i = p.1 i := by
    intro y i hi
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hi ⟨j, h.symm⟩
  -- Step 2: `Φ` is an isometry, hence a measurable embedding
  have hdist : ∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y' := by
    intro y y'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    symm
    refine Fintype.sum_of_injective p.2 hinj _ _ (fun i hi => ?_) (fun k => ?_)
    · rw [hcoord_nmem y i hi, hcoord_nmem y' i hi, dist_self]
      simp
    · rw [hcoord_mem, hcoord_mem, dist_add_left]
  have hiso : Isometry Φ := Isometry.of_dist_eq hdist
  have hemb : MeasurableEmbedding Φ := hiso.isClosedEmbedding.measurableEmbedding
  -- Step 3: `Φ` maps the closed cube `C` into `F`, `F ⊆ range Φ` and `Φ⁻¹(F) = C`
  have hCF : ∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F := by
    intro y hy i
    constructor
    · rintro ⟨k, rfl⟩
      rw [hcoord_mem]
      constructor <;> linarith [(hy k).1, (hy k).2]
    · exact hcoord_nmem y i
  have hFrange : F ⊆ range Φ := by
    intro x hx
    refine ⟨WithLp.toLp 2 fun k => x (p.2 k) - p.1 (p.2 k), PiLp.ext fun i => ?_⟩
    by_cases hi : i ∈ range p.2
    · obtain ⟨k, rfl⟩ := hi
      rw [hcoord_mem]
      simp
    · rw [hcoord_nmem _ i hi]
      exact ((hx i).2 hi).symm
  have hpreF : Φ ⁻¹' F = C := by
    ext y
    refine ⟨fun hy k => ?_, hCF y⟩
    have h := (hy (p.2 k)).1 ⟨k, rfl⟩
    rw [hcoord_mem] at h
    constructor <;> linarith [h.1, h.2]
  -- Step 4: `volume Q = volume C = 1`
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  have hQ_eq : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hC_eq : C = WithLp.ofLp ⁻¹' (Set.Icc (0 : Fin (m + 1) → ℝ) 1) := by
    ext y
    simp [C, Pi.le_def, forall_and]
  have hQmeas : MeasurableSet Q := by
    rw [hQ_eq]
    exact hvol.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hvolQ : volume Q = 1 := by
    rw [hQ_eq, hvol.measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hvolC : volume C = 1 := by
    rw [hC_eq, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp
  have hQC : volume.restrict C = volume.restrict Q := by
    refine (Measure.restrict_congr_set ?_).symm
    refine ae_eq_of_subset_of_measure_ge (fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩)
      (hvolC.trans hvolQ.symm).le hQmeas.nullMeasurableSet ?_
    rw [hvolC]
    exact ENNReal.one_ne_top
  -- Step 5: `F` is closed
  have hcont : ∀ i : Fin P, Continuous fun x : Euclid P => x i := fun i =>
    PiLp.continuous_apply 2 _ i
  have hFclosed : IsClosed F := by
    have hF : F = ⋂ i : Fin P, {x : Euclid P | (i ∈ Set.range p.2 →
        (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} :=
      Set.ofPred_forall _
    rw [hF]
    refine isClosed_iInter fun i =>
      (isClosed_imp isOpen_const ?_).inter (isClosed_imp isOpen_const ?_)
    · exact (isClosed_le continuous_const (hcont i)).inter (isClosed_le (hcont i) continuous_const)
    · exact isClosed_eq (hcont i) continuous_const
  have hFmeas : MeasurableSet F := hFclosed.measurableSet
  -- Step 6: `Hⁿ⌞F = Φ#(volume⌞Q)`
  have hmeas :
      (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) := by
    have h1 : Measure.map Φ (volume : Measure (Euclid (m + 1))) =
        (μHE[m + 1] : Measure (Euclid P)).restrict (range Φ) := by
      rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rw [← hQC, ← hpreF, ← hemb.restrict_map, h1, Measure.restrict_restrict hFmeas,
      inter_eq_left.2 hFrange]
  -- Step 7: `Hⁿ(F) = 1`
  have hFmass : μHE[m + 1] F = 1 := by
    have h := congrArg (fun μ : Measure (Euclid P) => μ univ) hmeas
    simp only [Measure.restrict_apply_univ] at h
    rw [h, hemb.map_apply, preimage_univ, Measure.restrict_apply_univ, hvolQ]
  refine ⟨hvolQ, hFmass, hmeas, fun f => ?_, hCF, hdist, ?_, hFclosed, ?_⟩
  -- Step 8: the integral formula
  · rw [hmeas, hemb.integral_map]
  -- Step 9: `diam F ≤ √P`
  · intro x hx x' hx'
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (x i) (x' i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => pow_le_one₀ dist_nonneg ?_
          by_cases hi : i ∈ range p.2
          · have h := (hx i).1 hi
            have h' := (hx' i).1 hi
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [h.1, h.2, h'.1, h'.2]
          · rw [(hx i).2 hi, (hx' i).2 hi, dist_self]
            exact zero_le_one
      _ = P := by simp
  -- Step 10: the open face `Φ(Q)` meets no other closed face
  · intro q hq hqp y hy hx
    apply hqp
    have hsub : range p.2 ⊆ range q.2 := by
      rintro _ ⟨k, rfl⟩
      by_contra hk
      have h := (hx (p.2 k)).2 hk
      rw [hcoord_mem] at h
      have a1 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) := by linarith [(hy k).1]
      have a2 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [(hy k).2]
      have b1 : p.1 (p.2 k) < q.1 (p.2 k) := by exact_mod_cast a1
      have b2 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a2
      omega
    have hrange : range p.2 = range q.2 := by
      apply Set.eq_of_subset_of_card_le hsub
      rw [Set.card_range_of_injective hq.injective, Set.card_range_of_injective hinj]
    have h2 : p.2 = q.2 := (hp.range_inj_of_wellFoundedLT hq).1 hrange
    have h1 : p.1 = q.1 := by
      funext i
      by_cases hi : i ∈ range p.2
      · obtain ⟨k, rfl⟩ := hi
        have h := (hx (p.2 k)).1 (hrange ▸ ⟨k, rfl⟩)
        rw [hcoord_mem] at h
        have a1 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [h.1, (hy k).2]
        have a2 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) + 1 := by linarith [h.2, (hy k).1]
        have b1 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a1
        have b2 : p.1 (p.2 k) < q.1 (p.2 k) + 1 := by exact_mod_cast a2
        omega
      · have h : (p.1 i : ℝ) = q.1 i := by
          rw [← hcoord_nmem y i hi]
          exact (hx i).2 (hrange ▸ hi)
        exact_mod_cast h
    exact Prod.ext h1.symm h2.symm

/-- **The `(m + 1)`-cells of the unit cubical lattice meeting a compact set** (Simon Ch. 6, proof
of the deformation theorem 5.1, (26)–(33), with `n = m + 1`).  `L_n` is the set of points of `ℝᴾ`
with at least `P − n` integer coordinates, `L_{n−1}` the set of those with at least `P − m`.
(0) `Hⁿ(L_{n−1}) = 0`: `L_{n−1}` lies in the countably many coordinate planes
`A(t, z) = {x : xᵢ = zᵢ, i ∈ t}`, `P ≤ m + |t|`, each the Lipschitz image of a space of dimension
`P − |t| < m + 1`.
(1) `L_n` is a finite union of finite intersections of the closed sets `{x : xᵢ ∈ ℤ}`.
(2) The faces `F_p` meeting the bounded set `K` have bounded integer corners, so they are finitely
many, and (3) by `diam F_p ≤ √P` they lie in the closed `√P`-neighbourhood of `K`.
(4) A point `x ∈ (L_n ∩ K) \ L_{n−1}` has exactly `n` non-integer coordinates; with `ι` their
increasing enumeration and `y` their fractional parts, `x = Φ_{(⌊x⌋, ι)}(y)`, `y ∈ Q₁`, and
`(⌊x⌋, ι)` is a face meeting `K`.  (5) By (0) this covers `Hⁿ`-a.e. point of `L_n ∩ K`. -/
theorem Submission.dor_lmb_fcd_fr_skeleton_cells : ∀ (P m : ℕ) (K : Set (Euclid P)), m + 1 < P → IsCompact K → ∃ s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ⊆ cthickening (Real.sqrt P) K) ∧ IsClosed {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧ ∀ i ∈ t, ∃ z : ℤ, x i = z} ∧ ∀ᵐ x ∂(μHE[m + 1].restrict ({x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧ ∀ i ∈ t, ∃ z : ℤ, x i = z} ∩ K)), ∃ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) = x := by
  intro P m K hmP hK
  -- Step 0: `Hⁿ(L_{n−1}) = 0`, i.e. the points with at least `P − m` integer coordinates are
  -- `μHE[m + 1]`-null
  have hnull : μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
    -- each coordinate plane `A(s, z)` with `P ≤ m + |s|` is `μH[m + 1]`-null
    have hplane : ∀ s : Finset (Fin P), P ≤ m + s.card → ∀ z : Fin P → ℤ,
        μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∀ i ∈ s, x i = z i} = 0 := by
      intro s hs z
      -- `A(s, z)` is the image of the Lipschitz map `g : t ↦ (zᵢ on s, tᵢ off s)`
      let g : ({i // i ∉ s} → ℝ) → Euclid P := fun t =>
        WithLp.toLp 2 fun i => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩
      have hg1 : LipschitzWith 1 fun t : {i // i ∉ s} → ℝ =>
          fun i : Fin P => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩ := by
        refine LipschitzWith.of_dist_le_mul fun t t' => ?_
        rw [NNReal.coe_one, one_mul]
        refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
        by_cases h : i ∈ s
        · simp [h]
        · simpa [h] using dist_le_pi_dist t t' ⟨i, h⟩
      have hg : LipschitzWith _ g := (PiLp.lipschitzWith_toLp 2 fun _ : Fin P => ℝ).comp hg1
      have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ g '' univ := by
        intro x hx
        refine ⟨fun j => x j.1, mem_univ _, ?_⟩
        ext i
        by_cases h : i ∈ s
        · simp [g, h, hx i h]
        · simp [g, h]
      -- the source of `g` has dimension `P − |s| ≤ m < m + 1`, so it is `μH[m + 1]`-null
      have hcard : Fintype.card {i // i ∉ s} ≤ m := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
        omega
      have huniv : (μH[((m + 1 : ℕ) : ℝ)] : Measure ({i // i ∉ s} → ℝ)) univ = 0 := by
        rw [← Metric.iUnion_ball_nat (0 : {i // i ∉ s} → ℝ)]
        refine measure_iUnion_null fun n => ?_
        refine (Measure.hausdorffMeasure_zero_or_top
          (d₁ := (Fintype.card {i // i ∉ s} : ℝ)) ?_ _).resolve_right ?_
        · exact_mod_cast Nat.lt_succ_of_le hcard
        · rw [hausdorffMeasure_pi_real]
          exact measure_ball_lt_top.ne
      refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
      calc μH[((m + 1 : ℕ) : ℝ)] (g '' univ)
          ≤ _ ^ ((m + 1 : ℕ) : ℝ) * μH[((m + 1 : ℕ) : ℝ)] (univ : Set ({i // i ∉ s} → ℝ)) :=
            hg.hausdorffMeasure_image_le (Nat.cast_nonneg _) univ
        _ = 0 := by rw [huniv, mul_zero]
    -- the set is covered by the countably many planes `A(s, z)`, `P ≤ m + |s|`, `z ∈ ℤᴾ`
    have hcover : {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, x i = z} ⊆ ⋃ (s : {s : Finset (Fin P) // P ≤ m + s.card})
          (z : Fin P → ℤ), {x : Euclid P | ∀ i ∈ s.1, x i = z i} := by
      rintro x ⟨s, hs, hx⟩
      choose! z hz using hx
      exact mem_iUnion₂.2 ⟨⟨s, hs⟩, z, hz⟩
    -- countable subadditivity gives `μH[m + 1]`-nullity, and `μHE[m + 1] = c • μH[m + 1]`
    have hnullH : μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 :=
      measure_mono_null hcover
        (measure_iUnion_null fun s => measure_iUnion_null fun z => hplane s.1 s.2 z)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hnullH, smul_zero]
  -- Step 1: `L_n` is closed, a finite union of finite intersections of the closed sets
  -- `{x : xᵢ ∈ ℤ}`
  have hLclosed : IsClosed {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧
      ∀ i ∈ t, ∃ z : ℤ, x i = z} := by
    have hcoord : ∀ i : Fin P, IsClosed {x : Euclid P | ∃ z : ℤ, x i = z} := by
      intro i
      have h : {x : Euclid P | ∃ z : ℤ, x i = z} =
          (fun x : Euclid P => x i) ⁻¹' range ((↑) : ℤ → ℝ) := by
        ext x
        exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
      rw [h]
      exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage (by fun_prop)
    have h : {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧
        ∀ i ∈ t, ∃ z : ℤ, x i = z} = ⋃ (t : Finset (Fin P)) (_ : P ≤ m + 1 + t.card),
          ⋂ i ∈ t, {x : Euclid P | ∃ z : ℤ, x i = z} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
    rw [h]
    exact isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
      isClosed_iInter fun i => isClosed_iInter fun _ => hcoord i
  classical
  -- Step 2: the faces `F_p` meeting `K ⊆ B̄_R(0)` have corners with `|zᵢ| ≤ ⌈R⌉ + 1`, so they
  -- form a finite set
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hKcoord : ∀ x ∈ K, ∀ i : Fin P, |x i| ≤ R := fun x hx i =>
    (Real.norm_eq_abs (x i)).symm.le.trans ((PiLp.norm_apply_le x i).trans (hR x hx))
  let faces : Set ((Fin P → ℤ) × (Fin (m + 1) → Fin P)) := {p | StrictMono p.2 ∧ ∃ k ∈ K,
    k ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧
      (i ∉ Set.range p.2 → x i = p.1 i)}}
  have hfin : faces.Finite := by
    refine ((Set.Finite.pi (t := fun _ : Fin P => Set.Icc (-(⌈R⌉ + 1)) (⌈R⌉ + 1))
      fun _ => Set.finite_Icc _ _).prod (Set.finite_univ (α := Fin (m + 1) → Fin P))).subset ?_
    rintro p ⟨-, k, hkK, hkF⟩
    have hceil := Int.le_ceil R
    refine ⟨fun i _ => ?_, mem_univ _⟩
    -- `zᵢ ≤ xᵢ ≤ R` and `zᵢ ≥ xᵢ − 1 ≥ −R − 1` for `x ∈ F_p ∩ K`
    obtain ⟨hk₁, hk₂⟩ := abs_le.1 (hKcoord k hkK i)
    have hzb : (p.1 i : ℝ) ≤ R ∧ -R - 1 ≤ (p.1 i : ℝ) := by
      by_cases hi : i ∈ Set.range p.2
      · obtain ⟨h₁, h₂⟩ := (hkF i).1 hi
        constructor <;> linarith
      · have h := (hkF i).2 hi
        constructor <;> linarith
    have h₁ : ((-(⌈R⌉ + 1) : ℤ) : ℝ) ≤ p.1 i := by
      push_cast
      linarith [hzb.2]
    have h₂ : (p.1 i : ℝ) ≤ ((⌈R⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [hzb.1]
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  refine ⟨hfin.toFinset, fun p hp => (hfin.mem_toFinset.1 hp).1, fun p hp => ?_, hLclosed, ?_⟩
  · -- Step 3: `diam F_p ≤ √P` and `F_p ∩ K ≠ ∅` give `F_p ⊆ cthickening √P K`
    obtain ⟨hp2, k, hkK, hkF⟩ := hfin.mem_toFinset.1 hp
    obtain ⟨-, -, -, -, -, -, hdiam, -, -⟩ := Submission.dor_lmb_fcd_fr_face_geometry P m p hp2
    exact fun x hx => mem_cthickening_of_dist_le x k _ K hkK (hdiam x hx k hkF)
  · -- Steps 4–5: off the null set `L_{n−1}` (step 0), every `x ∈ L_n ∩ K` is `Φ_p(y)` for a face
    -- `p` meeting `K` and some `y ∈ Q₁`
    rw [ae_restrict_iff' (hLclosed.inter hK.isClosed).measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hxL' hx
    obtain ⟨⟨t, ht, hxt⟩, hxK⟩ := hx
    -- `T` the integer and `S` the non-integer coordinates of `x`: `|T| = P − n`, `|S| = n`
    set T : Finset (Fin P) := Finset.univ.filter fun i => ∃ z : ℤ, x i = z with hT
    set S : Finset (Fin P) := Finset.univ.filter fun i => ¬ ∃ z : ℤ, x i = z with hS
    have hTS : T.card + S.card = P := by
      rw [hT, hS, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have htT : t.card ≤ T.card := Finset.card_le_card fun i hi =>
      Finset.mem_filter.2 ⟨Finset.mem_univ i, hxt i hi⟩
    have hT' : ¬ P ≤ m + T.card := fun h =>
      hxL' ⟨T, h, fun i hi => (Finset.mem_filter.1 hi).2⟩
    have hScard : S.card = m + 1 := by omega
    -- `ι` enumerates `S` increasingly, `z = ⌊x⌋`, and `y` collects the fractional parts
    let ι := S.orderEmbOfFin hScard
    have hιS : Set.range ι = S := Finset.range_orderEmbOfFin S hScard
    let y : Euclid (m + 1) := WithLp.toLp 2 fun k => Int.fract (x (ι k))
    have hy : ∀ k, 0 < y k ∧ y k < 1 := by
      intro k
      have hk : ι k ∈ S := Finset.orderEmbOfFin_mem S hScard k
      rw [hS, Finset.mem_filter] at hk
      exact ⟨Int.fract_pos.2 fun h => hk.2 ⟨_, h⟩, Int.fract_lt_one _⟩
    have hΦ : WithLp.toLp 2 (fun i => ((⌊x i⌋ : ℤ) : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ) = x := by
      ext i
      rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
      simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i ∈ S
      · -- `i = ι(j₀)`: the coordinate is `⌊xᵢ⌋ + fract xᵢ = xᵢ`
        obtain ⟨j₀, rfl⟩ : i ∈ Set.range ι := by rw [hιS]; exact hi
        rw [Fintype.sum_eq_single j₀, ite_eq_left rfl]
        · exact Int.floor_add_fract _
        · intro j hj
          exact ite_eq_right (ι.injective.ne hj.symm)
      · -- `i ∉ range ι`: the coordinate is `⌊xᵢ⌋ = xᵢ ∈ ℤ`
        obtain ⟨z, hz⟩ : ∃ z : ℤ, x i = z := by
          by_contra h
          exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
        have h0 : ∀ j, (if i = ι j then y j else 0) = 0 := fun j =>
          ite_eq_right fun h => hi (by rw [h]; exact Finset.orderEmbOfFin_mem S hScard j)
        simp only [h0, Finset.sum_const_zero, add_zero, hz, Int.floor_intCast]
    -- `x = Φ_p(y) ∈ F_p ∩ K` for `p = (⌊x⌋, ι)`, so `p` is one of the faces
    let p : (Fin P → ℤ) × (Fin (m + 1) → Fin P) := (fun i => ⌊x i⌋, ι)
    have hΦp : WithLp.toLp 2 (fun i => (p.1 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) = x := hΦ
    have hp : p ∈ faces := by
      refine ⟨ι.strictMono, x, hxK, ?_⟩
      obtain ⟨-, -, -, -, hcube, -, -, -, -⟩ :=
        Submission.dor_lmb_fcd_fr_face_geometry P m p ι.strictMono
      have h := hcube y fun k => ⟨(hy k).1.le, (hy k).2.le⟩
      rwa [hΦp] at h
    exact ⟨p, hfin.mem_toFinset.2 hp, y, hy, hΦp⟩
/-- **Unit orientations of the approximate tangent plane of a set in a coordinate plane** (Simon
Ch. 6, proof of 5.1, (26)–(27)).  Let `A ⊆ x + V`, `V = span{e_{ι j}}`, have approximate tangent
space `Q` at `x`, and let `ξ` orient `Q`.  The blow-ups `λ⁻¹(A − x)` lie in `V`, so every test
function vanishing on `V` has zero limit integral `∫_Q f dHⁿ`; since `Q` is the support of `Hⁿ⌞Q`,
this forces `Q ⊆ V`.  The orthonormal frame `τ` of `Q` then satisfies `τₖ = Σⱼ Mⱼₖ e_{ι j}` with
`MᵀM = 1`, so `α(τ) = det M · α(e_ι)` with `det M = ±1` for every `n`-covector `α`. -/
theorem Submission.dor_lmb_fcd_fr_plane_orientation : ∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) := by
  intro P n ι A x Q ξ hι hA hQ hξ
  obtain ⟨τ, hτ, hτQ, hξτ⟩ := hξ
  -- Step 1: every `q ∈ Q` has `qᵢ = 0` for `i ∉ range ι`
  have hQV : ∀ q ∈ Q, ∀ i, (∀ j, ι j ≠ i) → q i = 0 := by
    intro q hq i hi
    by_contra hqi
    have hc : 0 < |q i| := abs_pos.2 hqi
    -- the test function `g w = max 0 (|qᵢ| - |w - q|)`: positive near `q`, zero where `wᵢ = 0`
    let g : Euclid P → ℝ := fun w => max 0 (|q i| - dist w q)
    have hgc : Continuous g := by fun_prop
    have hgs : HasCompactSupport g := by
      refine HasCompactSupport.intro (isCompact_closedBall q |q i|) fun w hw => ?_
      rw [mem_closedBall, not_le] at hw
      exact max_eq_left (by linarith)
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := g
        continuous_toFun := hgc
        hasCompactSupport' := hgs }
    have hfg : ∀ w, f w = g w := fun _ => rfl
    have hg0 : ∀ w : Euclid P, w i = 0 → g w = 0 := by
      intro w hw
      have h1 : |q i| ≤ dist w q := by
        have h2 := PiLp.norm_apply_le (w - q) i
        rw [dist_eq_norm]
        simpa [hw] using h2
      exact max_eq_left (by linarith)
    -- the integrals over the blow-ups `λ⁻¹(A - x) ⊆ {wᵢ = 0}` vanish, so `∫_Q f dHⁿ = 0`
    have hlim : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] = 0 := by
      refine tendsto_nhds_unique (hQ.2 f) (tendsto_const_nhds.congr fun r => ?_)
      refine (setIntegral_eq_zero_of_forall_eq_zero ?_).symm
      rintro _ ⟨a, ha, rfl⟩
      rw [hfg]
      apply hg0
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, hA a ha i hi]
    -- but `q` lies in the support `Q` of `Hⁿ⌞Q` and `f > 0` near `q`, so `∫_Q f dHⁿ > 0`
    have hpos : 0 < ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
      have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
      have hf0 : (0 : Euclid P → ℝ) ≤ ⇑f := fun w => by rw [hfg]; exact le_max_left _ _
      rw [integral_pos_iff_support_of_nonneg hf0 f.integrable]
      have hq' : q ∈ (μHE[n].restrict (Q : Set (Euclid P))).support := by
        rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
        exact hq
      refine (Measure.mem_support_iff_forall q).1 hq' _ ?_
      refine Filter.mem_of_superset (ball_mem_nhds q hc) fun w hw => ?_
      rw [mem_ball] at hw
      rw [Function.mem_support, hfg]
      exact (lt_max_of_lt_right (by linarith)).ne'
    linarith
  -- Step 2: the frame `τ` lies in `V = span{e_ι}`
  have hτV : ∀ k i, (∀ j, ι j ≠ i) → τ k i = 0 := fun k i hi =>
    hQV (τ k) (by rw [← hτQ]; exact Submodule.subset_span (mem_range_self k)) i hi
  -- coordinates `m k = (τ k (ι j))ⱼ` of `τ k` in the frame `e_ι`, and `L w = Σⱼ wⱼ e_{ι j}`
  let m : Fin n → Fin n → ℝ := fun k j => τ k (ι j)
  let L : (Fin n → ℝ) →ₗ[ℝ] Euclid P :=
    Fintype.linearCombination ℝ fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  have hLm : ∀ k, L (m k) = τ k := by
    intro k
    refine PiLp.ext fun i => ?_
    simp only [L, m, Fintype.linearCombination_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero]
    by_cases h : ∃ j, ι j = i
    · obtain ⟨j, rfl⟩ := h
      simp [hι.injective.eq_iff]
    · have h' : ∀ j, ι j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [hτV k i h']
      exact Finset.sum_eq_zero fun j _ => ite_eq_right (h' j).symm
  have hLe : ∀ k, L (Pi.basisFun ℝ (Fin n) k) = EuclideanSpace.single (ι k) (1 : ℝ) := by
    intro k
    rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]
  -- Step 3: `M = (τ k (ι j))` is orthogonal, so `det M = ±1`
  let M : Matrix (Fin n) (Fin n) ℝ := (Pi.basisFun ℝ (Fin n)).toMatrix m
  have hMM : M.transpose * M = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← orthonormal_iff_ite.1 hτ k l, PiLp.inner_apply]
    simp only [Matrix.transpose_apply, M, Module.Basis.toMatrix_apply, Pi.basisFun_repr, m]
    refine Fintype.sum_of_injective ι hι.injective _ _ ?_ fun j => ?_
    · rintro i hi
      rw [hτV k i fun j hj => hi ⟨j, hj⟩]
      simp
    · simp [mul_comm]
  have hdet : M.det = 1 ∨ M.det = -1 := by
    have h := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact mul_self_eq_one_iff.1 h
  -- Step 4: `α(τ) = det M · α(e_ι)` for every `n`-covector `α`
  have hα : ∀ α : Covector (Euclid P) n,
      α τ = M.det * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    intro α
    have key := DFunLike.congr_fun
      (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) (α.toAlternatingMap.compLinearMap L)) m
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.coe_toAlternatingMap, hLm, hLe, Module.Basis.det_apply] at key
    rw [mul_comm] at key
    exact key
  rcases hξτ with h | h <;> rcases hdet with hd | hd
  · exact Or.inl fun α => by rw [h, hα, hd, one_mul]
  · exact Or.inr fun α => by rw [h, hα, hd, neg_one_mul]
  · exact Or.inr fun α => by rw [h, hα, hd, one_mul]
  · exact Or.inl fun α => by rw [h, hα, hd, neg_one_mul, neg_neg]
/-- **Coordinate covectors** (Simon Ch. 6, §1, 1.1, 1.2 and 1.5).  For `J : Fin k → Fin P`,
`dx^J = dx^{J(0)} ∧ ⋯ ∧ dx^{J(k−1)}` is the alternatization of the continuous multilinear map
`v ↦ ∏ᵣ (v_r)_{J(r)}`, so `dx^J(v) = Σ_σ sign σ ∏ᵣ (v_{σ(r)})_{J(r)}`.  At `e_I` the `σ`-term is
`[I ∘ σ = J]`; for strictly increasing `I, J`, `I ∘ σ = J` makes `σ` strictly increasing, hence
`σ = id` and `I = J`, so `dx^J(e_I) = [I = J]`.  For an injective family of strictly increasing
`J_l`, `(Σ_l c_l dx^{J_l})(e_I)` is `c_l` if `I = J_l` and `0` if `I ∉ range J`; summing the
squares over strictly increasing `I` gives `covectorEuclideanNorm (Σ_l c_l dx^{J_l}) = √(Σ_l c_l²)`.
-/
theorem Submission.dor_lmb_fcd_fr_coordinate_covectors : ∀ (P k : ℕ), ∃ dx : (Fin k → Fin P) → Covector (Euclid P) k, (∀ I J : Fin k → Fin P, StrictMono I → StrictMono J → dx J (fun r => EuclideanSpace.single (I r) (1 : ℝ)) = if I = J then 1 else 0) ∧ ∀ (N : ℕ) (J : Fin N → Fin k → Fin P) (c : Fin N → ℝ), Function.Injective J → (∀ l, StrictMono (J l)) → covectorEuclideanNorm (∑ l, c l • dx (J l)) = Real.sqrt (∑ l, c l ^ 2) := by
  intro P k
  classical
  -- Step 1: `dx^J` is the alternatization of `v ↦ ∏ᵣ (v_r)_{J(r)}`
  let dx : (Fin k → Fin P) → Covector (Euclid P) k := fun J =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
        (fun r => EuclideanSpace.proj (J r)))
  have hdx : ∀ (J : Fin k → Fin P) (v : Fin k → Euclid P),
      dx J v = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ r, (v (σ r)) (J r) := by
    intro J v
    simp only [dx, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
    rfl
  -- Step 2: if `I ∘ σ = J` with `I, J` strictly increasing, then `σ = id` and `I = J`
  have hperm : ∀ (I J : Fin k → Fin P), StrictMono I → StrictMono J →
      ∀ σ : Equiv.Perm (Fin k), (∀ r, I (σ r) = J r) → σ = 1 ∧ I = J := by
    intro I J hI hJ σ hσ
    have hσmono : StrictMono σ := by
      intro a b hab
      have : I (σ a) < I (σ b) := by rw [hσ a, hσ b]; exact hJ hab
      exact hI.lt_iff_lt.mp this
    have hrange : Set.range σ = Set.range (id : Fin k → Fin k) := by
      rw [Set.range_id]; exact σ.surjective.range_eq
    have hid : (σ : Fin k → Fin k) = id :=
      (StrictMono.range_inj_of_wellFoundedLT hσmono strictMono_id).mp hrange
    have hσ1 : σ = 1 := by
      ext r; simp [congrFun hid r]
    refine ⟨hσ1, ?_⟩
    funext r
    have := hσ r
    rw [hσ1] at this
    simpa using this
  -- duality `dx^J(e_I) = [I = J]` for strictly increasing `I, J`
  have hdual : ∀ I J : Fin k → Fin P, StrictMono I → StrictMono J →
      dx J (fun r => EuclideanSpace.single (I r) (1 : ℝ)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    rw [hdx]
    have hterm : ∀ σ : Equiv.Perm (Fin k),
        ∏ r, (EuclideanSpace.single (I (σ r)) (1 : ℝ)) (J r) =
          if (∀ r, I (σ r) = J r) then 1 else 0 := by
      intro σ
      split_ifs with h
      · refine Finset.prod_eq_one fun r _ => ?_
        rw [h r]; simp
      · push Not at h
        obtain ⟨r, hr⟩ := h
        refine Finset.prod_eq_zero (Finset.mem_univ r) ?_
        simp [Ne.symm hr]
    simp_rw [hterm]
    split_ifs with hIJ
    · subst hIJ
      rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
      · simp
      · intro σ _ hσ
        rw [ite_eq_right]
        · simp
        · intro h
          exact hσ (hperm I I hI hI σ h).1
      · simp
    · refine Finset.sum_eq_zero fun σ _ => ?_
      rw [ite_eq_right]
      · simp
      · intro h
        exact hIJ (hperm I J hI hJ σ h).2
  refine ⟨dx, hdual, ?_⟩
  intro N J c hJinj hJmono
  -- Step 3: values of `Σ_l c_l dx^{J_l}` on the coordinate frames `e_I`
  have hval : ∀ I : Fin k → Fin P, StrictMono I →
      (∑ l, c l • dx (J l)) (fun r => EuclideanSpace.basisFun (Fin P) ℝ (I r)) =
        ∑ l, if I = J l then c l else 0 := by
    intro I hI
    simp only [EuclideanSpace.basisFun_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousAlternatingMap.smul_apply, hdual I (J l) hI (hJmono l)]
    split_ifs <;> simp
  -- by injectivity of `J`, at most one `l` has `J_l = I`
  have hsq : ∀ I : Fin k → Fin P,
      (∑ l, if I = J l then c l else 0) ^ 2 = ∑ l, if I = J l then c l ^ 2 else 0 := by
    intro I
    by_cases hex : ∃ l, I = J l
    · obtain ⟨l₀, hl₀⟩ := hex
      have h1 : (∑ l, if I = J l then c l else 0) = c l₀ := by
        rw [Finset.sum_eq_single l₀]
        · simp [hl₀]
        · intro l _ hl
          rw [ite_eq_right]
          intro h
          exact hl (hJinj (h.symm.trans hl₀))
        · simp
      have h2 : (∑ l, if I = J l then c l ^ 2 else 0) = c l₀ ^ 2 := by
        rw [Finset.sum_eq_single l₀]
        · simp [hl₀]
        · intro l _ hl
          rw [ite_eq_right]
          intro h
          exact hl (hJinj (h.symm.trans hl₀))
        · simp
      rw [h1, h2]
    · push Not at hex
      simp [hex]
  -- Step 4: sum the squares over strictly increasing `I` and exchange the finite sums
  unfold covectorEuclideanNorm
  congr 1
  calc (∑ I : Fin k → Fin P, if StrictMono I then
          ((∑ l, c l • dx (J l)) (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
      = ∑ I : Fin k → Fin P, ∑ l, (if I = J l then c l ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        split_ifs with hI
        · rw [hval I hI, hsq I]
        · symm
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [ite_eq_right]
          rintro rfl
          exact hI (hJmono l)
    _ = ∑ l, ∑ I : Fin k → Fin P, (if I = J l then c l ^ 2 else 0) := Finset.sum_comm
    _ = ∑ l, c l ^ 2 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp
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

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0

/-- **Simon Ch. 6, 3.2(3) and 2.11–2.12**: if `T = τ(M, θ, ξ)` in the open set `U`, then
(i) `M_W(T) = μ_R(W)` for every open `W`, where `μ_R = θ Hⁿ⌞M`, and (ii) `spt T = U ∩ spt μ_R`.
`M_W(T) ≤ μ_R(W)` because admissible forms pair with `ξ` to at most `1`; `μ_R(W) ≤ M_W(T)` by
smoothing the dual covector field of `ξ` (Lusin); (ii) follows from (i) alone. -/
theorem Submission.dor_imrep_massOn_eq_measure_and_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support := by
  intro P n U T R hU hR
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  exact ⟨hmass, Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass⟩
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
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

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ
/-- **Face representation** (Simon Ch. 6, proof of 5.1, (26)–(28) and (33)).  Let
`Q ∈ 𝒟ₙ(ℝᴾ)`, `n = m + 1`, be integer multiplicity and vanish off the closed set `E`, `Hⁿ`-almost
all of which lies in the open unit faces `A_p = Φ_p(Q₁)`, `p ∈ s`.  Then
`Q(ω) = Σ_p ∫_{Q₁} u_p(y) ω(Φ_p(y))(e_p) dy` with integer-valued `u_p` integrable on `Q₁` and
`Σ_p ∫_{Q₁} |u_p| ≤ M(Q)`.  For an `IMRep` `(M, θ, ξ)` of `Q`, `μ_Q(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(Q) = 0`, so
`M` lies `Hⁿ`-a.e. in the pairwise disjoint `A_p`.  On `M_p = M ∩ A_p ⊆ z + V_ι`, `TₓM_p = TₓM`
a.e., so `ξ = σ_p e_p^*` a.e. for a Borel sign `σ_p`, read off from `ξ(dx^ι)`.  Then
`u_p = (θ σ_p 1_{M_p}) ∘ Φ_p`, and `Hⁿ⌞F_p = Φ_p#(volume⌞Q₁)` transports the integrals. -/
theorem Submission.dor_lmb_fcd_fr_face_representation : ∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (E : Set (Euclid P)) (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) → IsClosed E → (∀ᵐ x ∂(μHE[m + 1].restrict E), ∃ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) = x) → IsIntegerMultiplicity Q → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) E → Q ω = 0) → ∃ u : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → ℝ, (∀ p ∈ s, ∀ y, ∃ z : ℤ, u p y = z) ∧ (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) ≤ Q.mass ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) := by
  intro P m s E Q hs hE hcov hQ hvan
  classical
  obtain ⟨R, hR⟩ := hQ
  -- `Φ_p(y) = z + Σ_j y_j e_{ι(j)}`, the open cube `Q₁ = (0, 1)ⁿ` and the closed face `F_p`
  set Φ : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  set Q₁ : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set F : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P) := fun p =>
    {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧
      (i ∉ Set.range p.2 → x i = p.1 i)}
  /- Step 1 (face geometry): `Hⁿ⌞F_p = Φ_p#(volume⌞Q₁)`, `∫_{F_p} h dHⁿ = ∫_{Q₁} h ∘ Φ_p`,
  `Φ_p(Q̄₁) ⊆ F_p`, `Φ_p` is an isometry, `F_p` is closed and bounded, and the open face
  `A_p = Φ_p(Q₁)` misses every other face `F_q`. -/
  have hF3 : ∀ p ∈ s, (μHE[m + 1] : Measure (Euclid P)).restrict (F p) =
      Measure.map (Φ p) (volume.restrict Q₁) := fun p hp =>
    (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.1
  have hF4 : ∀ p ∈ s, ∀ h : Euclid P → ℝ,
      ∫ x in F p, h x ∂μHE[m + 1] = ∫ y in Q₁, h (Φ p y) := fun p hp =>
    (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.1
  have hF5 : ∀ p ∈ s, ∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ p y ∈ F p :=
    fun p hp => (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.2.1
  have hF6 : ∀ p ∈ s, ∀ y y' : Euclid (m + 1), dist (Φ p y) (Φ p y') = dist y y' :=
    fun p hp => (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.2.2.1
  have hF7 : ∀ p ∈ s, ∀ x ∈ F p, ∀ x' ∈ F p, dist x x' ≤ Real.sqrt P :=
    fun p hp => (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.2.2.2.1
  have hF8 : ∀ p ∈ s, IsClosed (F p) :=
    fun p hp => (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.2.2.2.2.1
  have hF9 : ∀ p ∈ s, ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p →
      ∀ y ∈ Q₁, Φ p y ∉ F q :=
    fun p hp => (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.2.2.2.2.2
  have hFc : ∀ p ∈ s, IsCompact (F p) := fun p hp =>
    isCompact_of_isClosed_isBounded (hF8 p hp) (isBounded_iff.mpr ⟨_, hF7 p hp⟩)
  have hΦemb : ∀ p ∈ s, MeasurableEmbedding (Φ p) := fun p hp =>
    (Isometry.of_dist_eq (hF6 p hp)).isClosedEmbedding.measurableEmbedding
  have hQ₁m : MeasurableSet Q₁ := by
    have hQ₁' : Q₁ = ⋂ i, {y : Euclid (m + 1) | 0 < y i} ∩ {y | y i < 1} := by
      ext y
      simp only [Q₁, Set.mem_ofPred_eq, mem_iInter, mem_inter_iff]
    rw [hQ₁']
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (PiLp.continuous_apply 2 _ i).measurable).inter
        (measurableSet_lt (PiLp.continuous_apply 2 _ i).measurable measurable_const)
  have hAm : ∀ p ∈ s, MeasurableSet (Φ p '' Q₁) := fun p hp =>
    (hΦemb p hp).measurableSet_image.mpr hQ₁m
  have hAF : ∀ p ∈ s, Φ p '' Q₁ ⊆ F p := by
    rintro p hp _ ⟨y, hy, rfl⟩
    exact hF5 p hp y fun i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hAdisj : (s : Set ((Fin P → ℤ) × (Fin (m + 1) → Fin P))).PairwiseDisjoint
      fun p => Φ p '' Q₁ := by
    intro p hp q hq hpq
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ hyq
    exact hF9 p hp q (hs q hq) (Ne.symm hpq) y hy (hAF q hq hyq)
  /- Step 2: an integer multiplicity representation `R = (M, θ, ξ)` of `Q`, its measure
  `μ_R = θ Hⁿ⌞M`, and `M_W(Q) = μ_R(W)` for open `W` (C1). -/
  have hMm : MeasurableSet R.carrier := R.measurableSet_carrier
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hθm' : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hfinθ : ∀ K : Set (Euclid P), IsCompact K →
      ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[m + 1] ≠ ∞ :=
    fun K hK => R.locallyIntegrable_mult K hK (subset_univ K)
  -- `Hⁿ(M ∩ B) ≤ ∫_{M ∩ B} θ dHⁿ`, as `θ ≥ 1` on `M`
  have hHle : ∀ B : Set (Euclid P),
      μHE[m + 1] (R.carrier ∩ B) ≤ ∫⁻ x in R.carrier ∩ B, (R.mult x : ℝ≥0∞) ∂μHE[m + 1] := by
    intro B
    calc μHE[m + 1] (R.carrier ∩ B) = ∫⁻ _ in R.carrier ∩ B, (1 : ℝ≥0∞) ∂μHE[m + 1] := by
          rw [setLIntegral_one]
      _ ≤ ∫⁻ x in R.carrier ∩ B, (R.mult x : ℝ≥0∞) ∂μHE[m + 1] := by
          refine setLIntegral_mono hθm' ?_
          intro x hx
          exact_mod_cast R.mult_pos x hx.1
  have hfinM : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ → μHE[m + 1] (R.carrier ∩ K) ≠ ∞ :=
    fun K hK _ => ne_top_of_le_ne_top (hfinθ K hK) (hHle K)
  have hμR : ∀ B : Set (Euclid P), MeasurableSet B →
      R.measure B = ∫⁻ x in R.carrier ∩ B, (R.mult x : ℝ≥0∞) ∂μHE[m + 1] := by
    intro B hB
    rw [IMRep.measure, withDensity_apply _ hB, Measure.restrict_restrict hB, inter_comm]
  have hC1 := (Submission.dor_imrep_massOn_eq_measure_and_support P (m + 1) univ Q R isOpen_univ
    hR).1
  /- Step 3: `M` is carried by the open faces.  `M_{ℝᴾ∖E}(Q) = 0` since every admissible form is
  supported off `E`, so `Hⁿ(M ∖ E) = 0`; and `Hⁿ(E ∖ ⋃_p A_p) = 0` by hypothesis. -/
  have hmassEc : Q.massOn Eᶜ = 0 := by
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, ⟨hωE, -⟩, rfl⟩
    show ENNReal.ofReal (Q ω) ≤ 0
    rw [hvan ω (subset_compl_iff_disjoint_right.mp hωE), ENNReal.ofReal_zero]
  have hMEc : μHE[m + 1] (R.carrier ∩ Eᶜ) = 0 := by
    refine le_antisymm ((hHle Eᶜ).trans (le_of_eq ?_)) zero_le
    rw [← hμR Eᶜ hE.isOpen_compl.measurableSet, ← hC1 Eᶜ hE.isOpen_compl, hmassEc]
  have hEcov : μHE[m + 1] (E \ ⋃ p ∈ s, Φ p '' Q₁) = 0 := by
    have h := ae_iff.mp hcov
    rw [Measure.restrict_apply' hE.measurableSet] at h
    refine measure_mono_null ?_ h
    rintro x ⟨hxE, hxA⟩
    refine ⟨?_, hxE⟩
    rintro ⟨p, hp, y, hy, hxy⟩
    exact hxA (mem_iUnion₂.mpr ⟨p, hp, y, hy, hxy⟩)
  -- the pieces `M_p = M ∩ A_p`
  obtain ⟨Mp, hMp⟩ : ∃ Mp : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P),
      ∀ p, Mp p = R.carrier ∩ Φ p '' Q₁ := ⟨_, fun _ => rfl⟩
  have hMpm : ∀ p ∈ s, MeasurableSet (Mp p) := fun p hp => by
    rw [hMp p]
    exact hMm.inter (hAm p hp)
  have hMpM : ∀ p, Mp p ⊆ R.carrier := fun p => by
    rw [hMp p]
    exact inter_subset_left
  have hMpF : ∀ p ∈ s, Mp p ⊆ F p := fun p hp => by
    rw [hMp p]
    exact inter_subset_right.trans (hAF p hp)
  have hMpdisj : (s : Set ((Fin P → ℤ) × (Fin (m + 1) → Fin P))).PairwiseDisjoint Mp :=
    hAdisj.mono fun p => by
      rw [hMp p]
      exact inter_subset_right
  have hMae : R.carrier =ᵐ[μHE[m + 1]] ⋃ p ∈ s, Mp p := by
    refine ae_eq_set.mpr ⟨measure_mono_null ?_ (measure_union_null hMEc hEcov), ?_⟩
    · rintro x ⟨hxM, hx⟩
      by_cases hxE : x ∈ E
      · refine mem_union_right _ ⟨hxE, fun hxA => hx ?_⟩
        obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hxA
        refine mem_iUnion₂.mpr ⟨p, hp, ?_⟩
        rw [hMp p]
        exact ⟨hxM, hxp⟩
      · exact mem_union_left _ ⟨hxM, hxE⟩
    · rw [sdiff_eq_empty.mpr (iUnion₂_subset fun p _ => hMpM p)]
      exact measure_empty
  /- Steps 4–5: on `M_p`, `ξ = σ_p e_p^*` a.e. for a Borel sign `σ_p`.  The orientation `ξ(x)`
  orients `TₓM = TₓM_p` (IMC(a)); `M_p ⊆ z + V_ι`, so `ξ(x) = ±e_p^*` (plane orientation); the
  sign is read off from `ξ'(x)(dx^ι)` with `dx^ι(e_p) = 1` and `ξ'` a Borel version of `ξ`. -/
  obtain ⟨dx, hdx, -⟩ := Submission.dor_lmb_fcd_fr_coordinate_covectors P (m + 1)
  have hdxe : ∀ p ∈ s, dx p.2 (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) = 1 :=
    fun p hp => (hdx p.2 p.2 (hs p hp) (hs p hp)).trans (ite_eq_left rfl)
  obtain ⟨ξ', hξ'm, hξξ'⟩ : ∃ ξ' : Euclid P → MultiVector P (m + 1), StronglyMeasurable ξ' ∧
      R.orient =ᵐ[μHE[m + 1].restrict R.carrier] ξ' :=
    ⟨_, R.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      R.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid P → ℝ,
      ∀ p x, σ p x = if 0 ≤ ξ' x (dx p.2) then 1 else -1 := ⟨_, fun _ _ => rfl⟩
  have hσm : ∀ p, Measurable (σ p) := by
    intro p
    have hev : Measurable fun x => ξ' x (dx p.2) :=
      ((continuous_eval_const (dx p.2)).comp_stronglyMeasurable hξ'm).measurable
    rw [show σ p = fun x => if 0 ≤ ξ' x (dx p.2) then (1 : ℝ) else -1 from funext (hσ p)]
    exact Measurable.ite (measurableSet_le measurable_const hev) measurable_const measurable_const
  have hσabs : ∀ p x, |σ p x| = 1 := by
    intro p x
    rw [hσ p x]
    split_ifs <;> simp
  have hor : ∀ p ∈ s, ∀ᵐ x ∂(μHE[m + 1].restrict (Mp p)), ∀ α : Covector (Euclid P) (m + 1),
      R.orient x α = σ p x * α (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) := by
    intro p hp
    -- (b) `TₓM_p = TₓM` a.e. on `M_p` (IMC(a))
    have hIMC := Submission.cmc_imRep_locality_restrict_sub.1 P (m + 1) univ (Mp p) R.carrier
      isOpen_univ (hMpm p hp) hMm (hMpM p) (subset_univ _) hfinM
    -- (a) `ξ(x)` orients `TₓM` a.e. on `M ⊇ M_p`
    have hori : ∀ᵐ x ∂(μHE[m + 1].restrict (Mp p)), ∃ Q' : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt (m + 1) R.carrier x Q' ∧
          IsUnitOrientationOf (R.orient x) Q' :=
      ae_restrict_of_ae_restrict_of_subset (hMpM p) R.orients
    have hξ'p : ∀ᵐ x ∂(μHE[m + 1].restrict (Mp p)), R.orient x = ξ' x :=
      ae_restrict_of_ae_restrict_of_subset (hMpM p) hξξ'
    filter_upwards [hIMC, hori, hξ'p, ae_restrict_mem (hMpm p hp)] with x hxT hxo hxξ hxM
    obtain ⟨Q', hQ'M, hQ'ξ⟩ := hxo
    -- (c) `M_p ⊆ F_p` lies in the plane `x_i = z_i` (`i ∉ range ι`)
    have hcoord : ∀ a ∈ Mp p, ∀ i, (∀ j, p.2 j ≠ i) → a i = x i := by
      intro a ha i hi
      have hi' : i ∉ Set.range p.2 := by
        rintro ⟨j, hj⟩
        exact hi j hj
      have haF : ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ a i ∧ a i ≤ p.1 i + 1) ∧
          (i ∉ Set.range p.2 → a i = p.1 i) := hMpF p hp ha
      have hxF : ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧
          (i ∉ Set.range p.2 → x i = p.1 i) := hMpF p hp hxM
      rw [(haF i).2 hi', (hxF i).2 hi']
    rcases Submission.dor_lmb_fcd_fr_plane_orientation P (m + 1) p.2 (Mp p) x Q' (R.orient x)
        (hs p hp) hcoord ((hxT Q').mpr hQ'M) hQ'ξ with h | h
    · -- `ξ(x) = e_p^*`, so `ξ'(x)(dx^ι) = 1` and `σ_p(x) = 1`
      have hv : ξ' x (dx p.2) = 1 := by
        rw [← hxξ, h, hdxe p hp]
      intro α
      rw [h α, hσ p x, ite_eq_left (by rw [hv]; exact zero_le_one), one_mul]
    · -- `ξ(x) = -e_p^*`, so `ξ'(x)(dx^ι) = -1` and `σ_p(x) = -1`
      have hv : ξ' x (dx p.2) = -1 := by
        rw [← hxξ, h, hdxe p hp]
      intro α
      rw [h α, hσ p x, ite_eq_right (by rw [hv]; norm_num), neg_one_mul]
  /- Step 6: the densities `f_p = θ σ_p 1_{M_p}` on `ℝᴾ` and `u_p = f_p ∘ Φ_p` on `ℝⁿ`. -/
  obtain ⟨f, hf⟩ : ∃ f : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid P → ℝ,
      ∀ p, f p = (Mp p).indicator fun x => (R.mult x : ℝ) * σ p x := ⟨_, fun _ => rfl⟩
  have hfm : ∀ p ∈ s, Measurable (f p) := fun p hp => by
    rw [hf p]
    exact (hθm.mul (hσm p)).indicator (hMpm p hp)
  have hfabs : ∀ p x, |f p x| = (Mp p).indicator (fun x => (R.mult x : ℝ)) x := by
    intro p x
    rw [hf p]
    by_cases hx : x ∈ Mp p
    · rw [indicator_of_mem hx, indicator_of_mem hx, abs_mul, hσabs, mul_one, Nat.abs_cast]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, abs_zero]
  /- Step 7: integrability and the mass bound.  `∫_{M_p} θ dHⁿ ≤ ∫_{M ∩ F_p} θ dHⁿ < ∞`. -/
  have hlin : ∀ p ∈ s, ∫⁻ x in Mp p, (R.mult x : ℝ≥0∞) ∂μHE[m + 1] ≠ ∞ := fun p hp =>
    ne_top_of_le_ne_top (hfinθ (F p) (hFc p hp))
      (lintegral_mono_set (subset_inter (hMpM p) (hMpF p hp)))
  have hθint : ∀ p ∈ s, IntegrableOn (fun x => (R.mult x : ℝ)) (Mp p) μHE[m + 1] := by
    intro p hp
    have h := integrable_toReal_of_lintegral_ne_top hθm'.aemeasurable (hlin p hp)
    simp only [ENNReal.toReal_natCast] at h
    exact h
  have hfint : ∀ p ∈ s, IntegrableOn (f p) (F p) μHE[m + 1] := by
    intro p hp
    have hb : IntegrableOn ((Mp p).indicator fun x => (R.mult x : ℝ)) (F p) μHE[m + 1] := by
      refine (integrable_indicator_iff (hMpm p hp)).mpr ?_
      show Integrable _ ((μHE[m + 1].restrict (F p)).restrict (Mp p))
      rw [Measure.restrict_restrict (hMpm p hp), inter_eq_left.mpr (hMpF p hp)]
      exact hθint p hp
    exact hb.mono' (hfm p hp).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hfabs p x).le)
  -- `∫_{Q₁} |u_p| = ∫_{F_p} |f_p| dHⁿ = ∫_{M_p} θ dHⁿ = μ_R(A_p)`
  have hint_eq : ∀ p ∈ s, ∫ y in Q₁, |f p (Φ p y)| = (R.measure (Φ p '' Q₁)).toReal := by
    intro p hp
    calc ∫ y in Q₁, |f p (Φ p y)| = ∫ x in F p, |f p x| ∂μHE[m + 1] :=
          (hF4 p hp fun x => |f p x|).symm
      _ = ∫ x in F p, (Mp p).indicator (fun x => (R.mult x : ℝ)) x ∂μHE[m + 1] :=
          integral_congr_ae (ae_of_all _ fun x => hfabs p x)
      _ = ∫ x in Mp p, (R.mult x : ℝ) ∂μHE[m + 1] := by
          rw [setIntegral_indicator (hMpm p hp), inter_eq_right.mpr (hMpF p hp)]
      _ = (∫⁻ x in Mp p, ENNReal.ofReal (R.mult x : ℝ) ∂μHE[m + 1]).toReal :=
          integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => Nat.cast_nonneg _)
            hθm.aestronglyMeasurable
      _ = (R.measure (Φ p '' Q₁)).toReal := by
          rw [hμR _ (hAm p hp), ← hMp p]
          simp only [ENNReal.ofReal_natCast]
  have hAfin : ∀ p ∈ s, R.measure (Φ p '' Q₁) ≠ ∞ := by
    intro p hp
    refine ne_top_of_le_ne_top ?_ (measure_mono (hAF p hp))
    rw [hμR (F p) (hF8 p hp).measurableSet]
    exact hfinθ (F p) (hFc p hp)
  refine ⟨fun p y => f p (Φ p y), ?_, ?_, ?_, ?_⟩
  · -- `u_p` is integer-valued: `θ ∈ ℕ`, `σ_p ∈ {1, -1}`
    intro p _ y
    show ∃ z : ℤ, f p (Φ p y) = z
    rw [hf p]
    by_cases hy : Φ p y ∈ Mp p
    · rw [indicator_of_mem hy, hσ p]
      split_ifs
      · exact ⟨R.mult (Φ p y), by push_cast; ring⟩
      · exact ⟨-(R.mult (Φ p y) : ℤ), by push_cast; ring⟩
    · exact ⟨0, by rw [indicator_of_notMem hy, Int.cast_zero]⟩
  · -- `u_p = f_p ∘ Φ_p` is integrable on `Q₁`, since `Hⁿ⌞F_p = Φ_p#(volume⌞Q₁)`
    intro p hp
    have h1 : Integrable (f p) (Measure.map (Φ p) (volume.restrict Q₁)) := by
      rw [← hF3 p hp]
      exact hfint p hp
    exact (hΦemb p hp).integrable_map_iff.mp h1
  · -- `Σ_p ∫_{Q₁} |u_p| = Σ_p μ_R(A_p) = μ_R(⋃_p A_p) ≤ μ_R(ℝᴾ) = M(Q)`
    calc ENNReal.ofReal (∑ p ∈ s, ∫ y in Q₁, |f p (Φ p y)|)
        = ∑ p ∈ s, ENNReal.ofReal (∫ y in Q₁, |f p (Φ p y)|) :=
          ENNReal.ofReal_sum_of_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
      _ = ∑ p ∈ s, R.measure (Φ p '' Q₁) := Finset.sum_congr rfl fun p hp => by
          rw [hint_eq p hp, ENNReal.ofReal_toReal (hAfin p hp)]
      _ = R.measure (⋃ p ∈ s, Φ p '' Q₁) := (measure_biUnion_finset hAdisj hAm).symm
      _ ≤ R.measure univ := measure_mono (subset_univ _)
      _ = Q.mass := (hC1 univ isOpen_univ).symm
  · /- Step 8: `Q(ω) = ∫_M θ ξ(ω) dHⁿ = Σ_p ∫_{M_p} θ σ_p ω(e_p) dHⁿ
    = Σ_p ∫_{F_p} f_p ω(e_p) dHⁿ = Σ_p ∫_{Q₁} u_p ω(Φ_p(·))(e_p)`. -/
    intro ω
    show Q ω = ∑ p ∈ s, ∫ y in Q₁, f p (Φ p y) * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y)
      (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))
    obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
    -- `x ↦ ω(x)(e_p)` is continuous with compact support, hence bounded
    have hωe : ∀ p : (Fin P → ℤ) × (Fin (m + 1) → Fin P),
        Continuous (fun x => (ω : DifferentialForm (Euclid P) (m + 1)) x
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) ∧
        ∃ C, ∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))‖ ≤ C := by
      intro p
      have hc := hsmooth.continuous.eval_const (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))
      refine ⟨hc, hc.bounded_above_of_compact_support ?_⟩
      exact hcpt.comp_left (g := fun α : Covector (Euclid P) (m + 1) =>
        α (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) rfl
    -- the integrand `g = θ ξ(ω)` of `Q(ω)` is `θ σ_p ω(e_p)` a.e. on `M_p`
    obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℝ, ∀ x,
        g x = (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) :=
      ⟨_, fun _ => rfl⟩
    have hk : ∀ p ∈ s, g =ᵐ[μHE[m + 1].restrict (Mp p)] fun x => (R.mult x : ℝ) * σ p x *
        (ω : DifferentialForm (Euclid P) (m + 1)) x
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) := by
      intro p hp
      filter_upwards [hor p hp] with x hx
      rw [hg x, hx, mul_assoc]
    have hkint : ∀ p ∈ s, IntegrableOn (fun x => (R.mult x : ℝ) * σ p x *
        (ω : DifferentialForm (Euclid P) (m + 1)) x
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) (Mp p) μHE[m + 1] := by
      intro p hp
      have hθσ : IntegrableOn (fun x => (R.mult x : ℝ) * σ p x) (Mp p) μHE[m + 1] := by
        refine (hθint p hp).mono' (hθm.mul (hσm p)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
        rw [Real.norm_eq_abs, abs_mul, hσabs, mul_one, Nat.abs_cast]
      obtain ⟨hc, C, hC⟩ := hωe p
      exact hθσ.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hC)
    have hgint : ∀ p ∈ s, IntegrableOn g (Mp p) μHE[m + 1] := fun p hp =>
      (hkint p hp).congr (hk p hp).symm
    -- each piece transported to the cube
    have hpiece : ∀ p ∈ s, ∫ x in Mp p, g x ∂μHE[m + 1] = ∫ y in Q₁, f p (Φ p y) *
        (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y)
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) := by
      intro p hp
      have hfun : (fun x => f p x * (ω : DifferentialForm (Euclid P) (m + 1)) x
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) = fun x => (Mp p).indicator
            (fun x => (R.mult x : ℝ) * σ p x * (ω : DifferentialForm (Euclid P) (m + 1)) x
              (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) x := by
        funext x
        rw [hf p]
        exact (indicator_mul_left (Mp p) (fun x => (R.mult x : ℝ) * σ p x) fun x =>
          (ω : DifferentialForm (Euclid P) (m + 1)) x
            (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))).symm
      calc ∫ x in Mp p, g x ∂μHE[m + 1]
          = ∫ x in Mp p, (R.mult x : ℝ) * σ p x * (ω : DifferentialForm (Euclid P) (m + 1)) x
              (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1] :=
            integral_congr_ae (hk p hp)
        _ = ∫ x in F p, f p x * (ω : DifferentialForm (Euclid P) (m + 1)) x
              (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1] := by
            rw [hfun, setIntegral_indicator (hMpm p hp), inter_eq_right.mpr (hMpF p hp)]
        _ = _ := hF4 p hp _
    calc Q ω = ∫ x in R.carrier, g x ∂μHE[m + 1] := by
          rw [hR ω, IMRep.action]
          exact integral_congr_ae (ae_of_all _ fun x => (hg x).symm)
      _ = ∫ x in ⋃ p ∈ s, Mp p, g x ∂μHE[m + 1] := setIntegral_congr_set hMae
      _ = ∑ p ∈ s, ∫ x in Mp p, g x ∂μHE[m + 1] := integral_biUnion_finset s hMpm hMpdisj hgint
      _ = _ := Finset.sum_congr rfl hpiece

/-- **Divergence-form test forms near a face** (Simon Ch. 6, (28), by the arguments of 2.34–2.35).
For the face `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` and `g : ℝⁿ → ℝⁿ` smooth with compact support and
`|g| ≤ 1`, put `ω = χ Σ_l (-1)^l (g_l ∘ π) dx^{J_l}` with `J_l = ι ∘ succAbove l`, the face
coordinates `π(x)_k = x_{ι(k)} - z_{ι(k)}` and the normal cut-off `χ = η(|x - Φ_p(π x)|²)`, `η = 1`
on `[0, δ²/2]` and `η = 0` on `[δ², ∞)`.  The `dx^{J_l}` are orthonormal, so `|ω| = χ |g ∘ π| ≤ 1`;
`spt ω` lies in `{|x - Φ_p(π x)| ≤ δ} ∩ π⁻¹(spt g)`; and near the face
`ω(x)(e_{J_i}) = (-1)^i gᵢ(π x)`, so the alternating-sum formula for `d` gives
`dω(Φ_p y)(e_p) = Σᵢ ∂ᵢgᵢ(y) = trace Dg(y)`. -/
theorem Submission.dor_lmb_fcd_fr_divergence_form : ∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) (g : Euclid (m + 1) → Euclid (m + 1)) (δ : ℝ), StrictMono p.2 → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → 0 < δ → ∃ ω : TestFormOn (univ : Set (Euclid P)) m, (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ (∀ x ∈ tsupport (ω : DifferentialForm (Euclid P) m), ∃ y ∈ tsupport g, dist x (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) ≤ δ) ∧ ∀ y : Euclid (m + 1), exteriorDerivative (ω : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
  intro P m p g δ hι hg hgc hg1 hδ
  -- 1. coordinate covectors `dx^J`
  obtain ⟨dx, hdx, hdxn⟩ := Submission.dor_lmb_fcd_fr_coordinate_covectors P m
  -- 2. the frames `J l = ι ∘ succAbove l`: strictly increasing and pairwise distinct
  let J : Fin (m + 1) → Fin m → Fin P := fun l r => p.2 (l.succAbove r)
  have hJ : ∀ l, StrictMono (J l) := fun l => hι.comp (Fin.strictMono_succAbove l)
  have hJinj : Injective J := by
    intro l l' h
    apply Fin.succAbove_left_injective
    funext r
    exact hι.injective (congrFun h r)
  -- the face map `Φ` and the face coordinates `π x = πL x - πL z`, with `π ∘ Φ = id`
  let z : Euclid P := WithLp.toLp 2 (fun i => (p.1 i : ℝ))
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    z + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let πL : Euclid P →L[ℝ] Euclid (m + 1) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => EuclideanSpace.proj (p.2 k))
  have hπL : ∀ x k, πL x k = x (p.2 k) := fun x k => rfl
  have hπLe : ∀ j, πL (EuclideanSpace.single (p.2 j) (1 : ℝ)) = EuclideanSpace.single j 1 := by
    intro j
    ext k
    simp [hπL, PiLp.single_apply, hι.injective.eq_iff]
  let π : Euclid P → Euclid (m + 1) := fun x => πL x - πL z
  have hπΦ : ∀ y, π (Φ y) = y := by
    intro y
    simp only [π, Φ, map_add, add_sub_cancel_left, map_sum, map_smul, hπLe]
    ext k
    simp [Pi.single_apply]
  -- the squared normal distance `ν x = |x - Φ(π x)|²` and the cut-off `χ = η ∘ ν`
  let ν : Euclid P → ℝ := fun x => ‖x - Φ (π x)‖ ^ 2
  let χ : Euclid P → ℝ := fun x => Real.smoothTransition (2 - 2 * ν x / δ ^ 2)
  -- 3. the form `ω = Σ_l (-1)^l χ (g_l ∘ π) dx^{J l}`
  let c : Fin (m + 1) → Euclid P → ℝ := fun l x => (-1) ^ (l : ℕ) * χ x * g (π x) l
  let ω : DifferentialForm (Euclid P) m := fun x => ∑ l, c l x • dx (J l)
  have hcoord : ∀ j : Fin (m + 1), ContDiff ℝ (⊤ : ℕ∞) fun y : Euclid (m + 1) => y j :=
    fun j => (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).contDiff
  have hπ : ContDiff ℝ (⊤ : ℕ∞) π := πL.contDiff.sub contDiff_const
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ :=
    contDiff_const.add (ContDiff.sum fun j _ => (hcoord j).smul contDiff_const)
  have hν : ContDiff ℝ (⊤ : ℕ∞) ν := (contDiff_norm_sq ℝ).comp (contDiff_id.sub (hΦ.comp hπ))
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_const.mul hν).div_const _))
  have hgπ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) fun x => g (π x) l := fun l =>
    (hcoord l).comp (hg.comp hπ)
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω :=
    ContDiff.sum fun l _ => ((contDiff_const.mul hχ).mul (hgπ l)).smul contDiff_const
  -- `χ = 0` where `ν ≥ δ²` and `χ = 1` where `2ν ≤ δ²`
  have hχ0 : ∀ x, δ ^ 2 ≤ ν x → χ x = 0 := by
    intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 ≤ 2 * ν x / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hχ1 : ∀ x, 2 * ν x ≤ δ ^ 2 → χ x = 1 := by
    intro x hx
    apply Real.smoothTransition.one_of_one_le
    have : 2 * ν x / δ ^ 2 ≤ 1 := by
      rw [div_le_one₀ (by positivity)]
      exact hx
    linarith
  -- `spt ω ⊆ Z = {ν ≤ δ²} ∩ π⁻¹(spt g)`, and `|x - Φ(π x)| ≤ δ` on `Z`
  have hω0 : ∀ x, (χ x = 0 ∨ g (π x) = 0) → ω x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases hx with h | h <;> simp [c, h]
  have hsuppZ : tsupport ω ⊆ {x | ν x ≤ δ ^ 2} ∩ π ⁻¹' tsupport g := by
    refine closure_minimal (fun x hx => ⟨?_, ?_⟩)
      ((isClosed_le hν.continuous continuous_const).inter
        ((isClosed_tsupport g).preimage hπ.continuous))
    · by_contra h
      exact hx (hω0 x (Or.inl (hχ0 x (le_of_not_ge h))))
    · by_contra h
      exact hx (hω0 x (Or.inr (image_eq_zero_of_notMem_tsupport h)))
  have hZδ : ∀ x, ν x ≤ δ ^ 2 → dist x (Φ (π x)) ≤ δ := fun x hx => by
    rw [dist_eq_norm]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp hx
  -- compact support: `Z ⊆ cthickening δ (Φ(spt g))`
  have hcpt : HasCompactSupport ω :=
    ((hgc.isCompact.image hΦ.continuous).cthickening (r := δ)).of_isClosed_subset
      (isClosed_tsupport ω) (hsuppZ.trans fun x hx =>
        Metric.mem_cthickening_of_dist_le x (Φ (π x)) δ _ (mem_image_of_mem Φ hx.2)
          (hZδ x hx.1))
  refine ⟨⟨ω, ⟨hω, hcpt⟩, subset_univ _⟩, fun x => ?_, fun x hx => ?_, fun y => ?_⟩
  · -- 4. (i) `|ω(x)| = χ(x) |g(π x)| ≤ 1`
    show covectorEuclideanNorm (∑ l, c l x • dx (J l)) ≤ 1
    rw [hdxn (m + 1) J (fun l => c l x) hJinj hJ]
    refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
    calc ∑ l, c l x ^ 2 = χ x ^ 2 * ‖g (π x)‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [c]
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm (l : ℕ) 2, pow_mul, neg_one_sq, one_pow,
            one_mul]
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (Real.smoothTransition.nonneg _)
          (Real.smoothTransition.le_one _)) (pow_le_one₀ (norm_nonneg _) (hg1 _)) (sq_nonneg _)
          zero_le_one
      _ = 1 := one_mul 1
  · -- 5. (ii) `x` is within `δ` of `Φ(π x)`, `π x ∈ spt g`
    obtain ⟨hxν, hxg⟩ := hsuppZ hx
    exact ⟨π x, hxg, hZδ x hxν⟩
  · -- 6. (iii) near `Φ y`, `χ = 1`, so `ω` agrees with `ω₀ = Σ_l (-1)^l (g_l ∘ π) dx^{J l}`
    let ω₀ : DifferentialForm (Euclid P) m := fun x =>
      ∑ l : Fin (m + 1), ((-1) ^ (l : ℕ) * g (π x) l) • dx (J l)
    have hω₀ : ContDiff ℝ (⊤ : ℕ∞) ω₀ :=
      ContDiff.sum fun l _ => (contDiff_const.mul (hgπ l)).smul contDiff_const
    have hνΦ : 2 * ν (Φ y) < δ ^ 2 := by
      simp only [ν, hπΦ, sub_self, norm_zero]
      simpa using pow_pos hδ 2
    have hloc : ω =ᶠ[𝓝 (Φ y)] ω₀ := by
      filter_upwards [(isOpen_lt (continuous_const.mul hν.continuous) continuous_const).mem_nhds
        hνΦ] with x hx
      simp only [ω, ω₀, c, hχ1 x (le_of_lt hx), mul_one]
    have hd : exteriorDerivative ω (Φ y) = exteriorDerivative ω₀ (Φ y) := hloc.extDeriv_eq
    -- `ω₀(x)(e_{J i}) = (-1)^i g_i(π x)`
    have hω₀e : ∀ i : Fin (m + 1),
        (fun x => ω₀ x (i.removeNth fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) =
          fun x => (-1) ^ (i : ℕ) * g (π x) i := by
      intro i
      funext x
      show (∑ l : Fin (m + 1), ((-1) ^ (l : ℕ) * g (π x) l) • dx (J l))
          (fun r => EuclideanSpace.single (J i r) (1 : ℝ)) = _
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single i]
      · rw [ContinuousAlternatingMap.smul_apply, hdx _ _ (hJ i) (hJ i), ite_eq_left rfl,
          smul_eq_mul, mul_one]
      · intro l _ hl
        rw [ContinuousAlternatingMap.smul_apply, hdx _ _ (hJ i) (hJ l),
          ite_eq_right fun h => hl (hJinj h).symm, smul_zero]
      · exact fun h => absurd (Finset.mem_univ i) h
    -- `D[(-1)^i g_i ∘ π](Φ y)(e_{ι i}) = (-1)^i (Dg(y) ê_i)_i`
    have hderiv : ∀ i : Fin (m + 1),
        fderiv ℝ (fun x => (-1) ^ (i : ℕ) * g (π x) i) (Φ y)
          (EuclideanSpace.single (p.2 i) (1 : ℝ)) =
          (-1) ^ (i : ℕ) * fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)) i := by
      intro i
      have hπd : HasFDerivAt π πL (Φ y) := πL.hasFDerivAt.sub_const (πL z)
      have hgd : HasFDerivAt g (fderiv ℝ g y) (π (Φ y)) := by
        rw [hπΦ]
        exact (hg.differentiable (by simp) y).hasFDerivAt
      have h2 : fderiv ℝ (fun x => (-1) ^ (i : ℕ) * g (π x) i) (Φ y) =
          ((-1 : ℝ) ^ (i : ℕ)) • ((EuclideanSpace.proj i).comp ((fderiv ℝ g y).comp πL)) :=
        (((EuclideanSpace.proj i).hasFDerivAt.comp (Φ y) (hgd.comp (Φ y) hπd)).const_mul
          ((-1 : ℝ) ^ (i : ℕ))).fderiv
      rw [h2, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, hπLe, smul_eq_mul]
      rfl
    show exteriorDerivative ω (Φ y) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) = _
    rw [hd, exteriorDerivative_apply (hω₀.differentiable (by simp)).differentiableAt,
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hω₀e i, hderiv i, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul, ContinuousLinearMap.coe_coe, zsmul_eq_mul]
    push_cast
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **Boundary variation on the faces** (Simon Ch. 6, proof of 5.1, (28), second part, by the
arguments of the Constancy Theorem 2.34 and of 2.35).  Let `Q(ω) = Σ_{p∈s} ∫_{Q₁} u_p ω(Φ_p)(e_p)`
with `M(∂Q) < ∞`.  The sets `W_p = {x : dist(x, F_p) < dist(x, F_q) for q ∈ s ∖ {p}}` are
pairwise disjoint, so disjointly supported admissible forms add up to an admissible form and
`Σ_{p∈s} M_{W_p}(∂Q) ≤ M(∂Q)`; put `V_p = M_{W_p}(∂Q)`.  For an admissible `g`, the compact
`Φ_p(spt g)` has positive distance from the other faces, so the divergence form `ω` of `g` is
supported in `W_p`, and `∂Q(ω) = Q(dω) = ∫_{Q₁} u_p div g` since `dω` vanishes on the other faces;
hence `∫_{Q₁} u_p div g ≤ M_{W_p}(∂Q) = V_p`. -/
theorem Submission.dor_lmb_fcd_fr_boundary_variation : ∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (u : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → ℝ) (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) → Q.boundary.mass ≠ ∞ → ∃ V : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℝ, (∀ p ∈ s, 0 ≤ V p) ∧ ENNReal.ofReal (∑ p ∈ s, V p) ≤ Q.boundary.mass ∧ ∀ p ∈ s, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V p := by
  intro P m s u Q hs hQ hmass
  classical
  -- the parametrizations `Φ_p`, the closed faces `F_p` and the sets `W_p`
  let Φ : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let F : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P) := fun p =>
    {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧
      (i ∉ Set.range p.2 → x i = p.1 i)}
  let W : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P) := fun p =>
    {x | ∀ q ∈ s, q ≠ p → infDist x (F p) < infDist x (F q)}
  -- face geometry: `Φ_p` maps the closed cube into `F_p`, is continuous, `F_p` is closed, and
  -- `Φ_p` maps the open cube off every other face
  have hFG : ∀ p ∈ s, (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ p y ∈ F p) ∧
      Continuous (Φ p) ∧ IsClosed (F p) ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P),
        StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → Φ p y ∉ F q := by
    intro p hp
    obtain ⟨-, -, -, -, h5, h6, -, h8, h9⟩ :=
      Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)
    exact ⟨h5, (Isometry.of_dist_eq h6).continuous, h8, h9⟩
  have hFne : ∀ p ∈ s, (F p).Nonempty := fun p hp =>
    ⟨Φ p 0, (hFG p hp).1 0 fun i => by simp⟩
  -- Step 1: the `W_p`, `p ∈ s`, are pairwise disjoint
  have hWdisj : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → ∀ x, x ∈ W p → x ∉ W q := by
    intro p hp q hq hpq x hxp hxq
    exact lt_asymm (hxp q hq (Ne.symm hpq)) (hxq p hp hpq)
  -- Step 2: `Σ_{p∈s} M_{W_p}(∂Q) ≤ M(∂Q)`
  set T := Q.boundary with hT
  have hadm0 : ∀ V : Set (Euclid P),
      (0 : TestFormOn (univ : Set (Euclid P)) m) ∈ massAdmissibleOn univ m V := by
    intro V
    refine ⟨?_, fun x => ?_⟩ <;> simp
  -- (a) a family of admissible forms, one in each `W_p`
  have hfam : ∀ ω : (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W p),
      ∑ p ∈ s, ENNReal.ofReal (T (ω p)) ≤ T.mass := by
    intro ω
    -- drop the forms with negative value
    let ω' : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → TestFormOn (univ : Set (Euclid P)) m :=
      fun p => if 0 ≤ T (ω p) then (ω p : TestFormOn (univ : Set (Euclid P)) m) else 0
    have hω' : ∀ p, ENNReal.ofReal (T (ω p)) = ENNReal.ofReal (T (ω' p)) ∧ 0 ≤ T (ω' p) ∧
        ω' p ∈ massAdmissibleOn univ m (W p) := by
      intro p
      by_cases h : 0 ≤ T (ω p)
      · have h0 : ω' p = ω p := ite_eq_left h
        rw [h0]
        exact ⟨rfl, h, (ω p).2⟩
      · have h0 : ω' p = 0 := ite_eq_right h
        rw [h0, map_zero, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero]
        exact ⟨(not_le.1 h).le, le_rfl, hadm0 (W p)⟩
    -- the sum is admissible in `ℝ^P`: at each point at most one summand is nonzero
    have hsum_adm : (∑ p ∈ s, ω' p) ∈ massAdmissibleOn univ m univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      have hx : ((∑ p ∈ s, ω' p : TestFormOn (univ : Set (Euclid P)) m) :
          DifferentialForm (Euclid P) m) x =
          ∑ p ∈ s, ((ω' p : TestFormOn (univ : Set (Euclid P)) m) :
            DifferentialForm (Euclid P) m) x := by
        rw [Submodule.coe_sum, Finset.sum_apply]
      rw [hx]
      by_cases hex : ∃ p ∈ s, ((ω' p : TestFormOn (univ : Set (Euclid P)) m) :
          DifferentialForm (Euclid P) m) x ≠ 0
      · obtain ⟨p, hp, hpx⟩ := hex
        have hzero : ∀ q ∈ s, q ≠ p → ((ω' q : TestFormOn (univ : Set (Euclid P)) m) :
            DifferentialForm (Euclid P) m) x = 0 := by
          intro q hq hqp
          by_contra hqx
          exact hWdisj p hp q hq (Ne.symm hqp) x ((hω' p).2.2.1 (subset_tsupport _ hpx))
            ((hω' q).2.2.1 (subset_tsupport _ hqx))
        rw [Finset.sum_eq_single p hzero fun h => absurd hp h]
        exact (hω' p).2.2.2 x
      · have hzero : ∀ p ∈ s, ((ω' p : TestFormOn (univ : Set (Euclid P)) m) :
            DifferentialForm (Euclid P) m) x = 0 := fun p hp =>
          not_not.1 fun hpx => hex ⟨p, hp, hpx⟩
        rw [Finset.sum_eq_zero hzero, covectorEuclideanNorm_zero]
        exact zero_le_one
    calc ∑ p ∈ s, ENNReal.ofReal (T (ω p)) = ∑ p ∈ s, ENNReal.ofReal (T (ω' p)) :=
          Finset.sum_congr rfl fun p _ => (hω' p).1
      _ = ENNReal.ofReal (∑ p ∈ s, T (ω' p)) :=
          (ENNReal.ofReal_sum_of_nonneg fun p _ => (hω' p).2.1).symm
      _ = ENNReal.ofReal (T (∑ p ∈ s, ω' p)) := by rw [map_sum]
      _ ≤ T.mass := T.le_massOn hsum_adm
  -- (b) `M_{W_p}(∂Q)` as a supremum over families, which are directed
  have hsupW : ∀ p, T.massOn (W p) =
      ⨆ ω : (q : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W q),
        ENNReal.ofReal (T (ω p)) := by
    intro p
    rw [GeometricCurrentOn.massOn, sSup_image']
    refine le_antisymm (iSup_le fun ω => ?_) (iSup_le fun ω => le_iSup_of_le (ω p) le_rfl)
    let z : (q : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W q) :=
      fun q => ⟨0, hadm0 (W q)⟩
    exact le_iSup_of_le (Function.update z p ω) (by simp only [Function.update_self, le_refl])
  have hdir : ∀ i j : (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W p),
      ∃ k : (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W p), ∀ p,
        ENNReal.ofReal (T (i p)) ≤ ENNReal.ofReal (T (k p)) ∧
          ENNReal.ofReal (T (j p)) ≤ ENNReal.ofReal (T (k p)) := by
    intro i j
    refine ⟨fun p => if ENNReal.ofReal (T (i p)) ≤ ENNReal.ofReal (T (j p)) then j p else i p,
      fun p => ?_⟩
    by_cases h : ENNReal.ofReal (T (i p)) ≤ ENNReal.ofReal (T (j p))
    · simp only [ite_eq_left h]
      exact ⟨h, le_rfl⟩
    · simp only [ite_eq_right h]
      exact ⟨le_rfl, (not_le.1 h).le⟩
  have hsum : ∑ p ∈ s, T.massOn (W p) ≤ T.mass := by
    rw [Finset.sum_congr rfl fun p _ => hsupW p, ENNReal.finsetSum_iSup hdir]
    exact iSup_le hfam
  -- Step 3: `V_p = M_{W_p}(∂Q)`
  have hne : ∀ p, T.massOn (W p) ≠ ∞ := fun p =>
    ne_top_of_le_ne_top hmass (T.massOn_mono (subset_univ (W p)))
  refine ⟨fun p => (T.massOn (W p)).toReal, fun p _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [ENNReal.ofReal_sum_of_nonneg fun p _ => ENNReal.toReal_nonneg]
    calc ∑ p ∈ s, ENNReal.ofReal (T.massOn (W p)).toReal = ∑ p ∈ s, T.massOn (W p) :=
          Finset.sum_congr rfl fun p _ => ENNReal.ofReal_toReal (hne p)
      _ ≤ T.mass := hsum
  intro p hp g hg hgc hgC hg1
  -- Step 4: `Φ_p(spt g)` is compact and has positive distance from the other faces
  have hGc : IsCompact (Φ p '' tsupport g) := IsCompact.image hgc (hFG p hp).2.1
  have hBc : IsClosed (⋃ q ∈ s.erase p, F q) :=
    isClosed_biUnion_finset fun q hq => (hFG q (Finset.mem_of_mem_erase hq)).2.2.1
  have hGB : Disjoint (Φ p '' tsupport g) (⋃ q ∈ s.erase p, F q) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyB
    obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.1 hyB
    exact (hFG p hp).2.2.2 q (hs q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq) y
      (hgC hy) hyq
  obtain ⟨r, hr0, hr⟩ := exists_pos_forall_lt_edist hGc hBc hGB
  set δ : ℝ := (r : ℝ) / 3 with hδ
  have hδ0 : 0 < δ := div_pos (NNReal.coe_pos.2 hr0) three_pos
  -- Step 5: the divergence form of `g`
  obtain ⟨ω, hω1, hωspt, hωd⟩ :=
    Submission.dor_lmb_fcd_fr_divergence_form P m p g δ (hs p hp) hg hgc hg1 hδ0
  -- Step 6: `spt ω ⊆ W_p`, so `ω` is admissible for `M_{W_p}(∂Q)`
  have hωW : tsupport (ω : DifferentialForm (Euclid P) m) ⊆ W p := by
    intro x hx q hq hqp
    obtain ⟨y, hy, hxy⟩ := hωspt x hx
    have hyC : ∀ i, 0 < y i ∧ y i < 1 := hgC hy
    have hxy' : dist (Φ p y) x ≤ δ := by
      rw [dist_comm]
      exact hxy
    have h1 : infDist x (F p) ≤ δ :=
      (infDist_le_dist_of_mem ((hFG p hp).1 y fun i => ⟨(hyC i).1.le, (hyC i).2.le⟩)).trans
        (by rw [dist_comm]; exact hxy')
    have h2 : 2 * δ ≤ infDist x (F q) := by
      refine (le_infDist (hFne q hq)).2 fun b hb => ?_
      have hb' : (r : ℝ≥0∞) < edist (Φ p y) b :=
        hr _ ⟨y, hy, rfl⟩ b (Set.mem_iUnion₂.2 ⟨q, Finset.mem_erase.2 ⟨hqp, hq⟩, hb⟩)
      have hrb : (r : ℝ) < dist (Φ p y) b := by
        rw [dist_edist]
        exact ENNReal.toReal_strict_mono (edist_ne_top _ _) hb'
      have htri := dist_triangle (Φ p y) x b
      linarith
    linarith
  have hωadm : ω ∈ massAdmissibleOn univ m (W p) := ⟨hωW, hω1⟩
  -- Step 7: `∂Q(ω) = Q(dω) = ∫_{Q₁} u_p div g`, `dω` vanishing on the other faces
  have hval : T ω = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
      u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
    rw [hT, GeometricCurrentOn.boundary_apply, hQ, Finset.sum_eq_single p]
    · congr 1
      funext y
      exact congrArg (fun t => u p y * t) (hωd y)
    · intro q hq hqp
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      have hyF : Φ q y ∈ F q := (hFG q hq).1 y fun i => ⟨(hy i).1.le, (hy i).2.le⟩
      have hnot : Φ q y ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) := by
        intro hmem
        have hlt := hωW (tsupport_exteriorDerivative_subset _ hmem) q hq hqp
        rw [infDist_zero_of_mem hyF] at hlt
        exact absurd hlt (not_lt.2 infDist_nonneg)
      have h0 : exteriorDerivative (ω : DifferentialForm (Euclid P) m) (Φ q y)
          (fun k => EuclideanSpace.single (q.2 k) (1 : ℝ)) = 0 := by
        rw [image_eq_zero_of_notMem_tsupport hnot]
        rfl
      exact (congrArg (fun t => u q y * t) h0).trans (mul_zero _)
    · intro h
      exact absurd hp h
  -- Step 8: `∫_{Q₁} u_p div g = ∂Q(ω) ≤ M_{W_p}(∂Q)`
  have hle : ENNReal.ofReal (T ω) ≤ T.massOn (W p) := T.le_massOn hωadm
  rw [hval] at hle
  exact (ENNReal.ofReal_le_iff_le_toReal (hne p)).1 hle
/-- **Currents given by `L¹` densities on unit faces** (Simon Ch. 6, proof of the deformation
theorem 5.1, (29), and the mass estimate (34) via 2.35).  For pairs `p = (z, ι)` with `ι` strictly
increasing, `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` and `e_p = (e_{ι(0)}, …, e_{ι(m)})`:
(I) `y ↦ w_p(y) ω(Φ_p(y))(e_p)` is integrable on `Q₁ = (0, 1)^{m+1}`, since `ω` is continuous with
compact support and `|ω(x)(e_p)| ≤ ‖ω(x)‖`; (II) `ω ↦ Σ_p ∫_{Q₁} w_p ω(Φ_p)(e_p)` is linear and
bounded by `(Σ_p ∫_{Q₁} |w_p|) · sup ‖ω‖`, hence a current; (III) `|ω(x)(e_p)|` is bounded by the
Euclidean coefficient norm of `ω(x)`, so every such current has `M ≤ Σ_p ∫_{Q₁} |w_p|`. -/
theorem Submission.dor_lmb_fcd_fr_chain_current : ∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (w : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.2) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) ∧ ∀ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) := by
  intro P m s w hmono hw
  -- Step 1: the frame `e_ι = (e_{ι 0}, …, e_{ι m})` consists of unit vectors, so `|α(e_ι)| ≤ ‖α‖`
  have hframe : ∀ (α : Covector (Euclid P) (m + 1)) (ι : Fin (m + 1) → Fin P),
      |α (fun k => EuclideanSpace.single (ι k) (1 : ℝ))| ≤ ‖α‖ := by
    intro α ι
    simpa using α.le_opNorm (fun k => EuclideanSpace.single (ι k) (1 : ℝ))
  -- for strictly increasing `ι`, `α(e_ι)` is one of the coefficients in the Euclidean norm of `α`
  have hcoeff : ∀ (α : Covector (Euclid P) (m + 1)) (ι : Fin (m + 1) → Fin P), StrictMono ι →
      |α (fun k => EuclideanSpace.single (ι k) (1 : ℝ))| ≤ covectorEuclideanNorm α := by
    intro α ι hι
    refine Real.abs_le_sqrt ?_
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun I : Fin (m + 1) → Fin P => if StrictMono I then
        (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
      (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ ι)
    simpa [hι, EuclideanSpace.basisFun_apply] using hle
  -- Step 2: `y ↦ ω(Φ_p(y))(e_p)` is continuous, and test forms are bounded
  have hcont : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1))
      (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)),
      Continuous fun y : Euclid (m + 1) => (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))
        (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) := by
    intro ω p
    have hω : Continuous (ω : DifferentialForm (Euclid P) (m + 1)) := ω.property.1.1.continuous
    have hΦ : Continuous fun y : Euclid (m + 1) =>
        WithLp.toLp 2 (fun i => (p.1 i : ℝ)) +
          ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) := by
      fun_prop
    exact (hω.comp hΦ).eval_const _
  have hbdd : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      ∃ C, ∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ C := fun ω =>
    ω.property.1.1.continuous.bounded_above_of_compact_support ω.property.1.2
  -- (I): an integrable density times a bounded continuous function is integrable
  have hint : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s,
      IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))
        (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)))
        {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro ω p hp
    obtain ⟨C, hC⟩ := hbdd ω
    exact (hw p hp).mul_bdd (hcont ω p).aestronglyMeasurable (Filter.Eventually.of_forall fun y =>
      (Real.norm_eq_abs _).trans_le ((hframe _ _).trans (hC _)))
  -- Step 3: `|Σ_p ∫ w_p ω(Φ_p)(e_p)| ≤ c · Σ_p ∫ |w_p|` whenever `|ω(Φ_p)(e_p)| ≤ c`
  have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) (c : ℝ),
      (∀ p ∈ s, ∀ y : Euclid (m + 1), |(ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))
        (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))| ≤ c) →
      |∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y *
        (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))
        (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))| ≤
      c * ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y| := by
    intro ω c hc
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hw p hp).abs.const_mul c)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hc p hp y) (abs_nonneg _)
  -- (II): the formula is a linear functional on test forms ...
  let L : TestFormOn (univ : Set (Euclid P)) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        w p y * (ω : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))
      map_add' := fun ω η => by
        have h : ∀ x v, ((ω + η : TestFormOn (univ : Set (Euclid P)) (m + 1)) :
            DifferentialForm (Euclid P) (m + 1)) x v =
            (ω : DifferentialForm (Euclid P) (m + 1)) x v +
              (η : DifferentialForm (Euclid P) (m + 1)) x v := fun x v => rfl
        simp only [h, mul_add]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p hp => integral_add (hint ω p hp) (hint η p hp)
      map_smul' := fun c ω => by
        have h : ∀ x v, ((c • ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) :
            DifferentialForm (Euclid P) (m + 1)) x v =
            c * (ω : DifferentialForm (Euclid P) (m + 1)) x v := fun x v => rfl
        simp only [h, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← integral_const_mul]
        congr 1
        funext y
        ring }
  -- ... and it is sequentially continuous: `ωⱼ → 0` forces `sup ‖ωⱼ‖ → 0`
  have hLcont : ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) (m + 1),
      TestFormOnConverges ωs 0 → Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    intro ωs hωs
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hωs
    have h0 := Metric.tendstoUniformlyOn_iff.1 (hunif 0)
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        |w p y| := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hδ : 0 < ε / (S + 1) := div_pos hε (by linarith)
    filter_upwards [h0 _ hδ] with j hj
    have hsup : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ ε / (S + 1) := by
      intro x
      by_cases hx : x ∈ K
      · have hjx := hj x hx
        have h00 : iteratedFDeriv ℝ 0 ((0 : TestFormOn (univ : Set (Euclid P)) (m + 1)) :
            DifferentialForm (Euclid P) (m + 1)) x = 0 := by
          rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
          simp
        rw [h00, dist_zero_left, norm_iteratedFDeriv_zero] at hjx
        exact hjx.le
      · rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h), norm_zero]
        exact hδ.le
    have hb := hbound (ωs j) (ε / (S + 1)) fun p _ y => (hframe _ _).trans (hsup _)
    rw [← hS] at hb
    rw [Real.dist_eq, sub_zero]
    calc |L (ωs j)| ≤ ε / (S + 1) * S := hb
      _ < ε / (S + 1) * (S + 1) := mul_lt_mul_of_pos_left (lt_add_one S) hδ
      _ = ε := div_mul_cancel₀ ε (by linarith : (0 : ℝ) < S + 1).ne'
  refine ⟨hint, ⟨⟨L, hLcont⟩, fun ω => rfl⟩, fun D hD => ?_⟩
  -- (III): admissible forms have `|ω(Φ_p)(e_p)| ≤ 1`, so every admissible value is `≤ Σ_p ∫ |w_p|`
  unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  dsimp only
  rw [hD ω]
  refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
  have hb := hbound ω 1 fun p hp y => (hcoeff _ _ (hmono p hp)).trans (hω.2 _)
  rwa [one_mul] at hb
/-- **A set that coincides near `x` with the plane `x + V` has approximate tangent space `V` at
`x`** (Simon Ch. 3, Definition 1.4).  A test function `f ∈ C_c(ℝᴾ)` vanishes off a ball `B_R(0)`,
so `∫_S f dHⁿ = ∫_{B_R(0) ∩ S} f dHⁿ` for every `S`.  For `0 < λ < r/R` the blow-up
`η_{x,λ}(N) = λ⁻¹(N − x)` coincides with `V` inside `B_R(0)`, hence the blow-up integrals equal
`∫_V f dHⁿ` for all small `λ > 0` and converge to it. -/
theorem Submission.dor_lmb_fcd_fr_local_plane_tangent : ∀ (P n : ℕ) (N : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (r : ℝ), Module.finrank ℝ V = n → 0 < r → (∀ y ∈ Metric.ball x r, y ∈ N ↔ y - x ∈ V) → HasApproximateTangentSpaceAt n N x V := by
  intro P n N x V r hV hr hN
  refine ⟨hV, fun f => ?_⟩
  -- Step 1: `f` vanishes off a ball `B_R(0)`
  obtain ⟨R, hR, hfR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ w, w ∉ ball (0 : Euclid P) R → f w = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.hasCompactSupport.isCompact.isBounded
    refine ⟨max C 0 + 1, add_pos_of_nonneg_of_pos (le_max_right C 0) one_pos,
      fun w hw => image_eq_zero_of_notMem_tsupport fun hwt => hw ?_⟩
    rw [mem_ball_zero_iff]
    exact (hC w hwt).trans_lt ((le_max_left C 0).trans_lt (lt_add_one _))
  -- Step 2: the integral of `f` over any `S` only sees `B_R(0) ∩ S`
  have hB : MeasurableSet (ball (0 : Euclid P) R) := measurableSet_ball
  have hloc : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) R ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict hB, setIntegral_eq_integral_of_forall_compl_eq_zero hfR]
  -- Step 3: for `0 < λ < r/R` the blow-up of `N` coincides with `V` inside `B_R(0)`
  have hblow : ∀ lam ∈ Ioo 0 (r / R), ball (0 : Euclid P) R ∩
      Poincare.SimonGMT.Chapter03.blowUpMap x lam '' N =
        ball (0 : Euclid P) R ∩ (V : Set (Euclid P)) := by
    rintro lam ⟨hlam0, hlamR⟩
    have hsmall : ∀ w : Euclid P, ‖w‖ < R → ‖lam • w‖ < r := fun w hw => by
      rw [norm_smul, Real.norm_of_nonneg hlam0.le]
      exact (mul_lt_mul_of_pos_left hw hlam0).trans ((lt_div_iff₀ hR).1 hlamR)
    ext w
    constructor
    · rintro ⟨hw, y, hy, rfl⟩
      have hyx : y - x = lam • Poincare.SimonGMT.Chapter03.blowUpMap x lam y := by
        rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hlam0.ne',
          one_smul]
      have hy' : y ∈ ball x r := by
        rw [Metric.mem_ball, dist_eq_norm, hyx]
        exact hsmall _ (mem_ball_zero_iff.1 hw)
      exact ⟨hw, V.smul_mem lam⁻¹ ((hN y hy').1 hy)⟩
    · rintro ⟨hw, hwV⟩
      have hy : x + lam • w ∈ ball x r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hsmall w (mem_ball_zero_iff.1 hw)
      refine ⟨hw, x + lam • w, (hN _ hy).2 ?_, ?_⟩
      · rw [add_sub_cancel_left]
        exact V.smul_mem lam hwV
      · rw [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ hlam0.ne', one_smul]
  -- Step 4: the blow-up integrals are eventually equal to `∫_V f dHⁿ`
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr hR)] with lam hlam
  rw [hloc (V : Set (Euclid P)), hloc (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' N),
    hblow lam hlam]

/-- **Lattice chains are integer multiplicity** (Simon Ch. 6, proof of 5.1: "the fact that `P`,
`R` are integer multiplicity … should be evident").  Let `T(ω) = Σ_{p ∈ s} ∫_{Q₁} β_p
ω(Φ_p(y))(e_p) dy`, where `p = (z, ι)` has `ι` strictly increasing, `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}`,
`e_p = (e_{ι(0)}, …, e_{ι(m)})` and `Q₁ = (0, 1)ⁿ`.  Then `T = τ(N, θ, ξ)`, where `N` is the union
of the open faces `A_p = Φ_p(Q₁)` with `β_p ≠ 0`, `θ = |β_p|` and `ξ = sgn(β_p) e_p^*` on `A_p`
(`e_p^*(α) = α(e_p)`).  The face facts (`Φ_p` an isometry, `A_p ⊆ F_p` closed with `Hⁿ(F_p) = 1`,
`∫_{F_p} f dHⁿ = ∫_{Q₁} f ∘ Φ_p`, `A_p ∩ F_q = ∅` for `q ≠ p`) make the `A_p` disjoint Borel sets
of measure `≤ 1`, so `(N, θ, ξ)` is Borel, countably `n`-rectifiable and locally integrable; near
`x ∈ A_p`, `N` coincides with `x + V_p`, `V_p = span e_p` (the other faces are closed and miss
`x`), so `TₓN = V_p`, oriented by `±e_p`; and face by face its action is `T(ω)`. -/
theorem Submission.dor_lmb_fcd_fr_lattice_chain_im : ∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) → IsIntegerMultiplicity T := by
  intro P m s β T hmono hT
  classical
  -- Step 1: the face facts, in the notation `Q₁`, `Φ_p`, `F_p`, `e_p`
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q : Set (Euclid (m + 1)), Q = {y | ∀ i, 0 < y i ∧ y i < 1} := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → Euclid P,
      Φ = fun p y => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P),
      F = fun p => {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧
        x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Fin (m + 1) → Euclid P,
      e = fun p k => EuclideanSpace.single (p.2 k) (1 : ℝ) := ⟨_, rfl⟩
  have hFG := fun p (hp : p ∈ s) => Submission.dor_lmb_fcd_fr_face_geometry P m p (hmono p hp)
  have hFmeas : ∀ p ∈ s, μHE[m + 1] (F p) = 1 := fun p hp => by
    rw [hF]; exact (hFG p hp).2.1
  have hFint : ∀ p ∈ s, ∀ f : Euclid P → ℝ,
      ∫ x in F p, f x ∂μHE[m + 1] = ∫ y in Q₁, f (Φ p y) := fun p hp f => by
    rw [hF, hQ₁, hΦ]; exact (hFG p hp).2.2.2.1 f
  have hΦF : ∀ p ∈ s, ∀ y ∈ Q₁, Φ p y ∈ F p := fun p hp y hy => by
    rw [hQ₁] at hy
    rw [hF, hΦ]
    exact (hFG p hp).2.2.2.2.1 y fun i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hiso : ∀ p ∈ s, Isometry (Φ p) := fun p hp => Isometry.of_dist_eq fun y y' => by
    rw [hΦ]; exact (hFG p hp).2.2.2.2.2.1 y y'
  have hFclosed : ∀ p ∈ s, IsClosed (F p) := fun p hp => by
    rw [hF]; exact (hFG p hp).2.2.2.2.2.2.2.1
  have hΦnotF : ∀ p ∈ s, ∀ q ∈ s, q ≠ p → ∀ y ∈ Q₁, Φ p y ∉ F q :=
    fun p hp q hq hqp y hy => by
      rw [hQ₁] at hy
      rw [hF, hΦ]
      exact (hFG p hp).2.2.2.2.2.2.2.2 q (hmono q hq) hqp y hy
  have hQ₁open : IsOpen Q₁ := by
    rw [hQ₁, ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  -- the open faces `A_p = Φ_p(Q₁) ⊆ F_p`: Borel, pairwise disjoint, `Hⁿ(A_p) ≤ 1`
  obtain ⟨A, hA⟩ : ∃ A : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P),
      A = fun p => Φ p '' Q₁ := ⟨_, rfl⟩
  have hAmem : ∀ p x, x ∈ A p ↔ ∃ y ∈ Q₁, Φ p y = x := fun p x => by
    rw [hA]; exact Iff.rfl
  have hAmeas : ∀ p ∈ s, MeasurableSet (A p) := fun p hp => by
    rw [hA]
    exact (hiso p hp).isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
      hQ₁open.measurableSet
  have hAF : ∀ p ∈ s, A p ⊆ F p := fun p hp x hx => by
    obtain ⟨y, hy, rfl⟩ := (hAmem p x).mp hx
    exact hΦF p hp y hy
  have hAdisj : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (A p) (A q) := fun p hp q hq hpq => by
    refine Set.disjoint_left.mpr fun x hxp hxq => ?_
    obtain ⟨y, hy, rfl⟩ := (hAmem p x).mp hxp
    exact hΦnotF p hp q hq (Ne.symm hpq) y hy (hAF q hq hxq)
  have hAfin : ∀ p ∈ s, μHE[m + 1] (A p) ≤ 1 := fun p hp =>
    (measure_mono (hAF p hp)).trans (hFmeas p hp).le
  -- Step 2: the triple `N = ⋃_{β_p ≠ 0} A_p`, `θ = Σ_p |β_p| 1_{A_p}`,
  -- `ξ = Σ_p sgn(β_p) 1_{A_p} e_p^*`
  obtain ⟨s', hs'⟩ : ∃ s' : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P)),
      s' = s.filter fun p => β p ≠ 0 := ⟨_, rfl⟩
  have hs's : ∀ p ∈ s', p ∈ s := fun p hp => by
    rw [hs'] at hp; exact (Finset.mem_filter.mp hp).1
  have hs'β : ∀ p ∈ s', β p ≠ 0 := fun p hp => by
    rw [hs'] at hp; exact (Finset.mem_filter.mp hp).2
  obtain ⟨N, hN⟩ : ∃ N : Set (Euclid P), N = ⋃ p ∈ s', A p := ⟨_, rfl⟩
  have hNmem : ∀ x, x ∈ N ↔ ∃ p ∈ s', x ∈ A p := fun x => by
    rw [hN]; simp only [mem_iUnion, exists_prop]
  have hNmeas : MeasurableSet N := by
    rw [hN]; exact Finset.measurableSet_biUnion s' fun p hp => hAmeas p (hs's p hp)
  obtain ⟨θ, hθ⟩ : ∃ θ : Euclid P → ℕ,
      θ = fun x => ∑ p ∈ s', (A p).indicator (fun _ => (β p).natAbs) x := ⟨_, rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Euclid P → MultiVector P (m + 1),
      ξ = fun x => ∑ p ∈ s', (A p).indicator
        (fun _ => ((β p).sign : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p)) x :=
    ⟨_, rfl⟩
  -- on `A_p` (`β_p ≠ 0`), by disjointness, `θ = |β_p|` and `ξ = sgn(β_p) e_p^*`
  have hθA : ∀ p ∈ s', ∀ x ∈ A p, θ x = (β p).natAbs := fun p hp x hx => by
    rw [hθ]
    beta_reduce
    rw [Finset.sum_eq_single_of_mem p hp, indicator_of_mem hx]
    intro q hq hqp
    exact indicator_of_notMem (fun hxq => Set.disjoint_left.mp
      (hAdisj p (hs's p hp) q (hs's q hq) (Ne.symm hqp)) hx hxq) _
  have hξA : ∀ p ∈ s', ∀ x ∈ A p,
      ξ x = ((β p).sign : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p) :=
    fun p hp x hx => by
      rw [hξ]
      beta_reduce
      rw [Finset.sum_eq_single_of_mem p hp, indicator_of_mem hx]
      intro q hq hqp
      exact indicator_of_notMem (fun hxq => Set.disjoint_left.mp
        (hAdisj p (hs's p hp) q (hs's q hq) (Ne.symm hqp)) hx hxq) _
  -- Step 3: measurability, positivity, rectifiability, local integrability
  have hθmeas : Measurable θ := by
    rw [hθ]
    exact Finset.measurable_sum s' fun p hp => measurable_const.indicator (hAmeas p (hs's p hp))
  have hξmeas : StronglyMeasurable ξ := by
    -- `Λₙ(ℝᴾ)` is a topological additive group; its `ContinuousAdd` is not found by inference
    have : ContinuousAdd (MultiVector P (m + 1)) :=
      (inferInstance : IsTopologicalAddGroup (MultiVector P (m + 1))).toContinuousAdd
    rw [hξ]
    exact Finset.stronglyMeasurable_fun_sum s' fun p hp =>
      stronglyMeasurable_const.indicator (hAmeas p (hs's p hp))
  have hθpos : ∀ x ∈ N, 0 < θ x := fun x hx => by
    obtain ⟨p, hp, hxp⟩ := (hNmem x).mp hx
    rw [hθA p hp x hxp]
    exact Int.natAbs_pos.mpr (hs'β p hp)
  -- `N ⊆ ⋃_{j < |s'|} Φ_{p_j}(ℝⁿ)`, each `Φ_p` being `1`-Lipschitz
  have hrect : CountablyRectifiable (m + 1) N := by
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun j : ℕ => if h : j < s'.card then range (Φ (s'.equivFin.symm ⟨j, h⟩)) else ∅)
      fun j => ?_).mono fun x hx => ?_
    · beta_reduce
      split_ifs with h
      · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range
          (hiso _ (hs's _ (s'.equivFin.symm ⟨j, h⟩).2)).lipschitzWith
      · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
    · obtain ⟨p, hp, hxp⟩ := (hNmem x).mp hx
      obtain ⟨y, -, rfl⟩ := (hAmem p x).mp hxp
      refine mem_iUnion.mpr ⟨s'.equivFin ⟨p, hp⟩, ?_⟩
      rw [dite_eq_left (s'.equivFin ⟨p, hp⟩).2]
      simp only [Fin.eta, Equiv.symm_apply_apply]
      exact mem_range_self y
  -- `∫_{N ∩ K} θ dHⁿ ≤ Σ_p |β_p| Hⁿ(A_p) < ∞`
  have hθint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in N ∩ K, (θ x : ℝ≥0∞) ∂μHE[m + 1] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_set inter_subset_left)
    rw [hN, lintegral_biUnion_finset
      (fun p hp q hq hpq => hAdisj p (hs's p hp) q (hs's q hq) hpq)
      fun p hp => hAmeas p (hs's p hp)]
    refine ENNReal.sum_ne_top.mpr fun p hp => ?_
    rw [setLIntegral_congr_fun (g := fun _ => ((β p).natAbs : ℝ≥0∞)) (hAmeas p (hs's p hp))
      fun x hx => by rw [hθA p hp x hx], setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hAfin p (hs's p hp)))
  -- Step 4: at `x ∈ A_p`, `TₓN = V_p = span e_p`, unit-oriented by `ξ(x) = ±e_p^*`
  have horth : ∀ p ∈ s, Orthonormal ℝ (e p) := fun p hp => by
    have h : e p = (EuclideanSpace.basisFun (Fin P) ℝ) ∘ p.2 := by
      funext k
      rw [he]
      simp only [Function.comp_apply, EuclideanSpace.basisFun_apply]
    rw [h]
    exact (EuclideanSpace.basisFun (Fin P) ℝ).orthonormal.comp p.2 (hmono p hp).injective
  have hunit : ∀ p ∈ s', IsUnitOrientationOf
      (((β p).sign : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p))
      (Submodule.span ℝ (range (e p))) := fun p hp => by
    refine ⟨e p, horth p (hs's p hp), rfl, ?_⟩
    rcases lt_or_gt_of_ne (hs'β p hp) with h | h
    · refine Or.inr fun α => ?_
      rw [Int.sign_eq_neg_one_of_neg h]
      simp
    · refine Or.inl fun α => ?_
      rw [Int.sign_eq_one_of_pos h]
      simp
  have htan : ∀ p ∈ s', ∀ x ∈ A p,
      HasApproximateTangentSpaceAt (m + 1) N x (Submodule.span ℝ (range (e p))) := by
    intro p hp x hx
    have hps := hs's p hp
    obtain ⟨y₀, hy₀, rfl⟩ := (hAmem p x).mp hx
    -- `B_{r₁}(y₀) ⊆ Q₁`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hQ₁open y₀ hy₀
    -- `B_{r₂}(x)` misses the closed faces `F_q`, `q ∈ s' \ {p}`
    have hGclosed : IsClosed (⋃ q ∈ s'.erase p, F q) :=
      isClosed_biUnion_finset fun q hq => hFclosed q (hs's q (Finset.mem_of_mem_erase hq))
    have hxG : Φ p y₀ ∉ ⋃ q ∈ s'.erase p, F q := by
      simp only [mem_iUnion, exists_prop, not_exists, not_and]
      intro q hq
      exact hΦnotF p hps q (hs's q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq)
        y₀ hy₀
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hGclosed.isOpen_compl _ hxG
    refine Submission.dor_lmb_fcd_fr_local_plane_tangent P (m + 1) N (Φ p y₀) _ (min r₁ r₂)
      ?_ (lt_min hr₁ hr₂) fun y hy => ?_
    · rw [finrank_span_eq_card (horth p hps).linearIndependent, Fintype.card_fin]
    have hy₁ : dist y (Φ p y₀) < r₁ := (mem_ball.mp hy).trans_le (min_le_left _ _)
    have hy₂ : y ∉ ⋃ q ∈ s'.erase p, F q :=
      hball₂ (mem_ball.mpr ((mem_ball.mp hy).trans_le (min_le_right _ _)))
    constructor
    · -- `y ∈ N` forces `y ∈ A_p`, so `y − x = Σ_k (y₁ − y₀)_k e_{ι(k)} ∈ V_p`
      intro hyN
      obtain ⟨q, hq, hyq⟩ := (hNmem y).mp hyN
      have hqp : q = p := by
        by_contra hqp
        exact hy₂ (mem_iUnion₂.mpr ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, hAF q (hs's q hq) hyq⟩)
      rw [hqp] at hyq
      obtain ⟨y₁, -, rfl⟩ := (hAmem p y).mp hyq
      have hdiff : Φ p y₁ - Φ p y₀ = ∑ k, (y₁ k - y₀ k) • e p k := by
        rw [hΦ, he]
        simp only [sub_smul, Finset.sum_sub_distrib, add_sub_add_left_eq_sub]
      rw [hdiff]
      exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self k))
    · -- `y − x = Σ_k c_k e_{ι(k)}` with `|c| = |y − x| < r₁`, so `y = Φ_p(y₀ + c) ∈ A_p`
      intro hyV
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hyV
      have hΦc : Φ p (y₀ + WithLp.toLp 2 c) = y := by
        have h : Φ p (y₀ + WithLp.toLp 2 c) = Φ p y₀ + ∑ k, c k • e p k := by
          rw [hΦ, he]
          simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
        rw [h, hc, add_sub_cancel]
      have hc₁ : y₀ + WithLp.toLp 2 c ∈ Q₁ := by
        apply hball₁
        rw [mem_ball, ← (hiso p hps).dist_eq, hΦc]
        exact hy₁
      exact (hNmem y).mpr ⟨p, hp, (hAmem p y).mpr ⟨_, hc₁, hΦc⟩⟩
  have horients : ∀ x ∈ N, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt (m + 1) N x Q ∧ IsUnitOrientationOf (ξ x) Q := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := (hNmem x).mp hx
    exact ⟨_, htan p hp x hxp, by rw [hξA p hp x hxp]; exact hunit p hp⟩
  -- `R = (N, θ, ξ)` is an `IMRep` in `ℝ^P`
  refine ⟨⟨N, θ, ξ, hNmeas, subset_univ N, hrect, hθmeas, hθpos, hθint,
    hξmeas.aestronglyMeasurable, ae_restrict_of_forall_mem hNmeas horients⟩, fun ω => ?_⟩
  -- Step 5: `R` represents `T`, face by face
  show T ω = ∫ x in N, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]
  obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) (m + 1)) := ContDiff.continuous hsmooth
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hωc
  -- on `A_p`: `θ ⟨ω, ξ⟩ = |β_p| sgn(β_p) ω(e_p) = β_p ω(e_p)`
  have hpt : ∀ p ∈ s', ∀ x ∈ A p, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) =
      (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p) := fun p hp x hx => by
    rw [hθA p hp x hx, hξA p hp x hx, smul_apply,
      ContinuousAlternatingMap.apply_apply, smul_eq_mul, ← mul_assoc]
    congr 1
    have h : (((β p).sign * ((β p).natAbs : ℤ) : ℤ) : ℝ) = (β p : ℝ) := by
      rw [Int.sign_mul_natAbs]
    rw [Int.cast_mul, Int.cast_natCast] at h
    rw [mul_comm]
    exact h
  -- integrability on each face: `|β_p ω(x)(e_p)| ≤ |β_p| sup ‖ω‖ ∏_k ‖e_{ι(k)}‖`, `Hⁿ(A_p) ≤ 1`
  have hintA : ∀ p ∈ s', IntegrableOn
      (fun x => (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x)) (A p)
      μHE[m + 1] := by
    intro p hp
    have hps := hs's p hp
    have hcont : Continuous fun x =>
        (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p) :=
      continuous_const.mul
        ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p)).continuous.comp hωc)
    refine IntegrableOn.congr_fun ?_ (fun x hx => (hpt p hp x hx).symm) (hAmeas p hps)
    refine Measure.integrableOn_of_bounded (M := |(β p : ℝ)| * (C * ∏ k, ‖e p k‖))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hAfin p hps)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    gcongr
    exact ((((ω : DifferentialForm (Euclid P) (m + 1)) x).le_opNorm (e p)).trans
      (by gcongr; exact hC x))
  -- on each face, `∫_{A_p} β_p ω(e_p) dHⁿ = ∫_{F_p} 1_{A_p} β_p ω(e_p) dHⁿ`
  -- `= ∫_{Q₁} β_p ω(Φ_p y)(e_p) dy`
  have hface : ∀ p ∈ s', ∫ x in A p, (θ x : ℝ) *
      ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
      ∫ y in Q₁, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (e p) := by
    intro p hp
    have hps := hs's p hp
    calc ∫ x in A p, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]
        = ∫ x in A p, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p)
            ∂μHE[m + 1] := setIntegral_congr_fun (hAmeas p hps) fun x hx => hpt p hp x hx
      _ = ∫ x in F p, (A p).indicator
            (fun x => (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p)) x
            ∂μHE[m + 1] := by
          rw [integral_indicator (hAmeas p hps), Measure.restrict_restrict (hAmeas p hps),
            inter_eq_left.mpr (hAF p hps)]
      _ = ∫ y in Q₁, (A p).indicator
            (fun x => (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p)) (Φ p y) :=
          hFint p hps _
      _ = ∫ y in Q₁, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (e p) :=
          setIntegral_congr_fun hQ₁open.measurableSet fun y hy =>
            indicator_of_mem ((hAmem p _).mpr ⟨y, hy, rfl⟩) _
  -- sum over the disjoint faces; the faces with `β_p = 0` contribute nothing
  rw [hT ω, hN, integral_biUnion_finset s' (fun p hp => hAmeas p (hs's p hp))
    (fun p hp q hq hpq => hAdisj p (hs's p hp) q (hs's q hq) hpq) hintA,
    Finset.sum_congr rfl hface, hs', Finset.sum_filter_of_ne]
  · subst hQ₁ hΦ he
    rfl
  · intro p _ hp0 hβ
    exact hp0 (by simp [hβ])
/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Total variation of a smooth function by duality with smooth test fields** (parent step 5:
`∫_W |Dw|` is bounded by the supremum of `∫ Dw · g` over `C^∞` fields `g` with compact support in
`W` and `|g| ≤ 1`).  Let `F = (Dw(·) eᵢ)ᵢ` be the gradient field of `w`, so `⟪F, h⟫ = Dw · h` and
`|F| = ‖Dw‖`; `F` is `C^∞`, and bounded by `M` on the compact set `closure W`.  Given `ε > 0`, the
smooth cut-off `rsd_mw_tfa_smooth_cutoff` (for `vol⌞W`) gives `χ ∈ C_c^∞(W)` with `0 ≤ χ ≤ 1` and
`vol (W ∩ {χ ≠ 1}) < ε`.  The field `g = χ F / √(|F|² + ε²)` is admissible, and
`Dw · g = ψ := χ |F|² / √(|F|² + ε²)`, which vanishes off `W`, so `∫_W ψ ≤ V`.  On `W`,
`|F| ≤ ψ + |M| 1_{χ ≠ 1} + ε` (if `χ = 1`, use `a ≤ a² / √(a² + ε²) + ε`; otherwise `|F| ≤ M`).
Integrating, `∫_W |F| ≤ V + (|M| + vol W) ε`, and `ε → 0` gives the claim. -/
theorem Submission.dor_lmb_fcd_cp_smooth_duality : ∀ (P : ℕ) (w : Euclid P → ℝ) (W : Set (Euclid P)) (V : ℝ), IsOpen W → Bornology.IsBounded W → ContDiff ℝ (⊤ : ℕ∞) w → (∀ g : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ W → (∀ y, ‖g y‖ ≤ 1) → ∫ y, fderiv ℝ w y (g y) ≤ V) → ∫ y in W, ‖fderiv ℝ w y‖ ≤ V := by
  intro P w W V hWo hWb hw hV
  -- Step 1: the gradient field `F y = (Dw(y) eᵢ)ᵢ`, with `⟪F y, h⟫ = Dw(y) h` and `‖F y‖ = ‖Dw(y)‖`
  set F : Euclid P → Euclid P :=
    fun y => WithLp.toLp 2 (fun i => fderiv ℝ w y (EuclideanSpace.single i 1))
  have hinner : ∀ y h, inner ℝ (F y) h = fderiv ℝ w y h := by
    intro y h
    have hh : h = ∑ i, h i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hh]
    simp [F, PiLp.inner_apply, map_sum, map_smul]
  have hFc : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hD : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ w y) :=
      hw.fderiv_right (by exact_mod_cast le_top)
    have : ContDiff ℝ (⊤ : ℕ∞) (fun y => (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)).symm
        (fun i => fderiv ℝ w y (EuclideanSpace.single i 1))) := by
      apply (LinearEquiv.toContinuousLinearEquiv
        (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)).symm).contDiff.comp
      exact contDiff_pi.2 fun i => hD.clm_apply contDiff_const
    simpa [F] using this
  have hFn : ∀ y, ‖F y‖ = ‖fderiv ℝ w y‖ := by
    intro y
    have hdual : InnerProductSpace.toDual ℝ (Euclid P) (F y) = fderiv ℝ w y := by
      ext h
      simp [InnerProductSpace.toDual_apply_apply, hinner]
    rw [← hdual, LinearIsometryEquiv.norm_map]
  simp_rw [← hFn]
  -- Step 2: `vol W < ∞`, `closure W` is compact, `‖F‖ ≤ M` on `closure W`, `‖F‖` integrable on `W`
  have hWm : volume W < ∞ := hWb.measure_lt_top
  have hWc : IsCompact (closure W) := hWb.isCompact_closure
  obtain ⟨M, hM⟩ := hWc.exists_bound_of_continuousOn hFc.continuous.continuousOn
  have hFi : IntegrableOn (fun y => ‖F y‖) W :=
    (hFc.continuous.norm.continuousOn.integrableOn_compact hWc).mono_set subset_closure
  -- the scalar inequality `a ≤ a² / S + ε` for `a ≤ S ≤ a + ε`
  have alg : ∀ ε a S : ℝ, 0 < S → a ≤ S → S ≤ a + ε → a ≤ S⁻¹ * a ^ 2 + ε := by
    intro ε a S hS haS hSa
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hS]
    nlinarith [sq_nonneg (S - a), mul_nonneg hS.le (sub_nonneg.2 hSa)]
  -- Step 3: for every `ε > 0`, `∫_W ‖F‖ ≤ V + (|M| + vol W) ε`
  have key : ∀ ε : ℝ, 0 < ε → ∫ y in W, ‖F y‖ ≤ V + (|M| + volume.real W) * ε := by
    intro ε hε
    -- the smooth cut-off `χ` with compact support in `W` and `vol (W ∩ {χ ≠ 1}) < ε`
    have hfin : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.2 hWm.ne
    obtain ⟨χ, hχ, hχc, hχW, hχ01, hχm⟩ :=
      Submission.rsd_mw_tfa_smooth_cutoff P (volume.restrict W) W hfin hWo
        (by rw [Measure.restrict_apply' hWo.measurableSet, compl_inter_self, measure_empty]) ε hε
    -- the regularised length `s = √(‖F‖² + ε²)` and the test field `g = χ s⁻¹ F`
    set s : Euclid P → ℝ := fun y => √(‖F y‖ ^ 2 + ε ^ 2)
    have hspos : ∀ y, 0 < s y := by
      intro y
      show 0 < √(‖F y‖ ^ 2 + ε ^ 2)
      positivity
    have hsc : ContDiff ℝ (⊤ : ℕ∞) s :=
      ((hFc.norm_sq ℝ).add contDiff_const).sqrt fun y =>
        (by positivity : (0 : ℝ) < ‖F y‖ ^ 2 + ε ^ 2).ne'
    have hFs : ∀ y, ‖F y‖ ≤ s y := by
      intro y
      show ‖F y‖ ≤ √(‖F y‖ ^ 2 + ε ^ 2)
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg ε))
    have hsF : ∀ y, s y ≤ ‖F y‖ + ε := by
      intro y
      show √(‖F y‖ ^ 2 + ε ^ 2) ≤ ‖F y‖ + ε
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [mul_nonneg (norm_nonneg (F y)) hε.le]
    have hgc : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y • ((s y)⁻¹ • F y)) :=
      hχ.smul ((hsc.inv fun y => (hspos y).ne').smul hFc)
    have hgcs : HasCompactSupport (fun y => χ y • ((s y)⁻¹ • F y)) :=
      hχc.smul_right (f' := fun y => (s y)⁻¹ • F y)
    have hgt : tsupport (fun y => χ y • ((s y)⁻¹ • F y)) ⊆ W :=
      (tsupport_smul_subset_left χ fun y => (s y)⁻¹ • F y).trans hχW
    have hg1 : ∀ y, ‖χ y • ((s y)⁻¹ • F y)‖ ≤ 1 := by
      intro y
      have hc0 : 0 ≤ (s y)⁻¹ * ‖F y‖ := mul_nonneg (inv_nonneg.2 (hspos y).le) (norm_nonneg _)
      have hc1 : (s y)⁻¹ * ‖F y‖ ≤ 1 := by
        rw [inv_mul_le_iff₀ (hspos y), mul_one]
        exact hFs y
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (hχ01 y).1,
        Real.norm_of_nonneg (inv_nonneg.2 (hspos y).le)]
      exact (mul_le_of_le_one_left hc0 (hχ01 y).2).trans hc1
    -- `Dw(y) (g y) = ψ y := χ y s(y)⁻¹ ‖F y‖²`; `ψ` vanishes off `W`, so `∫_W ψ ≤ V`
    set ψ : Euclid P → ℝ := fun y => χ y * ((s y)⁻¹ * ‖F y‖ ^ 2)
    have hDg : ∀ y, fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) = ψ y := by
      intro y
      show fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) = χ y * ((s y)⁻¹ * ‖F y‖ ^ 2)
      rw [← hinner, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hψ0W : ∀ y ∉ W, ψ y = 0 := by
      intro y hy
      have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hχW h)
      show χ y * ((s y)⁻¹ * ‖F y‖ ^ 2) = 0
      rw [h0, zero_mul]
    have hψV : ∫ y in W, ψ y ≤ V := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hψ0W]
      calc ∫ y, ψ y = ∫ y, fderiv ℝ w y (χ y • ((s y)⁻¹ • F y)) := by simp_rw [hDg]
        _ ≤ V := hV (fun y => χ y • ((s y)⁻¹ • F y)) hgc hgcs hgt hg1
    -- pointwise on `W`: `‖F‖ ≤ ψ + |M| 1_{χ ≠ 1} + ε`
    have hEm : MeasurableSet {x | χ x ≠ 1} :=
      (isOpen_ne_fun hχ.continuous continuous_const).measurableSet
    have hpt : ∀ y ∈ W,
        ‖F y‖ ≤ ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y + ε := by
      intro y hy
      by_cases hy1 : χ y = 1
      · have hyE : y ∉ {x | χ x ≠ 1} := fun h => h hy1
        rw [indicator_of_notMem hyE, add_zero]
        show ‖F y‖ ≤ χ y * ((s y)⁻¹ * ‖F y‖ ^ 2) + ε
        rw [hy1, one_mul]
        exact alg ε _ _ (hspos y) (hFs y) (hsF y)
      · have hyE : y ∈ {x | χ x ≠ 1} := hy1
        rw [indicator_of_mem hyE]
        have hψ0 : 0 ≤ ψ y :=
          mul_nonneg (hχ01 y).1 (mul_nonneg (inv_nonneg.2 (hspos y).le) (sq_nonneg _))
        have h1 := hM y (subset_closure hy)
        have h2 := le_abs_self M
        show ‖F y‖ ≤ ψ y + |M| + ε
        linarith
    -- integrate over `W`
    have hψc : Continuous ψ :=
      hχ.continuous.mul ((hsc.continuous.inv₀ fun y => (hspos y).ne').mul
        (hFc.continuous.norm.pow 2))
    have hψi : IntegrableOn ψ W :=
      (hψc.continuousOn.integrableOn_compact hWc).mono_set subset_closure
    have hEi : IntegrableOn (Set.indicator {x | χ x ≠ 1} fun _ => |M|) W :=
      (integrableOn_const hWm.ne).indicator hEm
    have hψEi : IntegrableOn (fun y => ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y) W :=
      hψi.add hEi
    have hεi : IntegrableOn (fun _ => ε) W := integrableOn_const hWm.ne
    have hEε : (volume.restrict W).real {x | χ x ≠ 1} ≤ ε :=
      (ENNReal.toReal_lt_of_lt_ofReal hχm).le
    calc ∫ y in W, ‖F y‖
        ≤ ∫ y in W, (ψ y + Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y + ε) :=
          setIntegral_mono_on hFi (hψEi.add hεi) hWo.measurableSet hpt
      _ = (∫ y in W, ψ y) + (∫ y in W, Set.indicator {x | χ x ≠ 1} (fun _ => |M|) y) +
            ∫ y in W, ε := by
          rw [integral_add hψEi hεi, integral_add hψi hEi]
      _ = (∫ y in W, ψ y) + (volume.restrict W).real {x | χ x ≠ 1} * |M| +
            volume.real W * ε := by
          rw [integral_indicator_const _ hEm, setIntegral_const, smul_eq_mul, smul_eq_mul]
      _ ≤ V + (|M| + volume.real W) * ε := by
          nlinarith [mul_le_mul_of_nonneg_right hEε (abs_nonneg M)]
  -- Step 4: let `ε → 0`
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hL : 0 ≤ volume.real W := measureReal_nonneg
  have hpos : 0 < |M| + volume.real W + 1 := by positivity
  have h1 := key (η / (|M| + volume.real W + 1)) (div_pos hη hpos)
  have h2 : (|M| + volume.real W) * (η / (|M| + volume.real W + 1)) ≤ η := by
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    nlinarith
  linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Integer median of an integer-valued function on the open unit cube `Q₁ ⊆ ℝ^{m+1}` (Simon
Ch. 6, 5.1, (31) and (35)): some `β ∈ ℤ` has `Lⁿ(Q₁ ∩ {β ≤ u}) ≥ 1/2`, `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`
and `|β| ≤ 2 ∫_{Q₁} |u|`.  `β` is the least integer with `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`; integrality
makes `{β ≤ u}` the complement of `{u ≤ β - 1}`, and Chebyshev's inequality for `|u|` gives both
the existence of `β` and the bound. -/
theorem dor_lmb_fcd_cp_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | (β : ℝ) ≤ u y}) ∧ 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | u y ≤ (β : ℝ)}) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hZ hu
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ
  -- Step 0: `Q₁` is the preimage of the box `(0, 1)ⁿ` under the measure-preserving coordinate map,
  -- so it is measurable with `Lⁿ(Q₁) = 1`.
  have hbox : MeasurableSet (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQeq : Q = WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hQm : MeasurableSet Q := by
    rw [hQeq]
    exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable hbox
  have hQ1 : volume Q = 1 := by
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage hbox.nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp
  -- Work with the probability measure `μ = Lⁿ⌞Q₁`; `Lⁿ(Q₁ ∩ s) = μ(s)` for every set `s`.
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q with hμQ
  have hμ : ∀ s, volume (Q ∩ s) = μ s := fun s => by
    rw [hμQ, Measure.restrict_apply' hQm, inter_comm]
  have hμuniv : μ univ = 1 := by rw [← hμ, inter_univ, hQ1]
  have : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.one_lt_top⟩
  simp only [hμ]
  set I := ∫ y, |u y| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  -- Chebyshev: `ε μ({ε ≤ |u|}) ≤ ∫ |u| dμ`; no measurability of `u` is needed.
  have hmarkov : ∀ ε : ℝ, ε * μ.real {y | ε ≤ |u y|} ≤ I := fun ε =>
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
      (Integrable.abs (μ := μ) hu) ε
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
  -- Tails: for `N > 2 ∫ |u|`, `μ({N ≤ |u|}) < 1/2`.
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * I)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by linarith) hN
  have htail : μ {y | (N : ℝ) ≤ |u y|} < 1 / 2 := by
    have h1 := hmarkov N
    have h2 : μ.real {y | (N : ℝ) ≤ |u y|} < 1 / 2 := not_le.1 fun h => by nlinarith
    rw [← hhalf, measureReal_def] at h2
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by norm_num)).1 h2
  -- `μ(A) + μ(B) ≥ 1` and `μ(B) < 1/2` force `μ(A) ≥ 1/2`.
  have hcompl : ∀ a b : ℝ≥0∞, 1 ≤ a + b → b < 1 / 2 → 1 / 2 ≤ a := by
    intro a b hab hb
    refine not_lt.1 fun h => ?_
    have h' := ENNReal.add_lt_add h hb
    rw [ENNReal.add_halves] at h'
    exact absurd hab (not_le.2 h')
  -- Steps 1–2: the least integer `β` with `μ({u ≤ β}) ≥ 1/2` (Simon (31)).  It exists since
  -- `μ({u ≤ N}) ≥ 1/2` while `μ({u ≤ z}) < 1/2` for `z < -N`.
  have hS : ∃ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} := by
    refine ⟨N, hcompl _ (μ {y | u y ≤ ((N : ℤ) : ℝ)}ᶜ) (hμuniv ▸ measure_univ_le_add_compl _)
      (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail)⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, Int.cast_natCast] at hy ⊢
    exact hy.le.trans (le_abs_self _)
  have hSb : ∃ b : ℤ, ∀ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} → b ≤ z := by
    refine ⟨-N, fun z hz => not_lt.1 fun hlt => ?_⟩
    have hz' : (z : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hlt.le
    refine absurd hz (not_le.2 (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail))
    simp only [mem_ofPred_eq] at hy ⊢
    linarith [neg_abs_le (u y)]
  obtain ⟨β, hβ, hβmin⟩ := Int.exists_least_of_bdd hSb hS
  have hβ1 : μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 :=
    not_le.1 fun h => by have := hβmin (β - 1) h; omega
  -- Step 3: by integrality `{β ≤ u}ᶜ = {u ≤ β - 1}`, so `μ({β ≤ u}) ≥ 1 - μ({u ≤ β - 1}) ≥ 1/2`.
  have hup : 1 / 2 ≤ μ {y | (β : ℝ) ≤ u y} := by
    refine hcompl _ _ ?_ hβ1
    calc (1 : ℝ≥0∞) = μ univ := hμuniv.symm
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | (β : ℝ) ≤ u y}ᶜ := measure_univ_le_add_compl _
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} := by
        gcongr
        intro y hy
        simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hy ⊢
        obtain ⟨k, hk⟩ := hZ y
        rw [hk] at hy ⊢
        have hk' : k < β := by exact_mod_cast hy
        have hk'' : k ≤ β - 1 := by omega
        exact_mod_cast hk''
  refine ⟨β, hup, hβ, ?_⟩
  -- Step 4 (Simon (35)): `{|β| ≤ |u|}` contains `{β ≤ u}` (`β ≥ 0`) or `{u ≤ β}` (`β ≤ 0`), so it
  -- has measure `≥ 1/2`, and Chebyshev gives `|β| / 2 ≤ ∫ |u|`.
  have hbig : 1 / 2 ≤ μ {y | |(β : ℝ)| ≤ |u y|} := by
    rcases le_total 0 β with h0 | h0
    · refine hup.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (0 : ℝ) ≤ β := by exact_mod_cast h0
      rw [abs_of_nonneg h0']
      exact hy.trans (le_abs_self _)
    · refine hβ.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (β : ℝ) ≤ 0 := by exact_mod_cast h0
      rw [abs_of_nonpos h0']
      exact (neg_le_neg hy).trans (neg_le_abs _)
  have hbig' : 1 / 2 ≤ μ.real {y | |(β : ℝ)| ≤ |u y|} := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) hbig
    rwa [hhalf, ← measureReal_def] at h
  have h4 := hmarkov |(β : ℝ)|
  nlinarith [abs_nonneg (β : ℝ)]
/-- Deviation from a `θ`-median `β` is controlled by the double-integral oscillation (Simon Ch. 2,
Lemma 2.7, proof): `∫_W |v − β| ≤ (1 + θ⁻¹) |W|⁻¹ ∫_W ∫_W |v(x) − v(y)|`.  With the mean
`v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`; Markov's inequality on the half
`{β ≤ v}` or `{v ≤ β}` on the far side of `β` from `v̄` gives `|W| |v̄ − β| ≤ θ⁻¹ ∫_W |v − v̄|`. -/
theorem dor_lmb_fcd_cp_median_deviation : ∀ (P : ℕ) (W : Set (Euclid P)) (v : Euclid P → ℝ) (β θ : ℝ), MeasurableSet W → volume W ≠ ∞ → IntegrableOn v W → 0 < θ → θ * (volume W).toReal ≤ (volume (W ∩ {y | β ≤ v y})).toReal → θ * (volume W).toReal ≤ (volume (W ∩ {y | v y ≤ β})).toReal → ∫ y in W, |v y - β| ≤ (1 + θ⁻¹) * ((volume W).toReal)⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
  intro P W v β θ hW hWfin hv hθ hge hle
  -- `volume⌞W` is a finite measure; write `m = |W|`
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hWfin
  set m := (volume W).toReal
  -- Step 0: if `|W| = 0`, then `volume⌞W = 0` and both sides vanish
  rcases (ENNReal.toReal_nonneg : 0 ≤ m).eq_or_lt with hm | hm
  · have hW0 : volume W = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hm.symm).resolve_right hWfin
    simp [Measure.restrict_eq_zero.mpr hW0]
  -- Step 1: integrability; the partial integral is integrable by Fubini
  have hvi : Integrable v (volume.restrict W) := hv
  have hint : ∀ c : ℝ, Integrable (fun x => |v x - c|) (volume.restrict W) := fun c =>
    (hvi.sub (integrable_const c)).abs
  have hprod : Integrable (fun p : Euclid P × Euclid P => |v p.1 - v p.2|)
      ((volume.restrict W).prod (volume.restrict W)) :=
    ((hvi.comp_fst _).sub (hvi.comp_snd _)).abs
  have hG : Integrable (fun x => ∫ y in W, |v x - v y|) (volume.restrict W) :=
    hprod.integral_prod_left
  -- Step 2: with the mean `v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`
  set vbar := m⁻¹ * ∫ y in W, v y with hvbar
  have hpt : ∀ x, |v x - vbar| ≤ m⁻¹ * ∫ y in W, |v x - v y| := by
    intro x
    have h1 : ∫ y in W, (v x - v y) = m * v x - ∫ y in W, v y := by
      rw [integral_sub (integrable_const _) hvi, integral_const, measureReal_restrict_apply_univ,
        smul_eq_mul]
      rfl
    have h2 : v x - vbar = m⁻¹ * ∫ y in W, (v x - v y) := by
      rw [h1, hvbar, mul_sub, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
    rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hm)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hm.le)
  have hJ : ∫ x in W, |v x - vbar| ≤ m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
    rw [← integral_const_mul]
    exact integral_mono (hint vbar) (hG.const_mul _) hpt
  -- Step 3: `|v − v̄| ≥ |β − v̄|` on the half on the far side of `β`, which has measure `≥ θ|W|`
  set I := ∫ x in W, |v x - vbar| with hI
  have hmeas : θ * m ≤ (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} := by
    rcases le_total vbar β with hb | hb
    · refine hge.trans ?_
      rw [show (volume (W ∩ {y | β ≤ v y})).toReal = (volume.restrict W).real {y | β ≤ v y} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : β ≤ v x) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (by linarith)]
      linarith
    · refine hle.trans ?_
      rw [show (volume (W ∩ {y | v y ≤ β})).toReal = (volume.restrict W).real {y | v y ≤ β} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : v x ≤ β) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonpos (sub_nonpos.mpr hb), abs_of_nonpos (by linarith)]
      linarith
  -- Markov's inequality for `|v − v̄|` at level `|β − v̄|`
  have hM : |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} ≤ I :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hint vbar) _
  have hmed : m * |vbar - β| ≤ θ⁻¹ * I := by
    rw [abs_sub_comm, le_inv_mul_iff₀ hθ]
    calc θ * (m * |β - vbar|) = |β - vbar| * (θ * m) := by ring
      _ ≤ |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} :=
        mul_le_mul_of_nonneg_left hmeas (abs_nonneg _)
      _ ≤ I := hM
  -- Step 4: triangle inequality `|v − β| ≤ |v − v̄| + |v̄ − β|`
  have htri : ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := by
    have h3 : ∫ y in W, (|v y - vbar| + |vbar - β|) = I + m * |vbar - β| := by
      rw [integral_add (hint vbar) (integrable_const _), integral_const,
        measureReal_restrict_apply_univ, smul_eq_mul]
      rfl
    rw [← h3]
    exact integral_mono (hint β) ((hint vbar).add (integrable_const _))
      fun y => abs_sub_le (v y) vbar β
  calc ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := htri
    _ ≤ I + θ⁻¹ * I := by linarith
    _ = (1 + θ⁻¹) * I := by ring
    _ ≤ (1 + θ⁻¹) * (m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y|) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (1 + θ⁻¹) * m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by ring
/-- Fubini identity for mixed points on the cube `Q_δ = {y | ∀ i, δ < y i < 1 - δ}`: if `a_k(x, y)`
takes the coordinates `j < k` from `y` and the others from `x`, then
`∫_{Q_δ} ∫_{Q_δ} h(a_k(x, y)) dy dx = vol(Q_δ) ∫_{Q_δ} h`.  The swap `σ` exchanging `x_j` and `y_j`
for `j < k` is an involution preserving `vol ⊗ vol` (a factorwise product of swaps and identities)
and `Q_δ × Q_δ`, so Fubini on the finite measure space `Q_δ × Q_δ` turns the left side into
`∫_{Q_δ × Q_δ} h(x)`. -/
theorem dor_lmb_fcd_cp_mixed_point_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) = (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- the coordinate swap on `(Fin (m+1) → ℝ)²`
  have hτ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      ((fun j => if j < k then p.2 j else p.1 j), (fun j => if j < k then p.1 j else p.2 j)))
      (volume.prod volume) (volume.prod volume) := by
    set A := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1))
    have hA : MeasurePreserving A (Measure.pi fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
        ((volume : Measure (Fin (m + 1) → ℝ)).prod volume) :=
      measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1)) (fun _ => volume) (fun _ => volume)
    let f : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ := fun j => if j < k then Prod.swap else id
    have hf : ∀ j, MeasurePreserving (f j) ((volume : Measure ℝ).prod volume)
        ((volume : Measure ℝ).prod volume) := by
      intro j
      by_cases hj : j < k
      · simp only [f, hj, ite_true]
        exact Measure.measurePreserving_swap
      · simp only [f, hj, ite_false]
        exact MeasurePreserving.id _
    have hP := measurePreserving_pi (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
      (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume) hf
    have hcomp := (hA.comp hP).comp hA.symm
    convert hcomp using 1
    funext p
    ext j
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  -- the same swap on `Euclid (m+1) × Euclid (m+1)`
  set σ : Euclid (m + 1) × Euclid (m + 1) → Euclid (m + 1) × Euclid (m + 1) := fun p =>
    (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j),
      WithLp.toLp 2 (fun j => if j < k then p.1 j else p.2 j)) with hσdef
  have hσ : MeasurePreserving σ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (PiLp.volume_preserving_ofLp (Fin (m + 1)))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (PiLp.volume_preserving_toLp (Fin (m + 1)))
    have := (h2.comp hτ).comp h1
    convert this using 1
    funext p
    rfl
  have hσσ : ∀ p, σ (σ p) = p := by
    intro p
    ext j
    · by_cases hj : j < k <;> simp [hσdef, hj]
    · by_cases hj : j < k <;> simp [hσdef, hj]
  let σe : (Euclid (m + 1) × Euclid (m + 1)) ≃ᵐ (Euclid (m + 1) × Euclid (m + 1)) :=
    { toFun := σ
      invFun := σ
      left_inv := hσσ
      right_inv := hσσ
      measurable_toFun := hσ.measurable
      measurable_invFun := hσ.measurable }
  have hemb : MeasurableEmbedding σ := σe.measurableEmbedding
  have hpre : σ ⁻¹' (Q ×ˢ Q) = Q ×ˢ Q := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hσdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
  have hQm : MeasurableSet Q := by
    have : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y; simp [hQ]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (by fun_prop)).inter (measurableSet_lt (by fun_prop) measurable_const)
  have hσQ : MeasurePreserving σ ((volume.prod volume).restrict (Q ×ˢ Q))
      ((volume.prod volume).restrict (Q ×ˢ Q)) := by
    have := hσ.restrict_preimage_emb hemb (Q ×ˢ Q)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict Q) =
      ((volume : Measure (Euclid (m + 1))).prod volume).restrict (Q ×ˢ Q) :=
    Measure.prod_restrict Q Q
  have hQfin : volume Q ≠ ∞ := by
    have hb : Bornology.IsBounded Q := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))]
      refine ⟨Real.sqrt (((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2), fun y hy => ?_⟩
      rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (|δ| + |1 - δ|) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := hy i
            rw [Real.norm_eq_abs]
            have h1 : |y i| ≤ |δ| + |1 - δ| := by
              rw [abs_le]
              constructor <;> cases abs_cases δ <;> cases abs_cases (1 - δ) <;> linarith [this.1, this.2]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = ((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2 := by simp
    exact hb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2 hQfin
  -- integrability of `p ↦ h p.1` on `Q × Q`
  have hint1 : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => h p.1)
      ((volume.restrict Q).prod (volume.restrict Q)) := hh.comp_fst (volume.restrict Q)
  have hint2 : Integrable (fun p => h (σ p).1) ((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr] at hint1 ⊢
    exact (hσQ.integrable_comp_emb hemb).2 hint1
  -- compute
  have e1 : ∫ x in Q, ∫ y in Q, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) =
      ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr]
    exact hσQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      (volume Q).toReal * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    rw [integral_const_mul]
  rw [e1, e2, e3]
/-- Fubini along the `k`-th coordinate of the cube `Q_δ = (δ, 1 − δ)^{m+1}` (Simon Ch. 2,
proof of Lemma 2.7): for `h` integrable on `Q_δ`,
`∫_{Q_δ} ∫_δ^{1−δ} h(x[k ↦ t]) dt dx = (1 − 2δ) ∫_{Q_δ} h`.  The slice swap
`ρ(x, t) = (x[k ↦ t], x_k)` is a measure-preserving involution of `Euclid (m + 1) × ℝ` that maps
`Q_δ × (δ, 1 − δ)` onto itself. -/
theorem dor_lmb_fcd_cp_slice_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ t in Ioo δ (1 - δ), h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) = (1 - 2 * δ) * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- Step 0: if `δ ≥ 1/2` the cube is empty and both sides vanish.
  rcases le_or_gt (1 / 2) δ with hδ | hδ
  · have hQe : Q = ∅ := by
      ext y
      simp only [hQ, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, fun h0 => by linarith [h0.1, h0.2]⟩
    simp [hQe]
  -- Step 2: the slice swap on `(Fin (m + 1) → ℝ) × ℝ` preserves volume.  Under
  -- `piFinSuccAbove` it is `((a, b), c) ↦ ((c, b), a)`, a composition of swaps and
  -- reassociations.
  have hρ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × ℝ => (Function.update p.1 k p.2, p.1 k))
      (volume.prod volume) (volume.prod volume) := by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    have he : MeasurePreserving e (volume : Measure (Fin (m + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    set T : (ℝ × (Fin m → ℝ)) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ := fun q => ((q.2, q.1.2), q.1.1) with hTdef
    have hT : MeasurePreserving T (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) := by
      have s1 : MeasurePreserving (Prod.map Prod.swap id : (ℝ × (Fin m → ℝ)) × ℝ → ((Fin m → ℝ) × ℝ) × ℝ)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have s2 := measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)
      have s3 : MeasurePreserving (Prod.map id Prod.swap : (Fin m → ℝ) × (ℝ × ℝ) → (Fin m → ℝ) × (ℝ × ℝ))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume)) :=
        (MeasurePreserving.id _).prod Measure.measurePreserving_swap
      have s4 := (measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)).symm
      have s5 : MeasurePreserving (Prod.map Prod.swap id : ((Fin m → ℝ) × ℝ) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have := s5.comp (s4.comp (s3.comp (s2.comp s1)))
      convert this using 1
      funext q
      rfl
    have hE2 : MeasurePreserving (e.prodCongr (MeasurableEquiv.refl ℝ))
        ((volume : Measure (Fin (m + 1) → ℝ)).prod (volume : Measure ℝ))
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
      he.prod (MeasurePreserving.id _)
    have hfull := (hE2.symm.comp hT).comp hE2
    convert hfull using 1
    funext p
    ext j
    · simp only [Function.comp, e, T]
      simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
    · simp [e, T, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
  -- Steps 1–2: the same map `ρ` on `Euclid (m + 1) × ℝ` (via `ofLp`/`toLp`) is a
  -- measure-preserving involution, hence a measurable embedding.
  set ρ : Euclid (m + 1) × ℝ → Euclid (m + 1) × ℝ := fun p =>
    (WithLp.toLp 2 (Function.update (WithLp.ofLp p.1) k p.2), p.1 k) with hρdef
  have hρE : MeasurePreserving ρ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have := (h2.comp hρ).comp h1
    convert this using 1
    funext p
    rfl
  have hρρ : ∀ p, ρ (ρ p) = p := by
    intro p
    ext j
    · by_cases hj : j = k
      · subst hj; simp [hρdef]
      · simp [hρdef]
    · simp [hρdef]
  let ρe : (Euclid (m + 1) × ℝ) ≃ᵐ (Euclid (m + 1) × ℝ) :=
    { toFun := ρ
      invFun := ρ
      left_inv := hρρ
      right_inv := hρρ
      measurable_toFun := hρE.measurable
      measurable_invFun := hρE.measurable }
  have hemb : MeasurableEmbedding ρ := ρe.measurableEmbedding
  -- Step 3: `ρ⁻¹(Q × I) = Q × I`, so `ρ` preserves `(vol⌞Q) ⊗ (vol⌞I)`.
  set I : Set ℝ := Ioo δ (1 - δ) with hI
  have hpre : ρ ⁻¹' (Q ×ˢ I) = Q ×ˢ I := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hρdef, hI, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · simpa using h1 k
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · exact h1 k
  have hρQ : MeasurePreserving ρ ((volume.prod volume).restrict (Q ×ˢ I))
      ((volume.prod volume).restrict (Q ×ˢ I)) := by
    have := hρE.restrict_preimage_emb hemb (Q ×ˢ I)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict I) =
      ((volume : Measure (Euclid (m + 1))).prod (volume : Measure ℝ)).restrict (Q ×ˢ I) :=
    Measure.prod_restrict Q I
  -- Step 4: `(x, t) ↦ h x` and `(x, t) ↦ h (x[k ↦ t])` are integrable on `Q × I`.
  have hfinI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.2 (by simp [hI])
  have hint1 : Integrable (fun p : Euclid (m + 1) × ℝ => h p.1)
      ((volume.restrict Q).prod (volume.restrict I)) := hh.comp_fst (volume.restrict I)
  have hint2 : Integrable (fun p => h (ρ p).1) ((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr] at hint1 ⊢
    exact (hρQ.integrable_comp_emb hemb).2 hint1
  -- Step 5: Fubini, the change of variables `ρ`, and `vol(I) = 1 − 2δ`.
  have e1 : ∫ x in Q, ∫ t in I, h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) =
      ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr]
    exact hρQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      (1 - 2 * δ) * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hI, Real.volume_Ioo]
    rw [integral_const_mul, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [e1, e2, e3]
/-- One coordinate step of the Poincaré inequality on the cube `Q_δ`: the points
`a_k(x, y)`, `b_k(x, y)` differ only in the `k`-th coordinate, so by the fundamental theorem of
calculus `|v(a_k) − v(b_k)| ≤ Φ(a_k) := ∫_{(δ, 1−δ)} |∂_k v(a_k[t])| dt`.  Integrating, the
mixed-point identity gives `∫∫ Φ(a_k) = |Q_δ| ∫_{Q_δ} Φ` and the slice identity gives
`∫_{Q_δ} Φ = (1 − 2δ) ∫_{Q_δ} |∂_k v|`. -/
theorem dor_lmb_fcd_cp_coordinate_step : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ) (k : Fin (m + 1)), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) - v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤ (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |fderiv ℝ v x (EuclideanSpace.single k 1)| := by
  intro m v δ k hv _ _
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- `Q` is open, and contained in the compact cube `K = [δ, 1 − δ]^{m+1}`.
  have hQo : IsOpen Q := by
    have hQi : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y
      simp [hQ]
    rw [hQi]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  set K : Set (Euclid (m + 1)) := WithLp.toLp 2 '' Set.pi univ fun _ => Icc δ (1 - δ)
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hQK : Q ⊆ K := fun y hy => ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
  -- `∂_k v` is continuous.
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hgc : Continuous fun p : Euclid (m + 1) => |fderiv ℝ v p (EuclideanSpace.single k 1)| :=
    (hfd.clm_apply continuous_const).abs
  -- `p[t]`, the point `p` with `k`-th coordinate `t`, is `p + (t − p_k) e_k`.
  have hupd : ∀ (p : Euclid (m + 1)) (t : ℝ),
      WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t) =
        p + (t - p k) • EuclideanSpace.single k (1 : ℝ) := by
    intro p t
    ext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  -- `Φ(p) = ∫_{(δ, 1−δ)} |∂_k v(p[t])| dt` is continuous.
  set Φ : Euclid (m + 1) → ℝ := fun p => ∫ t in Ioo δ (1 - δ),
    |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t)) (EuclideanSpace.single k 1)|
    with hΦ
  have hΦc : Continuous Φ := by
    have hGc : Continuous fun z : Euclid (m + 1) × ℝ =>
        |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp z.1) k z.2))
          (EuclideanSpace.single k 1)| := by
      simp_rw [hupd]
      exact hgc.comp (by fun_prop)
    have hΦ' : Φ = fun p => ∫ t in Icc δ (1 - δ),
        |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t))
          (EuclideanSpace.single k 1)| := by
      funext p
      exact integral_Icc_eq_integral_Ioo.symm
    rw [hΦ']
    exact continuous_parametric_integral_of_continuous
      (f := fun p t => |fderiv ℝ v (WithLp.toLp 2 (Function.update (WithLp.ofLp p) k t))
        (EuclideanSpace.single k 1)|) hGc isCompact_Icc
  -- `(x, y) ↦ Φ(a_k(x, y))` is continuous.
  have hac : Continuous fun z : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j) : Euclid (m + 1)) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => by fun_prop) (fun _ => by fun_prop)
  have hFc : Continuous fun z : Euclid (m + 1) × Euclid (m + 1) =>
      Φ (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j)) := hΦc.comp hac
  -- Integrability: continuous functions are integrable on the compact `K ⊇ Q`.
  have hI1 : IntegrableOn (fun p => |fderiv ℝ v p (EuclideanSpace.single k 1)|) Q :=
    (hgc.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hI2 : IntegrableOn Φ Q := (hΦc.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hI3 : ∀ x : Euclid (m + 1), IntegrableOn
      (fun y : Euclid (m + 1) => Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j))) Q :=
    fun x => ((hFc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      hKc).mono_set hQK
  have hI4 : IntegrableOn (fun x : Euclid (m + 1) =>
      ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j))) Q := by
    have hprod : Integrable (fun z : Euclid (m + 1) × Euclid (m + 1) =>
        Φ (WithLp.toLp 2 (fun j => if j < k then z.2 j else z.1 j)))
        ((volume.restrict Q).prod (volume.restrict Q)) := by
      rw [Measure.prod_restrict]
      exact (hFc.continuousOn.integrableOn_compact (hKc.prod hKc)).mono_set (prod_mono hQK hQK)
    exact hprod.integral_prod_left
  -- Step 1: the fundamental theorem of calculus along `t ↦ a_k[t]`.
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q,
      |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤
        Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := by
    intro x hx y hy
    set a : Euclid (m + 1) := WithLp.toLp 2 (fun j => if j < k then y j else x j) with ha
    set ℓ : ℝ → Euclid (m + 1) := fun t => a + (t - a k) • EuclideanSpace.single k (1 : ℝ)
      with hℓ
    have hak : a k = x k := by simp [ha]
    have hℓx : ℓ (x k) = a := by simp [hℓ, hak]
    have hℓy : ℓ (y k) = WithLp.toLp 2 (fun j => if j ≤ k then y j else x j) := by
      ext j
      rcases lt_trichotomy j k with h | h | h
      · simp [hℓ, ha, h, le_of_lt h, ne_of_lt h]
      · subst h
        simp [hℓ, ha]
      · simp [hℓ, ha, not_lt.2 (le_of_lt h), not_le.2 h, (ne_of_lt h).symm]
    have hℓd : ∀ t, HasDerivAt ℓ (EuclideanSpace.single k (1 : ℝ)) t := by
      intro t
      have := (((hasDerivAt_id' t).sub_const (a k)).smul_const
        (EuclideanSpace.single k (1 : ℝ))).const_add a
      rw [one_smul] at this
      exact this
    have hderiv : ∀ t, HasDerivAt (fun t => v (ℓ t))
        (fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)) t := fun t =>
      ((hv.differentiable one_ne_zero (ℓ t)).hasFDerivAt).comp_hasDerivAt t (hℓd t)
    have hcont : Continuous fun t => fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1) :=
      (hfd.comp (by fun_prop)).clm_apply continuous_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable (x k) (y k))
    simp only [hℓx, hℓy] at hftc
    have hsub : Set.uIoc (x k) (y k) ⊆ Ioo δ (1 - δ) := by
      intro t ht
      rcases Set.mem_uIoc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [(hx k).1], by linarith [(hy k).2]⟩
      · exact ⟨by linarith [(hy k).1], by linarith [(hx k).2]⟩
    rw [abs_sub_comm, ← hftc]
    calc |∫ t in x k..y k, fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)|
        = ‖∫ t in x k..y k, fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ (t : ℝ) in Set.uIoc (x k) (y k), ‖fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ (t : ℝ) in Ioo δ (1 - δ), ‖fderiv ℝ v (ℓ t) (EuclideanSpace.single k 1)‖ :=
          setIntegral_mono_set
            (hcont.norm.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
            (Eventually.of_forall fun t => norm_nonneg _) hsub.eventuallyLE
      _ = Φ a := by
          simp only [hΦ, hℓ, ← hupd, Real.norm_eq_abs]
  -- Step 3: integrate the pointwise bound.
  have hstep : ∫ x in Q, ∫ y in Q, |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| ≤
      ∫ x in Q, ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun x => integral_nonneg fun y => abs_nonneg _) hI4 ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hI3 x) ?_
    filter_upwards [ae_restrict_mem hQm] with y hy
    exact hpt x hx y hy
  -- Steps 4–6: the mixed-point and slice identities.
  calc _ ≤ ∫ x in Q, ∫ y in Q, Φ (WithLp.toLp 2 (fun j => if j < k then y j else x j)) := hstep
    _ = (volume Q).toReal * ∫ x in Q, Φ x :=
        Submission.dor_lmb_fcd_cp_mixed_point_integral m δ k Φ hI2
    _ = (volume Q).toReal *
        ((1 - 2 * δ) * ∫ x in Q, |fderiv ℝ v x (EuclideanSpace.single k 1)|) := by
        congr 1
        exact Submission.dor_lmb_fcd_cp_slice_integral m δ k
          (fun p => |fderiv ℝ v p (EuclideanSpace.single k 1)|) hI1
    _ = _ := by ring
/-- **Poincaré inequality on the cube `Q_δ = (δ, 1 − δ)^{m+1}` for `C¹` functions** (the "usual
Poincaré inequality for smooth functions" invoked in Simon Ch. 2, proof of Lemma 2.7, here on a
cube of side `1 − 2δ`):
`∫_Q ∫_Q |v(x) − v(y)| dy dx ≤ (m + 1)(1 − 2δ) Lⁿ(Q) ∫_Q ‖Dv‖`.  Along the coordinate path from
`x` to `y`, `v x − v y` telescopes into the `m + 1` coordinate steps bounded by
`dor_lmb_fcd_cp_coordinate_step`; every integrand is continuous on the compact cube
`[δ, 1 − δ]^{m+1} ⊇ Q`, hence integrable, and `|Dv(x) eₖ| ≤ ‖Dv(x)‖`. -/
theorem dor_lmb_fcd_cp_smooth_poincare : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → δ < 1 / 2 → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |v x - v y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v δ hv hδ0 hδ
  -- Step 1: telescoping along the coordinate path `W₀ = x, …, W_{m+1} = y`
  have htel : ∀ x y : Euclid (m + 1), v x - v y = ∑ k : Fin (m + 1),
      (v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))) := by
    intro x y
    set W : ℕ → Euclid (m + 1) :=
      fun n => WithLp.toLp 2 (fun j => if (j : ℕ) < n then y j else x j) with hW
    have h0 : W 0 = x := by
      simp [hW]
    have hN : W (m + 1) = y := by
      have hlt : ∀ j : Fin (m + 1), (j : ℕ) < m + 1 := fun j => j.is_lt
      simp only [hW, hlt, ite_true]
    have hk : ∀ k : Fin (m + 1),
        v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
          v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j)) = v (W k) - v (W (k + 1)) := by
      intro k
      have e1 : (fun j : Fin (m + 1) => if j < k then y j else x j) =
          (fun j : Fin (m + 1) => if (j : ℕ) < (k : ℕ) then y j else x j) := by
        funext j
        simp only [Fin.lt_def]
      have e2 : (fun j : Fin (m + 1) => if j ≤ k then y j else x j) =
          (fun j : Fin (m + 1) => if (j : ℕ) < (k : ℕ) + 1 then y j else x j) := by
        funext j
        simp only [Fin.le_iff_val_le_val, Nat.lt_succ_iff]
      rw [e1, e2]
    rw [Finset.sum_congr rfl (fun k _ => hk k),
      Fin.sum_univ_eq_sum_range (fun n => v (W n) - v (W (n + 1))) (m + 1),
      Finset.sum_range_sub', h0, hN]
  have habs : ∀ x y : Euclid (m + 1), |v x - v y| ≤ ∑ k : Fin (m + 1),
      |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| := by
    intro x y
    rw [htel x y]
    exact Finset.abs_sum_le_sum_abs _ _
  -- Step 2: integrability; `Q_δ` lies in the compact cube `K = [δ, 1 − δ]^{m+1}`
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  set K : Set (Euclid (m + 1)) := {y | ∀ i, δ ≤ y i ∧ y i ≤ 1 - δ}
  have hQK : Q ⊆ K := fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hKc : IsCompact K := by
    have hKeq : K = WithLp.toLp 2 '' Set.pi univ (fun _ : Fin (m + 1) => Icc δ (1 - δ)) := by
      ext y
      constructor
      · intro hy
        exact ⟨WithLp.ofLp y, fun i _ => hy i, rfl⟩
      · rintro ⟨z, hz, rfl⟩ i
        exact hz i (mem_univ i)
    rw [hKeq]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hint : ∀ g : Euclid (m + 1) → ℝ, Continuous g → IntegrableOn g Q :=
    fun g hg => (hg.continuousOn.integrableOn_compact hKc).mono_set hQK
  have hint2 : ∀ F : Euclid (m + 1) × Euclid (m + 1) → ℝ, Continuous F →
      Integrable F ((volume.restrict Q).prod (volume.restrict Q)) := by
    intro F hF
    rw [Measure.prod_restrict]
    exact (hF.continuousOn.integrableOn_compact (hKc.prod hKc)).mono_set (prod_mono hQK hQK)
  -- the coordinate points depend continuously on `(x, y)`
  have hlt : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j) : Euclid (m + 1)) := by
    intro k
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_snd)
      fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have hle : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      (WithLp.toLp 2 (fun j => if j ≤ k then p.2 j else p.1 j) : Euclid (m + 1)) := by
    intro k
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    exact continuous_if_const _ (fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_snd)
      fun _ => (PiLp.continuous_apply 2 _ j).comp continuous_fst
  have hF0 : Continuous fun p : Euclid (m + 1) × Euclid (m + 1) => |v p.1 - v p.2| :=
    ((hv.continuous.comp continuous_fst).sub (hv.continuous.comp continuous_snd)).abs
  have hFk : ∀ k : Fin (m + 1), Continuous fun p : Euclid (m + 1) × Euclid (m + 1) =>
      |v (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j)) -
        v (WithLp.toLp 2 (fun j => if j ≤ k then p.2 j else p.1 j))| :=
    fun k => ((hv.continuous.comp (hlt k)).sub (hv.continuous.comp (hle k))).abs
  have hfac : 0 ≤ (1 - 2 * δ) * (volume Q).toReal :=
    mul_nonneg (by linarith) ENNReal.toReal_nonneg
  -- Steps 3–4: integrate the telescoping bound, apply `coordinate_step`, and `|Dv eₖ| ≤ ‖Dv‖`
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      ≤ ∫ x in Q, ∑ k : Fin (m + 1), ∫ y in Q,
          |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
            v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| := by
        refine integral_mono (hint2 _ hF0).integral_prod_left
          (integrable_finsetSum _ fun k _ => (hint2 _ (hFk k)).integral_prod_left) fun x => ?_
        have hx : ∀ k : Fin (m + 1), IntegrableOn (fun y : Euclid (m + 1) =>
            |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
              v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))|) Q :=
          fun k => hint _ ((hFk k).comp (Continuous.prodMk_right x))
        exact (integral_mono (hint _ (hF0.comp (Continuous.prodMk_right x)))
          (integrable_finsetSum _ fun k _ => hx k) (habs x)).trans_eq
          (integral_finsetSum _ fun k _ => hx k)
    _ = ∑ k : Fin (m + 1), ∫ x in Q, ∫ y in Q,
          |v (WithLp.toLp 2 (fun j => if j < k then y j else x j)) -
            v (WithLp.toLp 2 (fun j => if j ≤ k then y j else x j))| :=
        integral_finsetSum _ fun k _ => (hint2 _ (hFk k)).integral_prod_left
    _ ≤ ∑ k : Fin (m + 1), (1 - 2 * δ) * (volume Q).toReal *
          ∫ x in Q, |fderiv ℝ v x (EuclideanSpace.single k 1)| :=
        Finset.sum_le_sum fun k _ => Submission.dor_lmb_fcd_cp_coordinate_step m v δ k hv hδ0 hδ
    _ ≤ ∑ _k : Fin (m + 1), (1 - 2 * δ) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ hfac
        have hDv : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
        refine integral_mono (hint _ (hDv.clm_apply continuous_const).abs) (hint _ hDv.norm)
          fun x => ?_
        calc |fderiv ℝ v x (EuclideanSpace.single k 1)|
            = ‖fderiv ℝ v x (EuclideanSpace.single k 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ v x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ := (fderiv ℝ v x).le_opNorm _
          _ = ‖fderiv ℝ v x‖ := by simp
    _ = ((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
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

/-- Simon Ch. 2, Lemma 2.5 on the cube `Q₁ = (0, 1)^{m+1}`: if `∫_{Q₁} u div g ≤ V` for every
smooth `g` with compact support in `Q₁` and `|g| ≤ 1`, then `u_η = η * 1_{Q₁} u` is smooth and
`∫_{Q_δ} |Du_η| ≤ V` whenever `spt η ⊆ B_δ(0)`.  For `g` with compact support in `Q_δ`, the
mollified field `G = η * g` is admissible, and `∫ Du_η · g = −∫_{Q₁} u div G = ∫_{Q₁} u div(−G)`. -/
theorem dor_lmb_fcd_cp_mollified_variation : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → (∀ z, 0 ≤ η z) → (∀ z, η (-z) = η z) → ∫ z, η z = 1 → support η ⊆ ball (0 : Euclid (m + 1)) δ → ContDiff ℝ (⊤ : ℕ∞) (convolution η (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ‖fderiv ℝ (convolution η (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ V := by
  intro m u V δ η hu hH hδ hη hηc hη0 heven hη1 hηs
  -- Step 0: `{y : a < yᵢ < b for all i}` is open, a finite intersection of open slabs.
  have hopen : ∀ a b : ℝ, IsOpen {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hQ₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    (hopen 0 1).measurableSet
  have hũ : Integrable ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) :=
    hu.integrable_indicator hQ₁
  -- Step 1: `1_{Q₁} u` is integrable, so `u_η` is smooth.
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (convolution η
      ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_left _ hη hũ.locallyIntegrable
  -- Step 2: `Q_δ` is open and bounded: it lies in the closed ball of radius `√(m + 1)`.
  have hbdd : Bornology.IsBounded {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} := by
    refine (isBounded_closedBall (x := (0 : Euclid (m + 1))) (r := √((m : ℝ) + 1))).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h0 : 0 < y i := by linarith [(hy i).1]
          have h1 : y i < 1 := by linarith [(hy i).2]
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = (m : ℝ) + 1 := by simp
  -- Step 3: by `smooth_duality` it suffices to bound `∫ Du_η · g` for admissible `g` in `Q_δ`.
  refine ⟨hsmooth, Submission.dor_lmb_fcd_cp_smooth_duality (m + 1) _ _ V (hopen δ (1 - δ)) hbdd
    hsmooth fun g hg hgc hgs hg1 => ?_⟩
  -- Step 4: `G = η * g` is smooth, compactly supported in `Q₁`, and `|G| ≤ 1`.
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.contDiff_convolution_left _ hη hg.continuous.locallyIntegrable
  have hGc : HasCompactSupport (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hηc.convolution _ hgc
  have hGs : tsupport (convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    -- `spt G ⊆ spt η + spt g ⊆ B̄_δ(0) + Q_δ ⊆ Q₁`, the middle set being compact.
    refine (closure_minimal ((support_convolution_subset (μ := volume)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1))).trans
      (add_subset_add (subset_tsupport η) (subset_tsupport g)))
      (hηc.isCompact.add hgc.isCompact).isClosed).trans ?_
    rintro _ ⟨z, hz, q, hq, rfl⟩ i
    have hz' : ‖z‖ ≤ δ :=
      mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall (closure_mono hηs hz))
    have hzi : |z i| ≤ δ := by
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le z i).trans hz'
    have hqi := hgs hq i
    rw [PiLp.add_apply]
    constructor <;> linarith [(abs_le.mp hzi).1, (abs_le.mp hzi).2, hqi.1, hqi.2]
  have hG1 : ∀ x, ‖convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ ≤ 1 := by
    intro x
    rw [convolution_def]
    calc ‖∫ t, ContinuousLinearMap.lsmul ℝ ℝ (η t) (g (x - t))‖ ≤ ∫ t, η t :=
          norm_integral_le_of_norm_le (hη.continuous.integrable_of_hasCompactSupport hηc)
            (Eventually.of_forall fun t => by
              rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (hη0 t)]
              exact mul_le_of_le_one_right (hη0 t) (hg1 _))
      _ = 1 := hη1
  -- Step 5: `mollifier_adjoint` gives `∫ Du_η · g = −∫ 1_{Q₁} u div G`.
  have hadj := codim1_rdo_dg_sp_mollifier_adjoint (m + 1) η
    ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) g
    (hη.of_le (by exact_mod_cast le_top)) hηc heven hũ
    (hg.continuous.integrable_of_hasCompactSupport hgc)
  -- Step 6: (H) for `−G` reads `−∫_{Q₁} u div G ≤ V`, since `div(−G) = −div G`.
  have hneg := hH (-convolution η g (ContinuousLinearMap.lsmul ℝ ℝ) volume) hGsmooth.neg hGc.neg
    (by rwa [tsupport_neg]) fun y => by rw [Pi.neg_apply, norm_neg]; exact hG1 y
  simp only [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg, mul_neg,
    integral_neg] at hneg
  rw [← integral_indicator hQ₁] at hneg
  simp_rw [indicator_mul_left] at hneg
  rw [hadj]
  exact hneg
/-- BV Poincaré inequality on the cube `Q_δ = (δ, 1 − δ)^{m+1}` in double-integral form (cf. the
proof of Simon Ch. 2, Lemma 2.7): if `∫_{Q₁} u div g ≤ V` for all smooth `g` with compact support
in `Q₁ = (0, 1)^{m+1}` and `|g| ≤ 1`, then `∫_{Q_δ} ∫_{Q_δ} |u(x) − u(y)| ≤ (m + 1)(1 − 2δ)|Q_δ| V`.
The mollifications `v_k = η_k ∗ 1_{Q₁}u` satisfy this bound by the smooth inequality, and
`v_k → u` a.e. on `Q_δ`, so Fatou's lemma on `Q_δ × Q_δ` passes it to `u`. -/
theorem dor_lmb_fcd_cp_bv_poincare : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ) (η : ℕ → Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → δ < 1 / 2 → (∀ k, ContDiff ℝ (⊤ : ℕ∞) (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ k, support (η k) ⊆ ball (0 : Euclid (m + 1)) δ) → (∀ᵐ x ∂volume, Tendsto (fun k => (convolution (η k) (Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) atTop (𝓝 ((Set.indicator {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} u) x))) → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |u x - u y| ≤ ((m : ℝ) + 1) * (1 - 2 * δ) * (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * V := by
  intro m u V δ η hu hH hδ hδ2 hη hηc hη0 hηe hη1 hηs hlim
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  set C : ℝ := ((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal
  set v : ℕ → Euclid (m + 1) → ℝ := fun k =>
    convolution (η k) (Q₁.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- Step 1: each `v k` is smooth with `∫_Q ‖D v_k‖ ≤ V` (sibling `mollified_variation`).
  have hmv : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k) ∧ ∫ x in Q, ‖fderiv ℝ (v k) x‖ ≤ V := fun k =>
    Submission.dor_lmb_fcd_cp_mollified_variation m u V δ (η k) hu hH hδ (hη k) (hηc k)
      (hη0 k) (hηe k) (hη1 k) (hηs k)
  have hV : 0 ≤ V := (integral_nonneg fun x => norm_nonneg _).trans (hmv 0).2
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 1 - 2 * δ := by linarith
    positivity
  -- Step 2: the smooth Poincaré inequality for `v k` (sibling `smooth_poincare`).
  have hD : ∀ k, ∫ x in Q, ∫ y in Q, |v k x - v k y| ≤ C * V := fun k =>
    (Submission.dor_lmb_fcd_cp_smooth_poincare m (v k) δ
      ((hmv k).1.of_le (by exact_mod_cast le_top)) hδ.le hδ2).trans
      (mul_le_mul_of_nonneg_left (hmv k).2 hC0)
  -- `Q` is a measurable subset of `Q₁` contained in a compact ball.
  have hQQ₁ : Q ⊆ Q₁ := fun y hy i => ⟨hδ.trans (hy i).1, (hy i).2.trans (by linarith)⟩
  have hQm : MeasurableSet Q := by
    have hc : ∀ i : Fin (m + 1), Measurable fun y : Euclid (m + 1) => y i := fun i => by fun_prop
    have hQi : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y
      rw [mem_iInter]
      exact Iff.rfl
    rw [hQi]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hc i)).inter (measurableSet_lt (hc i) measurable_const)
  have hQK : Q ⊆ closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1)) := by
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have h1 := (hy i).1
          have h2 := (hy i).2
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = m + 1 := by simp
  have hK : IsCompact (closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1))) :=
    isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict Q) :=
    isFiniteMeasure_restrict.2 ((measure_mono hQK).trans_lt hK.measure_lt_top).ne
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q
  -- Integrability on `Q × Q`.
  have huQ : Integrable u μ := hu.mono_set hQQ₁
  have hF : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|) (μ.prod μ) :=
    ((huQ.comp_fst μ).sub (huQ.comp_snd μ)).abs
  have hFk : ∀ k, Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => |v k p.1 - v k p.2|)
      (μ.prod μ) := fun k => by
    have hvk : Integrable (v k) μ :=
      (((hmv k).1.continuous.continuousOn).integrableOn_compact hK).mono_set hQK
    exact ((hvk.comp_fst μ).sub (hvk.comp_snd μ)).abs
  -- Step 3: `v k → u` a.e. on `Q`, hence `|v k x - v k y| → |u x - u y|` a.e. on `Q × Q`.
  have hlimQ : ∀ᵐ x ∂μ, Tendsto (fun k => v k x) atTop (𝓝 (u x)) := by
    filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem hQm] with x hx hxQ
    rwa [indicator_of_mem (hQQ₁ hxQ)] at hx
  have hlimP : ∀ᵐ p ∂(μ.prod μ), Tendsto (fun k => ENNReal.ofReal |v k p.1 - v k p.2|) atTop
      (𝓝 (ENNReal.ofReal |u p.1 - u p.2|)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hlimQ,
      Measure.quasiMeasurePreserving_snd.ae hlimQ] with p h1 h2
    exact ENNReal.tendsto_ofReal (h1.sub h2).abs
  -- Steps 4–5: Fatou's lemma on `Q × Q` and Fubini.
  have hFatou : ∫⁻ p, ENNReal.ofReal |u p.1 - u p.2| ∂(μ.prod μ) ≤ ENNReal.ofReal (C * V) :=
    calc ∫⁻ p, ENNReal.ofReal |u p.1 - u p.2| ∂(μ.prod μ)
        = ∫⁻ p, liminf (fun k => ENNReal.ofReal |v k p.1 - v k p.2|) atTop ∂(μ.prod μ) :=
          lintegral_congr_ae (hlimP.mono fun p hp => hp.liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ p, ENNReal.ofReal |v k p.1 - v k p.2| ∂(μ.prod μ)) atTop :=
          lintegral_liminf_le' fun k => (hFk k).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (C * V) := liminf_le_of_frequently_le' (Frequently.of_forall fun k => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hFk k) (ae_of_all _ fun p => abs_nonneg _),
            integral_prod _ (hFk k)]
          exact ENNReal.ofReal_le_ofReal (hD k))
  have hfin : ENNReal.ofReal (∫ x in Q, ∫ y in Q, |u x - u y|) ≤ ENNReal.ofReal (C * V) := by
    rw [← integral_prod (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|) hF,
      ofReal_integral_eq_lintegral_ofReal hF (ae_of_all _ fun p => abs_nonneg _)]
    exact hFatou
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 hV)).1 hfin
/-- Shrinking the unit cube `Q₁ = (0, 1)ᵐ⁺¹` to `Q_δ = (δ, 1 − δ)ᵐ⁺¹` while keeping half of the
`L¹` norm of `f` (Simon Ch. 2, proof of Lemma 2.7).  The cubes `Q_{1/(j+4)}` are open and
increase to `Q₁`, so continuity of the measure from above and of the integral along increasing
unions give one `j` for both the layer bound and the integral bound. -/
theorem dor_lmb_fcd_cp_shrinking : ∀ (m : ℕ) (f : Euclid (m + 1) → ℝ), IntegrableOn f {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} ≤ 1 ∧ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \ {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}) ≤ 1 / 4 ∧ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, |f y| := by
  intro m f hf
  -- Step 1: `Q_t` is open, `Q_t ⊆ Q₁` for `t ≥ 0`, and `volume Q₁ = 1`.
  have hopen : ∀ t : ℝ, IsOpen {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} := by
    intro t
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hmeas : ∀ t : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} :=
    fun t => (hopen t).measurableSet
  have hmeas₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    simpa using hmeas 0
  have hsub : ∀ t : ℝ, 0 ≤ t → {y : Euclid (m + 1) | ∀ i, t < y i ∧ y i < 1 - t} ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun t ht y hy i =>
    ⟨ht.trans_lt (hy i).1, (hy i).2.trans_le (by linarith)⟩
  have hvol₁ : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
    have hpre : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
        WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Set.mem_pi]
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  -- Step 2: `δ_j = 1/(j+4)` decreases to `0`, and the cubes `Q_{δ_j}` increase to `Q₁`.
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℕ → ℝ, δ = fun j : ℕ => 1 / ((j : ℝ) + 4) := ⟨_, rfl⟩
  have hδpos : ∀ j, 0 < δ j := fun j => by rw [hδdef]; positivity
  have hδle : ∀ j, δ j ≤ 1 / 4 := fun j => by
    simp only [hδdef]
    gcongr
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hδanti : Antitone δ := fun j k hjk => by
    simp only [hδdef]
    gcongr
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    rw [hδdef]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hmono : Monotone fun j => {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j} :=
    fun j k hjk y hy i =>
      ⟨(hδanti hjk).trans_lt (hy i).1, (hy i).2.trans_le (by linarith [hδanti hjk])⟩
  have hunion : ⋃ j, {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j} =
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    refine Subset.antisymm (iUnion_subset fun j => hsub _ (hδpos j).le) fun y hy => ?_
    have hev : ∀ᶠ j in atTop, ∀ i, δ j < y i ∧ y i < 1 - δ j := by
      rw [eventually_all]
      intro i
      filter_upwards [(tendsto_order.1 hδlim).2 _ (hy i).1,
        (tendsto_order.1 hδlim).2 _ (sub_pos.2 (hy i).2)] with j hj₁ hj₂
      exact ⟨hj₁, by linarith⟩
    obtain ⟨j, hj⟩ := hev.exists
    exact mem_iUnion.2 ⟨j, hj⟩
  -- Step 3: continuity from above, `volume (Q₁ \ Q_{δ_j}) → 0`.
  have hlayer : Tendsto (fun j => volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
      {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j})) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := volume)
      (s := fun j => {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
        {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j})
      (fun j => (hmeas₁.diff (hmeas _)).nullMeasurableSet)
      (fun j k hjk => Set.sdiff_subset_sdiff_right (hmono hjk))
      ⟨0, ((measure_mono Set.sdiff_subset).trans_lt (by rw [hvol₁]; exact ENNReal.one_lt_top)).ne⟩
    rw [← Set.sdiff_iUnion, hunion, Set.sdiff_self, measure_empty] at h
    exact h
  have hev₁ : ∀ᶠ j in atTop, volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} \
      {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}) < 1 / 4 :=
    (tendsto_order.1 hlayer).2 _ (by norm_num)
  -- Step 4: continuity of the integral, `∫_{Q_{δ_j}} |f| → ∫_{Q₁} |f|`.
  have hint : Tendsto (fun j => ∫ y in {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}, |f y|)
      atTop (𝓝 (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y|)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume) (f := fun y => |f y|)
      (fun j => hmeas (δ j)) hmono (by rw [hunion]; exact hf.abs)
    rw [hunion] at h
    exact h
  have hev₂ : ∀ᶠ j in atTop, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤
      2 * ∫ y in {y : Euclid (m + 1) | ∀ i, δ j < y i ∧ y i < 1 - δ j}, |f y| := by
    rcases (integral_nonneg fun y => abs_nonneg (f y) :
        0 ≤ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |f y|).eq_or_lt with h₀ | hpos
    · exact Eventually.of_forall fun j => by
        rw [← h₀]
        exact mul_nonneg zero_le_two (integral_nonneg fun y => abs_nonneg (f y))
    · filter_upwards [(tendsto_order.1 hint).1 _ (half_lt_self hpos)] with j hj
      linarith
  -- Step 5: one `j` works for both bounds.
  obtain ⟨j, hj₁, hj₂⟩ := (hev₁.and hev₂).exists
  exact ⟨δ j, hδpos j, hδle j, (measure_mono (hsub _ (hδpos j).le)).trans hvol₁.le, hj₁.le, hj₂⟩

/-- **Poincaré inequality with an integer median on the unit cube** (Simon Ch. 2, Lemma 2.7 with
`θ = 1/4`, and the choice (31), (35) of `β_F` in the proof of the Deformation Theorem, Ch. 6, 5.1):
there is `c = c(m) > 0` such that every integer-valued `u` integrable on `Q₁ = (0, 1)^{m+1}` with
`∫_{Q₁} u div g ≤ V` for all smooth `g` with compact support in `Q₁` and `|g| ≤ 1` has an integer
`β` with `∫_{Q₁} |u − β| ≤ c V` and `|β| ≤ 2 ∫_{Q₁} |u|`.  Take the integer median `β`
(`dor_lmb_fcd_cp_integer_median`) and shrink `Q₁` to `Q_δ = (δ, 1 − δ)^{m+1}`, keeping half of
`∫ |u − β|` with `Lⁿ(Q₁ \ Q_δ) ≤ 1/4` (`dor_lmb_fcd_cp_shrinking`), so `β` is a `¼`-median of `u`
on `Q_δ`.  Normalized bumps of radius `δ/(k + 2)` give the BV Poincaré inequality on `Q_δ`
(`dor_lmb_fcd_cp_bv_poincare`), and `dor_lmb_fcd_cp_median_deviation` gives
`∫_{Q₁} |u − β| ≤ 2 ∫_{Q_δ} |u − β| ≤ 2 · 5 (m + 1)(1 − 2δ) V ≤ 10 (m + 1) V`. -/
theorem dor_lmb_fcd_cube_poincare : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m
  refine ⟨10 * ((m : ℝ) + 1), by positivity, ?_⟩
  intro u V hZ hu hH
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  -- Step 0: `V ≥ 0` (test `g = 0`); `{a < yᵢ < b}` is the preimage of the box `(a, b)ⁿ`, so it is
  -- measurable, and `Lⁿ(Q₁) = 1`
  have hV : 0 ≤ V := by
    have h0 := hH (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa using h0
  have hpre : ∀ a b : ℝ, {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} =
      WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo a b) := fun a b => by
    ext y
    simp [Set.mem_pi]
  have hmeas : ∀ a b : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} :=
    fun a b => by
      rw [hpre]
      exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hvol₁ : volume Q₁ = 1 := by
    rw [hQ₁, hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  -- Step 1: the integer median `β` of `u` on `Q₁` (Simon (31), (35))
  obtain ⟨β, hβge, hβle, hβbd⟩ := dor_lmb_fcd_cp_integer_median m u hZ hu
  refine ⟨β, ?_, hβbd⟩
  -- Step 2: shrink `Q₁` to `Q = Q_δ`, keeping half of `∫_{Q₁} |u − β|`
  have hf : IntegrableOn (fun y => u y - β) Q₁ :=
    hu.sub (integrableOn_const (by rw [hvol₁]; exact ENNReal.one_ne_top))
  obtain ⟨δ, hδ0, hδ4, hQ1, hlayer, hhalf⟩ := dor_lmb_fcd_cp_shrinking m (fun y => u y - β) hf
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, δ < y i ∧ y i < 1 - δ}
  have hQQ₁ : Q ⊆ Q₁ := fun y hy i => ⟨hδ0.trans (hy i).1, (hy i).2.trans (by linarith)⟩
  have hQfin : volume Q ≠ ∞ := (hQ1.trans_lt ENNReal.one_lt_top).ne
  -- Step 3: median transfer, `Lⁿ(Q ∩ A) ≥ Lⁿ(Q₁ ∩ A) − Lⁿ(Q₁ \ Q) ≥ 1/4 ≥ ¼ Lⁿ(Q)` for
  -- `A = {β ≤ u}` and `A = {u ≤ β}`; in particular `Lⁿ(Q) > 0`
  have hq1 : (volume Q).toReal ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hQ1
    rwa [ENNReal.toReal_one] at h
  have htransfer : ∀ A : Set (Euclid (m + 1)), 1 / 2 ≤ volume (Q₁ ∩ A) →
      1 / 4 ≤ (volume (Q ∩ A)).toReal := by
    intro A hA
    have hsub : Q₁ ∩ A ⊆ (Q ∩ A) ∪ (Q₁ \ Q) := fun y hy => by
      by_cases hyQ : y ∈ Q
      · exact Or.inl ⟨hyQ, hy.2⟩
      · exact Or.inr ⟨hy.1, hyQ⟩
    have h1 : 1 / 2 ≤ volume (Q ∩ A) + 1 / 4 :=
      hA.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hlayer)))
    have hfinA : volume (Q ∩ A) ≠ ∞ :=
      ((measure_mono inter_subset_left).trans_lt (hQ1.trans_lt ENNReal.one_lt_top)).ne
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinA, by norm_num⟩) h1
    rw [ENNReal.toReal_add hfinA (by norm_num)] at h2
    have h3 : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
    have h4 : ((1 : ℝ≥0∞) / 4).toReal = 1 / 4 := by norm_num
    rw [h3, h4] at h2
    linarith
  have hge : 1 / 4 * (volume Q).toReal ≤ (volume (Q ∩ {y | (β : ℝ) ≤ u y})).toReal := by
    linarith [htransfer _ hβge]
  have hle : 1 / 4 * (volume Q).toReal ≤ (volume (Q ∩ {y | u y ≤ (β : ℝ)})).toReal := by
    linarith [htransfer _ hβle]
  have hqpos : 0 < (volume Q).toReal := by
    have h : (volume (Q ∩ {y | (β : ℝ) ≤ u y})).toReal ≤ (volume Q).toReal :=
      ENNReal.toReal_mono hQfin (measure_mono inter_subset_left)
    linarith [htransfer _ hβge]
  -- Step 4: deviation from the `¼`-median `β` on `Q` (Simon 2.7)
  have hdev := dor_lmb_fcd_cp_median_deviation (m + 1) Q u β (1 / 4) (hmeas δ (1 - δ)) hQfin
    (hu.mono_set hQQ₁) (by norm_num) hge hle
  -- Step 5: normalized bumps `η_k` of radius `δ/(k + 2)`; their mollifications of `1_{Q₁} u`
  -- converge a.e. (Lebesgue differentiation), so the BV Poincaré inequality holds on `Q`
  let φ : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    { rIn := δ / ((k : ℝ) + 2) / 2
      rOut := δ / ((k : ℝ) + 2)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : 0 < δ / ((k : ℝ) + 2) := by positivity
        linarith }
  have hφ0 : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hφK : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn :=
    Eventually.of_forall fun k => by
      change δ / ((k : ℝ) + 2) ≤ 2 * (δ / ((k : ℝ) + 2) / 2)
      linarith
  have hφs : ∀ k, support ((φ k).normed volume) ⊆ ball (0 : Euclid (m + 1)) δ := fun k => by
    rw [(φ k).support_normed_eq]
    exact ball_subset_ball (div_le_self hδ0.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hφ0 hφK (hu.integrable_indicator (hmeas 0 1)).locallyIntegrable
  have hbv := dor_lmb_fcd_cp_bv_poincare m u V δ (fun k => (φ k).normed volume) hu hH hδ0
    (by linarith) (fun k => (φ k).contDiff_normed) (fun k => (φ k).hasCompactSupport_normed)
    (fun k => (φ k).nonneg_normed) (fun k => (φ k).normed_neg) (fun k => (φ k).integral_normed)
    hφs hae
  -- Step 6: `∫_{Q₁} |u − β| ≤ 2 ∫_Q |u − β| ≤ 2 · 5 (m + 1)(1 − 2δ) V ≤ 10 (m + 1) V`
  have hQbd : ∫ y in Q, |u y - β| ≤ 5 * ((m : ℝ) + 1) * V := by
    have hmδV : 0 ≤ ((m : ℝ) + 1) * δ * V := by positivity
    calc ∫ y in Q, |u y - β|
        ≤ (1 + (1 / 4 : ℝ)⁻¹) * ((volume Q).toReal)⁻¹ * ∫ x in Q, ∫ y in Q, |u x - u y| := hdev
      _ ≤ (1 + (1 / 4 : ℝ)⁻¹) * ((volume Q).toReal)⁻¹ *
            (((m : ℝ) + 1) * (1 - 2 * δ) * (volume Q).toReal * V) :=
          mul_le_mul_of_nonneg_left hbv (by positivity)
      _ = 5 * ((m : ℝ) + 1) * (1 - 2 * δ) * V * (((volume Q).toReal)⁻¹ * (volume Q).toReal) := by
          ring
      _ = 5 * ((m : ℝ) + 1) * (1 - 2 * δ) * V := by rw [inv_mul_cancel₀ hqpos.ne', mul_one]
      _ ≤ 5 * ((m : ℝ) + 1) * V := by linarith
  calc ∫ y in Q₁, |u y - β| ≤ 2 * ∫ y in Q, |u y - β| := hhalf
    _ ≤ 2 * (5 * ((m : ℝ) + 1) * V) := by gcongr
    _ = 10 * ((m : ℝ) + 1) * V := by ring

end Submission

/-- **Face replacement** (Simon Ch. 6, proof of the Deformation Theorem 5.1, (26)–(37)): an
integer multiplicity `Q ∈ 𝒟ₙ(ℝᴾ)`, `n = m + 1 < P`, vanishing off `L_n ∩ K` (`K` compact) with
`M(∂Q) < ∞` is the lattice chain `Pc = Σ_{p ∈ s} β_p [[F_p]]` up to an integer multiplicity error
`Q − Pc` with `M(Q − Pc) ≤ c M(∂Q)`, where `Σ_p |β_p| ≤ c M(Q)` and `c = max(c_cp, 2)`.
The faces meeting `K` carry `Q` (`dor_lmb_fcd_fr_skeleton_cells`), so
`Q = Σ_p u_p [[F_p°]]` with integer densities `u_p` and `Σ_p ∫|u_p| ≤ M(Q)` ((26)–(28), (33));
testing `∂Q` near each face bounds the variation of `u_p` by `V_p`, `Σ_p V_p ≤ M(∂Q)` ((28)); the
cube Poincaré inequality gives integer medians `β_p` with `∫|u_p − β_p| ≤ c_cp V_p` and
`|β_p| ≤ 2∫|u_p|` ((31), (32), (35)).  Then `Q − Pc = Σ_p (u_p − β_p)[[F_p°]]` ((29)) has mass
`≤ Σ_p ∫|u_p − β_p| ≤ c_cp M(∂Q)` ((34)), `Σ_p |β_p| ≤ 2 M(Q)` ((36)), `Pc` is integer
multiplicity, and `Q − Pc` vanishes off `cthickening(√P, K) ⊇ F_p`. -/
theorem Submission.dor_lmb_fcd_face_replacement : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 ≤ c ∧ ∀ (K : Set (Euclid P)) (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity Q → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) ({x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ∩ K) → Q ω = 0) → Q.boundary.mass ≠ ∞ → ∃ (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (Pc : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Pc ω = ∑ p ∈ s, (β p : ℝ) * ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, (ω : DifferentialForm (Euclid P) (m + 1)) x (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity (Q - Pc) ∧ (Q - Pc).mass ≤ ENNReal.ofReal c * Q.boundary.mass ∧ (∑ p ∈ s, ((β p).natAbs : ℝ≥0∞)) ≤ ENNReal.ofReal c * Q.mass ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ⊆ cthickening (Real.sqrt P) K) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) (cthickening (Real.sqrt P) K) → (Q - Pc) ω = 0 := by
  intro P m hmP
  -- `c_cp`: the cube Poincaré constant with integer medians (Simon Ch. 2, 2.7; Ch. 6, (31), (35))
  obtain ⟨ccp, hccp, hcp⟩ := Submission.dor_lmb_fcd_cube_poincare m
  refine ⟨max ccp 2, le_max_of_le_right zero_le_two, ?_⟩
  intro K Q hK hQ hQK hbd
  -- the finitely many faces `F_p` (`p ∈ s`) meeting `K`; their open faces carry `L_n ∩ K` a.e.
  obtain ⟨s, hs, hsK, hL, hcover⟩ := Submission.dor_lmb_fcd_fr_skeleton_cells P m K hmP hK
  -- (26)–(28), (33): `Q = Σ_p u_p [[F_p°]]` with integer densities and `Σ ∫|u_p| ≤ M(Q)`
  obtain ⟨u, huZ, huint, humass, hQu⟩ := Submission.dor_lmb_fcd_fr_face_representation P m s _ Q
    hs (hL.inter hK.isClosed) hcover hQ hQK
  -- (28): `∫ u_p div g ≤ V_p` for admissible `g`, with `Σ V_p ≤ M(∂Q)`
  obtain ⟨V, -, hVsum, hVvar⟩ :=
    Submission.dor_lmb_fcd_fr_boundary_variation P m s u Q hs hQu hbd
  -- (31), (32), (35): integer medians `β_p` with `∫|u_p − β_p| ≤ c_cp V_p`, `|β_p| ≤ 2∫|u_p|`
  have hβex : ∀ p, ∃ b : ℤ, p ∈ s →
      (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y - b|) ≤ ccp * V p ∧
        |(b : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y| := by
    intro p
    by_cases hp : p ∈ s
    · obtain ⟨b, hb⟩ := hcp (u p) (V p) (huZ p hp) (huint p hp) (hVvar p hp)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose β hβ using hβex
  -- constants are integrable on the unit cube `Q₁ = (0, 1)ⁿ`, of volume `1`
  have hconst : ∀ p ∈ s, ∀ b : ℝ,
      IntegrableOn (fun _ : Euclid (m + 1) => b) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro p hp b
    have h1 := (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).1
    exact integrableOn_const (by rw [h1]; exact ENNReal.one_ne_top)
  -- the lattice chain `Pc = Σ_p β_p [[F_p]]`, and integrability of the face integrands
  obtain ⟨hβint, ⟨Pc, hPc⟩, -⟩ := Submission.dor_lmb_fcd_fr_chain_current P m s
    (fun p _ => (β p : ℝ)) hs fun p hp => hconst p hp _
  obtain ⟨huωint, -, -⟩ := Submission.dor_lmb_fcd_fr_chain_current P m s u hs huint
  -- the mass bound for currents with face densities `u_p − β_p`
  obtain ⟨-, -, hDmass⟩ := Submission.dor_lmb_fcd_fr_chain_current P m s
    (fun p y => u p y - β p) hs fun p hp => Integrable.sub (huint p hp) (hconst p hp _)
  beta_reduce at hβint hPc hDmass
  -- (29): `Q − Pc = Σ_p (u_p − β_p) [[F_p°]]`
  have hQP : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), (Q - Pc) ω =
      ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (u p y - β p) * (ω : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))
          (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) := by
    intro ω
    show Q ω - Pc ω = _
    rw [hQu ω, hPc ω, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← integral_sub (huωint ω p hp) (hβint ω p hp)]
    congr 1
    funext y
    ring
  refine ⟨s, β, Pc, hs, ?_, ?_, ?_, ?_, hsK, ?_⟩
  · -- the face formula of `Pc`: `∫_{F_p} f dHⁿ = ∫_{Q₁} f ∘ Φ_p`
    intro ω
    rw [hPc ω]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.1]
    exact integral_const_mul _ _
  · -- `Pc` is integer multiplicity, hence so is `Q − Pc`
    exact Submission.cmc_imRep_locality_restrict_sub.2.2.1 P (m + 1) univ Q Pc isOpen_univ hQ
      (Submission.dor_lmb_fcd_fr_lattice_chain_im P m s β Pc hs hPc)
  · -- (34): `M(Q − Pc) ≤ Σ_p ∫|u_p − β_p| ≤ c_cp Σ_p V_p ≤ c M(∂Q)`
    calc (Q - Pc).mass
        ≤ ENNReal.ofReal (∑ p ∈ s,
            ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y - β p|) :=
          hDmass (Q - Pc) hQP
      _ ≤ ENNReal.ofReal (ccp * ∑ p ∈ s, V p) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun p hp => (hβ p hp).1
      _ = ENNReal.ofReal ccp * ENNReal.ofReal (∑ p ∈ s, V p) := ENNReal.ofReal_mul hccp.le
      _ ≤ ENNReal.ofReal (max ccp 2) * Q.boundary.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hVsum
  · -- (36): `Σ_p |β_p| ≤ 2 Σ_p ∫|u_p| ≤ c M(Q)`
    calc (∑ p ∈ s, ((β p).natAbs : ℝ≥0∞))
        = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun p _ => abs_nonneg _]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← ENNReal.ofReal_natCast, Nat.cast_natAbs, Int.cast_abs]
      _ ≤ ENNReal.ofReal (2 * ∑ p ∈ s,
            ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun p hp => (hβ p hp).2
      _ = ENNReal.ofReal 2 * ENNReal.ofReal (∑ p ∈ s,
            ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) :=
          ENNReal.ofReal_mul zero_le_two
      _ ≤ ENNReal.ofReal (max ccp 2) * Q.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) humass
  · -- `Q − Pc` vanishes off `cthickening(√P, K)`, which contains every `F_p ⊇ Φ_p(Q₁)`
    intro ω hω
    rw [hQP ω]
    refine Finset.sum_eq_zero fun p hp => setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hmem := (Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)).2.2.2.2.1 y
      fun i => ⟨(hy i).1.le, (hy i).2.le⟩
    rw [image_eq_zero_of_notMem_tsupport (Set.disjoint_right.1 hω (hsK p hp hmem))]
    simp

end GMT.Ch07
