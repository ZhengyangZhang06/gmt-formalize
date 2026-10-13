import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.WeightedArea
import Poincare.SimonGMT.Chapter02.AreaCritical

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

/-- **Density points see every direction.**  If `y` is a Lebesgue density point of an arbitrary set
`Z ⊆ ℝᵈ`, i.e. `Lᵈ(Z ∩ B̄_r(y)) / Lᵈ(B̄_r(y)) → 1` as `r ↓ 0`, then every unit vector `v` is a limit
of secant directions `(yᵢ - y)/|yᵢ - y|` with `yᵢ ∈ Z ∖ {y}` and `yᵢ → y`.  For `0 < η ≤ 1` and
`r > 0` the ball `B_{ηr/4}(y + (r/2)v)` lies in `B̄_r(y) ∖ {y}` and in the `η`-cone around `v`, and
it has measure `(η/4)ᵈ Lᵈ(B̄_r(y))`, so density one forces `Z` to meet it for all small `r`; take
`η = 1/(i+1)` and `r < 1/(i+1)`. -/
theorem Submission.dor_lmbsf_density_directions : ∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v) := by
  intro d Z y hdens v hv
  -- the ball `B_{ηr/4}(y + (r/2)v)` lies in `B_r(y) ∖ {y}`, inside the `η`-cone around `v`
  have cone : ∀ η r : ℝ, 0 < η → η ≤ 1 → 0 < r → ∀ z ∈ ball (y + (r / 2) • v) (η * r / 4),
      ‖z - y‖ < r ∧ z ≠ y ∧ ‖‖z - y‖⁻¹ • (z - y) - v‖ < η := by
    intro η r hη hη1 hr z hz
    have hs : (0 : ℝ) < r / 2 := by positivity
    -- the offset `w = z - y - (r/2)v` of `z` from the centre has `‖w‖ < ηr/4 ≤ r/4`
    have hw : ‖z - y - (r / 2) • v‖ < η * r / 4 := by
      rwa [mem_ball, dist_eq_norm, sub_add_eq_sub_sub] at hz
    have hw' : ‖z - y - (r / 2) • v‖ < r / 4 := hw.trans_le (by nlinarith)
    have hsv : ‖(r / 2) • v‖ = r / 2 := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hs.le]
    have hdiff : |‖z - y‖ - r / 2| ≤ ‖z - y - (r / 2) • v‖ := by
      simpa only [hsv] using abs_norm_sub_norm_le (z - y) ((r / 2) • v)
    obtain ⟨hlo, hhi⟩ := abs_le.1 hdiff
    have hpos : 0 < ‖z - y‖ := by linarith
    refine ⟨by linarith, fun h => by rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos,
      ?_⟩
    -- `‖z - y‖⁻¹ (z - y) - v = (‖z - y‖⁻¹ - (r/2)⁻¹) (z - y) + (r/2)⁻¹ w`
    have hdecomp : ‖z - y‖⁻¹ • (z - y) - v
        = (‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y) + (r / 2)⁻¹ • (z - y - (r / 2) • v) := by
      rw [sub_smul ‖z - y‖⁻¹ (r / 2)⁻¹ (z - y), smul_sub (r / 2)⁻¹ (z - y) ((r / 2) • v), smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      abel
    have h1 : ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) := by
      have hne : ‖z - y‖ ≠ 0 := hpos.ne'
      have e : (‖z - y‖⁻¹ - (r / 2)⁻¹) * ‖z - y‖ = (r / 2 - ‖z - y‖) / (r / 2) := by
        field_simp
      calc ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ = |(‖z - y‖⁻¹ - (r / 2)⁻¹) * ‖z - y‖| := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_norm]
        _ = |‖z - y‖ - r / 2| / (r / 2) := by rw [e, abs_div, abs_of_pos hs, abs_sub_comm]
        _ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) := by gcongr
    have h2 : ‖(r / 2)⁻¹ • (z - y - (r / 2) • v)‖ = ‖z - y - (r / 2) • v‖ / (r / 2) := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div]
    calc ‖‖z - y‖⁻¹ • (z - y) - v‖
        ≤ ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ + ‖(r / 2)⁻¹ • (z - y - (r / 2) • v)‖ := by
          rw [hdecomp]; exact norm_add_le _ _
      _ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) + ‖z - y - (r / 2) • v‖ / (r / 2) := by
          rw [h2]; linarith
      _ < η := by rw [← add_div, div_lt_iff₀ hs]; linarith
  -- for `0 < η ≤ 1`, `Z` meets `B_{ηr/4}(y + (r/2)v)` for all small `r > 0`: otherwise
  -- `Lᵈ(Z ∩ B̄_r(y)) ≤ Lᵈ(B̄_r(y)) - Lᵈ(B_{ηr/4}(y + (r/2)v)) = (1 - (η/4)ᵈ) Lᵈ(B̄_r(y))`
  have hit : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∃ z ∈ Z, z ∈ ball (y + (r / 2) • v) (η * r / 4) := by
    intro η hη hη1
    have hκ : ENNReal.ofReal ((η / 4) ^ d) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (hdens.eventually_const_lt (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hκ))
    refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
    by_contra! hZ
    have hB : ball (y + (r / 2) • v) (η * r / 4) ⊆ closedBall y r := fun z hz => by
      rw [mem_closedBall, dist_eq_norm]; exact (cone η r hη hη1 hr z hz).1.le
    have hvol : volume (ball (y + (r / 2) • v) (η * r / 4))
        = ENNReal.ofReal ((η / 4) ^ d) * volume (closedBall y r) := by
      rw [Measure.addHaar_ball_of_pos volume _ (by positivity : (0 : ℝ) < η * r / 4),
        Measure.addHaar_closedBall volume _ hr.le, finrank_euclideanSpace_fin, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow, show η / 4 * r = η * r / 4 by ring]
    have hle : volume (Z ∩ closedBall y r)
        ≤ (1 - ENNReal.ofReal ((η / 4) ^ d)) * volume (closedBall y r) :=
      calc volume (Z ∩ closedBall y r)
          ≤ volume (closedBall y r \ ball (y + (r / 2) • v) (η * r / 4)) :=
            measure_mono fun z hz => ⟨hz.2, hZ z hz.1⟩
        _ = volume (closedBall y r) - volume (ball (y + (r / 2) • v) (η * r / 4)) :=
            measure_sdiff hB measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
        _ = (1 - ENNReal.ofReal ((η / 4) ^ d)) * volume (closedBall y r) := by
            rw [hvol, ENNReal.sub_mul fun _ _ => measure_closedBall_lt_top.ne, one_mul]
    have hgt : 1 - ENNReal.ofReal ((η / 4) ^ d)
        < volume (Z ∩ closedBall y r) / volume (closedBall y r) := hsub ⟨hr, hrr₀⟩
    exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
  -- take `η = 1/(i+1)` and `0 < rᵢ < min(r₀, 1/(i+1))`
  have hη : ∀ i : ℕ, (0 : ℝ) < 1 / ((i : ℝ) + 1) := fun i => by positivity
  have hη1 : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 := fun i =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hseq : ∀ i : ℕ, ∃ z ∈ Z, ∃ r : ℝ, 0 < r ∧ r < 1 / ((i : ℝ) + 1) ∧
      z ∈ ball (y + (r / 2) • v) (1 / ((i : ℝ) + 1) * r / 4) := by
    intro i
    obtain ⟨r₀, hr₀, h⟩ := hit _ (hη i) (hη1 i)
    have hm : 0 < min r₀ (1 / ((i : ℝ) + 1)) := lt_min hr₀ (hη i)
    obtain ⟨z, hzZ, hz⟩ := h (min r₀ (1 / ((i : ℝ) + 1)) / 2) (by positivity)
      (by linarith [min_le_left r₀ (1 / ((i : ℝ) + 1))])
    exact ⟨z, hzZ, _, by positivity, by linarith [min_le_right r₀ (1 / ((i : ℝ) + 1))], hz⟩
  choose ys hysZ rs hrs hrsi hysB using hseq
  have hcone := fun i => cone _ (rs i) (hη i) (hη1 i) (hrs i) (ys i) (hysB i)
  refine ⟨ys, fun i => ⟨hysZ i, (hcone i).2.1⟩, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => ((hcone i).1.trans (hrsi i)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => (hcone i).2.2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Chart transfer of a tangential pairing.**  Let `ψ` be an injective `C¹` immersion of an open
`V ⊆ ℝᵈ` into `ℝᴾ`, `Y ⊆ C ⊆ V` with `C` compact and `Y` Borel, `w ∈ L¹(Hᵈ⌞ψ(Y))`, and `W` a Borel
field with `|W| ≤ c'` that is `Hᵈ`-a.e. tangent to `ψ(Y)`.  Then one integrable `Φ`, vanishing off
`Y`, has `∫_{ψ(Y)} w β[W] dHᵈ = ∫ α[Φ] dLᵈ` whenever `β(ψ(y)) ∘ Dψ(y) = α(y)` on `Y`.  By the area
formula (Simon Ch. 2, (3.5)) with Jacobian `J = Jψ > 0` on `Y`, the left side is
`∫_Y J (w ∘ ψ) β(ψ)[W ∘ ψ] dLᵈ`, and the tangency pulls back to `Lᵈ`-a.e. `y ∈ Y`.  For a continuous
left inverse `R` of `Dψ` on `V`, `E = R (W ∘ ψ)` is bounded on `Y` by compactness of `C` and
`Dψ E = W ∘ ψ` a.e. on `Y`, so `Φ = 1_Y J (w ∘ ψ) E` works. -/
theorem Submission.dor_lmbsf_pwl_chart_pairing_transfer : ∀ (P d : ℕ) (V C Y : Set (Euclid d)) (ψ : Euclid d → Euclid P) (w : Euclid P → ℝ) (W : Euclid P → Euclid P) (c' : ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → IntegrableOn w (ψ '' Y) μHE[d] → Measurable W → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[d].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → W x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P)) → ∃ Φ : Euclid d → Euclid d, Integrable Φ ∧ (∀ y, y ∉ Y → Φ y = 0) ∧ ∀ (β : Euclid P → (Euclid P →L[ℝ] ℝ)) (α : Euclid d → (Euclid d →L[ℝ] ℝ)), (∀ y ∈ Y, (β (ψ y)).comp (fderiv ℝ ψ y) = α y) → ∫ x in ψ '' Y, w x * β x (W x) ∂μHE[d] = ∫ y, α y (Φ y) := by
  intro P d V C Y ψ w W c' hV hψ hψinj hDψ hC hCV hY hYC hw hWm hWb hWt
  -- a continuous left inverse `R` of `Dψ` on `V`, with `‖R‖ ≤ M` on the compact `C`
  obtain ⟨R, hRc, hRinv⟩ := Submission.dor_lmbsf_pwl_immersion_left_inverse P d V ψ hV hψ hDψ
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hRc.mono hCV)
  have hYV : Y ⊆ V := hYC.trans hCV
  -- the hypotheses of the area formula hold on `Y`
  have hdiff : ∀ y ∈ Y, DifferentiableAt ℝ ψ y := fun y hy =>
    (hψ.differentiableOn one_ne_zero y (hYV hy)).differentiableAt (hV.mem_nhds (hYV hy))
  have hreg : ∀ y ∈ Y, Injective (fderiv ℝ ψ y) := fun y hy => hDψ y (hYV hy)
  have hinjY : InjOn ψ Y := hψinj.mono hYV
  set J : Euclid d → ℝ := Poincare.SimonGMT.Chapter02.areaJacobianAt ψ
  -- the area formula `∫_{ψ(Y)} g dHᵈ = ∫_Y J (g ∘ ψ) dLᵈ`, for arbitrary `g`
  have harea : ∀ g : Euclid P → ℝ, ∫ x in ψ '' Y, g x ∂μHE[d] = ∫ y in Y, J y * g (ψ y) := by
    intro g
    have := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
      hY hdiff hreg hinjY g
    simp only [finrank_euclideanSpace_fin, smul_eq_mul] at this
    rw [this, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- `J (w ∘ ψ)` is integrable on `Y`
  have hJw : IntegrableOn (fun y => J y * w (ψ y)) Y := by
    have := Poincare.SimonGMT.Chapter02.integrableOn_image_iff_integrableOn_areaJacobian_smul
      hY hdiff hreg hinjY w
    simp only [finrank_euclideanSpace_fin, smul_eq_mul] at this
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact this.1 hw
  -- the tangency of `W` pulls back along `Hᵈ⌞ψ(Y) = ψ_#(J Lᵈ⌞Y)`, as `J > 0` on `Y`
  have htan : ∀ᵐ y ∂(volume.restrict Y),
      W (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) := by
    have hmap := Poincare.SimonGMT.Chapter02.map_withDensity_areaJacobian_eq hY hdiff hreg hinjY
    simp only [finrank_euclideanSpace_fin] at hmap
    have hp := hWt
    rw [← hmap] at hp
    have hcont : ContinuousOn ψ Y := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
    have hae : AEMeasurable ψ ((μHE[d].restrict Y).withDensity
        (fun x => ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt ψ x))) :=
      (hcont.aemeasurable hY).mono_ac (withDensity_absolutelyContinuous _ _)
    have h1 := ae_of_ae_map hae hp
    rw [ae_withDensity_iff
      (Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt ψ).ennreal_ofReal] at h1
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h1
    filter_upwards [h1, ae_restrict_mem hY] with y hy hyY
    have hJ : Poincare.SimonGMT.Chapter02.areaJacobianAt ψ y ≠ 0 := by
      rw [Ne, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_zero_iff_not_injective, not_not]
      exact hreg y hyY
    have hJpos : 0 < Poincare.SimonGMT.Chapter02.areaJacobianAt ψ y :=
      lt_of_le_of_ne (Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg ψ y) (Ne.symm hJ)
    exact hy (by simpa using hJpos) y hyY rfl
  -- the chart field `E = R (W ∘ ψ)`: a.e.-strongly measurable on `Y`, with `|E| ≤ M c'` there
  set E : Euclid d → Euclid d := fun y => R y (W (ψ y)) with hEdef
  have hEm : AEStronglyMeasurable E (volume.restrict Y) := by
    have hR : AEStronglyMeasurable R (volume.restrict Y) :=
      (hRc.mono hYV).aestronglyMeasurable hY
    have hWψ : AEStronglyMeasurable (fun y => W (ψ y)) (volume.restrict Y) :=
      (hWm.comp_aemeasurable ((hψ.continuousOn.mono hYV).aemeasurable hY)).aestronglyMeasurable
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Euclid P) (F := Euclid d)).continuous
      |>.comp_aestronglyMeasurable (hR.prodMk hWψ)
  have hEb : ∀ᵐ y ∂(volume.restrict Y), ‖E y‖ ≤ M * c' := by
    filter_upwards [ae_restrict_mem hY] with y hy
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (hYC hy))
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hM y (hYC hy)) (hWb _) (norm_nonneg _) hM0)
  -- `Φ = 1_Y J (w ∘ ψ) E`
  set Φ : Euclid d → Euclid d := Y.indicator (fun y => (J y * w (ψ y)) • E y) with hΦdef
  have hΦi : Integrable Φ := by
    rw [hΦdef, integrable_indicator_iff hY]
    exact hJw.smul_bdd (M * c') hEm hEb
  refine ⟨Φ, hΦi, fun y hy => by simp [hΦdef, indicator_of_notMem hy], ?_⟩
  intro β α hβα
  rw [harea]
  have hcompl : ∀ y, y ∉ Y → α y (Φ y) = 0 := fun y hy => by
    simp [hΦdef, indicator_of_notMem hy]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (f := fun y => α y (Φ y)) hcompl]
  refine setIntegral_congr_ae hY ?_
  -- for a.e. `y ∈ Y`, `W(ψ(y)) = Dψ(y) z` gives `E(y) = R(y) Dψ(y) z = z`, so
  -- `J w(ψ(y)) β(ψ(y))[W(ψ(y))] = J w(ψ(y)) β(ψ(y))[Dψ(y) E(y)] = α(y)[Φ(y)]`
  filter_upwards [ae_restrict_iff' hY |>.1 htan] with y hyt hyY
  obtain ⟨z, hz⟩ := hyt hyY
  have hz' : fderiv ℝ ψ y z = W (ψ y) := hz
  have hEz : E y = z := by
    have := congrArg (fun T : Euclid d →L[ℝ] Euclid d => T z) (hRinv y (hYV hyY))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [hEdef]
    simp only
    rw [← hz', this]
  have hE : fderiv ℝ ψ y (E y) = W (ψ y) := by rw [hEz, hz']
  rw [hΦdef, indicator_of_mem hyY, map_smul, ← hβα y hyY, ContinuousLinearMap.comp_apply, hE,
    smul_eq_mul]
  ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
