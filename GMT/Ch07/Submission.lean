import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.WeightedArea
import Poincare.SimonGMT.Chapter08.DistributionalConstancy

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

/-- Step 1 of the proof that an integer multiplicity cycle carried by a `C¹` graph is regular
(Simon 7.4.3, via Allard's theorem): orthogonal coordinates on `ℝ^{n+k}`.  If the linear
isometries `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` have orthogonal ranges `L`, `L'`, then every
`x ∈ ℝ^{n+k}` is `ι v + ι' w`, and `‖ι v + ι' w‖² = ‖v‖² + ‖w‖²`.  `L` and `L'` have dimensions `n`
and `k` and meet only in `0`, so by the dimension formula `L ⊔ L' = ℝ^{n+k}`; the norm identity
is Pythagoras. -/
theorem Submission.dgcr_orthogonal_coordinates : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ x : Euclid (n + k), ∃ v : Euclid n, ∃ w : Euclid k, x = ι v + ι' w) ∧ ∀ (v : Euclid n) (w : Euclid k), ‖ι v + ι' w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  intro n k ι ι' horth
  refine ⟨fun x => ?_, fun v w => ?_⟩
  · -- `L := range ι` and `L' := range ι'` have dimensions `n` and `k` (isometries are injective)
    have hL : Module.finrank ℝ (LinearMap.range ι.toLinearMap) = n := by
      rw [LinearMap.finrank_range_of_inj ι.injective, finrank_euclideanSpace_fin]
    have hL' : Module.finrank ℝ (LinearMap.range ι'.toLinearMap) = k := by
      rw [LinearMap.finrank_range_of_inj ι'.injective, finrank_euclideanSpace_fin]
    -- `L ⊓ L' = ⊥`: if `ι v = ι' w`, then `⟪ι v, ι v⟫ = ⟪ι v, ι' w⟫ = 0`, so `ι v = 0`
    have hinf : LinearMap.range ι.toLinearMap ⊓ LinearMap.range ι'.toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨⟨v, rfl⟩, w, hw⟩
      have h0 : inner ℝ (ι v) (ι v) = 0 := by
        have h := horth v w
        rwa [show ι' w = ι v from hw] at h
      exact inner_self_eq_zero.1 h0
    -- dimension formula: `dim (L ⊔ L') = n + k = dim ℝ^{n+k}`, so `L ⊔ L' = ⊤`
    have hsup : LinearMap.range ι.toLinearMap ⊔ LinearMap.range ι'.toLinearMap = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range ι.toLinearMap) (LinearMap.range ι'.toLinearMap)
      rw [hinf, finrank_bot, hL, hL'] at h
      rw [finrank_euclideanSpace_fin]
      omega
    -- `x ∈ L ⊔ L'`, so `x = ι v + ι' w`
    have hx : x ∈ LinearMap.range ι.toLinearMap ⊔ LinearMap.range ι'.toLinearMap := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, hvw⟩ := Submodule.mem_sup.1 hx
    exact ⟨v, w, hvw.symm⟩
  · -- Pythagoras: the cross term `2 ⟪ι v, ι' w⟫` vanishes and `ι`, `ι'` preserve norms
    rw [norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]
    ring
/-- Step 8 of the proof that an integer multiplicity cycle carried by a `C¹` graph is regular
(Simon 7.4.3, via Allard's theorem; consequences of the area formula, Ch. 2, 3.2–3.5): for the
graph map `Φ(v) = z + ιv + ι'u(v)` of a `C¹` function `u` on `B_s(0)` (`ι`, `ι'` orthogonal linear
isometries), `∫_A g ∘ Φ dLⁿ ≤ ∫_{Φ(A)} g dHⁿ` for Borel `A ⊆ B_s(0)` and Borel `g ≥ 0`, and
`Hⁿ(Φ(B̄_t(0))) < ∞` for `t < s`.  `Pr = ι*(· − z)` is a 1-Lipschitz left inverse of `Φ`, so
`Lⁿ(S) = Hⁿ(Pr(Φ(S))) ≤ Hⁿ(Φ(S))` and `Φ_#(Lⁿ⌞A) ≤ Hⁿ⌞Φ(A)`; on the compact convex set `B̄_t(0)`,
`Φ` is Lipschitz by the mean value inequality. -/
theorem Submission.dgcr_graph_measure_bounds : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → (∀ (A : Set (Euclid n)) (g : Euclid (n + k) → ℝ≥0∞), MeasurableSet A → A ⊆ ball 0 s → Measurable g → ∫⁻ v in A, g (z + ι v + ι' (u v)) ≤ ∫⁻ x in (fun v => z + ι v + ι' (u v)) '' A, g x ∂μHE[n]) ∧ ∀ t : ℝ, t < s → μHE[n] ((fun v => z + ι v + ι' (u v)) '' closedBall (0 : Euclid n) t) ≠ ∞ := by
  intro n k ι ι' u z s horth hs hu
  set Φ : Euclid n → Euclid (n + k) := fun v => z + ι v + ι' (u v) with hΦ
  -- step 1: `Pr = ι*(· − z)` is a 1-Lipschitz left inverse of `Φ`
  set ιs : Euclid (n + k) →L[ℝ] Euclid n := ContinuousLinearMap.adjoint ι.toContinuousLinearMap
    with hιs
  have hιsι : ∀ v, ιs (ι v) = v := fun v => ext_inner_right ℝ fun w => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.inner_map_map]
  have hιsι' : ∀ w, ιs (ι' w) = 0 := fun w => ext_inner_right ℝ fun v => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      inner_zero_left, real_inner_comm, horth]
  have hιs_le : ∀ y, ‖ιs y‖ ≤ ‖y‖ := fun y =>
    calc ‖ιs y‖ ≤ ‖ιs‖ * ‖y‖ := ιs.le_opNorm y
      _ = ‖ι.toContinuousLinearMap‖ * ‖y‖ := by rw [hιs, LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖y‖ := by gcongr; exact ι.norm_toContinuousLinearMap_le
      _ = ‖y‖ := one_mul _
  let Pr : Euclid (n + k) → Euclid n := fun x => ιs (x - z)
  have hPrΦ : ∀ v, Pr (Φ v) = v := fun v => by
    simp only [Pr, hΦ, add_assoc, add_sub_cancel_left, map_add, hιsι, hιsι', add_zero]
  have hPr : LipschitzWith 1 Pr := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [Pr, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul]
    exact hιs_le _
  -- step 3: `Lⁿ(S) ≤ Hⁿ(Φ(S))` for every `S`
  have hvol : ∀ S : Set (Euclid n), volume S ≤ μHE[n] (Φ '' S) := fun S => by
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hPr.lipschitzOnWith (s := Φ '' S))
    rwa [image_image, show (fun v => Pr (Φ v)) = id from funext hPrΦ, image_id,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ENNReal.coe_one, one_pow, one_mul] at h
  have hΦC1 : ContDiffOn ℝ 1 Φ (ball 0 s) :=
    (contDiffOn_const.add ι.contDiff.contDiffOn).add (ι'.contDiff.comp_contDiffOn hu)
  refine ⟨fun A g hA hAs hg => ?_, fun t ht => ?_⟩
  · -- steps 4–5: `Φ_#(Lⁿ⌞A) ≤ Hⁿ⌞Φ(A)`
    have hΦm : AEMeasurable Φ (volume.restrict A) := (hΦC1.continuousOn.mono hAs).aemeasurable hA
    have hν : Measure.map Φ (volume.restrict A) ≤ μHE[n].restrict (Φ '' A) := by
      refine Measure.le_iff.2 fun S hS => ?_
      rw [Measure.map_apply_of_aemeasurable hΦm hS, Measure.restrict_apply' hA,
        Measure.restrict_apply hS, ← image_preimage_inter]
      exact hvol _
    calc ∫⁻ v in A, g (Φ v) = ∫⁻ x, g x ∂(Measure.map Φ (volume.restrict A)) :=
          (lintegral_map' hg.aemeasurable hΦm).symm
      _ ≤ ∫⁻ x in Φ '' A, g x ∂μHE[n] := lintegral_mono' hν le_rfl
  · -- step 6: `Φ` is Lipschitz on `B̄_t(0)`
    rcases lt_or_ge t 0 with ht0 | ht0
    · rw [closedBall_eq_empty.2 ht0, image_empty, measure_empty]
      exact ENNReal.zero_ne_top
    have hKs : closedBall (0 : Euclid n) t ⊆ ball 0 s := closedBall_subset_ball ht
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid n) t).exists_bound_of_continuousOn
      ((hΦC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hKs)
    have hLip : LipschitzOnWith C.toNNReal Φ (closedBall 0 t) :=
      (convex_closedBall (0 : Euclid n) t).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun v hv => ((hΦC1.differentiableOn one_ne_zero).differentiableAt
          (isOpen_ball.mem_nhds (hKs hv))).hasFDerivAt.hasFDerivWithinAt)
        (fun v hv => by rw [← norm_toNNReal]; exact Real.toNNReal_le_toNNReal (hC v hv))
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (isCompact_closedBall (0 : Euclid n) t).measure_lt_top.ne
/-- Step 11 of the proof that an integer multiplicity cycle carried by a `C¹` graph is regular
(Simon 7.4.3, via Allard's theorem; orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in Ch. 6, 2.1–2.2): two unit
orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a
sign.  `τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.dgcr_unitOrientation_eq_or_neg : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ξ₂ = ξ₁ ∨ ξ₂ = -ξ₁ := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, h₁⟩ ⟨τ', hτ', hspan', h₂⟩
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
  -- `ξ₂ = ±ξ₁`
  rcases hd with hd | hd <;> rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · left; ext α; rw [h₂, h₁, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, h₂, h₁, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, h₂, h₁, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [h₂, h₁, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, h₂, h₁, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [h₂, h₁, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [h₂, h₁, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, h₂, h₁, hτ'τ, hd, neg_one_mul, neg_neg]

/-- **An integer multiplicity cycle carried by a `C¹` graph is regular** (Simon 7.4.3, p. 194,
"Hence by Allard's Theorem 5.2 of Ch. 5 we have `y ∈ reg T`", with the Constancy Theorem 6.2.34).
Let `T = τ(M, θ, ξ) ∈ 𝒟ₙ(U)` with `∂T = 0`, `ι`, `ι'` linear isometries with orthogonal ranges,
`Φ(v) = z + ιv + ι'u(v)` for a `C¹` map `u` on `B_s(0)` with `u(0) = 0`, and
`C = {z + ιv + ι'w : |v| < s, |w| < h} ⊆ U`.  If `spt μ_T ∩ C = Σ := Φ(B_s(0))` and `z ∈ spt T`,
then `z ∈ reg T`.  `Σ` is an embedded `C¹` submanifold through `z = Φ(0)` with a continuous unit
orientation `ξ_Σ`, and `T(ω) = ∫_Σ g ⟨ω, ξ_Σ⟩ dHⁿ` for `spt ω ⊆ C`, with `G = g ∘ Φ` locally
integrable and integer-valued on `B_s(0)`.  By the area formula and
`α(DΦe₁, …, DΦeₙ) = JΦ ⟨α, ξ_Σ⟩`, `T(ω) = ∫_{B_s(0)} G ω(Φ)(DΦe₁, …, DΦeₙ) dv`; `∂T = 0` kills
the weak derivatives of `G`, so `G = m ∈ ℤ` a.e. on the connected ball and `T = m[[Σ]]` in `C`.
`m ≠ 0` as `z ∈ spt T`, and `ρ = min(s, h)/2` gives `B̄_ρ(z) ⊆ C`. -/
theorem Submission.dor_graph_supported_cycle_regular : ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (T : GeometricCurrentOn U n) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s h : ℝ), 0 < n → IsOpen U → R.Represents T → BoundaryVanishes T → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → 0 < h → ContDiffOn ℝ 1 u (ball 0 s) → u 0 = 0 → {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} ⊆ U → R.measure.support ∩ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} = (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s → z ∈ T.support → z ∈ regularSet T := by
  intro n k U T R ι ι' u z s h hn _hU hRT hbd horth hs hh hu hu0 hCU hspt hzT
  -- step 1: orthogonal coordinates `x − z = ιv + ι'w` with `‖x − z‖² = ‖v‖² + ‖w‖²`
  obtain ⟨hdec, hpyth⟩ := Submission.dgcr_orthogonal_coordinates n k ι ι' horth
  have hle : ∀ (v : Euclid n) (w : Euclid k), ‖v‖ ≤ ‖ι v + ι' w‖ ∧ ‖w‖ ≤ ‖ι v + ι' w‖ := by
    intro v w
    have h2 := hpyth v w
    constructor <;> nlinarith [norm_nonneg v, norm_nonneg w, norm_nonneg (ι v + ι' w)]
  have huniq : ∀ (v v' : Euclid n) (w w' : Euclid k), ι v + ι' w = ι v' + ι' w' → w = w' := by
    intro v v' w w' heq
    have h0 : ι (v - v') + ι' (w - w') = 0 := by
      rw [map_sub, map_sub, sub_add_sub_comm, heq, sub_self]
    have h1 := (hle (v - v') (w - w')).2
    rw [h0, norm_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  -- `ρ := min(s, h)/2`, so `B̄_ρ(z) ⊆ C ⊆ U`
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min s h / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact half_pos (lt_min hs hh)
  have hρs : ρ < s := by rw [hρdef]; linarith [min_le_left s h, lt_min hs hh]
  have hρh : ρ < h := by rw [hρdef]; linarith [min_le_right s h, lt_min hs hh]
  have hclosed : closedBall z ρ ⊆ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} := by
    intro x hx
    obtain ⟨v, w, hvw⟩ := hdec (x - z)
    have hxz : ‖ι v + ι' w‖ ≤ ρ := by rw [← hvw, ← dist_eq_norm]; exact hx
    refine ⟨v, ?_, w, ?_, ?_⟩
    · rw [mem_ball_zero_iff]; exact ((hle v w).1.trans hxz).trans_lt hρs
    · rw [mem_ball_zero_iff]; exact ((hle v w).2.trans hxz).trans_lt hρh
    · rw [add_assoc, ← hvw, add_sub_cancel]
  have hballC : ball z ρ ⊆ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} :=
    ball_subset_closedBall.trans hclosed
  -- `‖v‖ ≤ ‖Φ(v) − z‖`, `z = Φ(0) ∈ Σ`, and `u(B_s(0)) ⊆ B_h(0)` because `Σ ⊆ C`
  have hnorm : ∀ v : Euclid n, ‖v‖ ≤ ‖z + ι v + ι' (u v) - z‖ := fun v => by
    rw [add_assoc, add_sub_cancel_left]; exact (hle v (u v)).1
  have hzS : z ∈ (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s :=
    ⟨0, mem_ball_self hs, by simp [hu0]⟩
  have huh : ∀ v ∈ ball (0 : Euclid n) s, u v ∈ ball (0 : Euclid k) h := by
    intro v hv
    have hmem : z + ι v + ι' (u v) ∈ R.measure.support ∩ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} := by
      rw [hspt]; exact ⟨v, hv, rfl⟩
    obtain ⟨v', -, w', hw', heq⟩ := hmem.2
    rw [add_assoc, add_assoc] at heq
    rwa [huniq v v' (u v) w' (add_left_cancel heq)]
  -- step 2: `Σ` is an embedded `C¹` submanifold with `T_{Φ(v)}Σ = range DΦ(v)`, oriented by `ξ`
  obtain ⟨hinj, hdiff, hemb, htan⟩ := Submission.dgcr_graph_chart_embedded n k ι ι' u z s horth hs hu
  obtain ⟨ξ, β, hξc, hβc, hξβ, hξo, hjac⟩ :=
    Submission.dgcr_graph_orientation_jacobian n k ι ι' u z s hn horth hs hu
  have hor : IsOrientation n ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ξ := by
    refine ⟨hξc, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, (htan v hv).symm, hξo v hv⟩
  -- step 3: an integer density `g` on `Σ` with `T(ω) = ∫_Σ g ⟨ω, ξ⟩ dHⁿ` for `spt ω ⊆ C`
  obtain ⟨g, hgloc, hgint, hgrep⟩ := Submission.dgcr_graph_integer_density_on_graph n k U T R ι ι' u z
    s h ξ β hn hRT horth hs hh hu hCU hspt hβc hξβ hξo
  -- step 4: area formula `∫_Σ F dHⁿ = ∫_{B_s(0)} JΦ · F ∘ Φ dLⁿ`, `JΦ = √det(DΦ* DΦ)`
  have harea : ∀ F : Euclid (n + k) → ℝ, ∫ x in (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, F x ∂μHE[n] = ∫ v in ball (0 : Euclid n) s, Real.sqrt (((fderiv ℝ (fun v => z + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => z + ι v + ι' (u v)) v).det) * F (z + ι v + ι' (u v)) := by
    intro F
    have h4 := Poincare.SimonGMT.Chapter02.integral_area_formula_of_injective_derivative
      measurableSet_ball (fun v hv => (hdiff v hv).1) (fun v hv => (hdiff v hv).2) hinj F
    rw [finrank_euclideanSpace_fin, EuclideanSpace.euclideanHausdorffMeasure_eq_volume n] at h4
    rw [h4]
    refine setIntegral_congr_fun measurableSet_ball fun v _ => ?_
    simp only [smul_eq_mul, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_sqrt_det_adjoint_comp]
  -- with `α(DΦe₁, …, DΦeₙ) = JΦ ⟨α, ξ⟩`: `T(ω) = ∫_{B_s(0)} G ω(Φ)(DΦe₁, …, DΦeₙ) dv`, `G = g ∘ Φ`
  have hrepD : ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid (n + k)) n) ⊆ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} → T ω = ∫ v in ball (0 : Euclid n) s, g (z + ι v + ι' (u v)) * (ω : DifferentialForm (Euclid (n + k)) n) (z + ι v + ι' (u v)) (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) := by
    intro ω hω
    rw [hgrep ω hω, harea]
    refine setIntegral_congr_fun measurableSet_ball fun v hv => ?_
    simp only [hjac v hv]
    ring
  -- step 5: `∂T = 0` gives `∫ G ∂ⱼa = 0` for all tests `a`; distributional constancy on `B_s(0)`
  have hBT := Submission.dgcr_graph_boundary_weak_derivatives n k U T ι ι' u z s h
    (fun v => g (z + ι v + ι' (u v))) hn hbd horth hs hh hu huh hCU hrepD
  have hSC := Submission.dgcr_smooth_tests_to_C1_tests n (ball (0 : Euclid n) s)
    (fun v => g (z + ι v + ι' (u v))) isOpen_ball hgloc hBT
  obtain ⟨c, hc⟩ := Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero
    hgloc isOpen_ball (convex_ball (0 : Euclid n) s).isPreconnected hSC
  -- the constant is an integer `m`: `G` is integer-valued a.e. and `Lⁿ(B_s(0)) > 0`
  obtain ⟨v₀, -, hv₀c, m, hv₀m⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos volume (0 : Euclid n) hs).ne' (hc.and hgint)
  have hGm : ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid n) s)), g (z + ι v + ι' (u v)) = m := by
    filter_upwards [hc] with v hv
    exact hv.trans (hv₀c.symm.trans hv₀m)
  -- step 6: `T = m[[Σ]]` in `C`
  have hrepm : ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid (n + k)) n) ⊆ {x | ∃ v ∈ ball (0 : Euclid n) s, ∃ w ∈ ball (0 : Euclid k) h, x = z + ι v + ι' w} → T ω = (m : ℝ) * ∫ x in (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, ξ x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n] := by
    intro ω hω
    rw [hrepD ω hω, harea, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hGm, ae_restrict_mem measurableSet_ball] with v hv hvD
    rw [hv, hjac v hvD]
  -- step 7: `m ≠ 0`, since otherwise `T` vanishes in `B_ρ(z)` and `z ∉ spt T`
  have hm0 : m ≠ 0 := by
    intro hm
    subst hm
    have hvan : T.VanishesOn (ball z ρ) := by
      intro ω hω
      rw [hrepm ω (hω.trans hballC), Int.cast_zero, zero_mul]
    exact hzT.2 (Set.mem_sUnion.2 ⟨ball z ρ, ⟨isOpen_ball,
      (isCompact_closedBall z ρ).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans (hclosed.trans hCU), hvan⟩, mem_ball_self hρ⟩)
  -- step 8: `Hⁿ(Σ ∩ K) ≤ Hⁿ(Φ(B̄_ρ(0))) < ∞` for `K ⊆ B_ρ(z)`
  have hfin : ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ ball z ρ → μHE[n] (((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∩ K) ≠ ∞ := by
    intro K _ hK
    refine ne_top_of_le_ne_top
      ((Submission.dgcr_graph_measure_bounds n k ι ι' u z s horth hs hu).2 ρ hρs) (measure_mono ?_)
    rintro _ ⟨⟨v, -, rfl⟩, hvK⟩
    refine ⟨v, ?_, rfl⟩
    have hv := hK hvK
    rw [mem_ball, dist_eq_norm] at hv
    rw [mem_closedBall_zero_iff]
    exact (hnorm v).trans hv.le
  exact ⟨hzT, ρ, hρ, hballC.trans hCU, m, (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, ξ,
    hm0, hzS, hemb, hor, hfin, fun ω hω => hrepm ω (hω.trans hballC)⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
