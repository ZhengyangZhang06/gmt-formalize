import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
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

/-- `Hⁿ(Q ∩ B_ρ(y)) = ωₙρⁿ` for an `n`-dimensional linear subspace `Q` of `ℝᴾ`, `y ∈ Q` and
`ρ > 0` (used in the proof of Simon 7.3.3(1), p. 191, for the density of the planes of a
2-dimensional minimizing cone).  The inclusion `Q → ℝᴾ` is an isometry, so `Q ∩ B_ρ(y)` has the
measure of the ball `B_ρ(y)` of `Q`; on `Q`, `μHE[n]` is the volume, Haar scaling gives
`vol(B_ρ(y)) = ρⁿ vol(B_1(0))`, and orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume, so
`vol(B_1(0)) = ωₙ`. -/
theorem Submission.idtp_tdc_subspace_ball_measure : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (y : Euclid P) (ρ : ℝ), Module.finrank ℝ Q = n → y ∈ Q → 0 < ρ → μHE[n] ((Q : Set (Euclid P)) ∩ ball y ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) := by
  intro P n Q y ρ hn hy hρ
  subst hn
  -- the inclusion `Q → ℝᴾ` is an isometry with range `Q`; `B_ρ(y)` pulls back to the ball of `Q`
  have hball : μHE[Module.finrank ℝ Q] ((Q : Set (Euclid P)) ∩ ball y ρ) =
      μHE[Module.finrank ℝ Q] (ball (⟨y, hy⟩ : Q) ρ) := by
    rw [← isometry_subtype_coe.preimage_ball (⟨y, hy⟩ : Q) ρ,
      isometry_subtype_coe.euclideanHausdorffMeasure_preimage, Subtype.range_coe, Set.inter_comm]
  -- orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume and map `B_1(0)` onto `B_1(0)`
  have hunit := (stdOrthonormalBasis ℝ Q).measurePreserving_repr.measure_preimage
    (measurableSet_ball (x := (0 : Euclid (Module.finrank ℝ Q))) (ε := 1)).nullMeasurableSet
  rw [LinearIsometryEquiv.preimage_ball, map_zero] at hunit
  -- `μHE[n] = volume` on `Q`, then Haar scaling of balls
  rw [hball, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, hunit, mul_comm]
  rfl

/-- **`Hⁿ⌞Q = ι_#(Lⁿ)` for the plane of an orthonormal frame** (step 3 of the planar constancy
argument, Simon Ch. 6, 2.34, in the proof of Simon 7.3.3).  For `τ` orthonormal in `ℝᴾ`,
`ι(s) = Σᵢ sᵢτᵢ` is linear with `|ι(s)|² = Σᵢ sᵢ² = |s|²`, so it is an isometry `ℝⁿ → ℝᴾ` with
range `Q = span{τ₁, …, τₙ}`; `Hⁿ` is preserved by isometries (`ι_#(Hⁿ) = Hⁿ⌞range ι`) and
`Hⁿ = Lⁿ` on `ℝⁿ`. -/
theorem Submission.idtp_pc_plane_hausdorff_eq_map : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → (μHE[n] : Measure (Euclid P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) = Measure.map (fun s : Euclid n => ∑ i, s i • τ i) volume := by
  intro P n τ hτ
  -- `ι(s) = Σᵢ sᵢτᵢ` is linear
  let L : Euclid n →ₗ[ℝ] Euclid P :=
    { toFun := fun s => ∑ i, s i • τ i
      map_add' := fun s t => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.smul_sum, smul_smul] }
  have hLapp : ∀ s, L s = ∑ i, s i • τ i := fun s => rfl
  -- `|ι(s)|² = ⟨ι(s), ι(s)⟩ = Σᵢ sᵢ² = |s|²`, so `ι` is an isometry
  have hnorm : ∀ s, ‖L s‖ = ‖s‖ := by
    intro s
    have h1 : ‖L s‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [hLapp, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hiso : Isometry L := AddMonoidHomClass.isometry_of_norm L hnorm
  -- `range ι = Q`: `ι(s) ∈ Q`, and each `y ∈ Q` is `Σᵢ cᵢτᵢ = ι(c)`
  have hrange : Set.range L = (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      rw [hLapp]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (SetLike.mem_coe.mp hy)
      exact ⟨(WithLp.equiv 2 (Fin n → ℝ)).symm c, by rw [hLapp]; rfl⟩
  -- `ι_#(Hⁿ) = Hⁿ⌞range ι = Hⁿ⌞Q`, and `Hⁿ = Lⁿ` on `ℝⁿ`
  have h := hiso.map_euclideanHausdorffMeasure (d := n)
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hrange] at h
  exact h.symm
/-- A test function on the parameter domain of a plane extends to an ambient test function (step 6
of the constancy argument for a current carried by a plane, Simon Ch. 6, 2.34).  For orthonormal
`τ`, `ι(s) = Σᵢ sᵢτᵢ` and `ψ ∈ C^∞_c` with `spt ψ ⊆ ι⁻¹(V)`, let `ι*(y) = (⟨τₖ, y⟩)ₖ` (so
`ι*ι = id`, `ι*τⱼ = eⱼ`) and `q(y) = y − ι(ι*y)`.  Choose `δ > 0` with
`cthickening δ (ι(spt ψ)) ⊆ V` and a smooth bump `χ`, `χ = 1` on `B̄_{δ/2}(0)`, `spt χ ⊆ B̄_δ(0)`,
and put `f(y) = ψ(ι*y)·χ(q y)`.  Then `spt f ⊆ {y : ι*y ∈ spt ψ, |q y| ≤ δ}`, a compact subset of
`V`, and `f = ψ ∘ ι*` near `ι(s)`, so `f(ι(s)) = ψ(s)` and `Df(ι(s))(τⱼ) = Dψ(s)(eⱼ)`. -/
theorem Submission.idtp_pc_plane_test_extension : ∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (ψ : Euclid n → ℝ), IsOpen V → Orthonormal ℝ τ → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∃ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V ∧ ∀ s : Euclid n, f (∑ i, s i • τ i) = ψ s ∧ ∀ j : Fin n, fderiv ℝ f (∑ i, s i • τ i) (τ j) = fderiv ℝ ψ s (EuclideanSpace.single j (1 : ℝ)) := by
  intro P n V τ ψ hV hτ hψ hψc hψΩ
  -- the parametrization L and its left inverse Ls
  let L₀ : Euclid n →ₗ[ℝ] Euclid P :=
    { toFun := fun s => ∑ i, s i • τ i
      map_add' := fun s t => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.smul_sum, smul_smul] }
  let L : Euclid n →L[ℝ] Euclid P := LinearMap.toContinuousLinearMap L₀
  have hLapp : ∀ s, L s = ∑ i, s i • τ i := fun s => rfl
  have hnorm : ∀ s, ‖L s‖ = ‖s‖ := by
    intro s
    have h1 : ‖L s‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [hLapp, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  let Ls₀ : Euclid P →ₗ[ℝ] Euclid n :=
    { toFun := fun y => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => inner ℝ (τ k) y)
      map_add' := fun y z => by ext k; simp [inner_add_right]
      map_smul' := fun c y => by ext k; simp [inner_smul_right] }
  let Ls : Euclid P →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap Ls₀
  have hLsL : ∀ s, Ls (L s) = s := by
    intro s
    ext k
    simp [Ls, Ls₀, L, L₀, orthonormal_iff_ite.mp hτ]
  have hLsτ : ∀ j, Ls (τ j) = EuclideanSpace.single j (1 : ℝ) := by
    intro j
    ext k
    simp [Ls, Ls₀, orthonormal_iff_ite.mp hτ, eq_comm]
  -- the normal component q y = y - L (Ls y)
  let q : Euclid P →L[ℝ] Euclid P := ContinuousLinearMap.id ℝ (Euclid P) - L.comp Ls
  have hqapp : ∀ y, q y = y - L (Ls y) := fun y => rfl
  have hqL : ∀ s, q (L s) = 0 := by intro s; rw [hqapp, hLsL, sub_self]
  -- compactness and a margin δ
  set K := tsupport ψ with hKdef
  have hK : IsCompact K := hψc
  have hLK : IsCompact (L '' K) := hK.image L.continuous
  have hLKV : L '' K ⊆ V := by
    rintro _ ⟨s, hs, rfl⟩
    exact hψΩ hs
  obtain ⟨δ, hδ, hδV⟩ := hLK.exists_cthickening_subset_open hV hLKV
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  -- the bump function
  let χ : ContDiffBump (0 : Euclid P) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let f : Euclid P → ℝ := fun y => ψ (Ls y) * χ (q y)
  have hfapp : ∀ y, f y = ψ (Ls y) * χ (q y) := fun y => rfl
  -- the set A
  let A : Set (Euclid P) := {y | Ls y ∈ K ∧ ‖q y‖ ≤ δ}
  have hAclosed : IsClosed A :=
    (isClosed_tsupport ψ |>.preimage Ls.continuous).inter
      (isClosed_le (continuous_norm.comp q.continuous) continuous_const)
  have hsuppA : support f ⊆ A := by
    intro y hy
    have hy' : ψ (Ls y) * χ (q y) ≠ 0 := hy
    refine ⟨subset_tsupport ψ (left_ne_zero_of_mul hy'), ?_⟩
    have hχ : χ (q y) ≠ 0 := right_ne_zero_of_mul hy'
    have : q y ∈ support χ := hχ
    rw [χ.support_eq] at this
    simpa [dist_eq_norm] using (mem_ball.mp this).le
  have htsuppA : tsupport f ⊆ A := closure_minimal hsuppA hAclosed
  have hAbdd : A ⊆ closedBall 0 (R + δ) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h1 : y = L (Ls y) + q y := by rw [hqapp]; abel
    have h2 : ‖Ls y‖ ≤ R := by simpa using hR hy.1
    calc ‖y‖ = ‖L (Ls y) + q y‖ := by rw [← h1]
      _ ≤ ‖L (Ls y)‖ + ‖q y‖ := norm_add_le _ _
      _ = ‖Ls y‖ + ‖q y‖ := by rw [hnorm]
      _ ≤ R + δ := add_le_add h2 hy.2
  have hAcpt : IsCompact A := (isCompact_closedBall 0 (R + δ)).of_isClosed_subset hAclosed hAbdd
  have hAV : A ⊆ V := by
    intro y hy
    apply hδV
    apply mem_cthickening_of_dist_le y (L (Ls y)) δ (L '' K) ⟨Ls y, hy.1, rfl⟩
    rw [dist_eq_norm, ← hqapp]
    exact hy.2
  refine ⟨f, ?_, ?_, htsuppA.trans hAV, fun s => ⟨?_, fun j => ?_⟩⟩
  · exact (hψ.comp Ls.contDiff).mul (χ.contDiff.comp q.contDiff)
  · exact HasCompactSupport.of_support_subset_isCompact hAcpt hsuppA
  · show ψ (Ls (L s)) * χ (q (L s)) = ψ s
    rw [hLsL, hqL, χ.one_of_mem_closedBall (by simp; positivity), mul_one]
  · -- near L s, f = ψ ∘ Ls
    have hev : f =ᶠ[𝓝 (L s)] fun y => ψ (Ls y) := by
      have hq : Tendsto q (𝓝 (L s)) (𝓝 0) := by
        have := q.continuous.tendsto (L s)
        rwa [hqL] at this
      filter_upwards [hq (closedBall_mem_nhds 0 (by positivity : (0:ℝ) < δ / 2))] with y hy
      rw [hfapp, χ.one_of_mem_closedBall hy, mul_one]
    show fderiv ℝ f (L s) (τ j) = _
    rw [hev.fderiv_eq]
    change fderiv ℝ (ψ ∘ Ls) (L s) (τ j) = _
    have hψd : DifferentiableAt ℝ ψ (Ls (L s)) := (hψ.differentiable (by simp)).differentiableAt
    rw [fderiv_comp (L s) hψd Ls.differentiableAt, ContinuousLinearMap.fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hLsτ, hLsL]
/-- **Simon Ch. 3, Definition 1.4 and Remark 1.5(1)**: an approximate tangent space of `M` at `x`
lies in every subspace `T` along which a set `N` carrying `Hⁿ`-almost all of `M` is flat at `x`
(for each `ε > 0` there is `ρ > 0` such that every `z ∈ N` with `|z − x| < ρ` has some `t ∈ T`
with `|z − x − t| ≤ ε|z − x|`).  If `q ∈ Q \ T`, put `δ = dist(q, T) > 0` and
`g = max(0, δ/2 − |· − q|) ∈ C_c(ℝᴾ)`; `∫_Q g dHⁿ > 0` because `spt(Hⁿ⌞Q) = Q`.  With
`ε = δ / (2(|q| + δ))` and `0 < r < ρ / (|q| + δ)`, flatness makes `g` vanish on `η_{x,r}(M ∩ N)`,
and `Hⁿ(η_{x,r}(M \ N)) = 0`; so `∫_{η_{x,r}(M)} g dHⁿ = 0` for all small `r`, contradicting
the defining limit. -/
theorem Submission.atsm_approxTangent_le_of_flat : ∀ (P n : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q T : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z x < ρ → ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → HasApproximateTangentSpaceAt n M x Q → Q ≤ T := by
  intro P n N M x Q T hnull hflat hQ q hq
  by_contra hqT
  -- `T` is closed, so `δ = dist(q, T) > 0`
  have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
  have hδ : 0 < infDist q (T : Set (Euclid P)) :=
    (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
  set δ := infDist q (T : Set (Euclid P)) with hδdef
  -- the bump `g = max(0, δ/2 − |· − q|)`, positive exactly on `B_{δ/2}(q)`
  set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg0 : 0 ≤ g := fun y => le_max_left _ _
  have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
    intro y hy
    by_contra h
    have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
    apply hy
    exact max_eq_left (by linarith)
  have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
    lt_max_of_lt_right (by linarith)
  have hgcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
    intro y hy
    by_contra h
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgsupp y h).le
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hgc⟩, hgcs⟩
  -- `∫_Q g dHⁿ > 0`: `Hⁿ⌞Q` is regular with support `Q ∋ q`
  have hQn : Module.finrank ℝ Q = n := hQ.1
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
  have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
  have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    hgc.integrable_of_hasCompactSupport hgcs
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
      rw [hsupp]
      exact hq
    have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
        (ball q (δ / 2)) :=
      (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
    refine hball.trans_le (measure_mono ?_)
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (hgpos y hy).ne'
  -- constants: `ε (|q| + δ) = δ / 2`
  have hqδ : 0 < ‖q‖ + δ := by positivity
  set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεq : ε * (‖q‖ + δ) = δ / 2 := by
    rw [hεdef]
    field_simp
  obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
  -- `∫_{η_{x,r}(M)} g dHⁿ = 0` for `0 < r < ρ / (|q| + δ)`
  have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = 0 := by
    intro r hr hrρ
    -- `η_{x,r}(M \ N) = r⁻¹ (M \ N − x)` is `Hⁿ`-null
    have hnull' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N)) = 0 := by
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) =
          (fun y => r⁻¹ • y) '' ((fun y => y - x) '' (M \ N)) := by
        rw [Set.image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq fun a b => dist_sub_right a b x
      rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, hnull, smul_zero]
    -- flatness: `g` vanishes on `η_{x,r}(M ∩ N)`
    have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) := by
      rintro y ⟨hgy, z, hzM, rfl⟩
      refine ⟨z, ⟨hzM, fun hzN => ?_⟩, rfl⟩
      have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
      set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
      have hy' : y = r⁻¹ • (z - x) := rfl
      have hzx : z - x = r • y := by
        rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
        calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
          _ < δ / 2 + ‖q‖ := by linarith
          _ = ‖q‖ + δ / 2 := by ring
      have hzxn : ‖z - x‖ = r * ‖y‖ := by
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
      have hdist : dist z x < ρ := by
        rw [dist_eq_norm, hzxn]
        calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
          _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
          _ = ρ := by field_simp
      obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
      have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
      have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
        rw [hy']
        exact (smul_sub _ _ _).symm
      have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
        rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
          _ = ε * ‖y‖ := by rw [hzxn]; field_simp
      have hle : δ ≤ ‖q - r⁻¹ • t‖ := by
        rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hrt
      have h2 : ε * ‖y‖ ≤ δ / 2 := by
        rw [← hεq]
        gcongr
        linarith
      have hlt : ‖q - r⁻¹ • t‖ < δ := by
        calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
          _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := by
            have h1 : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
            linarith
          _ = δ := by ring
      linarith
    -- so `g = 0` a.e. for `Hⁿ⌞η_{x,r}(M)`, evaluated on the open set `{g ≠ 0}`
    have hopen : MeasurableSet {y | g y ≠ 0} :=
      (isOpen_ne_fun hgc continuous_const).measurableSet
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_iff]
    change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) {y | g y ≠ 0} = 0
    rw [Measure.restrict_apply hopen]
    exact measure_mono_null hsub hnull'
  -- the blow-up integrals of `g` are eventually `0`, so their limit `∫_Q g dHⁿ` is `0`
  have hlim := hQ.2 f
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n])
      =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
    exact hvan r hr.1 hr.2
  have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have heq := tendsto_nhds_unique hlim hlim0
  have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
  linarith
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
/-- **An `L¹` pairing that vanishes on uniform approximants vanishes in the limit** (step 5 of the
extension from smooth to `C¹` tests in the graph-cycle regularity step of Simon 7.4.3).  Let
`K ⊆ ℝⁿ` be measurable, `G` integrable on `K` and `f` AE-strongly measurable with `|f| ≤ C` on `K`.
If for every `ε > 0` some AE-strongly measurable `g` with `|f − g| ≤ ε` on `K` has `∫_K G g = 0`,
then `∫_K G f = 0`: `|g| ≤ C + ε` on `K`, so both products are integrable on `K`, and
`|∫_K G f| = |∫_K G (f − g)| ≤ ε ∫_K |G|` for every `ε > 0`. -/
theorem Submission.dgcr_stc_setIntegral_mul_eq_zero_of_uniform_approx : ∀ (n : ℕ) (K : Set (Euclid n)) (G f : Euclid n → ℝ) (C : ℝ), MeasurableSet K → IntegrableOn G K volume → AEStronglyMeasurable f (volume.restrict K) → (∀ x ∈ K, |f x| ≤ C) → (∀ ε : ℝ, 0 < ε → ∃ g : Euclid n → ℝ, AEStronglyMeasurable g (volume.restrict K) ∧ (∀ x ∈ K, |f x - g x| ≤ ε) ∧ ∫ x in K, G x * g x = 0) → ∫ x in K, G x * f x = 0 := by
  intro n K G f C hK hG hf hfC happrox
  -- `M = ∫_K |G| ≥ 0`, and `G f` is integrable on `K` since `|f| ≤ C` on `K`.
  have hM : 0 ≤ ∫ x in K, |G x| := integral_nonneg fun x => abs_nonneg (G x)
  have hGf : Integrable (fun x => G x * f x) (volume.restrict K) :=
    Integrable.mul_bdd hG hf (ae_restrict_of_forall_mem hK fun x hx => hfC x hx)
  -- `|∫_K G f| ≤ ε M` for every `ε > 0`.
  have hbound : ∀ ε : ℝ, 0 < ε → |∫ x in K, G x * f x| ≤ ε * ∫ x in K, |G x| := by
    intro ε hε
    obtain ⟨g, hg, hfg, hGg⟩ := happrox ε hε
    -- `|g| ≤ |f| + |f − g| ≤ C + ε` on `K`, so `G g` is integrable on `K`.
    have hGg_int : Integrable (fun x => G x * g x) (volume.restrict K) :=
      Integrable.mul_bdd (c := C + ε) hG hg (ae_restrict_of_forall_mem hK fun x hx => by
        have h1 := abs_le.mp (hfC x hx)
        have h2 := abs_le.mp (hfg x hx)
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩)
    -- `∫_K G f = ∫_K G f − ∫_K G g = ∫_K G (f − g)`.
    have heq : ∫ x in K, G x * f x = ∫ x in K, G x * (f x - g x) := by
      simp_rw [mul_sub]
      rw [integral_sub hGf hGg_int, hGg, sub_zero]
    -- `|G (f − g)| ≤ |G| ε` on `K`.
    rw [heq]
    calc |∫ x in K, G x * (f x - g x)| ≤ ∫ x in K, |G x| * ε :=
          norm_integral_le_of_norm_le ((Integrable.abs hG).mul_const ε)
            (ae_restrict_of_forall_mem hK fun x hx => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul_of_nonneg_left (hfg x hx) (abs_nonneg _))
      _ = ε * ∫ x in K, |G x| := by rw [integral_mul_const, mul_comm]
  -- If `a = |∫_K G f| > 0`, then `ε = a / (2(M + 1))` gives `a ≤ a M / (2(M + 1)) < a`.
  by_contra hne
  set M := ∫ x in K, |G x|
  set a := |∫ x in K, G x * f x|
  have ha : 0 < a := abs_pos.mpr hne
  have hpos : 0 < 2 * (M + 1) := by linarith
  have h := hbound (a / (2 * (M + 1))) (div_pos ha hpos)
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos] at h
  nlinarith
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
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'

/-- Orientation step of the constancy theorem for an integer multiplicity current carried by an
`n`-plane (Simon Ch. 3, Definition 1.4; Ch. 6, 3.1): if `Hⁿ(M \ Q) = 0` for the plane
`Q = span{τ₁, …, τₙ}` of an orthonormal family `τ`, then `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for `Hⁿ`-a.e.
`x ∈ M`.  For `Hⁿ⌞M`-a.e. `x` we have `x ∈ Q` and an approximate tangent space `Qₓ` oriented by
`ξ(x)`; `Q` is trivially flat at `x` along `Q`, so `Qₓ ≤ Q`, hence `Qₓ = Q` as both have dimension
`n`; then `ξ(x)` and `α ↦ α(τ)` are unit orientations of the same plane, so they agree up to
sign. -/
theorem Submission.idtp_pc_orient_ae_eq_or_neg : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → μHE[n] (R.carrier \ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) = 0 → ∀ᵐ x ∂(μHE[n].restrict R.carrier), (∀ α : Covector (Euclid P) n, R.orient x α = α τ) ∨ (∀ α : Covector (Euclid P) n, R.orient x α = -α τ) := by
  intro P n U R τ hτ hnull
  set Q : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range τ) with hQ
  have hfin : Module.finrank ℝ Q = n := by
    rw [hQ, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- `ξ_Q = τ₁ ∧ ⋯ ∧ τₙ`, i.e. `α ↦ α(τ)`, is a unit orientation of `Q`
  let ξQ : MultiVector P n :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclid P) ℝ τ).comp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have hξQ : ∀ α : Covector (Euclid P) n, ξQ α = α τ := fun α => rfl
  have hξQo : IsUnitOrientationOf ξQ Q := ⟨τ, hτ, rfl, Or.inl hξQ⟩
  -- `Hⁿ⌞M`-almost every point lies in `Q`
  have hmemQ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ (Q : Set (Euclid P)) := by
    rw [ae_restrict_iff' R.measurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxM
    by_contra h
    exact hx ⟨hxM, h⟩
  filter_upwards [R.orients, hmemQ] with x hx hxQ
  obtain ⟨Qx, htan, hor⟩ := hx
  -- `Q` is flat at `x ∈ Q` along `Q`, so `Qₓ ≤ Q`, and `Qₓ = Q` by dimension
  have hflat : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ (Q : Set (Euclid P)), dist z x < ρ →
      ∃ t ∈ Q, ‖z - x - t‖ ≤ ε * ‖z - x‖ := by
    intro ε hε
    refine ⟨1, one_pos, fun z hz _ => ⟨z - x, Q.sub_mem hz hxQ, ?_⟩⟩
    simp only [sub_self, norm_zero]
    positivity
  have hle : Qx ≤ Q :=
    Submission.atsm_approxTangent_le_of_flat P n Q R.carrier x Qx Q hnull hflat htan
  have heq : Qx = Q := Submodule.eq_of_le_of_finrank_eq hle (htan.1.trans hfin.symm)
  rw [heq] at hor
  -- two unit orientations of `Q` agree up to sign
  rcases Submission.dgcr_unitOrientation_eq_or_neg P n Q ξQ (R.orient x) hξQo hor with h | h
  · left; intro α; rw [h]; exact hξQ α
  · right; intro α; rw [h]; rfl
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero
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
/-- **Simon Ch. 6, 1.2 (p. 132)**: `Λⁿ(ℝᴾ)` is finite-dimensional.  An `n`-covector `α` is
determined by its values `α(e_{I(1)}, …, e_{I(n)})` on tuples of standard basis vectors
(alternating maps agreeing on distinct basis vectors are equal), so
`Φ α = (α(e ∘ I))_{I : Fin n → Fin P}` is an injective linear map into the finite-dimensional
space `ℝ^(Fin n → Fin P)`. -/
theorem Submission.lcn_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `Φ α = (α(e ∘ I))_I`, linear since addition and scaling of covectors are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α I => α fun i => e (I i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `Φ α = Φ β` makes `α` and `β` agree on distinct basis vectors, hence everywhere
  refine FiniteDimensional.of_injective Φ fun α β h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)

/-- **Simon Ch. 6, 3.1 (‡)**: for an integer multiplicity triple `(M, θ, ξ)` in `U`, a compact
`K ⊆ U` and an `n`-covector `α`, the component `θ ⟨α, ξ⟩` is `Hⁿ`-integrable on `M ∩ K`.  `θ` is
locally `Hⁿ`-integrable, and `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, so `‖ξ‖ ≤ 1` and
`|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ`, an integrable majorant on `M ∩ K`. -/
theorem Submission.lcn_mult_mul_orient_apply_integrableOn : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → ∀ α : Covector (Euclid P) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x α) (R.carrier ∩ K) μHE[n] := by
  intro P n U K R hK hKU α
  -- `μ := Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`
  have hμ : μHE[n].restrict (R.carrier ∩ K) ≤ μHE[n].restrict R.carrier :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- `θ` is `μ`-integrable, as `∫⁻_{M ∩ K} θ dHⁿ < ∞`; hence so is `‖α‖ θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hmaj : Integrable (fun x => ‖α‖ * (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
    simpa using (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
      (R.locallyIntegrable_mult K hK hKU)).const_mul ‖α‖
  -- `‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e., hence `μ`-a.e.
  have hξ : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ K)), ‖R.orient x‖ ≤ 1 := by
    refine ae_mono hμ ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `θ ⟨α, ξ⟩` is `μ`-a.e. strongly measurable: `ξ` is, and evaluation at `α` is continuous
  have hm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ K)) := by
    have hξα : AEStronglyMeasurable (fun x => R.orient x α) (μHE[n].restrict (R.carrier ∩ K)) :=
      (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_measure hμ)
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul hξα
  -- domination: `|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ` `μ`-a.e.
  refine hmaj.mono' hm ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (R.mult x : ℝ) * |R.orient x α| ≤ (R.mult x : ℝ) * (‖R.orient x‖ * ‖α‖) := by
        gcongr
        exact (Real.norm_eq_abs _).symm.trans_le ((R.orient x).le_opNorm α)
    _ ≤ (R.mult x : ℝ) * (1 * ‖α‖) := by gcongr
    _ = ‖α‖ * R.mult x := by ring

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then for every
`n`-covector `α`, `⟨α, ξ⟩ = 0` `Hⁿ`-a.e. on `M ∩ W`.  Let `ν = Hⁿ⌞(M ∩ closure W)`; then
`f = θ ⟨α, ξ⟩` is `ν`-integrable (`lcn_mult_mul_orient_apply_integrableOn`, `closure W` being a
compact subset of `U`).  For smooth `g` with compact support in `W`, `ω = g α` is a test form in
`U` supported in `W`, so `0 = T(ω) = ∫_M θ ⟨g α, ξ⟩ dHⁿ = ∫ g f dν` (`g = 0` off `W`).  The
fundamental lemma of the calculus of variations on `W` gives `f = 0` `ν`-a.e. on `W`; as
`Hⁿ⌞(M ∩ W) ≤ ν` and `θ > 0` on `M`, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. -/
theorem Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW α
  -- `f = θ ⟨α, ξ⟩` is integrable for `ν = Hⁿ⌞(M ∩ closure W)`
  have hf : Integrable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ closure W)) :=
    Submission.lcn_mult_mul_orient_apply_integrableOn P n U (closure W) R hWc hWU α
  -- fundamental lemma on the open set `W`: `f = 0` `ν`-a.e. on `W`
  have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ closure W)), x ∈ W →
      (R.mult x : ℝ) * R.orient x α = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrable.locallyIntegrableOn W) fun g hg hgc hgW => ?_
    -- `ω = g α` is a test form in `U` supported in `W`, so `T(ω) = 0`
    have hωW : tsupport (fun x => g x • α) ⊆ W := (tsupport_smul_subset_left g _).trans hgW
    have hω : (fun x => g x • α) ∈ TestFormOn U n :=
      ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, hωW.trans (subset_closure.trans hWU)⟩
    calc ∫ x, g x • ((R.mult x : ℝ) * R.orient x α) ∂(μHE[n].restrict (R.carrier ∩ closure W))
        = ∫ x in R.carrier ∩ closure W, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          congr 1
          funext x
          rw [map_smul, smul_eq_mul, smul_eq_mul]
          ring
      -- `g = 0` off `closure W`, so the integral over `M` is the integral over `M ∩ closure W`
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
            inter_subset_left fun x hx => ?_).symm
          have hgx : g x = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, subset_closure (hgW h)⟩
          rw [hgx, zero_smul, map_zero, mul_zero]
      _ = T ⟨_, hω⟩ := (hRT ⟨_, hω⟩).symm
      _ = 0 := hTW ⟨_, hω⟩ hωW
  -- pass to `Hⁿ⌞(M ∩ W) ≤ ν` and cancel `θ > 0` on `M`
  have hle : μHE[n].restrict (R.carrier ∩ W) ≤ μHE[n].restrict (R.carrier ∩ closure W) :=
    Measure.restrict_mono (inter_subset_inter_right _ subset_closure) le_rfl
  filter_upwards [ae_mono hle hae,
    ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)] with x hx hxMW
  have hθ : (R.mult x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (R.mult_pos x hxMW.1).ne'
  exact (mul_eq_zero.mp (hx hxMW.2)).resolve_left hθ

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then
`Hⁿ(M ∩ W) = 0`.  `Λⁿ` is finite-dimensional (`lcn_covector_finiteDimensional`); for each `α` of
a basis, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. (`lcn_orient_apply_ae_eq_zero_of_vanishesOn`), so
`ξ = 0` `Hⁿ⌞(M ∩ W)`-a.e.  But `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, hence nonzero
(`imsupp_unit_orientation_ne_zero_norm_le_one`), so `Hⁿ⌞(M ∩ W) = 0`. -/
theorem Submission.imrep_carrier_inter_null_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μHE[n] (R.carrier ∩ W) = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW
  -- a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ`
  have := Submission.lcn_covector_finiteDimensional P n
  let b := Module.finBasis ℝ (Covector (Euclid P) n)
  -- `⟨αₖ, ξ⟩ = 0` for every `k`, `Hⁿ⌞(M ∩ W)`-a.e.
  have h0 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ k, R.orient x (b k) = 0 :=
    ae_all_iff.mpr fun k =>
      Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn P n U W T R hRT hW hWc hWU hTW (b k)
  -- `ξ ≠ 0` `Hⁿ⌞M`-a.e., hence `Hⁿ⌞(M ∩ W)`-a.e.
  have h1 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x ≠ 0 := by
    refine ae_mono (Measure.restrict_mono inter_subset_left le_rfl) ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).1
  -- a functional on `Λⁿ` vanishing on a basis is zero, so `Hⁿ⌞(M ∩ W)`-a.e. `x` is impossible
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), False := by
    filter_upwards [h0, h1] with x hx hne
    exact hne (ContinuousLinearMap.coe_injective (b.ext fun k => hx k))
  exact Measure.restrict_eq_zero.mp (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp h2))

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` in `U`, then `Hⁿ(M ∖ spt T) = 0`, i.e.
`μ_T(U ∖ spt T) = 0`.  As `M ⊆ U` and `spt T = U ∖ Z`, `M ∖ spt T ⊆ M ∩ Z`, where the zero region
`Z = ⋃ 𝒲` is the union of the open `W ⊂⊂ U` on which `T` vanishes.  `ℝᴾ` is second countable, so
`Z = ⋃_{W ∈ 𝒮} W` for a countable `𝒮 ⊆ 𝒲`; each `Hⁿ(M ∩ W) = 0`
(`imrep_carrier_inter_null_of_vanishesOn`), and countable subadditivity concludes. -/
theorem Submission.imrep_carrier_sdiff_support_null : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → μHE[n] (R.carrier \ T.support) = 0 := by
  intro P n U T R _ hRT
  -- the zero region `Z = ⋃₀ 𝒲` is the union of a countable subfamily `𝒮 ⊆ 𝒲`
  obtain ⟨𝒮, h𝒮c, h𝒮W, h𝒮⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Euclid P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- `M ∖ spt T ⊆ ⋃_{W ∈ 𝒮} M ∩ W`: a point of `M ⊆ U` outside `spt T = U ∖ Z` lies in `Z`
  have hsub : R.carrier \ T.support ⊆ ⋃ W ∈ 𝒮, R.carrier ∩ W := by
    rintro x ⟨hxM, hxS⟩
    have hxZ : x ∈ ⋃₀ 𝒮 := by
      rw [h𝒮]
      by_contra hxZ
      exact hxS (mem_sdiff_of_mem (R.carrier_subset hxM) hxZ)
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxZ
    exact mem_biUnion hW ⟨hxM, hxW⟩
  -- `Hⁿ(M ∩ W) = 0` for each of the countably many `W ∈ 𝒮`
  refine measure_mono_null hsub ((measure_biUnion_null_iff h𝒮c).mpr fun W hW => ?_)
  obtain ⟨hWo, hWc, hWU, hTW⟩ := h𝒮W hW
  exact Submission.imrep_carrier_inter_null_of_vanishesOn P n U W T R hRT hWo hWc hWU hTW

/-- **Simon Ch. 6, 3.1, 3.2(3) and 2.34** (chapter-06.txt lines 569–604 and 733–768; the
constancy step of 7.3.2(1) and 7.3.3, chapter-07.txt lines 311–314 and 504–507): an integer
multiplicity `S = τ(M, θ, ξ) ∈ 𝒟ₙ(V)` with `spt S ⊆ Q = span{τ₁, …, τₙ}` (`τ` orthonormal) is
`g[[Q]]` for an integer density `g`, i.e. `S(ω) = ∫_{V∩Q} g ⟨ω, τ₁ ∧ ⋯ ∧ τₙ⟩ dHⁿ` and
`M_W(S) = ∫_{W∩Q} |g| dHⁿ` for open `W ⊆ V`.  `Hⁿ(M ∖ Q) ≤ Hⁿ(M ∖ spt S) = 0`
(`imrep_carrier_sdiff_support_null`), so `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` `Hⁿ`-a.e. on `M`
(`idtp_pc_orient_ae_eq_or_neg`).  The sign is `ε = ⟨β₀, ξ⟩` for the covector
`β₀(w) = det(⟨τᵢ, wⱼ⟩)`, which has `β₀(τ) = 1`, and `g = 1_M θ ε`.  Then `θ⟨ω, ξ⟩ = g ω(τ)` and
`|g| = 1_M θ` `Hⁿ`-a.e., while `M_W(S) = μ_S(W) = ∫_{W∩M} θ dHⁿ` (`dimred_im_mass_measure`). -/
theorem Submission.idtp_pc_signed_density : ∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P), IsOpen V → Orthonormal ℝ τ → IsIntegerMultiplicity S → S.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) → ∃ g : Euclid P → ℝ, AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) ∧ (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) ∧ (∀ ω : TestFormOn V n, S ω = ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → S.massOn W = ∫⁻ x in W ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] := by
  intro P n V S τ hV hτ hS hspt
  obtain ⟨R, hR⟩ := hS
  set Q : Set (Euclid P) := (Submodule.span ℝ (Set.range τ) : Set (Euclid P))
  have hQm : MeasurableSet Q := (Submodule.closed_of_finiteDimensional _).measurableSet
  have hMm : MeasurableSet R.carrier := R.measurableSet_carrier
  -- `Hⁿ(M ∖ Q) ≤ Hⁿ(M ∖ spt S) = 0`, as `spt S ⊆ Q`
  have hnull : μHE[n] (R.carrier \ Q) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hspt)
      (Submission.imrep_carrier_sdiff_support_null P n V S R hV hR)
  -- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` `Hⁿ`-a.e. on `M`
  have hor := Submission.idtp_pc_orient_ae_eq_or_neg P n V R τ hτ hnull
  -- the covector `β₀(w) = δ(Ls w₁, …, Ls wₙ) = det(⟨τᵢ, wⱼ⟩)`, `δ` the determinant of `ℝⁿ`,
  -- `Ls w = (⟨τₖ, w⟩)ₖ`; `Ls τᵢ = eᵢ`, so `β₀(τ) = 1`
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : Covector (Euclid P) n, β₀ τ = 1 := by
    classical
    let b : Module.Basis (Fin n) ℝ (Euclid n) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    have hdet : ∀ c : Fin n → Euclid n, b.det c = (Matrix.of fun r l => c l r).det := by
      intro c
      rw [Module.Basis.det_apply]
      congr 1
    have hcont : Continuous (fun c : Fin n → Euclid n => b.det c) := by
      simp only [hdet]
      apply Continuous.matrix_det
      refine continuous_matrix fun r l => ?_
      exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
    let δ : Covector (Euclid n) n := { b.det with cont := hcont }
    let Ls₀ : Euclid P →ₗ[ℝ] Euclid n :=
      { toFun := fun y => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => inner ℝ (τ k) y)
        map_add' := fun y z => by ext k; simp [inner_add_right]
        map_smul' := fun c y => by ext k; simp [inner_smul_right] }
    let Ls : Euclid P →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap Ls₀
    have hLsτ : ∀ i, Ls (τ i) = b i := by
      intro i
      ext k
      simp [Ls, Ls₀, b, orthonormal_iff_ite.mp hτ, eq_comm]
    refine ⟨δ.compContinuousLinearMap Ls, ?_⟩
    show δ (fun i => Ls (τ i)) = 1
    simp only [hLsτ]
    exact b.det_self
  -- the sign `ε = ⟨β₀, ξ⟩` and the signed density `g = 1_M θ ε`
  set ε : Euclid P → ℝ := fun x => R.orient x β₀
  have hεm : AEStronglyMeasurable ε (μHE[n].restrict R.carrier) :=
    (ContinuousLinearMap.apply ℝ ℝ β₀).continuous.comp_aestronglyMeasurable
      R.aestronglyMeasurable_orient
  set g : Euclid P → ℝ := R.carrier.indicator (fun x => (R.mult x : ℝ) * ε x)
  -- `Hⁿ`-a.e. on `M`: `ε = ±1` and `ξ = ε τ₁ ∧ ⋯ ∧ τₙ`
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      (ε x = 1 ∨ ε x = -1) ∧ ∀ α : Covector (Euclid P) n, R.orient x α = ε x * α τ := by
    filter_upwards [hor] with x hx
    rcases hx with h | h
    · exact ⟨Or.inl (by simp [ε, h, hβ₀]), fun α => by simp [ε, h, hβ₀]⟩
    · exact ⟨Or.inr (by simp [ε, h, hβ₀]), fun α => by simp [ε, h, hβ₀]⟩
  have hgood' : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier →
      ((ε x = 1 ∨ ε x = -1) ∧ ∀ α : Covector (Euclid P) n, R.orient x α = ε x * α τ) :=
    (ae_restrict_iff' hMm).mp hgood
  -- `g = ±θ ∈ ℤ` on `M` and `g = 0` off `M`, so `g ∈ ℤ` and `|g| = 1_M θ` `Hⁿ`-a.e.
  have hgint : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∃ m : ℤ, g x = m := by
    filter_upwards [hgood'] with x hx
    by_cases hxM : x ∈ R.carrier
    · rcases (hx hxM).1 with h1 | h1
      · exact ⟨R.mult x, by simp [g, hxM, h1]⟩
      · exact ⟨-(R.mult x : ℤ), by simp [g, hxM, h1]⟩
    · exact ⟨0, by simp [g, hxM]⟩
  have hgabs : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)),
      ‖g x‖ₑ = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
    filter_upwards [hgood'] with x hx
    by_cases hxM : x ∈ R.carrier
    · rcases (hx hxM).1 with h1 | h1
      · simp [g, hxM, h1]
      · simp [g, hxM, h1]
    · simp [g, hxM]
  have hnullae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ R.carrier \ Q :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  refine ⟨g, ?_, ae_restrict_of_ae hgint, ?_, ?_, ?_⟩
  · -- (i) `θε` is a.e.-strongly measurable on `M`, and `g` is its extension by `0`
    have hθm : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) :=
      ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp
        R.measurable_mult).aestronglyMeasurable
    have : AEStronglyMeasurable g (μHE[n] : Measure (Euclid P)) :=
      (aestronglyMeasurable_indicator_iff hMm).mpr (hθm.mul hεm)
    exact this.restrict
  · -- (iii) `∫_{K∩Q} |g| ≤ ∫_K 1_M θ = ∫_{M∩K} θ < ∞`
    intro K hK hKV
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKV) ?_
    calc ∫⁻ x in K ∩ Q, ‖g x‖ₑ ∂μHE[n] ≤ ∫⁻ x in K, ‖g x‖ₑ ∂μHE[n] :=
          lintegral_mono_set inter_subset_left
      _ = ∫⁻ x in K, R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x ∂μHE[n] :=
          lintegral_congr_ae (ae_restrict_of_ae hgabs)
      _ = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
          rw [lintegral_indicator hMm, Measure.restrict_restrict hMm]
  · -- (iv) `1_M θ⟨ω, ξ⟩ = 1_{V∩Q} g ω(τ)` `Hⁿ`-a.e.: both vanish off `M`, and a.e. `x ∈ M`
    -- lies in `V ∩ Q`
    intro ω
    rw [hR ω, IMRep.action, ← integral_indicator hMm,
      ← integral_indicator (hV.measurableSet.inter hQm)]
    refine integral_congr_ae ?_
    filter_upwards [hgood', hnullae] with x hx hxn
    by_cases hxM : x ∈ R.carrier
    · have hxQ : x ∈ Q := by
        by_contra h
        exact hxn ⟨hxM, h⟩
      have hxVQ : x ∈ V ∩ Q := ⟨R.carrier_subset hxM, hxQ⟩
      rw [indicator_of_mem hxM, indicator_of_mem hxVQ, (hx hxM).2]
      simp only [g, indicator_of_mem hxM]
      ring
    · by_cases hxVQ : x ∈ V ∩ Q
      · rw [indicator_of_notMem hxM, indicator_of_mem hxVQ]
        simp [g, hxM]
      · rw [indicator_of_notMem hxM, indicator_of_notMem hxVQ]
  · -- (v) `M_W(S) = μ_S(W) = ∫_{W∩M} θ = ∫_W |g| = ∫_{W∩Q} |g|`, as `g = 0` a.e. on `W ∖ Q`
    intro W hW hWV
    rw [(Submission.dimred_im_mass_measure P n V S R hV hR).1 W hW hWV, IMRep.measure,
      withDensity_apply _ hW.measurableSet, Measure.restrict_restrict hW.measurableSet]
    have hzero : ∫⁻ x in W \ Q, ‖g x‖ₑ ∂μHE[n] = 0 := by
      have h0 : ∀ᵐ x ∂(μHE[n].restrict (W \ Q)), ‖g x‖ₑ = 0 := by
        rw [ae_restrict_iff' (hW.measurableSet.diff hQm)]
        filter_upwards [hnullae] with x hxn hxWQ
        have hxM : x ∉ R.carrier := fun hxM => hxn ⟨hxM, hxWQ.2⟩
        simp [g, hxM]
      rw [lintegral_congr_ae h0, lintegral_zero]
    calc ∫⁻ a in W ∩ R.carrier, (R.mult a : ℝ≥0∞) ∂μHE[n]
        = ∫⁻ x in W, R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x ∂μHE[n] := by
          rw [lintegral_indicator hMm, Measure.restrict_restrict hMm, inter_comm]
      _ = ∫⁻ x in W, ‖g x‖ₑ ∂μHE[n] := (lintegral_congr_ae (ae_restrict_of_ae hgabs)).symm
      _ = ∫⁻ x in W ∩ Q, ‖g x‖ₑ ∂μHE[n] := by
          rw [← lintegral_inter_add_sdiff (fun x => ‖g x‖ₑ) W hQm, hzero, add_zero]
/-- **The coordinate covector `eⱼ ⌟ δ` on `ℝ^{m+1}`** (step 2 of the boundary weak-derivative
computation in the graph-cycle regularity step of Simon 7.4.3).  For `j ∈ Fin (m + 1)` there is a
continuous alternating `m`-form `β` on `ℝ^{m+1}` with `β(e₀, …, êᵢ, …, e_m) = (−1)ʲ` if `i = j`
and `0` otherwise: `β(w₁, …, w_m) = δ(eⱼ, w₁, …, w_m)` for the standard determinant form `δ`. -/
theorem Submission.dgcr_bwd_coordinate_covector : ∀ (m : ℕ) (j : Fin (m + 1)), ∃ β : Covector (Euclid (m + 1)) m, ∀ i : Fin (m + 1), β (i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ))) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0 := by
  intro m j
  classical
  -- The standard basis `b l = e_l` and its determinant `δ₀ c = det (c l r)_{r,l}`.
  let b : Module.Basis (Fin (m + 1)) ℝ (Euclid (m + 1)) :=
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  have hb : (b : Fin (m + 1) → Euclid (m + 1)) = fun l => EuclideanSpace.single l (1 : ℝ) := by
    funext l; simp [b]
  have hdet : ∀ c : Fin (m + 1) → Euclid (m + 1), b.det c = (Matrix.of fun r l => c l r).det := by
    intro c
    rw [Module.Basis.det_apply]
    congr 1
  -- `δ₀` is continuous (entrywise continuous matrix, then `det`), so it is a covector `δ`.
  have hcont : Continuous (fun c : Fin (m + 1) → Euclid (m + 1) => b.det c) := by
    simp only [hdet]
    apply Continuous.matrix_det
    refine continuous_matrix fun r l => ?_
    exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
  let δ : Covector (Euclid (m + 1)) (m + 1) := { b.det with cont := hcont }
  have hδ : ∀ c, δ c = b.det c := fun c => rfl
  -- `β = δ.curryLeft (b j)`, i.e. `β w = δ (b j, w₁, …, w_m)`.
  refine ⟨δ.curryLeft (b j), fun i => ?_⟩
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, hδ, ← hb]
  split_ifs with hij
  · -- `i = j`: `(b i, removeNth i b) = b ∘ (cycleRange i)⁻¹`, of sign `(−1)ⁱ`.
    subst hij
    have hc : (Matrix.vecCons (b i) (i.removeNth ⇑b) : Fin (m + 1) → Euclid (m + 1)) =
        ⇑b ∘ ⇑(Equiv.symm i.cycleRange) :=
      Fin.cons_removeNth_eq_comp_cycleRange_symm (⇑b) i
    rw [hc, AlternatingMap.map_perm, Module.Basis.det_self, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp [Units.smul_def]
  · -- `i ≠ j`: `e_j` occurs at positions `0` and `l.succ`, where `i.succAbove l = j`.
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := l.succ)
    · simp [Fin.removeNth_apply, hl]
    · exact (Fin.succ_ne_zero l).symm
/-- **Vanishing boundary gives the ambient weak-derivative identity** (the zero weak derivatives
step of the planar constancy argument, after Simon 6.2.34).  Let `∂S = 0` in `V` and
`S(ω) = ∫_{V ∩ Q} g(x) ω(x)(τ₁, …, τₙ) dHⁿ(x)` for an orthonormal family `τ` with `Q = span τ`.
Then `∫_{V ∩ Q} g · D_{τⱼ} f dHⁿ = 0` for every smooth compactly supported `f` with
`spt f ⊆ V`: test `∂S = 0` against `φ = f · α`, where `α(w) = β(⟨τ, w⟩)` pulls back the
coordinate covector `β = eⱼ ⌟ δ`, so that `dφ(x)(τ) = Df(x)(τⱼ)`. -/
theorem Submission.idtp_pc_boundary_weak_derivative : ∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), 1 ≤ n → Orthonormal ℝ τ → BoundaryVanishes S → (∀ ω : TestFormOn V n, S ω = ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) → ∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0 := by
  intro P n V S τ g hn hτ hbd hrep f hf hfc hfV j
  -- Degree: `n = m + 1`, so `BoundaryVanishes S` is `∂S = 0`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hbd' : S.boundary = 0 := hbd
  -- The coordinate covector `β` on `ℝ^{m+1}` and its pullback `α` by `y ↦ (⟨τₖ, y⟩)ₖ`.
  obtain ⟨β, hβ⟩ := Submission.dgcr_bwd_coordinate_covector m j
  let Ls₀ : Euclid P →ₗ[ℝ] Euclid (m + 1) :=
    { toFun := fun y => (WithLp.equiv 2 (Fin (m + 1) → ℝ)).symm (fun k => inner ℝ (τ k) y)
      map_add' := fun y z => by ext k; simp [inner_add_right]
      map_smul' := fun c y => by ext k; simp [inner_smul_right] }
  let Ls : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap Ls₀
  have hLsτ : ∀ i, Ls (τ i) = EuclideanSpace.single i (1 : ℝ) := by
    intro i
    ext k
    simp [Ls, Ls₀, orthonormal_iff_ite.mp hτ, eq_comm]
  let α : Covector (Euclid P) m := β.compContinuousLinearMap Ls
  have hα : ∀ i : Fin (m + 1), α (i.removeNth τ) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0 := by
    intro i
    have : (fun l => Ls (i.removeNth τ l)) =
        i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ)) := by
      funext l
      simp [Fin.removeNth_apply, hLsτ]
    show β (fun l => Ls (i.removeNth τ l)) = _
    rw [this, hβ i]
  -- The test form `φ = f · α ∈ 𝒟^m(V)`.
  let φ : DifferentialForm (Euclid P) m := fun y => f y • α
  have hφtest : IsTestForm φ ∧ tsupport φ ⊆ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hf.smul contDiff_const
    · exact hfc.smul_right
    · exact (tsupport_smul_subset_left _ _).trans hfV
  let φt : TestFormOn V m := ⟨φ, hφtest⟩
  -- `dφ(x)(τ) = Σᵢ (−1)ⁱ Df(x)(τᵢ) α(τ without τᵢ) = Df(x)(τⱼ)`.
  have hd : ∀ x, exteriorDerivative φ x τ = fderiv ℝ f x (τ j) := by
    intro x
    have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply (hfd.smul_const α) τ]
    have h1 : ∀ i : Fin (m + 1),
        (fun y => (f y • α) (i.removeNth τ)) = fun y => f y * α (i.removeNth τ) := by
      intro i; funext y; simp [smul_eq_mul]
    simp only [h1]
    simp only [fderiv_mul_const hfd, hα]
    rw [Finset.sum_eq_single j]
    · simp only [ite_true]
      rw [zsmul_eq_mul]
      push_cast
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    · intro i _ hij
      simp [hij]
    · simp
  -- `0 = ∂S(φ) = S(dφ) = ∫_{V ∩ Q} g · dφ(τ) dHⁿ = ∫_{V ∩ Q} g · D_{τⱼ} f dHⁿ`.
  have h0 : S.boundary φt = 0 := by rw [hbd']; rfl
  rw [GeometricCurrentOn.boundary_apply] at h0
  have h2 := hrep (exteriorDerivativeTestOn V m φt)
  rw [h0] at h2
  rw [h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← hd x]
  rfl
/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

/-- **Mollification approximates a `C¹_c` function in a directional derivative** (step 3 of the
extension from smooth to `C¹` tests in the graph-cycle regularity step of Simon 7.4.3).  For
`φ ∈ C¹_c(ℝⁿ)`, `δ > 0`, a direction `v` and `ε > 0` there is `ψ ∈ C^∞_c(ℝⁿ)` with `spt ψ` in the
closed `δ`-neighbourhood of `spt φ` and `|Dψ(x)v − Dφ(x)v| ≤ ε` for all `x`.  Take `r₀ > 0` with
`|∂ᵥφ(a) − ∂ᵥφ(b)| < ε` when `|a − b| < r₀` (`∂ᵥφ` is continuous with compact support), a
normalized mollifier `ρ` with `spt ρ ⊆ B_r(0)`, `r = min r₀ δ`, and `ψ = ρ ⋆ φ`; then
`∂ᵥψ = ρ ⋆ ∂ᵥφ`, which is within `ε` of `∂ᵥφ`. -/
theorem Submission.dgcr_stc_mollify_C1_fderiv_approx : ∀ (n : ℕ) (φ : Euclid n → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ (δ : ℝ), 0 < δ → ∀ (v : Euclid n) (ε : ℝ), 0 < ε → ∃ ψ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ cthickening δ (tsupport φ) ∧ ∀ x, |fderiv ℝ ψ x v - fderiv ℝ φ x v| ≤ ε := by
  intro n φ hφ hφc δ hδ v ε hε
  -- `∂ᵥφ = Dφ(·) v` is continuous with compact support, hence uniformly continuous: it varies by
  -- less than `ε` on balls of radius `r₀`
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hDφc : HasCompactSupport (fderiv ℝ φ) := hφc.fderiv ℝ
  have hg : Continuous fun x => fderiv ℝ φ x v := hDφ.clm_apply continuous_const
  have hgc : HasCompactSupport fun x => fderiv ℝ φ x v :=
    hDφc.comp_left (g := fun A : Euclid n →L[ℝ] ℝ => A v) rfl
  obtain ⟨r₀, hr₀, hr₀g⟩ :=
    Metric.uniformContinuous_iff.mp (hgc.uniformContinuous_of_continuous hg) ε hε
  -- a normalized mollifier `ρ` with `spt ρ ⊆ B_r(0)`, `r = min r₀ δ`; `ψ = ρ ⋆ φ`
  obtain ⟨ρ, hρ, hρc, hρ0, hρ1, hρs⟩ :=
    Submission.dgcr_stc_exists_normalized_mollifier n (min r₀ δ) (lt_min hr₀ hδ)
  have hρi : LocallyIntegrable ρ volume := hρ.continuous.locallyIntegrable
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  -- `spt ψ ⊆ spt ρ + spt φ ⊆ B_r(0) + spt φ`, inside the closed set `cthickening δ (spt φ)`
  have hsupp : tsupport (convolution ρ φ L volume) ⊆ cthickening δ (tsupport φ) := by
    refine closure_minimal (fun z hz => ?_) isClosed_cthickening
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp (support_convolution_subset L hz)
    refine mem_cthickening_of_dist_le _ b δ _ (subset_tsupport φ hb) ?_
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (mem_ball_zero_iff.mp (hρs ha)).le.trans (min_le_right r₀ δ)
  -- `ψ` is smooth, and compactly supported as `cthickening δ (spt φ)` is compact
  refine ⟨convolution ρ φ L volume,
    hρc.contDiff_convolution_left L hρ hφ.continuous.locallyIntegrable,
    (IsCompact.cthickening hφc).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp, fun x => ?_⟩
  -- `Dψ(x) v = (ρ ⋆ ∂ᵥφ)(x)`
  rw [(hφc.hasFDerivAt_convolution_right L hρi hφ x).fderiv,
    convolution_precompR_apply L hρi hDφc hDφ x v, ← Real.dist_eq]
  -- `ρ ≥ 0`, `∫ ρ = 1`, `spt ρ ⊆ B_r(0)` and `|∂ᵥφ(y) − ∂ᵥφ(x)| < ε` on `B_r(x)`
  exact dist_convolution_le hε.le hρs hρ0 hρ1 hg.aestronglyMeasurable fun y hy =>
    (hr₀g ((mem_ball.mp hy).trans_le (min_le_left r₀ δ))).le

/-- Step 14 of the proof that an integer multiplicity cycle carried by a `C¹` graph is regular
(Simon 7.4.3, via Allard's theorem): weak derivatives tested against `C^∞` functions may be
tested against `C¹` functions.  If `∫_D G ∂ⱼa = 0` for every `a ∈ C_c^∞(D)`, then `∫ G ∂ᵢφ = 0`
for every `φ ∈ C_c¹(D)`.  On the compact set `K = cthickening δ (spt φ) ⊆ D`, `G` is integrable
and `∂ᵢφ` is bounded.  The mollified tests `ψ` satisfy `spt ψ ⊆ K` and `|∂ᵢψ − ∂ᵢφ| ≤ ε`, so
`∫_K G ∂ᵢφ = 0` in the limit; every integrand vanishes off `K`. -/
theorem Submission.dgcr_smooth_tests_to_C1_tests : ∀ (n : ℕ) (D : Set (Euclid n)) (G : Euclid n → ℝ), IsOpen D → LocallyIntegrableOn G D volume → (∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ D → ∀ j : Fin n, ∫ v in D, G v * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0) → ∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∀ i : Fin n, ∫ x, G x * fderiv ℝ φ x ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0 := by
  intro n D G hD hG htest φ hφ hφc hφD i
  rw [EuclideanSpace.basisFun_apply]
  -- step 1: `K = cthickening δ (tsupport φ) ⊆ D` is compact and `G` is integrable on `K`
  obtain ⟨δ, hδ, hKD⟩ := hφc.isCompact.exists_cthickening_subset_open hD hφD
  have hK : IsCompact (cthickening δ (tsupport φ)) := hφc.isCompact.cthickening
  have hGK : IntegrableOn G (cthickening δ (tsupport φ)) volume :=
    hG.integrableOn_compact_subset hKD hK
  -- `G ∂ᵢu` vanishes off `K` when `tsupport u ⊆ K`
  have hvan : ∀ u : Euclid n → ℝ, tsupport u ⊆ cthickening δ (tsupport φ) →
      ∀ x ∉ cthickening δ (tsupport φ), G x * fderiv ℝ u x (EuclideanSpace.single i 1) = 0 :=
    fun u hu x hx => by rw [fderiv_of_notMem_tsupport ℝ fun h => hx (hu h), zero_apply, mul_zero]
  -- step 2: `∂ᵢφ` is continuous, hence bounded on `K`
  have hf : Continuous fun x => fderiv ℝ φ x (EuclideanSpace.single i 1) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  -- step 3: the integral over `ℝⁿ` is the integral over `K`
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (hvan φ (self_subset_cthickening _))]
  -- step 4: smooth tests `ψ` with `tsupport ψ ⊆ K` approximate `∂ᵢφ` uniformly on `K`
  refine Submission.dgcr_stc_setIntegral_mul_eq_zero_of_uniform_approx n
    (cthickening δ (tsupport φ)) G (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) C
    isClosed_cthickening.measurableSet hGK hf.aestronglyMeasurable
    (fun x hx => (Real.norm_eq_abs _).symm.trans_le (hC x hx)) fun ε hε => ?_
  obtain ⟨ψ, hψ, hψc, hψK, hψε⟩ := Submission.dgcr_stc_mollify_C1_fderiv_approx n φ hφ hφc δ hδ
    (EuclideanSpace.single i 1) ε hε
  refine ⟨fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1),
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable,
    fun x _ => (abs_sub_comm _ _).trans_le (hψε x), ?_⟩
  -- `∫_K G ∂ᵢψ = ∫ G ∂ᵢψ = ∫_D G ∂ᵢψ`, which vanishes as `ψ` is a smooth test in `D`
  have hvanD : ∀ x ∉ D, G x * fderiv ℝ ψ x (EuclideanSpace.single i 1) = 0 :=
    fun x hx => hvan ψ hψK x fun h => hx (hKD h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hvan ψ hψK),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hvanD]
  exact htest ψ hψ hψc (hψK.trans hKD) i

/-- **Reduction of the constancy of an integer density on a plane to `ℝⁿ`** (steps 3 and 6–8 of
the planar constancy step in the integer density of tangent planes, Simon 7.3).  Let
`ι(s) = ∑ᵢ sᵢτᵢ` for an orthonormal family `τ`, `Q = span τ`, `Ω = ι⁻¹(V)` and `h = g ∘ ι`.
Since `Hⁿ⌞Q = ι_#Lⁿ` and the isometry `ι` is a measurable embedding, restricted measures,
integrals, a.e. statements and a.e.-measurability transfer between `V ∩ Q` and `Ω`.  So `Ω` is open,
`Ω = ι*(V ∩ Q)` is connected (`ι*(y) = (⟨τₖ, y⟩)ₖ` is a left inverse of `ι`, and `ι ∘ ι* = id` on
`Q`), and `h` is locally integrable on `Ω`.  A smooth test `ψ` in `Ω` extends to a smooth test `f`
in `V` with `D_{τⱼ}f ∘ ι = ∂ⱼψ`, so `∫_Ω h ∂ⱼψ = ∫_{V∩Q} g D_{τⱼ}f dHⁿ = 0`, and `C¹` tests follow.
Finally, if `h = c₀` a.e. on `Ω`, then `c₀ ∈ ℤ` (`h` is integer valued a.e. and `Lⁿ(Ω) > 0`), and
`g = c₀` `Hⁿ`-a.e. on `V ∩ Q`. -/
theorem Submission.idtp_pc_constancy_reduction : ∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), IsOpen V → Orthonormal ℝ τ → IsConnected (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) → (∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0) → IsOpen {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ IsPreconnected {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ LocallyIntegrableOn (fun s : Euclid n => g (∑ i, s i • τ i)) {s : Euclid n | ∑ i, s i • τ i ∈ V} volume ∧ (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∀ i : Fin n, ∫ s, g (∑ k, s k • τ k) * fderiv ℝ φ s ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0) ∧ ∀ c₀ : ℝ, (∀ᵐ s ∂(volume.restrict {s : Euclid n | ∑ i, s i • τ i ∈ V}), g (∑ i, s i • τ i) = c₀) → ∃ c : ℤ, ∀ᵐ x ∂(μHE[n].restrict (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)))), g x = c := by
  intro P n V τ g hV hτ hconn hgm hgint hgloc hweak
  -- the parametrization `ι = L`: a linear isometry, hence a measurable embedding
  let L : Euclid n →ₗ[ℝ] Euclid P :=
    { toFun := fun s => ∑ i, s i • τ i
      map_add' := fun s t => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c s => by simp [Finset.smul_sum, smul_smul] }
  have hLapp : ∀ s, L s = ∑ i, s i • τ i := fun s => rfl
  have hnorm : ∀ s, ‖L s‖ = ‖s‖ := by
    intro s
    have h1 : ‖L s‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [hLapp, ← real_inner_self_eq_norm_sq, hτ.inner_sum, EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      simp [sq]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1
  have hiso : Isometry L := AddMonoidHomClass.isometry_of_norm L hnorm
  have hcont : Continuous L := hiso.continuous
  have hemb : MeasurableEmbedding L := hiso.isClosedEmbedding.measurableEmbedding
  have hinj : Injective L := hiso.injective
  set Q : Set (Euclid P) := (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) with hQ
  -- step 1: `Hⁿ⌞Q = ι_#Lⁿ`, so `Hⁿ⌞(A ∩ Q) = ι_#(Lⁿ⌞ι⁻¹(A))` for measurable `A`
  have hmap : (μHE[n] : Measure (Euclid P)).restrict Q = Measure.map L volume :=
    Submission.idtp_pc_plane_hausdorff_eq_map P n τ hτ
  have htr : ∀ A : Set (Euclid P), MeasurableSet A →
      (μHE[n] : Measure (Euclid P)).restrict (A ∩ Q) =
        Measure.map L (volume.restrict (L ⁻¹' A)) := by
    intro A hA
    rw [← Measure.restrict_restrict hA, hmap, hemb.restrict_map]
  -- step 2: `Ω = ι⁻¹(V)` is open
  set Ω : Set (Euclid n) := {s : Euclid n | ∑ i, s i • τ i ∈ V} with hΩ
  have hΩo : IsOpen Ω := hV.preimage hcont
  -- step 3: the left inverse `ι*(y) = (⟨τₖ, y⟩)ₖ` maps `V ∩ Q` onto `Ω`, so `Ω` is connected
  let Ls : Euclid P → Euclid n :=
    fun y => (WithLp.equiv 2 (Fin n → ℝ)).symm (fun k => inner ℝ (τ k) y)
  have hLscont : Continuous Ls := by
    refine (PiLp.continuous_toLp 2 _).comp ?_
    exact continuous_pi fun k => continuous_const.inner continuous_id
  have hLsL : ∀ s, Ls (L s) = s := by
    intro s
    ext k
    simp [Ls, hLapp, hτ.inner_right_fintype]
  have hrangeL : ∀ y ∈ Q, L (Ls y) = y := by
    intro y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
    have : Ls (∑ i, c i • τ i) = (WithLp.equiv 2 (Fin n → ℝ)).symm c := by
      ext k
      simp [Ls, hτ.inner_right_fintype]
    rw [this]
    simp [hLapp]
  have hLmemQ : ∀ s, L s ∈ Q := by
    intro s
    rw [hLapp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have himage : Ls '' (V ∩ Q) = Ω := by
    ext s
    constructor
    · rintro ⟨y, ⟨hyV, hyQ⟩, rfl⟩
      show L (Ls y) ∈ V
      rw [hrangeL y hyQ]; exact hyV
    · intro hs
      exact ⟨L s, ⟨hs, hLmemQ s⟩, hLsL s⟩
  have hΩc : IsPreconnected Ω := by
    rw [← himage]
    exact hconn.isPreconnected.image Ls hLscont.continuousOn
  -- step 4: `h = g ∘ ι` is a.e.-strongly measurable, and `∫_{K'} |h| = ∫_{ι(K') ∩ Q} |g| dHⁿ < ∞`
  -- for compact `K' ⊆ Ω`
  have hgm' : AEStronglyMeasurable (fun s => g (L s)) volume := by
    have : AEStronglyMeasurable g (Measure.map L volume) := hmap ▸ hgm
    exact (hemb.aestronglyMeasurable_map_iff).mp this
  have hloc : LocallyIntegrableOn (fun s : Euclid n => g (∑ i, s i • τ i)) Ω volume := by
    refine (locallyIntegrableOn_iff hΩo.isLocallyClosed).mpr fun k hkΩ hk => ?_
    refine ⟨hgm'.restrict, ?_⟩
    have hKc : IsCompact (L '' k) := hk.image hcont
    have hKV : L '' k ⊆ V := by
      rintro _ ⟨s, hs, rfl⟩; exact hkΩ hs
    have hfin := hgloc (L '' k) hKc hKV
    have h1 : ∫⁻ x in L '' k ∩ Q, ‖g x‖ₑ ∂μHE[n] = ∫⁻ s in k, ‖g (L s)‖ₑ := by
      rw [htr _ hKc.isClosed.measurableSet, hemb.lintegral_map, hinj.preimage_image]
    show ∫⁻ s in k, ‖g (L s)‖ₑ < ∞
    rw [← h1]
    exact lt_top_iff_ne_top.mpr hfin
  -- step 5: for a smooth test `ψ` in `Ω`, `∫_Ω h ∂ⱼψ = ∫_{V∩Q} g D_{τⱼ}f dHⁿ = 0`, where `f` is
  -- the extension of `ψ` to a smooth test in `V`
  have hsmooth : ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a →
      tsupport a ⊆ Ω → ∀ j : Fin n,
        ∫ v in Ω, g (∑ i, v i • τ i) * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro a ha hac has j
    obtain ⟨f, hf, hfc, hfV, hfa⟩ :=
      Submission.idtp_pc_plane_test_extension P n V τ a hV hτ ha hac has
    have h0 := hweak f hf hfc hfV j
    have h2 : ∫ x in V ∩ Q, g x * fderiv ℝ f x (τ j) ∂μHE[n] =
        ∫ s in Ω, g (L s) * fderiv ℝ f (L s) (τ j) := by
      rw [htr V hV.measurableSet, hemb.integral_map]
      rfl
    rw [h2] at h0
    rw [← h0]
    refine setIntegral_congr_fun hΩo.measurableSet fun s _ => ?_
    simp only [hLapp] at *
    rw [(hfa s).2 j]
  -- step 6: `C¹` tests, by mollification
  refine ⟨hΩo, hΩc, hloc, Submission.dgcr_smooth_tests_to_C1_tests n Ω _ hΩo hloc hsmooth, ?_⟩
  -- step 7: `h = c₀` a.e. on `Ω` forces `c₀ ∈ ℤ`; transfer `g = c₀` back to `V ∩ Q`
  intro c₀ hc₀
  have hne : Ω.Nonempty := by
    rw [← himage]; exact hconn.nonempty.image Ls
  have hint' : ∀ᵐ s ∂(volume : Measure (Euclid n)), ∃ m : ℤ, g (L s) = m := by
    have : ∀ᵐ x ∂(Measure.map L (volume : Measure (Euclid n))), ∃ m : ℤ, g x = m := hmap ▸ hgint
    exact (hemb.ae_map_iff).mp this
  have hpos : (volume : Measure (Euclid n)) Ω ≠ 0 := (hΩo.measure_pos volume hne).ne'
  obtain ⟨s, -, hs1, m, hm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (hc₀.and (ae_restrict_of_ae hint'))
  have hc : c₀ = m := hs1.symm.trans hm
  refine ⟨m, ?_⟩
  rw [htr V hV.measurableSet, hemb.ae_map_iff]
  filter_upwards [hc₀] with s hs
  rw [← hc]; exact hs
/-- **Constancy theorem for an integer multiplicity cycle carried by an `n`-plane** (Simon Ch. 6,
Theorem 2.34, as applied to currents in a plane in the deformation theorem, Ch. 6, (26)–(27)).
Let `τ` be orthonormal, `Q = span{τ₁, …, τₙ}`, `n ≥ 1`, and let `S ∈ 𝒟ₙ(V)` be integer
multiplicity with `∂S = 0` in `V`, `spt S ⊆ Q` and `V ∩ Q` connected.  Then `S = c[[Q]]` in `V`
for some `c ∈ ℤ`: `S(ω) = c ∫_{V∩Q} ω(x)(τ₁, …, τₙ) dHⁿ(x)`, and `M_W(S) = |c| Hⁿ(W ∩ Q)` for open
`W ⊆ V`.  `S(ω) = ∫_{V∩Q} g ω(τ) dHⁿ` and `M_W(S) = ∫_{W∩Q} |g| dHⁿ` for an integer-valued,
locally `Hⁿ`-integrable signed density `g`; `∂S = 0` kills the weak derivatives of `h = g ∘ ι`,
`ι(s) = Σᵢ sᵢτᵢ`, on the connected open set `Ω = ι⁻¹(V)`.  By distributional constancy
`h = c₀` a.e. on `Ω`, so `g = c ∈ ℤ` `Hⁿ`-a.e. on `V ∩ Q`. -/
theorem Submission.idtp_planar_cycle_eq_const_mul : ∀ (P n : ℕ) (V : Set (Euclid P)) (S : GeometricCurrentOn V n) (τ : Fin n → Euclid P), 1 ≤ n → IsOpen V → Orthonormal ℝ τ → IsIntegerMultiplicity S → BoundaryVanishes S → S.support ⊆ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) → IsConnected (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → ∃ c : ℤ, (∀ ω : TestFormOn V n, S ω = (c : ℝ) * ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) ∧ ∀ W : Set (Euclid P), IsOpen W → W ⊆ V → S.massOn W = (c.natAbs : ℝ≥0∞) * μHE[n] (W ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) := by
  intro P n V S τ hn hV hτ hIM hbd hspt hconn
  -- steps 1–5: the integer-valued signed density `g` on `Q`, with `S(ω) = ∫_{V∩Q} g ω(τ) dHⁿ`
  -- and `M_W(S) = ∫_{W∩Q} |g| dHⁿ`
  obtain ⟨g, hgm, hgZ, hgK, hSg, hmass⟩ :=
    Submission.idtp_pc_signed_density P n V S τ hV hτ hIM hspt
  -- step 6: `∂S = 0` gives `∫_{V∩Q} g D_{τⱼ}f dHⁿ = 0` for every `f ∈ C^∞_c(V)`
  have hweak := Submission.idtp_pc_boundary_weak_derivative P n V S τ g hn hτ hbd hSg
  -- `h = g ∘ ι` on `Ω = ι⁻¹(V)`: `Ω` is open and connected, `h ∈ L¹_loc(Ω)` and `∫_Ω h ∂ᵢφ = 0`
  -- for every `φ ∈ C¹_c(Ω)`
  obtain ⟨hΩ, hΩc, hloc, hC1, hconst⟩ :=
    Submission.idtp_pc_constancy_reduction P n V τ g hV hτ hconn hgm hgZ hgK hweak
  -- step 7: distributional constancy, `h = c₀` a.e. on `Ω`; so `g = c ∈ ℤ` `Hⁿ`-a.e. on `V ∩ Q`
  obtain ⟨c₀, hc₀⟩ :=
    Poincare.SimonGMT.Chapter08.ae_eq_const_of_weak_coordinate_derivatives_zero hloc hΩ hΩc hC1
  obtain ⟨c, hc⟩ := hconst c₀ hc₀
  -- step 8: `S(ω) = c ∫_{V∩Q} ω(τ) dHⁿ` and `M_W(S) = ∫_{W∩Q} |c| dHⁿ = |c| Hⁿ(W ∩ Q)`
  refine ⟨c, fun ω => ?_, fun W hW hWV => ?_⟩
  · rw [hSg ω, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hc] with x hx
    rw [hx]
  · rw [hmass W hW hWV, ← setLIntegral_const]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hWV) hc]
      with x hx
    rw [hx, Real.enorm_eq_ofReal_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ENNReal.ofReal_natCast]

/-- **A cycle carried by an `n`-plane `Q` in an open set `V` has constant multiplicity there**
(the constancy step in the proof of Simon 7.3.3(1), p. 191, by the constancy theorem, Simon Ch. 6,
2.34).  Let `C = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)` with `∂C = 0`, `n ≥ 1`, `spt C ∩ V ⊆ Q`, `dim Q = n` and
`V ∩ Q` connected.  The restriction `C⌞V = τ(M ∩ V, θ, ξ) ∈ 𝒟ₙ(V)` is integer multiplicity
(approximate tangent planes are local), `∂(C⌞V) = 0` (as `ι(dβ) = d(ιβ)` for the inclusion `ι` of
test forms) and `spt(C⌞V) ⊆ spt C ∩ V ⊆ Q` (as `μ_{C⌞V} = μ_C⌞V`).  For an orthonormal basis `τ`
of `Q` the planar constancy theorem gives `c ∈ ℤ` with `μ_C(W) = M_W(C⌞V) = |c| Hⁿ(W ∩ Q)` for
open `W ⊆ V`.  So `μ_C⌞V` and `|c| Hⁿ⌞Q⌞V` agree on open sets, which form a π-system generating
the Borel sets, and are finite on balls (`θ` is locally `Hⁿ`-integrable); hence they are equal. -/
theorem Submission.idtp_tdc_puvd_planar_piece_measure : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (V : Set (Euclid P)) (Q : Submodule ℝ (Euclid P)), 1 ≤ n → IsOpen V → BoundaryVanishes C → R.Represents C → Module.finrank ℝ Q = n → IsConnected (V ∩ (Q : Set (Euclid P))) → C.support ∩ V ⊆ (Q : Set (Euclid P)) → ∃ c : ℕ, ∀ E : Set (Euclid P), MeasurableSet E → E ⊆ V → R.measure E = (c : ℝ≥0∞) * μHE[n] (E ∩ (Q : Set (Euclid P))) := by
  intro P n C R V Q hn hV hbd hR hQ hconn hsupp
  -- an orthonormal basis `τ` of `Q`, pushed into `ℝᴾ`, is orthonormal with `span τ = Q`
  obtain ⟨τ, hτ, hτQ⟩ : ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧
      Submodule.span ℝ (range τ) = Q := by
    let b := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    refine ⟨fun k => (b k : Euclid P), b.orthonormal.comp_linearIsometry Q.subtypeₗᵢ, ?_⟩
    have hrange : range (fun k => (b k : Euclid P)) = Q.subtype '' range b := by
      rw [← range_comp]; rfl
    rw [hrange, Submodule.span_image, ← b.coe_toBasis, b.toBasis.span_eq,
      Submodule.map_subtype_top]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hbd' : C.boundary = 0 := hbd
  -- the restriction `C⌞V ∈ 𝒟ₙ(V)`, `C⌞V(ω) = C(ιω)`
  set CV := C.restrictDomain (subset_univ V) with hCV
  -- at `x ∈ V`, an approximate tangent plane of `M` is one of `M ∩ V`: the blow-ups of `M` and
  -- of `M ∩ V` agree in `B_L(0) ⊇ spt f` once `B_{rL}(x) ⊆ V`
  have htan : ∀ x ∈ V, ∀ T : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt (m + 1) R.carrier x T →
        HasApproximateTangentSpaceAt (m + 1) (R.carrier ∩ V) x T := by
    intro x hxV T hT
    refine ⟨hT.1, fun f => ?_⟩
    obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV x hxV
    obtain ⟨L, hL, hfL⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
    refine (hT.2 f).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
    have hr0 : 0 < r := hr.1
    have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
    rw [hη]
    -- `f` vanishes off `B_L(0)`, so each blow-up integral may be cut to `B_L(0)`
    have hfB : ∀ y, y ∉ ball (0 : Euclid P) L → f y = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun h => hy (hfL h)
    have hcut : ∀ S : Set (Euclid P),
        ∫ y in S, f y ∂μHE[m + 1] = ∫ y in ball (0 : Euclid P) L ∩ S, f y ∂μHE[m + 1] := by
      intro S
      rw [← Measure.restrict_restrict measurableSet_ball]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hfB).symm
    -- `η_{x,r}(z) ∈ B_L(0)` forces `z ∈ B_{rL}(x) ⊆ B_s(x) ⊆ V`
    have hset : ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' R.carrier =
        ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' (R.carrier ∩ V) := by
      refine Subset.antisymm ?_ (inter_subset_inter_right _ (image_mono inter_subset_left))
      rintro y ⟨hyB, z, hz, rfl⟩
      refine ⟨hyB, z, ⟨hz, hsV ?_⟩, rfl⟩
      rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
        inv_mul_lt_iff₀ hr0] at hyB
      have hrL := (lt_div_iff₀ hL).mp hr.2
      rw [mem_ball, dist_eq_norm]
      linarith
    rw [hcut, hcut ((fun y : Euclid P => r⁻¹ • (y - x)) '' (R.carrier ∩ V)), hset]
  -- the restricted triple `R' = (M ∩ V, θ, ξ)` in `V`
  let R' : IMRep V (m + 1) :=
    { carrier := R.carrier ∩ V
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hV.measurableSet
      carrier_subset := inter_subset_right
      rectifiable := R.rectifiable.mono inter_subset_left
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      locallyIntegrable_mult := fun K hK hKV => by
        rw [inter_assoc, inter_eq_right.2 hKV]
        exact R.locallyIntegrable_mult K hK (subset_univ K)
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
      orients := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
          (inter_subset_left : R.carrier ∩ V ⊆ R.carrier) R.orients,
          ae_restrict_mem (R.measurableSet_carrier.inter hV.measurableSet)] with x hx hxMV
        obtain ⟨T, hT, hξT⟩ := hx
        exact ⟨T, htan x hxMV.2 T hT, hξT⟩ }
  -- `C⌞V = τ(M ∩ V, θ, ξ)`: a test form supported in `V` vanishes on `M ∖ V`
  have hR' : R'.Represents CV := by
    intro ω
    rw [hCV, GeometricCurrentOn.restrictDomain_apply, hR, testFormOnInclusion_coe]
    change ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x
        ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
      ∫ x in R.carrier ∩ V, (R.mult x : ℝ) * R.orient x
        ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
      inter_subset_left fun x hx => ?_
    have hxω : x ∉ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) :=
      fun h => hx.2 ⟨hx.1, ω.property.2 h⟩
    rw [image_eq_zero_of_notMem_tsupport hxω, map_zero, mul_zero]
  -- `μ_{R'} = θHⁿ⌞(M ∩ V) = μ_R⌞V`
  have hR'meas : R'.measure = R.measure.restrict V := by
    change (μHE[m + 1].restrict (R.carrier ∩ V)).withDensity (fun x => (R.mult x : ℝ≥0∞)) =
      ((μHE[m + 1].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)).restrict V
    rw [restrict_withDensity hV.measurableSet, Measure.restrict_restrict hV.measurableSet,
      inter_comm]
  -- `∂(C⌞V) = 0`: `∂(C⌞V)(β) = C(ι(dβ)) = C(d(ιβ)) = ∂C(ιβ) = 0`
  have hbdV : BoundaryVanishes CV := by
    change CV.boundary = 0
    ext β
    have hι : testFormOnInclusion (subset_univ V) (m + 1) (exteriorDerivativeTestOn V m β) =
        exteriorDerivativeTestOn univ m (testFormOnInclusion (subset_univ V) m β) :=
      Subtype.ext rfl
    rw [GeometricCurrentOn.boundary_apply, hCV, GeometricCurrentOn.restrictDomain_apply, hι,
      ← GeometricCurrentOn.boundary_apply, hbd', GeometricCurrentOn.zero_apply,
      GeometricCurrentOn.zero_apply]
  -- `spt(C⌞V) ⊆ spt C ∩ V ⊆ Q`: balls about `x ∈ spt(C⌞V)` have positive `μ_R⌞V ≤ μ_R` measure
  have hsptV : CV.support ⊆ (Q : Set (Euclid P)) := by
    intro x hx
    have hxV : x ∈ V := CV.support_subset_domain hx
    refine hsupp ⟨?_, hxV⟩
    rw [(Submission.dimred_im_mass_measure P (m + 1) univ C R isOpen_univ hR).2.1 x (mem_univ x)]
    intro ε hε h0
    refine ((Submission.dimred_im_mass_measure P (m + 1) V CV R' hV hR').2.1 x hxV).mp hx ε hε ?_
    rw [hR'meas]
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans h0.le)
  -- constancy: `M_W(C⌞V) = |c| Hⁿ(W ∩ Q)` for open `W ⊆ V`
  obtain ⟨c, -, hmass⟩ := Submission.idtp_planar_cycle_eq_const_mul P (m + 1) V CV τ hn hV hτ
    ⟨R', hR'⟩ hbdV (by rw [hτQ]; exact hsptV) (by rw [hτQ]; exact hconn)
  rw [hτQ] at hmass
  -- `μ_R(W) = μ_{R'}(W) = M_W(C⌞V) = |c| Hⁿ(W ∩ Q)` for open `W ⊆ V`
  have hopen : ∀ W : Set (Euclid P), IsOpen W → W ⊆ V →
      R.measure W = (c.natAbs : ℝ≥0∞) * μHE[m + 1] (W ∩ (Q : Set (Euclid P))) := by
    intro W hW hWV
    rw [← hmass W hW hWV, (Submission.dimred_im_mass_measure P (m + 1) V CV R' hV hR').1 W hW hWV,
      hR'meas, Measure.restrict_eq_self _ hWV]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` for compact `K`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → R.measure K ≠ ∞ := by
    intro K hK
    change (μHE[m + 1].restrict R.carrier).withDensity (fun x => (R.mult x : ℝ≥0∞)) K ≠ ∞
    rw [withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
      inter_comm]
    exact R.locallyIntegrable_mult K hK (subset_univ K)
  -- `μ_R⌞V = |c| Hⁿ⌞Q⌞V`: they agree on the open sets and are finite on the balls `B_i(0)`
  have hext : R.measure.restrict V =
      ((c.natAbs : ℝ≥0∞) • μHE[m + 1].restrict (Q : Set (Euclid P))).restrict V := by
    refine Measure.ext_of_generateFrom_of_iUnion {s | IsOpen s}
      (fun i : ℕ => ball (0 : Euclid P) i) BorelSpace.measurable_eq isPiSystem_isOpen
      (iUnion_ball_nat 0) (fun i => show IsOpen (ball (0 : Euclid P) i) from isOpen_ball)
      (fun i => ?_) (fun s hs => ?_)
    · exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall 0 i))
        ((Measure.restrict_apply_le _ _).trans (measure_mono ball_subset_closedBall))
    · have hs' : IsOpen s := hs
      rw [Measure.restrict_apply hs'.measurableSet, Measure.restrict_apply hs'.measurableSet,
        Measure.smul_apply, Measure.restrict_apply (hs'.measurableSet.inter hV.measurableSet),
        smul_eq_mul]
      exact hopen _ (hs'.inter hV) inter_subset_right
  -- for Borel `E ⊆ V`: `μ_R(E) = (μ_R⌞V)(E) = |c| Hⁿ(E ∩ Q)`
  refine ⟨c.natAbs, fun E hE hEV => ?_⟩
  rw [← Measure.restrict_eq_self R.measure hEV, hext, Measure.restrict_eq_self _ hEV,
    Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul]

end GMT.Ch07
