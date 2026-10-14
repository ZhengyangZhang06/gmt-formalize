import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.AreaLipschitz

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

/-- **Simon Ch. 3, Lemma 1.2 and Remark 1.3**, with bi-Lipschitz Borel pieces in place of `C¹`
submanifolds: a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null set, the disjoint
union of Borel sets `Fᵢ(Bᵢ) ⊆ M`, where `Fᵢ : ℝⁿ → ℝᴾ` is Lipschitz, `Bᵢ` is Borel,
`mᵢ|a − a'| ≤ |Fᵢ(a) − Fᵢ(a')|` on `Bᵢ` for some `mᵢ > 0`, and `DFᵢ` exists and is injective on
`Bᵢ`.  Each Lipschitz `Fⱼ` of the cover maps its non-differentiability points (Rademacher) and
its critical points (the image of `{JFⱼ = 0}`) to `Hⁿ`-null sets.  Mathlib's partition lemma cuts
the regular points into pieces on which `Fⱼ` is close to an injective linear map, hence
bi-Lipschitz; the images of the pieces are Borel (Lusin–Souslin) and are made disjoint as in
Remark 1.3. -/
theorem Submission.dpf_rectifiable_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → ∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0 := by
  intro P n M hM hrect
  have hvol : (μHE[n] : Measure (Euclid n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- Step 1: the rectifiable cover `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)`
  obtain ⟨M₀, hM₀, F₀, hF₀, hcover⟩ := hrect
  choose K hK using hF₀
  -- Step 2: the regular sets `Gⱼ` are Borel and `Hⁿ(Fⱼ(ℝⁿ ∖ Gⱼ)) = 0`
  have hGmeas : ∀ f : Euclid n → Euclid P,
      MeasurableSet {a | DifferentiableAt ℝ f a ∧ Injective (fderiv ℝ f a)} := fun f =>
    (measurableSet_of_differentiableAt ℝ f).inter
      (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet)
  -- Step 2(a): nondifferentiability points have null image (Rademacher)
  have hrad : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | ¬ DifferentiableAt ℝ f a}) = 0 := by
    intro f L hf
    have hz : volume {a : Euclid n | ¬ DifferentiableAt ℝ f a} = 0 :=
      ae_iff.mp (hf.ae_differentiableAt (μ := volume))
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hf.lipschitzOnWith (s := {a | ¬ DifferentiableAt ℝ f a}))
    rw [hvol, hz, mul_zero] at hle
    exact le_antisymm hle bot_le
  -- Step 2(b): critical points have null image.  On a piece where `f` is `ε`-close to a
  -- rank-deficient `A` (`Av = 0`, `‖v‖ = 1`), `|f a - f a'| ≤ (L + 1)|D a - D a'|` for
  -- `D = id - (1 - ε) v ⊗ v`, and `det D = ε`.
  have hsard : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}) = 0 := by
    intro f L hf
    set S := {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}
    have hSmeas : MeasurableSet S :=
      (measurableSet_of_differentiableAt ℝ f).inter
        (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet).compl
    have hR : ∀ R : ℕ, μHE[n] (f '' (S ∩ ball (0 : Euclid n) R)) = 0 := by
      intro R
      set s := S ∩ ball (0 : Euclid n) R
      have hsmeas : MeasurableSet s := hSmeas.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (f '' s) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
        intro ε hε hε1
        rcases s.eq_empty_or_nonempty with hse | hsne
        · rw [hse, image_empty, measure_empty]; exact bot_le
        obtain ⟨t, A, htdisj, htmeas, hst, hA, hAy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
            (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => ε) (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (f '' (s ∩ t k)) ≤
            ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
          intro k
          obtain ⟨y, hy, hAk⟩ := hAy hsne k
          have hAnorm : ‖A k‖ ≤ L := hAk ▸ norm_fderiv_le_of_lipschitz ℝ hf
          have hAni : ¬ Injective (A k) := hAk ▸ hy.1.2
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ A k v = 0 := by
            simp only [Injective, not_forall] at hAni
            obtain ⟨a, b, hab, hne⟩ := hAni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c : ℝ := 1 - (ε : ℝ) with hc
          have hc0 : 0 ≤ c := by
            rw [hc]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hAD : ∀ h, A k (D h) = A k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc]; ring
          have hfD : ∀ a ∈ s ∩ t k, ∀ a' ∈ s ∩ t k,
              ‖f a - f a'‖ ≤ ((L : ℝ) + 1) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hA k a ha a' ha'
            have h2 : ‖A k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hAD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (f a - f a') (A k (a - a'))
            linarith
          have himg : μHE[n] (f '' (s ∩ t k)) ≤
              ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := by
            set X := s ∩ t k
            set g := Function.invFunOn D X
            have hg : ∀ y ∈ D '' X, g y ∈ X ∧ D (g y) = y :=
              fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
            have hLip : LipschitzOnWith (L + 1) (f ∘ g) (D '' X) := by
              refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
              obtain ⟨hgy, hDy⟩ := hg y hy
              obtain ⟨hgy', hDy'⟩ := hg y' hy'
              simp only [comp_apply, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
              calc ‖f (g y) - f (g y')‖ ≤ ((L : ℝ) + 1) * ‖D (g y) - D (g y')‖ :=
                    hfD _ hgy _ hgy'
                _ = _ := by rw [hDy, hDy']
            have hsub : f '' X ⊆ (f ∘ g) '' (D '' X) := by
              rintro _ ⟨a, ha, rfl⟩
              refine ⟨D a, mem_image_of_mem D ha, ?_⟩
              obtain ⟨hga, hDa⟩ := hg (D a) (mem_image_of_mem D ha)
              have := hfD _ hga _ ha
              rw [hDa, sub_self, norm_zero, mul_zero] at this
              exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
            exact (measure_mono hsub).trans
              (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c * v i) = 1 - c * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc]; ring
          calc μHE[n] (f '' (s ∩ t k)) ≤
                ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := himg
            _ = ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
              rw [hvol, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
                NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
              push_cast
              ring
        calc μHE[n] (f '' s) ≤ μHE[n] (⋃ k, f '' (s ∩ t k)) := by
              apply measure_mono
              rintro _ ⟨a, ha, rfl⟩
              obtain ⟨k, hk⟩ := mem_iUnion.mp (hst ha)
              exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
          _ ≤ ∑' k, μHE[n] (f '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := ENNReal.tsum_le_tsum hpiece
          _ = ((L : ℝ≥0∞) + 1) ^ n * volume (⋃ k, s ∩ t k) * ε := by
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right
              · exact fun k => hsmeas.inter (htmeas k)
          _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left.trans inter_subset_right
      have hfin : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have htend : Tendsto (fun ε : NNReal =>
          ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * (ε : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.coe_zero]
          exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hfin)
      refine le_antisymm (ge_of_tendsto htend ?_) bot_le
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
      exact hbound ε hε.1 hε.2
    refine measure_mono_null ?_ (measure_iUnion_null hR)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
  set G : ℕ → Set (Euclid n) := fun j =>
    {a | DifferentiableAt ℝ (F₀ j) a ∧ Injective (fderiv ℝ (F₀ j) a)}
  have hGnull : ∀ j, μHE[n] (F₀ j '' (G j)ᶜ) = 0 := by
    intro j
    refine measure_mono_null ?_ (measure_union_null (hrad _ _ (hK j)) (hsard _ _ (hK j)))
    rintro _ ⟨a, ha, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F₀ j) a
    · exact Or.inr ⟨a, ⟨hd, fun hi => ha ⟨hd, hi⟩⟩, rfl⟩
    · exact Or.inl ⟨a, hd, rfl⟩
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Step 4: Mathlib's partition of `Gⱼ` into pieces on which `Fⱼ` is close to linear
  have hpart : ∀ j, ∃ (t : ℕ → Set (Euclid n)) (A : ℕ → Euclid n →L[ℝ] Euclid P),
      Pairwise (Disjoint on t) ∧ (∀ k, MeasurableSet (t k)) ∧ G j ⊆ ⋃ k, t k ∧
      (∀ k, ApproximatesLinearOn (F₀ j) (A k) (G j ∩ t k) (c (A k) / 2)) ∧
      ((G j).Nonempty → ∀ k, ∃ y ∈ G j, A k = fderiv ℝ (F₀ j) y) := fun j =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F₀ j) (G j) (fderiv ℝ (F₀ j))
      (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) (fun A => c A / 2)
      (fun A => (div_pos (hcpos A) two_pos).ne')
  choose t A htdisj htmeas hGt hAapprox hAy using hpart
  -- Step 5: `Fⱼ` is bi-Lipschitz on `Gⱼ ∩ tⱼₖ` with lower constant `c(Aⱼₖ)/2`
  have hlow : ∀ j k, ∀ a ∈ G j ∩ t j k, ∀ a' ∈ G j ∩ t j k,
      ((c (A j k) / 2 : NNReal) : ℝ) * ‖a - a'‖ ≤ ‖F₀ j a - F₀ j a'‖ := by
    intro j k a ha a' ha'
    obtain ⟨y, hy, hAk⟩ := hAy j ⟨a, ha.1⟩ k
    have hinj : Injective (A j k) := hAk ▸ hy.2
    have h1 := hc (A j k) hinj (a - a')
    have h2 := hAapprox j k a ha a' ha'
    have h3 := norm_sub_norm_le (A j k (a - a')) (F₀ j a - F₀ j a')
    rw [norm_sub_rev (A j k (a - a'))] at h3
    push_cast at h2 ⊢
    linarith
  -- Step 6: enumerate the pieces by `i ↦ (unpair i)`; their images are Borel (Lusin–Souslin)
  set Fi : ℕ → Euclid n → Euclid P := fun i => F₀ (Nat.unpair i).1 with hFi
  set Di : ℕ → Set (Euclid n) := fun i =>
    G (Nat.unpair i).1 ∩ t (Nat.unpair i).1 (Nat.unpair i).2 with hDi
  set mi : ℕ → ℝ := fun i =>
    ((c (A (Nat.unpair i).1 (Nat.unpair i).2) / 2 : NNReal) : ℝ) with hmi
  have hDmeas : ∀ i, MeasurableSet (Di i) := fun i =>
    (hGmeas _).inter (htmeas _ _)
  have hmipos : ∀ i, 0 < mi i := fun i => by
    simp only [hmi, NNReal.coe_div, NNReal.coe_ofNat]
    exact div_pos (hcpos _) two_pos
  have hlowi : ∀ i, ∀ a ∈ Di i, ∀ a' ∈ Di i, mi i * ‖a - a'‖ ≤ ‖Fi i a - Fi i a'‖ :=
    fun i => hlow _ _
  have hNmeas : ∀ i, MeasurableSet (Fi i '' Di i) := by
    intro i
    refine (hDmeas i).image_of_continuousOn_injOn (hK _).continuous.continuousOn ?_
    intro a ha a' ha' h
    have := hlowi i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmipos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 7: disjointify the images inside `M`
  set Ñ : ℕ → Set (Euclid P) := fun i => Fi i '' Di i ∩ M
  have hÑmeas : ∀ i, MeasurableSet (Ñ i) := fun i => (hNmeas i).inter hM
  set B : ℕ → Set (Euclid n) := fun i => Di i ∩ Fi i ⁻¹' disjointed Ñ i with hB
  have himg : ∀ i, Fi i '' B i = disjointed Ñ i := by
    intro i
    rw [hB, image_inter_preimage]
    exact inter_eq_right.mpr ((disjointed_subset Ñ i).trans inter_subset_left)
  refine ⟨Fi, B, mi, fun i => ⟨K _, hK _⟩,
    fun i => (hDmeas i).inter ((hK _).continuous.measurable (MeasurableSet.disjointed hÑmeas i)),
    hmipos, fun i a ha a' ha' => hlowi i a ha.1 a' ha'.1, fun i a ha => ha.1.1,
    fun i => himg i ▸ MeasurableSet.disjointed hÑmeas i,
    fun i => himg i ▸ ((disjointed_subset Ñ i).trans inter_subset_right), ?_, ?_⟩
  · intro i j hij
    rw [himg i, himg j]
    exact disjoint_disjointed Ñ hij
  -- Step 8: the remainder lies in `M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ ∖ Gⱼ)`
  · have hU : (⋃ i, Fi i '' B i) = ⋃ i, Ñ i := by
      simp_rw [himg]
      exact iUnion_disjointed
    rw [hU]
    refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hGnull))
    rintro x ⟨hxM, hxN⟩
    rcases hcover hxM with hx0 | hx
    · exact Or.inl hx0
    · obtain ⟨j, a, rfl⟩ := mem_iUnion.mp hx
      by_cases ha : a ∈ G j
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hGt j ha)
        apply hxN
        refine mem_iUnion.mpr ⟨Nat.pair j k, ⟨a, ?_, ?_⟩, hxM⟩
        · simp only [hDi, Nat.unpair_pair]
          exact ⟨ha, hk⟩
        · simp only [hFi, Nat.unpair_pair]
      · exact Or.inr (mem_iUnion.mpr ⟨j, a, ha, rfl⟩)

/-- **Suspension of a map** (the product pieces `Ĝ(t, u) = (t, G(u))` of a cylinder over a
rectifiable set): if `Ĝ(t, u) = (t, G(u))` for `G : ℝⁿ → ℝᴺ`, then `Ĝ` is `max(1, L)`-Lipschitz
when `G` is `L`-Lipschitz, `min(1, m)|z − z'| ≤ |Ĝ(z) − Ĝ(z')|` on `ℝ × A` when
`m|a − a'| ≤ |G(a) − G(a')|` on `A`, and, where `G` is differentiable at `u`, `Ĝ` is
differentiable at `(t, u)` with `DĜ(t, u)(s, w) = (s, DG(u)w)`.  Hence `DĜ(t, u)` is injective
when `DG(u)` is, its range is `ℝe₀ ⊕ (0, range DG(u))`, and its Gram matrix is
`diag(1, Gram(DG(u)))`, so the two Gram determinants agree. -/
theorem Submission.dimred_mbl_dt_lp_imc_suspension : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (Gh : Euclid (n + 1) → Euclid (N + 1)), (∀ (t : ℝ) (u : Euclid n), Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp (G u)))) → (∀ L : NNReal, LipschitzWith L G → LipschitzWith (max 1 L) Gh) ∧ (∀ (m : ℝ) (A : Set (Euclid n)), (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → ∀ (t t' : ℝ), ∀ u ∈ A, ∀ u' ∈ A, min 1 m * ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) - WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u'))‖ ≤ ‖Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) - Gh (WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')))‖) ∧ ∀ (t : ℝ) (u : Euclid n), DifferentiableAt ℝ G u → DifferentiableAt ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) ∧ (∀ (s : ℝ) (w : Euclid n), fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp w))) = WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w)))) ∧ (Injective (fderiv ℝ G u) → Injective (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))))) ∧ LinearMap.range (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) : Euclid (n + 1) →ₗ[ℝ] Euclid (N + 1)) = Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (LinearMap.range (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N) : Set (Euclid N)))) ∧ Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single i 1)) (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single j 1))) = Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single i 1)) (fderiv ℝ G u (EuclideanSpace.single j 1))) := by
  intro N n G Gh hGh
  -- `Φ_d(t, u) = (t, u₁, …, u_d)` is a bijection `ℝ × ℝᵈ → ℝᵈ⁺¹`, linear in `(t, u)`,
  -- with `⟨Φ_d(s, v), Φ_d(s', v')⟩ = s s' + ⟨v, v'⟩`
  have hsurj : ∀ z : Euclid (n + 1), ∃ (t : ℝ) (u : Euclid n),
      z = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) := fun z =>
    ⟨WithLp.ofLp z 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)), by simp [Fin.cons_self_tail]⟩
  have hinj : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1)) =
        WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')) → t = t' ∧ u = u' := by
    intro d t t' u u' h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.1 (WithLp.toLp_injective 2 h)
    exact ⟨h1, WithLp.ofLp_injective 2 h2⟩
  have hsub : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1)) -
          WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')) =
        WithLp.toLp 2 (Fin.cons (t - t') (WithLp.ofLp (u - u'))) := by
    intro d t t' u u'
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hinner : ∀ (d : ℕ) (s s' : ℝ) (v v' : Euclid d),
      inner ℝ (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp v)) : Euclid (d + 1))
        (WithLp.toLp 2 (Fin.cons s' (WithLp.ofLp v'))) = s * s' + inner ℝ v v' := by
    intro d s s' v v'
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
  have hnorm : ∀ (d : ℕ) (t : ℝ) (u : Euclid d),
      ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1))‖ ^ 2 = t ^ 2 + ‖u‖ ^ 2 := by
    intro d t u
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner, sq]
  refine ⟨fun L hL => LipschitzWith.of_dist_le_mul fun z z' => ?_,
    fun m A hA t t' u hu u' hu' => ?_, fun t u hG => ?_⟩
  · -- (i) `|Gh z − Gh z'|² = (z₀ − z'₀)² + |G(tail z) − G(tail z')|² ≤ max(1, L)²|z − z'|²`
    obtain ⟨t, u, rfl⟩ := hsurj z
    obtain ⟨t', u', rfl⟩ := hsurj z'
    rw [dist_eq_norm, dist_eq_norm, hGh, hGh, hsub, hsub]
    have hGL : ‖G u - G u'‖ ≤ L * ‖u - u'‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul u u'
    have hM1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have hML : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have hb : ‖G u - G u'‖ ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * ‖u - u'‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hGL.trans (mul_le_mul_of_nonneg_right hML (norm_nonneg _))) 2
    have hs : (t - t') ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * (t - t') ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hM1)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hnorm, hnorm]
    linarith
  · -- (ii) `min(1, m)²|Φ(t, u) − Φ(t', u')|² ≤ (t − t')² + |G u − G u'|²`
    rw [hGh, hGh, hsub, hsub]
    rcases le_or_gt (min 1 m) 0 with hk | hk
    · exact (mul_nonpos_of_nonpos_of_nonneg hk (norm_nonneg _)).trans (norm_nonneg _)
    have hb : min 1 m ^ 2 * ‖u - u'‖ ^ 2 ≤ ‖G u - G u'‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity)
        ((mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans
          (hA u hu u' hu')) 2
    have hs : min 1 m ^ 2 * (t - t') ^ 2 ≤ (t - t') ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hk.le (min_le_left _ _))
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hnorm, hnorm]
    linarith
  · -- (iii) `Gh = cs ∘ (p₀, G ∘ tl)` with continuous linear `p₀`, `tl`, `cs`
    obtain ⟨p0, hp0⟩ : ∃ p0 : Euclid (n + 1) →L[ℝ] ℝ, ∀ z, p0 z = WithLp.ofLp z 0 :=
      ⟨EuclideanSpace.proj 0, fun z => rfl⟩
    obtain ⟨tl, htl⟩ : ∃ tl : Euclid (n + 1) →L[ℝ] Euclid n,
        ∀ z, tl z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }, fun z => rfl⟩
    obtain ⟨cs, hcs⟩ : ∃ cs : ℝ × Euclid N →L[ℝ] Euclid (N + 1),
        ∀ p, cs p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
          map_add' := fun x y => by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_smul' := fun c x => by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp }, fun p => rfl⟩
    have hGfun : Gh = fun y => cs (p0 y, G (tl y)) := by
      funext y
      obtain ⟨s, w, rfl⟩ := hsurj y
      simp [hGh, hcs, hp0, htl]
    have htlz : tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = u := by simp [htl]
    have hD : HasFDerivAt Gh (cs.comp (p0.prod ((fderiv ℝ G u).comp tl)))
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) := by
      have hG' : HasFDerivAt G (fderiv ℝ G u) (tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))) := by
        rw [htlz]
        exact hG.hasFDerivAt
      rw [hGfun]
      exact cs.hasFDerivAt.comp _ (p0.hasFDerivAt.prodMk (hG'.comp _ tl.hasFDerivAt))
    have hform : ∀ (s : ℝ) (w : Euclid n),
        fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp w))) =
          WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w))) := by
      intro s w
      rw [hD.fderiv]
      simp [hcs, hp0, htl]
    refine ⟨hD.differentiableAt, hform, fun hinjG y y' hyy => ?_, ?_, ?_⟩
    · -- injectivity
      obtain ⟨s, w, rfl⟩ := hsurj y
      obtain ⟨s', w', rfl⟩ := hsurj y'
      rw [hform, hform] at hyy
      obtain ⟨rfl, hw⟩ := hinj N s s' _ _ hyy
      rw [hinjG hw]
    · -- range
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        obtain ⟨s, w, rfl⟩ := hsurj y
        have hsplit : (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w))) : Euclid (N + 1)) =
            s • EuclideanSpace.single 0 1 +
              WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (fderiv ℝ G u w))) := by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        rw [ContinuousLinearMap.coe_coe, hform, hsplit]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
          (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨_, ⟨w, rfl⟩, rfl⟩))
      · rw [Submodule.span_le, Set.insert_subset_iff]
        refine ⟨⟨WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp (0 : Euclid n))), ?_⟩, ?_⟩
        · rw [ContinuousLinearMap.coe_coe, hform, map_zero]
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        · rintro _ ⟨v, ⟨w, rfl⟩, rfl⟩
          exact ⟨WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp w)), by
            rw [ContinuousLinearMap.coe_coe, hform]; rfl⟩
    · -- Gram determinant: block diagonal `diag(1, Gram(DG(u)c))`
      have hb0 : (EuclideanSpace.single 0 1 : Euclid (n + 1)) =
          WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp (0 : Euclid n))) := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      have hbs : ∀ j : Fin n, (EuclideanSpace.single j.succ 1 : Euclid (n + 1)) =
          WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (EuclideanSpace.single j 1 : Euclid n))) := by
        intro j
        ext i
        refine Fin.cases ?_ (fun k => ?_) i <;> simp [PiLp.single_apply, Pi.single_apply]
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
      · simp only [Matrix.of_apply, Fin.val_zero, pow_zero, one_mul, hb0, hform, map_zero,
          hinner, inner_zero_left, mul_one, add_zero, Fin.succAbove_zero]
        congr 1
        ext i j
        simp [hbs, hform, hinner]
      · intro j _
        simp [Matrix.of_apply, hb0, hbs, hform, hinner]
/-- **Product-null lemma**: if `Z ⊆ ℝᴺ` has `Hⁿ(Z) = 0`, then the cylinder `Ψ(ℝ × Z) ⊆ ℝᴺ⁺¹`,
`Ψ(t, x) = (t, x₁, …, x_N)`, has `Hⁿ⁺¹(Ψ(ℝ × Z)) = 0`.  Since `μHE = c • μH` with `c ≠ 0` and `Ψ`
is linear, hence Lipschitz for the max metric on `ℝ × ℝᴺ`, it suffices that `μH[n + 1](ℝ × Z) = 0`;
for `n = 0`, `Z = ∅`.  Given `ε ∈ (0, 1]`, cover `Z` by sets `Cⱼ` with `diam Cⱼ ≤ ε` and
`Σ (diam Cⱼ)ⁿ < ε`, pick `eⱼ > 0` with `Σ eⱼ < ε`, and cut each strip `[m, m + 1] × Cⱼ` into
`⌊1/dⱼ⌋ + 1` boxes of side `dⱼ = max(diam Cⱼ, eⱼ)`; their `(n + 1)`-cost is `≤ 4ε`. -/
theorem Submission.dimred_mbl_dt_lp_imc_product_null : ∀ (N n : ℕ) (Z : Set (Euclid N)), μHE[n] Z = 0 → μHE[n + 1] ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (univ ×ˢ Z)) = 0 := by
  intro N n Z hZ
  -- Step 1: `μHE[d] = c_d • μH[d]` with `c_d ≠ 0`, so it suffices to work with `μH`
  have hZ' : μH[(n : ℝ)] Z = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      mul_eq_zero] at hZ
    exact hZ.resolve_left
      (by simpa using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  suffices h : μH[((n + 1 : ℕ) : ℝ)] ((fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (univ ×ˢ Z)) = 0 by
    rw [h, smul_zero]
  -- Step 3: for `n = 0`, `μH[0] Z = 0` forces `Z = ∅`
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hZe : Z = ∅ := by
      rcases Z.eq_empty_or_nonempty with h | h
      · exact h
      · have := Measure.one_le_hausdorffMeasure_zero_of_nonempty h
        rw [Nat.cast_zero] at hZ'
        rw [hZ'] at this
        exact absurd this (by simp)
    simp [hZe]
  -- Step 2: `Ψ` is linear, hence Lipschitz for the max metric on `ℝ × ℝᴺ`
  let L : (ℝ × Euclid N) →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
      map_add' := fun p q => by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := fun c p => by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  have hL : LipschitzWith ‖LinearMap.toContinuousLinearMap L‖₊ (fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) :=
    (LinearMap.toContinuousLinearMap L).lipschitzWith
  refine le_antisymm ((hL.hausdorffMeasure_image_le (by positivity) _).trans ?_) bot_le
  suffices hprod : μH[((n + 1 : ℕ) : ℝ)] (univ ×ˢ Z : Set (ℝ × Euclid N)) = 0 by
    rw [hprod, mul_zero]
  -- in the max metric, `diam (I × C) ≤ max (diam I) (diam C)`
  have hdiam_prod : ∀ (s : Set ℝ) (c : Set (Euclid N)),
      ediam (s ×ˢ c) ≤ max (ediam s) (ediam c) := by
    intro s c
    refine ediam_le ?_
    rintro ⟨a, x⟩ ⟨ha, hx⟩ ⟨b, y⟩ ⟨hb, hy⟩
    rw [Prod.edist_eq]
    exact max_le_max (edist_le_ediam_of_mem ha hb) (edist_le_ediam_of_mem hx hy)
  -- Steps 4–8: each strip `[m, m + 1] × Z` is `μH[n + 1]`-null
  have hstrip : ∀ m : ℤ, μH[((n + 1 : ℕ) : ℝ)] (Icc (m : ℝ) (m + 1) ×ˢ Z) = 0 := by
    intro m
    have hcov : ∀ ε : ℝ≥0∞, 0 < ε → ε ≤ 1 → ∃ t : ℕ × ℕ → Set (ℝ × Euclid N),
        Icc (m : ℝ) (m + 1) ×ˢ Z ⊆ ⋃ i, t i ∧ (∀ i, ediam (t i) ≤ ε) ∧
          ∑' i, ediam (t i) ^ ((n + 1 : ℕ) : ℝ) ≤ 4 * ε := by
      intro ε hε hε1
      -- Step 5: covers `C j` of `Z` with mesh `≤ ε` and `n`-cost `< ε`
      obtain ⟨C, hZC, hCε, hCsum⟩ : ∃ C : ℕ → Set (Euclid N), Z ⊆ ⋃ j, C j ∧
          (∀ j, ediam (C j) ≤ ε) ∧ ∑' j, ⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ) < ε := by
        have h0 : (⨅ (C : ℕ → Set (Euclid N)) (_ : Z ⊆ ⋃ j, C j) (_ : ∀ j, ediam (C j) ≤ ε),
            ∑' j, ⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) < ε := by
          refine lt_of_le_of_lt ?_ hε
          rw [← hZ', Measure.hausdorffMeasure_apply]
          exact le_iSup₂_of_le ε hε le_rfl
        simpa only [iInf_lt_iff, exists_prop] using h0
      obtain ⟨e, he0, hesum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
      have hCtop : ∀ j, ediam (C j) ≠ ⊤ := fun j =>
        ((hCε j).trans_lt (hε1.trans_lt ENNReal.one_lt_top)).ne
      have hele : ∀ j, (e j : ℝ≥0∞) < ε := fun j => (ENNReal.le_tsum j).trans_lt hesum
      -- side lengths `d j = max (diam C j) (e j) ∈ (0, 1]`
      set d : ℕ → ℝ := fun j => max (ediam (C j)).toReal (e j) with hd
      have hdpos : ∀ j, 0 < d j := fun j => lt_max_of_lt_right (he0 j)
      have hdofReal : ∀ j, ENNReal.ofReal (d j) = max (ediam (C j)) (e j) := by
        intro j
        rw [hd, ENNReal.ofReal_max, ENNReal.ofReal_toReal (hCtop j), ENNReal.ofReal_coe_nnreal]
      have hdε : ∀ j, ENNReal.ofReal (d j) ≤ ε := fun j => by
        rw [hdofReal]
        exact max_le (hCε j) (hele j).le
      have hd1 : ∀ j, d j ≤ 1 := by
        intro j
        have := (hdε j).trans hε1
        rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at this
      -- Step 6: boxes `[m + q d j, m + (q + 1) d j] × C j`, `q < p j`
      set p : ℕ → ℕ := fun j => ⌊1 / d j⌋₊ + 1 with hp
      set t : ℕ → ℕ → Set (ℝ × Euclid N) := fun j q =>
        if q < p j then Icc (m + q * d j) (m + (q + 1) * d j) ×ˢ C j else ∅ with ht
      have hpiece : ∀ j q, ediam (t j q) ≤ ENNReal.ofReal (d j) := by
        intro j q
        simp only [ht]
        split_ifs
        · refine (hdiam_prod _ _).trans (max_le ?_ ?_)
          · rw [Real.ediam_Icc]
            exact le_of_eq (congrArg ENNReal.ofReal (by ring))
          · rw [hdofReal]
            exact le_max_left _ _
        · simp
      refine ⟨fun i => t i.1 i.2, ?_, fun i => (hpiece i.1 i.2).trans (hdε i.1), ?_⟩
      · rintro ⟨s, x⟩ ⟨⟨hs1, hs2⟩, hx⟩
        obtain ⟨j, hxj⟩ := mem_iUnion.1 (hZC hx)
        have hsm : 0 ≤ (s - m) / d j := div_nonneg (sub_nonneg.2 hs1) (hdpos j).le
        have hq1 : (⌊(s - m) / d j⌋₊ : ℝ) ≤ (s - m) / d j := Nat.floor_le hsm
        have hq2 : (s - m) / d j < ⌊(s - m) / d j⌋₊ + 1 := Nat.lt_floor_add_one _
        have hqp : ⌊(s - m) / d j⌋₊ < p j := by
          refine Nat.lt_succ_of_le (Nat.floor_mono ?_)
          exact div_le_div_of_nonneg_right (by linarith) (hdpos j).le
        refine mem_iUnion.2 ⟨(j, ⌊(s - m) / d j⌋₊), ?_⟩
        simp only [ht, hqp, ↓reduceIte]
        refine ⟨⟨?_, ?_⟩, hxj⟩
        · rw [le_div_iff₀ (hdpos j)] at hq1
          linarith
        · rw [div_lt_iff₀ (hdpos j)] at hq2
          linarith
      -- Step 7: the `(n + 1)`-cost is `≤ 2 Σ (diam C j)ⁿ + 2 Σ e j ≤ 4ε`
      have hcostj : ∀ j, ∑' q, ediam (t j q) ^ ((n + 1 : ℕ) : ℝ) ≤
          2 * ((⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + e j) := by
        intro j
        rw [tsum_eq_sum (s := Finset.range (p j)) ?_]
        · calc ∑ q ∈ Finset.range (p j), ediam (t j q) ^ ((n + 1 : ℕ) : ℝ)
              ≤ ∑ q ∈ Finset.range (p j), ENNReal.ofReal (d j) ^ (n + 1) := by
                refine Finset.sum_le_sum fun q _ => ?_
                rw [ENNReal.rpow_natCast]
                exact pow_le_pow_left' (hpiece j q) _
            _ = (p j : ℝ≥0∞) * ENNReal.ofReal (d j) * ENNReal.ofReal (d j) ^ n := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
                ring
            _ ≤ 2 * ENNReal.ofReal (d j) ^ n := by
                gcongr
                rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
                  show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
                apply ENNReal.ofReal_le_ofReal
                have h1 : (⌊1 / d j⌋₊ : ℝ) ≤ 1 / d j := Nat.floor_le (by positivity)
                simp only [hp]
                push_cast
                calc ((⌊1 / d j⌋₊ : ℝ) + 1) * d j ≤ (1 / d j + 1) * d j := by gcongr
                  _ = 1 + d j := by rw [add_mul, one_div, inv_mul_cancel₀ (hdpos j).ne', one_mul]
                  _ ≤ 2 := by linarith [hd1 j]
            _ ≤ 2 * ((⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + e j) := by
                gcongr
                rw [hdofReal]
                rcases le_total (ediam (C j)) (e j : ℝ≥0∞) with h | h
                · rw [max_eq_right h]
                  refine le_add_left ?_
                  exact pow_le_of_le_one zero_le ((hele j).le.trans hε1) hn.ne'
                · rw [max_eq_left h]
                  refine le_add_right ?_
                  rcases (C j).eq_empty_or_nonempty with hC | hC
                  · rw [hC, ediam_empty, zero_pow hn.ne']
                    exact zero_le
                  · rw [← ENNReal.rpow_natCast]
                    exact le_iSup_of_le hC le_rfl
        · intro q hq
          rw [Finset.mem_range] at hq
          simp only [ht, hq, ↓reduceIte, ediam_empty]
          exact ENNReal.zero_rpow_of_pos (by positivity)
      calc ∑' i : ℕ × ℕ, ediam (t i.1 i.2) ^ ((n + 1 : ℕ) : ℝ)
          = ∑' j, ∑' q, ediam (t j q) ^ ((n + 1 : ℕ) : ℝ) :=
            ENNReal.tsum_prod (f := fun j q => ediam (t j q) ^ ((n + 1 : ℕ) : ℝ))
        _ ≤ ∑' j, 2 * ((⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + e j) :=
            ENNReal.tsum_le_tsum hcostj
        _ = 2 * (∑' j, (⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + ∑' j, (e j : ℝ≥0∞)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ ≤ 2 * (ε + ε) := by gcongr
        _ = 4 * ε := by ring
    -- Step 8: covers with mesh and cost tending to `0`
    choose t ht using fun k : ℕ => hcov ((k : ℝ≥0∞) + 1)⁻¹ (ENNReal.inv_pos.2 (by simp))
      (ENNReal.inv_le_one.2 le_add_self)
    have hr : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    refine le_antisymm ?_ bot_le
    calc μH[((n + 1 : ℕ) : ℝ)] (Icc (m : ℝ) (m + 1) ×ˢ Z)
        ≤ liminf (fun k => ∑' i, ediam (t k i) ^ ((n + 1 : ℕ) : ℝ)) atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum _ _ _ hr t
            (Eventually.of_forall fun k => (ht k).2.1) (Eventually.of_forall fun k => (ht k).1)
      _ ≤ liminf (fun k : ℕ => 4 * ((k : ℝ≥0∞) + 1)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => (ht k).2.2)
      _ = 0 := by
          refine Tendsto.liminf_eq ?_
          simpa using ENNReal.Tendsto.const_mul hr (Or.inr ENNReal.ofNat_ne_top)
  -- Step 4: `ℝ × Z` is the union of the strips
  refine measure_mono_null ?_ (measure_iUnion_null hstrip)
  rintro ⟨s, x⟩ ⟨-, hx⟩
  exact mem_iUnion.2 ⟨⌊s⌋, ⟨Int.floor_le s, (Int.lt_floor_add_one s).le⟩, hx⟩
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.ptd_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
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
/-- Localized Besicovitch density (Simon Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6, with
Simon Ch. 1, Theorem 3.16 = Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be
open, `A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e.
`x` and every `ε > 0`, `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`; the
exceptional set does not depend on `ε`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `a/β`, where
  `a = Hⁿ(A ∩ B̄_ρ(x))` and `β = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `a/β > 1 − ε`, which forces `0 < β < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = β − a ≤ εβ`. -/
theorem Submission.ptd_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many open balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2–3: Besicovitch density for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`, off one
  -- `Hⁿ⌞A`-null set for all `y ∈ D` at once
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
  -- Step 4: `x ∈ B(y, r y)` for some `y ∈ D`, so `B̄_ρ(x) ⊆ B̄(y, r y)` for `ρ < δ`
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- (i)–(ii): for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
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
  -- (iii): `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄(y, r y)) < ∞` for `ρ < δ`
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- (iv): `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
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
  -- Step 5: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- (a) `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- (b) `ε < 1`: eventually `a / β > 1 − ε`, with `β ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set β := μHE[n] (B ∩ closedBall x ρ)
    set a := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hβtop : β ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + a = β := hsplit ρ
    -- `β ≠ 0`, since otherwise `a / β = 0 / 0 = 0 ≤ 1 − ε`
    have hβ0 : β ≠ 0 := by
      intro h0
      have ha0 : a = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : a / β = 0 := by rw [ha0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * β < a :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hβ0) (Or.inl hβtop)).1 hρq
    -- `e + (1 − ε)β ≤ e + a = β = εβ + (1 − ε)β`, and `(1 − ε)β ≠ ∞`
    have h1 : e + (1 - ε) * β ≤ ε * β + (1 - ε) * β := by
      calc e + (1 - ε) * β ≤ e + a := by gcongr
        _ = β := hsplitρ
        _ = (ε + (1 - ε)) * β := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * β + (1 - ε) * β := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hβtop) h1

/-- **Simon Ch. 3, Remark 1.5(3)** (the upper bound, with `ε = 1`): if `D` has approximate
tangent space `Q` at `x` and `Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all
small `ρ > 0`.

* Test Definition 1.4 with `φ = max(0, min(1, 2 − |w|)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`:
  `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`, so for `0 < ρ < r₁` it is `< C := |Λ| + 1`, and
  `2ρ < r₀`.
* By the blow-up scaling, `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, so `φ` is
  integrable on `η_{x,ρ}(D)` and `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} φ dHⁿ < C`.
* Scaling back, `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ Cρⁿ`. -/
theorem Submission.ptd_tl_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1: the cutoff `φ = max(0, min(1, 2 − ‖w‖)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`
  have hout : ∀ w : Euclid P, w ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖w‖)) = 0 := by
    intro w hw
    rw [mem_closedBall_zero_iff, not_le] at hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let φ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun w => max 0 (min 1 (2 - ‖w‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hφ0 : ∀ w, 0 ≤ φ w := fun w => le_max_left _ _
  have hφ1 : ∀ w, φ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hφB : ∀ w ∈ closedBall (0 : Euclid P) 1, φ w = 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    show max 0 (min 1 (2 - ‖w‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 2: `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`; choose `r₁` such that
  -- `∫_{η_{x,ρ}(D)} φ dHⁿ < |Λ| + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set Λ := ∫ w in (Q : Set (Euclid P)), φ w ∂μHE[n]
  have hC : (0 : ℝ) ≤ |Λ| + 1 := by positivity
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, φ w ∂μHE[n]) < |Λ| + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 φ).eventually_lt_const ((le_abs_self Λ).trans_lt (lt_add_one _))).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨|Λ| + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hI, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.2 hρ).ne'
  -- the blow-up scaling with `R = 2` and `R = 1`
  have h2 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 2 D hρ
  have h1 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 1 D hρ
  rw [mul_one ρ] at h1
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  -- Step 3: `Hⁿ(T ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, as `2ρ < r₀`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    rw [h2]
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hρ0)) ?_
    refine ne_top_of_le_ne_top hfin (measure_mono (Set.inter_subset_inter_right _ ?_))
    exact closedBall_subset_closedBall (by linarith)
  -- Step 4: `|φ| ≤ 1_{B̄₂(0)}`, which is integrable for `Hⁿ⌞T`; hence so is `φ`
  have hint : Integrable (fun w => φ w) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      φ.continuous.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hw : w ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hw, Real.norm_of_nonneg (hφ0 w)]
        exact hφ1 w
      · rw [Set.indicator_of_notMem hw, norm_le_zero_iff]
        exact hout w hw
  -- Step 5: `Hⁿ(T ∩ B̄₁(0)) = ∫⁻ 1_{B̄₁(0)} d(Hⁿ⌞T) ≤ ∫⁻ φ d(Hⁿ⌞T) = ∫_T φ dHⁿ < |Λ| + 1`
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (|Λ| + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ w, (closedBall (0 : Euclid P) 1).indicator 1 w ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ w, ENNReal.ofReal (φ w) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hw, Pi.one_apply, hφB w hw, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hw]
            exact zero_le
      _ = ENNReal.ofReal (∫ w, φ w ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hφ0)).symm
      _ ≤ ENNReal.ofReal (|Λ| + 1) := ENNReal.ofReal_le_ofReal hI.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(T ∩ B̄₁(0)) ≤ (|Λ| + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      = ENNReal.ofReal ρ ^ n * ((ENNReal.ofReal ρ)⁻¹ ^ n * μHE[n] (D ∩ closedBall x ρ)) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hρ0 ENNReal.ofReal_ne_top, one_pow,
          one_mul]
    _ = ENNReal.ofReal ρ ^ n * μHE[n] (T ∩ closedBall 0 1) := by rw [h1]
    _ ≤ ENNReal.ofReal ρ ^ n * ENNReal.ofReal (|Λ| + 1) := by gcongr
    _ = ENNReal.ofReal ((|Λ| + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hρ.le, mul_comm (ENNReal.ofReal ρ ^ n)]
/-- Zero `n`-density of the excess `B ∖ A` (step 6 of the tangent-locality argument for a piece):
if `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0` as
`ρ ↓ 0`.  With `ε = 1/2`, subadditivity and cancellation of the finite half give
`Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ`; then `ε = δ/(2C + 1)` gives
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.ptd_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hG hE
  -- Step 1: for `ρ > 0`, `ofReal (Cρⁿ) = ofReal C · (ofReal ρ)ⁿ`
  have hA : ∀ ρ : ℝ, 0 < ρ → ρ < r₁ →
      μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal C * ENNReal.ofReal ρ ^ n := by
    intro ρ hρ hρ₁
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul' (pow_nonneg hρ.le n)]
    exact hG ρ hρ hρ₁
  -- Step 2: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ κ (ofReal ρ)ⁿ` with `κ = 2 ofReal C`
  set κ : ℝ≥0∞ := 2 * ENNReal.ofReal C with hκ
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ κ * ENNReal.ofReal ρ ^ n := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hE 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := hρ.2.le.trans (min_le_left _ _)
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hβ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hρ₀)))
    -- `B ∩ B̄_ρ(x) ⊆ (A ∩ B̄_ρ(x)) ∪ ((B ∖ A) ∩ B̄_ρ(x))`, so subadditivity applies
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- `β/2 + β/2 = β ≤ a + e ≤ a + β/2`; cancelling the finite `β/2` gives `β/2 ≤ a`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hβ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add le_rfl he)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * (ENNReal.ofReal C * ENNReal.ofReal ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = κ * ENNReal.ofReal ρ ^ n := by rw [hκ, mul_assoc]
  -- Step 3: for `δ > 0`, `ε = δ/(κ + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δ (ofReal ρ)ⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hκ₁ : κ + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hκ₀ : κ + 1 ≠ 0 := by positivity
  filter_upwards [hB, hE (δ / (κ + 1)) (ENNReal.div_pos hδ.ne' hκ₁)] with ρ hρB hρe
  -- Step 4: hence `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / (ofReal ρ)ⁿ ≤ δ`
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ)
      ≤ δ / (κ + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (κ + 1) * ((κ + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hκ₀ hκ₁]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value
(by `Submission.ptd_tl_blowUp_measure_scaling`), and this tends to `0`. -/
theorem Submission.ptd_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)` is Borel
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
  -- Step 2: for every `f ∈ C_c`, `Δ_f(ρ) = ∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- (a): `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- (b): `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
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
    -- (c)–(e) give `|Δ_f(ρ)| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for `0 < ρ < r₀/R`; (f) sends the
    -- bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- (c): for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- (d): `Δ_f(ρ) = ∫_{η_{x,ρ}(B ∖ A)} f`, as `η_{x,ρ}(B ∖ A) = η_{x,ρ}(B) ∖ η_{x,ρ}(A)`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- (e): `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- (f): `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
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
      rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
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
  -- Steps 3–4: transfer the limits of Definition 1.4 in both directions; `finrank Q = n` is shared
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

/-- **Simon Ch. 3, Remarks 1.5(2)–(3) and the proof of Theorem 1.6 "⇒"**: let `U` be open,
`A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x`,
simultaneously for every subspace `Q`, `B` has approximate tangent space `Q` at `x` iff `A` does.

* Off one `Hⁿ⌞A`-null set, independent of `Q`, `x ∈ A` and for every `ε > 0`,
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0` (Besicovitch).
* `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U` is compact, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`.
* A tangent plane of `B` or of `A` at `x` gives `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for small `ρ` (via
  `A ⊆ B` in the first case), hence `Hⁿ((B \ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals
  of `B` and `A` have the same limits. -/
theorem Submission.ptd_ae_approxTangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 2–4: off one `Hⁿ⌞A`-null set, chosen before `Q`, `x ∈ A` and the excess of `B` over
  -- `A` near `x` is eventually small relative to `Hⁿ(B ∩ B̄_ρ(x))`
  filter_upwards [Submission.ptd_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB_le : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 6–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` makes the excess `o(ρⁿ)`, which forces
  -- the same approximate tangent spaces
  have hiff : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.ptd_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.ptd_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth
          hexc) Q
  -- Step 8: step 5 turns the assumed tangent plane into the growth bound
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (hiff C r₁ hr₁ fun ρ hρ hρr₁ => (hAB_le ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB_le (s / 2))) hTA
    exact (hiff C r₁ hr₁ hgrowth).2 hTA
/-- Borel image and null-set pullback along a bi-Lipschitz piece: if `F : ℝⁿ → ℝᴾ` is Lipschitz,
`B ⊆ ℝⁿ` is Borel and `m‖a − a'‖ ≤ ‖F a − F a'‖` on `B` (`m > 0`), then `F(B)` is Borel
(Lusin–Souslin), and a property holding `Hⁿ⌞F(B)`-a.e. holds at `F b` for Lebesgue-a.e. `b ∈ B`:
`invFunOn F B` is `m⁻¹`-Lipschitz on `F(B)` (Simon Ch. 2, 1.8(i)) and maps the `Hⁿ`-null bad
image set onto a superset of the bad parameters, and `Hⁿ` is Lebesgue measure on `ℝⁿ`. -/
theorem Submission.ptd_piece_image_measurable_ae_pullback : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → MeasurableSet (F '' B) ∧ ∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ b ∂(volume.restrict B), p (F b) := by
  intro P n F B L m hF hB hm hlow
  -- Step 1: the lower bound makes `F` injective on `B`
  have hinj : InjOn F B := fun a ha a' ha' h => by
    have hle := hlow a ha a' ha'
    rw [h, sub_self, norm_zero] at hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle hm))
  -- Step 2: Lusin–Souslin
  have hFB : MeasurableSet (F '' B) := hB.image_of_continuousOn_injOn hF.continuous.continuousOn hinj
  refine ⟨hFB, fun p hp => ?_⟩
  -- Step 3: `G = invFunOn F B` is `m⁻¹`-Lipschitz on `F '' B`
  have hG : LipschitzOnWith (Real.toNNReal m⁻¹) (invFunOn F B) (F '' B) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [hinj.leftInvOn_invFunOn ha, hinj.leftInvOn_invFunOn ha', dist_eq_norm, dist_eq_norm,
      inv_mul_eq_div, le_div_iff₀' hm]
    exact hlow a ha a' ha'
  -- Step 4: the bad parameters lie in the `G`-image of the `Hⁿ`-null bad image set
  rw [ae_restrict_iff' hFB, ae_iff] at hp
  rw [ae_restrict_iff' hB, ae_iff, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hnull : μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)}) = 0 := by
    refine le_zero_iff.1 ?_
    calc μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)})
        ≤ (Real.toNNReal m⁻¹ : ℝ≥0∞) ^ n * μHE[n] {y | ¬(y ∈ F '' B → p y)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hG.mono fun y hy => (not_imp.1 hy).1)
      _ = 0 := by rw [hp, mul_zero]
  refine measure_mono_null (fun b hb => ?_) hnull
  obtain ⟨hbB, hpb⟩ := not_imp.1 (show ¬(b ∈ B → p (F b)) from hb)
  exact ⟨F b, show ¬(F b ∈ F '' B → p (F b)) from not_imp.2 ⟨mem_image_of_mem F hbB, hpb⟩,
    hinj.leftInvOn_invFunOn hbB⟩
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.pit_setIntegral_blowUpMap_image : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
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

/-- **Rescaled area formula** (Jacobian kept abstract): if `F` is continuous, `B` and `J ≥ 0` are
Borel and `∫⁻_{F(B)} g dHⁿ = ∫⁻_B J(x) g(F(x)) dλ(x)` for every `g ≥ 0`, then for `r > 0` and
continuous `f`,
`∫_{η_{F(b),r}(F(B))} f dHⁿ = ∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dλ(c)`.
The area hypothesis says `Hⁿ⌞F(B) = F_#ν` with `ν = J λ⌞B`, which transports every integral;
the substitution `a = b + rc` produces the factor `rⁿ` that cancels the `r⁻ⁿ` of the blow-up. -/
theorem Submission.pit_blowUp_image_setIntegral_eq_rescaled : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (b : Euclid n) (r : ℝ) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume) → 0 < r → Continuous f → ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (F b) r '' (F '' B), f z ∂μHE[n] = ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume := by
  intro P n F B J b r f hF hB hJ hJ0 harea hr hf
  -- blow-up scaling: `∫_{η(F(B))} f dHⁿ = r⁻ⁿ ∫_{F(B)} f ∘ η dHⁿ`, `η = η_{F(b),r}`
  rw [Submission.pit_setIntegral_blowUpMap_image P n (F '' B) (F b) r hr f]
  -- `Hⁿ⌞F(B) = F_#ν`: the area hypothesis with `g = 1_T` for every Borel `T`
  have hmeas : μHE[n].restrict (F '' B) =
      Measure.map F ((volume.restrict B).withDensity fun x => ENNReal.ofReal (J x)) := by
    ext T hT
    have h := harea (T.indicator 1)
    rw [lintegral_indicator_one hT] at h
    rw [h, Measure.map_apply hF.measurable hT, withDensity_apply _ (hT.preimage hF.measurable),
      ← lintegral_indicator (hT.preimage hF.measurable)]
    congr 1
    funext x
    by_cases hx : F x ∈ T <;> simp [hx]
  -- `∫_{F(B)} f ∘ η dHⁿ = ∫ 1_B J (f ∘ η ∘ F) dλ`, with no integrability needed
  have hη : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r z) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hpull : ∫ y in F '' B, f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r y) ∂μHE[n] =
      ∫ x, B.indicator J x * f (r⁻¹ • (F x - F b)) ∂volume := by
    rw [hmeas, integral_map hF.aemeasurable hη.aestronglyMeasurable]
    have h := integral_withDensity_eq_integral_smul (μ := volume.restrict B) hJ.real_toNNReal
      (fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r (F x)))
    simp only [ENNReal.ofReal]
    rw [h, ← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B
    · simp [hx, NNReal.smul_def, hJ0 x, Poincare.SimonGMT.Chapter03.blowUpMap]
    · simp [hx]
  rw [hpull]
  -- substitution `a = b + rc`: `∫ G(b + rc) dλ(c) = r⁻ⁿ ∫ G dλ`
  set G : Euclid n → ℝ := fun x => B.indicator J x * f (r⁻¹ • (F x - F b))
  have hsubst : ∫ c, G (b + r • c) ∂volume = r⁻¹ ^ n * ∫ a, G a ∂volume := by
    rw [Measure.integral_comp_smul volume (fun x => G (b + x)) r,
      integral_add_left_eq_self (fun x => G x) b, finrank_euclideanSpace_fin, smul_eq_mul,
      ← inv_pow, abs_of_pos (pow_pos (inv_pos.2 hr) n)]
  exact hsubst.symm
/-- Co-Lipschitz bounds pass to the derivative at density points: if `m > 0`,
`m‖a − b‖ ≤ ‖F(a) − F(b)‖` for every `a ∈ B` (`B` arbitrary), `F` is differentiable at `b` and
`λ(B ∩ B̄_ρ(b)) / λ(B̄_ρ(b)) → 1` as `ρ ↓ 0`, then `m‖c‖ ≤ ‖DF(b)c‖` for every `c`.
For small `r > 0` the ball `B_{rδ}(b + rc)`, a fixed fraction `(δ / (‖c‖ + δ))ⁿ` of
`B̄_{r(‖c‖+δ)}(b)`, must meet `B`; the bound at such a point and differentiability give
`m‖c‖ ≤ ‖DF(b)c‖ + δ(m + ‖DF(b)‖ + ‖c‖ + δ)`, and `δ ↓ 0`. -/
theorem Submission.pit_fderiv_lower_bound_of_density : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (m : ℝ) (b : Euclid n), 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → ∀ c : Euclid n, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ := by
  intro P n F B m b hm hB hF hdens c
  set L := fderiv ℝ F b with hL
  have hFL : HasFDerivAt F L b := hF.hasFDerivAt
  -- main estimate: for every `δ > 0`, `m‖c‖ ≤ ‖Lc‖ + δ (m + ‖L‖ + ‖c‖ + δ)`
  have key : ∀ δ : ℝ, 0 < δ → m * ‖c‖ ≤ ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ) := by
    intro δ hδ
    have hK : 0 < ‖c‖ + δ := by positivity
    -- differentiability: `‖F a - F b - L (a - b)‖ ≤ δ ‖a - b‖` near `b`
    obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.1 (hFL.isLittleO.bound hδ)
    -- density: the ratio exceeds `1 - q`, `q = (δ / (‖c‖ + δ)) ^ n`, on some `(0, ρ₀)`
    obtain ⟨q, hq_def⟩ : ∃ q : ℝ≥0∞, q = ENNReal.ofReal ((δ / (‖c‖ + δ)) ^ n) := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq_def, Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hlt : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.1 (hdens.eventually_const_lt hlt)
    have hρ₀' : 0 < ρ₀ := hρ₀
    -- the radius `ρ = r (‖c‖ + δ)`
    obtain ⟨ρ, hρ, hρε, hρρ₀⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ρ < ρ₀ :=
      ⟨min ε ρ₀ / 2, by positivity, by linarith [min_le_left ε ρ₀, lt_min hε hρ₀'],
        by linarith [min_le_right ε ρ₀, lt_min hε hρ₀']⟩
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / (‖c‖ + δ) := ⟨_, rfl⟩
    have hr : 0 < r := by rw [hr_def]; positivity
    have hrK : r * (‖c‖ + δ) = ρ := by rw [hr_def]; field_simp
    -- some point of `B` lies in `B_{rδ}(b + r c)`, else the ratio at `ρ` is `≤ 1 - q`
    obtain ⟨a, haB, ha⟩ : ∃ a ∈ B, ‖a - (b + r • c)‖ < r * δ := by
      by_contra! hcon
      have hsub : ball (b + r • c) (r * δ) ⊆ closedBall b ρ := by
        intro x hx
        rw [mem_ball, dist_eq_norm] at hx
        rw [mem_closedBall, dist_eq_norm]
        calc ‖x - b‖ = ‖(x - (b + r • c)) + r • c‖ := by congr 1; abel
          _ ≤ ‖x - (b + r • c)‖ + ‖r • c‖ := norm_add_le _ _
          _ = ‖x - (b + r • c)‖ + r * ‖c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
          _ ≤ ρ := by rw [← hrK]; linarith
      have hBsub : B ∩ closedBall b ρ ⊆ closedBall b ρ \ ball (b + r • c) (r * δ) := by
        rintro x ⟨hxB, hx⟩
        refine ⟨hx, fun hxW => ?_⟩
        rw [mem_ball, dist_eq_norm] at hxW
        exact (hcon x hxB).not_gt hxW
      have hVfin : volume (closedBall b ρ) ≠ ∞ := measure_closedBall_lt_top.ne
      have hball : volume (ball (b + r • c) (r * δ)) = q * volume (closedBall b ρ) := by
        rw [Measure.addHaar_ball_of_pos volume _ (mul_pos hr hδ),
          Measure.addHaar_closedBall volume _ hρ.le, finrank_euclideanSpace_fin, ← mul_assoc,
          hq_def, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (δ / (‖c‖ + δ)) ^ n), ← mul_pow,
          ← hrK]
        congr 3
        field_simp
      have hle : volume (B ∩ closedBall b ρ) ≤ (1 - q) * volume (closedBall b ρ) := by
        calc volume (B ∩ closedBall b ρ)
            ≤ volume (closedBall b ρ \ ball (b + r • c) (r * δ)) := measure_mono hBsub
          _ = volume (closedBall b ρ) - volume (ball (b + r • c) (r * δ)) :=
            measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
          _ = (1 - q) * volume (closedBall b ρ) := by
            rw [hball, ENNReal.sub_mul (fun _ _ => hVfin), one_mul]
      have hgt : 1 - q < volume (B ∩ closedBall b ρ) / volume (closedBall b ρ) :=
        hρ₀sub ⟨hρ, hρρ₀⟩
      exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
    -- the estimate at `a`, with `a - b = r c + e`, `‖e‖ < r δ`
    obtain ⟨e, he_def⟩ : ∃ e : Euclid n, e = a - (b + r • c) := ⟨_, rfl⟩
    rw [← he_def] at ha
    have hab : a - b = r • c + e := by rw [he_def]; abel
    have hab_le : ‖a - b‖ ≤ r * ‖c‖ + ‖e‖ := by
      rw [hab]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
    have hab_lt : ‖a - b‖ < r * (‖c‖ + δ) := by rw [mul_add]; linarith
    have hdist : dist a b < ε := by rw [dist_eq_norm]; linarith
    have h1 : m * ‖a - b‖ ≤ ‖F a - F b‖ := hB a haB
    have h2 : ‖F a - F b‖ ≤ ‖L (a - b)‖ + δ * ‖a - b‖ := by
      have h := hεF hdist
      have h' := norm_sub_norm_le (F a - F b) (L (a - b))
      linarith
    have h3 : ‖L (a - b)‖ ≤ r * ‖L c‖ + ‖L‖ * ‖e‖ := by
      rw [hab, map_add, map_smul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      linarith [L.le_opNorm e]
    have h4 : r * ‖c‖ ≤ ‖a - b‖ + ‖e‖ := by
      have : r • c = (a - b) - e := by rw [hab]; abel
      calc r * ‖c‖ = ‖r • c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ = ‖(a - b) - e‖ := by rw [this]
        _ ≤ ‖a - b‖ + ‖e‖ := norm_sub_le _ _
    have h5 : ‖L‖ * ‖e‖ ≤ ‖L‖ * (r * δ) := mul_le_mul_of_nonneg_left ha.le (norm_nonneg _)
    have h6 : m * ‖e‖ ≤ m * (r * δ) := mul_le_mul_of_nonneg_left ha.le hm.le
    have h7 : δ * ‖a - b‖ ≤ δ * (r * (‖c‖ + δ)) := mul_le_mul_of_nonneg_left hab_lt.le hδ.le
    have h8 : m * (r * ‖c‖) ≤ m * (‖a - b‖ + ‖e‖) := mul_le_mul_of_nonneg_left h4 hm.le
    have hfin : r * (m * ‖c‖) ≤ r * (‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by
      linarith
    exact le_of_mul_le_mul_left hfin hr
  -- let `δ → 0⁺`
  have hlim : Tendsto (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) (𝓝[>] 0) (𝓝 ‖L c‖) := by
    have hcont : Continuous (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
/-- If `F` has derivative `L` at `b` and `f` is continuous with compact support, then
`∫_{B̄_R(0)} |f(r⁻¹(F(b + rc) − F(b))) − f(Lc)| dc → 0` as `r ↓ 0` (the error term `T₃` in the
limit of rescaled integrals over the image of a `C¹` piece; cf. the tangent-plane limit in Simon
Ch. 3, proof of 1.6 "⇒").  With `V = |B̄_R(0)|` and `S = |R| + 1`, take `η` from the uniform
continuity of `f` for `ε / (V + 1)`, then `δ₀` with `‖F(b + k) − F(b) − Lk‖ ≤ (η / 2S)‖k‖` for
`‖k‖ < δ₀`; for `0 < r < δ₀ / S` the integrand is `≤ ε / (V + 1)` on the ball. -/
theorem Submission.pit_ril_diffQuot_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (b : Euclid n) (f : Euclid P → ℝ) (R : ℝ), HasFDerivAt F L b → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro P n F L b f R hF hfc hfs
  -- `D = B̄_R(0)` has finite measure `V`, and `‖c‖ < S = |R| + 1` on `D`
  have hDfin : (volume : Measure (Euclid n)) (closedBall 0 R) < ∞ := measure_closedBall_lt_top
  set V : ℝ := (volume : Measure (Euclid n)).real (closedBall 0 R)
  have hV : 0 ≤ V := measureReal_nonneg
  set S : ℝ := |R| + 1
  have hS : 0 < S := by positivity
  have hcS : ∀ c ∈ closedBall (0 : Euclid n) R, ‖c‖ < S := fun c hc =>
    ((mem_closedBall_zero_iff.1 hc).trans (le_abs_self R)).trans_lt (lt_add_one _)
  -- uniform continuity of `f` and the little-o form of `HasFDerivAt`
  have huc := Metric.uniformContinuous_iff.1 (hfs.uniformContinuous_of_continuous hfc)
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hV1 : 0 < V + 1 := by linarith
  set ε₁ : ℝ := ε / (V + 1) with hε₁_def
  have hε₁ : 0 < ε₁ := div_pos hε hV1
  obtain ⟨η, hη, hηf⟩ := huc ε₁ hε₁
  set θ : ℝ := η / (2 * S) with hθ_def
  have hθ : 0 < θ := div_pos hη (by linarith)
  obtain ⟨δ₀, hδ₀, hδ₀F⟩ := Metric.eventually_nhds_iff.1 (hlo.bound hθ)
  refine ⟨δ₀ / S, div_pos hδ₀ hS, fun r hr hrδ => ?_⟩
  rw [mem_Ioi] at hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hrδ
  have hrS : r * S < δ₀ := (lt_div_iff₀ hS).1 hrδ
  -- pointwise bound on the integrand
  have hpt : ∀ c ∈ closedBall (0 : Euclid n) R,
      ‖‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖ ≤ ε₁ := by
    intro c hc
    have hc' := hcS c hc
    have hnorm : ‖r • c‖ = r * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hrc : dist (r • c) 0 < δ₀ := by
      rw [dist_zero_right, hnorm]
      calc r * ‖c‖ ≤ r * S := mul_le_mul_of_nonneg_left hc'.le hr.le
        _ < δ₀ := hrS
    have hbound := hδ₀F hrc
    have heq : r⁻¹ • (F (b + r • c) - F b) - L c
        = r⁻¹ • (F (b + r • c) - F b - L (r • c)) := by
      rw [map_smul, smul_sub _ (F (b + r • c) - F b), inv_smul_smul₀ hr.ne']
    have hclose : dist (r⁻¹ • (F (b + r • c) - F b)) (L c) < η := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      calc r⁻¹ * ‖F (b + r • c) - F b - L (r • c)‖
          ≤ r⁻¹ * (θ * ‖r • c‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr.le)
        _ = θ * ‖c‖ := by rw [hnorm]; field_simp
        _ ≤ θ * S := mul_le_mul_of_nonneg_left hc'.le hθ.le
        _ = η / 2 := by rw [hθ_def]; field_simp
        _ < η := half_lt_self hη
    have := hηf hclose
    rw [Real.dist_eq] at this
    rw [norm_norm, Real.norm_eq_abs]
    exact this.le
  -- integral bound
  have hint := norm_setIntegral_le_of_norm_le_const hDfin hpt
  rw [dist_zero_right]
  calc ‖∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖
      ≤ ε₁ * V := hint
    _ < ε := by
      rw [hε₁_def, div_mul_eq_mul_div, div_lt_iff₀ hV1]
      nlinarith
/-- At a point `b` of Lebesgue density one of the Borel set `B` (`λ(B ∩ B̄_ρ(b))/λ(B̄_ρ(b)) → 1`
as `ρ ↓ 0`, the quotient taken in `[0, ∞]`), the averages `⨍_{B̄_s(b)} 1_{ℝⁿ∖B} dλ` tend to `0`
as `s ↓ 0`.  For `s > 0`, `0 < λ(B̄_s(b)) < ∞` and, by additivity, the average equals
`1 − (λ(B ∩ B̄_s(b))/λ(B̄_s(b))).toReal`; `toReal` is continuous at `1`. -/
theorem Submission.pit_ril_compl_average_tendsto : ∀ (n : ℕ) (B : Set (Euclid n)) (b : Euclid n), MeasurableSet B → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, Bᶜ.indicator (fun _ => (1 : ℝ)) a ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n B b hB hlim
  -- `q(ρ).toReal → 1` (`toReal` is continuous at `1 ≠ ∞`), so `1 - q(ρ).toReal → 0`
  have h1 : Tendsto (fun ρ : ℝ =>
      1 - (volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).sub
      ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim)
    rwa [ENNReal.toReal_one, sub_self] at h
  refine h1.congr' ?_
  -- for `s > 0`, `0 < λ(C_s) < ∞` and the average equals `1 - q(s).toReal`
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hfin : volume (closedBall b s) ≠ ∞ := measure_closedBall_lt_top.ne
  have hC : volume.real (closedBall b s) ≠ 0 :=
    (ENNReal.toReal_pos (measure_closedBall_pos volume b hs).ne' hfin).ne'
  -- `λ_ℝ(C_s ∩ B) + λ_ℝ(C_s \ B) = λ_ℝ(C_s)`
  have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := closedBall b s) hB hfin
  rw [setAverage_eq, setIntegral_indicator hB.compl, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, inter_comm B,
    ← Set.sdiff_eq, ← hsplit]
  rw [← hsplit] at hC
  field_simp
  ring
/-- Localised three-term estimate for the rescaled area integrals (one fixed `r > 0`).  With
`Φ_r(c) = r⁻¹(F(b + rc) − F(b))` and `D = B̄_{R/m}(0)`, the integrands
`X(c) = 1_B(b + rc) J(b + rc) f(Φ_r(c))` and `Y(c) = J(b) f(Lc)` vanish off `D` (by the lower
bounds for `F` on `B` and for `L`, as `f = 0` off the open `R`-ball), and pointwise
`|X − Y| ≤ KM·1_{Bᶜ}(b + rc) + M|J(b + rc) − J(b)| + J(b)|f(Φ_r(c)) − f(Lc)|`, by cases on
`b + rc ∈ B`; all are bounded Borel functions, so integrate over `D`. -/
theorem Submission.pit_ril_three_term_bound : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ) (R M r : ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → (∀ c, m * ‖c‖ ≤ ‖L c‖) → Continuous f → (∀ w, R ≤ ‖w‖ → f w = 0) → (∀ w, ‖f w‖ ≤ M) → 0 < r → ‖(∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) - J b * (∫ c, f (L c) ∂volume)‖ ≤ K * M * (∫ c in closedBall (0 : Euclid n) (R / m), Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) ∂volume) + M * (∫ c in closedBall (0 : Euclid n) (R / m), ‖J (b + r • c) - J b‖ ∂volume) + J b * (∫ c in closedBall (0 : Euclid n) (R / m), ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) := by
  intro P n F L B J K m b f R M r hF hB hJ hJK hm hFB hL hf hfR hfM hr
  -- constants: `0 ≤ M`, `0 ≤ J b ≤ K`, `0 ≤ K`, and `λ(D) < ∞` for `D = B̄_{R/m}(0)`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfM 0)
  have hJb0 : 0 ≤ J b := (hJK b).1
  have hJbK : J b ≤ K := (hJK b).2
  have hK0 : 0 ≤ K := hJb0.trans hJbK
  have hDfin : volume (closedBall (0 : Euclid n) (R / m)) ≠ ∞ := measure_closedBall_lt_top.ne
  -- measurability of the integrands
  have hshift : Continuous fun c : Euclid n => b + r • c :=
    continuous_const.add (continuous_id.const_smul r)
  have hΦ : Continuous fun c : Euclid n => f (r⁻¹ • (F (b + r • c) - F b)) :=
    hf.comp (((hF.comp hshift).sub continuous_const).const_smul r⁻¹)
  have hfL : Continuous fun c : Euclid n => f (L c) := hf.comp L.continuous
  have hIJ : Measurable fun c : Euclid n => B.indicator J (b + r • c) :=
    (hJ.indicator hB).comp hshift.measurable
  have hg₁ : Measurable fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) :=
    (measurable_const.indicator hB.compl).comp hshift.measurable
  have hg₂ : Measurable fun c : Euclid n => ‖J (b + r • c) - J b‖ :=
    ((hJ.comp hshift.measurable).sub measurable_const).norm
  have hg₃ : Continuous fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
    (hΦ.sub hfL).norm
  -- bounded measurable functions are integrable on `D`
  have hIJb : ∀ c : Euclid n, ‖B.indicator J (b + r • c)‖ ≤ K := by
    intro c
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (hJK _).1]
      exact (hJK _).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact hK0
  have hXint : IntegrableOn
      (fun c : Euclid n => B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (hIJ.mul hΦ.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul]
    exact mul_le_mul (hIJb c) (hfM _) (norm_nonneg _) hK0
  have hYint : IntegrableOn (fun c : Euclid n => J b * f (L c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (measurable_const.mul hfL.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul, Real.norm_of_nonneg hJb0]
    exact mul_le_mul hJbK (hfM _) (norm_nonneg _) hK0
  have hg₁int : IntegrableOn (fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := 1) hDfin hg₁.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    by_cases h : b + r • c ∈ Bᶜ
    · rw [Set.indicator_of_mem h, norm_one]
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact zero_le_one
  have hg₂int : IntegrableOn (fun c : Euclid n => ‖J (b + r • c) - J b‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K) hDfin hg₂.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm, Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hJK (b + r • c), hJK b]
  have hg₃int : IntegrableOn
      (fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := M + M) hDfin hg₃.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hfM _) (hfM _))
  -- localisation: both integrands vanish off `D`
  have hloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → R < m * ‖c‖ := by
    intro c hc
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hc
    rwa [mul_comm] at hc
  have hXloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) →
      B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) = 0 := by
    intro c hc
    by_cases h : b + r • c ∈ B
    · have h1 := hFB _ h
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h2 : R ≤ ‖r⁻¹ • (F (b + r • c) - F b)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc R ≤ m * ‖c‖ := (hloc c hc).le
          _ = r⁻¹ * (m * (r * ‖c‖)) := by rw [mul_left_comm m r, inv_mul_cancel_left₀ hr.ne']
          _ ≤ r⁻¹ * ‖F (b + r • c) - F b‖ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hr.le)
      rw [hfR _ h2, mul_zero]
    · rw [Set.indicator_of_notMem h, zero_mul]
  have hYloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → J b * f (L c) = 0 := by
    intro c hc
    rw [hfR _ ((hloc c hc).le.trans (hL c)), mul_zero]
  -- pointwise three-term estimate, by cases on `b + r • c ∈ B`
  have hpt : ∀ c : Euclid n,
      ‖B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖ ≤
        K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) + M * ‖J (b + r • c) - J b‖ +
          J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
    intro c
    have hu := hfM (r⁻¹ • (F (b + r • c) - F b))
    have hv := hfM (L c)
    have hA : 0 ≤ M * ‖J (b + r • c) - J b‖ := mul_nonneg hM0 (norm_nonneg _)
    have hB' : 0 ≤ J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
      mul_nonneg hJb0 (norm_nonneg _)
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h), mul_zero,
        zero_add]
      have hJu := mul_le_mul_of_nonneg_left hu (norm_nonneg (J (b + r • c) - J b))
      calc ‖J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖
          = ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b)) +
              J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := by
            congr 1
            ring
        _ ≤ ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b))‖ +
              ‖J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := norm_add_le _ _
        _ = ‖J (b + r • c) - J b‖ * ‖f (r⁻¹ • (F (b + r • c) - F b))‖ +
              J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg hJb0]
        _ ≤ M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            linarith [mul_comm M ‖J (b + r • c) - J b‖]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), zero_mul, zero_sub,
        norm_neg, norm_mul, Real.norm_of_nonneg hJb0, mul_one]
      have hJv : J b * ‖f (L c)‖ ≤ K * M := mul_le_mul hJbK hv (norm_nonneg _) hK0
      linarith
  -- integrate the pointwise estimate over `D`
  have h1 : (∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m),
        B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hXloc).symm
  have h2 : J b * (∫ c, f (L c) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m), J b * f (L c) ∂volume := by
    rw [← integral_const_mul]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hYloc).symm
  have hG₁₂ : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖) (closedBall (0 : Euclid n) (R / m)) volume :=
    (hg₁int.const_mul _).add (hg₂int.const_mul _)
  have hG : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume :=
    hG₁₂.add (hg₃int.const_mul _)
  rw [h1, h2, ← integral_sub hXint hYint]
  refine (norm_integral_le_of_norm_le hG (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add hG₁₂ (hg₃int.const_mul _), integral_add (hg₁int.const_mul _) (hg₂int.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
/-- **Rescaled integrals at a point of vanishing ball averages**: for `R > 0`, if
`⨍_{B̄_s(b)} h → 0` as `s → 0⁺`, then `∫_{B̄_R(0)} h(b + rc) dc → 0` as `r → 0⁺`.
For `r > 0`, dilation by `r` and translation by `b` give
`∫_{B̄_R(0)} h(b + rc) dc = r⁻ⁿ ∫_{B̄_{rR}(b)} h = ω Rⁿ ⨍_{B̄_{rR}(b)} h`, `ω = λ(B̄₁(0))`. -/
theorem Submission.pit_integral_closedBall_rescale_tendsto : ∀ (n : ℕ) (h : Euclid n → ℝ) (b : Euclid n) (R : ℝ), 0 < R → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, h a ∂volume) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n h b R hR hlim
  -- `ω = λ(B̄₁(0)) ∈ (0, ∞)` and `λ(B̄_s(z)) = sⁿ ω` for `s ≥ 0`
  set ω : ℝ := volume.real (closedBall (0 : Euclid n) 1) with hω_def
  have hω : 0 < ω := by
    rw [hω_def, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  have hvol : ∀ (z : Euclid n) {s : ℝ}, 0 ≤ s → volume.real (closedBall z s) = s ^ n * ω := by
    intro z s hs
    rw [Measure.addHaar_real_closedBall' volume z hs, finrank_euclideanSpace_fin]
  -- for `r > 0`: `∫_{B̄_R(0)} h(b + rc) dc = Rⁿ ω ⨍_{B̄_{rR}(b)} h`
  have key : ∀ r : ℝ, 0 < r → ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
      R ^ n * ω * ⨍ a in closedBall b (r * R), h a ∂volume := by
    intro r hr
    set H : Euclid n → ℝ := (closedBall b (r * R)).indicator h with hH
    have hmem : ∀ c : Euclid n, b + r • c ∈ closedBall b (r * R) ↔ c ∈ closedBall (0 : Euclid n) R := by
      intro c
      rw [mem_closedBall, mem_closedBall, dist_self_add_left, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, mul_le_mul_iff_of_pos_left hr]
    -- `1_{B̄_R(0)}(c) h(b + rc) = H(b + rc)`
    have h1 : ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
        ∫ c, H (b + r • c) ∂volume := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      ext c
      by_cases hc : c ∈ closedBall (0 : Euclid n) R
      · rw [indicator_of_mem hc, hH, indicator_of_mem ((hmem c).2 hc)]
      · rw [indicator_of_notMem hc, hH, indicator_of_notMem (mt (hmem c).1 hc)]
    -- dilation by `r` and translation by `b`
    have h2 : ∫ c, H (b + r • c) ∂volume = (r ^ n)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [Measure.integral_comp_smul volume (fun x => H (b + x)) r, integral_add_left_eq_self H b,
        hH, integral_indicator measurableSet_closedBall, finrank_euclideanSpace_fin, smul_eq_mul,
        abs_of_pos (inv_pos.2 (pow_pos hr n))]
    have h3 : ⨍ a in closedBall b (r * R), h a ∂volume =
        ((r * R) ^ n * ω)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [setAverage_eq, hvol b (mul_pos hr hR).le, smul_eq_mul]
    rw [h1, h2, h3, mul_pow]
    field_simp
  -- `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have hlim' := (hlim.comp hmap).const_mul (R ^ n * ω)
  rw [mul_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (key r hr).symm

/-- **Rescaled integrals at a density point of `B` and a Lebesgue point of `J`**: let
`m|a − b| ≤ |F(a) − F(b)|` on `B`, `m|c| ≤ |Lc|` for `L = DF(b)`, `0 ≤ J ≤ K`, let `B` have
density `1` at `b` and `⨍_{B̄_ρ(b)} |J − J(b)| → 0`.  Then for `f ∈ C_c(ℝᴾ)`,
`∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dc → J(b) ∫ f(Lc) dc` as `r → 0⁺`.
With `f = 0` off `B_R(0)` and `|f| ≤ M`, the error is at most `K M T₁ + M T₂ + J(b) T₃`, where
`T₁, T₂, T₃` integrate `1_{Bᶜ}(b + rc)`, `|J(b + rc) − J(b)|` and
`|f(r⁻¹(F(b + rc) − F(b))) − f(Lc)|` over `B̄_{R/m}(0)`; each tends to `0`. -/
theorem Submission.pit_rescaled_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → (∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖) → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) (𝓝[>] 0) (𝓝 (J b * ∫ c, f (fderiv ℝ F b c) ∂volume)) := by
  intro P n F B J K m b f hF hB hJ hJK hm hFB hdiff hL hdens hLeb hf hfc
  -- `f = 0` off `B_R(0)` and `|f| ≤ M`; the integrals live on `B̄_{R/m}(0)`
  obtain ⟨R, hR, hRf⟩ := hfc.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hRm : 0 < R / m := div_pos hR hm
  -- `T₁ → 0`: `B` has density `1` at `b`
  have hT₁ := Submission.pit_integral_closedBall_rescale_tendsto n
    (Bᶜ.indicator fun _ => (1 : ℝ)) b (R / m) hRm
    (Submission.pit_ril_compl_average_tendsto n B b hB hdens)
  -- `T₂ → 0`: `b` is a Lebesgue point of `J`
  have hT₂ := Submission.pit_integral_closedBall_rescale_tendsto n (fun a => ‖J a - J b‖) b
    (R / m) hRm hLeb
  -- `T₃ → 0`: `r⁻¹(F(b + rc) − F(b)) → Lc` uniformly on `B̄_{R/m}(0)`
  have hT₃ := Submission.pit_ril_diffQuot_integral_tendsto P n F (fderiv ℝ F b) b f (R / m)
    hdiff.hasFDerivAt hf hfc
  have hlim := ((hT₁.const_mul (K * M)).add (hT₂.const_mul M)).add (hT₃.const_mul (J b))
  simp only [mul_zero, add_zero] at hlim
  -- squeeze `|I(r) − J(b) ∫ f(Lc) dc| ≤ K M T₁(r) + M T₂(r) + J(b) T₃(r)` for `r > 0`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Submission.pit_ril_three_term_bound P n F (fderiv ℝ F b) B J K m b f R M r hF hB hJ hJK
    hm hFB hL hf hRf hM hr
/-- Integral over the range of a linear map with constant Jacobian: if `T : ℝⁿ → ℝᴾ` is linear
and `Hⁿ(T(S)) = j λ(S)` for every `S ⊆ ℝⁿ` (`j ≥ 0`, `λ` Lebesgue measure), then for continuous
`f`, `∫_{T(ℝⁿ)} f dHⁿ = j ∫ f(T(c)) dλ(c)`.  On Borel `A`, `A ∩ T(ℝⁿ) = T(T⁻¹(A))`, so
`Hⁿ⌞T(ℝⁿ) = j T_#λ`. -/
theorem Submission.pit_setIntegral_range_linear : ∀ (P n : ℕ) (T : Euclid n →L[ℝ] Euclid P) (j : ℝ) (f : Euclid P → ℝ), 0 ≤ j → (∀ S : Set (Euclid n), μHE[n] (T '' S) = ENNReal.ofReal j * volume S) → Continuous f → ∫ y in (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = j * ∫ c, f (T c) ∂volume := by
  intro P n T j f hj hT hf
  -- the carrier of the submodule `range T` is the set `T(ℝⁿ)`
  have hrange : (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) = range T := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  -- `Hⁿ⌞T(ℝⁿ) = ofReal(j) • T_#λ`, checked on Borel sets
  have hmeas : μHE[n].restrict (range T) = ENNReal.ofReal j • volume.map T := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply T.measurable hA,
      ← image_preimage_eq_inter_range, hT, smul_eq_mul]
  -- change of variables, with `(ofReal j).toReal = j` since `j ≥ 0`
  rw [hrange, hmeas, integral_smul_measure,
    integral_map T.measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hj, smul_eq_mul]
/-- **Simon Ch. 3, 1.4** (approximate tangent spaces of a bi-Lipschitz piece): let `F : ℝⁿ → ℝᴾ`
be `L`-Lipschitz, `B ⊆ ℝⁿ` Borel and `m > 0` with `m|a − a'| ≤ |F a − F a'|` on `B`, and let `F`
be differentiable at every point of `B` with injective derivative.  Then for a.e. `b ∈ B`,
`F(B)` has approximate tangent space `range DF(b)` at `F b`.
With `J := normDet DF` (Borel, `0 ≤ J ≤ Lⁿ`) the injective area formula holds on `B`.  A.e.
`b ∈ B` is a density point of `B` and a Lebesgue point of `J`; there
`∫_{η_{F b,r}(F(B))} f dHⁿ = ∫ 1_B J(b + rc) f(r⁻¹(F(b + rc) − F b)) dc` tends to
`J(b) ∫ f(DF(b)c) dc = ∫_{range DF(b)} f dHⁿ` as `r ↓ 0`. -/
theorem Submission.ptd_piece_image_approxTangent_ae : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n (F '' B) (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F B L m hF hB hm hcolip hreg
  have hfin : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  -- the area Jacobian `J = normDet DF`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid n → ℝ, J = Poincare.SimonGMT.Chapter02.areaJacobianAt F :=
    ⟨_, rfl⟩
  have hJmeas : Measurable J := hJ ▸ Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
  have hJnonneg : ∀ a, 0 ≤ J a := hJ ▸ Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
  -- `Hⁿ(T(S)) = normDet T · λ(S)` for every linear `T`
  have hlin : ∀ (T : Euclid n →L[ℝ] Euclid P) (S : Set (Euclid n)),
      μHE[n] (T '' S) = ENNReal.ofReal (T : Euclid n →ₗ[ℝ] Euclid P).normDet * volume S := by
    intro T S
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (T : Euclid n →ₗ[ℝ] Euclid P) S
    rw [hfin] at h
    simpa using h
  have hJlin : ∀ a (S : Set (Euclid n)),
      μHE[n] (fderiv ℝ F a '' S) = ENNReal.ofReal (J a) * volume S := by
    intro a S
    rw [hlin, hJ, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
  -- `J ≤ Lⁿ`: compare `Hⁿ(DF(a)(B̄₁(0)))` with the Lipschitz bound `‖DF(a)‖ ≤ L`
  have hJle : ∀ a, J a ≤ (L : ℝ) ^ n := by
    intro a
    have hTL : ‖fderiv ℝ F a‖₊ ≤ L := by
      have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := a) hF
      exact_mod_cast h
    have hpos : volume (closedBall (0 : Euclid n) 1) ≠ 0 :=
      (measure_closedBall_pos volume (0 : Euclid n) one_pos).ne'
    have hfin' : volume (closedBall (0 : Euclid n) 1) ≠ ∞ := measure_closedBall_lt_top.ne
    have hle : ENNReal.ofReal (J a) * volume (closedBall (0 : Euclid n) 1) ≤
        (L : ℝ≥0∞) ^ n * volume (closedBall (0 : Euclid n) 1) := by
      rw [← hJlin a, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
      calc μHE[n] (fderiv ℝ F a '' closedBall 0 1)
          ≤ (‖fderiv ℝ F a‖₊ : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (fderiv ℝ F a).lipschitzWith.lipschitzOnWith
        _ ≤ (L : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) := by gcongr
    have h2 : ENNReal.ofReal (J a) ≤ (L : ℝ≥0∞) ^ n :=
      (ENNReal.mul_le_mul_iff_left hpos hfin').1 hle
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_pow L.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    exact h2
  -- `F` is injective on `B`, so the area formula holds on `B` with weight `J`
  have hinjOn : InjOn F B := by
    intro a ha a' ha' hFa
    have h := hcolip a ha a' ha'
    rw [hFa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hm
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have harea : ∀ g : Euclid P → ℝ≥0∞,
      ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume := by
    intro g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hB hinjOn g
    rw [hfin] at h
    rw [h, hJ]
  -- `J` is bounded and Borel, hence locally integrable
  have hJloc : LocallyIntegrable J volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne hJmeas.aestronglyMeasurable
      (M := (L : ℝ) ^ n) (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hJnonneg a)]
    exact hJle a
  -- a.e. `b ∈ B` is a density point of `B` and a Lebesgue point of `J`
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Euclid n))
    hJloc 1
  filter_upwards [ae_restrict_mem hB, Besicovitch.ae_tendsto_measure_inter_div volume B,
    ae_restrict_of_ae hleb] with b hbB hα hβ
  have hβ' : Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) :=
    hβ (fun _ => b) id tendsto_id (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) =>
      mem_closedBall_self (by simpa using hρ.le))
  obtain ⟨hdb, hinj⟩ := hreg b hbB
  have hcolb : ∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖ := fun a ha => hcolip a ha b hbB
  have hγ : ∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ :=
    Submission.pit_fderiv_lower_bound_of_density P n F B m b hm hcolb hdb hα
  refine ⟨?_, fun f => ?_⟩
  · rw [LinearMap.finrank_range_of_inj (by simpa using hinj), hfin]
  · rw [Submission.pit_setIntegral_range_linear P n (fderiv ℝ F b) (J b) f (hJnonneg b)
      (hJlin b) f.continuous]
    refine (Submission.pit_rescaled_integral_tendsto P n F B J ((L : ℝ) ^ n) m b f hF.continuous
      hB hJmeas (fun a => ⟨hJnonneg a, hJle a⟩) hm hcolb hdb hγ hα hβ' f.continuous
      f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (Submission.pit_blowUp_image_setIntegral_eq_rescaled P n F B J b r f hF.continuous hB
      hJmeas hJnonneg harea hr f.continuous).symm

/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"**, for a bi-Lipschitz piece: let `U` be open,
`Y ⊆ U` Borel with `Hⁿ(Y ∩ C) < ∞` for compact `C ⊆ U`, `F` Lipschitz, `B` Borel with
`m|a − a'| ≤ |F(a) − F(a')|` on `B`, `DF(a)` injective for `a ∈ B`, and `F(B) ⊆ Y`.  Then for
a.e. `b ∈ B`, `Y` has approximate tangent space `range DF(b)` at `F(b)`.  The image `F(B)` itself
has this tangent space at `F(b)` for a.e. `b`; `Y` and its Borel subset `F(B)` have the same
approximate tangent spaces `Hⁿ`-a.e. on `F(B)`; and `Hⁿ⌞F(B)`-null sets pull back along `F` to
Lebesgue-null subsets of `B`. -/
theorem Submission.dpf_approxTangent_ae_bilipschitz_piece : ∀ (P n : ℕ) (U Y : Set (Euclid P)) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → MeasurableSet Y → Y ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (Y ∩ C) ≠ ∞) → LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → F '' B ⊆ Y → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n Y (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n U Y F B L m hU hY hYU hfin hF hB hm hbi hdiff hFBY
  -- Step 0(a)–(b): `F(B)` is Borel; `Hⁿ⌞F(B)`-a.e. properties hold at `F(b)` for a.e. `b ∈ B`
  obtain ⟨hA, hpull⟩ := Submission.ptd_piece_image_measurable_ae_pullback P n F B L m hF hB hm hbi
  -- Steps 1–3 and 6: `Hⁿ`-a.e. on `F(B)`, `Y` and `F(B)` have the same approximate tangent spaces
  have hloc := Submission.ptd_ae_approxTangent_iff_of_subset P n U (F '' B) Y hU hA hY hFBY hYU hfin
  -- Steps 4, 5 and 7: `F(B)` has approximate tangent space `range DF(b)` at `F(b)` for a.e. `b ∈ B`
  filter_upwards [hpull _ hloc,
    Submission.ptd_piece_image_approxTangent_ae P n F B L m hF hB hm hbi hdiff] with b hYA hA'
  exact (hYA _).2 hA'
/-- Orientation of a cylinder: let `e₀` be the first basis vector of `ℝᴺ⁺¹` and `J v = (0, v)`
for `v ∈ ℝᴺ`.  If `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` orients `Q ⊆ ℝᴺ` and the `(n+1)`-vector `ξ'` pairs with each
`α` as `ξ` pairs with `α(e₀, J ·)`, then `ξ' = ±e₀ ∧ Jτ₁ ∧ ⋯ ∧ Jτₙ` orients `ℝe₀ ⊕ J(Q)`
(Simon 6.1.1, 6.1.7).  The frame `(e₀, Jτ₁, …, Jτₙ)` is orthonormal because `J` is a linear
isometry onto `e₀^⊥`. -/
theorem Submission.dimred_mbl_dt_lp_imc_orientation : ∀ (N n : ℕ) (ξ : MultiVector N n) (ξ' : MultiVector (N + 1) (n + 1)) (Q : Submodule ℝ (Euclid N)), IsUnitOrientationOf ξ Q → (∀ (α : Covector (Euclid (N + 1)) (n + 1)) (β : Covector (Euclid N) n), (∀ v : Fin n → Euclid N, β v = α (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ξ' α = ξ β) → IsUnitOrientationOf ξ' (Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (Q : Set (Euclid N))))) := by
  intro N n ξ ξ' Q hξ hrel
  obtain ⟨τ, hτon, hτspan, hτsign⟩ := hξ
  set e₀ : Euclid (N + 1) := EuclideanSpace.single 0 1 with he₀
  -- Step 1: `J` is linear and isometric, `J(ℝᴺ) ⊥ e₀` and `‖e₀‖ = 1`
  let J : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := fun v w => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun c v => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  have hJ : (fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) =
      ⇑J := rfl
  have hJJ : ∀ v w, inner ℝ (J v) (J w) = inner ℝ v w := by
    intro v w
    simp [J, PiLp.inner_apply, Fin.sum_univ_succ]
  have he₀J : ∀ v, inner ℝ e₀ (J v) = 0 := by
    intro v
    simp [he₀, J, EuclideanSpace.inner_single_left]
  have he₀e₀ : inner ℝ e₀ e₀ = (1 : ℝ) := by
    simp [he₀]
  -- Step 2: the frame `τ' = (e₀, Jτ₁, …, Jτₙ)` is orthonormal
  set τ' : Fin (n + 1) → Euclid (N + 1) := Fin.cons e₀ (fun i => J (τ i)) with hτ'
  have hτ'on : Orthonormal ℝ τ' := by
    rw [orthonormal_iff_ite] at hτon ⊢
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rw [hτ', Fin.cons_zero, ite_eq_left rfl]
      exact he₀e₀
    · simp [hτ', he₀J, (Fin.succ_ne_zero j).symm]
    · simp [hτ', real_inner_comm, he₀J, Fin.succ_ne_zero i]
    · simp [hτ', hJJ, hτon]
  -- Step 3: `span τ' = ℝe₀ ⊔ J(span τ) = ℝe₀ ⊔ J(Q)`
  have hspan : Submodule.span ℝ (range τ') =
      Submodule.span ℝ (insert e₀ (J '' (Q : Set (Euclid N)))) := by
    rw [hτ', Fin.range_cons, Submodule.span_insert, Submodule.span_insert, range_comp',
      ← Submodule.map_span, hτspan, ← Submodule.map_span, Submodule.span_eq]
  -- Step 4: `ξ' α = ξ β` for `β = α(e₀, J ·)`, and `β(τ) = α(τ')`
  let Jc : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap J
  have hval : ∀ α : Covector (Euclid (N + 1)) (n + 1),
      ξ' α = ξ ((α.curryLeft e₀).compContinuousLinearMap Jc) :=
    fun α => hrel α _ fun v => rfl
  have hβτ : ∀ α : Covector (Euclid (N + 1)) (n + 1),
      (α.curryLeft e₀).compContinuousLinearMap Jc τ = α τ' := fun α => rfl
  rw [hJ]
  refine ⟨τ', hτ'on, hspan, ?_⟩
  rcases hτsign with h | h
  · exact Or.inl fun α => by rw [hval, h, hβτ]
  · exact Or.inr fun α => by rw [hval, h, hβτ]
/-- **The cylinder over one piece.**  Let `G : ℝⁿ → ℝᴺ` be Lipschitz, `A ⊆ ℝⁿ` Borel, `G`
injective on `A` and differentiable at every point of `A`, and `Hⁿ(G(A)) < ∞`.  Then
`Ψ(t, x) = (t, x)` carries `(L¹⌞(0, 1)) × (Hⁿ⌞G(A))` to `Hⁿ⁺¹⌞Ψ((0, 1) × G(A))`.  By
`Measure.prod_eq` it suffices that `Hⁿ⁺¹(Ψ(s × G(B))) = |s| Hⁿ(G(B))` for Borel `s ⊆ (0, 1)` and
`B ⊆ A`.  Where `DG` is injective, Mathlib's partition lemma cuts `B` into Borel pieces on which `G`
is `(1 + 2δ)`-bi-Lipschitz relative to a linear `S` with `|S h| = |DG(y) h|`; the Lipschitz image
bound compares `Hⁿ(G(P))` and `Hⁿ⁺¹(Ψ(s × G(P)))` with `Lⁿ(S(P))` and `|s| Lⁿ(S(P))`, and `δ → 0`.
Where `DG` is not injective, `G(B)` and the cylinder over it are null (Sard: on each piece `G` is
`(L + 1)`-Lipschitz relative to a linear `D` with `det D = ε`). -/
theorem Submission.dimred_mbl_dt_lp_imc_piece_measure : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (L : NNReal), LipschitzWith L G → MeasurableSet A → InjOn G A → (∀ a ∈ A, DifferentiableAt ℝ G a) → μHE[n] (G '' A) ≠ ∞ → Measure.map (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) (((volume : Measure ℝ).restrict (Ioo 0 1)).prod (μHE[n].restrict (G '' A))) = μHE[n + 1].restrict ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ (G '' A))) := by
  intro N n G A L hG hA hinj hdiff hfin
  -- Step 0.  `Φ_d(t, u) = (t, u₁, …, u_d)` is a continuous bijection `ℝ × ℝᵈ → ℝᵈ⁺¹` with
  -- `|Φ_d(t, u) − Φ_d(t', u')|² = (t − t')² + |u − u'|²`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (d : ℕ) → ℝ × Euclid d → Euclid (d + 1),
      ∀ d p, Φ d p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :=
    ⟨fun d p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)), fun _ _ => rfl⟩
  have hΦfun : ∀ d, (fun p : ℝ × Euclid d =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (d + 1))) = Φ d :=
    fun d => funext fun p => (hΦ d p).symm
  rw [hΦfun N]
  have hΦc : ∀ d, Continuous (Φ d) := fun d => by
    rw [← hΦfun d]
    fun_prop
  have hΦi : ∀ d, Injective (Φ d) := by
    rintro d ⟨t, u⟩ ⟨t', u'⟩ h
    rw [hΦ, hΦ] at h
    obtain ⟨h1, h2⟩ := Fin.cons_injective2 (WithLp.toLp_injective 2 h)
    exact Prod.ext h1 (WithLp.ofLp_injective 2 h2)
  have hΦs : ∀ d, Surjective (Φ d) := fun d z =>
    ⟨(WithLp.ofLp z 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))), by simp [hΦ, Fin.cons_self_tail]⟩
  have hΦe : ∀ d, MeasurableEmbedding (Φ d) := fun d => (hΦc d).measurableEmbedding (hΦi d)
  have hΦsub : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      Φ d (t, u) - Φ d (t', u') = Φ d (t - t', u - u') := by
    intro d t t' u u'
    simp only [hΦ]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hΦinner : ∀ (d : ℕ) (s s' : ℝ) (v v' : Euclid d),
      inner ℝ (Φ d (s, v)) (Φ d (s', v')) = s * s' + inner ℝ v v' := by
    intro d s s' v v'
    simp [hΦ, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
  have hΦnorm : ∀ (d : ℕ) (t : ℝ) (u : Euclid d), ‖Φ d (t, u)‖ ^ 2 = t ^ 2 + ‖u‖ ^ 2 := by
    intro d t u
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hΦinner, sq]
  -- a `K`-Lipschitz comparison `y ↔ x` (`K ≥ 1`) extends to the cylinders `Φ(t, y) ↔ Φ(t, x)`
  have hcyl : ∀ (d₁ d₂ : ℕ) (K t t' : ℝ) (x x' : Euclid d₁) (y y' : Euclid d₂), 1 ≤ K →
      ‖y - y'‖ ≤ K * ‖x - x'‖ → ‖Φ d₂ (t, y) - Φ d₂ (t', y')‖ ≤ K * ‖Φ d₁ (t, x) - Φ d₁ (t', x')‖ := by
    intro d₁ d₂ K t t' x x' y y' hK hyx
    rw [hΦsub, hΦsub]
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hΦnorm, hΦnorm]
    have h1 : ‖y - y'‖ ^ 2 ≤ K ^ 2 * ‖x - x'‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hyx 2
    have h2 : (t - t') ^ 2 ≤ K ^ 2 * (t - t') ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hK)
    linarith
  have himgprod : ∀ (d d' : ℕ) (f : Euclid d → Euclid d') (s : Set ℝ) (P : Set (Euclid d)),
      (fun p : ℝ × Euclid d => Φ d' (p.1, f p.2)) '' (s ×ˢ P) = Φ d' '' (s ×ˢ (f '' P)) := by
    intro d d' f s P
    ext z
    simp only [mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨t, a, ⟨ht, ha⟩, rfl⟩
      exact ⟨t, f a, ⟨ht, a, ha, rfl⟩, rfl⟩
    · rintro ⟨t, _, ⟨ht, a, ha, rfl⟩, rfl⟩
      exact ⟨t, a, ⟨ht, ha⟩, rfl⟩
  -- `Hᵈ` is Lebesgue measure on `ℝᵈ`, and `Φ_n` carries `L¹ × Lⁿ` to `Lⁿ⁺¹`
  have hvol : ∀ d : ℕ, (μHE[d] : Measure (Euclid d)) = volume := fun d =>
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume d
  have hΦmp : MeasurePreserving (Φ n) := by
    have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : Euclid n → (Fin n → ℝ)))
        ((volume : Measure ℝ).prod (volume : Measure (Euclid n)))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin n))
    have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        (volume : Measure (Fin (n + 1) → ℝ)) :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have h3 := (PiLp.volume_preserving_toLp (Fin (n + 1))).comp (h2.comp h1)
    rw [← hΦfun n]
    convert h3 using 1
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  have hvolΦ : ∀ (s : Set ℝ) (Q : Set (Euclid n)),
      μHE[n + 1] (Φ n '' (s ×ˢ Q)) = volume s * μHE[n] Q := by
    intro s Q
    rw [hvol (n + 1), hvol n, ← hΦmp.map_eq, (hΦe n).map_apply, preimage_image_eq _ (hΦi n),
      Measure.volume_eq_prod, Measure.prod_prod]
  -- Comparison of images: if `|v a − v a'| ≤ K|u a − u a'|` on `P`, then `Hᵈ(v(P)) ≤ Kᵈ Hᵈ(u(P))`
  have hcomp : ∀ (α : Type) (k₁ k₂ d : ℕ) (u : α → Euclid k₁) (v : α → Euclid k₂) (P : Set α)
      (K : NNReal), (∀ a ∈ P, ∀ a' ∈ P, ‖v a - v a'‖ ≤ K * ‖u a - u a'‖) →
      μHE[d] (v '' P) ≤ (K : ℝ≥0∞) ^ d * μHE[d] (u '' P) := by
    intro α k₁ k₂ d u v P K h
    rcases P.eq_empty_or_nonempty with hP | ⟨a₀, -⟩
    · simp [hP]
    have : Nonempty α := ⟨a₀⟩
    set g := Function.invFunOn u P
    have hg : ∀ y ∈ u '' P, g y ∈ P ∧ u (g y) = y :=
      fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
    have hLip : LipschitzOnWith K (v ∘ g) (u '' P) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      obtain ⟨hgy, huy⟩ := hg y hy
      obtain ⟨hgy', huy'⟩ := hg y' hy'
      simp only [comp_apply, dist_eq_norm]
      calc ‖v (g y) - v (g y')‖ ≤ K * ‖u (g y) - u (g y')‖ := h _ hgy _ hgy'
        _ = K * ‖y - y'‖ := by rw [huy, huy']
    have hsub : v '' P ⊆ (v ∘ g) '' (u '' P) := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨u a, mem_image_of_mem u ha, ?_⟩
      obtain ⟨hga, hua⟩ := hg (u a) (mem_image_of_mem u ha)
      have := h _ hga _ ha
      rw [hua, sub_self, norm_zero, mul_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    exact (measure_mono hsub).trans
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d hLip)
  -- Limits `ε → 0` and `δ → 0`
  have hlim0 : ∀ x C : ℝ≥0∞, C ≠ ∞ → (∀ ε : NNReal, 0 < ε → ε ≤ 1 → x ≤ C * ε) → x = 0 := by
    intro x C hC h
    have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
      rw [← ENNReal.coe_zero]
      exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
    have htend : Tendsto (fun ε : NNReal => C * (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hC)
    refine le_antisymm (ge_of_tendsto htend ?_) bot_le
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
    exact h ε hε.1 hε.2
  have hlim1 : ∀ (x y : ℝ≥0∞) (m : ℕ),
      (∀ δ : NNReal, 0 < δ → δ ≤ 1 / 2 → x ≤ ((1 + 2 * δ : NNReal) : ℝ≥0∞) ^ m * y) → x ≤ y := by
    intro x y m h
    have h1 : Tendsto (fun δ : NNReal => (((1 + 2 * δ) ^ m : NNReal) : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous fun δ : NNReal => (1 + 2 * δ) ^ m := by fun_prop
      rw [← ENNReal.coe_one]
      exact ENNReal.tendsto_coe.mpr ((hc.tendsto' 0 1 (by simp)).mono_left nhdsWithin_le_nhds)
    have htend : Tendsto (fun δ : NNReal => (((1 + 2 * δ) ^ m : NNReal) : ℝ≥0∞) * y) (𝓝[>] 0)
        (𝓝 y) := by
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num)] with δ hδ
    rw [ENNReal.coe_pow]
    exact h δ hδ.1 hδ.2
  -- Step 1.  Linear algebra: coercivity `c(T)|h| ≤ |T h|` and an `S` with `|S h| = |T h|` for
  -- injective `T`
  have hcoer : ∀ T : Euclid n →L[ℝ] Euclid N, ∃ c : NNReal, 0 < c ∧
      (Injective T → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖T h‖) := by
    intro T
    by_cases hT : Injective T
    · obtain ⟨C, Cpos, hC⟩ := T.injective_iff_antilipschitz.mp hT
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := T.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖T h‖) := by gcongr
        _ = ‖T h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hT⟩
  choose c hcpos hc using hcoer
  have hiso : ∀ T : Euclid n →L[ℝ] Euclid N, ∃ S : Euclid n →ₗ[ℝ] Euclid n,
      Injective T → ∀ h, ‖S h‖ = ‖T h‖ := by
    intro T
    by_cases hT : Injective T
    · have hr : Module.finrank ℝ (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid N)) = n := by
        rw [LinearMap.finrank_range_of_inj hT, finrank_euclideanSpace_fin]
      let e := (stdOrthonormalBasis ℝ (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid N))).repr.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hr))
      refine ⟨e.toLinearEquiv.toLinearMap ∘ₗ (T : Euclid n →ₗ[ℝ] Euclid N).rangeRestrict,
        fun _ h => ?_⟩
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        LinearIsometryEquiv.norm_map]
      rfl
    · exact ⟨0, fun h => absurd h hT⟩
  choose S hS using hiso
  -- Step 2.  Regular part: for Borel `X ⊆ A` on which `DG` is injective,
  -- `Hⁿ⁺¹(Φ_N(s × G(X))) = |s| Hⁿ(G(X))`
  have hreg : ∀ (X : Set (Euclid n)) (s : Set ℝ), MeasurableSet X → MeasurableSet s → X ⊆ A →
      (∀ a ∈ X, Injective (fderiv ℝ G a)) →
      μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) = volume s * μHE[n] (G '' X) := by
    intro X s hX hs hXA hXi
    rcases X.eq_empty_or_nonempty with hXe | hXne
    · simp [hXe]
    have hbound : ∀ δ : NNReal, 0 < δ → δ ≤ 1 / 2 →
        μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) ≤
            ((1 + 2 * δ : NNReal) : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' X)) ∧
          volume s * μHE[n] (G '' X) ≤
            ((1 + 2 * δ : NNReal) : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) := by
      intro δ hδ hδ2
      set K : NNReal := 1 + 2 * δ with hKdef
      have hδ0 : (0 : ℝ) ≤ δ := NNReal.coe_nonneg δ
      have hδ' : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ2
      have hK1 : (1 : ℝ) ≤ K := by
        rw [hKdef]
        push_cast
        linarith
      -- Mathlib's partition of `X` into Borel pieces on which `G` is `δ c(T)`-close to `T = DG(y)`
      obtain ⟨t, T, htdisj, htmeas, hXt, hT, hTy⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G X (fderiv ℝ G)
          (fun x hx => (hdiff x (hXA hx)).hasFDerivAt.hasFDerivWithinAt) (fun T => δ * c T)
          (fun T => (mul_pos hδ (hcpos T)).ne')
      -- on each piece `G` is `K`-bi-Lipschitz relative to `S(T)`, so both `Hⁿ(G(P))` and
      -- `Hⁿ⁺¹(Φ_N(s × G(P)))` are within `K^{2n+1}` of `Lⁿ(S P)` resp. `|s| Lⁿ(S P)`
      have hpiece : ∀ k, μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) ≤
            (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' (X ∩ t k))) ∧
          volume s * μHE[n] (G '' (X ∩ t k)) ≤
            (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by
        intro k
        obtain ⟨y, hy, hTk⟩ := hTy hXne k
        have hTinj : Injective (T k) := hTk ▸ hXi y hy
        have hST : ∀ a a', ‖S (T k) a - S (T k) a'‖ = ‖T k (a - a')‖ := fun a a' => by
          rw [← map_sub, hS (T k) hTinj]
        have happ : ∀ a ∈ X ∩ t k, ∀ a' ∈ X ∩ t k,
            ‖G a - G a' - T k (a - a')‖ ≤ δ * ‖T k (a - a')‖ := by
          intro a ha a' ha'
          have h1 := hT k a ha a' ha'
          have h2 := hc (T k) hTinj (a - a')
          simp only [NNReal.coe_mul] at h1
          calc ‖G a - G a' - T k (a - a')‖ ≤ δ * c (T k) * ‖a - a'‖ := h1
            _ = δ * (c (T k) * ‖a - a'‖) := by ring
            _ ≤ δ * ‖T k (a - a')‖ := by gcongr
        have hGS : ∀ a ∈ X ∩ t k, ∀ a' ∈ X ∩ t k,
            ‖G a - G a'‖ ≤ K * ‖S (T k) a - S (T k) a'‖ := by
          intro a ha a' ha'
          have h1 := happ a ha a' ha'
          have h2 := norm_sub_norm_le (G a - G a') (T k (a - a'))
          rw [hST, hKdef]
          push_cast
          linarith [mul_nonneg hδ0 (norm_nonneg (T k (a - a')))]
        have hSG : ∀ a ∈ X ∩ t k, ∀ a' ∈ X ∩ t k,
            ‖S (T k) a - S (T k) a'‖ ≤ K * ‖G a - G a'‖ := by
          intro a ha a' ha'
          have h1 := happ a ha a' ha'
          have h2 := norm_sub_norm_le (T k (a - a')) (G a - G a')
          rw [norm_sub_rev (T k (a - a'))] at h2
          rw [hST, hKdef]
          push_cast
          have h3 : (1 - (δ : ℝ)) * ‖T k (a - a')‖ ≤ ‖G a - G a'‖ := by linarith
          have h4 : (1 + 2 * (δ : ℝ)) * ((1 - δ) * ‖T k (a - a')‖) ≤
              (1 + 2 * (δ : ℝ)) * ‖G a - G a'‖ :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
          have h5 : 0 ≤ (δ : ℝ) * (1 - 2 * δ) * ‖T k (a - a')‖ :=
            mul_nonneg (mul_nonneg hδ0 (by linarith)) (norm_nonneg _)
          linarith
        have ha := hcomp (Euclid n) n N n (S (T k)) G (X ∩ t k) K hGS
        have hb := hcomp (Euclid n) N n n G (S (T k)) (X ∩ t k) K hSG
        have hc1 := hcomp (ℝ × Euclid n) (n + 1) (N + 1) (n + 1)
          (fun p => Φ n (p.1, S (T k) p.2)) (fun p => Φ N (p.1, G p.2)) (s ×ˢ (X ∩ t k)) K
          (fun p hp p' hp' => hcyl n N K p.1 p'.1 _ _ _ _ hK1 (hGS _ hp.2 _ hp'.2))
        have hd1 := hcomp (ℝ × Euclid n) (N + 1) (n + 1) (n + 1)
          (fun p => Φ N (p.1, G p.2)) (fun p => Φ n (p.1, S (T k) p.2)) (s ×ˢ (X ∩ t k)) K
          (fun p hp p' hp' => hcyl N n K p.1 p'.1 _ _ _ _ hK1 (hSG _ hp.2 _ hp'.2))
        rw [himgprod n N G, himgprod n n (S (T k)), hvolΦ] at hc1
        rw [himgprod n N G, himgprod n n (S (T k)), hvolΦ] at hd1
        constructor
        · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k))))
              ≤ (K : ℝ≥0∞) ^ (n + 1) * (volume s * μHE[n] (S (T k) '' (X ∩ t k))) := hc1
            _ ≤ (K : ℝ≥0∞) ^ (n + 1) * (volume s * ((K : ℝ≥0∞) ^ n * μHE[n] (G '' (X ∩ t k)))) := by
              gcongr
            _ = (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' (X ∩ t k))) := by ring
        · calc volume s * μHE[n] (G '' (X ∩ t k))
              ≤ volume s * ((K : ℝ≥0∞) ^ n * μHE[n] (S (T k) '' (X ∩ t k))) := by gcongr
            _ = (K : ℝ≥0∞) ^ n * (volume s * μHE[n] (S (T k) '' (X ∩ t k))) := by ring
            _ ≤ (K : ℝ≥0∞) ^ n * ((K : ℝ≥0∞) ^ (n + 1) *
                μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k))))) := by gcongr
            _ = (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by ring
      -- sum over the pieces: the images are Borel (Lusin–Souslin) and disjoint (`G` is injective)
      have hGPmeas : ∀ k, MeasurableSet (G '' (X ∩ t k)) := fun k =>
        (hX.inter (htmeas k)).image_of_continuousOn_injOn hG.continuous.continuousOn
          (hinj.mono (inter_subset_left.trans hXA))
      have hCPmeas : ∀ k, MeasurableSet (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := fun k =>
        (hΦe N).measurableSet_image.2 (hs.prod (hGPmeas k))
      have hGPdisj : Pairwise (Disjoint on fun k => G '' (X ∩ t k)) := by
        intro i j hij
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        have hba : b = a := hinj (hXA hb.1) (hXA ha.1) hab
        exact Set.disjoint_left.mp (htdisj hij) ha.2 (hba ▸ hb.2)
      have hCPdisj : Pairwise (Disjoint on fun k => Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by
        intro i j hij
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
        have hqp' : q = p := hΦi N hqp
        subst hqp'
        exact Set.disjoint_left.mp (hGPdisj hij) hp.2 hq.2
      have hGU : G '' X = ⋃ k, G '' (X ∩ t k) := by
        rw [← image_iUnion, ← inter_iUnion, inter_eq_left.mpr hXt]
      have hCU : Φ N '' (s ×ˢ (G '' X)) = ⋃ k, Φ N '' (s ×ˢ (G '' (X ∩ t k))) := by
        rw [hGU, prod_iUnion, image_iUnion]
      constructor
      · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' X)))
            = ∑' k, μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by
              rw [hCU, measure_iUnion hCPdisj hCPmeas]
          _ ≤ ∑' k, (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' (X ∩ t k))) :=
              ENNReal.tsum_le_tsum fun k => (hpiece k).1
          _ = (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' X)) := by
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hGU,
                measure_iUnion hGPdisj hGPmeas]
      · calc volume s * μHE[n] (G '' X) = ∑' k, volume s * μHE[n] (G '' (X ∩ t k)) := by
              rw [ENNReal.tsum_mul_left, hGU, measure_iUnion hGPdisj hGPmeas]
          _ ≤ ∑' k, (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) :=
              ENNReal.tsum_le_tsum fun k => (hpiece k).2
          _ = (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) := by
              rw [ENNReal.tsum_mul_left, hCU, measure_iUnion hCPdisj hCPmeas]
    exact le_antisymm (hlim1 _ _ _ fun δ hδ hδ2 => (hbound δ hδ hδ2).1)
      (hlim1 _ _ _ fun δ hδ hδ2 => (hbound δ hδ hδ2).2)
  -- Step 3.  Critical part (Sard): for Borel `X ⊆ A` on which `DG` is not injective, `G(X)` and
  -- the cylinder over it are null.  On a piece where `G` is `ε`-close to a rank-deficient `T`
  -- (`Tv = 0`, `|v| = 1`), `|G a − G a'| ≤ (L + 1)|D a − D a'|` for `D = id − (1 − ε) v ⊗ v`,
  -- and `det D = ε`.
  have hcrit : ∀ (X : Set (Euclid n)) (s : Set ℝ), MeasurableSet X → X ⊆ A →
      (∀ a ∈ X, ¬ Injective (fderiv ℝ G a)) → volume s ≠ ∞ →
      μHE[n] (G '' X) = 0 ∧ μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) = 0 := by
    intro X s hX hXA hXi hs
    have hR : ∀ R : ℕ, μHE[n] (G '' (X ∩ ball 0 R)) = 0 ∧
        μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ ball 0 R)))) = 0 := by
      intro R
      set Y := X ∩ ball (0 : Euclid n) R with hYdef
      have hYmeas : MeasurableSet Y := hX.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (G '' Y) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε ∧
          μHE[n + 1] (Φ N '' (s ×ˢ (G '' Y))) ≤
            ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (ball (0 : Euclid n) R)) * ε := by
        intro ε hε hε1
        rcases Y.eq_empty_or_nonempty with hYe | hYne
        · simp [hYe]
        obtain ⟨t, T, htdisj, htmeas, hYt, hT, hTy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G Y (fderiv ℝ G)
            (fun x hx => (hdiff x (hXA hx.1)).hasFDerivAt.hasFDerivWithinAt) (fun _ => ε)
            (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (G '' (Y ∩ t k)) ≤
              ((L : ℝ≥0∞) + 1) ^ n * volume (Y ∩ t k) * ε ∧
            μHE[n + 1] (Φ N '' (s ×ˢ (G '' (Y ∩ t k)))) ≤
              ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (Y ∩ t k)) * ε := by
          intro k
          obtain ⟨y, hy, hTk⟩ := hTy hYne k
          have hTnorm : ‖T k‖ ≤ L := hTk ▸ norm_fderiv_le_of_lipschitz ℝ hG
          have hTni : ¬ Injective (T k) := hTk ▸ hXi y hy.1
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ T k v = 0 := by
            simp only [Injective, not_forall] at hTni
            obtain ⟨a, b, hab, hne⟩ := hTni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c₀ : ℝ := 1 - (ε : ℝ) with hc₀
          have hc₀0 : 0 ≤ c₀ := by
            rw [hc₀]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c₀ • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c₀ * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hTD : ∀ h, T k (D h) = T k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc₀]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c₀ * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc₀]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c₀ * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c₀ * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc₀0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc₀]; ring
          have hGD : ∀ a ∈ Y ∩ t k, ∀ a' ∈ Y ∩ t k,
              ‖G a - G a'‖ ≤ ((L + 1 : NNReal) : ℝ) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hT k a ha a' ha'
            have h2 : ‖T k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hTD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (G a - G a') (T k (a - a'))
            push_cast
            linarith
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c₀ * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c₀ * v i) = 1 - c₀ * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc₀]; ring
          have hDvol : ∀ Q : Set (Euclid n), μHE[n] (D '' Q) = volume Q * ε := by
            intro Q
            rw [hvol n, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
              NNReal.abs_eq, ENNReal.ofReal_coe_nnreal, mul_comm]
          have h1 := hcomp (Euclid n) n N n D G (Y ∩ t k) (L + 1) hGD
          have h2 := hcomp (ℝ × Euclid n) (n + 1) (N + 1) (n + 1)
            (fun p => Φ n (p.1, D p.2)) (fun p => Φ N (p.1, G p.2)) (s ×ˢ (Y ∩ t k)) (L + 1)
            (fun p hp p' hp' => hcyl n N _ p.1 p'.1 _ _ _ _
              (by have := NNReal.coe_nonneg L; push_cast; linarith) (hGD _ hp.2 _ hp'.2))
          rw [hDvol] at h1
          rw [himgprod n N G, himgprod n n D, hvolΦ, hDvol] at h2
          constructor
          · calc μHE[n] (G '' (Y ∩ t k))
                ≤ ((L + 1 : NNReal) : ℝ≥0∞) ^ n * (volume (Y ∩ t k) * ε) := h1
              _ = ((L : ℝ≥0∞) + 1) ^ n * volume (Y ∩ t k) * ε := by push_cast; ring
          · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' (Y ∩ t k))))
                ≤ ((L + 1 : NNReal) : ℝ≥0∞) ^ (n + 1) * (volume s * (volume (Y ∩ t k) * ε)) := h2
              _ = ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (Y ∩ t k)) * ε := by
                push_cast; ring
        have hvolU : ∑' k, volume (Y ∩ t k) ≤ volume (ball (0 : Euclid n) R) := by
          rw [← measure_iUnion (fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right)
            (fun k => hYmeas.inter (htmeas k))]
          exact measure_mono (iUnion_subset fun k => inter_subset_left.trans inter_subset_right)
        constructor
        · calc μHE[n] (G '' Y) ≤ ∑' k, μHE[n] (G '' (Y ∩ t k)) := by
                refine (measure_mono ?_).trans (measure_iUnion_le _)
                rintro _ ⟨a, ha, rfl⟩
                obtain ⟨k, hk⟩ := mem_iUnion.mp (hYt ha)
                exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
            _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (Y ∩ t k) * ε :=
                ENNReal.tsum_le_tsum fun k => (hpiece k).1
            _ = ((L : ℝ≥0∞) + 1) ^ n * (∑' k, volume (Y ∩ t k)) * ε := by
                rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
            _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by gcongr
        · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' Y)))
              ≤ ∑' k, μHE[n + 1] (Φ N '' (s ×ˢ (G '' (Y ∩ t k)))) := by
                refine (measure_mono ?_).trans (measure_iUnion_le _)
                rintro _ ⟨⟨τ, x⟩, ⟨hτ, a, ha, rfl⟩, rfl⟩
                obtain ⟨k, hk⟩ := mem_iUnion.mp (hYt ha)
                exact mem_iUnion.mpr ⟨k, ⟨τ, G a⟩, ⟨hτ, a, ⟨ha, hk⟩, rfl⟩, rfl⟩
            _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (Y ∩ t k)) * ε :=
                ENNReal.tsum_le_tsum fun k => (hpiece k).2
            _ = ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * ∑' k, volume (Y ∩ t k)) * ε := by
                rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
            _ ≤ ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (ball (0 : Euclid n) R)) * ε := by
                gcongr
      have hfin1 : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have hfin2 : ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (ball (0 : Euclid n) R)) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
          (ENNReal.mul_ne_top hs measure_ball_lt_top.ne)
      exact ⟨hlim0 _ _ hfin1 fun ε hε hε1 => (hbound ε hε hε1).1,
        hlim0 _ _ hfin2 fun ε hε hε1 => (hbound ε hε hε1).2⟩
    constructor
    · refine measure_mono_null ?_ (measure_iUnion_null fun R => (hR R).1)
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
      exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
    · refine measure_mono_null ?_ (measure_iUnion_null fun R => (hR R).2)
      rintro _ ⟨⟨τ, x⟩, ⟨hτ, a, ha, rfl⟩, rfl⟩
      obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
      exact mem_iUnion.mpr ⟨R, ⟨τ, G a⟩, ⟨hτ, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩, rfl⟩
  -- Step 4.  Both parts: `Hⁿ⁺¹(Φ_N(s × G(B))) = |s| Hⁿ(G(B))` for Borel `B ⊆ A`, `|s| < ∞`
  have hmeasI : MeasurableSet {a : Euclid n | Injective (fderiv ℝ G a)} :=
    measurable_fderiv ℝ G ContinuousLinearMap.isOpen_injective.measurableSet
  have hcore : ∀ (s : Set ℝ) (B : Set (Euclid n)), MeasurableSet s → volume s ≠ ∞ →
      MeasurableSet B → B ⊆ A →
      μHE[n + 1] (Φ N '' (s ×ˢ (G '' B))) = volume s * μHE[n] (G '' B) := by
    intro s B hs hsfin hB hBA
    obtain ⟨hc1, hc2⟩ := hcrit (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ) s (hB.inter hmeasI.compl)
      (inter_subset_left.trans hBA) (fun a ha => ha.2) hsfin
    have hr := hreg (B ∩ {a | Injective (fderiv ℝ G a)}) s (hB.inter hmeasI) hs
      (inter_subset_left.trans hBA) (fun a ha => ha.2)
    have hGB : G '' B = G '' (B ∩ {a | Injective (fderiv ℝ G a)}) ∪
        G '' (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ) := by
      rw [← image_union, inter_union_compl]
    apply le_antisymm
    · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' B)))
          ≤ μHE[n + 1] (Φ N '' (s ×ˢ (G '' (B ∩ {a | Injective (fderiv ℝ G a)})))) +
            μHE[n + 1] (Φ N '' (s ×ˢ (G '' (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ)))) := by
            rw [hGB, prod_union, image_union]
            exact measure_union_le _ _
        _ = volume s * μHE[n] (G '' (B ∩ {a | Injective (fderiv ℝ G a)})) := by
            rw [hc2, add_zero, hr]
        _ ≤ volume s * μHE[n] (G '' B) :=
            mul_le_mul' le_rfl (measure_mono (image_mono inter_subset_left))
    · calc volume s * μHE[n] (G '' B)
          ≤ volume s * (μHE[n] (G '' (B ∩ {a | Injective (fderiv ℝ G a)})) +
            μHE[n] (G '' (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ))) := by
            rw [hGB]
            exact mul_le_mul' le_rfl (measure_union_le _ _)
        _ = μHE[n + 1] (Φ N '' (s ×ˢ (G '' (B ∩ {a | Injective (fderiv ℝ G a)})))) := by
            rw [hc1, add_zero, hr]
        _ ≤ μHE[n + 1] (Φ N '' (s ×ˢ (G '' B))) :=
            measure_mono (image_mono (prod_mono subset_rfl (image_mono inter_subset_left)))
  -- Step 5.  Both measures agree on rectangles (`Measure.prod_eq`); push forward by `Φ_N`
  have hEmeas : MeasurableSet (G '' A) :=
    hA.image_of_continuousOn_injOn hG.continuous.continuousOn hinj
  have : IsFiniteMeasure (μHE[n].restrict (G '' A)) := isFiniteMeasure_restrict.mpr hfin
  have hprod : ((volume : Measure ℝ).restrict (Ioo 0 1)).prod (μHE[n].restrict (G '' A)) =
      Measure.comap (Φ N) (μHE[n + 1].restrict (Φ N '' (Ioo 0 1 ×ˢ (G '' A)))) := by
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [(hΦe N).comap_apply, Measure.restrict_apply ((hΦe N).measurableSet_image.2 (hs.prod ht)),
      ← image_inter (hΦi N), prod_inter_prod, Measure.restrict_apply hs, Measure.restrict_apply ht,
      inter_comm t (G '' A), ← image_inter_preimage]
    exact hcore _ _ (hs.inter measurableSet_Ioo)
      ((measure_mono inter_subset_right).trans_lt measure_Ioo_lt_top).ne
      (hA.inter (hG.continuous.measurable ht)) inter_subset_left
  rw [hprod, (hΦe N).map_comap, (hΦs N).range_eq, Measure.restrict_univ]

/-- **Cylinder measure.**  For a Borel countably `n`-rectifiable `M ⊆ ℝᴺ` with `Hⁿ(M) < ∞` and
`Ψ(t, x) = (t, x₁, …, x_N)`, `Ψ_*(L¹⌞(0, 1) ⊗ Hⁿ⌞M) = Hⁿ⁺¹⌞Ψ((0, 1) × M)`.  Up to an `Hⁿ`-null
set `Z`, `M` is the disjoint union of the bi-Lipschitz pieces `Sᵢ = Fᵢ(Bᵢ)`
(`dpf_rectifiable_bilipschitz_pieces`), for which the identity is
`dimred_mbl_dt_lp_imc_piece_measure`.  Both sides are countably additive in the piece, and the
cylinders `Ψ((0, 1) × Sᵢ)` cover `Ψ((0, 1) × M)` up to `Ψ(ℝ × Z)`, which is `Hⁿ⁺¹`-null by
`dimred_mbl_dt_lp_imc_product_null`. -/
theorem Submission.dimred_mbl_dt_lp_imc_cylinder_measure : ∀ (N n : ℕ) (M : Set (Euclid N)), MeasurableSet M → CountablyRectifiable n M → μHE[n] M ≠ ∞ → Measure.map (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) (((volume : Measure ℝ).restrict (Ioo 0 1)).prod (μHE[n].restrict M)) = μHE[n + 1].restrict ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M)) := by
  intro N n M hM hrect hfin
  set Ψ : ℝ × Euclid N → Euclid (N + 1) := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
  -- `Ψ` is a continuous injection, hence a measurable embedding
  have hΨemb : MeasurableEmbedding Ψ := by
    refine Continuous.measurableEmbedding (by fun_prop) ?_
    rintro ⟨t, x⟩ ⟨s, y⟩ h
    obtain ⟨hts, hxy⟩ := Fin.cons_injective2 (WithLp.toLp_injective 2 h)
    exact Prod.ext hts (WithLp.ofLp_injective 2 hxy)
  -- the bi-Lipschitz pieces `Sᵢ = Fᵢ(Bᵢ)` of `M`
  obtain ⟨F, B, m, hLip, hBm, hm, hbil, hdiff, hSm, hSM, hdisj, hZ⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces N n M hM hrect
  have hinj : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have h' := hbil i a ha a' ha'
    rw [h, sub_self, norm_zero] at h'
    have h0 : ‖a - a'‖ ≤ 0 := by nlinarith [hm i, norm_nonneg (a - a')]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  have hSfin : ∀ i, μHE[n] (F i '' B i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hfin (measure_mono (hSM i))
  have : ∀ i, SFinite (μHE[n].restrict (F i '' B i)) := fun i =>
    haveI := isFiniteMeasure_restrict.mpr (hSfin i)
    inferInstance
  -- the identity on each piece
  have hpiece : ∀ i, Measure.map Ψ (((volume : Measure ℝ).restrict (Ioo 0 1)).prod
      (μHE[n].restrict (F i '' B i))) =
      μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ (F i '' B i))) := by
    intro i
    obtain ⟨L, hL⟩ := hLip i
    exact Submission.dimred_mbl_dt_lp_imc_piece_measure N n (F i) (B i) L hL (hBm i) (hinj i)
      (fun a ha => (hdiff i a ha).1) (hSfin i)
  -- source side: `Hⁿ⌞M = ∑ᵢ Hⁿ⌞Sᵢ`
  have hsrc : μHE[n].restrict M = Measure.sum fun i => μHE[n].restrict (F i '' B i) := by
    refine (Measure.restrict_congr_set (ae_eq_set.mpr ⟨hZ, ?_⟩)).trans
      (Measure.restrict_iUnion (s := fun i => F i '' B i) hdisj hSm)
    rw [Set.sdiff_eq_empty.mpr (iUnion_subset hSM), measure_empty]
  -- target side: `Hⁿ⁺¹⌞Ψ((0, 1) × M) = ∑ᵢ Hⁿ⁺¹⌞Ψ((0, 1) × Sᵢ)`
  have htgt : μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ M)) =
      Measure.sum fun i => μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ (F i '' B i))) := by
    refine (Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)).trans
      (Measure.restrict_iUnion (s := fun i => Ψ '' (Ioo (0 : ℝ) 1 ×ˢ (F i '' B i))) ?_ ?_)
    · refine measure_mono_null (t := Ψ '' (univ ×ˢ (M \ ⋃ i, F i '' B i))) ?_
        (Submission.dimred_mbl_dt_lp_imc_product_null N n _ hZ)
      rintro _ ⟨⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩, hnot⟩
      refine ⟨(t, x), ⟨mem_univ t, hx, fun hxU => hnot ?_⟩, rfl⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
      exact mem_iUnion.mpr ⟨i, (t, x), ⟨ht, hi⟩, rfl⟩
    · rw [Set.sdiff_eq_empty.mpr
        (iUnion_subset fun i => image_mono (prod_mono subset_rfl (hSM i))), measure_empty]
    · intro i j hij
      exact (disjoint_image_iff hΨemb.injective).mpr (disjoint_prod.mpr (Or.inr (hdisj hij)))
    · exact fun i => hΨemb.measurableSet_image.mpr (measurableSet_Ioo.prod (hSm i))
  rw [hsrc, Measure.prod_sum_right, Measure.map_sum hΨemb.measurable.aemeasurable, htgt]
  exact congrArg Measure.sum (funext hpiece)
/-- **Simon Ch. 6, 2.21 and 2.27** (the cylinder `[[(0, 1)]] × T`), with **Ch. 3, 1.4**:
approximate tangent spaces of the cylinder `(0, 1) × M`.  Let `M ⊆ ℝᴺ` be Borel and countably
`n`-rectifiable with `Hⁿ(M) < ∞`, and `M̃ := Ψ((0, 1) × M)`, `Ψ(t, x) = (t, x) ∈ ℝ^{N+1}`.  For
`H^{n+1}`-a.e. `y = Ψ(t, x) ∈ M̃`, if `M` has approximate tangent space `Q` at `x`, then `M̃` has
approximate tangent space `Q̃ = span(e₀, J(Q))` at `y`.  `M` is covered up to an `Hⁿ`-null set
`Z₀` by bi-Lipschitz pieces `Fᵢ(Bᵢ)`, and `M̃` by the product pieces `Ĝᵢ(Φₙ((0, 1) × Bᵢ))`,
`Ĝᵢ(t, u) = (t, Fᵢ u)`.  For a.e. `u ∈ Bᵢ`, `M` has approximate tangent space `range DFᵢ(u)` at
`Fᵢ u`; for a.e. `z`, `M̃` has approximate tangent space `range DĜᵢ(z) = Q̃(range DFᵢ(u))` at
`Ĝᵢ z`.  The exceptional points lie in Lipschitz images of null sets and in `Ψ(ℝ × Z₀)`, an
`H^{n+1}`-null set; elsewhere uniqueness of approximate tangent spaces gives `Q = range DFᵢ(u)`. -/
theorem Submission.dimred_mbl_dt_lp_imc_cylinder_tangent : ∀ (N n : ℕ) (M : Set (Euclid N)), MeasurableSet M → CountablyRectifiable n M → μHE[n] M ≠ ∞ → ∀ᵐ y ∂(μHE[n + 1].restrict ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M))), ∀ (t : ℝ) (x : Euclid N), y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) → ∀ Q : Submodule ℝ (Euclid N), HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt (n + 1) ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M)) y (Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (Q : Set (Euclid N))))) := by
  intro N n M hM hrect hfinM
  -- `Φ_d(t, u) = (t, u)` is a continuous injection `ℝ × ℝᵈ → ℝ^{d+1}`, so a measurable embedding
  have hinj : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1)) =
        WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')) → t = t' ∧ u = u' := by
    intro d t t' u u' h
    obtain ⟨h1, h2⟩ := Fin.cons_injective2 (WithLp.toLp_injective 2 h)
    exact ⟨h1, WithLp.ofLp_injective 2 h2⟩
  have hemb : ∀ d : ℕ, MeasurableEmbedding (fun p : ℝ × Euclid d =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (d + 1))) := by
    intro d
    refine Continuous.measurableEmbedding (by fun_prop) ?_
    rintro ⟨t, u⟩ ⟨t', u'⟩ h
    obtain ⟨rfl, rfl⟩ := hinj d t t' u u' h
    rfl
  -- Step 1: `M̃` is Borel and `H^{n+1}(M̃) = Hⁿ(M) < ∞`
  have hCM := Submission.dimred_mbl_dt_lp_imc_cylinder_measure N n M hM hrect hfinM
  set Mt := (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
    Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M)
  have hMt : MeasurableSet Mt := (hemb N).measurableSet_image.2 (measurableSet_Ioo.prod hM)
  have hfinMt : μHE[n + 1] Mt ≠ ∞ := by
    have : IsFiniteMeasure (μHE[n].restrict M) := isFiniteMeasure_restrict.2 hfinM
    have h := congrArg (fun μ : Measure (Euclid (N + 1)) => μ univ) hCM
    simp only [Measure.restrict_apply_univ] at h
    rw [← h, Measure.map_apply (hemb N).measurable MeasurableSet.univ, preimage_univ,
      ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinM
  -- Step 2: bi-Lipschitz pieces `Fᵢ(Bᵢ) ⊆ M` covering `M` up to the `Hⁿ`-null set `Z₀`
  obtain ⟨F, B, m, hFlip, hBmeas, hmpos, hbi, hdiff, -, hFBsub, -, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces N n M hM hrect
  choose L hL using hFlip
  -- Step 3: for `u ∈ Bᵢ` off a null set `Zᵢ`, `M` has approximate tangent space `range DFᵢ(u)`
  -- at `Fᵢ u`
  have hZ : ∀ i, ∃ Z : Set (Euclid n), volume Z = 0 ∧ ∀ u ∈ B i, u ∉ Z →
      HasApproximateTangentSpaceAt n M (F i u)
        (LinearMap.range (fderiv ℝ (F i) u : Euclid n →ₗ[ℝ] Euclid N)) := by
    intro i
    have h := Submission.dpf_approxTangent_ae_bilipschitz_piece N n univ M (F i) (B i) (L i) (m i)
      isOpen_univ hM (subset_univ M)
      (fun C _ _ => ne_top_of_le_ne_top hfinM (measure_mono inter_subset_left)) (hL i) (hBmeas i)
      (hmpos i) (hbi i) (hdiff i) (hFBsub i)
    refine ⟨_, ae_iff.1 ((ae_restrict_iff' (hBmeas i)).1 h), fun u hu huZ => ?_⟩
    by_contra hcon
    exact huZ fun h' => hcon (h' hu)
  choose Z hZnull hZgood using hZ
  -- Step 4: the product pieces `Ĝᵢ(t, u) = (t, Fᵢ u)`
  obtain ⟨G, hGcons⟩ : ∃ G : ℕ → Euclid (n + 1) → Euclid (N + 1), ∀ i (t : ℝ) (u : Euclid n),
      G i (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) =
        WithLp.toLp 2 (Fin.cons t (WithLp.ofLp (F i u))) :=
    ⟨fun i z => WithLp.toLp 2 (Fin.cons ((WithLp.ofLp z) 0)
      (WithLp.ofLp (F i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))))), fun i t u => by simp⟩
  -- Step 5: off a null set `Wᵢ`, `M̃` has approximate tangent space `range DĜᵢ(z)` at `Ĝᵢ z`
  -- for `z ∈ Âᵢ = Φₙ((0, 1) × Bᵢ)`
  have hW : ∀ i, ∃ W : Set (Euclid (n + 1)), volume W = 0 ∧ ∀ (t : ℝ) (u : Euclid n),
      t ∈ Ioo (0 : ℝ) 1 → u ∈ B i →
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) ∉ W →
      HasApproximateTangentSpaceAt (n + 1) Mt (G i (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))))
        (LinearMap.range (fderiv ℝ (G i) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) :
          Euclid (n + 1) →ₗ[ℝ] Euclid (N + 1))) := by
    intro i
    obtain ⟨hlip, hcolip, hder⟩ :=
      Submission.dimred_mbl_dt_lp_imc_suspension N n (F i) (G i) (hGcons i)
    set A := (fun p : ℝ × Euclid n => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
      Euclid (n + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ B i)
    have hA : MeasurableSet A := (hemb n).measurableSet_image.2 (measurableSet_Ioo.prod (hBmeas i))
    have hAbi : ∀ a ∈ A, ∀ a' ∈ A, min 1 (m i) * ‖a - a'‖ ≤ ‖G i a - G i a'‖ := by
      rintro _ ⟨⟨t, u⟩, ⟨-, hu⟩, rfl⟩ _ ⟨⟨t', u'⟩, ⟨-, hu'⟩, rfl⟩
      exact hcolip (m i) (B i) (hbi i) t t' u hu u' hu'
    have hAdiff : ∀ a ∈ A, DifferentiableAt ℝ (G i) a ∧ Injective (fderiv ℝ (G i) a) := by
      rintro _ ⟨⟨t, u⟩, ⟨-, hu⟩, rfl⟩
      obtain ⟨hd, -, hinj', -⟩ := hder t u (hdiff i u hu).1
      exact ⟨hd, hinj' (hdiff i u hu).2⟩
    have hAsub : G i '' A ⊆ Mt := by
      rintro _ ⟨_, ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩, rfl⟩
      exact ⟨(t, F i u), ⟨ht, hFBsub i ⟨u, hu, rfl⟩⟩, (hGcons i t u).symm⟩
    have h := Submission.dpf_approxTangent_ae_bilipschitz_piece (N + 1) (n + 1) univ Mt (G i) A
      (max 1 (L i)) (min 1 (m i)) isOpen_univ hMt (subset_univ _)
      (fun C _ _ => ne_top_of_le_ne_top hfinMt (measure_mono inter_subset_left))
      (hlip (L i) (hL i)) hA (lt_min one_pos (hmpos i)) hAbi hAdiff hAsub
    refine ⟨_, ae_iff.1 ((ae_restrict_iff' hA).1 h), fun t u ht hu hz => ?_⟩
    by_contra hcon
    exact hz fun h' => hcon (h' ⟨(t, u), ⟨ht, hu⟩, rfl⟩)
  choose W hWnull hWgood using hW
  -- Steps 6–7: the exceptional set `⋃ᵢ Ĝᵢ(Wᵢ ∪ Φₙ(ℝ × Zᵢ)) ∪ Ψ(ℝ × Z₀)` is `H^{n+1}`-null
  have hE : μHE[n + 1] ((⋃ i, G i '' (W i ∪ (fun p : ℝ × Euclid n =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (n + 1))) '' (univ ×ˢ Z i))) ∪
      (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
        Euclid (N + 1))) '' (univ ×ˢ (M \ ⋃ i, F i '' B i))) = 0 := by
    refine measure_union_null (measure_iUnion_null fun i => ?_)
      (Submission.dimred_mbl_dt_lp_imc_product_null N n _ hnull)
    have h0 : μHE[n + 1] (W i ∪ (fun p : ℝ × Euclid n =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (n + 1))) '' (univ ×ˢ Z i)) =
        0 := by
      refine measure_union_null ?_ (Submission.dimred_mbl_dt_lp_imc_product_null n n (Z i) ?_)
      · rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact hWnull i
      · rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact hZnull i
    obtain ⟨hlip, -, -⟩ :=
      Submission.dimred_mbl_dt_lp_imc_suspension N n (F i) (G i) (hGcons i)
    refine nonpos_iff_eq_zero.1
      ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (n + 1)
        (hlip (L i) (hL i)).lipschitzOnWith).trans ?_)
    rw [h0, mul_zero]
  -- Steps 8–9: the asserted property holds at every point of `M̃` outside the exceptional set
  rw [ae_restrict_iff' hMt]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE] with y hyE hyMt t x hyx Q hQ
  subst hyx
  -- `t ∈ (0, 1)` and `x ∈ M`, by injectivity of `Ψ`
  obtain ⟨ht, hxM⟩ : t ∈ Ioo (0 : ℝ) 1 ∧ x ∈ M := by
    obtain ⟨⟨t', x'⟩, ⟨ht', hx'⟩, hyeq⟩ := hyMt
    obtain ⟨rfl, rfl⟩ := hinj N t' t x' x hyeq
    exact ⟨ht', hx'⟩
  -- `x = Fᵢ u` with `u ∈ Bᵢ`, since `y ∉ Ψ(ℝ × Z₀)`
  have hx : x ∈ ⋃ i, F i '' B i := by
    by_contra hx
    exact hyE (Or.inr ⟨(t, x), ⟨mem_univ _, hxM, hx⟩, rfl⟩)
  obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.1 hx
  -- `z = Φₙ(t, u)` avoids `Wᵢ ∪ Φₙ(ℝ × Zᵢ)`, since `Ĝᵢ z = y` is not exceptional
  have hz : (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) ∉ W i ∪
      (fun p : ℝ × Euclid n => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
        Euclid (n + 1))) '' (univ ×ˢ Z i) :=
    fun hz => hyE (Or.inl (mem_iUnion.2 ⟨i, _, hz, hGcons i t u⟩))
  have huZ : u ∉ Z i := fun huZ => hz (Or.inr ⟨(t, u), ⟨mem_univ _, huZ⟩, rfl⟩)
  -- uniqueness gives `Q = range DFᵢ(u)`, and `range DĜᵢ(z) = Q̃(range DFᵢ(u))`
  have hQeq := hQ.unique (hZgood i u hu huZ)
  have hT := hWgood i t u ht hu fun h => hz (Or.inl h)
  obtain ⟨-, -, -, hrange, -⟩ := (Submission.dimred_mbl_dt_lp_imc_suspension N n (F i) (G i)
    (hGcons i)).2.2 t u (hdiff i u hu).1
  rwa [hGcons, hrange, ← hQeq] at hT

/-- **Cylinders over rectifiable sets** (the carrier `(0, 1) × M` of `[[(0, 1)]] × T`, Simon
Ch. 6, 2.17–2.21, with an arbitrary `I ⊆ ℝ` in place of `(0, 1)`): if `M ⊆ ℝᴺ` is countably
`n`-rectifiable, then `Ψ(I × M) ⊆ ℝ^{N+1}`, `Ψ(t, x) = (t, x₁, …, x_N)`, is countably
`(n + 1)`-rectifiable.  If `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ` Lipschitz, then
`Ψ(I × M) ⊆ Ψ(ℝ × M₀) ∪ ⋃ⱼ F̃ⱼ(ℝ^{n+1})`, where `F̃ⱼ(z) = Ψ(z₀, Fⱼ(z₁, …, zₙ))` is Lipschitz
(suspension lemma) and `Ψ(ℝ × M₀)` is `H^{n+1}`-null (product-null lemma). -/
theorem Submission.dimred_mbl_dt_lp_imc_cylinder_rectifiable : ∀ (N n : ℕ) (I : Set ℝ) (M : Set (Euclid N)), CountablyRectifiable n M → CountablyRectifiable (n + 1) ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (I ×ˢ M)) := by
  intro N n I M hM
  -- Step 1: the rectifiable cover `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)`
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  -- Step 2: the lifted maps `F̃ⱼ(z) = (z₀, Fⱼ(tail z))` satisfy `F̃ⱼ(t, u) = (t, Fⱼ(u))` and are
  -- Lipschitz by the suspension lemma
  let Fh : ℕ → Euclid (n + 1) → Euclid (N + 1) := fun j z =>
    WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0)
      (WithLp.ofLp (F j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))))
  have hFh : ∀ j (t : ℝ) (u : Euclid n), Fh j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) =
      WithLp.toLp 2 (Fin.cons t (WithLp.ofLp (F j u))) := by
    intro j t u
    simp [Fh]
  have hFhlip : ∀ j, ∃ K : NNReal, LipschitzWith K (Fh j) := by
    intro j
    obtain ⟨K, hK⟩ := hF j
    exact ⟨max 1 K, (Submission.dimred_mbl_dt_lp_imc_suspension N n (F j) (Fh j) (hFh j)).1 K hK⟩
  -- Step 3: the exceptional set `Ψ(ℝ × M₀)` is `H^{n+1}`-null by the product-null lemma
  refine ⟨_, Submission.dimred_mbl_dt_lp_imc_product_null N n M₀ hM₀, Fh, hFhlip, ?_⟩
  -- Step 4: the covering `Ψ(I × M) ⊆ Ψ(ℝ × M₀) ∪ ⋃ⱼ F̃ⱼ(ℝ^{n+1})`
  rintro _ ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩
  rcases hcover hx with hx0 | hx
  · exact Or.inl ⟨(t, x), ⟨mem_univ t, hx0⟩, rfl⟩
  · obtain ⟨j, u, rfl⟩ := mem_iUnion.mp hx
    exact Or.inr (mem_iUnion.mpr ⟨j, _, hFh j t u⟩)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
