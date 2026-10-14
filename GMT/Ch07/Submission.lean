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

/-- **Support calculus** for currents in `ℝᴾ` (Simon 6.2.11): (i) if `E` is closed and `X(ω) = 0`
whenever `spt ω ∩ E = ∅`, then `spt X ⊆ E`; (ii) `spt X` is closed; (iii)
`spt(A − B) ⊆ spt A ∪ spt B`; (iv) `spt 0 = ∅`; (v) `spt ∂A ⊆ spt A`.  A point lies off `spt X`
iff it has an open neighbourhood with compact closure on which `X` vanishes.  Small balls are such
neighbourhoods in the proper space `ℝᴾ`; zero neighbourhoods of `A` and `B` intersect to one of
`A − B`; and since `spt dη ⊆ spt η`, a zero neighbourhood of `A` is one of `∂A`. -/
theorem Submission.cmcsd_support_calculus : ∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support) := by
  intro P n
  -- `B_ε(x)` is open, and its closure lies in the compact `closedBall x ε` (`ℝᴾ` is proper)
  have hball : ∀ (x : Euclid P) (ε : ℝ), IsOpen (ball x ε) ∧ IsCompact (closure (ball x ε)) ∧
      closure (ball x ε) ⊆ univ := fun x ε =>
    ⟨isOpen_ball, (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i) for `x ∉ E`, a ball around `x` inside the open set `Eᶜ` is a zero neighbourhood of `x`
    intro E X hE hX x hx
    by_contra hxE
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
    refine hx.2 (mem_sUnion_of_mem (mem_ball_self hε)
      ⟨(hball x ε).1, (hball x ε).2.1, (hball x ε).2.2, fun ω hω => hX ω ?_⟩)
    exact subset_compl_iff_disjoint_right.mp (hω.trans hεE)
  · -- (ii) `spt X = univ \ X.zeroRegion`, and the zero region is open
    intro X
    exact isClosed_univ.sdiff X.isOpen_zeroRegion
  · -- (iii) the intersection of zero neighbourhoods of `A` and `B` is one of `A − B`
    intro A B x hx
    by_contra hAB
    have hxA : x ∈ A.zeroRegion := by
      by_contra h
      exact hAB (mem_union_left _ ⟨mem_univ x, h⟩)
    have hxB : x ∈ B.zeroRegion := by
      by_contra h
      exact hAB (mem_union_right _ ⟨mem_univ x, h⟩)
    obtain ⟨WA, ⟨hWAo, hWAc, -, hWAv⟩, hxWA⟩ := mem_sUnion.mp hxA
    obtain ⟨WB, ⟨hWBo, -, -, hWBv⟩, hxWB⟩ := mem_sUnion.mp hxB
    refine hx.2 (mem_sUnion_of_mem (⟨hxWA, hxWB⟩ : x ∈ WA ∩ WB) ⟨hWAo.inter hWBo,
      hWAc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩)
    change A ω - B ω = 0
    rw [hWAv ω (hω.trans inter_subset_left), hWBv ω (hω.trans inter_subset_right), sub_zero]
  · -- (iv) every ball is a zero neighbourhood of the zero current
    exact eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 (mem_sUnion_of_mem
      (mem_ball_self one_pos) ⟨(hball x 1).1, (hball x 1).2.1, (hball x 1).2.2,
        fun ω _ => GeometricCurrentOn.zero_apply ω⟩)
  · -- (v) `∂A(η) = A(dη)` with `spt dη ⊆ spt η`: a zero neighbourhood of `A` is one of `∂A`
    intro A x hx
    refine ⟨mem_univ x, fun hxA => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := mem_sUnion.mp hxA
    refine mem_sUnion_of_mem hxW ⟨hWo, hWc, hWU, fun η hη => ?_⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) n)).trans hη)
/-- **The Euclidean coefficient norm is a continuous seminorm dominated by the operator norm**
(Simon Ch. 6, 1.15 and 2.4; used by the smooth approximation of test forms behind the mass of
`τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})`
for strictly increasing `I : Fin n → Fin P` and `c_I α = 0` otherwise.  Then
`covectorEuclideanNorm α = ‖v α‖` for the coefficient vector
`v α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)`, which is linear in `α`; this gives the
triangle inequality and homogeneity.  `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖` gives the bound with
`C = √(card (Fin n → Fin P))`, and then the norm is `C`-Lipschitz, hence continuous. -/
theorem Submission.rsd_mw_tfa_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
  intro P n
  classical
  -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
    if StrictMono I then α (fun i => e (I i)) else 0
  let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
    WithLp.toLp 2 (fun I => c I α)
  have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [v, c, e, hI]
  -- Step 2: `v` is additive and `ℝ`-homogeneous
  have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
    intro α α'
    simp only [v, ← WithLp.toLp_add]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
    intro t α
    simp only [v, ← WithLp.toLp_smul]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
  have h1 : ∀ α α' : Covector (Euclid P) n,
      covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
    intro α α'
    rw [hN, hN, hN, hadd]
    exact norm_add_le _ _
  -- Step 4: (ii), homogeneity of the Euclidean norm
  have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
  -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
  have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
    intro I α
    by_cases hI : StrictMono I
    · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
    · simp [c, hI]
  -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
  have h3 : ∀ α : Covector (Euclid P) n,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
    intro α
    have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
      Finset.sum_le_sum fun I _ => by
        simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
    rw [hN, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
  have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
      (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
    intro α α'
    have ha : covectorEuclideanNorm α ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
      simpa only [sub_add_cancel] using h1 (α - α') α'
    have hb : covectorEuclideanNorm α' ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
      have h := h1 (α' - α) α
      rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
    have hC := h3 (α - α')
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    constructor <;> linarith
  exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
    (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩
/-- **Simon §6.1** (the test-form topology, the case `β = 0`): if `ωⱼ → 0` in `𝒟ⁿ(U)`, the
`ωⱼ` vanish outside one compact `C ⊆ U`, and `supₓ ‖ωⱼ(x)‖ → 0`.  The compact set is the one in
`TestFormOnConverges`; uniform convergence of the `0`-th iterated derivatives on `C` gives the
bound on `C`, and `ωⱼ = 0` off `C`. -/
theorem Submission.dpf_pfc_testFormOnConverges_zero_uniform : ∀ (P n : ℕ) (U : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), TestFormOnConverges ωs 0 → ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ U ∧ (∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε := by
  intro P n U ωs h
  obtain ⟨C, hC, hCU, hsupp, -, hderiv⟩ := h
  have hzero : ∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')
  refine ⟨C, hC, hCU, hzero, fun ε hε => ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hderiv 0) ε hε] with j hj x
  by_cases hx : x ∈ C
  · have hjx := hj x hx
    simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
      norm_iteratedFDeriv_zero] at hjx
    exact hjx.le
  · rw [hzero j x hx, norm_zero]
    exact hε.le

/-- **A linear functional on test forms dominated by the coefficient sup norm is a current**
(Simon Ch. 6, proof of 7.2, where the `M`-absolutely convergent series define currents; the
topology of `𝒟ⁿ(U)` is that of §6.1).  Suppose `|L ω| ≤ c A` whenever `|ω(x)| ≤ c` for all `x`.
Then `A ≥ 0` (take `ω = 0`).  If `ωⱼ → 0` in `𝒟ⁿ(U)`, then for large `j` and all `x`,
`|ωⱼ(x)| ≤ C ‖ωⱼ(x)‖ ≤ (C + 1) ε`, so `|L ωⱼ| ≤ (C + 1) ε A < η` for
`ε = η / (2 (C + 1) (A + 1))`.  Hence `L` is sequentially continuous, and `⟨L, ·⟩` is the
current. -/
theorem Submission.cmc_fc_sc_current_of_coeff_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ) (A : ℝ), (∀ (ω : TestFormOn U n) (c : ℝ), 0 < c → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |L ω| ≤ c * A) → ∃ Y : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, Y ω = L ω := by
  intro P n U L A hL
  -- Step 1: `A ≥ 0`, from the bound at `ω = 0`, `c = 1`
  have hA : 0 ≤ A := by simpa using hL 0 1 one_pos fun x => by simp
  -- Step 2: `|α| ≤ C ‖α‖`
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P n).2.2.1
  -- Step 4: `Y = ⟨L, ·⟩`; its continuity is Step 3
  refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => rfl⟩
  -- Step 3: eventually `supₓ ‖ωⱼ(x)‖ ≤ ε`, hence `|L ωⱼ| ≤ (C + 1) ε A < η`
  obtain ⟨K, -, -, -, hunif⟩ := Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
  rw [Metric.tendsto_atTop]
  intro η hη
  have hC1 : 0 < C + 1 := by linarith
  have hA1 : 0 < A + 1 := by linarith
  set ε : ℝ := η / (2 * (C + 1) * (A + 1)) with hε
  have hεpos : 0 < ε := div_pos hη (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hεpos)
  refine ⟨N, fun j hj => ?_⟩
  have hbound : ∀ x, covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x) ≤
      (C + 1) * ε := fun x =>
    (hC _).trans <| (mul_le_mul_of_nonneg_left (hN j hj x) hC0).trans <| by nlinarith
  have hkey : (C + 1) * ε * (A + 1) = η / 2 := by
    rw [hε]
    field_simp
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ (C + 1) * ε * A := hL (ωs j) _ (by positivity) hbound
    _ ≤ (C + 1) * ε * (A + 1) := by nlinarith
    _ = η / 2 := hkey
    _ < η := by linarith
/-- **Current toolkit** in `ℝᴺ` (Simon 6.2.4–6.2.11), given that a current kills forms supported
off its support (VO) and the representation theorem (REP): (A0) `|X(ψ)| ≤ c M(X)` if `|ψ| ≤ c` on
`spt X`; (MB) `|T(ω)| ≤ C c` whenever `|ω| ≤ c` gives `M(T) ≤ C`; (LOC) `X(η) = X(η')` if `η = η'`
on an open `W ⊇ spt X`; (NCD) differences and (NCB) boundaries of currents with compact support,
finite mass and finite boundary mass are again such currents.  For (A0), (REP) gives `(μ, ξ)` with
`μ(ℝᴺ) = M(X)`, and (VO) gives `μ((spt X)ᶜ) = 0`; the rest uses mass suprema, the support calculus
and `∂∂ = 0`. -/
theorem Submission.dimred_mbl_dt_lpo_current_toolkit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) ∧ (∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T ω| ≤ C * c) → T.mass ≤ ENNReal.ofReal C) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η') ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → (X - Y).support ⊆ X.support ∪ Y.support ∧ IsCompact (X - Y).support ∧ (X - Y).mass < ∞ ∧ boundaryMassOn (X - Y) univ < ∞) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.boundary.mass < ∞ → X.boundary.support ⊆ X.support ∧ IsCompact X.boundary.support ∧ boundaryMassOn X.boundary univ < ∞ := by
  intro hVO hREP
  -- (MB) each admissible test form has value at most `C`, so their supremum `M(T)` is at most `C`
  have hMB : ∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : ℝ),
      (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) →
          |T ω| ≤ C * c) → T.mass ≤ ENNReal.ofReal C := by
    intro N k T C hT
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((hT ω 1 hω.2).trans_eq (mul_one C)))
  -- `M(A − B) ≤ M(A) + M(B)`: `(A − B)(ω) = A(ω) + B(−ω)`, and `−ω` is admissible with `ω`
  have hmass_sub : ∀ (N k : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid N)) k),
      (A - B).mass ≤ A.mass + B.mass := by
    intro N k A B
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have hω' : -ω ∈ massAdmissibleOn univ k univ :=
      ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
    have hneg : B (-ω) = -B ω := map_neg B.toCurrent ω
    calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by
          rw [hneg, ← sub_eq_add_neg]
          rfl
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.mass + B.mass := add_le_add (A.le_massOn hω) (B.le_massOn hω')
  refine ⟨?_, hMB, ?_, ?_, ?_⟩
  · -- (A0) represent `X` by `(μ, ξ)`; `μ` is finite, with `μ(univ) = M(X)`, and carried by `spt X`
    intro N k X ψ c hX hψ
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hrep, -⟩ := hREP N k univ X isOpen_univ
      fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨by rw [hμ]; exact hX⟩
    -- `μ((spt X)ᶜ) = M_{(spt X)ᶜ}(X) = 0`: `X` kills the forms supported off `spt X` (VO)
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine nonpos_iff_eq_zero.mp (sSup_le ?_)
      rintro _ ⟨ω, hω, rfl⟩
      simp [hVO N k univ X ω (Set.disjoint_left.mpr fun x hx hxX => hxX.2 (hω.1 hx))]
    have hspt : ∀ᵐ x ∂μ, x ∈ X.support :=
      ae_iff.mpr (measure_mono_null (fun x hx => not_not.mp fun h => hx ⟨mem_univ x, h⟩) hZ)
    have hb : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
      filter_upwards [hspt] with x hx
      exact (Real.norm_eq_abs _).trans_le ((hξ x _).trans (hψ x hx))
    calc |X ψ| = ‖∫ x, ξ x ((ψ : DifferentialForm (Euclid N) k) x) ∂μ‖ := by
          rw [hrep ψ, Real.norm_eq_abs]
      _ ≤ c * μ.real univ := norm_integral_le_of_norm_le_const hb
      _ = c * X.mass.toReal := by rw [measureReal_def, hμ]
  · -- (LOC) `η − η'` vanishes on `W`, so `spt(η − η') ⊆ Wᶜ` misses `spt X ⊆ W`; apply (VO)
    intro N k X η η' W hW hXW hηη'
    have hsupp : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
        DifferentialForm (Euclid N) k) ⊆ Wᶜ :=
      closure_minimal (fun x hx hxW => hx (by simp [hηη' x hxW])) hW.isClosed_compl
    have hlin : X (η - η') = X η - X η' := map_sub X.toCurrent η η'
    rw [← sub_eq_zero, ← hlin]
    exact hVO N k univ X (η - η') (disjoint_compl_left.mono hsupp hXW)
  · -- (NCD) `spt(X − Y) ⊆ spt X ∪ spt Y` is closed, hence compact; masses add up, also for `∂`
    intro N k X Y hXc hXm hXb hYc hYm hYb
    have hspt := (Submission.cmcsd_support_calculus N k).2.2.1 X Y
    refine ⟨hspt, (hXc.union hYc).of_isClosed_subset
      ((Submission.cmcsd_support_calculus N k).2.1 _) hspt,
      (hmass_sub N k X Y).trans_lt (ENNReal.add_lt_top.mpr ⟨hXm, hYm⟩), ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      -- `∂(X − Y) = ∂X − ∂Y`: both send `ω` to `X(dω) − Y(dω)`
      have hb : (X - Y).boundary = X.boundary - Y.boundary := GeometricCurrentOn.ext fun ω => rfl
      show (X - Y).boundary.mass < ∞
      rw [hb]
      exact (hmass_sub N k _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hXb, hYb⟩)
  · -- (NCB) `spt ∂X ⊆ spt X` is closed, hence compact; `∂∂X = 0` has mass `0` by (MB)
    intro N k X hXc hXb
    have hspt := (Submission.cmcsd_support_calculus N k).2.2.2.2 X
    refine ⟨hspt, hXc.of_isClosed_subset ((Submission.cmcsd_support_calculus N k).2.1 _) hspt, ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      show X.boundary.boundary.mass < ∞
      rw [GeometricCurrentOn.boundary_boundary]
      exact (hMB N k 0 0 fun ω c _ => by simp).trans_lt ENNReal.ofReal_lt_top
/-- **A cut-off of the pull-back that is compatible with `d`** (Simon 6.1.13–6.1.14).  Let
`F : ℝᴺ → ℝᴺ'` be `C^∞`, `ω ∈ 𝒟ᵏ(ℝᴺ')` and `K ⊆ ℝᴺ` compact.  Then some test form `η ∈ 𝒟ᵏ(ℝᴺ)`
and open `W ⊇ K` satisfy `η = F^#ω` and `dη = F^#(dω)` on `W`.  The pull-back
`F^#ω(x) = Φ(DF(x))(ω(F x))` is `C^∞` because the precomposition `Φ(L) = (γ ↦ γ ∘ L)` is
analytic.  It satisfies `d(F^#ω) = F^#(dω)` (`extDeriv_pullback`).  Take `η = ζ · F^#ω` for a
smooth `ζ` with `support ζ = thickening 1 K` and `ζ = 1` on `cthickening (1/2) K`.  Then
`η = F^#ω` on the open set `W = thickening (1/2) K ⊇ K`, so `dη = d(F^#ω)` there. -/
theorem Submission.dimred_mbl_dt_lpo_cutoff_pullback : ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
  intro N N' k F ω K hF hK
  -- `ω` is `C^∞`
  have hωs : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid N') k) := ω.property.1.1
  -- the precomposition `Φ(L) = (γ ↦ γ ∘ L)` on `k`-covectors is analytic, hence `C^∞`
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Euclid N →L[ℝ] Euclid N') →
        (Euclid N' [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (Euclid N [⋀^Fin k]→L[ℝ] ℝ)) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- `DF` and `ω ∘ F` are `C^∞`, so `F^#ω = Φ(DF)(ω ∘ F)` is `C^∞`
  have hDF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) :=
    (hΦ.comp hDF).clm_apply (hωs.comp hF)
  -- `d(F^#ω) = F^#(dω)` at every point
  have hpb : ∀ x, exteriorDerivative (fun y =>
      ((ω : DifferentialForm (Euclid N') k) (F y)).compContinuousLinearMap (fderiv ℝ F y)) x =
      (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap
        (fderiv ℝ F x) := fun x =>
    extDeriv_pullback (hωs.differentiable (by simp)).differentiableAt hF.contDiffAt (by simp)
  -- a cut-off `ζ` with `support ζ = thickening 1 K` and `ζ = 1` exactly on `cthickening (1/2) K`
  obtain ⟨ζ, hζ, -, hζsupp, hζone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := 1) (E := K)) (isClosed_cthickening (δ := 1 / 2) (E := K))
    (cthickening_subset_thickening' one_pos (by norm_num) K)
  -- `spt ζ ⊆ cthickening 1 K`, which is compact
  have hζc : HasCompactSupport ζ := by
    refine (hK.cthickening (r := 1)).of_isClosed_subset (isClosed_tsupport ζ) ?_
    show closure (support ζ) ⊆ _
    rw [hζsupp]
    exact closure_thickening_subset_cthickening 1 K
  -- `ζ = 1` on the open set `W = thickening (1/2) K ⊇ K`
  have hW : ∀ x ∈ thickening (1 / 2) K, ζ x = 1 := fun x hx =>
    (hζone x).mp (thickening_subset_cthickening _ _ hx)
  -- `η = ζ · F^#ω` is a test form, equal to `F^#ω` on `W`
  refine ⟨⟨fun x => ζ x • ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap
      (fderiv ℝ F x), ⟨hζ.smul hβ, hζc.smul_right⟩, subset_univ _⟩, thickening (1 / 2) K,
    isOpen_thickening, self_subset_thickening (by norm_num) K, fun x hx => ?_, fun x hx => ?_⟩
  · show ζ x • _ = _
    rw [hW x hx, one_smul]
  · -- `η = F^#ω` near `x ∈ W`, so `dη(x) = d(F^#ω)(x) = F^#(dω)(x)`
    rw [← hpb x]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
    show ζ y • _ = _
    rw [hW y hy, one_smul]
/-- **Smooth `Λ`-Lipschitz mollifications of a `Λ`-Lipschitz map.**  For `σ = 1/(j+1)` let `φ` be
a `C^∞` bump with support `B(0, σ)` and `ρⱼ = (∫ φ)⁻¹ φ` its normalization (`ρⱼ ≥ 0`,
`∫ ρⱼ = 1`).  Then `Fⱼ = ρⱼ ⋆ F`, `Fⱼ(x) = ∫ ρⱼ(t) F(x − t) dt`, is `C^∞` (convolution with a
compactly supported smooth kernel), `Λ`-Lipschitz (an average of the `Λ`-Lipschitz translates of
`F`), and `|Fⱼ(x) − F(x)| ≤ Λσ`, since `|F(y) − F(x)| ≤ Λσ` on `B(x, σ)`. -/
theorem Submission.dimred_mbl_dt_lpo_mollify_lipschitz : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ ∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := by
  intro N N' Λ F hF
  -- for each `j` a mollifier `ρ j`: `C^∞`, compactly supported, `≥ 0`, `∫ ρ j = 1`,
  -- `spt ρ j ⊆ B(0, 1/(j+1))`; it is the normalized bump `(∫ φ)⁻¹ φ`
  have hmoll : ∀ j : ℕ, ∃ ρ : Euclid N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∀ y, 0 ≤ ρ y) ∧ ∫ y, ρ y = 1 ∧ support ρ ⊆ ball 0 (1 / ((j : ℝ) + 1)) := by
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
    have hσ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    let φ : ContDiffBump (0 : Euclid N) :=
      ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), half_pos hσ, half_lt_self hσ⟩
    have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    -- `∫ φ > 0`, as `φ ≥ 0` and `support φ = B(0, σ)` has positive measure
    have hφp : 0 < ∫ y, φ y := by
      rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
      exact measure_ball_pos volume 0 φ.rOut_pos
    have hsupp : support (fun y => (∫ z, φ z)⁻¹ * φ y) ⊆ support φ :=
      support_mul_subset_right _ _
    refine ⟨fun y => (∫ z, φ z)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
      φ.hasCompactSupport.mono hsupp, fun y => mul_nonneg (inv_nonneg.2 hφp.le) φ.nonneg, ?_,
      hsupp.trans φ.support_eq.subset⟩
    rw [integral_const_mul, inv_mul_cancel₀ hφp.ne']
  choose ρ hρs hρc hρn hρi hρsupp using hmoll
  -- `Fs j = ρ j ⋆ F`
  refine ⟨fun j => convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun j => ?_,
    fun j => ?_, fun j x => ?_⟩
  · -- `C^∞`: `ρ j` is `C^∞` with compact support and `F` is continuous, so locally integrable
    exact (hρc j).contDiff_convolution_left _ (hρs j) hF.continuous.locallyIntegrable
  · -- `Λ`-Lipschitz: `Fs j x - Fs j x' = ∫ ρ j t • (F (x - t) - F (x' - t)) dt`
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hint : ∀ z, Integrable (fun t => ρ j t • F (z - t)) := fun z =>
      ((hρs j).continuous.smul (hF.continuous.comp (continuous_const.sub continuous_id))
        ).integrable_of_hasCompactSupport ((hρc j).smul_right (f' := fun t => F (z - t)))
    show dist (∫ t, ρ j t • F (x - t)) (∫ t, ρ j t • F (x' - t)) ≤ Λ * dist x x'
    rw [dist_eq_norm, ← integral_sub (hint x) (hint x')]
    calc ‖∫ t, ρ j t • F (x - t) - ρ j t • F (x' - t)‖
        ≤ ∫ t, ρ j t * ((Λ : ℝ) * dist x x') := by
          refine norm_integral_le_of_norm_le
            (((hρs j).continuous.integrable_of_hasCompactSupport (hρc j)).mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hρn j t), ← dist_eq_norm]
          refine mul_le_mul_of_nonneg_left ?_ (hρn j t)
          calc dist (F (x - t)) (F (x' - t)) ≤ Λ * dist (x - t) (x' - t) := hF.dist_le_mul _ _
            _ = Λ * dist x x' := by rw [dist_sub_right]
      _ = (Λ : ℝ) * dist x x' := by rw [integral_mul_const, hρi j, one_mul]
  · -- distance: `dist (F y) (F x) ≤ Λ / (j + 1)` on `B(x, 1/(j+1))`, and `ρ j` is a mollifier
    have hg : ∀ y ∈ ball x (1 / ((j : ℝ) + 1)), dist (F y) (F x) ≤ Λ * (1 / ((j : ℝ) + 1)) :=
      fun y hy => (hF.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le Λ.coe_nonneg)
    calc dist (convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x) (F x)
        ≤ Λ * (1 / ((j : ℝ) + 1)) :=
          dist_convolution_le (by positivity) (hρsupp j) (hρn j) (hρi j)
            hF.continuous.aestronglyMeasurable hg
      _ = Λ / ((j : ℝ) + 1) := by ring
/-- **Affine homotopies `ℝ^{N+1} → ℝ^{N'}`.**  Write `ι(t, x) = (t, x₁, …, x_N)`,
`e₀ = ι(1, 0)` and `J v = ι(0, v)`.  (i) For `C^∞` maps `F, G : ℝ^N → ℝ^{N'}`, the map
`H(y) = F(tail y) + y₀ • (G(tail y) − F(tail y))` is `C^∞` with
`H(ι(t, x)) = F(x) + t • (G(x) − F(x))`.  (ii) If `H(ι(s, z)) = F(z) + s • (G(z) − F(z))` for all
`s, z`, with `F, G` differentiable at `x` and `H` differentiable at `ι(t, x)`, then the chain rule
along `s ↦ ι(s, x)` and along `z ↦ ι(t, z)` gives `DH e₀ = G(x) − F(x)` and
`DH ∘ J = DF(x) + t • (DG(x) − DF(x))`.  Since `w = w₀ • e₀ + J(tail w)` with
`|w₀|, ‖tail w‖ ≤ ‖w‖`, we get `‖DH‖ ≤ ‖G(x) − F(x)‖ + ‖DF(x) + t • (DG(x) − DF(x))‖`. -/
theorem Submission.dimred_mbl_dt_lpo_affine_homotopy : (∀ (N N' : ℕ) (F G : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ∃ H : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) H ∧ ∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) ∧ ∀ (N N' : ℕ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (t : ℝ) (x : Euclid N), DifferentiableAt ℝ F x → DifferentiableAt ℝ G x → DifferentiableAt ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) → (∀ (s : ℝ) (z : Euclid N), H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp z))) = F z + s • (G z - F z)) → fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = G x - F x ∧ (∀ v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v + t • (fderiv ℝ G x v - fderiv ℝ F x v)) ∧ ‖fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖G x - F x‖ + ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ := by
  constructor
  · intro N N' F G hF hG
    -- the coordinates `y ↦ y₀` and `y ↦ tail y = (y₁, …, y_N)` are continuous linear
    obtain ⟨p, hp⟩ : ∃ p : Euclid (N + 1) →L[ℝ] ℝ, ∀ y, p y = WithLp.ofLp y 0 :=
      ⟨EuclideanSpace.proj 0, fun y => rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : Euclid (N + 1) →L[ℝ] Euclid N,
        ∀ y, T y = WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
          map_add' := fun a b => rfl
          map_smul' := fun c a => rfl }, fun y => rfl⟩
    -- `H(y) = F(tail y) + y₀ • (G(tail y) − F(tail y))` is `C^∞`, and `tail ι(t, x) = x`
    refine ⟨fun y => F (T y) + p y • (G (T y) - F (T y)), ?_, fun t x => ?_⟩
    · exact (hF.comp T.contDiff).add
        (p.contDiff.smul ((hG.comp T.contDiff).sub (hF.comp T.contDiff)))
    · simp only [hp, hT, Fin.tail_cons, Fin.cons_zero, WithLp.toLp_ofLp]
  · intro N N' F G H t x hF hG hH hHFG
    -- `J v = ι(0, v)` is continuous linear
    obtain ⟨J, hJ⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
        ∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
          map_add' := fun a b => by ext i; cases i using Fin.cases <;> simp
          map_smul' := fun c a => by ext i; cases i using Fin.cases <;> simp }, fun v => rfl⟩
    set D := fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) with hD
    set A := fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x) with hA
    -- (a) chain rule along the line `s ↦ ι(s, x) = s • e₀ + J x`: `D e₀ = G(x) − F(x)`
    have he : D (EuclideanSpace.single 0 1) = G x - F x := by
      have hc : HasDerivAt
          (fun s : ℝ => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)))
          (EuclideanSpace.single 0 1) t := by
        have : (fun s : ℝ => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) =
            fun s => s • EuclideanSpace.single 0 1 + J x := by
          funext s; ext i; cases i using Fin.cases <;> simp [hJ]
        rw [this]
        simpa using ((hasDerivAt_id t).smul_const
          (EuclideanSpace.single 0 1 : Euclid (N + 1))).add_const (J x)
      have h1 := hH.hasFDerivAt.comp_hasDerivAt t hc
      have h2 : HasDerivAt (fun s : ℝ => F x + s • (G x - F x)) (G x - F x) t := by
        simpa using ((hasDerivAt_id t).smul_const (G x - F x)).const_add (F x)
      have h3 : (H ∘ fun s : ℝ => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) =
          fun s => F x + s • (G x - F x) := by
        funext s; exact hHFG s x
      rw [h3] at h1
      exact h1.unique h2
    -- (b) chain rule along the affine map `z ↦ ι(t, z) = J z + t • e₀`: `D ∘ J = A`
    have hDJ : D.comp J = A := by
      have hl : HasFDerivAt
          (fun z : Euclid N => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) : Euclid (N + 1)))
          J x := by
        have : (fun z : Euclid N => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) : Euclid (N + 1))) =
            fun z => J z + t • EuclideanSpace.single 0 1 := by
          funext z; ext i; cases i using Fin.cases <;> simp [hJ]
        rw [this]
        exact J.hasFDerivAt.add_const _
      have h1 := hH.hasFDerivAt.comp x hl
      have h2 := hF.hasFDerivAt.add ((hG.hasFDerivAt.sub hF.hasFDerivAt).const_smul t)
      have h3 : (H ∘ fun z : Euclid N => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z)) :
          Euclid (N + 1))) = fun z => F z + t • (G z - F z) := by
        funext z; exact hHFG t z
      rw [h3] at h1
      exact h1.unique h2
    have hDJv : ∀ v, D (J v) = A v := fun v => by
      rw [← ContinuousLinearMap.comp_apply, hDJ]
    refine ⟨he, fun v => ?_, ?_⟩
    · rw [← hJ, hDJv, hA]
      simp
    -- (c) `w = w₀ • e₀ + J (tail w)`, so `D w = w₀ • (G(x) − F(x)) + A (tail w)`
    · refine ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
        fun w => ?_
      have hw : w = WithLp.ofLp w 0 • EuclideanSpace.single 0 1 +
          J (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w))) := by
        ext i; cases i using Fin.cases <;> simp [hJ, Fin.tail]
      have hDw : D w = WithLp.ofLp w 0 • (G x - F x) +
          A (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w))) := by
        rw [congrArg D hw, map_add, map_smul, he, hDJv]
      -- `|w₀| ≤ ‖w‖` and `‖tail w‖ ≤ ‖w‖`
      have h0 : |WithLp.ofLp w 0| ≤ ‖w‖ := by
        simpa using PiLp.norm_apply_le w 0
      have h1 : ‖(WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)) : Euclid N)‖ ≤ ‖w‖ := by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        apply Real.sqrt_le_sqrt
        rw [Fin.sum_univ_succ]
        exact le_add_of_nonneg_left (sq_nonneg _)
      calc ‖D w‖ ≤ ‖WithLp.ofLp w 0 • (G x - F x)‖ +
            ‖A (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)))‖ := by
            rw [hDw]; exact norm_add_le _ _
        _ ≤ |WithLp.ofLp w 0| * ‖G x - F x‖ +
            ‖A‖ * ‖(WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)) : Euclid N)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            exact add_le_add le_rfl (A.le_opNorm _)
        _ ≤ ‖w‖ * ‖G x - F x‖ + ‖A‖ * ‖w‖ := by gcongr
        _ = (‖G x - F x‖ + ‖A‖) * ‖w‖ := by ring

/-- **Homotopy formula for `C^∞` maps, evaluated on test forms** (Simon 6.2.25–6.2.26).  Let
`H(ι(t, x)) = F(x) + t(G(x) − F(x))` be the affine homotopy of the `C^∞` maps `F`, `G`, and let
`C` (and, in degree `k + 1`, `C'`) be currents supported in `S(X) = ι([0, 1] × spt X)` with
`∂C(β) = X(β₁) − X(β₀)` (resp. `− C'(β)`) for the slices `β_s(x)(v) = β(ι(s, x))(J v)`.  If `ηF`,
`ηG` agree with `F^#ω`, `G^#ω` near `spt X` and `θ`, `θ'` agree with `H^#(dω)`, `H^#ω` near
`S(X)`, then `X(ηG) − X(ηF) = C(θ)` (resp. `C(θ) + C'(θ')`).  A cut-off `θ''` of `H^#ω` near the
compact set `S(X)` has `dθ'' = H^#(dω)` there, so `C(θ) = ∂C(θ'')` by locality; the slices of
`θ''` at `t = 0, 1` agree with `F^#ω`, `G^#ω` near `spt X`, since `H(ι(0, ·)) = F`,
`DH(ι(0, x)) ∘ J = DF(x)`, and likewise at `t = 1` with `G`. -/
theorem Submission.dimred_mbl_dt_lpo_smooth_homotopy_identity : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (N N' : ℕ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (⊤ : ℕ∞) H → (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (0 + 1)) (ω : TestFormOn (univ : Set (Euclid N')) 0) (ηF ηG : TestFormOn (univ : Set (Euclid N)) 0) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (0 + 1)), IsCompact X.support → C.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → (∀ β : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ C.boundary β = X η₁ - X η₀) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) 0) x = ((ω : DifferentialForm (Euclid N') 0) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) 0) x = ((ω : DifferentialForm (Euclid N') 0) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ W : Set (Euclid (N + 1)), IsOpen W ∧ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W ∧ ∀ y ∈ W, (θ : DifferentialForm (Euclid (N + 1)) (0 + 1)) y = (exteriorDerivative (ω : DifferentialForm (Euclid N') 0) (H y)).compContinuousLinearMap (fderiv ℝ H y)) → X ηG - X ηF = C θ) ∧ ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)) (C' : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)) (ηF ηG : TestFormOn (univ : Set (Euclid N)) (k + 1)) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)) (θ' : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), IsCompact X.support → C.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → C'.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → (∀ β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ C.boundary β = X η₁ - X η₀ - C' β) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ W : Set (Euclid (N + 1)), IsOpen W ∧ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W ∧ ∀ y ∈ W, (θ : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) y = (exteriorDerivative (ω : DifferentialForm (Euclid N') (k + 1)) (H y)).compContinuousLinearMap (fderiv ℝ H y)) → (∃ W : Set (Euclid (N + 1)), IsOpen W ∧ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W ∧ ∀ y ∈ W, (θ' : DifferentialForm (Euclid (N + 1)) (k + 1)) y = ((ω : DifferentialForm (Euclid N') (k + 1)) (H y)).compContinuousLinearMap (fderiv ℝ H y)) → X ηG - X ηF = C θ + C' θ' := by
  intro hVO hREP N N' F G H hF hG hH hHF
  -- (LOC): a current only sees a test form on an open neighbourhood of its support
  have hLOC := (Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP).2.2.1
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hHd : Differentiable ℝ H := hH.differentiable (by simp)
  -- `(t, x) ↦ ι(t, x)` is continuous, so `S(A) = ι([0, 1] × A)` is compact for compact `A`
  have hι : Continuous fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1)) := by
    fun_prop
  have hScpt : ∀ A : Set (Euclid N), IsCompact A →
      IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ A,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
    intro A hA
    have hS : {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ A,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} =
        (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
          Euclid (N + 1))) '' (Icc (0 : ℝ) 1 ×ˢ A) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [hS]
    exact (isCompact_Icc.prod hA).image hι
  -- near `spt X`, the slice at `t = s` of `β = H^#ω` is the pull-back by `Φ = H(ι(s, ·))`
  have hslice : ∀ (d : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) d)
      (ω : TestFormOn (univ : Set (Euclid N')) d)
      (β : TestFormOn (univ : Set (Euclid (N + 1))) d) (W'' : Set (Euclid (N + 1))) (s : ℝ)
      (Φ : Euclid N → Euclid N') (η ηΦ : TestFormOn (univ : Set (Euclid N)) d),
      s ∈ Icc (0 : ℝ) 1 → IsOpen W'' →
      {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ⊆ W'' →
      (∀ y ∈ W'', (β : DifferentialForm (Euclid (N + 1)) d) y =
        ((ω : DifferentialForm (Euclid N') d) (H y)).compContinuousLinearMap (fderiv ℝ H y)) →
      (∀ x : Euclid N, H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) = Φ x) →
      (∀ x v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
        (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ Φ x v) →
      (∀ (x : Euclid N) (v : Fin d → Euclid N), (η : DifferentialForm (Euclid N) d) x v =
        (β : DifferentialForm (Euclid (N + 1)) d) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        (ηΦ : DifferentialForm (Euclid N) d) x =
          ((ω : DifferentialForm (Euclid N') d) (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x)) →
      X η = X ηΦ := by
    rintro d X ω β W'' s Φ η ηΦ hs hW'' hSW'' hβ hΦ hDΦ hη ⟨WΦ, hWΦ, hXWΦ, hηΦ⟩
    -- `η = ηΦ` on the open set `WΦ ∩ ι(s, ·)⁻¹(W'') ⊇ spt X`
    refine hLOC N d X η ηΦ (WΦ ∩ (fun x : Euclid N =>
        (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) ⁻¹' W'')
      (hWΦ.inter (hW''.preimage (by fun_prop)))
      (fun x hx => ⟨hXWΦ hx, (hSW'' ⟨s, hs, x, hx, rfl⟩ :
        WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) ∈ W'')⟩) ?_
    rintro x ⟨hxΦ, hxW''⟩
    rw [hηΦ x hxΦ]
    ext v
    rw [hη x v, hβ (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) hxW'']
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hΦ x]
    congr 1
    funext i
    exact hDΦ x (v i)
  -- `H(ι(0, ·)) = F`, `DH(ι(0, x)) ∘ J = DF(x)`, `H(ι(1, ·)) = G`, `DH(ι(1, x)) ∘ J = DG(x)`
  have hH0 : ∀ x : Euclid N, H (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) = F x := by
    intro x
    rw [hHF]
    simp
  have hH1 : ∀ x : Euclid N, H (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) = G x := by
    intro x
    rw [hHF]
    simp
  have hDH0 : ∀ x v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)))
      (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v := by
    intro x v
    rw [(Submission.dimred_mbl_dt_lpo_affine_homotopy.2 N N' F G H 0 x (hFd x) (hGd x)
      (hHd _) hHF).2.1 v]
    simp
  have hDH1 : ∀ x v : Euclid N, fderiv ℝ H (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x)))
      (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ G x v := by
    intro x v
    rw [(Submission.dimred_mbl_dt_lpo_affine_homotopy.2 N N' F G H 1 x (hFd x) (hGd x)
      (hHd _) hHF).2.1 v]
    simp
  refine ⟨?_, ?_⟩
  · -- degree `0`
    intro X C ω ηF ηG θ hXc hCS hbd hηF hηG hθ
    obtain ⟨Wθ, hWθ, hSWθ, hθeq⟩ := hθ
    -- a cut-off `θ''` of `H^#ω` near `S(X)`, with `dθ'' = H^#(dω)` there
    obtain ⟨θ'', W'', hW'', hSW'', hθ''eq, hdθ''eq⟩ :=
      Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N' 0 H ω _ hH (hScpt _ hXc)
    -- `C(θ) = C(dθ'') = ∂C(θ'')`, as `θ = H^#(dω) = dθ''` near `S(X) ⊇ spt C`
    have hCθ : C θ = C.boundary θ'' := by
      rw [GeometricCurrentOn.boundary_apply]
      refine hLOC (N + 1) (0 + 1) C θ
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 θ'') (Wθ ∩ W'')
        (hWθ.inter hW'') (fun y hy => ⟨hSWθ (hCS hy), hSW'' (hCS hy)⟩) ?_
      rintro y ⟨hyθ, hy''⟩
      exact (hθeq y hyθ).trans (hdθ''eq y hy'').symm
    -- the boundary relation for `β = θ''`; its slices give `X(η₀) = X(ηF)`, `X(η₁) = X(ηG)`
    obtain ⟨η₀, η₁, hη₀, hη₁, hbdθ''⟩ := hbd θ''
    rw [hCθ, hbdθ'', hslice 0 X ω θ'' W'' 0 F η₀ ηF (left_mem_Icc.2 zero_le_one) hW'' hSW''
      hθ''eq hH0 hDH0 hη₀ hηF, hslice 0 X ω θ'' W'' 1 G η₁ ηG (right_mem_Icc.2 zero_le_one)
      hW'' hSW'' hθ''eq hH1 hDH1 hη₁ hηG]
  · -- degree `k + 1`
    intro k X C C' ω ηF ηG θ θ' hXc hCS hC'S hbd hηF hηG hθ hθ'
    obtain ⟨Wθ, hWθ, hSWθ, hθeq⟩ := hθ
    obtain ⟨Wθ', hWθ', hSWθ', hθ'eq⟩ := hθ'
    obtain ⟨θ'', W'', hW'', hSW'', hθ''eq, hdθ''eq⟩ :=
      Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N' (k + 1) H ω _ hH (hScpt _ hXc)
    have hCθ : C θ = C.boundary θ'' := by
      rw [GeometricCurrentOn.boundary_apply]
      refine hLOC (N + 1) (k + 1 + 1) C θ
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) θ'') (Wθ ∩ W'')
        (hWθ.inter hW'') (fun y hy => ⟨hSWθ (hCS hy), hSW'' (hCS hy)⟩) ?_
      rintro y ⟨hyθ, hy''⟩
      exact (hθeq y hyθ).trans (hdθ''eq y hy'').symm
    -- `C'(θ'') = C'(θ')`, as both are `H^#ω` near `S(X) ⊇ spt C'`
    have hC'θ : C' θ'' = C' θ' := by
      refine hLOC (N + 1) (k + 1) C' θ'' θ' (W'' ∩ Wθ') (hW''.inter hWθ')
        (fun y hy => ⟨hSW'' (hC'S hy), hSWθ' (hC'S hy)⟩) ?_
      rintro y ⟨hy'', hyθ'⟩
      exact (hθ''eq y hy'').trans (hθ'eq y hyθ').symm
    obtain ⟨η₀, η₁, hη₀, hη₁, hbdθ''⟩ := hbd θ''
    rw [hCθ, hbdθ'', ← hC'θ, hslice (k + 1) X ω θ'' W'' 0 F η₀ ηF (left_mem_Icc.2 zero_le_one)
      hW'' hSW'' hθ''eq hH0 hDH0 hη₀ hηF, hslice (k + 1) X ω θ'' W'' 1 G η₁ ηG
      (right_mem_Icc.2 zero_le_one) hW'' hSW'' hθ''eq hH1 hDH1 hη₁ hηG]
    ring
/-- **Mass bound for the affine homotopy current** (Simon Ch. 6, 2.25–2.27, p. 140).  Let
`H(t, x) = F(x) + t(G(x) − F(x))` be the affine homotopy (2.26) of the `C^∞` maps `F, G`, and let
`C ∈ 𝒟_{k+1}(ℝ^{N+1})` be given by `C(ω) = ∫₀¹ X(η_t) dt`, `η_t(x)(v) = ω(t, x)(e₀, Jv)`.  If
`‖DF‖, ‖DG‖ ≤ Λ` and `|F − G| ≤ δ` on `spt X`, `|β| ≤ b` and `θ = H^#β` on `[0,1] × spt X`, then
`|C(θ)| ≤ δ Λᵏ b M(X)` (the estimate behind 2.27).  Indeed
`η_t(x) = (β(H(t, x)) ⌞ (G x − F x)) ∘ ((1 − t) DF(x) + t DG(x))`, so (L1) and (L2) give
`|η_t(x)| ≤ Λᵏ δ b` on `spt X`; the toolkit bound `|X(ψ)| ≤ c M(X)` is then integrated over
`t ∈ [0,1]`. -/
theorem Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (Λ δ b : ℝ) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (β : TestFormOn (univ : Set (Euclid N')) (k + 1)) (θ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (⊤ : ℕ∞) H → (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → X.mass < ∞ → (∀ x ∈ X.support, ‖fderiv ℝ F x‖ ≤ Λ ∧ ‖fderiv ℝ G x‖ ≤ Λ) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (∀ y, covectorEuclideanNorm ((β : DifferentialForm (Euclid N') (k + 1)) y) ≤ b) → (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support, (θ : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((β : DifferentialForm (Euclid N') (k + 1)) (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))).compContinuousLinearMap (fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = ∫ t in (0 : ℝ)..1, X (η t)) → |C θ| ≤ δ * Λ ^ k * b * X.mass.toReal := by
  intro hVO hREP hL N N' k Λ δ b F G H X C β θ hF hG hH hHdef hXmass hΛ hδ hb hθ hC
  obtain ⟨hL1, hL2⟩ := hL
  -- (A0): `|X(ψ)| ≤ c·M(X)` whenever `|ψ| ≤ c` on `spt X`
  have hA0 := (Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP).1
  -- step 1: `C(θ) = ∫₀¹ X(η_t) dt` with `η_t(x)(v) = θ(ι(t,x))(e₀, Jv)`
  obtain ⟨η, hη, hCθ⟩ := hC θ
  -- steps 2–4: `|η_t(x)| ≤ Λ^k·δ·b` for `t ∈ [0,1]` and `x ∈ spt X`
  have hpt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support,
      covectorEuclideanNorm ((η t : DifferentialForm (Euclid N) k) x) ≤ Λ ^ k * δ * b := by
    intro t ht x hx
    -- step 2: `DH(e₀) = G x - F x` and `DH(Jv) = A v`, `A = DF(x) + t•(DG(x) - DF(x))`
    obtain ⟨he₀, hJ, -⟩ := Submission.dimred_mbl_dt_lpo_affine_homotopy.2 N N' F G H t x
      (hF.differentiable (by simp) x) (hG.differentiable (by simp) x)
      (hH.differentiable (by simp) _) hHdef
    -- step 3: `η_t(x) = ((β(H y)).curryLeft (G x - F x)).compContinuousLinearMap A`
    have hrep : (η t : DifferentialForm (Euclid N) k) x =
        (((β : DifferentialForm (Euclid N') (k + 1))
          (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))).curryLeft
            (G x - F x)).compContinuousLinearMap
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
      ext v
      have hJv : (fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∘
          fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) =
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) ∘ v := by
        funext i
        exact hJ (v i)
      rw [hη, hθ t ht x hx, ContinuousAlternatingMap.compContinuousLinearMap_apply, Fin.comp_cons,
        he₀, hJv]
      rfl
    -- step 4: `‖A‖ ≤ Λ`, as `A = (1 - t)•DF(x) + t•DG(x)` lies in the convex ball `‖·‖ ≤ Λ`;
    -- `‖G x - F x‖ ≤ δ` and `|β(H y)| ≤ b`; then (L1) and (L2)
    have hA : ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ ≤ Λ :=
      mem_closedBall_zero_iff.mp
        ((convex_closedBall (0 : Euclid N →L[ℝ] Euclid N') Λ).add_smul_sub_mem
          (mem_closedBall_zero_iff.mpr (hΛ x hx).1) (mem_closedBall_zero_iff.mpr (hΛ x hx).2) ht)
    have hu : ‖G x - F x‖ ≤ δ := by
      rw [← dist_eq_norm, dist_comm]
      exact hδ x hx
    have hAk : ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ ^ k ≤ Λ ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hA k
    rw [hrep]
    refine (hL1 _ _ _ _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (hL2 _ _ _ _) (pow_nonneg (norm_nonneg _) k)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul hAk (mul_le_mul hu (hb _) (covectorEuclideanNorm_nonneg _)
      ((norm_nonneg _).trans hu)) (mul_nonneg (norm_nonneg _) (covectorEuclideanNorm_nonneg _))
      ((pow_nonneg (norm_nonneg _) k).trans hAk)
  -- step 5: (A0) for each `t ∈ [0,1]`
  have hXt : ∀ t ∈ Icc (0 : ℝ) 1, |X (η t)| ≤ Λ ^ k * δ * b * X.mass.toReal :=
    fun t ht => hA0 N k X (η t) _ hXmass (hpt t ht)
  -- step 6: the interval-integral bound on `Ι 0 1 = Ioc 0 1 ⊆ Icc 0 1`
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t => X (η t)) (C := Λ ^ k * δ * b * X.mass.toReal) fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      rw [Real.norm_eq_abs]
      exact hXt t (Ioc_subset_Icc_self ht)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  rw [hCθ]
  calc |∫ t in (0 : ℝ)..1, X (η t)| ≤ Λ ^ k * δ * b * X.mass.toReal := hint
    _ = δ * Λ ^ k * b * X.mass.toReal := by ring

/-- **Comparison of two smooth push-forwards of a normal current** (Simon 6.2.25–6.2.27, the
estimate in the proof of 6.2.29).  If `F`, `G` are `C^∞` with `‖DF‖, ‖DG‖ ≤ Λ` and
`|F − G| ≤ δ` on `spt X`, and `|ω| ≤ a`, `|dω| ≤ b`, then
`|G_#X(ω) − F_#X(ω)| ≤ δ (Λᵏ M(X) b + Λᵏ⁻¹ M(∂X) a)`.  For the affine homotopy `H` from `F`
to `G`, the homotopy formula 2.25 reads `X(ηG) − X(ηF) = cyl(X)(H^#dω) + cyl(∂X)(H^#ω)` (no
second term if `k = 0`), and 2.27 bounds the two cylinder terms by `δΛᵏbM(X)` and
`δΛᵏ⁻¹aM(∂X)`. -/
theorem Submission.dimred_mbl_dt_lpo_cauchy_estimate : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass ≤ X.mass ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N 0 X).boundary ω = X η₁ - X η₀) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N (k + 1) X).boundary ω = X η₁ - X η₀ - cyl N k X.boundary ω) → ∀ (N N' k : ℕ) (Λ δ a b : ℝ) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηF ηG : TestFormOn (univ : Set (Euclid N)) k), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ‖fderiv ℝ F x‖ ≤ Λ ∧ ‖fderiv ℝ G x‖ ≤ Λ) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) y) ≤ a) → (∀ y, covectorEuclideanNorm (exteriorDerivative (ω : DifferentialForm (Euclid N') k) y) ≤ b) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → |X ηG - X ηF| ≤ δ * (Λ ^ k * X.mass.toReal * b + Λ ^ (k - 1) * (boundaryMassOn X univ).toReal * a) := by
  intro hVO hREP hcov cyl hC1 hC3 hC4 hC5 N N' k Λ δ a b F G X ω ηF ηG hF hG hXc hXm hXb hDFG
    hdist ha hb hηF hηG
  -- the affine homotopy `H(ι(t, x)) = F(x) + t • (G(x) − F(x))` (sibling `affine_homotopy` (i))
  obtain ⟨H, hH, hHform⟩ := Submission.dimred_mbl_dt_lpo_affine_homotopy.1 N N' F G hF hG
  -- `S(X) = ι '' ([0, 1] × spt X)` is compact
  have hS : IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
      y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
    have hι : Continuous fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1)) := by
      fun_prop
    convert ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod hXc).image hι using 1
    ext y
    constructor
    · rintro ⟨t, ht, x, hx, rfl⟩
      exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨t, ht, x, hx, rfl⟩
  -- (C1) for `X`: `spt cyl(X) ⊆ S(X)`
  obtain ⟨-, -, -, hCX⟩ := hC1 N k X hXc hXm hXb
  cases k with
  | zero =>
    -- `θ = H^#(dω)` on an open `W ⊇ S(X)` (sibling `cutoff`)
    obtain ⟨θ, W, hW, hSW, hθ, -⟩ := Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N'
      (0 + 1) H (exteriorDerivativeTestOn univ 0 ω) _ hH hS
    -- `X(ηG) − X(ηF) = cyl(X)(θ)`, the boundary relation being (C4)
    have hid := (Submission.dimred_mbl_dt_lpo_smooth_homotopy_identity hVO hREP N N' F G H hF hG
      hH hHform).1 X (cyl N 0 X) ω ηF ηG θ hXc hCX (hC4 N X hXc hXm) hηF hηG ⟨W, hW, hSW, hθ⟩
    -- `|cyl(X)(θ)| ≤ δ Λ⁰ b M(X)`, the cylinder formula being (C3)
    have hm := Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass hVO hREP hcov N N' 0 Λ δ b F G H
      X (cyl N 0 X) (exteriorDerivativeTestOn univ 0 ω) θ hF hG hH hHform hXm hDFG hdist hb
      (fun t ht x hx => hθ _ (hSW ⟨t, ht, x, hx, rfl⟩)) (hC3 N 0 X hXc hXm hXb)
    -- in degree `0`, `boundaryMassOn X univ = 0`
    have h0 : boundaryMassOn X univ = 0 := rfl
    rw [hid, h0, ENNReal.toReal_zero]
    calc |cyl N 0 X θ| ≤ δ * Λ ^ 0 * b * X.mass.toReal := hm
      _ = δ * (Λ ^ 0 * X.mass.toReal * b + Λ ^ (0 - 1) * 0 * a) := by ring
  | succ k =>
    -- `∂X` is NC with `spt ∂X ⊆ spt X` (toolkit (NCB)), so `spt cyl(∂X) ⊆ S(∂X) ⊆ S(X)` by (C1)
    have hXb' : X.boundary.mass < ∞ := hXb
    obtain ⟨hbX, hbXc, hbXb⟩ :=
      (Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP).2.2.2.2 N k X hXc hXb'
    obtain ⟨-, -, -, hCbX⟩ := hC1 N k X.boundary hbXc hXb' hbXb
    have hCbX' : (cyl N k X.boundary).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1,
        ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      intro y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hCbX hy
      exact ⟨t, ht, x, hbX hx, rfl⟩
    -- `θ = H^#(dω)` and `θ' = H^#ω` on open sets containing `S(X)` (sibling `cutoff`)
    obtain ⟨θ, W, hW, hSW, hθ, -⟩ := Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N'
      (k + 1 + 1) H (exteriorDerivativeTestOn univ (k + 1) ω) _ hH hS
    obtain ⟨θ', W', hW', hSW', hθ', -⟩ := Submission.dimred_mbl_dt_lpo_cutoff_pullback (N + 1) N'
      (k + 1) H ω _ hH hS
    -- `X(ηG) − X(ηF) = cyl(X)(θ) + cyl(∂X)(θ')`, the boundary relation being (C5)
    have hid := (Submission.dimred_mbl_dt_lpo_smooth_homotopy_identity hVO hREP N N' F G H hF hG
      hH hHform).2 k X (cyl N (k + 1) X) (cyl N k X.boundary) ω ηF ηG θ θ' hXc hCX hCbX'
      (hC5 N k X hXc hXm hXb') hηF hηG ⟨W, hW, hSW, hθ⟩ ⟨W', hW', hSW', hθ'⟩
    -- `|cyl(X)(θ)| ≤ δ Λ^(k+1) b M(X)`, the cylinder formula being (C3) for `X`
    have hm := Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass hVO hREP hcov N N' (k + 1) Λ δ b
      F G H X (cyl N (k + 1) X) (exteriorDerivativeTestOn univ (k + 1) ω) θ hF hG hH hHform hXm
      hDFG hdist hb (fun t ht x hx => hθ _ (hSW ⟨t, ht, x, hx, rfl⟩))
      (hC3 N (k + 1) X hXc hXm hXb)
    -- `|cyl(∂X)(θ')| ≤ δ Λ^k a M(∂X)`, the cylinder formula being (C3) for `∂X`
    have hm' := Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass hVO hREP hcov N N' k Λ δ a F G H
      X.boundary (cyl N k X.boundary) ω θ' hF hG hH hHform hXb' (fun x hx => hDFG x (hbX hx))
      (fun x hx => hdist x (hbX hx)) ha (fun t ht x hx => hθ' _ (hSW' ⟨t, ht, x, hbX hx, rfl⟩))
      (hC3 N k X.boundary hbXc hXb' hbXb)
    -- triangle inequality, with `k + 1 - 1 = k` and `boundaryMassOn X univ = M(∂X)`
    have hbm : boundaryMassOn X univ = X.boundary.mass := rfl
    rw [hid, Nat.add_sub_cancel, hbm]
    calc |cyl N (k + 1) X θ + cyl N k X.boundary θ'|
        ≤ |cyl N (k + 1) X θ| + |cyl N k X.boundary θ'| := abs_add_le _ _
      _ ≤ δ * Λ ^ (k + 1) * b * X.mass.toReal + δ * Λ ^ k * a * X.boundary.mass.toReal :=
        add_le_add hm hm'
      _ = δ * (Λ ^ (k + 1) * X.mass.toReal * b + Λ ^ k * X.boundary.mass.toReal * a) := by ring
/-- **Lipschitz homotopy formula and homotopy mass bound** (Simon 6.2.24–6.2.25 for Lipschitz maps,
as used in the deformation theorem 6.4.1).  For `Λ`-Lipschitz `F, G : ℝᴺ → ℝᴺ'` and an
`L`-Lipschitz `H` which is the affine homotopy `H(t, x) = F x + t (G x − F x)` on `[0, 1] × spt X`,
the push-forward `lpush` characterized by smooth approximation satisfies
`G#X − F#X = ∂ H#(cyl X)` in degree `0`, `G#X − F#X − H#(cyl ∂X) = ∂ H#(cyl X)` in degree `k + 1`,
and `M(H#(cyl X)) ≤ δ (2Λ)ᵏ M(X)` when `dist(F, G) ≤ δ` on `spt X`.  Mollify `F, G` to `Fⱼ, Gⱼ`,
take the smooth affine homotopies `Hⱼ` (which converge to `H` uniformly on `[0, 1] × spt X` with
bounded derivatives), apply the smooth homotopy identity and mass bound to cut-off pull-backs, and
pass to the limit with the characterization of `lpush`. -/
theorem Submission.dimred_mbl_dt_lpo_lipschitz_homotopy : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass ≤ X.mass ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N 0 X).boundary ω = X η₁ - X η₀) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N (k + 1) X).boundary ω = X η₁ - X η₀ - cyl N k X.boundary ω) → (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP hL lpush cyl hCHAR hC1 hC3 hC4 hC5
  obtain ⟨-, hMB, -, -, hNCB⟩ := Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP
  obtain ⟨hAH, hAHd⟩ := Submission.dimred_mbl_dt_lpo_affine_homotopy
  have hSI := Submission.dimred_mbl_dt_lpo_smooth_homotopy_identity hVO hREP
  have hSM := Submission.dimred_mbl_dt_lpo_smooth_homotopy_mass hVO hREP hL
  have hcut := Submission.dimred_mbl_dt_lpo_cutoff_pullback
  have hsub : ∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n) (ω : TestFormOn U n),
      (S - T) ω = S ω - T ω := fun _ _ _ _ _ _ => rfl
  -- `S(K) = {ι(t, x) : t ∈ [0, 1], x ∈ K}` is compact for compact `K`.
  have hScpt : ∀ (N : ℕ) (K : Set (Euclid N)), IsCompact K →
      IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
    intro N K hK
    have hc : Continuous (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) := by
      fun_prop
    convert (isCompact_Icc.prod hK).image hc using 1
    ext y
    constructor
    · rintro ⟨t, ht, x, hx, rfl⟩
      exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
      exact ⟨t, ht, x, hx, rfl⟩
  -- Steps 0–0.2: mollified maps `Fⱼ, Gⱼ`, smooth affine homotopies `Hⱼ`, uniform convergence and
  -- derivative bounds.
  have key : ∀ (N N' : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N')
      (K : Set (Euclid N)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact K →
      (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1,
        H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) →
      ∃ (Fs Gs : ℕ → Euclid N → Euclid N') (Hs : ℕ → Euclid (N + 1) → Euclid N') (Λ' : ℝ),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Gs j)) ∧
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Hs j)) ∧
        (∀ j (t : ℝ) (x : Euclid N),
          Hs j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = Fs j x + t • (Gs j x - Fs j x)) ∧
        (∀ j x, ‖fderiv ℝ (Fs j) x‖ ≤ Λ) ∧ (∀ j x, ‖fderiv ℝ (Gs j) x‖ ≤ Λ) ∧
        (∀ (j : ℕ) x, dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) ∧
        (∀ (j : ℕ) x, dist (Gs j x) (G x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) ∧
        TendstoUniformlyOn Fs F atTop K ∧ TendstoUniformlyOn Gs G atTop K ∧
        TendstoUniformlyOn Hs H atTop {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
          y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} ∧
        ∀ j, ∀ y ∈ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
          y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}, ‖fderiv ℝ (Hs j) y‖ ≤ Λ' := by
    intro N N' Λ F G H K hF hG hK hHK
    obtain ⟨Fs, hFsC, hFsL, hFd⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ F hF
    obtain ⟨Gs, hGsC, hGsL, hGd⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ G hG
    choose Hs hHsC hHsid using fun j => hAH N N' (Fs j) (Gs j) (hFsC j) (hGsC j)
    obtain ⟨D₀, hD₀⟩ :=
      hK.exists_bound_of_continuousOn (hG.continuous.sub hF.continuous).continuousOn
    have hFsD : ∀ j x, ‖fderiv ℝ (Fs j) x‖ ≤ Λ := fun j _ => norm_fderiv_le_of_lipschitz ℝ (hFsL j)
    have hGsD : ∀ j x, ‖fderiv ℝ (Gs j) x‖ ≤ Λ := fun j _ => norm_fderiv_le_of_lipschitz ℝ (hGsL j)
    have hdiv : ∀ j : ℕ, (Λ : ℝ) / ((j : ℝ) + 1) ≤ Λ := fun j =>
      div_le_self Λ.coe_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg j))
    have h0 : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ : ℝ)
    refine ⟨Fs, Gs, Hs, D₀ + 5 * (Λ : ℝ), hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, hFd, hGd,
      ?_, ?_, ?_, ?_⟩
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj x _
      rw [dist_comm]
      exact (hFd j x).trans_lt hj
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj x _
      rw [dist_comm]
      exact (hGd j x).trans_lt hj
    · -- Step 0.1: `‖Hⱼ − H‖ ≤ Λ/(j+1)` on `S(K)`.
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj
      rintro y ⟨t, ht, x, hx, rfl⟩
      rw [hHsid j t x, hHK x hx t ht, dist_eq_norm]
      have e : F x + t • (G x - F x) - (Fs j x + t • (Gs j x - Fs j x)) =
          (1 - t) • (F x - Fs j x) + t • (G x - Gs j x) := by
        simp only [sub_smul, one_smul, smul_sub]
        abel
      have h1 : ‖F x - Fs j x‖ ≤ Λ / (j + 1) := by
        rw [← dist_eq_norm, dist_comm]
        exact hFd j x
      have h2 : ‖G x - Gs j x‖ ≤ Λ / (j + 1) := by
        rw [← dist_eq_norm, dist_comm]
        exact hGd j x
      rw [e]
      calc ‖(1 - t) • (F x - Fs j x) + t • (G x - Gs j x)‖
          ≤ ‖(1 - t) • (F x - Fs j x)‖ + ‖t • (G x - Gs j x)‖ := norm_add_le _ _
        _ = (1 - t) * ‖F x - Fs j x‖ + t * ‖G x - Gs j x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht.2),
            Real.norm_of_nonneg ht.1]
        _ ≤ (1 - t) * (Λ / (j + 1)) + t * (Λ / (j + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht.2))
            (mul_le_mul_of_nonneg_left h2 ht.1)
        _ = Λ / (j + 1) := by ring
        _ < ε := hj
    · -- Step 0.2: `‖DHⱼ‖ ≤ D₀ + 5Λ` on `S(K)`.
      intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      have hd := (hAHd N N' (Fs j) (Gs j) (Hs j) t x ((hFsC j).differentiable (by simp) x)
        ((hGsC j).differentiable (by simp) x) ((hHsC j).differentiable (by simp) _) (hHsid j)).2.2
      have a1 : ‖Gs j x - G x‖ ≤ Λ := by
        rw [← dist_eq_norm]
        exact (hGd j x).trans (hdiv j)
      have a2 : ‖F x - Fs j x‖ ≤ Λ := by
        rw [← dist_eq_norm, dist_comm]
        exact (hFd j x).trans (hdiv j)
      have a3 : ‖G x - F x‖ ≤ D₀ := hD₀ x hx
      have b1 : ‖Gs j x - Fs j x‖ ≤ 2 * Λ + D₀ := by
        have e : Gs j x - Fs j x = (Gs j x - G x) + (G x - F x) + (F x - Fs j x) := by abel
        rw [e]
        have n1 := norm_add_le (Gs j x - G x + (G x - F x)) (F x - Fs j x)
        have n2 := norm_add_le (Gs j x - G x) (G x - F x)
        linarith
      have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have b2 : ‖fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)‖ ≤ 3 * Λ := by
        have n1 := norm_add_le (fderiv ℝ (Fs j) x) (t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))
        have n2 : ‖t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)‖ ≤ 1 * (Λ + Λ) := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul ht1 ((norm_sub_le _ _).trans (add_le_add (hGsD j x) (hFsD j x)))
            (norm_nonneg _) zero_le_one
        have n3 := hFsD j x
        linarith
      linarith
  refine ⟨?_, ?_, ?_⟩
  · -- (10): degree `0`.
    intro N N' Λ L F G H X hF hG hH hXc hXm hHX
    have hXb : boundaryMassOn X univ < ∞ := by simp [boundaryMassOn]
    obtain ⟨Fs, Gs, Hs, Λ', hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, -, -, hFU, hGU, hHU, hHsD⟩ :=
      key N N' Λ F G H X.support hF hG hXc hHX
    obtain ⟨hcylc, hcylm, hcylb, hcylS⟩ := hC1 N 0 X hXc hXm hXb
    apply GeometricCurrentOn.ext
    intro ω
    rw [hsub, GeometricCurrentOn.boundary_apply]
    choose ηF WF hWFo hWFK hηF _ using
      fun j => hcut N N' 0 (Fs j) ω X.support (hFsC j) hXc
    choose ηG WG hWGo hWGK hηG _ using
      fun j => hcut N N' 0 (Gs j) ω X.support (hGsC j) hXc
    choose θ WH hWHo hWHK hθ _ using
      fun j => hcut (N + 1) N' (0 + 1) (Hs j) (exteriorDerivativeTestOn univ 0 ω) _ (hHsC j)
        (hScpt N X.support hXc)
    have lF : Tendsto (fun j => X (ηF j)) atTop (𝓝 (lpush N N' 0 F X ω)) :=
      hCHAR N N' 0 Λ Λ F Fs X ω ηF hF hXc hXm hXb hFsC (fun j x _ => hFsD j x) hFU
        (fun j => ⟨WF j, hWFo j, hWFK j, hηF j⟩)
    have lG : Tendsto (fun j => X (ηG j)) atTop (𝓝 (lpush N N' 0 G X ω)) :=
      hCHAR N N' 0 Λ Λ G Gs X ω ηG hG hXc hXm hXb hGsC (fun j x _ => hGsD j x) hGU
        (fun j => ⟨WG j, hWGo j, hWGK j, hηG j⟩)
    have lH : Tendsto (fun j => cyl N 0 X (θ j)) atTop
        (𝓝 (lpush (N + 1) N' (0 + 1) H (cyl N 0 X) (exteriorDerivativeTestOn univ 0 ω))) :=
      hCHAR (N + 1) N' (0 + 1) L Λ' H Hs (cyl N 0 X) (exteriorDerivativeTestOn univ 0 ω) θ hH
        hcylc (hcylm.trans_lt hXm) hcylb hHsC (fun j y hy => hHsD j y (hcylS hy))
        (hHU.mono hcylS) (fun j => ⟨WH j, hWHo j, hcylS.trans (hWHK j), hθ j⟩)
    have hid : ∀ j, X (ηG j) - X (ηF j) = cyl N 0 X (θ j) := fun j =>
      (hSI N N' (Fs j) (Gs j) (Hs j) (hFsC j) (hGsC j) (hHsC j) (hHsid j)).1 X (cyl N 0 X) ω
        (ηF j) (ηG j) (θ j) hXc hcylS (hC4 N X hXc hXm) ⟨WF j, hWFo j, hWFK j, hηF j⟩
        ⟨WG j, hWGo j, hWGK j, hηG j⟩ ⟨WH j, hWHo j, hWHK j, hθ j⟩
    exact tendsto_nhds_unique (lG.sub lF) (lH.congr fun j => (hid j).symm)
  · -- (11): degree `k + 1`.
    intro N N' k Λ L F G H X hF hG hH hXc hXm hXbm hHX
    have hXb : boundaryMassOn X univ < ∞ := hXbm
    obtain ⟨hbS, hbc, hbb⟩ := hNCB N k X hXc hXbm
    obtain ⟨Fs, Gs, Hs, Λ', hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, -, -, hFU, hGU, hHU, hHsD⟩ :=
      key N N' Λ F G H X.support hF hG hXc hHX
    obtain ⟨hcylc, hcylm, hcylb, hcylS⟩ := hC1 N (k + 1) X hXc hXm hXb
    obtain ⟨hcbc, hcbm, hcbb, hcbS⟩ := hC1 N k X.boundary hbc hXbm hbb
    have hcbS' : (cyl N k X.boundary).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1,
        ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      intro y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hcbS hy
      exact ⟨t, ht, x, hbS hx, rfl⟩
    apply GeometricCurrentOn.ext
    intro ω
    rw [hsub, hsub, GeometricCurrentOn.boundary_apply]
    choose ηF WF hWFo hWFK hηF _ using
      fun j => hcut N N' (k + 1) (Fs j) ω X.support (hFsC j) hXc
    choose ηG WG hWGo hWGK hηG _ using
      fun j => hcut N N' (k + 1) (Gs j) ω X.support (hGsC j) hXc
    choose θ WH hWHo hWHK hθ _ using
      fun j => hcut (N + 1) N' (k + 1 + 1) (Hs j) (exteriorDerivativeTestOn univ (k + 1) ω) _
        (hHsC j) (hScpt N X.support hXc)
    choose θ' WH' hWH'o hWH'K hθ' _ using
      fun j => hcut (N + 1) N' (k + 1) (Hs j) ω _ (hHsC j) (hScpt N X.support hXc)
    have lF : Tendsto (fun j => X (ηF j)) atTop (𝓝 (lpush N N' (k + 1) F X ω)) :=
      hCHAR N N' (k + 1) Λ Λ F Fs X ω ηF hF hXc hXm hXb hFsC (fun j x _ => hFsD j x) hFU
        (fun j => ⟨WF j, hWFo j, hWFK j, hηF j⟩)
    have lG : Tendsto (fun j => X (ηG j)) atTop (𝓝 (lpush N N' (k + 1) G X ω)) :=
      hCHAR N N' (k + 1) Λ Λ G Gs X ω ηG hG hXc hXm hXb hGsC (fun j x _ => hGsD j x) hGU
        (fun j => ⟨WG j, hWGo j, hWGK j, hηG j⟩)
    have lH : Tendsto (fun j => cyl N (k + 1) X (θ j)) atTop
        (𝓝 (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)
          (exteriorDerivativeTestOn univ (k + 1) ω))) :=
      hCHAR (N + 1) N' (k + 1 + 1) L Λ' H Hs (cyl N (k + 1) X)
        (exteriorDerivativeTestOn univ (k + 1) ω) θ hH hcylc (hcylm.trans_lt hXm) hcylb hHsC
        (fun j y hy => hHsD j y (hcylS hy)) (hHU.mono hcylS)
        (fun j => ⟨WH j, hWHo j, hcylS.trans (hWHK j), hθ j⟩)
    have lH' : Tendsto (fun j => cyl N k X.boundary (θ' j)) atTop
        (𝓝 (lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) ω)) :=
      hCHAR (N + 1) N' (k + 1) L Λ' H Hs (cyl N k X.boundary) ω θ' hH hcbc
        (hcbm.trans_lt hXbm) hcbb hHsC (fun j y hy => hHsD j y (hcbS' hy)) (hHU.mono hcbS')
        (fun j => ⟨WH' j, hWH'o j, hcbS'.trans (hWH'K j), hθ' j⟩)
    have hid : ∀ j, X (ηG j) - X (ηF j) = cyl N (k + 1) X (θ j) + cyl N k X.boundary (θ' j) :=
      fun j => (hSI N N' (Fs j) (Gs j) (Hs j) (hFsC j) (hGsC j) (hHsC j) (hHsid j)).2 k X
        (cyl N (k + 1) X) (cyl N k X.boundary) ω (ηF j) (ηG j) (θ j) (θ' j) hXc hcylS hcbS'
        (hC5 N k X hXc hXm hXbm) ⟨WF j, hWFo j, hWFK j, hηF j⟩ ⟨WG j, hWGo j, hWGK j, hηG j⟩
        ⟨WH j, hWHo j, hWHK j, hθ j⟩ ⟨WH' j, hWH'o j, hWH'K j, hθ' j⟩
    have hlim := tendsto_nhds_unique (lG.sub lF) ((lH.add lH').congr fun j => (hid j).symm)
    linarith
  · -- (12): the homotopy mass bound.
    intro N N' k Λ L F G H X δ hF hG hH hXc hXm hXb hHX hδ
    obtain ⟨Fs, Gs, Hs, Λ', hFsC, hGsC, hHsC, hHsid, hFsD, hGsD, hFd, hGd, -, -, hHU, hHsD⟩ :=
      key N N' Λ F G H X.support hF hG hXc hHX
    obtain ⟨hcylc, hcylm, hcylb, hcylS⟩ := hC1 N k X hXc hXm hXb
    have hδp : 0 ≤ max δ 0 := le_max_right δ 0
    have h0 : Tendsto (fun j : ℕ => 2 * (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (Λ : ℝ))
    have hbound : (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤
        ENNReal.ofReal (max δ 0 * (Λ : ℝ) ^ k * X.mass.toReal) := by
      apply hMB N' (k + 1)
      intro ω c hωc
      choose θ WH hWHo hWHK hθ _ using
        fun j => hcut (N + 1) N' (k + 1) (Hs j) ω _ (hHsC j) (hScpt N X.support hXc)
      have lH : Tendsto (fun j => cyl N k X (θ j)) atTop
          (𝓝 (lpush (N + 1) N' (k + 1) H (cyl N k X) ω)) :=
        hCHAR (N + 1) N' (k + 1) L Λ' H Hs (cyl N k X) ω θ hH hcylc (hcylm.trans_lt hXm) hcylb
          hHsC (fun j y hy => hHsD j y (hcylS hy)) (hHU.mono hcylS)
          (fun j => ⟨WH j, hWHo j, hcylS.trans (hWHK j), hθ j⟩)
      have hj : ∀ j : ℕ, |cyl N k X (θ j)| ≤
          (max δ 0 + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * (Λ : ℝ) ^ k * c * X.mass.toReal := by
        intro j
        refine hSM N N' k Λ (max δ 0 + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) c (Fs j) (Gs j) (Hs j) X
          (cyl N k X) ω (θ j) (hFsC j) (hGsC j) (hHsC j) (hHsid j) hXm
          (fun x _ => ⟨hFsD j x, hGsD j x⟩) ?_ hωc ?_ (hC3 N k X hXc hXm hXb)
        · intro x hx
          have e1 := hFd j x
          have e2 := hGd j x
          have e3 := hδ x hx
          have e4 := dist_triangle4 (Fs j x) (F x) (G x) (Gs j x)
          rw [dist_comm (G x) (Gs j x)] at e4
          have e5 : 2 * (Λ : ℝ) / ((j : ℝ) + 1) = Λ / (j + 1) + Λ / (j + 1) := by ring
          have e6 := le_max_left δ 0
          linarith
        · intro t ht x hx
          exact hθ j _ (hWHK j ⟨t, ht, x, hx, rfl⟩)
      have hlim : Tendsto (fun j : ℕ =>
          (max δ 0 + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * (Λ : ℝ) ^ k * c * X.mass.toReal) atTop
          (𝓝 ((max δ 0 + 0) * (Λ : ℝ) ^ k * c * X.mass.toReal)) :=
        (((tendsto_const_nhds.add h0).mul_const _).mul_const _).mul_const _
      have hle := le_of_tendsto_of_tendsto' lH.abs hlim hj
      calc |lpush (N + 1) N' (k + 1) H (cyl N k X) ω|
          ≤ (max δ 0 + 0) * (Λ : ℝ) ^ k * c * X.mass.toReal := hle
        _ = max δ 0 * (Λ : ℝ) ^ k * X.mass.toReal * c := by ring
    have hmax : ENNReal.ofReal (max δ 0) = ENNReal.ofReal δ := by
      rcases le_total 0 δ with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    have h2 : (Λ : ℝ≥0∞) ≤ 2 * (Λ : ℝ≥0∞) := le_mul_of_one_le_left (by positivity) one_le_two
    calc (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass
        ≤ ENNReal.ofReal (max δ 0 * (Λ : ℝ) ^ k * X.mass.toReal) := hbound
      _ = ENNReal.ofReal δ * (Λ : ℝ≥0∞) ^ k * X.mass := by
        rw [ENNReal.ofReal_mul (mul_nonneg hδp (pow_nonneg Λ.coe_nonneg k)),
          ENNReal.ofReal_mul hδp, ENNReal.ofReal_toReal hXm.ne, hmax, ← NNReal.coe_pow,
          ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]
      _ ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by gcongr
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

/-- **The Lipschitz push-forward** (Simon Ch. 6, 2.29, p. 141: `f_#T(ω) = lim_σ f_{σ#}T(ω)` for
mollifications `f_σ` of a Lipschitz `f`, the limit existing by the homotopy estimate 2.27–2.28).
Fix a `Λ`-Lipschitz `F` and `X` with compact support, `M(X) < ∞` and `M(∂X) < ∞`.  Take smooth
`Λ`-Lipschitz `F_j` with `|F_j − F| ≤ Λ/(j+1)` and test forms `η°_j(ω)` equal to `F_j^#ω` near
`spt X`.  The estimate `|X(G^#ω) − X(F^#ω)| ≤ δ (Λ^k M(X) b + Λ^{k−1} M(∂X) a)` (for
`|F − G| ≤ δ` on `spt X`, `|ω| ≤ a`, `|dω| ≤ b`) makes `X(η°_j(ω))` Cauchy, with limit `L(ω)`,
and gives `X(ηs_j) → L(ω)` for every admissible `(Fs, ηs)`.  Hence `L` is linear; by (L1),
`|L ω| ≤ c Λ^k M(X)` when `|ω| ≤ c`, so `L` is a current.  `lpush N N' k F X` is this current
(for a chosen Lipschitz constant; the limit does not depend on it) when `F` is Lipschitz and `X`
is NC, and `0` otherwise. -/
theorem Submission.dimred_mbl_dt_lpo_lpush_construction : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass ≤ X.mass ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N 0 X).boundary ω = X η₁ - X η₀) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N (k + 1) X).boundary ω = X η₁ - X η₀ - cyl N k X.boundary ω) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) := by
  intro hVO hREP hL cyl hC1 hC3 hC4 hC5
  classical
  -- A0 of the toolkit (`|X ψ| ≤ c M(X)` when `|ψ| ≤ c` on `spt X`) and the estimate (E)
  have hA0 := (Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP).1
  have hE := Submission.dimred_mbl_dt_lpo_cauchy_estimate hVO hREP hL cyl hC1 hC3 hC4 hC5
  -- A2: a test form has bounded coefficient norm, `|φ(y)| ≤ C ‖φ(y)‖ ≤ C B`
  have hbdd : ∀ (P m : ℕ) (φ : DifferentialForm (Euclid P) m), IsTestForm φ →
      ∃ a : ℝ, ∀ y, covectorEuclideanNorm (φ y) ≤ a := by
    intro P m φ hφ
    obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P m).2.2.1
    obtain ⟨B, hB⟩ := (ContDiff.continuous hφ.1).bounded_above_of_compact_support hφ.2
    exact ⟨C * B, fun y => (hC _).trans (mul_le_mul_of_nonneg_left (hB y) hC0)⟩
  -- Part A: for a `Λ`-Lipschitz `F` and an NC current `X`, one current `T` with property (★)
  have partA : ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N')
      (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F →
      IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ →
      ∃ T : GeometricCurrentOn (univ : Set (Euclid N')) k, ∀ (Λ' : ℝ)
        (Fs : ℕ → Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k)
        (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') →
        TendstoUniformlyOn Fs F atTop X.support →
        (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
          (ηs j : DifferentialForm (Euclid N) k) x =
            ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x)) →
        Tendsto (fun j => X (ηs j)) atTop (𝓝 (T ω)) := by
    intro N N' k Λ F X hF hXc hXm hXb
    -- A1: mollifiers `F_j` (`‖DF_j‖ ≤ Λ`, `F_j → F` uniformly) and cut-off pull-backs `η°_j(ω)`
    obtain ⟨Fj, hFj, hFjL, hFjd⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ F hF
    have hDFj : ∀ j x, ‖fderiv ℝ (Fj j) x‖ ≤ Λ := fun j _ => norm_fderiv_le_of_lipschitz ℝ (hFjL j)
    have he : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ : ℝ)
      rw [mul_zero] at h
      exact h.congr fun j => mul_one_div _ _
    have hFjF : TendstoUniformlyOn Fj F atTop X.support := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [he.eventually (gt_mem_nhds hε)] with j hj x _
      rw [dist_comm]
      exact (hFjd j x).trans_lt hj
    have hcut : ∀ (ω : TestFormOn (univ : Set (Euclid N')) k) (j : ℕ),
        ∃ η : TestFormOn (univ : Set (Euclid N)) k, ∃ W : Set (Euclid N), IsOpen W ∧
          X.support ⊆ W ∧ ∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x =
            ((ω : DifferentialForm (Euclid N') k) (Fj j x)).compContinuousLinearMap
              (fderiv ℝ (Fj j) x) := by
      intro ω j
      obtain ⟨η, W, hW, hXW, hη, -⟩ :=
        Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fj j) ω X.support (hFj j) hXc
      exact ⟨η, W, hW, hXW, hη⟩
    choose ηo hηo using hcut
    -- A2: bounds `a_ω ≥ |ω|` and `b_ω ≥ |dω|`
    have hab : ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
        (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) y) ≤ a) ∧
        ∀ y, covectorEuclideanNorm
          (exteriorDerivative (ω : DifferentialForm (Euclid N') k) y) ≤ b := by
      intro ω
      obtain ⟨a, ha⟩ := hbdd N' k _ ω.property.1
      obtain ⟨b, hb⟩ := hbdd N' (k + 1) _ (exteriorDerivative_isTestForm ω.property.1)
      exact ⟨a, b, (covectorEuclideanNorm_nonneg _).trans (ha 0),
        (covectorEuclideanNorm_nonneg _).trans (hb 0), ha, hb⟩
    -- A3: `X(η°_j(ω))` is Cauchy, by (E) with `δ = Λ/(i+1) + Λ/(j+1)`; `L(ω)` is its limit
    have hcauchy : ∀ ω : TestFormOn (univ : Set (Euclid N')) k,
        CauchySeq (fun j => X (ηo ω j)) := by
      intro ω
      obtain ⟨a, b, ha0, hb0, ha, hb⟩ := hab ω
      set K : ℝ := (Λ : ℝ) ^ k * X.mass.toReal * b +
        (Λ : ℝ) ^ (k - 1) * (boundaryMassOn X univ).toReal * a
      have hK0 : 0 ≤ K := by positivity
      refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => 2 * ((Λ : ℝ) / ((n : ℝ) + 1)) * K)
        (fun n m M hn hm => ?_) ?_
      · have hest := hE N N' k Λ ((Λ : ℝ) / ((m : ℝ) + 1) + (Λ : ℝ) / ((n : ℝ) + 1)) a b
          (Fj m) (Fj n) X ω (ηo ω m) (ηo ω n) (hFj m) (hFj n) hXc hXm hXb
          (fun x _ => ⟨hDFj m x, hDFj n x⟩)
          (fun x _ => (dist_triangle_right _ _ (F x)).trans (add_le_add (hFjd m x) (hFjd n x)))
          ha hb (hηo ω m) (hηo ω n)
        have hmono : ∀ i, M ≤ i → (Λ : ℝ) / ((i : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
          fun i hi => div_le_div_of_nonneg_left (NNReal.coe_nonneg Λ) (by positivity)
            (by exact_mod_cast Nat.add_le_add_right hi 1)
        rw [Real.dist_eq]
        calc |X (ηo ω n) - X (ηo ω m)|
            ≤ ((Λ : ℝ) / ((m : ℝ) + 1) + (Λ : ℝ) / ((n : ℝ) + 1)) * K := hest
          _ ≤ 2 * ((Λ : ℝ) / ((M : ℝ) + 1)) * K :=
            mul_le_mul_of_nonneg_right (by linarith [hmono m hm, hmono n hn]) hK0
      · have h := (he.const_mul 2).mul_const K
        rwa [mul_zero, zero_mul] at h
    choose Lf hLf using fun ω => cauchySeq_tendsto_of_complete (hcauchy ω)
    -- A4: for every admissible `(Fs, ηs)`, `X(ηs_j) - X(η°_j(ω)) → 0`, by (E) with
    -- `δ = Λ/(j+1) + ε` and `Λ'' = max Λ Λ'`; hence `X(ηs_j) → L(ω)`
    have hstar : ∀ (Λ' : ℝ) (Fs : ℕ → Euclid N → Euclid N')
        (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') →
        TendstoUniformlyOn Fs F atTop X.support →
        (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
          (ηs j : DifferentialForm (Euclid N) k) x =
            ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
              (fderiv ℝ (Fs j) x)) →
        Tendsto (fun j => X (ηs j)) atTop (𝓝 (Lf ω)) := by
      intro Λ' Fs ω ηs hFs hDFs hFsF hηs
      obtain ⟨a, b, ha0, hb0, ha, hb⟩ := hab ω
      set Λ'' : ℝ := max (Λ : ℝ) Λ'
      have hΛ''0 : 0 ≤ Λ'' := (NNReal.coe_nonneg Λ).trans (le_max_left _ _)
      set K : ℝ := Λ'' ^ k * X.mass.toReal * b +
        Λ'' ^ (k - 1) * (boundaryMassOn X univ).toReal * a
      have hK0 : 0 ≤ K := by positivity
      have hdiff : Tendsto (fun j => X (ηs j) - X (ηo ω j)) atTop (𝓝 0) := by
        rw [Metric.tendsto_atTop]
        intro ε hε
        set ε₁ : ℝ := ε / 4 / (K + 1) with hε₁
        have hε₁0 : 0 < ε₁ := by positivity
        obtain ⟨j₁, hj₁⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hFsF ε₁ hε₁0)
        obtain ⟨j₂, hj₂⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds hε₁0))
        refine ⟨max j₁ j₂, fun j hj => ?_⟩
        have hdist : ∀ x ∈ X.support,
            dist (Fj j x) (Fs j x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) + ε₁ := fun x hx =>
          (dist_triangle _ (F x) _).trans
            (add_le_add (hFjd j x) (hj₁ j (le_of_max_le_left hj) x hx).le)
        have hest := hE N N' k Λ'' ((Λ : ℝ) / ((j : ℝ) + 1) + ε₁) a b (Fj j) (Fs j) X ω
          (ηo ω j) (ηs j) (hFj j) (hFs j) hXc hXm hXb
          (fun x hx => ⟨(hDFj j x).trans (le_max_left _ _), (hDFs j x hx).trans (le_max_right _ _)⟩)
          hdist ha hb (hηo ω j) (hηs j)
        have hj₂' := hj₂ j (le_of_max_le_right hj)
        have hε₁K : 2 * ε₁ * (K + 1) = ε / 2 := by
          rw [hε₁, mul_assoc, div_mul_cancel₀ _ (by positivity)]
          ring
        rw [Real.dist_eq, sub_zero]
        calc |X (ηs j) - X (ηo ω j)| ≤ ((Λ : ℝ) / ((j : ℝ) + 1) + ε₁) * K := hest
          _ ≤ 2 * ε₁ * (K + 1) := by
            calc ((Λ : ℝ) / ((j : ℝ) + 1) + ε₁) * K ≤ 2 * ε₁ * K :=
                  mul_le_mul_of_nonneg_right (by linarith) hK0
              _ ≤ 2 * ε₁ * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = ε / 2 := hε₁K
          _ < ε := by linarith
      have h := hdiff.add (hLf ω)
      rw [zero_add] at h
      exact h.congr fun j => sub_add_cancel _ _
    -- A5: `L` is linear, by (★) for `(F_j)` with `η°_j(ω) + η°_j(ω')`, `r • η°_j(ω)`
    have hadd : ∀ ω ω' : TestFormOn (univ : Set (Euclid N')) k, Lf (ω + ω') = Lf ω + Lf ω' := by
      intro ω ω'
      have h := hstar Λ Fj (ω + ω') (fun j => ηo ω j + ηo ω' j) hFj (fun j x _ => hDFj j x) hFjF
        fun j => by
          obtain ⟨W, hW, hXW, hη⟩ := hηo ω j
          obtain ⟨W', hW', hXW', hη'⟩ := hηo ω' j
          refine ⟨W ∩ W', hW.inter hW', subset_inter hXW hXW', fun x hx => ?_⟩
          simp only [Submodule.coe_add, Pi.add_apply, hη x hx.1, hη' x hx.2]
          ext v
          simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      refine tendsto_nhds_unique h (((hLf ω).add (hLf ω')).congr fun j => ?_)
      exact (map_add X.toCurrent _ _).symm
    have hsmul : ∀ (r : ℝ) (ω : TestFormOn (univ : Set (Euclid N')) k), Lf (r • ω) = r * Lf ω := by
      intro r ω
      have h := hstar Λ Fj (r • ω) (fun j => r • ηo ω j) hFj (fun j x _ => hDFj j x) hFjF
        fun j => by
          obtain ⟨W, hW, hXW, hη⟩ := hηo ω j
          refine ⟨W, hW, hXW, fun x hx => ?_⟩
          simp only [Submodule.coe_smul, Pi.smul_apply, hη x hx]
          ext v
          simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      refine tendsto_nhds_unique h (((hLf ω).const_mul r).congr fun j => ?_)
      exact (map_smul X.toCurrent r _).symm
    let L : TestFormOn (univ : Set (Euclid N')) k →ₗ[ℝ] ℝ :=
      { toFun := Lf
        map_add' := hadd
        map_smul' := fun r ω => hsmul r ω }
    -- A6: `|X(η°_j(ω))| ≤ Λ^k c M(X)` by (L1) and A0, so `|L ω| ≤ c (Λ^k M(X))`
    have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid N')) k) (c : ℝ), 0 < c →
        (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) y) ≤ c) →
        |L ω| ≤ c * ((Λ : ℝ) ^ k * X.mass.toReal) := by
      intro ω c hc hωc
      have hj : ∀ j, |X (ηo ω j)| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal := by
        intro j
        obtain ⟨W, -, hXW, hη⟩ := hηo ω j
        refine hA0 N k X (ηo ω j) ((Λ : ℝ) ^ k * c) hXm fun x hx => ?_
        rw [hη x (hXW hx)]
        exact (hL.1 N N' k _ _).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDFj j x) k)
          (hωc _) (covectorEuclideanNorm_nonneg _) (by positivity))
      calc |L ω| = |Lf ω| := rfl
        _ ≤ (Λ : ℝ) ^ k * c * X.mass.toReal := le_of_tendsto' (hLf ω).abs hj
        _ = c * ((Λ : ℝ) ^ k * X.mass.toReal) := by ring
    -- A7: `L` is a current `T`, and `T` has property (★)
    obtain ⟨T, hT⟩ := Submission.cmc_fc_sc_current_of_coeff_bound N' k univ L
      ((Λ : ℝ) ^ k * X.mass.toReal) hbound
    refine ⟨T, fun Λ' Fs ω ηs hFs hDFs hFsF hηs => ?_⟩
    rw [hT ω]
    exact hstar Λ' Fs ω ηs hFs hDFs hFsF hηs
  -- Part B: `lpush N N' k F X` is the current of Part A when `F` is Lipschitz and `X` is NC
  -- (for a chosen Lipschitz constant; (★) does not involve it), and `0` otherwise
  refine ⟨fun N N' k F X =>
    if h : (∃ Λ : NNReal, LipschitzWith Λ F) ∧ IsCompact X.support ∧ X.mass < ∞ ∧
        boundaryMassOn X univ < ∞ then
      (partA N N' k h.1.choose F X h.1.choose_spec h.2.1 h.2.2.1 h.2.2.2).choose
    else 0, ?_⟩
  intro N N' k Λ Λ' F Fs X ω ηs hF hXc hXm hXb hFs hDFs hFsF hηs
  have h : (∃ Λ : NNReal, LipschitzWith Λ F) ∧ IsCompact X.support ∧ X.mass < ∞ ∧
      boundaryMassOn X univ < ∞ := ⟨⟨Λ, hF⟩, hXc, hXm, hXb⟩
  simp only [dite_eq_left h]
  exact (partA N N' k h.1.choose F X h.1.choose_spec h.2.1 h.2.2.1 h.2.2.2).choose_spec
    Λ' Fs ω ηs hFs hDFs hFsF hηs

/-- **Properties of the Lipschitz push-forward** `F_#` (Simon 6.2.23–2.29), derived from its
characterization `CHAR` (`X(ηⱼ) → F_# X(ω)` along smooth `Fⱼ → F` with `‖DFⱼ‖` bounded on `spt X`
and test forms `ηⱼ = Fⱼ^#ω` near `spt X`): (1) `id_# X = X`; (2) `F_#(X − Y) = F_# X − F_# Y`;
(3) `F_# X` only depends on `F` on `spt X`; (4) `M(F_# X) ≤ Λᵏ M(X)`, `spt F_# X ⊆ F(spt X)`;
(5) `∂F_# X = F_# ∂X`; (6) `F_# X(ω)` is such a limit for smooth `Λ`-Lipschitz `Fⱼ → F`.  Each
follows from `CHAR` along the standard approximants (mollified `Fⱼ`, cut-off pull-backs `ηⱼ`)
and uniqueness of limits. -/
theorem Submission.dimred_mbl_dt_lpo_lpush_properties : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) := by
  intro hVO hREP hL lpush hCHAR
  obtain ⟨hA0, hMB, hLOC, hNCD, hNCB⟩ := Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP
  obtain ⟨hL1, -⟩ := hL
  -- standard approximants: the mollified `Fⱼ` are smooth and `Λ`-Lipschitz (so `‖DFⱼ‖ ≤ Λ`), and
  -- `Λ/(j+1)`-close to `F`, hence eventually `ε`-close to `F` and uniformly convergent to it
  have hstd : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F →
      ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧
        (∀ j, LipschitzWith Λ (Fs j)) ∧ (∀ j x, ‖fderiv ℝ (Fs j) x‖ ≤ Λ) ∧
        (∀ ε > 0, ∀ᶠ j in atTop, ∀ x, dist (Fs j x) (F x) < ε) ∧ TendstoUniformly Fs F atTop := by
    intro N N' Λ F hF
    obtain ⟨Fs, hsm, hlip, hdist⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ F hF
    have h0 : Tendsto (fun j : ℕ => (Λ : ℝ) * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Λ : ℝ)
    have hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∀ x, dist (Fs j x) (F x) < ε := fun ε hε =>
      ((tendsto_order.1 h0).2 ε hε).mono fun j hj x =>
        ((hdist j x).trans_eq (mul_one_div _ _).symm).trans_lt hj
    exact ⟨Fs, hsm, hlip, fun j _ => norm_fderiv_le_of_lipschitz ℝ (hlip j), hclose,
      Metric.tendstoUniformly_iff.2 fun ε hε => (hclose ε hε).mono fun j hj x => by
        rw [dist_comm]
        exact hj x⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `CHAR` for `F = Fⱼ = id` and `ηⱼ = ω`: the constant sequence `X(ω)` tends to `id_# X(ω)`
    intro N k X hXc hXm hXb
    ext ω
    refine tendsto_nhds_unique (hCHAR N N k 1 1 (fun x => x) (fun _ x => x) X ω (fun _ => ω)
      LipschitzWith.id hXc hXm hXb (fun _ => contDiff_id) (fun _ x _ => ?_)
      (fun u hu => Eventually.of_forall fun _ x _ => refl_mem_uniformity hu)
      fun _ => ⟨univ, isOpen_univ, subset_univ _, fun x _ => ?_⟩) tendsto_const_nhds
    · rw [fderiv_fun_id]
      exact ContinuousLinearMap.norm_id_le
    · rw [fderiv_fun_id]
      ext v
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  · -- (2) shared approximants for `K = spt X ∪ spt Y ⊇ spt(X − Y)`; `(X − Y)(ηⱼ) = X(ηⱼ) − Y(ηⱼ)`
    intro N N' k Λ F X Y hF hXc hXm hXb hYc hYm hYb
    obtain ⟨hXYs, hXYc, hXYm, hXYb⟩ := hNCD N k X Y hXc hXm hXb hYc hYm hYb
    obtain ⟨Fs, hsm, -, hD, -, hU⟩ := hstd N N' Λ F hF
    ext ω
    choose η W hWo hKW hη _ using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) (hXc.union hYc)
    have hX := hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, subset_union_left.trans (hKW j), hη j⟩
    have hY := hCHAR N N' k Λ Λ F Fs Y ω η hF hYc hYm hYb hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, subset_union_right.trans (hKW j), hη j⟩
    have hXY : Tendsto (fun j => X (η j) - Y (η j)) atTop (𝓝 (lpush N N' k F (X - Y) ω)) :=
      hCHAR N N' k Λ Λ F Fs (X - Y) ω η hF hXYc hXYm hXYb hsm (fun j x _ => hD j x)
        hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hXYs.trans (hKW j), hη j⟩
    exact tendsto_nhds_unique hXY (hX.sub hY)
  · -- (3) `Fⱼ → F = G` uniformly on `spt X`: `CHAR` for `F` and for `G` share the sequence `X(ηⱼ)`
    intro N N' k Λ F G X hF hG hXc hXm hXb hFG
    obtain ⟨Fs, hsm, -, hD, -, hU⟩ := hstd N N' Λ F hF
    ext ω
    choose η W hWo hKW hη _ using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
    exact tendsto_nhds_unique
      (hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm (fun j x _ => hD j x)
        hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩)
      (hCHAR N N' k Λ Λ G Fs X ω η hG hXc hXm hXb hsm (fun j x _ => hD j x)
        (hU.tendstoUniformlyOn.congr_right hFG) fun j => ⟨W j, hWo j, hKW j, hη j⟩)
  · intro N N' k Λ F X hF hXc hXm hXb
    obtain ⟨Fs, hsm, -, hD, hclose, hU⟩ := hstd N N' Λ F hF
    refine ⟨?_, ?_⟩
    · -- (4) mass: on `spt X`, `|ηⱼ| ≤ ‖DFⱼ‖ᵏ|ω ∘ Fⱼ| ≤ Λᵏc`, so `|X(ηⱼ)| ≤ ΛᵏcM(X)`; take limits
      refine (hMB N' k (lpush N N' k F X) ((Λ : ℝ) ^ k * X.mass.toReal)
        fun ω c hc => ?_).trans_eq ?_
      · choose η W hWo hKW hη _ using fun j =>
          Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
        refine le_of_tendsto' (hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm
          (fun j x _ => hD j x) hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩).abs
          fun j => (hA0 N k X (η j) ((Λ : ℝ) ^ k * c) hXm fun x hx => ?_).trans_eq (by ring)
        rw [hη j x (hKW j hx)]
        exact (hL1 N N' k _ _).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hD j x) k)
          (hc _) (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.coe_nonneg k))
      · rw [ENNReal.ofReal_mul (pow_nonneg Λ.coe_nonneg k), ENNReal.ofReal_pow Λ.coe_nonneg,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXm.ne]
    · -- (4) support: if `spt ω` misses the compact `F(spt X)`, then eventually `Fⱼ(spt X)` misses
      -- `spt ω`, so `ηⱼ = 0` near `spt X` (locality) and `F_# X(ω) = lim X(ηⱼ) = 0`
      have hEc : IsCompact (F '' X.support) := hXc.image hF.continuous
      refine (Submission.cmcsd_support_calculus N' k).1 _ _ hEc.isClosed fun ω hω => ?_
      obtain ⟨δ, hδ, hδE⟩ := hEc.exists_thickening_subset_open
        (isClosed_tsupport (ω : DifferentialForm (Euclid N') k)).isOpen_compl
        (subset_compl_iff_disjoint_left.2 hω)
      choose η W hWo hKW hη _ using fun j =>
        Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
      have hzero : ∀ᶠ j in atTop, X (η j) = 0 := (hclose δ hδ).mono fun j hj => by
        refine (hLOC N k X (η j) 0 _ ((hWo j).inter ((isClosed_tsupport _).isOpen_compl.preimage
          (hsm j).continuous)) (fun x hx => ⟨hKW j hx, hδE (mem_thickening_iff.2
            ⟨F x, mem_image_of_mem F hx, hj x⟩)⟩) fun x hx => ?_).trans (map_zero _)
        rw [hη j x hx.1, image_eq_zero_of_notMem_tsupport hx.2]
        ext v
        simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact tendsto_nhds_unique (hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm
        (fun j x _ => hD j x) hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩)
        (tendsto_const_nhds.congr' (hzero.mono fun j hj => hj.symm))
  · -- (5) `CHAR` for `X`, `dω`, `dηⱼ` and for `∂X`, `ω`, `ηⱼ`; both sequences are `X(dηⱼ) = ∂X(ηⱼ)`
    intro N N' k Λ F X hF hXc hXm hbm
    obtain ⟨hbs, hbc, hbb⟩ := hNCB N k X hXc hbm
    obtain ⟨Fs, hsm, -, hD, -, hU⟩ := hstd N N' Λ F hF
    ext ω
    choose η W hWo hKW hη hdη using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
    have h1 := hCHAR N N' (k + 1) Λ Λ F Fs X (exteriorDerivativeTestOn univ k ω)
      (fun j => exteriorDerivativeTestOn univ k (η j)) hF hXc hXm hbm hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hdη j⟩
    have h2 := hCHAR N N' k Λ Λ F Fs X.boundary ω η hF hbc hbm hbb hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hbs.trans (hKW j), hη j⟩
    simp only [GeometricCurrentOn.boundary_apply] at h2
    rw [GeometricCurrentOn.boundary_apply]
    exact tendsto_nhds_unique h1 h2
  · -- (6) the mollified `Fⱼ` with the cut-off pull-backs `ηⱼ` of `ω`
    intro N N' k Λ F X hF hXc hXm hXb
    obtain ⟨Fs, hsm, hlip, hD, -, hU⟩ := hstd N N' Λ F hF
    refine ⟨Fs, hsm, hlip, hU, fun ω => ?_⟩
    choose η W hWo hKW hη _ using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
    exact ⟨η, fun j => ⟨W j, hWo j, hKW j, hη j⟩, hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm
      (fun j x _ => hD j x) hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩⟩

/-- **Test forms are Lipschitz in the Euclidean coefficient norm** (the constant `c` of the cone
inequality, Simon Ch. 6, 2.27/2.30 as used in 8.2(4)–(6)).  `ω` is `C^∞` with compact support, so
`Dω` is continuous with compact support and `‖Dω(z)‖ ≤ L₀` for some `L₀ ≥ 0`; the mean value
inequality on the convex set `ℝᴾ` gives `‖ω(x) - ω(y)‖ ≤ L₀ ‖x - y‖`.  With the bound
`covectorEuclideanNorm β ≤ C ‖β‖` of `Submission.rsd_mw_tfa_norm_props`, `c = C L₀` works. -/
theorem Submission.cbrld_cone_testForm_coeff_lipschitz : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : Euclid P, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y) ≤ c * dist x y := by
  intro P k U ω
  -- Step 1: the coefficient norm is dominated by the operator norm, `|β| ≤ C ‖β‖`
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P k).2.2.1
  -- Step 2: `ω` is smooth with compact support, so `Dω` is continuous with compact support
  have hsm : IsSmoothForm (ω : DifferentialForm (Euclid P) k) := ω.property.1.1
  have hcs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.property.1.2
  have hcont : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) :=
    hsm.continuous_fderiv (by simp)
  have hcs' : HasCompactSupport (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) := hcs.fderiv ℝ
  -- Step 3: `Dω` is bounded, `‖Dω(z)‖ ≤ L ≤ max L 0`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ z, ‖fderiv ℝ (ω : DifferentialForm (Euclid P) k) z‖ ≤ L :=
    Continuous.bounded_above_of_compact_support
      (f := fderiv ℝ (ω : DifferentialForm (Euclid P) k)) hcont hcs'
  -- Step 4: the mean value inequality on the convex set `ℝᴾ`
  have hdiff : Differentiable ℝ (ω : DifferentialForm (Euclid P) k) :=
    hsm.differentiable (by simp)
  have hmv : ∀ x y : Euclid P, ‖(ω : DifferentialForm (Euclid P) k) x -
      (ω : DifferentialForm (Euclid P) k) y‖ ≤ max L 0 * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => (hL z).trans (le_max_left _ _)) (mem_univ y) (mem_univ x)
  -- Step 5: `c = C · max L 0`
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right _ _), fun x y => ?_⟩
  have h1 := hC ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y)
  have h2 := mul_le_mul_of_nonneg_left (hmv x y) hC0
  rw [dist_eq_norm]
  calc covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x -
        (ω : DifferentialForm (Euclid P) k) y)
      ≤ C * ‖(ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y‖ := h1
    _ ≤ C * (max L 0 * ‖x - y‖) := h2
    _ = C * max L 0 * ‖x - y‖ := by ring
/-- **Radial retraction onto the closed unit ball is nonexpansive towards the ball** (step 0(d)
of `regcomp_exists_smooth_unit_form_approx`).  If `‖y‖ ≤ 1`, then
`‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖`: for `‖x‖ ≤ 1` the retraction fixes `x`; for `s = ‖x‖ > 1`,
`‖x - y‖² - ‖s⁻¹ • x - y‖² = s² - 1 - 2(1 - s⁻¹)⟨x, y⟩ ≥ (s - 1)²` by Cauchy–Schwarz. -/
theorem Submission.regcomp_norm_radial_retraction_sub_le : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E), ‖y‖ ≤ 1 → ‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖ := by
  intro E _ _ x y hy
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · -- Step 1: if `‖x‖ ≤ 1`, the retraction fixes `x`.
    rw [max_eq_left hx, inv_one, one_smul]
  · -- Steps 2–5: `s = ‖x‖ > 1`; compare the squared distances.
    rw [max_eq_right hx.le]
    have hs : 0 < ‖x‖ := one_pos.trans hx
    -- Cauchy–Schwarz with `‖y‖ ≤ 1`: `⟨x, y⟩ ≤ s`; and `s⁻¹ < 1`, `s⁻¹ s = 1`.
    have hxy : inner ℝ x y ≤ ‖x‖ :=
      (real_inner_le_norm x y).trans (mul_le_of_le_one_right hs.le hy)
    have hinv : ‖x‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    have hcancel : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hs.ne'
    -- `‖s⁻¹ • x - y‖² = 1 - 2s⁻¹⟨x, y⟩ + ‖y‖²`.
    have h2 : ‖‖x‖⁻¹ • x - y‖ ^ 2 = 1 - 2 * (‖x‖⁻¹ * inner ℝ x y) + ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hs), hcancel, one_pow]
    -- The difference of the squares is at least `(s - 1)² ≥ 0`.
    have key : ‖‖x‖⁻¹ • x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [h2, norm_sub_sq_real]
      nlinarith [mul_nonneg (sub_nonneg.2 hinv.le) (sub_nonneg.2 hxy), sq_nonneg (‖x‖ - 1)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 key

/-- **The Euclidean coefficient norm** `|α|_E = covectorEuclideanNorm α` on `Λⁿ(ℝᴾ)` (Simon
6.1.15) is a continuous seminorm dominated by the operator norm, and the radial retraction
`v ↦ (max 1 |v|_E)⁻¹ v` onto its unit ball does not increase the distance to points of that ball.

The coefficient map `Φ α = (ev_j α)_j ∈ ℓ²(Fin n → Fin P)`, with
`ev_j α = α(e_{j 0}, …, e_{j (n-1)})` for increasing `j` and `0` otherwise, is continuous linear
with `‖Φ α‖ = |α|_E` (`EuclideanSpace.norm_eq`).  So (i)–(iii) are those of `‖·‖ ∘ Φ`, (iv) holds
with `c = 1 + ‖Φ‖`, and (v) is `regcomp_norm_radial_retraction_sub_le` for `x = Φ v`, `y = Φ b`. -/
theorem Submission.regcomp_covectorEuclideanNorm_seminorm_retract : ∀ (P n : ℕ), ∃ c : ℝ, 0 < c ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) ∧ (∀ α β : Covector (Euclid P) n, covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β) ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ c * ‖α‖) ∧ ∀ v b : Covector (Euclid P) n, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm ((max 1 (covectorEuclideanNorm v))⁻¹ • v - b) ≤ covectorEuclideanNorm (v - b) := by
  intro P n
  classical
  -- `ev j α = α(e_{j 0}, …, e_{j (n-1)})` for increasing `j`, and `0` otherwise
  let ev : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun j =>
    if StrictMono j then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
        (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (j i))
    else 0
  -- the coefficient map `Φ : Λⁿ → ℓ²(Fin n → Fin P)`
  let Φ : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    (EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi ev)
  have hΦ : ∀ α, ‖Φ α‖ = covectorEuclideanNorm α := by
    intro α
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : StrictMono j <;> simp [Φ, ev, hj]
  refine ⟨1 + ‖Φ‖, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_norm.comp Φ.continuous).congr hΦ
  · intro α β
    simpa only [← hΦ, map_add] using norm_add_le (Φ α) (Φ β)
  · intro t α
    simp only [← hΦ, map_smul, norm_smul, Real.norm_eq_abs]
  · intro α
    rw [← hΦ]
    exact (Φ.le_opNorm α).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg α))
  · intro v b hb
    rw [← hΦ] at hb
    simp only [← hΦ, map_sub, map_smul]
    exact Submission.regcomp_norm_radial_retraction_sub_le (EuclideanSpace ℝ (Fin n → Fin P))
      (Φ v) (Φ b) hb
/-- **Evaluation of a finite-mass current is bounded by mass times the coefficient sup norm**
(Simon Ch. 6, 2.4: `M(X) = sup_{|ω| ≤ 1} X(ω)`, so `|X(ω)| ≤ sup |ω| · M(X)`; used for the
mass-absolutely convergent series in the proof of 7.2).  For `|s| = c⁻¹` the rescaled form
`s • ω` is admissible for `M(X) = M_U(X)`, as `|s • ω(x)| = c⁻¹ |ω(x)| ≤ 1` by homogeneity of
the coefficient norm; hence `s X(ω) = X(s • ω) ≤ M(X)`.  The choices `s = ±c⁻¹` give
`±X(ω) ≤ c M(X)`. -/
theorem Submission.cmc_fc_sc_abs_le_mul_mass : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n) (ω : TestFormOn U n) (c : ℝ), 0 < c → X.mass ≠ ∞ → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |X ω| ≤ c * X.mass.toReal := by
  intro P n U X ω c hc hX hω
  -- Step 1: for `|s| = c⁻¹`, `s • ω` is admissible, so `s X(ω) = X(s • ω) ≤ M(X)`
  have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * X ω ≤ X.mass.toReal := by
    intro s hs
    have hadm : s • ω ∈ massAdmissibleOn U n U := by
      refine ⟨(s • ω).property.2, fun x => ?_⟩
      have hx : ((s • ω : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
          s • ((ω : DifferentialForm (Euclid P) n) x) := rfl
      rw [hx, (Submission.rsd_mw_tfa_norm_props P n).2.1, hs]
      calc c⁻¹ * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c⁻¹ * c :=
            mul_le_mul_of_nonneg_left (hω x) (inv_nonneg.mpr hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    have hle : ENNReal.ofReal (X (s • ω)) ≤ X.mass := X.le_massOn hadm
    rw [ENNReal.ofReal_le_iff_le_toReal hX] at hle
    have hlin : X (s • ω) = s * X ω := by
      rw [map_smul, smul_eq_mul]
    rwa [hlin] at hle
  -- Step 2: `s = c⁻¹` and `s = -c⁻¹` give `X(ω) ≤ c M(X)` and `-X(ω) ≤ c M(X)`
  have hinv : |c⁻¹| = c⁻¹ := abs_of_pos (inv_pos.mpr hc)
  have hpos := mul_le_mul_of_nonneg_left (hbound c⁻¹ hinv) hc.le
  have hneg := mul_le_mul_of_nonneg_left (hbound (-c⁻¹) (by rw [abs_neg, hinv])) hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hpos
  rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hneg
  exact abs_le.mpr ⟨by linarith, hpos⟩
/-- **Mass of a difference** (Simon (6.2.5), chapter-06.txt line 231; this subadditivity makes the
flat distances `d_W` of 7.1 (lines 2018–2022) pseudometrics and is used in the proof of 7.2):
`M_G(A − B) ≤ M_G(A) + M_G(B)` for every set `G`.  If `ω` is admissible for `M_G` then so is `−ω`
(same support, same coefficient norm), and `(A − B)(ω) = A(ω) + B(−ω)`, so
`ofReal ((A − B)(ω)) ≤ ofReal (A(ω)) + ofReal (B(−ω)) ≤ M_G(A) + M_G(B)`. -/
theorem Submission.cmc_fc_cs_massOn_sub_le : ∀ (P n : ℕ) (U G : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).massOn G ≤ A.massOn G + B.massOn G := by
  intro P n U G A B
  -- Step 1: it suffices to bound `ofReal ((A − B)(ω))` for each admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  -- Step 2: `−ω` is admissible: same support, same coefficient norm
  have hneg : -ω ∈ massAdmissibleOn U n G := by
    refine ⟨?_, fun x => ?_⟩
    · rw [Submodule.coe_neg, tsupport_neg]
      exact hω.1
    · rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 3: `(A − B)(ω) = A(ω) − B(ω) = A(ω) + B(−ω)`, by linearity of `B`
  have hsplit : (A - B) ω = A ω + B (-ω) := by
    have hB : B (-ω) = -B ω := B.toCurrent.map_neg ω
    change A ω - B ω = A ω + B (-ω)
    rw [hB, sub_eq_add_neg]
  -- Steps 4–5: `ofReal` is subadditive, and each term is bounded by the corresponding mass
  calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
    _ ≤ A.massOn G + B.massOn G := add_le_add (A.le_massOn hω) (B.le_massOn hneg)
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

/-- **Slice and restriction forms along `x ↦ ι(t, x) = (t, x)`** (the forms entering the cylinder
`[[(0, 1)]] × X` of Simon Ch. 6, 2.18–2.21 and the homotopy formula 2.25, as used for the
Lipschitz push-forward in the deformation theorem).  With `J v = (0, v)` and `e₀ = (1, 0, …, 0)`,
the forms `η_t = (ω(·).curryLeft e₀)(ι(t, ·)) ∘ J`, `β_s = ω(ι(s, ·)) ∘ J` and
`γ_t = (Dω(ι(t, ·)) e₀) ∘ J` are affine pull-backs along the isometry `x ↦ single(0, t) + J x`,
which is proper, so they are test forms.  Every slice family satisfies `η_t(x) = S(ω(ι(t, x)))`
for the slice map `S α = (α.curryLeft e₀).compContinuousLinearMap J`; the covector bounds (L1),
(L2) and `‖J‖ ≤ 1` give `|S α| ≤ |α|`, which with `Submission.cbrld_cone_testForm_coeff_lipschitz`
yields the pointwise bound, the Lipschitz estimate in `t` and the support inclusion. -/
theorem Submission.dimred_mbl_dt_lpc_slice_forms : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), (∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ (t : ℝ) (x : Euclid N), covectorEuclideanNorm ((η t : DifferentialForm (Euclid N) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) ∧ (∀ (s t : ℝ) (x : Euclid N), covectorEuclideanNorm ((η s : DifferentialForm (Euclid N) k) x - (η t : DifferentialForm (Euclid N) k) x) ≤ c * |s - t|) ∧ ∀ t : ℝ, tsupport (η t : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), (∃ β : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∃ γ : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (γ t : DifferentialForm (Euclid N) k) x v = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ β : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∀ (s : ℝ) (x : Euclid N), covectorEuclideanNorm ((β s : DifferentialForm (Euclid N) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) := by
  rintro ⟨hL1, hL2⟩
  -- Step 1(a): the embedding `J v = (0, v)` is linear with `‖J v‖ = ‖v‖`
  have hJex : ∀ N : ℕ, ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧ ∀ v, ‖J v‖ = ‖v‖ := by
    intro N
    let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun v w => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun c v => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    have hn : ∀ v, ‖Jl v‖ = ‖v‖ := by
      intro v
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
      simp [Jl]
    exact ⟨LinearMap.mkContinuous Jl 1 fun v => by rw [hn, one_mul], fun v => rfl, hn⟩
  -- Step 1(a)–(d): `‖J‖ ≤ 1`, `ι(t, x) = single(0, t) + J x`, each `x ↦ ι(t, x)` is an
  -- isometry, hence proper, and `dist (ι(s, x)) (ι(t, x)) = |s - t|`
  have hJprops : ∀ (N : ℕ) (J : Euclid N →L[ℝ] Euclid (N + 1)),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) → (∀ v, ‖J v‖ = ‖v‖) →
      ‖J‖ ≤ 1 ∧
      (∀ (t : ℝ) (x : Euclid N), (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) =
        EuclideanSpace.single 0 t + J x) ∧
      (∀ t : ℝ, IsProperMap fun x => EuclideanSpace.single (0 : Fin (N + 1)) t + J x) ∧
      ∀ (s t : ℝ) (x : Euclid N),
        dist (EuclideanSpace.single (0 : Fin (N + 1)) s + J x)
          (EuclideanSpace.single 0 t + J x) = |s - t| := by
    intro N J hJ hn
    refine ⟨J.opNorm_le_bound zero_le_one fun v => by rw [hn, one_mul], fun t x => ?_,
      fun t => ?_, fun s t x => ?_⟩
    · rw [hJ]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · have hiso : Isometry fun x => EuclideanSpace.single (0 : Fin (N + 1)) t + J x :=
        Isometry.of_dist_eq fun x y => by
          rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← map_sub, hn]
      exact hiso.isClosedEmbedding.isProperMap
    · rw [dist_add_right]
      simp [Real.dist_eq]
  refine ⟨fun N k ω => ?_, fun N k ω => ?_⟩
  · obtain ⟨J, hJ, hn⟩ := hJex N
    obtain ⟨hJ1, hι, hprop, hdist⟩ := hJprops N J hJ hn
    -- Step 2: the slice map `S α = (α.curryLeft e₀).compContinuousLinearMap J` is continuous
    -- linear, `S α v = α (e₀, J v)`, and `|S α| ≤ ‖J‖ ^ k |α.curryLeft e₀| ≤ |α|` by (L1), (L2)
    let Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid (N + 1)) k :=
      (ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k) (EuclideanSpace.single 0 1)).comp
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid (N + 1)) (F := ℝ)
          (n := k)).toContinuousLinearMap
    let S : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k :=
      (ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp Φ
    have hS : ∀ (α : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N),
        S α v = α (Fin.cons (EuclideanSpace.single 0 1) fun i => J (v i)) := fun α v => rfl
    have hSb : ∀ α, covectorEuclideanNorm (S α) ≤ covectorEuclideanNorm α := by
      intro α
      have h1 := hL1 N (N + 1) k J (α.curryLeft (EuclideanSpace.single 0 1))
      have h2 := hL2 (N + 1) k (EuclideanSpace.single 0 1) α
      have he : ‖(EuclideanSpace.single (0 : Fin (N + 1)) (1 : ℝ))‖ = 1 := by simp
      have hJk : ‖J‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hJ1
      have h0 := covectorEuclideanNorm_nonneg (α.curryLeft (EuclideanSpace.single 0 1))
      rw [he, one_mul] at h2
      calc covectorEuclideanNorm (S α)
          = covectorEuclideanNorm
              ((α.curryLeft (EuclideanSpace.single 0 1)).compContinuousLinearMap J) := rfl
        _ ≤ ‖J‖ ^ k * covectorEuclideanNorm (α.curryLeft (EuclideanSpace.single 0 1)) := h1
        _ ≤ 1 * covectorEuclideanNorm (α.curryLeft (EuclideanSpace.single 0 1)) :=
            mul_le_mul_of_nonneg_right hJk h0
        _ ≤ covectorEuclideanNorm α := by rw [one_mul]; exact h2
    -- Step 3: (A1), `η_t` is the affine pull-back of `ω₁ = ω(·).curryLeft e₀` along
    -- `x ↦ ι(t, x)`
    have hω₁ : IsTestForm fun y => Φ ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) :=
      ⟨Φ.contDiff.comp ω.property.1.1, ω.property.1.2.comp_left (map_zero Φ)⟩
    refine ⟨⟨fun t => ⟨affinePullbackForm J (EuclideanSpace.single 0 t)
      (fun y => Φ ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y)),
      affinePullbackForm_isTestForm J _ (hprop t) hω₁, subset_univ _⟩,
      fun t x v => ?_⟩, ?_⟩
    · show S ((ω : DifferentialForm (Euclid (N + 1)) (k + 1))
        (EuclideanSpace.single 0 t + J x)) v = _
      rw [hS, ← hι t x]
      simp only [hJ]
    -- Step 5: the Lipschitz constant `c` of `ω`, fixed before the family `η`
    obtain ⟨c, hc0, hc⟩ :=
      Submission.cbrld_cone_testForm_coeff_lipschitz (N + 1) (k + 1) univ ω
    refine ⟨c, hc0, fun η hη => ?_⟩
    -- Step 4: every slice family is `η_t(x) = S(ω(ι(t, x)))`
    have hnf : ∀ t x, (η t : DifferentialForm (Euclid N) k) x =
        S ((ω : DifferentialForm (Euclid (N + 1)) (k + 1))
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) := by
      intro t x
      ext v
      rw [hη t x v, hS]
      simp only [hJ]
    -- Step 5: (A2), (i) the pointwise bound, (ii) the Lipschitz estimate, (iii) the support
    refine ⟨fun t x => ?_, fun s t x => ?_, fun t => ?_⟩
    · rw [hnf]
      exact hSb _
    · rw [hnf, hnf, ← map_sub]
      calc _ ≤ _ := hSb _
        _ ≤ c * dist (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) := hc _ _
        _ = c * |s - t| := by rw [hι, hι, hdist]
    · have hcont : Continuous fun x : Euclid N =>
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) := by
        simp only [hι]
        exact continuous_const.add J.continuous
      refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport _).preimage hcont)
      by_contra hx'
      apply hx
      rw [hnf, image_eq_zero_of_notMem_tsupport hx', map_zero]
  · obtain ⟨J, hJ, hn⟩ := hJex N
    obtain ⟨hJ1, hι, hprop, -⟩ := hJprops N J hJ hn
    have hω : IsTestForm (ω : DifferentialForm (Euclid (N + 1)) k) := ω.property.1
    -- Step 6: (B1), `β_s` is the affine pull-back of `ω` along `x ↦ ι(s, x)`
    refine ⟨⟨fun s => ⟨affinePullbackForm J (EuclideanSpace.single 0 s)
      (ω : DifferentialForm (Euclid (N + 1)) k),
      affinePullbackForm_isTestForm J _ (hprop s) hω, subset_univ _⟩,
      fun s x v => ?_⟩, ?_, ?_⟩
    · show (ω : DifferentialForm (Euclid (N + 1)) k) (EuclideanSpace.single 0 s + J x)
        (fun i => J (v i)) = _
      rw [← hι s x]
      simp only [hJ]
    -- Step 6: (B2), `γ_t` is the affine pull-back of the test form `ω' = Dω(·) e₀`
    · have hω' : IsTestForm fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y
          (EuclideanSpace.single 0 1) :=
        ⟨(hω.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply
            contDiff_const,
          (hω.2.fderiv ℝ).comp_left
            (g := fun L : Euclid (N + 1) →L[ℝ] Covector (Euclid (N + 1)) k =>
              L (EuclideanSpace.single 0 1)) rfl⟩
      refine ⟨fun t => ⟨affinePullbackForm J (EuclideanSpace.single 0 t)
        (fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y
          (EuclideanSpace.single 0 1)),
        affinePullbackForm_isTestForm J _ (hprop t) hω', subset_univ _⟩, fun t x v => ?_⟩
      show fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (EuclideanSpace.single 0 t + J x)
        (EuclideanSpace.single 0 1) (fun i => J (v i)) = _
      rw [← hι t x]
      simp only [hJ]
    -- Step 7: (B3), `β_s(x) = ω(ι(s, x)).compContinuousLinearMap J`, so (L1) and `‖J‖ ≤ 1`
    -- give `|β_s(x)| ≤ |ω(ι(s, x))|`
    · intro β hβ s x
      have hnf : (β s : DifferentialForm (Euclid N) k) x =
          ((ω : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))).compContinuousLinearMap J := by
        ext v
        rw [hβ s x v, ContinuousAlternatingMap.compContinuousLinearMap_apply]
        simp only [Function.comp_def, hJ]
      rw [hnf]
      have hJk : ‖J‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hJ1
      calc _ ≤ ‖J‖ ^ k * covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) := hL1 _ _ _ _ _
        _ ≤ 1 * covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) :=
          mul_le_mul_of_nonneg_right hJk (covectorEuclideanNorm_nonneg _)
        _ = _ := one_mul _
/-- **Exterior derivative along a slice.**  Write `ι(t, x) = (t, x)`, `e₀ = (1, 0, …, 0)` and
`J v = (0, v)`.  (a) If `η_t(x)(v) = ω(ι(t, x))(e₀, Jv)` for a test form `ω` of degree `k + 1`,
then `dω(ι(t, x))(e₀, Jv) = (Dω(ι(t, x))e₀)(Jv) − d(η_t)(x)(v)`.  (b) In degree `0`,
`dω(ι(t, x))(e₀) = (Dω(ι(t, x))e₀)()`. -/
theorem Submission.dimred_mbl_dt_lpc_slice_extDeriv : ((∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (η : ℝ → TestFormOn (univ : Set (Euclid N)) k), (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N), exteriorDerivative (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (η t : DifferentialForm (Euclid N) k) x v) ∧ ∀ (N : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) 0) (t : ℝ) (x : Euclid N) (v : Fin 0 → Euclid N), exteriorDerivative (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
  refine ⟨?_, ?_⟩
  -- (a)
  · intro N k ω η hη
    -- the continuous linear map `J v = (0, v)`, with `ι(t, x) = single 0 t + J x`
    obtain ⟨J, hJ, hι⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
        (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧
        ∀ (t : ℝ) (x : Euclid N), (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) =
          EuclideanSpace.single 0 t + J x := by
      let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
        { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
          map_add' := by
            intro a b
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_smul' := by
            intro c a
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp }
      refine ⟨LinearMap.toContinuousLinearMap Jl, fun v => rfl, fun t x => ?_⟩
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Jl]
      · simp [Jl]
    intro t x v
    have hωd : Differentiable ℝ (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) :=
      ω.property.1.1.differentiable (by simp)
    have hηd : Differentiable ℝ (η t : DifferentialForm (Euclid N) k) :=
      (η t).property.1.1.differentiable (by simp)
    -- coordinate formula for `d`, split into the term `i = 0` and the terms `i = j + 1`
    rw [exteriorDerivative_apply (hωd _), exteriorDerivative_apply (hηd _), Fin.sum_univ_succ]
    -- chain rule through the affine slice map `x ↦ ι(t, x)`
    have hchain : ∀ (u : Fin k → Euclid N) (w : Euclid N),
        fderiv ℝ (fun x' => (η t : DifferentialForm (Euclid N) k) x' u) x w =
          fderiv ℝ (fun y => (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i))))))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (J w) := by
      intro u w
      have hfun : (fun x' => (η t : DifferentialForm (Euclid N) k) x' u) =
          (fun y => (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i))))))
            ∘ (fun x' => EuclideanSpace.single 0 t + J x') := by
        funext x'
        simp only [Function.comp_apply, ← hι]
        exact hη t x' u
      have hg : DifferentiableAt ℝ (fun y => (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i))))))
            (EuclideanSpace.single 0 t + J x) :=
        (hωd _).continuousAlternatingMap_apply_const _
      have hA : HasFDerivAt (fun x' : Euclid N => EuclideanSpace.single 0 t + J x') J x :=
        J.hasFDerivAt.const_add _
      rw [hfun, (hg.hasFDerivAt.comp x hA).fderiv, ← hι]
      rfl
    -- the term `i = 0` is `(Dω(ι(t, x))e₀)(Jv)`
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.removeNth_zero, Fin.tail_cons]
    rw [fderiv_continuousAlternatingMap_apply_const (hωd _)]
    simp only [ContinuousLinearMap.flipAlternating_apply_apply]
    -- the terms `i = j + 1` are minus the terms of `d(η_t)(x)(v)`
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hchain, hJ]
    have hrm : Fin.removeNth j.succ (Fin.cons (EuclideanSpace.single 0 1)
        (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :
          Fin (k + 1 + 1) → Euclid (N + 1)) =
        Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))) :=
      Fin.cons_comp_succ_succAbove _ _ j
    rw [hrm, pow_succ]
    simp only [mul_neg, mul_one, neg_smul]
  -- (b): in degree `0` only the term `i = 0` occurs
  · intro N ω t x v
    have hωd : Differentiable ℝ (ω : DifferentialForm (Euclid (N + 1)) 0) :=
      ω.property.1.1.differentiable (by simp)
    rw [exteriorDerivative_apply (hωd _), Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero]
    rw [fderiv_continuousAlternatingMap_apply_const (hωd _)]
    simp only [ContinuousLinearMap.flipAlternating_apply_apply]
    congr 1
/-- **Fundamental theorem of calculus under a finite-mass current** (step 5 of
`dimred_mbl_dt_lp_cylinder`).  Let `X ∈ 𝒟ₖ(ℝᴺ)` have finite mass, `ω ∈ 𝒟ᵏ(ℝᴺ⁺¹)`, and let
`β_s(x) = ω(ι(s, x)) ∘ J`, `γ_t(x) = (Dω(ι(t, x)) e₀) ∘ J`, where `ι(t, x) = (t, x)` and
`J v = (0, v)`.  Then `∫₀¹ X(γ_t) dt = X(β₁) - X(β₀)`: (REP) gives `X(φ) = ∫ ξ(x)(φ(x)) dμ` with
`μ` finite and `ξ` bounded, Fubini swaps the integrals, and the fundamental theorem of calculus
applies to `t ↦ ξ(x)(β_t(x))` for each `x`. -/
theorem Submission.dimred_mbl_dt_lpc_ftc_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), X.mass < ∞ → ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) k) (β γ : ℝ → TestFormOn (univ : Set (Euclid N)) k), (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (γ t : DifferentialForm (Euclid N) k) x v = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∫ t in (0 : ℝ)..1, X (γ t) = X (β 1) - X (β 0) := by
  intro REP N k X hX ω β γ hβ hγ
  -- Step 1: (REP) with `U = univ` represents `X` by a finite measure `μ` and an orientation `ξ`.
  have hloc : ∀ W : Set (Euclid N), IsOpen W → CompactlyContained W univ → X.massOn W < ∞ :=
    fun W _ _ => lt_of_le_of_lt (X.massOn_mono (subset_univ W)) hX
  obtain ⟨μ, ξ, -, -, hμW, hξm, hξb, hrep, -⟩ := REP N k univ X isOpen_univ hloc
  have : IsFiniteMeasure μ := ⟨by rw [← hμW univ isOpen_univ]; exact hX⟩
  -- Step 2: `J v = (0, v)`, so `ι(t, x) = t e₀ + J x`; normal forms `β_s(x) = C_J(ω(ι(s, x)))`
  -- and `γ_t(x) = C_J(Dω(ι(t, x)) e₀)` with `C_J α = α ∘ J`.
  obtain ⟨J, hJ, hι⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧
      ∀ (t : ℝ) (x : Euclid N), (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) =
        t • EuclideanSpace.single 0 1 + J x := by
    let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun a b => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun c a => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    refine ⟨LinearMap.toContinuousLinearMap Jl, fun v => rfl, fun t x => ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Jl]
  set e₀ : Euclid (N + 1) := EuclideanSpace.single 0 1
  let CJ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM J
  have hCJ : ∀ a : Covector (Euclid (N + 1)) k, CJ a = a.compContinuousLinearMap J := fun a => rfl
  have hβc : ∀ s x, (β s : DifferentialForm (Euclid N) k) x =
      CJ ((ω : DifferentialForm (Euclid (N + 1)) k) (s • e₀ + J x)) := by
    intro s x
    ext v
    rw [hβ s x v, hCJ, hι s x]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hJ]
  have hγc : ∀ t x, (γ t : DifferentialForm (Euclid N) k) x =
      CJ (fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (t • e₀ + J x) e₀) := by
    intro t x
    ext v
    rw [hγ t x v, hCJ, hι t x]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hJ]
  -- Step 3: `ω` is `C¹` with compact support, so `ω` and `y ↦ Dω(y) e₀` are bounded.
  have hωC : ContDiff ℝ 1 (ω : DifferentialForm (Euclid (N + 1)) k) :=
    ω.property.1.1.of_le (by simp)
  have hωd : Differentiable ℝ (ω : DifferentialForm (Euclid (N + 1)) k) :=
    hωC.differentiable one_ne_zero
  have hDω : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k)) :=
    hωC.continuous_fderiv one_ne_zero
  have hωcont : Continuous (ω : DifferentialForm (Euclid (N + 1)) k) := hωC.continuous
  have hωcs : HasCompactSupport (ω : DifferentialForm (Euclid (N + 1)) k) := ω.property.1.2
  have hDe : Continuous (fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y e₀) :=
    hDω.clm_apply continuous_const
  have hDecs : HasCompactSupport
      (fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y e₀) :=
    HasCompactSupport.comp_left
      (g := fun L : Euclid (N + 1) →L[ℝ] Covector (Euclid (N + 1)) k => L e₀)
      (hωcs.fderiv ℝ) (by simp)
  -- Step 4: `t ↦ ξ(x)(β_t(x))` has derivative `ξ(x)(γ_t(x))` (chain rule).
  have hderiv : ∀ (x : Euclid N) (t : ℝ),
      HasDerivAt (fun s => ξ x ((β s : DifferentialForm (Euclid N) k) x))
        (ξ x ((γ t : DifferentialForm (Euclid N) k) x)) t := by
    intro x t
    have h1 : HasDerivAt (fun s : ℝ => s • e₀ + J x) e₀ t := by
      simpa using ((hasDerivAt_id t).smul_const e₀).add_const (J x)
    have h2 : HasDerivAt (fun s => (ω : DifferentialForm (Euclid (N + 1)) k) (s • e₀ + J x))
        (fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (t • e₀ + J x) e₀) t :=
      (hωd _).hasFDerivAt.comp_hasDerivAt t h1
    have h4 := (ξ x).hasFDerivAt.comp_hasDerivAt t (CJ.hasFDerivAt.comp_hasDerivAt t h2)
    simp only [hβc, hγc]
    exact h4
  -- Step 5: continuity, and uniform bounds via `|α| ≤ c ‖α‖` (coefficient-norm toolkit (iv)).
  have hγcont : Continuous
      (fun p : ℝ × Euclid N => (γ p.1 : DifferentialForm (Euclid N) k) p.2) := by
    simp only [hγc]
    exact CJ.continuous.comp ((hDω.comp ((continuous_fst.smul continuous_const).add
      (J.continuous.comp continuous_snd))).clm_apply continuous_const)
  have hβcont : ∀ s, Continuous (fun x => (β s : DifferentialForm (Euclid N) k) x) := by
    intro s
    simp only [hβc]
    exact CJ.continuous.comp (hωcont.comp (continuous_const.add J.continuous))
  obtain ⟨c, hc, -, -, -, hcle, -⟩ := Submission.regcomp_covectorEuclideanNorm_seminorm_retract N k
  obtain ⟨M₁, hM₁⟩ := hDe.bounded_above_of_compact_support hDecs
  obtain ⟨M₀, hM₀⟩ := hωcont.bounded_above_of_compact_support hωcs
  have hγb : ∀ t x, ‖ξ x ((γ t : DifferentialForm (Euclid N) k) x)‖ ≤ c * (‖CJ‖ * M₁) := by
    intro t x
    rw [Real.norm_eq_abs]
    refine (hξb x _).trans ((hcle _).trans (mul_le_mul_of_nonneg_left ?_ hc.le))
    rw [hγc]
    exact (CJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM₁ _) (norm_nonneg _))
  have hβb : ∀ s x, ‖ξ x ((β s : DifferentialForm (Euclid N) k) x)‖ ≤ c * (‖CJ‖ * M₀) := by
    intro s x
    rw [Real.norm_eq_abs]
    refine (hξb x _).trans ((hcle _).trans (mul_le_mul_of_nonneg_left ?_ hc.le))
    rw [hβc]
    exact (CJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM₀ _) (norm_nonneg _))
  -- Step 6: measurability and integrability on `(0, 1] × ℝᴺ` and on `ℝᴺ`.
  have hev : Continuous
      (Function.uncurry fun (α : Covector (Euclid N) k) (L : MultiVector N k) => L α) :=
    continuous_snd.clm_apply continuous_fst
  have hβint : ∀ s, Integrable (fun x => ξ x ((β s : DifferentialForm (Euclid N) k) x)) μ := by
    intro s
    refine Integrable.of_bound ?_ (c * (‖CJ‖ * M₀)) (Eventually.of_forall fun x => hβb s x)
    exact hev.comp_aestronglyMeasurable₂ (hβcont s).aestronglyMeasurable hξm
  have hint : Integrable (Function.uncurry fun (t : ℝ) (x : Euclid N) =>
      ξ x ((γ t : DifferentialForm (Euclid N) k) x)) ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
    refine Integrable.of_bound ?_ (c * (‖CJ‖ * M₁)) (Eventually.of_forall fun p => hγb p.1 p.2)
    exact hev.comp_aestronglyMeasurable₂ hγcont.aestronglyMeasurable hξm.comp_snd
  -- Step 7: (REP), Fubini, the fundamental theorem of calculus for each `x`, and (REP) again.
  have hftc : ∀ x, ∫ t in (0 : ℝ)..1, ξ x ((γ t : DifferentialForm (Euclid N) k) x) =
      ξ x ((β 1 : DifferentialForm (Euclid N) k) x) -
        ξ x ((β 0 : DifferentialForm (Euclid N) k) x) := by
    intro x
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv x t) ?_
    exact ((ξ x).continuous.comp
      (hγcont.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  calc ∫ t in (0 : ℝ)..1, X (γ t)
      = ∫ t in (0 : ℝ)..1, ∫ x, ξ x ((γ t : DifferentialForm (Euclid N) k) x) ∂μ := by
        congr 1
        funext t
        exact hrep (γ t)
    _ = ∫ x, (∫ t in (0 : ℝ)..1, ξ x ((γ t : DifferentialForm (Euclid N) k) x)) ∂μ := by
        simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
        exact integral_integral_swap hint
    _ = X (β 1) - X (β 0) := by
        simp_rw [hftc]
        rw [integral_sub (hβint 1) (hβint 0), ← hrep, ← hrep]
/-- **The cylinder `[[(0, 1)]] × X`** (Simon Ch. 6, 2.17–2.21, the product current of the
homotopy formula 2.25).  Write `ι(t, x) = (t, x)`, `Jv = ι(0, v)`, and call `η : ℝ → 𝒟ᵏ(ℝᴺ)` a
slice family of `ω ∈ 𝒟ᵏ⁺¹(ℝᴺ⁺¹)` if `η_t(x)(v) = ω(ι(t, x))(e₀, Jv₁, …, Jvₖ)`.  Every `ω` has
a slice family `η^ω`, which is unique, and `|η_s(x) − η_t(x)| ≤ c|s − t|` makes `t ↦ X(η_t)`
`c M(X)`-Lipschitz (`dimred_mbl_dt_lpc_slice_forms`).  So `L(ω) = ∫₀¹ X(η^ω_t) dt` is linear,
and `|η^ω_t(x)| ≤ |ω(ι(t, x))|` gives `|L(ω)| ≤ c M(X)` when `|ω| ≤ c`: `L` is a current `Y`
with `M(Y) ≤ M(X)` (cf. 2.20).  If `spt X` is compact and `spt ω` misses the compact set
`E = ι([0, 1] × spt X)`, each slice `η^ω_t`, `t ∈ [0, 1]`, misses `spt X`, so `Y(ω) = 0`; hence
`spt Y ⊆ E` is compact. -/
theorem Submission.dimred_mbl_dt_lpc_cylinder_current : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), X.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1), Y.mass ≤ X.mass ∧ (IsCompact X.support → IsCompact Y.support ∧ Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (η : ℝ → TestFormOn (univ : Set (Euclid N)) k), (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → Continuous (fun t => X (η t)) ∧ Y ω = ∫ t in (0 : ℝ)..1, X (η t) := by
  intro hCB hVO N k X hX
  classical
  have hS := (Submission.dimred_mbl_dt_lpc_slice_forms hCB).1 N k
  have hXm : X.mass ≠ ∞ := hX.ne
  -- Step 1: a slice family `η^ω` of every `ω`; every slice family of `ω` equals `η^ω`
  choose ηf hηf using fun ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) => (hS ω).1
  have huniq : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
      (η : ℝ → TestFormOn (univ : Set (Euclid N)) k),
      (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N),
        (η t : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) →
      η = ηf ω := by
    intro ω η hη
    funext t
    apply Subtype.ext
    funext x
    ext v
    rw [hη, hηf]
  -- Step 2: `|X(η_s) − X(η_t)| ≤ c M(X) |s − t|`, so `t ↦ X(η_t)` is continuous
  have hcont : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
      (η : ℝ → TestFormOn (univ : Set (Euclid N)) k),
      (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N),
        (η t : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) →
      Continuous (fun t => X (η t)) := by
    intro ω η hη
    obtain ⟨c, hc0, hc⟩ := (hS ω).2
    obtain ⟨-, hlip, -⟩ := hc η hη
    have hM : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hL : ∀ s t, dist (X (η s)) (X (η t)) ≤ (c * X.mass.toReal) * dist s t := by
      intro s t
      rw [Real.dist_eq, Real.dist_eq]
      have hsub : X (η s) - X (η t) = X (η s - η t) := (map_sub X.toCurrent _ _).symm
      rw [hsub]
      -- (a)–(b): `|(η_s − η_t)(x)| ≤ c|s − t| + ε`, so `|X(η_s − η_t)| ≤ (c|s − t| + ε) M(X)`
      have hε : ∀ ε > 0, |X (η s - η t)| ≤ (c * |s - t| + ε) * X.mass.toReal := by
        intro ε hε
        apply Submission.cmc_fc_sc_abs_le_mul_mass N k univ X (η s - η t) (c * |s - t| + ε)
          (by positivity) hXm
        intro x
        simp only [Submodule.coe_sub, Pi.sub_apply]
        linarith [hlip s t x]
      -- (c): let `ε ↓ 0`
      refine le_of_forall_pos_le_add (fun δ hδ => ?_)
      have h := hε (δ / (X.mass.toReal + 1)) (by positivity)
      have h2 : (δ / (X.mass.toReal + 1)) * X.mass.toReal ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hL' : LipschitzWith (Real.toNNReal (c * X.mass.toReal)) (fun t => X (η t)) := by
      refine LipschitzWith.of_dist_le_mul (fun s t => ?_)
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hL s t
    exact hL'.continuous
  -- Step 3: `L(ω) = ∫₀¹ X(η^ω_t) dt` is linear: by Step 1, `η^{ω₁ + ω₂} = η^{ω₁} + η^{ω₂}` and
  -- `η^{aω} = a η^ω`, and the integrands are continuous by Step 2
  let L : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ t in (0 : ℝ)..1, X (ηf ω t)
      map_add' := by
        intro ω₁ ω₂
        have h : ηf (ω₁ + ω₂) = fun t => ηf ω₁ t + ηf ω₂ t := by
          refine (huniq (ω₁ + ω₂) (fun t => ηf ω₁ t + ηf ω₂ t) ?_).symm
          intro t x v
          simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
          rw [hηf ω₁, hηf ω₂]
        simp only [h, map_add]
        exact intervalIntegral.integral_add ((hcont ω₁ _ (hηf ω₁)).intervalIntegrable 0 1)
          ((hcont ω₂ _ (hηf ω₂)).intervalIntegrable 0 1)
      map_smul' := by
        intro a ω
        have h : ηf (a • ω) = fun t => a • ηf ω t := by
          refine (huniq (a • ω) (fun t => a • ηf ω t) ?_).symm
          intro t x v
          simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
          rw [hηf ω]
        simp only [h, map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_const_mul a _ }
  have hLω : ∀ ω, L ω = ∫ t in (0 : ℝ)..1, X (ηf ω t) := fun ω => rfl
  -- Step 4: if `|ω| ≤ c`, then `|η^ω_t(x)| ≤ |ω(ι(t, x))| ≤ c`, so `|X(η^ω_t)| ≤ c M(X)` and
  -- `|L(ω)| ≤ c M(X)`
  have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), 0 < c →
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) →
      |L ω| ≤ c * X.mass.toReal := by
    intro ω c hc hω
    obtain ⟨c', -, hc'⟩ := (hS ω).2
    obtain ⟨hpt, -, -⟩ := hc' (ηf ω) (hηf ω)
    have h1 : ∀ t, ‖X (ηf ω t)‖ ≤ c * X.mass.toReal := fun t => by
      rw [Real.norm_eq_abs]
      exact Submission.cmc_fc_sc_abs_le_mul_mass N k univ X (ηf ω t) c hc hXm
        (fun x => (hpt t x).trans (hω _))
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (fun t _ => h1 t)
    rw [hLω, ← Real.norm_eq_abs]
    simpa using h2
  -- Step 5: `L` is a current `Y`; with Steps 1–2 this is (c)
  obtain ⟨Y, hY⟩ := Submission.cmc_fc_sc_current_of_coeff_bound (N + 1) (k + 1) univ L
    X.mass.toReal (fun ω c hc hω => hbound ω c hc hω)
  refine ⟨Y, ?_, ?_, fun ω η hη => ⟨hcont ω η hη, ?_⟩⟩
  · -- Step 6, (a): an admissible `ω` has `|ω| ≤ 1`, so `Y(ω) = L(ω) ≤ M(X)`
    show Y.massOn univ ≤ X.mass
    unfold GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    have h := hbound ω 1 one_pos hω.2
    show ENNReal.ofReal (Y ω) ≤ X.mass
    rw [hY ω]
    calc ENNReal.ofReal (L ω) ≤ ENNReal.ofReal (X.mass.toReal) :=
          ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (L ω)])
      _ = X.mass := ENNReal.ofReal_toReal hXm
  · -- Step 7, (b): `Y` vanishes on forms missing the compact set `E = ι([0, 1] × spt X)`
    intro hXc
    -- (a) `E` is the continuous image of the compact set `[0, 1] × spt X`
    have hE : {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} =
        (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
          Euclid (N + 1))) '' (Icc (0 : ℝ) 1 ×ˢ X.support) := by
      ext y
      simp only [mem_ofPred_eq, mem_image, mem_prod, Prod.exists]
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨t, x, ⟨ht, hx⟩, rfl⟩
      · rintro ⟨t, x, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    have hιc : Continuous (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)
    have hEc : IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      rw [hE]
      exact (isCompact_Icc.prod hXc).image hιc
    -- (b)–(d) if `spt ω ∩ E = ∅`, every slice `η^ω_t`, `t ∈ [0, 1]`, misses `spt X`, so
    -- `X(η^ω_t) = 0` and `Y(ω) = 0`
    have hvan : ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1),
        Disjoint (tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1)))
          {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
            y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} →
        Y ω = 0 := by
      intro ω hω
      rw [hY ω, hLω]
      obtain ⟨c, -, hc⟩ := (hS ω).2
      obtain ⟨-, -, hsup⟩ := hc (ηf ω) (hηf ω)
      have h0 : ∀ t ∈ uIcc (0 : ℝ) 1, X (ηf ω t) = 0 := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        apply hVO N k univ X (ηf ω t)
        rw [Set.disjoint_left]
        intro x hx hxX
        exact Set.disjoint_left.1 hω (hsup t hx) ⟨t, ht, x, hxX, rfl⟩
      rw [intervalIntegral.integral_congr h0]
      simp
    -- (e) hence `spt Y ⊆ E` and `spt Y` is compact
    obtain ⟨h1, h2⟩ := Submission.rsd_cmr_support_subset_of_vanish (N + 1) (k + 1) univ _ Y
      isOpen_univ hEc (subset_univ _) hvan
    exact ⟨h2, h1⟩
  · rw [hY ω, hLω, huniq ω η hη]
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

/-- **Two-sided Hausdorff comparison on a bi-Lipschitz piece**: let `G : ℝⁿ → ℝᴾ` be
`L`-Lipschitz and `m > 0` with `m|a − a'| ≤ |G a − G a'|` on `A`.  Then for every `Z ⊆ A`,
`mⁿ λ(Z) ≤ Hⁿ(G(Z)) ≤ Lⁿ λ(Z)`.
`Hⁿ = λ` on `ℝⁿ`, and a `K`-Lipschitz map scales `Hⁿ` by at most `Kⁿ` (Simon Ch. 2, 1.8(i)).
The upper bound applies this to `G`.  For the lower bound, `G` is injective on `A`, and
`g := invFunOn G A` is `m⁻¹`-Lipschitz on `G(Z)` with `g(G(Z)) = Z`, so `λ(Z) ≤ m⁻ⁿ Hⁿ(G(Z))`. -/
theorem Submission.dimred_mbl_dt_lpip_bilipschitz_measure_bounds : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L G → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → ∀ Z : Set (Euclid n), Z ⊆ A → ENNReal.ofReal m ^ n * volume Z ≤ μHE[n] (G '' Z) ∧ μHE[n] (G '' Z) ≤ (L : ℝ≥0∞) ^ n * volume Z := by
  intro P n G A L m hG hm hcolip Z hZA
  -- `Hⁿ = λ` on `ℝⁿ`
  have hvol : (μHE[n] : Measure (Euclid n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  refine ⟨?_, ?_⟩
  · -- `G` is injective on `A`, with left inverse `g := invFunOn G A`
    have hinjOn : InjOn G A := by
      intro a ha a' ha' hGa
      have h := hcolip a ha a' ha'
      rw [hGa, sub_self, norm_zero] at h
      have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hm
      exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
    have hleft : LeftInvOn (invFunOn G A) G A := hinjOn.leftInvOn_invFunOn
    have hgZ : invFunOn G A '' (G '' Z) = Z := by
      rw [image_image]
      exact (image_congr fun a ha => hleft (hZA ha)).trans (image_id' Z)
    -- `g` is `m⁻¹`-Lipschitz on `G(Z)`
    have hgLip : LipschitzOnWith (Real.toNNReal m⁻¹) (invFunOn G A) (G '' Z) := by
      refine LipschitzOnWith.of_dist_le_mul ?_
      rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      rw [hleft (hZA ha), hleft (hZA ha'), Real.coe_toNNReal _ (inv_nonneg.2 hm.le),
        dist_eq_norm, dist_eq_norm, le_inv_mul_iff₀ hm]
      exact hcolip a (hZA ha) a' (hZA ha')
    -- `λ(Z) = Hⁿ(g(G(Z))) ≤ m⁻ⁿ Hⁿ(G(Z))`
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hgLip
    rw [hgZ, hvol] at h
    have hone : ENNReal.ofReal m * (Real.toNNReal m⁻¹ : ℝ≥0∞) = 1 := by
      rw [← ENNReal.ofReal.eq_def, ← ENNReal.ofReal_mul hm.le, mul_inv_cancel₀ hm.ne',
        ENNReal.ofReal_one]
    calc ENNReal.ofReal m ^ n * volume Z
        ≤ ENNReal.ofReal m ^ n * ((Real.toNNReal m⁻¹ : ℝ≥0∞) ^ n * μHE[n] (G '' Z)) := by
          gcongr
      _ = (ENNReal.ofReal m * (Real.toNNReal m⁻¹ : ℝ≥0∞)) ^ n * μHE[n] (G '' Z) := by
          rw [mul_pow, mul_assoc]
      _ = μHE[n] (G '' Z) := by rw [hone, one_pow, one_mul]
  · -- `Hⁿ(G(Z)) ≤ Lⁿ Hⁿ(Z) = Lⁿ λ(Z)`
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hG.lipschitzOnWith (s := Z))
    rwa [hvol] at h
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
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
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable
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

/-- Step 4(d) of the local unit representation of `∂[[E]]` (Simon 7.5; Gram–Schmidt as in the
graph chart): if `a₁, …, aₙ` are linearly independent in `ℝᴾ`, the Gram determinant
`Γ = det(⟨aᵢ, aⱼ⟩)` is positive and `ξ = Γ^{-1/2} a₁ ∧ ⋯ ∧ aₙ`, i.e.
`⟨α, ξ⟩ = Γ^{-1/2} α(a₁, …, aₙ)`, is a unit orientation of `span a`.  For an orthonormal frame
`σ` of `span a` and `R = (⟨σᵢ, aⱼ⟩)`, `Γ = (det R)²` and `α(a) = det R · α(σ)`, so
`ξ = sign(det R) σ₁ ∧ ⋯ ∧ σₙ`. -/
theorem Submission.codim1_lur_normalized_wedge_orientation : ∀ (P n : ℕ) (a : Fin n → Euclid P), LinearIndependent ℝ a → 0 < Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i) (a j)) ∧ ∀ ξ : MultiVector P n, (∀ α : Covector (Euclid P) n, ξ α = (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i) (a j))))⁻¹ * α a) → IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range a)) := by
  intro P n a ha
  -- an orthonormal frame `σ` of `span a` with `Γ = (det R)²`, `R = (⟨σᵢ, aⱼ⟩)` invertible
  obtain ⟨σ, hσ, hspan, hgram, hdet, -⟩ :=
    Submission.dpf_exists_orthonormal_frame_det_gram P n a ha
  set d := Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (a j))
  refine ⟨hgram ▸ sq_pos_of_ne_zero hdet, fun ξ hξ => ⟨σ, hσ, hspan, ?_⟩⟩
  -- `α(a) = det R · α(σ)`, hence `⟨α, ξ⟩ = |det R|⁻¹ det R · α(σ)`
  have hξ' : ∀ α : Covector (Euclid P) n, ξ α = |d|⁻¹ * d * α σ := fun α => by
    rw [hξ, hgram, Real.sqrt_sq_eq_abs, mul_assoc,
      Submission.dgoj_covector_eq_det_mul_of_mem_span P n σ a hσ
        (fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩) α]
  rcases hdet.lt_or_gt with hneg | hpos
  · exact Or.inr fun α => by
      rw [hξ', abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hdet, neg_one_mul]
  · exact Or.inl fun α => by
      rw [hξ', abs_of_pos hpos, inv_mul_cancel₀ hdet, one_mul]
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

/-- The cylinder over an integer multiplicity representation: for `R = (M, θ, ξ)` in `ℝᴺ` with
`∫_M θ dHⁿ < ∞`, `Ψ(t, x) = (t, x)`, `J v = (0, v)` and `e₀ = (1, 0)`, the triple
`(Ψ((0, 1) × M), θ ∘ tail, ξ(tail ·)(α ↦ α(e₀, J ·)))` is an integer multiplicity
representation in `ℝ^{N+1}` (the current `[[0, 1]] × τ(M, θ, ξ)`).  `θ ≥ 1` on `M` gives
`Hⁿ(M) < ∞`; `ξ` is replaced by a strongly measurable version; `Hⁿ⌞M`-a.e. properties of `x` hold
at `H^{n+1}`-a.e. point `Ψ(t, x)` of the cylinder by the product-null lemma; local integrability
follows from the product formula and the orientation condition from the approximate tangent
planes `span(e₀, J(TₓM))` of the cylinder. -/
theorem Submission.dimred_mbl_dt_lp_imc_cylinder_imrep : ∀ (N n : ℕ) (R : IMRep (univ : Set (Euclid N)) n), ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ → ∃ R' : IMRep (univ : Set (Euclid (N + 1))) (n + 1), R'.carrier = (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier) ∧ (∀ (t : ℝ) (x : Euclid N), R'.mult (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = R.mult x) ∧ ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ (t : ℝ) (α : Covector (Euclid (N + 1)) (n + 1)) (β : Covector (Euclid N) n), (∀ v : Fin n → Euclid N, β v = α (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → R'.orient (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) α = R.orient x β := by
  have hPN := @Submission.dimred_mbl_dt_lp_imc_product_null
  have hCM := @Submission.dimred_mbl_dt_lp_imc_cylinder_measure
  have hCT := @Submission.dimred_mbl_dt_lp_imc_cylinder_tangent
  have hOR := @Submission.dimred_mbl_dt_lp_imc_orientation
  have hRC := @Submission.dimred_mbl_dt_lp_imc_cylinder_rectifiable
  intro N n R hint
  -- Step 1: `Hⁿ(M) ≤ ∫_M θ dHⁿ < ∞`, since `θ ≥ 1` on `M`
  have hMmeas := R.measurableSet_carrier
  have hMfin : μHE[n] R.carrier ≠ ∞ := by
    refine ne_top_of_le_ne_top hint ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono ((measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp
      R.measurable_mult) fun x hx => Nat.one_le_cast.mpr (R.mult_pos x hx)
  -- `Ψ(t, x) = (t, x)` is a continuous injection, hence a measurable embedding
  set Ψ : ℝ × Euclid N → Euclid (N + 1) :=
    fun p => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))
  have hΨc : Continuous Ψ := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin (N + 1) => ℝ)).comp (continuous_pi fun i => ?_)
    induction i using Fin.cases with
    | zero => simpa using continuous_fst
    | succ j =>
      simp only [Fin.cons_succ]
      exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) j).comp continuous_snd
  have hΨi : Injective Ψ := by
    rintro ⟨t, x⟩ ⟨t', x'⟩ h
    have h' : (Fin.cons t (WithLp.ofLp x) : Fin (N + 1) → ℝ) = Fin.cons t' (WithLp.ofLp x') :=
      congrArg WithLp.ofLp h
    obtain ⟨rfl, h2⟩ := Fin.cons_injective2 h'
    have hx : x = x' := by simpa using congrArg (WithLp.toLp 2) h2
    rw [hx]
  have hΨemb : MeasurableEmbedding Ψ := hΨc.measurableEmbedding hΨi
  have hCmeas : MeasurableSet (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier)) :=
    hΨemb.measurableSet_image.mpr (measurableSet_Ioo.prod hMmeas)
  -- the projection `tail(y) = (y₁, …, y_N)`, a left inverse of `Ψ(t, ·)`
  obtain ⟨tl, htlc, htl⟩ : ∃ tl : Euclid (N + 1) → Euclid N, Continuous tl ∧
      ∀ (t : ℝ) (x : Euclid N), tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x :=
    ⟨fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)),
      (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp
        (continuous_pi fun j => PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) j.succ),
      fun t x => by simp⟩
  have htlΨ : ∀ p : ℝ × Euclid N, tl (Ψ p) = p.2 := fun p => htl p.1 p.2
  -- Step 2: a strongly measurable version `ξ'` of `ξ`
  obtain ⟨ξ', hξ'sm, hξ'eq⟩ : ∃ ξ' : Euclid N → MultiVector N n, StronglyMeasurable ξ' ∧
      R.orient =ᵐ[μHE[n].restrict R.carrier] ξ' :=
    ⟨_, R.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      R.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 3: `L₁ α = (α.curryLeft e₀) ∘ J`, continuous linear in `α`
  let Jl : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := fun v w => by
        ext i
        induction i using Fin.cases <;> simp
      map_smul' := fun c v => by
        ext i
        induction i using Fin.cases <;> simp }
  let L₁ : Covector (Euclid (N + 1)) (n + 1) →L[ℝ] Covector (Euclid N) n :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM Jl).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) n)
        (EuclideanSpace.single 0 1)).comp
          ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap)
  have hK : ∀ (α : Covector (Euclid (N + 1)) (n + 1)) (β : Covector (Euclid N) n),
      (∀ v : Fin n → Euclid N, β v = α (Fin.cons (EuclideanSpace.single 0 1)
        (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → L₁ α = β := by
    intro α β h
    ext v
    rw [h v]
    rfl
  -- Step 4: an `Hⁿ⌞M`-a.e. property of `x` holds `H^{n+1}⌞M̃`-a.e. at `y = Ψ(t, x)`
  have hT : ∀ P : Euclid N → Prop, (∀ᵐ x ∂(μHE[n].restrict R.carrier), P x) →
      ∀ᵐ y ∂(μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier))),
        ∀ (t : ℝ) (x : Euclid N), y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) → P x := by
    intro P hP
    rw [ae_restrict_iff' hMmeas] at hP
    have hnull := hPN N n _ (ae_iff.mp hP)
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull),
      ae_restrict_mem hCmeas] with y hy hyC t x hyx
    obtain ⟨⟨t', x'⟩, ⟨-, hx'⟩, hy'⟩ := hyC
    have hxx : x' = x := congrArg Prod.snd (@hΨi (t', x') (t, x) (hy'.trans hyx))
    rw [hxx] at hx'
    by_contra hPx
    exact hy ⟨(t, x), ⟨mem_univ _, fun h => hPx (h hx')⟩, hyx.symm⟩
  -- Step 5: the fields of `R'`
  have hint' : ∫⁻ y in Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier), (R.mult (tl y) : ℝ≥0∞) ∂μHE[n + 1] =
      ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    have : IsFiniteMeasure (μHE[n].restrict R.carrier) := isFiniteMeasure_restrict.mpr hMfin
    have hm : Measurable fun y => (R.mult (tl y) : ℝ≥0∞) :=
      (measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp
        (R.measurable_mult.comp htlc.measurable)
    have hCM' : Measure.map Ψ (((volume : Measure ℝ).restrict (Ioo 0 1)).prod
        (μHE[n].restrict R.carrier)) = μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier)) :=
      hCM N n R.carrier hMmeas R.rectifiable hMfin
    rw [← hCM', lintegral_map hm hΨc.measurable,
      lintegral_prod (fun p => (R.mult (tl (Ψ p)) : ℝ≥0∞)) (hm.comp hΨc.measurable).aemeasurable]
    simp only [htlΨ, lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_one, mul_one]
  have hfin' :
      ∫⁻ y in Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier), (R.mult (tl y) : ℝ≥0∞) ∂μHE[n + 1] ≠ ∞ := by
    rw [hint']
    exact hint
  have hmult_pos : ∀ y ∈ Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier), 0 < R.mult (tl y) := by
    rintro y ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩
    rw [htlΨ]
    exact R.mult_pos x hx
  have hcont : Continuous fun φ : MultiVector N n => φ.comp L₁ :=
    continuous_id.clm_comp continuous_const
  have hsm : AEStronglyMeasurable (fun y => (ξ' (tl y)).comp L₁)
      (μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier))) :=
    (hcont.comp_stronglyMeasurable (hξ'sm.comp_measurable htlc.measurable)).aestronglyMeasurable
  have horients : ∀ᵐ y ∂(μHE[n + 1].restrict (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier))),
      ∃ Q : Submodule ℝ (Euclid (N + 1)),
        HasApproximateTangentSpaceAt (n + 1) (Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier)) y Q ∧
          IsUnitOrientationOf ((ξ' (tl y)).comp L₁) Q := by
    filter_upwards [hT _ R.orients, hT (fun x => R.orient x = ξ' x) hξ'eq,
      hCT N n R.carrier hMmeas R.rectifiable hMfin, ae_restrict_mem hCmeas] with y h1 h2 h3 hy
    obtain ⟨⟨t, x⟩, -, rfl⟩ := hy
    obtain ⟨Q, hQt, hQo⟩ := h1 t x rfl
    refine ⟨_, h3 t x rfl Q hQt, hOR N n (R.orient x) ((ξ' (tl (Ψ (t, x)))).comp L₁) Q hQo
      fun α β hαβ => ?_⟩
    show ξ' (tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) (L₁ α) = R.orient x β
    rw [htl, ← h2 t x rfl, hK α β hαβ]
  -- Step 6: `R' = (M̃, θ ∘ tail, ξ'(tail ·) ∘ L₁)`
  refine ⟨⟨Ψ '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier), fun y => R.mult (tl y),
    fun y => (ξ' (tl y)).comp L₁, hCmeas, subset_univ _, hRC N n _ _ R.rectifiable,
    R.measurable_mult.comp htlc.measurable, hmult_pos,
    fun K _ _ => ne_top_of_le_ne_top hfin' (lintegral_mono_set inter_subset_left), hsm,
    horients⟩, rfl, fun t x => congrArg R.mult (htl t x), ?_⟩
  filter_upwards [hξ'eq] with x hx t α β hαβ
  show ξ' (tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) (L₁ α) = R.orient x β
  rw [htl, ← hx, hK α β hαβ]
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

/-- **Simon 6.1.8** (the pull-back estimate behind the mass bound of Lemma 6.2.29): for a linear
map `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β` on `ℝᴺ'`, the pull-back `A^#β = β(A ·, …, A ·)` satisfies
`|A^#β|_E ≤ ‖A‖ᵏ |β|_E`.  With the standard bases `e`, `e'` and `S_b(γ) = Σ_j γ(b ∘ j)²` over all
`j : Fin m → Fin P`, induction on the degree `m` gives `S_e(A^#γ) ≤ ‖A‖^{2m} S_{e'}(γ)`: split
`j = Fin.cons a j'`, use `ι_x(A^#γ) = A^#(ι_{Ax}γ)` (`ι_x = curryLeft x`) and the induction
hypothesis for `ι_{Ae_a}γ`, then the one-slot estimate
`Σ_a μ(Ae_a)² = ‖μ ∘ A‖² ≤ ‖A‖² ‖μ‖² = ‖A‖² Σ_b μ(e'_b)²` (Parseval for functionals) for
`μ(u) = (ι_u γ)(e' ∘ j')`.  Finally `S_e(A^#β) = k! |A^#β|_E²` and `S_{e'}(β) = k! |β|_E²`
(`regcomp_covector_sq_sum_orthonormalBasis`). -/
theorem Submission.dimred_mbl_dt_lp_cb_pullback_le : ∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β := by
  intro N N' k A β
  -- Parseval for functionals: `Σ_a μ(b_a)² = ‖g‖² = ‖μ‖²` for the Riesz vector `g` of `μ`
  have hpars : ∀ (M : ℕ) (b : OrthonormalBasis (Fin M) ℝ (Euclid M)) (μ : Euclid M →L[ℝ] ℝ),
      ∑ a, (μ (b a)) ^ 2 = ‖μ‖ ^ 2 := by
    intro M b μ
    obtain ⟨g, hg, hgn⟩ : ∃ g : Euclid M, (∀ x, μ x = inner ℝ g x) ∧ ‖g‖ = ‖μ‖ :=
      ⟨(InnerProductSpace.toDual ℝ (Euclid M)).symm μ,
        fun x => InnerProductSpace.toDual_symm_apply.symm,
        (InnerProductSpace.toDual ℝ (Euclid M)).symm.norm_map μ⟩
    rw [← hgn, ← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner g g]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg, sq, real_inner_comm g (b a)]
  -- the standard orthonormal bases `e` of `ℝᴺ` and `e'` of `ℝᴺ'`
  have e : OrthonormalBasis (Fin N) ℝ (Euclid N) := EuclideanSpace.basisFun (Fin N) ℝ
  have e' : OrthonormalBasis (Fin N') ℝ (Euclid N') := EuclideanSpace.basisFun (Fin N') ℝ
  -- one-slot estimate: `Σ_a μ(Ae_a)² = ‖μ ∘ A‖² ≤ ‖A‖² ‖μ‖² = ‖A‖² Σ_b μ(e'_b)²`
  have hone : ∀ μ : Euclid N' →L[ℝ] ℝ,
      ∑ a, (μ (A (e a))) ^ 2 ≤ ‖A‖ ^ 2 * ∑ b, (μ (e' b)) ^ 2 := fun μ =>
    calc ∑ a, (μ (A (e a))) ^ 2 = ‖μ.comp A‖ ^ 2 := hpars N e (μ.comp A)
      _ ≤ (‖μ‖ * ‖A‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (μ.opNorm_comp_le A) 2
      _ = ‖A‖ ^ 2 * ∑ b, (μ (e' b)) ^ 2 := by rw [hpars N' e' μ]; ring
  -- first-slot splitting `J = Fin.cons a j` of the index tuples
  have hcons : ∀ (M m : ℕ) (F : (Fin (m + 1) → Fin M) → ℝ),
      ∑ J : Fin (m + 1) → Fin M, F J = ∑ a : Fin M, ∑ j : Fin m → Fin M, F (Fin.cons a j) := by
    intro M m F
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin M) _ _ fun _ => rfl).symm
  -- `γ(b ∘ Fin.cons a j) = (ι_{b_a} γ)(b ∘ j)` for the interior product `ι_x = curryLeft x`
  have hcurry : ∀ (M m : ℕ) (γ : Covector (Euclid M) (m + 1)) (b : Fin M → Euclid M) (a : Fin M)
      (j : Fin m → Fin M),
      γ (fun i => b ((Fin.cons a j : Fin (m + 1) → Fin M) i)) =
        γ.curryLeft (b a) (fun i => b (j i)) := by
    intro M m γ b a j
    rw [ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- `S_e(A^#γ) ≤ ‖A‖^{2m} S_{e'}(γ)` for every `m`-covector `γ`, by induction on `m`
  have hHS : ∀ (m : ℕ) (γ : Covector (Euclid N') m),
      ∑ j : Fin m → Fin N, (γ.compContinuousLinearMap A (fun i => e (j i))) ^ 2 ≤
        (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N', (γ (fun i => e' (j i))) ^ 2 := by
    intro m
    induction m with
    | zero =>
      -- both sums consist of the single term `γ(∅)²`
      intro γ
      rw [pow_zero, one_mul, Fintype.sum_unique, Fintype.sum_unique,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact le_of_eq (congrArg (· ^ 2) (congrArg γ (Subsingleton.elim _ _)))
    | succ m ih =>
      intro γ
      calc ∑ j : Fin (m + 1) → Fin N, (γ.compContinuousLinearMap A (fun i => e (j i))) ^ 2
          = ∑ a, ∑ j : Fin m → Fin N,
              ((γ.curryLeft (A (e a))).compContinuousLinearMap A (fun i => e (j i))) ^ 2 := by
            rw [hcons]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hcurry, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap]
        _ ≤ ∑ a, (‖A‖ ^ 2) ^ m *
              ∑ j : Fin m → Fin N', (γ.curryLeft (A (e a)) (fun i => e' (j i))) ^ 2 :=
            Finset.sum_le_sum fun a _ => ih _
        _ = (‖A‖ ^ 2) ^ m *
              ∑ j : Fin m → Fin N', ∑ a, (γ.curryLeft (A (e a)) (fun i => e' (j i))) ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N',
              ‖A‖ ^ 2 * ∑ b, (γ.curryLeft (e' b) (fun i => e' (j i))) ^ 2 := by
            -- the one-slot estimate for `μ(u) = (ι_u γ)(e' ∘ j)`
            gcongr with j
            exact hone ((ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ
              (fun i => e' (j i))).comp γ.curryLeft)
        _ = (‖A‖ ^ 2) ^ (m + 1) * ∑ j : Fin (m + 1) → Fin N', (γ (fun i => e' (j i))) ^ 2 := by
            rw [hcons, Finset.sum_comm, ← Finset.mul_sum, ← mul_assoc, ← pow_succ]
            congr 1
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hcurry]
  -- `k! |A^#β|_E² = S_e(A^#β) ≤ ‖A‖^{2k} S_{e'}(β) = ‖A‖^{2k} k! |β|_E²`; cancel `k!`
  have h := hHS k β
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis N k _ e,
    Submission.regcomp_covector_sq_sum_orthonormalBasis N' k β e',
    mul_left_comm ((‖A‖ ^ 2) ^ k)] at h
  have hsq : covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2 ≤
      (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 :=
    calc covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2
        ≤ (‖A‖ ^ 2) ^ k * covectorEuclideanNorm β ^ 2 :=
          le_of_mul_le_mul_left h (by exact_mod_cast Nat.factorial_pos k)
      _ = (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (pow_nonneg (norm_nonneg A) k) (covectorEuclideanNorm_nonneg β)) two_ne_zero).mp hsq
/-- **Interior product bound for the Euclidean coefficient norm** (Simon 6.1): for `v ∈ ℝᴺ` and a
`(k+1)`-covector `β` on `ℝᴺ`, the interior product `ι_v β = β.curryLeft v`,
`ι_v β(w₁, …, w_k) = β(v, w₁, …, w_k)`, satisfies `|ι_v β|_E ≤ ‖v‖ |β|_E`.  By homogeneity it
suffices to treat `u = v / ‖v‖ = f_{i₀}` for an orthonormal basis `f` of `ℝᴺ`.  The position sums
`R_p = Σ_{J(p) = i₀} β(f ∘ J)²` all equal `R_0 = k! |ι_u β|_E²` (transpose `0 ↔ p`), and
`Σ_p R_p ≤ Σ_J β(f ∘ J)² = (k+1)! |β|_E²` because tuples with `i₀` in two slots vanish
(`regcomp_covector_sq_sum_orthonormalBasis` evaluates both sums). -/
theorem Submission.dimred_mbl_dt_lp_cb_curryLeft_le : ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
  intro N k v β
  classical
  -- the case `v = 0`
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- homogeneity: `|c γ|_E = |c| |γ|_E`
  have hhom : ∀ (c : ℝ) (γ : Covector (Euclid N) k),
      covectorEuclideanNorm (c • γ) = |c| * covectorEuclideanNorm γ := by
    intro c γ
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  -- `N ≥ 1` as `ℝ⁰ = {0}`; an orthonormal basis `f` of `ℝᴺ` with `f i₀ = ‖v‖⁻¹ v`
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => hv (by subst h; exact Subsingleton.elim v 0)
  set i₀ : Fin N := ⟨0, hN⟩
  obtain ⟨f, hf⟩ : ∃ f : OrthonormalBasis (Fin N) ℝ (Euclid N), f i₀ = ‖v‖⁻¹ • v := by
    have hon : Orthonormal ℝ (({i₀} : Set (Fin N)).domRestrict fun _ => ‖v‖⁻¹ • v) := by
      refine ⟨fun _ => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
      rw [Set.domRestrict_apply, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
    exact ⟨b, hb i₀ rfl⟩
  -- `|ι_v β|_E = ‖v‖ |ι_{f i₀} β|_E`, so it suffices to show `|ι_{f i₀} β|_E ≤ |β|_E`
  have hvu : β.curryLeft v = ‖v‖ • β.curryLeft (f i₀) := by
    rw [hf, map_smul, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  rw [hvu, hhom, abs_of_pos hvpos]
  refine mul_le_mul_of_nonneg_left ?_ hvpos.le
  -- `g J = β(f ∘ J)²` and the position sums `R p = Σ_{J p = i₀} g J`
  set g : (Fin (k + 1) → Fin N) → ℝ := fun J => (β fun t => f (J t)) ^ 2 with hg
  set R : Fin (k + 1) → ℝ := fun p => ∑ J, if J p = i₀ then g J else 0 with hR
  -- `R 0 = Σ_j (ι_{f i₀} β)(f ∘ j)² = k! |ι_{f i₀} β|_E²` (reindex `J = Fin.cons a j`)
  have hR0 : R 0 = (k.factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2 := by
    rw [← Submission.regcomp_covector_sq_sum_orthonormalBasis N k (β.curryLeft (f i₀)) f]
    simp only [hR]
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin N).sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single i₀]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.consEquiv_apply, Fin.cons_zero, ↓reduceIte, hg]
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext t
      refine Fin.cases ?_ (fun s => ?_) t <;> simp
    · intro a _ ha
      exact Finset.sum_eq_zero fun j _ => by simp [ha]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  -- `R p = R 0`: reindex `J ↦ J ∘ (0 p)`, and `β(f ∘ J ∘ (0 p)) = ±β(f ∘ J)`
  have hRp : ∀ p, R p = R 0 := by
    intro p
    simp only [hR]
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N))) _ _
      fun J => ?_
    have hJ : ∀ t, Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N)) J t =
        J (Equiv.swap 0 p t) := fun t => by
      simp [Equiv.arrowCongr_apply]
    have hperm : β (fun t => f (J (Equiv.swap 0 p t))) =
        Equiv.Perm.sign (Equiv.swap 0 p) • β (fun t => f (J t)) :=
      β.toAlternatingMap.map_perm (fun t => f (J t)) (Equiv.swap 0 p)
    have hgJ : g (Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N)) J) = g J := by
      simp only [hg, hJ, hperm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (k + 1)) p)) with h | h <;>
        simp [h]
    rw [hgJ, hJ, Equiv.swap_apply_left]
  -- `Σ_p R p ≤ Σ_J g J`: a tuple `J` with `i₀` in two slots has `β(f ∘ J) = 0`
  have hsum : ∑ p, R p ≤ ∑ J, g J := by
    simp only [hR]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun J _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    by_cases h : (Finset.univ.filter fun p => J p = i₀).card ≤ 1
    · exact mul_le_of_le_one_left (sq_nonneg _) (by exact_mod_cast h)
    · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (not_le.mp h)
      rw [Finset.mem_filter] at hp hq
      have h0 : β (fun t => f (J t)) = 0 :=
        β.map_eq_zero_of_eq _ (by rw [hp.2, hq.2]) hpq
      simp [hg, h0]
  -- `(k+1)! |ι_{f i₀} β|_E² = Σ_p R p ≤ Σ_J g J = (k+1)! |β|_E²`
  have key : ((k + 1).factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2 ≤
      ((k + 1).factorial : ℝ) * covectorEuclideanNorm β ^ 2 :=
    calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2
        = ∑ p, R p := by
          rw [Finset.sum_congr rfl fun p _ => hRp p, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, hR0, Nat.factorial_succ]
          push_cast
          ring
      _ ≤ ∑ J, g J := hsum
      _ = ((k + 1).factorial : ℝ) * covectorEuclideanNorm β ^ 2 := by
          simp only [hg]
          exact Submission.regcomp_covector_sq_sum_orthonormalBasis N (k + 1) β f
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _) (covectorEuclideanNorm_nonneg _)
    two_ne_zero).mp (le_of_mul_le_mul_left key (by exact_mod_cast Nat.factorial_pos _))

/-- **Covector bounds for the Lipschitz push-forward** (Simon 6.1, (L1)–(L2)): the pull-back
estimate `|A^#β|_E ≤ ‖A‖ᵏ |β|_E` for a linear map `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β` on `ℝᴺ'`
(Simon 6.1.8, `dimred_mbl_dt_lp_cb_pullback_le`), and the interior product estimate
`|ι_v β|_E ≤ ‖v‖ |β|_E` for `v ∈ ℝᴺ` and a `(k+1)`-covector `β` on `ℝᴺ`
(`dimred_mbl_dt_lp_cb_curryLeft_le`). -/
theorem Submission.dimred_mbl_dt_lp_covector_bounds : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
  exact ⟨Submission.dimred_mbl_dt_lp_cb_pullback_le, Submission.dimred_mbl_dt_lp_cb_curryLeft_le⟩
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]

/-- **The cylinder operator `X ↦ [[(0, 1)]] × X`** (Simon Ch. 6, 2.17–2.22, in the `t`-integral
form of the homotopy formula 2.25; the product used for the Lipschitz push-forward in the
deformation theorem).  Write `ι(t, x) = (t, x)`, `e₀ = (1, 0, …, 0)` and `Jv = ι(0, v)`.  For
`M(X) < ∞`, `cyl(X)(ω) = ∫₀¹ X(η^ω_t) dt` with `η^ω_t(x)(v) = ω(ι(t, x))(e₀, Jv)` is a current
with `M(cyl X) ≤ M(X)` and, for compact `spt X`, compact support in `ι([0, 1] × spt X)`
(`Submission.dimred_mbl_dt_lpc_cylinder_current`); this gives (C3), and (C2) follows from
`M(X − Y) ≤ M(X) + M(Y)`.  The coordinate formula for `d` gives `η^{dω}_t = ∂_tβ^ω_t − d(η^ω_t)`
for `β^ω_s(x) = ω(ι(s, x)) ∘ J`, and Fubini with the fundamental theorem of calculus gives
`∫₀¹ X(∂_tβ^ω_t) dt = X(β^ω_1) − X(β^ω_0)`.  Hence (C4), (C5) and, for `|ω| ≤ 1`,
`∂cyl(X)(ω) ≤ 2M(X) + M(∂X)`, so `M(∂cyl X) < ∞`. -/
theorem Submission.dimred_mbl_dt_lp_cylinder : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∃ cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass ≤ X.mass ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) ∧ (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N 0 X).boundary ω = X η₁ - X η₀) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N (k + 1) X).boundary ω = X η₁ - X η₀ - cyl N k X.boundary ω := by
  intro hVO hREP
  have hCB := Submission.dimred_mbl_dt_lp_covector_bounds
  classical
  -- Step 1: slice families `η^ω_t`, restriction families `β^ω_s` and their `t`-derivatives
  -- `∂_tβ^ω_t`, with `|β^ω_s(x)| ≤ |ω(ι(s, x))|` (0(e))
  have hS := Submission.dimred_mbl_dt_lpc_slice_forms hCB
  -- Steps 2 and 4: for `M(X) < ∞`, `cyl(X)(ω) = ∫₀¹ X(η^ω_t) dt` is a current with
  -- `M(cyl X) ≤ M(X)`; if `spt X` is compact, `spt cyl(X)` is a compact subset of
  -- `ι([0, 1] × spt X)`
  choose! cyl hmass hsupp hint using Submission.dimred_mbl_dt_lpc_cylinder_current hCB hVO
  -- 0(b): `|X(β^ω_s)| ≤ M(X)` when `|ω| ≤ 1`
  have hβbd : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), X.mass < ∞ →
      ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) k,
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k) y) ≤ 1) →
      ∀ β : ℝ → TestFormOn (univ : Set (Euclid N)) k,
      (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N),
        (β s : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      ∀ s, |X (β s)| ≤ X.mass.toReal := by
    intro N k X hX ω hω β hβ s
    have h := Submission.cmc_fc_sc_abs_le_mul_mass N k univ X (β s) 1 one_pos hX.ne
      fun x => ((hS.2 N k ω).2.2 β hβ s x).trans (hω _)
    rwa [one_mul] at h
  -- Step 5, degree `0`: `η^{dω}_t = ∂_tβ^ω_t`, so by Fubini and the fundamental theorem of
  -- calculus `∂cyl(X)(ω) = cyl(X)(dω) = ∫₀¹ X(∂_tβ^ω_t) dt = X(β^ω_1) − X(β^ω_0)`
  have hB₀ : ∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), X.mass < ∞ →
      ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) 0)
        (β : ℝ → TestFormOn (univ : Set (Euclid N)) 0),
      (∀ (s : ℝ) (x : Euclid N) (v : Fin 0 → Euclid N),
        (β s : DifferentialForm (Euclid N) 0) x v =
          (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      (cyl N 0 X).boundary ω = X (β 1) - X (β 0) := by
    intro N X hX ω β hβ
    obtain ⟨-, ⟨γ, hγ⟩, -⟩ := hS.2 N 0 ω
    have hγd : ∀ (t : ℝ) (x : Euclid N) (v : Fin 0 → Euclid N),
        (γ t : DifferentialForm (Euclid N) 0) x v =
          (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 ω :
            DifferentialForm (Euclid (N + 1)) (0 + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
      intro t x v
      rw [hγ t x v]
      exact (Submission.dimred_mbl_dt_lpc_slice_extDeriv.2 N ω t x v).symm
    rw [GeometricCurrentOn.boundary_apply, (hint N 0 X hX _ γ hγd).2]
    exact Submission.dimred_mbl_dt_lpc_ftc_current hREP N 0 X hX ω β γ hβ hγ
  -- Step 5, degree `k + 1`: the coordinate formula for `d` gives
  -- `η^{dω}_t = ∂_tβ^ω_t − d(η^ω_t)` (*), and `X(dη^ω_t) = ∂X(η^ω_t)`, so
  -- `∂cyl(X)(ω) = ∫₀¹ X(∂_tβ^ω_t) dt − ∫₀¹ ∂X(η^ω_t) dt = X(β^ω_1) − X(β^ω_0) − cyl(∂X)(ω)`
  have hB : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), X.mass < ∞ →
      X.boundary.mass < ∞ → ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
        (β : ℝ → TestFormOn (univ : Set (Euclid N)) (k + 1)),
      (∀ (s : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N),
        (β s : DifferentialForm (Euclid N) (k + 1)) x v =
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      (cyl N (k + 1) X).boundary ω = X (β 1) - X (β 0) - cyl N k X.boundary ω := by
    intro N k X hX hbX ω β hβ
    obtain ⟨⟨η, hη⟩, -⟩ := hS.1 N k ω
    obtain ⟨-, ⟨γ, hγ⟩, -⟩ := hS.2 N (k + 1) ω
    have hηd : ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N),
        ((γ t - exteriorDerivativeTestOn (univ : Set (Euclid N)) k (η t) :
            TestFormOn (univ : Set (Euclid N)) (k + 1)) :
          DifferentialForm (Euclid N) (k + 1)) x v =
          (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) ω :
            DifferentialForm (Euclid (N + 1)) (k + 1 + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
      intro t x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
      rw [hγ t x v]
      exact (Submission.dimred_mbl_dt_lpc_slice_extDeriv.1 N k ω η hη t x v).symm
    obtain ⟨hc₁, h₁⟩ := hint N (k + 1) X hX _ _ hηd
    obtain ⟨hc₂, h₂⟩ := hint N k X.boundary hbX ω η hη
    have hsplit : ∀ t, X (γ t - exteriorDerivativeTestOn (univ : Set (Euclid N)) k (η t)) =
        X (γ t) - X.boundary (η t) := fun t => map_sub X.toCurrent _ _
    -- `t ↦ X(∂_tβ^ω_t) = X(η^{dω}_t) + ∂X(η^ω_t)` is continuous
    have hc₃ : Continuous fun t => X (γ t) := by
      have h : (fun t => X (γ t)) = fun t =>
          X (γ t - exteriorDerivativeTestOn (univ : Set (Euclid N)) k (η t)) +
            X.boundary (η t) := by
        funext t
        rw [hsplit t, sub_add_cancel]
      rw [h]
      exact hc₁.add hc₂
    rw [GeometricCurrentOn.boundary_apply, h₁, h₂]
    simp_rw [hsplit]
    rw [intervalIntegral.integral_sub (hc₃.intervalIntegrable 0 1) (hc₂.intervalIntegrable 0 1),
      Submission.dimred_mbl_dt_lpc_ftc_current hREP N (k + 1) X hX ω β γ hβ hγ]
  refine ⟨cyl, fun N k X hXc hX hbX => ?_, fun N k X Y hXc hX hbX hYc hY hbY => ?_,
    fun N k X hXc hX hbX ω => ?_, fun N X hXc hX ω => ?_, fun N k X hXc hX hbX ω => ?_⟩
  · -- (C1): steps 2 and 4; step 6: `∂cyl(X)(ω) ≤ 2M(X) + M(∂X)` for admissible `ω`
    obtain ⟨hc, hs⟩ := hsupp N k X hX hXc
    refine ⟨hc, hmass N k X hX, ?_, hs⟩
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid (N + 1))) k univ,
        (cyl N k X).boundary ω ≤ C := by
      rcases k with _ | k
      · refine ⟨2 * X.mass.toReal, fun ω hω => ?_⟩
        obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N 0 ω
        have h₁ := abs_le.mp (hβbd N 0 X hX ω hω.2 β hβ 1)
        have h₀ := abs_le.mp (hβbd N 0 X hX ω hω.2 β hβ 0)
        rw [hB₀ N X hX ω β hβ]
        linarith [h₁.2, h₀.1]
      · have hbX' : X.boundary.mass < ∞ := hbX
        refine ⟨2 * X.mass.toReal + X.boundary.mass.toReal, fun ω hω => ?_⟩
        obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N (k + 1) ω
        have h₁ := abs_le.mp (hβbd N (k + 1) X hX ω hω.2 β hβ 1)
        have h₀ := abs_le.mp (hβbd N (k + 1) X hX ω hω.2 β hβ 0)
        -- `|cyl(∂X)(ω)| ≤ M(cyl ∂X) ≤ M(∂X)`
        have hm := hmass N k X.boundary hbX'
        have h₂ := abs_le.mp (Submission.cmc_fc_sc_abs_le_mul_mass (N + 1) (k + 1) univ
          (cyl N k X.boundary) ω 1 one_pos (ne_top_of_le_ne_top hbX'.ne hm) hω.2)
        have h₃ := ENNReal.toReal_mono hbX'.ne hm
        rw [hB N k X hX hbX' ω β hβ]
        linarith [h₁.2, h₀.1, h₂.1]
    calc (cyl N k X).boundary.mass ≤ ENNReal.ofReal C := by
          unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
          refine sSup_le ?_
          rintro _ ⟨ω, hω, rfl⟩
          exact ENNReal.ofReal_le_ofReal (hC ω hω)
      _ < ∞ := ENNReal.ofReal_lt_top
  · -- (C2), step 3: `M(X − Y) ≤ M(X) + M(Y) < ∞`, and the `t`-integrals are linear
    have hXY : (X - Y).mass < ∞ := lt_of_le_of_lt
      (Submission.cmc_fc_cs_massOn_sub_le N k univ univ X Y) (ENNReal.add_lt_top.mpr ⟨hX, hY⟩)
    ext ω
    obtain ⟨⟨η, hη⟩, -⟩ := hS.1 N k ω
    obtain ⟨hcX, hX'⟩ := hint N k X hX ω η hη
    obtain ⟨hcY, hY'⟩ := hint N k Y hY ω η hη
    change cyl N k (X - Y) ω = cyl N k X ω - cyl N k Y ω
    rw [(hint N k (X - Y) hXY ω η hη).2, hX', hY',
      ← intervalIntegral.integral_sub (hcX.intervalIntegrable 0 1) (hcY.intervalIntegrable 0 1)]
    rfl
  · -- (C3), step 2
    obtain ⟨⟨η, hη⟩, -⟩ := hS.1 N k ω
    exact ⟨η, hη, (hint N k X hX ω η hη).2⟩
  · -- (C4), step 5 with `η_s = β^ω_s`
    obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N 0 ω
    exact ⟨β 0, β 1, hβ 0, hβ 1, hB₀ N X hX ω β hβ⟩
  · -- (C5), step 5 with `η_s = β^ω_s`
    obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N (k + 1) ω
    exact ⟨β 0, β 1, hβ 0, hβ 1, hB N k X hX hbX ω β hβ⟩

/-- **Lipschitz push-forwards of normal currents and the product with `[[0, 1]]`** (Simon Ch. 6,
2.23–2.29, the operators behind the deformation theorem).  Assume (VO) and (REP).  `cyl` is the
product with `[[0, 1]]` of the sibling `dimred_mbl_dt_lp_cylinder`, with (C1)–(C5).  `lpush` comes
from `dimred_mbl_dt_lpo_lpush_construction`: for `Λ`-Lipschitz `F` and `X` with compact support and
finite mass and boundary mass, `lpush F X ω` is the limit (CHAR) of `X(ηⱼ)` whenever `C^∞` maps
`Fⱼ → F` uniformly on `spt X` with `‖DFⱼ‖` bounded there and `ηⱼ = Fⱼ^#ω` near `spt X`.  With the
covector bounds (L1), (L2) of `dimred_mbl_dt_lp_covector_bounds`, (CHAR) gives (1)–(6) by
`dimred_mbl_dt_lpo_lpush_properties`, and with (C1), (C3)–(C5) the homotopy formulas and mass bound
(10)–(12) by `dimred_mbl_dt_lpo_lipschitz_homotopy`.  (8), (9) are (C2), (C3), and (7) is (C1)
with `M(cyl X) ≤ M(X) < ∞`. -/
theorem Submission.dimred_mbl_dt_lp_pushforward_operators : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) ∧ (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP
  -- (L1), (L2) and the product with `[[0, 1]]`: `cyl` with (C1)–(C5)
  have hcov := Submission.dimred_mbl_dt_lp_covector_bounds
  obtain ⟨cyl, hC1, hC2, hC3, hC4, hC5⟩ := Submission.dimred_mbl_dt_lp_cylinder hVO hREP
  -- `lpush` with its characterization (CHAR) by smooth approximations and cut-off pull-backs
  obtain ⟨lpush, hchar⟩ :=
    Submission.dimred_mbl_dt_lpo_lpush_construction hVO hREP hcov cyl hC1 hC3 hC4 hC5
  -- (1)–(6) follow from (CHAR); (10)–(12) from (CHAR) and (C1), (C3)–(C5)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    Submission.dimred_mbl_dt_lpo_lpush_properties hVO hREP hcov lpush hchar
  obtain ⟨h10, h11, h12⟩ := Submission.dimred_mbl_dt_lpo_lipschitz_homotopy hVO hREP hcov lpush
    cyl hchar hC1 hC3 hC4 hC5
  refine ⟨lpush, cyl, h1, h2, h3, h4, h5, h6, ?_, hC2, hC3, h10, h11, h12⟩
  -- (7) is (C1), with `M(cyl X) ≤ M(X) < ∞`
  intro N k X hXc hXm hXb
  obtain ⟨hc, hm, hb, hs⟩ := hC1 N k X hXc hXm hXb
  exact ⟨hc, hm.trans_lt hXm, hb, hs⟩
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

/-- **An integer multiplicity triple carried by a Borel subset of a rectifiable set with tangent
data** (Simon Ch. 6, Definitions 3.1 and 4.4; for the slice `(M₊ ∩ f⁻¹(t), θ, ξ⌞ν)` take
`A = M₊ ∩ f⁻¹(t)` and `S = M ∩ f⁻¹(t)`).  Let `A ⊆ S ⊆ ℝᴾ` be Borel with `S` countably
`n`-rectifiable, `θ` Borel with `θ > 0` on `S` and `∫_{S ∩ K} θ dHⁿ < ∞` for compact `K`, and `ζ`
`Hⁿ⌞A`-measurable with `ζ(x)` a unit orientation of `TₓS` for `Hⁿ`-a.e. `x ∈ A`.  Then
`(A, θ, ζ)` is an `IMRep` in `ℝᴾ`.

`θ ≥ 1` on `S` makes `S` locally `Hⁿ`-finite, so tangent locality (`cmc_imRep_locality_restrict_sub`
(a) with `U = ℝᴾ`) gives `TₓA = TₓS` for `Hⁿ`-a.e. `x ∈ A`; rectifiability, positivity and local
integrability of `θ` pass from `S` to `A ⊆ S`. -/
theorem Submission.dtc_bc_lc_sl_sf_imrep_of_subset : ∀ (P n : ℕ) (A S : Set (Euclid P)) (θ : Euclid P → ℕ) (ζ : Euclid P → MultiVector P n), MeasurableSet A → MeasurableSet S → A ⊆ S → CountablyRectifiable n S → Measurable θ → (∀ x ∈ S, 0 < θ x) → (∀ K : Set (Euclid P), IsCompact K → ∫⁻ x in S ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞) → AEStronglyMeasurable ζ (μHE[n].restrict A) → (∀ᵐ x ∂(μHE[n].restrict A), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n S x Q ∧ IsUnitOrientationOf (ζ x) Q) → ∃ R : IMRep (univ : Set (Euclid P)) n, R.carrier = A ∧ R.mult = θ ∧ R.orient = ζ := by
  intro P n A S θ ζ hA hS hAS hrect hθ hpos hint hζ hor
  -- Step 1: `S` is locally `Hⁿ`-finite: `Hⁿ(S ∩ K) = ∫_{S ∩ K} 1 dHⁿ ≤ ∫_{S ∩ K} θ dHⁿ < ∞`
  have hSfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ → μHE[n] (S ∩ K) ≠ ∞ := by
    intro K hK _
    refine ne_top_of_le_ne_top (hint K hK) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (hS.inter hK.measurableSet) fun x hx => Nat.one_le_cast.2 (hpos x hx.1))
  -- Step 2: `TₓA = TₓS` for `Hⁿ`-a.e. `x ∈ A` (tangent locality, `U = ℝᴾ`, `M = A`, `M' = S`)
  have hloc := Submission.cmc_imRep_locality_restrict_sub.1 P n univ A S isOpen_univ hA hS hAS
    (subset_univ S) hSfin
  -- Step 3: `ζ(x)` orients `TₓA` for `Hⁿ`-a.e. `x ∈ A`
  have horA : ∀ᵐ x ∂(μHE[n].restrict A), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n A x Q ∧ IsUnitOrientationOf (ζ x) Q := by
    filter_upwards [hor, hloc] with x ⟨Q, hQ, hζQ⟩ hx
    exact ⟨Q, (hx Q).2 hQ, hζQ⟩
  -- Step 4: `∫_{A ∩ K} θ dHⁿ ≤ ∫_{S ∩ K} θ dHⁿ < ∞` for compact `K`, as `A ∩ K ⊆ S ∩ K`
  have hAint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in A ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := fun K hK _ =>
    ne_top_of_le_ne_top (hint K hK) (lintegral_mono_set (inter_subset_inter_left K hAS))
  -- Step 5: assemble `R = (A, θ, ζ)`; `A ⊆ S` is countably `n`-rectifiable and `θ > 0` on `A`
  exact ⟨IMRep.mk A θ ζ hA (subset_univ A) (hrect.mono hAS) hθ (fun x hx => hpos x (hAS hx))
    hAint hζ horA, rfl, rfl, rfl⟩
/-- **Simon Ch. 6, 3.4–3.5 and 3.7** (printed pp. 147–148), for one bi-Lipschitz piece `(G, A)` of
the carrier `M` of `R = τ(M, θ, ξ)`: `D₁G(u) ∧ ⋯ ∧ DₙG(u) = det(DᵢG(u) · τⱼ) τ₁ ∧ ⋯ ∧ τₙ` with
`|det(DᵢG(u) · τⱼ)| = J_G(u)`, so `J_G(u) ξ(G(u)) = ±D₁G(u) ∧ ⋯ ∧ DₙG(u)` for `λ`-a.e. `u ∈ A`,
with a measurable choice of the sign.  By `bilip_measure`, `Hⁿ`-null subsets of `G(A)` pull back to
`λ`-null subsets of `A`; `G(A)` has approximate tangent space `range DG(u)` at `G(u)`
(`piece_tangent`), hence so has `M` (locality (IMC)(a)), and `ξ(G(u))` orients it (`R.orients`,
uniqueness of `T_{G(u)}M`).  `J_G(u)⁻¹ D₁G(u) ∧ ⋯ ∧ DₙG(u)` is another unit orientation of
`range DG(u)` (`wedge_orientation`), so the two agree up to sign (`orientation_sign`). -/
theorem Submission.dimred_mbl_dt_lpip_piece_orientation_sign : ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → LipschitzWith L G → MeasurableSet A → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ R.carrier → ∃ s : Euclid n → ℤ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧ ∀ᵐ u ∂(volume.restrict A), ∀ α : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1)) (fderiv ℝ G u (EuclideanSpace.single b 1)))) * R.orient (G u) α = (s u : ℝ) * α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
  classical
  intro hIMC P n U R G A L m hU hG hA hm hbi hdiff hGA
  -- `G` is continuous and injective on `A`, so `G(A)` is Borel
  have hGc : Continuous G := hG.continuous
  have hinj : InjOn G A := by
    intro a ha a' ha' h
    have h1 := hbi a ha a' ha'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by rwa [mul_zero]) hm
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  have hYm : MeasurableSet (G '' A) := hA.image_of_continuousOn_injOn hGc.continuousOn hinj
  -- the carrier is locally `Hⁿ`-finite in `U`, since `θ ≥ 1` on it
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
        setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
          fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1)
  -- `bilip_measure`: `Hⁿ`-null subsets of `G(A)` pull back to `λ`-null subsets of `A`, so `G` is
  -- quasi-measure-preserving from `λ⌞A` to `Hⁿ⌞G(A)`
  have hnull : ∀ Z ⊆ A, μHE[n] (G '' Z) = 0 → volume Z = 0 := by
    intro Z hZ h0
    have h1 :=
      (Submission.dimred_mbl_dt_lpip_bilipschitz_measure_bounds P n G A L m hG hm hbi Z hZ).1
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (ENNReal.ofReal_pos.2 hm).ne')
  have hqmp : Measure.QuasiMeasurePreserving G (volume.restrict A) (μHE[n].restrict (G '' A)) := by
    refine ⟨hGc.measurable, Measure.AbsolutelyContinuous.mk fun T hT h0 => ?_⟩
    rw [Measure.restrict_apply hT] at h0
    rw [Measure.map_apply hGc.measurable hT, Measure.restrict_apply (hGc.measurable hT)]
    refine hnull _ inter_subset_right (measure_mono_null ?_ h0)
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hu.1, mem_image_of_mem G hu.2⟩
  -- a.e. on `A`: `G(A)` has approximate tangent space `range DG(u)` at `G(u)` (`piece_tangent`),
  -- `G(A)` and `M` have the same approximate tangent spaces at `G(u)` (locality (IMC)(a)), and
  -- `ξ(G(u))` orients an approximate tangent space of `M` at `G(u)` (`R.orients`)
  have hpt := Submission.ptd_piece_image_approxTangent_ae P n G A L m hG hA hm hbi hdiff
  have hloc := hqmp.ae (hIMC.1 P n U (G '' A) R.carrier hU hYm R.measurableSet_carrier hGA
    R.carrier_subset hfin)
  have hor := hqmp.ae (ae_restrict_of_ae_restrict_of_subset hGA R.orients)
  -- the frame `v(u) = (DG(u)eₐ)ₐ`, `J(u) = J_G(u)` and `ev_v = v₁ ∧ ⋯ ∧ vₙ : α ↦ α(v)`
  let v : Euclid n → Fin n → Euclid P := fun u a => fderiv ℝ G u (EuclideanSpace.single a 1)
  let J : Euclid n → ℝ := fun u =>
    Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (v u a) (v u b)))
  let ev := (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
  have hev : ∀ (w : Fin n → Euclid P) (α : Covector (Euclid P) n), ev w α = α w := fun w α => by
    simp only [ev, ContinuousLinearMap.flipAlternating_apply_apply, ContinuousLinearMap.id_apply]
  -- a.e. on `A`: `J(u) ξ(G(u)) = ±ev_{v(u)}`
  have hsign : ∀ᵐ u ∂(volume.restrict A),
      J u • R.orient (G u) = ev (v u) ∨ J u • R.orient (G u) = -ev (v u) := by
    filter_upwards [hpt, hloc, hor, ae_restrict_mem hA] with u hpt hloc hor huA
    -- `v(u)` is the image of the standard basis under the injective `DG(u)`
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    have hvu : v u = (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid P) ∘ b := by
      funext a
      simp [v, b]
    have hli : LinearIndependent ℝ (v u) := by
      rw [hvu]
      exact b.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 (hdiff u huA).2)
    have hspan : Submodule.span ℝ (range (v u)) =
        LinearMap.range (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid P) := by
      rw [hvu, range_comp, Submodule.span_image, b.span_eq, Submodule.map_top]
    -- `ξ(G(u))` is a unit orientation of `T_{G(u)}M = range DG(u) = span v(u)`
    obtain ⟨Q, hQ, hξQ⟩ := hor
    have hQeq : Q = Submodule.span ℝ (range (v u)) := by
      rw [hspan]
      exact hQ.unique ((hloc _).1 hpt)
    rw [hQeq] at hξQ
    -- so is `J(u)⁻¹ ev_{v(u)}` (`wedge_orientation`); they agree up to sign (`orientation_sign`)
    obtain ⟨hdet, hwedge⟩ := Submission.codim1_lur_normalized_wedge_orientation P n (v u) hli
    have hJ : 0 < J u := Real.sqrt_pos.2 hdet
    have hζ := hwedge ((J u)⁻¹ • ev (v u)) fun α => by
      rw [smul_apply, smul_eq_mul, hev]
    rcases Submission.rsdic_unitOrientation_eq_or_eq_neg P n _ _ _ hζ hξQ with h | h
    · left
      rw [h, smul_smul, mul_inv_cancel₀ hJ.ne', one_smul]
    · right
      rw [h, smul_neg (J u) ((J u)⁻¹ • ev (v u)), smul_smul, mul_inv_cancel₀ hJ.ne', one_smul]
  -- measurability: `J` (`gram_area`), `v` (`measurable_fderiv`), `ev` continuous, and `ξ ∘ G`
  -- through the quasi-measure-preserving `G`
  have hJm : Measurable J := (Submission.codim1_lura_gram_area_formula n P G).1
  have hvm : Measurable v :=
    Measurable.of_eval fun a => measurable_fderiv_apply_const ℝ G (EuclideanSpace.single a 1)
  have hfm : AEStronglyMeasurable (fun u => J u • R.orient (G u)) (volume.restrict A) :=
    hJm.aestronglyMeasurable.smul
      ((R.aestronglyMeasurable_orient.mono_measure
        (Measure.restrict_mono_set _ hGA)).comp_quasiMeasurePreserving hqmp)
  have hem : AEStronglyMeasurable (fun u => ev (v u)) (volume.restrict A) :=
    (map_continuous ev).comp_aestronglyMeasurable hvm.aestronglyMeasurable
  -- the sign: `1` on a measurable version `S` of `{J ξ ∘ G = ev_v}`, `-1` off it; the
  -- operator-norm uniformity of `Λₙ` is countably generated and induces its topology
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
      Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
  have hS₀ := hfm.nullMeasurableSet_eq_fun hem
  set S := toMeasurable (volume.restrict A) {u | J u • R.orient (G u) = ev (v u)}
  have hSm : MeasurableSet S := measurableSet_toMeasurable _ _
  refine ⟨fun u => if u ∈ S then 1 else -1, Measurable.ite hSm measurable_const measurable_const,
    fun u => by by_cases hu : u ∈ S <;> simp [hu], ?_⟩
  filter_upwards [hsign, hS₀.toMeasurable_ae_eq] with u hu hSu α
  have hSu' : u ∈ S ↔ J u • R.orient (G u) = ev (v u) := Iff.of_eq hSu
  have key : J u * R.orient (G u) α = (J u • R.orient (G u)) α := by
    rw [smul_apply, smul_eq_mul]
  show J u * R.orient (G u) α = ((if u ∈ S then (1 : ℤ) else -1 : ℤ) : ℝ) * α (v u)
  by_cases huS : u ∈ S
  · rw [ite_eq_left huS, key, hSu'.1 huS, hev, Int.cast_one, one_mul]
  · rw [ite_eq_right huS, key, hu.resolve_left (fun h => huS (hSu'.2 h)), neg_apply, hev,
      Int.cast_neg, Int.cast_one, neg_one_mul]
/-- **Normalized representation** (Simon 6.3.1, 6.2.11): an integer multiplicity `X ∈ 𝒟ₙ(U)`,
`U` open, has a representation `X = τ(M, θ, ξ)` with `M ⊆ spt X` and `μ_X(U) = M(X)`.
Take any `X = τ(M₀, θ, ξ)`.  Every form admissible for `M_Z(X)`, `Z` the open zero region, is
supported away from `spt X = U ∖ Z`, so `M_Z(X) = 0`; as `θ ≥ 1` on `M₀`,
`Hⁿ(M₀ ∖ spt X) = Hⁿ(M₀ ∩ Z) ≤ θHⁿ⌞M₀(Z) = M_Z(X) = 0`.  Restricting `(M₀, θ, ξ)` to the Borel
set `spt X` therefore still represents `X`, and its weight of `U` is `M_U(X) = M(X)`. -/
theorem Submission.dimred_mbl_dt_lpip_normalized_rep : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity X → ∃ R : IMRep U n, R.Represents X ∧ R.carrier ⊆ X.support ∧ R.measure U = X.mass := by
  intro hVO hMR hIMC P n U X hU hX
  obtain ⟨R₀, hR₀⟩ := hX
  -- `spt X = U ∖ Z` with `Z` the open zero region, so `spt X` is Borel
  have hZ : IsOpen X.zeroRegion := X.isOpen_zeroRegion
  have hspt : MeasurableSet X.support := hU.measurableSet.diff hZ.measurableSet
  -- `M_Z(X) = 0`: every admissible form is supported in `Z`, away from `spt X`
  have hmassZ : X.massOn X.zeroRegion = 0 := by
    refine le_antisymm (sSup_le ?_) bot_le
    rintro r ⟨ω, hω, rfl⟩
    dsimp only
    rw [hVO P n U X ω (disjoint_sdiff_right.mono_left hω.1), ENNReal.ofReal_zero]
  -- `Hⁿ(M₀ ∖ spt X) = Hⁿ(Z ∩ M₀) ≤ ∫_{Z ∩ M₀} θ dHⁿ = M_Z(X) = 0`, as `θ ≥ 1` on `M₀`
  have hnull : μHE[n] (R₀.carrier \ X.support) = 0 := by
    have h := hMR P n U X R₀ hU hR₀ X.zeroRegion hZ
    rw [hmassZ, IMRep.measure, withDensity_apply _ hZ.measurableSet,
      Measure.restrict_restrict hZ.measurableSet] at h
    have hdiff : R₀.carrier \ X.support = X.zeroRegion ∩ R₀.carrier := by
      ext x
      simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_inter_iff, not_and, not_not]
      exact ⟨fun hx => ⟨hx.2 (R₀.carrier_subset hx.1), hx.1⟩, fun hx => ⟨hx.2, fun _ => hx.1⟩⟩
    rw [hdiff, ← nonpos_iff_eq_zero]
    calc μHE[n] (X.zeroRegion ∩ R₀.carrier) = ∫⁻ _ in X.zeroRegion ∩ R₀.carrier, 1 ∂μHE[n] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in X.zeroRegion ∩ R₀.carrier, (R₀.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono (measurable_from_nat.comp R₀.measurable_mult) fun x hx =>
            Nat.one_le_cast.2 (R₀.mult_pos x hx.2)
      _ = 0 := h.symm
  -- restrict `(M₀, θ, ξ)` to `spt X`; this changes `Hⁿ⌞M₀` only on a null set
  obtain ⟨-, R, -, hcar, hmult, horient⟩ := hIMC.2.1 P n U R₀ X.support hU hspt
  have hres : μHE[n].restrict R.carrier = μHE[n].restrict R₀.carrier := by
    rw [hcar, ← Measure.restrict_inter_add_sdiff R₀.carrier hspt, Measure.restrict_eq_zero.2 hnull,
      add_zero]
  have hRX : R.Represents X := by
    intro ω
    rw [hR₀ ω, IMRep.action, IMRep.action, hres, hmult, horient]
  refine ⟨R, hRX, ?_, (hMR P n U X R hU hRX U hU).symm⟩
  rw [hcar]
  exact inter_subset_right

/-- **Bi-Lipschitz piece representation of an integer multiplicity current of finite mass**
(Simon Ch. 6, 3.1 with Ch. 3, (B1)).  Let `R = (M, θ, ξ)` in `ℝᴾ` have `∫_M θ dHⁿ < ∞`.  (B1)
cuts `M` into pairwise disjoint Borel pieces `G i '' A i` exhausting `M` up to an `Hⁿ`-null set,
with `G i` Lipschitz, bi-Lipschitz on `A i` and differentiable there with injective derivative.
Let `c i = √det(⟨DG_i e_a, DG_i e_b⟩)` be the Gram Jacobian and `s i = ±1` the orientation signs
of `dimred_mbl_dt_lpip_piece_orientation_sign` (`c i · ξ ∘ G i = s i · ev_{DG_i e}` a.e. on
`A i`), and put `w i = θ ∘ G i · s i`.  (GB) gives `|α(DG_i e)| ≤ c i |α|`; the lower bound
`ofReal(m i)ⁿ λ(Z) ≤ Hⁿ(G i '' Z)` makes `w i` integrable on `A i`; the area formula gives
`∑ᵢ ∫_{A i} |w i| c i = ∫_{⋃ G i '' A i} θ dHⁿ ≤ R.measure ℝᴾ`; and as `θ ξ(η)` is `Hⁿ`-integrable
on `M` by (IMC)(d), countable additivity over the pieces, the area formula and the sign identity
give `∑ᵢ ∫_{A i} w i · η(G i)(DG_i e) = R.action η`. -/
theorem Submission.dimred_mbl_dt_lpip_piece_representation : (∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → ∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0) → (∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), R.measure univ ≠ ∞ → ∃ (G : ℕ → Euclid n → Euclid P) (A : ℕ → Set (Euclid n)) (w : ℕ → Euclid n → ℤ) (c : ℕ → Euclid n → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i, Measurable (w i)) ∧ (∀ i, Measurable (c i)) ∧ (∀ i, ∀ u ∈ A i, DifferentiableAt ℝ (G i) u) ∧ (∀ i, G i '' A i ⊆ R.carrier) ∧ (∀ i, IntegrableOn (fun u => (w i u : ℝ)) (A i)) ∧ (∀ i, ∀ u ∈ A i, 0 ≤ c i u ∧ ∀ α : Covector (Euclid P) n, |α (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))| ≤ c i u * covectorEuclideanNorm α) ∧ ∑' i, ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) ≤ R.measure univ ∧ ∀ η : DifferentialForm (Euclid P) n, Continuous η → HasCompactSupport η → HasSum (fun i => ∫ u in A i, (w i u : ℝ) * η (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (R.action η) := by
  intro hB1 hGB hIMC P n R hRfin
  -- (B1): bi-Lipschitz pieces `G i '' A i` of `M = R.carrier`, pairwise disjoint and exhausting
  -- `M` up to an `Hⁿ`-null set
  obtain ⟨G, A, m, hLip, hAmeas, hmpos, hcolip, hreg, hGAmeas, hGAsub, hdisj, hnull⟩ :=
    hB1 P n R.carrier R.measurableSet_carrier R.rectifiable
  choose L hL using hLip
  have hGm : ∀ i, Measurable (G i) := fun i => (hL i).continuous.measurable
  have hinj : ∀ i, InjOn (G i) (A i) := by
    intro i a ha a' ha' hGa
    have h := hcolip i a ha a' ha'
    rw [hGa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) (hmpos i)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  -- `c i = √det(⟨DG_i e_a, DG_i e_b⟩)`, the Gram Jacobian of `G i`
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Euclid n → ℝ, ∀ i u, c i u = Real.sqrt (Matrix.det
      (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ (G i) u (EuclideanSpace.single a 1))
        (fderiv ℝ (G i) u (EuclideanSpace.single b 1)))) :=
    ⟨_, fun i u => rfl⟩
  -- signs `s i = ±1` with `c i · ξ(G i u) = s i u · α(DG_i(u) e)` for a.e. `u ∈ A i`
  choose s hsmeas hspm hsae using fun i =>
    Submission.dimred_mbl_dt_lpip_piece_orientation_sign hIMC P n univ R (G i) (A i) (L i) (m i)
      isOpen_univ (hL i) (hAmeas i) (hmpos i) (hcolip i) (hreg i) (hGAsub i)
  -- integer weights `w i = θ ∘ G i · s i`, so `|w i| = θ ∘ G i`
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Euclid n → ℤ, ∀ i u, w i u = (R.mult (G i u) : ℤ) * s i u :=
    ⟨_, fun i u => rfl⟩
  have habsw : ∀ i u, |(w i u : ℝ)| = (R.mult (G i u) : ℝ) := by
    intro i u
    rcases hspm i u with h | h <;> simp [hw, h]
  have hwmeas : ∀ i, Measurable (w i) := by
    intro i
    rw [show w i = fun u => (R.mult (G i u) : ℤ) * s i u from funext (hw i)]
    exact (measurable_of_countable fun p : ℤ × ℤ => p.1 * p.2).comp
      (((measurable_of_countable fun k : ℕ => (k : ℤ)).comp
        (R.measurable_mult.comp (hGm i))).prodMk (hsmeas i))
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    (measurable_of_countable fun k : ℕ => (k : ℝ≥0∞)).comp R.measurable_mult
  -- `R.measure univ = ∫_M θ dHⁿ < ∞`
  have hRmeas : R.measure univ = ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hθfin : ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := hRmeas ▸ hRfin
  -- `ofReal(m i)ⁿ ∫_{A i} g ∘ G i ≤ ∫_{G i '' A i} g dHⁿ` for Borel `g ≥ 0`, as
  -- `ofReal(m i)ⁿ λ(Z) ≤ Hⁿ(G i '' Z)` for `Z ⊆ A i`
  have hcmp : ∀ i (g : Euclid P → ℝ≥0∞), Measurable g →
      ENNReal.ofReal (m i) ^ n * ∫⁻ u in A i, g (G i u) ≤ ∫⁻ y in G i '' A i, g y ∂μHE[n] := by
    intro i g hg
    have hle : ENNReal.ofReal (m i) ^ n • Measure.map (G i) (volume.restrict (A i)) ≤
        μHE[n].restrict (G i '' A i) := by
      refine Measure.le_iff.2 fun B hB => ?_
      rw [Measure.smul_apply, Measure.map_apply (hGm i) hB, Measure.restrict_apply (hGm i hB),
        Measure.restrict_apply hB, smul_eq_mul]
      calc ENNReal.ofReal (m i) ^ n * volume (G i ⁻¹' B ∩ A i)
          ≤ μHE[n] (G i '' (G i ⁻¹' B ∩ A i)) :=
            (Submission.dimred_mbl_dt_lpip_bilipschitz_measure_bounds P n (G i) (A i) (L i) (m i)
              (hL i) (hmpos i) (hcolip i) _ inter_subset_right).1
        _ ≤ μHE[n] (B ∩ G i '' A i) := by
            refine measure_mono ?_
            rintro _ ⟨u, ⟨hu, hu'⟩, rfl⟩
            exact ⟨hu, mem_image_of_mem _ hu'⟩
    calc ENNReal.ofReal (m i) ^ n * ∫⁻ u in A i, g (G i u)
        = ∫⁻ y, g y ∂(ENNReal.ofReal (m i) ^ n • Measure.map (G i) (volume.restrict (A i))) := by
          rw [lintegral_smul_measure, lintegral_map hg (hGm i), smul_eq_mul]
      _ ≤ ∫⁻ y in G i '' A i, g y ∂μHE[n] := lintegral_mono' hle le_rfl
  refine ⟨G, A, w, c, fun i => ⟨L i, hL i⟩, hAmeas, hwmeas, fun i => ?_,
    fun i u hu => (hreg i u hu).1, hGAsub, fun i => ?_, fun i u _ => ⟨?_, fun α => ?_⟩, ?_,
    fun η hη hηc => ?_⟩
  · rw [show c i = _ from funext (hc i)]
    exact (Submission.codim1_lura_gram_area_formula n P (G i)).1
  · -- `∫_{A i} |w i| = ∫_{A i} θ ∘ G i ≤ ofReal(m i)⁻ⁿ ∫_M θ dHⁿ < ∞`
    have hfin : ∫⁻ u in A i, (R.mult (G i u) : ℝ≥0∞) ≠ ∞ := by
      have hle : ENNReal.ofReal (m i) ^ n * ∫⁻ u in A i, (R.mult (G i u) : ℝ≥0∞) ≤
          R.measure univ :=
        calc ENNReal.ofReal (m i) ^ n * ∫⁻ u in A i, (R.mult (G i u) : ℝ≥0∞)
            ≤ ∫⁻ y in G i '' A i, (R.mult y : ℝ≥0∞) ∂μHE[n] := hcmp i _ hθ
          _ ≤ ∫⁻ y in R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[n] := lintegral_mono_set (hGAsub i)
          _ = R.measure univ := hRmeas.symm
      exact (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hRfin hle)
        (pow_ne_zero n (ENNReal.ofReal_pos.2 (hmpos i)).ne')).ne
    refine (integrable_toReal_of_lintegral_ne_top (hθ.comp (hGm i)).aemeasurable hfin).mono'
      ((measurable_of_countable fun k : ℤ => (k : ℝ)).comp (hwmeas i)).aestronglyMeasurable
      (Eventually.of_forall fun u => le_of_eq ?_)
    rw [Real.norm_eq_abs, habsw, comp_apply, ENNReal.toReal_natCast]
  · rw [hc]
    exact Real.sqrt_nonneg _
  · -- (GB)(i): `|α(DG_i(u) e)| ≤ |α| · √det(⟨DG_i(u) e_a, DG_i(u) e_b⟩)`
    rw [hc]
    exact ((hGB P n).1 α _).trans_eq (mul_comm _ _)
  · -- area formula on each piece: `∫_{A i} |w i| c i = ∫_{G i '' A i} θ dHⁿ`; the pieces are
    -- disjoint Borel subsets of `M`
    calc ∑' i, ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u)
        = ∑' i, ∫⁻ y in G i '' A i, (R.mult y : ℝ≥0∞) ∂μHE[n] := by
          refine tsum_congr fun i => ?_
          rw [(Submission.codim1_lura_gram_area_formula n P (G i)).2 (A i) (hAmeas i)
            (fun u hu => (hreg i u hu).1) (fun u hu => (hreg i u hu).2) (hinj i)]
          refine lintegral_congr fun u => ?_
          rw [habsw, hc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
      _ = ∫⁻ y in ⋃ i, G i '' A i, (R.mult y : ℝ≥0∞) ∂μHE[n] :=
          (lintegral_iUnion hGAmeas hdisj _).symm
      _ ≤ ∫⁻ y in R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[n] := lintegral_mono_set (iUnion_subset hGAsub)
      _ = R.measure univ := hRmeas.symm
  · -- `f = θ · ξ(η)` is `Hⁿ`-integrable on `M`: `|f| ≤ θ · sup |η|` a.e. on `M` by (IMC)(d)
    have hcont : Continuous fun x => covectorEuclideanNorm (η x) := by
      unfold covectorEuclideanNorm
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => ((continuous_eval_const _).comp hη).pow 2)
        (fun _ => continuous_const)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
      (hηc.comp_left (g := covectorEuclideanNorm) (covectorEuclideanNorm_zero P n))
    have hfint : IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (η x)) R.carrier μHE[n] := by
      refine ((integrable_toReal_of_lintegral_ne_top hθ.aemeasurable hθfin).mul_const C).mono'
        ?_ ?_
      · exact ((measurable_of_countable fun k : ℕ => (k : ℝ)).comp
          R.measurable_mult).aestronglyMeasurable.mul
          (Continuous.comp_aestronglyMeasurable₂ (g := fun (ζ : MultiVector P n) α => ζ α)
            isBoundedBilinearMap_apply.continuous R.aestronglyMeasurable_orient
            hη.aestronglyMeasurable)
      · filter_upwards [hIMC.2.2.2 P n univ R] with x hx
        rw [ENNReal.toReal_natCast, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          ((hx (η x)).trans ((Real.le_norm_self _).trans (hC x))) (Nat.cast_nonneg _)
    -- area formula and orientation signs: `∫_{G i '' A i} f dHⁿ = ∫_{A i} w i · η(G i)(DG_i e)`
    have hterm : ∀ i, ∫ y in G i '' A i, (R.mult y : ℝ) * R.orient y (η y) ∂μHE[n] =
        ∫ u in A i, (w i u : ℝ) *
          η (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1)) := by
      intro i
      rw [Submission.codim1_lur_cd_injective_area_formula_gram P n (G i) (A i) (hAmeas i)
        (fun u hu => (hreg i u hu).1) (fun u hu => (hreg i u hu).2) (hinj i)]
      refine integral_congr_ae ?_
      filter_upwards [hsae i] with u hu
      rw [hw]
      push_cast
      linear_combination (R.mult (G i u) : ℝ) * hu (η (G i u))
    -- countable additivity over the pieces, which exhaust `M` up to an `Hⁿ`-null set
    have hae : (⋃ i, G i '' A i : Set (Euclid P)) =ᵐ[μHE[n]] R.carrier :=
      ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 (iUnion_subset hGAsub), measure_empty], hnull⟩
    have hsum := hasSum_integral_iUnion hGAmeas hdisj (hfint.mono_set (iUnion_subset hGAsub))
    rw [setIntegral_congr_set hae] at hsum
    simp only [hterm] at hsum
    exact hsum

/-- **Integer multiplicity current of an integer-weighted bi-Lipschitz image piece** (Simon Ch. 6,
3.3–3.9, for one piece `H|_A` of a Lipschitz push-forward).  Assume (MR) (`M_W(T) = μ_T(W)` for
`T = τ(M, θ, ξ)`) and (IMC) (locality/restriction/difference/orientation bound of `IMRep`s).  Let
`H : ℝⁿ → ℝᴾ` be `L`-Lipschitz, `A ⊆ ℝⁿ` Borel with `κ|a − a'| ≤ |H a − H a'|` on `A` (`κ > 0`),
`H` differentiable on `A` with injective derivative, and `g : ℝⁿ → ℤ` Borel, nonzero on `A` and
integrable over `A`.  Then `Φ(ω) = ∫_A g(u) ω(H u)(DH(u)e₁, …, DH(u)eₙ) du` is an integer
multiplicity current in `ℝᴾ` with `M(Φ) ≤ Lⁿ ∫_A |g|`.

`N = H(A)` is Borel and `H|_A` is a Borel isomorphism onto `N` (Lusin–Souslin).  With
`v(u) = (DH(u)e_a)_a` and `J = √det(⟨v_a, v_b⟩) > 0` on `A`, put `θ(H u) = |g(u)|` and
`ζ(H u) = sign(g u) J(u)⁻¹ v₁(u) ∧ ⋯ ∧ vₙ(u)`, a unit orientation of `range DH(u)`; this is the
approximate tangent space of `N` at `H u` for a.e. `u ∈ A`, and `Hⁿ(H(Z)) ≤ Lⁿ λ(Z)` makes the
exceptional set `Hⁿ`-null.  `τ(N, θ, ζ)` is the current; the area formula
`∫_N f dHⁿ = ∫_A J f(H u) du` gives the action, and (MR) with `Hⁿ⌞N ≤ Lⁿ H_#(λ⌞A)` the mass. -/
theorem Submission.dimred_mbl_dt_lpip_bilipschitz_image_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P n : ℕ) (L : NNReal) (κ : ℝ) (H : Euclid n → Euclid P) (A : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ A, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → (∀ a ∈ A, g a ≠ 0) → IntegrableOn (fun u => (g u : ℝ)) A → ∃ Φ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity Φ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Φ ω = ∫ u in A, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) ∧ Φ.mass ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in A, ‖(g u : ℝ)‖ₑ := by
  intro hMR hIMC P n L κ H A g hH hA hκ hbi hreg hg hg0 hgint
  -- Step 1: `H` is continuous and injective on `A`, so `N = H(A)` is Borel and `H|_A` is a
  -- measurable embedding (Lusin–Souslin)
  have hHc : Continuous H := hH.continuous
  have hinj : InjOn H A := by
    intro a ha a' ha' haa'
    have h := hbi a ha a' ha'
    rw [haa', sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := by
      by_contra hc
      exact absurd h (not_le.2 (mul_pos hκ (not_le.1 hc)))
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have hN : MeasurableSet (H '' A) := hA.image_of_continuousOn_injOn hHc.continuousOn hinj
  have hemb : MeasurableEmbedding (A.domRestrict H) :=
    ContinuousOn.measurableEmbedding hA hHc.continuousOn hinj
  -- `Hⁿ(H(Z)) ≤ Lⁿ λ(Z)` for `Z ⊆ A`
  have hbilip := Submission.dimred_mbl_dt_lpip_bilipschitz_measure_bounds P n H A L κ hH hκ hbi
  -- Step 2: the frame `v(u) = (DH(u)e_a)_a` and its Gram Jacobian `J(u) = √det(⟨v_a, v_b⟩)`
  obtain ⟨v, hv⟩ : ∃ v : Euclid n → Fin n → Euclid P,
      v = fun u a => fderiv ℝ H u (EuclideanSpace.single a 1) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : Euclid n → ℝ,
      J = fun u => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (v u i) (v u j))) :=
    ⟨_, rfl⟩
  have hJm : Measurable J := by
    subst hJ hv
    exact (Submission.codim1_lura_gram_area_formula n P H).1
  -- the injective area formula `∫_{H(A)} f dHⁿ = ∫_A J f(H u) du`
  have harea : ∀ f : Euclid P → ℝ, ∫ w in H '' A, f w ∂μHE[n] = ∫ u in A, J u * f (H u) := by
    intro f
    subst hJ hv
    exact Submission.codim1_lur_cd_injective_area_formula_gram P n H A hA
      (fun u hu => (hreg u hu).1) (fun u hu => (hreg u hu).2) hinj f
  -- `v(u)` is a basis of `range DH(u)` for `u ∈ A`, as `DH(u)` is injective
  have hbf : ⇑(EuclideanSpace.basisFun (Fin n) ℝ) =
      fun a : Fin n => (EuclideanSpace.single a (1 : ℝ) : Euclid n) :=
    funext fun a => EuclideanSpace.basisFun_apply (Fin n) ℝ a
  have hsingle : Submodule.span ℝ (Set.range fun a : Fin n => (EuclideanSpace.single a (1 : ℝ) :
      Euclid n)) = ⊤ := by
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
    rwa [OrthonormalBasis.coe_toBasis, hbf] at h
  have hli : ∀ u ∈ A, LinearIndependent ℝ (v u) := by
    intro u hu
    have hb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
    rw [OrthonormalBasis.coe_toBasis, hbf] at hb
    rw [hv]
    exact hb.map' (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.2 (hreg u hu).2)
  have hspan : ∀ u, Submodule.span ℝ (Set.range (v u)) =
      LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P) := by
    intro u
    have h1 : Set.range (v u) = (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P) ''
        Set.range fun a : Fin n => (EuclideanSpace.single a (1 : ℝ) : Euclid n) := by
      rw [hv, ← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, hsingle, Submodule.map_top]
  have hJpos : ∀ u ∈ A, 0 < J u := fun u hu => by
    rw [hJ]
    exact Real.sqrt_pos.2
      (Submission.codim1_lur_normalized_wedge_orientation P n (v u) (hli u hu)).1
  -- Step 3: `Ψ(u) = sign(g u) J(u)⁻¹ v₁(u) ∧ ⋯ ∧ vₙ(u)` is strongly measurable, as
  -- `w ↦ (α ↦ α(w))` is a continuous multilinear map `(ℝᴾ)ⁿ → Λₙ(ℝᴾ)`
  obtain ⟨Ψ, hΨm, hΨ⟩ : ∃ Ψ : Euclid n → MultiVector P n, StronglyMeasurable Ψ ∧
      ∀ u (α : Covector (Euclid P) n), Ψ u α = ((g u).sign : ℝ) * ((J u)⁻¹ * α (v u)) := by
    let ev : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclid P) (MultiVector P n) :=
      ContinuousLinearMap.flipMultilinear (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
    have hvm : Measurable v := by
      rw [hv]
      exact Measurable.of_eval fun a =>
        measurable_fderiv_apply_const ℝ H (EuclideanSpace.single a 1)
    refine ⟨fun u => (((g u).sign : ℝ) * (J u)⁻¹) • ev (v u), ?_, fun u α => ?_⟩
    · exact (((Measurable.of_discrete (f := fun z : ℤ => (z.sign : ℝ))).comp hg).mul
        hJm.inv).stronglyMeasurable.smul (ev.coe_continuous.comp_stronglyMeasurable
          hvm.stronglyMeasurable)
    · simp only [smul_apply, smul_eq_mul, ev,
        ContinuousLinearMap.flipMultilinear_apply_apply,
        ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply,
        ContinuousAlternatingMap.coe_toContinuousMultilinearMap]
      ring
  -- multiplicity `θ(H u) = |g(u)|` and orientation `ζ(H u) = Ψ(u)` on `N`, extended by `0`
  obtain ⟨θ, hθm, hθH⟩ : ∃ θ : Euclid P → ℕ, Measurable θ ∧ ∀ u ∈ A, θ (H u) = (g u).natAbs :=
    ⟨Function.extend (A.domRestrict H) (fun a => (g a).natAbs) fun _ => 0,
      hemb.measurable_extend ((Measurable.of_discrete (f := Int.natAbs)).comp
        (hg.comp measurable_subtype_coe)) measurable_const,
      fun u hu => hemb.injective.extend_apply _ _ ⟨u, hu⟩⟩
  obtain ⟨ζ, hζm, hζH⟩ : ∃ ζ : Euclid P → MultiVector P n, StronglyMeasurable ζ ∧
      ∀ u ∈ A, ζ (H u) = Ψ u :=
    ⟨Function.extend (A.domRestrict H) (fun a => Ψ a) fun _ => 0,
      hemb.stronglyMeasurable_extend (hΨm.comp_measurable measurable_subtype_coe)
        stronglyMeasurable_const,
      fun u hu => hemb.injective.extend_apply _ _ ⟨u, hu⟩⟩
  have hθpos : ∀ y ∈ H '' A, 0 < θ y := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hθH u hu]
    exact Int.natAbs_pos.2 (hg0 u hu)
  -- Step 4: `Hⁿ⌞N ≤ Lⁿ H_#(λ⌞A)`, hence `∫_N θ dHⁿ ≤ Lⁿ ∫_A |g| < ∞`
  have hle : μHE[n].restrict (H '' A) ≤ ((L : ℝ≥0∞) ^ n) • (volume.restrict A).map H := by
    refine Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB, Measure.smul_apply, Measure.map_apply hHc.measurable hB,
      Measure.restrict_apply (hHc.measurable hB), smul_eq_mul]
    have hset : B ∩ H '' A = H '' (H ⁻¹' B ∩ A) := by
      ext y
      constructor
      · rintro ⟨hyB, u, hu, rfl⟩
        exact ⟨u, ⟨hyB, hu⟩, rfl⟩
      · rintro ⟨u, ⟨huB, hu⟩, rfl⟩
        exact ⟨huB, u, hu, rfl⟩
    rw [hset]
    exact (hbilip _ inter_subset_right).2
  have hθint : ∫⁻ y in H '' A, (θ y : ℝ≥0∞) ∂μHE[n] ≤
      (L : ℝ≥0∞) ^ n * ∫⁻ u in A, ‖(g u : ℝ)‖ₑ := by
    have hθm' : Measurable fun y => (θ y : ℝ≥0∞) :=
      (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ≥0∞))).comp hθm
    calc ∫⁻ y in H '' A, (θ y : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ y, (θ y : ℝ≥0∞) ∂(((L : ℝ≥0∞) ^ n) • (volume.restrict A).map H) :=
          lintegral_mono' hle le_rfl
      _ = (L : ℝ≥0∞) ^ n * ∫⁻ u in A, (θ (H u) : ℝ≥0∞) := by
          rw [lintegral_smul_measure, lintegral_map hθm' hHc.measurable, smul_eq_mul]
      _ = (L : ℝ≥0∞) ^ n * ∫⁻ u in A, ‖(g u : ℝ)‖ₑ := by
          congr 1
          refine setLIntegral_congr_fun hA fun u hu => ?_
          show (θ (H u) : ℝ≥0∞) = ‖(g u : ℝ)‖ₑ
          rw [hθH u hu, Real.enorm_eq_ofReal_abs, ← Int.cast_abs, Int.abs_eq_natAbs,
            Int.cast_natCast, ENNReal.ofReal_natCast]
  have hfin : ∫⁻ u in A, ‖(g u : ℝ)‖ₑ < ∞ := hgint.2
  have hθloc : ∀ K : Set (Euclid P), IsCompact K →
      ∫⁻ x in H '' A ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := fun K _ =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfin.ne)
      ((lintegral_mono_set inter_subset_left).trans hθint)
  -- Step 5: `ζ(H u) = ±J(u)⁻¹ v₁(u) ∧ ⋯ ∧ vₙ(u)` orients `range DH(u)` for every `u ∈ A`
  have horH : ∀ u ∈ A, IsUnitOrientationOf (ζ (H u))
      (LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)) := by
    intro u hu
    have hJu : J u =
        Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (v u i) (v u j))) := by
      rw [hJ]
    have hw := (Submission.codim1_lur_normalized_wedge_orientation P n (v u) (hli u hu)).2
    rw [hspan u] at hw
    rw [hζH u hu]
    rcases (hg0 u hu).lt_or_gt with hlt | hgt
    · -- `-ζ(H u)` is the normalized wedge; a unit orientation may carry either sign
      obtain ⟨τ, hτ, hτQ, h | h⟩ := hw (-Ψ u) fun α => by
        rw [neg_apply, hΨ, Int.sign_eq_neg_one_of_neg hlt, hJu]
        push_cast
        ring
      · refine ⟨τ, hτ, hτQ, Or.inr fun α => ?_⟩
        have h' := h α
        rw [neg_apply] at h'
        linarith
      · refine ⟨τ, hτ, hτQ, Or.inl fun α => ?_⟩
        have h' := h α
        rw [neg_apply] at h'
        linarith
    · exact hw (Ψ u) fun α => by
        rw [hΨ, Int.sign_eq_one_of_pos hgt, hJu]
        push_cast
        ring
  -- the approximate tangent space of `N` at `H u` is `range DH(u)` for a.e. `u ∈ A`; the
  -- exceptional parameters form a `λ`-null `Z ⊆ A` with `Hⁿ(H(Z)) ≤ Lⁿ λ(Z) = 0`
  have hor : ∀ᵐ y ∂(μHE[n].restrict (H '' A)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (H '' A) y Q ∧ IsUnitOrientationOf (ζ y) Q := by
    have htan := Submission.ptd_piece_image_approxTangent_ae P n H A L κ hH hA hκ hbi hreg
    rw [ae_restrict_iff' hA, ae_iff] at htan
    have hHZ := (hbilip {u | ¬(u ∈ A → HasApproximateTangentSpaceAt n (H '' A) (H u)
      (LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)))} fun u hu => (not_imp.1 hu).1).2
    rw [htan, mul_zero, nonpos_iff_eq_zero] at hHZ
    rw [ae_iff, Measure.restrict_apply' hN]
    refine measure_mono_null ?_ hHZ
    rintro _ ⟨hy, u, hu, rfl⟩
    exact ⟨u, fun hT => hy ⟨_, hT hu, horH u hu⟩, rfl⟩
  -- Step 6: the `IMRep` `(N, θ, ζ)` in `ℝᴾ`
  obtain ⟨R₁, hR₁c, hR₁m, hR₁o⟩ := Submission.dtc_bc_lc_sl_sf_imrep_of_subset P n (H '' A) (H '' A)
    θ ζ hN hN subset_rfl
    ((Poincare.SimonGMT.Chapter03.countablyRectifiable_range hH).mono (image_subset_range H A))
    hθm hθpos hθloc hζm.aestronglyMeasurable hor
  -- Step 7: the current `Φ = τ(N, θ, ζ)`, by (IMC)(b) with `E = ℝᴾ`
  obtain ⟨Φ, R, hRep, hRc, hRm, hRo⟩ := hIMC.2.1 P n univ R₁ univ isOpen_univ MeasurableSet.univ
  refine ⟨Φ, ⟨R, hRep⟩, fun ω => ?_, ?_⟩
  · -- Step 8: `Φ(ω) = ∫_N θ⟨ω, ζ⟩ dHⁿ = ∫_A J θ(H u)⟨ω(H u), ζ(H u)⟩ du = ∫_A g⟨ω(H u), v(u)⟩ du`
    rw [hRep ω, IMRep.action, hRc, hRm, hRo, hR₁c, hR₁m, hR₁o, inter_univ, harea]
    refine setIntegral_congr_fun hA fun u hu => ?_
    show J u * ((θ (H u) : ℝ) * ζ (H u) ((ω : DifferentialForm (Euclid P) n) (H u))) =
      (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))
    have hvu : v u = fun a => fderiv ℝ H u (EuclideanSpace.single a 1) := by rw [hv]
    have hgs : ((g u).natAbs : ℝ) * ((g u).sign : ℝ) = (g u : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, mul_comm]
      exact_mod_cast Int.sign_mul_abs (g u)
    have key : ∀ s a b X : ℝ, s ≠ 0 → s * (a * (b * (s⁻¹ * X))) = a * b * X := by
      intro s a b X hs
      field_simp
    rw [hθH u hu, hζH u hu, hΨ, hvu, key _ _ _ _ (hJpos u hu).ne', hgs]
  · -- Step 9: `M(Φ) = μ_Φ(ℝᴾ) = ∫_N θ dHⁿ ≤ Lⁿ ∫_A |g|` by (MR)
    show Φ.massOn univ ≤ _
    rw [hMR P n univ Φ R isOpen_univ hRep univ isOpen_univ, IMRep.measure,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hRc, hRm, hR₁c, hR₁m,
      inter_univ]
    exact hθint

/-- **Lipschitz push-forward of a weighted parameter domain** (Simon Ch. 6, (3.3)–(3.7), printed
pp. 146–148, for the flat domain `A ⊆ ℝⁿ` with integer weight `g`).  Assume (MR), (IMC) and the
integer multiplicity series lemma (IMSc).  Let `n = k + 1`, `H : ℝⁿ → ℝᴾ` be `L`-Lipschitz,
`A ⊆ ℝⁿ` Borel and `g : ℝⁿ → ℤ` measurable and integrable on `A`.  Then
`ω ↦ ∫_A g(u) ω(H u)(DH(u)e₀, …, DH(u)eₖ) du` is an integer multiplicity current in `ℝᴾ`.
The integrand vanishes off `A⁺ = {u ∈ A : (DH(u)eₐ)ₐ independent, g(u) ≠ 0}` (alternating maps
vanish on dependent vectors, as in (3.4)), and `H` is differentiable on `A⁺` because `DH = 0` off
the differentiability set and `n ≥ 1`.  Mathlib's approximately-linear partition, with radius half
the coercivity constant of the model map, cuts `A⁺` into disjoint Borel pieces `Aₗ` on which `H`
is bi-Lipschitz.  The bi-Lipschitz image current gives integer multiplicity `Φₗ` with
`Φₗ(ω) = ∫_{Aₗ} g ω(H)(DH e)` and `M(Φₗ) ≤ Lⁿ ∫_{Aₗ} |g|`, so `Σₗ M(Φₗ) ≤ Lⁿ ∫_A |g| < ∞`;
(IMSc) sums the `Φₗ` to an integer multiplicity `S`, and countable additivity of the integral
identifies `S(ω)`. -/
theorem Submission.dimred_mbl_dt_lpip_lipschitz_piece_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (P k : ℕ) (L : NNReal) (H : Euclid (k + 1) → Euclid P) (A : Set (Euclid (k + 1))) (g : Euclid (k + 1) → ℤ), LipschitzWith L H → MeasurableSet A → Measurable g → IntegrableOn (fun u => (g u : ℝ)) A → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), IsIntegerMultiplicity S ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), S ω = ∫ u in A, (g u : ℝ) * (ω : DifferentialForm (Euclid P) (k + 1)) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
  intro hMR hIMC hIMS P k L H A g hH hA hg hgi
  have hIC := Submission.dimred_mbl_dt_lpip_bilipschitz_image_current hMR hIMC
  -- `Lip H ≤ L` bounds every `DH(u)eₐ`
  have hDH : ∀ u (a : Fin (k + 1)), ‖fderiv ℝ H u (EuclideanSpace.single a 1)‖ ≤ L := by
    intro u a
    calc ‖fderiv ℝ H u (EuclideanSpace.single a 1)‖
        ≤ L * ‖(EuclideanSpace.single a 1 : Euclid (k + 1))‖ :=
          (fderiv ℝ H u).le_of_opNorm_le (norm_fderiv_le_of_lipschitz ℝ hH) _
      _ = L := by simp
  -- `u ↦ (DH(u)eₐ)ₐ` is Borel
  have hvmeas : Measurable fun u (a : Fin (k + 1)) => fderiv ℝ H u (EuclideanSpace.single a 1) :=
    measurable_pi_iff.2 fun a => measurable_fderiv_apply_const ℝ H _
  -- step 1: `Ψ_ω = g · ω(H)(DH e)` is integrable on `A`, with `|Ψ_ω| ≤ C_ω Lⁿ |g|`
  have hΨint : ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1),
      IntegrableOn (fun u => (g u : ℝ) * (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) A := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) (k + 1)) :=
      ContDiff.continuous ω.property.1.1
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    have hev : Continuous fun p : Euclid P × (Fin (k + 1) → Euclid P) =>
        (ω : DifferentialForm (Euclid P) (k + 1)) p.1 p.2 :=
      continuous_eval.comp ((hωc.comp continuous_fst).prodMk continuous_snd)
    have hmeas : Measurable fun u => (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) :=
      hev.measurable.comp (hH.continuous.measurable.prodMk hvmeas)
    refine (hgi.norm.mul_const (C * (L : ℝ) ^ (k + 1))).mono'
      (hgi.aestronglyMeasurable.mul hmeas.aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖(ω : DifferentialForm (Euclid P) (k + 1)) (H u)
          (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))‖
        ≤ ‖(ω : DifferentialForm (Euclid P) (k + 1)) (H u)‖ *
            ∏ a : Fin (k + 1), ‖fderiv ℝ H u (EuclideanSpace.single a 1)‖ :=
          ContinuousAlternatingMap.le_opNorm _ _
      _ ≤ C * ∏ _a : Fin (k + 1), (L : ℝ) := by
          refine mul_le_mul (hC _) ?_ (by positivity) hC0
          gcongr with a
          exact hDH u a
      _ = C * (L : ℝ) ^ (k + 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- `DH(u)` is injective as soon as `(DH(u)eₐ)ₐ` is linearly independent
  have hLIinj : ∀ T : Euclid (k + 1) →L[ℝ] Euclid P,
      LinearIndependent ℝ (fun a => T (EuclideanSpace.single a 1)) → Injective T := by
    intro T hT x y hxy
    have hrepr : ∀ z : Euclid (k + 1), T z = ∑ a, z a • T (EuclideanSpace.single a 1) := by
      intro z
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).sum_repr z]
      simp [map_sum, map_smul]
    have hc := Fintype.linearIndependent_iff.1 hT (fun a => (x - y) a)
      (by rw [← hrepr, map_sub, hxy, sub_self])
    rw [← sub_eq_zero]
    ext a
    simpa using hc a
  -- step 2: the regular part `A⁺ = {u ∈ A : (DH(u)eₐ)ₐ independent, g(u) ≠ 0}`
  obtain ⟨Ap, hAp⟩ : ∃ Ap : Set (Euclid (k + 1)), Ap = A ∩
      {u | LinearIndependent ℝ (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))} ∩
        {u | g u ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ u, u ∈ Ap ↔ (u ∈ A ∧
      LinearIndependent ℝ (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) ∧ g u ≠ 0 := by
    intro u
    rw [hAp]
    rfl
  have hApA : Ap ⊆ A := fun u hu => ((hmem u).1 hu).1.1
  have hApm : MeasurableSet Ap := by
    rw [hAp]
    exact (hA.inter ((isOpen_setOfPred_linearIndependent (𝕜 := ℝ) (E := Euclid P)
      (ι := Fin (k + 1))).measurableSet.preimage hvmeas)).inter
        (hg (measurableSet_singleton 0)).compl
  have hinj : ∀ u ∈ Ap, Injective (fderiv ℝ H u) := fun u hu => hLIinj _ ((hmem u).1 hu).1.2
  -- `n ≥ 1`, so `DH(u) = 0` is not injective where `H` is not differentiable
  have hdiff : ∀ u ∈ Ap, DifferentiableAt ℝ H u := by
    intro u hu
    by_contra hnd
    have h0 := hinj u hu
    rw [fderiv_zero_of_not_differentiableAt hnd] at h0
    have he : (EuclideanSpace.single 0 1 : Euclid (k + 1)) = 0 := h0 (by simp)
    simpa using congrArg norm he
  have hgne : ∀ u ∈ Ap, g u ≠ 0 := fun u hu => ((hmem u).1 hu).2
  -- off `A⁺`, `g = 0` or `ω(H u)` is evaluated on dependent vectors
  have hzero : ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), ∀ u ∈ A \ Ap,
      (g u : ℝ) * (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) = 0 := by
    intro ω u hu
    by_cases hgu : g u = 0
    · simp [hgu]
    · have hdep : ¬LinearIndependent ℝ (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) :=
        fun hLI => hu.2 ((hmem u).2 ⟨⟨hu.1, hLI⟩, hgu⟩)
      have hω0 : (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
          (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) = 0 :=
        ((ω : DifferentialForm (Euclid P) (k + 1)) (H u)).toAlternatingMap.map_linearDependent _
          hdep
      rw [hω0, mul_zero]
  -- step 3: a coercivity radius `δ(T) > 0`, `2δ(T)|w| ≤ |T w|` for injective `T`
  have hcoer : ∀ T : Euclid (k + 1) →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧
      (Injective T → ∀ w, 2 * (δ : ℝ) * ‖w‖ ≤ ‖T w‖) := by
    intro T
    by_cases hT : Injective T
    · obtain ⟨K, hKpos, hK⟩ := (T : Euclid (k + 1) →ₗ[ℝ] Euclid P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr hT)
      refine ⟨(2 * K)⁻¹, by positivity, fun _ w => ?_⟩
      have h := hK.le_mul_dist w 0
      simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h
      have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
      have h2 : 2 * (((2 * K)⁻¹ : NNReal) : ℝ) = (K : ℝ)⁻¹ := by
        push_cast
        field_simp
      rw [h2, inv_mul_le_iff₀ hK']
      exact h
    · exact ⟨1, one_pos, fun h => (hT h).elim⟩
  choose δ hδpos hδ using hcoer
  -- Mathlib's approximately-linear partition of `A⁺` with radius `δ`
  obtain ⟨t, T, hdisj, ht, hcover, happrox, hT⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H Ap (fderiv ℝ H)
      (fun u hu => (hdiff u hu).hasFDerivAt.hasFDerivWithinAt) δ (fun T => (hδpos T).ne')
  -- `H` is bi-Lipschitz with constant `δ(Tₗ)` on `Aₗ = A⁺ ∩ tₗ`
  have hbilip : ∀ l, ∀ a ∈ Ap ∩ t l, ∀ a' ∈ Ap ∩ t l,
      (δ (T l) : ℝ) * ‖a - a'‖ ≤ ‖H a - H a'‖ := by
    intro l a ha a' ha'
    obtain ⟨y, hy, hTy⟩ := hT ⟨a, ha.1⟩ l
    have h1 := hδ (T l) (hTy ▸ hinj y hy) (a - a')
    have h2 : ‖H a - H a' - T l (a - a')‖ ≤ δ (T l) * ‖a - a'‖ := happrox l a ha a' ha'
    have h3 := norm_sub_le (H a - H a') (H a - H a' - T l (a - a'))
    rw [sub_sub_cancel] at h3
    linarith
  -- step 4: the integer multiplicity piece currents `Φₗ`
  have hpiece : ∀ l, ∃ Φ : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1),
      IsIntegerMultiplicity Φ ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1),
        Φ ω = ∫ u in Ap ∩ t l, (g u : ℝ) * (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
          (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) ∧
      Φ.mass ≤ (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in Ap ∩ t l, ‖(g u : ℝ)‖ₑ := fun l =>
    hIC P (k + 1) L (δ (T l)) H (Ap ∩ t l) g hH (hApm.inter (ht l))
      (by exact_mod_cast hδpos (T l)) (hbilip l)
      (fun a ha => ⟨hdiff a ha.1, hinj a ha.1⟩) hg (fun a ha => hgne a ha.1)
      (hgi.mono_set (inter_subset_left.trans hApA))
  choose Φ hΦim hΦeq hΦmass using hpiece
  have hdisj' : Pairwise (Disjoint on fun l => Ap ∩ t l) :=
    fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right
  have hunion : (⋃ l, Ap ∩ t l) = Ap := by
    rw [← inter_iUnion]
    exact inter_eq_left.2 hcover
  -- step 5: `Σₗ M(Φₗ) ≤ Lⁿ ∫_A |g| < ∞`
  have hmass : ∑' l, (Φ l).mass < ∞ := by
    calc ∑' l, (Φ l).mass
        ≤ ∑' l, (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in Ap ∩ t l, ‖(g u : ℝ)‖ₑ :=
          ENNReal.tsum_le_tsum hΦmass
      _ = (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in Ap, ‖(g u : ℝ)‖ₑ := by
          rw [ENNReal.tsum_mul_left, ← lintegral_iUnion (fun l => hApm.inter (ht l)) hdisj',
            hunion]
      _ ≤ (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in A, ‖(g u : ℝ)‖ₑ := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hgi.2
  -- step 6: sum the pieces with (IMSc)
  obtain ⟨S, hS, -, -, hSim⟩ := hIMS P k Φ hmass
  refine ⟨S, hSim hΦim, fun ω => ?_⟩
  -- step 7: countable additivity identifies `S(ω) = ∫_{A⁺} Ψ_ω = ∫_A Ψ_ω`
  have h1 : HasSum (fun l => ∫ u in Ap ∩ t l, (g u : ℝ) *
      (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)))
      (∫ u in ⋃ l, Ap ∩ t l, (g u : ℝ) * (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) :=
    hasSum_integral_iUnion (fun l => hApm.inter (ht l)) hdisj'
      (by rw [hunion]; exact (hΨint ω).mono_set hApA)
  have h2 : HasSum (fun l => ∫ u in Ap ∩ t l, (g u : ℝ) *
      (ω : DifferentialForm (Euclid P) (k + 1)) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) (S ω) := by
    simpa only [hΦeq] using hS ω
  rw [h2.unique h1, hunion]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA hApA (hzero ω)).symm
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
/-- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
`n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
formula, and the Leibniz formula with `|x(l)| ≤ ‖x‖` gives `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`, so
`θ⁰` is continuous. -/
theorem Submission.cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
  intro P n I
  -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => x (I k)
      map_add' := fun x y => by
        funext k
        simp
      map_smul' := fun c x => by
        funext k
        simp }
  -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
  let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
  have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  -- Step 4: the Leibniz formula, `|sign σ| = 1` and `|x(l)| ≤ ‖x‖` give
  -- `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`
  have hbound : ∀ v : Fin n → Euclid P, ‖θ₀ v‖ ≤ (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
    intro v
    rw [hθ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, ‖v j‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| =
              ∏ j, |v j (I (σ j))| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [hσ]
          gcongr with j
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (v j) (I (σ j))
      _ = (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  -- Step 5: `θ = θ⁰.mkContinuous n!` is an `n`-covector with the same values as `θ⁰`
  exact ⟨θ₀.mkContinuous (n.factorial : ℝ) hbound, hθ₀⟩
/-- **Coordinate expansion of a `k`-covector** (the pointwise identity behind
`H^#ω(u)(e) = Σ_I ω_I(H(u)) det D(H^I)(u)`): for `f ∈ Λᵏ(ℝ^{N'})` and `u ∈ (ℝ^{N'})ᵏ`,
`k! f(u) = Σ_I f(e'_{I 0}, …, e'_{I (k-1)}) det (u_b (I c))_{c,b}`, the sum over all maps
`I : Fin k → Fin N'`.  Expand each `u_b = Σ_i u_b(i) e'_i` and use multilinearity; for each
permutation `σ` reindex `J = I ∘ σ` and use `f (v ∘ σ) = sign σ • f v`; average over the `k!`
permutations and recognize the Leibniz formula for the determinant. -/
theorem Submission.dor_lmb_fcd_jwc_covector_det_expansion : ∀ (N' k : ℕ) (f : Covector (Euclid N') k) (u : Fin k → Euclid N'), (k.factorial : ℝ) * f u = ∑ I : Fin k → Fin N', f (fun c => EuclideanSpace.single (I c) (1 : ℝ)) * Matrix.det (Matrix.of fun c b => u b (I c)) := by
  intro N' k f u
  set e : Fin N' → Euclid N' := fun i => EuclideanSpace.single i (1 : ℝ) with he
  -- step 1: multilinear expansion in the standard basis
  have h1 : f u = ∑ J : Fin k → Fin N', (∏ b, u b (J b)) * f (fun b => e (J b)) := by
    have hu : u = fun b => ∑ i, u b i • e i := by
      funext b
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N') ℝ).sum_repr (u b)]
      simp [he]
    conv_lhs => rw [hu]
    rw [show f (fun b => ∑ i, u b i • e i) = f.toMultilinearMap (fun b => ∑ i, u b i • e i) from rfl,
      MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [MultilinearMap.map_smul_univ]
    simp [smul_eq_mul]
  -- step 2: reindex by a permutation `σ`, using alternation
  have h2 : ∀ σ : Equiv.Perm (Fin k), f u = ∑ I : Fin k → Fin N',
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) := by
    intro σ
    rw [h1]
    rw [← Equiv.sum_comp ((σ.symm).arrowCongr (Equiv.refl (Fin N')))]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hperm : f (fun b => e (I (σ b))) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * f (fun c => e (I c)) := by
      have := f.toAlternatingMap.map_perm (fun c => e (I c)) σ
      simp only [Function.comp_def] at this
      rw [show f (fun b => e (I (σ b))) = f.toAlternatingMap (fun b => e (I (σ b))) from rfl, this,
        Units.smul_def, zsmul_eq_mul]
      rfl
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm, Function.comp_apply]
    rw [hperm]
    ring
  -- step 3: average over `σ` and recognize the Leibniz formula
  have h3 : (k.factorial : ℝ) * f u = ∑ σ : Equiv.Perm (Fin k), f u := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [h3]
  calc ∑ σ : Equiv.Perm (Fin k), f u
      = ∑ σ : Equiv.Perm (Fin k), ∑ I : Fin k → Fin N',
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_congr rfl fun σ _ => h2 σ
    _ = ∑ I : Fin k → Fin N', ∑ σ : Equiv.Perm (Fin k),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ b, u b (I (σ b))) * f (fun c => e (I c)) :=
        Finset.sum_comm
    _ = _ := ?_
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp only [Matrix.of_apply, he]
  ring
/-- **Weak-* convergence against `L¹` test functions** (density step of the weak continuity of
Jacobian minors): if `|F_j|, |F| ≤ C` and `∫ ψ F_j → ∫ ψ F` for every `C^∞` compactly supported
`ψ`, then `∫ φ F_j → ∫ φ F` for every integrable `φ`.  `C_c^∞` is dense in `L¹`: by
`MemLp.induction_dense` it suffices to approximate `c 1_s` with `μ(s) < ∞`; regularity gives
`K ⊆ s ⊆ U`, `K` compact, `U` open, `μ(U \ K)` small, and `c χ` works for a smooth Urysohn
function `χ` (`χ = 1` exactly on `K`, `support χ = U ∩ B_R(0)`).  (Mathlib's
`MemLp.exist_eLpNorm_sub_le` is outside the import closure.)  For `ε > 0` take such `ψ` with
`∫ |φ − ψ| ≤ η = ε/(4C + 1)`; then `|∫ φ F_j − ∫ φ F| ≤ 2Cη + |∫ ψ F_j − ∫ ψ F| < ε` for large
`j`. -/
theorem Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade : ∀ (k : ℕ) (C : ℝ) (Fs : ℕ → Euclid k → ℝ) (F : Euclid k → ℝ), (∀ j, AEStronglyMeasurable (Fs j) (volume : Measure (Euclid k))) → AEStronglyMeasurable F (volume : Measure (Euclid k)) → (∀ j x, |Fs j x| ≤ C) → (∀ x, |F x| ≤ C) → (∀ ψ : Euclid k → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → Tendsto (fun j => ∫ x, ψ x * Fs j x) atTop (𝓝 (∫ x, ψ x * F x))) → ∀ φ : Euclid k → ℝ, Integrable φ → Tendsto (fun j => ∫ x, φ x * Fs j x) atTop (𝓝 (∫ x, φ x * F x)) := by
  intro k C Fs F hFs hF hFsb hFb hconv φ hφ
  have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
  -- step 1: `C_c^∞` is dense in `L¹`; by `MemLp.induction_dense` only `c 1_s` needs approximating
  have hdense : ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ ψ : Euclid k → ℝ,
      eLpNorm (φ - ψ) 1 (volume : Measure (Euclid k)) ≤ ε ∧
        (ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ) := by
    intro ε hε
    refine MemLp.induction_dense ENNReal.one_ne_top
      (fun g => ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g) ?_ ?_
      (memLp_one_iff_integrable.2 hφ) hε
    · intro c s hs hμs ε' hε'
      -- `K ⊆ s ⊆ U` with `μ(U \ s), μ(s \ K) < δ/2`, `δ = ε'/‖c‖`
      set δ : ℝ≥0∞ := ε' / ‖c‖ₑ with hδ
      have hδ0 : δ ≠ 0 := by
        rw [hδ, Ne, ENNReal.div_eq_zero_iff, not_or]
        exact ⟨hε', enorm_ne_top⟩
      have hδ2 : δ / 2 ≠ 0 := (ENNReal.half_pos hδ0).ne'
      obtain ⟨K, hKs, hKc, hK⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hδ2
      obtain ⟨U, hsU, hUo, -, hU⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hδ2
      -- smooth Urysohn function `χ`: `χ = 1` on `K`, `support χ = U ∩ B_R(0)`, `0 ≤ χ ≤ 1`
      obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball (0 : Euclid k)
      obtain ⟨χ, hχd, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
        (hUo.inter isOpen_ball) hKc.isClosed (subset_inter (hKs.trans hsU) hR)
      have hχc : HasCompactSupport χ := by
        refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid k) R) (fun x hx => ?_)
        rw [← notMem_support, hχs]
        exact fun h => hx (ball_subset_closedBall h.2)
      refine ⟨fun x => c * χ x, ?_, contDiff_const.mul hχd, hχc.mul_left⟩
      -- `|c χ − c 1_s| ≤ |c| 1_{U \ K}`, so `‖c χ − c 1_s‖₁ ≤ ‖c‖ μ(U \ K) ≤ ‖c‖ δ ≤ ε'`
      have hle : ∀ x, ‖((fun x => c * χ x) - s.indicator fun _ => c) x‖ ≤
          ‖(U \ K).indicator (fun _ => c) x‖ := by
        intro x
        obtain ⟨h0, h1⟩ := hχr (mem_range_self x)
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        by_cases hxK : x ∈ K
        · rw [(hχ1 x).1 hxK, indicator_of_mem (hKs hxK)]
          simp
        by_cases hxU : x ∈ U
        · rw [indicator_of_mem (show x ∈ U \ K from ⟨hxU, hxK⟩)]
          by_cases hxs : x ∈ s
          · rw [indicator_of_mem hxs, show c * χ x - c = c * (χ x - 1) by ring, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg c) (by rw [abs_le]; constructor <;> linarith)
          · rw [indicator_of_notMem hxs, sub_zero, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg c) (by rw [abs_le]; constructor <;> linarith)
        · have hχ0 : χ x = 0 := by
            rw [← notMem_support, hχs]
            exact fun h => hxU h.1
          rw [hχ0, indicator_of_notMem (fun h => hxU (hsU h))]
          simp
      calc eLpNorm ((fun x => c * χ x) - s.indicator fun _ => c) 1 volume
          ≤ eLpNorm ((U \ K).indicator fun _ => c) 1 volume :=
            eLpNorm_mono (((contDiff_const.mul hχd).continuous.aestronglyMeasurable).sub
              (aestronglyMeasurable_const.indicator hs)) hle
        _ = ‖c‖ₑ * volume (U \ K) := by
          rw [eLpNorm_indicator_const (hUo.measurableSet.diff hKc.isClosed.measurableSet).nullMeasurableSet
            one_ne_zero ENNReal.one_ne_top]
          simp
        _ ≤ ‖c‖ₑ * δ := by
          gcongr
          calc volume (U \ K) ≤ volume ((U \ s) ∪ (s \ K)) := by
                refine measure_mono fun x hx => ?_
                by_cases hxs : x ∈ s
                · exact Or.inr ⟨hxs, hx.2⟩
                · exact Or.inl ⟨hx.1, hxs⟩
            _ ≤ volume (U \ s) + volume (s \ K) := measure_union_le _ _
            _ ≤ δ / 2 + δ / 2 := add_le_add hU.le hK.le
            _ = δ := ENNReal.add_halves δ
        _ ≤ ε' := ENNReal.mul_div_le
    · rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
      exact ⟨hf1.add hg1, hf2.add hg2⟩
  -- step 2: `|∫ θ G| ≤ C ∫ |θ|` for integrable `θ` and `|G| ≤ C`
  have hint : ∀ θ : Euclid k → ℝ, Integrable θ → ∀ G : Euclid k → ℝ,
      AEStronglyMeasurable G (volume : Measure (Euclid k)) → (∀ x, |G x| ≤ C) →
      Integrable (fun x => θ x * G x) ∧ |∫ x, θ x * G x| ≤ C * ∫ x, ‖θ x‖ := by
    intro θ hθ G hG hGb
    refine ⟨hθ.mul_bdd hG (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hGb x), ?_⟩
    calc |∫ x, θ x * G x| = ‖∫ x, θ x * G x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, C * ‖θ x‖ := by
          refine norm_integral_le_of_norm_le (hθ.norm.const_mul C) (Eventually.of_forall fun x => ?_)
          rw [norm_mul, Real.norm_eq_abs (G x), mul_comm]
          exact mul_le_mul_of_nonneg_right (hGb x) (norm_nonneg _)
      _ = C * ∫ x, ‖θ x‖ := integral_const_mul _ _
  -- step 3: `ψ ∈ C_c^∞` with `∫ |φ − ψ| ≤ η = ε/(4C + 1)`, and `N` from the convergence on `ψ`
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (4 * C + 1) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨ψ, hψε, hψs, hψc⟩ := hdense (ENNReal.ofReal_pos.2 hηpos).ne'
  have hψi : Integrable ψ := hψs.continuous.integrable_of_hasCompactSupport hψc
  have hdiff : ∫ x, ‖(φ - ψ) x‖ ≤ η := by
    have h1 := integral_norm_eq_lintegral_enorm (μ := (volume : Measure (Euclid k)))
      (hφ.sub hψi).aestronglyMeasurable
    rw [h1, ← eLpNorm_one_eq_lintegral_enorm]
    · exact ENNReal.toReal_le_of_le_ofReal hηpos.le hψε
    · exact (hφ.sub hψi).aestronglyMeasurable
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv ψ hψs hψc) (ε / 2) (by positivity)
  -- step 4: three-term estimate `|∫ φ F_j − ∫ φ F| ≤ 2Cη + |∫ ψ F_j − ∫ ψ F| < ε` for `j ≥ N`
  refine ⟨N, fun j hj => ?_⟩
  have h1 := hint (φ - ψ) (hφ.sub hψi) (Fs j) (hFs j) (hFsb j)
  have h2 := hint (φ - ψ) (hφ.sub hψi) F hF hFb
  have h3 := hint ψ hψi (Fs j) (hFs j) (hFsb j)
  have h4 := hint ψ hψi F hF hFb
  have e1 : ∫ x, φ x * Fs j x = (∫ x, (φ - ψ) x * Fs j x) + ∫ x, ψ x * Fs j x := by
    rw [← integral_add h1.1 h3.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have e2 : ∫ x, φ x * F x = (∫ x, (φ - ψ) x * F x) + ∫ x, ψ x * F x := by
    rw [← integral_add h2.1 h4.1]
    congr 1; funext x; simp only [Pi.sub_apply]; ring
  have hNj := hN j hj
  rw [Real.dist_eq] at hNj ⊢
  rw [e1, e2]
  have hCη : C * η < ε / 4 := by
    rw [hη, mul_div_assoc']
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hA := h1.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have hB := h2.2.trans (mul_le_mul_of_nonneg_left hdiff hC)
  have key : ∀ a1 b1 a2 b2 : ℝ, |(a1 + b1) - (a2 + b2)| ≤ |a1| + |a2| + |b1 - b2| := by
    intro a1 b1 a2 b2
    calc |(a1 + b1) - (a2 + b2)| = |(a1 - a2) + (b1 - b2)| := by ring_nf
      _ ≤ |a1 - a2| + |b1 - b2| := abs_add_le _ _
      _ ≤ |a1| + |a2| + |b1 - b2| := by
          have := abs_sub a1 a2
          linarith
  have := key (∫ x, (φ - ψ) x * Fs j x) (∫ x, ψ x * Fs j x) (∫ x, (φ - ψ) x * F x) (∫ x, ψ x * F x)
  linarith

/-- **The Piola identity** (the Jacobian minors are null Lagrangians): for `C²` functions
`g₀, …, g_{r-1}` on `ℝᵏ` and directions `V₀, …, V_r`, the minors
`M_b(y) = det (Dg_c(y) V_{s_b(b')})_{c,b'}` (`s_b = Fin.succAbove b`, so `V_b` is deleted) satisfy
`∑_b (-1)^b DM_b(x) V_b = 0`.  With `G = (g₀, …, g_{r-1})` and the constant determinant form
`θ = dy⁰ ∧ ⋯ ∧ dy^{r-1}` one has `M_b(y) = (G^*θ)(y)(V ∘ s_b)`, so the left side is
`d(G^*θ)(x)(V)`, and `d(G^*θ) = G^*(dθ) = 0` by the naturality of `d` (which is where the symmetry
of `D²G` enters). -/
theorem Submission.dor_lmb_fcd_jwc_piola_identity : ∀ (k r : ℕ) (g : Fin r → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (x : Euclid k), (∀ c, ContDiff ℝ 2 (g c)) → ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c) y (V (b.succAbove b')))) x (V b) = 0 := by
  intro k r g V x hg
  -- Step 1: the map `G = (g₀, …, g_{r-1}) : ℝᵏ → ℝʳ` is `C²`, and `(DG(y) w)_c = Dg_c(y) w`
  set e : (Fin r → ℝ) ≃L[ℝ] Euclid r := (EuclideanSpace.equiv (Fin r) ℝ).symm with he
  set G : Euclid k → Euclid r := fun y => e (fun c => g c y) with hG
  have hGc : ContDiff ℝ 2 G := e.contDiff.comp (contDiff_pi.2 hg)
  have hGd : ∀ y w (c : Fin r), fderiv ℝ G y w c = fderiv ℝ (g c) y w := by
    intro y w c
    have hpi : HasFDerivAt (fun y => fun c => g c y)
        (ContinuousLinearMap.pi fun c => fderiv ℝ (g c) y) y :=
      hasFDerivAt_pi.2 fun c => ((hg c).differentiable (by norm_num) y).hasFDerivAt
    have h := e.hasFDerivAt.comp y hpi
    rw [show G = e ∘ (fun y => fun c => g c y) from rfl, h.fderiv]
    simp [he]
  -- Step 2: the constant determinant form `Θ ≡ θ`, `θ(w) = det (w_b(c))_{c,b}`
  obtain ⟨θ, hθ⟩ := Submission.cmr_cc_det_covector_exists r r id
  set Θ : Euclid r → Covector (Euclid r) r := fun _ => θ with hΘ
  -- Step 3: `dΘ = 0`, since `DΘ = 0` and the alternatization is linear
  have hdΘ : extDeriv Θ (G x) = 0 := by
    simp [extDeriv, hΘ, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  -- Step 4: naturality of `d` gives `d(G^*Θ)(x) = (dΘ)(G x) ∘ DG(x) = 0`
  have hpull := extDeriv_pullback (ω := Θ) (f := G) (x := x) (r := 2) (differentiableAt_const θ)
    hGc.contDiffAt (by simp)
  rw [hdΘ] at hpull
  -- Step 5: the coordinate formula `d(G^*Θ)(x)(V) = ∑_b (-1)^b D[(G^*Θ)(·)(V ∘ s_b)](x) V_b`
  have hβd : DifferentiableAt ℝ (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)) x :=
    (differentiableAt_const θ).continuousAlternatingMapCompContinuousLinearMap
      ((hGc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  have happ := extDeriv_apply hβd V
  rw [hpull] at happ
  -- Step 6: `(G^*Θ)(y)(V ∘ s_b) = M_b(y)` by Steps 1 and 2
  have hβ : ∀ i : Fin (r + 1), (fun y => (Θ (G y)).compContinuousLinearMap (fderiv ℝ G y)
      (i.removeNth V)) = fun y => Matrix.det (Matrix.of fun (c b' : Fin r) =>
        fderiv ℝ (g c) y (V (i.succAbove b'))) := by
    intro i
    funext y
    simp only [hΘ, ContinuousAlternatingMap.compContinuousLinearMap_apply, hθ]
    congr 1
    ext c b'
    simp [Matrix.of_apply, Fin.removeNth, hGd]
  -- Step 7: hence `0 = d(G^*Θ)(x)(V) = ∑_b (-1)^b DM_b(x) V_b`
  simp only [hβ] at happ
  rw [eq_comm] at happ
  simpa [zsmul_eq_mul] using happ
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]
/-- **Jacobian minors of Lipschitz maps are measurable and bounded** (the integrands in the weak
continuity of Jacobian minors): if `g₀, …, g_{r-1}` are `L`-Lipschitz on `ℝᵏ` and
`V₀, …, V_{r-1} ∈ ℝᵏ`, then `D(x) = det (Dg_c(x) V_b)_{c,b}` is measurable and
`|D(x)| ≤ r! (L ∑_b ‖V_b‖)ʳ` for every `x`, where `Dg(x) = fderiv ℝ g x` (`0` where `g` is not
differentiable).  Each entry `x ↦ Dg_c(x) V_b` is measurable (`measurable_fderiv_apply_const`)
and bounded by `‖Dg_c(x)‖ ‖V_b‖ ≤ L ‖V_b‖ ≤ L ∑_b ‖V_b‖` (`norm_fderiv_le_of_lipschitz`); by the
Leibniz formula `D` is a signed sum of `r!` products of `r` entries, which gives both claims.
(`Matrix.det_le` is outside the import closure, so the bound is done by hand.) -/
theorem Submission.dor_lmb_fcd_jwc_minor_measurable_bound : ∀ (k r : ℕ) (L : NNReal) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k), (∀ c, LipschitzWith L (g c)) → Measurable (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))) ∧ ∀ x, |Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b))| ≤ (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r := by
  intro k r L g V hg
  -- Leibniz formula: `D(x) = ∑_σ sign σ ∏_b Dg_{σ b}(x) V_b`
  have hdet : ∀ x, Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b) :=
    fun x => Matrix.det_apply' _
  refine ⟨?_, fun x => ?_⟩
  · -- steps 1–2: the entries are measurable, hence so is the signed sum of their products
    have hm : Measurable fun x => ∑ σ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b) :=
      Finset.measurable_sum _ fun σ _ => measurable_const.mul
        (Finset.measurable_prod _ fun b _ => measurable_fderiv_apply_const ℝ (g (σ b)) (V b))
    simpa only [hdet] using hm
  · -- step 3: every entry is bounded by `s = L ∑_b ‖V_b‖`
    have hent : ∀ c b, |fderiv ℝ (g c) x (V b)| ≤ (L : ℝ) * ∑ b, ‖V b‖ := by
      intro c b
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (g c) x (V b)‖ ≤ ‖fderiv ℝ (g c) x‖ * ‖V b‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * ‖V b‖ :=
            mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hg c)) (norm_nonneg _)
        _ ≤ L * ∑ b, ‖V b‖ := by
            gcongr
            exact Finset.single_le_sum (f := fun b => ‖V b‖) (fun b _ => norm_nonneg _)
              (Finset.mem_univ b)
    -- step 4: the triangle inequality and `|sign σ| = 1` give `|D(x)| ≤ ∑_σ sʳ = r! sʳ`
    rw [hdet]
    calc |∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b)|
        ≤ ∑ σ : Equiv.Perm (Fin r),
            |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ b, fderiv ℝ (g (σ b)) x (V b)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm (Fin r), ∏ b, |fderiv ℝ (g (σ b)) x (V b)| := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [abs_mul, Finset.abs_prod]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      _ ≤ ∑ _σ : Equiv.Perm (Fin r), ∏ _b : Fin r, (L : ℝ) * ∑ b, ‖V b‖ := by
          gcongr with σ _ b _
          exact hent (σ b) b
      _ = (r.factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ r := by
          rw [Finset.sum_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
/-- **Derivative of the mollification of a Lipschitz function**: for an `L`-Lipschitz `f` and a
`C¹` kernel `ρ` with compact support, `D(ρ ⋆ f)(x) v = ∫ ρ(t) Df(x − t) v dt`.  Differentiating
under the integral (`HasCompactSupport.hasFDerivAt_convolution_left`) gives
`D(ρ ⋆ f)(x) v = ∫ Dρ(t) v · f(x − t) dt`.  With `t = x − s` and the reflected kernel
`h(s) = ρ(x − s)` (`C¹` with compact support, hence Lipschitz, and `∂_{−v} h(s) = Dρ(x − s) v`)
the two sides become `∫ ∂_{−v} h · f` and `∫ h · Df(·) v`; they agree by integration by parts for
Lipschitz functions (`LipschitzWith.integral_lineDeriv_mul_eq`: `∫ ∂_v f · h = ∫ ∂_{−v} h · f`)
and Rademacher (`∂_v f = Df · v` a.e.). -/
theorem Submission.dimred_mbl_dt_lp_jc_mollify_fderiv_eq : ∀ (k : ℕ) (L : NNReal) (f ρ : Euclid k → ℝ), LipschitzWith L f → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x v : Euclid k, fderiv ℝ (fun y => ∫ t, ρ t * f (y - t)) x v = ∫ t, ρ t * fderiv ℝ f (x - t) v := by
  intro k L f ρ hf hρ hρs x v
  have hconv : (fun y => ∫ t, ρ t * f (y - t)) =
      convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext y; simp [convolution_def]
  have hD := hρs.hasFDerivAt_convolution_left (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ) hρ
    hf.continuous.locallyIntegrable x
  have hint := (hρs.fderiv (𝕜 := ℝ)).convolutionExists_left (μ := (volume : Measure (Euclid k)))
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Euclid k)) (hρ.continuous_fderiv (by norm_num))
    (hf.continuous.locallyIntegrable (μ := (volume : Measure (Euclid k)))) x
  rw [hconv, hD.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- change of variables `t ↦ x - t` on both sides
  rw [← integral_sub_left_eq_self (fun t => fderiv ℝ ρ t v * f (x - t)) (μ := volume) x,
    ← integral_sub_left_eq_self (fun t => ρ t * fderiv ℝ f (x - t) v) (μ := volume) x]
  simp only [sub_sub_cancel]
  -- integration by parts against `h(s) = ρ(x - s)`
  set h : Euclid k → ℝ := fun s => ρ (x - s) with hh
  have hhC1 : ContDiff ℝ 1 h := hρ.comp (contDiff_const.sub contDiff_id)
  have hhs : HasCompactSupport h := hρs.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hhL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hhs hhC1 (by norm_num)
  have hibp := hf.integral_lineDeriv_mul_eq (μ := volume) hhL hhs v
  have hlh : ∀ s, lineDeriv ℝ h s (-v) = fderiv ℝ ρ (x - s) v := by
    intro s
    rw [(hhC1.differentiable (by norm_num) s).lineDeriv_eq_fderiv]
    have h1 : HasFDerivAt h (-(fderiv ℝ ρ (x - s))) s := by
      have := (hρ.differentiable (by norm_num) (x - s)).hasFDerivAt.comp s
        ((hasFDerivAt_const x s).sub (hasFDerivAt_id s))
      simpa [hh, Function.comp_def] using this
    rw [h1.fderiv]
    simp
  -- Rademacher: `∂_v f = Df · v` almost everywhere
  have hlf : ∀ᵐ s ∂(volume : Measure (Euclid k)), lineDeriv ℝ f s v = fderiv ℝ f s v := by
    filter_upwards [hf.ae_differentiableAt] with s hs
    exact hs.lineDeriv_eq_fderiv
  simp only [hlh] at hibp
  rw [← hibp]
  refine integral_congr_ae ?_
  filter_upwards [hlf] with s hs
  rw [hs, hh]
  ring
/-- **Smooth approximation of a Lipschitz function** (step 4 of the weak continuity of Jacobians):
an `L`-Lipschitz `f : ℝᵏ → ℝ` is the uniform limit of `C^∞`, `L`-Lipschitz functions `f_n` with
`Df_n(x) → Df(x)` in operator norm for a.e. `x`.  Take `f_n = ρ_n ⋆ f`, where `ρ_n = φ_n / ∫ φ_n`
normalizes a bump `φ_n` equal to `1` on `B(0, 1/(n+2))` and supported in `B(0, 2/(n+2))`.  Then
`f_n` is smooth, `L`-Lipschitz (`cmcs_ls_mollify_lipschitz`) and `|f_n - f| ≤ 2L/(n+2)`.  By
`dimred_mbl_dt_lp_jc_mollify_fderiv_eq`, `Df_n(x) eᵢ = (ρ_n ⋆ Df(·) eᵢ)(x)`; as `∫ φ_n ≥ |B(0, 1/(n+2))|`
gives `0 ≤ ρ_n ≤ 2ᵈ / |B(0, 2/(n+2))|`, this tends to `Df(x) eᵢ` at every Lebesgue point of the
bounded function `Df(·) eᵢ`, and `‖T‖ ≤ ∑ᵢ |T eᵢ|` gives convergence in operator norm. -/
theorem Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  intro k L f hf
  -- step 1: bumps `φ n` with `rIn = 1/(n+2)`, `rOut = 2/(n+2)`, normalized to `ρ n = φ n / ∫ φ n`
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  let φ : ℕ → ContDiffBump (0 : Euclid k) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by have := hpos n; positivity,
      div_lt_div_of_pos_right (by norm_num) (hpos n)⟩
  have hrOut : ∀ n, (φ n).rOut = 2 * (φ n).rIn := fun n => by
    show 2 / ((n : ℝ) + 2) = 2 * (1 / ((n : ℝ) + 2))
    rw [mul_one_div]
  -- `|B(x, r)| = r ^ d * c` with `c = |B(0, 1)| > 0`
  set d := Module.finrank ℝ (Euclid k)
  set c := (volume : Measure (Euclid k)).real (closedBall 0 1)
  have hcpos : 0 < c := ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne'
    measure_closedBall_lt_top.ne
  have hvol : ∀ (x : Euclid k) (r : ℝ), 0 ≤ r →
      (volume : Measure (Euclid k)).real (closedBall x r) = r ^ d * c :=
    fun x r hr => Measure.addHaar_real_closedBall' _ x hr
  -- `φ n = 1` on `B(0, rIn)` and `φ n ≥ 0`, so `∫ φ n ≥ |B(0, rIn)| = rIn ^ d * c > 0`
  have hφint : ∀ n, Integrable (φ n) (volume : Measure (Euclid k)) := fun n =>
    (φ n).continuous.integrable_of_hasCompactSupport (φ n).hasCompactSupport
  have hIge : ∀ n, (φ n).rIn ^ d * c ≤ ∫ x, φ n x := by
    intro n
    rw [← hvol 0 _ (φ n).rIn_pos.le]
    calc (volume : Measure (Euclid k)).real (closedBall 0 (φ n).rIn)
        = ∫ x in closedBall (0 : Euclid k) (φ n).rIn, φ n x := by
          rw [setIntegral_congr_fun measurableSet_closedBall
            (fun x hx => (φ n).one_of_mem_closedBall hx), setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ ∫ x, φ n x :=
          setIntegral_le_integral (hφint n) (Eventually.of_forall fun x => (φ n).nonneg)
  have hIpos : ∀ n, 0 < ∫ x, φ n x := fun n =>
    (mul_pos (pow_pos (φ n).rIn_pos d) hcpos).trans_le (hIge n)
  set ρ : ℕ → Euclid k → ℝ := fun n x => φ n x / ∫ y, φ n y with hρ
  have hρc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρc1 : ∀ n, ContDiff ℝ 1 (ρ n) := fun n => (φ n).contDiff.div_const _
  have hρcont : ∀ n, Continuous (ρ n) := fun n => (φ n).continuous.div_const _
  have hρs : ∀ n, HasCompactSupport (ρ n) := fun n =>
    (φ n).hasCompactSupport.comp_left (g := fun t : ℝ => t / ∫ y, φ n y) (zero_div _)
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n x => div_nonneg (φ n).nonneg (hIpos n).le
  have hρint : ∀ n, ∫ x, ρ n x = 1 := fun n => by
    show ∫ x, φ n x / ∫ y, φ n y = 1
    rw [integral_div, div_self (hIpos n).ne']
  have hρsupp : ∀ n, support (ρ n) ⊆ ball 0 (φ n).rOut := fun n x hx => by
    rw [← (φ n).support_eq, mem_support]
    intro h0
    exact (mem_support.1 hx) (by simp [hρ, h0])
  have hρle : ∀ n x, ρ n x ≤ 1 / ((φ n).rIn ^ d * c) := fun n x =>
    calc ρ n x = φ n x / ∫ y, φ n y := rfl
      _ ≤ 1 / ∫ y, φ n y := div_le_div_of_nonneg_right (φ n).le_one (hIpos n).le
      _ ≤ 1 / ((φ n).rIn ^ d * c) :=
          one_div_le_one_div_of_le (mul_pos (pow_pos (φ n).rIn_pos d) hcpos) (hIge n)
  -- `f_n = ρ n ⋆ f`
  set fs : ℕ → Euclid k → ℝ := fun n x => ∫ t, ρ n t * f (x - t) with hfs
  have hconv : ∀ n, fs n = convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro n; funext x; simp [hfs, convolution_def]
  have hrOut0 : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := tendsto_const_nhds (x := (2 : ℝ)) |>.div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [φ] using this
  refine ⟨fs, fun n => ?_, fun n => ?_, ?_, ?_⟩
  · -- step 2: `ρ n ⋆ f` is smooth
    rw [hconv]
    exact (hρs n).contDiff_convolution_left _ (hρc n) hf.continuous.locallyIntegrable
  · -- step 3: `ρ n ⋆ f` is `L`-Lipschitz
    exact Submission.cmcs_ls_mollify_lipschitz k (ρ n) f L (hρcont n) (hρs n) (hρ0 n) (hρint n) hf
  · -- step 4: `|f_n x - f x| ≤ L * rOut` for all `x`, and `rOut → 0`
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(hrOut0.const_mul (L : ℝ)).eventually (gt_mem_nhds (by simpa using hε))]
      with n hn x
    have hdist := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := f x) (g := f)
      (by positivity : (0 : ℝ) ≤ L * (φ n).rOut) (hρsupp n) (hρ0 n) (hρint n)
      hf.continuous.aestronglyMeasurable (fun y hy => by
        calc dist (f y) (f x) ≤ L * dist y x := hf.dist_le_mul y x
          _ ≤ L * (φ n).rOut := by gcongr; exact (mem_ball.1 hy).le)
    rw [← hconv] at hdist
    rw [dist_comm]
    exact lt_of_le_of_lt hdist hn
  · -- step 5: `Df_n(x) v = ∫ ρ n t * Df(x - t) v dt`
    have hB1 : ∀ n x v, fderiv ℝ (fs n) x v = ∫ t, ρ n t * fderiv ℝ f (x - t) v := fun n x v =>
      Submission.dimred_mbl_dt_lp_jc_mollify_fderiv_eq k L f (ρ n) hf (hρc1 n) (hρs n) x v
    have hδ : Tendsto (fun n => (φ n).rOut) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hrOut0, Eventually.of_forall fun n => (φ n).rOut_pos⟩
    -- steps 6-7: for each basis vector `e_i`, `Df_n(x) e_i → Df(x) e_i` for a.e. `x`
    have hDi : ∀ i : Fin k, ∀ᵐ x ∂(volume : Measure (Euclid k)),
        Tendsto (fun n => fderiv ℝ (fs n) x (EuclideanSpace.single i (1 : ℝ))) atTop
          (𝓝 (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)))) := by
      intro i
      set g : Euclid k → ℝ := fun s => fderiv ℝ f s (EuclideanSpace.single i (1 : ℝ)) with hg
      have hloc : LocallyIntegrable g (volume : Measure (Euclid k)) := by
        refine (locallyIntegrable_const ((L : ℝ) * ‖EuclideanSpace.single i (1 : ℝ)‖)).mono
          ((measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable)
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs (_ * _), abs_of_nonneg (by positivity)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      -- Lebesgue differentiation: `⨍_{B(x, r)} |g - g x| → 0` as `r → 0`, for a.e. `x`
      filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc 1]
        with x hx
      have havg := hx (fun _ => x) (fun n => (φ n).rOut) hδ
        (Eventually.of_forall fun n => mem_closedBall_self (by simpa using (φ n).rOut_pos.le))
      -- `0 ≤ ρ n (x - ·) ≤ 2 ^ d / |B(x, rOut)|`, supported in `B(x, rOut)`, with integral `1`
      have key := tendsto_integral_smul_of_tendsto_average_norm_sub ((2 : ℝ) ^ d) havg
        (g := fun n y => ρ n (x - y))
        (Eventually.of_forall fun n => hloc.integrableOn_isCompact (isCompact_closedBall _ _))
        (tendsto_const_nhds.congr fun n => by
          rw [integral_sub_left_eq_self (ρ n) volume x, hρint n])
        (Eventually.of_forall fun n y hy => by
          have hy' : x - y ∈ ball (0 : Euclid k) (φ n).rOut := hρsupp n hy
          rw [mem_ball, dist_zero_right] at hy'
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact hy'.le)
        (Eventually.of_forall fun n y => by
          rw [abs_of_nonneg (hρ0 n _), hvol x _ (φ n).rOut_pos.le, hrOut n]
          calc ρ n (x - y) ≤ 1 / ((φ n).rIn ^ d * c) := hρle n _
            _ = 2 ^ d / ((2 * (φ n).rIn) ^ d * c) := by
              rw [mul_pow]
              field_simp)
      refine key.congr fun n => ?_
      rw [hB1, ← integral_sub_left_eq_self (fun y => ρ n (x - y) • g y) volume x]
      simp only [sub_sub_cancel, smul_eq_mul, hg]
    filter_upwards [ae_all_iff.2 hDi] with x hx
    -- step 8: `‖T‖ ≤ ∑ᵢ |T eᵢ|`, so convergence on the basis gives convergence in norm
    have hbound : ∀ T : Euclid k →L[ℝ] ℝ, ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound T (Finset.sum_nonneg fun i _ => norm_nonneg _)
        fun w => ?_
      have hw : w = ∑ i, w i • EuclideanSpace.single i (1 : ℝ) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr w]
        simp
      calc ‖T w‖ = ‖∑ i, w i • T (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hw]
            simp [map_sum, map_smul]
        _ ≤ ∑ i, ‖w i • T (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
        _ = ∑ i, ‖w i‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by simp
        _ ≤ ∑ i, ‖w‖ * ‖T (EuclideanSpace.single i (1 : ℝ))‖ := by
            gcongr with i
            exact PiLp.norm_apply_le w i
        _ = (∑ i, ‖T (EuclideanSpace.single i (1 : ℝ))‖) * ‖w‖ := by
            rw [Finset.sum_mul]; simp [mul_comm]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => hbound _) ?_
    have : Tendsto (fun n => ∑ i : Fin k, ‖(fderiv ℝ (fs n) x - fderiv ℝ f x)
        (EuclideanSpace.single i (1 : ℝ))‖) atTop (𝓝 (∑ i : Fin k, (0 : ℝ))) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hx i)
      simpa using this
    simpa using this
/-- **Integration by parts for Jacobian minors** (formula (∗) of the weak continuity of Jacobian
minors, for `C²` maps): for `C²` functions `g₀, …, g_r` on `ℝᵏ`, directions `V₀, …, V_r` and a
compactly supported `C¹` function `ψ`, with `A = (Dg_c V_b)_{c,b}` and `M_b` the minor of `A`
without row `0` and column `b`, `∫ ψ det A = −Σ_b (−1)^b ∫ (Dψ V_b) g₀ M_b`.  Laplace expansion
along row `0`, the product rule for `F_b = ψ g₀ M_b` and the Piola identity
`Σ_b (−1)^b ∂_{V_b} M_b = 0` give `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
pointwise, and `∫ ∂_W F = 0` for every compactly supported `C¹` function `F` (integration by
parts of the Lipschitz functions `1` and `F`). -/
theorem Submission.dimred_mbl_dt_lp_jc_smooth_minor_ibp : ∀ (k r : ℕ) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, ContDiff ℝ 2 (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r g V ψ hg hψ hψs
  -- Step 2: the entries `Dg_c(·)W` are `C¹` (`g_c` is `C²`), hence so is every determinant of
  -- such entries (Leibniz formula), in particular every minor `M_b`
  have hdetC1 : ∀ {m : ℕ} (A : Euclid k → Fin m → Fin m → ℝ),
      (∀ i j, ContDiff ℝ 1 (fun x => A x i j)) →
      ContDiff ℝ 1 (fun x => Matrix.det (Matrix.of (A x))) := by
    intro m A hA
    have hLeib : (fun x => Matrix.det (Matrix.of (A x))) =
        fun x => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A x (σ i) i := by
      funext x
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      simp [Matrix.of_apply]
    rw [hLeib]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hA _ _)
  have hentry : ∀ c (W : Euclid k), ContDiff ℝ 1 (fun x => fderiv ℝ (g c) x W) := fun c W =>
    ((hg c).fderiv_right (by norm_num)).clm_apply contDiff_const
  set M : Fin (r + 1) → Euclid k → ℝ := fun b x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
    fderiv ℝ (g c.succ) x (V (b.succAbove b')))
  have hMC1 : ∀ b, ContDiff ℝ 1 (M b) := fun b =>
    hdetC1 (fun x c b' => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) fun c b' => hentry _ _
  -- `F_b = ψ g₀ M_b` is `C¹` with compact support
  have hFC1 : ∀ b, ContDiff ℝ 1 (fun y => ψ y * g 0 y * M b y) := fun b =>
    (hψ.mul ((hg 0).of_le (by norm_num))).mul (hMC1 b)
  have hFs : ∀ b, HasCompactSupport (fun y => ψ y * g 0 y * M b y) := fun b =>
    hψs.mul_right.mul_right
  -- Step 3: product rule for `∂_{V_b} F_b`
  have hdiff : ∀ b x, fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) =
      fderiv ℝ ψ x (V b) * g 0 x * M b x + ψ x * fderiv ℝ (g 0) x (V b) * M b x +
        ψ x * g 0 x * fderiv ℝ (M b) x (V b) := by
    intro b x
    have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
    have hgd : DifferentiableAt ℝ (g 0) x := (hg 0).differentiable (by norm_num) x
    have hMd : DifferentiableAt ℝ (M b) x := (hMC1 b).differentiable (by norm_num) x
    have h : HasFDerivAt (fun y => ψ y * g 0 y * M b y) _ x :=
      (hψd.hasFDerivAt.mul hgd.hasFDerivAt).mul hMd.hasFDerivAt
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, Pi.mul_apply]
    ring
  -- Steps 1, 4, 5: Laplace expansion along row `0` and the Piola identity give, pointwise,
  -- `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
  have hpt : ∀ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) =
      ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) := by
    intro x
    have hp : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) = 0 :=
      Submission.dor_lmb_fcd_jwc_piola_identity k r (fun c => g c.succ) V x fun c => hg c.succ
    simp_rw [hdiff]
    have halg : ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x +
          ψ x * fderiv ℝ (g 0) x (V b) * M b x + ψ x * g 0 x * fderiv ℝ (M b) x (V b)) -
        ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * (fderiv ℝ ψ x (V b) * g 0 x * M b x) =
        ψ x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (g 0) x (V b) * M b x +
          ψ x * g 0 x * ∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * fderiv ℝ (M b) x (V b) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [halg, hp, mul_zero, add_zero, Matrix.det_succ_row_zero]
    rfl
  -- Step 6: `∫ ∂_W F = 0` for `C¹` compactly supported `F` (integration by parts of the
  -- Lipschitz functions `1` and `F`)
  have hIBP0 : ∀ F : Euclid k → ℝ, ContDiff ℝ 1 F → HasCompactSupport F → ∀ W,
      ∫ x, fderiv ℝ F x W = 0 := by
    intro F hF hFs W
    obtain ⟨C, hFL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hFs hF (by norm_num)
    have h := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid k)))
      (LipschitzWith.const (1 : ℝ)) hFL hFs (-W)
    have h0 : ∀ x : Euclid k, lineDeriv ℝ (fun _ : Euclid k => (1 : ℝ)) x (-W) = 0 := by
      intro x
      rw [(differentiableAt_const (1 : ℝ)).lineDeriv_eq_fderiv]
      simp
    have h1 : ∀ x, lineDeriv ℝ F x W = fderiv ℝ F x W := fun x =>
      (hF.differentiable (by norm_num) x).lineDeriv_eq_fderiv
    simp only [h0, zero_mul, integral_zero, neg_neg, mul_one, h1] at h
    exact h.symm
  -- Step 7: every term is continuous with compact support, hence integrable; integrate
  have hi1 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b)) := fun b =>
    ((((hFC1 b).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hFs b).fderiv_apply ℝ (V b))).const_mul _
  have hi2 : ∀ b : Fin (r + 1), Integrable (fun x => (-1 : ℝ) ^ (b : ℕ) *
      (fderiv ℝ ψ x (V b) * g 0 x * M b x)) := fun b =>
    (((((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hg 0).continuous).mul (hMC1 b).continuous).integrable_of_hasCompactSupport
      ((hψs.fderiv_apply ℝ (V b)).mul_right.mul_right)).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_sub (integrable_finsetSum _ fun b _ => hi1 b)
      (integrable_finsetSum _ fun b _ => hi2 b),
    integral_finsetSum _ fun b _ => hi1 b, integral_finsetSum _ fun b _ => hi2 b]
  have hz : ∑ b : Fin (r + 1), ∫ x, (-1 : ℝ) ^ (b : ℕ) *
      fderiv ℝ (fun y => ψ y * g 0 y * M b y) x (V b) = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [integral_const_mul, hIBP0 _ (hFC1 b) (hFs b) _, mul_zero]
  rw [hz, zero_sub]
  simp only [integral_const_mul]
  rfl

/-- **Integration by parts for Jacobian minors of Lipschitz maps** (the step "`(∗)` holds for
Lipschitz `v`" in the weak continuity of Jacobian minors): for `L`-Lipschitz `g₀, …, g_r` on `ℝᵏ`,
vectors `V₀, …, V_r` and `ψ ∈ C¹_c(ℝᵏ)`,
`∫ ψ det A = −Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, where `A = (Dg_c V_b)_{c,b}` and `M_b` is the minor
`det (Dg_{c+1} V_{s_b(b')})_{c,b'}`, `s_b = b.succAbove`.  Mollify every `g_c`: `C^∞`, `L`-Lipschitz
`g^n_c → g_c` uniformly with `Dg^n_c → Dg_c` a.e.  The identity holds for every `n` (smooth case);
the determinants converge a.e. and are bounded by `(r+1)! (L Σ_b ‖V_b‖)^(r+1)`, resp.
`r! (L Σ_b' ‖V_{s_b(b')}‖)^r`, so both sides converge by dominated convergence (on the right with
`|g^n_0| ≤ |g_0| + 1` for large `n`), and the limits agree. -/
theorem Submission.dimred_mbl_dt_lp_jc_lipschitz_minor_ibp : ∀ (k r : ℕ) (L : NNReal) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, LipschitzWith L (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r L g V ψ hg hψ hψs
  -- step 1: smooth `L`-Lipschitz approximants `fs c n` of every component `g c`
  choose fs hfs_smooth hfs_lip hfs_unif hfs_ae using
    fun c => Submission.dimred_mbl_dt_lp_jc_lipschitz_smooth_approx k L (g c) (hg c)
  -- step 2: the identity for the smooth maps `fs · n`
  have hid := fun n => Submission.dimred_mbl_dt_lp_jc_smooth_minor_ibp k r (fun c => fs c n) V ψ
    (fun c => (hfs_smooth c n).of_le (by simp)) hψ hψs
  -- step 3: off a null set all derivatives converge, hence so do the entries and determinants
  have hae : ∀ᵐ x ∂(volume : Measure (Euclid k)), ∀ c,
      Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x)) := ae_all_iff.2 hfs_ae
  have hdet_lim : ∀ {m : ℕ} (σ : Fin m → Fin (r + 1)) (W : Fin m → Euclid k) (x : Euclid k),
      (∀ c, Tendsto (fun n => fderiv ℝ (fs c n) x) atTop (𝓝 (fderiv ℝ (g c) x))) →
      Tendsto (fun n => Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.det (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b)))) := by
    intro m σ W x hx
    have hM : Tendsto (fun n => (Matrix.of fun (c b : Fin m) => fderiv ℝ (fs (σ c) n) x (W b)))
        atTop (𝓝 (Matrix.of fun (c b : Fin m) => fderiv ℝ (g (σ c)) x (W b))) := by
      refine tendsto_pi_nhds.2 fun c => tendsto_pi_nhds.2 fun b => ?_
      exact ((ContinuousLinearMap.apply ℝ ℝ (W b)).continuous.tendsto _).comp (hx (σ c))
    exact ((continuous_id.matrix_det).tendsto _).comp hM
  -- step 4: the bound `B` of the full determinants and the integrability of `ψ`
  set B : ℝ := ((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1)
  have hψc : Continuous ψ := hψ.continuous
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  -- step 5: the left side converges, dominated by `B |ψ|`
  have hL : Tendsto
      (fun n => ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (fs c n) x (V b)))
      atTop (𝓝 (∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => B * ‖ψ x‖) (fun n => ?_)
      (hψi.norm.const_mul B) (fun n => Eventually.of_forall fun x => ?_) ?_
    · exact hψc.aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
          (fun c => hfs_lip c n)).1.aestronglyMeasurable
    · have h := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (fun c => fs c n) V
        (fun c => hfs_lip c n)).2 x
      rw [norm_mul, Real.norm_eq_abs (Matrix.det _), mul_comm]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · filter_upwards [hae] with x hx
      exact tendsto_const_nhds.mul (hdet_lim id V x hx)
  -- step 6: each term of the right side converges, dominated by `Br |∂_{V_b}ψ| (|g 0| + 1)`
  have hR : ∀ b : Fin (r + 1), Tendsto (fun n => ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x *
      Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) := by
    intro b
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) := hψs.fderiv_apply (𝕜 := ℝ) (V b)
    have hwi : Integrable (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1))) := by
      refine Integrable.const_mul ?_ _
      exact Continuous.integrable_of_hasCompactSupport
        (hdψc.norm.mul ((hg 0).continuous.norm.add continuous_const)) hdψs.norm.mul_right
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)))
      (Eventually.of_forall fun n => ?_) ?_ hwi ?_
    · exact (hdψc.mul (hfs_smooth 0 n).continuous).aestronglyMeasurable.mul
        (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
          (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).1.aestronglyMeasurable
    · -- `|fs 0 n| ≤ |g 0| + 1` once `fs 0 n` is uniformly `1`-close to `g 0`
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hfs_unif 0) 1 one_pos).exists_forall_of_atTop
      refine eventually_atTop.2 ⟨N, fun n hn => Eventually.of_forall fun x => ?_⟩
      have h1 : ‖fs 0 n x‖ ≤ ‖g 0 x‖ + 1 := by
        have := hN n hn x
        rw [dist_comm, dist_eq_norm] at this
        have := norm_le_insert' (fs 0 n x) (g 0 x)
        linarith
      have h2 := (Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L (fun c => fs c.succ n)
        (fun b' => V (b.succAbove b')) (fun c => hfs_lip c.succ n)).2 x
      rw [norm_mul, norm_mul, Real.norm_eq_abs (Matrix.det _)]
      calc ‖fderiv ℝ ψ x (V b)‖ * ‖fs 0 n x‖ * |Matrix.det _|
          ≤ ‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1) * Br := by gcongr
        _ = Br * (‖fderiv ℝ ψ x (V b)‖ * (‖g 0 x‖ + 1)) := by ring
    · filter_upwards [hae] with x hx
      refine (tendsto_const_nhds.mul ((hfs_unif 0).tendsto_at x)).mul ?_
      exact hdet_lim Fin.succ (fun b' => V (b.succAbove b')) x hx
  have hRall : Tendsto (fun n => -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) *
      ∫ x, fderiv ℝ ψ x (V b) * fs 0 n x * Matrix.det
        (Matrix.of fun (c b' : Fin r) => fderiv ℝ (fs c.succ n) x (V (b.succAbove b'))))
      atTop (𝓝 (-∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x *
        Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) :=
    Tendsto.neg (tendsto_finsetSum _ fun b _ => (hR b).const_mul _)
  -- step 7: both sides of step 2 agree for every `n`, so their limits agree
  exact tendsto_nhds_unique hL (hRall.congr fun n => (hid n).symm)
/-- **Weak continuity of Jacobian minors** (null Lagrangians; Reshetnyak 1967, Ball 1977): if the
`L`-Lipschitz `gʲ_c` converge uniformly to the `L`-Lipschitz `g_c` on `ℝᵏ` (`c < r`), then
`∫ φ det(Dgʲ_c V_b) → ∫ φ det(Dg_c V_b)` for every `φ ∈ L¹`.  Induction on `r`; for `r = 0` both
determinants are `1`.  For `r + 1` the minors are measurable and bounded by
`(r+1)! (L Σ_b ‖V_b‖)^{r+1}`, so by the weak-* to `L¹` upgrade it suffices to take `φ = ψ ∈ C^∞_c`.
Integration by parts in the first row writes `∫ ψ det(Dg_c V_b)` as
`−Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, `M_b` the minor of the rows `c ≥ 1` and the columns `≠ b`.
Split `gʲ₀ = (gʲ₀ − g₀) + g₀`: the first part is at most
`r! (L Σ_{b'} ‖V_{b'}‖)^r sup |gʲ₀ − g₀| ∫ |∂_{V_b}ψ| → 0`, and the second converges by the
induction hypothesis with the continuous compactly supported weight `∂_{V_b}ψ · g₀`. -/
theorem Submission.dimred_mbl_dt_lp_jc_minor_weak_continuity : ∀ (k r : ℕ) (L : NNReal) (gs : ℕ → Fin r → Euclid k → ℝ) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k) (φ : Euclid k → ℝ), Integrable φ → (∀ j c, LipschitzWith L (gs j c)) → (∀ c, LipschitzWith L (g c)) → (∀ c, TendstoUniformly (fun j => gs j c) (g c) atTop) → Tendsto (fun j => ∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b))) atTop (𝓝 (∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
  intro k r
  induction r with
  | zero =>
    -- the empty determinant is `1`
    intro L gs g V φ hφ hgs hg hU
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro L gs g V φ hφ hgs hg hU
    -- Step 2: the minors are bounded, so it suffices to test against `ψ ∈ C^∞_c`
    have hb := fun (G : Fin (r + 1) → Euclid k → ℝ) (hG : ∀ c, LipschitzWith L (G c)) =>
      Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L G V hG
    refine Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade k
      (((r + 1).factorial : ℝ) * ((L : ℝ) * ∑ b, ‖V b‖) ^ (r + 1))
      (fun j x => Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b)))
      (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))
      (fun j => (hb (gs j) (hgs j)).1.aestronglyMeasurable) (hb g hg).1.aestronglyMeasurable
      (fun j => (hb (gs j) (hgs j)).2) (hb g hg).2 ?_ φ hφ
    intro ψ hψ hψs
    -- Step 3: integrate by parts in the first row
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hIBPj := fun j =>
      Submission.dimred_mbl_dt_lp_jc_lipschitz_minor_ibp k r L (gs j) V ψ (hgs j) hψ1 hψs
    have hIBP := Submission.dimred_mbl_dt_lp_jc_lipschitz_minor_ibp k r L g V ψ hg hψ1 hψs
    simp only [hIBPj, hIBP]
    refine Tendsto.neg (tendsto_finsetSum _ fun b _ => Tendsto.const_mul _ ?_)
    -- the minors `Mʲ_b`, `M_b` and their bound
    set Mj : ℕ → Euclid k → ℝ := fun j x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
      fderiv ℝ (gs j c.succ) x (V (b.succAbove b'))) with hMj
    set M : Euclid k → ℝ := fun x => Matrix.det (Matrix.of fun (c b' : Fin r) =>
      fderiv ℝ (g c.succ) x (V (b.succAbove b'))) with hM
    set Br : ℝ := (r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r with hBr
    have hbr := fun j => Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L
      (fun c => gs j c.succ) (fun b' => V (b.succAbove b')) (fun c => hgs j c.succ)
    -- Step 4: the weight `θ_b = ∂_{V_b}ψ · g₀` is continuous with compact support
    have hdψc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) :=
      (hψs.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Euclid k →L[ℝ] ℝ => T (V b)) (by simp)
    have hdψi : Integrable (fun x => fderiv ℝ ψ x (V b)) :=
      hdψc.integrable_of_hasCompactSupport hdψs
    have hθi : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x) :=
      (hdψc.mul (hg 0).continuous).integrable_of_hasCompactSupport hdψs.mul_right
    -- Step 6: the induction hypothesis with the weight `θ_b`
    have hih := ih L (fun j c => gs j c.succ) (fun c => g c.succ) (fun b' => V (b.succAbove b'))
      (fun x => fderiv ℝ ψ x (V b) * g 0 x) hθi (fun j c => hgs j c.succ) (fun c => hg c.succ)
      (fun c => hU c.succ)
    -- Step 5: `|∫ ∂_{V_b}ψ (gʲ₀ − g₀) Mʲ_b| ≤ Br sup |gʲ₀ − g₀| ∫ |∂_{V_b}ψ| → 0`
    have herr : Tendsto (fun j => ∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x) atTop
        (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set K : ℝ := Br * (∫ x, ‖fderiv ℝ ψ x (V b)‖) + 1 with hK
      have hBr0 : 0 ≤ Br := by positivity
      have hK0 : 0 < K := by
        have : 0 ≤ ∫ x, ‖fderiv ℝ ψ x (V b)‖ := integral_nonneg fun _ => norm_nonneg _
        positivity
      have hδ : 0 < ε / (2 * K) := by positivity
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 (hU 0) (ε / (2 * K)) hδ).exists_forall_of_atTop
      refine ⟨N, fun j hj => ?_⟩
      rw [Real.dist_eq, sub_zero]
      have hbd : ∀ x, ‖fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x‖ ≤
          (ε / (2 * K) * Br) * ‖fderiv ℝ ψ x (V b)‖ := by
        intro x
        have h1 : |gs j 0 x - g 0 x| ≤ ε / (2 * K) := by
          have := hN j hj x
          rw [dist_comm, Real.dist_eq] at this
          exact this.le
        have h2 : |Mj j x| ≤ Br := (hbr j).2 x
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        calc |fderiv ℝ ψ x (V b)| * |gs j 0 x - g 0 x| * |Mj j x|
            ≤ |fderiv ℝ ψ x (V b)| * (ε / (2 * K)) * Br := by gcongr
          _ = (ε / (2 * K) * Br) * |fderiv ℝ ψ x (V b)| := by ring
      calc |∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x|
          = ‖∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ x, (ε / (2 * K) * Br) * ‖fderiv ℝ ψ x (V b)‖ :=
            norm_integral_le_of_norm_le (hdψi.norm.const_mul _) (Eventually.of_forall hbd)
        _ = (ε / (2 * K)) * (Br * ∫ x, ‖fderiv ℝ ψ x (V b)‖) := by
            rw [integral_const_mul]; ring
        _ ≤ (ε / (2 * K)) * K := by gcongr; linarith
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    -- Step 7: `∫ ∂_{V_b}ψ gʲ₀ Mʲ_b = ∫ ∂_{V_b}ψ (gʲ₀ − g₀) Mʲ_b + ∫ θ_b Mʲ_b → 0 + ∫ θ_b M_b`
    have hsum := herr.add hih
    rw [zero_add] at hsum
    refine hsum.congr' (Eventually.of_forall fun j => ?_)
    have i2 : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x * Mj j x) := by
      have h1 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * g 0 x)) :=
        Integrable.bdd_mul (c := Br) hθi (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      exact h1.congr (Eventually.of_forall fun x => by simp only; ring)
    have i1 : Integrable (fun x => fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Mj j x) := by
      have hgj : Integrable (fun x => fderiv ℝ ψ x (V b) * gs j 0 x) :=
        (hdψc.mul (hgs j 0).continuous).integrable_of_hasCompactSupport hdψs.mul_right
      have h1 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * gs j 0 x)) :=
        Integrable.bdd_mul (c := Br) hgj (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      have h2 : Integrable (fun x => Mj j x * (fderiv ℝ ψ x (V b) * g 0 x)) :=
        Integrable.bdd_mul (c := Br) hθi (hbr j).1.aestronglyMeasurable
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hbr j).2 x)
      exact (h1.sub h2).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    simp only
    rw [← integral_add i1 i2]
    congr 1
    funext x
    ring

/-- **Weak continuity of Jacobians** (step (B4) of the Lipschitz push-forward): if
`H_j, H : ℝⁿ → ℝ^{N'}` are `L`-Lipschitz, `H_j → H` uniformly, `w ∈ L¹` and `ω` is a continuous
compactly supported `n`-form, then `∫ w ω(H_j)(DH_j e₁, …, DH_j eₙ) → ∫ w ω(H)(DH e₁, …, DH eₙ)`.
With `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (n-1)})` and the Jacobian minors
`Δ_I(K) = det (D(K^{I c}) e_b)_{c,b}` (`I : Fin n → Fin N'`, `K^i` the coordinates of `K`), the
coordinate expansion of covectors and the chain rule `D(K^i) = (DK)^i` give
`n! ω(K)(DK e) = Σ_I ω_I(K) Δ_I(K)` wherever `K` is differentiable, hence a.e. (Rademacher).
For each `I` write `w ω_I(H_j) Δ_I(H_j) = w (ω_I(H_j) − ω_I(H)) Δ_I(H_j) + w ω_I(H) Δ_I(H_j)`:
the first integral tends to `0` by dominated convergence (`|ω_I| ≤ C`,
`|Δ_I| ≤ n! (L Σ_b ‖e_b‖)ⁿ`, `ω_I` continuous), the second converges by the weak continuity of
Jacobian minors with the `L¹` weight `w ω_I(H)`.  No separate case `n = 0` is needed. -/
theorem Submission.dimred_mbl_dt_lp_jacobian_weak_continuity : ∀ (n N' : ℕ) (L : NNReal) (Hs : ℕ → Euclid n → Euclid N') (H : Euclid n → Euclid N') (w : Euclid n → ℝ) (ω : DifferentialForm (Euclid N') n), (∀ j, LipschitzWith L (Hs j)) → LipschitzWith L H → TendstoUniformly Hs H atTop → Integrable w → Continuous ω → HasCompactSupport ω → Tendsto (fun j => ∫ u, w u * ω (Hs j u) (fun a => fderiv ℝ (Hs j) u (EuclideanSpace.single a 1))) atTop (𝓝 (∫ u, w u * ω (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)))) := by
  intro n N' L Hs H w ω hHs hH hconv hw hωc hωs
  -- `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (n-1)})` and `Δ_I(K)(u) = det (D(K^{I c})(u) e_b)_{c,b}`
  set ωI : (Fin n → Fin N') → Euclid N' → ℝ :=
    fun I y => ω y (fun c => EuclideanSpace.single (I c) (1 : ℝ)) with hωI
  set Δ : (Fin n → Fin N') → (Euclid n → Euclid N') → Euclid n → ℝ := fun I K u =>
    Matrix.det (Matrix.of fun c b => fderiv ℝ (fun y => K y (I c)) u (EuclideanSpace.single b 1))
    with hΔ
  -- the coordinates `K^i` of an `L`-Lipschitz map are `L`-Lipschitz; `H_j^i → H^i` uniformly
  have hcoord : ∀ K : Euclid n → Euclid N', LipschitzWith L K → ∀ i : Fin N',
      LipschitzWith L (fun y => K y i) := by
    intro K hK i
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← Real.norm_eq_abs, ← PiLp.sub_apply]
    exact (PiLp.norm_apply_le _ _).trans ((dist_eq_norm (K x) (K y)).symm.le.trans
      (hK.dist_le_mul x y))
  have hcoordconv : ∀ i : Fin N', TendstoUniformly (fun j y => Hs j y i) (fun y => H y i) atTop :=
    fun i => (EuclideanSpace.proj i : Euclid N' →L[ℝ] ℝ).uniformContinuous.comp_tendstoUniformly
      hconv
  -- Step 1: `ω_I` is continuous with `|ω_I| ≤ C_I`; `Δ_I(K)` is measurable with `|Δ_I(K)| ≤ B`
  obtain ⟨Cω, hCω⟩ := hωc.bounded_above_of_compact_support hωs
  set CI : (Fin n → Fin N') → ℝ :=
    fun I => Cω * ∏ c, ‖(EuclideanSpace.single (I c) (1 : ℝ) : Euclid N')‖ with hCI
  have hωIc : ∀ I, Continuous (ωI I) := fun I => hωc.eval_const _
  have hωIb : ∀ I y, |ωI I y| ≤ CI I := by
    intro I y
    rw [← Real.norm_eq_abs]
    exact ((ω y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hCω y) (Finset.prod_nonneg fun c _ => norm_nonneg _))
  set B : ℝ := (n.factorial : ℝ) *
    ((L : ℝ) * ∑ b : Fin n, ‖(EuclideanSpace.single b (1 : ℝ) : Euclid n)‖) ^ n with hB
  have hΔmb : ∀ I K, LipschitzWith L K → Measurable (Δ I K) ∧ ∀ u, |Δ I K u| ≤ B :=
    fun I K hK => Submission.dor_lmb_fcd_jwc_minor_measurable_bound n n L (fun c y => K y (I c))
      (fun b => EuclideanSpace.single b 1) fun c => hcoord K hK (I c)
  -- Step 4: `n! ω(K u)(DK(u) e) = Σ_I ω_I(K u) Δ_I(K)(u)` wherever `K` is differentiable
  have hexp : ∀ (K : Euclid n → Euclid N') (u : Euclid n), DifferentiableAt ℝ K u →
      (n.factorial : ℝ) * ω (K u) (fun a => fderiv ℝ K u (EuclideanSpace.single a 1)) =
        ∑ I : Fin n → Fin N', ωI I (K u) * Δ I K u := by
    intro K u hK
    have hcd : ∀ (i : Fin N') (v : Euclid n),
        fderiv ℝ (fun y => K y i) u v = fderiv ℝ K u v i := by
      intro i v
      have h := ((EuclideanSpace.proj i : Euclid N' →L[ℝ] ℝ).hasFDerivAt.comp u
        hK.hasFDerivAt).fderiv
      exact congrArg (fun T : Euclid n →L[ℝ] ℝ => T v) h
    rw [Submission.dor_lmb_fcd_jwc_covector_det_expansion N' n (ω (K u))
      (fun a => fderiv ℝ K u (EuclideanSpace.single a 1))]
    simp only [hΔ, hωI, hcd]
  -- Step 4: hence `∫ w ω(K)(DK e) = (n!)⁻¹ Σ_I ∫ w ω_I(K) Δ_I(K)` (Rademacher)
  have hint : ∀ K : Euclid n → Euclid N', LipschitzWith L K →
      ∫ u, w u * ω (K u) (fun a => fderiv ℝ K u (EuclideanSpace.single a 1)) =
        (n.factorial : ℝ)⁻¹ * ∑ I : Fin n → Fin N', ∫ u, w u * (ωI I (K u) * Δ I K u) := by
    intro K hK
    have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hterm : ∀ I, Integrable (fun u => w u * (ωI I (K u) * Δ I K u)) := fun I =>
      hw.mul_bdd (((hωIc I).comp hK.continuous).aestronglyMeasurable.mul
        (hΔmb I K hK).1.aestronglyMeasurable) (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hωIb I (K u)) ((hΔmb I K hK).2 u) (abs_nonneg _)
            ((abs_nonneg _).trans (hωIb I (K u))))
    rw [← integral_finsetSum _ fun I _ => hterm I, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with u hu
    rw [← Finset.mul_sum, ← hexp K u hu, mul_left_comm, inv_mul_cancel_left₀ hfac]
  -- Step 5: convergence for a fixed `I`
  have hI : ∀ I : Fin n → Fin N', Tendsto (fun j => ∫ u, w u * (ωI I (Hs j u) * Δ I (Hs j) u))
      atTop (𝓝 (∫ u, w u * (ωI I (H u) * Δ I H u))) := by
    intro I
    -- the weight `w ω_I(H)` is integrable
    have hφ : Integrable (fun u => w u * ωI I (H u)) :=
      hw.mul_bdd ((hωIc I).comp hH.continuous).aestronglyMeasurable
        (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hωIb I (H u))
    have hφΔ : ∀ j, Integrable (fun u => (w u * ωI I (H u)) * Δ I (Hs j) u) := fun j =>
      hφ.mul_bdd (hΔmb I (Hs j) (hHs j)).1.aestronglyMeasurable (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs]; exact (hΔmb I (Hs j) (hHs j)).2 u)
    -- the error term `w (ω_I(H_j) − ω_I(H)) Δ_I(H_j)` is dominated by `2 C_I B |w|`
    have hdiff : ∀ y y', |ωI I y - ωI I y'| ≤ CI I + CI I := fun y y' =>
      (abs_sub _ _).trans (add_le_add (hωIb I y) (hωIb I y'))
    have hG : ∀ j u, ‖(ωI I (Hs j u) - ωI I (H u)) * Δ I (Hs j) u‖ ≤ (CI I + CI I) * B := by
      intro j u
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hdiff _ _) ((hΔmb I (Hs j) (hHs j)).2 u) (abs_nonneg _)
        ((abs_nonneg _).trans (hdiff (H u) (H u)))
    have hGm : ∀ j, AEStronglyMeasurable (fun u => (ωI I (Hs j u) - ωI I (H u)) * Δ I (Hs j) u)
        volume := fun j =>
      ((((hωIc I).comp (hHs j).continuous).sub
        ((hωIc I).comp hH.continuous)).aestronglyMeasurable).mul
          (hΔmb I (Hs j) (hHs j)).1.aestronglyMeasurable
    have hF : ∀ j, Integrable (fun u => w u * ((ωI I (Hs j u) - ωI I (H u)) * Δ I (Hs j) u)) :=
      fun j => hw.mul_bdd (hGm j) (Eventually.of_forall (hG j))
    -- first term `→ 0` by dominated convergence
    have h1 : Tendsto (fun j => ∫ u, w u * ((ωI I (Hs j u) - ωI I (H u)) * Δ I (Hs j) u)) atTop
        (𝓝 0) := by
      have h := tendsto_integral_of_dominated_convergence (μ := volume)
        (F := fun j u => w u * ((ωI I (Hs j u) - ωI I (H u)) * Δ I (Hs j) u))
        (f := fun _ => (0 : ℝ)) (fun u => ‖w u‖ * ((CI I + CI I) * B))
        (fun j => (hF j).aestronglyMeasurable) (hw.norm.mul_const _)
        (fun j => Eventually.of_forall fun u => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hG j u) (norm_nonneg _))
        (Eventually.of_forall fun u => by
          refine squeeze_zero_norm' (Eventually.of_forall fun j => ?_) (a := fun j =>
            ‖w u‖ * (|ωI I (Hs j u) - ωI I (H u)| * B)) ?_
          · rw [norm_mul, Real.norm_eq_abs (_ * _), abs_mul]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              ((hΔmb I (Hs j) (hHs j)).2 u) (abs_nonneg _)) (norm_nonneg _)
          · have h := (((((hωIc I).tendsto (H u)).comp (hconv.tendsto_at u)).sub_const
              (ωI I (H u))).abs.mul_const B).const_mul ‖w u‖
            simpa using h)
      simpa using h
    -- second term by the weak continuity of Jacobian minors, with the `L¹` weight `w ω_I(H)`
    have h2 : Tendsto (fun j => ∫ u, (w u * ωI I (H u)) * Δ I (Hs j) u) atTop
        (𝓝 (∫ u, (w u * ωI I (H u)) * Δ I H u)) :=
      Submission.dimred_mbl_dt_lp_jc_minor_weak_continuity n n L (fun j c y => Hs j y (I c))
        (fun c y => H y (I c)) (fun b => EuclideanSpace.single b 1)
        (fun u => w u * ωI I (H u)) hφ (fun j c => hcoord (Hs j) (hHs j) (I c))
        (fun c => hcoord H hH (I c)) (fun c => hcoordconv (I c))
    have h3 := h1.add h2
    rw [zero_add] at h3
    have hlim : ∫ u, w u * (ωI I (H u) * Δ I H u) = ∫ u, (w u * ωI I (H u)) * Δ I H u := by
      congr 1; funext u; ring
    rw [hlim]
    refine h3.congr' (Eventually.of_forall fun j => ?_)
    rw [← integral_add (hF j) (hφΔ j)]
    congr 1; funext u; ring
  -- Step 7: sum over `I` and multiply by `(n!)⁻¹`
  have hj : (fun j => ∫ u, w u * ω (Hs j u) (fun a => fderiv ℝ (Hs j) u
      (EuclideanSpace.single a 1))) = fun j => (n.factorial : ℝ)⁻¹ *
        ∑ I : Fin n → Fin N', ∫ u, w u * (ωI I (Hs j u) * Δ I (Hs j) u) :=
    funext fun j => hint (Hs j) (hHs j)
  rw [hj, hint H hH]
  exact (tendsto_finsetSum _ fun I _ => hI I).const_mul _

/-- **Integrality of the Lipschitz push-forward** (Simon Ch. 6, 3.3–3.9, with the push-forward of
the deformation theorem).  Assume (VO), (MR), (IMC) and (IMS).  Let `F : ℝᴺ → ℝᴺ'` be
`Λ`-Lipschitz, `X ∈ 𝒟ₙ(ℝᴺ)` (`n = k + 1`) integer multiplicity with compact support and
`M(X) < ∞`, and let `S(ω) = lim_j X(ηⱼ)` with `ηⱼ = Fⱼ^#ω` near `spt X` for smooth `Λ`-Lipschitz
`Fⱼ → F` uniformly.  Then `S` is integer multiplicity.

Normalize `X = τ(M, θ, ξ)` with `M ⊆ spt X` and cut it into integer-weighted bi-Lipschitz pieces
`(G i, A i, w i)`: `X(η) = ∑ᵢ ∫_{A i} w i · η(G i)(DG_i e)`, `|α(DG_i e)| ≤ c i |α|` and
`∑ᵢ ∫_{A i} |w i| c i ≤ M(X)`.  The pieces of the Lipschitz maps `F ∘ G i` give integer multiplicity
`Sᵢ(ω) = ∫_{A i} w i · ω(F ∘ G i)(D(F ∘ G i) e)`.  As `G i '' A i ⊆ spt X`, the chain rule gives
`X(ηⱼ) = ∑ᵢ ∫_{A i} w i · ω(Fⱼ ∘ G i)(D(Fⱼ ∘ G i) e)`; the `i`-th term tends to `Sᵢ(ω)` by the weak
continuity of Jacobians and is bounded by `Λⁿ sup|ω| ∫_{A i} |w i| c i` by (L1) and `‖DFⱼ‖ ≤ Λ`.
Tannery's theorem gives `S(ω) = ∑ᵢ Sᵢ(ω)`, and testing with `|ω| ≤ 1` gives
`M(Sᵢ) ≤ Λⁿ ∫_{A i} |w i| c i`, so `∑ᵢ M(Sᵢ) ≤ Λⁿ M(X) < ∞`; (IMS) sums the `Sᵢ` to an integer
multiplicity current, which is `S`. -/
theorem Submission.dimred_mbl_dt_lp_im_pushforward : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ((∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (S : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1)), LipschitzWith Λ F → IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (S ω))) → IsIntegerMultiplicity S := by
  have hCB := Submission.dimred_mbl_dt_lp_covector_bounds
  have hJC := Submission.dimred_mbl_dt_lp_jacobian_weak_continuity
  intro hVO hMR hIMC hIMS N N' k Λ F X S hF hX _hXcpt hXmass hFs
  obtain ⟨Fs, hFs_smooth, hFs_lip, hFs_unif, hηex⟩ := hFs
  have hIMSc := hIMS hVO hMR hIMC
  -- step 1: `X = τ(M, θ, ξ)` with `M ⊆ spt X` and `∫_M θ dHⁿ = M(X) < ∞`
  obtain ⟨R, hRX, hRsub, hRmass⟩ :=
    Submission.dimred_mbl_dt_lpip_normalized_rep hVO hMR hIMC N (k + 1) univ X isOpen_univ hX
  have hRfin : R.measure univ ≠ ∞ := by
    rw [hRmass]
    exact hXmass.ne
  -- steps 2–3: integer-weighted bi-Lipschitz pieces `(G i, A i, w i)` of `(M, θ, ξ)`, with
  -- `|α(DG_i e)| ≤ c i |α|` on `A i` and `∑ᵢ ∫_{A i} |w i| c i ≤ M(X)`
  obtain ⟨G, A, w, c, hGlip, hAmeas, hwmeas, hcmeas, hGdiff, hGsub, hwint, hc, hBsum, hrep⟩ :=
    Submission.dimred_mbl_dt_lpip_piece_representation Submission.dpf_rectifiable_bilipschitz_pieces
      Submission.covectorEuclideanNorm_gram_bounds hIMC N (k + 1) R hRfin
  choose L hL using hGlip
  -- step 5: `Sᵢ(ω) = ∫_{A i} w i · ω(F ∘ G i)(D(F ∘ G i) e)` is integer multiplicity
  obtain ⟨Si, hSiIM, hSiω⟩ : ∃ Si : ℕ → GeometricCurrentOn (univ : Set (Euclid N')) (k + 1),
      (∀ i, IsIntegerMultiplicity (Si i)) ∧
        ∀ i (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)),
          Si i ω = ∫ u in A i, (w i u : ℝ) * (ω : DifferentialForm (Euclid N') (k + 1))
            ((F ∘ G i) u) (fun a => fderiv ℝ (F ∘ G i) u (EuclideanSpace.single a 1)) := by
    choose Si hSiIM hSiω using fun i =>
      Submission.dimred_mbl_dt_lpip_lipschitz_piece_current hMR hIMC hIMSc N' k (Λ * L i)
        (F ∘ G i) (A i) (w i) (hF.comp (hL i)) (hAmeas i) (hwmeas i) (hwint i)
    exact ⟨Si, hSiIM, hSiω⟩
  -- the piece weights `B i = ∫_{A i} |w i| c i` are finite and summable
  obtain ⟨B, hB⟩ : ∃ B : ℕ → ℝ≥0∞,
      ∀ i, B i = ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) := ⟨_, fun _ => rfl⟩
  have hBtsum : ∑' i, B i ≠ ∞ := by
    simp only [hB]
    exact ne_top_of_le_ne_top hRfin hBsum
  have hBne : ∀ i, B i ≠ ∞ := fun i => ne_top_of_le_ne_top hBtsum (ENNReal.le_tsum i)
  have hBsummable : Summable fun i => (B i).toReal := ENNReal.summable_toReal hBtsum
  -- Tannery's theorem: dominated convergence for series
  have tannery : ∀ (f : ℕ → ℕ → ℝ) (g bound : ℕ → ℝ), Summable bound →
      (∀ i, Tendsto (fun j => f j i) atTop (𝓝 (g i))) → (∀ j i, ‖f j i‖ ≤ bound i) →
      Tendsto (fun j => ∑' i, f j i) atTop (𝓝 (∑' i, g i)) := by
    intro f g bound h_sum hab h_bound
    have h_g_le : ∀ i, ‖g i‖ ≤ bound i := fun i =>
      le_of_tendsto' (tendsto_norm.comp (hab i)) fun j => h_bound j i
    have h_sumg : Summable fun i => ‖g i‖ :=
      h_sum.of_norm_bounded fun i => (norm_norm (g i)).symm ▸ h_g_le i
    have h_suma : ∀ j, Summable fun i => ‖f j i‖ := fun j =>
      h_sum.of_norm_bounded <| by simpa only [norm_norm] using h_bound j
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨s₀, hs₀⟩ := h_sum
    obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset ℕ, dist (∑ b ∈ T₀, bound b) s₀ < ε / 3 := by
      rw [HasSum, Metric.tendsto_nhds] at hs₀
      exact Eventually.exists <| hs₀ _ (by positivity)
    have h1 : ∑' (i : (T₀ᶜ : Set ℕ)), bound i < ε / 3 := by
      calc _ ≤ ‖∑' (i : (T₀ᶜ : Set ℕ)), bound i‖ := Real.le_norm_self _
        _ = ‖s₀ - ∑ b ∈ T₀, bound b‖ := congrArg _ ?_
        _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT₀
      simpa only [hs₀.summable.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hs₀.tsum_eq
    have h2 : Tendsto (fun j => ∑ i ∈ T₀, f j i) atTop (𝓝 (T₀.sum g)) :=
      tendsto_finsetSum _ fun i _ => hab i
    rw [Metric.tendsto_nhds] at h2
    filter_upwards [h2 (ε / 3) (by positivity)] with j hj
    rw [dist_eq_norm, ← (h_suma j).of_norm.tsum_sub h_sumg.of_norm,
      ← ((h_suma j).of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T₀),
      (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
    refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
    · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hj
    · rw [((h_suma j).subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
      refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
      · refine ((norm_tsum_le_tsum_norm ((h_suma j).subtype _)).trans ?_).trans_lt h1
        exact ((h_suma j).subtype _).tsum_le_tsum (fun i => h_bound j i)
          (hs₀.summable.subtype _)
      · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
        exact (h_sumg.subtype _).tsum_le_tsum (fun i => h_g_le i) (hs₀.summable.subtype _)
  -- step 6: for `ω` with `|ω| ≤ C`, `|Sᵢ(ω)| ≤ Λⁿ C B i` and `S(ω) = ∑ᵢ Sᵢ(ω)`
  have key : ∀ (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)) (C : ℝ),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) ≤ C) →
      (∀ i, ‖Si i ω‖ ≤ (Λ : ℝ) ^ (k + 1) * C * (B i).toReal) ∧
        HasSum (fun i => Si i ω) (S ω) := by
    intro ω C hC
    have hC0 : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hC 0)
    have hK0 : 0 ≤ (Λ : ℝ) ^ (k + 1) * C := mul_nonneg (pow_nonneg Λ.coe_nonneg _) hC0
    have hωc : Continuous (ω : DifferentialForm (Euclid N') (k + 1)) :=
      ContDiff.continuous ω.property.1.1
    obtain ⟨ηs, hηW, hηlim⟩ := hηex ω
    -- `X(ηⱼ) = ∑ᵢ ∫_{A i} w i · ηⱼ(G i)(DG_i e)`
    have hTsum : ∀ j, HasSum (fun i => ∫ u in A i, (w i u : ℝ) *
        (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
          (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (X (ηs j)) := by
      intro j
      rw [hRX (ηs j)]
      exact hrep _ (ContDiff.continuous (ηs j).property.1.1) (ηs j).property.1.2
    -- on `A i` (so `G i u ∈ spt X ⊆ Wⱼ`), `ηⱼ(G i)(DG_i e) = ω(Fⱼ ∘ G i)(D(Fⱼ ∘ G i) e)` by the
    -- chain rule, and `|ηⱼ(G i u)| ≤ ‖DFⱼ‖ⁿ |ω(Fⱼ(G i u))| ≤ Λⁿ C` by (L1)
    have hpt : ∀ j i, ∀ u ∈ A i, (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
        (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1)) =
          (ω : DifferentialForm (Euclid N') (k + 1)) ((Fs j ∘ G i) u)
            (fun a => fderiv ℝ (Fs j ∘ G i) u (EuclideanSpace.single a 1)) ∧
        covectorEuclideanNorm ((ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)) ≤
          (Λ : ℝ) ^ (k + 1) * C := by
      intro j i u hu
      obtain ⟨W, -, hXW, hW⟩ := hηW j
      rw [hW _ (hXW (hRsub (hGsub i ⟨u, hu, rfl⟩)))]
      refine ⟨?_, ?_⟩
      · rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
          fderiv_comp u (((hFs_smooth j).differentiable (by simp)) _) (hGdiff i u hu)]
        rfl
      · calc _ ≤ ‖fderiv ℝ (Fs j) (G i u)‖ ^ (k + 1) *
              covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j (G i u))) :=
            hCB.1 N N' (k + 1) _ _
          _ ≤ (Λ : ℝ) ^ (k + 1) * C :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
              (norm_fderiv_le_of_lipschitz ℝ (hFs_lip j)) _) (hC _)
              (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.coe_nonneg _)
    -- termwise limits: weak continuity of Jacobians with the weight `1_{A i} w i`
    have hTlim : ∀ i, Tendsto (fun j => ∫ u in A i, (w i u : ℝ) *
        (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
          (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) atTop (𝓝 (Si i ω)) := by
      intro i
      have hind : ∀ H : Euclid (k + 1) → Euclid N',
          ∫ u, (A i).indicator (fun u => (w i u : ℝ)) u *
            (ω : DifferentialForm (Euclid N') (k + 1)) (H u)
              (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) =
          ∫ u in A i, (w i u : ℝ) * (ω : DifferentialForm (Euclid N') (k + 1)) (H u)
            (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
        intro H
        rw [← integral_indicator (hAmeas i)]
        congr 1
        funext u
        by_cases hu : u ∈ A i <;> simp [hu]
      have hJC := hJC (k + 1) N' (Λ * L i)
        (fun j => Fs j ∘ G i) (F ∘ G i) ((A i).indicator fun u => (w i u : ℝ))
        (ω : DifferentialForm (Euclid N') (k + 1)) (fun j => (hFs_lip j).comp (hL i))
        (hF.comp (hL i)) (hFs_unif.comp (G i)) ((hwint i).integrable_indicator (hAmeas i))
        hωc ω.property.1.2
      simp only [hind] at hJC
      rw [hSiω i ω]
      refine hJC.congr fun j => ?_
      exact setIntegral_congr_fun (hAmeas i) fun u hu => by rw [(hpt j i u hu).1]
    -- the uniform bound `|Tᵢⱼ| ≤ Λⁿ C B i`
    have hTbd : ∀ j i, ‖∫ u in A i, (w i u : ℝ) *
        (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
          (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))‖ ≤
          (Λ : ℝ) ^ (k + 1) * C * (B i).toReal := by
      intro j i
      have hle : ∀ u ∈ A i, ENNReal.ofReal ‖(w i u : ℝ) *
          (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
            (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))‖ ≤
          ENNReal.ofReal ((Λ : ℝ) ^ (k + 1) * C) * ENNReal.ofReal (|(w i u : ℝ)| * c i u) := by
        intro u hu
        rw [← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |(w i u : ℝ)| * |(ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
              (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))|
            ≤ |(w i u : ℝ)| * (c i u * ((Λ : ℝ) ^ (k + 1) * C)) :=
              mul_le_mul_of_nonneg_left (((hc i u hu).2 _).trans
                (mul_le_mul_of_nonneg_left (hpt j i u hu).2 (hc i u hu).1)) (abs_nonneg _)
          _ = (Λ : ℝ) ^ (k + 1) * C * (|(w i u : ℝ)| * c i u) := by ring
      have hmeas : Measurable fun u => ENNReal.ofReal (|(w i u : ℝ)| * c i u) :=
        (((Measurable.of_discrete (f := fun z : ℤ => |(z : ℝ)|)).comp (hwmeas i)).mul
          (hcmeas i)).ennreal_ofReal
      calc _ ≤ (∫⁻ u in A i, ENNReal.ofReal ‖(w i u : ℝ) *
              (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
                (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))‖).toReal :=
            norm_integral_le_lintegral_norm _
        _ ≤ (ENNReal.ofReal ((Λ : ℝ) ^ (k + 1) * C) * B i).toReal := by
            refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hBne i)) ?_
            rw [hB i, ← lintegral_const_mul _ hmeas]
            exact setLIntegral_mono' (hAmeas i) hle
        _ = (Λ : ℝ) ^ (k + 1) * C * (B i).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0]
    have hSibd : ∀ i, ‖Si i ω‖ ≤ (Λ : ℝ) ^ (k + 1) * C * (B i).toReal := fun i =>
      le_of_tendsto' (tendsto_norm.comp (hTlim i)) fun j => hTbd j i
    refine ⟨hSibd, ?_⟩
    -- dominated convergence for the series: `X(ηⱼ) = ∑ᵢ Tᵢⱼ → ∑ᵢ Sᵢ(ω)`, and `X(ηⱼ) → S(ω)`
    have hsumm : Summable fun i => (Λ : ℝ) ^ (k + 1) * C * (B i).toReal :=
      hBsummable.mul_left _
    have hlim := tannery (fun j i => ∫ u in A i, (w i u : ℝ) *
        (ηs j : DifferentialForm (Euclid N) (k + 1)) (G i u)
          (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (fun i => Si i ω) _ hsumm
      hTlim hTbd
    have hXlim : Tendsto (fun j => X (ηs j)) atTop (𝓝 (∑' i, Si i ω)) :=
      hlim.congr fun j => (hTsum j).tsum_eq
    rw [tendsto_nhds_unique hηlim hXlim]
    exact (hsumm.of_norm_bounded hSibd).hasSum
  -- masses: `M(Sᵢ) ≤ Λⁿ B i` (test with admissible `|ω| ≤ 1`), so `∑ᵢ M(Sᵢ) ≤ Λⁿ M(X) < ∞`
  have hmass : ∀ i, (Si i).mass ≤ (Λ : ℝ≥0∞) ^ (k + 1) * B i := by
    intro i
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have h := (key ω 1 hω.2).1 i
    rw [mul_one] at h
    calc ENNReal.ofReal (Si i ω) ≤ ENNReal.ofReal ((Λ : ℝ) ^ (k + 1) * (B i).toReal) :=
          ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans h)
      _ = (Λ : ℝ≥0∞) ^ (k + 1) * B i := by
          rw [ENNReal.ofReal_mul (pow_nonneg Λ.coe_nonneg _), ENNReal.ofReal_toReal (hBne i),
            ENNReal.ofReal_pow Λ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hmass_sum : ∑' i, (Si i).mass < ∞ :=
    calc ∑' i, (Si i).mass ≤ ∑' i, (Λ : ℝ≥0∞) ^ (k + 1) * B i := ENNReal.tsum_le_tsum hmass
      _ = (Λ : ℝ≥0∞) ^ (k + 1) * ∑' i, B i := ENNReal.tsum_mul_left
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hBtsum.lt_top
  -- step 7: (IMS) sums the `Sᵢ` to an integer multiplicity current, which is `S`
  obtain ⟨Ŝ, hŜsum, -, -, hŜIM⟩ := hIMSc N' k Si hmass_sum
  have hŜS : Ŝ = S := by
    ext ω
    have hωc : Continuous (ω : DifferentialForm (Euclid N') (k + 1)) :=
      ContDiff.continuous ω.property.1.1
    have hcont : Continuous fun y =>
        covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) := by
      unfold covectorEuclideanNorm
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => ((continuous_eval_const _).comp hωc).pow 2)
        (fun _ => continuous_const)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support
      (ω.property.1.2.comp_left (g := covectorEuclideanNorm) (covectorEuclideanNorm_zero N' (k + 1)))
    exact (hŜsum ω).unique (key ω C fun y => (Real.le_norm_self _).trans (hC y)).2
  rw [← hŜS]
  exact hŜIM hSiIM
/-- **Covector bounds for the Lipschitz push-forward** (Simon 6.1, (L1)–(L2)): the pull-back
estimate `|A^#β|_E ≤ ‖A‖ᵏ |β|_E` for a linear map `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β` on `ℝᴺ'`
(Simon 6.1.8, `dimred_mbl_dt_lp_cb_pullback_le`), and the interior product estimate
`|ι_v β|_E ≤ ‖v‖ |β|_E` for `v ∈ ℝᴺ` and a `(k+1)`-covector `β` on `ℝᴺ`
(`dimred_mbl_dt_lp_cb_curryLeft_le`). -/
theorem Submission.dimred_mbl_dt_lp_covector_bounds : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
  exact ⟨Submission.dimred_mbl_dt_lp_cb_pullback_le, Submission.dimred_mbl_dt_lp_cb_curryLeft_le⟩

/-- **Simon 6.3.2(2)** with `T₁ = [[(0,1)]]`: the product `C = [[(0,1)]] × X` of 6.2.17, written
as `C(ω) = ∫₀¹ X(ηₜ) dt` with `ηₜ(x)(v) = ω(ι(t, x))(e₀, Jv)`, `ι(t, x) = (t, x)`,
`e₀ = (1, 0, …, 0)` and `Jv = ι(0, v)`, is integer multiplicity whenever `X ∈ 𝒟_{k+1}(ℝᴺ)` is
integer multiplicity with `M(X) < ∞`.  If `X = τ(M, θ, ξ)`, then
`C = τ((0,1) × M, θ ∘ tail, e₀ ∧ ξ)`.  By 6.3.2(3), `∫_M θ dHᵏ⁺¹ = M(X) < ∞`; the cylinder
triple is an integer multiplicity representation, and `H^{k+2}⌞((0,1) × M) = ι_#(L¹⌞(0,1) ⊗
Hᵏ⁺¹⌞M)` together with Fubini identifies its action with `∫₀¹ X(ηₜ) dt`.  The integrand is
bounded by `θ ∘ tail · sup |ω|` on `spt ω`, since `|ξ'(y)(α)| ≤ |α|` for a.e. `y`. -/
theorem Submission.dimred_mbl_dt_lp_im_cylinder : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)), IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η t : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = ∫ t in (0 : ℝ)..1, X (η t)) → IsIntegerMultiplicity C := by
  intro _hVO hMR hIMC N k X C hX _hXspt hXmass hC
  obtain ⟨R, hR⟩ := hX
  -- Step 1: `∫_M θ dHᵏ⁺¹ = R.measure(ℝᴺ) = M(X) < ∞` by (MR), so `Hᵏ⁺¹(M) < ∞` (`θ ≥ 1` on `M`)
  have hθ : ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] ≠ ∞ := by
    have h := hMR N (k + 1) univ X R isOpen_univ hR univ isOpen_univ
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    rw [← h]
    exact hXmass.ne
  have hM : μHE[k + 1] R.carrier ≠ ∞ := by
    refine ne_top_of_le_ne_top hθ ?_
    calc μHE[k + 1] R.carrier = ∫⁻ _ in R.carrier, (1 : ℝ≥0∞) ∂μHE[k + 1] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] :=
          setLIntegral_mono' R.measurableSet_carrier fun x hx =>
            Nat.one_le_cast.mpr (R.mult_pos x hx)
  have : IsFiniteMeasure (μHE[k + 1].restrict R.carrier) := isFiniteMeasure_restrict.2 hM
  -- Step 2: the cylinder triple `R' = ((0,1) × M, θ ∘ tail, e₀ ∧ ξ)`, and
  -- `H^{k+2}⌞R'.carrier = ι_#(L¹⌞(0,1) ⊗ Hᵏ⁺¹⌞M)`
  obtain ⟨R', hcarrier, hmult, horient⟩ :=
    Submission.dimred_mbl_dt_lp_imc_cylinder_imrep N (k + 1) R hθ
  have hmeas := Submission.dimred_mbl_dt_lp_imc_cylinder_measure N (k + 1) R.carrier
    R.measurableSet_carrier R.rectifiable hM
  rw [← hcarrier] at hmeas
  have hι : Measurable fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1)) := by
    fun_prop
  refine ⟨R', fun ω => ?_⟩
  obtain ⟨η, hη, hCω⟩ := hC ω
  have hωc : Continuous (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) :=
    ContDiff.continuous ω.property.1.1
  have hωK : IsCompact (tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1))) :=
    ω.property.1.2
  -- Step 3: `|ω(y)| ≤ c` for every `y`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ y,
      ‖covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) y)‖ ≤ c := by
    have hnorm : Continuous fun α : Covector (Euclid (N + 1)) (k + 1 + 1) =>
        covectorEuclideanNorm α := by
      unfold covectorEuclideanNorm
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      by_cases hI : StrictMono I
      · simp only [hI, ↓reduceIte]
        exact (continuous_eval_const _).pow 2
      · simp only [hI, ↓reduceIte]
        exact continuous_const
    have hcs : HasCompactSupport fun y =>
        covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) y) :=
      HasCompactSupport.comp_left (g := covectorEuclideanNorm) hωK
        (covectorEuclideanNorm_zero _ _)
    exact Continuous.bounded_above_of_compact_support (hnorm.comp hωc) hcs
  -- Step 4: the integrand `θ'·ξ'(ω)` of `R'.action ω` is integrable: by (IMC)(d) it is bounded by
  -- `θ'·c` on the compact set `spt ω`, where `θ'` is integrable, and it vanishes off `spt ω`
  have hfm : AEStronglyMeasurable (fun y => (R'.mult y : ℝ) *
      R'.orient y ((ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) y))
      (μHE[k + 1 + 1].restrict R'.carrier) :=
    ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp
      R'.measurable_mult).aestronglyMeasurable.mul
      (Continuous.comp_aestronglyMeasurable₂ (g := fun (L : MultiVector (N + 1) (k + 1 + 1))
          (α : Covector (Euclid (N + 1)) (k + 1 + 1)) => L α)
        (continuous_fst.clm_apply continuous_snd) R'.aestronglyMeasurable_orient
        hωc.aestronglyMeasurable)
  have hfi : Integrable (fun y => (R'.mult y : ℝ) *
      R'.orient y ((ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) y))
      (μHE[k + 1 + 1].restrict R'.carrier) := by
    refine Integrable.mono'
      (g := (tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1))).indicator
        fun y => (R'.mult y : ℝ) * c) ?_ hfm ?_
    · rw [integrable_indicator_iff hωK.measurableSet, IntegrableOn,
        Measure.restrict_restrict hωK.measurableSet, inter_comm]
      refine Integrable.mul_const ?_ c
      simpa using integrable_toReal_of_lintegral_ne_top
        ((measurable_from_nat (f := fun m : ℕ => (m : ℝ≥0∞))).comp
          R'.measurable_mult).aemeasurable
        (R'.locallyIntegrable_mult _ hωK (subset_univ _))
    · filter_upwards [hIMC.2.2.2 (N + 1) (k + 1 + 1) univ R'] with y hy
      by_cases hyK : y ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1))
      · rw [indicator_of_mem hyK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((hy _).trans ((Real.le_norm_self _).trans (hc y)))
          (Nat.cast_nonneg _)
      · simp [indicator_of_notMem hyK, image_eq_zero_of_notMem_tsupport hyK]
  rw [← hmeas] at hfm hfi
  -- Step 5: `C(ω) = ∫₀¹ X(ηₜ) dt = ∫₀¹ ∫_M θ(x) ξ(x)(ηₜ(x)) dHᵏ⁺¹ dt`, where
  -- `ξ(x)(ηₜ(x)) = ξ'(ι(t, x))(ω(ι(t, x)))` for a.e. `x ∈ M`; Fubini and Step 2 give `R'.action ω`
  calc C ω = ∫ t in (0 : ℝ)..1, X (η t) := hCω
    _ = ∫ t in Ioo (0 : ℝ) 1, X (η t) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    _ = ∫ t in Ioo (0 : ℝ) 1, ∫ x in R.carrier,
          (R'.mult (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) : ℝ) *
            R'.orient (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
              ((ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1))
                (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) ∂μHE[k + 1] := by
      refine integral_congr_ae ?_
      filter_upwards with t
      rw [hR (η t), IMRep.action]
      refine integral_congr_ae ?_
      filter_upwards [horient] with x hx
      rw [hmult, hx t _ _ (hη t x)]
    _ = R'.action ω := by
      rw [IMRep.action, ← hmeas, integral_map hι.aemeasurable hfm]
      exact (integral_prod _ ((integrable_map_measure hfm hι.aemeasurable).1 hfi)).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
