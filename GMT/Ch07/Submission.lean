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

/-- **Orthogonal frame adapted to an `n`-plane** (Step 0 of the graph first-variation estimate in
the tilt-excess step of Allard's theorem, used for Simon 7.4.3).  Let `T ⊆ ℝⁿ⁺ᵏ` have dimension
`n`, let `ι : ℝⁿ → ℝⁿ⁺ᵏ`, `ι' : ℝᵏ → ℝⁿ⁺ᵏ` be linear isometries with orthogonal ranges and
`ι(ℝⁿ) ⊆ T`, and let `P : ℝⁿ⁺ᵏ → ℝⁿ` satisfy `P ∘ ι = id` and `P ∘ ι' = 0`.  Then `range ι = T`
(both have dimension `n`), so `ι'w ∈ Tᗮ`, and `range ι' = Tᗮ` (both have dimension `k`).  Every
`y` splits as `y = p_T y + (y − p_T y) = ιu + ι'w` with `Py = u`.  This gives `⟪ιu', y⟫ = ⟪u', Py⟫`,
`p_T y = ι(Py)`, Pythagoras `|y|² = |Py|² + |y − p_T y|²`, and `|Py| ≤ |y|`. -/
theorem Submission.dorag_tes_gv_adapted_frame : ∀ (n k : ℕ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ (u : Euclid n) (y : Euclid (n + k)), inner ℝ (ι u) y = inner ℝ u (P y)) ∧ (∀ y, T.starProjection y = ι (P y)) ∧ (∀ w, ι' w ∈ Tᗮ) ∧ (∀ y, ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - T.starProjection y‖ ^ 2) ∧ (∀ y, ‖P y‖ ≤ ‖y‖) := by
  intro n k T ι ι' P hT hιι' hιT hPι hPι'
  -- `range ι ⊆ T`, and both have dimension `n`, so `range ι = T`
  have hrange : LinearMap.range ι.toLinearMap = T := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact hιT v
    · rw [LinearMap.finrank_range_of_inj ι.injective, finrank_euclideanSpace_fin, hT]
  -- (c): `ι'w` is orthogonal to every `ιv`, hence to `T`
  have hι'T : ∀ w, ι' w ∈ Tᗮ := by
    intro w
    rw [← hrange, Submodule.mem_orthogonal]
    rintro _ ⟨v, rfl⟩
    exact hιι' v w
  -- `range ι' ⊆ Tᗮ`, and both have dimension `(n + k) − n = k`, so `range ι' = Tᗮ`
  have hrange' : LinearMap.range ι'.toLinearMap = Tᗮ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨w, rfl⟩
      exact hι'T w
    · have h := Submodule.finrank_add_finrank_orthogonal T
      rw [finrank_euclideanSpace_fin, hT] at h
      rw [LinearMap.finrank_range_of_inj ι'.injective, finrank_euclideanSpace_fin]
      omega
  -- `y = p_T y + (y − p_T y) = ιu + ι'w`
  have hdecomp : ∀ y, ∃ u w, y = ι u + ι' w := by
    intro y
    obtain ⟨u, hu⟩ : T.starProjection y ∈ LinearMap.range ι.toLinearMap :=
      hrange ▸ T.starProjection_apply_mem y
    obtain ⟨w, hw⟩ : y - T.starProjection y ∈ LinearMap.range ι'.toLinearMap :=
      hrange' ▸ T.sub_starProjection_mem_orthogonal y
    rw [LinearIsometry.coe_toLinearMap] at hu hw
    exact ⟨u, w, by rw [hu, hw, add_sub_cancel]⟩
  -- `P(ιu + ι'w) = u`
  have hP : ∀ u w, P (ι u + ι' w) = u := fun u w => by rw [map_add, hPι, hPι', add_zero]
  -- (a): `⟪ιu, ιu₀ + ι'w⟫ = ⟪u, u₀⟫ = ⟪u, P(ιu₀ + ι'w)⟫`
  have hadj : ∀ (u : Euclid n) (y : Euclid (n + k)), inner ℝ (ι u) y = inner ℝ u (P y) := by
    intro u y
    obtain ⟨u₀, w, rfl⟩ := hdecomp y
    rw [hP, inner_add_right, hιι', add_zero, LinearIsometry.inner_map_map]
  -- (b): `p_T(ιu₀ + ι'w) = ιu₀ + 0 = ι(P(ιu₀ + ι'w))`
  have hpT : ∀ y, T.starProjection y = ι (P y) := by
    intro y
    obtain ⟨u₀, w, rfl⟩ := hdecomp y
    rw [hP, map_add, Submodule.starProjection_eq_self_iff.mpr (hιT u₀),
      (T.starProjection_apply_eq_zero_iff).mpr (hι'T w), add_zero]
  -- (d): Pythagoras for `y = p_T y + (y − p_T y)`, with `|p_T y| = |ι(Py)| = |Py|`
  have hpyth : ∀ y, ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - T.starProjection y‖ ^ 2 := by
    intro y
    have h0 : inner ℝ (T.starProjection y) (y - T.starProjection y) = 0 := by
      rw [real_inner_comm]
      exact T.starProjection_inner_eq_zero y _ (T.starProjection_apply_mem y)
    have h1 : ‖T.starProjection y‖ = ‖P y‖ := by rw [hpT, LinearIsometry.norm_map]
    have h2 := norm_add_sq_real (T.starProjection y) (y - T.starProjection y)
    rw [add_sub_cancel, h0, h1] at h2
    linarith
  -- (e): `|Py|² ≤ |y|²` by (d)
  have hPle : ∀ y, ‖P y‖ ≤ ‖y‖ := by
    intro y
    have h : ‖P y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hpyth y]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  exact ⟨hadj, hpT, hι'T, hpyth, hPle⟩

/-- **Graph-plane estimates at one point** (Simon Ch. 5, proof of 4.5, (7), (9), (10),
`chapter-05.txt` lines 833–872).  `Q = {ιw + ι'(Lw)}` is the graph plane of `L`, `‖L‖ ≤ 1`, over
`T = ι(ℝⁿ)`, and (Q1), (Q2) are the tilt bounds `|⟨p_Q a, b⟩ − ⟨a, b⟩| ≤ t|a||b|` on `T` and
`|p_Q e|² ≤ t|e|²` on `Tᗮ`.  Let `α` be the Riesz vector of `λ = proj_j ∘ L`.  Every
`q = ιw + ι'(Lw) ∈ Q` has `⟨q, ι'ε_j⟩ = λw = ⟨q, ια⟩`, so `p_Q(ι'ε_j) = p_Q(ια)` ((7)).  Hence
`⟨p_Q(ια), ια⟩ = |p_Q(ια)|² = |p_Q(ι'ε_j)|² ≤ t`, and (Q1) with `a = b = ια` gives
`‖λ‖² = |ια|² ≤ t + t|ια|² ≤ 2t`.  For `m` with Riesz vector `β`, `⟨ιβ, y⟩ = ⟨β, Py⟩`
(`dorag_tes_gv_adapted_frame`) gives `m(P p_Q(ι'ε_j)) = ⟨p_Q(ια), ιβ⟩`, Parseval gives
`Σᵢ λ(eᵢ)m(eᵢ) = ⟨α, β⟩ = ⟨ια, ιβ⟩`, and (Q1) bounds the difference by `t‖λ‖‖m‖ ≤ t‖m‖`. -/
theorem Submission.dorag_tes_gv_graph_plane_pointwise : ∀ (n k : ℕ) (T Q : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (L : Euclid n →L[ℝ] Euclid k) (j : Fin k) (t : ℝ), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → Q = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ L.toLinearMap) → ‖L‖ ≤ 1 → 0 ≤ t → (∀ a b : Euclid (n + k), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ t * ‖a‖ * ‖b‖) → (∀ e : Euclid (n + k), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ t * ‖e‖ ^ 2) → ‖(EuclideanSpace.proj j).comp L‖ ^ 2 ≤ 2 * t ∧ ∀ m : Euclid n →L[ℝ] ℝ, |m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) - ∑ i : Fin n, ((EuclideanSpace.proj j).comp L) (EuclideanSpace.single i (1 : ℝ)) * m (EuclideanSpace.single i (1 : ℝ))| ≤ t * ‖m‖ := by
  intro n k T Q ι ι' P L j t hT hιι' hιT hPι hPι' hQ hL ht hQ1 hQ2
  obtain ⟨hadj, -, hι'T, -, -⟩ :=
    Submission.dorag_tes_gv_adapted_frame n k T ι ι' P hT hιι' hιT hPι hPι'
  -- `λ = proj_j ∘ L` has `|λw| = |(Lw)_j| ≤ |Lw| ≤ |w|`, so `‖λ‖ ≤ 1`
  have hlamj : ∀ w, (EuclideanSpace.proj j).comp L w = L w j := fun w => rfl
  have hlam1 : ‖(EuclideanSpace.proj j).comp L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    calc ‖(EuclideanSpace.proj j).comp L w‖ = ‖L w j‖ := by rw [hlamj]
      _ ≤ ‖L w‖ := PiLp.norm_apply_le (L w) j
      _ ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg w)
  generalize (EuclideanSpace.proj j).comp L = lam at hlam1 hlamj ⊢
  -- Riesz vectors: `⟨γ, w⟩ = μ w` and `|ιγ| = ‖μ‖`
  have riesz : ∀ μ : Euclid n →L[ℝ] ℝ,
      ∃ γ : Euclid n, (∀ w, inner ℝ γ w = μ w) ∧ ‖ι γ‖ = ‖μ‖ := fun μ =>
    ⟨(InnerProductSpace.toDual ℝ (Euclid n)).symm μ, fun _ => InnerProductSpace.toDual_symm_apply,
      by rw [ι.norm_map, LinearIsometryEquiv.norm_map]⟩
  obtain ⟨α, hα, ha⟩ := riesz lam
  -- (7): `ι'ε_j − ια ⊥ Q`, since `⟨q, ι'ε_j⟩ = λw = ⟨q, ια⟩` for `q = ιw + ι'(Lw)`
  have hgraph : Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))) =
      Q.starProjection (ι α) := by
    have hperp : ι' (EuclideanSpace.single j (1 : ℝ)) - ι α ∈ Qᗮ := by
      rw [Submodule.mem_orthogonal]
      intro q hq
      rw [hQ] at hq
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hq
      have h1 : inner ℝ (ι w) (ι' (EuclideanSpace.single j (1 : ℝ))) = 0 := hιι' _ _
      have h2 : inner ℝ (ι' (L w)) (ι' (EuclideanSpace.single j (1 : ℝ))) = lam w := by
        rw [LinearIsometry.inner_map_map, EuclideanSpace.inner_single_right, hlamj]
        simp
      have h3 : inner ℝ (ι w) (ι α) = lam w := by
        rw [LinearIsometry.inner_map_map, real_inner_comm, hα]
      have h4 : inner ℝ (ι' (L w)) (ι α) = 0 := by
        rw [real_inner_comm]
        exact hιι' _ _
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toLinearMap, ContinuousLinearMap.coe_coe]
      rw [inner_sub_right, inner_add_left, inner_add_left, h1, h2, h3, h4]
      ring
    have h0 := (Submodule.starProjection_apply_eq_zero_iff (K := Q)).2 hperp
    rwa [map_sub, sub_eq_zero] at h0
  -- (9): `⟨p_Q(ια), ια⟩ = |p_Q(ια)|² = |p_Q(ι'ε_j)|² ≤ t` by (Q2)
  have hpa : inner ℝ (Q.starProjection (ι α)) (ι α) = ‖Q.starProjection (ι α)‖ ^ 2 := by
    have h := Submodule.starProjection_inner_eq_zero (K := Q) (ι α) _
      (Q.starProjection_apply_mem (ι α))
    rw [inner_sub_left, sub_eq_zero] at h
    rw [real_inner_comm, h, real_inner_self_eq_norm_sq]
  have hpa_le : ‖Q.starProjection (ι α)‖ ^ 2 ≤ t := by
    have h := hQ2 _ (hι'T (EuclideanSpace.single j (1 : ℝ)))
    have he : ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
    rwa [he, one_pow, mul_one, hgraph] at h
  refine ⟨?_, fun m => ?_⟩
  · -- (Q1) with `a = b = ια`: `|ια|² ≤ |p_Q(ια)|² + t|ια|² ≤ t + t`
    have h := hQ1 (ι α) (ι α) (hιT α) (hιT α)
    rw [hpa, real_inner_self_eq_norm_sq, ha] at h
    have hsq : ‖lam‖ * ‖lam‖ ≤ 1 := by nlinarith [norm_nonneg lam]
    nlinarith [(abs_le.1 h).1, mul_le_mul_of_nonneg_left hsq ht]
  · -- (10): with `β` the Riesz vector of `m`, `m(P y) = ⟨β, P y⟩ = ⟨ιβ, y⟩`
    obtain ⟨β, hβ, hb⟩ := riesz m
    have hmP : m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) =
        inner ℝ (Q.starProjection (ι α)) (ι β) := by
      rw [← hβ, ← hadj, hgraph, real_inner_comm]
    -- Parseval in the basis `(eᵢ)`: `Σᵢ λ(eᵢ)m(eᵢ) = ⟨α, β⟩ = ⟨ια, ιβ⟩`
    have hsum : ∑ i : Fin n, lam (EuclideanSpace.single i (1 : ℝ)) *
        m (EuclideanSpace.single i (1 : ℝ)) = inner ℝ (ι α) (ι β) := by
      rw [LinearIsometry.inner_map_map,
        ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner α β]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.basisFun_apply, hα, real_inner_comm, hβ]
    rw [hmP, hsum]
    calc |inner ℝ (Q.starProjection (ι α)) (ι β) - inner ℝ (ι α) (ι β)|
        ≤ t * ‖ι α‖ * ‖ι β‖ := hQ1 _ _ (hιT α) (hιT β)
      _ = t * ‖lam‖ * ‖m‖ := by rw [ha, hb]
      _ ≤ t * 1 * ‖m‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam1 ht) (norm_nonneg m)
      _ = t * ‖m‖ := by rw [mul_one]
/-- First variation of a vertical field (Simon Ch. 4, 2.2–2.3): for differentiable `ζ` and a
fixed `e`, `D(ζe)(x) = Dζ(x)(·) e`, so `p_x ∘ D(ζe)(x)` is the rank-one map `y ↦ Dζ(x)(y) p_x e`
and `div_M(ζe)(x) = Dζ(x)(p_x e)`.  As `μ_V = (Hⁿ⌞M).withDensity θ` with `θ` measurable and
finite, `δV(ζe) = ∫_M θ Dζ(x)(p_x e) dHⁿ = ∫ Dζ(x)(p_x e) dμ_V`, with no integrability needed. -/
theorem Submission.dorag_tes_gv_vertical_field_first_variation : ∀ (m n : ℕ) (U : Set (Euclid m)) (R : IMRep U n) (ζ : Euclid m → ℝ) (e : Euclid m), Differentiable ℝ ζ → R.firstVariation (fun x => ζ x • e) = ∫ x, fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure := by
  intro m n U R ζ e hζ
  -- `div_M(ζe)(x) = trace(p_x ∘ Dζ(x).smulRight e) = trace(Dζ(x).smulRight (p_x e)) = Dζ(x)(p_x e)`
  have hdiv : ∀ x, tangentialDivergence n R.carrier (fun x => ζ x • e) x =
      fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) := by
    intro x
    unfold tangentialDivergence
    rw [fderiv_smul_const (hζ x) e]
    have hrank : (approxTangentPlane n R.carrier x).starProjection.toLinearMap ∘ₗ
        ((fderiv ℝ ζ x).smulRight e).toLinearMap =
        (fderiv ℝ ζ x).toLinearMap.smulRight
          ((approxTangentPlane n R.carrier x).starProjection e) := by
      ext y
      simp [map_smul]
    rw [hrank, LinearMap.trace_smulRight]
    rfl
  -- `μ_V = (Hⁿ⌞M).withDensity θ`, `θ` measurable and finite: `∫ g dμ_V = ∫_M θ g dHⁿ` for all `g`
  unfold IMRep.firstVariation IMRep.measure
  have hmeas : Measurable fun x => ((R.mult x : ℕ) : ℝ≥0∞) :=
    measurable_from_nat.comp R.measurable_mult
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall fun x => by simp)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hdiv x, ENNReal.toReal_natCast, smul_eq_mul]
/-- **Cutoff extension along a projection** (Steps 3.1–3.3 of the graph first-variation estimate):
if `n ≥ 1`, `ζ ∈ C¹(ℝⁿ)` has `tsupport ζ ⊆ B̆_{r/2}(0)` and `‖Dζ‖ ≤ G`, then
`ψ = (ζ ∘ φ) h₀`, `φ(x) = P(x − ξ)`, with `h₀` the `ContDiffBump` at `ξ` of radii `7r/8 < r`, is
`C¹` with compact support in `B_r(ξ)` and `|ψ| ≤ Gr/2` (`ζ` is `G`-Lipschitz and vanishes on the
sphere `|v| = r/2`).  If `|x − ξ|² ≤ |φ(x)|² + r²/16`, then `Dψ(x) = Dζ(φ(x)) ∘ P`: for
`|φ(x)| < r/2` we get `|x − ξ| < 7r/8`, so `h₀ = 1` near `x`; for `|φ(x)| ≥ r/2` both sides
vanish, `φ(x)` lying outside `tsupport ζ`. -/
theorem Submission.dorag_tes_gv_cutoff_extension : ∀ (n m : ℕ), 0 < n → ∀ (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ), 0 < r → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ∃ ψ : Euclid m → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ closedBall ξ r ∧ (∀ x, |ψ x| ≤ G * (r / 2)) ∧ ∀ x, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16 → fderiv ℝ ψ x = (fderiv ℝ ζ (P (x - ξ))).comp P := by
  intro n m hn ξ r P ζ G hr hζ hζc hζs hζG
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  have hζdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- `ζ` is `G`-Lipschitz and vanishes outside `B̆_{r/2}(0)`
  have hζlip : ∀ v w, |ζ v - ζ w| ≤ G * ‖v - w‖ := by
    intro v w
    simpa [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hζdiff x) (fun x _ => hζG x) (mem_univ w) (mem_univ v)
  have hζs' : ∀ v, r / 2 ≤ ‖v‖ → v ∉ tsupport ζ := by
    intro v hv h
    have := hζs h
    rw [mem_ball, dist_zero_right] at this
    linarith
  -- `|ζ v| ≤ G r/2`: compare `v` with `w = v + (r/2 − |v|) u` on the sphere `|w| = r/2`
  have hζsup : ∀ v, |ζ v| ≤ G * (r / 2) := by
    intro v
    by_cases hv : r / 2 ≤ ‖v‖
    · rw [image_eq_zero_of_notMem_tsupport (hζs' v hv), abs_zero]
      positivity
    · replace hv := not_le.mp hv
      obtain ⟨u, hu1, hu⟩ : ∃ u : Euclid n, ‖u‖ = 1 ∧ ‖v + (r / 2 - ‖v‖) • u‖ = r / 2 := by
        by_cases hv0 : v = 0
        · refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), by simp, ?_⟩
          subst hv0
          simp [norm_smul, abs_of_pos hr]
        · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
          refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne'], ?_⟩
          have : v + (r / 2 - ‖v‖) • (‖v‖⁻¹ • v) = ((r / 2) / ‖v‖) • v := by
            rw [smul_smul, ← one_smul ℝ v, smul_smul, ← add_smul, one_smul]
            congr 1
            field_simp
            ring
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
            div_mul_cancel₀ _ hvpos.ne']
      have hw : ζ (v + (r / 2 - ‖v‖) • u) = 0 := image_eq_zero_of_notMem_tsupport (hζs' _ hu.ge)
      calc |ζ v| = |ζ v - ζ (v + (r / 2 - ‖v‖) • u)| := by rw [hw, sub_zero]
        _ ≤ G * ‖v - (v + (r / 2 - ‖v‖) • u)‖ := hζlip _ _
        _ = G * (r / 2 - ‖v‖) := by
            rw [sub_add_cancel_left, norm_neg, norm_smul, hu1, mul_one, Real.norm_eq_abs,
              abs_of_pos (by linarith)]
        _ ≤ G * (r / 2) := by gcongr; linarith [norm_nonneg v]
  -- `ψ = (ζ ∘ φ) h₀`, `φ(y) = P(y − ξ)`
  let h0 : ContDiffBump ξ := ⟨7 * r / 8, r, by positivity, by linarith⟩
  have hφd : ∀ x, HasFDerivAt (fun y : Euclid m => P (y - ξ)) P x := by
    intro x
    have h := P.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const ξ)
    rwa [ContinuousLinearMap.comp_id] at h
  have hφc : Continuous (fun y : Euclid m => P (y - ξ)) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  refine ⟨fun x => ζ (P (x - ξ)) * h0 x, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hζ.comp (P.contDiff.comp (contDiff_id.sub contDiff_const))).mul h0.contDiff
  · exact HasCompactSupport.mul_left (f := fun x => ζ (P (x - ξ))) h0.hasCompactSupport
  · exact tsupport_mul_subset_right.trans h0.tsupport_eq.subset
  · intro x
    rw [abs_mul, abs_of_nonneg h0.nonneg]
    calc |ζ (P (x - ξ))| * h0 x ≤ G * (r / 2) * 1 :=
          mul_le_mul (hζsup _) h0.le_one h0.nonneg (by positivity)
      _ = G * (r / 2) := mul_one _
  · intro x hx
    by_cases hφ : ‖P (x - ξ)‖ < r / 2
    · -- `|x − ξ|² < r²/4 + r²/16 < (7r/8)²`, so `h₀ = 1` near `x` and the chain rule applies
      have hx' : ‖x - ξ‖ < 7 * r / 8 := by
        have h1 : ‖x - ξ‖ ^ 2 < (7 * r / 8) ^ 2 := by nlinarith [norm_nonneg (P (x - ξ))]
        nlinarith [norm_nonneg (x - ξ)]
      have hev : (fun y => ζ (P (y - ξ)) * h0 y) =ᶠ[𝓝 x] fun y => ζ (P (y - ξ)) := by
        filter_upwards [h0.eventuallyEq_one_of_mem_ball (show x ∈ ball ξ (7 * r / 8) by
          rwa [mem_ball, dist_eq_norm])] with y hy
        rw [hy, Pi.one_apply, mul_one]
      rw [hev.fderiv_eq]
      exact ((hζdiff _).hasFDerivAt.comp x (hφd x)).fderiv
    · -- `φ = P(· − ξ)` maps a neighbourhood of `x` outside `tsupport ζ`: both sides vanish
      have hns := hζs' _ (not_lt.mp hφ)
      have hev : (fun y => ζ (P (y - ξ)) * h0 y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [((isClosed_tsupport ζ).isOpen_compl.preimage hφc).mem_nhds hns] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      rw [hev.fderiv_eq, fderiv_of_notMem_tsupport ℝ hns]
      simp

/-- **First-variation bound for vertical cutoff fields** (Simon Ch. 5, proof of 4.5: the
first-variation identity (6) tested with the vertical field `X = ζ̃ e`).  Let `R` satisfy
`δV(X) = −∫ X · H dμ` for `X ∈ C¹_c` with `spt X ⊆ W ⊆ U`, where `|H| ≤ κ`, `μ = μ_V`, and
`x ↦ p_{TₓM}` is `μ`-measurable.  Let `B_r(ξ) ⊆ W`, `|Py| ≤ |y|`, and
`|x − ξ|² ≤ |P(x − ξ)|² + r²/16` on `spt μ ∩ B_r(ξ)`.  If `ζ ∈ C¹_c(ℝⁿ)`,
`spt ζ ⊆ B̆ⁿ_{r/2}(0)`, `‖Dζ‖ ≤ G` and `|e| ≤ 1`, then `u(x) = Dζ(P(x − ξ))(P(p_{TₓM} e))` is
`μ`-integrable on `B_r(ξ)` and `|∫_{B_r(ξ)} u dμ| ≤ G (κr/2) μ(B_r(ξ))`.
Proof: extend `ζ` to the cutoff `ψ` of `dorag_tes_gv_cutoff_extension`, test with `X = ψ e`,
compute `δV(X) = ∫ Dψ(p_{TₓM} e) dμ` by `dorag_tes_gv_vertical_field_first_variation`, localize
to `B_r(ξ)` (where `Dψ = Dζ(P(· − ξ)) ∘ P` on the conull set `spt μ`), and bound
`|ψ e · H| ≤ (Gr/2) κ 1_{B_r(ξ)}`. -/
theorem Submission.dorag_tes_gv_vertical_variation_bound : ∀ (n m : ℕ), 0 < n → ∀ (U W : Set (Euclid m)) (R : IMRep U n) (H : Euclid m → Euclid m) (κ : ℝ) (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ) (e : Euclid m), W ⊆ U → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid m → Euclid m, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → (∀ y, ‖P y‖ ≤ ‖y‖) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ‖e‖ ≤ 1 → IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure ∧ ENNReal.ofReal |∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure| ≤ ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
  intro n m hn U W R H κ ξ r P ζ G e hWU hHκ hFV hp hr hBW hPle hspt hζ hζc hζs hζG he
  -- Step 1: `G, κ ≥ 0`.
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- Step 2: `μ(B_r(ξ)) < ∞`, since `B_r(ξ)` is a compact subset of `U`.
  have hfin : R.measure (closedBall ξ r) ≠ ∞ := by
    unfold IMRep.measure
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall ξ r) (hBW.trans hWU)
  -- Step 3: the cutoff `ψ` extending `ζ ∘ P(· − ξ)`.
  obtain ⟨ψ, hψ, hψc, hψs, hψb, hψd⟩ :=
    Submission.dorag_tes_gv_cutoff_extension n m hn ξ r P ζ G hr hζ hζc hζs hζG
  have hψ0 : ∀ x, x ∉ closedBall ξ r → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hψs h)
  -- Step 4: `X = ψ e` is an admissible test field.
  have hX : ContDiff ℝ 1 (fun x => ψ x • e) := hψ.smul contDiff_const
  have hXc : HasCompactSupport (fun x => ψ x • e) := hψc.smul_right
  have hXs : tsupport (fun x => ψ x • e) ⊆ W :=
    (tsupport_smul_subset_left _ _).trans (hψs.trans hBW)
  have hfv : R.firstVariation (fun x => ψ x • e) =
      -∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure := hFV _ hX hXc hXs
  -- Step 5: `δV(ψ e) = ∫ Dψ(x)(p_{TₓM} e) dμ`.
  rw [Submission.dorag_tes_gv_vertical_field_first_variation m n U R ψ e
    (hψ.differentiable one_ne_zero)] at hfv
  -- Step 6: localization to `B_r(ξ)`, where `Dψ = Dζ(P(· − ξ)) ∘ P` on `spt μ`.
  have hloc : ∫ x, fderiv ℝ ψ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure =
      ∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall ξ r)]
    · refine setIntegral_congr_ae measurableSet_closedBall ?_
      filter_upwards [Measure.support_mem_ae (μ := R.measure)] with x hxs hxB
      rw [hψd x (hspt x ⟨hxs, hxB⟩), ContinuousLinearMap.comp_apply]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hψs h)), zero_apply]
  -- Step 8: `|ψ e · H| ≤ (Gr/2) κ 1_{B_r(ξ)}`, hence the bound on `∫ ψ e · H dμ`.
  have hpt : ∀ x, ‖inner ℝ (ψ x • e) (H x)‖ ≤
      (closedBall ξ r).indicator (fun _ => G * (r / 2) * κ) x := by
    intro x
    by_cases hx : x ∈ closedBall ξ r
    · rw [indicator_of_mem hx, real_inner_smul_left, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have heH : |inner ℝ e (H x)| ≤ κ :=
        calc |inner ℝ e (H x)| ≤ ‖e‖ * ‖H x‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * κ := mul_le_mul he (hHκ x) (norm_nonneg _) zero_le_one
          _ = κ := one_mul κ
      exact mul_le_mul (hψb x) heH (abs_nonneg _) (by positivity)
    · rw [indicator_of_notMem hx, hψ0 x hx, zero_smul, inner_zero_left, norm_zero]
  have hbd : |∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure| ≤
      G * (r / 2) * κ * R.measure.real (closedBall ξ r) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure‖
        ≤ ∫ x, (closedBall ξ r).indicator (fun _ => G * (r / 2) * κ) x ∂R.measure :=
          norm_integral_le_of_norm_le
            ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin))
            (Eventually.of_forall hpt)
      _ = G * (r / 2) * κ * R.measure.real (closedBall ξ r) := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
  -- Step 10: `u` is a.e. strongly measurable and bounded by `G`, hence integrable on `B_r(ξ)`.
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ ζ (P (x - ξ))
      (P ((approxTangentPlane n R.carrier x).starProjection e))) R.measure := by
    have hDζ : Continuous fun x : Euclid m => fderiv ℝ ζ (P (x - ξ)) :=
      (hζ.continuous_fderiv one_ne_zero).comp
        (P.continuous.comp (continuous_id.sub continuous_const))
    exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hDζ.aestronglyMeasurable.prodMk
        (P.continuous.comp_aestronglyMeasurable (hp.apply_continuousLinearMap e)))
  have hint : IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ))
      (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure := by
    refine Measure.integrableOn_of_bounded (M := G) hfin hmeas (Eventually.of_forall fun x => ?_)
    calc ‖fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))‖
        ≤ ‖fderiv ℝ ζ (P (x - ξ))‖ *
            ‖P ((approxTangentPlane n R.carrier x).starProjection e)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ G * 1 := mul_le_mul (hζG _)
          ((hPle _).trans ((Submodule.norm_starProjection_apply_le _ _).trans he))
          (norm_nonneg _) hG
      _ = G := mul_one G
  -- Steps 7 and 9: `∫_{B_r(ξ)} u dμ = −∫ ψ e · H dμ`, then pass to `ℝ≥0∞`.
  refine ⟨hint, ?_⟩
  rw [← hloc, hfv, abs_neg]
  calc ENNReal.ofReal |∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure|
      ≤ ENNReal.ofReal (G * (κ * r / 2 * R.measure.real (closedBall ξ r))) :=
        ENNReal.ofReal_le_ofReal (hbd.trans_eq (by ring))
    _ = ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
        rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_mul (by positivity), ofReal_measureReal hfin]
/-- Splitting estimate for set integrals (the splitting of `B_r(ξ)` into the graph part and its
complement in the graph first-variation estimate, for abstract integrands).  If `g` is integrable
on `A`, then `∫_A g = ∫_B u − ∫_{B∖A} u − ∫_A (u − g)`; the first term is bounded by `C`, the
second by `G μ(B ∖ F)` (as `|u| ≤ G` on `B` and `u = 0` on `(B ∖ A) ∩ F`), and the third by
`G ∫_B t` (as `|u − g| ≤ G t` on `A ⊆ B`).  Otherwise `∫_A g = 0`. -/
theorem Submission.dorag_tes_gv_split_integral_estimate : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (A B F : Set X) (u g t : X → ℝ) (G : ℝ) (C : ℝ≥0∞), MeasurableSet A → MeasurableSet B → MeasurableSet F → A ⊆ B → 0 ≤ G → IntegrableOn u B μ → ENNReal.ofReal |∫ x in B, u x ∂μ| ≤ C → (∀ᵐ x ∂μ, x ∈ B → |u x| ≤ G) → (∀ᵐ x ∂μ, x ∈ B → x ∉ A → x ∈ F → u x = 0) → (∀ᵐ x ∂μ, x ∈ A → |u x - g x| ≤ G * t x) → ENNReal.ofReal |∫ x in A, g x ∂μ| ≤ ENNReal.ofReal G * (∫⁻ x in B, ENNReal.ofReal (t x) ∂μ + μ (B \ F)) + C := by
  intro X _ μ A B F u g t G C hA hB hF hAB hG hu hC hbd hzero hdiff
  -- if `g` is not integrable on `A`, the left side is `ofReal |0| = 0`
  by_cases hg : IntegrableOn g A μ
  swap
  · rw [integral_undef hg]
    simp
  -- `∫_A g = ∫_B u − ∫_{B∖A} u − ∫_A (u − g)`
  have huA : IntegrableOn u A μ := hu.mono_set hAB
  have hgA : ∫ x in A, g x ∂μ =
      ∫ x in B, u x ∂μ - ∫ x in B \ A, u x ∂μ - ∫ x in A, (u x - g x) ∂μ := by
    rw [integral_sub huA hg, ← integral_inter_add_sdiff hA hu, inter_eq_right.mpr hAB]
    ring
  -- off `A`: `‖u‖ₑ ≤ ofReal G · 1_{X∖F}` a.e. on `B ∖ A`
  have hoff : ENNReal.ofReal |∫ x in B \ A, u x ∂μ| ≤ ENNReal.ofReal G * μ (B \ F) := by
    calc ENNReal.ofReal |∫ x in B \ A, u x ∂μ| = ‖∫ x in B \ A, u x ∂μ‖ₑ :=
          (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ x in B \ A, ‖u x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in B \ A, Fᶜ.indicator (fun _ => ENNReal.ofReal G) x ∂μ := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' (hB.diff hA)]
          filter_upwards [hbd, hzero] with x hxbd hxzero hx
          by_cases hxF : x ∈ F
          · simp [hxzero hx.1 hx.2 hxF]
          · rw [indicator_of_mem (mem_compl hxF), Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hxbd hx.1)
      _ = ENNReal.ofReal G * μ (Fᶜ ∩ (B \ A)) := by
          rw [lintegral_indicator_const hF.compl, Measure.restrict_apply hF.compl]
      _ ≤ ENNReal.ofReal G * μ (B \ F) := by
          gcongr
          exact fun x hx => ⟨hx.2.1, hx.1⟩
  -- on `A`: `‖u − g‖ₑ ≤ ofReal G · ofReal t` a.e. on `A`, and `A ⊆ B`
  have hon : ENNReal.ofReal |∫ x in A, (u x - g x) ∂μ| ≤
      ENNReal.ofReal G * ∫⁻ x in B, ENNReal.ofReal (t x) ∂μ := by
    calc ENNReal.ofReal |∫ x in A, (u x - g x) ∂μ| = ‖∫ x in A, (u x - g x) ∂μ‖ₑ :=
          (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ x in A, ‖u x - g x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in A, ENNReal.ofReal G * ENNReal.ofReal (t x) ∂μ := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hA]
          filter_upwards [hdiff] with x hx hxA
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hG]
          exact ENNReal.ofReal_le_ofReal (hx hxA)
      _ = ENNReal.ofReal G * ∫⁻ x in A, ENNReal.ofReal (t x) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal G * ∫⁻ x in B, ENNReal.ofReal (t x) ∂μ := by
          gcongr
  -- triangle inequality and subadditivity of `ofReal`, then the three bounds
  calc ENNReal.ofReal |∫ x in A, g x ∂μ|
      ≤ ENNReal.ofReal (|∫ x in B, u x ∂μ| + |∫ x in B \ A, u x ∂μ| +
          |∫ x in A, (u x - g x) ∂μ|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hgA]
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ ENNReal.ofReal |∫ x in B, u x ∂μ| + ENNReal.ofReal |∫ x in B \ A, u x ∂μ| +
          ENNReal.ofReal |∫ x in A, (u x - g x) ∂μ| := by
        refine ENNReal.ofReal_add_le.trans ?_
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ C + ENNReal.ofReal G * μ (B \ F) +
          ENNReal.ofReal G * ∫⁻ x in B, ENNReal.ofReal (t x) ∂μ := by
        gcongr
    _ = ENNReal.ofReal G * (∫⁻ x in B, ENNReal.ofReal (t x) ∂μ + μ (B \ F)) + C := by
        ring
/-- **Hilbert–Schmidt inequalities for orthogonal projections** (Simon Ch. 5, Remark 4.4 and
(10)–(11) in the proof of 4.5; chapter-05.txt lines 715–737, 869–883).  Write
`eᵢ = EuclideanSpace.single i 1`, `|A|² = Σᵢ ‖A eᵢ‖²` and `p_Q = Q.starProjection`.  Then
(a) `‖A y‖² ≤ |A|² ‖y‖²` (operator norm `≤` inner product norm); (b)
`|p_S − p_T|² ≤ 2|p_Q − p_S|² + 2|p_Q − p_T|²`; (c) `|⟨p_Q a, b⟩ − ⟨a, b⟩| ≤ |p_Q − p_T|² ‖a‖ ‖b‖`
for `a, b ∈ T`, since `⟨p_Q a, b⟩ − ⟨a, b⟩ = −⟨(p_Q − p_T) a, (p_Q − p_T) b⟩`; (d)
`‖p_Q e‖² ≤ |p_Q − p_T|² ‖e‖²` for `e ∈ Tᗮ`, since `p_Q e = (p_Q − p_T) e`. -/
theorem Submission.dorag_tes_projection_algebra : ∀ (N : ℕ), (∀ (A : Euclid N →L[ℝ] Euclid N) (y : Euclid N), ‖A y‖ ^ 2 ≤ (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖y‖ ^ 2) ∧ (∀ Q S T : Submodule ℝ (Euclid N), ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 + 2 * ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∧ (∀ (Q T : Submodule ℝ (Euclid N)) (a b : Euclid N), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ (∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖a‖ * ‖b‖) ∧ ∀ (Q T : Submodule ℝ (Euclid N)) (e : Euclid N), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ (∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖e‖ ^ 2 := by
  intro N
  -- (a): `y = Σᵢ yᵢ eᵢ`, so `‖Ay‖ ≤ Σᵢ |yᵢ| ‖Aeᵢ‖`; then Cauchy–Schwarz and `Σᵢ yᵢ² = ‖y‖²`.
  have ha : ∀ (A : Euclid N →L[ℝ] Euclid N) (y : Euclid N), ‖A y‖ ^ 2 ≤
      (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖y‖ ^ 2 := by
    intro A y
    have hAy : A y = ∑ i : Fin N, y i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr y]
      simp [map_sum, map_smul]
    have h1 : ‖A y‖ ≤ ∑ i : Fin N, |y i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAy]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_smul]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin N => |y i|)
      (fun i => ‖A (EuclideanSpace.single i (1 : ℝ))‖)
    have h3 : ∑ i : Fin N, |y i| ^ 2 = ‖y‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq]
    calc ‖A y‖ ^ 2 ≤ (∑ i : Fin N, |y i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ i : Fin N, |y i| ^ 2) * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := h2
      _ = _ := by rw [h3, mul_comm]
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b): termwise `‖sᵢ − tᵢ‖ ≤ ‖qᵢ − sᵢ‖ + ‖qᵢ − tᵢ‖` and `(u + w)² ≤ 2u² + 2w²`.
    intro Q S T
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h : ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ≤
        ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ +
        ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [norm_sub_rev (Q.starProjection _) (S.starProjection _)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    nlinarith [mul_self_le_mul_self (norm_nonneg _) h,
      sq_nonneg (‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ -
        ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖)]
  · -- (c): with `B = p_Q − p_T`, `⟨p_Q a, b⟩ − ⟨a, b⟩ = −⟨Ba, Bb⟩`; Cauchy–Schwarz and (a).
    intro Q T a b haT hbT
    have hBa := ha (Q.starProjection - T.starProjection) a
    have hBb := ha (Q.starProjection - T.starProjection) b
    simp only [sub_apply, Submodule.starProjection_eq_self_iff.mpr haT,
      Submodule.starProjection_eq_self_iff.mpr hbT] at hBa hBb
    have hid : inner ℝ (Q.starProjection a) b - inner ℝ a b =
        -inner ℝ (Q.starProjection a - a) (Q.starProjection b - b) := by
      have h1 : inner ℝ (Q.starProjection a) (Q.starProjection b) =
          inner ℝ (Q.starProjection a) b := by
        rw [Submodule.inner_starProjection_left_eq_right Q a,
          Submodule.starProjection_eq_self_iff.mpr (Q.starProjection_apply_mem b),
          ← Submodule.inner_starProjection_left_eq_right Q a]
      have h2 : inner ℝ a (Q.starProjection b) = inner ℝ (Q.starProjection a) b :=
        (Submodule.inner_starProjection_left_eq_right Q a b).symm
      simp only [inner_sub_left, inner_sub_right, h1, h2]
      ring
    rw [hid, abs_neg]
    refine (abs_real_inner_le_norm _ _).trans ?_
    set H := ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
      T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
    have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : (‖Q.starProjection a - a‖ * ‖Q.starProjection b - b‖) ^ 2 ≤
        (H * ‖a‖ * ‖b‖) ^ 2 := by
      calc (‖Q.starProjection a - a‖ * ‖Q.starProjection b - b‖) ^ 2 =
            ‖Q.starProjection a - a‖ ^ 2 * ‖Q.starProjection b - b‖ ^ 2 := by ring
        _ ≤ (H * ‖a‖ ^ 2) * (H * ‖b‖ ^ 2) :=
          mul_le_mul hBa hBb (sq_nonneg _) (mul_nonneg hH (sq_nonneg _))
        _ = (H * ‖a‖ * ‖b‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (mul_nonneg hH (norm_nonneg _)) (norm_nonneg _)) two_ne_zero).mp hsq
  · -- (d): `p_T e = 0`, so `p_Q e = (p_Q − p_T) e`; then (a).
    intro Q T e he
    have hBe := ha (Q.starProjection - T.starProjection) e
    simp only [sub_apply,
      (Submodule.starProjection_apply_eq_zero_iff T).mpr he, sub_zero] at hBe
    exact hBe

/-- **First variation along a Lipschitz graph, tested with vertical fields** (Simon Ch. 5, proof
of 4.5, (5)–(13); chapter-05.txt lines 807–893).  Write `φ(x) = P(x − ξ)`, `Φ(v) = ξ + ιv + ι'f(v)`,
`D = B̆ⁿ_{r/2}(0)`, `fʲ = proj_j ∘ f` and `tilt(x) = Σᵢ ‖p_{TₓM} eᵢ − p_T eᵢ‖²`.  Then (i)
`∫_{Φ(D)} ‖Dfʲ(φ)‖² dμ ≤ 2 ∫_{B_r(ξ)} tilt dμ` ((9), (13)), and (ii) for `ζ ∈ C¹_c(D)` with
`‖Dζ‖ ≤ G`, `|∫_{Φ(D)} Σᵢ ∂ᵢfʲ(φ) ∂ᵢζ(φ) dμ| ≤ G (∫_{B_r(ξ)} tilt dμ + μ(B_r(ξ) \ Φ(ℝⁿ)) +
(κr/2) μ(B_r(ξ)))` ((8), (11), (12)).  On `Φ(D)` the graph identity (7) and
`dorag_tes_projection_algebra` (c), (d) give the pointwise bounds; the vertical field `ζ(φ) e`,
`e = ι' εⱼ`, is tested in the first variation (6). -/
theorem Submission.dorag_tes_graph_first_variation_estimate : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r : ℝ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖(x - ξ) - T.starProjection (x - ξ)‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → ∀ v : Euclid n, x = ξ + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ j : Fin k, ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2) ∂R.measure ≤ 2 * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) ∧ ∀ (j : Fin k) (ζ : Euclid n → ℝ) (G : ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ENNReal.ofReal |∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) ∂R.measure| ≤ ENNReal.ofReal G * (∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure + R.measure (closedBall ξ r \ range (fun v => ξ + ι v + ι' (f v))) + ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
  intro n k hn U W R H κ ξ r T ι ι' P f _ hWU _ hHκ hFV hpx hr hBW hT hιι' hιT hPι hPι' hfLip hfbd
    hheight htan
  -- Frame: `|y|² = |Py|² + |y − p_T y|²` and `|Py| ≤ |y|`.
  obtain ⟨-, -, -, hpyth, hPle⟩ :=
    Submission.dorag_tes_gv_adapted_frame n k T ι ι' P hT hιι' hιT hPι hPι'
  -- Graph geometry: `φ(Φ(v)) = v`, `|Φ(v) − ξ|² = |v|² + |f(v)|²`, `Φ(D) ⊆ B_r(ξ)`.
  have hLip : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun v w => by
    simpa [dist_eq_norm] using hfLip v w
  have hΦsub : ∀ v, (ξ + ι v + ι' (f v)) - ξ = ι v + ι' (f v) := fun v => by abel
  have hPΦ : ∀ v, P ((ξ + ι v + ι' (f v)) - ξ) = v := fun v => by
    rw [hΦsub, map_add, hPι, hPι', add_zero]
  have hnormΦ : ∀ v, ‖(ξ + ι v + ι' (f v)) - ξ‖ ^ 2 = ‖v‖ ^ 2 + ‖f v‖ ^ 2 := fun v => by
    rw [hΦsub, norm_add_sq_real, hιι', LinearIsometry.norm_map, LinearIsometry.norm_map]; ring
  have hΦD : (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) ⊆ closedBall ξ r := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_closedBall, dist_eq_norm]
    have hv' : ‖v‖ < r / 2 := by simpa using hv
    have h1 := hnormΦ v
    have h3 : ‖f v‖ ^ 2 ≤ (r / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hfbd v) 2
    have h4 : ‖v‖ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv'.le 2
    have h5 : ‖(ξ + ι v + ι' (f v)) - ξ‖ ^ 2 ≤ r ^ 2 := by nlinarith
    nlinarith [norm_nonneg ((ξ + ι v + ι' (f v)) - ξ)]
  -- `Φ(D) = {x | Φ(φ(x)) = x} ∩ φ⁻¹(D)` and `Φ(ℝⁿ) = {x | Φ(φ(x)) = x}` are Borel.
  have hΦcont : Continuous (fun v => ξ + ι v + ι' (f v)) :=
    (continuous_const.add ι.continuous).add (ι'.continuous.comp hLip.continuous)
  have hφcont : Continuous (fun x : Euclid (n + k) => P (x - ξ)) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  have hclosed : IsClosed {x : Euclid (n + k) | ξ + ι (P (x - ξ)) + ι' (f (P (x - ξ))) = x} :=
    isClosed_eq (hΦcont.comp hφcont) continuous_id
  have hAeq : (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) =
      {x : Euclid (n + k) | ξ + ι (P (x - ξ)) + ι' (f (P (x - ξ))) = x} ∩
        (fun x => P (x - ξ)) ⁻¹' ball (0 : Euclid n) (r / 2) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · show ξ + ι (P ((ξ + ι v + ι' (f v)) - ξ)) + ι' (f (P ((ξ + ι v + ι' (f v)) - ξ))) =
          ξ + ι v + ι' (f v)
        rw [hPΦ v]
      · show P ((ξ + ι v + ι' (f v)) - ξ) ∈ ball (0 : Euclid n) (r / 2)
        rw [hPΦ v]; exact hv
    · rintro ⟨h1, h2⟩
      exact ⟨P (x - ξ), h2, h1⟩
  have hFeq : range (fun v => ξ + ι v + ι' (f v)) =
      {x : Euclid (n + k) | ξ + ι (P (x - ξ)) + ι' (f (P (x - ξ))) = x} := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      show ξ + ι (P ((ξ + ι v + ι' (f v)) - ξ)) + ι' (f (P ((ξ + ι v + ι' (f v)) - ξ))) =
        ξ + ι v + ι' (f v)
      rw [hPΦ v]
    · intro h
      exact ⟨P (x - ξ), h⟩
  have hAmeas : MeasurableSet ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) := by
    rw [hAeq]
    exact hclosed.measurableSet.inter (isOpen_ball.preimage hφcont).measurableSet
  have hFmeas : MeasurableSet (range (fun v => ξ + ι v + ι' (f v))) := by
    rw [hFeq]; exact hclosed.measurableSet
  -- Pointwise bounds μ-a.e. on `Φ(D)` (Simon (7), (9)–(11)): the tangent identification
  -- `TₓM = range(ι + ι' ∘ Df(v))`, `Dfʲ(v) = proj_j ∘ Df(v)`, `‖Df(v)‖ ≤ 1`, and
  -- `dorag_tes_projection_algebra` (c), (d) for `(TₓM, T)` with `t = tilt(x)`.
  have hpa := Submission.dorag_tes_projection_algebra (n + k)
  have key : ∀ j : Fin k, ∀ᵐ x ∂R.measure,
      x ∈ (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) →
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2 ≤
          2 * (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∧
        ∀ m : Euclid n →L[ℝ] ℝ,
          |m (P ((approxTangentPlane n R.carrier x).starProjection
              (ι' (EuclideanSpace.single j (1 : ℝ))))) -
            ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
              (EuclideanSpace.single i (1 : ℝ)) * m (EuclideanSpace.single i (1 : ℝ))| ≤
            (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
              (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖m‖ := by
    intro j
    filter_upwards [htan] with x hx hxA
    obtain ⟨v, hv, rfl⟩ := hxA
    obtain ⟨hdiff, hQ⟩ := hx (hΦD ⟨v, hv, rfl⟩) v rfl
    have hchain : fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v =
        (EuclideanSpace.proj j).comp (fderiv ℝ f v) :=
      ((EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).hasFDerivAt.comp v hdiff.hasFDerivAt).fderiv
    have hL : ‖fderiv ℝ f v‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hLip
    dsimp only
    rw [hPΦ v, hchain]
    exact Submission.dorag_tes_gv_graph_plane_pointwise n k T _ ι ι' P (fderiv ℝ f v) j
      (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier (ξ + ι v + ι' (f v))).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      hT hιι' hιT hPι hPι' hQ hL (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (fun a b ha hb => hpa.2.2.1 _ T a b ha hb) (fun e he => hpa.2.2.2 _ T e he)
  refine ⟨fun j => ?_, fun j ζ G hζ hζc hζs hζG => ?_⟩
  · -- (i): integrate `‖Dfʲ(φ)‖² ≤ 2 tilt` over `Φ(D) ⊆ B_r(ξ)` ((9), (13)).
    calc ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
          ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2)
            ∂R.measure
        ≤ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
          2 * ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
          apply lintegral_mono_ae
          filter_upwards [(ae_restrict_iff' hAmeas).mpr (key j)] with x hx
          refine (ENNReal.ofReal_le_ofReal hx.1).trans_eq ?_
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
      _ = 2 * ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
          ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 2 * ∫⁻ x in closedBall ξ r,
          ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
          gcongr
  · -- (ii): test the first variation with the vertical field `ζ(φ) e`, `e = ι' εⱼ` ((6), (8)),
    -- then split `B_r(ξ)` into `Φ(D)` and its complement ((11), (12)).
    have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
    have he1 : ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
    -- Height bound: `|x − ξ|² ≤ |φ(x)|² + r²/16` on `spt μ ∩ B_r(ξ)` (Simon (5)).
    have hloc : ∀ x ∈ R.measure.support ∩ closedBall ξ r,
        ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16 := by
      intro x hx
      have h1 := hpyth (x - ξ)
      have h3 : ‖(x - ξ) - T.starProjection (x - ξ)‖ ^ 2 ≤ (r / 4) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hheight x hx) 2
      nlinarith
    obtain ⟨hint, hbound⟩ := Submission.dorag_tes_gv_vertical_variation_bound n (n + k) hn U W R H
      κ ξ r P ζ G (ι' (EuclideanSpace.single j (1 : ℝ))) hWU hHκ hFV hpx hr hBW hPle hloc hζ hζc
      hζs hζG he1.le
    have hu_bd : ∀ x, |fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection
          (ι' (EuclideanSpace.single j (1 : ℝ)))))| ≤ G := by
      intro x
      rw [← Real.norm_eq_abs]
      calc _ ≤ ‖fderiv ℝ ζ (P (x - ξ))‖ *
            ‖P ((approxTangentPlane n R.carrier x).starProjection
              (ι' (EuclideanSpace.single j (1 : ℝ))))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ G * 1 := by
          gcongr
          · exact hζG _
          · calc _ ≤ ‖(approxTangentPlane n R.carrier x).starProjection
                    (ι' (EuclideanSpace.single j (1 : ℝ)))‖ := hPle _
              _ ≤ ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ :=
                  Submodule.norm_starProjection_apply_le _ _
              _ = 1 := he1
        _ = G := mul_one G
    -- On `(B_r(ξ) \ Φ(D)) ∩ Φ(ℝⁿ)`, `φ(x) ∉ D ⊇ tsupport ζ`, so `Dζ(φ(x)) = 0`.
    have hzero : ∀ x ∈ closedBall ξ r,
        x ∉ (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) →
        x ∈ range (fun v => ξ + ι v + ι' (f v)) →
        fderiv ℝ ζ (P (x - ξ))
          (P ((approxTangentPlane n R.carrier x).starProjection
            (ι' (EuclideanSpace.single j (1 : ℝ))))) = 0 := by
      rintro x - hxA ⟨v, rfl⟩
      have hvD : v ∉ ball (0 : Euclid n) (r / 2) := fun hv => hxA ⟨v, hv, rfl⟩
      have hvs : v ∉ tsupport ζ := fun h => hvD (hζs h)
      dsimp only
      rw [hPΦ v, fderiv_of_notMem_tsupport ℝ hvs]
      rfl
    have hmain := Submission.dorag_tes_gv_split_integral_estimate (Euclid (n + k)) R.measure
      ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) (closedBall ξ r)
      (range (fun v => ξ + ι v + ι' (f v)))
      (fun x => fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection
          (ι' (EuclideanSpace.single j (1 : ℝ))))))
      (fun x => ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
        (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)))
      (fun x => ∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      G (ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)))
      hAmeas measurableSet_closedBall hFmeas hΦD hG hint hbound
      (Eventually.of_forall fun x _ => hu_bd x)
      (Eventually.of_forall fun x hxB hxA hxF => hzero x hxB hxA hxF)
      (by
        filter_upwards [key j] with x hx hxA
        obtain ⟨-, h2⟩ := hx hxA
        have ht : 0 ≤ ∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        refine (h2 (fderiv ℝ ζ (P (x - ξ)))).trans ?_
        rw [mul_comm G]
        exact mul_le_mul_of_nonneg_left (hζG _) ht)
    rw [mul_add]
    exact hmain
/-- Squared columns of a derivative are bounded by its squared rows: for any `f : ℝⁿ → ℝᵏ` and
`v`, `Σᵢ |Df(v)eᵢ|² ≤ Σⱼ ‖Dfʲ(v)‖²`, where `fʲ = projⱼ ∘ f`.  If `f` is not differentiable at `v`,
then `Df(v) = 0` and the left side is `0`.  Otherwise `Dfʲ(v) = projⱼ ∘ Df(v)` by the chain rule;
the Riesz representative `u` of a functional `ψ` on `ℝⁿ` has `|u| = ‖ψ‖` and `uᵢ = ⟨u, eᵢ⟩ = ψ(eᵢ)`,
so `‖ψ‖² = Σᵢ ψ(eᵢ)²`, and exchanging the two finite sums gives equality. -/
theorem Submission.dorag_tes_gt_fderiv_columns_sq_le_rows_sq : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (v : Euclid n), ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 := by
  intro n k f v
  by_cases hf : DifferentiableAt ℝ f v
  · have hrow : ∀ ψ : Euclid n →L[ℝ] ℝ,
        ∑ i : Fin n, ψ (EuclideanSpace.single i (1 : ℝ)) ^ 2 = ‖ψ‖ ^ 2 := by
      intro ψ
      rw [← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ (Euclid n)).symm ψ,
        EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right, one_mul,
        conj_trivial]
    have hder : ∀ j : Fin k, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v =
        (EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).comp (fderiv ℝ f v) := fun j =>
      ((EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).hasFDerivAt.comp v hf.hasFDerivAt).fderiv
    refine le_of_eq ?_
    calc ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
        = ∑ i : Fin n, ∑ j : Fin k, fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ)) j ^ 2 :=
          Finset.sum_congr rfl fun i _ => EuclideanSpace.real_norm_sq_eq _
      _ = ∑ j : Fin k, ∑ i : Fin n, fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ)) j ^ 2 :=
          Finset.sum_comm
      _ = ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [hder j, ← hrow]; rfl
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp only [zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
/-- Exceptional parameter set for the multiplicity-one graph measure.  Let `μ = θ Hⁿ⌞M` be the
weight of `R = (M, θ, ·)`, `Φ(v) = ξ + ιv + ι'f(v)` with `|f(v) - f(w)| ≤ |v - w|`,
`|f| ≤ r/4`, `P ∘ ι = id`, `P ∘ ι' = 0`, and `D = B_{r/2}(0)`.  If `θ = 1` `μ`-a.e. on
`B̄_r(ξ) ⊆ W ⊆ U`, `Hⁿ((spt μ ∩ W) \ M) = 0` and `Hⁿ((range Φ \ spt μ) ∩ B̄_r(ξ)) ≤ a`, then
`μ(Φ(D)) < ∞`, and `Z = D ∩ Φ⁻¹(Mᶜ ∪ {θ ≠ 1})` is a Borel set with `Hⁿ(Φ(Z)) ≤ a` and
`∫_{Φ(D)} h dμ = ∫_{Φ(D \ Z)} h dHⁿ`.  As `P(Φ(v) - ξ) = v`, `Φ` is a continuous injection, so
`Φ(D)` is Borel; `Φ(D) ⊆ B̄_r(ξ)` by the triangle inequality, so `μ(Φ(D)) ≤ μ(B̄_r(ξ)) < ∞` by
local integrability of `θ`.  As `θ > 0` on `M`, `θ = 1` `Hⁿ`-a.e. on `M ∩ B̄_r(ξ)`; hence
`μ⌞Φ(D) = θ Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞Φ(D \ Z)`, and `Φ(Z)` lies in the union of
`(range Φ \ spt μ) ∩ B̄_r(ξ)`, `(spt μ ∩ W) \ M` and the null set `M ∩ B̄_r(ξ) ∩ {θ ≠ 1}`. -/
theorem Submission.dorag_tes_gt_graph_measure_exceptional_set : ∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (r a : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), W ⊆ U → 0 < r → closedBall ξ r ⊆ W → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → R.measure ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) ≠ ∞ ∧ ∃ Z : Set (Euclid n), MeasurableSet Z ∧ μHE[n] ((fun v => ξ + ι v + ι' (f v)) '' Z) ≤ ENNReal.ofReal a ∧ ∀ h : Euclid (n + k) → ℝ≥0∞, Measurable h → ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h x ∂R.measure = ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' (ball (0 : Euclid n) (r / 2) \ Z), h x ∂μHE[n] := by
  intro n k U W R ξ r a ι ι' P f hWU _ hBW hPι hPι' hf hfr H1 H2 H3
  set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v) with hΦ
  set D : Set (Euclid n) := ball 0 (r / 2)
  have hμ : R.measure = (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞) :=
    rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  -- `Φ` is continuous and injective (`P (Φ v - ξ) = v`), so `Φ '' D` is Borel.
  have hfc : Continuous f :=
    (LipschitzWith.mk_one fun v w => by simpa only [dist_eq_norm] using hf v w).continuous
  have hΦc : Continuous Φ := (continuous_const.add ι.continuous).add (ι'.continuous.comp hfc)
  have hΦξ : ∀ v, Φ v - ξ = ι v + ι' (f v) := fun v => by
    simp only [hΦ]
    abel
  have hPΦ : ∀ v, P (Φ v - ξ) = v := fun v => by rw [hΦξ, map_add, hPι, hPι', add_zero]
  have hΦD : MeasurableSet (Φ '' D) :=
    measurableSet_ball.image_of_continuousOn_injOn hΦc.continuousOn
      fun v _ w _ hvw => by rw [← hPΦ v, ← hPΦ w, hvw]
  -- `Φ` maps `D` into `closedBall ξ r`.
  have hΦB : ∀ v ∈ D, Φ v ∈ closedBall ξ r := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm, hΦξ]
    have hv' : ‖v‖ < r / 2 := mem_ball_zero_iff.1 hv
    calc ‖ι v + ι' (f v)‖ ≤ ‖ι v‖ + ‖ι' (f v)‖ := norm_add_le _ _
      _ = ‖v‖ + ‖f v‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
      _ ≤ r := by linarith [hfr v]
  -- `θ = 1` holds `Hⁿ`-a.e. on `M ∩ closedBall ξ r`, as `θ ≠ 0` on `M`.
  have H1' : ∀ᵐ x ∂μHE[n], x ∈ R.carrier → x ∈ closedBall ξ r → R.mult x = 1 := by
    rw [hμ, ae_withDensity_iff hθ, ae_restrict_iff' R.measurableSet_carrier] at H1
    filter_upwards [H1] with x hx hxM
    exact hx hxM (Nat.cast_ne_zero.2 (R.mult_pos x hxM).ne')
  set N := {x | x ∈ R.carrier ∧ x ∈ closedBall ξ r ∧ R.mult x ≠ 1}
  have hN : μHE[n] N = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 H1')
    intro x hx
    simp only [mem_ofPred_eq, not_imp]
    exact hx
  set Z := D ∩ Φ ⁻¹' (R.carrierᶜ ∪ {x | R.mult x ≠ 1})
  refine ⟨?_, Z, ?_, ?_, ?_⟩
  · -- `μ (Φ '' D) ≤ μ (closedBall ξ r) < ∞`.
    have hB : R.measure (closedBall ξ r) ≠ ∞ := by
      rw [hμ, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact R.locallyIntegrable_mult _ (isCompact_closedBall ξ r) (hBW.trans hWU)
    refine ne_top_of_le_ne_top hB (measure_mono ?_)
    rintro _ ⟨v, hv, rfl⟩
    exact hΦB v hv
  · have hne : MeasurableSet {x | R.mult x ≠ 1} :=
      R.measurable_mult (measurableSet_singleton 1).compl
    exact measurableSet_ball.inter (hΦc.measurable (R.measurableSet_carrier.compl.union hne))
  · -- `Φ '' Z` lies in the off-support part, `(spt μ ∩ W) \ M`, or `N`.
    have hsub : Φ '' Z ⊆ (range Φ \ R.measure.support) ∩ closedBall ξ r ∪
        ((R.measure.support ∩ W) \ R.carrier ∪ N) := by
      rintro _ ⟨v, ⟨hvD, hvZ⟩, rfl⟩
      have hxB := hΦB v hvD
      by_cases hxM : Φ v ∈ R.carrier
      · have h1 : R.mult (Φ v) ≠ 1 := by
          rcases hvZ with h | h
          · exact absurd hxM h
          · exact h
        exact Or.inr (Or.inr ⟨hxM, hxB, h1⟩)
      · by_cases hxs : Φ v ∈ R.measure.support
        · exact Or.inr (Or.inl ⟨⟨hxs, hBW hxB⟩, hxM⟩)
        · exact Or.inl ⟨⟨mem_range_self v, hxs⟩, hxB⟩
    calc μHE[n] (Φ '' Z)
        ≤ μHE[n] ((range Φ \ R.measure.support) ∩ closedBall ξ r ∪
          ((R.measure.support ∩ W) \ R.carrier ∪ N)) := measure_mono hsub
      _ ≤ μHE[n] ((range Φ \ R.measure.support) ∩ closedBall ξ r) +
          μHE[n] ((R.measure.support ∩ W) \ R.carrier ∪ N) := measure_union_le _ _
      _ = μHE[n] ((range Φ \ R.measure.support) ∩ closedBall ξ r) := by
        rw [measure_union_null H2 hN, add_zero]
      _ ≤ ENNReal.ofReal a := H3
  · -- `μ⌞Φ(D) = θ Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞Φ(D \ Z)`.
    have hae : (Φ '' D ∩ R.carrier : Set (Euclid (n + k))) =ᵐ[μHE[n]] Φ '' (D \ Z) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [H1'] with x hx
      constructor
      · rintro ⟨⟨v, hvD, rfl⟩, hxM⟩
        refine ⟨v, ⟨hvD, fun hvZ => ?_⟩, rfl⟩
        rcases hvZ.2 with h | h
        · exact h hxM
        · exact h (hx hxM (hΦB v hvD))
      · rintro ⟨v, ⟨hvD, hvZ⟩, rfl⟩
        refine ⟨⟨v, hvD, rfl⟩, ?_⟩
        by_contra hxM
        exact hvZ ⟨hvD, Or.inl hxM⟩
    have hmeas : R.measure.restrict (Φ '' D) = μHE[n].restrict (Φ '' (D \ Z)) := by
      rw [hμ, restrict_withDensity hΦD, Measure.restrict_restrict hΦD]
      calc (μHE[n].restrict (Φ '' D ∩ R.carrier)).withDensity (fun x => (R.mult x : ℝ≥0∞))
          = (μHE[n].restrict (Φ '' D ∩ R.carrier)).withDensity 1 := by
            refine withDensity_congr_ae ?_
            rw [Filter.EventuallyEq, ae_restrict_iff' (hΦD.inter R.measurableSet_carrier)]
            filter_upwards [H1'] with x hx hxs
            obtain ⟨⟨v, hvD, rfl⟩, hxM⟩ := hxs
            simp [hx hxM (hΦB v hvD)]
        _ = μHE[n].restrict (Φ '' D ∩ R.carrier) := withDensity_one
        _ = μHE[n].restrict (Φ '' (D \ Z)) := Measure.restrict_congr_set hae
    intro h _
    rw [hmeas]
/-- Bounded transfer from a two-sided lower-integral comparison: let `Z` be measurable with
`m(Z) ≤ a`, `m(D), ν(S) < ∞`, `c ≥ 0` and `s ≥ 0` integrable on `D`, and suppose that
`∫⁻_{D∖Z} h dm ≤ ∫⁻_S h∘φ dν ≤ ∫⁻_{D∖Z} (1 + c s) h dm` for every measurable `h ≥ 0`.  Then
(a) `∫⁻_D g dm ≤ ∫⁻_S g∘φ dν + G a` for measurable `0 ≤ g ≤ G`, and
(b) `|∫_D g dm - ∫_S g∘φ dν| ≤ G (a + c ∫_D s dm)` for measurable `|g| ≤ G`.
For (a), the part of `∫⁻_D g` over `D ∩ Z` is at most `G m(Z) ≤ G a`, and the part over `D ∖ Z`
is at most `∫⁻_S g∘φ`.  For (b), bounded measurable functions are integrable on `D` and `S`, so
for measurable `0 ≤ h ≤ G` the comparison passes to Bochner integrals and gives
`-G a ≤ ∫_S h∘φ - ∫_D h ≤ G c ∫_D s`; this is applied to `g⁺` and `g⁻`, and `g = g⁺ - g⁻`. -/
theorem Submission.dorag_tes_gt_bounded_transfer_of_lintegral_bounds : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] (m : Measure X) (ν : Measure Y) (D Z : Set X) (S : Set Y) (φ : Y → X) (s : X → ℝ) (a c : ℝ), MeasurableSet D → MeasurableSet Z → Measurable φ → m D ≠ ∞ → ν S ≠ ∞ → m Z ≤ ENNReal.ofReal a → 0 ≤ a → 0 ≤ c → (∀ v, 0 ≤ s v) → IntegrableOn s D m → (∀ h : X → ℝ≥0∞, Measurable h → (∫⁻ v in D \ Z, h v ∂m) ≤ (∫⁻ y in S, h (φ y) ∂ν) ∧ (∫⁻ y in S, h (φ y) ∂ν) ≤ ∫⁻ v in D \ Z, ENNReal.ofReal (1 + c * s v) * h v ∂m) → (∀ (g : X → ℝ) (G : ℝ), Measurable g → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ G) → (∫⁻ v in D, ENNReal.ofReal (g v) ∂m) ≤ (∫⁻ y in S, ENNReal.ofReal (g (φ y)) ∂ν) + ENNReal.ofReal (G * a)) ∧ ∀ (g : X → ℝ) (G : ℝ), Measurable g → (∀ v, |g v| ≤ G) → |(∫ v in D, g v ∂m) - (∫ y in S, g (φ y) ∂ν)| ≤ G * (a + c * (∫ v in D, s v ∂m)) := by
  intro X Y _ _ _ m ν D Z S φ s a c hD hZ hφ hmD hνS hmZ ha hc hs hsD hcmp
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hmDZ : m (D ∩ Z) ≤ ENNReal.ofReal a := (measure_mono inter_subset_right).trans hmZ
  refine ⟨fun g G hg hg0 hgG => ?_, fun g G hg hgG => ?_⟩
  · have hG0 : 0 ≤ G := (hg0 x₀).trans (hgG x₀)
    have h1 : ∫⁻ v in D ∩ Z, ENNReal.ofReal (g v) ∂m ≤ ENNReal.ofReal (G * a) :=
      calc ∫⁻ v in D ∩ Z, ENNReal.ofReal (g v) ∂m ≤ ∫⁻ v in D ∩ Z, ENNReal.ofReal G ∂m :=
            lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hgG v)
        _ = ENNReal.ofReal G * m (D ∩ Z) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal G * ENNReal.ofReal a := by gcongr
        _ = ENNReal.ofReal (G * a) := (ENNReal.ofReal_mul hG0).symm
    have h2 := (hcmp (fun v => ENNReal.ofReal (g v)) (ENNReal.measurable_ofReal.comp hg)).1
    calc ∫⁻ v in D, ENNReal.ofReal (g v) ∂m
        = ∫⁻ v in D ∩ Z, ENNReal.ofReal (g v) ∂m + ∫⁻ v in D \ Z, ENNReal.ofReal (g v) ∂m :=
          (lintegral_inter_add_sdiff _ D hZ).symm
      _ ≤ ENNReal.ofReal (G * a) + ∫⁻ y in S, ENNReal.ofReal (g (φ y)) ∂ν := add_le_add h1 h2
      _ = _ := add_comm _ _
  · have hDZ : m.real (D ∩ Z) ≤ a := ENNReal.toReal_le_of_le_ofReal ha hmDZ
    have hsDZ : IntegrableOn s (D \ Z) m := hsD.mono_set Set.sdiff_subset
    have hint : ∀ (u : X → ℝ) (G : ℝ), Measurable u → (∀ v, ‖u v‖ ≤ G) →
        IntegrableOn u D m ∧ IntegrableOn (fun y => u (φ y)) S ν := fun u G hu huG =>
      ⟨Measure.integrableOn_of_bounded hmD hu.aestronglyMeasurable (ae_of_all _ huG),
        Measure.integrableOn_of_bounded hνS (hu.comp hφ).aestronglyMeasurable
          (ae_of_all _ fun y => huG (φ y))⟩
    -- the key estimate `-G a ≤ ∫_S h∘φ - ∫_D h ≤ G c ∫_D s` for measurable `0 ≤ h ≤ G`
    have key : ∀ (h : X → ℝ) (G : ℝ), Measurable h → (∀ v, 0 ≤ h v) → (∀ v, h v ≤ G) →
        -(G * a) ≤ (∫ y in S, h (φ y) ∂ν) - ∫ v in D, h v ∂m ∧
          (∫ y in S, h (φ y) ∂ν) - ∫ v in D, h v ∂m ≤ G * (c * ∫ v in D, s v ∂m) := by
      intro h G hh hh0 hhG
      have hG0 : 0 ≤ G := (hh0 x₀).trans (hhG x₀)
      have hnorm : ∀ v, ‖h v‖ ≤ G := fun v => (Real.norm_of_nonneg (hh0 v)).trans_le (hhG v)
      obtain ⟨hhD, hhS⟩ := hint h G hh hnorm
      have hhDZ : IntegrableOn h (D \ Z) m := hhD.mono_set Set.sdiff_subset
      have hshDZ : IntegrableOn (fun v => s v * h v) (D \ Z) m := by
        refine Integrable.mono' (hsDZ.const_mul G)
          (hsDZ.aestronglyMeasurable.mul hh.aestronglyMeasurable) (ae_of_all _ fun v => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (hs v) (hh0 v)), mul_comm G]
        exact mul_le_mul_of_nonneg_left (hhG v) (hs v)
      have hwDZ : IntegrableOn (fun v => (1 + c * s v) * h v) (D \ Z) m := by
        have e : (fun v => (1 + c * s v) * h v) = fun v => h v + c * (s v * h v) := by
          funext v; ring
        rw [e]
        exact hhDZ.add (hshDZ.const_mul c)
      obtain ⟨L1, L2⟩ := hcmp (fun v => ENNReal.ofReal (h v)) (ENNReal.measurable_ofReal.comp hh)
      have L2' : ∫⁻ y in S, ENNReal.ofReal (h (φ y)) ∂ν ≤
          ∫⁻ v in D \ Z, ENNReal.ofReal ((1 + c * s v) * h v) ∂m := by
        refine L2.trans (le_of_eq (lintegral_congr fun v => ?_))
        exact (ENNReal.ofReal_mul (add_nonneg zero_le_one (mul_nonneg hc (hs v)))).symm
      have eDZ : ∫ v in D \ Z, h v ∂m = (∫⁻ v in D \ Z, ENNReal.ofReal (h v) ∂m).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0) hhDZ.aestronglyMeasurable
      have eS : ∫ y in S, h (φ y) ∂ν = (∫⁻ y in S, ENNReal.ofReal (h (φ y)) ∂ν).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hh0 (φ y))
          hhS.aestronglyMeasurable
      have eW : ∫ v in D \ Z, (1 + c * s v) * h v ∂m =
          (∫⁻ v in D \ Z, ENNReal.ofReal ((1 + c * s v) * h v) ∂m).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun v => mul_nonneg (add_nonneg zero_le_one (mul_nonneg hc (hs v))) (hh0 v))
          hwDZ.aestronglyMeasurable
      have B1 : ∫ v in D \ Z, h v ∂m ≤ ∫ y in S, h (φ y) ∂ν := by
        rw [eDZ, eS]
        exact ENNReal.toReal_mono hhS.lintegral_lt_top.ne L1
      have B2 : ∫ y in S, h (φ y) ∂ν ≤ ∫ v in D \ Z, (1 + c * s v) * h v ∂m := by
        rw [eS, eW]
        exact ENNReal.toReal_mono hwDZ.lintegral_lt_top.ne L2'
      have eD : ∫ v in D, h v ∂m = (∫ v in D ∩ Z, h v ∂m) + ∫ v in D \ Z, h v ∂m :=
        (integral_inter_add_sdiff hZ hhD).symm
      have I0 : 0 ≤ ∫ v in D ∩ Z, h v ∂m := integral_nonneg hh0
      have I1 : ∫ v in D ∩ Z, h v ∂m ≤ G * a := by
        have hn : ‖∫ v in D ∩ Z, h v ∂m‖ ≤ G * m.real (D ∩ Z) :=
          norm_setIntegral_le_of_norm_le_const
            ((measure_mono inter_subset_left).trans_lt hmD.lt_top) fun v _ => hnorm v
        exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hn).trans
          (mul_le_mul_of_nonneg_left hDZ hG0))
      have eW' : ∫ v in D \ Z, (1 + c * s v) * h v ∂m =
          (∫ v in D \ Z, h v ∂m) + c * ∫ v in D \ Z, s v * h v ∂m := by
        have e : ∀ v, (1 + c * s v) * h v = h v + c * (s v * h v) := fun v => by ring
        simp_rw [e]
        rw [integral_add hhDZ (hshDZ.const_mul c), integral_const_mul]
      have I2 : ∫ v in D \ Z, s v * h v ∂m ≤ G * ∫ v in D, s v ∂m :=
        calc ∫ v in D \ Z, s v * h v ∂m ≤ ∫ v in D \ Z, G * s v ∂m :=
              setIntegral_mono hshDZ (hsDZ.const_mul G) fun v => by
                rw [mul_comm G]
                exact mul_le_mul_of_nonneg_left (hhG v) (hs v)
          _ = G * ∫ v in D \ Z, s v ∂m := integral_const_mul G _
          _ ≤ G * ∫ v in D, s v ∂m :=
              mul_le_mul_of_nonneg_left (setIntegral_mono_set hsD (ae_of_all _ hs)
                (LE.le.eventuallySubset Set.sdiff_subset)) hG0
      have I3 : c * ∫ v in D \ Z, s v * h v ∂m ≤ c * (G * ∫ v in D, s v ∂m) :=
        mul_le_mul_of_nonneg_left I2 hc
      constructor
      · linarith
      · linarith
    have hG0 : 0 ≤ G := (abs_nonneg _).trans (hgG x₀)
    have hp : ∀ v, max (g v) 0 ≤ G := fun v => max_le ((le_abs_self _).trans (hgG v)) hG0
    have hn : ∀ v, max (-g v) 0 ≤ G := fun v => max_le ((neg_le_abs _).trans (hgG v)) hG0
    have hpm : Measurable fun v => max (g v) 0 := hg.max measurable_const
    have hnm : Measurable fun v => max (-g v) 0 := hg.neg.max measurable_const
    obtain ⟨hpD, hpS⟩ := hint _ G hpm fun v =>
      (Real.norm_of_nonneg (le_max_right _ _)).trans_le (hp v)
    obtain ⟨hnD, hnS⟩ := hint _ G hnm fun v =>
      (Real.norm_of_nonneg (le_max_right _ _)).trans_le (hn v)
    obtain ⟨k1, k2⟩ := key _ G hpm (fun v => le_max_right _ _) hp
    obtain ⟨k3, k4⟩ := key _ G hnm (fun v => le_max_right _ _) hn
    have eD : ∫ v in D, g v ∂m = (∫ v in D, max (g v) 0 ∂m) - ∫ v in D, max (-g v) 0 ∂m := by
      rw [← integral_sub hpD hnD]
      exact integral_congr_ae (ae_of_all _ fun v => (max_zero_sub_max_neg_zero_eq_self (g v)).symm)
    have eS : ∫ y in S, g (φ y) ∂ν =
        (∫ y in S, max (g (φ y)) 0 ∂ν) - ∫ y in S, max (-g (φ y)) 0 ∂ν := by
      rw [← integral_sub hpS hnS]
      exact integral_congr_ae
        (ae_of_all _ fun y => (max_zero_sub_max_neg_zero_eq_self (g (φ y))).symm)
    rw [eD, eS, abs_le]
    constructor
    · linarith
    · linarith
/-- Frame bounds for the affine graph plane (Simon Ch. 5, proof of Theorem 4.5).  Let
`L = ι + ι' ∘ Λ`, `S = range L` and `τ = ξ + ι' c`, where `ι`, `ι'` are orthogonal isometric
frames with `range ι ⊆ T`, `dim T = n`.  Then (a) `dim S = n`; (b) at `ξ + ι v + ι' w`, the
distance to `τ + S` is at most `‖w - c - Λ v‖`, and `‖v‖ ≤ ‖ξ + ι v + ι' w - τ‖`; (c) for every
`x`, `dist(x - τ, S) ≤ dist(x - ξ, T) + ‖c‖ + ‖Λ‖ ‖x - τ‖`, since `range ι = T`,
`range ι' = Tᗮ` and so `x = ξ + ι v + ι' w` with `‖w‖ = dist(x - ξ, T)`. -/
theorem Submission.dorag_tes_gah_plane_frame_bounds : ∀ (n k : ℕ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (Λ : Euclid n →L[ℝ] Euclid k) (ξ : Euclid (n + k)) (c : Euclid k), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → Module.finrank ℝ (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)) = n ∧ (∀ (v : Euclid n) (w : Euclid k), ‖(ξ + ι v + ι' w - (ξ + ι' c)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)).starProjection (ξ + ι v + ι' w - (ξ + ι' c))‖ ≤ ‖w - c - Λ v‖ ∧ ‖v‖ ≤ ‖ξ + ι v + ι' w - (ξ + ι' c)‖) ∧ ∀ x : Euclid (n + k), ‖(x - (ξ + ι' c)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)).starProjection (x - (ξ + ι' c))‖ ≤ ‖(x - ξ) - T.starProjection (x - ξ)‖ + ‖c‖ + ‖Λ‖ * ‖x - (ξ + ι' c)‖ := by
  intro n k T ι ι' Λ ξ c hT horth hιT
  set L : Euclid n →ₗ[ℝ] Euclid (n + k) := ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap
  have hLv : ∀ v, L v = ι v + ι' (Λ v) := fun v => rfl
  -- Step 1 (Pythagoras): `‖ι v + ι' u‖² = ‖v‖² + ‖u‖²`
  have hpy : ∀ (v : Euclid n) (u : Euclid k), ‖ι v + ι' u‖ ^ 2 = ‖v‖ ^ 2 + ‖u‖ ^ 2 := by
    intro v u
    rw [norm_add_sq_real, horth v u, ι.norm_map, ι'.norm_map]
    ring
  -- Step 2 (a): `L` is injective, so `dim S = n`
  have ha : Module.finrank ℝ (LinearMap.range L) = n := by
    have hinj : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have h := hpy v (Λ v)
      rw [← hLv, hv, norm_zero] at h
      have h0 : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖Λ v‖]
      simpa using h0
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  -- Step 3 (nearest point): `‖y - p_S y‖ ≤ ‖y - s‖` for `s ∈ S`
  have hnear : ∀ y s : Euclid (n + k), s ∈ LinearMap.range L →
      ‖y - (LinearMap.range L).starProjection y‖ ≤ ‖y - s‖ := by
    intro y s hs
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ (⟨s, hs⟩ : LinearMap.range L)
  -- Step 4 (b)
  have hb : ∀ (v : Euclid n) (w : Euclid k),
      ‖(ξ + ι v + ι' w - (ξ + ι' c)) - (LinearMap.range L).starProjection (ξ + ι v + ι' w - (ξ + ι' c))‖
        ≤ ‖w - c - Λ v‖ ∧ ‖v‖ ≤ ‖ξ + ι v + ι' w - (ξ + ι' c)‖ := by
    intro v w
    have hy : ξ + ι v + ι' w - (ξ + ι' c) = ι v + ι' (w - c) := by
      rw [map_sub]; abel
    rw [hy]
    refine ⟨?_, ?_⟩
    · have h1 : ι v + ι' (w - c) - L v = ι' (w - c - Λ v) := by
        rw [hLv, map_sub ι' (w - c) (Λ v)]; abel
      calc _ ≤ ‖ι v + ι' (w - c) - L v‖ := hnear _ _ (LinearMap.mem_range_self L v)
        _ = ‖w - c - Λ v‖ := by rw [h1, ι'.norm_map]
    · have h2 := hpy v (w - c)
      have h3 : ‖v‖ ^ 2 ≤ ‖ι v + ι' (w - c)‖ ^ 2 := by nlinarith [sq_nonneg ‖w - c‖]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3
  -- Step 5: `range ι = T`
  have hrι : LinearMap.range ι.toLinearMap = T := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v, rfl⟩
      exact hιT v
    · rw [LinearMap.finrank_range_of_inj ι.injective, finrank_euclideanSpace_fin, hT]
  -- Step 6: `range ι' = Tᗮ`
  have hrι' : LinearMap.range ι'.toLinearMap = Tᗮ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [← hrι] at hu
      obtain ⟨v, rfl⟩ := hu
      exact horth v w
    · have h := Submodule.finrank_add_finrank_orthogonal T
      rw [hT, finrank_euclideanSpace_fin] at h
      rw [LinearMap.finrank_range_of_inj ι'.injective, finrank_euclideanSpace_fin]
      omega
  -- Step 7 (c)
  refine ⟨ha, hb, ?_⟩
  intro x
  obtain ⟨v, hv⟩ : T.starProjection (x - ξ) ∈ LinearMap.range ι.toLinearMap := by
    rw [hrι]; exact T.starProjection_apply_mem _
  obtain ⟨w, hw⟩ : (x - ξ) - T.starProjection (x - ξ) ∈ LinearMap.range ι'.toLinearMap := by
    rw [hrι']; exact Submodule.sub_starProjection_mem_orthogonal _
  simp only [LinearIsometry.coe_toLinearMap] at hv hw
  have hx : ξ + ι v + ι' w = x := by
    rw [hv, hw]; abel
  have hwn : ‖w‖ = ‖(x - ξ) - T.starProjection (x - ξ)‖ := by
    rw [← hw, ι'.norm_map]
  obtain ⟨hb1, hb2⟩ := hb v w
  rw [hx] at hb1 hb2
  rw [← hwn]
  calc _ ≤ ‖w - c - Λ v‖ := hb1
    _ ≤ ‖w - c‖ + ‖Λ v‖ := norm_sub_le _ _
    _ ≤ ‖w‖ + ‖c‖ + ‖Λ‖ * ‖v‖ := by gcongr; exacts [norm_sub_le _ _, Λ.le_opNorm v]
    _ ≤ ‖w‖ + ‖c‖ + ‖Λ‖ * ‖x - (ξ + ι' c)‖ := by gcongr
/-- Where the multiplicity is `1` `μ`-a.e., `μ = θ Hⁿ⌞M` is dominated by `Hⁿ` (Simon Ch. 5, proof of
Theorem 4.5): if `θ = 1` `μ`-a.e. on the measurable set `B`, then `μ⌞B ≤ Hⁿ⌞B`, hence
`∫⁻_A h dμ ≤ ∫⁻_A h dHⁿ` for every `A ⊆ B` and every `h ≥ 0`.  As `θ ≥ 1` on `M`, the exceptional
set `{x ∈ M ∩ B : θ(x) ≠ 1}` is `Hⁿ`-null, so `μ⌞B = Hⁿ⌞(B ∩ M)`. -/
theorem Submission.dorag_tes_gah_mult_one_le_hausdorff : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (B : Set (Euclid P)), MeasurableSet B → (∀ᵐ x ∂R.measure, x ∈ B → R.mult x = 1) → R.measure.restrict B ≤ (μHE[n] : Measure (Euclid P)).restrict B ∧ ∀ (A : Set (Euclid P)) (h : Euclid P → ℝ≥0∞), A ⊆ B → (∫⁻ x in A, h x ∂R.measure) ≤ ∫⁻ x in A, h x ∂μHE[n] := by
  intro P n U R B hB hmult
  -- Step 1: `θ = R.mult` is measurable and `μ⌞B = ((Hⁿ⌞M)⌞B).withDensity θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hμB : R.measure.restrict B =
      ((μHE[n].restrict R.carrier).restrict B).withDensity fun x => (R.mult x : ℝ≥0∞) :=
    restrict_withDensity hB _
  -- Step 2: for `Hⁿ⌞M`-a.e. `x`, `θ(x) ≠ 0 → x ∈ B → θ(x) = 1`
  have h2 : ∀ᵐ x ∂μHE[n].restrict R.carrier,
      (R.mult x : ℝ≥0∞) ≠ 0 → x ∈ B → R.mult x = 1 :=
    (ae_withDensity_iff hθ).1 hmult
  -- Step 3: `θ = 1` a.e. for `(Hⁿ⌞M)⌞B`, since `θ ≥ 1` on `M`
  have h3 : (fun x => (R.mult x : ℝ≥0∞)) =ᵐ[(μHE[n].restrict R.carrier).restrict B] 1 := by
    filter_upwards [ae_restrict_of_ae h2,
      ae_restrict_of_ae (ae_restrict_mem R.measurableSet_carrier), ae_restrict_mem hB]
      with x hx hxM hxB
    rw [hx (Nat.cast_ne_zero.2 (R.mult_pos x hxM).ne') hxB, Pi.one_apply, Nat.cast_one]
  -- Step 4: `μ⌞B = (Hⁿ⌞M)⌞B = Hⁿ⌞(B ∩ M) ≤ Hⁿ⌞B`
  have hle : R.measure.restrict B ≤ (μHE[n] : Measure (Euclid P)).restrict B := by
    rw [hμB, withDensity_congr_ae h3, withDensity_one, Measure.restrict_restrict hB]
    exact Measure.restrict_mono inter_subset_left le_rfl
  refine ⟨hle, fun A h hAB => ?_⟩
  -- Step 5: restrict to `A ⊆ B` and compare lower integrals
  have hA : R.measure.restrict A ≤ (μHE[n] : Measure (Euclid P)).restrict A := by
    simpa only [Measure.restrict_restrict_of_subset hAB] using Measure.restrict_mono_measure hle A
  exact lintegral_mono' hA le_rfl
/-- Area-weight bound for `1`-Lipschitz graphs, closed to open parameter ball: if `n ≥ 1` and
`|f(v) - f(w)| ≤ |v - w|`, then `∫⁻_{B̄ₜ(0)} (1 + 2ⁿ Σᵢ |Df(v)eᵢ|²) G ≤ (1 + n2ⁿ) ∫⁻_{Bₜ(0)} G`
for every `G ≥ 0` and `t`.  As `f` is `1`-Lipschitz, `‖Df(v)‖ ≤ 1` (also where `Df(v) = 0`), so
`|Df(v)eᵢ| ≤ 1`, `Σᵢ |Df(v)eᵢ|² ≤ n` and the weight is at most the finite constant `1 + n2ⁿ`,
which is pulled out of the integral.  For `n ≥ 1` the sphere is Lebesgue-null, so
`closedBall 0 t =ᵐ ball 0 t` and the two lower integrals of `G` agree. -/
theorem Submission.dorag_tes_gah_lipschitz_weight_ball_le : ∀ (n k : ℕ), 0 < n → ∀ (f : Euclid n → Euclid k), (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → ∀ (G : Euclid n → ℝ≥0∞) (t : ℝ), (∫⁻ v in closedBall (0 : Euclid n) t, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * G v) ≤ ENNReal.ofReal (1 + n * 2 ^ n) * (∫⁻ v in ball (0 : Euclid n) t, G v) := by
  intro n k hn f hf G t
  have hlip : LipschitzWith 1 f := LipschitzWith.mk_one fun v w => by
    simpa only [dist_eq_norm] using hf v w
  have hw : ∀ v, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n,
      ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal (1 + n * 2 ^ n) := by
    intro v
    have hD : ‖fderiv ℝ f v‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hlip
    have hsum : ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ n := by
      calc ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
          ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => pow_le_one₀ (norm_nonneg _) ?_
            calc ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖
                ≤ ‖fderiv ℝ f v‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ := (fderiv ℝ f v).le_opNorm _
              _ ≤ 1 := by simpa using hD
        _ = n := by simp
    have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
    have := mul_le_mul_of_nonneg_left hsum h2
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hae : closedBall (0 : Euclid n) t =ᵐ[volume] ball (0 : Euclid n) t := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [closedBall_sdiff_ball]
      exact Measure.addHaar_sphere volume 0 t
    · rw [Set.sdiff_eq_empty.2 ball_subset_closedBall]
      exact measure_empty
  calc (∫⁻ v in closedBall (0 : Euclid n) t, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n,
        ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * G v)
      ≤ ∫⁻ v in closedBall (0 : Euclid n) t, ENNReal.ofReal (1 + n * 2 ^ n) * G v :=
        lintegral_mono fun v => mul_le_mul_left (hw v) (G v)
    _ = ENNReal.ofReal (1 + n * 2 ^ n) * ∫⁻ v in closedBall (0 : Euclid n) t, G v :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (1 + n * 2 ^ n) * ∫⁻ v in ball (0 : Euclid n) t, G v := by
        rw [setLIntegral_congr hae]
/-- Product bound used for the graph area Jacobian: if `0 ≤ λᵢ ≤ 1` for `i < m`, then
`1 ≤ Πᵢ (1 + λᵢ) ≤ 1 + 2ᵐ Σᵢ λᵢ`.  Induction on `m`, splitting off the last index:
`Π = P'(1 + μ)` and `Σ = S' + μ` with `0 ≤ μ ≤ 1`, `S' ≥ 0` and `1 ≤ P' ≤ 1 + 2ᵐS'`.  Then
`P'(1 + μ) - 1 = (P' - 1)(1 + μ) + μ ≥ 0` and
`P'(1 + μ) ≤ (1 + 2ᵐS')(1 + μ) ≤ 1 + 2ᵐ⁺¹S' + μ ≤ 1 + 2ᵐ⁺¹(S' + μ)`. -/
theorem Submission.dorag_tes_ga_prod_one_add_bounds : ∀ (m : ℕ) (lam : Fin m → ℝ), (∀ i, 0 ≤ lam i) → (∀ i, lam i ≤ 1) → 1 ≤ ∏ i, (1 + lam i) ∧ ∏ i, (1 + lam i) ≤ 1 + 2 ^ m * ∑ i, lam i := by
  intro m
  induction m with
  | zero => intro lam _ _; simp
  | succ m ih =>
    intro lam h0 h1
    obtain ⟨hP1, hP2⟩ := ih (fun i => lam i.castSucc) (fun i => h0 _) (fun i => h1 _)
    have hS : 0 ≤ ∑ i : Fin m, lam i.castSucc := Finset.sum_nonneg fun i _ => h0 _
    have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hμ0 := h0 (Fin.last m)
    have hμ1 := h1 (Fin.last m)
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, pow_succ]
    constructor
    · linarith [mul_nonneg (sub_nonneg.2 hP1) (by linarith : (0 : ℝ) ≤ 1 + lam (Fin.last m))]
    · linarith [mul_nonneg (sub_nonneg.2 hP2) (by linarith : (0 : ℝ) ≤ 1 + lam (Fin.last m)),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ m) hS) (sub_nonneg.2 hμ1),
        mul_nonneg hμ0 (by linarith : (0 : ℝ) ≤ 2 ^ m * 2 - 1)]
/-- **Gram operator of a linear graph** (Simon Ch. 5, after (14): `DᵢF · DⱼF = δᵢⱼ + Dᵢf · Dⱼf`
for the graph map `F(x) = (x, f(x))`; here `Df(x)` is an arbitrary `B` and the splitting
`ℝⁿ⁺ᵏ = ℝⁿ × ℝᵏ` is given by isometries `ι`, `ι'` with orthogonal ranges).  For `L = ι + ι' ∘ B`,
`L* L = id + B* B`: `⟪w, L* L u⟫ = ⟪L w, L u⟫` expands into four inner products; `ι`, `ι'`
preserve the two diagonal ones and orthogonality kills the two cross terms, leaving
`⟪w, u⟫ + ⟪B w, B u⟫ = ⟪w, (id + B* B) u⟫`. -/
theorem Submission.dorag_tes_ga_graph_linear_gram_identity : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (B : Euclid n →L[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L B).adjoint ∘L (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L B) = ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B := by
  intro n k ι ι' B h
  -- operators agree if `⟪w, · u⟫` agree for all `u, w`
  ext1 u
  refine ext_inner_left ℝ fun w => ?_
  -- `⟪w, L* L u⟫ = ⟪L w, L u⟫`, `⟪w, B* B u⟫ = ⟪B w, B u⟫`; expand, `ι` and `ι'` are isometric
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, add_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap, inner_add_left,
    inner_add_right, LinearIsometry.inner_map_map]
  -- the cross terms vanish by orthogonality
  rw [h w (B u), inner_eq_zero_symm.mp (h u (B w))]
  ring

/-- Determinant bounds for `id + B* ∘ B` (graph area, steps 6–7).  If `B : ℝⁿ → ℝᵏ` has
`‖B‖ ≤ 1`, then `1 ≤ det (id + B* B) ≤ 1 + 2ⁿ ∑ᵢ |B eᵢ|²`: in an orthonormal eigenbasis of the
symmetric map `B* B` the eigenvalues are `λᵢ = |B bᵢ|² ∈ [0, 1]`, `det (id + B* B) = ∏ (1 + λᵢ)`,
and `∑ λᵢ = trace (B* B) = ∑ |B eᵢ|²`. -/
theorem Submission.dorag_tes_ga_det_id_add_adjoint_comp_bounds : ∀ (n k : ℕ) (B : Euclid n →L[ℝ] Euclid k), ‖B‖ ≤ 1 → 1 ≤ (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B).det ∧ (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B).det ≤ 1 + 2 ^ n * ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  intro n k B hB
  -- Step 1: `P = B* ∘ B` is symmetric, with `⟪x, P y⟫ = ⟪B x, B y⟫`
  let P : Euclid n →ₗ[ℝ] Euclid n := (B.adjoint ∘L B : Euclid n →L[ℝ] Euclid n)
  have hP : ∀ x y, inner ℝ x (P y) = inner ℝ (B x) (B y) := fun x y =>
    ContinuousLinearMap.adjoint_inner_right B x (B y)
  have hsym : P.IsSymmetric := fun x y => by
    rw [real_inner_comm, hP, hP, real_inner_comm]
  -- Step 2: an orthonormal eigenbasis `b` of `P`, with eigenvalues `lam`
  have hn : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  set b := hsym.eigenvectorBasis hn
  set lam := hsym.eigenvalues hn
  have hPb : ∀ i, P (b i) = lam i • b i := fun i => hsym.apply_eigenvectorBasis hn i
  -- Step 3: `lam i = ‖B (b i)‖ ^ 2`, so `0 ≤ lam i ≤ 1`
  have hlam : ∀ i, lam i = ‖B (b i)‖ ^ 2 := fun i => by
    rw [← real_inner_self_eq_norm_sq, ← hP, hPb, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i, one_pow, mul_one]
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => (hlam i).symm ▸ sq_nonneg _
  have hlam1 : ∀ i, lam i ≤ 1 := fun i => by
    have h : ‖B (b i)‖ ≤ 1 :=
      calc ‖B (b i)‖ ≤ ‖B‖ * ‖b i‖ := B.le_opNorm _
        _ = ‖B‖ := by rw [b.orthonormal.1 i, mul_one]
        _ ≤ 1 := hB
    rw [hlam i]
    exact pow_le_one₀ (norm_nonneg _) h
  -- Step 4: the matrix of `id + P` in the basis `b` is `diagonal (1 + lam i)`
  have hdet : (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B).det = ∏ i, (1 + lam i) := by
    have hM : LinearMap.toMatrix b.toBasis b.toBasis
        ((ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B : Euclid n →L[ℝ] Euclid n) :
          Euclid n →ₗ[ℝ] Euclid n) = Matrix.diagonal (fun i => 1 + lam i) := by
      ext i j
      have hj : (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B) (b j) = (1 + lam j) • b j := by
        rw [add_smul, one_smul, ← hPb j]
        rfl
      rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, ContinuousLinearMap.coe_coe, hj,
        map_smul, b.repr_self, Matrix.diagonal_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b.toBasis, hM, Matrix.det_diagonal]
  -- Step 5: `trace P` in the bases `b` and `e` gives `∑ lam i = ∑ ‖B e_i‖ ^ 2`
  have htr : ∑ i, lam i = ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    calc ∑ i, lam i = LinearMap.trace ℝ (Euclid n) P := (hsym.trace_eq_sum_eigenvalues hn).symm
      _ = ∑ i, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) (P (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
        LinearMap.trace_eq_sum_inner P _
      _ = ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
        simp_rw [EuclideanSpace.basisFun_apply, hP, real_inner_self_eq_norm_sq]
  -- Step 6: the sibling `prod_bound` with `m = n`
  rw [hdet, ← htr]
  exact Submission.dorag_tes_ga_prod_one_add_bounds n lam hlam0 hlam1
/-- **Simon Ch. 5, between (14) and (15)** (`1 ≤ J_F ≤ 1 + C|∇f|²`), with the area formula
**Ch. 2, 3.5**: for a `1`-Lipschitz `f : ℝⁿ → ℝᵏ` and the graph map `Φ(v) = ξ + ιv + ι'f(v)`
over the orthogonal isometric embeddings `ι`, `ι'`,
`∫_A h ∘ Φ ≤ ∫_{Φ(A)} h dHⁿ ≤ ∫_A (1 + 2ⁿ Σᵢ |Df(v)eᵢ|²) h ∘ Φ`.  `Φ` is injective and
`2`-Lipschitz, so the injective Lipschitz area formula applies.  Where `f` is differentiable
(Rademacher), `DΦ = ι + ι' ∘ Df` with `‖Df‖ ≤ 1`, `DΦ*DΦ = I + Df*Df`, and
`1 ≤ J_Φ² = det(I + Df*Df) ≤ 1 + 2ⁿ Σᵢ |Df eᵢ|²`; since `J_Φ ≥ 0`, `1 ≤ J_Φ ≤ J_Φ²`. -/
theorem Submission.dorag_tes_lipschitz_graph_area_bounds : ∀ (n k : ℕ), 0 < n → ∀ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (f : Euclid n → Euclid k) (A : Set (Euclid n)) (h : Euclid (n + k) → ℝ≥0∞), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → MeasurableSet A → Measurable h → (∫⁻ v in A, h (ξ + ι v + ι' (f v)) ≤ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' A, h x ∂μHE[n]) ∧ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' A, h x ∂μHE[n] ≤ ∫⁻ v in A, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * h (ξ + ι v + ι' (f v)) := by
  intro n k _hn ι ι' ξ f A h horth hf hA _hh
  set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v) with hΦ
  have hfL : LipschitzWith 1 f :=
    LipschitzWith.of_dist_le_mul fun v w => by simpa [dist_eq_norm] using hf v w
  -- Step 2: `Φ` is `2`-Lipschitz
  have hΦL : LipschitzWith 2 Φ := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hvw : Φ v - Φ w = ι (v - w) + ι' (f v - f w) := by
      simp only [hΦ, map_sub]; abel
    rw [hvw]
    calc ‖ι (v - w) + ι' (f v - f w)‖ ≤ ‖ι (v - w)‖ + ‖ι' (f v - f w)‖ := norm_add_le _ _
      _ = ‖v - w‖ + ‖f v - f w‖ := by rw [ι.norm_map, ι'.norm_map]
      _ ≤ ‖v - w‖ + ‖v - w‖ := by gcongr; exact hf v w
      _ = ((2 : NNReal) : ℝ) * ‖v - w‖ := by push_cast; ring
  -- Step 1: `Φ` is injective, since `ι(v - w) = ι'(f w - f v)` is orthogonal to itself
  have hΦi : Injective Φ := by
    intro v w hvw
    have h1 : ι (v - w) = ι' (f w - f v) := by
      have h2 : ι v + ι' (f v) = ι w + ι' (f w) := by
        simpa only [hΦ, add_assoc, add_right_inj] using hvw
      rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, h2, add_comm (ι w)]
    have h3 : ι (v - w) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ)]
      nth_rewrite 2 [h1]
      exact horth _ _
    exact sub_eq_zero.mp (ι.injective (h3.trans (map_zero ι).symm))
  -- Step 3: the area formula `∫_{Φ(A)} h dHⁿ = ∫_A J_Φ · h ∘ Φ`
  have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hΦL hA
    hΦi.injOn h
  rw [finrank_euclideanSpace_fin] at harea
  -- Steps 4–8: `1 ≤ J_Φ ≤ 1 + 2ⁿ Σᵢ |Df eᵢ|²` wherever `f` is differentiable
  have hJ : ∀ᵐ v ∂(volume : Measure (Euclid n)),
      1 ≤ Poincare.SimonGMT.Chapter02.areaJacobianAt Φ v ∧
        Poincare.SimonGMT.Chapter02.areaJacobianAt Φ v ≤
          1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    filter_upwards [hfL.ae_differentiableAt (μ := volume)] with v hv
    have hB : ‖fderiv ℝ f v‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hfL
    have hD : HasFDerivAt Φ
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ f v) v := by
      have := ((ι.toContinuousLinearMap.hasFDerivAt (x := v)).add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp v hv.hasFDerivAt)).const_add ξ
      convert this using 1
      funext x
      simp [hΦ, add_assoc]
    have hsq := Poincare.SimonGMT.Chapter02.areaJacobianAt_sq_eq_det_adjoint_comp Φ v
    rw [hD.fderiv,
      Submission.dorag_tes_ga_graph_linear_gram_identity n k ι ι' (fderiv ℝ f v) horth] at hsq
    obtain ⟨hlo, hhi⟩ :=
      Submission.dorag_tes_ga_det_id_add_adjoint_comp_bounds n k (fderiv ℝ f v) hB
    have hJ0 := Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg Φ v
    have hJ1 : 1 ≤ Poincare.SimonGMT.Chapter02.areaJacobianAt Φ v := by nlinarith
    exact ⟨hJ1, by nlinarith⟩
  -- Step 9: integrate the a.e. bounds against `h ∘ Φ`
  rw [harea]
  constructor
  · refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae hJ] with v hv
    exact le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr hv.1)
  · refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae hJ] with v hv
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hv.2) zero_le

/-- **Choice of a plane with small tilt and small height** (Simon Ch. 5, proof of 4.5, (1)–(2)).
Write `J(S) = ∫_{B_σ(ξ)} |p_{Q(x)} − p_S|² dμ` (Hilbert–Schmidt norm).  If `J(T) ≤ a`, keep
`S = T`: integrating `|p_T − p_{T₁}|² ≤ 2|p_{Q(x)} − p_T|² + 2|p_{Q(x)} − p_{T₁}|²` over
`B_σ(ξ)`, where `μ(B_σ(ξ)) ≥ M`, gives `|p_T − p_{T₁}|² ≤ 4a/M`, and then
`y − p_T y = (y − p_{T₁} y) + (p_{T₁} − p_T) y` gives the height bound.  Otherwise `S = T₁`,
as `J(T₁) ≤ a < J(T)`. -/
theorem Submission.dorag_tes_plane_reduction : ∀ (N : ℕ) (μ : Measure (Euclid N)) (Q : Euclid N → Submodule ℝ (Euclid N)) (ξ : Euclid N) (σ a M h₁ : ℝ) (T T₁ : Submodule ℝ (Euclid N)), 0 < σ → 0 ≤ a → 0 < M → AEStronglyMeasurable (fun x => (Q x).starProjection) μ → ENNReal.ofReal M ≤ μ (closedBall ξ σ) → ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₁.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal a → (∀ x ∈ μ.support ∩ closedBall ξ σ, ‖(x - ξ) - T₁.starProjection (x - ξ)‖ ≤ h₁) → ∃ S : Submodule ℝ (Euclid N), (S = T ∨ S = T₁) ∧ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal a ∧ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ∧ ∀ x ∈ μ.support ∩ closedBall ξ σ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ h₁ + Real.sqrt (4 * a / M) * σ := by
  intro N μ Q ξ σ a M h₁ T T₁ hσ ha hM hQ hμB hJ₁ hh₁
  obtain ⟨hHS, htri, -, -⟩ := Submission.dorag_tes_projection_algebra N
  -- `τ S x = |p_{Q(x)} − p_S|²`, so that `J(S) = ∫_{B_σ(ξ)} τ S dμ`
  let τ : Submodule ℝ (Euclid N) → Euclid N → ℝ := fun S x =>
    ∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
      S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  change ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T₁ x) ∂μ ≤ ENNReal.ofReal a at hJ₁
  change ∃ S : Submodule ℝ (Euclid N), (S = T ∨ S = T₁) ∧
    ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ S x) ∂μ ≤ ENNReal.ofReal a ∧
    ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ S x) ∂μ ≤
      ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T x) ∂μ ∧
    ∀ x ∈ μ.support ∩ closedBall ξ σ,
      ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ h₁ + Real.sqrt (4 * a / M) * σ
  by_cases hT : ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T x) ∂μ ≤ ENNReal.ofReal a
  swap
  · -- `J(T) > a`: take `S = T₁`
    refine ⟨T₁, Or.inr rfl, hJ₁, hJ₁.trans (not_le.mp hT).le, fun x hx => ?_⟩
    have h₂ : 0 ≤ Real.sqrt (4 * a / M) * σ := mul_nonneg (Real.sqrt_nonneg _) hσ.le
    linarith [hh₁ x hx]
  -- `J(T) ≤ a`: keep `S = T`
  refine ⟨T, Or.inl rfl, hT, le_rfl, ?_⟩
  -- `c₀ = |p_T − p_{T₁}|²`
  set c₀ : ℝ := ∑ i : Fin N, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
    T₁.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hτ : ∀ S x, 0 ≤ τ S x := fun S x => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- each `x ↦ τ S x` is `μ`-a.e. measurable, being continuous in `p_{Q(x)}`
  have hmeas : ∀ S : Submodule ℝ (Euclid N),
      AEMeasurable (fun x => ENNReal.ofReal (τ S x)) (μ.restrict (closedBall ξ σ)) := by
    intro S
    have hcont : Continuous fun L : Euclid N →L[ℝ] Euclid N =>
        ∑ i : Fin N, ‖L (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).sub continuous_const).norm.pow 2
    exact (hcont.comp_aestronglyMeasurable hQ).aemeasurable.ennreal_ofReal.restrict
  -- `c₀ μ(B_σ(ξ)) ≤ 2 J(T) + 2 J(T₁) ≤ 4a`
  have hint : ENNReal.ofReal c₀ * μ (closedBall ξ σ) ≤ ENNReal.ofReal (4 * a) := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in closedBall ξ σ, ENNReal.ofReal c₀ ∂μ
        ≤ ∫⁻ x in closedBall ξ σ,
            (2 * ENNReal.ofReal (τ T x) + 2 * ENNReal.ofReal (τ T₁ x)) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc ENNReal.ofReal c₀ ≤ ENNReal.ofReal (2 * τ T x + 2 * τ T₁ x) :=
                ENNReal.ofReal_le_ofReal (htri (Q x) T T₁)
            _ = 2 * ENNReal.ofReal (τ T x) + 2 * ENNReal.ofReal (τ T₁ x) := by
                rw [ENNReal.ofReal_add (mul_nonneg zero_le_two (hτ T x))
                    (mul_nonneg zero_le_two (hτ T₁ x)),
                  ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two,
                  ENNReal.ofReal_ofNat]
      _ = 2 * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T x) ∂μ +
            2 * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T₁ x) ∂μ := by
          rw [lintegral_add_left' ((hmeas T).const_mul 2),
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal a + 2 * ENNReal.ofReal a := by gcongr
      _ = ENNReal.ofReal (4 * a) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring
  -- hence `c₀ ≤ 4a/M`, as `μ(B_σ(ξ)) ≥ M > 0`
  have hc₀M : c₀ ≤ 4 * a / M := by
    rw [le_div_iff₀ hM, ← ENNReal.ofReal_le_ofReal_iff (by linarith), ENNReal.ofReal_mul hc₀]
    calc ENNReal.ofReal c₀ * ENNReal.ofReal M ≤ ENNReal.ofReal c₀ * μ (closedBall ξ σ) := by
          gcongr
      _ ≤ ENNReal.ofReal (4 * a) := hint
  -- the height bound: `y − p_T y = (y − p_{T₁} y) + (p_{T₁} − p_T) y` with `y = x − ξ`
  intro x hx
  have hy : ‖x - ξ‖ ≤ σ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  have hA : ‖T.starProjection (x - ξ) - T₁.starProjection (x - ξ)‖ ≤
      Real.sqrt c₀ * ‖x - ξ‖ := by
    have h := hHS (T.starProjection - T₁.starProjection) (x - ξ)
    simp only [sub_apply] at h
    rw [← Real.sqrt_sq (norm_nonneg (T.starProjection (x - ξ) - T₁.starProjection (x - ξ))),
      ← Real.sqrt_sq (norm_nonneg (x - ξ)), ← Real.sqrt_mul hc₀]
    exact Real.sqrt_le_sqrt h
  calc ‖(x - ξ) - T.starProjection (x - ξ)‖
      = ‖((x - ξ) - T₁.starProjection (x - ξ)) +
          (T₁.starProjection (x - ξ) - T.starProjection (x - ξ))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖(x - ξ) - T₁.starProjection (x - ξ)‖ +
          ‖T₁.starProjection (x - ξ) - T.starProjection (x - ξ)‖ := norm_add_le _ _
    _ ≤ h₁ + Real.sqrt (4 * a / M) * σ := by
        refine add_le_add (hh₁ x hx) ?_
        rw [norm_sub_rev]
        refine hA.trans ?_
        gcongr

/-- **Graph parameter transfer** (Simon Ch. 5, proof of 4.5, (14)–(16)).  Let
`Φ(v) = ξ + ιv + ι'f(v)` be the graph map of the `1`-Lipschitz `f`, `D = B̆_{r/2}(0)`,
`φ(x) = P(x − ξ)` (so `φ ∘ Φ = id`), and `μ = θHⁿ⌞M` with `θ = 1` `μ`-a.e. on `B_r(ξ)`.  Then
(a) `∫_D g ≤ ∫_{Φ(D)} g ∘ φ dμ + G·a` for measurable `0 ≤ g ≤ G`, and
(b) `|∫_D g − ∫_{Φ(D)} g ∘ φ dμ| ≤ G(a + 2ⁿ∫_D Σⱼ‖Dfʲ‖²)` for measurable `|g| ≤ G`.
The exceptional set lemma gives `μ(Φ(D)) < ∞` and a measurable `Z` with `Hⁿ(Φ(Z)) ≤ a` and
`∫_{Φ(D)} h dμ = ∫_{Φ(D ∖ Z)} h dHⁿ`; the graph area bounds then give `Lⁿ(Z) ≤ a` and
`∫_{D∖Z} h ≤ ∫_{Φ(D)} h ∘ φ dμ ≤ ∫_{D∖Z} (1 + 2ⁿs)h`, using `Σᵢ|Df eᵢ|² ≤ s = Σⱼ‖Dfʲ‖² ≤ k`;
the bounded transfer lemma yields (a) and (b). -/
theorem Submission.dorag_tes_graph_parameter_transfer : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (r a : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → 0 < r → closedBall ξ r ⊆ W → 0 ≤ a → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → (∀ (g : Euclid n → ℝ) (G : ℝ), Measurable g → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ G) → (∫⁻ v in ball (0 : Euclid n) (r / 2), ENNReal.ofReal (g v)) ≤ (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ENNReal.ofReal (g (P (x - ξ))) ∂R.measure) + ENNReal.ofReal (G * a)) ∧ ∀ (g : Euclid n → ℝ) (G : ℝ), Measurable g → (∀ v, |g v| ≤ G) → |(∫ v in ball (0 : Euclid n) (r / 2), g v) - (∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), g (P (x - ξ)) ∂R.measure)| ≤ G * (a + 2 ^ n * (∫ v in ball (0 : Euclid n) (r / 2), ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2)) := by
  intro n k hn U W R ξ r a ι ι' P f _hW hWU hr hrW ha horth hPι hPι' hf hfr hmult hspt hF
  -- Step 0.1: `φ(Φ(v)) = v` for `φ(x) = P(x − ξ)`, and `φ` is measurable
  have hφΦ : ∀ v, P (ξ + ι v + ι' (f v) - ξ) = v := fun v => by
    rw [add_assoc, add_sub_cancel_left, map_add, hPι, hPι', add_zero]
  have hφ : Measurable fun x : Euclid (n + k) => P (x - ξ) :=
    (P.continuous.comp (continuous_id.sub continuous_const)).measurable
  -- Steps 1–2: `μ(Φ(D)) < ∞`, and the exceptional set `Z` with `Hⁿ(Φ(Z)) ≤ a` and
  -- `∫_{Φ(D)} h̃ dμ = ∫_{Φ(D ∖ Z)} h̃ dHⁿ`
  obtain ⟨hμD, Z, hZ, hΦZ, hμ⟩ :=
    Submission.dorag_tes_gt_graph_measure_exceptional_set n k U W R ξ r a ι ι' P f hWU hr hrW
      hPι hPι' hf hfr hmult hspt hF
  -- Step 1.3: `Lⁿ(Z) ≤ Hⁿ(Φ(Z)) ≤ a`, by the graph area lower bound with `h ≡ 1`
  have hZa : volume Z ≤ ENNReal.ofReal a := by
    have h1 := (Submission.dorag_tes_lipschitz_graph_area_bounds n k hn ι ι' ξ f Z
      (fun _ => 1) horth hf hZ measurable_const).1
    simp only [setLIntegral_one] at h1
    exact h1.trans hΦZ
  -- Step 0.6: each `fʲ` is `1`-Lipschitz, so `0 ≤ s = Σⱼ ‖Dfʲ‖² ≤ k`; `s` is measurable,
  -- hence integrable on `D`
  have hfj : ∀ j : Fin k, LipschitzWith 1 fun v => EuclideanSpace.proj j (f v) := fun j =>
    LipschitzWith.of_dist_le_mul fun v w => by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
      exact (PiLp.norm_apply_le (f v - f w) j).trans (hf v w)
  have hs0 : ∀ v, 0 ≤ ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 :=
    fun v => Finset.sum_nonneg fun j _ => by positivity
  have hsD : IntegrableOn
      (fun v => ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2)
      (ball (0 : Euclid n) (r / 2)) := by
    refine IntegrableOn.of_bound measure_ball_lt_top (Measurable.aestronglyMeasurable
      (Finset.measurable_sum _ fun j _ => (measurable_fderiv ℝ _).norm.pow_const 2)) k
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (hs0 v)]
    calc ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2
        ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
          pow_le_one₀ (norm_nonneg _) ((norm_fderiv_le_of_lipschitz ℝ (hfj j)).trans_eq
            NNReal.coe_one)
      _ = k := by simp
  -- Step 3, (3a): `∫_{D∖Z} h ≤ ∫_{Φ(D)} h ∘ φ dμ ≤ ∫_{D∖Z} (1 + 2ⁿs) h`, by the graph area
  -- bounds on `D ∖ Z` and `Σᵢ |Df(v)eᵢ|² ≤ Σⱼ ‖Dfʲ(v)‖²`
  have hbd : ∀ h : Euclid n → ℝ≥0∞, Measurable h →
      (∫⁻ v in ball (0 : Euclid n) (r / 2) \ Z, h v) ≤
        (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h (P (x - ξ))
          ∂R.measure) ∧
      (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h (P (x - ξ))
          ∂R.measure) ≤
        ∫⁻ v in ball (0 : Euclid n) (r / 2) \ Z, ENNReal.ofReal (1 + 2 ^ n *
          ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2) * h v := by
    intro h hh
    have hhφ : Measurable fun x => h (P (x - ξ)) := hh.comp hφ
    rw [hμ _ hhφ]
    obtain ⟨hlo, hhi⟩ := Submission.dorag_tes_lipschitz_graph_area_bounds n k hn ι ι' ξ f
      (ball 0 (r / 2) \ Z) _ horth hf (measurableSet_ball.diff hZ) hhφ
    simp only [hφΦ] at hlo hhi
    refine ⟨hlo, hhi.trans (lintegral_mono fun v => ?_)⟩
    gcongr
    exact Submission.dorag_tes_gt_fderiv_columns_sq_le_rows_sq n k f v
  -- Steps 4–5: (a) and (b), by the bounded transfer lemma
  exact Submission.dorag_tes_gt_bounded_transfer_of_lintegral_bounds (Euclid n) (Euclid (n + k))
    volume R.measure (ball 0 (r / 2)) Z ((fun v => ξ + ι v + ι' (f v)) '' ball 0 (r / 2))
    (fun x => P (x - ξ))
    (fun v => ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2) a (2 ^ n)
    measurableSet_ball hZ hφ measure_ball_lt_top.ne hμD hZa ha (by positivity) hs0 hsD hbd

/-- **Weak harmonicity of the Lipschitz graph** (Simon Ch. 5, proof of Theorem 4.5, (12)–(16): the
graph estimates (12), (13) transferred to `B̆_{r/2}` by the area formula).  Let `f : ℝⁿ → ℝᵏ` be
`1`-Lipschitz with graph `Φ(v) = ξ + ιv + ι'f(v)` over `T`, let `e` bound the tilt
`∫_{B_r(ξ)} |p_{TₓM} − p_T|² dμ`, `a` the graph defect `μ(B_r(ξ) ∖ F) + Hⁿ((F ∖ spt μ) ∩ B_r(ξ))`,
`m` the mass `μ(B_r(ξ))` and `κ` the mean curvature `|H|`.  With `P = ι*` (so `P ∘ ι = id`,
`P ∘ ι' = 0`), the first-variation estimate on `Φ(B̆_{r/2})` and the transfer of integrals from
`Φ(B̆_{r/2})` to `B̆_{r/2}` give, for each component `fʲ`, (E) `∫_{B̆_{r/2}} |Dfʲ|² ≤ 2e + a` and
(W) `|∫_{B̆_{r/2}} Dfʲ · Dζ| ≤ G((2 + 2ⁿ⁺¹k)(e + a) + κrm)` for `ζ ∈ C¹_c(B̆_{r/2})`, `|Dζ| ≤ G`. -/
theorem Submission.dorag_tes_graph_weak_harmonic : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r e a m : ℝ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → 0 ≤ e → 0 ≤ a → 0 ≤ m → Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖(x - ξ) - T.starProjection (x - ξ)‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → ∀ v : Euclid n, x = ξ + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → ∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal e → R.measure (closedBall ξ r \ range (fun v => ξ + ι v + ι' (f v))) + μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → R.measure (closedBall ξ r) ≤ ENNReal.ofReal m → (∀ j : Fin k, ∫ v in ball (0 : Euclid n) (r / 2), ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 ≤ 2 * e + a) ∧ ∀ (j : Fin k) (ζ : Euclid n → ℝ) (G : ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) (r / 2), ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ G * ((2 + 2 ^ (n + 1) * k) * (e + a) + κ * r * m) := by
  intro n k hn U W R H κ ξ r e a m T ι ι' f hW hWU hHm hHκ hδ hpm hr hball he ha hm hT hιι' hιT
    hf hfr hheight htan hmult hnull htilt hFa hμm
  -- Step 1: `P = ι*`, so `P (ι v) = v` and `P (ι' w) = 0`
  obtain ⟨P, hPι, hPι'⟩ : ∃ P : Euclid (n + k) →L[ℝ] Euclid n,
      (∀ v, P (ι v) = v) ∧ ∀ w, P (ι' w) = 0 :=
    ⟨ContinuousLinearMap.adjoint ι.toContinuousLinearMap,
      fun v => ext_inner_right ℝ fun u => by
        rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
          LinearIsometry.inner_map_map],
      fun w => ext_inner_right ℝ fun u => by
        rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
          inner_zero_left, real_inner_comm, hιι' u w]⟩
  -- Step 2: `κ ≥ 0`, and the two summands of the graph defect are each `≤ a`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hFa₁ : R.measure (closedBall ξ r \ range (fun v => ξ + ι v + ι' (f v))) ≤
      ENNReal.ofReal a := le_self_add.trans hFa
  have hFa₂ : μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩
      closedBall ξ r) ≤ ENNReal.ofReal a := le_add_self.trans hFa
  -- Step 3: the first-variation estimate and the transfer of integrals, with this `P`
  obtain ⟨hvarE, hvarW⟩ := Submission.dorag_tes_graph_first_variation_estimate n k hn U W R H κ ξ
    r T ι ι' P f hW hWU hHm hHκ hδ hpm hr hball hT hιι' hιT hPι hPι' hf hfr hheight htan
  obtain ⟨htrA, htrB⟩ := Submission.dorag_tes_graph_parameter_transfer n k hn U W R ξ r a ι ι' P f
    hW hWU hr hball ha hιι' hPι hPι' hf hfr hmult hnull hFa₂
  -- Step 4: each `fʲ` is `1`-Lipschitz, so `‖Dfʲ‖ ≤ 1`
  have hDf : ∀ (j : Fin k) (v : Euclid n),
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ≤ 1 := by
    intro j v
    have hlip : LipschitzWith 1 (fun v => EuclideanSpace.proj j (f v)) :=
      LipschitzWith.of_dist_le_mul fun v w => by
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub]
        exact (PiLp.norm_apply_le (f v - f w) j).trans (hf v w)
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hlip
    rwa [NNReal.coe_one] at this
  -- Step 5: (E), from the transfer (a) with `g = ‖Dfʲ‖² ≤ 1` and the estimate (i)
  have hE : ∀ j : Fin k, ∫ v in ball (0 : Euclid n) (r / 2),
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 ≤ 2 * e + a := by
    intro j
    have hgm : Measurable fun v => ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 :=
      (measurable_fderiv ℝ _).norm.pow_const 2
    have hg0 : 0 ≤ᵐ[volume.restrict (ball (0 : Euclid n) (r / 2))]
        fun v => ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 :=
      Eventually.of_forall fun v => sq_nonneg _
    have hlin : ∫⁻ v in ball (0 : Euclid n) (r / 2),
        ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2) ≤
          ENNReal.ofReal (2 * e + a) :=
      calc ∫⁻ v in ball (0 : Euclid n) (r / 2),
            ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2)
          ≤ (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
              ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2)
                ∂R.measure) + ENNReal.ofReal (1 * a) :=
            htrA _ 1 hgm (fun v => sq_nonneg _) fun v => pow_le_one₀ (norm_nonneg _) (hDf j v)
        _ ≤ 2 * ENNReal.ofReal e + ENNReal.ofReal a := by
            rw [one_mul]
            gcongr
            exact (hvarE j).trans (by gcongr)
        _ = ENNReal.ofReal (2 * e + a) := by
            rw [ENNReal.ofReal_add (mul_nonneg zero_le_two he) ha,
              ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (add_nonneg (mul_nonneg zero_le_two he) ha) hlin
  refine ⟨hE, ?_⟩
  -- Step 6: (W)
  intro j ζ G hζ hζc hζs hζG
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  -- 6.1: `|Σᵢ A(eᵢ) B(eᵢ)| = |⟨a, b⟩| ≤ ‖A‖ ‖B‖` for the Riesz vectors `a`, `b` of `A`, `B`
  have hCS : ∀ A B : Euclid n →L[ℝ] ℝ, |∑ i : Fin n, A (EuclideanSpace.single i (1 : ℝ)) *
      B (EuclideanSpace.single i (1 : ℝ))| ≤ ‖A‖ * ‖B‖ := by
    intro A B
    have hsum : ∑ i : Fin n, A (EuclideanSpace.single i (1 : ℝ)) *
        B (EuclideanSpace.single i (1 : ℝ)) =
          inner ℝ ((InnerProductSpace.toDual ℝ (Euclid n)).symm A)
            ((InnerProductSpace.toDual ℝ (Euclid n)).symm B) := by
      rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.basisFun_apply, InnerProductSpace.toDual_symm_apply, real_inner_comm,
        InnerProductSpace.toDual_symm_apply]
    rw [hsum]
    exact (abs_real_inner_le_norm _ _).trans_eq
      (by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map])
  have hgm : Measurable fun v => ∑ i : Fin n,
      fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ)) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_fderiv_apply_const ℝ (fun v => EuclideanSpace.proj j (f v))
        (EuclideanSpace.single i (1 : ℝ))).mul
      (measurable_fderiv_apply_const ℝ ζ (EuclideanSpace.single i (1 : ℝ)))
  have hgG : ∀ v, |∑ i : Fin n,
      fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ G := fun v =>
    (hCS _ _).trans ((mul_le_mul (hDf j v) (hζG v) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul G))
  -- 6.2: `∫ Σⱼ' ‖Dfʲ'‖² = Σⱼ' ∫ ‖Dfʲ'‖² ≤ k (2e + a)`
  have hint : ∀ j' : Fin k, IntegrableOn
      (fun v => ‖fderiv ℝ (fun v => EuclideanSpace.proj j' (f v)) v‖ ^ 2)
      (ball (0 : Euclid n) (r / 2)) := fun j' =>
    IntegrableOn.of_bound measure_ball_lt_top
      ((measurable_fderiv ℝ _).norm.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall fun v => by
        rw [norm_pow, norm_norm]
        exact pow_le_one₀ (norm_nonneg _) (hDf j' v))
  have hS : ∫ v in ball (0 : Euclid n) (r / 2), ∑ j' : Fin k,
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j' (f v)) v‖ ^ 2 ≤ k * (2 * e + a) := by
    rw [integral_finsetSum _ fun j' _ => hint j']
    calc ∑ j' : Fin k, ∫ v in ball (0 : Euclid n) (r / 2),
          ‖fderiv ℝ (fun v => EuclideanSpace.proj j' (f v)) v‖ ^ 2
        ≤ ∑ _j' : Fin k, (2 * e + a) := Finset.sum_le_sum fun j' _ => hE j'
      _ = k * (2 * e + a) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- 6.3: the transfer (b): `|X − Y| ≤ G (a + 2ⁿ k (2e + a))`
  have hX : |(∫ v in ball (0 : Euclid n) (r / 2), ∑ i : Fin n,
      fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))) -
      (∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ∑ i : Fin n,
        fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
          (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) ∂R.measure)| ≤
        G * (a + 2 ^ n * (k * (2 * e + a))) :=
    (htrB _ G hgm hgG).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hS (by positivity))) hG)
  -- 6.4: the first-variation estimate (ii): `|Y| ≤ G (e + a + κrm/2)`
  have hκr : 0 ≤ κ * r / 2 := by positivity
  have hY0 : 0 ≤ G * (e + a + κ * r / 2 * m) := by positivity
  have hY : |∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ∑ i : Fin n,
      fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
        (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) ∂R.measure| ≤
        G * (e + a + κ * r / 2 * m) := by
    refine (ENNReal.ofReal_le_ofReal_iff hY0).1 ((hvarW j ζ G hζ hζc hζs hζG).trans ?_)
    calc ENNReal.ofReal G * (∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k),
          ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure +
          R.measure (closedBall ξ r \ range (fun v => ξ + ι v + ι' (f v))) +
          ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r))
        ≤ ENNReal.ofReal G * (ENNReal.ofReal e + ENNReal.ofReal a +
            ENNReal.ofReal (κ * r / 2) * ENNReal.ofReal m) := by
          gcongr
      _ = ENNReal.ofReal (G * (e + a + κ * r / 2 * m)) := by
          rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_add (add_nonneg he ha) (mul_nonneg hκr hm),
            ENNReal.ofReal_add he ha, ENNReal.ofReal_mul hκr]
  -- 6.5: `|X| ≤ |X − Y| + |Y|`, and `e + 2ⁿka + κrm/2 ≥ 0` absorbs the constants
  have key : a + 2 ^ n * (k * (2 * e + a)) + (e + a + κ * r / 2 * m) ≤
      (2 + 2 ^ (n + 1) * k) * (e + a) + κ * r * m := by
    have h1 : 0 ≤ (2 : ℝ) ^ n * k * a := by positivity
    have h2 : 0 ≤ κ * r * m := by positivity
    rw [pow_succ]
    linarith
  calc |∫ v in ball (0 : Euclid n) (r / 2), ∑ i : Fin n,
        fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))|
      ≤ G * (a + 2 ^ n * (k * (2 * e + a))) + G * (e + a + κ * r / 2 * m) := by
        linarith [abs_sub_abs_le_abs_sub (∫ v in ball (0 : Euclid n) (r / 2), ∑ i : Fin n,
          fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
            fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ)))
          (∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ∑ i : Fin n,
            fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
              (EuclideanSpace.single i (1 : ℝ)) *
              fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) ∂R.measure)]
    _ = G * (a + 2 ^ n * (k * (2 * e + a)) + (e + a + κ * r / 2 * m)) := by ring
    _ ≤ G * ((2 + 2 ^ (n + 1) * k) * (e + a) + κ * r * m) := mul_le_mul_of_nonneg_left key hG
/-- **`L²` height of `μ` about the plane of an affine approximation of a Lipschitz graph** (Simon
Ch. 5, proof of 4.5; chapter-05.txt lines 960–970, with (2)–(4) at lines 789–797).  Put
`τ = ξ + ι'c`, `S = range(ι + ι'Λ)`, `Φ(v) = ξ + ιv + ι'f(v)` and `F = Φ(ℝⁿ)`.  Then `dim S = n`,
and if `θ = 1` `μ`-a.e. on `B = B_t(τ)` and `|(x − ξ) − p_T(x − ξ)| ≤ h₀` on `spt μ ∩ B`, then
`∫_B |(x − τ) − p_S(x − τ)|² dμ ≤ (1 + n2ⁿ) ∫_{B̆ⁿ_t(0)} |f − c − Λ·|²` plus
`(h₀ + |c| + ‖Λ‖t)² μ(B ∖ F)`.  On `B ∩ F ⊆ Φ(Bⁿ_t)` we have `μ ≤ Hⁿ`, and the area formula with
`|(Φ(v) − τ) − p_S(Φ(v) − τ)| ≤ |f(v) − c − Λv|` gives the first term; `μ`-a.e. point of `B ∖ F`
lies in `spt μ`, where the integrand is at most `(h₀ + |c| + ‖Λ‖t)²`. -/
theorem Submission.dorag_tes_graph_affine_height : ∀ (n k : ℕ), 0 < n → ∀ (U : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (c : Euclid k) (Λ : Euclid n →L[ℝ] Euclid k) (t h₀ : ℝ), 0 < t → 0 ≤ h₀ → Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ᵐ x ∂R.measure, x ∈ closedBall (ξ + ι' c) t → R.mult x = 1) → (∀ x ∈ R.measure.support ∩ closedBall (ξ + ι' c) t, ‖(x - ξ) - T.starProjection (x - ξ)‖ ≤ h₀) → Module.finrank ℝ (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)) = n ∧ (∫⁻ x in closedBall (ξ + ι' c) t, ENNReal.ofReal (‖(x - (ξ + ι' c)) - (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)).starProjection (x - (ξ + ι' c))‖ ^ 2) ∂R.measure) ≤ ENNReal.ofReal (1 + n * 2 ^ n) * (∫⁻ v in ball (0 : Euclid n) t, ENNReal.ofReal (‖f v - c - Λ v‖ ^ 2)) + ENNReal.ofReal ((h₀ + ‖c‖ + ‖Λ‖ * t) ^ 2) * R.measure (closedBall (ξ + ι' c) t \ range (fun v => ξ + ι v + ι' (f v))) := by
  intro n k hn U R ξ T ι ι' f c Λ t h₀ ht hh₀ hT horth hιT hf hmult hheight
  -- `dim S = n` and the pointwise distance bounds come from the frame lemma.
  obtain ⟨hrank, hgraph, hoff⟩ :=
    Submission.dorag_tes_gah_plane_frame_bounds n k T ι ι' Λ ξ c hT horth hιT
  refine ⟨hrank, ?_⟩
  set τ := ξ + ι' c
  set S := LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ Λ.toLinearMap)
  set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v)
  set g : Euclid (n + k) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (‖(x - τ) - S.starProjection (x - τ)‖ ^ 2)
  have hgm : Measurable g := by fun_prop
  -- Split `B = (B ∩ F) ∪ (B ∖ F)`; no measurability of `F` is needed.
  have hsplit : ∫⁻ x in closedBall τ t, g x ∂R.measure ≤
      ∫⁻ x in closedBall τ t ∩ range Φ, g x ∂R.measure +
        ∫⁻ x in closedBall τ t \ range Φ, g x ∂R.measure := by
    conv_lhs => rw [← Set.inter_union_sdiff (closedBall τ t) (range Φ)]
    exact lintegral_union_le _ _ _
  -- Graph part: `B ∩ F ⊆ Φ(Bⁿ_t)` since `|v| ≤ |Φ(v) − τ|`.
  have hsub : closedBall τ t ∩ range Φ ⊆ Φ '' closedBall (0 : Euclid n) t := by
    rintro x ⟨hxB, v, rfl⟩
    refine ⟨v, ?_, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at hxB
    rw [mem_closedBall_zero_iff]
    exact (hgraph v (f v)).2.trans hxB
  have hgraph_part : ∫⁻ x in closedBall τ t ∩ range Φ, g x ∂R.measure ≤
      ENNReal.ofReal (1 + n * 2 ^ n) *
        ∫⁻ v in ball (0 : Euclid n) t, ENNReal.ofReal (‖f v - c - Λ v‖ ^ 2) := by
    calc ∫⁻ x in closedBall τ t ∩ range Φ, g x ∂R.measure
        ≤ ∫⁻ x in closedBall τ t ∩ range Φ, g x ∂μHE[n] :=
          (Submission.dorag_tes_gah_mult_one_le_hausdorff (n + k) n U R (closedBall τ t)
            measurableSet_closedBall hmult).2 _ g inter_subset_left
      _ ≤ ∫⁻ x in Φ '' closedBall (0 : Euclid n) t, g x ∂μHE[n] := lintegral_mono_set hsub
      _ ≤ ∫⁻ v in closedBall (0 : Euclid n) t, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n,
            ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * g (Φ v) :=
          (Submission.dorag_tes_lipschitz_graph_area_bounds n k hn ι ι' ξ f
            (closedBall (0 : Euclid n) t) g horth hf measurableSet_closedBall hgm).2
      _ ≤ ∫⁻ v in closedBall (0 : Euclid n) t, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n,
            ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) *
              ENNReal.ofReal (‖f v - c - Λ v‖ ^ 2) := by
          refine lintegral_mono fun v => mul_le_mul' le_rfl ?_
          exact ENNReal.ofReal_le_ofReal
            (pow_le_pow_left₀ (norm_nonneg _) (hgraph v (f v)).1 2)
      _ ≤ _ := Submission.dorag_tes_gah_lipschitz_weight_ball_le n k hn f hf _ t
  -- Off-graph part: `μ`-a.e. point of `B ∖ F` lies in `spt μ ∩ B`, where `g ≤ K²`.
  have hoff_part : ∫⁻ x in closedBall τ t \ range Φ, g x ∂R.measure ≤
      ENNReal.ofReal ((h₀ + ‖c‖ + ‖Λ‖ * t) ^ 2) * R.measure (closedBall τ t \ range Φ) := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    have h1 : ∀ᵐ x ∂R.measure.restrict (closedBall τ t \ range Φ), x ∈ R.measure.support :=
      ae_restrict_of_ae Measure.support_mem_ae
    have h2 : ∀ᵐ x ∂R.measure.restrict (closedBall τ t \ range Φ), x ∈ closedBall τ t :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset (ae_restrict_mem measurableSet_closedBall)
    filter_upwards [h1, h2] with x hx1 hx2
    have hxt : ‖x - τ‖ ≤ t := by rwa [mem_closedBall, dist_eq_norm] at hx2
    have hK : ‖(x - τ) - S.starProjection (x - τ)‖ ≤ h₀ + ‖c‖ + ‖Λ‖ * t :=
      calc ‖(x - τ) - S.starProjection (x - τ)‖
          ≤ ‖(x - ξ) - T.starProjection (x - ξ)‖ + ‖c‖ + ‖Λ‖ * ‖x - τ‖ := hoff x
        _ ≤ h₀ + ‖c‖ + ‖Λ‖ * t := by
          gcongr
          exact hheight x ⟨hx1, hx2⟩
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hK 2)
  exact hsplit.trans (add_le_add hgraph_part hoff_part)
/-- **Componentwise affine assembly** (Simon Ch. 5, proof of 4.5, (17)–(19); chapter-05.txt
lines 928–960).  Let `f : ℝⁿ → ℝᵏ` be continuous and `s > 0`, and suppose every rescaled
coordinate `s⁻¹fʲ` is `L²`-close on the open ball `B̆ₜ = ball 0 t` to an affine function:
`|a_j| ≤ A`, `‖b_j‖ ≤ B` and `∫_{B̆ₜ} (s⁻¹fʲ − a_j − b_j)² ≤ Q`.  With
`eⱼ = EuclideanSpace.single j 1`, the choices `c = Σⱼ s a_j eⱼ` and `Λ = Σⱼ (s b_j)(·) eⱼ` satisfy
`|c| ≤ k s A` and `‖Λ‖ ≤ k s B` (triangle inequality), and
`|f − c − Λ·|² = Σⱼ s² (s⁻¹fʲ − a_j − b_j)²` pointwise, so `∫_{B̆ₜ} |f − c − Λ·|² ≤ k s² Q`. -/
theorem Submission.dorag_tes_componentwise_affine_assembly : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (s A B Q t : ℝ), Continuous f → 0 < s → (∀ j : Fin k, ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ B ∧ |a| ≤ A ∧ ∫ v in ball (0 : Euclid n) t, (s⁻¹ * EuclideanSpace.proj j (f v) - a - b v) ^ 2 ≤ Q) → ∃ (c : Euclid k) (Λ : Euclid n →L[ℝ] Euclid k), ‖c‖ ≤ k * s * A ∧ ‖Λ‖ ≤ k * s * B ∧ ∫⁻ v in ball (0 : Euclid n) t, ENNReal.ofReal (‖f v - c - Λ v‖ ^ 2) ≤ ENNReal.ofReal (k * s ^ 2 * Q) := by
  intro n k f s A B Q t hf hs h
  choose a b hb ha hQ using h
  set e : Fin k → Euclid k := fun j => EuclideanSpace.single j (1 : ℝ) with he
  have hen : ∀ j, ‖e j‖ = 1 := fun j => by simp [he]
  set c : Euclid k := ∑ j, (s * a j) • e j with hc
  set Λ : Euclid n →L[ℝ] Euclid k := ∑ j, (s • b j).smulRight (e j) with hΛ
  refine ⟨c, Λ, ?_, ?_, ?_⟩
  · -- `|c| ≤ Σⱼ s |a_j| ≤ k s A`.
    calc ‖c‖ ≤ ∑ j, ‖(s * a j) • e j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin k, s * A := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, hen, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left (ha j) hs.le
      _ = k * s * A := by simp [mul_assoc]
  · -- `‖Λ‖ ≤ Σⱼ s ‖b_j‖ ≤ k s B`.
    calc ‖Λ‖ ≤ ∑ j, ‖(s • b j).smulRight (e j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin k, s * B := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ContinuousLinearMap.norm_smulRight_apply, hen, mul_one, norm_smul, Real.norm_eq_abs,
          abs_of_pos hs]
        exact mul_le_mul_of_nonneg_left (hb j) hs.le
      _ = k * s * B := by simp [mul_assoc]
  · set g : Fin k → Euclid n → ℝ := fun j v => (s⁻¹ * EuclideanSpace.proj j (f v) - a j - b j v) ^ 2
      with hg
    -- Pointwise `|f − c − Λ·|² = Σⱼ s² gⱼ`: the `j`-th coordinate is `s (s⁻¹fʲ − a_j − b_j)`.
    have hpt : ∀ v, ‖f v - c - Λ v‖ ^ 2 = ∑ j, s ^ 2 * g j v := by
      intro v
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcoord : (f v - c - Λ v).ofLp j =
          s * (s⁻¹ * EuclideanSpace.proj j (f v) - a j - b j v) := by
        simp [hc, hΛ, he, Pi.single_apply]
        field_simp
      rw [hcoord, hg, mul_pow]
    -- Each `gⱼ` is continuous, hence integrable on the bounded ball.
    have hint : ∀ j, IntegrableOn (g j) (ball (0 : Euclid n) t) := by
      intro j
      have hcont : Continuous (g j) := by
        simp only [hg]
        fun_prop
      exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 t)).mono_set
        ball_subset_closedBall
    have hint' : IntegrableOn (fun v => ‖f v - c - Λ v‖ ^ 2) (ball (0 : Euclid n) t) := by
      simp_rw [hpt]
      exact integrable_finsetSum _ fun j _ => (hint j).const_mul _
    -- Pass to the Bochner integral and sum the componentwise bounds.
    rw [← ofReal_integral_eq_lintegral_ofReal hint' (Eventually.of_forall fun v => sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc ∫ v in ball (0 : Euclid n) t, ‖f v - c - Λ v‖ ^ 2
        = ∫ v in ball (0 : Euclid n) t, ∑ j, s ^ 2 * g j v := by simp_rw [hpt]
      _ = ∑ j, ∫ v in ball (0 : Euclid n) t, s ^ 2 * g j v :=
        integral_finsetSum _ fun j _ => (hint j).const_mul _
      _ = ∑ j, s ^ 2 * ∫ v in ball (0 : Euclid n) t, g j v := by simp_rw [integral_const_mul]
      _ ≤ ∑ _j : Fin k, s ^ 2 * Q :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hQ j) (sq_nonneg s)
      _ = k * s ^ 2 * Q := by simp [mul_assoc]
/-- **A null set at whose points the measure is locally finite has open neighbourhoods of
arbitrarily small measure** (localized outer regularity).  The balls `B(x, r(x))` of finite
measure, `x ∈ A`, have a countable subfamily `B(i, r(i))`, `i ∈ T ⊆ A`, still covering `A`
(Lindelöf).  With budgets `δᵢ > 0`, `∑ᵢ δᵢ < ε`, outer regularity of the finite measure
`μ ⌞ B(i, r(i))` at `A` gives an open `Uᵢ ⊇ A` with `μ (Uᵢ ∩ B(i, r(i))) < δᵢ`; take
`O = ⋃ᵢ Uᵢ ∩ B(i, r(i))`. -/
theorem Submission.dorag_sn_open_superset_measure_lt : ∀ (N : ℕ) (μ : Measure (Euclid N)) (A : Set (Euclid N)), μ A = 0 → (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ μ (ball x r) ≠ ∞) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ O : Set (Euclid N), IsOpen O ∧ A ⊆ O ∧ μ O < ε := by
  intro N μ A hA hloc ε hε
  choose! r hr hfin using hloc
  -- Lindelöf: countably many of the balls `B(x, r(x))`, `x ∈ A`, still cover `A`
  obtain ⟨T, hTA, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable A
    (fun x => ball x (r x)) fun x _ => isOpen_ball
  have : Countable T := hTc.to_subtype
  -- budgets `δᵢ > 0` with `∑ᵢ δᵢ < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' T
  -- outer regularity of the finite measure `μ ⌞ B(i, r(i))` at the null set `A`
  have hU : ∀ i : T, ∃ U : Set (Euclid N), A ⊆ U ∧ IsOpen U ∧
      μ (U ∩ ball (i : Euclid N) (r i)) < δ i := by
    intro i
    have : IsFiniteMeasure (μ.restrict (ball (i : Euclid N) (r i))) :=
      isFiniteMeasure_restrict.2 (hfin i (hTA i.2))
    obtain ⟨U, hAU, hUo, hUδ⟩ := A.exists_isOpen_lt_of_lt
      (μ := μ.restrict (ball (i : Euclid N) (r i))) (δ i)
      ((Measure.restrict_apply_le _ A).trans_lt (by rw [hA]; exact hδ i))
    exact ⟨U, hAU, hUo, by rwa [Measure.restrict_apply hUo.measurableSet] at hUδ⟩
  choose U hAU hUo hUδ using hU
  refine ⟨⋃ i : T, U i ∩ ball (i : Euclid N) (r i),
    isOpen_iUnion fun i => (hUo i).inter isOpen_ball, fun x hx => ?_, ?_⟩
  · obtain ⟨i, hiT, hxi⟩ :=
      mem_iUnion₂.1 (hTU.superset (mem_biUnion hx (mem_ball_self (hr x hx))))
    exact mem_iUnion.2 ⟨⟨i, hiT⟩, hAU _ hx, hxi⟩
  · calc μ (⋃ i : T, U i ∩ ball (i : Euclid N) (r i))
        ≤ ∑' i : T, μ (U i ∩ ball (i : Euclid N) (r i)) := measure_iUnion_le _
      _ ≤ ∑' i : T, δ i := ENNReal.tsum_le_tsum fun i => (hUδ i).le
      _ < ε := hδε
/-- **Simon Ch. 1, Theorem 3.3** (comparison theorem, p. 14), with a non-sharp constant and
`Hⁿ = μHE[n]` on `ℝᴺ`: if `ν(B̄_t(x)) ≥ c tⁿ` for all small `t > 0` at every point `x` of a subset
`A` of an open set `O`, then `Hⁿ(A) ≤ C ν(O)` with `C = C(n, c) < ∞`.  At each scale `δ` the
5-times covering lemma (Simon 3.4) selects, among the balls `B̄_r(x) ⊆ O` with `x ∈ A`, `10r ≤ δ`
and `ν(B̄_r(x)) ≥ c rⁿ`, a disjoint, hence countable, subfamily whose 5-times enlargements cover
`A`.  This `δ`-cover costs `Σ (10rⱼ)ⁿ ≤ (10ⁿ/c) Σ ν(B̄_{rⱼ}(xⱼ)) ≤ (10ⁿ/c) ν(O)`, and `μHE[n]` is
a finite multiple of `μH[n]`. -/
theorem Submission.dorag_sn_hausdorff_le_mul_of_lower_density : ∀ (N n : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ν : Measure (Euclid N)) (A O : Set (Euclid N)), IsOpen O → A ⊆ O → (∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ ν (closedBall x t)) → μHE[n] A ≤ C * ν O := by
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
/-- Step 2 of the Lipschitz approximation lemma (Simon Ch. 5, Lemma 2.6, in Allard's theorem as used
for 7.4.3): orthonormal graph coordinates adapted to an `n`-plane `T₀ ⊆ ℝ^{n+k}`.  With orthonormal
bases `a` of `T₀` and `b` of `T₀ᗮ` (`dim T₀ᗮ = k`), `ι v = Σ vᵢaᵢ` and `ι' w = Σ wⱼbⱼ` are linear
isometries onto `T₀` and `T₀ᗮ`; hence `⟪ι v, ι' w⟫ = 0`, every `x = p_{T₀} x + (x − p_{T₀} x)` is
`ι v + ι' w`, and `p_{T₀}(ι v + ι' w) = ι v`. -/
theorem Submission.dorag_lip_orthonormal_coordinates : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))), Module.finrank ℝ T₀ = n → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ v, ι v ∈ T₀) ∧ (∀ x, ∃ v w, x = ι v + ι' w) ∧ (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) := by
  intro n k T₀ hT₀
  -- `dim T₀ᗮ = k`, since `dim T₀ + dim T₀ᗮ = n + k`
  have hTo : Module.finrank ℝ T₀ᗮ = k := by
    have h := Submodule.finrank_add_finrank_orthogonal T₀
    rw [finrank_euclideanSpace_fin, hT₀] at h
    omega
  -- orthonormal bases of `T₀` and `T₀ᗮ` indexed by `Fin n` and `Fin k`
  let b := (stdOrthonormalBasis ℝ T₀).reindex (finCongr hT₀)
  let b' := (stdOrthonormalBasis ℝ T₀ᗮ).reindex (finCongr hTo)
  -- inverse coordinate maps followed by the inclusions of `T₀` and `T₀ᗮ`
  let ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k) := T₀.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k) := T₀ᗮ.subtypeₗᵢ.comp b'.repr.symm.toLinearIsometry
  have hιmem : ∀ v, ι v ∈ T₀ := fun v => (b.repr.symm v).2
  have hι'mem : ∀ w, ι' w ∈ T₀ᗮ := fun w => (b'.repr.symm w).2
  refine ⟨ι, ι', fun v w => Submodule.inner_right_of_mem_orthogonal (hιmem v) (hι'mem w), hιmem,
    ?_, ?_⟩
  · -- `x = p_{T₀} x + (x − p_{T₀} x)` with `p_{T₀} x ∈ T₀` and `x − p_{T₀} x ∈ T₀ᗮ`
    intro x
    refine ⟨b.repr ⟨T₀.starProjection x, Submodule.starProjection_apply_mem _ _⟩,
      b'.repr ⟨x - T₀.starProjection x, Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    simp [ι, ι']
  · -- `p_{T₀}` fixes `ι v ∈ T₀` and kills `ι' w ∈ T₀ᗮ`
    intro v w
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hιmem v),
      (Submodule.starProjection_apply_eq_zero_iff T₀).mpr (hι'mem w), add_zero]
/-- **Two-measure five-times covering bound**: the summation step after the 5-times Covering
Lemma (Simon Ch. 1, 3.4, chapter-01.txt lines 612–622) in the proof of the Lipschitz
approximation lemma (Simon Ch. 5, proof of 2.6, chapter-05.txt lines 413–425 and 536–548).
If each `y ∈ A` has `0 < r(y) ≤ R₀`, `B_{r(y)}(y) ⊆ B` and `μ(A ∩ B_{5r(y)}(y)) ≤ c ν(B_{r(y)}(y))`,
then `μ(A) ≤ c ν(B)`.  Vitali's lemma (factor `5 > 3`) gives `u ⊆ A` with the balls
`B_{r(b)}(b)`, `b ∈ u`, pairwise disjoint, hence countable in the separable `ℝᴾ`, and
`A ⊆ ⋃_{b ∈ u} B_{5r(b)}(b)`; so `μ(A) ≤ Σ_b μ(A ∩ B_{5r(b)}(b)) ≤ c Σ_b ν(B_{r(b)}(b))
= c ν(⋃_b B_{r(b)}(b)) ≤ c ν(B)`. -/
theorem Submission.dorag_lip_vitali_two_measure_bound : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (A B : Set (Euclid P)) (r : Euclid P → ℝ) (R₀ : ℝ) (c : ℝ≥0∞), (∀ y ∈ A, 0 < r y ∧ r y ≤ R₀ ∧ closedBall y (r y) ⊆ B ∧ μ (A ∩ closedBall y (5 * r y)) ≤ c * ν (closedBall y (r y))) → μ A ≤ c * ν B := by
  intro P μ ν A B r R₀ c h
  -- Vitali selection with enlargement factor `5 > 3`.
  obtain ⟨u, huA, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    A id r R₀ (fun a ha => (h a ha).2.1) 5 (by norm_num)
  simp only [id] at hdisj hcov
  -- Disjoint balls with nonempty interior in the separable `ℝᴾ` are countably many.
  have hu : u.Countable := hdisj.countable_of_nonempty_interior fun a ha => by
    have hr := (h a (huA ha)).1
    exact ⟨a, interior_mono ball_subset_closedBall
      (by rw [isOpen_ball.interior_eq]; exact mem_ball_self hr)⟩
  -- `a ∈ B_{r(a)}(a) ⊆ B_{5r(b)}(b)`.
  have hAsub : A ⊆ ⋃ b ∈ u, A ∩ closedBall b (5 * r b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact mem_iUnion₂.2 ⟨b, hb, ha, hab (mem_closedBall_self (h a ha).1.le)⟩
  calc μ A ≤ μ (⋃ b ∈ u, A ∩ closedBall b (5 * r b)) := measure_mono hAsub
    _ ≤ ∑' b : u, μ (A ∩ closedBall b (5 * r b)) := measure_biUnion_le μ hu _
    _ ≤ ∑' b : u, c * ν (closedBall b (r b)) :=
        ENNReal.tsum_le_tsum fun b => (h b (huA b.2)).2.2.2
    _ = c * ∑' b : u, ν (closedBall b (r b)) := ENNReal.tsum_mul_left
    _ = c * ν (⋃ b ∈ u, closedBall b (r b)) := by
        rw [measure_biUnion hu hdisj fun b _ => measurableSet_closedBall]
    _ ≤ c * ν B := by
        gcongr
        exact iUnion₂_subset fun b hb => (h b (huA hb)).2.2.1
/-- **A cone set lies in a bounded Lipschitz graph**: Steps 5–6 of the proof of the Lipschitz
approximation lemma (Simon Ch. 5, proof of 2.6, chapter-05.txt lines 456–480: from
`|Q(y₂ − y₁)| ≤ CβL|y₁ − y₂|` and `Cβ ≤ ½`, "`|Q(y₁) − Q(y₂)| ≤ 2CβL|P(y₁) − P(y₂)|`", so by the
Lipschitz Extension Theorem (Ch. 2, 1.2, chapter-02.txt line 33) `G ⊆ graph f`, and replacing
`fʲ` by `max{min{fʲ, Cδ^{1/(2n+2)}}, −Cδ^{1/(2n+2)}}` gives `sup |f| ≤ Cδ^{1/(2n+2)}`).  Here
`P = p_{T₀}`, `Q = 1 − P`, `λ = lam`.  Writing `y − ξ = ιv_y + ι'w_y`, `Q(y − ξ) = ι'w_y`, so
`|w_y| ≤ A` and the cone condition gives `|w_{y₂} − w_{y₁}| ≤ 2λ|v_{y₂} − v_{y₁}|`; hence
`v_y ↦ w_y` is a well-defined `2λ`-Lipschitz map on `{v_y : y ∈ G}`, whose coordinates are
extended (McShane) and truncated to `[−A, A]`, giving `f` with `Lip f ≤ 2√k λ`, `|f| ≤ √k A` and
`G ⊆ {ξ + ιv + ι'f(v)}`. -/
theorem Submission.dorag_lip_cone_set_graph_extension : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (G : Set (Euclid (n + k))) (lam A : ℝ), (∀ x, ∃ v w, x = ι v + ι' w) → (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) → 0 ≤ lam → lam ≤ 1 / 2 → 0 ≤ A → (∀ y₁ ∈ G, ∀ y₂ ∈ G, ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ lam * ‖y₂ - y₁‖) → (∀ y ∈ G, ‖(y - ξ) - T₀.starProjection (y - ξ)‖ ≤ A) → ∃ f : Euclid n → Euclid k, (∀ v w, ‖f v - f w‖ ≤ 2 * Real.sqrt k * lam * ‖v - w‖) ∧ (∀ v, ‖f v‖ ≤ Real.sqrt k * A) ∧ G ⊆ range (fun v => ξ + ι v + ι' (f v)) := by
  intro n k T₀ ι ι' ξ G lam A hspan hproj hlam0 hlam1 hA hcone hbound
  classical
  -- Step 1: coordinates `y - ξ = ι (φ y) + ι' (ψ y)`, with `Q (y - ξ) = ι' (ψ y)`.
  choose φ ψ hφψ using fun y : Euclid (n + k) => hspan (y - ξ)
  have hψA : ∀ y ∈ G, ‖ψ y‖ ≤ A := by
    intro y hy
    have h := hbound y hy
    rw [hφψ y, hproj, add_sub_cancel_left, LinearIsometry.norm_map] at h
    exact h
  -- Step 2: the two-point estimate `|ψ y₂ - ψ y₁| ≤ 2λ |φ y₂ - φ y₁|`.
  have hdiff : ∀ y₁ y₂ : Euclid (n + k), y₂ - y₁ = ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁) := by
    intro y₁ y₂
    have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
    rw [e, hφψ y₁, hφψ y₂, map_sub, map_sub]
    abel
  have htwo : ∀ y₁ ∈ G, ∀ y₂ ∈ G, ‖ψ y₂ - ψ y₁‖ ≤ 2 * lam * ‖φ y₂ - φ y₁‖ := by
    intro y₁ hy₁ y₂ hy₂
    have h := hcone y₁ hy₁ y₂ hy₂
    rw [hdiff y₁ y₂, hproj, add_sub_cancel_left, LinearIsometry.norm_map] at h
    have h2 : ‖ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁)‖ ≤ ‖φ y₂ - φ y₁‖ + ‖ψ y₂ - ψ y₁‖ := by
      calc ‖ι (φ y₂ - φ y₁) + ι' (ψ y₂ - ψ y₁)‖
          ≤ ‖ι (φ y₂ - φ y₁)‖ + ‖ι' (ψ y₂ - ψ y₁)‖ := norm_add_le _ _
        _ = ‖φ y₂ - φ y₁‖ + ‖ψ y₂ - ψ y₁‖ := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
    have h3 := mul_le_mul_of_nonneg_left h2 hlam0
    have h4 := mul_nonneg (sub_nonneg.mpr hlam1) (norm_nonneg (ψ y₂ - ψ y₁))
    nlinarith [norm_nonneg (ψ y₂ - ψ y₁), norm_nonneg (φ y₂ - φ y₁)]
  -- Step 3: a function `g` on `D := φ '' G` with `g (φ y) = ψ y`.
  set D : Set (Euclid n) := φ '' G
  let g : Euclid n → Euclid k := fun v => ψ (Function.invFunOn φ G v)
  have hg_eq : ∀ y ∈ G, g (φ y) = ψ y := by
    intro y hy
    obtain ⟨h1, h2⟩ := Function.invFunOn_pos (b := φ y) ⟨y, hy, rfl⟩
    have h := htwo y hy _ h1
    simp only [h2, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hgLip : ∀ v₁ ∈ D, ∀ v₂ ∈ D, ‖g v₁ - g v₂‖ ≤ 2 * lam * ‖v₁ - v₂‖ := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [hg_eq y₁ hy₁, hg_eq y₂ hy₂]
    exact htwo y₂ hy₂ y₁ hy₁
  -- Step 4: McShane extension of each coordinate (Simon Ch. 2, 1.2).
  have hcoordLip : ∀ j : Fin k,
      LipschitzOnWith (Real.toNNReal (2 * lam)) (fun v => g v j) D := by
    intro j
    apply LipschitzOnWith.of_dist_le'
    intro v₁ hv₁ v₂ hv₂
    rw [Real.dist_eq, dist_eq_norm]
    calc |g v₁ j - g v₂ j| = ‖(g v₁ - g v₂) j‖ := by rw [PiLp.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖g v₁ - g v₂‖ := PiLp.norm_apply_le _ j
      _ ≤ 2 * lam * ‖v₁ - v₂‖ := hgLip v₁ hv₁ v₂ hv₂
  choose h hhLip hhEq using fun j => (hcoordLip j).extend_real
  -- Step 5: truncation of each coordinate to `[-A, A]`.
  let F : Fin k → Euclid n → ℝ := fun j v => max (-A) (min A (h j v))
  have hFLip : ∀ j, LipschitzWith (Real.toNNReal (2 * lam)) (F j) :=
    fun j => ((hhLip j).const_min A).const_max (-A)
  have hFbound : ∀ j v, |F j v| ≤ A := by
    intro j v
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hFeq : ∀ y ∈ G, ∀ j, F j (φ y) = ψ y j := by
    intro y hy j
    have hmem : φ y ∈ D := ⟨y, hy, rfl⟩
    have e1 : h j (φ y) = g (φ y) j := (hhEq j hmem).symm
    rw [hg_eq y hy] at e1
    have hb : |ψ y j| ≤ A := by
      calc |ψ y j| = ‖ψ y j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ψ y‖ := PiLp.norm_apply_le _ j
        _ ≤ A := hψA y hy
    show max (-A) (min A (h j (φ y))) = ψ y j
    rw [e1, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  -- Step 6: assemble `f` from its coordinates.
  let f : Euclid n → Euclid k := fun v => WithLp.toLp 2 (fun j => F j v)
  have hf_apply : ∀ v j, f v j = F j v := fun v j => rfl
  have hK : ((Real.toNNReal (2 * lam) : NNReal) : ℝ) = 2 * lam :=
    Real.coe_toNNReal _ (by linarith)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro v w
    rw [EuclideanSpace.norm_eq (f v - f w)]
    have hterm : ∀ j, ‖(f v - f w) j‖ ^ 2 ≤ (2 * lam * ‖v - w‖) ^ 2 := by
      intro j
      have h1 := (hFLip j).dist_le_mul v w
      rw [hK, Real.dist_eq, dist_eq_norm] at h1
      rw [PiLp.sub_apply, hf_apply, hf_apply, Real.norm_eq_abs, sq_abs]
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc √(∑ j, ‖(f v - f w) j‖ ^ 2) ≤ √(∑ _j : Fin k, (2 * lam * ‖v - w‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
      _ = √(k : ℝ) * (2 * lam * ‖v - w‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
      _ = 2 * √(k : ℝ) * lam * ‖v - w‖ := by ring
  · intro v
    rw [EuclideanSpace.norm_eq (f v)]
    have hterm : ∀ j, ‖(f v) j‖ ^ 2 ≤ A ^ 2 := by
      intro j
      rw [hf_apply, Real.norm_eq_abs, sq_abs]
      have h1 := hFbound j v
      exact sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    calc √(∑ j, ‖(f v) j‖ ^ 2) ≤ √(∑ _j : Fin k, A ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hterm j)
      _ = √(k : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hA]
  · -- Step 7: `G` lies in the graph `{ξ + ι v + ι' (f v)}`.
    intro y hy
    refine Set.mem_range.mpr ⟨φ y, ?_⟩
    have hfy : f (φ y) = ψ y := by
      apply PiLp.ext
      intro j
      rw [hf_apply]
      exact hFeq y hy j
    show ξ + ι (φ y) + ι' (f (φ y)) = y
    rw [hfy, add_assoc, ← hφψ y]
    abel
/-- **Cone condition and `Hⁿ` bound for a rotated Lipschitz graph**: Steps 8–9 of the proof of the
Lipschitz approximation lemma (Simon Ch. 5, proof of 2.6, chapter-05.txt lines 519–521 and
544–545: `|Q(x − y)| ≤ Cβ|x − y|` on `F` "because `Lip f ≤ βL`", and `Hⁿ(B_{5σⱼ}(ξⱼ) ∩ F) ≤ Cσⱼⁿ`
"since `F` is the graph of the Lipschitz function `f` with `Lip f ≤ 1`").  Here
`Φ(v) = ξ + ιv + ι'f(v)`, `F = Φ(ℝⁿ)` and `P = p_{T₀}`, `Q = 1 − P`.  As `ι ⟂ ι'` are isometries,
`|ιa + ι'b|² = |a|² + |b|²`, and `P(ιa + ι'b) = ιa`; so (i) `|Q(Φv − Φv')| = |f v − f v'| ≤ Λ|v − v'|
≤ Λ|Φv − Φv'|`, and (ii) `F ∩ B_r(Φv₀) ⊆ Φ(Bⁿ_r(v₀))` with `Φ` `√2`-Lipschitz, whence
`Hⁿ(F ∩ B_r(x)) ≤ (√2)ⁿ ωₙ rⁿ` by Simon Ch. 2, 1.8(i). -/
theorem Submission.dorag_lip_graph_cone_hausdorff_bound : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (f : Euclid n → Euclid k) (Λ : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) → 0 ≤ Λ → Λ ≤ 1 → (∀ v w, ‖f v - f w‖ ≤ Λ * ‖v - w‖) → (∀ x ∈ range (fun v => ξ + ι v + ι' (f v)), ∀ x' ∈ range (fun v => ξ + ι v + ι' (f v)), ‖(x - x') - T₀.starProjection (x - x')‖ ≤ Λ * ‖x - x'‖) ∧ (∀ x ∈ range (fun v => ξ + ι v + ι' (f v)), ∀ r : ℝ, 0 < r → μHE[n] (range (fun v => ξ + ι v + ι' (f v)) ∩ closedBall x r) ≤ ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n * ENNReal.ofReal (r ^ n)) := by
  intro n k T₀ ι ι' ξ f Λ horth hproj hΛ0 hΛ1 hf
  -- `Φ v − Φ v' = ι(v − v') + ι'(f v − f v')`, and Pythagoras `|ιa + ι'b|² = |a|² + |b|²`.
  have hdiff : ∀ v v' : Euclid n, (ξ + ι v + ι' (f v)) - (ξ + ι v' + ι' (f v')) =
      ι (v - v') + ι' (f v - f v') := by
    intro v v'; rw [map_sub, map_sub]; abel
  have hpyth : ∀ (a : Euclid n) (b : Euclid k), ‖ι a + ι' b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    intro a b
    rw [norm_add_sq_real, horth a b, LinearIsometry.norm_map, LinearIsometry.norm_map]
    ring
  have hlow : ∀ (a : Euclid n) (b : Euclid k), ‖a‖ ≤ ‖ι a + ι' b‖ := by
    intro a b
    have h := hpyth a b
    have h2 : ‖a‖ ^ 2 ≤ ‖ι a + ι' b‖ ^ 2 := by rw [h]; nlinarith [sq_nonneg ‖b‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hQ : ∀ (a : Euclid n) (b : Euclid k),
      (ι a + ι' b) - T₀.starProjection (ι a + ι' b) = ι' b := by
    intro a b; rw [hproj]; abel
  constructor
  · -- (i) `|Q(x − x')| = |f v − f v'| ≤ Λ|v − v'| ≤ Λ|x − x'|`.
    rintro x ⟨v, rfl⟩ x' ⟨v', rfl⟩
    dsimp only
    rw [hdiff, hQ, LinearIsometry.norm_map]
    exact (hf v v').trans (mul_le_mul_of_nonneg_left (hlow _ _) hΛ0)
  · -- (ii) `F ∩ B_r(Φ v₀) ⊆ Φ(Bⁿ_r(v₀))`, `Φ` is `√2`-Lipschitz and `Hⁿ = Lⁿ` on `ℝⁿ`.
    rintro x ⟨v₀, rfl⟩ r hr
    set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v)
    have hdiffΦ : ∀ v v', Φ v - Φ v' = ι (v - v') + ι' (f v - f v') := fun v v' => hdiff v v'
    have hsub : range Φ ∩ closedBall (Φ v₀) r ⊆ Φ '' closedBall v₀ r := by
      rintro x ⟨⟨v, rfl⟩, hx⟩
      refine ⟨v, ?_, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      calc ‖v - v₀‖ ≤ ‖ι (v - v₀) + ι' (f v - f v₀)‖ := hlow _ _
        _ = ‖Φ v - Φ v₀‖ := by rw [hdiffΦ]
        _ ≤ r := hx
    have hLip : LipschitzOnWith (NNReal.sqrt 2) Φ (closedBall v₀ r) := by
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro v v'
      rw [dist_eq_norm, dist_eq_norm, Real.coe_sqrt, NNReal.coe_ofNat]
      have h := hpyth (v - v') (f v - f v')
      have hfv := hf v v'
      have hsq : ‖Φ v - Φ v'‖ ^ 2 ≤ (Real.sqrt 2 * ‖v - v'‖) ^ 2 := by
        rw [hdiffΦ, h, mul_pow, Real.sq_sqrt (by norm_num)]
        have h1 : ‖f v - f v'‖ ^ 2 ≤ (Λ * ‖v - v'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hfv 2
        have h2 : (Λ * ‖v - v'‖) ^ 2 ≤ ‖v - v'‖ ^ 2 := by
          rw [mul_pow]
          have : Λ ^ 2 ≤ 1 := by nlinarith
          nlinarith [sq_nonneg ‖v - v'‖]
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
    have hpow : ((NNReal.sqrt 2 : NNReal) : ℝ≥0∞) ^ n = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) := by
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, NNReal.coe_ofNat,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _)]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      ring_nf
    calc μHE[n] (range Φ ∩ closedBall (Φ v₀) r) ≤ μHE[n] (Φ '' closedBall v₀ r) := measure_mono hsub
      _ ≤ ((NNReal.sqrt 2 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (closedBall v₀ r) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip
      _ = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n * ENNReal.ofReal (r ^ n) := by
          rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
            Measure.addHaar_closedBall _ _ hr.le, finrank_euclideanSpace_fin, hpow]
          unfold unitBallVolume
          ring
/-- **Simon Ch. 5, proof of 2.6, (3)–(4)**, with the case `|y₂ − y₁| > σ₀/2` added (good-set cone
estimate of the Lipschitz approximation).  Put `t = |y₂ − y₁|`, `P = p_{T₀}`, `Q = 1 − P`.
If `t ≤ σ₀/2`, the affine approximation at `(y₁, t)` gives a plane `S` with
`|(y₂ − y₁) − p_S(y₂ − y₁)| ≤ C₃εt`.  Comparing the tilt integrals of `S` and `T₀` over
`B_{t/2}(y₁)` and using the lower density bound yields `|p_S − P|² ≤ (8C₃ + 2^{n+3})β²L²/ω`, and
the Hilbert–Schmidt bound `|(p_S − P)u| ≤ |p_S − P||u|` finishes.  If `t > σ₀/2`, flatness at
scale `σ₀` gives `|Q(y₂ − y₁)| ≤ 2C₆εσ₀ ≤ 4C₆βLt`.  Here `C₈ = max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆)`
and `ω = |B₁ⁿ|`. -/
theorem Submission.dorag_lip_good_set_cone_estimate : ∀ (n k : ℕ) (C₃ C₆ : ℝ), 1 ≤ C₃ → 1 ≤ C₆ → ∃ C₈ : ℝ, 0 < C₈ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ ε β L : ℝ), AEStronglyMeasurable (fun x => (τ x).starProjection) μ → 0 < σ₀ → 0 ≤ ε → 0 < β → 0 < L → ε ≤ β * L → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∃ S : Submodule ℝ (Euclid (n + k)), (∀ x ∈ μ.support ∩ closedBall y t, ‖(x - y) - S.starProjection (x - y)‖ ≤ C₃ * ε * t) ∧ ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ x ∈ μ.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * ε * σ₀) → ∀ y₁ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ y₂ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), (∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y₁ (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)) → ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖ := by
  intro n k C₃ C₆ hC₃ hC₆
  -- Hilbert–Schmidt bound `‖A u‖ ≤ |A| ‖u‖` with `|A|² = ∑ᵢ ‖A eᵢ‖²`
  have hHS : ∀ (A : Euclid (n + k) →L[ℝ] Euclid (n + k)) (u : Euclid (n + k)),
      ‖A u‖ ≤ Real.sqrt (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ := by
    intro A u
    have hu : u = ∑ i : Fin (n + k), u i • EuclideanSpace.single i (1 : ℝ) := by
      have := (EuclideanSpace.basisFun (Fin (n + k)) ℝ).sum_repr u
      simpa using this.symm
    have hAu : A u = ∑ i : Fin (n + k), u i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [hu]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul A _ _
    have h1 : ‖A u‖ ≤ ∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAu]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
        (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ i : Fin (n + k), |u i| ^ 2 = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => sq_abs _
    rw [h3] at h2
    have h4 : ∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ ≤
        Real.sqrt (‖u‖ ^ 2 * ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
      (le_abs_self _).trans (Real.abs_le_sqrt h2)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4
    calc ‖A u‖ ≤ _ := h1
      _ ≤ _ := h4
      _ = _ := mul_comm _ _
  -- `‖b − c‖² ≤ 2‖a − b‖² + 2‖a − c‖²`
  have hsq : ∀ a b c : Euclid (n + k), ‖b - c‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 := by
    intro a b c
    have h : ‖b - c‖ ≤ ‖a - b‖ + ‖a - c‖ := by
      calc ‖b - c‖ = ‖(a - c) - (a - b)‖ := by congr 1; abel
        _ ≤ ‖a - c‖ + ‖a - b‖ := norm_sub_le _ _
        _ = ‖a - b‖ + ‖a - c‖ := add_comm _ _
    have h0 : 0 ≤ ‖b - c‖ := norm_nonneg _
    have hab := norm_nonneg (a - b)
    have hac := norm_nonneg (a - c)
    have hmul : ‖b - c‖ * ‖b - c‖ ≤ (‖a - b‖ + ‖a - c‖) * (‖a - b‖ + ‖a - c‖) :=
      mul_le_mul h h h0 (by positivity)
    nlinarith [sq_nonneg (‖a - b‖ - ‖a - c‖)]
  -- pointwise Hilbert–Schmidt triangle bound `|B − C|² ≤ 2|A − B|² + 2|A − C|²`, in `ℝ≥0∞`
  have hpt : ∀ A B C : Euclid (n + k) →L[ℝ] Euclid (n + k),
      ENNReal.ofReal (∑ i : Fin (n + k), ‖B (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        2 * ENNReal.ofReal (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        2 * ENNReal.ofReal (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro A B C
    have hle : ∑ i : Fin (n + k), ‖B (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤
        2 * ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 +
        2 * ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          C (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hsq _ _ _
    refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- from the `ℝ≥0∞` inequalities to a real one
  have hreal_of : ∀ {h w X Y s : ℝ} {m : ℝ≥0∞}, 0 ≤ h → 0 ≤ w → 0 ≤ X → 0 ≤ Y →
      ENNReal.ofReal h * m ≤ 2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y →
      ENNReal.ofReal w * ENNReal.ofReal s ≤ 2 * m → h * w * s ≤ 4 * X + 4 * Y := by
    intro h w X Y s m hh hw hX hY h1 h2
    have h3 : ENNReal.ofReal (h * w * s) ≤ ENNReal.ofReal (4 * X + 4 * Y) := by
      calc ENNReal.ofReal (h * w * s)
          = ENNReal.ofReal h * (ENNReal.ofReal w * ENNReal.ofReal s) := by
            rw [ENNReal.ofReal_mul (mul_nonneg hh hw), ENNReal.ofReal_mul hh, mul_assoc]
        _ ≤ ENNReal.ofReal h * (2 * m) := by gcongr
        _ = 2 * (ENNReal.ofReal h * m) := by ring
        _ ≤ 2 * (2 * ENNReal.ofReal X + 2 * ENNReal.ofReal Y) := by gcongr
        _ = ENNReal.ofReal (4 * X + 4 * Y) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_ofNat]
            ring
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  have hC₃0 : 0 < C₃ := by linarith
  -- dividing out the radius factor
  have hdiv : ∀ {h w e b l s : ℝ}, 0 < w → 0 < s → 0 ≤ e → e ≤ b * l →
      h * w * s ≤ 4 * (C₃ * e ^ 2 * s) + 4 * (b ^ 2 * l ^ 2 * (2 ^ n * s)) →
      h ≤ (8 * C₃ + 2 ^ (n + 3)) / w * (b * l) ^ 2 := by
    intro h w e b l s hw hs he hebl H
    have h1 : h * w ≤ 4 * C₃ * e ^ 2 + 4 * 2 ^ n * (b * l) ^ 2 := by
      have : h * w * s ≤ (4 * C₃ * e ^ 2 + 4 * 2 ^ n * (b * l) ^ 2) * s := by
        calc h * w * s ≤ _ := H
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hs
    have he2 : e ^ 2 ≤ (b * l) ^ 2 := pow_le_pow_left₀ he hebl 2
    have h2n : (2:ℝ) ^ (n + 3) = 8 * 2 ^ n := by ring
    have hp : (0:ℝ) ≤ 2 ^ n := by positivity
    have hb : 0 ≤ (b * l) ^ 2 := sq_nonneg _
    have h2 : h * w ≤ (8 * C₃ + 2 ^ (n + 3)) * (b * l) ^ 2 := by
      rw [h2n]
      nlinarith [mul_le_mul_of_nonneg_left he2 hC₃0.le, mul_nonneg hC₃0.le hb, mul_nonneg hp hb]
    rw [div_mul_eq_mul_div, le_div_iff₀ hw]
    exact h2
  -- the constants: `ω = |B₁ⁿ|` and `C₈ = max(C₃ + √((8C₃ + 2^{n+3})/ω), 4C₆)`
  have hvol_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume; exact measure_ball_pos _ _ one_pos
  have hvol_lt : unitBallVolume n < ⊤ := by
    unfold unitBallVolume; exact measure_ball_lt_top
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hw_pos : 0 < w := by rw [hw]; exact ENNReal.toReal_pos hvol_pos.ne' hvol_lt.ne
  have hw_eq : unitBallVolume n = ENNReal.ofReal w := by
    rw [hw, ENNReal.ofReal_toReal hvol_lt.ne]
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (8 * C₃ + 2 ^ (n + 3)) / w := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hK_def]; positivity
  obtain ⟨C₈, hC₈⟩ : ∃ C : ℝ, C = max (C₃ + Real.sqrt K) (4 * C₆) := ⟨_, rfl⟩
  have hC₈a : C₃ + Real.sqrt K ≤ C₈ := by rw [hC₈]; exact le_max_left _ _
  have hC₈b : 4 * C₆ ≤ C₈ := by rw [hC₈]; exact le_max_right _ _
  refine ⟨C₈, by linarith, ?_⟩
  intro μ τ T₀ ξ σ₀ ε β L hmeas hσ₀ hε hβ hL hεβL H1 H2 H3 y₁ hy₁ y₂ hy₂ Hgood
  have hβL : 0 < β * L := mul_pos hβ hL
  -- a.e.-measurability of the tilt integrands
  have haem : ∀ S : Submodule ℝ (Euclid (n + k)), AEMeasurable (fun x => ENNReal.ofReal
      (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) μ := by
    intro S
    have hc : Continuous (fun A : Euclid (n + k) →L[ℝ] Euclid (n + k) => ENNReal.ofReal
        (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) := by
      refine ENNReal.continuous_ofReal.comp ?_
      exact continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).sub continuous_const).norm.pow 2
    exact (hc.comp_aestronglyMeasurable hmeas).aemeasurable
  -- integrating a pointwise bound over a set
  have hlint : ∀ {s : Set (Euclid (n + k))} {f g : Euclid (n + k) → ℝ≥0∞} {c : ℝ≥0∞},
      AEMeasurable f (μ.restrict s) → (∀ x, c ≤ 2 * f x + 2 * g x) →
      c * μ s ≤ 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
    intro s f g c hf hfg
    rw [← setLIntegral_const]
    calc ∫⁻ _ in s, c ∂μ ≤ ∫⁻ x in s, (2 * f x + 2 * g x) ∂μ := lintegral_mono hfg
      _ = ∫⁻ x in s, 2 * f x ∂μ + ∫⁻ x in s, 2 * g x ∂μ :=
          lintegral_add_left' (hf.const_mul 2) _
      _ = 2 * ∫⁻ x in s, f x ∂μ + 2 * ∫⁻ x in s, g x ∂μ := by
          rw [lintegral_const_mul' 2 f ENNReal.ofNat_ne_top,
            lintegral_const_mul' 2 g ENNReal.ofNat_ne_top]
  rcases (norm_nonneg (y₂ - y₁)).eq_or_lt with ht0 | htpos
  · have hu0 : y₂ - y₁ = 0 := norm_eq_zero.1 ht0.symm
    rw [hu0]; simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ‖y₂ - y₁‖ = t := ⟨_, rfl⟩
  rw [ht] at htpos ⊢
  rcases le_or_gt t (σ₀ / 2) with hts | hts
  · -- Case `0 < t ≤ σ₀ / 2`.
    obtain ⟨S, hS1, hS2⟩ := H1 y₁ hy₁ t htpos hts
    have hgood := Hgood t htpos hts
    have hy₂ball : y₂ ∈ μ.support ∩ closedBall y₁ t :=
      ⟨hy₂.1, mem_closedBall.2 (le_of_eq (by rw [dist_eq_norm, ht]))⟩
    have hQS : ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ ≤ C₃ * ε * t := hS1 y₂ hy₂ball
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = ∑ i : Fin (n + k),
        ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := ⟨_, rfl⟩
    have hh0 : 0 ≤ h := by rw [hh_def]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have hint := hlint (s := closedBall y₁ (t / 2)) (haem S).restrict
      (fun x => hpt ((τ x).starProjection) S.starProjection T₀.starProjection)
    rw [← hh_def] at hint
    have hint2 : ENNReal.ofReal h * μ (closedBall y₁ (t / 2)) ≤
        2 * ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n) +
          2 * ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n) := by
      refine hint.trans ?_
      gcongr
    have hdens := H2 y₁ hy₁ (t / 2) (by positivity) (by linarith)
    rw [hw_eq] at hdens
    have hreal := hreal_of hh0 hw_pos.le (by positivity) (by positivity) hint2 hdens
    have htn : t ^ n = 2 ^ n * (t / 2) ^ n := by
      rw [← mul_pow]; congr 1; ring
    rw [htn] at hreal
    have hhK : h ≤ K * (β * L) ^ 2 := by
      rw [hK_def]
      exact hdiv hw_pos (by positivity) hε hεβL hreal
    have hsqrt : Real.sqrt h ≤ Real.sqrt K * (β * L) := by
      calc Real.sqrt h ≤ Real.sqrt (K * (β * L) ^ 2) := Real.sqrt_le_sqrt hhK
        _ = Real.sqrt K * (β * L) := by rw [Real.sqrt_mul hK, Real.sqrt_sq hβL.le]
    have hHS' := hHS (S.starProjection - T₀.starProjection) (y₂ - y₁)
    simp only [_root_.sub_apply] at hHS'
    rw [← hh_def, ht] at hHS'
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - y₁) - S.starProjection (y₂ - y₁)) +
            (S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁))‖ := by
          congr 1; abel
      _ ≤ ‖(y₂ - y₁) - S.starProjection (y₂ - y₁)‖ +
            ‖S.starProjection (y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ := norm_add_le _ _
      _ ≤ C₃ * ε * t + Real.sqrt h * t := add_le_add hQS hHS'
      _ ≤ C₃ * (β * L) * t + Real.sqrt K * (β * L) * t := by
          have e1 : C₃ * ε * t ≤ C₃ * (β * L) * t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL hC₃0.le) htpos.le
          have e2 : Real.sqrt h * t ≤ Real.sqrt K * (β * L) * t :=
            mul_le_mul_of_nonneg_right hsqrt htpos.le
          linarith
      _ = (C₃ + Real.sqrt K) * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈a (by positivity)
      _ = C₈ * β * L * t := by ring
  · -- Case `t > σ₀ / 2`.
    have hsub : ∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), y ∈ μ.support ∩ closedBall ξ σ₀ :=
      fun y hy => ⟨hy.1, closedBall_subset_closedBall (by linarith) hy.2⟩
    have h1 := H3 y₁ (hsub y₁ hy₁)
    have h2 := H3 y₂ (hsub y₂ hy₂)
    have hQ : (y₂ - y₁) - T₀.starProjection (y₂ - y₁) =
        ((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) - ((y₁ - ξ) - T₀.starProjection (y₁ - ξ)) := by
      have e : y₂ - y₁ = (y₂ - ξ) - (y₁ - ξ) := by abel
      rw [e, map_sub T₀.starProjection (y₂ - ξ) (y₁ - ξ)]; abel
    have hC₆0 : 0 ≤ C₆ := by linarith
    have hCε : 0 ≤ C₆ * ε := mul_nonneg hC₆0 hε
    calc ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖
        = ‖((y₂ - ξ) - T₀.starProjection (y₂ - ξ)) -
            ((y₁ - ξ) - T₀.starProjection (y₁ - ξ))‖ := by rw [hQ]
      _ ≤ ‖(y₂ - ξ) - T₀.starProjection (y₂ - ξ)‖ + ‖(y₁ - ξ) - T₀.starProjection (y₁ - ξ)‖ :=
          norm_sub_le _ _
      _ ≤ C₆ * ε * σ₀ + C₆ * ε * σ₀ := add_le_add h2 h1
      _ = 2 * (C₆ * ε) * σ₀ := by ring
      _ ≤ 2 * (C₆ * ε) * (2 * t) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * C₆ * ε * t := by ring
      _ ≤ 4 * C₆ * (β * L) * t := by
          have : 0 ≤ 4 * C₆ := by linarith
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεβL this) htpos.le
      _ = 4 * C₆ * (β * L * t) := by ring
      _ ≤ C₈ * (β * L * t) := mul_le_mul_of_nonneg_right hC₈b (by positivity)
      _ = C₈ * β * L * t := by ring

/-- **Simon Ch. 5, proof of 2.6, (9)–(10), corrected** (estimate (10') of the Lipschitz
approximation: `B_σ(η)` becomes `B_{3s}(η)`, and as only `κσ₀ ≤ 1` is used there is no additive
error `Cδσⁿ`).
For `η ∈ (F ∖ spt μ) ∩ B_{σ₀/4}(ξ)` let `y ∈ spt μ` be a nearest point and `s = |y − η|/2`.  Then
`μ(B_s(η)) = 0`, the density bounds give `ωsⁿ/2 ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ`, and monotonicity with
radii `s < 3s` and `e^{3κs} ≤ 2` gives `μ(B_{3s}(η)) ≤ 2·3ⁿs⁻²∫_{B_{3s}(η)}|p_x^⊥(x − η)|² dμ`.
Splitting `p_x^⊥(x − η) = Q(x − η) + (P − p_x)(x − η)` (cone condition on `F`, Hilbert–Schmidt
bound) and absorbing the `λ²`-term yields `sⁿ ≤ C₉[μ(B_{3s}(η) ∖ F) + ∫_{B_{3s}(η)}|p_x − P|² dμ]`,
with `λ₀ = (288·15ⁿ)^{-1/2}` and `C₉ = 144·3ⁿ/ω`. -/
theorem Submission.dorag_lip_off_support_estimate : ∀ (n k : ℕ), ∃ lam₀ C₉ : ℝ, 0 < lam₀ ∧ 0 < C₉ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (F : Set (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ κ lam : ℝ), 0 < σ₀ → 0 ≤ κ → κ * σ₀ ≤ 1 → 0 ≤ lam → lam ≤ lam₀ → ξ ∈ μ.support → (∀ x ∈ F, ∀ x' ∈ F, ‖(x - x') - T₀.starProjection (x - x')‖ ≤ lam * ‖x - x'‖) → (∀ y ∈ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 8 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 8 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ (y : Euclid (n + k)) (s t : ℝ), y ∈ closedBall ξ (σ₀ / 4) → 0 < s → s < t → t ≤ 3 * σ₀ / 8 → ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * μ (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (τ x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ) → ∀ η ∈ (F \ μ.support) ∩ closedBall ξ (σ₀ / 4), ∃ s : ℝ, ∃ y ∈ μ.support, 0 < s ∧ 2 * s ≤ dist η ξ ∧ dist y η = 2 * s ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) := by
  intro n k
  -- Hilbert–Schmidt bound `‖A u‖² ≤ (∑ᵢ ‖A eᵢ‖²) ‖u‖²`
  have hHS : ∀ (A : Euclid (n + k) →L[ℝ] Euclid (n + k)) (u : Euclid (n + k)),
      ‖A u‖ ^ 2 ≤ (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
    intro A u
    have hu : ∑ i : Fin (n + k), u i • EuclideanSpace.single i (1 : ℝ) = u := by
      have h := (EuclideanSpace.basisFun (Fin (n + k)) ℝ).sum_repr u
      simpa using h
    have hAu : A u = ∑ i : Fin (n + k), u i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← hu]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul A _ _
    have h1 : ‖A u‖ ≤ ∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAu]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
        (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ i : Fin (n + k), |u i| ^ 2 = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => sq_abs _
    calc ‖A u‖ ^ 2 ≤ (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := h2
      _ = (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
          rw [h3, mul_comm]
  -- pointwise splitting `u - S u = (u - T u) + (T u - S u)` with the Hilbert–Schmidt bound
  have hsplit : ∀ (T S : Submodule ℝ (Euclid (n + k))) (u : Euclid (n + k)) (r q : ℝ),
      ‖u‖ ≤ r → ‖u - T.starProjection u‖ ≤ q →
      ‖u - S.starProjection u‖ ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2 *
        ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    intro T S u r q hr hq
    have hHS0 : 0 ≤ ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hA := hHS (T.starProjection - S.starProjection) u
    have e : ∑ i : Fin (n + k), ‖(T.starProjection - S.starProjection)
        (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_apply, norm_sub_rev]
    rw [e, sub_apply] at hA
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have hur : ‖u‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hu0 hr 2
    have hq2 : ‖u - T.starProjection u‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have htri : ‖u - S.starProjection u‖ ≤
        ‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖ := by
      have e2 : u - S.starProjection u =
          (u - T.starProjection u) + (T.starProjection u - S.starProjection u) := by abel
      rw [e2]
      exact norm_add_le _ _
    have hB : ‖T.starProjection u - S.starProjection u‖ ^ 2 ≤
        (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * r ^ 2 :=
      hA.trans (mul_le_mul_of_nonneg_left hur hHS0)
    have ha0 : 0 ≤ ‖u - T.starProjection u‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖T.starProjection u - S.starProjection u‖ := norm_nonneg _
    have hc0 : 0 ≤ ‖u - S.starProjection u‖ := norm_nonneg _
    have hsq : ‖u - S.starProjection u‖ ^ 2 ≤
        (‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖) ^ 2 :=
      pow_le_pow_left₀ hc0 htri 2
    nlinarith [sq_nonneg (‖u - T.starProjection u‖ - ‖T.starProjection u - S.starProjection u‖)]
  -- the pointwise bound in `ℝ≥0∞`, in the two cases `x ∈ F` / `x ∉ F`
  have hptE : ∀ (T S : Submodule ℝ (Euclid (n + k))) (u : Euclid (n + k)) (s lam : ℝ)
      (c : ℝ≥0∞), ‖u‖ ≤ 3 * s →
      (‖u - T.starProjection u‖ ≤ lam * (3 * s) ∨ c = ENNReal.ofReal (18 * s ^ 2)) →
      ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + c + ENNReal.ofReal (18 * s ^ 2) *
          ENNReal.ofReal (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro T S u s lam c hu h
    have hHS0 : 0 ≤ ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases h with hq | hc
    · have h1 := hsplit T S u (3 * s) (lam * (3 * s)) hu hq
      calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
          ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2 + 18 * s ^ 2 *
            ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            refine h1.trans (le_of_eq ?_)
            ring
        _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
        _ ≤ _ := add_le_add le_self_add le_rfl
    · have hq : ‖u - T.starProjection u‖ ≤ 3 * s := by
        calc ‖u - T.starProjection u‖ = ‖Tᗮ.starProjection u‖ := by
              rw [Submodule.starProjection_orthogonal_val]
          _ ≤ ‖u‖ := Submodule.norm_starProjection_apply_le _ _
          _ ≤ 3 * s := hu
      have h1 := hsplit T S u (3 * s) (3 * s) hu hq
      rw [hc]
      calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
          ≤ ENNReal.ofReal (18 * s ^ 2 + 18 * s ^ 2 *
            ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            refine h1.trans (le_of_eq ?_)
            ring
        _ = ENNReal.ofReal (18 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
        _ ≤ _ := add_le_add le_add_self le_rfl
  -- monotonicity with radii `s < 3 s`, combined with `e^{3κs} ≤ 2`
  have hexpb : ∀ (κ s : ℝ) (a J I₂ : ℝ≥0∞), 0 ≤ κ → 0 < s → κ * (3 * s) ≤ 3 / 8 →
      ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a ≤ J →
      J ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * I₂ →
      a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := by
    intro κ s a J I₂ hκ hs hκs hM hJ
    have hexp : Real.exp (κ * (3 * s)) ≤ 2 := by
      have h0 : 0 ≤ κ * (3 * s) := by positivity
      calc Real.exp (κ * (3 * s)) ≤ (2 + κ * (3 * s)) / (2 - κ * (3 * s)) :=
            Real.exp_le_two_add_div_two_sub h0 (by linarith)
        _ ≤ 2 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
    have hc : 0 ≤ Real.exp (κ * (3 * s)) * (3 * s) ^ n := by positivity
    have hcinv : ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
        ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) = 1 := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one]
      congr 1
      have h1 : Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s))) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h2 : (3 * s) ^ n / (3 * s) ^ n = 1 := div_self (by positivity)
      calc Real.exp (κ * (3 * s)) * (3 * s) ^ n * (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n)
          = (Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s)))) *
            ((3 * s) ^ n / (3 * s) ^ n) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    have hcs : Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2)) ≤
        2 * 3 ^ n / s ^ 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), mul_pow, pow_add]
      have hpos : 0 ≤ 3 ^ n * s ^ n * s ^ 2 := by positivity
      nlinarith
    calc a = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
          (ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a) := by
          rw [← mul_assoc, hcinv, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
          (ENNReal.ofReal (1 / s ^ (n + 2)) * I₂) := mul_le_mul_right (hM.trans hJ) _
      _ = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2))) * I₂ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
      _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hcs) _
  -- the final absorption argument (pure `ℝ≥0∞` arithmetic)
  have hfinal : ∀ (ω s lam : ℝ) (a I₂ X₁ X₂ : ℝ≥0∞), 0 < ω → 0 < s →
      72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 → ENNReal.ofReal (ω * s ^ n / 2) ≤ a →
      a ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) →
      a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ →
      I₂ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a + ENNReal.ofReal (18 * s ^ 2) * X₁ +
        ENNReal.ofReal (18 * s ^ 2) * X₂ →
      ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
    intro ω s lam a I₂ X₁ X₂ hω hs hlam2 ha_lower ha_upper haI hI
    have e1 : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) =
        ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      ring
    have e2 : ENNReal.ofReal (36 * 3 ^ n) =
        ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      ring
    have hmain : a ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
        ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      calc a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := haI
        _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a +
            ENNReal.ofReal (18 * s ^ 2) * X₁ + ENNReal.ofReal (18 * s ^ 2) * X₂) :=
            mul_le_mul_right hI _
        _ = ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
            ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
            rw [e1, e2]
            ring
    have hlamterm : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a ≤
        ENNReal.ofReal (ω * s ^ n / 4) := by
      calc ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a
          ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) :=
            mul_le_mul_right ha_upper _
        _ = ENNReal.ofReal (72 * 15 ^ n * lam ^ 2 * (ω * s ^ n)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (15 : ℝ) ^ n = 3 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
            ring
        _ ≤ ENNReal.ofReal (1 / 4 * (ω * s ^ n)) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right hlam2 (by positivity)
        _ = ENNReal.ofReal (ω * s ^ n / 4) := by
            congr 1
            ring
    have hfin : ENNReal.ofReal (ω * s ^ n / 4) ≤ ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      have h1 : ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4) ≤
          ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
        calc ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4)
            = ENNReal.ofReal (ω * s ^ n / 2) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
          _ ≤ a := ha_lower
          _ ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
              ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := hmain
          _ ≤ ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) :=
              add_le_add hlamterm le_rfl
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp h1
    calc ENNReal.ofReal (s ^ n) = ENNReal.ofReal (4 / ω) * ENNReal.ofReal (ω * s ^ n / 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_mul_div_comm, eq_div_iff (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (4 / ω) * (ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂)) :=
          mul_le_mul_right hfin _
      _ = ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  -- Step 0: the constants `λ₀ = (288·15ⁿ)^{-1/2}` and `C₉ = 144·3ⁿ/ω`
  have hV_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact measure_ball_pos _ _ one_pos
  have hV_lt : unitBallVolume n < ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, ω = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hω_pos : 0 < ω := by
    rw [hω_def]
    exact ENNReal.toReal_pos hV_pos.ne' hV_lt.ne
  have hV_eq : unitBallVolume n = ENNReal.ofReal ω := by
    rw [hω_def, ENNReal.ofReal_toReal hV_lt.ne]
  refine ⟨1 / Real.sqrt (288 * 15 ^ n), 144 * 3 ^ n / ω, by positivity, by positivity, ?_⟩
  intro μ τ T₀ F ξ σ₀ κ lam hσ₀ hκ hκσ hlam hlam₀ hξ hF hDa hDb hM2 η hη
  obtain ⟨⟨hηF, hηS⟩, hηξ'⟩ := hη
  have hηξ : dist η ξ ≤ σ₀ / 4 := mem_closedBall.mp hηξ'
  -- `72·15ⁿ·λ² ≤ 1/4` for `0 ≤ λ ≤ λ₀`
  have hlam2 : 72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 := by
    have hpos : (0 : ℝ) < 288 * 15 ^ n := by positivity
    have hsq : lam ^ 2 ≤ 1 / (288 * 15 ^ n) := by
      have h1 : lam ^ 2 ≤ (1 / Real.sqrt (288 * 15 ^ n)) ^ 2 := pow_le_pow_left₀ hlam hlam₀ 2
      rwa [div_pow, Real.sq_sqrt hpos.le, one_pow] at h1
    calc 72 * 15 ^ n * lam ^ 2 ≤ 72 * 15 ^ n * (1 / (288 * 15 ^ n)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 1 / 4 := by
          rw [mul_one_div, div_eq_iff hpos.ne']
          ring
  -- Step 1: nearest point of the support
  have hSc : IsClosed μ.support := Measure.isClosed_support
  have hSne : μ.support.Nonempty := ⟨ξ, hξ⟩
  have hd_pos : 0 < Metric.infDist η μ.support := (hSc.notMem_iff_infDist_pos hSne).mp hηS
  have hd_le : Metric.infDist η μ.support ≤ dist η ξ := Metric.infDist_le_dist_of_mem hξ
  obtain ⟨y, hyS, hyd⟩ := hSc.exists_infDist_eq_dist hSne η
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Metric.infDist η μ.support / 2 := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]
    positivity
  have h2s : 2 * s ≤ dist η ξ := by
    rw [hs_def]
    linarith
  have hyη : dist y η = 2 * s := by
    rw [dist_comm, ← hyd, hs_def]
    ring
  have hs8 : s ≤ σ₀ / 8 := by linarith
  have hyξ : dist y ξ ≤ σ₀ / 2 := by linarith [dist_triangle y η ξ]
  refine ⟨s, y, hyS, hs, h2s, hyη, ?_⟩
  -- Step 2: the small ball around `η` misses the support
  have hμs0 : μ (closedBall η s) = 0 := by
    have hsub : closedBall η s ⊆ μ.supportᶜ := by
      intro x hx
      rw [mem_compl_iff]
      intro hxS
      have h1 := Metric.infDist_le_dist_of_mem (x := η) hxS
      have h2 : dist x η ≤ s := mem_closedBall.mp hx
      rw [dist_comm] at h1
      linarith
    exact measure_mono_null hsub (Measure.measure_compl_support (μ := μ))
  -- Step 3: mass bounds `½ωsⁿ ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ`
  have hsub1 : closedBall y s ⊆ closedBall η (3 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x y η]
  have hsub2 : closedBall η (3 * s) ⊆ closedBall y (5 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    have h := dist_triangle x η y
    rw [dist_comm η y] at h
    linarith
  have hDb' := hDb y ⟨hyS, mem_closedBall.mpr hyξ⟩ s hs hs8
  have hDa' := hDa y (mem_closedBall.mpr hyξ) (5 * s) (by positivity) (by linarith)
  have ha_lower : ENNReal.ofReal (ω * s ^ n / 2) ≤ μ (closedBall η (3 * s)) := by
    have h1 : ENNReal.ofReal (ω * s ^ n) ≤ 2 * μ (closedBall η (3 * s)) := by
      calc ENNReal.ofReal (ω * s ^ n) = unitBallVolume n * ENNReal.ofReal (s ^ n) := by
            rw [hV_eq, ENNReal.ofReal_mul hω_pos.le]
        _ ≤ 2 * μ (closedBall y s) := hDb'
        _ ≤ 2 * μ (closedBall η (3 * s)) := mul_le_mul_right (measure_mono hsub1) _
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul' h1
  have ha_upper : μ (closedBall η (3 * s)) ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
    calc μ (closedBall η (3 * s)) ≤ μ (closedBall y (5 * s)) := measure_mono hsub2
      _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * s) ^ n) := hDa'
      _ = ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
        rw [hV_eq, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  -- Step 4: monotonicity at `η` with radii `s < 3 s`
  have hM2' := hM2 η s (3 * s) hηξ' hs (by linarith) (by linarith)
  rw [hμs0, mul_zero, zero_add] at hM2'
  have hJ : ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ ≤
      ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s) \ closedBall η s, ENNReal.ofReal (1 / s ^ (n + 2)) *
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
          refine setLIntegral_mono' (measurableSet_closedBall.diff measurableSet_closedBall) ?_
          intro x hx
          have hx2 : s < ‖x - η‖ := by
            rw [← dist_eq_norm]
            have h := hx.2
            rw [mem_closedBall, not_le] at h
            exact h
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)
              ≤ ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / s ^ (n + 2) := by
                gcongr
            _ = 1 / s ^ (n + 2) * ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 := by ring
      _ = ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          mul_le_mul_right (lintegral_mono_set sdiff_subset) _
  -- Step 5: the exponential factor
  have hκs : κ * (3 * s) ≤ 3 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hκ]
  have ha_I2 := hexpb κ s _ _ _ hκ hs hκs hM2' hJ
  -- Step 6: pointwise bound on the ball `B_{3s}(η)`
  obtain ⟨M, hM_def⟩ : ∃ M : Set (Euclid (n + k)),
      M = toMeasurable μ (closedBall η (3 * s) \ F) := ⟨_, rfl⟩
  have hMmeas : MeasurableSet M := by
    rw [hM_def]
    exact measurableSet_toMeasurable _ _
  have hMsub : closedBall η (3 * s) \ F ⊆ M := by
    rw [hM_def]
    exact subset_toMeasurable _ _
  have hMmu : μ M = μ (closedBall η (3 * s) \ F) := by
    rw [hM_def]
    exact measure_toMeasurable _
  have hpt : ∀ x ∈ closedBall η (3 * s),
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
          M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
          ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
            ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro x hx
    have hxr : ‖x - η‖ ≤ 3 * s := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hx
    apply hptE T₀ (τ x) (x - η) s lam _ hxr
    by_cases hxF : x ∈ F
    · left
      exact (hF x hxF η hηF).trans (mul_le_mul_of_nonneg_left hxr hlam)
    · right
      exact Set.indicator_of_mem (hMsub ⟨hx, hxF⟩) _
  -- Step 7: integration over `B_{3s}(η)`
  have hI2 : ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
        ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
        ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
          (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
            ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ∂μ :=
          setLIntegral_mono' measurableSet_closedBall hpt
      _ = ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x) ∂μ +
          ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ :=
          lintegral_add_left ((measurable_const.indicator hMmeas).const_add _) _
      _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (M ∩ closedBall η (3 * s)) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_indicator_const hMmeas, Measure.restrict_apply hMmeas,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          have hμM : μ (M ∩ closedBall η (3 * s)) ≤ μ (closedBall η (3 * s) \ F) :=
            (measure_mono inter_subset_left).trans hMmu.le
          exact add_le_add (add_le_add le_rfl (mul_le_mul_right hμM _)) le_rfl
  -- Step 8: absorption of the `λ²`-term
  exact hfinal ω s lam _ _ _ _ hω_pos hs hlam2 ha_lower ha_upper ha_I2 hI2

/-- **Measure of the bad set** (Simon Ch. 5, proof of Lemma 2.6, (2) and (6)).  If
`μ(B_t(y)) ≤ 2ωₙtⁿ` for `y ∈ B_{3σ₀/4}(ξ)`, `t ∈ (0, 5σ₀/4]`, and
`G' = {y ∈ spt μ : ∫_{B_{t/2}(y)} e⁺ dμ ≤ a tⁿ for all t ∈ (0, σ₀/2]}`, then
`μ(B_{3σ₀/4}(ξ) \ G') ≤ (2(5/2)ⁿ/a) ωₙ ∫_{B_{σ₀}(ξ)} e⁺ dμ`.

Since `μ(ℝ^{n+k} \ spt μ) = 0`, only `A' = (B_{3σ₀/4}(ξ) \ G') ∩ spt μ` counts.  Each `y ∈ A'` has
a bad radius `t_y ∈ (0, σ₀/2]` with `a t_yⁿ < ∫_{B_{t_y/2}(y)} e⁺ dμ` (Simon's (2)), so
`μ(A' ∩ B_{5t_y/2}(y)) ≤ 2ωₙ(5t_y/2)ⁿ ≤ (2(5/2)ⁿ/a) ωₙ (μ ⌞ e⁺)(B_{t_y/2}(y))`.  The five-times
covering bound `dorag_lip_vitali_two_measure_bound`, with radii `t_y/2 ≤ σ₀/4` and
`B_{t_y/2}(y) ⊆ B_{σ₀}(ξ)`, gives the claim. -/
theorem Submission.dorag_lip_bad_set_measure_bound : ∀ (n k : ℕ) (μ : Measure (Euclid (n + k))) (e : Euclid (n + k) → ℝ) (ξ : Euclid (n + k)) (σ₀ a : ℝ), 0 < σ₀ → 0 < a → (∀ y ∈ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 4 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → μ (closedBall ξ (3 * σ₀ / 4) \ {y | y ∈ μ.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ ≤ ENNReal.ofReal (a * t ^ n)}) ≤ ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂μ := by
  intro n k μ e ξ σ₀ a hσ₀ ha hdens
  classical
  set Gs := {y | y ∈ μ.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
    ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ ≤ ENNReal.ofReal (a * t ^ n)} with hGs
  set A' := (closedBall ξ (3 * σ₀ / 4) \ Gs) ∩ μ.support with hA'
  -- Step 1: the complement of `spt μ` is `μ`-null.
  have hsplit : μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ A' := by
    calc μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ (A' ∪ μ.supportᶜ) := by
          apply measure_mono
          intro x hx
          by_cases h : x ∈ μ.support
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr h
      _ ≤ μ A' + μ μ.supportᶜ := measure_union_le _ _
      _ = μ A' := by rw [Measure.measure_compl_support, add_zero]
  -- Step 2: every point of `A'` has a bad radius `T y ∈ (0, σ₀/2]`.
  have hbad : ∀ y ∈ A', ∃ t : ℝ, 0 < t ∧ t ≤ σ₀ / 2 ∧
      ENNReal.ofReal (a * t ^ n) < ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ := by
    intro y hy
    have hyG : y ∉ Gs := hy.1.2
    simp only [hGs, Set.mem_ofPred_eq, not_and, not_forall, not_le] at hyG
    obtain ⟨t, ht, ht', hlt⟩ := hyG hy.2
    exact ⟨t, ht, ht', hlt⟩
  choose! T hT0 hTσ hTlt using hbad
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n with hc
  -- Step 3: the five-times covering bound for `μ` and `ν = μ ⌞ e⁺` with radii `T y / 2`.
  have key := Submission.dorag_lip_vitali_two_measure_bound (n + k) μ
    (μ.withDensity (fun x => ENNReal.ofReal (e x))) A' (closedBall ξ σ₀)
    (fun y => T y / 2) (σ₀ / 4) c (by
    intro y hy
    have hT0y := hT0 y hy
    have hTσy := hTσ y hy
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · intro x hx
      rw [mem_closedBall] at hx ⊢
      have := dist_triangle x y ξ
      have hyξ := mem_closedBall.1 hy.1.1
      linarith
    · calc μ (A' ∩ closedBall y (5 * (T y / 2))) ≤ μ (closedBall y (5 * (T y / 2))) :=
            measure_mono inter_subset_right
        _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * (T y / 2)) ^ n) :=
            hdens y hy.1.1 _ (by linarith) (by linarith)
        _ = c * ENNReal.ofReal (a * T y ^ n) := by
            have hreal : 2 * (5 / 2) ^ n / a * (a * T y ^ n) = 2 * (5 * (T y / 2)) ^ n := by
              field_simp
              ring
            have h2 : ENNReal.ofReal (2 * (5 / 2) ^ n / a) * ENNReal.ofReal (a * T y ^ n) =
                2 * ENNReal.ofReal ((5 * (T y / 2)) ^ n) := by
              rw [← ENNReal.ofReal_mul (by positivity), hreal, ENNReal.ofReal_mul (by norm_num),
                ENNReal.ofReal_ofNat]
            rw [hc]
            calc 2 * unitBallVolume n * ENNReal.ofReal ((5 * (T y / 2)) ^ n)
                = unitBallVolume n * (2 * ENNReal.ofReal ((5 * (T y / 2)) ^ n)) := by ring
              _ = unitBallVolume n * (ENNReal.ofReal (2 * (5 / 2) ^ n / a) *
                    ENNReal.ofReal (a * T y ^ n)) := by rw [h2]
              _ = ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n *
                    ENNReal.ofReal (a * T y ^ n) := by ring
        _ ≤ c * ∫⁻ x in closedBall y (T y / 2), ENNReal.ofReal (e x) ∂μ := by
            gcongr
            exact (hTlt y hy).le
        _ = c * (μ.withDensity fun x => ENNReal.ofReal (e x)) (closedBall y (T y / 2)) := by
            rw [withDensity_apply _ measurableSet_closedBall])
  -- Step 4: `ν(B_{σ₀}(ξ)) = ∫_{B_{σ₀}(ξ)} e⁺ dμ`.
  calc μ (closedBall ξ (3 * σ₀ / 4) \ Gs) ≤ μ A' := hsplit
    _ ≤ c * (μ.withDensity fun x => ENNReal.ofReal (e x)) (closedBall ξ σ₀) := key
    _ = _ := by rw [withDensity_apply _ measurableSet_closedBall]

/-- **`Hⁿ`-measure of the graph off the support** (Simon Ch. 5, proof of Lemma 2.6, the estimate
after (10) via the covering (11), with the balls `B_{3s}(η)`).  Let `A ⊆ F`, let
`Hⁿ(F ∩ B_r(η)) ≤ K rⁿ` for `η ∈ A` and `r > 0`, and let every `η ∈ A` have a radius
`0 < s_η ≤ R₀` with `B_{3s_η}(η) ⊆ B` and `s_ηⁿ ≤ C₉ (μ(B_{3s_η}(η) ∖ F) + ∫_{B_{3s_η}(η)} e⁺ dμ)`.
The comparison measure `ν = μ⌞Fᶜ + μ.withDensity e⁺` has `ν(S) = μ(S ∖ F) + ∫_S e⁺ dμ` for
measurable `S`.  The growth bound at radius `15s_η = 5 · 3s_η` gives
`Hⁿ(A ∩ B_{5·3s_η}(η)) ≤ K 15ⁿ C₉ ν(B_{3s_η}(η))`, and the two-measure Vitali bound with the
radii `3s_η` gives `Hⁿ(A) ≤ K 15ⁿ C₉ ν(B)`. -/
theorem Submission.dorag_lip_graph_hole_measure_bound : ∀ (n k : ℕ) (μ : Measure (Euclid (n + k))) (e : Euclid (n + k) → ℝ) (F A B : Set (Euclid (n + k))) (K : ℝ≥0∞) (C₉ R₀ : ℝ), MeasurableSet B → A ⊆ F → (∀ η ∈ A, ∀ r : ℝ, 0 < r → μHE[n] (F ∩ closedBall η r) ≤ K * ENNReal.ofReal (r ^ n)) → (∀ η ∈ A, ∃ s : ℝ, 0 < s ∧ s ≤ R₀ ∧ closedBall η (3 * s) ⊆ B ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (e x) ∂μ)) → μHE[n] A ≤ K * ENNReal.ofReal (15 ^ n * C₉) * (μ (B \ F) + ∫⁻ x in B, ENNReal.ofReal (e x) ∂μ) := by
  intro n k μ e F A B K C₉ R₀ hB hAF hball hrad
  -- Step 1: the radii `r(η) = 3s_η`
  choose! s hs0 hsR hsB hsineq using hrad
  -- Step 2: the comparison measure `ν = μ⌞Fᶜ + μ.withDensity e⁺` (`F` need not be measurable)
  set ν : Measure (Euclid (n + k)) :=
    μ.restrict Fᶜ + μ.withDensity (fun x => ENNReal.ofReal (e x)) with hν
  have hνS : ∀ S : Set (Euclid (n + k)), MeasurableSet S →
      ν S = μ (S \ F) + ∫⁻ x in S, ENNReal.ofReal (e x) ∂μ := by
    intro S hS
    rw [hν, Measure.add_apply, Measure.restrict_apply hS, withDensity_apply _ hS, Set.sdiff_eq]
  -- Step 4: the two-measure Vitali bound gives `Hⁿ(A) ≤ K 15ⁿ C₉ ν(B)`
  rw [← hνS B hB]
  refine Submission.dorag_lip_vitali_two_measure_bound (n + k) μHE[n] ν A B (fun η => 3 * s η)
    (3 * R₀) (K * ENNReal.ofReal (15 ^ n * C₉)) fun η hη => ?_
  -- Step 3: its hypotheses at `η ∈ A`
  have hs0η := hs0 η hη
  refine ⟨by linarith, by linarith [hsR η hη], hsB η hη, ?_⟩
  calc μHE[n] (A ∩ closedBall η (5 * (3 * s η)))
      ≤ μHE[n] (F ∩ closedBall η (15 * s η)) :=
        measure_mono (Set.inter_subset_inter hAF (closedBall_subset_closedBall (by linarith)))
    _ ≤ K * ENNReal.ofReal ((15 * s η) ^ n) := hball η hη _ (by linarith)
    _ = K * ENNReal.ofReal (15 ^ n) * ENNReal.ofReal (s η ^ n) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
    _ ≤ K * ENNReal.ofReal (15 ^ n) * (ENNReal.ofReal C₉ * (μ (closedBall η (3 * s η) \ F) +
          ∫⁻ x in closedBall η (3 * s η), ENNReal.ofReal (e x) ∂μ)) := by
        gcongr
        exact hsineq η hη
    _ = K * ENNReal.ofReal (15 ^ n * C₉) * ν (closedBall η (3 * s η)) := by
        rw [hνS _ measurableSet_closedBall, ENNReal.ofReal_mul (by positivity)]
        ring
/-- **Finite separated net** (Simon Ch. 5, proof of Lemma 2.5, (2)–(3)).  Let `0 < s`, `0 < a`,
`μ(A) < ∞`, and let every `y ∈ K` satisfy `B̄_{s/2}(y) ⊆ A` and `a ≤ μ(B̄_{s/2}(y))`.  If the points
of a finite `G ⊆ K` are pairwise more than `s` apart, the balls `B̄_{s/2}(y)`, `y ∈ G`, are disjoint
subsets of `A`, so `#G · a ≤ μ(A)`; since `μ(A) < N₀ a` for some `N₀ ∈ ℕ`, `#G < N₀`.  Such a `G` of
the greatest cardinality (`Nat.findGreatest`) is an `s`-net of `K`: a point of `K` more than `s`
from every point of `G` could be added to `G`. -/
theorem Submission.dorag_aa_finite_separated_net : ∀ (P : ℕ) (μ : Measure (Euclid P)) (K A : Set (Euclid P)) (s : ℝ) (a : ℝ≥0∞), 0 < s → 0 < a → μ A ≠ ∞ → (∀ y ∈ K, closedBall y (s / 2) ⊆ A) → (∀ y ∈ K, a ≤ μ (closedBall y (s / 2))) → ∃ F : Finset (Euclid P), (↑F : Set (Euclid P)) ⊆ K ∧ (F.card : ℝ≥0∞) * a ≤ μ A ∧ ∀ x ∈ K, ∃ y ∈ F, dist x y ≤ s := by
  intro P μ K A s a hs ha hA hKA hKa
  classical
  -- if the points of a finite `G ⊆ K` are pairwise more than `s` apart, the balls `B̄_{s/2}(y)`,
  -- `y ∈ G`, are disjoint, have measure `≥ a` and lie in `A`, so `#G · a ≤ μ(A)`
  have hcount : ∀ G : Finset (Euclid P), (↑G : Set (Euclid P)) ⊆ K →
      (↑G : Set (Euclid P)).Pairwise (fun y y' => s < dist y y') → (G.card : ℝ≥0∞) * a ≤ μ A := by
    intro G hGK hG
    have hdisj : (↑G : Set (Euclid P)).PairwiseDisjoint fun y => closedBall y (s / 2) := by
      intro y hy y' hy' hne
      have h1 : s < dist y y' := hG hy hy' hne
      refine Set.disjoint_left.mpr fun w hw hw' => ?_
      have h2 : dist w y ≤ s / 2 := hw
      have h3 : dist w y' ≤ s / 2 := hw'
      linarith [dist_triangle_left y y' w]
    calc (G.card : ℝ≥0∞) * a = ∑ y ∈ G, a := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ G, μ (closedBall y (s / 2)) := Finset.sum_le_sum fun y hy => hKa y (hGK hy)
      _ = μ (⋃ y ∈ G, closedBall y (s / 2)) :=
        (measure_biUnion_finset hdisj fun y _ => measurableSet_closedBall).symm
      _ ≤ μ A := measure_mono (iUnion₂_subset fun y hy => hKA y (hGK hy))
  -- `μ(A) < N₀ · a`, so such a `G` has fewer than `N₀` points
  obtain ⟨N₀, hN₀⟩ := ENNReal.exists_nat_mul_gt ha.ne' hA
  have hlt : ∀ G : Finset (Euclid P), (↑G : Set (Euclid P)) ⊆ K →
      (↑G : Set (Euclid P)).Pairwise (fun y y' => s < dist y y') → G.card < N₀ := by
    intro G hGK hG
    by_contra h
    have hN : (N₀ : ℝ≥0∞) * a ≤ G.card * a := by gcongr; exact_mod_cast not_lt.mp h
    exact (hN₀.trans_le (hN.trans (hcount G hGK hG))).false
  -- `F`: such a set of the greatest cardinality `m ≤ N₀`
  obtain ⟨F, hFK, hF, hFmax⟩ : ∃ F : Finset (Euclid P), (↑F : Set (Euclid P)) ⊆ K ∧
      (↑F : Set (Euclid P)).Pairwise (fun y y' => s < dist y y') ∧
      ∀ G : Finset (Euclid P), (↑G : Set (Euclid P)) ⊆ K →
        (↑G : Set (Euclid P)).Pairwise (fun y y' => s < dist y y') → G.card ≤ F.card := by
    obtain ⟨F, hFK, hF, hFm⟩ := Nat.findGreatest_spec (P := fun m => ∃ G : Finset (Euclid P),
      (↑G : Set (Euclid P)) ⊆ K ∧ (↑G : Set (Euclid P)).Pairwise (fun y y' => s < dist y y') ∧
        G.card = m) (Nat.zero_le N₀) ⟨∅, by simp, by simp, rfl⟩
    refine ⟨F, hFK, hF, fun G hGK hG => ?_⟩
    rw [hFm]
    exact Nat.le_findGreatest (hlt G hGK hG).le ⟨G, hGK, hG, rfl⟩
  refine ⟨F, hFK, hcount F hFK hF, fun x hx => ?_⟩
  -- a point `x ∈ K` more than `s` from every point of `F` would give the larger set `F ∪ {x}`
  by_contra hfar'
  have hfar : ∀ y ∈ F, s < dist x y := fun y hy => not_le.mp fun h => hfar' ⟨y, hy, h⟩
  have hxF : x ∉ F := fun h => by
    have h1 := hfar x h
    rw [dist_self] at h1
    linarith
  have hK' : (↑(insert x F) : Set (Euclid P)) ⊆ K := by
    rw [Finset.coe_insert]
    exact insert_subset hx hFK
  have hG' : (↑(insert x F) : Set (Euclid P)).Pairwise (fun y y' => s < dist y y') := by
    rw [Finset.coe_insert]
    exact hF.insert fun y hy _ => ⟨hfar y hy, by rw [dist_comm]; exact hfar y hy⟩
  have hle := hFmax _ hK' hG'
  rw [Finset.card_insert_of_notMem hxF] at hle
  omega
/-- **Explicit constants for the standing density bounds** (Simon Ch. 5, 2.3–2.4,
chapter-05.txt lines 266–288, where `δ ≤ δ₀(n)` gives `1 + Cδ ≤ 2`).  Take `δ₁ = 1/(24(n + 1))`
and `C₁ = 4 + 12n`, so `0 < δ₁ ≤ 1/8` and `C₁δ₁ ≤ 1/2`.  For `0 ≤ δ ≤ δ₁`: `e^δ ≤ 1 + 2δ` (from
`1 − δ ≤ e^{−δ}`), and Bernoulli `(1 − 4δ)ⁿ ≥ 1 − 4nδ` with `8nδ ≤ 1/3` gives
`(1 − 4δ)^{−n} ≤ 1 + 8nδ`; hence
`e^δ(1 + δ)/(1 − 4δ)ⁿ ≤ (1 + 2δ)(1 + δ)(1 + 8nδ) ≤ (1 + 4δ)(1 + 8nδ) ≤ 1 + C₁δ`. -/
theorem Submission.dorag_dbs_density_constants : ∀ n : ℕ, ∃ δ₁ C₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 8 ∧ 0 < C₁ ∧ C₁ * δ₁ ≤ 1 / 2 ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ δ₁ → Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 1 + C₁ * δ := by
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Steps 1–2: `δ₁ = 1/(24(n + 1))` and `C₁ = 4 + 12n`.
  refine ⟨1 / (24 * (n + 1)), 4 + 12 * n, by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · -- Step 3: `δ ≤ 1/24` and `nδ ≤ 1/24`.
    intro δ hδ0 hδ1
    have hpos : (0 : ℝ) < 24 * (n + 1) := by positivity
    have hδ' : δ * (24 * (n + 1)) ≤ 1 := (le_div_iff₀ hpos).mp hδ1
    have hδ24 : δ ≤ 1 / 24 := by nlinarith
    have hnδ : n * δ ≤ 1 / 24 := by nlinarith
    have hnδ0 : 0 ≤ (n : ℝ) * δ := mul_nonneg hn0 hδ0
    -- Step 4: `e^δ ≤ 1 + 2δ`, from `1 − δ ≤ e^{−δ}` and `e^δ e^{−δ} = 1`.
    have hexp : Real.exp δ ≤ 1 + 2 * δ := by
      have hlow := Real.add_one_le_exp (-δ)
      have hprod : Real.exp δ * Real.exp (-δ) = 1 := by rw [← Real.exp_add]; simp
      have hepos := Real.exp_pos δ
      nlinarith
    -- Step 5: Bernoulli `(1 − 4δ)ⁿ ≥ 1 − 4nδ`, hence `1/(1 − 4δ)ⁿ ≤ 1 + 8nδ`.
    have hbern : 1 + (n : ℝ) * (-4 * δ) ≤ (1 + (-4 * δ)) ^ n :=
      one_add_mul_le_pow (by linarith) n
    have hA : 1 + (n : ℝ) * (-4 * δ) = 1 - 4 * n * δ := by ring
    have hB : (1 + (-4 * δ)) = 1 - 4 * δ := by ring
    rw [hA, hB] at hbern
    have hden_pos : 0 < (1 - 4 * δ) ^ n := pow_pos (by linarith) n
    have h8 : 0 ≤ 1 + 8 * n * δ := by positivity
    have hden : 1 ≤ (1 + 8 * n * δ) * (1 - 4 * δ) ^ n := by
      have h1 : (1 + 8 * n * δ) * (1 - 4 * n * δ) ≤ (1 + 8 * n * δ) * (1 - 4 * δ) ^ n :=
        mul_le_mul_of_nonneg_left hbern h8
      have h2 : 1 ≤ (1 + 8 * n * δ) * (1 - 4 * n * δ) := by
        nlinarith [mul_nonneg hnδ0 (by linarith : (0 : ℝ) ≤ 1 - 8 * n * δ)]
      linarith
    have hinv : 1 / (1 - 4 * δ) ^ n ≤ 1 + 8 * n * δ := by
      rw [div_le_iff₀ hden_pos]; linarith
    -- Step 6: multiply the three factor bounds.
    have hq1 : (1 + 2 * δ) * (1 + δ) ≤ 1 + 4 * δ := by nlinarith
    have hq2 : (1 + 4 * δ) * (1 + 8 * n * δ) ≤ 1 + (4 + 12 * n) * δ := by
      nlinarith [mul_nonneg hnδ0 (by linarith : (0 : ℝ) ≤ 1 - 8 * δ)]
    calc Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n
        = Real.exp δ * (1 + δ) * (1 / (1 - 4 * δ) ^ n) := by ring
      _ ≤ (1 + 2 * δ) * (1 + δ) * (1 + 8 * n * δ) := by
          apply mul_le_mul _ hinv (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hexp (by linarith)
      _ ≤ (1 + 4 * δ) * (1 + 8 * n * δ) := mul_le_mul_of_nonneg_right hq1 h8
      _ ≤ 1 + (4 + 12 * n) * δ := hq2
/-- **Sharp mass ratio on the standing balls** (Simon Ch. 5, 2.4, chapter-05.txt lines 278–288,
with the radii `4δρ`, `(1 − 4δ)ρ` and an exact constant).  Put `t' = (1 − 4δ)ρ ∈ (0, ρ]`.  For
`|y − z| ≤ 4δρ` the triangle inequality gives `B_{t'}(y) ⊆ B_ρ(z) ⊆ W`, and `κt' ≤ κρ ≤ δ`, so
`e^{κt'} t'^{−n} μ(B_{t'}(y)) ≤ e^δ t'^{−n} (1 + δ) ωₙ ρⁿ = K ωₙ`, `K = e^δ(1 + δ)/(1 − 4δ)ⁿ`.
The monotonicity hypothesis (Simon Ch. 4, 4.7–4.8, chapter-04.txt lines 536–546) carries this to
every `t ∈ (0, t']`, and `e^{κt} ≥ 1` then gives `μ(B_t(y)) ≤ K ωₙ tⁿ`. -/
theorem Submission.dorag_dbs_sharp_mass_ratio : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (W : Set (Euclid P)) (κ δ ρ : ℝ) (z : Euclid P), 0 < ρ → 0 ≤ δ → δ ≤ 1 / 8 → 0 ≤ κ → κ * ρ ≤ δ → closedBall z ρ ⊆ W → μ (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → (∀ (y : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * μ (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t)) → ∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n ∧ μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n * ENNReal.ofReal (t ^ n) := by
  intro P n μ W κ δ ρ z hρ hδ0 hδ8 hκ hκρ hball hmass hmono y hy t ht htle
  -- Step 1: `t' = (1 − 4δ)ρ ∈ (0, ρ]`.
  set t' := (1 - 4 * δ) * ρ with ht'_def
  have h14 : 0 < 1 - 4 * δ := by linarith
  have ht'pos : 0 < t' := mul_pos h14 hρ
  have ht'ρ : t' ≤ ρ := by nlinarith
  -- Step 2: `B_{t'}(y) ⊆ B_ρ(z)`.
  have hsub : closedBall y t' ⊆ closedBall z ρ := by
    intro p hp
    rw [mem_closedBall] at hp hy ⊢
    calc dist p z ≤ dist p y + dist y z := dist_triangle p y z
      _ ≤ t' + 4 * δ * ρ := add_le_add hp hy
      _ = ρ := by rw [ht'_def]; ring
  -- Step 3: the normalized mass at the radius `t'`.
  have hstep3 : ENNReal.ofReal (Real.exp (κ * t') / t' ^ n) * μ (closedBall y t') ≤
      ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n := by
    have ht'n : 0 < t' ^ n := pow_pos ht'pos n
    have he : Real.exp (κ * t') / t' ^ n ≤ Real.exp δ / t' ^ n := by
      apply div_le_div_of_nonneg_right _ ht'n.le
      apply Real.exp_le_exp.mpr
      calc κ * t' ≤ κ * ρ := mul_le_mul_of_nonneg_left ht'ρ hκ
        _ ≤ δ := hκρ
    calc ENNReal.ofReal (Real.exp (κ * t') / t' ^ n) * μ (closedBall y t')
        ≤ ENNReal.ofReal (Real.exp δ / t' ^ n) * μ (closedBall z ρ) := by
          gcongr
      _ ≤ ENNReal.ofReal (Real.exp δ / t' ^ n) *
            (ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp δ / t' ^ n * (1 + δ) * ρ ^ n) * unitBallVolume n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
          ring
      _ = ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n := by
          congr 2
          rw [ht'_def, mul_pow]
          field_simp
  -- Step 4: monotonicity carries the bound to every `t ∈ (0, t']`.
  have hi : ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t) ≤
      ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n := by
    rcases lt_or_eq_of_le htle with hlt | heq
    · exact (hmono y t t' ht hlt (hsub.trans hball)).trans hstep3
    · rw [heq]; exact hstep3
  refine ⟨hi, ?_⟩
  -- Step 5: `e^{κt} ≥ 1` turns the normalized bound into `μ(B_t(y)) ≤ K ωₙ tⁿ`.
  have htn : 0 < t ^ n := pow_pos ht n
  have hexp1 : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (mul_nonneg hκ ht.le)
  have hfac : ENNReal.ofReal (t ^ n / Real.exp (κ * t)) *
      ENNReal.ofReal (Real.exp (κ * t) / t ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [show t ^ n / Real.exp (κ * t) * (Real.exp (κ * t) / t ^ n) = 1 by field_simp]
    simp
  have hle : ENNReal.ofReal (t ^ n / Real.exp (κ * t)) ≤ ENNReal.ofReal (t ^ n) :=
    ENNReal.ofReal_le_ofReal (div_le_self htn.le hexp1)
  calc μ (closedBall y t)
      = ENNReal.ofReal (t ^ n / Real.exp (κ * t)) *
          (ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * μ (closedBall y t)) := by
        rw [← mul_assoc, hfac, one_mul]
    _ ≤ ENNReal.ofReal (t ^ n / Real.exp (κ * t)) *
          (ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n) := by
        gcongr
    _ ≤ ENNReal.ofReal (t ^ n) *
          (ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n *
          ENNReal.ofReal (t ^ n) := by ring
/-- Lower density of `Hⁿ⌞M` at an approximate tangent point (Simon Ch. 3, Definition 1.4 and
Remark 1.5(3)): if `Q` is an approximate tangent space of `M` at `x` (`dim Q = n ≥ 1`), then
`c ωₙ tⁿ ≤ Hⁿ(M ∩ B_t(x))` for every `c < 1` and all small `t > 0`.  For `0 < c < 1` fix `ε > 0`
with `c (1 + ε)ⁿ < 1`.  The cutoff `ψ = max(0, min(1, (1 + ε − |y|)/ε))` satisfies
`1_{B₁(0)} ≤ ψ ≤ 1_{B_{1+ε}(0)}`, so `∫_Q ψ dHⁿ ≥ Hⁿ(Q ∩ B₁(0)) = ωₙ`.  The blow-up integrals
`∫_{η_{x,r}(M)} ψ dHⁿ` tend to `∫_Q ψ dHⁿ` and are at most `r⁻ⁿ Hⁿ(M ∩ B_{r(1+ε)}(x))` by
scaling; taking `t = r(1 + ε)` gives the bound. -/
theorem Submission.dorag_dbs_approxTangent_lower_density : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → HasApproximateTangentSpaceAt n M x Q → ∀ c : ℝ, c < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ μHE[n] (M ∩ closedBall x t) := by
  intro P n M x Q hn hQ c hc
  by_cases hc0 : c ≤ 0
  · filter_upwards with t
    simp [ENNReal.ofReal_of_nonpos hc0]
  push Not at hc0
  obtain ⟨hfin, hconv⟩ := hQ
  -- the unit-ball volume
  have hω0 : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have hωr : 0 < (unitBallVolume n).toReal := ENNReal.toReal_pos hω0 hωtop
  -- Step 5(a): the plane ball has measure ω_n
  have hQball : (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 1) = unitBallVolume n := by
    have : Nontrivial Q := Module.nontrivial_of_finrank_pos (hfin.symm ▸ hn)
    have hrange : Set.range (Q.subtypeₗᵢ : Q → Euclid P) = (Q : Set (Euclid P)) := by
      ext y; simp
    rw [← hrange, ← Q.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
      Measure.map_apply Q.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
    have hpre : (Q.subtypeₗᵢ : Q → Euclid P) ⁻¹' closedBall (0 : Euclid P) 1 =
        closedBall (0 : Q) 1 := by
      ext y; simp [mem_closedBall, dist_eq_norm]
    have hvol : (μHE[n] : Measure Q) = volume := by
      rw [← hfin]; exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [hpre, hvol, Measure.addHaar_closedBall_eq_addHaar_ball]
    rw [← hfin]
    unfold unitBallVolume
    let e := (stdOrthonormalBasis ℝ Q).repr
    have hmp : MeasurePreserving e volume volume := e.measurePreserving
    rw [← hmp.measure_preimage measurableSet_ball.nullMeasurableSet]
    congr 1
    ext y
    simp [e, mem_ball, dist_eq_norm]
  -- choice of ε
  have hεlim : Tendsto (fun ε : ℝ => c * (1 + ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa only [id_eq, add_zero, one_pow, mul_one] using
      ((hone.add (tendsto_id.mono_left inf_le_left :
        Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0))).pow n).const_mul c
  obtain ⟨ε, hεc, hε⟩ :=
    ((hεlim.eventually (gt_mem_nhds hc)).and self_mem_nhdsWithin).exists
  have hε0 : 0 < ε := hε
  have hA : 0 < 1 + ε := by linarith
  -- the cutoff ψ
  let ψf : Euclid P → ℝ := fun y => max 0 (min 1 ((1 + ε - ‖y‖) / ε))
  have hψcont : Continuous ψf := by
    apply continuous_const.max
    apply continuous_const.min
    exact (continuous_const.sub continuous_norm).div_const ε
  have hψ0 : ∀ y, y ∉ closedBall (0 : Euclid P) (1 + ε) → ψf y = 0 := by
    intro y hy
    have hy' : 1 + ε < ‖y‖ := by simpa [mem_closedBall, dist_eq_norm] using hy
    have hneg : (1 + ε - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε0
    simp only [ψf]
    exact max_eq_left ((min_le_right _ _).trans hneg.le)
  have hψsupp : HasCompactSupport ψf :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) (1 + ε)) hψ0
  let ψ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    { toFun := ψf, continuous_toFun := hψcont, hasCompactSupport' := hψsupp }
  have hψapp : ∀ y, ψ y = ψf y := fun _ => rfl
  have hψ01 : ∀ y, 0 ≤ ψf y ∧ ψf y ≤ 1 := by
    intro y
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hψ1 : ∀ y ∈ closedBall (0 : Euclid P) 1, ψf y = 1 := by
    intro y hy
    have hy' : ‖y‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hy
    have h1 : 1 ≤ (1 + ε - ‖y‖) / ε := by
      rw [le_div_iff₀ hε0]; linarith
    simp only [ψf]
    rw [min_eq_left h1]
    exact max_eq_right zero_le_one
  -- Step 5: the plane integral is at least ω_n
  have hplane : (unitBallVolume n).toReal ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hfin
    have hint : Integrable ψ (μHE[n].restrict (Q : Set (Euclid P))) :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hle := setIntegral_le_integral (s := closedBall (0 : Euclid P) 1) hint
      (Eventually.of_forall (fun y => (hψ01 y).1))
    have heq : ∫ y in closedBall (0 : Euclid P) 1, ψ y ∂(μHE[n].restrict (Q : Set (Euclid P))) =
        (unitBallVolume n).toReal := by
      have hcongr : ∫ y in closedBall (0 : Euclid P) 1, ψ y ∂(μHE[n].restrict (Q : Set (Euclid P))) =
          ∫ _ in closedBall (0 : Euclid P) 1, (1 : ℝ) ∂(μHE[n].restrict (Q : Set (Euclid P))) :=
        setIntegral_congr_fun measurableSet_closedBall (fun y hy => by rw [hψapp]; exact hψ1 y hy)
      rw [hcongr]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
        Measure.restrict_apply_univ, hQball]
    rw [heq] at hle
    exact hle
  -- Step 6: eventually the blow-up integrals exceed c (1+ε)^n ω_n
  have hgap : c * (1 + ε) ^ n * (unitBallVolume n).toReal <
      ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have : c * (1 + ε) ^ n * (unitBallVolume n).toReal < (unitBallVolume n).toReal := by
      nlinarith
    linarith
  have hev := (hconv ψ).eventually (lt_mem_nhds hgap)
  -- Step 8: scaling of the blow-up
  have hscale : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) =
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] S := by
    intro r hr S
    have hshift : Isometry (fun y : Euclid P => y - x) := by
      apply Isometry.of_dist_eq
      intro a b
      simp only [dist_eq_norm]
      congr 1
      abel
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        AffineMap.homothety (0 : Euclid P) r⁻¹ '' ((fun y : Euclid P => y - x) '' S) := by
      rw [← image_comp]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Euclid P) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image]
    simp only [ENNReal.smul_def, ENNReal.coe_pow, smul_eq_mul]
    congr 2
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hinter : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (closedBall x (r * (1 + ε)) ∩ S) =
        closedBall (0 : Euclid P) (1 + ε) ∩ (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) := by
    intro r hr S
    have hmem : ∀ y : Euclid P, Poincare.SimonGMT.Chapter03.blowUpMap x r y ∈
        closedBall (0 : Euclid P) (1 + ε) ↔ y ∈ closedBall x (r * (1 + ε)) := by
      intro y
      simp only [mem_closedBall, dist_eq_norm, sub_zero, Poincare.SimonGMT.Chapter03.blowUpMap,
        norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      rw [← div_eq_inv_mul, div_le_iff₀ hr, mul_comm r (1 + ε)]
    ext y
    constructor
    · rintro ⟨z, ⟨hzB, hzS⟩, rfl⟩
      exact ⟨(hmem z).mpr hzB, mem_image_of_mem _ hzS⟩
    · rintro ⟨hyB, z, hzS, rfl⟩
      exact ⟨z, ⟨(hmem z).mp hyB, hzS⟩, rfl⟩
  -- Step 7: upper bound for the blow-up integrals
  have hup : ∀ r : ℝ, 0 < r → μHE[n] (M ∩ closedBall x (r * (1 + ε))) ≠ ∞ →
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]) ≤
        (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x (r * (1 + ε)))).toReal := by
    intro r hr hfinM
    have hνB : (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        (closedBall (0 : Euclid P) (1 + ε)) =
          ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * (1 + ε))) := by
      rw [Measure.restrict_apply measurableSet_closedBall, ← hinter r hr M, hscale r hr,
        inter_comm]
    have hνfin : (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        (closedBall (0 : Euclid P) (1 + ε)) < ∞ := by
      rw [hνB]
      exact ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top hfinM.lt_top
    have hnorm := norm_setIntegral_le_of_norm_le_const_ae (f := fun y => ψ y) hνfin
      (Eventually.of_forall (fun y => show ‖ψ y‖ ≤ 1 by
        rw [hψapp, Real.norm_of_nonneg (hψ01 y).1]
        exact (hψ01 y).2))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hψapp]; exact hψ0 y hy),
      one_mul] at hnorm
    calc (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n])
        ≤ ‖∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]‖ := le_abs_self _
      _ ≤ _ := hnorm
      _ = (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x (r * (1 + ε)))).toReal := by
        rw [measureReal_def, hνB, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (inv_pos.mpr hr).le]
  -- Step 9: conclusion with r = t / (1 + ε)
  have hrA : Tendsto (fun t : ℝ => t / (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, id_eq] using
        (tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).div_const (1 + ε)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos ht hA
  filter_upwards [hrA.eventually hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : 0 < t := htpos
  have hr : 0 < t / (1 + ε) := div_pos htpos' hA
  have hrA' : t / (1 + ε) * (1 + ε) = t := div_mul_cancel₀ _ hA.ne'
  by_cases hH : μHE[n] (M ∩ closedBall x t) = ∞
  · rw [hH]; exact le_top
  have hb := hup (t / (1 + ε)) hr (by rwa [hrA'])
  rw [hrA'] at hb
  have h1 : c * (1 + ε) ^ n * (unitBallVolume n).toReal <
      ((t / (1 + ε))⁻¹) ^ n * (μHE[n] (M ∩ closedBall x t)).toReal := lt_of_lt_of_le ht hb
  have hrn : 0 < (t / (1 + ε)) ^ n := pow_pos hr n
  have h2 : ((t / (1 + ε))⁻¹) ^ n * (t / (1 + ε)) ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  have h3 : (1 + ε) ^ n * (t / (1 + ε)) ^ n = t ^ n := by
    rw [← mul_pow, mul_comm, hrA']
  have hreal : c * (unitBallVolume n).toReal * t ^ n ≤ (μHE[n] (M ∩ closedBall x t)).toReal := by
    have h4 := mul_lt_mul_of_pos_right h1 hrn
    calc c * (unitBallVolume n).toReal * t ^ n
        = c * (1 + ε) ^ n * (unitBallVolume n).toReal * (t / (1 + ε)) ^ n := by
          rw [← h3]; ring
      _ ≤ ((t / (1 + ε))⁻¹) ^ n * (μHE[n] (M ∩ closedBall x t)).toReal * (t / (1 + ε)) ^ n :=
          h4.le
      _ = (μHE[n] (M ∩ closedBall x t)).toReal := by
          rw [mul_right_comm, h2, one_mul]
  calc ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n)
      = ENNReal.ofReal (c * (unitBallVolume n).toReal * t ^ n) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc0.le,
          ENNReal.ofReal_toReal hωtop]
    _ ≤ ENNReal.ofReal (μHE[n] (M ∩ closedBall x t)).toReal := ENNReal.ofReal_le_ofReal hreal
    _ = μHE[n] (M ∩ closedBall x t) := ENNReal.ofReal_toReal hH
/-- **Localized Besicovitch density theorem** (Simon Ch. 1, 3.16 with Remark 3.7(2)): if `ν` is
finite on compact subsets of the open set `W` and `s` is measurable, then `ν⌞s`-a.e. `x ∈ W` has
`a · ν(B_t(x)) ≤ ν(s ∩ B_t(x))` for every `a < 1` and all small `t > 0`.  `W` is covered by
countably many open balls `B̆_{rᵢ}(i)` with `B_{2rᵢ}(i) ⊆ W` compact; on each, Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div` for the finite measure `ν⌞B_{2rᵢ}(i)` gives
`ν(s ∩ B_t(x)) / ν(B_t(x)) → 1` for `ν⌞s`-a.e. `x ∈ B̆_{rᵢ}(i)`, and the countable union
(`ae_ball_iff`) gives the claim. -/
theorem Submission.dorag_dbs_localized_density_point : ∀ (P : ℕ) (W s : Set (Euclid P)) (ν : Measure (Euclid P)), IsOpen W → MeasurableSet s → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → ν K ≠ ∞) → ∀ᵐ x ∂ν.restrict s, x ∈ W → ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t) := by
  intro P W s ν hW hs hfin
  -- radii: closedBall x (2 r) ⊆ W
  have hr : ∀ x : W, ∃ r : ℝ, 0 < r ∧ closedBall (x : Euclid P) (2 * r) ⊆ W := by
    intro x
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x x.2
    exact ⟨ε / 3, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  choose r hr0 hrW using hr
  -- countable subcover of W by the balls ball x (r x)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : W => ball (x : Euclid P) (r x)) (fun _ => isOpen_ball)
  have hcover : ∀ x ∈ W, ∃ i ∈ T, x ∈ ball (i : Euclid P) (r i) := by
    intro x hx
    have hmem : x ∈ ⋃ i : W, ball (i : Euclid P) (r i) :=
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr0 _)⟩
    rw [← hTU] at hmem
    simpa only [mem_iUnion, exists_prop] using hmem
  -- the local statement on each ball
  have hloc : ∀ i : W, ∀ᵐ x ∂ν.restrict s, x ∈ ball (i : Euclid P) (r i) →
      ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t) := by
    intro i
    have hKm : MeasurableSet (closedBall (i : Euclid P) (2 * r i)) := measurableSet_closedBall
    have hKfin : ν (closedBall (i : Euclid P) (2 * r i)) ≠ ∞ :=
      hfin _ (isCompact_closedBall _ _) (hrW i)
    have : IsFiniteMeasure (ν.restrict (closedBall (i : Euclid P) (2 * r i))) :=
      isFiniteMeasure_restrict.mpr hKfin
    have hB := Besicovitch.ae_tendsto_measure_inter_div
      (ν.restrict (closedBall (i : Euclid P) (2 * r i))) s
    have heq : (ν.restrict (closedBall (i : Euclid P) (2 * r i))).restrict s =
        (ν.restrict s).restrict (closedBall (i : Euclid P) (2 * r i)) := by
      rw [Measure.restrict_restrict hs, Measure.restrict_restrict hKm, inter_comm]
    rw [heq, ae_restrict_iff' hKm] at hB
    filter_upwards [hB] with x hx hxV a ha
    have hxd : dist x i < r i := mem_ball.mp hxV
    have hxK : x ∈ closedBall (i : Euclid P) (2 * r i) := by
      rw [mem_closedBall]; linarith [hr0 i]
    have hlim := hx hxK
    by_cases ha0 : a ≤ 0
    · filter_upwards with t
      simp [ENNReal.ofReal_of_nonpos ha0]
    have hlt : ENNReal.ofReal a < 1 := ENNReal.ofReal_lt_one.mpr ha
    have ht0 : (0 : ℝ) < r i - dist x i := by linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hlt), Ioo_mem_nhdsGT ht0] with t ht hti
    have hBK : closedBall x t ⊆ closedBall (i : Euclid P) (2 * r i) := by
      intro p hp
      rw [mem_closedBall] at hp ⊢
      calc dist p i ≤ dist p x + dist x i := dist_triangle _ _ _
        _ ≤ 2 * r i := by linarith [hti.2, hr0 i]
    rw [Measure.restrict_apply' hKm, Measure.restrict_apply' hKm,
      inter_eq_left.mpr hBK, inter_eq_left.mpr (inter_subset_right.trans hBK)] at ht
    by_cases hB0 : ν (closedBall x t) = 0
    · simp [hB0]
    have hBtop : ν (closedBall x t) ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hBK)
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp ht).le
  -- countably many balls
  have hall : ∀ᵐ x ∂ν.restrict s, ∀ i ∈ T, x ∈ ball (i : Euclid P) (r i) →
      ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t) :=
    (ae_ball_iff hTc).mpr (fun i _ => hloc i)
  filter_upwards [hall] with x hx hxW
  obtain ⟨i, hiT, hxi⟩ := hcover x hxW
  exact hx i hiT hxi

/-- Simon Ch. 3, Remark 1.5(3) with the density theorem of Ch. 1, 3.16: for `μ = θHⁿ⌞M` and an
open `W ⊆ U`, at `Hⁿ⌞M`-a.e. `x ∈ W` every `c < θ(x)` has `cωₙtⁿ ≤ μ(B_t(x))` for small `t > 0`.
With `m = θ(x)` and `M_m = {θ = m} ∩ M`, the density theorem on `M_m` and the approximate tangent
plane at `x` give `μ(B_t(x)) ≥ m Hⁿ(M_m ∩ B_t(x)) ≥ m a Hⁿ(M ∩ B_t(x)) ≥ m a² ωₙtⁿ`, and
`a = (1 + c/m)/2 < 1` has `c ≤ m a²`. -/
theorem Submission.dorag_dbs_lower_density_ge_mult : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n), 0 < n → IsOpen W → W ⊆ U → ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ W → ∀ c : ℝ, c < R.mult x → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ R.measure (closedBall x t) := by
  intro P n U W R hn hW hWU
  have hM := R.measurableSet_carrier
  -- Step 1: `Hⁿ⌞M` is finite on compact `K ⊆ W`, as `θ ≥ 1` on `M` and `θ` is locally integrable
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ W →
      (μHE[n].restrict R.carrier) K ≠ ∞ := by
    intro K hK hKW
    rw [Measure.restrict_apply' hM]
    have h := R.locallyIntegrable_mult K hK (hKW.trans hWU)
    refine ne_top_of_le_ne_top h ?_
    calc μHE[n] (K ∩ R.carrier) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
          rw [setLIntegral_const, one_mul, inter_comm]
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_mono' (hM.inter hK.measurableSet)
          intro x hx
          have := R.mult_pos x hx.1
          exact_mod_cast this
  -- Step 2: the density theorem on each level set `M_m = {y ∈ M | θ(y) = m}`, for all `m` at once
  have hs : ∀ m : ℕ, MeasurableSet {y | y ∈ R.carrier ∧ R.mult y = m} := fun m =>
    hM.inter (R.measurable_mult (measurableSet_singleton m))
  have hlev : ∀ m : ℕ, ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      x ∈ {y | y ∈ R.carrier ∧ R.mult y = m} → x ∈ W → ∀ a : ℝ, a < 1 →
        ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal a * (μHE[n].restrict R.carrier) (closedBall x t) ≤
          (μHE[n].restrict R.carrier) ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t) := by
    intro m
    have := Submission.dorag_dbs_localized_density_point P W {y | y ∈ R.carrier ∧ R.mult y = m}
      (μHE[n].restrict R.carrier) hW (hs m) hfin
    rwa [ae_restrict_iff' (hs m)] at this
  have hlev' := ae_all_iff.mpr hlev
  -- Steps 3–4: a.e. `x` lies in `M` and has an approximate tangent plane `Q`
  have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R.carrier := ae_restrict_mem hM
  filter_upwards [hlev', R.orients, hmem] with x hlevx htanx hxM hxW c hc
  obtain ⟨Q, hQ, -⟩ := htanx
  -- Step 5: with `m = θ(x) ≥ 1` and `0 < c < m`, `a = (1 + c/m)/2 < 1` satisfies `c ≤ m a²`
  have hm1 : 1 ≤ R.mult x := R.mult_pos x hxM
  have hm0 : (0 : ℝ) < R.mult x := by exact_mod_cast hm1
  by_cases hc0 : c ≤ 0
  · filter_upwards with t
    simp [ENNReal.ofReal_of_nonpos hc0]
  push Not at hc0
  set m := R.mult x
  have hq0 : 0 < c / m := div_pos hc0 hm0
  have hq1 : c / m < 1 := (div_lt_one hm0).mpr hc
  set a := (1 + c / m) / 2 with ha_def
  have ha1 : a < 1 := by linarith
  have ha0 : 0 < a := by linarith
  have haq : c / m ≤ a * a := by nlinarith
  have hcm : c ≤ m * (a * a) := by
    have := (div_le_iff₀ hm0).mp haq
    linarith
  -- Step 6: `μ(B_t(x)) ≥ m Hⁿ(M_m ∩ B_t(x)) ≥ m a Hⁿ(M ∩ B_t(x)) ≥ m a² ωₙtⁿ ≥ c ωₙtⁿ`
  have hA := Submission.dorag_dbs_approxTangent_lower_density P n R.carrier x Q hn hQ a ha1
  have hB := hlevx m ⟨hxM, rfl⟩ hxW a ha1
  filter_upwards [hA, hB] with t hAt hBt
  rw [Measure.restrict_apply measurableSet_closedBall,
    Measure.restrict_apply ((hs m).inter measurableSet_closedBall)] at hBt
  have hset : {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t ∩ R.carrier =
      {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t := by
    ext y; constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, h.1.1⟩
  rw [hset] at hBt
  have hmeas : (m : ℝ≥0∞) * μHE[n] ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t) ≤
      R.measure (closedBall x t) := by
    unfold IMRep.measure
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall]
    calc (m : ℝ≥0∞) * μHE[n] ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t)
        = ∫⁻ _ in {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t, (m : ℝ≥0∞) ∂μHE[n] := by
          rw [setLIntegral_const, mul_comm]
      _ = ∫⁻ y in {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t,
            (R.mult y : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_congr_fun ((hs m).inter measurableSet_closedBall)
          intro y hy
          exact (congrArg (fun k : ℕ => (k : ℝ≥0∞)) hy.1.2).symm
      _ ≤ ∫⁻ y in closedBall x t ∩ R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[n] := by
          apply lintegral_mono_set
          intro y hy
          exact ⟨hy.2, hy.1.1⟩
  have hinter : μHE[n] (closedBall x t ∩ R.carrier) = μHE[n] (R.carrier ∩ closedBall x t) := by
    rw [inter_comm]
  rw [hinter] at hBt
  calc ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n)
      ≤ ENNReal.ofReal (m * (a * a)) * unitBallVolume n * ENNReal.ofReal (t ^ n) := by
        gcongr
    _ = (m : ℝ≥0∞) * (ENNReal.ofReal a * (ENNReal.ofReal a * unitBallVolume n *
          ENNReal.ofReal (t ^ n))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul ha0.le,
          ENNReal.ofReal_natCast]
        ring
    _ ≤ (m : ℝ≥0∞) * (ENNReal.ofReal a * μHE[n] (R.carrier ∩ closedBall x t)) := by
        gcongr
    _ ≤ (m : ℝ≥0∞) * μHE[n] ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t) := by
        gcongr
    _ ≤ R.measure (closedBall x t) := hmeas

/-- **Unit multiplicity where the mass ratio stays below `2`** (Simon Ch. 5, 2.3–2.4; the step
`θ = 1` a.e. of the density bounds for Allard's graph theorem).  If `S ⊆ W` and every `x ∈ S` has
`μ_V(B_t(x)) ≤ c₀ ωₙ tⁿ` for small `t > 0`, with `c₀ < 2`, then `θ = 1` `μ_V`-a.e. on `S`.  At a
`μ_V`-typical `x ∈ S ∩ M`, `dorag_dbs_lower_density_ge_mult` gives `c ωₙ tⁿ ≤ μ_V(B_t(x))` for small
`t` and every `c < θ(x)`; if `θ(x) ≥ 2`, then `c = (max c₀ 0 + 2) / 2` contradicts the upper bound
after cancelling `0 < ωₙ tⁿ < ∞`. -/
theorem Submission.dorag_dbs_mult_eq_one_of_density_lt_two : ∀ (P n : ℕ) (U W S : Set (Euclid P)) (R : IMRep U n) (c₀ : ℝ), 0 < n → IsOpen W → W ⊆ U → S ⊆ W → c₀ < 2 → (∀ x ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), R.measure (closedBall x t) ≤ ENNReal.ofReal c₀ * unitBallVolume n * ENNReal.ofReal (t ^ n)) → ∀ᵐ x ∂R.measure, x ∈ S → R.mult x = 1 := by
  intro P n U W S R c₀ hn hW hWU hSW hc₀ hup
  -- Step 1: `μ_V ≪ Hⁿ⌞M`, so the lower density bound holds and `x ∈ M` for `μ_V`-a.e. `x`
  have h5 := Submission.dorag_dbs_lower_density_ge_mult P n U W R hn hW hWU
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have h5' := hac.ae_le h5
  have hmem : ∀ᵐ x ∂R.measure, x ∈ R.carrier :=
    hac.ae_le (ae_restrict_mem R.measurableSet_carrier)
  filter_upwards [h5', hmem] with x hx hxM hxS
  -- Step 2: if `θ(x) ≠ 1` then `θ(x) ≥ 2 > c > max c₀ 0` for `c = (max c₀ 0 + 2) / 2`
  have hxW := hSW hxS
  have hpos := R.mult_pos x hxM
  by_contra hne
  have h2 : 2 ≤ R.mult x := by omega
  have hc₁ : max c₀ 0 < 2 := max_lt hc₀ (by norm_num)
  have h2' : (2 : ℝ) ≤ R.mult x := by exact_mod_cast h2
  have hcm : (max c₀ 0 + 2) / 2 < (R.mult x : ℝ) := by linarith
  -- Step 3: some `t > 0` has `c ωₙ tⁿ ≤ μ_V(B_t(x)) ≤ c₀ ωₙ tⁿ`
  have hlow := hx hxW ((max c₀ 0 + 2) / 2) hcm
  obtain ⟨t, ht1, ht2, htpos⟩ := (hlow.and ((hup x hxS).and self_mem_nhdsWithin)).exists
  -- Step 4: cancel `0 < ωₙ tⁿ < ∞`, giving `c ≤ c₀` or `c ≤ 0`, both false
  have hω0 : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have htn0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos htpos n
  have hcomb := ht1.trans ht2
  rw [mul_assoc, mul_assoc] at hcomb
  have hle : ENNReal.ofReal ((max c₀ 0 + 2) / 2) ≤ ENNReal.ofReal c₀ :=
    (ENNReal.mul_le_mul_iff_left (mul_ne_zero hω0 htn0)
      (ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top)).mp hcomb
  rw [ENNReal.ofReal_le_ofReal_iff'] at hle
  rcases hle with h | h
  · have := le_max_left c₀ 0
    linarith
  · have := le_max_right c₀ 0
    linarith
/-- **Simon Ch. 4, §3 (p. 90)**, the cutoff `φ` chosen after (3.3), with `1 + ε = A`: for `A > 1`
there is a `C¹` nonincreasing `φ` with `0 ≤ φ ≤ 1`, `φ ≡ 1` on `(-∞, 1]`, `φ ≡ 0` on `[A, ∞)`,
`φ' ≤ 0`, and `φ'(u) ≠ 0` only for `1 < u < A`.  Take `φ(u) = Ψ((A − u)/(A − 1))` for Mathlib's
smooth transition `Ψ` (`Ψ = 0` on `(-∞, 0]`, `Ψ = 1` on `[1, ∞)`, monotone).  `φ` is antitone, so
`φ' ≤ 0`; on the plateaus `u` is a global extremum of `φ`, so `φ'(u) = 0`. -/
theorem Submission.doragm_sab_cutoff_profile : ∀ (A : ℝ), 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, u ≤ 1 → φ u = 1) ∧ (∀ u, A ≤ u → φ u = 0) ∧ (∀ u, deriv φ u ≤ 0) ∧ (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A) := by
  intro A hA
  -- `a = A − 1 > 0` and `φ(u) = Ψ((A − u)/a)` for the smooth transition `Ψ`
  have ha : 0 < A - 1 := sub_pos.2 hA
  set φ : ℝ → ℝ := fun u => Real.smoothTransition ((A - u) / (A - 1))
  -- `u ↦ (A − u)/a` is antitone and `Ψ` is monotone
  have hanti : Antitone φ := fun u v huv =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_left huv A) ha.le)
  have hbd : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1 := fun u =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `u ≤ 1` gives `(A − u)/a ≥ 1`, and `A ≤ u` gives `(A − u)/a ≤ 0`
  have h1 : ∀ u, u ≤ 1 → φ u = 1 := fun u hu =>
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ ha).2 (by linarith))
  have h0 : ∀ u, A ≤ u → φ u = 0 := fun u hu =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
  refine ⟨φ, ?_, hanti, hbd, h1, h0, fun u => hanti.deriv_nonpos, fun u hu => ?_⟩
  · -- `Ψ` is `C^∞` and `u ↦ (A − u)/a` is affine
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  · -- on the plateaus `u` is a global maximum (`φ u = 1`) or minimum (`φ u = 0`), so `φ'(u) = 0`
    by_contra hcon
    rcases le_or_gt u 1 with hu1 | hu1
    · refine hu (IsLocalMax.deriv_eq_zero ?_)
      exact (isMaxOn_univ_iff.2 fun v => (h1 u hu1).symm ▸ (hbd v).2).isLocalMax Filter.univ_mem
    · have hAu : A ≤ u := not_lt.1 fun h => hcon ⟨hu1, h⟩
      refine hu (IsLocalMin.deriv_eq_zero ?_)
      exact (isMinOn_univ_iff.2 fun v => (h0 u hAu).symm ▸ (hbd v).1).isLocalMin Filter.univ_mem
/-- **Integrating-factor comparison on `[s, t]`** (Simon Ch. 4, 3.16, p. 92: the integrating-factor
step, done here by comparing derivatives).  If `n I − τ I' + τ J = −h`, `|h| ≤ cτI`,
`J ≥ 0` and `G' ≤ J/τⁿ ≤ K G'` on `[s, t]` (`c ≥ 0`, `0 < s < t`), then with
`Φ_b(σ) = e^{bσ} σ⁻ⁿ I(σ)`: `G(t) − G(s) ≤ Φ_c(t) − Φ_c(s)` and
`Φ_{−c}(t) − Φ_{−c}(s) ≤ K (G(t) − G(s))`.  By the quotient rule and `(E)`,
`Φ_b' = e^{bτ}τ⁻ⁿ (J + bI + h/τ)`; since `cI + h/τ ≥ 0 ≥ −cI + h/τ` and `e^{−cτ} ≤ 1 ≤ e^{cτ}`,
`Φ_c − G` and `K G − Φ_{−c}` have nonnegative derivative, hence are nondecreasing on `[s, t]`. -/
theorem Submission.doragm_sab_exp_ratio_compare : ∀ (n : ℕ) (c K s t : ℝ) (I I' G G' J h : ℝ → ℝ), 0 ≤ c → 0 < s → s < t → (∀ τ ∈ Icc s t, HasDerivAt I (I' τ) τ) → (∀ τ ∈ Icc s t, HasDerivAt G (G' τ) τ) → (∀ τ ∈ Icc s t, (n : ℝ) * I τ - τ * I' τ + τ * J τ = -h τ) → (∀ τ ∈ Icc s t, |h τ| ≤ c * τ * I τ) → (∀ τ ∈ Icc s t, 0 ≤ J τ) → (∀ τ ∈ Icc s t, G' τ ≤ J τ / τ ^ n) → (∀ τ ∈ Icc s t, J τ / τ ^ n ≤ K * G' τ) → G t - G s ≤ Real.exp (c * t) / t ^ n * I t - Real.exp (c * s) / s ^ n * I s ∧ Real.exp (-(c * t)) / t ^ n * I t - Real.exp (-(c * s)) / s ^ n * I s ≤ K * (G t - G s) := by
  intro n c K s t I I' G G' J h hc hs hst hI hG hE hH hJ hC1 hC2
  -- every `τ ∈ [s, t]` is positive
  have hpos : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => hs.trans_le hτ.1
  -- `Φ_b(σ) = e^{bσ}/σⁿ · I(σ)` has derivative `e^{bτ}/τⁿ · (J + bI + h/τ)`, by `(E)`
  have hΦ : ∀ b : ℝ, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => Real.exp (b * σ) / σ ^ n * I σ)
      (Real.exp (b * τ) / τ ^ n * (J τ + b * I τ + h τ / τ)) τ := by
    intro b τ hτ
    have hτ0 : τ ≠ 0 := (hpos τ hτ).ne'
    have he : HasDerivAt (fun σ => Real.exp (b * σ)) (Real.exp (b * τ) * b) τ := by
      simpa using ((hasDerivAt_id τ).const_mul b).exp
    have hd := (he.fun_div (hasDerivAt_pow n τ) (pow_ne_zero n hτ0)).fun_mul (hI τ hτ)
    convert hd using 1
    have hI' : I' τ = ((n : ℝ) * I τ + τ * J τ + h τ) / τ := by
      field_simp
      linarith [hE τ hτ]
    rw [hI']
    rcases n with _ | m
    · simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, one_pow, div_one, zero_add]
      field_simp
      ring
    · simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]
      field_simp
      ring
  -- a nonnegative derivative on `[s, t]` gives `f s ≤ f t`
  have hmono : ∀ f f' : ℝ → ℝ, (∀ τ ∈ Icc s t, HasDerivAt f (f' τ) τ) →
      (∀ τ ∈ Icc s t, 0 ≤ f' τ) → f s ≤ f t := by
    intro f f' hf hf'
    have hmon : MonotoneOn f (Icc s t) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc s t)
        (fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt) (fun τ hτ => ?_) (fun τ hτ => ?_)
      · rw [interior_Icc] at hτ
        exact (hf τ (Ioo_subset_Icc_self hτ)).hasDerivWithinAt
      · rw [interior_Icc] at hτ
        exact hf' τ (Ioo_subset_Icc_self hτ)
    exact hmon (left_mem_Icc.2 hst.le) (right_mem_Icc.2 hst.le) hst.le
  -- `|h| ≤ cτI` gives `cI + h/τ ≥ 0` and `−cI + h/τ ≤ 0`
  have hsign : ∀ τ ∈ Icc s t, 0 ≤ c * I τ + h τ / τ ∧ -c * I τ + h τ / τ ≤ 0 := by
    intro τ hτ
    have hτ0 := hpos τ hτ
    obtain ⟨hl, hu⟩ := abs_le.1 (hH τ hτ)
    have h1 : -(c * I τ) ≤ h τ / τ := by
      rw [le_div_iff₀ hτ0]; linarith
    have h2 : h τ / τ ≤ c * I τ := by
      rw [div_le_iff₀ hτ0]; linarith
    constructor <;> linarith
  constructor
  · -- (a): `Φ_c' ≥ e^{cτ} J/τⁿ ≥ J/τⁿ ≥ G'`, so `Φ_c − G` is nondecreasing
    have key := hmono (fun σ => Real.exp (c * σ) / σ ^ n * I σ - G σ)
      (fun τ => Real.exp (c * τ) / τ ^ n * (J τ + c * I τ + h τ / τ) - G' τ)
      (fun τ hτ => (hΦ c τ hτ).fun_sub (hG τ hτ)) (fun τ hτ => by
        have hτn : 0 < τ ^ n := pow_pos (hpos τ hτ) n
        have hJn : 0 ≤ J τ / τ ^ n := div_nonneg (hJ τ hτ) hτn.le
        have hexp : 1 ≤ Real.exp (c * τ) := Real.one_le_exp (mul_nonneg hc (hpos τ hτ).le)
        have hA : 0 ≤ Real.exp (c * τ) / τ ^ n * (c * I τ + h τ / τ) :=
          mul_nonneg (div_nonneg (Real.exp_pos _).le hτn.le) (hsign τ hτ).1
        have hB : J τ / τ ^ n ≤ Real.exp (c * τ) * (J τ / τ ^ n) := le_mul_of_one_le_left hJn hexp
        have hsplit : Real.exp (c * τ) / τ ^ n * (J τ + c * I τ + h τ / τ) =
            Real.exp (c * τ) * (J τ / τ ^ n) + Real.exp (c * τ) / τ ^ n * (c * I τ + h τ / τ) := by
          ring
        rw [hsplit]
        linarith [hC1 τ hτ])
    linarith
  · -- (b): `Φ_{−c}' ≤ e^{−cτ} J/τⁿ ≤ J/τⁿ ≤ K G'`, so `K G − Φ_{−c}` is nondecreasing
    have key := hmono (fun σ => K * G σ - Real.exp (-c * σ) / σ ^ n * I σ)
      (fun τ => K * G' τ - Real.exp (-c * τ) / τ ^ n * (J τ + -c * I τ + h τ / τ))
      (fun τ hτ => ((hG τ hτ).const_mul K).fun_sub (hΦ (-c) τ hτ)) (fun τ hτ => by
        have hτn : 0 < τ ^ n := pow_pos (hpos τ hτ) n
        have hJn : 0 ≤ J τ / τ ^ n := div_nonneg (hJ τ hτ) hτn.le
        have hexp : Real.exp (-c * τ) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [hpos τ hτ])
        have hA : Real.exp (-c * τ) / τ ^ n * (-c * I τ + h τ / τ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.exp_pos _).le hτn.le) (hsign τ hτ).2
        have hB : Real.exp (-c * τ) * (J τ / τ ^ n) ≤ J τ / τ ^ n := mul_le_of_le_one_left hJn hexp
        have hsplit : Real.exp (-c * τ) / τ ^ n * (J τ + -c * I τ + h τ / τ) =
            Real.exp (-c * τ) * (J τ / τ ^ n) + Real.exp (-c * τ) / τ ^ n * (-c * I τ + h τ / τ) := by
          ring
        rw [hsplit]
        linarith [hC2 τ hτ])
    simp only [neg_mul] at key
    linarith
/-- **The mean-curvature term of a radial cutoff** (Simon Ch. 4, 3.16): if `φ ≥ 0` vanishes on
`[A, ∞)`, `τ > 0` and `‖H‖ ≤ κ`, then
`|∫ φ(|x − y|/τ) ⟨x − y, H x⟩ dμ| ≤ A κ τ ∫ φ(|x − y|/τ) dμ`.  Where `φ(|x − y|/τ) ≠ 0`,
`|x − y| < Aτ`, so Cauchy–Schwarz bounds the integrand by the integrable `Aκτ φ(|x − y|/τ)`. -/
theorem Submission.doragm_sab_curvature_term_le : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (H : Euclid P → Euclid P) (φ : ℝ → ℝ) (κ A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u) → (∀ u, A ≤ u → φ u = 0) → (∀ x, ‖H x‖ ≤ κ) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → |∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂μ| ≤ A * κ * τ * ∫ x, φ (‖x - y‖ / τ) ∂μ := by
  intro P μ y H φ κ A τ hτ hφ hφA hH hint
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hH 0)
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hint.const_mul (A * κ * τ)) (ae_of_all μ fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hφ _)]
  by_cases h0 : φ (‖x - y‖ / τ) = 0
  · simp [h0]
  have hr : ‖x - y‖ ≤ A * τ :=
    ((div_lt_iff₀ hτ).mp (lt_of_not_ge fun hA => h0 (hφA _ hA))).le
  calc φ (‖x - y‖ / τ) * ‖inner ℝ (x - y) (H x)‖
      ≤ φ (‖x - y‖ / τ) * (‖x - y‖ * κ) :=
        mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hH x) (norm_nonneg _))) (hφ _)
    _ ≤ φ (‖x - y‖ / τ) * (A * τ * κ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hκ) (hφ _)
    _ = A * κ * τ * φ (‖x - y‖ / τ) := by ring
/-- **Simon Ch. 4, 3.5 (p. 90)**, comparison of the scale-derivative weights.  With
`r = |x − y|`, `d = −(r/τ²)·φ'(r/τ) ≥ 0` and `q = N/max(s, r)ⁿ`: where `φ'(r/τ) ≠ 0` we have
`τ < r < Aτ`, so `max(s, r) = r` and `r⁻ⁿ ≤ τ⁻ⁿ ≤ Aⁿr⁻ⁿ`; multiplying by `d·N ≥ 0` and
integrating gives `0 ≤ ∫ d·N dμ` and `∫ d·q dμ ≤ (∫ d·N dμ)/τⁿ ≤ Aⁿ ∫ d·q dμ`. -/
theorem Submission.doragm_sab_deriv_weight_squeeze : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (N : Euclid P → ℝ) (A s τ : ℝ), 1 < A → 0 < s → s ≤ τ → (∀ u, deriv φ u ≤ 0) → (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A) → (∀ x, 0 ≤ N x) → Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) μ → Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x) μ → 0 ≤ ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ ∧ ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂μ ≤ (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ) / τ ^ n ∧ (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ) / τ ^ n ≤ A ^ n * ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂μ := by
  intro P n μ y φ N A s τ hA hs hsτ hφ' hsupp hN hq hD
  have hτ : 0 < τ := hs.trans_le hsτ
  -- `d·N ≥ 0`: `r/τ² ≥ 0` and `φ' ≤ 0` give `d ≥ 0`, and `N ≥ 0`
  have hDnn : ∀ x, 0 ≤ -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x := fun x =>
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (by positivity)) (hφ' _)) (hN x)
  -- pointwise, `d·q ≤ d·N/τⁿ ≤ Aⁿ·d·q`
  have hpt : ∀ x,
      -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ≤
          -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x / τ ^ n ∧
        -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x / τ ^ n ≤
          A ^ n * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) := by
    intro x
    by_cases h0 : deriv φ (‖x - y‖ / τ) = 0
    · -- `d(x) = 0`, so all three terms vanish
      simp [h0]
    · -- `1 < r/τ < A`, so `τ < r < Aτ` and `max(s, r) = r`
      obtain ⟨h1, h2⟩ := hsupp _ h0
      have hr1 : τ < ‖x - y‖ := (one_lt_div₀ hτ).1 h1
      have hr2 : ‖x - y‖ < A * τ := (div_lt_iff₀ hτ).1 h2
      have hr : 0 < ‖x - y‖ := hτ.trans hr1
      have hrA : ‖x - y‖ ^ n ≤ A ^ n * τ ^ n :=
        (pow_le_pow_left₀ hr.le hr2.le n).trans_eq (mul_pow A τ n)
      rw [max_eq_right (hsτ.trans hr1.le), ← mul_div_assoc]
      have hDx := hDnn x
      generalize -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x = D at hDx ⊢
      refine ⟨div_le_div_of_nonneg_left hDx (pow_pos hτ n) (pow_le_pow_left₀ hτ.le hr1.le n), ?_⟩
      -- `D/τⁿ ≤ Aⁿ·D/rⁿ ⟺ D·rⁿ ≤ Aⁿ·D·τⁿ`, from `rⁿ ≤ (Aτ)ⁿ` and `D ≥ 0`
      rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hτ n) (pow_pos hr n)]
      calc D * ‖x - y‖ ^ n ≤ D * (A ^ n * τ ^ n) := mul_le_mul_of_nonneg_left hrA hDx
        _ = A ^ n * D * τ ^ n := by ring
  refine ⟨integral_nonneg hDnn, ?_, ?_⟩
  · -- `∫ d·q ≤ ∫ d·N/τⁿ = (∫ d·N)/τⁿ`
    rw [← integral_div]
    exact integral_mono hq (hD.div_const _) fun x => (hpt x).1
  · -- `(∫ d·N)/τⁿ = ∫ d·N/τⁿ ≤ ∫ Aⁿ·d·q = Aⁿ ∫ d·q`
    rw [← integral_div, ← integral_const_mul]
    exact integral_mono (hD.div_const _) (hq.const_mul _) fun x => (hpt x).2
/-- **Simon Ch. 4, (3.5)–(3.6) (p. 90)**, the passage from the smoothed to the sharp masses: if
`0 ≤ φ ≤ 1`, `φ ≡ 1` on `(-∞, 1]` and `φ ≡ 0` on `[A, ∞)`, then pointwise
`1_{B̄_τ(y)} ≤ φ(|x − y|/τ) ≤ 1_{B̄_{Aτ}(y)}`, so `μ(B̄_τ(y)) ≤ ∫ φ(|x − y|/τ) dμ ≤ μ(B̄_{Aτ}(y))`
in `[0, ∞]` (`ofReal ∫ f = ∫⁻ ofReal f` for integrable `f ≥ 0`; no finiteness of `μ` is needed). -/
theorem Submission.doragm_sab_cutoff_mass_sandwich : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → μ (closedBall y τ) ≤ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ∧ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ≤ μ (closedBall y (A * τ)) := by
  intro P μ y φ A τ hτ hbd h1 h0 hint
  -- `ofReal ∫ f dμ = ∫⁻ ofReal f dμ` for the integrable `f(x) = φ(|x − y|/τ) ≥ 0`, and
  -- `μ(B̄_ρ(y)) = ∫⁻ 1_{B̄_ρ(y)} dμ` since closed balls are measurable
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hbd _).1),
    ← lintegral_indicator_one (measurableSet_closedBall : MeasurableSet (closedBall y τ)),
    ← lintegral_indicator_one (measurableSet_closedBall : MeasurableSet (closedBall y (A * τ)))]
  refine ⟨lintegral_mono fun x => ?_, lintegral_mono fun x => ?_⟩
  · -- on `B̄_τ(y)`, `|x − y|/τ ≤ 1`, so `φ(|x − y|/τ) = 1`
    by_cases hx : x ∈ closedBall y τ
    · rw [indicator_of_mem hx, Pi.one_apply,
        h1 _ ((div_le_one hτ).2 (mem_closedBall_iff_norm.1 hx)), ENNReal.ofReal_one]
    · rw [indicator_of_notMem hx]
      exact zero_le
  · -- `φ ≤ 1` everywhere, and off `B̄_{Aτ}(y)`, `|x − y|/τ > A`, so `φ(|x − y|/τ) = 0`
    by_cases hx : x ∈ closedBall y (A * τ)
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hbd _).2
    · rw [mem_closedBall_iff_norm, not_le] at hx
      rw [h0 _ ((le_div_iff₀ hτ).2 hx.le), ENNReal.ofReal_zero]
      exact zero_le
/-- The cutoff increment `Δ = ∫ φ(r/t) q dμ - ∫ φ(r/s) q dμ`, `r = ‖x - y‖`, lies between two
annular integrals of `F` (Simon Ch. 4, 3.5): `Δ ≥ 0` and, in `[0, ∞]`,
`∫⁻_{B̄_t(y) \ B̄_{As}(y)} F ≤ Δ ≤ ∫⁻_{B̄_{At}(y) \ B̄_s(y)} F`.  The point is that
`g = (φ(r/t) - φ(r/s)) q` is `≥ 0`, equals `q = F` on the first annulus and vanishes off the
second. -/
theorem Submission.doragm_sab_annulus_increment_sandwich : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q F : Euclid P → ℝ) (A s t : ℝ), 1 < A → 0 < s → s ≤ t → Antitone φ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → (∀ x, 0 ≤ q x) → (∀ x, s < ‖x - y‖ → F x = q x) → Integrable (fun x => φ (‖x - y‖ / s) * q x) μ → Integrable (fun x => φ (‖x - y‖ / t) * q x) μ → 0 ≤ (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ ∧ (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ∧ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ≤ ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (F x) ∂μ := by
  intro P μ y φ q F A s t hA hs hst hφ hφ01 hφ1 hφ0 hq hFq hint_s hint_t
  have ht : 0 < t := hs.trans_le hst
  -- Step 1: `Δ = ∫ g dμ` for the integrable `g = φ(r/t) q - φ(r/s) q`
  set g : Euclid P → ℝ := fun x => φ (‖x - y‖ / t) * q x - φ (‖x - y‖ / s) * q x with hg_def
  have hΔ : (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ = ∫ x, g x ∂μ :=
    (integral_sub hint_t hint_s).symm
  -- Step 2: `g ≥ 0`, as `r/t ≤ r/s` and `φ` is antitone; so `ofReal Δ = ∫⁻ ofReal g`
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x =>
    sub_nonneg.2 (mul_le_mul_of_nonneg_right
      (hφ (div_le_div_of_nonneg_left (norm_nonneg _) hs hst)) (hq x))
  have hg_int : Integrable g μ := hint_t.sub hint_s
  rw [hΔ, ofReal_integral_eq_lintegral_ofReal hg_int (Eventually.of_forall hg_nonneg)]
  refine ⟨integral_nonneg hg_nonneg, ?_, ?_⟩
  · -- Step 3: on `B̄_t(y) \ B̄_{As}(y)`, `φ(r/t) = 1`, `φ(r/s) = 0` and `r > As > s`, so `g = q = F`
    calc (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ)
        = ∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (g x) ∂μ := by
          refine setLIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
            fun x hx => ?_
          simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, not_le] at hx
          have h1 : φ (‖x - y‖ / t) = 1 := hφ1 _ ((div_le_one ht).2 hx.1)
          have h0 : φ (‖x - y‖ / s) = 0 := hφ0 _ ((le_div_iff₀ hs).2 hx.2.le)
          simp only [hg_def, h1, h0, hFq x ((lt_mul_of_one_lt_left hs hA).trans hx.2), one_mul,
            zero_mul, sub_zero]
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := setLIntegral_le_lintegral _ _
  · -- Step 4: `ofReal g ≤ 1_{B̄_{At}(y) \ B̄_s(y)} ofReal F` pointwise
    rw [← lintegral_indicator (measurableSet_closedBall.diff measurableSet_closedBall)]
    refine lintegral_mono fun x => ?_
    rcases le_or_gt ‖x - y‖ s with hrs | hsr
    · -- `r ≤ s ≤ t`: `φ(r/t) = φ(r/s) = 1`, so `g = 0`
      have h1t : φ (‖x - y‖ / t) = 1 := hφ1 _ ((div_le_one ht).2 (hrs.trans hst))
      have h1s : φ (‖x - y‖ / s) = 1 := hφ1 _ ((div_le_one hs).2 hrs)
      refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
      simp only [hg_def, h1t, h1s, sub_self, le_refl]
    rcases le_or_gt ‖x - y‖ (A * t) with hrAt | hAtr
    · -- `s < r ≤ At`: `x` lies in the annulus, where `g ≤ φ(r/t) q ≤ q = F`
      have hx : x ∈ closedBall y (A * t) \ closedBall y s := by
        simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, not_le]
        exact ⟨hrAt, hsr⟩
      rw [indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht1 := mul_le_mul_of_nonneg_right (hφ01 (‖x - y‖ / t)).2 (hq x)
      have hs0 := mul_nonneg (hφ01 (‖x - y‖ / s)).1 (hq x)
      simp only [hg_def, hFq x hsr]
      linarith
    · -- `r > At`: `φ(r/t) = 0`, so `g = -φ(r/s) q ≤ 0`
      have h0t : φ (‖x - y‖ / t) = 0 := hφ0 _ ((le_div_iff₀ ht).2 hAtr.le)
      have hs0 := mul_nonneg (hφ01 (‖x - y‖ / s)).1 (hq x)
      refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
      simp only [hg_def, h0t, zero_mul]
      linarith
/-- **Simon Ch. 4, 3.4 and 3.16** (differentiating `ρ ↦ ∫ φ(r/ρ) dμ` under the integral sign):
for a `C¹` cutoff `φ` vanishing on `[A, ∞)` and a bounded weight `q`, with `0 < τ`, `Aτ < R₀`
and `ν(B̄_{R₀}(y)) < ∞`, the integrands `φ(|x - y|/τ) q` and `-(|x - y|/τ²) φ'(|x - y|/τ) q` are
`ν`-integrable and `σ ↦ ∫ φ(|x - y|/σ) q dν` has derivative `∫ -(|x - y|/τ²) φ'(|x - y|/τ) q dν`
at `τ`.  For `σ ∈ (τ/2, R₀/A)` both integrands vanish off `B̄_{R₀}(y)` and are bounded on it
uniformly in `σ`, so dominated differentiation applies. -/
theorem Submission.doragm_radial_cutoff_hasDerivAt : ∀ (P : ℕ) (ν : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q : Euclid P → ℝ) (A B τ R₀ : ℝ), ContDiff ℝ 1 φ → (∀ u, A ≤ u → φ u = 0) → 0 < A → 0 < τ → A * τ < R₀ → ν (closedBall y R₀) ≠ ∞ → AEStronglyMeasurable q ν → (∀ x, ‖q x‖ ≤ B) → Integrable (fun x => φ (‖x - y‖ / τ) * q x) ν ∧ Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * q x) ν ∧ HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) * q x ∂ν) (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * q x ∂ν) τ := by
  intro P ν y φ q A B τ R₀ hφ hφA hA hτ hAτ hν hq hqB
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  -- `φ' = 0` on `(A, ∞)`, where `φ` vanishes identically
  have hφ'A : ∀ u, A < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun v hv => hφA v (le_of_lt hv)
    rw [h.deriv_eq, deriv_const]
  have hR₀ : 0 < R₀ := (mul_pos hA hτ).trans hAτ
  -- bounds `C₀`, `C₁` for `|φ|`, `|φ'|` on `[0, 2R₀/τ]`
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * R₀ / τ)) hφ.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * R₀ / τ)) hφ'c.continuousOn
  have h0K : (0 : ℝ) ∈ Icc 0 (2 * R₀ / τ) := ⟨le_rfl, by positivity⟩
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0 h0K)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 h0K)
  -- the neighbourhood `(τ/2, R₀/A)` of `τ`
  have hτs : τ ∈ Ioo (τ / 2) (R₀ / A) := ⟨by linarith, by rw [lt_div_iff₀ hA]; linarith⟩
  have hs : Ioo (τ / 2) (R₀ / A) ∈ 𝓝 τ := Ioo_mem_nhds hτs.1 hτs.2
  -- for `σ ∈ (τ/2, R₀/A)`: off `B̄_{R₀}(y)`, `|x - y|/σ > A`; on it, `|x - y|/σ ∈ [0, 2R₀/τ]`
  have hout : ∀ σ ∈ Ioo (τ / 2) (R₀ / A), ∀ x ∉ closedBall y R₀, A < ‖x - y‖ / σ := by
    rintro σ ⟨hσ1, hσ2⟩ x hx
    rw [mem_closedBall_iff_norm, not_le] at hx
    rw [lt_div_iff₀ hA] at hσ2
    have hσ : 0 < σ := by linarith
    rw [lt_div_iff₀ hσ]
    linarith
  have hin : ∀ σ ∈ Ioo (τ / 2) (R₀ / A), ∀ x ∈ closedBall y R₀,
      ‖x - y‖ / σ ∈ Icc 0 (2 * R₀ / τ) := by
    rintro σ ⟨hσ1, -⟩ x hx
    rw [mem_closedBall_iff_norm] at hx
    have hσ : 0 < σ := by linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ hσ hτ]
    nlinarith [norm_nonneg (x - y)]
  -- the integrands `F σ`, their `σ`-derivatives `F' σ`, and their measurability
  set F : ℝ → Euclid P → ℝ := fun σ x => φ (‖x - y‖ / σ) * q x with hF
  set F' : ℝ → Euclid P → ℝ := fun σ x => -(‖x - y‖ / σ ^ 2) * deriv φ (‖x - y‖ / σ) * q x
    with hF'
  have hr : Continuous fun x : Euclid P => ‖x - y‖ := (continuous_id.sub continuous_const).norm
  have hF_meas : ∀ σ, AEStronglyMeasurable (F σ) ν := fun σ =>
    (hφ.continuous.comp (hr.div_const σ)).aestronglyMeasurable.mul hq
  have hF'_meas : ∀ σ, AEStronglyMeasurable (F' σ) ν := fun σ =>
    ((hr.div_const _).neg.mul (hφ'c.comp (hr.div_const σ))).aestronglyMeasurable.mul hq
  -- constant multiples of `1_{B̄_{R₀}(y)}` are integrable, as `ν(B̄_{R₀}(y)) < ∞`
  have hind : ∀ c : ℝ, Integrable ((closedBall y R₀).indicator fun _ => c) ν := fun c =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hν)
  -- (a): `|F τ| ≤ C₀ B 1_{B̄_{R₀}(y)}`
  have hF_int : Integrable (F τ) ν := by
    refine (hind (C₀ * B)).mono' (hF_meas τ) (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall y R₀
    · rw [Set.indicator_of_mem hx, hF]
      simp only
      rw [norm_mul]
      exact mul_le_mul (hC₀ _ (hin τ hτs x hx)) (hqB x) (norm_nonneg _) hC₀0
    · rw [Set.indicator_of_notMem hx, hF]
      simp only
      rw [hφA _ (hout τ hτs x hx).le, zero_mul, norm_zero]
  -- domination: `|F' σ| ≤ (R₀/(τ/2)²) C₁ B 1_{B̄_{R₀}(y)}` for `σ ∈ (τ/2, R₀/A)`
  have h_bound : ∀ᵐ x ∂ν, ∀ σ ∈ Ioo (τ / 2) (R₀ / A),
      ‖F' σ x‖ ≤ (closedBall y R₀).indicator (fun _ => R₀ / (τ / 2) ^ 2 * C₁ * B) x := by
    refine ae_of_all _ fun x σ hσs => ?_
    have hσ : 0 < σ := by linarith [hσs.1]
    by_cases hx : x ∈ closedBall y R₀
    · rw [Set.indicator_of_mem hx, hF']
      simp only
      rw [norm_mul, norm_mul, norm_neg, Real.norm_of_nonneg (by positivity)]
      have hrσ : ‖x - y‖ / σ ^ 2 ≤ R₀ / (τ / 2) ^ 2 :=
        calc ‖x - y‖ / σ ^ 2 ≤ R₀ / σ ^ 2 := by gcongr; exact mem_closedBall_iff_norm.1 hx
          _ ≤ R₀ / (τ / 2) ^ 2 := by gcongr; exact hσs.1.le
      exact mul_le_mul (mul_le_mul hrσ (hC₁ _ (hin σ hσs x hx)) (norm_nonneg _) (by positivity))
        (hqB x) (norm_nonneg _) (mul_nonneg (by positivity) hC₁0)
    · rw [Set.indicator_of_notMem hx, hF']
      simp only
      rw [hφ'A _ (hout σ hσs x hx), mul_zero, zero_mul, norm_zero]
  -- `∂_σ φ(|x - y|/σ) = -(|x - y|/σ²) φ'(|x - y|/σ)`
  have h_diff : ∀ᵐ x ∂ν, ∀ σ ∈ Ioo (τ / 2) (R₀ / A), HasDerivAt (F · x) (F' σ x) σ := by
    refine ae_of_all _ fun x σ hσs => ?_
    have hσ : σ ≠ 0 := by linarith [hσs.1]
    have h1 : HasDerivAt (fun σ => ‖x - y‖ / σ) (-(‖x - y‖ / σ ^ 2)) σ := by
      convert (hasDerivAt_inv hσ).const_mul ‖x - y‖ using 1
      · funext σ
        rw [div_eq_mul_inv]
      · ring
    have h2 : HasDerivAt (fun σ => φ (‖x - y‖ / σ))
        (deriv φ (‖x - y‖ / σ) * -(‖x - y‖ / σ ^ 2)) σ :=
      (hφd _).hasDerivAt.comp σ h1
    convert h2.mul_const (q x) using 1
    rw [hF']
    ring
  -- (b), (c): dominated differentiation under the integral sign
  obtain ⟨hF'_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall hF_meas) hF_int (hF'_meas τ) h_bound (hind _) h_diff
  exact ⟨hF_int, hF'_int, hderiv⟩
/-- The radial test field `X(x) = φ(|x − y|/τ)(x − y)` (Simon Ch. 4, 3.2–3.3, cutoff
`γ(r) = φ(r/τ)`) is `C¹` with compact support in `B̄_{Aτ}(y)`: it equals `x − y` on `B_τ(y)`, and
away from `y` the norm `|x − y|` is smooth. -/
theorem Submission.doragm_rfv_radial_field_c1 : ∀ (P : ℕ) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → ContDiff ℝ 1 (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ HasCompactSupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ) := by
  intro P y φ A τ hφ hφ1 hφA hτ
  -- (iii) off `B̄_{Aτ}(y)` we have `A ≤ ‖x - y‖ / τ`, so `φ (‖x - y‖ / τ) = 0`
  have hsupp : tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ) := by
    refine closure_minimal (support_subset_iff'.2 fun x hx => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have hA : A ≤ ‖x - y‖ / τ := (le_div_iff₀ hτ).2 hx.le
    simp [hφA _ hA]
  -- (ii) a closed subset of the compact ball `B̄_{Aτ}(y)` is compact
  refine ⟨?_, (isCompact_closedBall y (A * τ)).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp⟩
  -- (i) `C¹` at every point
  rw [contDiff_iff_contDiffAt]
  intro x
  have hsub : ContDiffAt ℝ 1 (fun z : Euclid P => z - y) x := contDiffAt_id.sub contDiffAt_const
  by_cases hxy : x = y
  · -- near `y` we have `‖z - y‖ / τ < 1`, so the field is `z ↦ z - y`
    subst hxy
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds x hτ] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z - x‖ / τ ≤ 1 := (div_le_one hτ).2 hz.le
    simp [hφ1 _ h1]
  · -- away from `y` the norm `z ↦ ‖z - y‖` is smooth, since `x - y ≠ 0`
    have hnorm : ContDiffAt ℝ 1 (fun z : Euclid P => ‖z - y‖) x := hsub.norm ℝ (sub_ne_zero.2 hxy)
    exact (hφ.comp_contDiffAt x (hnorm.div_const τ)).smul hsub
/-- **Trace of the derivative of a radial field** (Simon Ch. 4, 3.2 and the identity after it,
with a subspace `Q` in place of `TₓM`; chapter-04.txt lines 225–262).  Let `φ` be `C¹` with
`φ = 1` on `(-∞, 1]`, `τ > 0`, `X(z) = φ(|z − y|/τ)(z − y)`, `p = Q.starProjection`, `v = x − y`
and `r = |v|`.  Then `trace(p ∘ DX(x)) = dim Q · φ(r/τ) + (r/τ) φ'(r/τ) (1 − |v − p v|²/r²)`.
`p` is a projection onto `Q`, so `trace p = dim Q` (`LinearMap.IsProj.trace`).  At `x = y` the
field is `z ↦ z − y` on `B_τ(y)`, so `DX(y) = I` and both sides equal `dim Q`.  For `x ≠ y`,
`DX(x) = φ(r/τ) I + φ'(r/τ) τ⁻¹ r⁻¹ ⟨v, ·⟩ v` (`|z − y| = √(|z − y|²)`, chain and product
rules), the rank-one part has trace `φ'(r/τ) τ⁻¹ r⁻¹ ⟨v, p v⟩` (`LinearMap.trace_smulRight`), and
`⟨v, p v⟩ = r² − |v − p v|²` since `v − p v ⊥ p v`. -/
theorem Submission.doragm_rfv_trace_radial_field : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (y x : Euclid P) (φ : ℝ → ℝ) (τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → 0 < τ → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) x).toLinearMap) = (Module.finrank ℝ Q : ℝ) * φ (‖x - y‖ / τ) + ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) - Q.starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) := by
  intro P Q y x φ τ hφ hφ1 hτ
  -- `p = Q.starProjection` is a projection onto `Q`, so its trace is `dim Q`.
  have htr : LinearMap.trace ℝ (Euclid P) Q.starProjection.toLinearMap = Module.finrank ℝ Q :=
    LinearMap.IsProj.trace ⟨fun w => Q.starProjection_apply_mem w,
      fun w hw => Submodule.starProjection_eq_self_iff.mpr hw⟩
  by_cases hxy : x = y
  · -- On `B(y, τ)` the field is `z ↦ z - y`, whose derivative is the identity.
    subst hxy
    have hev : (fun z : Euclid P => φ (‖z - x‖ / τ) • (z - x)) =ᶠ[𝓝 x] fun z => z - x := by
      filter_upwards [Metric.ball_mem_nhds x hτ] with z hz
      rw [hφ1 _ ((div_le_one hτ).mpr (mem_ball_iff_norm.mp hz).le), one_smul]
    rw [hev.fderiv_eq, fderiv_sub_const, fderiv_fun_id]
    simp [htr, hφ1 0 zero_le_one]
  · -- Derivative of `z ↦ ‖z - y‖` at `x ≠ y`, via `√(‖z - y‖²)`.
    have hr0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hsub : HasFDerivAt (fun z : Euclid P => z - y) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const y
    have hnorm := hsub.norm_sq.sqrt (pow_ne_zero 2 hr0.ne')
    have hsqrt : (fun z : Euclid P => √(‖z - y‖ ^ 2)) = fun z => ‖z - y‖ :=
      funext fun z => Real.sqrt_sq (norm_nonneg _)
    rw [hsqrt] at hnorm
    -- Chain rule for `c(z) = φ(‖z - y‖ / τ)`, then the product rule for `c(z) • (z - y)`.
    have hφd : HasDerivAt (fun t => φ (t / τ)) (deriv φ (‖x - y‖ / τ) * (1 / τ)) ‖x - y‖ :=
      ((hφ.differentiable one_ne_zero) _).hasDerivAt.comp _
        (HasDerivAt.div_const (hasDerivAt_id' ‖x - y‖) τ)
    have hX := (hφd.comp_hasFDerivAt x hnorm).smul hsub
    rw [show (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) =
      ((fun t => φ (t / τ)) ∘ fun z => ‖z - y‖) • fun z => z - y from rfl, hX.fderiv]
    -- `p ∘ (a I + ℓ(·) v) = a p + ℓ(·) p v`; the rank-one part has trace `ℓ(p v)`.
    have key : ∀ (a : ℝ) (ℓ : Euclid P →L[ℝ] ℝ) (v : Euclid P),
        LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ
          (a • ContinuousLinearMap.id ℝ (Euclid P) + ℓ.smulRight v).toLinearMap) =
          a * Module.finrank ℝ Q + ℓ (Q.starProjection v) := by
      intro a ℓ v
      have hcomp : Q.starProjection.toLinearMap ∘ₗ
          (a • ContinuousLinearMap.id ℝ (Euclid P) + ℓ.smulRight v).toLinearMap =
          a • Q.starProjection.toLinearMap +
            (ℓ : Euclid P →ₗ[ℝ] ℝ).smulRight (Q.starProjection v) := by
        ext w
        simp
      rw [hcomp, map_add, map_smul, htr, LinearMap.trace_smulRight, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
    -- Pythagoras: `⟨v, p v⟩ = ‖v‖² - ‖v - p v‖²`, as `v - p v ⊥ p v`.
    have hinner : inner ℝ (x - y) (Q.starProjection (x - y)) =
        ‖x - y‖ ^ 2 - ‖(x - y) - Q.starProjection (x - y)‖ ^ 2 := by
      have h0 := Submodule.starProjection_inner_eq_zero (K := Q) (x - y)
        (Q.starProjection (x - y)) (Q.starProjection_apply_mem _)
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0
      rw [norm_sub_sq_real (x - y) (Q.starProjection (x - y))]
      linarith
    rw [key]
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
      Real.sqrt_sq (norm_nonneg _), hinner]
    field_simp
    ring
/-- **Simon Ch. 4, 2.2 and 4.1.1**: for `R = (M, θ, ξ)` and `X ∈ C¹_c(U; ℝᴾ)` with `x ↦ p_{TₓM}`
`μ_R`-measurable, `div_M X` is `μ_R`-integrable and `δV(X) = ∫_M θ div_M X dHⁿ = ∫ div_M X dμ_R`,
`μ_R = θ Hⁿ⌞M`.  `div_M X(x) = tr(p_{TₓM} ∘ DX(x))` is bounded by `‖tr‖ ‖DX(x)‖`, and it vanishes
off the compact `spt X ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dsmc_firstVariation_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure ∧ R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
  intro P n U R X hX hcpt hU hp
  -- the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and `div_M X(x) = tr(p_x ∘ DX(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ x, tangentialDivergence n R.carrier X x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ X x) := fun x => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hD : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- `div_M X` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
      (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp.aestronglyMeasurable
      hD.aestronglyMeasurable
  -- `|div_M X(x)| ≤ ‖tr‖ C 1_K(x)`, `K = spt X`, `C = sup ‖DX‖`
  obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hcpt.fderiv ℝ)
  have hKm : MeasurableSet (tsupport X) := (isClosed_tsupport X).measurableSet
  have hbound : ∀ x, ‖tangentialDivergence n R.carrier X x‖ ≤
      (tsupport X).indicator (fun _ => ‖tr‖ * C) x := by
    intro x
    rw [hdiv]
    by_cases hxK : x ∈ tsupport X
    · rw [Set.indicator_of_mem hxK]
      refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _) zero_le_one
    · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
        ContinuousLinearMap.comp_zero, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport X) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport X) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.firstVariation]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
/-- The approximate tangent planes `TₓM` of `R = τ(M, θ, ξ)` are `n`-dimensional for `μ_R`-a.e.
`x`: by `R.orients`, `Hⁿ⌞M`-a.e. `x` has an approximate tangent plane (Simon Ch. 3, 1.4), which is
`n`-dimensional by definition, and `μ_R = θ Hⁿ⌞M ≪ Hⁿ⌞M`. -/
theorem Submission.dorag_aa_ae_finrank_approxTangentPlane : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
  intro P n U R
  -- `μ_R = θ Hⁿ⌞M ≪ Hⁿ⌞M`, and `Hⁿ⌞M`-a.e. `x` has an approximate tangent plane
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le R.orients] with x hx
  obtain ⟨Q, hQ, -⟩ := hx
  -- `TₓM` is then the chosen approximate tangent plane, whose dimension is `n`
  have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
  rw [approxTangentPlane, dite_eq_left h]
  exact h.choose_spec.finrank_eq
/-- Chebyshev selection of a point with small heights over a finite family (Simon Ch. 5, proof of
Lemma 2.5, (1), (4), (5)).  On `B̄_{2r}(y)` one has `|q|² ≤ (2r)^m |q|² / |x − y|^m`, where
`q = (x − y) − p_{T(x)}(x − y)`, and `B̄_r(ξ) ⊆ B̄_{2r}(y)`; summing over `y ∈ F` gives
`∫_{B̄_r(ξ)} Σ_y |q_{T(x)}(x − y)|² dμ ≤ #F (2r)^m c`.  If every `Q`-point `x ∈ B̄_s(ξ)` had some
`|q_{T(x)}(y − x)|² > λ`, the sum would be `≥ λ` a.e. on `B̄_s(ξ)`, forcing
`λ μ(B̄_s(ξ)) ≤ #F (2r)^m c`. -/
theorem Submission.dorag_aa_exists_low_height_point : ∀ (P m : ℕ) (μ : Measure (Euclid P)) (T : Euclid P → Submodule ℝ (Euclid P)) (Q : Euclid P → Prop) (F : Finset (Euclid P)) (ξ : Euclid P) (r s c lam : ℝ), AEStronglyMeasurable (fun x => (T x).starProjection) μ → (∀ᵐ x ∂μ, Q x) → 0 < r → s ≤ r → (∀ y ∈ F, dist y ξ ≤ r) → (∀ y ∈ F, ∫⁻ x in closedBall y (2 * r), ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) ∂μ ≤ ENNReal.ofReal c) → (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ m * c) < ENNReal.ofReal lam * μ (closedBall ξ s) → ∃ x₀ ∈ closedBall ξ s, Q x₀ ∧ ∀ y ∈ F, ‖(y - x₀) - (T x₀).starProjection (y - x₀)‖ ^ 2 ≤ lam := by
  intro P m μ T Q F ξ r s c lam hT hQ hr hsr hF hc hmass
  -- Step 1: `x ↦ ofReal |q_{T(x)}(x − y)|²` is a.e. measurable (evaluate `p_{T(x)}` at `x − y`)
  have hmeas : ∀ y : Euclid P, AEMeasurable
      (fun x => ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2)) μ := by
    intro y
    have hsub : AEStronglyMeasurable (fun x : Euclid P => x - y) μ :=
      (continuous_id.sub continuous_const).aestronglyMeasurable
    have hproj : AEStronglyMeasurable (fun x => (T x).starProjection (x - y)) μ :=
      (ContinuousLinearMap.id ℝ (Euclid P →L[ℝ] Euclid P)).aestronglyMeasurable_comp₂ hT hsub
    exact ((hsub.sub hproj).norm.pow 2).aemeasurable.ennreal_ofReal
  -- Steps 2–3: `∫_{B̄_r(ξ)} |q_{T(x)}(x − y)|² dμ ≤ (2r)^m c` for every `y ∈ F`
  have hstep3 : ∀ y ∈ F, ∫⁻ x in closedBall ξ r,
      ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ ≤
        ENNReal.ofReal ((2 * r) ^ m * c) := by
    intro y hy
    have hball : closedBall ξ r ⊆ closedBall y (2 * r) := by
      intro x hx
      rw [mem_closedBall] at hx ⊢
      calc dist x y ≤ dist x ξ + dist ξ y := dist_triangle x ξ y
        _ ≤ r + r := add_le_add hx (by rw [dist_comm]; exact hF y hy)
        _ = 2 * r := by ring
    -- Simon (1): `|q|² ≤ (2r)^m |q|² / |x − y|^m` on `B̄_{2r}(y)`
    have hpt : ∀ᵐ x ∂μ.restrict (closedBall y (2 * r)),
        ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ≤
          ENNReal.ofReal ((2 * r) ^ m) *
            ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) := by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [mem_closedBall, dist_eq_norm] at hx
      rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
      · have hxy : x - y = 0 := norm_eq_zero.mp h0.symm
        simp [hxy]
      · calc ‖(x - y) - (T x).starProjection (x - y)‖ ^ 2
            = ‖x - y‖ ^ m * (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) := by
              rw [mul_div_cancel₀ _ (pow_pos hpos m).ne']
          _ ≤ (2 * r) ^ m * (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx m) (by positivity)
    calc ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ
        ≤ ∫⁻ x in closedBall y (2 * r),
            ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ :=
          lintegral_mono_set hball
      _ ≤ ∫⁻ x in closedBall y (2 * r), ENNReal.ofReal ((2 * r) ^ m) *
            ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) ∂μ :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal ((2 * r) ^ m) * ∫⁻ x in closedBall y (2 * r),
            ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ m) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((2 * r) ^ m) * ENNReal.ofReal c := by gcongr; exact hc y hy
      _ = ENNReal.ofReal ((2 * r) ^ m * c) := (ENNReal.ofReal_mul (by positivity)).symm
  -- Step 4: summation over `F`
  have hstep4 : ∫⁻ x in closedBall ξ r,
      ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ ≤
        (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ m * c) := by
    rw [lintegral_finsetSum' F (fun y _ => (hmeas y).restrict)]
    calc ∑ y ∈ F, ∫⁻ x in closedBall ξ r,
          ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ
        ≤ ∑ _y ∈ F, ENNReal.ofReal ((2 * r) ^ m * c) := Finset.sum_le_sum hstep3
      _ = (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ m * c) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 5: otherwise the sum is `≥ λ` a.e. on `B̄_s(ξ)`, contradicting the mass condition
  by_contra hcon
  push Not at hcon
  have hae : ∀ᵐ x ∂μ.restrict (closedBall ξ s), ENNReal.ofReal lam ≤
      ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall, ae_restrict_of_ae hQ] with x hx hQx
    obtain ⟨y, hy, hlt⟩ := hcon x hx hQx
    have hsymm : ‖(x - y) - (T x).starProjection (x - y)‖ =
        ‖(y - x) - (T x).starProjection (y - x)‖ := by
      rw [← neg_sub y x, map_neg, ← norm_neg]
      congr 1
      abel
    calc ENNReal.ofReal lam
        ≤ ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) := by
          rw [hsymm]
          exact ENNReal.ofReal_le_ofReal hlt.le
      _ ≤ ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) :=
          Finset.single_le_sum
            (f := fun y => ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2))
            (fun _ _ => zero_le) hy
  have hle : ENNReal.ofReal lam * μ (closedBall ξ s) ≤
      (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ m * c) :=
    calc ENNReal.ofReal lam * μ (closedBall ξ s)
        = ∫⁻ _x in closedBall ξ s, ENNReal.ofReal lam ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in closedBall ξ s,
            ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ :=
          lintegral_mono_ae hae
      _ ≤ ∫⁻ x in closedBall ξ r,
            ∑ y ∈ F, ENNReal.ofReal (‖(x - y) - (T x).starProjection (x - y)‖ ^ 2) ∂μ :=
          lintegral_mono_set (closedBall_subset_closedBall hsr)
      _ ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ m * c) := hstep4
  exact absurd hmass (not_lt.mpr hle)
/-- **Height bounds from a net near an affine plane** (Simon Ch. 5, proof of Lemma 2.5, (6) and the
`L²` height bound; chapter-05.txt lines 356–374).  Write `q(v) = v − p_S(v)`.  If every
`x ∈ spt μ ∩ B̄_r(ξ)` lies within `s` of some `y ∈ F`, `|q(y − x₀)| ≤ L` for `y ∈ F` and
`|x₀ − ξ| ≤ s`, then (a) `|q(x − ξ)| ≤ 2s + L` on `spt μ ∩ B̄_r(ξ)`, because `q = p_{S⊥}` is additive
and `1`-Lipschitz and `x − ξ = (x − y) + (y − x₀) + (x₀ − ξ)`; (b)
`∫_{B̄_r(ξ)} |q(x − ξ)|² dμ ≤ (2s + L)² μ(B̄_r(ξ))`, since `spt μ` is `μ`-conull, so (a) holds
`μ⌞B̄_r(ξ)`-a.e. -/
theorem Submission.dorag_aa_height_bounds_of_net : ∀ (P : ℕ) (μ : Measure (Euclid P)) (S : Submodule ℝ (Euclid P)) (F : Finset (Euclid P)) (ξ x₀ : Euclid P) (r s L : ℝ), (∀ x ∈ μ.support ∩ closedBall ξ r, ∃ y ∈ F, dist x y ≤ s) → (∀ y ∈ F, ‖(y - x₀) - S.starProjection (y - x₀)‖ ≤ L) → dist x₀ ξ ≤ s → (∀ x ∈ μ.support ∩ closedBall ξ r, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ 2 * s + L) ∧ ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂μ ≤ ENNReal.ofReal ((2 * s + L) ^ 2) * μ (closedBall ξ r) := by
  intro P μ S F ξ x₀ r s L hnet hL hx₀
  -- Step 1: `q(v) = v − p_S(v) = p_{S⊥}(v)` is additive and `|q(v)| ≤ |v|`.
  have hq_le : ∀ v : Euclid P, ‖v - S.starProjection v‖ ≤ ‖v‖ := fun v => by
    rw [← Submodule.starProjection_orthogonal_val]
    exact Sᗮ.norm_starProjection_apply_le v
  have hq_add : ∀ u v : Euclid P, (u + v) - S.starProjection (u + v) =
      (u - S.starProjection u) + (v - S.starProjection v) := fun u v => by
    rw [map_add]
    abel
  -- Step 2 (a): pick `y ∈ F` with `|x − y| ≤ s` and split `x − ξ = (x − y) + (y − x₀) + (x₀ − ξ)`.
  have ha : ∀ x ∈ μ.support ∩ closedBall ξ r,
      ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ 2 * s + L := by
    intro x hx
    obtain ⟨y, hyF, hxy⟩ := hnet x hx
    have hsplit : x - ξ = (x - y) + ((y - x₀) + (x₀ - ξ)) := by abel
    rw [hsplit, hq_add, hq_add]
    calc ‖(x - y - S.starProjection (x - y)) + ((y - x₀ - S.starProjection (y - x₀)) +
          (x₀ - ξ - S.starProjection (x₀ - ξ)))‖
        ≤ ‖x - y - S.starProjection (x - y)‖ + (‖y - x₀ - S.starProjection (y - x₀)‖ +
          ‖x₀ - ξ - S.starProjection (x₀ - ξ)‖) :=
          (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ ‖x - y‖ + (L + ‖x₀ - ξ‖) := add_le_add (hq_le _) (add_le_add (hL y hyF) (hq_le _))
      _ ≤ s + (L + s) := by
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact add_le_add hxy (add_le_add le_rfl hx₀)
      _ = 2 * s + L := by ring
  refine ⟨ha, ?_⟩
  -- Step 3: `spt μ` is `μ`-conull, so `μ⌞B̄_r(ξ)`-a.e. `x` lies in `spt μ ∩ B̄_r(ξ)`.
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := Measure.support_mem_ae
  have hae : ∀ᵐ x ∂(μ.restrict (closedBall ξ r)), x ∈ μ.support ∩ closedBall ξ r := by
    filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_closedBall]
      with x h₁ h₂
    exact ⟨h₁, h₂⟩
  -- Step 4 (b): square the a.e. bound (a) and integrate the constant.
  calc ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂μ
      ≤ ∫⁻ _ in closedBall ξ r, ENNReal.ofReal ((2 * s + L) ^ 2) ∂μ := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (ha x hx) 2)
    _ = ENNReal.ofReal ((2 * s + L) ^ 2) * μ (closedBall ξ r) := setLIntegral_const _ _
/-- **Radial cut-off** (step 1 of the tilt-excess/height estimate, Simon 5.2.1: `ζ ≡ 1` in
`B_{ρ/2}`, `ζ ≡ 0` outside `B_ρ`, `|∇ζ| ≤ 3/ρ`).  For `r > 0` there is a `C¹` function `ζ` on `ℝᴾ`
with `0 ≤ ζ ≤ 1`, `ζ = 1` on `B̄_{r/2}(ξ)`, `tsupport ζ ⊆ B̄_r(ξ)` and `‖Dζ‖ ≤ 3/r`.  Take
`ζ(x) = φ(‖x − ξ‖/r)` for a `C^∞` profile `φ` that is `1` on `(−∞, 1/2]`, `0` on `[1, ∞)` and
`3`-Lipschitz: `φ(σ) = 1 − c⁻¹∫_{1/2}^σ g`, where `g` is a smooth bump on `[1/2, 1]` equal to `1`
on `[7/12, 11/12]` and `c = ∫_{1/2}^1 g ≥ 1/3`.  Then `ζ` is constant near `ξ` and smooth away
from `ξ`, and `(3/r)`-Lipschitz by the reverse triangle inequality. -/
theorem Submission.dorag_th_radial_cutoff : ∀ (P : ℕ) (ξ : Euclid P) (r : ℝ), 0 < r → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall ξ (r / 2), ζ x = 1) ∧ tsupport ζ ⊆ closedBall ξ r ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r := by
  intro P ξ r hr
  -- Steps 1–2: an admissible profile `φ`, the smoothTransition primitive of the Remark
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ : ∃ φ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧
      (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
    -- the bump `g(t) = S(12(t − 1/2)) S(12(1 − t))`
    set g : ℝ → ℝ := fun t =>
      Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_eq
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
      have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
      have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
      exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
    have hg_cont : Continuous g := hg_smooth.continuous
    have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hg_cont.intervalIntegrable a b
    have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
      mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
      (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
        (Real.smoothTransition.le_one _)
    have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
      simp only [hg_eq]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
      simp only [hg_eq]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
    have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
      simp only [hg_eq]
      rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith), mul_one]
    -- `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`
    set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_eq
    have hc_ge : 1 / 3 ≤ c := by
      have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
        · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
          norm_num
        · intro s hs
          rw [uIcc_of_le (by norm_num)] at hs
          exact hg_mid s hs.1 hs.2
      rw [← h]
      exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
        (ae_of_all _ hg_nonneg) (hg_int _ _)
    have hc_pos : 0 < c := by linarith
    have hcinv_le : c⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ hc_pos (by norm_num)]
      linarith
    -- the primitive `F(t) = ∫_{1/2}^t g`, with `F' = g`
    set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_eq
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
      (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
    have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
      contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
        (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
    have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
      simp only [hF_eq]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_ge ht] at hs
        exact hg_left s hs.2
    have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
      simp only [hF_eq, hc_eq]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
      have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro s hs
          rw [uIcc_of_le ht] at hs
          exact hg_right s hs.1
      rw [h, add_zero]
    have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
      rcases le_total t (1 / 2) with ht | ht
      · rw [hF_left t ht]
        exact ⟨le_rfl, hc_pos.le⟩
      rcases le_total 1 t with ht' | ht'
      · rw [hF_right t ht']
        exact ⟨hc_pos.le, le_rfl⟩
      exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
        intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
    -- `φ = 1 − c⁻¹F`, with `φ' = −c⁻¹g`
    have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
      simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
    refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
    · intro t
      obtain ⟨h₀, h₁⟩ := hF_bounds t
      have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
      have h : c⁻¹ * F t ≤ 1 := by
        calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
          _ = 1 := inv_mul_cancel₀ hc_pos.ne'
      exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
    · intro t ht
      simp only [hF_left t ht, mul_zero, sub_zero]
    · intro t ht
      simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
    · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
      rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
      calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
        _ ≤ 3 := by rw [mul_one]; exact hcinv_le
        _ = ((3 : NNReal) : ℝ) := by norm_num
  -- Step 3: `ζ(x) = φ(‖x − ξ‖/r)`.  Step 6: `ζ` is `C^∞` — constant `1` on `B_{r/2}(ξ)`, and
  -- `φ` composed with the smooth map `‖· − ξ‖/r` on `ℝᴾ \ {ξ}`
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => φ (‖x - ξ‖ / r)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x ξ with rfl | hx
    · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x (half_pos hr)] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact hφ_one _ ((div_le_iff₀ hr).2 (by linarith))
    · have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Euclid P => ‖y - ξ‖ / r) x :=
        ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const r
      exact hφ_smooth.contDiffAt.comp x h
  -- Step 7: `ζ` is `(3/r)`-Lipschitz (`φ` is `3`-Lipschitz, reverse triangle inequality)
  have hlip : LipschitzWith (3 / r.toNNReal) fun y : Euclid P => φ (‖y - ξ‖ / r) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [NNReal.coe_div, Real.coe_toNNReal r hr.le]
    calc dist (φ (‖y - ξ‖ / r)) (φ (‖z - ξ‖ / r))
        ≤ (3 : NNReal) * dist (‖y - ξ‖ / r) (‖z - ξ‖ / r) := hφ_lip.dist_le_mul _ _
      _ = 3 / r * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr, NNReal.coe_ofNat]; ring
      _ ≤ 3 / r * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = (3 : NNReal) / r * dist y z := by
          rw [sub_sub_sub_cancel_right, dist_eq_norm, NNReal.coe_ofNat]
  refine ⟨fun x => φ (‖x - ξ‖ / r), hC.of_le (by norm_cast), fun x => hφ_bounds _,
    fun x hx => hφ_one _ ?_, ?_, fun x => ?_⟩
  -- Step 4: plateau, `‖x − ξ‖ ≤ r/2 ⇒ ‖x − ξ‖/r ≤ 1/2`
  · rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hr]
    linarith
  -- Step 5: `ζ = 0` off `B_r(ξ)`, so `tsupport ζ ⊆ closure B_r(ξ) ⊆ B̄_r(ξ)`
  · refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro x hx
    by_contra hxb
    apply hx
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hxb
    exact hφ_zero _ ((le_div_iff₀ hr).2 (by linarith))
  -- Step 7: `‖Dζ(x)‖ ≤ 3/r` from the Lipschitz bound
  · have h := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
    rwa [NNReal.coe_div, Real.coe_toNNReal r hr.le] at h
/-- Step 3 of the tilt-excess/height estimate (Simon Ch. 5, Lemma 2.1, display (2)): for
subspaces `T`, `S` of `ℝᴾ` with `dim T = dim S`,
`trace(p_T ∘ (I − p_S)) = ½ Σᵢ |p_T eᵢ − p_S eᵢ|²`, i.e. `½ |p_T − p_S|²` in the Hilbert–Schmidt
norm.  `p_T`, `p_S` are symmetric idempotents with `trace p_T = dim T`, `trace p_S = dim S`
(`p = ι ∘ π`, cyclicity), so `Σᵢ |(p_T − p_S) eᵢ|² = trace((p_T − p_S)²) =
dim T + dim S − 2 trace(p_T p_S)`, while `trace(p_T (I − p_S)) = dim T − trace(p_T p_S)`. -/
theorem Submission.dorag_th_trace_proj_comp_compl : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)), Module.finrank ℝ T = Module.finrank ℝ S → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) = 1 / 2 * ∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  intro P T S hTS
  -- step 2: `trace p_K = dim K`, as `p_K = ι ∘ π`, `π ∘ ι = id_K` and the trace is cyclic
  have htr : ∀ K : Submodule ℝ (Euclid P),
      LinearMap.trace ℝ (Euclid P) K.starProjection.toLinearMap =
        (Module.finrank ℝ K : ℝ) := by
    intro K
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp :
        K.orthogonalProjectionOnto.toLinearMap ∘ₗ K.subtypeL.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.trace_id]
  set p : Euclid P →L[ℝ] Euclid P := T.starProjection
  set s : Euclid P →L[ℝ] Euclid P := S.starProjection
  have hp : LinearMap.trace ℝ (Euclid P) p.toLinearMap = (Module.finrank ℝ T : ℝ) := htr T
  have hs : LinearMap.trace ℝ (Euclid P) s.toLinearMap = (Module.finrank ℝ S : ℝ) := htr S
  -- step 1: `p` and `s` are symmetric idempotents
  have hp_symm : ∀ u w : Euclid P, inner ℝ (p u) w = inner ℝ u (p w) :=
    T.inner_starProjection_left_eq_right
  have hs_symm : ∀ u w : Euclid P, inner ℝ (s u) w = inner ℝ u (s w) :=
    S.inner_starProjection_left_eq_right
  have hpp : p.toLinearMap ∘ₗ p.toLinearMap = p.toLinearMap := by
    rw [← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap T.isIdempotentElem_starProjection.eq
  have hss : s.toLinearMap ∘ₗ s.toLinearMap = s.toLinearMap := by
    rw [← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection.eq
  -- steps 3–4: `D = p - s` is symmetric, so `Σᵢ ‖D eᵢ‖² = Σᵢ ⟪eᵢ, D (D eᵢ)⟫ = trace (D ∘ D)`
  have hD : ∀ u w : Euclid P, inner ℝ ((p - s) u) w = inner ℝ u ((p - s) w) := by
    intro u w
    simp only [sub_apply, inner_sub_left, inner_sub_right, hp_symm, hs_symm]
  have hsum : ∑ i : Fin P,
      ‖p (EuclideanSpace.single i (1 : ℝ)) - s (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        LinearMap.trace ℝ (Euclid P) ((p - s).toLinearMap ∘ₗ (p - s).toLinearMap) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← hD,
      real_inner_self_eq_norm_sq, sub_apply]
  -- step 6: `p ∘ (I - s) = p - p ∘ s`
  have hlhs : p.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - s).toLinearMap =
      p.toLinearMap - p.toLinearMap ∘ₗ s.toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub, ContinuousLinearMap.coe_id,
      LinearMap.comp_id]
  -- step 5: `D ∘ D = p + s - p ∘ s - s ∘ p` and `trace (s ∘ p) = trace (p ∘ s)`; step 7
  rw [hlhs, hsum, ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, hpp, hss, map_sub, map_sub, map_sub, map_sub,
    LinearMap.trace_comp_comm' p.toLinearMap s.toLinearMap, hp, hs, hTS]
  ring
/-- **Operator norm ≤ Hilbert–Schmidt norm** (step 3 of the tilt-excess estimate, Simon 5.2.1: the
bound `‖p_x − p_S‖ ≤ |p_x − p_S|` used for the cross term).  For every linear map `A` of `ℝᴾ` and
every `v ∈ ℝᴾ`, `|Av|² ≤ (Σᵢ |A eᵢ|²) |v|²`, where `eᵢ` is the standard basis.  Expanding
`v = Σᵢ vᵢ eᵢ` gives `Av = Σᵢ vᵢ A eᵢ`, so `|Av| ≤ Σᵢ |vᵢ| |A eᵢ|` by the triangle inequality;
squaring and Cauchy–Schwarz give `|Av|² ≤ (Σᵢ vᵢ²)(Σᵢ |A eᵢ|²)`, and `Σᵢ vᵢ² = |v|²`. -/
theorem Submission.dorag_th_norm_apply_sq_le_hs : ∀ (P : ℕ) (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P), ‖A v‖ ^ 2 ≤ (∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v‖ ^ 2 := by
  intro P A v
  -- Step 1: `v = Σᵢ vᵢ eᵢ` in the orthonormal basis `EuclideanSpace.basisFun`
  have hv : v = ∑ i : Fin P, v i • EuclideanSpace.single i (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v).symm
  -- Step 2: `Av = Σᵢ vᵢ A eᵢ`, so `|Av| ≤ Σᵢ |vᵢ| |A eᵢ|`
  have hAv : A v = ∑ i : Fin P, v i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  have h1 : ‖A v‖ ≤ ∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAv]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_smul]
  -- Step 3: Cauchy–Schwarz for finite sums, and `Σᵢ |vᵢ|² = |v|²`
  have h2 : (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin P, |v i| ^ 2) * ∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin P, |v i| ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  -- Step 4: both sides of step 2 are nonnegative, so square it and combine with step 3
  calc ‖A v‖ ^ 2 ≤ (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = _ := by rw [h3, mul_comm]
/-- **Divergence of the tilt test field `X(y) = ζ(y)²((y − ξ) − p_S(y − ξ))`** (Simon Ch. 5, proof
of Lemma 2.1: the test field `X = ζ²(x)x′` and the computation of `div_M X`, chapter-05.txt
lines 222–247).  With `w(y) = (y − ξ) − p_S(y − ξ)`, `Dw(x) = I − p_S` and
`D(ζ²)(x) = 2ζ(x)Dζ(x)`, so by the product rule `DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x)`
(`(L ⊗ u)h = L(h)u`).  Composing with `p_T`, linearity of the trace and `trace(L ⊗ u) = L(u)` give
`trace(p_T ∘ DX(x)) = ζ(x)² trace(p_T ∘ (I − p_S)) + 2ζ(x) Dζ(x)[p_T w(x)]`; for
`T = approxTangentPlane n M x` the left side is `tangentialDivergence n M X x = div_M X(x)`. -/
theorem Submission.dorag_th_trace_comp_fderiv_test_field : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)) (ζ : Euclid P → ℝ) (ξ x : Euclid P), DifferentiableAt ℝ ζ x → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))) x).toLinearMap) = ζ x ^ 2 * LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) + 2 * ζ x * fderiv ℝ ζ x (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
  intro P T S ζ ξ x hζ
  -- Step 1: `w(y) = (y − ξ) − p_S(y − ξ)` is affine, with `Dw(x) = I − p_S`.
  have hw : HasFDerivAt (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ))
      (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection) x := by
    have h : HasFDerivAt (fun y : Euclid P => y - ξ) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const ξ
    have h' := h.sub (S.starProjection.hasFDerivAt.comp x h)
    rwa [ContinuousLinearMap.comp_id] at h'
  -- Step 2: `D(ζ²)(x) = 2ζ(x)·Dζ(x)`.
  have hg : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    simpa using hζ.hasFDerivAt.pow 2
  -- Step 3: product rule, `DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x)`.
  have hX : HasFDerivAt (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ)))
      (ζ x ^ 2 • (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection) +
        ((2 * ζ x) • fderiv ℝ ζ x).smulRight ((x - ξ) - S.starProjection (x - ξ))) x :=
    hg.smul hw
  rw [hX.fderiv]
  -- Step 4: `p_T ∘ DX(x) = ζ(x)²(p_T ∘ (I − p_S)) + (2ζ(x)Dζ(x)) ⊗ p_T w(x)`.
  have hcomp : T.starProjection.toLinearMap ∘ₗ (ζ x ^ 2 • (ContinuousLinearMap.id ℝ (Euclid P) -
        S.starProjection) + ((2 * ζ x) • fderiv ℝ ζ x).smulRight
          ((x - ξ) - S.starProjection (x - ξ))).toLinearMap =
      ζ x ^ 2 • (T.starProjection.toLinearMap ∘ₗ
          (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) +
        (2 * ζ x) • (fderiv ℝ ζ x).toLinearMap.smulRight
          (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
    ext v
    simp [smul_smul]
  -- Steps 5–6: the trace is linear and `trace(L ⊗ u) = L(u)`.
  rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, smul_eq_mul, smul_eq_mul,
    ContinuousLinearMap.coe_coe]

/-- **Simon, proof of Ch. 5, Lemma 2.1** (displays (1)–(3)), for an arbitrary cut-off `ζ`: with
`w(x) = (x − ξ) − p_S(x − ξ)`, `∫ζ²|p_{TₓM} − p_S|² dμ ≤ 16∫|Dζ|²|w|² dμ + 4∫κζ²|w| dμ`.
Test the first variation with `X = ζ²w`.  For `μ`-a.e. `x` we have `dim TₓM = n = dim S`, so
`div_M X = ½ζ²|p_{TₓM} − p_S|² + 2ζ Dζ[p_{TₓM}w]` (`dorag_th_trace_comp_fderiv_test_field`,
`dorag_th_trace_proj_comp_compl`).  As `p_S w = 0`, `|p_{TₓM}w| ≤ |p_{TₓM} − p_S| |w|`
(`dorag_th_norm_apply_sq_le_hs`), and `2αβ ≤ ¼α² + 4β²` bounds the cross term; `|⟨X, H⟩| ≤ κζ²|w|`.
Every integrand is bounded and vanishes off the compact `tsupport ζ ⊆ U`, which has finite
`μ`-measure, so the `¼`-term can be absorbed. -/
theorem Submission.dorag_th_tilt_energy_inequality : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (S : Submodule ℝ (Euclid P)) (ξ : Euclid P) (ζ : Euclid P → ℝ), W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → Module.finrank ℝ S = n → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ W → ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure := by
  intro P n U W R H κ S ξ ζ hWU hpM hH hHκ hMC hS hζC hζcpt hζW
  -- Step 1: `κ ≥ 0`.
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- Step 2: `K = tsupport ζ` is compact and `K ⊆ U`, so `μ(K) < ∞`.
  have hKm : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
  have hμK : R.measure (tsupport ζ) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hζcpt (hζW.trans hWU)
  -- Step 3: bounded a.e. strongly measurable functions vanishing off `K` are integrable.
  have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f R.measure → (∃ C, ∀ x, |f x| ≤ C) →
      (∀ x, x ∉ tsupport ζ → f x = 0) → Integrable f R.measure := by
    rintro f hf ⟨C, hC⟩ h0
    have hg : Integrable ((tsupport ζ).indicator (fun _ => C)) R.measure :=
      (integrableOn_const hμK).integrable_indicator hKm
    refine hg.mono' hf (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport ζ
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hC x
    · rw [Set.indicator_of_notMem hx, h0 x hx, norm_zero]
  -- Step 4: `|ζ| ≤ Z`, `‖Dζ‖ ≤ D'`, `|w| ≤ B` on `K`, `ζ = Dζ = 0` off `K`, `0 ≤ a ≤ 4P`.
  have hζ_cont : Continuous ζ := hζC.continuous
  have hDζ_cont : Continuous (fderiv ℝ ζ) := hζC.continuous_fderiv one_ne_zero
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx => fderiv_of_notMem_tsupport ℝ hx
  have hw_cont : Continuous (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ)) := by fun_prop
  obtain ⟨Z, hZ⟩ := hζ_cont.bounded_above_of_compact_support hζcpt
  obtain ⟨D', hD'⟩ := hDζ_cont.bounded_above_of_compact_support (hζcpt.fderiv (𝕜 := ℝ))
  obtain ⟨B₁, hB₁⟩ := IsCompact.exists_bound_of_continuousOn hζcpt hw_cont.continuousOn
  set B := max B₁ 0
  have hB : ∀ x ∈ tsupport ζ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ B :=
    fun x hx => (hB₁ x hx).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ ξ)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' ξ)
  have hζsq : ∀ x, ζ x ^ 2 ≤ Z ^ 2 := by
    intro x
    have := hZ x; rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (ζ x), sq_abs (ζ x)]
  set a : Euclid P → ℝ := fun x => ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
      (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have ha0 : ∀ x, 0 ≤ a x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha_le : ∀ x, a x ≤ 4 * P := by
    intro x
    have : ∀ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
          ≤ 4 := by
      intro i
      have h1 := (approxTangentPlane n R.carrier x).norm_starProjection_apply_le
        (EuclideanSpace.single i (1 : ℝ))
      have h2 := S.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℝ))
      have h3 := norm_sub_le ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ))) (S.starProjection (EuclideanSpace.single i (1 : ℝ)))
      simp only [PiLp.norm_single, norm_one] at h1 h2
      nlinarith [norm_nonneg ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ)))]
    calc a x ≤ ∑ _i : Fin P, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
      _ = 4 * P := by simp [mul_comm]
  -- Step 5: `a` and `x ↦ p_x w(x)` are `μ`-a.e. strongly measurable.
  have ha_meas : AEStronglyMeasurable a R.measure := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (((hpM.apply_continuousLinearMap _).sub aestronglyMeasurable_const).norm).pow 2
  have hpw_meas : AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ))) R.measure :=
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P) => A v)
      (by fun_prop) hpM hw_cont.aestronglyMeasurable
  -- Step 6: `F₁ = ζ²a`, `F₂ = 2ζ Dζ[p_x w]`, `F₃ = ⟨X, H⟩` (`X = ζ²w`), `G₁ = ‖Dζ‖²|w|²` and
  -- `G₂ = κζ²|w|` are bounded and vanish off `K`, hence are `μ`-integrable.
  set F1 : Euclid P → ℝ := fun x => ζ x ^ 2 * a x
  set F2 : Euclid P → ℝ := fun x => 2 * ζ x * fderiv ℝ ζ x
      ((approxTangentPlane n R.carrier x).starProjection ((x - ξ) - S.starProjection (x - ξ)))
  set X : Euclid P → Euclid P := fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))
  set F3 : Euclid P → ℝ := fun x => inner ℝ (X x) (H x)
  set G1 : Euclid P → ℝ := fun x => ‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2
  set G2 : Euclid P → ℝ := fun x => κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖
  have hX_cont : Continuous X := by fun_prop
  have hF1i : Integrable F1 R.measure := by
    refine hint F1 ((hζ_cont.aestronglyMeasurable.pow 2).mul ha_meas)
      ⟨Z ^ 2 * (4 * P), fun x => ?_⟩ (fun x hx => by simp [F1, hζ0 x hx])
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (ha0 x))]
    exact mul_le_mul (hζsq x) (ha_le x) (ha0 x) (sq_nonneg _)
  have hF2i : Integrable F2 R.measure := by
    refine hint F2 ?_ ⟨2 * Z * (D' * B), fun x => ?_⟩ (fun x hx => by simp [F2, hζ0 x hx])
    · exact (aestronglyMeasurable_const.mul hζ_cont.aestronglyMeasurable).mul
        (Continuous.comp_aestronglyMeasurable₂
          (g := fun (L : Euclid P →L[ℝ] ℝ) (v : Euclid P) => L v)
          (by fun_prop) hDζ_cont.aestronglyMeasurable hpw_meas)
    · by_cases hx : x ∈ tsupport ζ
      · have h1 : |ζ x| ≤ Z := by simpa [Real.norm_eq_abs] using hZ x
        have h2 : |fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
            ((x - ξ) - S.starProjection (x - ξ)))| ≤ D' * B := by
          rw [← Real.norm_eq_abs]
          calc _ ≤ ‖fderiv ℝ ζ x‖ * ‖(approxTangentPlane n R.carrier x).starProjection
                ((x - ξ) - S.starProjection (x - ξ))‖ := (fderiv ℝ ζ x).le_opNorm _
            _ ≤ D' * B := by
              apply mul_le_mul (hD' x) _ (norm_nonneg _) hD'0
              exact ((approxTangentPlane n R.carrier x).norm_starProjection_apply_le _).trans
                (hB x hx)
        simp only [F2, abs_mul, abs_two]
        have := mul_le_mul h1 h2 (abs_nonneg _) hZ0
        nlinarith [abs_nonneg (ζ x)]
      · simp only [F2, hζ0 x hx, mul_zero, zero_mul, abs_zero]
        positivity
  have hF3i : Integrable F3 R.measure := by
    refine hint F3 (Continuous.comp_aestronglyMeasurable₂
      (g := fun (u v : Euclid P) => (inner ℝ u v : ℝ)) continuous_inner
      hX_cont.aestronglyMeasurable hH) ⟨Z ^ 2 * B * κ, fun x => ?_⟩
      (fun x hx => by simp [F3, X, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · calc |F3 x| ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
        _ ≤ (Z ^ 2 * B) * κ := by
          apply mul_le_mul _ (hHκ x) (norm_nonneg _) (by positivity)
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
          exact mul_le_mul (hζsq x) (hB x hx) (norm_nonneg _) (sq_nonneg _)
    · simp only [F3, X, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul,
        inner_zero_left, abs_zero]
      positivity
  have hG1i : Integrable G1 R.measure := by
    refine hint G1 ((hDζ_cont.norm.pow 2).mul (hw_cont.norm.pow 2)).aestronglyMeasurable
      ⟨D' ^ 2 * B ^ 2, fun x => ?_⟩ (fun x hx => by simp [G1, hDζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hD' x) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hB x hx) 2) (sq_nonneg _) (sq_nonneg _)
    · simp only [G1, hDζ0 x hx, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, abs_zero]
      positivity
  have hG2i : Integrable G2 R.measure := by
    refine hint G2 ((continuous_const.mul (hζ_cont.pow 2)).mul hw_cont.norm).aestronglyMeasurable
      ⟨κ * Z ^ 2 * B, fun x => ?_⟩ (fun x hx => by simp [G2, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hζsq x) hκ) (hB x hx) (norm_nonneg _)
        (by positivity)
    · simp only [G2, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
        abs_zero]
      positivity
  -- Step 7: `X` is `C¹` with `tsupport X ⊆ K ⊆ W`, so `δV(X) = -∫F₃ dμ`.
  have hXC : ContDiff ℝ 1 X :=
    (hζC.pow 2).smul ((contDiff_id.sub contDiff_const).sub
      (S.starProjection.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hXsupp : tsupport X ⊆ tsupport ζ := by
    apply closure_mono
    intro y hy
    by_contra h
    apply hy
    simp only [Function.mem_support, not_not] at h
    simp [X, h]
  have hXcpt : HasCompactSupport X := hζcpt.mono' ((subset_tsupport X).trans hXsupp)
  have hMCX := hMC X hXC hXcpt (hXsupp.trans hζW)
  -- Step 8: `δV(X) = ∫ div_M X dμ`, since `μ = (Hⁿ⌞M).withDensity θ`.
  have hFV : R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
    have hm : Measurable (fun x => ((R.mult x : NNReal))) :=
      (measurable_from_nat (f := fun m : ℕ => (m : NNReal))).comp R.measurable_mult
    have h := integral_withDensity_eq_integral_smul hm
      (fun x => tangentialDivergence n R.carrier X x) (μ := μHE[n].restrict R.carrier)
    simp only [ENNReal.coe_natCast] at h
    rw [IMRep.measure, h, IMRep.firstVariation]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])
  rw [hFV] at hMCX
  -- Step 9: `dim TₓM = n` for `μ`-a.e. `x` (`R.orients`, `μ ≪ Hⁿ⌞M`).
  have hdim : ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec.1
  -- Step 10: `div_M X = ½F₁ + F₂` `μ`-a.e. (children (D) and (B)).
  have hdiv : (fun x => tangentialDivergence n R.carrier X x) =ᵐ[R.measure]
      (fun x => 1 / 2 * F1 x + F2 x) := by
    filter_upwards [hdim] with x hx
    have hd := Submission.dorag_th_trace_comp_fderiv_test_field P
      (approxTangentPlane n R.carrier x) S ζ ξ x ((hζC.differentiable one_ne_zero) x)
    rw [tangentialDivergence, hd,
      Submission.dorag_th_trace_proj_comp_compl P _ S (by rw [hx, hS])]
    simp only [F1, F2, a]
    ring
  -- Step 11: `½∫F₁ + ∫F₂ = ∫ div_M X dμ = δV(X) = -∫F₃`.
  have hid : 1 / 2 * ∫ x, F1 x ∂R.measure + ∫ x, F2 x ∂R.measure = -∫ x, F3 x ∂R.measure := by
    rw [← integral_const_mul, ← integral_add (hF1i.const_mul _) hF2i, ← integral_congr_ae hdiv]
    exact hMCX
  -- Step 12: cross term.  `p_S w = 0` gives `p_T w = (p_T - p_S)w`, so by child (C)
  -- `|L(p_T w)| ≤ ‖L‖ √|p_T - p_S|² |w|`; then `-F₂ ≤ ¼F₁ + 4G₁` by `2αβ ≤ ¼α² + 4β²`.
  have hcross : ∀ (T : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] ℝ) (v : Euclid P),
      |L (T.starProjection (v - S.starProjection v))| ≤
        ‖L‖ * (Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v - S.starProjection v‖) := by
    intro T L v
    set w := v - S.starProjection v
    have hw : S.starProjection w = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff S).mpr
        (Submodule.sub_starProjection_mem_orthogonal v)
    have heq : T.starProjection w = (T.starProjection - S.starProjection) w := by
      simp [hw]
    have hsq := Submission.dorag_th_norm_apply_sq_le_hs P (T.starProjection - S.starProjection) w
    simp only [sub_apply] at hsq
    have hn : ‖(T.starProjection - S.starProjection) w‖ ≤
        Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg w),
        ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by simpa [sub_apply] using hsq)
    rw [heq]
    calc |L ((T.starProjection - S.starProjection) w)|
        ≤ ‖L‖ * ‖(T.starProjection - S.starProjection) w‖ := by
          rw [← Real.norm_eq_abs]; exact L.le_opNorm _
      _ ≤ _ := by gcongr
  have hb1 : ∀ x, -F2 x ≤ 1 / 4 * F1 x + 4 * G1 x := by
    intro x
    have ht := hcross (approxTangentPlane n R.carrier x) (fderiv ℝ ζ x) (x - ξ)
    set t := fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ)))
    set c := ‖fderiv ℝ ζ x‖
    set s := Real.sqrt (a x)
    set β := ‖(x - ξ) - S.starProjection (x - ξ)‖
    have hs : s ^ 2 = a x := Real.sq_sqrt (ha0 x)
    have hc0 : 0 ≤ c := norm_nonneg _
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hβ0 : 0 ≤ β := norm_nonneg _
    have h1 : -(2 * ζ x * t) ≤ 2 * |ζ x| * |t| := by
      have := neg_le_abs (2 * ζ x * t)
      rwa [abs_mul, abs_mul, abs_two] at this
    have h2 : 2 * |ζ x| * |t| ≤ 2 * |ζ x| * (c * (s * β)) := by gcongr
    have h3 : 2 * |ζ x| * (c * (s * β)) ≤ 1 / 4 * (ζ x ^ 2 * s ^ 2) + 4 * (c ^ 2 * β ^ 2) := by
      nlinarith [sq_nonneg (|ζ x| * s - 4 * c * β), sq_abs (ζ x), abs_nonneg (ζ x)]
    simp only [F1, F2, G1]
    rw [← hs]
    linarith
  -- Step 13: curvature term `-F₃ ≤ |X| |H| ≤ G₂`.
  have hb2 : ∀ x, -F3 x ≤ G2 x := by
    intro x
    calc -F3 x ≤ |F3 x| := neg_le_abs _
      _ ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
      _ = ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * ‖H x‖ := by
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
      _ ≤ ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * κ := by
          gcongr
          exact hHκ x
      _ = G2 x := by simp only [G2]; ring
  -- Step 14: integrate and absorb `¼∫F₁`: `∫F₁ ≤ 16∫G₁ + 4∫G₂`.
  have i1 : ∫ x, -F2 x ∂R.measure ≤ ∫ x, (1 / 4 * F1 x + 4 * G1 x) ∂R.measure :=
    integral_mono hF2i.neg ((hF1i.const_mul _).add (hG1i.const_mul _)) hb1
  have i2 : ∫ x, -F3 x ∂R.measure ≤ ∫ x, G2 x ∂R.measure := integral_mono hF3i.neg hG2i hb2
  rw [integral_neg] at i1 i2
  rw [integral_add (hF1i.const_mul _) (hG1i.const_mul _), integral_const_mul,
    integral_const_mul] at i1
  have hreal : ∫ x, F1 x ∂R.measure ≤ 16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure := by
    linarith
  -- Step 15: `F₁, G₁, G₂ ≥ 0` are integrable, so pass to lower integrals of `ofReal`.
  have hF1n : ∀ x, 0 ≤ F1 x := fun x => mul_nonneg (sq_nonneg _) (ha0 x)
  have hG1n : ∀ x, 0 ≤ G1 x := fun x => by positivity
  have hG2n : ∀ x, 0 ≤ G2 x := fun x => by positivity
  have l1 := ofReal_integral_eq_lintegral_ofReal hF1i (Filter.Eventually.of_forall hF1n)
  have l2 := ofReal_integral_eq_lintegral_ofReal hG1i (Filter.Eventually.of_forall hG1n)
  have l3 := ofReal_integral_eq_lintegral_ofReal hG2i (Filter.Eventually.of_forall hG2n)
  have hI1 : 0 ≤ ∫ x, G1 x ∂R.measure := integral_nonneg hG1n
  have hI2 : 0 ≤ ∫ x, G2 x ∂R.measure := integral_nonneg hG2n
  calc ∫⁻ x, ENNReal.ofReal (F1 x) ∂R.measure = ENNReal.ofReal (∫ x, F1 x ∂R.measure) := l1.symm
    _ ≤ ENNReal.ofReal (16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 16 * ENNReal.ofReal (∫ x, G1 x ∂R.measure) +
          ENNReal.ofReal 4 * ENNReal.ofReal (∫ x, G2 x ∂R.measure) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by rw [l2, l3]
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

/-- **Simon Ch. 4, 3.2–3.3 with generalized mean curvature (3.14)**: the radial first-variation
identity.  The radial field `X(x) = φ(r/τ)(x − y)`, `r = |x − y|`, is `C¹` with support in
`B̄_{Aτ}(y) ⊆ W`, so `∫ div_M X dμ = δV(X) = −∫ X · H dμ` (2.2, and 3.14 (★) in `W`), and
wherever `dim TₓM = n`, i.e. `μ`-a.e., `div_M X = n φ(r/τ) + (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²)`, where
`|(Dr)^⊥|² = |(x − y) − p_{TₓM}(x − y)|²/r²` (3.2).  Both terms are `μ`-integrable: `φ(r/τ)` is
continuous and vanishes off `B̄_{Aτ}(y)`, which has finite `μ`-measure, and the second term is
`div_M X − n φ(r/τ)` `μ`-a.e. -/
theorem Submission.doragm_radial_first_variation : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → closedBall y (A * τ) ⊆ W → (n : ℝ) * (∫ x, φ (‖x - y‖ / τ) ∂R.measure) + (∫ x, ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ∂R.measure) = -∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure := by
  intro P n U W R H _ hWU hp hH y φ A τ hφ h1 h0 hτ hball
  -- `X(x) = φ(r/τ)(x − y)` is `C¹`, with compact support in `B̄_{Aτ}(y) ⊆ W ⊆ U`
  obtain ⟨hXc, hXcpt, hXK⟩ := Submission.doragm_rfv_radial_field_c1 P y φ A τ hφ h1 h0 hτ
  have hXW := hXK.trans hball
  -- `δV(X) = −∫ X · H dμ` by hypothesis, and `δV(X) = ∫ div_M X dμ` with `div_M X ∈ L¹(μ)`
  have hmc := hH _ hXc hXcpt hXW
  obtain ⟨hint, hfv⟩ := Submission.dsmc_firstVariation_eq_integral P n U R _ hXc hXcpt
    (hXW.trans hWU) hp.aemeasurable
  -- `div_M X = n φ(r/τ) + (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²)` wherever `dim TₓM = n`, i.e. `μ`-a.e.
  have hdiv : (fun x => tangentialDivergence n R.carrier
      (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) x) =ᵐ[R.measure] fun x =>
      (n : ℝ) * φ (‖x - y‖ / τ) + ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) *
        (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
          ‖x - y‖ ^ 2) := by
    filter_upwards [Submission.dorag_aa_ae_finrank_approxTangentPlane P n U R] with x hx
    have htr := Submission.doragm_rfv_trace_radial_field P (approxTangentPlane n R.carrier x) y x
      φ τ hφ h1 hτ
    rw [hx] at htr
    exact htr
  -- `φ(r/τ)` is continuous and vanishes off the compact `K = B̄_{Aτ}(y)`, and `μ(K) < ∞`
  have hK : IsCompact (closedBall y (A * τ)) := isCompact_closedBall y (A * τ)
  have hKfin := (Submission.rsd_imrep_compact_measure_ne_top P n U R _ hK (hball.trans hWU)).2
  have hf₁c : Continuous fun x : Euclid P => φ (‖x - y‖ / τ) :=
    hφ.continuous.comp ((continuous_id.sub continuous_const).norm.div_const τ)
  have hf₁0 : ∀ x, x ∉ closedBall y (A * τ) → φ (‖x - y‖ / τ) = 0 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact h0 _ ((le_div_iff₀ hτ).2 hx.le)
  obtain ⟨C, hC⟩ := hf₁c.bounded_above_of_compact_support (HasCompactSupport.intro hK hf₁0)
  have hf₁ : Integrable (fun x : Euclid P => φ (‖x - y‖ / τ)) R.measure := by
    refine ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const (C := C) hKfin)).mono'
      hf₁c.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall y (A * τ)
    · rw [indicator_of_mem hx]
      exact hC x
    · rw [indicator_of_notMem hx, hf₁0 x hx, norm_zero]
  -- the second term is `div_M X − n φ(r/τ)` `μ`-a.e., hence integrable as well
  have hf₂ : Integrable (fun x => ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) *
      (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
        ‖x - y‖ ^ 2)) R.measure := by
    refine (hint.sub (hf₁.const_mul (n : ℝ))).congr ?_
    filter_upwards [hdiv] with x hx
    simp only [Pi.sub_apply, hx, add_sub_cancel_left]
  -- `n ∫ φ(r/τ) dμ + ∫ (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²) dμ = ∫ div_M X dμ = δV(X) = −∫ X · H dμ`
  rw [← integral_const_mul, ← integral_add (hf₁.const_mul _) hf₂, ← integral_congr_ae hdiv,
    ← hfv, hmc]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => real_inner_smul_left _ _ _)

/-- **Simon Ch. 4, 3.4–3.5 and 3.16** (smoothed annular monotonicity bounds, `|H| ≤ κ`): if
`A > 1`, `0 < s < t` and `B̄_{At}(y) ⊆ W`, then with `c = Aκ` and
`F_y = |(x − y) − p_x(x − y)|²/|x − y|^{n+2}`,
`∫_{B̄_t∖B̄_{As}} F_y dμ + e^{cs}s⁻ⁿμ(B̄_s) ≤ e^{ct}t⁻ⁿμ(B̄_{At})` and
`e^{−ct}t⁻ⁿμ(B̄_t) ≤ e^{−cs}s⁻ⁿμ(B̄_{As}) + Aⁿ∫_{B̄_{At}∖B̄_s} F_y dμ` in `[0, ∞]`.  For the profile
`φ`, `N = |(x − y) − p_x(x − y)|²/|x − y|²` and `q = N/max(s, |x − y|)ⁿ`, the scale functions
`I(τ) = ∫ φ(r/τ) dμ` and `G(τ) = ∫ φ(r/τ) q dμ` satisfy `n I − τ I' + τ J' = −h` (radial first
variation), `|h| ≤ Aκτ I` and `G' ≤ τ⁻ⁿ J' ≤ Aⁿ G'` on `[s, t]`; the integrating-factor comparison
bounds `G(t) − G(s)`, which lies between the two annular integrals, while `I(τ)` lies between
`μ(B̄_τ)` and `μ(B̄_{Aτ})`. -/
theorem Submission.doragm_smoothed_annular_bounds : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (A s t : ℝ), 1 < A → 0 < s → s < t → closedBall y (A * t) ⊆ W → (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (A * κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n) * R.measure (closedBall y (A * t)) ∧ ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n) * R.measure (closedBall y (A * s)) + ENNReal.ofReal (A ^ n) * ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure := by
  intro P n U W R H κ hW hWU hp _ hκ hFV y A s t hA hs hst hball
  -- Step 1: `A > 0`, `t > 0`, and `c = Aκ ≥ 0` because `κ ≥ ‖H 0‖ ≥ 0`
  have hA0 : 0 < A := zero_lt_one.trans hA
  have ht : 0 < t := hs.trans hst
  have hc : 0 ≤ A * κ := mul_nonneg hA0.le ((norm_nonneg _).trans (hκ 0))
  -- a radius `R₀ = δ + At > At` with `B̄_{R₀}(y) ⊆ W`; this compact subset of `U` has finite mass
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_closedBall y (A * t)).exists_cthickening_subset_open hW hball
  rw [cthickening_closedBall hδ.le (mul_pos hA0 ht).le] at hδW
  have hAτR₀ : ∀ τ ∈ Icc s t, A * τ < δ + A * t := fun τ hτ =>
    (mul_le_mul_of_nonneg_left hτ.2 hA0.le).trans_lt (lt_add_of_pos_left _ hδ)
  have hμR₀ : R.measure (closedBall y (δ + A * t)) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall _ _) (hδW.trans hWU)
  -- Step 2: the cutoff profile `φ`
  obtain ⟨φ, hφC, hφanti, hφbd, hφ1, hφ0, hφ'le, hφ'ne⟩ :=
    Submission.doragm_sab_cutoff_profile A hA
  -- Step 3: `N = |(x - y) - p_x(x - y)|²/|x - y|² ∈ [0, 1]` and `q = N/max(s, |x - y|)ⁿ ∈ [0, s⁻ⁿ]`
  obtain ⟨N, hN⟩ : ∃ N : Euclid P → ℝ, ∀ x, N x =
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hN01 : ∀ x, 0 ≤ N x ∧ N x ≤ 1 := by
    intro x
    rw [hN]
    refine ⟨by positivity,
      div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)⟩
    -- `v - p_x v` is the projection of `v` onto `(TₓM)^⊥`
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_starProjection_apply_le _ _
  have hr : Continuous fun x : Euclid P => ‖x - y‖ := (continuous_id.sub continuous_const).norm
  have hNm : AEStronglyMeasurable N R.measure := by
    have hpx : AEStronglyMeasurable
        (fun x => (approxTangentPlane n R.carrier x).starProjection (x - y)) R.measure :=
      (ContinuousLinearMap.id ℝ (Euclid P →L[ℝ] Euclid P)).aestronglyMeasurable_comp₂ hp
        (continuous_id.sub continuous_const).aestronglyMeasurable
    rw [show N = _ from funext hN]
    exact ((((continuous_id.sub continuous_const).aestronglyMeasurable.sub hpx).norm.aemeasurable
      |>.pow_const 2).div (hr.pow 2).measurable.aemeasurable).aestronglyMeasurable
  have hqm : AEStronglyMeasurable (fun x => N x / (max s ‖x - y‖) ^ n) R.measure :=
    (hNm.aemeasurable.div
      ((continuous_const.max hr).pow n).measurable.aemeasurable).aestronglyMeasurable
  have hq0 : ∀ x, 0 ≤ N x / (max s ‖x - y‖) ^ n := fun x =>
    div_nonneg (hN01 x).1 (pow_nonneg (hs.le.trans (le_max_left _ _)) n)
  have hqB : ∀ x, ‖N x / (max s ‖x - y‖) ^ n‖ ≤ 1 / s ^ n := by
    intro x
    rw [Real.norm_of_nonneg (hq0 x)]
    have hsn : 0 < s ^ n := pow_pos hs n
    have hDs : s ^ n ≤ (max s ‖x - y‖) ^ n := pow_le_pow_left₀ hs.le (le_max_left _ _) n
    calc N x / (max s ‖x - y‖) ^ n ≤ 1 / (max s ‖x - y‖) ^ n :=
          div_le_div_of_nonneg_right (hN01 x).2 (hsn.le.trans hDs)
      _ ≤ 1 / s ^ n := one_div_le_one_div_of_le hsn hDs
  -- `q = F_y` where `|x - y| > s`
  have hFq : ∀ x, s < ‖x - y‖ →
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)
        = N x / (max s ‖x - y‖) ^ n := by
    intro x hx
    rw [max_eq_right hx.le, hN]
    ring
  -- Step 4: integrability and `τ`-derivatives of the cutoff integrals (weights `1`, `q`, `N`)
  have hcd1 : ∀ τ ∈ Icc s t, Integrable (fun x => φ (‖x - y‖ / τ)) R.measure ∧
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ)) R.measure ∧
      HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) ∂R.measure)
        (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure) τ := fun τ hτ => by
    simpa only [mul_one] using Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ
      (fun _ => 1) A 1 τ (δ + A * t) hφC hφ0 hA0 (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀
      aestronglyMeasurable_const (fun _ => by simp)
  have hcdq : ∀ τ ∈ Icc s t,
      Integrable (fun x => φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) R.measure ∧
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) *
        (N x / (max s ‖x - y‖) ^ n)) R.measure ∧
      HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)
        (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)
          ∂R.measure) τ := fun τ hτ =>
    Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ
      (fun x => N x / (max s ‖x - y‖) ^ n) A (1 / s ^ n) τ (δ + A * t) hφC hφ0 hA0
      (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀ hqm hqB
  have hcdN : ∀ τ ∈ Icc s t,
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x) R.measure :=
    fun τ hτ => (Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ N A 1 τ (δ + A * t)
      hφC hφ0 hA0 (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀ hNm
      (fun x => by rw [Real.norm_of_nonneg (hN01 x).1]; exact (hN01 x).2)).2.1
  -- Step 5: the identity `(E)`: `n I − τ I' + τ J' = −h` on `[s, t]`, from the radial first
  -- variation and `(r/τ) φ'(r/τ) (1 − N) = (−τ)(−(r/τ²) φ'(r/τ)) + τ (−(r/τ²) φ'(r/τ)) N`
  have hE : ∀ τ ∈ Icc s t, (n : ℝ) * (∫ x, φ (‖x - y‖ / τ) ∂R.measure)
      - τ * (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure)
      + τ * (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂R.measure)
      = -∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure := by
    intro τ hτ
    have hτ0 : 0 < τ := hs.trans_le hτ.1
    have hrv := Submission.doragm_radial_first_variation P n U W R H hW hWU hp hFV y φ A τ
      hφC hφ1 hφ0 hτ0
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hτ.2 hA0.le)).trans hball)
    have hsplit : ∫ x, ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) -
        (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ∂R.measure
        = ∫ x, (-τ * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ)) +
          τ * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x)) ∂R.measure := by
      congr 1
      ext x
      rw [← hN x]
      generalize deriv φ (‖x - y‖ / τ) = d
      field_simp
      ring
    rw [hsplit, integral_add ((hcd1 τ hτ).2.1.const_mul _) ((hcdN τ hτ).const_mul _),
      integral_const_mul, integral_const_mul] at hrv
    linarith
  -- Steps 6–7: the curvature bound `|h| ≤ Aκτ I` and the comparison `G' ≤ τ⁻ⁿ J' ≤ Aⁿ G'`
  have hsq := fun τ (hτ : τ ∈ Icc s t) =>
    Submission.doragm_sab_deriv_weight_squeeze P n R.measure y φ N A s τ hA hs hτ.1 hφ'le hφ'ne
      (fun x => (hN01 x).1) (hcdq τ hτ).2.1 (hcdN τ hτ)
  -- Steps 8–9: the integrating-factor comparison on `[s, t]`
  obtain ⟨ha, hb⟩ := Submission.doragm_sab_exp_ratio_compare n (A * κ) (A ^ n) s t
    (fun τ => ∫ x, φ (‖x - y‖ / τ) ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure)
    (fun τ => ∫ x, φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)
      ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂R.measure)
    (fun τ => ∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure)
    hc hs hst (fun τ hτ => (hcd1 τ hτ).2.2) (fun τ hτ => (hcdq τ hτ).2.2) hE
    (fun τ hτ => Submission.doragm_sab_curvature_term_le P R.measure y H φ κ A τ
      (hs.trans_le hτ.1) (fun u => (hφbd u).1) hφ0 hκ (hcd1 τ hτ).1)
    (fun τ hτ => (hsq τ hτ).1) (fun τ hτ => (hsq τ hτ).2.1) (fun τ hτ => (hsq τ hτ).2.2)
  -- Step 10: `μ(B̄_τ) ≤ I(τ) ≤ μ(B̄_{Aτ})` at `τ = s, t`, and the annular comparison
  have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
  obtain ⟨hms, hmAs⟩ :=
    Submission.doragm_sab_cutoff_mass_sandwich P R.measure y φ A s hs hφbd hφ1 hφ0 (hcd1 s hsI).1
  obtain ⟨hmt, hmAt⟩ :=
    Submission.doragm_sab_cutoff_mass_sandwich P R.measure y φ A t ht hφbd hφ1 hφ0 (hcd1 t htI).1
  obtain ⟨hΔ, hX, hY⟩ := Submission.doragm_sab_annulus_increment_sandwich P R.measure y φ
    (fun x => N x / (max s ‖x - y‖) ^ n)
    (fun x => ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
      ‖x - y‖ ^ (n + 2)) A s t hA hs hst.le hφanti hφbd hφ1 hφ0 hq0 hFq (hcdq s hsI).1
    (hcdq t htI).1
  beta_reduce at ha hb hΔ hX hY
  have hIs : 0 ≤ ∫ x, φ (‖x - y‖ / s) ∂R.measure := integral_nonneg fun x => (hφbd _).1
  -- Steps 11–12: combine in `[0, ∞]`
  refine ⟨?_, ?_⟩
  · calc _ ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) +
          ENNReal.ofReal (Real.exp (A * κ * s) / s ^ n) *
            ENNReal.ofReal (∫ x, φ (‖x - y‖ / s) ∂R.measure) := by gcongr
      _ = ENNReal.ofReal (((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) +
          Real.exp (A * κ * s) / s ^ n * ∫ x, φ (‖x - y‖ / s) ∂R.measure) := by
        rw [ENNReal.ofReal_add hΔ (mul_nonneg (by positivity) hIs),
          ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n * ∫ x, φ (‖x - y‖ / t) ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n) *
          ENNReal.ofReal (∫ x, φ (‖x - y‖ / t) ∂R.measure) := ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by gcongr
  · calc _ ≤ ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n) *
          ENNReal.ofReal (∫ x, φ (‖x - y‖ / t) ∂R.measure) := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n * ∫ x, φ (‖x - y‖ / t) ∂R.measure) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n * (∫ x, φ (‖x - y‖ / s) ∂R.measure) +
          A ^ n * ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n) *
            ENNReal.ofReal (∫ x, φ (‖x - y‖ / s) ∂R.measure) +
          ENNReal.ofReal (A ^ n) *
            ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
              ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hIs) (mul_nonneg (by positivity) hΔ),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by gcongr

/-- **Annular monotonicity with bounded mean curvature** (Simon Ch. 4, 3.5 → 3.6 and 3.17,
"letting `ε ↓ 0`").  Let `μ = θ Hⁿ⌞M`, `|H| ≤ κ`,
`F_y(x) = |(x − y) − p_{TₓM}(x − y)|²/|x − y|^{n+2}` and `0 < s < t` with `B̄_t(y) ⊆ W`.  Then
(M1) `∫_{B̄_t∖B̄_s} F_y dμ + e^{κs} s⁻ⁿ μ(B̄_s) ≤ e^{κt} t⁻ⁿ μ(B̄_t)` and
(M2) `e^{−κt} t⁻ⁿ μ(B̄_t) ≤ e^{−κs} s⁻ⁿ μ(B̄_s) + ∫_{B̄_t∖B̄_s} F_y dμ`.

Choose `δ₀ > 0` with `B̄_{t+δ₀}(y) ⊆ W` and the widths `A_m = 1 + (δ₀/t)/(m + 1) ↓ 1`, and apply
the smoothed bounds `Submission.doragm_smoothed_annular_bounds` with `A = A_m`.  As `m → ∞`,
`μ(B̄_{A_mρ}) → μ(B̄_ρ)` by continuity from above (`μ(B̄_{t+δ₀}) < ∞`).  For `ν = F_y μ` the inner
annuli `B̄_t∖B̄_{A_ms}` increase to `B̄_t∖B̄_s`, and the outer annuli `B̄_{A_mt}∖B̄_s` decrease to
it with `ν(B̄_{A_0t}∖B̄_s) ≤ s⁻ⁿ μ(B̄_{A_0t}) < ∞`, because `F_y(x) ≤ |x − y|⁻ⁿ`.  The coefficients
converge, and `e^{κs} ≤ e^{A_mκs}` as `κ ≥ 0`; passing to the limit gives (M1) and (M2). -/
theorem Submission.doragm_annular_monotonicity : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) ∧ ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * R.measure (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure := by
  intro P n U W R H κ hW hWU hp hH hHκ hFV y s t hs hst hBt
  have hsm := Submission.doragm_smoothed_annular_bounds P n U W R H κ hW hWU hp hH hHκ hFV y
  have ht : 0 < t := hs.trans hst
  -- `κ ≥ 0`, since `‖H y‖ ≤ κ`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ y)
  -- `μ` is finite on compact subsets of `U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Step 1: `B̄_{t+δ₀}(y) ⊆ W`, so `μ(B̄_ρ(y)) < ∞` for `ρ ≤ t + δ₀`
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := (isCompact_closedBall y t).exists_cthickening_subset_open hW hBt
  rw [cthickening_closedBall hδ₀.le ht.le] at hδ₀W
  have hfinB : ∀ ρ, ρ ≤ δ₀ + t → R.measure (closedBall y ρ) ≠ ∞ := fun ρ hρ =>
    hfin _ (isCompact_closedBall y ρ) ((closedBall_subset_closedBall hρ).trans (hδ₀W.trans hWU))
  -- Step 2: the widths `A_m = 1 + (δ₀/t)/(m + 1)`: `A_m > 1`, `A_m ↓ 1` and `A_m t ≤ t + δ₀`
  obtain ⟨A, hA1, hAanti, hAlim, hAt⟩ : ∃ A : ℕ → ℝ, (∀ m, 1 < A m) ∧ Antitone A ∧
      Tendsto A atTop (𝓝 1) ∧ ∀ m, A m * t ≤ δ₀ + t := by
    have hc : 0 < δ₀ / t := div_pos hδ₀ ht
    have he : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
    have he1 : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ≤ 1 := fun m =>
      (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    refine ⟨fun m => 1 + δ₀ / t * (1 / ((m : ℝ) + 1)), fun m => ?_, fun i j hij => ?_, ?_,
      fun m => ?_⟩
    · dsimp only
      linarith [mul_pos hc (he m)]
    · have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
      have := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1) hij') hc.le
      dsimp only
      linarith
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ₀ / t)).const_add 1
      rwa [mul_zero, add_zero] at h
    · have h2 : (1 + δ₀ / t * (1 / ((m : ℝ) + 1))) * t = t + δ₀ * (1 / ((m : ℝ) + 1)) := by
        field_simp
      dsimp only
      rw [h2]
      linarith [mul_le_mul_of_nonneg_left (he1 m) hδ₀.le]
  have hBA : ∀ m, closedBall y (A m * t) ⊆ W := fun m =>
    (closedBall_subset_closedBall (hAt m)).trans hδ₀W
  -- Step 3: for `0 < ρ ≤ t`, the balls `B̄_{A_mρ}` decrease to `B̄_ρ`, so
  -- `μ(B̄_{A_mρ}) → μ(B̄_ρ)` (continuity from above)
  have hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ t →
      Antitone (fun m => closedBall y (A m * ρ)) ∧
      (⋂ m, closedBall y (A m * ρ)) = closedBall y ρ ∧
      Tendsto (fun m => R.measure (closedBall y (A m * ρ))) atTop
        (𝓝 (R.measure (closedBall y ρ))) := by
    intro ρ hρ hρt
    have hanti : Antitone (fun m => closedBall y (A m * ρ)) := fun i j hij =>
      closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (hAanti hij) hρ.le)
    have hinter : (⋂ m, closedBall y (A m * ρ)) = closedBall y ρ := by
      ext x
      simp only [mem_iInter, mem_closedBall]
      refine ⟨fun h => ?_, fun h m => h.trans (le_mul_of_one_le_left hρ.le (hA1 m).le)⟩
      have hlim : Tendsto (fun m => A m * ρ) atTop (𝓝 (1 * ρ)) := hAlim.mul_const ρ
      rw [one_mul] at hlim
      exact ge_of_tendsto' hlim h
    have hfin0 : R.measure (closedBall y (A 0 * ρ)) ≠ ∞ :=
      hfinB _ ((mul_le_mul_of_nonneg_left hρt (by linarith [hA1 0])).trans (hAt 0))
    have h := tendsto_measure_iInter_atTop (μ := R.measure)
      (fun m => measurableSet_closedBall.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rw [hinter] at h
    exact ⟨hanti, hinter, h⟩
  obtain ⟨hanti_s, hinter_s, hlim_s⟩ := hball s hs hst.le
  obtain ⟨hanti_t, hinter_t, hlim_t⟩ := hball t ht le_rfl
  have hfin_s : R.measure (closedBall y s) ≠ ∞ := hfinB s (by linarith)
  have hfin_t : R.measure (closedBall y t) ≠ ∞ := hfinB t (by linarith)
  -- `ν = F_y μ`, so that `∫⁻_S F_y dμ = ν(S)` for Borel `S`
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Euclid P), ∀ S, MeasurableSet S →
      ∫⁻ x in S, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection
        (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure = ν S :=
    ⟨_, fun S hS => (withDensity_apply _ hS).symm⟩
  have hmeas : ∀ a b : ℝ, MeasurableSet (closedBall y a \ closedBall y b) := fun a b =>
    measurableSet_closedBall.diff measurableSet_closedBall
  -- the smoothed bounds (i'_m) and (ii'_m), with the annular integrals written via `ν`
  have hbd : ∀ m, ν (closedBall y t \ closedBall y (A m * s)) +
        ENNReal.ofReal (Real.exp (A m * κ * s) / s ^ n) * R.measure (closedBall y s) ≤
        ENNReal.ofReal (Real.exp (A m * κ * t) / t ^ n) * R.measure (closedBall y (A m * t)) ∧
      ENNReal.ofReal (Real.exp (-(A m * κ * t)) / t ^ n) * R.measure (closedBall y t) ≤
        ENNReal.ofReal (Real.exp (-(A m * κ * s)) / s ^ n) * R.measure (closedBall y (A m * s)) +
        ENNReal.ofReal (A m ^ n) * ν (closedBall y (A m * t) \ closedBall y s) := by
    intro m
    rw [← hν _ (hmeas _ _), ← hν _ (hmeas _ _)]
    exact hsm (A m) s t (hA1 m) hs hst (hBA m)
  -- Step 4(a): the inner annuli `B̄_t∖B̄_{A_ms}` increase to `B̄_t∖B̄_s`
  have hin : Tendsto (fun m => ν (closedBall y t \ closedBall y (A m * s))) atTop
      (𝓝 (ν (closedBall y t \ closedBall y s))) := by
    have hmono : Monotone fun m => closedBall y t \ closedBall y (A m * s) := fun i j hij =>
      sdiff_subset_sdiff_right (hanti_s hij)
    have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [← Set.sdiff_iInter, hinter_s] at h
  -- Step 4(b): `F_y(x) ≤ |x − y|⁻ⁿ ≤ s⁻ⁿ` off `B̄_s`, as `|v − p v| ≤ |v|`
  have hF : ∀ x : Euclid P, x ∉ closedBall y s →
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
        ‖x - y‖ ^ (n + 2) ≤ 1 / s ^ n := by
    intro x hx
    rw [mem_closedBall, not_le, dist_eq_norm] at hx
    have hr : 0 < ‖x - y‖ := hs.trans hx
    have hperp : ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ≤
        ‖x - y‖ := by
      rw [← Submodule.starProjection_orthogonal_val]
      exact Submodule.norm_starProjection_apply_le _ _
    calc ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
          ‖x - y‖ ^ (n + 2)
        ≤ ‖x - y‖ ^ 2 / ‖x - y‖ ^ (n + 2) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hperp 2) (by positivity)
      _ = 1 / ‖x - y‖ ^ n := by
          rw [pow_add, div_mul_eq_div_div_swap, div_self (pow_ne_zero 2 hr.ne')]
      _ ≤ 1 / s ^ n := one_div_le_one_div_of_le (pow_pos hs n) (pow_le_pow_left₀ hs.le hx.le n)
  -- Step 4(b): the outer annuli `B̄_{A_mt}∖B̄_s` decrease to `B̄_t∖B̄_s`, the first having
  -- `ν(B̄_{A_0t}∖B̄_s) ≤ s⁻ⁿ μ(B̄_{A_0t}) < ∞`
  have hout : Tendsto (fun m => ν (closedBall y (A m * t) \ closedBall y s)) atTop
      (𝓝 (ν (closedBall y t \ closedBall y s))) := by
    have hanti' : Antitone fun m => closedBall y (A m * t) \ closedBall y s := fun i j hij =>
      sdiff_subset_sdiff_left (hanti_t hij)
    have hinter' : (⋂ m, closedBall y (A m * t) \ closedBall y s) =
        closedBall y t \ closedBall y s := by
      rw [← hinter_t]
      ext x
      simp only [mem_iInter, Set.mem_sdiff]
      exact ⟨fun h => ⟨fun m => (h m).1, (h 0).2⟩, fun h m => ⟨h.1 m, h.2⟩⟩
    have hle : ν (closedBall y (A 0 * t) \ closedBall y s) ≤
        ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t)) := by
      rw [← hν _ (hmeas _ _)]
      calc ∫⁻ x in closedBall y (A 0 * t) \ closedBall y s, ENNReal.ofReal
            (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
              ‖x - y‖ ^ (n + 2)) ∂R.measure
          ≤ ∫⁻ _ in closedBall y (A 0 * t) \ closedBall y s, ENNReal.ofReal (1 / s ^ n)
              ∂R.measure :=
            setLIntegral_mono' (hmeas _ _) fun x hx => ENNReal.ofReal_le_ofReal (hF x hx.2)
        _ = ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t) \ closedBall y s) :=
            setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t)) :=
            mul_le_mul' le_rfl (measure_mono sdiff_subset)
    have hfin' : ν (closedBall y (A 0 * t) \ closedBall y s) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinB _ (hAt 0))) hle
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun m => (hmeas _ _).nullMeasurableSet) hanti' ⟨0, hfin'⟩
    rwa [hinter'] at h
  -- Step 5: the coefficients converge
  have hAκ : Tendsto (fun m => A m * κ) atTop (𝓝 κ) := by
    have h := hAlim.mul_const κ
    rwa [one_mul] at h
  have hexp : ∀ ρ : ℝ,
      Tendsto (fun m => ENNReal.ofReal (Real.exp (A m * κ * ρ) / ρ ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n))) ∧
      Tendsto (fun m => ENNReal.ofReal (Real.exp (-(A m * κ * ρ)) / ρ ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(κ * ρ)) / ρ ^ n))) := fun ρ =>
    ⟨ENNReal.tendsto_ofReal (((hAκ.mul_const ρ).rexp).div_const _),
      ENNReal.tendsto_ofReal (((hAκ.mul_const ρ).neg.rexp).div_const _)⟩
  have hpow : Tendsto (fun m => ENNReal.ofReal (A m ^ n)) atTop (𝓝 1) := by
    have h := ENNReal.tendsto_ofReal (hAlim.pow n)
    rwa [one_pow, ENNReal.ofReal_one] at h
  rw [hν _ (hmeas _ _)]
  constructor
  · -- Step 6, (M1): `e^{κs} ≤ e^{A_mκs}`; pass to the limit in (i'_m)
    refine le_of_tendsto_of_tendsto' (hin.add tendsto_const_nhds)
      (ENNReal.Tendsto.mul (hexp t).1 (Or.inr hfin_t) hlim_t (Or.inr ENNReal.ofReal_ne_top))
      fun m => ?_
    have hcoef : ENNReal.ofReal (Real.exp (κ * s) / s ^ n) ≤
        ENNReal.ofReal (Real.exp (A m * κ * s) / s ^ n) := by
      refine ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (pow_pos hs n).le)
      rw [mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg hκ hs.le) (hA1 m).le
    exact le_trans (add_le_add le_rfl (mul_le_mul' hcoef le_rfl)) (hbd m).1
  · -- Step 7, (M2): pass to the limit in (ii'_m)
    have h := le_of_tendsto_of_tendsto'
      (ENNReal.Tendsto.mul_const (hexp t).2 (Or.inr hfin_t))
      ((ENNReal.Tendsto.mul (hexp s).2 (Or.inr hfin_s) hlim_s (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.mul hpow (Or.inl one_ne_zero) hout (Or.inr ENNReal.one_ne_top)))
      fun m => (hbd m).2
    rwa [one_mul] at h
/-- Lower density bound at a point with an approximate tangent plane (Simon Ch. 3, 1.5(3), and
Ch. 4, 4.10(1)): if `Q` is the approximate tangent space of `M` at `x`, `n ≥ 1` and `c < ωₙ`, then
`c ρⁿ ≤ Hⁿ(M ∩ B̄_ρ(x))` for all small `ρ > 0`.  Choose `ε > 0` with `c (1 + ε)ⁿ < ωₙ` and test
against `ψ(y) = max 0 (min 1 ((1 + ε − |y|)/ε))`, so `1_{B̄₁(0)} ≤ ψ ≤ 1_{B̄_{1+ε}(0)}`.  A linear
isometry `ℝⁿ → ℝᴾ` onto `Q` gives `∫_Q ψ dHⁿ ≥ Hⁿ(Q ∩ B₁(0)) = ωₙ`, while
`∫_{η_{x,r}(M)} ψ dHⁿ ≤ Hⁿ(B̄_{1+ε}(0) ∩ η_{x,r}(M)) = r⁻ⁿ Hⁿ(M ∩ B̄_{(1+ε)r}(x))`; the blow-up
integrals converge to `∫_Q ψ dHⁿ`, and `ρ = (1 + ε) r`. -/
theorem Submission.doragm_approxTangent_lower_density : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → HasApproximateTangentSpaceAt n M x Q → ∀ c : ℝ≥0∞, c < unitBallVolume n → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal (ρ ^ n) ≤ μHE[n] (M ∩ closedBall x ρ) := by
  intro P n M x Q _hn hQ c hc
  -- Step 1: `ωₙ < ∞`, so `c < ∞`; choose `ε > 0` with `c (1 + ε)ⁿ < ωₙ`
  have hω_top : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcont : Tendsto (fun ε : ℝ => c * ENNReal.ofReal ((1 + ε) ^ n)) (𝓝 0) (𝓝 c) := by
    have h1 : Tendsto (fun ε : ℝ => (1 + ε) ^ n) (𝓝 0) (𝓝 1) := by
      have hc1 : Continuous fun ε : ℝ => (1 + ε) ^ n := by fun_prop
      simpa using hc1.tendsto 0
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h1) (Or.inr hc_top)
  obtain ⟨ε, hεω, hε⟩ := ((hcont.eventually (gt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  set A : ℝ := 1 + ε
  have hA : 0 < A := by linarith
  -- Step 2: the test function `ψ(y) = max 0 (min 1 ((1 + ε − |y|)/ε))`
  have hψcs : HasCompactSupport (fun y : Euclid P => max 0 (min 1 ((A - ‖y‖) / ε))) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) A) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have hneg : (A - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    rw [min_eq_right (hneg.le.trans zero_le_one), max_eq_left hneg.le]
  let ψ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 ((A - ‖y‖) / ε)), continuous_const.max
      (continuous_const.min ((continuous_const.sub continuous_norm).div_const ε))⟩, hψcs⟩
  have hψ_apply : ∀ y, ψ y = max 0 (min 1 ((A - ‖y‖) / ε)) := fun y => rfl
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => le_max_left _ _
  have hψle1 : ∀ y, ψ y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hψ1 : ∀ y : Euclid P, ‖y‖ ≤ 1 → ψ y = 1 := by
    intro y hy
    have hge : 1 ≤ (A - ‖y‖) / ε := by rw [le_div_iff₀ hε]; linarith
    rw [hψ_apply, min_eq_left hge, max_eq_right zero_le_one]
  have hψ_out : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) A → ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have hneg : (A - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    rw [hψ_apply, min_eq_right (hneg.le.trans zero_le_one), max_eq_left hneg.le]
  -- Step 3: `Hⁿ(Q ∩ B₁(0)) = ωₙ`, via a linear isometry `ℝⁿ → ℝᴾ` onto `Q`
  have hplane : μHE[n] (ball (0 : Euclid P) 1 ∩ (Q : Set (Euclid P))) = unitBallVolume n := by
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ.1)
    have hj : Isometry (Q.subtypeₗᵢ ∘ b.repr.symm) := Q.subtypeₗᵢ.isometry.comp b.repr.symm.isometry
    have himg : (Q.subtypeₗᵢ ∘ b.repr.symm) '' ball (0 : Euclid n) 1 =
        ball (0 : Euclid P) 1 ∩ (Q : Set (Euclid P)) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨?_, (b.repr.symm v).2⟩
        rw [mem_ball_zero_iff] at hv ⊢
        rwa [Function.comp_apply, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]
      · rintro ⟨hy, hyQ⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_ball_zero_iff] at hy ⊢
          rwa [LinearIsometryEquiv.norm_map, ← Submodule.norm_coe]
        · simp
    rw [← himg, hj.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rfl
  have hL : (unitBallVolume n).toReal ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hQ.1
    calc (unitBallVolume n).toReal
        = ∫ y in ball (0 : Euclid P) 1, ψ y ∂((μHE[n] : Measure (Euclid P)).restrict Q) := by
          rw [setIntegral_congr_fun measurableSet_ball
            (fun y hy => hψ1 y (mem_ball_zero_iff.mp hy).le),
            setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
            Measure.restrict_apply measurableSet_ball, hplane]
      _ ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] :=
          setIntegral_le_integral ψ.integrable (Eventually.of_forall hψ0)
  -- the blow-up integrals `a(r) = ∫_{η_r(M)} ψ dHⁿ` converge to `∫_Q ψ dHⁿ ≥ ωₙ > c (1 + ε)ⁿ`
  have hcA_top : c * ENNReal.ofReal (A ^ n) ≠ ∞ := ne_top_of_lt hεω
  have hcA_lt : (c * ENNReal.ofReal (A ^ n)).toReal < ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] :=
    (ENNReal.toReal_strict_mono hω_top hεω).trans_le hL
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (c * ENNReal.ofReal (A ^ n)).toReal <
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n] :=
    (hQ.2 ψ).eventually (lt_mem_nhds hcA_lt)
  -- Step 4: `ofReal (a(r)) ≤ Hⁿ(B̄_A(0) ∩ η_r(M)) = r⁻ⁿ Hⁿ(M ∩ B̄_{rA}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] T := by
    intro r hr T
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' T =
        AffineMap.homothety (0 : Euclid P) r⁻¹ '' ((fun y : Euclid P => y - x) '' T) := by
      rw [Set.image_image]
      refine Set.image_congr fun y _ => ?_
      change r⁻¹ • (y - x) = _
      rw [AffineMap.homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]
    have hτ : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Euclid P) (inv_ne_zero hr.ne'),
      hτ.euclideanHausdorffMeasure_image, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
      Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hball : ∀ r : ℝ, 0 < r → closedBall (0 : Euclid P) A ∩
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (r * A)) := by
    intro r hr
    have hmem : ∀ y : Euclid P, Poincare.SimonGMT.Chapter03.blowUpMap x r y ∈
        closedBall (0 : Euclid P) A ↔ y ∈ closedBall x (r * A) := by
      intro y
      change r⁻¹ • (y - x) ∈ closedBall (0 : Euclid P) A ↔ y ∈ closedBall x (r * A)
      rw [mem_closedBall_zero_iff, mem_closedBall, dist_eq_norm, norm_smul,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, ← div_eq_inv_mul, div_le_iff₀ hr, mul_comm A r]
    ext y
    constructor
    · rintro ⟨hyB, z, hzM, rfl⟩
      exact ⟨z, ⟨hzM, (hmem z).mp hyB⟩, rfl⟩
    · rintro ⟨z, ⟨hzM, hzB⟩, rfl⟩
      exact ⟨(hmem z).mpr hzB, z, hzM, rfl⟩
  have hupper : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]) ≤
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
    intro r hr
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hψ0)
      ψ.continuous.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal_le.trans ?_
    calc ∫⁻ y, ENNReal.ofReal (ψ y)
          ∂((μHE[n] : Measure (Euclid P)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        ≤ ∫⁻ y, (closedBall (0 : Euclid P) A).indicator 1 y
          ∂((μHE[n] : Measure (Euclid P)).restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) A
          · rw [indicator_of_mem hy, Pi.one_apply]
            exact ENNReal.ofReal_le_one.mpr (hψle1 y)
          · rw [hψ_out y hy, ENNReal.ofReal_zero]
            exact zero_le
      _ = μHE[n] (closedBall (0 : Euclid P) A ∩
            Poincare.SimonGMT.Chapter03.blowUpMap x r '' M) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall]
      _ = ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
          rw [hball r hr, hscale r hr]
  -- Step 5: `c (rA)ⁿ ≤ Hⁿ(M ∩ B̄_{rA}(x))` for small `r > 0`; reparametrize `ρ = rA`
  have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * ENNReal.ofReal ((r * A) ^ n) ≤ μHE[n] (M ∩ closedBall x (r * A)) := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have h1 : c * ENNReal.ofReal (A ^ n) ≤
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
      rw [← ENNReal.ofReal_toReal hcA_top]
      exact (ENNReal.ofReal_le_ofReal hr.le).trans (hupper r hr0')
    calc c * ENNReal.ofReal ((r * A) ^ n)
        = c * ENNReal.ofReal (A ^ n) * ENNReal.ofReal r ^ n := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr0'.le n), ENNReal.ofReal_pow hr0'.le,
            mul_comm (ENNReal.ofReal r ^ n), mul_assoc]
      _ ≤ ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) * ENNReal.ofReal r ^ n := by
          gcongr
      _ = μHE[n] (M ∩ closedBall x (r * A)) := by
          rw [mul_comm (ENNReal.ofReal (r⁻¹) ^ n), mul_assoc, ← mul_pow,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hr0'.le), inv_mul_cancel₀ hr0'.ne',
            ENNReal.ofReal_one, one_pow, mul_one]
  have htend : Tendsto (fun ρ : ℝ => ρ / A) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const A).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact div_pos hρ hA
  filter_upwards [htend.eventually hev2] with ρ hρ
  rwa [div_mul_cancel₀ ρ hA.ne'] at hρ

/-- **Unit lower bound for the monotone ball ratio at support points** (Simon Ch. 4, 3.8–3.11
and 4.10(1)).  Let `μ = θ Hⁿ⌞M`, and let `f_z(ρ) = e^{κρ} ρ^{−n} μ(B_ρ(z))` be nondecreasing in
`ρ` whenever `B_ρ(z) ⊆ W`.  Then `ωₙ ≤ f_y(t)` for every `y ∈ spt μ` and `t > 0` with
`B_t(y) ⊆ W`.

Suppose `f_y(t) < ωₙ`.  By continuity from above there is `δ > 0` with `B_{t+δ}(y) ⊆ W` and
`b = e^{κt} t^{−n} μ(B_{t+δ}(y)) < c < ωₙ` for some `c`.  As `y ∈ spt μ`, `μ(B_δ(y)) > 0`, so
`B_δ(y)` contains a point `x` at which `M` has an approximate tangent space (`μ`-a.e. point does).
Then `Submission.doragm_approxTangent_lower_density` gives `c σⁿ ≤ Hⁿ(M ∩ B_σ(x))` for some
`0 < σ < t`.  Since `e^{κσ} ≥ 1`, `θ ≥ 1` on `M` and `B_t(x) ⊆ B_{t+δ}(y)`, monotonicity at `x`
gives `c ≤ f_x(σ) ≤ f_x(t) ≤ b`, a contradiction. -/
theorem Submission.doragm_support_ball_ratio_ge : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (κ : ℝ), 0 < n → IsOpen W → W ⊆ U → 0 ≤ κ → (∀ (z : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall z t ⊆ W → ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall z s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall z t)) → ∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
  intro P n U W R κ hn hW hWU hκ hmono y hy t ht hyt
  -- `μ ≥ Hⁿ⌞M` on measurable sets, since `θ ≥ 1` on `M`
  have hHμ : ∀ S : Set (Euclid P), MeasurableSet S → μHE[n] (R.carrier ∩ S) ≤ R.measure S := by
    intro S hS
    rw [IMRep.measure, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_comm,
      ← setLIntegral_one]
    apply setLIntegral_mono' (hS.inter R.measurableSet_carrier)
    intro x hx
    exact_mod_cast R.mult_pos x hx.2
  -- `μ` is finite on compact subsets of `U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- `μ`-a.e. point has an approximate tangent space, as `μ ≪ Hⁿ⌞M`
  have hgood : ∀ᵐ x ∂R.measure, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (R.orients.mono fun x ⟨Q, hQ, _⟩ => ⟨Q, hQ⟩)
  -- suppose `f_y(t) < ωₙ`
  by_contra hlt
  rw [not_le] at hlt
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (κ * t) / t ^ n)
  -- `B_{t+δ₀}(y) ⊆ W`, and `μ(B_{t+δ₀/(m+1)}(y)) → μ(B_t(y))` by continuity from above
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := (isCompact_closedBall y t).exists_cthickening_subset_open hW hyt
  rw [cthickening_closedBall hδ₀.le ht.le] at hδ₀W
  have hanti : Antitone (fun m : ℕ => closedBall y (t + δ₀ / ((m : ℝ) + 1))) := by
    intro i j hij
    apply closedBall_subset_closedBall
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have : δ₀ / ((j : ℝ) + 1) ≤ δ₀ / ((i : ℝ) + 1) :=
      div_le_div_of_nonneg_left hδ₀.le hi hij'
    linarith
  have hinter : (⋂ m : ℕ, closedBall y (t + δ₀ / ((m : ℝ) + 1))) = closedBall y t := by
    ext z
    simp only [mem_iInter, mem_closedBall]
    constructor
    · intro h
      have hlim : Tendsto (fun m : ℕ => t + δ₀ * (1 / ((m : ℝ) + 1))) atTop (𝓝 (t + δ₀ * 0)) :=
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ₀)
      rw [mul_zero, add_zero] at hlim
      exact ge_of_tendsto' hlim fun m => by rw [mul_one_div]; exact h m
    · intro h m
      have : 0 < δ₀ / ((m : ℝ) + 1) := by positivity
      linarith
  have hfin0 : R.measure (closedBall y (t + δ₀ / (((0 : ℕ) : ℝ) + 1))) ≠ ∞ := by
    apply hfin _ (isCompact_closedBall _ _)
    refine Subset.trans (closedBall_subset_closedBall ?_) (hδ₀W.trans hWU)
    simp only [Nat.cast_zero, zero_add, div_one]
    linarith
  have hT : Tendsto (fun m : ℕ => A * R.measure (closedBall y (t + δ₀ / ((m : ℝ) + 1)))) atTop
      (𝓝 (A * R.measure (closedBall y t))) := by
    have h := tendsto_measure_iInter_atTop (μ := R.measure)
      (fun m => measurableSet_closedBall.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rw [hinter] at h
    exact ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top)
  -- fix `δ = δ₀/(m+1)` with `b = A μ(B_{t+δ}(y)) < c < ωₙ`
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds hlt)).exists
  set δ : ℝ := δ₀ / ((m : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  have hδδ₀ : δ ≤ δ₀ := div_le_self hδ₀.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  obtain ⟨c, hbc, hcω⟩ := exists_between hm
  -- `y ∈ spt μ`, so `B_δ(y)` has positive measure and contains a point `x` with a tangent space
  have hpos : R.measure (ball y δ) ≠ 0 :=
    ((Measure.mem_support_iff_forall y).1 hy _ (ball_mem_nhds y hδ)).ne'
  obtain ⟨x, hx, Q, hQ⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hgood)
  -- `B_t(x) ⊆ B_{t+δ}(y) ⊆ W`
  have hxy : dist x y < δ := mem_ball.1 hx
  have hBx : closedBall x t ⊆ closedBall y (t + δ) := closedBall_subset_closedBall' (by linarith)
  have hBxW : closedBall x t ⊆ W :=
    hBx.trans ((closedBall_subset_closedBall (by linarith)).trans hδ₀W)
  -- the tangent lower density at `x`: `c σⁿ ≤ Hⁿ(M ∩ B_σ(x))` for some `0 < σ < t`
  obtain ⟨σ, hσc, hσ0, hσt⟩ :=
    ((Submission.doragm_approxTangent_lower_density P n R.carrier x Q hn hQ c hcω).and
      (Ioo_mem_nhdsGT ht)).exists
  have hσn : 0 < σ ^ n := pow_pos hσ0 n
  have hcoef : ENNReal.ofReal (1 / σ ^ n) ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) :=
    ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (Real.one_le_exp (mul_nonneg hκ hσ0.le)) hσn.le)
  have hone : ENNReal.ofReal (1 / σ ^ n) * ENNReal.ofReal (σ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hσn.ne', ENNReal.ofReal_one]
  -- `c ≤ f_x(σ) ≤ f_x(t) ≤ b < c`
  have key : c ≤ A * R.measure (closedBall y (t + δ)) :=
    calc c = ENNReal.ofReal (1 / σ ^ n) * (c * ENNReal.ofReal (σ ^ n)) := by
          rw [mul_comm c, ← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * μHE[n] (R.carrier ∩ closedBall x σ) :=
          mul_le_mul' hcoef hσc
      _ ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (closedBall x σ) :=
          mul_le_mul' le_rfl (hHμ _ measurableSet_closedBall)
      _ ≤ A * R.measure (closedBall x t) := hmono x σ t hσ0 hσt hBxW
      _ ≤ A * R.measure (closedBall y (t + δ)) := mul_le_mul' le_rfl (measure_mono hBx)
  exact absurd (key.trans_lt hbc) (lt_irrefl c)
/-- **The approximate tangent projection is `μ_V`-measurable** (Simon Ch. 3, 1.4 and 1.5(1);
Ch. 6, 3.1).  For `R = (M, θ, ξ)` with weight `μ_V = θ Hⁿ⌞M`, `x ↦ p_{TₓM}` is `μ_V`-a.e. strongly
measurable.  Since `μ_V ≪ Hⁿ⌞M`, it suffices to prove this for `Hⁿ⌞M`.  By uniqueness of
approximate tangent planes, `TₓM` is `Hⁿ⌞M`-a.e. the plane oriented by `ξ(x)`.  A unit simple
`n`-vector `ζ = ±τ₁ ∧ ⋯ ∧ τₙ` determines its plane: if also `ζ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` and
`y ⊥ span τ'`, the `n`-covector `α(u) = det(⟨cₖ, uⱼ⟩)`, where `c` is `τ` with `τᵢ` replaced by `y`,
gives `±⟨y, τᵢ⟩ = ±α(τ) = ζ(α) = ±α(τ') = 0`, so `τᵢ ∈ span τ'`.  Hence `p_{TₓM} = G(ξ(x))` a.e.,
where `G(ζ)` is the projection onto the plane of `ζ` (`0` if there is none).  `G` is Borel:
`Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` is continuous on the compact set `Ω` of orthonormal frames and signs, and
`G(Φ(τ, s)) = Σₖ ⟨τₖ, ·⟩ τₖ` is continuous, so for closed `t`,
`G⁻¹(t) = Φ(Ω ∩ (G ∘ Φ)⁻¹(t)) ∪ (Φ(Ω)ᶜ ∩ {0 ∈ t})` is Borel. -/
theorem Submission.dorag_approxTangent_starProjection_aesm : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n U R
  classical
  -- `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`, so it suffices to prove measurability for `Hⁿ⌞M`
  refine AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (μHE[n].restrict R.carrier) fun x => (R.mult x : ℝ≥0∞)) ?_
  -- `ev τ = (α ↦ α(τ₁, …, τₙ))`, a continuous alternating map of `τ`
  let ev : Euclid P [⋀^Fin n]→L[ℝ] MultiVector P n :=
    (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
  have hev : ∀ (τ : Fin n → Euclid P) (α : Covector (Euclid P) n), ev τ α = α τ :=
    fun τ α => rfl
  -- `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` on the compact set `Ω` of orthonormal frames and signs `s = ±1`
  let Φ : (Fin n → Euclid P) × ℝ → MultiVector P n := fun ω => ω.2 • ev ω.1
  have hΦc : Continuous Φ := continuous_snd.smul (ev.coe_continuous.comp continuous_fst)
  let Ω : Set ((Fin n → Euclid P) × ℝ) := {τ | Orthonormal ℝ τ} ×ˢ {1, -1}
  have hΩ : IsCompact Ω := by
    refine IsCompact.prod (isCompact_of_isClosed_isBounded ?_ ?_) (Set.toFinite _).isCompact
    · have hset : {τ : Fin n → Euclid P | Orthonormal ℝ τ} =
          ⋂ i, ⋂ j, {τ | inner ℝ (τ i) (τ j) = if i = j then (1 : ℝ) else 0} := by
        ext τ
        simp [orthonormal_iff_ite]
      rw [hset]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
    · refine (isBounded_iff_subset_closedBall 0).mpr ⟨1, fun τ hτ => ?_⟩
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hτ.1 i).le
  -- `ζ` orients `Q` iff `ζ = Φ(τ, s)` for a point `(τ, s)` of `Ω` with `span τ = Q`
  have horient : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q ↔ ∃ ω ∈ Ω, Φ ω = ζ ∧ Submodule.span ℝ (range ω.1) = Q := by
    intro ζ Q
    constructor
    · rintro ⟨τ, hτ, hQ, h | h⟩
      · refine ⟨(τ, 1), ⟨hτ, Or.inl rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
      · refine ⟨(τ, -1), ⟨hτ, Or.inr rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
    · rintro ⟨⟨τ, s⟩, ⟨hτ, hs⟩, rfl, hQ⟩
      refine ⟨τ, hτ, hQ, ?_⟩
      rcases hs with rfl | rfl
      · left
        intro α
        simp [Φ, hev]
      · right
        intro α
        simp [Φ, hev]
  -- the `n`-covector `u ↦ det(⟨cₖ, uⱼ⟩)ₖⱼ`
  have hdet : ∀ c : Fin n → Euclid P, ∃ α : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, α u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
    intro c
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => (innerSL ℝ (c k)).toLinearMap
    let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hA : ∀ u : Fin n → Euclid P, A u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
      intro u
      rw [← Matrix.det_transpose]
      rfl
    have hAc : Continuous fun u : Fin n → Euclid P => A u := by
      simp only [hA]
      exact Continuous.matrix_det (continuous_matrix fun k j => by
        simp only [Matrix.of_apply]
        exact continuous_const.inner (continuous_apply j))
    exact ⟨{ A with cont := hAc }, hA⟩
  -- a unit simple `n`-vector determines its plane: if `ζ` orients `span τ` and `span τ'`, then
  -- each `τᵢ` is orthogonal to `(span τ')ᗮ`
  have hle : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q ≤ Q' := by
    rintro ζ Q Q' ⟨τ, hτ, rfl, hζ⟩ ⟨τ', hτ', rfl, hζ'⟩
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ')),
      Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨α, hα⟩ := hdet (Function.update τ i y)
    -- `α(τ)` is the determinant of the identity matrix with row `i` replaced by `(⟨y, τⱼ⟩)ⱼ`
    have h1 : α τ = inner ℝ y (τ i) := by
      rw [hα]
      have hM : (Matrix.of fun k j => inner ℝ (Function.update τ i y k) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => inner ℝ y (τ j)) := by
        ext k j
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk, Matrix.one_apply, orthonormal_iff_ite.mp hτ k j]
      rw [hM, ← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
        ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    -- row `i` of the matrix of `α(τ')` is `(⟨y, τ'ⱼ⟩)ⱼ = 0`
    have h2 : α τ' = 0 := by
      rw [hα]
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      simp only [Matrix.of_apply, Function.update_self]
      rw [real_inner_comm]
      exact hy _ (Submodule.subset_span ⟨j, rfl⟩)
    have h3 : ζ α = 0 := by
      rcases hζ' with h | h <;> simp [h, h2]
    rcases hζ with h | h
    · rw [← h1, ← h, h3]
    · have h4 := h α
      rw [h3] at h4
      rw [← h1]
      linarith
  have huniq : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q = Q' :=
    fun ζ Q Q' h h' => le_antisymm (hle ζ Q Q' h h') (hle ζ Q' Q h' h)
  -- the projection onto the span of an orthonormal frame `τ` is `Σₖ ⟨τₖ, ·⟩ τₖ`, continuous in `τ`
  let F : (Fin n → Euclid P) × ℝ → (Euclid P →L[ℝ] Euclid P) :=
    fun ω => ∑ k, (innerSL ℝ (ω.1 k)).smulRight (ω.1 k)
  have hFapply : ∀ ω v, F ω v = ∑ k, inner ℝ (ω.1 k) v • ω.1 k := by
    intro ω v
    simp [F]
  have hFc : Continuous F := by
    refine continuous_clm_apply.mpr fun v => ?_
    simp only [hFapply]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hFproj : ∀ ω ∈ Ω, (Submodule.span ℝ (range ω.1)).starProjection = F ω := by
    rintro ⟨τ, s⟩ ⟨hτ, -⟩
    refine ContinuousLinearMap.ext fun v => ?_
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hFapply]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨j, rfl⟩
        rw [hFapply, inner_sub_left, sum_inner]
        simp [inner_smul_left, orthonormal_iff_ite.mp hτ, real_inner_comm]
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx
        rw [inner_smul_right, hx, mul_zero]
  -- `G ζ` is the projection onto the plane oriented by `ζ` (`0` if there is none)
  let G : MultiVector P n → (Euclid P →L[ℝ] Euclid P) := fun ζ =>
    if h : ∃ Q, IsUnitOrientationOf ζ Q then h.choose.starProjection else 0
  have hGQ : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → G ζ = Q.starProjection := by
    intro ζ Q hQ
    have hex : ∃ Q, IsUnitOrientationOf ζ Q := ⟨Q, hQ⟩
    simp only [G, dite_eq_left hex]
    rw [huniq _ _ _ hex.choose_spec hQ]
  have hGΦ : ∀ ω ∈ Ω, G (Φ ω) = F ω := fun ω hω => by
    rw [hGQ _ _ ((horient _ _).mpr ⟨ω, hω, rfl, rfl⟩), hFproj ω hω]
  -- `G` is Borel: for closed `t`, `G⁻¹(t)` is the compact set `Φ(Ω ∩ F⁻¹(t))` together with the
  -- complement of the compact set `Φ(Ω)` (if `0 ∈ t`)
  have hG : Measurable G := by
    refine measurable_of_isClosed fun t ht => ?_
    have hset : G ⁻¹' t = Φ '' (Ω ∩ F ⁻¹' t) ∪
        ((Φ '' Ω)ᶜ ∩ {_ζ | (0 : Euclid P →L[ℝ] Euclid P) ∈ t}) := by
      ext ζ
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
        Set.mem_compl_iff]
      by_cases h : ∃ Q, IsUnitOrientationOf ζ Q
      · obtain ⟨Q, hQ⟩ := h
        obtain ⟨ω, hω, hΦω, -⟩ := (horient ζ Q).mp hQ
        have hGζ : G ζ = F ω := by
          rw [← hΦω]
          exact hGΦ ω hω
        constructor
        · intro hζt
          exact Or.inl ⟨ω, ⟨hω, by rwa [← hGζ]⟩, hΦω⟩
        · rintro (⟨ω', ⟨hω', hω't⟩, hΦω'⟩ | ⟨hn, -⟩)
          · rw [← hΦω', hGΦ ω' hω']
            exact hω't
          · exact absurd ⟨ω, hω, hΦω⟩ hn
      · have hGζ : G ζ = 0 := dite_eq_right h
        have hn : ¬∃ ω, ω ∈ Ω ∧ Φ ω = ζ := fun ⟨ω, hω, hΦω⟩ =>
          h ⟨_, (horient ζ _).mpr ⟨ω, hω, hΦω, rfl⟩⟩
        rw [hGζ]
        constructor
        · intro h0
          exact Or.inr ⟨hn, h0⟩
        · rintro (⟨ω', ⟨hω', -⟩, hΦω'⟩ | ⟨-, h0⟩)
          · exact absurd ⟨ω', hω', hΦω'⟩ hn
          · exact h0
    rw [hset]
    exact ((hΩ.inter_right (ht.preimage hFc)).image hΦc).isClosed.measurableSet.union
      ((hΩ.image hΦc).isClosed.measurableSet.compl.inter (MeasurableSet.const _))
  -- `Hⁿ⌞M`-a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes),
  -- so `p_{TₓM} = G(ξ(x))`
  have hae : (fun x => (approxTangentPlane n R.carrier x).starProjection)
      =ᵐ[μHE[n].restrict R.carrier] G ∘ R.orient := by
    filter_upwards [R.orients] with x ⟨Q, hQ, hor⟩
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    have h1 : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    rw [Function.comp_apply, hGQ _ _ hor, h1]
  -- `G ∘ ξ` is a.e. measurable, with values in the finite-dimensional space `End(ℝᴾ)`
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  exact ((hG.comp_aemeasurable R.aestronglyMeasurable_orient.aemeasurable).aestronglyMeasurable
    ).congr hae.symm

/-- **Monotonicity inequalities and the unit density lower bound** for bounded generalized mean
curvature (Simon Ch. 4, 3.16–3.17 with `‖H‖ ≤ κ`, and 4.10(1)).  Let `μ = θ Hⁿ⌞M` have generalized
mean curvature `H` in `W`, and let `F_y(x) = |p_x^⊥(x − y)|² / |x − y|^{n+2}`.
(1) The annular inequalities (M1) and (M2) are `Submission.doragm_annular_monotonicity` at
`P = n + k`.  The map `x ↦ p_x` is `μ`-measurable by
`Submission.dorag_approxTangent_starProjection_aesm`.
(2) Let `y ∈ spt μ`.  Since `κ ≥ ‖H 0‖ ≥ 0` and (M1) makes `ρ ↦ e^{κρ} ρ^{−n} μ(B_ρ(z))`
nondecreasing, `Submission.doragm_support_ball_ratio_ge` gives `e^{κs} s^{−n} μ(B_s(y)) ≥ ωₙ`.
With (M1) this yields `∫_{B_t(y) \ B_s(y)} F_y dμ + ωₙ ≤ e^{κt} t^{−n} μ(B_t(y))` for `0 < s < t`.
For `s = t/(m + 2)` the annuli increase to `B_t(y) \ {y}`, and `F_y(y) = 0`.  Monotone convergence
for the measure `F_y μ` therefore gives (D). -/
theorem Submission.dorag_monotonicity_density : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → (∀ (y : Euclid (n + k)) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) ∧ ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * R.measure (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) ∧ ∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
  intro n k hn U W R H κ hW hWU hH hHκ hFV
  -- (1) is the annular monotonicity, with `x ↦ p_x` measurable by the sibling lemma
  have hann := Submission.doragm_annular_monotonicity (n + k) n U W R H κ hW hWU
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hH hHκ hFV
  refine ⟨hann, fun y hy t ht hyt => ?_⟩
  -- `κ ≥ ‖H 0‖ ≥ 0`, and dropping the annular term of (M1) makes `ρ ↦ e^{κρ} ρ^{-n} μ(B_ρ(z))`
  -- nondecreasing, so this ratio is at least `ωₙ` at the support point `y`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hratio := Submission.doragm_support_ball_ratio_ge (n + k) n U W R κ hn hW hWU hκ
    (fun z s t hs hst hzt => le_add_self.trans (hann z s t hs hst hzt).1) y hy
  -- the integrand `F_y`, which vanishes at `y` because `‖0‖ ^ (n + 2) = 0`
  set F : Euclid (n + k) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
      ‖x - y‖ ^ (n + 2)) with hF
  have hFy : F y = 0 := by simp [hF]
  -- for `0 < s < t`: `∫_{B_t(y) \ B_s(y)} F_y dμ + ωₙ ≤ e^{κt} t^{-n} μ(B_t(y))`
  have hannulus : ∀ s, 0 < s → s < t →
      (∫⁻ x in closedBall y t \ closedBall y s, F x ∂R.measure) + unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
    fun s hs hst => (add_le_add le_rfl
      (hratio s hs ((closedBall_subset_closedBall hst.le).trans hyt))).trans
        (hann y s t hs hst hyt).1
  -- the annuli `B_t(y) \ B_{t/(m+2)}(y)` increase and cover `B_t(y) \ {y}`
  let A : ℕ → Set (Euclid (n + k)) := fun m => closedBall y t \ closedBall y (t / (m + 2))
  have hA : Monotone A := fun m m' hmm' => Set.sdiff_subset_sdiff_right
    (closedBall_subset_closedBall (div_le_div_of_nonneg_left ht.le (by positivity) (by gcongr)))
  have hcover : closedBall y t ⊆ (⋃ m, A m) ∪ {y} := by
    intro x hx
    by_cases hxy : x = y
    · exact Or.inr hxy
    have hd : 0 < dist x y := dist_pos.mpr hxy
    obtain ⟨m, hm⟩ := exists_nat_gt (t / dist x y)
    refine Or.inl (mem_iUnion.mpr ⟨m, hx, fun hxm => ?_⟩)
    rw [mem_closedBall, le_div_iff₀ (by positivity)] at hxm
    rw [div_lt_iff₀ hd] at hm
    nlinarith
  -- monotone convergence for the measure `F_y μ`
  have hν : ∀ s, MeasurableSet s → R.measure.withDensity F s = ∫⁻ x in s, F x ∂R.measure :=
    fun s hs => withDensity_apply F hs
  calc (∫⁻ x in closedBall y t, F x ∂R.measure) + unitBallVolume n
      = R.measure.withDensity F (closedBall y t) + unitBallVolume n := by
        rw [hν _ measurableSet_closedBall]
    _ ≤ (⨆ m, R.measure.withDensity F (A m)) + unitBallVolume n := by
        refine add_le_add ?_ le_rfl
        calc R.measure.withDensity F (closedBall y t)
            ≤ R.measure.withDensity F ((⋃ m, A m) ∪ {y}) := measure_mono hcover
          _ ≤ R.measure.withDensity F (⋃ m, A m) + R.measure.withDensity F {y} :=
            measure_union_le _ _
          _ = ⨆ m, R.measure.withDensity F (A m) := by
            rw [hA.measure_iUnion, hν _ (measurableSet_singleton y), lintegral_singleton, hFy,
              zero_mul, add_zero]
    _ = ⨆ m, (R.measure.withDensity F (A m) + unitBallVolume n) := ENNReal.iSup_add _
    _ ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
        refine iSup_le fun m => ?_
        have hm : (1 : ℝ) < m + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
        rw [hν (A m) (measurableSet_closedBall.diff measurableSet_closedBall)]
        exact hannulus _ (div_pos ht (by linarith)) (div_lt_self ht hm)

/-- **The support minus the carrier is `Hⁿ`-null** (Simon Ch. 1, 3.3; Ch. 4, 4.10(1)).  Let
`V = v(M, θ)` have mean curvature `H`, `|H| ≤ κ`, in the open set `W ⊆ U`, and let
`A = (spt μ_V ∩ W) \ M`.  Then `μ_V(A) = 0`, as `μ_V = θ Hⁿ⌞M` is concentrated on `M`.  At
`x ∈ A` the monotonicity bound `ωₙ ≤ e^{κt} t⁻ⁿ μ_V(B̄_t(x))` (`B̄_t(x) ⊆ W`) gives
`μ_V(B̄_t(x)) ≥ c tⁿ` for small `t`, with `c = ωₙ e^{-|κ|}`.  Since `μ_V` is locally finite at the
points of `A`, `A` has open neighbourhoods `O` with `μ_V(O) < ε`, and the density comparison
theorem gives `Hⁿ(A) ≤ C μ_V(O) ≤ C ε` with `C < ∞` depending only on `n + k`, `n` and `c`.
Letting `ε ↓ 0`, `Hⁿ(A) = 0`. -/
theorem Submission.dorag_support_sdiff_carrier_null : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 := by
  intro n k hn U W R H κ hW hWU hH hHκ hfv
  -- (D): `∫_{B̄_t(y)} F_y dμ_V + ωₙ ≤ e^{κt} t⁻ⁿ μ_V(B̄_t(y))` for `y ∈ spt μ_V`, `B̄_t(y) ⊆ W`
  have hD := (Submission.dorag_monotonicity_density n k hn U W R H κ hW hWU hH hHκ hfv).2
  -- `0 < ωₙ < ∞`, so `c = ωₙ e^{-|κ|} > 0`
  have hω0 : 0 < unitBallVolume n := by
    rw [unitBallVolume]
    exact measure_ball_pos _ _ one_pos
  have hωtop : unitBallVolume n ≠ ∞ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top.ne
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (unitBallVolume n).toReal * Real.exp (-|κ|) := ⟨_, rfl⟩
  have hc : 0 < c := hc_def ▸ mul_pos (ENNReal.toReal_pos hω0.ne' hωtop) (Real.exp_pos _)
  obtain ⟨C, hCtop, hcomp⟩ :=
    Submission.dorag_sn_hausdorff_le_mul_of_lower_density (n + k) n c hc
  -- step 1: `μ_V(Mᶜ) = 0`, as `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`; hence `μ_V(A) = 0`
  have hMc : R.measure R.carrierᶜ = 0 := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' R.measurableSet_carrier, compl_inter_self, measure_empty]
  have hA0 : R.measure ((R.measure.support ∩ W) \ R.carrier) = 0 :=
    measure_mono_null (fun x hx => hx.2) hMc
  -- every `x ∈ A ⊆ W` is the centre of a closed ball `B̄_r(x) ⊆ W`
  have hball : ∀ x ∈ (R.measure.support ∩ W) \ R.carrier,
      ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ W := by
    intro x hx
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x hx.1.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεW⟩
  -- a closed ball `B̄_r(x) ⊆ W ⊆ U` is a compact subset of `U`, so
  -- `μ_V(B̄_r(x)) = ∫_{M ∩ B̄_r(x)} θ dHⁿ < ∞`
  have hloc : ∀ x ∈ (R.measure.support ∩ W) \ R.carrier,
      ∃ r : ℝ, 0 < r ∧ R.measure (ball x r) ≠ ∞ := by
    intro x hx
    obtain ⟨r, hr, hrW⟩ := hball x hx
    refine ⟨r, hr, ne_top_of_le_ne_top ?_ (measure_mono ball_subset_closedBall)⟩
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall x r) (hrW.trans hWU)
  -- step 2: for `x ∈ A` and `0 < t < min r 1`, (D) gives
  -- `μ_V(B̄_t(x)) ≥ e^{-κt} ωₙ tⁿ ≥ c tⁿ`, since `κt ≤ |κ|`
  have hdens : ∀ x ∈ (R.measure.support ∩ W) \ R.carrier, ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ R.measure (closedBall x t) := by
    intro x hx
    obtain ⟨r, hr, hrW⟩ := hball x hx
    refine ⟨min r 1, lt_min hr one_pos, fun t ht htr => ?_⟩
    have htW : closedBall x t ⊆ W :=
      (closedBall_subset_closedBall (htr.le.trans (min_le_left _ _))).trans hrW
    have h1 : unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall x t) :=
      le_add_self.trans (hD x hx.1.1 t ht htW)
    have hkt : κ * t ≤ |κ| :=
      calc κ * t ≤ |κ| * t := mul_le_mul_of_nonneg_right (le_abs_self κ) ht.le
        _ ≤ |κ| := mul_le_of_le_one_right (abs_nonneg κ) (htr.le.trans (min_le_right _ _))
    have htn : t ^ n ≠ 0 := (pow_pos ht n).ne'
    have hexp : Real.exp (κ * t) ≠ 0 := (Real.exp_pos _).ne'
    calc ENNReal.ofReal (c * t ^ n)
        ≤ ENNReal.ofReal (Real.exp (-(κ * t)) * t ^ n * (unitBallVolume n).toReal) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hc_def, show Real.exp (-(κ * t)) * t ^ n * (unitBallVolume n).toReal =
            (unitBallVolume n).toReal * Real.exp (-(κ * t)) * t ^ n by ring]
          gcongr
      _ = ENNReal.ofReal (Real.exp (-(κ * t)) * t ^ n) * unitBallVolume n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hωtop]
      _ ≤ ENNReal.ofReal (Real.exp (-(κ * t)) * t ^ n) *
          (ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall x t)) := by
          gcongr
      _ = R.measure (closedBall x t) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            show Real.exp (-(κ * t)) * t ^ n * (Real.exp (κ * t) / t ^ n) = 1 by
              rw [Real.exp_neg]
              field_simp,
            ENNReal.ofReal_one, one_mul]
  -- steps 3–4: an open `O ⊇ A` with `μ_V(O) < ε` gives `Hⁿ(A) ≤ C μ_V(O) ≤ C ε`
  have hbound : ∀ ε : ℝ≥0∞, 0 < ε →
      μHE[n] ((R.measure.support ∩ W) \ R.carrier) ≤ C * ε := by
    intro ε hε
    obtain ⟨O, hO, hAO, hOε⟩ :=
      Submission.dorag_sn_open_superset_measure_lt (n + k) R.measure _ hA0 hloc ε hε
    calc μHE[n] ((R.measure.support ∩ W) \ R.carrier) ≤ C * R.measure O :=
          hcomp R.measure _ O hO hAO hdens
      _ ≤ C * ε := by gcongr
  -- step 5: `C < ∞`, so `C ε_j → 0` along `ε_j = 1 / j`, and `Hⁿ(A) = 0`
  have hlim : Tendsto (fun j : ℕ => C * (j : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hCtop)
  exact nonpos_iff_eq_zero.mp
    (ge_of_tendsto' hlim fun j => hbound _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j)))
/-- **Gram identity for the linear graph map** (Simon Ch. 2, 3.3 and Example 3.6(3): the area
Jacobian of a graph).  If `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` are linear isometries with
`⟨ιv, ι'w⟩ = 0` and `T : ℝⁿ → ℝᵏ` is linear, then `A = ι + ι' ∘ T` has `A* ∘ A = id + T* ∘ T`.
Pair both sides with `y`: `⟨A*Ax, y⟩ = ⟨Ax, Ay⟩ = ⟨ιx, ιy⟩ + ⟨ι'Tx, ι'Ty⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩`,
the cross terms vanishing by orthogonality, and `⟨(id + T*T)x, y⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩`. -/
theorem Submission.doraggt_graph_map_gram_identity : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (T : Euclid n →ₗ[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LinearMap.adjoint (ι.toLinearMap + ι'.toLinearMap ∘ₗ T) ∘ₗ (ι.toLinearMap + ι'.toLinearMap ∘ₗ T) = LinearMap.id + LinearMap.adjoint T ∘ₗ T := by
  intro n k ι ι' T h
  -- the other cross term vanishes too, by symmetry of the real inner product
  have h' : ∀ v w, inner ℝ (ι' w) (ι v) = 0 := fun v w => by rw [real_inner_comm]; exact h v w
  -- endomorphisms of `ℝⁿ` agree once `⟨S x, y⟩` agrees for all `x, y`
  refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
  -- `⟨A*Ax, y⟩ = ⟨Ax, Ay⟩` and `⟨T*Tx, y⟩ = ⟨Tx, Ty⟩`; expand, isometries keep `⟨·, ·⟩`
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply,
    LinearMap.id_apply, LinearIsometry.coe_toLinearMap, inner_add_left, inner_add_right,
    LinearIsometry.inner_map_map, h, h', add_zero, zero_add]

/-- **Metric and Hausdorff-measure properties of a Lipschitz graph map** (Simon Ch. 2,
Theorem 1.8(i); Steps 0, 1 and 3 of the graph-tangent argument for Allard's graph).  Let
`ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` be linear isometries with orthogonal ranges, `g` an
`L`-Lipschitz map and `Ψ(u) = b + ιu + ι'(g u)`.  Then (i) `|u − u'| ≤ |Ψ(u) − Ψ(u')|`
(Pythagoras), (ii) `Ψ` is `(1 + L)`-Lipschitz, (iii) `Ψ(ℝⁿ)` is closed (antilipschitz and
uniformly continuous on the complete `ℝⁿ`), (iv) `Hⁿ(Ψ(ℝⁿ) ∩ K) < ∞` for compact `K` (by (i),
`Ψ(ℝⁿ) ∩ K ⊆ Ψ(B̄ₘ(0))`), (v) `Hⁿ(Ψ(N)) = 0` if `Lⁿ(N) = 0`; (iv) and (v) use
`Hⁿ(Ψ(A)) ≤ (1 + L)ⁿ Hⁿ(A)` and `Hⁿ = Lⁿ` on `ℝⁿ`. -/
theorem Submission.doraggt_lipschitz_graph_map_basics : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (b : Euclid (n + k)) (g : Euclid n → Euclid k) (L : NNReal), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L g → (∀ u u' : Euclid n, dist u u' ≤ dist (b + ι u + ι' (g u)) (b + ι u' + ι' (g u'))) ∧ LipschitzWith (1 + L) (fun u => b + ι u + ι' (g u)) ∧ IsClosed (Set.range fun u => b + ι u + ι' (g u)) ∧ (∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range (fun u => b + ι u + ι' (g u)) ∩ K) ≠ ∞) ∧ ∀ N : Set (Euclid n), volume N = 0 → μHE[n] ((fun u => b + ι u + ι' (g u)) '' N) = 0 := by
  intro n k ι ι' b g L horth hg
  set Ψ : Euclid n → Euclid (n + k) := fun u => b + ι u + ι' (g u) with hΨ
  -- Step 1: `Ψ(u) − Ψ(u') = ι(u − u') + ι'(g u − g u')`.
  have hdiff : ∀ u u', Ψ u - Ψ u' = ι (u - u') + ι' (g u - g u') := by
    intro u u'
    simp only [hΨ, map_sub]
    abel
  -- Step 2 (i): Pythagoras, `|Ψ(u) − Ψ(u')|² = |u − u'|² + |g u − g u'|²`.
  have hdist : ∀ u u', dist u u' ≤ dist (Ψ u) (Ψ u') := by
    intro u u'
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth (u - u') (g u - g u'))
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map] at h
    refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
    rw [h]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  -- Step 3 (ii): triangle inequality and the Lipschitz bound for `g`.
  have hlip : LipschitzWith (1 + L) Ψ := by
    refine LipschitzWith.of_dist_le_mul fun u u' => ?_
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    calc ‖ι (u - u') + ι' (g u - g u')‖ ≤ ‖ι (u - u')‖ + ‖ι' (g u - g u')‖ := norm_add_le _ _
      _ = ‖u - u'‖ + dist (g u) (g u') := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map, dist_eq_norm]
      _ ≤ ‖u - u'‖ + L * ‖u - u'‖ := by
          rw [← dist_eq_norm u u']
          gcongr
          exact hg.dist_le_mul u u'
      _ = ((1 + L : NNReal) : ℝ) * ‖u - u'‖ := by
          push_cast
          ring
  -- Step 4 (iii): `Ψ` is antilipschitz and uniformly continuous on the complete `ℝⁿ`.
  have hclosed : IsClosed (Set.range Ψ) := by
    have hanti : AntilipschitzWith 1 Ψ :=
      AntilipschitzWith.of_le_mul_dist fun u u' => by simpa using hdist u u'
    exact hanti.isClosed_range hlip.uniformContinuous
  -- Step 5: `Hⁿ(Ψ(A)) ≤ (1 + L)ⁿ Lⁿ(A)`, using `Hⁿ = Lⁿ` on `ℝⁿ`.
  have himage : ∀ A : Set (Euclid n),
      μHE[n] (Ψ '' A) ≤ ((1 + L : NNReal) : ℝ≥0∞) ^ n * volume A := by
    intro A
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hlip.lipschitzOnWith (s := A))
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  -- Step 6 (iv): `Ψ(ℝⁿ) ∩ K ⊆ Ψ(B̄ₘ(0))` for `K ⊆ B̄ₘ(Ψ(0))`, by (i).
  have hfin : ∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range Ψ ∩ K) ≠ ∞ := by
    intro K hK
    obtain ⟨m, hm⟩ := hK.isBounded.subset_closedBall (Ψ 0)
    have hsub : Set.range Ψ ∩ K ⊆ Ψ '' closedBall 0 m := by
      rintro _ ⟨⟨u, rfl⟩, huK⟩
      exact ⟨u, mem_closedBall.2 ((hdist u 0).trans (mem_closedBall.1 (hm huK))), rfl⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (himage _))
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_closedBall_lt_top.ne
  -- Step 7 (v): null sets go to null sets.
  have hnull : ∀ N : Set (Euclid n), volume N = 0 → μHE[n] (Ψ '' N) = 0 := by
    intro N hN
    exact le_zero_iff.1 ((himage N).trans (by rw [hN, mul_zero]))
  exact ⟨hdist, hlip, hclosed, hfin, hnull⟩

/-- **Blow-ups of a graph are graphs of difference quotients** (Simon Ch. 3, 1.4: the dilation
`η_{x,λ}(y) = λ⁻¹(y − x)`).  Let `Φ(u) = a + ιu + ι'f(u)`, `r ≠ 0` and
`f_{v,r}(w) = r⁻¹(f(v + rw) − f(v))`.  By linearity
`η_{Φ(v),r}(Φ(u)) = ι(r⁻¹(u − v)) + ι'(r⁻¹(f(u) − f(v)))`, so the bijection `u = v + rw` of `ℝⁿ`
gives `η_{Φ(v),r}(Φ(ℝⁿ)) = {ιw + ι'f_{v,r}(w) : w ∈ ℝⁿ}`.  Where `f` is differentiable at
`v + rw`, the chain rule gives `Df_{v,r}(w) = r⁻¹ Df(v + rw) ∘ (r id) = Df(v + rw)`; elsewhere
`f_{v,r}` is not differentiable at `w` either (`f(u) = f(v) + r f_{v,r}(r⁻¹(u − v))`), and both
`fderiv`s are `0`. -/
theorem Submission.doraggt_graph_blowup_rescaling : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (a : Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (r : ℝ), r ≠ 0 → Poincare.SimonGMT.Chapter03.blowUpMap (a + ι v + ι' (f v)) r '' Set.range (fun u => a + ι u + ι' (f u)) = Set.range (fun w => ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) ∧ ∀ w : Euclid n, fderiv ℝ (fun w' => r⁻¹ • (f (v + r • w') - f v)) w = fderiv ℝ f (v + r • w) := by
  intro n k ι ι' a f v r hr
  refine ⟨?_, fun w => ?_⟩
  · -- Steps 2–3: reparametrize `ℝⁿ` by the bijection `w ↦ v + r • w`
    have he : Function.Surjective fun w : Euclid n => v + r • w := fun u =>
      ⟨r⁻¹ • (u - v), by simp only [smul_inv_smul₀ hr, add_sub_cancel]⟩
    rw [← Set.range_comp, ← he.range_comp]
    congr 1
    funext w
    -- Step 1: `η(Φ(v + r • w)) = r⁻¹ • (r • ι w + (ι' (f (v + r • w)) - ι' (f v)))`
    simp only [Function.comp_apply, Poincare.SimonGMT.Chapter03.blowUpMap, map_add, map_smul,
      map_sub]
    rw [show a + (ι v + r • ι w) + ι' (f (v + r • w)) - (a + ι v + ι' (f v)) =
        r • ι w + (ι' (f (v + r • w)) - ι' (f v)) by abel, smul_add, inv_smul_smul₀ hr]
  · by_cases hf : DifferentiableAt ℝ f (v + r • w)
    · -- Step 4: chain rule through `w' ↦ v + r • w'`, whose derivative is `r • id`
      have h : HasFDerivAt (fun w' => r⁻¹ • (f (v + r • w') - f v))
          (r⁻¹ • (fderiv ℝ f (v + r • w)).comp (r • ContinuousLinearMap.id ℝ (Euclid n))) w :=
        ((hf.hasFDerivAt.comp w (((hasFDerivAt_id w).const_smul r).const_add v)).sub_const
          (f v)).const_smul r⁻¹
      rw [h.fderiv, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
        ContinuousLinearMap.comp_id, inv_smul_smul₀ hr]
    · -- Step 5: `u ↦ r⁻¹ • (u - v)` maps `v + r • w` to `w` and
      -- `f u = f v + r • f_{v,r} (r⁻¹ • (u - v))`, so `f_{v,r}` is not differentiable at `w`
      -- either; both derivatives are `0`
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt]
      intro hg
      have hw : r⁻¹ • (v + r • w - v) = w := by rw [add_sub_cancel_left, inv_smul_smul₀ hr]
      rw [← hw] at hg
      have hL : DifferentiableAt ℝ (fun u : Euclid n => r⁻¹ • (u - v)) (v + r • w) :=
        (differentiableAt_id.sub_const v).const_smul r⁻¹
      refine hf ((((hg.comp (v + r • w) hL).const_smul r).const_add (f v)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u => ?_))
      simp only [Pi.smul_apply, Function.comp_apply, smul_inv_smul₀ hr, add_sub_cancel]

/-- Difference quotients `r⁻¹(f(v + rw) − f(v))` of a map differentiable at `v` converge to
`Df(v)w` uniformly on every closed ball `B̄_R(0)` as `r ↓ 0` (the `o(|h|)` estimate in the
weighted blow-up limit of the Allard graph step).  With `R' = max R 1`, pick `ρ > 0` such that
`|f(v + h) − f(v) − Df(v)h| ≤ ε|h|/(2R')` for `|h| < ρ`.  For `0 < r < ρ/R'` and `|w| ≤ R`,
`|rw| < ρ`, and linearity of `Df(v)` gives `|Df(v)w − r⁻¹(f(v + rw) − f(v))| ≤ ε|w|/(2R') < ε`. -/
theorem Submission.dorwbl_diff_quotient_tendstoUniformlyOn : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (v : Euclid n), DifferentiableAt ℝ f v → ∀ R : ℝ, TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => r⁻¹ • (f (v + r • w) - f v)) (fun w => fderiv ℝ f v w) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
  intro n k f v hf R
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hR : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hc : 0 < ε / (2 * max R 1) := by positivity
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).bound hc)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / max R 1 by positivity)] with r hr w hw
  obtain ⟨hr0, hrρ⟩ := hr
  have hw' : ‖w‖ ≤ max R 1 := (mem_closedBall_zero_iff.1 hw).trans (le_max_left R 1)
  have hrw : ‖r • w‖ = r * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
  -- `|rw| ≤ rR' < ρ`, so the little-o bound applies to `h = rw`
  have hbound := hsmall (show dist (r • w) 0 < ρ by
    rw [dist_zero_right, hrw]
    calc r * ‖w‖ ≤ r * max R 1 := mul_le_mul_of_nonneg_left hw' hr0.le
      _ < ρ / max R 1 * max R 1 := mul_lt_mul_of_pos_right hrρ hR
      _ = ρ := div_mul_cancel₀ ρ hR.ne')
  -- `Df(v)w − r⁻¹(f(v + rw) − f(v)) = −r⁻¹(f(v + rw) − f(v) − Df(v)(rw))`
  have hid : fderiv ℝ f v w - r⁻¹ • (f (v + r • w) - f v) =
      -(r⁻¹ • (f (v + r • w) - f v - fderiv ℝ f v (r • w))) := by
    simp only [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
    abel
  rw [dist_eq_norm, hid, norm_neg, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le]
  calc r⁻¹ * ‖f (v + r • w) - f v - fderiv ℝ f v (r • w)‖
      ≤ r⁻¹ * (ε / (2 * max R 1) * ‖r • w‖) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr0.le)
    _ = ε / (2 * max R 1) * ‖w‖ := by
        rw [hrw]
        field_simp
    _ ≤ ε / (2 * max R 1) * max R 1 := mul_le_mul_of_nonneg_left hw' hc.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- Test-function step (Step 8) of the weighted graph blow-up limit used for the tangent planes of
Lipschitz graphs (cf. Simon Ch. 3, proof of 1.6 "⇒", where `∫_{η_{x,λ}(N)} f dHⁿ → ∫_{T_x N} f dHⁿ`).
If `f : ℝⁿ → ℝᵏ` is differentiable at `v` and `ψ ∈ C_c(ℝ^{n+k})`, then
`U(r) = ∫_{B̄_R(0)} |ψ(ιw + ι'(r⁻¹(f(v + rw) − f(v)))) − ψ(ιw + ι'(Df(v)w))| dw → 0` as `r ↓ 0`.
The difference quotients tend to `Df(v)` uniformly on `B̄_R(0)`; the isometry `ι'` carries this to
the graph maps, and `ψ` is uniformly continuous, so eventually the integrand is at most
`ε / (Lⁿ(B̄_R(0)) + 1)` on the ball, which has finite measure.  Continuity of `f` is not used. -/
theorem Submission.dorwbl_test_fn_diff_quotient_integral_tendsto_zero : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (ψ : Euclid (n + k) → ℝ), Continuous f → DifferentiableAt ℝ f v → Continuous ψ → HasCompactSupport ψ → ∀ R : ℝ, Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|) (𝓝[>] 0) (𝓝 0) := by
  intro n k ι ι' f v ψ _hf hfv hψ hψc R
  -- the graph maps `Φ_r w = ι w + ι' (f_{v,r} w)` tend to `Φ w = ι w + ι' (Df(v) w)` uniformly on
  -- `B̄_R(0)`: `dist (Φ w) (Φ_r w) = dist (Df(v) w) (f_{v,r} w)` since `ι'` is an isometry
  have hΦ : TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => ι w + ι' (r⁻¹ • (f (v + r • w) - f v)))
      (fun w => ι w + ι' (fderiv ℝ f v w)) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
    have h := Submission.dorwbl_diff_quotient_tendstoUniformlyOn n k f v hfv R
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with r hr w hw
    simp only [dist_add_left, LinearIsometry.dist_map]
    exact hr w hw
  -- `ψ` is uniformly continuous (continuous with compact support), so `ψ ∘ Φ_r → ψ ∘ Φ` uniformly
  have hψΦ := (hψc.uniformContinuous_of_continuous hψ).comp_tendstoUniformlyOn hΦ
  rw [Metric.tendstoUniformlyOn_iff] at hψΦ
  have hB : volume (closedBall (0 : Euclid n) R) < ∞ := measure_closedBall_lt_top
  have hV : 0 ≤ volume.real (closedBall (0 : Euclid n) R) := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- with `η = ε / (Lⁿ(B̄_R(0)) + 1)`, eventually `|U(r)| ≤ η Lⁿ(B̄_R(0)) < ε`
  have hη : 0 < ε / (volume.real (closedBall (0 : Euclid n) R) + 1) := div_pos hε (by linarith)
  filter_upwards [hψΦ _ hη] with r hr
  rw [dist_zero_right]
  refine (norm_setIntegral_le_of_norm_le_const
    (C := ε / (volume.real (closedBall (0 : Euclid n) R) + 1)) hB fun w hw => ?_).trans_lt ?_
  · have h1 := hr w hw
    simp only [Function.comp_apply, Real.dist_eq] at h1
    rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]
    exact h1.le
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith

/-- Weighted blow-up limit at one good point `v`.  Let `f` be continuous and differentiable at
`v`, `G` Borel with `|G| ≤ C`, and `∫_{B_R(0)} |G(v + r w) - G(v)| dw → 0` as `r ↓ 0` for every
`R > 0`.  With `Φ_r w = ι w + ι'(r⁻¹(f(v + r w) - f(v)))` and `Φ w = ι w + ι'(Df(v) w)`, every
continuous compactly supported `ψ` has `∫ ψ(Φ_r w) G(v + r w) dw → G(v) ∫ ψ(Φ w) dw`.
Orthogonality gives `‖w‖ ≤ ‖ι w + ι' u‖`, so both integrands vanish off `B_R(0)` once
`spt ψ ⊆ B_R(0)`; there they differ by at most `C |ψ ∘ Φ_r - ψ ∘ Φ| + M |G(v + r ·) - G(v)|`
(`|ψ| ≤ M`), whose integral tends to `0`. -/
theorem Submission.dorwbl_weighted_blowup_tendsto_at_point : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (G : Euclid n → ℝ) (C : ℝ) (v : Euclid n), (∀ x y, inner ℝ (ι x) (ι' y) = 0) → Continuous f → Measurable G → (∀ u, |G u| ≤ C) → DifferentiableAt ℝ f v → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v|) (𝓝[>] 0) (𝓝 0)) → ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)))) := by
  intro n k ι ι' f G C v horth hf hG hGC hdiff hleb ψ hψ hψc
  -- `|ψ| ≤ M`, and `tsupport ψ ⊆ closedBall 0 R₀` with `R₀ ≤ R`, `0 < R`.
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  have hψM : ∀ y, |ψ y| ≤ M := fun y => by rw [← Real.norm_eq_abs]; exact hM y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hψM 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hGC 0)
  obtain ⟨R₀, hR₀⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euclid (n + k))
  obtain ⟨R, hRpos, hR₀R⟩ : ∃ R : ℝ, 0 < R ∧ R₀ ≤ R :=
    ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  have hBfin : volume (closedBall (0 : Euclid n) R) ≠ ∞ := measure_closedBall_lt_top.ne
  -- Pythagoras: `‖w‖ ≤ ‖ι w + ι' u‖`.
  have hpyth : ∀ (w : Euclid n) (u : Euclid k), ‖w‖ ≤ ‖ι w + ι' u‖ := by
    intro w u
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth w u)
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map] at h
    refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
    rw [h]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  -- Both integrands vanish off `closedBall 0 R`.
  have hvanish : ∀ w : Euclid n, w ∉ closedBall (0 : Euclid n) R → ∀ u : Euclid k,
      ψ (ι w + ι' u) = 0 := by
    intro w hw u
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hw
    have h1 := hR₀ hmem
    rw [mem_closedBall_zero_iff] at h1 ⊢
    exact (hpyth w u).trans (h1.trans hR₀R)
  -- `C ∫_{B_R} |ψ ∘ Φ_r - ψ ∘ Φ| + M ∫_{B_R} |G(v + r ·) - G(v)| → 0`.
  have hU := Submission.dorwbl_test_fn_diff_quotient_integral_tendsto_zero n k ι ι' f v ψ hf
    hdiff hψ hψc R
  have hV := hleb R hRpos
  have hlim := (hU.const_mul C).add (hV.const_mul M)
  rw [mul_zero, mul_zero, add_zero] at hlim
  -- Pointwise: `a x - G(v) b = (a - b) x + b (x - G(v))`.
  have hpt : ∀ a b x : ℝ, |b| ≤ M → |x| ≤ C →
      |a * x - G v * b| ≤ C * |a - b| + M * |x - G v| := by
    intro a b x hb hx
    calc |a * x - G v * b| = |(a - b) * x + b * (x - G v)| := by congr 1; ring
      _ ≤ |(a - b) * x| + |b * (x - G v)| := abs_add_le _ _
      _ = |a - b| * |x| + |b| * |x - G v| := by rw [abs_mul, abs_mul]
      _ ≤ |a - b| * C + M * |x - G v| :=
        add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
      _ = C * |a - b| + M * |x - G v| := by ring
  -- For every `r`, the error is bounded by the quantity in `hlim`.
  have key : ∀ r : ℝ,
      ‖(∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) -
          G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))‖ ≤
        C * (∫ w in closedBall (0 : Euclid n) R,
            |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|) +
          M * ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v| := by
    intro r
    have hcr : Continuous fun w : Euclid n => ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) := by
      fun_prop
    have hc : Continuous fun w : Euclid n => ψ (ι w + ι' (fderiv ℝ f v w)) := by fun_prop
    have hGr : Measurable fun w : Euclid n => G (v + r • w) :=
      hG.comp (by fun_prop : Continuous fun w : Euclid n => v + r • w).measurable
    have ha : IntegrableOn
        (fun w => ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w))
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := M * C) hBfin
        (hcr.measurable.mul hGr).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hψM _) (hGC _) (abs_nonneg _) hM0)
    have hb : IntegrableOn (fun w => G v * ψ (ι w + ι' (fderiv ℝ f v w)))
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := C * M) hBfin
        (hc.measurable.const_mul (G v)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hGC _) (hψM _) (abs_nonneg _) hC0)
    have hΔ : IntegrableOn
        (fun w => |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|)
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := M + M) hBfin
        (continuous_abs.measurable.comp (hcr.measurable.sub hc.measurable)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (add_le_add (hψM _) (hψM _)))
    have hg : IntegrableOn (fun w => |G (v + r • w) - G v|) (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := C + C) hBfin
        (continuous_abs.measurable.comp (hGr.sub measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (add_le_add (hGC _) (hGC _)))
    have hA : (∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) =
        ∫ w in closedBall (0 : Euclid n) R,
          ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hvanish w hw, zero_mul]
    have hB : G v * (∫ w, ψ (ι w + ι' (fderiv ℝ f v w))) =
        ∫ w in closedBall (0 : Euclid n) R, G v * ψ (ι w + ι' (fderiv ℝ f v w)) := by
      rw [← integral_const_mul]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hvanish w hw, mul_zero]
    rw [hA, hB, ← integral_sub ha hb, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hΔ.const_mul C) (hg.const_mul M)]
    refine norm_integral_le_of_norm_le ((hΔ.const_mul C).add (hg.const_mul M))
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs]
    exact hpt _ _ _ (hψM _) (hGC _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun r => norm_nonneg _) key hlim
/-- **Lebesgue points, rescaled** (Simon Ch. 1, Corollary 3.17, in the Lebesgue-point form of
Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`): if `g : ℝⁿ → ℝ` is locally
`Lⁿ`-integrable, then for `Lⁿ`-a.e. `v` and every `R > 0`, `∫_{B_R(0)} |g(v + rw) − g(v)| dw → 0`
as `r ↓ 0`.  The substitutions `u = rw`, `y = v + u` and `Lⁿ(B_{rR}(v)) = rⁿ Lⁿ(B_R(0))` give
`∫_{B_R(0)} |g(v + rw) − g(v)| dw = Lⁿ(B_R(0)) ⨍_{B_{rR}(v)} |g − g(v)|`, and these averages tend
to `0` at every Lebesgue point `v` of `g`. -/
theorem Submission.doraggt_ae_rescaled_lebesgue_point : ∀ (n : ℕ) (g : Euclid n → ℝ), LocallyIntegrable g volume → ∀ᵐ v ∂(volume : Measure (Euclid n)), ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v|) (𝓝[>] 0) (𝓝 0) := by
  intro n g hg
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (volume : Measure (Euclid n)) hg 1] with v hv R hR
  -- Lebesgue point: the averages over `closedBall v (r * R)` tend to `0` as `r ↓ 0`
  have hδ : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  have hA : Tendsto (fun r : ℝ => ⨍ y in closedBall v (r * R), |g y - g v|) (𝓝[>] 0) (𝓝 0) := by
    have h := hv (fun _ => v) (fun r : ℝ => r * R) hδ (by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      rw [one_mul]
      exact mem_closedBall_self (mul_pos hr hR).le)
    simpa only [Real.norm_eq_abs] using h
  -- change of variables `u = r • w` (dilation), `y = v + u` (translation)
  have key : ∀ r : ℝ, 0 < r → ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v| =
      volume.real (closedBall (0 : Euclid n) R) * ⨍ y in closedBall v (r * R), |g y - g v| := by
    intro r hr
    have h1 : ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v| =
        (r ^ n)⁻¹ • ∫ u in closedBall (0 : Euclid n) (r * R), |g (v + u) - g v| := by
      rw [Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euclid n))
        (fun u => |g (v + u) - g v|) _ hr, _root_.smul_closedBall _ _ hR.le, smul_zero,
        Real.norm_of_nonneg hr.le, finrank_euclideanSpace_fin]
    have h2 : ∫ u in closedBall (0 : Euclid n) (r * R), |g (v + u) - g v| =
        ∫ y in closedBall v (r * R), |g y - g v| := by
      have h := MeasurePreserving.setIntegral_preimage_emb
        (measurePreserving_add_left (volume : Measure (Euclid n)) v)
        (measurableEmbedding_addLeft v) (fun y => |g y - g v|) (closedBall v (r * R))
      simpa using h
    -- `∫_{B_{rR}(v)} = Lⁿ(B_{rR}(v)) ⨍_{B_{rR}(v)}` and `Lⁿ(B_{rR}(v)) = rⁿ Lⁿ(B_R(0))`
    have h3 := measure_smul_setAverage (μ := (volume : Measure (Euclid n)))
      (fun y => |g y - g v|) (s := closedBall v (r * R)) measure_closedBall_lt_top.ne
    rw [h1, h2, ← h3, smul_eq_mul, smul_eq_mul,
      Measure.addHaar_real_closedBall _ _ (mul_pos hr hR).le,
      Measure.addHaar_real_closedBall _ _ hR.le, finrank_euclideanSpace_fin, mul_pow]
    have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr.ne'
    field_simp
  have hlim : Tendsto (fun r : ℝ => volume.real (closedBall (0 : Euclid n) R) *
      ⨍ y in closedBall v (r * R), |g y - g v|) (𝓝[>] 0) (𝓝 0) := by
    simpa using hA.const_mul (volume.real (closedBall (0 : Euclid n) R))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact (key r hr).symm

/-- **Weighted blow-ups of a Lipschitz graph** (Simon Ch. 2, Theorem 1.4 (Rademacher) and Ch. 1,
Corollary 3.17).  Let `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` be linear isometries with
orthogonal ranges, `f : ℝⁿ → ℝᵏ` Lipschitz and `G : ℝⁿ → ℝ` measurable with `|G| ≤ C`.  Then for
`Lⁿ`-a.e. `v`, `f` is differentiable at `v` and, for every continuous compactly supported `ψ`,
`∫ ψ(ιw + ι'(r⁻¹(f(v + rw) − f(v)))) G(v + rw) dw → G(v) ∫ ψ(ιw + ι'(Df(v)w)) dw` as `r ↓ 0`.
The bounded measurable weight `G` is locally integrable, so Rademacher's theorem and the rescaled
Lebesgue-point property of `G` hold simultaneously at a.e. `v`; at every such `v` the convergence
is the blow-up limit at a differentiability point that is a rescaled Lebesgue point of `G`. -/
theorem Submission.doraggt_ae_weighted_graph_blowup_tendsto : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (L : NNReal) (G : Euclid n → ℝ) (C : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L f → Measurable G → (∀ u, |G u| ≤ C) → ∀ᵐ v ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f v ∧ ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)))) := by
  intro n k ι ι' f L G C horth hf hG hGC
  -- `G` is bounded and measurable, hence integrable on every compact set
  have hloc : LocallyIntegrable G volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hG.aestronglyMeasurable (M := C)
      (Eventually.of_forall fun u => (Real.norm_eq_abs (G u)).trans_le (hGC u))
  -- Rademacher and the rescaled Lebesgue-point property of `G` hold simultaneously a.e.
  filter_upwards [hf.ae_differentiableAt (μ := volume),
    Submission.doraggt_ae_rescaled_lebesgue_point n G hloc] with v hv hleb
  -- at such `v`, the blow-up limit holds for every test function `ψ`
  exact ⟨hv, Submission.dorwbl_weighted_blowup_tendsto_at_point n k ι ι' f G C v horth
    hf.continuous hG hGC hv hleb⟩

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

/-- **The approximate tangent plane of a Lipschitz graph, transferred to an integer multiplicity
carrier** (Simon Ch. 3, Definition 1.4, Remarks 1.5(1)–(2) and the proof of Theorem 1.6 "⇒";
Ch. 2, area formula 3.2–3.5 and Example 3.6(3); Ch. 1, Upper Density Theorem 3.6).
Let `Φ(u) = a + ιu + ι'(f u)`, `F = Φ(ℝⁿ)` and `P_v = range (ι + ι' ∘ Df(v))`.  With the graph
Jacobian `Ĵ(T) = normDet (ι + ι' ∘ T)` (continuous in `T`, SimonGMT `continuous_normDet`), the
injective Lipschitz area formula (SimonGMT `injective_area_formula_lipschitz`, Rademacher) gives
`Hⁿ⌞(graph of g through 0) = (w ↦ ιw + ι'(g w))_# (Ĵ(Dg) Lⁿ)` for Lipschitz `g`.  Applied to the
blow-ups `η_{Φ(v),r}(F)`, graphs of the difference quotients `f_{v,r}` with `Df_{v,r}(w) =
Df(v + rw)`, and to `P_v`, the graph of `Df(v)`, this turns the weighted blow-up limit for the
bounded measurable weight `G = Ĵ ∘ Df` into `HasApproximateTangentSpaceAt n F (Φ v) P_v` for
`Lⁿ`-a.e. `v`.  The exceptional parameters have `Hⁿ`-null image, and the approximate tangent
planes of `F` and of the carrier `M` agree `Hⁿ`-a.e. on `M ∩ F ∩ W` (both are Borel and locally
`Hⁿ`-finite in `W`, `θ ≥ 1` on `M`); uniqueness of the approximate tangent plane concludes. -/
theorem Submission.dorag_lipschitz_graph_approxTangent : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (a : Euclid (n + k)) (f : Euclid n → Euclid k) (L : NNReal), IsOpen W → W ⊆ U → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L f → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ v : Euclid n, x = a + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) := by
  intro n k _ U W R ι ι' a f L hW hWU horth hf
  -- Step 0: the graph Jacobian `Ĵ(T) = normDet (ι + ι' ∘ T)` is continuous in `T`.
  obtain ⟨Jh, hJh_def⟩ : ∃ Jh : (Euclid n →L[ℝ] Euclid k) → ℝ, ∀ T, Jh T =
      ((ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp T :
        Euclid n →L[ℝ] Euclid (n + k)) : Euclid n →ₗ[ℝ] Euclid (n + k)).normDet :=
    ⟨_, fun _ => rfl⟩
  have hJh : Continuous Jh := by
    rw [show Jh = fun T => ((ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp T :
        Euclid n →L[ℝ] Euclid (n + k)) : Euclid n →ₗ[ℝ] Euclid (n + k)).normDet from
      funext hJh_def]
    exact Poincare.SimonGMT.Chapter02.continuous_normDet.comp
      (continuous_const.add (continuous_const.clm_comp continuous_id))
  have hJh0 : ∀ T, 0 ≤ Jh T := fun T => by
    rw [hJh_def]
    exact LinearMap.normDet_nonneg _
  -- Step 2, area formula (Simon Ch. 2, 3.2–3.5) for a Lipschitz graph through the origin, as an
  -- identity of measures `Hⁿ⌞(graph g) = (w ↦ ιw + ι'(g w))_# (Ĵ(Dg) Lⁿ)` (Rademacher).
  have area : ∀ (g : Euclid n → Euclid k) (K : NNReal), LipschitzWith K g →
      (μHE[n] : Measure (Euclid (n + k))).restrict (Set.range fun u => ι u + ι' (g u)) =
        Measure.map (fun u => ι u + ι' (g u)) ((volume : Measure (Euclid n)).withDensity
          fun u => ENNReal.ofReal (Jh (fderiv ℝ g u))) := by
    intro g K hg
    obtain ⟨h1, h2, -, -, -⟩ :=
      Submission.doraggt_lipschitz_graph_map_basics n k ι ι' 0 g K horth hg
    simp only [zero_add] at h1 h2
    have hinj : Injective fun u => ι u + ι' (g u) := fun u u' h => by
      have h' : ι u + ι' (g u) = ι u' + ι' (g u') := h
      have h3 := h1 u u'
      rw [h', dist_self] at h3
      exact dist_le_zero.1 h3
    have hmeas : Measurable fun u => ι u + ι' (g u) := h2.continuous.measurable
    ext S hS
    rw [Measure.restrict_apply hS, Measure.map_apply hmeas hS, withDensity_apply _ (hmeas hS),
      ← Set.image_preimage_eq_inter_range]
    have key :=
      Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitz h2 (hmeas hS) hinj.injOn
    rw [finrank_euclideanSpace_fin] at key
    rw [key]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hg.ae_differentiableAt (μ := volume)] with u hu
    have hd : HasFDerivAt (fun u => ι u + ι' (g u))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ g u)) u :=
      ι.toContinuousLinearMap.hasFDerivAt.add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp u hu.hasFDerivAt)
    rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet, hd.fderiv, hJh_def]
  -- Hence `∫_{graph g} ψ dHⁿ = ∫ ψ(ιw + ι'(g w)) Ĵ(Dg(w)) dw` for every continuous `ψ`.
  have areaInt : ∀ (g : Euclid n → Euclid k) (K : NNReal), LipschitzWith K g →
      ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ →
        ∫ y in Set.range (fun u => ι u + ι' (g u)), ψ y ∂μHE[n] =
          ∫ w, ψ (ι w + ι' (g w)) * Jh (fderiv ℝ g w) := by
    intro g K hg ψ hψ
    have h2 := (Submission.doraggt_lipschitz_graph_map_basics n k ι ι' 0 g K horth hg).2.1
    simp only [zero_add] at h2
    have hJm : Measurable fun u => ENNReal.ofReal (Jh (fderiv ℝ g u)) :=
      (hJh.measurable.comp (measurable_fderiv ℝ g)).ennreal_ofReal
    rw [area g K hg, integral_map h2.continuous.measurable.aemeasurable hψ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hJm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hJh0 _), mul_comm]
  -- Step 1: the weight `G = Ĵ ∘ Df` is measurable and bounded (`‖Df‖ ≤ L`).
  obtain ⟨G, hG⟩ : ∃ G : Euclid n → ℝ, ∀ u, G u = Jh (fderiv ℝ f u) :=
    ⟨fun u => Jh (fderiv ℝ f u), fun _ => rfl⟩
  have hGm : Measurable G := by
    rw [show G = fun u => Jh (fderiv ℝ f u) from funext hG]
    exact hJh.measurable.comp (measurable_fderiv ℝ f)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Euclid n →L[ℝ] Euclid k) L).exists_bound_of_continuousOn
      hJh.continuousOn
  have hGC : ∀ u, |G u| ≤ C := fun u => by
    rw [hG, ← Real.norm_eq_abs]
    exact hC _ (mem_closedBall_zero_iff.2 (norm_fderiv_le_of_lipschitz ℝ hf))
  -- Step 2, blow-up limit: at good parameters `v`, `F` has approximate tangent plane `P_v`
  -- at `Φ(v)`.
  have tangentF : ∀ v : Euclid n, (∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ →
        Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w))
          (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))))) →
      HasApproximateTangentSpaceAt n (Set.range fun u => a + ι u + ι' (f u)) (a + ι v + ι' (f v))
        (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) := by
    intro v hlim
    have hD1 := (Submission.doraggt_lipschitz_graph_map_basics n k ι ι' 0 (fderiv ℝ f v)
      ‖fderiv ℝ f v‖₊ horth (fderiv ℝ f v).lipschitzWith).1
    simp only [zero_add] at hD1
    have hPset : ((LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ
        (fderiv ℝ f v).toLinearMap) : Submodule ℝ (Euclid (n + k))) : Set (Euclid (n + k))) =
        Set.range fun u => ι u + ι' (fderiv ℝ f v u) := by
      rw [LinearMap.coe_range]
      rfl
    refine ⟨?_, fun ψ => ?_⟩
    · rw [LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin]
      intro u u' h
      have h' : ι u + ι' (fderiv ℝ f v u) = ι u' + ι' (fderiv ℝ f v u') := h
      have h3 := hD1 u u'
      rw [h', dist_self] at h3
      exact dist_le_zero.1 h3
    · have hval : ∫ y in ((LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ
          (fderiv ℝ f v).toLinearMap) : Submodule ℝ (Euclid (n + k))) : Set (Euclid (n + k))),
            ψ y ∂μHE[n] = G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)) := by
        rw [hPset, areaInt _ _ (fderiv ℝ f v).lipschitzWith ψ (map_continuous ψ)]
        simp only [ContinuousLinearMap.fderiv]
        rw [integral_mul_const, hG, mul_comm]
      rw [hval]
      refine (hlim ψ (map_continuous ψ) ψ.hasCompactSupport).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      have hfr : LipschitzWith L fun w' => r⁻¹ • (f (v + r • w') - f v) := by
        refine LipschitzWith.of_dist_le_mul fun w w' => ?_
        rw [dist_smul₀, dist_sub_right, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * dist (f (v + r • w)) (f (v + r • w'))
            ≤ r⁻¹ * (L * dist (v + r • w) (v + r • w')) :=
              mul_le_mul_of_nonneg_left (hf.dist_le_mul _ _) (inv_nonneg.2 hr.le)
          _ = L * dist w w' := by
              rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le, mul_left_comm,
                inv_mul_cancel_left₀ hr.ne']
      obtain ⟨hset, hder⟩ := Submission.doraggt_graph_blowup_rescaling n k ι ι' a f v r hr.ne'
      rw [hset, areaInt _ L hfr ψ (map_continuous ψ)]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [hder w, hG]
  -- Steps 1–2: Rademacher and the weighted blow-up limit hold at `Lⁿ`-a.e. parameter.
  have hgood :=
    Submission.doraggt_ae_weighted_graph_blowup_tendsto n k ι ι' f L G C horth hf hGm hGC
  have hgood' : ∀ᵐ v ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f v ∧
      HasApproximateTangentSpaceAt n (Set.range fun u => a + ι u + ι' (f u)) (a + ι v + ι' (f v))
        (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) :=
    hgood.mono fun v hv => ⟨hv.1, tangentF v hv.2⟩
  -- Steps 1 and 3: the bad parameters have `Hⁿ`-null image; `M` and `F` are Borel and locally
  -- `Hⁿ`-finite in `W` (`θ ≥ 1` on `M`), so their approximate tangent planes agree a.e. (Step 4).
  obtain ⟨-, -, hFclosed, hFfin, hnull⟩ :=
    Submission.doraggt_lipschitz_graph_map_basics n k ι ι' a f L horth hf
  have hN := hnull _ (ae_iff.1 hgood')
  have hMfin : ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ W → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKW
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK (hKW.trans hWU)) ?_
    rw [← setLIntegral_one]
    refine setLIntegral_mono' (R.measurableSet_carrier.inter hK.isClosed.measurableSet)
      fun x hx => ?_
    exact Nat.one_le_cast.2 (R.mult_pos x hx.1)
  have htransfer := Submission.doraggt_ae_approxTangent_transfer (n + k) n W R.carrier
    (Set.range fun u => a + ι u + ι' (f u)) hW R.measurableSet_carrier hFclosed.measurableSet
    hMfin (fun K hK _ => hFfin K hK)
  -- Step 5: conclusion, by uniqueness of the approximate tangent plane (Remark 1.5(1)).
  rw [ae_restrict_iff' (R.measurableSet_carrier.inter hW.measurableSet)]
  filter_upwards [htransfer, measure_eq_zero_iff_ae_notMem.1 hN] with x hxT hxN
  rintro ⟨hxM, hxW⟩ v rfl
  obtain ⟨hdiff, hF⟩ : DifferentiableAt ℝ f v ∧
      HasApproximateTangentSpaceAt n (Set.range fun u => a + ι u + ι' (f u)) (a + ι v + ι' (f v))
        (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) := by
    by_contra hcon
    exact hxN ⟨v, hcon, rfl⟩
  have hM := (hxT hxW hxM ⟨v, rfl⟩ _).2 hF
  have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier (a + ι v + ι' (f v)) Q := ⟨_, hM⟩
  refine ⟨hdiff, ?_⟩
  rw [approxTangentPlane, dite_eq_left hex]
  exact hex.choose_spec.unique hM
/-- **Tilt-excess is controlled by height** (Simon Ch. 5, Lemma 2.1, with `|H| ≤ κ`).  With
`p_S^⊥ = I − p_S` and `C = 146`,
`∫_{B_{r/2}(ξ)} |p_{TₓM} − p_S|² dμ ≤ C (r⁻² ∫_{B_r(ξ)} |p_S^⊥(x − ξ)|² dμ + κ²r² μ(B_r(ξ)))`.
Take the radial cut-off `ζ` (`ζ = 1` on `B_{r/2}(ξ)`, `tsupport ζ ⊆ B_r(ξ)`, `|Dζ| ≤ 3/r`); the
energy inequality for the test field `ζ² p_S^⊥(x − ξ)` gives
`∫ ζ² |p_{TₓM} − p_S|² dμ ≤ 16 ∫ |Dζ|² |p_S^⊥(x − ξ)|² dμ + 4 ∫ κ ζ² |p_S^⊥(x − ξ)| dμ`.
As `ζ = 1` on `B_{r/2}(ξ)`, the left side bounds the tilt over the half ball.  Off `B_r(ξ)` both
`ζ` and `Dζ` vanish, while on `B_r(ξ)`, `16 |Dζ|² ≤ 144/r²` and, as `0 ≤ ζ ≤ 1` and `κ ≥ 0`,
`4 κ ζ² t ≤ 4 κ t ≤ 2 t²/r² + 2 κ² r²` for `t = |p_S^⊥(x − ξ)|`.  Finally `144 + 2 = 146` and
`2 ≤ 146`. -/
theorem Submission.dorag_tilt_height_estimate : ∀ (n k : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r : ℝ) (S : Submodule ℝ (Euclid (n + k))), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → 0 < r → closedBall ξ r ⊆ W → Module.finrank ℝ S = n → ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r)) := by
  intro n k
  refine ⟨146, by norm_num, ?_⟩
  intro U W R H κ ξ r S _hW hWU hH hHκ hMC hr hball hS
  -- `κ ≥ 0`, since `‖H 0‖ ≤ κ`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- the radial cut-off `ζ`; its support is compact and lies in `B_r(ξ) ⊆ W`
  obtain ⟨ζ, hζC, hζ01, hζ1, hζsupp, hζD⟩ := Submission.dorag_th_radial_cutoff (n + k) ξ r hr
  have hζcpt : HasCompactSupport ζ :=
    (isCompact_closedBall ξ r).of_isClosed_subset (isClosed_tsupport ζ) hζsupp
  -- the energy inequality for the test field `ζ² p_S^⊥(x − ξ)`
  have hE := Submission.dorag_th_tilt_energy_inequality (n + k) n U W R H κ S ξ ζ hWU
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hH hHκ hMC hS hζC hζcpt
    (hζsupp.trans hball)
  -- the left side: `ζ = 1` on `B_{r/2}(ξ)`
  have h1 : ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k),
        ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤
      ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin (n + k),
        ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall ξ (r / 2)
    · simp only [indicator_of_mem hx, hζ1 x hx, one_pow, one_mul, le_refl]
    · simp only [indicator_of_notMem hx, zero_le]
  -- the gradient term: `Dζ = 0` off `B_r(ξ)`, and `16 |Dζ|² ≤ 144/r²`
  have h2 : ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 *
        ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure ≤
      ENNReal.ofReal 144 * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r,
        ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall ξ r
    · simp only [indicator_of_mem hx]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hD : ‖fderiv ℝ ζ x‖ ^ 2 ≤ (3 / r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hζD x) 2
      calc 16 * (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2)
          ≤ 16 * ((3 / r) ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) := by gcongr
        _ = 144 * (1 / r ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) := by ring
    · simp [indicator_of_notMem hx, fderiv_of_notMem_tsupport ℝ fun h => hx (hζsupp h)]
  -- the mean-curvature term: `ζ = 0` off `B_r(ξ)`, and `4 κ ζ² t ≤ 2 t²/r² + 2 κ²r²`
  have h3 : ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 *
        ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r,
        ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure) +
      ENNReal.ofReal 2 * (ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r)) := by
    rw [← mul_assoc (ENNReal.ofReal 2) (ENNReal.ofReal (κ ^ 2 * r ^ 2)), ← setLIntegral_const,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_right _ measurable_const, ← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall ξ r
    · simp only [indicator_of_mem hx]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht : 0 ≤ ‖(x - ξ) - S.starProjection (x - ξ)‖ := norm_nonneg _
      have hz2 : ζ x ^ 2 ≤ 1 := pow_le_one₀ (hζ01 x).1 (hζ01 x).2
      have hκt : κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤
          κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ := by
        calc κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖
            = κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ * ζ x ^ 2 := by ring
          _ ≤ κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ * 1 :=
            mul_le_mul_of_nonneg_left hz2 (mul_nonneg hκ ht)
          _ = κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ := mul_one _
      -- `2ab ≤ a² + b²` with `a = t/r`, `b = κr`, where `t = |p_S^⊥(x − ξ)|`
      have hab := two_mul_le_add_sq (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) (κ * r)
      have e1 : 2 * (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) * (κ * r) =
          2 * (κ * ‖(x - ξ) - S.starProjection (x - ξ)‖) := by
        rw [show 2 * (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) * (κ * r) =
            2 * (κ * ‖(x - ξ) - S.starProjection (x - ξ)‖) * (r / r) by ring,
          div_self hr.ne', mul_one]
      have e2 : (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) ^ 2 + (κ * r) ^ 2 =
          1 / r ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2 + κ ^ 2 * r ^ 2 := by ring
      linarith
    · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h => hx (hζsupp h)]
  -- combine: `144 + 2 = 146` and `2 ≤ 146`
  have arith : ∀ X Y : ℝ≥0∞,
      ENNReal.ofReal 144 * X + (ENNReal.ofReal 2 * X + ENNReal.ofReal 2 * Y) ≤
        ENNReal.ofReal 146 * (X + Y) := by
    intro X Y
    simp only [ENNReal.ofReal_ofNat]
    calc 144 * X + (2 * X + 2 * Y) ≤ 144 * X + (2 * X + 2 * Y) + 144 * Y := le_self_add
      _ = 146 * (X + Y) := by ring
  exact h1.trans (hE.trans ((add_le_add h2 h3).trans (arith _ _)))
/-- **Simon, Ch. 5, 3.3** ("applying this with `D_j u` in place of `u`"): a directional derivative
`u_e = Dh(·) e` of a smooth harmonic `h` on an open `U ⊆ ℝⁿ` is smooth and harmonic on `U`.  With
`G = D²h` and `H = D³h`: near `y ∈ U`, `Du_e(z) b = G z b e`, so `D²u_e(y)(a, b) = H y a b e`;
symmetry of `D²h` on `U` and of `D²(Dh)` at `y` give `H y eᵢ eᵢ e = H y e eᵢ eᵢ`, and
`∑ᵢ H y e eᵢ eᵢ` is the `e`-derivative at `y` of `z ↦ Δh(z)`, which vanishes near `y`. -/
theorem Submission.dorag_ha_ie_fderiv_apply_harmonic : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (e : Euclid n), IsOpen U → (∀ m : ℕ, ContDiffOn ℝ m h U) → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ m : ℕ, ContDiffOn ℝ m (fun y => fderiv ℝ h y e) U) ∧ ∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun z => fderiv ℝ h z e) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
  intro n U h e hU hh hΔ
  -- (i): `Dh` is `Cᵐ` on the open set `U`, and so is its evaluation at `e`
  have hu : ∀ m : ℕ, ContDiffOn ℝ m (fun y => fderiv ℝ h y e) U := fun m =>
    ((hh (m + 1)).fderiv_of_isOpen (m := m) hU (by push_cast; exact le_rfl)).clm_apply
      contDiffOn_const
  refine ⟨hu, fun y hy => ?_⟩
  -- `h` is `C³` at every point of `U`, so `F = Dh` is differentiable on `U`
  have h3 : ∀ z ∈ U, ContDiffAt ℝ 3 h z := fun z hz => (hh 3).contDiffAt (hU.mem_nhds hz)
  have hFd : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ h) z := fun z hz =>
    ((h3 z hz).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  -- the derivative of `z ↦ c z v` at `z` is `a ↦ Dc(z) a v`
  have ev : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (c : Euclid n → Euclid n →L[ℝ] W) (v z a : Euclid n), DifferentiableAt ℝ c z →
      fderiv ℝ (fun z' => c z' v) z a = fderiv ℝ c z a v := by
    intro W _ _ c v z a hc
    rw [fderiv_clm_apply hc (differentiableAt_const v)]
    simp
  -- `F` is `C²` at `y`, so `G = D²h` is differentiable at `y`
  have hF2 : ContDiffAt ℝ 2 (fderiv ℝ h) y := (h3 y hy).fderiv_right (by norm_num)
  have hGd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ h)) y :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGbd : ∀ b, DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ h) z b) y := fun b =>
    hGd.clm_apply (differentiableAt_const b)
  -- (∗): `D(z ↦ G z b c)(y) a = H y a b c`
  have hstar : ∀ a b c, fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ h) z b c) y a =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b c := by
    intro a b c
    rw [ev (fun z => fderiv ℝ (fderiv ℝ h) z b) c y a (hGbd b), ev _ b y a hGd]
  -- `D²u_e(y)(a, b) = H y a b e`
  have hud : DifferentiableAt ℝ (fderiv ℝ (fun z => fderiv ℝ h z e)) y :=
    (((hu 2).contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hu2 : ∀ a b, iteratedFDeriv ℝ 2 (fun z => fderiv ℝ h z e) y ![a, b] =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b e := by
    intro a b
    have hloc : (fun z => fderiv ℝ (fun z => fderiv ℝ h z e) z b) =ᶠ[𝓝 y]
        fun z => fderiv ℝ (fderiv ℝ h) z b e := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ev (fderiv ℝ h) e z b (hFd z hz)
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ev _ b y a hud, hloc.fderiv_eq, hstar]
  -- symmetry of `D²(Dh)` at `y`: `H y a b = H y b a`
  have hsym1 : ∀ a b, fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y b a := fun a b =>
    (hF2.isSymmSndFDerivAt (by norm_num)).eq a b
  -- symmetry of `D²h` on `U`, differentiated at `y`: `H y a b c = H y a c b`
  have hsym2 : ∀ a b c, fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a c b := by
    intro a b c
    have hloc : (fun z => fderiv ℝ (fderiv ℝ h) z b c) =ᶠ[𝓝 y]
        fun z => fderiv ℝ (fderiv ℝ h) z c b := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ((h3 z hz).isSymmSndFDerivAt (by norm_num)).eq b c
    rw [← hstar a b c, ← hstar a c b, hloc.fderiv_eq]
  -- the `e`-derivative of `z ↦ Δh(z) = ∑ᵢ G z eᵢ eᵢ`, which vanishes near `y`
  have hL : ∑ i : Fin n, fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y e (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    have hloc : (fun z => ∑ i : Fin n, fderiv ℝ (fderiv ℝ h) z (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
        hΔ z hz
    have h0 := congrArg (fun φ : Euclid n →L[ℝ] ℝ => φ e) (hloc.fderiv_eq (𝕜 := ℝ))
    simp only [fderiv_const_apply, zero_apply] at h0
    rw [fderiv_fun_sum fun i _ => (hGbd _).clm_apply (differentiableAt_const _),
      sum_apply] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => (hstar e _ _).symm
  rw [← hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hu2, hsym2 _ _ e, hsym1 _ e]
/-- If `f` is continuous on `closedBall y ρ` and equals its own ball mean at `y`,
`∫_{B_ρ(y)} f = V f(y)` with `V = Lⁿ(B_ρ(y))`, then `f(y)² V ≤ ∫_{B_ρ(y)} f²` (Simon Ch. 5, 3.2
with `q = 0`): `0 ≤ ∫_{B_ρ(y)} (f − f(y))² = ∫_{B_ρ(y)} f² − 2f(y) ∫_{B_ρ(y)} f + f(y)² V
= ∫_{B_ρ(y)} f² − f(y)² V`. -/
theorem Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value : ∀ (n : ℕ) (f : Euclid n → ℝ) (y : Euclid n) (ρ : ℝ), 0 < ρ → ContinuousOn f (closedBall y ρ) → ∫ z in ball y ρ, f z = (volume (ball y ρ)).toReal * f y → f y ^ 2 * (volume (ball y ρ)).toReal ≤ ∫ z in ball y ρ, f z ^ 2 := by
  intro n f y ρ _ hf hmean
  -- `f` and `f²` are continuous on the compact closed ball, hence integrable on the ball
  have hfi : IntegrableOn f (ball y ρ) :=
    (hf.integrableOn_compact (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
  have hf2i : IntegrableOn (fun z => f z ^ 2) (ball y ρ) :=
    ((hf.pow 2).integrableOn_compact (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
  have hci : IntegrableOn (fun _ => f y ^ 2) (ball y ρ) := integrableOn_const measure_ball_lt_top.ne
  have hnonneg : 0 ≤ ∫ z in ball y ρ, (f z - f y) ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun z _ => sq_nonneg _
  -- expand the square: `∫ (f − f(y))² = ∫ f² − 2f(y) ∫ f + f(y)² V`
  have hexp : ∫ z in ball y ρ, (f z - f y) ^ 2 = (∫ z in ball y ρ, f z ^ 2) -
      2 * f y * (∫ z in ball y ρ, f z) + f y ^ 2 * (volume (ball y ρ)).toReal := by
    have hi : IntegrableOn (fun z => f z ^ 2 - 2 * f y * f z) (ball y ρ) :=
      hf2i.sub (hfi.const_mul _)
    calc ∫ z in ball y ρ, (f z - f y) ^ 2
        = ∫ z in ball y ρ, ((f z ^ 2 - 2 * f y * f z) + f y ^ 2) := by
          congr 1; funext z; ring
      _ = (∫ z in ball y ρ, f z ^ 2) - 2 * f y * (∫ z in ball y ρ, f z) +
            f y ^ 2 * (volume (ball y ρ)).toReal := by
          rw [integral_add hi hci, integral_sub hf2i (hfi.const_mul _), integral_const_mul,
            setIntegral_const, smul_eq_mul, measureReal_def, mul_comm (volume (ball y ρ)).toReal]
  -- insert `∫ f = V f(y)`
  rw [hexp, hmean] at hnonneg
  linarith

/-- **Operator-norm `L²` bound from the ball mean value identity** (the gradient case of the
interior estimates for harmonic functions, Simon Ch. 5, 3.2–3.3; chapter-05.txt lines 643–653).
Let `g : ℝⁿ → (ℝⁿ)*` be continuous on `closedBall y ρ`, `ρ > 0`, with `V = |B_ρ(y)|` and
`I = ∫_{B_ρ(y)} ‖g‖²`.  If every component `z ↦ g z e` has ball average `g y e`, then
`Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value` and `|g z e| ≤ ‖g z‖ ‖e‖` give
`(g y e)² V ≤ ∫_{B_ρ(y)} (g z e)² ≤ ‖e‖² I`, i.e. `|g y e| ≤ √(I/V) ‖e‖` for every `e`.  Hence
`‖g y‖ ≤ √(I/V)` (`opNorm_le_bound`) and `‖g y‖² V ≤ I`. -/
theorem Submission.dorag_ha_ie_opNorm_sq_mul_volume_le_of_mean_value : ∀ (n : ℕ) (g : Euclid n → (Euclid n →L[ℝ] ℝ)) (y : Euclid n) (ρ : ℝ), 0 < ρ → ContinuousOn g (closedBall y ρ) → (∀ e : Euclid n, ∫ z in ball y ρ, g z e = (volume (ball y ρ)).toReal * g y e) → ‖g y‖ ^ 2 * (volume (ball y ρ)).toReal ≤ ∫ z in ball y ρ, ‖g z‖ ^ 2 := by
  intro n g y ρ hρ hg hmv
  set V := (volume (ball y ρ)).toReal
  set I := ∫ z in ball y ρ, ‖g z‖ ^ 2
  -- `V > 0`, and `‖g‖²` is integrable on the ball (continuous on the compact closed ball).
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume y hρ).ne' measure_ball_lt_top.ne
  have hgn : IntegrableOn (fun z => ‖g z‖ ^ 2) (ball y ρ) :=
    ((hg.norm.pow 2).integrableOn_compact (isCompact_closedBall y ρ)).mono_set
      ball_subset_closedBall
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun z _ => sq_nonneg _
  -- Each component: `(g y e)² V ≤ ∫_{B_ρ(y)} (g z e)² ≤ ‖e‖² I`.
  have hcomp : ∀ e : Euclid n, g y e ^ 2 * V ≤ ‖e‖ ^ 2 * I := by
    intro e
    have hfe : ContinuousOn (fun z => g z e) (closedBall y ρ) := hg.clm_apply continuousOn_const
    have hfe2 : IntegrableOn (fun z => g z e ^ 2) (ball y ρ) :=
      ((hfe.pow 2).integrableOn_compact (isCompact_closedBall y ρ)).mono_set
        ball_subset_closedBall
    have hpt : ∀ z, g z e ^ 2 ≤ ‖e‖ ^ 2 * ‖g z‖ ^ 2 := fun z => by
      have h : |g z e| ≤ ‖g z‖ * ‖e‖ := by
        simpa only [Real.norm_eq_abs] using (g z).le_opNorm e
      calc g z e ^ 2 = |g z e| ^ 2 := (sq_abs _).symm
        _ ≤ (‖g z‖ * ‖e‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = ‖e‖ ^ 2 * ‖g z‖ ^ 2 := by ring
    calc g y e ^ 2 * V ≤ ∫ z in ball y ρ, g z e ^ 2 :=
          Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value n (fun z => g z e) y ρ hρ hfe
            (hmv e)
      _ ≤ ∫ z in ball y ρ, ‖e‖ ^ 2 * ‖g z‖ ^ 2 := setIntegral_mono hfe2 (hgn.const_mul _) hpt
      _ = ‖e‖ ^ 2 * I := integral_const_mul _ _
  -- Hence `|g y e| ≤ √(I/V) ‖e‖` for every `e`, so `‖g y‖ ≤ √(I/V)`.
  have hIV : 0 ≤ I / V := div_nonneg hI hV.le
  have hop : ‖g y‖ ≤ √(I / V) := by
    refine (g y).opNorm_le_bound (Real.sqrt_nonneg _) fun e => ?_
    have h : g y e ^ 2 ≤ ‖e‖ ^ 2 * (I / V) := by
      rw [mul_div_assoc', le_div_iff₀ hV]
      exact hcomp e
    calc ‖g y e‖ = √(g y e ^ 2) := by rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
      _ ≤ √(‖e‖ ^ 2 * (I / V)) := Real.sqrt_le_sqrt h
      _ = √(I / V) * ‖e‖ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]
  -- Square and multiply by `V > 0`.
  calc ‖g y‖ ^ 2 * V ≤ √(I / V) ^ 2 * V :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hop 2) hV.le
    _ = I := by rw [Real.sq_sqrt hIV, div_mul_cancel₀ I hV.ne']
/-- Shifted-ball comparison: if `‖w‖ ≤ ρ` and `|u| ≤ K` on `B_{ρ+‖w‖}(x)`, then the integrals of
`u` over `B_ρ(x + w)` and `B_ρ(x)` differ by at most `K ωₙ ((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)`.  Both balls
lie in `B_{ρ+‖w‖}(x)`; the difference of the integrals is `∫_{S₁} u − ∫_{S₂} u` with
`S₁ = B_ρ(x + w) \ B_ρ(x)`, `S₂ = B_ρ(x) \ B_ρ(x + w)`, and the disjoint sets `S₁`, `S₂` lie in the
annulus `B_{ρ+‖w‖}(x) \ B_{ρ−‖w‖}(x)`, of measure `ωₙ ((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)`. -/
theorem Submission.dorag_ha_ie_shifted_ball_integral_sub_le : ∀ (n : ℕ) (u : Euclid n → ℝ) (x w : Euclid n) (ρ K : ℝ), 0 < n → ‖w‖ ≤ ρ → 0 ≤ K → IntegrableOn u (ball x (ρ + ‖w‖)) → (∀ z ∈ ball x (ρ + ‖w‖), |u z| ≤ K) → |(∫ y in ball (x + w) ρ, u y) - ∫ y in ball x ρ, u y| ≤ K * (volume (ball (0 : Euclid n) 1)).toReal * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := by
  intro n u x w ρ K hn hwρ hK hint hbound
  have hs0 : 0 ≤ ‖w‖ := norm_nonneg w
  -- Step 1: both balls lie in `B_{ρ+‖w‖}(x)`
  have hdist : ∀ z : Euclid n, ‖z - x‖ ≤ ‖z - (x + w)‖ + ‖w‖ := fun z => by
    calc ‖z - x‖ = ‖(z - (x + w)) + w‖ := by congr 1; abel
      _ ≤ ‖z - (x + w)‖ + ‖w‖ := norm_add_le _ _
  have hdist' : ∀ z : Euclid n, ‖z - (x + w)‖ ≤ ‖z - x‖ + ‖w‖ := fun z => by
    calc ‖z - (x + w)‖ = ‖(z - x) + -w‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖-w‖ := norm_add_le _ _
      _ = ‖z - x‖ + ‖w‖ := by rw [norm_neg]
  have h₁ : ball (x + w) ρ ⊆ ball x (ρ + ‖w‖) := by
    intro z hz
    rw [mem_ball_iff_norm] at hz ⊢
    linarith [hdist z]
  have h₀ : ball x ρ ⊆ ball x (ρ + ‖w‖) := ball_subset_ball (by linarith)
  -- Step 2: split each ball along the other
  have e₁ := integral_inter_add_sdiff (μ := volume) (t := ball x ρ) measurableSet_ball
    (hint.mono_set h₁)
  have e₀ := integral_inter_add_sdiff (μ := volume) (t := ball (x + w) ρ) measurableSet_ball
    (hint.mono_set h₀)
  rw [inter_comm] at e₀
  rw [← e₁, ← e₀, add_sub_add_left_eq_sub]
  -- Step 3: bound each piece by `K` times its measure
  have hS₁ : ball (x + w) ρ \ ball x ρ ⊆ ball x (ρ + ‖w‖) := sdiff_subset.trans h₁
  have hS₂ : ball x ρ \ ball (x + w) ρ ⊆ ball x (ρ + ‖w‖) := sdiff_subset.trans h₀
  have hpiece : ∀ S ⊆ ball x (ρ + ‖w‖), |∫ y in S, u y| ≤ K * volume.real S := by
    intro S hS
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := u)
      ((measure_mono hS).trans_lt measure_ball_lt_top) (fun z hz => by
        rw [Real.norm_eq_abs]; exact hbound z (hS hz))
    rwa [Real.norm_eq_abs] at this
  -- Step 4: the two pieces are disjoint and lie in the annulus `B_{ρ+‖w‖}(x) \ B_{ρ−‖w‖}(x)`
  have hdisj : Disjoint (ball (x + w) ρ \ ball x ρ) (ball x ρ \ ball (x + w) ρ) :=
    disjoint_sdiff_sdiff
  have hin : Disjoint ((ball (x + w) ρ \ ball x ρ) ∪ (ball x ρ \ ball (x + w) ρ))
      (ball x (ρ - ‖w‖)) := by
    rw [Set.disjoint_left]
    rintro z (⟨_, hz0⟩ | ⟨_, hz1⟩) hzin
    · exact hz0 (ball_subset_ball (by linarith) hzin)
    · apply hz1
      rw [mem_ball_iff_norm] at hzin ⊢
      linarith [hdist' z]
  have hU : (ball (x + w) ρ \ ball x ρ) ∪ (ball x ρ \ ball (x + w) ρ) ∪ ball x (ρ - ‖w‖) ⊆
      ball x (ρ + ‖w‖) :=
    union_subset (union_subset hS₁ hS₂) (ball_subset_ball (by linarith))
  have hmeas : volume.real (ball (x + w) ρ \ ball x ρ) + volume.real (ball x ρ \ ball (x + w) ρ) +
      volume.real (ball x (ρ - ‖w‖)) ≤ volume.real (ball x (ρ + ‖w‖)) := by
    rw [← measureReal_union hdisj (measurableSet_ball.diff measurableSet_ball)
      (measure_ne_top_of_subset hS₁ measure_ball_lt_top.ne)
      (measure_ne_top_of_subset hS₂ measure_ball_lt_top.ne),
      ← measureReal_union hin measurableSet_ball
      (measure_ne_top_of_subset (union_subset hS₁ hS₂) measure_ball_lt_top.ne)
      measure_ball_lt_top.ne]
    exact measureReal_mono hU measure_ball_lt_top.ne
  -- Step 5: measure of balls, `Lⁿ(B_r(x)) = ωₙ rⁿ` for `r ≥ 0`
  have : Nontrivial (Euclid n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hball : ∀ r : ℝ, 0 ≤ r →
      volume.real (ball x r) = r ^ n * (volume (ball (0 : Euclid n) 1)).toReal := by
    intro r hr
    rw [measureReal_def, Measure.addHaar_ball volume x hr, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n)]
  rw [hball (ρ + ‖w‖) (by linarith), hball (ρ - ‖w‖) (by linarith)] at hmeas
  -- Step 6: conclusion
  calc |(∫ y in ball (x + w) ρ \ ball x ρ, u y) - ∫ y in ball x ρ \ ball (x + w) ρ, u y|
      ≤ |∫ y in ball (x + w) ρ \ ball x ρ, u y| + |∫ y in ball x ρ \ ball (x + w) ρ, u y| :=
        abs_sub _ _
    _ ≤ K * volume.real (ball (x + w) ρ \ ball x ρ) +
        K * volume.real (ball x ρ \ ball (x + w) ρ) := add_le_add (hpiece _ hS₁) (hpiece _ hS₂)
    _ = K * (volume.real (ball (x + w) ρ \ ball x ρ) +
        volume.real (ball x ρ \ ball (x + w) ρ)) := by ring
    _ ≤ K * ((ρ + ‖w‖) ^ n * (volume (ball (0 : Euclid n) 1)).toReal -
        (ρ - ‖w‖) ^ n * (volume (ball (0 : Euclid n) 1)).toReal) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = K * (volume (ball (0 : Euclid n) 1)).toReal * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := by ring

/-- **Interior gradient bound from the ball mean value identity** (Simon Ch. 5, estimates
3.2–3.4, derived by comparing ball means over shifted balls).  Let `ω = Lⁿ(B̆₁(0))`, so
`Lⁿ(B̆_ρ(z)) = ωρⁿ`.  For `‖w‖ ≤ ρ/2` the mean value identity at `x + w` and at `x`, together
with `Submission.dorag_ha_ie_shifted_ball_integral_sub_le`, give
`ρⁿ|u(x + w) − u(x)| ≤ K((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)`, and `abs_pow_sub_pow_le` bounds the right
side by `2‖w‖nK(ρ + η)ⁿ⁻¹` when `‖w‖ ≤ η`.  Hence `‖Du(x)‖ ≤ 2nK(ρ + η)ⁿ⁻¹/ρⁿ` for
`0 < η ≤ ρ/2` (`HasFDerivAt.le_of_lip'`), and letting `η → 0⁺` gives `‖Du(x)‖ ≤ 2nK/ρ`. -/
theorem Submission.dorag_ha_ie_norm_fderiv_le_of_mean_value : ∀ (n : ℕ) (u : Euclid n → ℝ) (x : Euclid n) (ρ K : ℝ), 0 < n → 0 < ρ → DifferentiableAt ℝ u x → ContinuousOn u (closedBall x (3 * ρ / 2)) → (∀ z ∈ closedBall x (3 * ρ / 2), |u z| ≤ K) → (∀ z ∈ closedBall x (ρ / 2), ∫ y in ball z ρ, u y = (volume (ball z ρ)).toReal * u z) → ‖fderiv ℝ u x‖ ≤ 2 * (n : ℝ) * K / ρ := by
  intro n u x ρ K hn hρ hdiff hcont hbound hmv
  -- Step 1: `Lⁿ(B̆_ρ(z)) = ρⁿω` with `ω > 0`, and `K ≥ |u(x)| ≥ 0`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, (volume (ball (0 : Euclid n) 1)).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := by
    rw [← hω_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hvol : ∀ z : Euclid n, (volume (ball z ρ)).toReal = ρ ^ n * ω := by
    intro z
    rw [Measure.addHaar_ball_of_pos volume z hρ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le n), hω_def]
  have hx : x ∈ closedBall x (ρ / 2) := mem_closedBall_self (by positivity)
  have hK : 0 ≤ K := (abs_nonneg _).trans (hbound x (mem_closedBall_self (by positivity)))
  -- Step 2: `ρⁿ|u(x + w) − u(x)| ≤ K((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)` for `‖w‖ ≤ ρ/2`
  have hshift : ∀ w : Euclid n, ‖w‖ ≤ ρ / 2 →
      ρ ^ n * |u (x + w) - u x| ≤ K * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := by
    intro w hw
    have hsub : ball x (ρ + ‖w‖) ⊆ closedBall x (3 * ρ / 2) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    have hint : IntegrableOn u (ball x (ρ + ‖w‖)) :=
      (hcont.integrableOn_compact (isCompact_closedBall x _)).mono_set hsub
    have hcmp := Submission.dorag_ha_ie_shifted_ball_integral_sub_le n u x w ρ K hn
      (by linarith) hK hint fun z hz => hbound z (hsub hz)
    have hxw : x + w ∈ closedBall x (ρ / 2) := by
      rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    have hdiffint : (∫ y in ball (x + w) ρ, u y) - ∫ y in ball x ρ, u y
        = ω * (ρ ^ n * (u (x + w) - u x)) := by
      rw [hmv (x + w) hxw, hmv x hx, hvol, hvol]
      ring
    rw [hdiffint, abs_mul, abs_mul, abs_of_pos hω, abs_of_pos (pow_pos hρ n), hω_def] at hcmp
    refine le_of_mul_le_mul_left ?_ hω
    calc ω * (ρ ^ n * |u (x + w) - u x|) ≤ K * ω * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := hcmp
      _ = ω * (K * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n)) := by ring
  -- Step 3: `(ρ + s)ⁿ − (ρ − s)ⁿ ≤ 2sn(ρ + η)ⁿ⁻¹` for `0 ≤ s ≤ ρ`, `s ≤ η`
  have hpow : ∀ s η : ℝ, 0 ≤ s → s ≤ ρ → s ≤ η →
      (ρ + s) ^ n - (ρ - s) ^ n ≤ 2 * s * n * (ρ + η) ^ (n - 1) := by
    intro s η hs hsρ hsη
    have h := abs_pow_sub_pow_le (ρ + s) (ρ - s) n
    rw [show ρ + s - (ρ - s) = 2 * s by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ + s), abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ - s),
      max_eq_left (by linarith : ρ - s ≤ ρ + s)] at h
    calc (ρ + s) ^ n - (ρ - s) ^ n ≤ |(ρ + s) ^ n - (ρ - s) ^ n| := le_abs_self _
      _ ≤ 2 * s * n * (ρ + s) ^ (n - 1) := h
      _ ≤ 2 * s * n * (ρ + η) ^ (n - 1) := by gcongr
  -- Step 4: `‖Du(x)‖ ≤ C_η := 2nK(ρ + η)ⁿ⁻¹/ρⁿ` for `0 < η ≤ ρ/2`
  have hstep : ∀ η : ℝ, 0 < η → η ≤ ρ / 2 →
      ‖fderiv ℝ u x‖ ≤ 2 * n * K * (ρ + η) ^ (n - 1) / ρ ^ n := by
    intro η hη hηρ
    refine hdiff.hasFDerivAt.le_of_lip' (by positivity) ?_
    filter_upwards [ball_mem_nhds x hη] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h₁ := hshift (y - x) (by linarith)
    rw [add_sub_cancel] at h₁
    have h₂ := hpow ‖y - x‖ η (norm_nonneg _) (by linarith) hy.le
    rw [Real.norm_eq_abs, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hρ n)]
    calc |u y - u x| * ρ ^ n = ρ ^ n * |u y - u x| := mul_comm _ _
      _ ≤ K * ((ρ + ‖y - x‖) ^ n - (ρ - ‖y - x‖) ^ n) := h₁
      _ ≤ K * (2 * ‖y - x‖ * n * (ρ + η) ^ (n - 1)) := mul_le_mul_of_nonneg_left h₂ hK
      _ = 2 * n * K * (ρ + η) ^ (n - 1) * ‖y - x‖ := by ring
  -- Step 5: let `η → 0⁺`; `C_η → 2nKρⁿ⁻¹/ρⁿ = 2nK/ρ`
  have hlim : Tendsto (fun η : ℝ => 2 * n * K * (ρ + η) ^ (n - 1) / ρ ^ n) (𝓝[>] 0)
      (𝓝 (2 * n * K * (ρ + 0) ^ (n - 1) / ρ ^ n)) := by
    have hC : Continuous fun η : ℝ => 2 * n * K * (ρ + η) ^ (n - 1) / ρ ^ n := by fun_prop
    exact (hC.tendsto 0).mono_left nhdsWithin_le_nhds
  have hval : 2 * n * K * (ρ + 0) ^ (n - 1) / ρ ^ n = 2 * n * K / ρ := by
    have hpn : ρ ^ n = ρ * ρ ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [add_zero, hpn, mul_div_mul_right _ _ (pow_ne_zero _ hρ.ne')]
  rw [← hval]
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hρ)] with η hη
  exact hstep η hη.1 hη.2.le
/-- **Integration by parts for a Lipschitz function against a `C²` test function on a ball**
(Step 0 of the harmonic approximation lemma: the integration by parts in Simon Ch. 5, Lemma 3.1,
made explicit for Lipschitz `u` via Rademacher's theorem).  Both integrands vanish off
`tsupport ζ ⊆ B_R`, so the ball integrals are integrals over `ℝⁿ`.  In each direction `v`,
`g = Dζ(·)v` is `C¹` with compact support, hence Lipschitz, and Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` gives `∫ ∂ᵥu · g = ∫ ∂₋ᵥg · u`; by Rademacher's theorem
`∂ᵥu = Du(·)v` a.e., and `∂₋ᵥg = −D²ζ(·)(v, v)`.  Summing over `v = eᵢ` (every term is integrable)
gives the identity. -/
theorem Submission.dorag_haa_lipschitz_ibp : ∀ (n : ℕ) (R : ℝ) (u ζ : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ y (EuclideanSpace.single i (1 : ℝ)) = -∫ y in ball (0 : Euclid n) R, u y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
  intro n R u ζ L hu hζ hcs hsub
  -- both integrands vanish off `tsupport ζ ⊆ B_R`, since `Dζ` and `D²ζ` do
  have hD1 : ∀ y, y ∉ tsupport ζ → fderiv ℝ ζ y = 0 := fun y hy =>
    Function.notMem_support.mp fun h => hy (support_fderiv_subset ℝ h)
  have hD2 : ∀ y, y ∉ tsupport ζ → iteratedFDeriv ℝ 2 ζ y = 0 := fun y hy =>
    Function.notMem_support.mp fun h => hy (support_iteratedFDeriv_subset 2 h)
  have hout : ∀ y, y ∉ ball (0 : Euclid n) R → y ∉ tsupport ζ := fun y hy h => hy (hsub h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hD1 y (hout y hy)],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hD2 y (hout y hy)]]
  -- `Dζ` is `C¹`
  have hζ1 : ContDiff ℝ 1 (fderiv ℝ ζ) := hζ.fderiv_right one_add_one_eq_two.le
  -- integrability of the terms
  have hint1 : ∀ v : Euclid n, Integrable (fun y => fderiv ℝ u y v * fderiv ℝ ζ y v) := by
    intro v
    have hg : Integrable (fun y => fderiv ℝ ζ y v) :=
      (hζ1.continuous.clm_apply continuous_const).integrable_of_hasCompactSupport
        (hcs.fderiv_apply ℝ v)
    refine hg.bdd_mul (c := L * ‖v‖) (measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    calc ‖fderiv ℝ u y v‖ ≤ ‖fderiv ℝ u y‖ * ‖v‖ := (fderiv ℝ u y).le_opNorm v
      _ ≤ L * ‖v‖ := by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hu
  have hint2 : ∀ v : Euclid n, Integrable (fun y => u y * iteratedFDeriv ℝ 2 ζ y ![v, v]) := by
    intro v
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hu.continuous.mul ((hζ.continuous_iteratedFDeriv le_rfl).eval_const _)
    · refine hcs.mono' (Function.support_subset_iff'.mpr fun y hy => ?_)
      simp [hD2 y hy]
  -- the identity in each direction `v`
  have key : ∀ v : Euclid n,
      ∫ y, fderiv ℝ u y v * fderiv ℝ ζ y v = -∫ y, u y * iteratedFDeriv ℝ 2 ζ y ![v, v] := by
    intro v
    have hg1 : ContDiff ℝ 1 (fun y => fderiv ℝ ζ y v) := hζ1.clm_apply contDiff_const
    have hgcs : HasCompactSupport (fun y => fderiv ℝ ζ y v) := hcs.fderiv_apply ℝ v
    obtain ⟨C, hgC⟩ := hg1.lipschitzWith_of_hasCompactSupport hgcs one_ne_zero
    have ibp := hu.integral_lineDeriv_mul_eq hgC hgcs v (μ := volume)
    have lhs : ∫ y, fderiv ℝ u y v * fderiv ℝ ζ y v = ∫ y, lineDeriv ℝ u y v * fderiv ℝ ζ y v := by
      refine integral_congr_ae ?_
      filter_upwards [hu.ae_differentiableAt (μ := volume)] with y hy
      rw [hy.lineDeriv_eq_fderiv]
    have rhs : ∀ y, lineDeriv ℝ (fun y => fderiv ℝ ζ y v) y (-v) * u y =
        -(u y * iteratedFDeriv ℝ 2 ζ y ![v, v]) := by
      intro y
      have hd2 : DifferentiableAt ℝ (fderiv ℝ ζ) y := hζ1.differentiable one_ne_zero y
      rw [(hg1.differentiable one_ne_zero y).lineDeriv_eq_fderiv,
        fderiv_clm_apply hd2 (differentiableAt_const v), iteratedFDeriv_two_apply]
      simp
      ring
    rw [lhs, ibp, ← integral_neg]
    congr 1
    funext y
    exact rhs y
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 _, integral_finsetSum _ fun i _ => hint2 _,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => key _
namespace Submission

/-- Strong `L²(B_R)` convergence `fⱼ → W` gives `∫_{B_R} fⱼ g → ∫_{B_R} W g` for every
`g ∈ L²(B_R)`: by Cauchy–Schwarz (Hölder with `p = q = 2`),
`|∫ fⱼ g − ∫ W g| ≤ ∫ |fⱼ − W| |g| ≤ (∫ (fⱼ − W)²)^{1/2} (∫ g²)^{1/2} → 0`. -/
theorem dorag_haa_l2_pairing_tendsto : ∀ (n : ℕ) (R : ℝ) (f : ℕ → Euclid n → ℝ) (W g : Euclid n → ℝ), (∀ j, MemLp (f j) 2 (volume.restrict (ball (0 : Euclid n) R))) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → MemLp g 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, f j x * g x) atTop (𝓝 (∫ x in ball (0 : Euclid n) R, W x * g x)) := by
  intro n R f W g hf hW hg hlim
  -- Cauchy–Schwarz: `|∫ fⱼ g − ∫ W g| ≤ √(∫ (fⱼ − W)²) · √(∫ g²)`.
  have hbound : ∀ j, ‖(∫ x in ball (0 : Euclid n) R, f j x * g x) -
      ∫ x in ball (0 : Euclid n) R, W x * g x‖ ≤
      √(∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) *
        √(∫ x in ball (0 : Euclid n) R, g x ^ 2) := by
    intro j
    have hd : MemLp (fun x => f j x - W x) (ENNReal.ofReal 2)
        (volume.restrict (ball (0 : Euclid n) R)) := by
      rw [ENNReal.ofReal_ofNat]; exact (hf j).sub hW
    have hg' : MemLp g (ENNReal.ofReal 2) (volume.restrict (ball (0 : Euclid n) R)) := by
      rw [ENNReal.ofReal_ofNat]; exact hg
    -- Products of two `L²` functions are integrable (Hölder `2, 2, 1`).
    have hi₁ : Integrable (fun x => f j x * g x) (volume.restrict (ball (0 : Euclid n) R)) :=
      (hf j).integrable_mul hg
    have hi₂ : Integrable (fun x => W x * g x) (volume.restrict (ball (0 : Euclid n) R)) :=
      hW.integrable_mul hg
    rw [← integral_sub hi₁ hi₂, Real.norm_eq_abs]
    calc |∫ x in ball (0 : Euclid n) R, (f j x * g x - W x * g x)|
        ≤ ∫ x in ball (0 : Euclid n) R, |f j x * g x - W x * g x| := abs_integral_le_integral_abs
      _ = ∫ x in ball (0 : Euclid n) R, ‖f j x - W x‖ * ‖g x‖ := by
          congr 1; funext x; rw [← sub_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (∫ x in ball (0 : Euclid n) R, ‖f j x - W x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫ x in ball (0 : Euclid n) R, ‖g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hd hg'
      _ = _ := by simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow]
  -- The bound tends to `√0 · √(∫ g²) = 0`; squeeze.
  have hsq : Tendsto (fun j => √(∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) *
      √(∫ x in ball (0 : Euclid n) R, g x ^ 2)) atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hlim).mul_const
      (√(∫ x in ball (0 : Euclid n) R, g x ^ 2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun j => norm_nonneg _) hbound hsq

end Submission

/-- **`L²` limits of almost-harmonic Lipschitz functions are weakly harmonic** (step A3 of the
harmonic approximation, Simon Ch. 5, proof of Lemma 3.1, p. 114; chapter-05.txt lines 632–639,
replacing "by the weak convergence of `∇f_{k'}` to `∇w` and by (1)").  Write `B = B̆_R(0)`,
`eᵢ = EuclideanSpace.single i 1` and `Δζ = Σᵢ D²ζ(eᵢ, eᵢ)`.  For `vⱼ = uⱼ − cⱼ`, which is
Lipschitz with `Dvⱼ = Duⱼ`, `dorag_haa_lipschitz_ibp` gives `∫_B vⱼ Δζ = −∫_B Σᵢ Duⱼ eᵢ · Dζ eᵢ`,
so the hypothesis with `G = sup ‖Dζ‖` gives `|∫_B vⱼ Δζ| ≤ δⱼ G → 0`.  As `vⱼ → W` in `L²(B)`,
`dorag_haa_l2_pairing_tendsto` gives `∫_B vⱼ Δζ → ∫_B W Δζ`, which is therefore `0`. -/
theorem Submission.dorag_haa_weakly_harmonic_limit : ∀ (n : ℕ) (R : ℝ) (u : ℕ → Euclid n → ℝ) (c δ : ℕ → ℝ) (W : Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → Tendsto δ atTop (𝓝 0) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → (∀ (j : ℕ) (ζ : Euclid n → ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ (u j) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ j * G) → ∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
  intro n R u c δ W hu hδ hW hconv hweak ζ hζ hζc hζB
  -- Step 1: `Δζ` is continuous, `ζ` being `C²`
  have hΔ : Continuous fun y => ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] :=
    continuous_finsetSum _ fun i _ =>
      (hζ.continuous_iteratedFDeriv (m := 2) le_rfl).eval_const _
  -- Step 2: continuous functions are bounded on `B ⊆ closedBall 0 R`, hence in `L²(B)`
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_ne_top
  have hL2 : ∀ f : Euclid n → ℝ, Continuous f →
      MemLp f 2 (volume.restrict (ball (0 : Euclid n) R)) := by
    intro f hf
    obtain ⟨K, hK⟩ :=
      (isCompact_closedBall (0 : Euclid n) R).exists_bound_of_continuousOn hf.continuousOn
    exact MemLp.of_bound hf.aestronglyMeasurable K
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hK x (ball_subset_closedBall hx))
  -- Step 3: `‖Dζ‖ ≤ G`, `Dζ` being continuous with compact support
  obtain ⟨G, hG⟩ := (hζc.fderiv ℝ).exists_bound_of_continuous (hζ.continuous_fderiv two_ne_zero)
  -- Step 4: integration by parts for `vⱼ = uⱼ − cⱼ` (`Dvⱼ = Duⱼ`) and the hypothesis give
  -- `|∫_B vⱼ Δζ| = |∫_B Σᵢ Duⱼ eᵢ · Dζ eᵢ| ≤ δⱼ G`
  have hbound : ∀ j, |∫ y in ball (0 : Euclid n) R, (u j y - c j) * ∑ i : Fin n,
      iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]|
      ≤ δ j * G := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    have hibp := Submission.dorag_haa_lipschitz_ibp n R (fun y => u j y - c j) ζ (L + 0)
      (hL.sub (LipschitzWith.const (c j))) hζ hζc hζB
    simp only [fderiv_sub_const] at hibp
    have h := hweak j ζ (hζ.of_le one_le_two) hζc hζB G hG
    rwa [hibp, abs_neg] at h
  -- Step 5: hence `∫_B vⱼ Δζ → 0`, as `δⱼ G → 0`
  have h0 : Tendsto (fun j => ∫ y in ball (0 : Euclid n) R, (u j y - c j) * ∑ i : Fin n,
      iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)])
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans (hbound j)) ?_
    simpa using hδ.mul_const G
  -- Step 6: `vⱼ → W` in `L²(B)` and `Δζ ∈ L²(B)`, so `∫_B vⱼ Δζ → ∫_B W Δζ`
  have hlim := Submission.dorag_haa_l2_pairing_tendsto n R (fun j y => u j y - c j) W _
    (fun j => hL2 _ (by
      obtain ⟨L, hL⟩ := hu j
      exact hL.continuous.sub continuous_const))
    hW (hL2 _ hΔ) hconv
  -- Step 7: limits in `ℝ` are unique
  exact tendsto_nhds_unique hlim h0
/-- **Change of variables `x = r • y` between `B₁(0)` and `B_r(0)`** (step B1 of the harmonic
approximation lemma, with `r` for `R₀`).  For `r > 0` and an arbitrary `F : ℝⁿ → ℝ`,
`y ↦ F (r • y)` is integrable on `B₁(0)` iff `F` is integrable on `B_r(0)`, and
`∫_{B₁(0)} F (r • y) dy = r⁻ⁿ ∫_{B_r(0)} F`.  The identity is Mathlib's Haar-measure change of
variables with `r • B₁(0) = B_r(0)` and `finrank ℝ ℝⁿ = n`; it needs no integrability, a
non-integrable function having integral `0` on both sides.  Integrability passes to the indicators
of the two balls, which correspond under `y ↦ r • y`. -/
theorem Submission.dorag_haa_ball_rescale_integral : ∀ (n : ℕ) (F : Euclid n → ℝ) (r : ℝ), 0 < r → (IntegrableOn (fun y => F (r • y)) (ball (0 : Euclid n) 1) ↔ IntegrableOn F (ball (0 : Euclid n) r)) ∧ ∫ y in ball (0 : Euclid n) 1, F (r • y) = (r ^ n)⁻¹ * ∫ x in ball (0 : Euclid n) r, F x := by
  intro n F r hr
  -- `r • y ∈ B_r ↔ y ∈ B_1`, since `‖r • y‖ = r ‖y‖`
  have hmem : ∀ y : Euclid n, r • y ∈ ball (0 : Euclid n) r ↔ y ∈ ball (0 : Euclid n) 1 := by
    intro y
    rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_iff_lt_one_right hr
  refine ⟨?_, ?_⟩
  · -- integrability: pass to indicators and use `integrable_comp_smul_iff`
    have hind : (ball (0 : Euclid n) 1).indicator (fun y => F (r • y)) =
        fun y => (ball (0 : Euclid n) r).indicator F (r • y) := by
      ext y
      by_cases hy : y ∈ ball (0 : Euclid n) 1
      · rw [indicator_of_mem hy, indicator_of_mem ((hmem y).2 hy)]
      · rw [indicator_of_notMem hy, indicator_of_notMem (mt (hmem y).1 hy)]
    rw [← integrable_indicator_iff measurableSet_ball, ← integrable_indicator_iff measurableSet_ball,
      hind]
    exact integrable_comp_smul_iff volume _ hr.ne'
  · -- the change of variables `x = r • y`, with `r • B_1 = B_r`
    rw [Measure.setIntegral_comp_smul_of_pos volume F (ball 0 1) hr, smul_unitBall_of_pos hr,
      finrank_euclideanSpace_fin, smul_eq_mul]

/-- Rescaling to the unit ball in the harmonic approximation lemma (Simon Ch. 5, Lemma 3.1, steps
B1–B2 of the scaling): if `w` is `Lw`-Lipschitz, `∫_{B_{R₀}} ‖Dw‖² ≤ R₀ⁿ` and
`|∫_{B_{R₀}} Dw · Dζ| ≤ δ R₀ⁿ G` for `ζ ∈ C¹_c(B_{R₀})` with `‖Dζ‖ ≤ G`, then
`w₁(y) = R₀⁻¹ w(R₀ y)` is `Lw`-Lipschitz, `∫_{B_1} ‖Dw₁‖² ≤ 1` and `|∫_{B_1} Dw₁ · Dζ₁| ≤ δ G` for
`ζ₁ ∈ C¹_c(B_1)` with `‖Dζ₁‖ ≤ G`.  `D(y ↦ c⁻¹ f(c y))(x) = Df(c x)` for `c ≠ 0`, with no
differentiability hypothesis; `ζ₁` is tested through `ζ(x) = R₀ ζ₁(R₀⁻¹ x)`, for which
`Dζ(x) = Dζ₁(R₀⁻¹ x)`, and `dorag_haa_ball_rescale_integral` turns each integral over `B_1` into
`R₀⁻ⁿ` times the integral over `B_{R₀}`. -/
theorem Submission.dorag_haa_rescale_hypotheses : ∀ (n : ℕ) (δ R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * R₀ ^ n * G) → LipschitzWith Lw (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) ∧ ∫ v in ball (0 : Euclid n) 1, ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2 ≤ 1 ∧ ∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) 1 → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) 1, ∑ i : Fin n, fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * G := by
  intro n δ R₀ w Lw hR₀ hw hE hW
  have hR₀ne : R₀ ≠ 0 := hR₀.ne'
  have hRn : 0 < R₀ ^ n := pow_pos hR₀ n
  -- Step 0: `D(y ↦ c⁻¹ f(c y))(x) = Df(c x)` for `c ≠ 0`, with no differentiability hypothesis
  have hscale : ∀ (f : Euclid n → ℝ) (c : ℝ), c ≠ 0 → ∀ x : Euclid n,
      fderiv ℝ (fun y : Euclid n => c⁻¹ * f (c • y)) x = fderiv ℝ f (c • x) := by
    intro f c hc x
    have h1 : (fun y : Euclid n => c⁻¹ * f (c • y)) = c⁻¹ • fun y : Euclid n => f (c • y) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, inv_smul_smul₀ hc]
  -- Step 1 (a): `w₁` is `Lw`-Lipschitz
  have ha : LipschitzWith Lw (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := hw.dist_le_mul (R₀ • x) (R₀ • y)
    rw [dist_smul₀, Real.norm_of_nonneg hR₀.le] at h
    calc dist (R₀⁻¹ * w (R₀ • x)) (R₀⁻¹ * w (R₀ • y))
        = R₀⁻¹ * dist (w (R₀ • x)) (w (R₀ • y)) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hR₀)]
      _ ≤ R₀⁻¹ * (Lw * (R₀ * dist x y)) := by gcongr
      _ = Lw * dist x y := by field_simp
  -- Step 2 (b): `∫_{B_1} ‖Dw₁‖² = R₀⁻ⁿ ∫_{B_{R₀}} ‖Dw‖² ≤ 1`
  have hb : ∫ v in ball (0 : Euclid n) 1,
      ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2 ≤ 1 := by
    have e : (fun v => ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2) =
        fun v => ‖fderiv ℝ w (R₀ • v)‖ ^ 2 := funext fun v => by rw [hscale w R₀ hR₀ne v]
    rw [e, (Submission.dorag_haa_ball_rescale_integral n (fun x => ‖fderiv ℝ w x‖ ^ 2) R₀ hR₀).2,
      inv_mul_le_iff₀ hRn, mul_one]
    exact hE
  refine ⟨ha, hb, ?_⟩
  -- Step 3 (c): test with `ζ(x) = R₀ ζ₁(R₀⁻¹ x)` on `B_{R₀}`
  intro ζ₁ hζ₁ hcs₁ hts₁ G hG
  set ζ : Euclid n → ℝ := fun x => R₀ * ζ₁ (R₀⁻¹ • x)
  -- 3a: `ζ` is `C¹`
  have hζC : ContDiff ℝ 1 ζ := contDiff_const.mul (hζ₁.comp (contDiff_const_smul R₀⁻¹))
  -- 3b: `ζ` has compact support
  have hζcs : HasCompactSupport ζ := (hcs₁.comp_smul (inv_ne_zero hR₀ne)).mul_left
  -- 3c: `tsupport ζ ⊆ B_{R₀}`
  have hζts : tsupport ζ ⊆ ball (0 : Euclid n) R₀ := by
    intro x hx
    have hx1 : x ∈ tsupport fun x : Euclid n => ζ₁ (R₀⁻¹ • x) := tsupport_mul_subset_right hx
    have hx2 : R₀⁻¹ • x ∈ tsupport ζ₁ :=
      tsupport_comp_subset_preimage ζ₁ (continuous_const_smul R₀⁻¹) hx1
    have hx3 := hts₁ hx2
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR₀.le),
      inv_mul_lt_iff₀ hR₀, mul_one] at hx3
    exact mem_ball_zero_iff.2 hx3
  -- 3d: `Dζ(x) = Dζ₁(R₀⁻¹ x)`, so `‖Dζ‖ ≤ G`
  have hDζ : ∀ x, fderiv ℝ ζ x = fderiv ℝ ζ₁ (R₀⁻¹ • x) := by
    intro x
    have h := hscale ζ₁ R₀⁻¹ (inv_ne_zero hR₀ne) x
    rwa [inv_inv] at h
  have hGζ : ∀ v, ‖fderiv ℝ ζ v‖ ≤ G := fun v => by rw [hDζ]; exact hG _
  -- 3e: the hypothesis applies to `(ζ, G)`
  have hbound := hW ζ hζC hζcs hζts G hGζ
  -- 3f: `F(R₀ v) = Σᵢ Dw₁(v)eᵢ · Dζ₁(v)eᵢ` for `F = Σᵢ Dw eᵢ · Dζ eᵢ`; rescale `∫_{B_1}`
  have hF : (fun v : Euclid n => ∑ i : Fin n,
      fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ₁ v (EuclideanSpace.single i (1 : ℝ))) =
      fun v => ∑ i : Fin n, fderiv ℝ w (R₀ • v) (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ (R₀ • v) (EuclideanSpace.single i (1 : ℝ)) := by
    funext v
    simp only [hscale w R₀ hR₀ne v, hDζ, inv_smul_smul₀ hR₀ne]
  rw [hF, (Submission.dorag_haa_ball_rescale_integral n (fun x => ∑ i : Fin n,
      fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) R₀ hR₀).2,
    abs_mul, abs_of_pos (inv_pos.2 hRn)]
  -- 3g: `R₀⁻ⁿ |∫_{B_{R₀}} F| ≤ R₀⁻ⁿ δ R₀ⁿ G = δ G`
  calc (R₀ ^ n)⁻¹ * |∫ x in ball (0 : Euclid n) R₀, ∑ i : Fin n,
        fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
      ≤ (R₀ ^ n)⁻¹ * (δ * R₀ ^ n * G) := by gcongr
    _ = δ * G := by field_simp
/-- **Rescaling a unit-scale harmonic approximant to scale `R₀`** (step B3 of the harmonic
approximation lemma).  Let `h₁` be smooth and harmonic on `B₁(0)`, with `∫_{B₁} |Dh₁|² ≤ 1` and
`∫_{B₁} (h₁ − w₁)² ≤ ε` for `w₁(y) = R₀⁻¹ w(R₀ y)`.  Then `h(x) = R₀ h₁(R₀⁻¹ x)` is smooth and
harmonic on `B_{R₀}(0)`, with `∫_{B_{R₀}} |Dh|² ≤ R₀ⁿ` and `∫_{B_{R₀}} (h − w)² ≤ ε R₀ⁿ⁺²`.
Since `x ↦ R₀⁻¹ x` is a linear isomorphism mapping `B_{R₀}(0)` into `B₁(0)`, the identities
`Dh(x) = Dh₁(R₀⁻¹ x)` and `D²h(y) = R₀⁻¹ D²h₁(R₀⁻¹ y)` hold at every point.  Both integrals
transform by the change of variables `x = R₀ y`, under which `|Dh|²(R₀ y) = |Dh₁|²(y)` and
`(h − w)²(R₀ y) = R₀² (h₁ − w₁)²(y)`. -/
theorem Submission.dorag_haa_rescale_conclusion : ∀ (n : ℕ) (ε R₀ : ℝ) (w h₁ : Euclid n → ℝ), 0 < R₀ → (∀ m : ℕ, ContDiffOn ℝ m h₁ (ball (0 : Euclid n) 1)) → (∀ y ∈ ball (0 : Euclid n) 1, ∑ i : Fin n, iteratedFDeriv ℝ 2 h₁ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun y => ‖fderiv ℝ h₁ y‖ ^ 2) (ball (0 : Euclid n) 1) → ∫ y in ball (0 : Euclid n) 1, ‖fderiv ℝ h₁ y‖ ^ 2 ≤ 1 → IntegrableOn (fun y => (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2) (ball (0 : Euclid n) 1) → ∫ y in ball (0 : Euclid n) 1, (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2 ≤ ε → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R₀)) ∧ (∀ y ∈ ball (0 : Euclid n) R₀, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2 ≤ R₀ ^ n ∧ IntegrableOn (fun y => (h y - w y) ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2 ≤ ε * R₀ ^ (n + 2) := by
  intro n ε R₀ w h₁ hR₀ hsmooth hlap hint₁ hle₁ hint₂ hle₂
  have hR₀ne : R₀ ≠ 0 := hR₀.ne'
  have hR₀n : 0 < R₀ ^ n := pow_pos hR₀ n
  -- the rescaled function `h(x) = R₀ h₁(R₀⁻¹ x)`
  obtain ⟨h, hh⟩ : ∃ h : Euclid n → ℝ, ∀ x, h x = R₀ * h₁ (R₀⁻¹ • x) := ⟨_, fun _ => rfl⟩
  -- step 0: `x ↦ R₀⁻¹ x` maps `B_{R₀}(0)` into `B₁(0)`
  have hmaps : MapsTo (fun x : Euclid n => R₀⁻¹ • x) (ball (0 : Euclid n) R₀)
      (ball (0 : Euclid n) 1) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    show R₀⁻¹ • x ∈ ball (0 : Euclid n) 1
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR₀.le),
      inv_mul_lt_iff₀ hR₀, mul_one]
    exact hx
  -- step 2: `Dh(x) = R₀ R₀⁻¹ Dh₁(R₀⁻¹ x) = Dh₁(R₀⁻¹ x)` at every `x`
  have hDh : fderiv ℝ h = fun x => fderiv ℝ h₁ (R₀⁻¹ • x) := by
    have hfun : h = R₀ • fun x => h₁ (R₀⁻¹ • x) := funext hh
    funext x
    rw [hfun, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul,
      mul_inv_cancel₀ hR₀ne, one_smul]
  -- step 3: `D²h(y)(a, b) = R₀⁻¹ D²h₁(R₀⁻¹ y)(a, b)` at every `y`
  have hD2h : ∀ y a b : Euclid n, iteratedFDeriv ℝ 2 h y ![a, b] =
      R₀⁻¹ * iteratedFDeriv ℝ 2 h₁ (R₀⁻¹ • y) ![a, b] := by
    intro y a b
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hDh, fderiv_comp_smul]
    rfl
  -- steps 4–5: the change of variables `x = R₀ y`, with `|Dh|²(R₀ y) = |Dh₁|²(y)` and
  -- `(h − w)²(R₀ y) = R₀² (h₁ − w₁)²(y)`
  have hF₁ : ∀ y : Euclid n, ‖fderiv ℝ h (R₀ • y)‖ ^ 2 = ‖fderiv ℝ h₁ y‖ ^ 2 := by
    intro y
    simp only [hDh, inv_smul_smul₀ hR₀ne]
  have hF₂ : ∀ y : Euclid n,
      (h (R₀ • y) - w (R₀ • y)) ^ 2 = R₀ ^ 2 * (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2 := by
    intro y
    rw [hh, inv_smul_smul₀ hR₀ne, ← mul_pow, mul_sub, mul_inv_cancel_left₀ hR₀ne]
  obtain ⟨hiff₁, heq₁⟩ :=
    Submission.dorag_haa_ball_rescale_integral n (fun x => ‖fderiv ℝ h x‖ ^ 2) R₀ hR₀
  obtain ⟨hiff₂, heq₂⟩ :=
    Submission.dorag_haa_ball_rescale_integral n (fun x => (h x - w x) ^ 2) R₀ hR₀
  simp only [hF₁] at hiff₁ heq₁
  simp only [hF₂, integral_const_mul] at hiff₂ heq₂
  refine ⟨h, fun m => ?_, fun y hy => ?_, hiff₁.1 hint₁, ?_, hiff₂.1 (hint₂.const_mul _), ?_⟩
  · -- step 1: `h = R₀ · (h₁ ∘ R₀⁻¹ ·)` is `Cᵐ` on `B_{R₀}(0)`
    exact (contDiffOn_const.mul ((hsmooth m).comp (contDiff_const_smul R₀⁻¹).contDiffOn
      hmaps)).congr fun x _ => hh x
  · -- step 3: `Δh(y) = R₀⁻¹ Δh₁(R₀⁻¹ y) = 0`, as `R₀⁻¹ y ∈ B₁(0)`
    simp_rw [hD2h]
    rw [← Finset.mul_sum, hlap (R₀⁻¹ • y) (hmaps hy), mul_zero]
  · -- step 4: `∫_{B_{R₀}} |Dh|² = R₀ⁿ ∫_{B₁} |Dh₁|² ≤ R₀ⁿ`
    rw [← mul_inv_cancel_left₀ hR₀n.ne' (∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2),
      ← heq₁]
    exact (mul_le_mul_of_nonneg_left hle₁ hR₀n.le).trans_eq (mul_one _)
  · -- step 5: `∫_{B_{R₀}} (h − w)² = R₀ⁿ R₀² ∫_{B₁} (h₁ − w₁)² ≤ ε R₀ⁿ⁺²`
    rw [← mul_inv_cancel_left₀ hR₀n.ne' (∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2),
      ← heq₂, pow_add, mul_comm ε, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hle₂ (mul_pos hR₀n (pow_pos hR₀ 2)).le
/-- **Order-2 Taylor bound along a segment** (Simon Ch. 5, 3.4, p. 115: "an order 2 Taylor series
expansion for `u`").  If `h` is `C²` on `B_R(0)`, `‖v‖ < R` and `|D²h(τv)(v, v)| ≤ S` for
`τ ∈ [0, 1]`, then `|h(v) − h(0) − Dh(0)v| ≤ S/2`: with `φ(τ) = h(τv)` and `φ₁(τ) = Dh(τv)v`, the
mean value inequality gives `|φ₁(τ) − φ₁(0)| ≤ Sτ`, and comparing `ψ(τ) = φ(τ) − φ(0) − τφ₁(0)`
with `Sτ²/2` gives `|ψ(1)| ≤ S/2`. -/
theorem Submission.dorag_ha_ie_taylor_two_le : ∀ (n : ℕ) (h : Euclid n → ℝ) (R S : ℝ) (v : Euclid n), ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) → ‖v‖ < R → (∀ τ ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 2 h (τ • v) ![v, v]| ≤ S) → |h v - h 0 - fderiv ℝ h 0 v| ≤ S / 2 := by
  intro n h R S v hh hv hS
  -- Step 1: the segment `τ ↦ τ • v`, `τ ∈ [0, 1]`, lies in the open ball
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, τ • v ∈ ball (0 : Euclid n) R := by
    intro τ hτ
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) hτ.2).trans_lt hv
  -- Step 2: `h` and `Dh` are differentiable on the open ball
  have hD1 : ∀ p ∈ ball (0 : Euclid n) R, HasFDerivAt h (fderiv ℝ h p) p := fun p hp =>
    ((hh.differentiableOn two_ne_zero).differentiableAt (isOpen_ball.mem_nhds hp)).hasFDerivAt
  have hD2 : ∀ p ∈ ball (0 : Euclid n) R,
      HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) p) p := fun p hp =>
    (((hh.fderiv_of_isOpen isOpen_ball (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
      one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hp)).hasFDerivAt
  -- Step 3: `φ τ = h (τ • v)` has derivative `φ₁ τ = Dh (τ • v) v`, and `φ₁` has derivative
  -- `D²h (τ • v) (v, v)`
  have hline : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => t • v) v τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const v
  have hφ : ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => h (t • v)) (fderiv ℝ h (τ • v) v) τ := fun τ hτ =>
    (hD1 _ (hmem τ hτ)).comp_hasDerivAt τ (hline τ)
  have hφ₁ : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => fderiv ℝ h (t • v) v)
      (iteratedFDeriv ℝ 2 h (τ • v) ![v, v]) τ := fun τ hτ => by
    have h1 : HasDerivAt (fderiv ℝ h ∘ fun t : ℝ => t • v)
        (fderiv ℝ (fderiv ℝ h) (τ • v) v) τ :=
      (hD2 _ (hmem τ hτ)).comp_hasDerivAt τ (hline τ)
    rw [iteratedFDeriv_two_apply]
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt τ h1
  -- Step 4: mean value inequality, `|φ₁ τ - φ₁ 0| ≤ S τ` on `[0, 1]`
  have hmvt : ∀ τ ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ h (τ • v) v - fderiv ℝ h 0 v‖ ≤ S * τ := by
    have := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun τ hτ => (hφ₁ τ hτ).hasDerivWithinAt) (fun τ hτ => hS τ (Ico_subset_Icc_self hτ))
    simpa using this
  -- Step 5: compare `ψ τ = φ τ - φ 0 - τ φ₁ 0` with `S τ² / 2`
  have hψ : ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => h (t • v) - h 0 - t * fderiv ℝ h 0 v)
        (fderiv ℝ h (τ • v) v - fderiv ℝ h 0 v) τ := fun τ hτ => by
    simpa using
      ((hφ τ hτ).sub_const (h 0)).fun_sub ((hasDerivAt_id τ).mul_const (fderiv ℝ h 0 v))
  have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => S * t ^ 2 / 2) (S * x) x := fun x => by
    convert ((hasDerivAt_pow 2 x).const_mul S).div_const 2 using 1
    ring
  have hcmp := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun τ hτ => (hψ τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hψ τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (by simp) hB (fun τ hτ => hmvt τ (Ico_subset_Icc_self hτ))
    (right_mem_Icc.2 zero_le_one)
  -- Step 6: at `τ = 1`, `ψ 1 = h v - h 0 - Dh 0 v`
  simpa using hcmp
/-- **Radial mollifier** (step 0 of the Weyl lemma used in Simon Ch. 5, proof of Lemma 3.1; cf. the
standard mollifier of Evans, *PDE*, App. C.5).  With `θ = Real.smoothTransition`,
`k(y) = θ(1 − ‖y‖²)` is continuous, nonnegative, vanishes off `B̄₁(0)` and has `k(0) = 1`, so
`c = ∫ k > 0`.  Then `C = c⁻¹` and `g ε t = θ(1 − t/ε²)/(c εⁿ)` work: `g ε` is continuous, vanishes
for `t ≥ ε²`, satisfies `0 ≤ g ε t ≤ C/εⁿ`, `y ↦ g ε (‖y‖²)` is `C^∞`, and the substitution
`y = εu` gives `∫ θ(1 − ‖y‖²/ε²) dy = εⁿ c`, so `∫ g ε (‖y‖²) dy = 1`. -/
theorem Submission.dorag_ha_weyl_radial_mollifier : ∀ n : ℕ, 0 < n → ∃ C : ℝ, ∃ g : ℝ → ℝ → ℝ, ∀ ε : ℝ, 0 < ε → Continuous (g ε) ∧ (∀ t : ℝ, ε ^ 2 ≤ t → g ε t = 0) ∧ (∀ t : ℝ, |g ε t| ≤ C / ε ^ n) ∧ (∀ m : ℕ, ContDiff ℝ m (fun y : Euclid n => g ε (‖y‖ ^ 2))) ∧ ∫ y : Euclid n, g ε (‖y‖ ^ 2) = 1 := by
  intro n _hn
  -- the unscaled bump `k y = θ (1 - ‖y‖²)`, `θ = Real.smoothTransition`
  obtain ⟨k, hk⟩ : ∃ k : Euclid n → ℝ, ∀ y, k y = Real.smoothTransition (1 - ‖y‖ ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hk_cont : Continuous k := by
    rw [show k = fun y => Real.smoothTransition (1 - ‖y‖ ^ 2) from funext hk]
    exact Real.smoothTransition.continuous.comp (continuous_const.sub (continuous_norm.pow 2))
  have hk_supp : HasCompactSupport k := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun y hy => ?_
    have h1 : 1 < ‖y‖ := by simpa using hy
    rw [hk]
    exact Real.smoothTransition.zero_of_nonpos (by nlinarith)
  have hk_nonneg : 0 ≤ k := fun y => by rw [hk]; exact Real.smoothTransition.nonneg _
  have hk0 : k 0 ≠ 0 := by rw [hk]; simp
  have hcpos : 0 < ∫ y, k y :=
    hk_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hk_supp hk_nonneg hk0
  -- change of variables `y = ε u`
  have hscale : ∀ ε : ℝ, 0 < ε →
      ∫ y : Euclid n, Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2) = ε ^ n * ∫ y, k y := by
    intro ε hε
    have h := Measure.integral_comp_inv_smul_of_nonneg volume k hε.le
    rw [finrank_euclideanSpace_fin, smul_eq_mul] at h
    rw [← h]
    congr 1
    ext y
    rw [hk, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, mul_pow, inv_pow, inv_mul_eq_div]
  generalize ∫ y, k y = c at hcpos hscale
  refine ⟨c⁻¹, fun ε t => Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n), fun ε hε => ?_⟩
  have hεn : 0 < ε ^ n := pow_pos hε n
  have hden : 0 < c * ε ^ n := mul_pos hcpos hεn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a) continuity
    exact (Real.smoothTransition.continuous.comp
      (continuous_const.sub (continuous_id.div_const _))).div_const _
  · -- (b) vanishing for `t ≥ ε²`
    intro t ht
    have h1 : 1 ≤ t / ε ^ 2 := (one_le_div (pow_pos hε 2)).mpr ht
    show Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n) = 0
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]
  · -- (c) sup bound
    intro t
    show |Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n)| ≤ c⁻¹ / ε ^ n
    rw [abs_of_nonneg (div_nonneg (Real.smoothTransition.nonneg _) hden.le)]
    calc Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n) ≤ 1 / (c * ε ^ n) :=
          div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) hden.le
      _ = c⁻¹ / ε ^ n := by rw [one_div, mul_inv, div_eq_mul_inv]
  · -- (d) smoothness
    intro m
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Euclid n =>
        Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2) / (c * ε ^ n) :=
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))).div_const _
    exact contDiff_infty.mp h m
  · -- (e) normalization
    show ∫ y : Euclid n, Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2) / (c * ε ^ n) = 1
    rw [integral_div, hscale ε hε, mul_comm]
    exact div_self hden.ne'
namespace Submission

/-- Weyl's lemma, convolution step: for locally integrable `f` and `φ` smooth with compact
support, `F(x) = ∫ f(y) φ(x − y) dy` is `C^m` for every `m` and `ΔF(x) = ∫ f(y) Δφ(x − y) dy`,
`Δψ(z) = Σᵢ D²ψ(z)(eᵢ, eᵢ)` (Evans, PDE, App. C, Thm 7(i)).  `F = f ⋆[L] φ` for multiplication
`L`; differentiating under the integral twice gives `D(DF) = f ⋆ D²φ`, and evaluation at
`(v, w)` commutes with the integral (`convolution_precompR_apply`). -/
theorem dorag_ha_weyl_conv_laplacian : ∀ (n : ℕ) (f φ : Euclid n → ℝ), LocallyIntegrable f → (∀ m : ℕ, ContDiff ℝ m φ) → HasCompactSupport φ → (∀ m : ℕ, ContDiff ℝ m (fun x => ∫ y, f y * φ (x - y))) ∧ ∀ x : Euclid n, ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun x => ∫ y, f y * φ (x - y)) x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = ∫ y, f y * ∑ i : Fin n, iteratedFDeriv ℝ 2 φ (x - y) ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
  intro n f φ hf hφ hφc
  -- `F = f ⋆[L] φ` for the multiplication bilinear map `L a b = a * b`.
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ with hL
  have hF : (fun x => ∫ y, f y * φ (x - y)) = convolution f φ L volume := by
    funext x
    rw [hL, convolution_mul]
  have hφ1 : ContDiff ℝ 1 φ := by exact_mod_cast hφ 1
  have hφ2 : ContDiff ℝ 2 φ := by exact_mod_cast hφ 2
  have hdφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right one_add_one_eq_two.le
  refine ⟨fun m => ?_, fun x => ?_⟩
  · rw [hF]
    exact hφc.contDiff_convolution_right L hf (hφ m)
  -- `DF = f ⋆[L.precompR] Dφ` and `D(DF)(x) v w = ∫ f(y) D²φ(x − y) v w dy`.
  have hD : fderiv ℝ (convolution f φ L volume) =
      convolution f (fderiv ℝ φ) (L.precompR (Euclid n)) volume := by
    ext1 x₀
    exact (hφc.hasFDerivAt_convolution_right L hf hφ1 x₀).fderiv
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ φ)) := hdφ.continuous_fderiv one_ne_zero
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ φ)) := (hφc.fderiv ℝ).fderiv ℝ
  have hD2 : ∀ v w : Euclid n, fderiv ℝ (fderiv ℝ (convolution f φ L volume)) x v w =
      ∫ y, f y * fderiv ℝ (fderiv ℝ φ) (x - y) v w := by
    intro v w
    have hc3 : Continuous fun a => fderiv ℝ (fderiv ℝ φ) a v := hc2.clm_apply continuous_const
    have hs3 : HasCompactSupport fun a => fderiv ℝ (fderiv ℝ φ) a v :=
      hs2.comp_left (g := fun A : Euclid n →L[ℝ] Euclid n →L[ℝ] ℝ => A v) rfl
    rw [hD, ((hφc.fderiv ℝ).hasFDerivAt_convolution_right (L.precompR (Euclid n)) hf hdφ x).fderiv,
      convolution_precompR_apply (L.precompR (Euclid n)) hf hs2 hc2 x v,
      convolution_precompR_apply L hf hs3 hc3 x w, hL, convolution_mul]
  -- Each integrand `f(y) D²φ(x − y) v w` is integrable, so the sum over `i` commutes with `∫`.
  have hint : ∀ v w : Euclid n, Integrable fun y => f y * fderiv ℝ (fderiv ℝ φ) (x - y) v w := by
    intro v w
    have hc4 : Continuous fun a => fderiv ℝ (fderiv ℝ φ) a v w :=
      (hc2.clm_apply continuous_const).clm_apply continuous_const
    have hs4 : HasCompactSupport fun a => fderiv ℝ (fderiv ℝ φ) a v w :=
      hs2.comp_left (g := fun A : Euclid n →L[ℝ] Euclid n →L[ℝ] ℝ => A v w) rfl
    exact hs4.convolutionExists_right L hf hc4 x
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hF]
  simp_rw [hD2, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint _ _]
/-- Weyl's lemma, mollification step: if `W ∈ L¹(B)`, `B = B_R(0)`, is weakly harmonic in `B`
and `φ` is smooth and vanishes for `‖y‖ ≥ ε`, then `F = (1_B W) ⋆ φ` is `C^m` for every `m` and
`ΔF = 0` on `B_{R−ε}(0)`.  By `dorag_ha_weyl_conv_laplacian`, `ΔF(x) = ∫ (1_B W)(y) Δφ(x − y) dy`;
for `‖x‖ < R − ε` the test function `ζ(y) = φ(x − y)` has `spt ζ ⊆ B̄_ε(x) ⊆ B` and
`Δζ(y) = Δφ(x − y)`, so this is `∫_B W Δζ = 0`. -/
theorem dorag_ha_weyl_mollify_harmonic : ∀ (n : ℕ) (R ε : ℝ) (W φ : Euclid n → ℝ), 0 < ε → IntegrableOn W (ball (0 : Euclid n) R) → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ m : ℕ, ContDiff ℝ m φ) → (∀ y : Euclid n, ε ≤ ‖y‖ → φ y = 0) → (∀ m : ℕ, ContDiff ℝ m (fun x => ∫ y, (ball (0 : Euclid n) R).indicator W y * φ (x - y))) ∧ ∀ x ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun x => ∫ y, (ball (0 : Euclid n) R).indicator W y * φ (x - y)) x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
  intro n R ε W φ hε hW hharm hφ hφ0
  -- `1_B W` is integrable, and `φ` vanishes off the compact ball `B̄_ε(0)`.
  have hWB : Integrable ((ball (0 : Euclid n) R).indicator W) :=
    hW.integrable_indicator measurableSet_ball
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) ε) fun y hy =>
      hφ0 y (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)
  obtain ⟨hsmooth, hlap⟩ := Submission.dorag_ha_weyl_conv_laplacian n
    ((ball (0 : Euclid n) R).indicator W) φ hWB.locallyIntegrable hφ hφc
  refine ⟨hsmooth, fun x hx => ?_⟩
  rw [hlap x]
  -- The test function `ζ(y) = φ(x − y)`, supported in `B̄_ε(x) ⊆ B`.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid n → ℝ, ζ = fun y => φ (x - y) := ⟨_, rfl⟩
  have hζ2 : ContDiff ℝ 2 ζ := by
    rw [hζ]
    exact (hφ 2).comp (contDiff_const.sub contDiff_id)
  have hζspt : tsupport ζ ⊆ closedBall x ε := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra h
    exact hy (by rw [hζ]; exact hφ0 _ (not_le.1 h).le)
  have hball : closedBall x ε ⊆ ball (0 : Euclid n) R := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle y x 0]
  -- `D²ζ(y)(v, v) = D²φ(x − y)(v, v)`: write `ζ = φ(x + ·) ∘ (−id)`.
  have hD2 : ∀ y v : Euclid n,
      iteratedFDeriv ℝ 2 ζ y ![v, v] = iteratedFDeriv ℝ 2 φ (x - y) ![v, v] := by
    intro y v
    have hψ : ContDiff ℝ (2 : ℕ) fun z => φ (x + z) :=
      (hφ 2).comp (contDiff_const.add contDiff_id)
    have hζψ : ζ = (fun z => φ (x + z)) ∘ ⇑(-ContinuousLinearMap.id ℝ (Euclid n)) := by
      rw [hζ]
      funext z
      simp [sub_eq_add_neg]
    rw [hζψ, ContinuousLinearMap.iteratedFDeriv_comp_right _ hψ y le_rfl,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left,
      iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp [sub_eq_add_neg]
  -- `∫ 1_B W Δφ(x − ·) = ∫_B W Δζ = 0` by weak harmonicity.
  have hζW := hharm ζ hζ2
    ((isCompact_closedBall x ε).of_isClosed_subset (isClosed_tsupport ζ) hζspt) (hζspt.trans hball)
  rw [← integral_indicator measurableSet_ball] at hζW
  simpa only [Set.indicator_mul_left, hD2] using hζW

end Submission
/-- **Fubini symmetry of iterated convolutions** (step 4 of the proof of Weyl's lemma, which gives
"Thus w is harmonic in B" in the proof of Simon Ch. 5, Lemma 3.1): for `f ∈ L¹(ℝⁿ)` and continuous
compactly supported kernels `φ, ψ`, `((f ⋆ φ) ⋆ ψ)(x) = ((f ⋆ ψ) ⋆ φ)(x)`.  For continuous
compactly supported `a, b` the kernel `f(y) a(x − z − y) b(z)` is integrable on `ℝⁿ × ℝⁿ`
(dominated by `sup |a| · |b(z)| · |f(y)|`), so Fubini and the substitution `z ↦ (x − y) − z` give
`∫_z (∫_y f(y) a(x − z − y)) b(z) = ∫_y f(y) ∫_z a(z) b(x − y − z)`; the inner kernel integrals
for `(a, b) = (φ, ψ)` and `(ψ, φ)` agree by the same substitution. -/
theorem Submission.dorag_ha_weyl_conv_swap : ∀ (n : ℕ) (f φ ψ : Euclid n → ℝ) (x : Euclid n), Integrable f → Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ → ∫ z, (∫ y, f y * φ (x - z - y)) * ψ z = ∫ z, (∫ y, f y * ψ (x - z - y)) * φ z := by
  intro n f φ ψ x hf hφ hφs hψ hψs
  -- reflection invariance: `∫ a(w − z) b(z) dz = ∫ a(z) b(w − z) dz`, via `z ↦ w − z`
  have refl : ∀ (a b : Euclid n → ℝ) (w : Euclid n),
      ∫ z, a (w - z) * b z = ∫ z, a z * b (w - z) := by
    intro a b w
    rw [← integral_sub_left_eq_self (fun z => a z * b (w - z)) volume w]
    simp only [sub_sub_cancel]
  -- (★): for continuous compactly supported `a, b`,
  -- `∫_z (∫_y f(y) a(x − z − y)) b(z) = ∫_y f(y) ∫_z a(z) b(x − y − z)`
  have gen : ∀ a b : Euclid n → ℝ, Continuous a → HasCompactSupport a → Continuous b →
      HasCompactSupport b →
      ∫ z, (∫ y, f y * a (x - z - y)) * b z = ∫ y, f y * ∫ z, a z * b (x - y - z) := by
    intro a b ha has hb hbs
    obtain ⟨M, hM⟩ := has.exists_bound_of_continuous ha
    have hbi : Integrable b := hb.integrable_of_hasCompactSupport hbs
    -- `K(z, y) = f(y) a(x − z − y) b(z)` is integrable on `ℝⁿ × ℝⁿ`, being a.e.-strongly
    -- measurable and dominated by `M |b(z)| |f(y)|`
    have hK : Integrable (uncurry fun z y => f y * a (x - z - y) * b z)
        (volume.prod (volume : Measure (Euclid n))) := by
      refine ((hbi.norm.mul_prod hf.norm).const_mul M).mono' ?_ (Eventually.of_forall fun p => ?_)
      · have ha' : Continuous fun p : Euclid n × Euclid n => a (x - p.1 - p.2) := by fun_prop
        have hb' : Continuous fun p : Euclid n × Euclid n => b p.1 := by fun_prop
        exact (hf.aestronglyMeasurable.comp_snd.mul ha'.aestronglyMeasurable).mul
          hb'.aestronglyMeasurable
      · simp only [uncurry, norm_mul]
        calc ‖f p.2‖ * ‖a (x - p.1 - p.2)‖ * ‖b p.1‖ ≤ ‖f p.2‖ * M * ‖b p.1‖ := by
              gcongr
              exact hM _
          _ = M * (‖b p.1‖ * ‖f p.2‖) := by ring
    calc ∫ z, (∫ y, f y * a (x - z - y)) * b z
        = ∫ z, ∫ y, f y * a (x - z - y) * b z := by
          simp only [integral_mul_const]
      _ = ∫ y, ∫ z, f y * a (x - z - y) * b z := integral_integral_swap hK
      _ = ∫ y, f y * ∫ z, a z * b (x - y - z) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [sub_right_comm x _ y, mul_assoc, integral_const_mul, refl a b (x - y)]
  rw [gen φ ψ hφ hφs hψ hψs, gen ψ φ hψ hψs hφ hφs]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [← refl ψ φ (x - y), mul_comm]
/-- Patching step of Weyl's lemma (step 5 of its proof).  If each `F ε` is smooth and harmonic on
`B_{R-ε}(0)` and `F ε x = F δ x` whenever `‖x‖ + ε + δ < R`, then `h(x) = F ((R - ‖x‖) / 3) x` is
smooth and harmonic on `B_R(0)`, and `F ε x = h x` for all small `ε > 0`.  The point is that on
`B_r(0)`, `r < R`, `h` coincides with the single function `F ((R - r) / 3)`. -/
theorem Submission.dorag_ha_weyl_glue : ∀ (n : ℕ) (R : ℝ) (F : ℝ → Euclid n → ℝ), 0 < R → (∀ ε : ℝ, 0 < ε → ε < R → ∀ m : ℕ, ContDiffOn ℝ m (F ε) (ball (0 : Euclid n) (R - ε))) → (∀ ε : ℝ, 0 < ε → ε < R → ∀ y ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (F ε) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ (ε δ : ℝ) (x : Euclid n), 0 < ε → 0 < δ → ‖x‖ + ε + δ < R → F ε x = F δ x) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) ∧ (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ ∀ x ∈ ball (0 : Euclid n) R, ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε x = h x := by
  intro n R F hR hsmooth hharm hcons
  -- Step 2: for `r < R`, `F ((R - r) / 3) = h` on `B_r(0)`, by (iii) with `ε = (R - r) / 3` and
  -- `δ = (R - ‖x‖) / 3`, as `‖x‖ + ε + δ < (2R + r) / 3 < R`
  have key : ∀ r : ℝ, r < R → ∀ x : Euclid n, ‖x‖ < r →
      F ((R - r) / 3) x = F ((R - ‖x‖) / 3) x := fun r hr x hx =>
    hcons ((R - r) / 3) ((R - ‖x‖) / 3) x (by linarith) (by linarith) (by linarith)
  -- each `x ∈ B_R(0)` lies in a smaller ball `B_r(0)`, `r < R` (take `r = (‖x‖ + R) / 2`)
  have mid : ∀ x ∈ ball (0 : Euclid n) R, ∃ r, ‖x‖ < r ∧ r < R := fun x hx =>
    ⟨(‖x‖ + R) / 2, by linarith [mem_ball_zero_iff.1 hx], by linarith [mem_ball_zero_iff.1 hx]⟩
  refine ⟨fun x => F ((R - ‖x‖) / 3) x, fun m => ?_, fun y hy => ?_, fun x hx => ?_⟩
  · -- Step 3: on `B_R(0) ∩ B_r(0)`, `h` is the `C^m` function `F ((R - r) / 3)`, as
    -- `B_r(0) ⊆ B_{R - (R - r) / 3}(0)`; `C^m` is a local property
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    obtain ⟨r, hxr, hrR⟩ := mid x hx
    refine ⟨ball 0 r, isOpen_ball, mem_ball_zero_iff.2 hxr, ?_⟩
    have hF : ContDiffOn ℝ m (F ((R - r) / 3)) (ball 0 R ∩ ball 0 r) :=
      (hsmooth ((R - r) / 3) (by linarith) (by linarith [norm_nonneg x]) m).mono fun z hz =>
        mem_ball_zero_iff.2 (by linarith [mem_ball_zero_iff.1 hz.2])
    exact hF.congr fun z hz => (key r hrR z (mem_ball_zero_iff.1 hz.2)).symm
  · -- Step 4: `h = F ((R - r) / 3)` near `y`, so both have the same second derivative at `y`,
    -- and (ii) applies to `F ((R - r) / 3)` at `y ∈ B_r(0) ⊆ B_{R - (R - r) / 3}(0)`
    obtain ⟨r, hyr, hrR⟩ := mid y hy
    have heq : (fun x => F ((R - ‖x‖) / 3) x) =ᶠ[𝓝 y] F ((R - r) / 3) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hyr)] with z hz
      exact (key r hrR z (mem_ball_zero_iff.1 hz)).symm
    rw [(heq.iteratedFDeriv ℝ 2).eq_of_nhds]
    exact hharm ((R - r) / 3) (by linarith) (by linarith [norm_nonneg y]) y
      (mem_ball_zero_iff.2 (by linarith))
  · -- Step 5: for `0 < ε < 2 (R - ‖x‖) / 3`, (iii) with `δ = (R - ‖x‖) / 3` gives `F ε x = h x`
    have hxR := mem_ball_zero_iff.1 hx
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * (R - ‖x‖) / 3 by linarith)] with ε hε
    exact hcons ε ((R - ‖x‖) / 3) x hε.1 (by linarith) (by linarith [hε.2])
/-- **Weyl's lemma, a.e. convergence of approximate identities** (Lebesgue differentiation; cf.
Evans, *PDE*, App. C, Thm. 7(ii)).  If `f ∈ L¹(ℝⁿ)` and for every `ε > 0` the kernel `φ ε` is
continuous, vanishes on `{|y| ≥ ε}`, satisfies `|φ ε| ≤ C ε⁻ⁿ` and has integral `1`, then
`∫ f(y) φ ε(x − y) dy → f(x)` as `ε → 0⁺` for `Lⁿ`-a.e. `x`.  At a Lebesgue point `x₀` the
kernels `y ↦ φ ε(x₀ − y)` have integral `1`, support in `B_ε(x₀)` and sup `≤ C c₁ / Lⁿ(B_ε(x₀))`,
`c₁ = Lⁿ(B₁(0))`, so `|∫ f φ ε(x₀ − ·) − f(x₀)| ≤ C c₁ ⨍_{B_ε(x₀)} |f − f(x₀)| → 0`. -/
theorem Submission.dorag_ha_weyl_ae_tendsto : ∀ (n : ℕ) (f : Euclid n → ℝ) (C : ℝ) (φ : ℝ → Euclid n → ℝ), 0 < n → Integrable f → (∀ ε : ℝ, 0 < ε → Continuous (φ ε)) → (∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, ε ≤ ‖y‖ → φ ε y = 0) → (∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, |φ ε y| ≤ C / ε ^ n) → (∀ ε : ℝ, 0 < ε → ∫ y, φ ε y = 1) → ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun ε => ∫ y, f y * φ ε (x - y)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  intro n f C φ _hn hf _hcont hsupp hbound hint
  -- Lebesgue differentiation: `⨍_{B_r(x₀)} |f - f x₀| → 0` as `r → 0⁺` for a.e. `x₀`
  filter_upwards [VitaliFamily.ae_tendsto_average_norm_sub
    (Besicovitch.vitaliFamily (volume : Measure (Euclid n))) hf.locallyIntegrable] with x₀ h₀
  -- `c₁ = Lⁿ(B₁(0)) > 0`, and `Lⁿ(B_ε(x₀)) = εⁿ c₁`
  have hc₁ : 0 < (volume : Measure (Euclid n)).real (closedBall 0 1) :=
    ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
  -- `y ↦ φ ε (x₀ - y)` has integral `1`, support in `B_ε(x₀)` and sup `≤ C c₁ / Lⁿ(B_ε(x₀))`
  have key : Tendsto (fun ε => ∫ y, φ ε (x₀ - y) • f y) (𝓝[>] (0 : ℝ)) (𝓝 (f x₀)) := by
    apply tendsto_integral_smul_of_tendsto_average_norm_sub
      (C * (volume : Measure (Euclid n)).real (closedBall 0 1))
      (h₀.comp (Besicovitch.tendsto_filterAt _ x₀))
    · exact Eventually.of_forall fun _ => hf.integrableOn
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [integral_sub_left_eq_self (φ ε) volume x₀, hint ε hε]
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) y hy
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      by_contra! h
      exact hy (hsupp ε hε _ h.le)
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) y
      rw [Measure.addHaar_real_closedBall' _ x₀ hε.le, finrank_euclideanSpace_fin,
        mul_div_mul_right _ _ hc₁.ne']
      exact hbound ε hε (x₀ - y)
  refine key.congr fun ε => ?_
  simp_rw [smul_eq_mul, mul_comm]
/-- The radial potential of the mean value property (Simon Ch. 5, 3.2–3.4).  For continuous `g`
vanishing on `[r², ∞)`, `Ψ(y) = P(|y|²)` with `P(t) = ½∫_{r²}^t g` is `C¹` with
`DΨ(y)v = P'(|y|²)·2⟨y, v⟩ = g(|y|²)⟨y, v⟩` (FTC and the chain rule), and `Ψ(y) = 0` for
`|y| ≥ r`, so `tsupport Ψ ⊆ closedBall 0 r`, which is compact. -/
theorem Submission.dorag_ha_mv_radial_potential : ∀ (n : ℕ) (r : ℝ) (g : ℝ → ℝ), 0 < r → Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∃ Ψ : Euclid n → ℝ, ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ ∧ tsupport Ψ ⊆ closedBall 0 r ∧ ∀ y v : Euclid n, fderiv ℝ Ψ y v = g (‖y‖ ^ 2) * inner ℝ y v := by
  intro n r g hr hg hgr
  set P : ℝ → ℝ := fun t => (1/2 : ℝ) * ∫ τ in r ^ 2..t, g τ with hP
  have hPd : ∀ t, HasDerivAt P ((1/2 : ℝ) * g t) t := fun t =>
    ((hg.integral_hasStrictDerivAt (r ^ 2) t).hasDerivAt).const_mul (1/2 : ℝ)
  have hPC : ContDiff ℝ 1 P := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hPd t).differentiableAt, ?_⟩
    have : deriv P = fun t => (1/2 : ℝ) * g t := funext fun t => (hPd t).deriv
    rw [this]; exact continuous_const.mul hg
  have hP0 : ∀ t, r ^ 2 ≤ t → P t = 0 := by
    intro t ht
    simp only [hP]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    · intro τ hτ
      rw [uIcc_of_le ht] at hτ
      exact hgr τ hτ.1
  have hsupp : tsupport (fun y : Euclid n => P (‖y‖ ^ 2)) ⊆ closedBall 0 r := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    exact hy (hP0 _ (pow_le_pow_left₀ hr.le hlt.le 2))
  refine ⟨fun y => P (‖y‖ ^ 2), hPC.comp (contDiff_norm_sq ℝ), ?_, hsupp, ?_⟩
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 r) (isClosed_tsupport _) hsupp
  · intro y v
    have hd : HasFDerivAt (fun y : Euclid n => P (‖y‖ ^ 2))
        (((1/2 : ℝ) * g (‖y‖ ^ 2)) • (2 • innerSL ℝ y)) y :=
      (hPd _).comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
    rw [hd.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    ring
/-- **Green's first identity** for a compactly supported `C¹` function `Ψ` against a function `G`
that is `C²` on an open set `V ⊇ tsupport Ψ` (step 4 of the mean value argument):
`∫ ∑ᵢ DΨ(y)eᵢ · DG(y)eᵢ dy = -∫ Ψ(y) ∑ᵢ D²G(y)(eᵢ, eᵢ) dy`.

For each direction `v = eᵢ`, the product `h = Ψ · DG(·)v` is differentiable everywhere (it vanishes
near every point off `K = tsupport Ψ ⊆ V`), and `y ↦ Dh(y)v = DΨ(y)v · DG(y)v + Ψ(y) D²G(y)(v, v)`
is continuous with compact support.  By translation invariance `t ↦ ∫ h(y + tv) dy` is constant,
and differentiating under the integral at `t = 0` gives `∫ Dh(y)v dy = 0`.  Summing over `i`, with
every summand integrable, gives the identity. -/
theorem Submission.dorag_ha_mv_green_identity : ∀ (n : ℕ) (V : Set (Euclid n)) (G Ψ : Euclid n → ℝ), IsOpen V → ContDiffOn ℝ 2 G V → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ V → ∫ y : Euclid n, ∑ i : Fin n, fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = -∫ y : Euclid n, Ψ y * ∑ i : Fin n, iteratedFDeriv ℝ 2 G y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
  intro n V G Ψ hV hG hΨ hΨc hΨV
  -- Step 1: `DG` is `C¹` on the open set `V`
  have hG1 : ContDiffOn ℝ 1 (fderiv ℝ G) V := hG.fderiv_of_isOpen hV (by norm_num)
  have hGd : ∀ y ∈ V, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
    (hG1.differentiableOn one_ne_zero y hy).differentiableAt (hV.mem_nhds hy)
  have hG1c : ContinuousOn (fderiv ℝ G) V := hG1.continuousOn
  have hG2c : ContinuousOn (fderiv ℝ (fderiv ℝ G)) V :=
    hG1.continuousOn_fderiv_of_isOpen hV le_rfl
  -- Step 2: `Ψ` and `DΨ` vanish off `K = tsupport Ψ`
  have hΨ0 : ∀ y, y ∉ tsupport Ψ → Ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdΨ0 : ∀ y, y ∉ tsupport Ψ → fderiv ℝ Ψ y = 0 := fun y hy => by
    by_contra h'
    exact hy (support_fderiv_subset ℝ h')
  have hdΨc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv one_ne_zero
  have hKo : ∀ y, y ∉ tsupport Ψ → (tsupport Ψ)ᶜ ∈ 𝓝 y := fun y hy =>
    (isClosed_tsupport Ψ).isOpen_compl.mem_nhds hy
  -- Step 3: continuous on `V` and zero off `K` gives continuous with compact support
  have glue : ∀ f : Euclid n → ℝ, ContinuousOn f V → (∀ y, y ∉ tsupport Ψ → f y = 0) →
      Continuous f ∧ HasCompactSupport f := by
    intro f hf h0
    refine ⟨continuous_iff_continuousAt.2 fun y => ?_, ?_⟩
    · by_cases hy : y ∈ V
      · exact hf.continuousAt (hV.mem_nhds hy)
      · have hy' : y ∉ tsupport Ψ := fun h => hy (hΨV h)
        have hfy : f =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [hKo y hy'] with z hz
          exact h0 z hz
        exact continuousAt_const.congr hfy.symm
    · refine IsCompact.of_isClosed_subset hΨc (isClosed_tsupport _) ?_
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport Ψ)
      by_contra h
      exact hy (h0 y h)
  -- the derivative along `v` of a compactly supported function has integral zero
  have core : ∀ (h k : Euclid n → ℝ) (v : Euclid n), Continuous h → HasCompactSupport h →
      Continuous k → HasCompactSupport k →
      (∀ (y : Euclid n) (t : ℝ), HasDerivAt (fun s : ℝ => h (y + s • v)) (k (y + t • v)) t) →
      ∫ y, k y = 0 := by
    intro h k v hh hhc hk hkc hd
    obtain ⟨C, hC⟩ := hk.bounded_above_of_compact_support hkc
    have hSc : IsCompact (cthickening ‖v‖ (tsupport k)) := IsCompact.cthickening hkc
    have hbound : ∀ (y : Euclid n) (t : ℝ), t ∈ ball (0 : ℝ) 1 →
        ‖k (y + t • v)‖ ≤ (cthickening ‖v‖ (tsupport k)).indicator (fun _ => C) y := by
      intro y t ht
      by_cases hy : y ∈ cthickening ‖v‖ (tsupport k)
      · rw [indicator_of_mem hy]
        exact hC _
      · rw [indicator_of_notMem hy]
        have hk0 : k (y + t • v) = 0 := by
          by_contra hne
          apply hy
          refine mem_cthickening_of_dist_le y (y + t • v) ‖v‖ (tsupport k)
            (subset_tsupport k hne) ?_
          have ht1 : ‖t‖ < 1 := by simpa using ht
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul]
          nlinarith [norm_nonneg v, norm_nonneg t]
        simp [hk0]
    have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun (t : ℝ) (y : Euclid n) => h (y + t • v))
      (F' := fun (t : ℝ) (y : Euclid n) => k (y + t • v))
      (x₀ := 0) (bound := (cthickening ‖v‖ (tsupport k)).indicator (fun _ => C))
      (ball_mem_nhds 0 one_pos)
      (Eventually.of_forall fun t =>
        (hh.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (by simpa using hh.integrable_of_hasCompactSupport hhc)
      ((hk.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (ae_of_all _ fun y t ht => hbound y t ht)
      ((integrableOn_const hSc.measure_lt_top.ne).integrable_indicator
        isClosed_cthickening.measurableSet)
      (ae_of_all _ fun y t _ => hd y t)).2
    have hconst : (fun t : ℝ => ∫ y, h (y + t • v)) = fun _ => ∫ y, h y := by
      funext t
      exact integral_add_right_eq_self (fun y => h y) (t • v)
    rw [hconst] at hderiv
    simpa using hderiv.unique (hasDerivAt_const (0 : ℝ) (∫ y, h y))
  -- Steps 4–6: one coordinate direction
  have key : ∀ i : Fin n,
      Integrable (fun y => fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ))) ∧
      Integrable (fun y => Ψ y * iteratedFDeriv ℝ 2 G y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) ∧
      ∫ y, fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) =
        -∫ y, Ψ y * iteratedFDeriv ℝ 2 G y
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
    intro i
    set v : Euclid n := EuclideanSpace.single i (1 : ℝ)
    have h2 : (fun y => Ψ y * iteratedFDeriv ℝ 2 G y ![v, v]) =
        fun y => Ψ y * fderiv ℝ (fderiv ℝ G) y v v := by
      funext y
      simp [iteratedFDeriv_two_apply]
    rw [h2]
    have hgc : ContinuousOn (fun y => fderiv ℝ G y v) V :=
      (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn hG1c
    have hg2c : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ G) y v v) V :=
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        (ContinuousLinearMap.apply ℝ (Euclid n →L[ℝ] ℝ) v).continuous).comp_continuousOn hG2c
    obtain ⟨hAc, hAs⟩ := glue (fun y => fderiv ℝ Ψ y v * fderiv ℝ G y v)
      ((hdΨc.clm_apply continuous_const).continuousOn.mul hgc)
      (fun y hy => by simp [hdΨ0 y hy])
    obtain ⟨hBc, hBs⟩ := glue (fun y => Ψ y * fderiv ℝ (fderiv ℝ G) y v v)
      (hΨ.continuous.continuousOn.mul hg2c) (fun y hy => by simp [hΨ0 y hy])
    obtain ⟨hhc, hhs⟩ := glue (fun y => Ψ y * fderiv ℝ G y v)
      (hΨ.continuous.continuousOn.mul hgc) (fun y hy => by simp [hΨ0 y hy])
    -- the product `Ψ · DG(·)v` is differentiable everywhere
    have hF : ∀ z, HasFDerivAt (fun y => Ψ y * fderiv ℝ G y v)
        (Ψ z • ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ G) z)) +
          fderiv ℝ G z v • fderiv ℝ Ψ z) z := by
      intro z
      by_cases hz : z ∈ V
      · exact (hΨ.differentiable one_ne_zero z).hasFDerivAt.mul
          ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z (hGd z hz).hasFDerivAt)
      · have hz' : z ∉ tsupport Ψ := fun h => hz (hΨV h)
        rw [hΨ0 z hz', hdΨ0 z hz', zero_smul, smul_zero, add_zero]
        refine (hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq ?_
        filter_upwards [hKo z hz'] with y hy
        simp [hΨ0 y hy]
    have hd : ∀ (y : Euclid n) (t : ℝ),
        HasDerivAt (fun s : ℝ => Ψ (y + s • v) * fderiv ℝ G (y + s • v) v)
          ((fun y => fderiv ℝ Ψ y v * fderiv ℝ G y v + Ψ y * fderiv ℝ (fderiv ℝ G) y v v)
            (y + t • v)) t := by
      intro y t
      have hp : HasDerivAt (fun s : ℝ => y + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add y
      refine ((hF (y + t • v)).comp_hasDerivAt t hp).congr_deriv ?_
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, smul_eq_mul]
      ring
    have hA := hAc.integrable_of_hasCompactSupport (μ := volume) hAs
    have hB := hBc.integrable_of_hasCompactSupport (μ := volume) hBs
    have h0 := core (fun y => Ψ y * fderiv ℝ G y v)
      (fun y => fderiv ℝ Ψ y v * fderiv ℝ G y v + Ψ y * fderiv ℝ (fderiv ℝ G) y v v) v
      hhc hhs (hAc.add hBc) (hAs.add hBs) hd
    rw [integral_add hA hB] at h0
    exact ⟨hA, hB, by linarith⟩
  -- Step 7: sum over the coordinate directions
  rw [integral_finsetSum _ (fun i _ => (key i).1)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => (key i).2.1), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (key i).2.2
/-- **Derivatives of `z ↦ h(x − s z)`** (the chain-rule step in the proof of the mean-value
property of harmonic functions, cited in Simon Ch. 5 before 3.2; chapter-05.txt lines 643–644).
For an arbitrary `h : ℝⁿ → ℝ` and `G(z) = h(x − s z)`: `DG(y) a = −s·Dh(x − s y) a` and
`D²G(y)(a, b) = s²·D²h(x − s y)(a, b)`, with Mathlib's total derivatives (`0` where undefined).
If `s = 0`, `G` is constant.  Otherwise `G = h(x + ·) ∘ L` for the continuous linear equivalence
`L z = (−s) z`, and `fderiv`, `iteratedFDeriv` commute with `∘ L` and with translations for every
function. -/
theorem Submission.dorag_ha_mv_affine_comp_deriv : ∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (s : ℝ) (y a b : Euclid n), fderiv ℝ (fun z : Euclid n => h (x - s • z)) y a = -(s * fderiv ℝ h (x - s • y) a) ∧ iteratedFDeriv ℝ 2 (fun z : Euclid n => h (x - s • z)) y ![a, b] = s ^ 2 * iteratedFDeriv ℝ 2 h (x - s • y) ![a, b] := by
  intro n h x s y a b
  rcases eq_or_ne s 0 with rfl | hs
  -- `s = 0`: `G` is the constant `h x`, so both sides vanish.
  · simp only [zero_smul, sub_zero, zero_mul, neg_zero]
    rw [iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  -- `s ≠ 0`: `G = h (x + ·) ∘ L` with `L z = (-s) • z`.
  · let L : Euclid n ≃L[ℝ] Euclid n :=
      ContinuousLinearEquiv.smulLeft (Units.mk0 (-s) (neg_ne_zero.2 hs))
    have hL : ∀ z, L z = (-s) • z := fun z => rfl
    have hfun : (fun z : Euclid n => h (x - s • z)) = (fun w => h (x + w)) ∘ L := by
      funext z; simp [hL, sub_eq_add_neg, neg_smul]
    constructor
    -- `DG(y) a = Dh(x + L y)(L a)`, and `L a = (-s) • a`.
    · rw [hfun, ContinuousLinearEquiv.comp_right_fderiv, fderiv_comp_add_left]
      simp [hL, sub_eq_add_neg, neg_smul, map_smul]
    -- `D²G(y)(a, b) = D²h(x + L y)(L a, L b) = (-s) * (-s) * D²h(x - s • y)(a, b)`.
    · rw [hfun]
      have hcomp := L.iteratedFDerivWithin_comp_right (fun w => h (x + w)) uniqueDiffOn_univ
        (mem_univ (L y)) 2
      rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hcomp
      rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply,
        iteratedFDeriv_comp_add_left]
      have hv : (fun i : Fin 2 => (L : Euclid n →L[ℝ] Euclid n) (![a, b] i)) =
          fun i => (-s) • ![a, b] i := by
        funext i; exact hL _
      rw [hv, ContinuousMultilinearMap.map_smul_univ]
      simp [hL, sub_eq_add_neg, neg_smul, sq]
/-- **Differentiation under the integral sign** for `M(σ) = ∫ h(x − σy) g(|y|²) dy`, the step
`M'(s) = −∫ Dh(x − sy)(y) g(|y|²) dy` in the proof of the mean value property of harmonic
functions.  Here `h` is `C¹` on the open set `U ⊇ B̄_R(x)`, `r > 0`, `g` is continuous with
`g(t) = 0` for `t ≥ r²`, and `|s| r < R`.  For `|σ − s| < δ = (R − |s|r)/(2r)` and `|y| ≤ r`,
`x − σy ∈ B̄_{R₁}(x) ⊆ U` with `R₁ = (|s| + δ) r < R`; the integrand and its `σ`-derivative
`−Dh(x − σy)(y) g(|y|²)` vanish for `|y| ≥ r`, and the derivative is bounded by
`A₁ r γ 1_{B̄_r(0)}` with `A₁ = max_{B̄_{R₁}(x)} ‖Dh‖` and `γ = max_{[0,r²]} |g|`, so
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies. -/
theorem Submission.dorag_ha_mv_deriv_under_integral : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (x : Euclid n) (r R : ℝ) (g : ℝ → ℝ), IsOpen U → ContDiffOn ℝ 1 h U → closedBall x R ⊆ U → 0 < r → Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∀ s : ℝ, |s| * r < R → HasDerivAt (fun σ : ℝ => ∫ y : Euclid n, h (x - σ • y) * g (‖y‖ ^ 2)) (-∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2)) s := by
  intro n U h x r R g hU hh hRU hr hg hgr s hs
  -- the neighbourhood `ball s δ` of `s` and the radius `R₁ = (|s| + δ) r < R`
  set δ : ℝ := (R - |s| * r) / (2 * r) with hδ
  have hδpos : 0 < δ := div_pos (by linarith) (by positivity)
  set R₁ : ℝ := (|s| + δ) * r with hR₁
  have hR₁R : R₁ < R := by
    have : R₁ = |s| * r + (R - |s| * r) / 2 := by
      simp only [hR₁, hδ]; field_simp
    rw [this]; linarith
  -- `g(|y|²) = 0` for `|y| ≥ r`, and `|(x − σy) − x| = |σ| |y|`
  have hgz : ∀ y : Euclid n, r ≤ ‖y‖ → g (‖y‖ ^ 2) = 0 := fun y hy =>
    hgr _ (pow_le_pow_left₀ hr.le hy 2)
  have hnorm : ∀ (σ : ℝ) (y : Euclid n), ‖x - σ • y - x‖ = |σ| * ‖y‖ := by
    intro σ y; rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  -- for `|y| ≤ r`: `x − σy ∈ U` if `|σ| r < R`, and `x − σy ∈ B̄_{R₁}(x)` if `σ ∈ ball s δ`
  have hmemU : ∀ σ : ℝ, |σ| * r < R → ∀ y : Euclid n, ‖y‖ ≤ r → x - σ • y ∈ U := by
    intro σ hσ y hy
    apply hRU
    rw [mem_closedBall, dist_eq_norm, hnorm]
    nlinarith [abs_nonneg σ]
  have hball : ∀ σ ∈ ball s δ, |σ| < |s| + δ := by
    intro σ hσ
    rw [mem_ball, Real.dist_eq] at hσ
    have := abs_sub_abs_le_abs_sub σ s
    linarith
  have hball' : ∀ σ ∈ ball s δ, |σ| * r < R := by
    intro σ hσ
    have := hball σ hσ
    have : |σ| * r < (|s| + δ) * r := mul_lt_mul_of_pos_right this hr
    linarith
  have hmemK : ∀ σ ∈ ball s δ, ∀ y : Euclid n, ‖y‖ ≤ r → x - σ • y ∈ closedBall x R₁ := by
    intro σ hσ y hy
    rw [mem_closedBall, dist_eq_norm, hnorm]
    have := hball σ hσ
    calc |σ| * ‖y‖ ≤ (|s| + δ) * r := by
          apply mul_le_mul this.le hy (norm_nonneg _) (by positivity)
      _ = R₁ := rfl
  -- `h` is continuous and differentiable at every point of `U`, and `Dh` is continuous on `U`
  have hhc : ∀ z ∈ U, ContinuousAt h z := fun z hz =>
    hh.continuousOn.continuousAt (hU.mem_nhds hz)
  have hdc : ContinuousOn (fderiv ℝ h) U := hh.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ h z := fun z hz =>
    (hh.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- bounds `A₁` for `‖Dh‖` on the compact `B̄_{R₁}(x)` and `γ` for `|g(|y|²)|`
  obtain ⟨A₁, hA₁⟩ := (isCompact_closedBall x R₁).exists_bound_of_continuousOn
    (hdc.mono ((closedBall_subset_closedBall hR₁R.le).trans hRU))
  obtain ⟨γ, hγ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := r ^ 2)).exists_bound_of_continuousOn
    hg.continuousOn
  have hgγ : ∀ y : Euclid n, ‖g (‖y‖ ^ 2)‖ ≤ γ := by
    intro y
    by_cases hy : ‖y‖ ≤ r
    · exact hγ _ ⟨by positivity, pow_le_pow_left₀ (norm_nonneg _) hy 2⟩
    · rw [hgz y (le_of_not_ge hy), norm_zero]
      exact (norm_nonneg _).trans (hγ 0 ⟨le_rfl, by positivity⟩)
  -- continuity in `y` of the integrand for `|σ| r < R`, and of its `σ`-derivative at `s`
  have hFcont : ∀ σ : ℝ, |σ| * r < R →
      Continuous (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : ‖y₀‖ ≤ r
    · have h1 : ContinuousAt (fun y : Euclid n => h (x - σ • y)) y₀ :=
        ContinuousAt.comp (f := fun y : Euclid n => x - σ • y) (hhc _ (hmemU σ hσ y₀ hy₀)) (by fun_prop)
      exact h1.mul (by fun_prop)
    · push Not at hy₀
      have : (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) =ᶠ[𝓝 y₀] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy₀] with y hy
        rw [hgz y (le_of_lt hy), mul_zero]
      exact continuousAt_const.congr this.symm
  have hF'cont : Continuous (fun y : Euclid n => -(fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2))) := by
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : ‖y₀‖ ≤ r
    · have h1 : ContinuousAt (fun y : Euclid n => fderiv ℝ h (x - s • y)) y₀ :=
        ContinuousAt.comp (f := fun y : Euclid n => x - s • y)
          (hdc.continuousAt (hU.mem_nhds (hmemU s hs y₀ hy₀))) (by fun_prop)
      exact ((h1.clm_apply continuousAt_id).mul (by fun_prop)).neg
    · push Not at hy₀
      have : (fun y : Euclid n => -(fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2))) =ᶠ[𝓝 y₀]
          fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy₀] with y hy
        rw [hgz y (le_of_lt hy), mul_zero, neg_zero]
      exact continuousAt_const.congr this.symm
  -- the integrand vanishes off `B̄_r(0)`
  have hsupp : ∀ σ : ℝ, HasCompactSupport (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) := by
    intro σ
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) r) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    rw [hgz y hy.le, mul_zero]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ (y : Euclid n) => h (x - σ • y) * g (‖y‖ ^ 2))
    (F' := fun σ (y : Euclid n) => -(fderiv ℝ h (x - σ • y) y * g (‖y‖ ^ 2)))
    (x₀ := s) (bound := (closedBall (0 : Euclid n) r).indicator fun _ => A₁ * r * γ)
    (ball_mem_nhds s hδpos)
    (eventually_of_mem (ball_mem_nhds s hδpos) fun σ hσ =>
      (hFcont σ (hball' σ hσ)).aestronglyMeasurable)
    ((hFcont s hs).integrable_of_hasCompactSupport (hsupp s))
    hF'cont.aestronglyMeasurable
    -- domination: `|Dh(x − σy)(y) g(|y|²)| ≤ A₁ r γ` for `|y| ≤ r`, and `0` otherwise
    (Eventually.of_forall fun y σ hσ => by
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem (by rwa [mem_closedBall, dist_zero_right])]
        rw [norm_neg, norm_mul]
        have h1 : ‖fderiv ℝ h (x - σ • y) y‖ ≤ A₁ * r :=
          ((fderiv ℝ h (x - σ • y)).le_opNorm y).trans
            (mul_le_mul (hA₁ _ (hmemK σ hσ y hy)) hy (norm_nonneg _)
              ((norm_nonneg _).trans (hA₁ _ (hmemK σ hσ y hy))))
        exact mul_le_mul h1 (hgγ y) (norm_nonneg _) (by nlinarith [norm_nonneg (fderiv ℝ h (x - σ • y) y)])
      · rw [hgz y (le_of_not_ge hy), mul_zero, neg_zero, norm_zero]
        rw [indicator_of_notMem (by rwa [mem_closedBall, dist_zero_right])])
    ((integrableOn_const (measure_closedBall_lt_top (x := (0 : Euclid n)) (r := r)).ne).integrable_indicator
      measurableSet_closedBall)
    -- pointwise derivative: the chain rule for `|y| < r`, the zero function for `|y| ≥ r`
    (Eventually.of_forall fun y σ hσ => by
      by_cases hy : ‖y‖ < r
      · have hd := (hdiff _ (hmemU σ (hball' σ hσ) y hy.le)).hasFDerivAt
        have hγ' : HasDerivAt (fun σ : ℝ => x - σ • y) (-y) σ := by
          simpa using (hasDerivAt_id σ).smul_const y |>.const_sub x
        have := (hd.comp_hasDerivAt σ hγ').mul_const (g (‖y‖ ^ 2))
        simpa [map_neg, neg_mul] using this
      · push Not at hy
        have h0 : (fun σ : ℝ => h (x - σ • y) * g (‖y‖ ^ 2)) = fun _ => 0 := by
          funext σ; rw [hgz y hy, mul_zero]
        rw [h0, hgz y hy, mul_zero, neg_zero]
        exact hasDerivAt_const σ 0)
  simpa [integral_neg] using key.2

/-- **Vanishing flux in the mean value property** (step 4 of the mean value proof, `M'(s) = 0`).
Let `h` be `C²` and harmonic on the open set `U ⊇ B̄_R(x)`, `0 < r < R`, `g` continuous with
`g(t) = 0` for `t ≥ r²`, and `0 < s ≤ 1`.  Take the radial potential `Ψ` (`spt Ψ ⊆ B̄_r(0)`,
`DΨ(y)v = g(|y|²) y · v`) and `G(z) = h(x − s z)`, `C²` on `B_R(0)`.  Green's identity gives
`∫ DΨ · DG = −∫ Ψ ΔG = 0`, since `ΔG(y) = s² Δh(x − s y) = 0` on `B_R(0)` and `Ψ = 0` off it;
as `DG(y) = −s Dh(x − s y)`, the left side is `−s ∫ Dh(x − s y)(y) g(|y|²) dy`. -/
theorem Submission.dorag_ha_mv_flux_zero : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ), IsOpen U → ContDiffOn ℝ 2 h U → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → ∀ (x : Euclid n) (r R : ℝ), 0 < r → r < R → closedBall x R ⊆ U → ∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∀ s : ℝ, 0 < s → s ≤ 1 → ∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2) = 0 := by
  intro n U h hU hh hΔ x r R hr hrR hRU g hg hgr s hs0 hs1
  -- the radial potential: `Ψ ∈ C¹_c`, `spt Ψ ⊆ B̄_r(0)`, `DΨ(y)v = g(|y|²) y · v`
  obtain ⟨Ψ, hΨC, hΨc, hΨsupp, hΨd⟩ := Submission.dorag_ha_mv_radial_potential n r g hr hg hgr
  -- `G(z) = h(x − s z)` is `C²` on `V = B_R(0)`, which `z ↦ x − s z` maps into `B̄_R(x) ⊆ U`
  set G : Euclid n → ℝ := fun z => h (x - s • z) with hG
  have hVmaps : ∀ z ∈ ball (0 : Euclid n) R, x - s • z ∈ U := by
    intro z hz
    apply hRU
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0]
    rw [mem_ball, dist_zero_right] at hz
    nlinarith [norm_nonneg z]
  have hGC : ContDiffOn ℝ 2 G (ball (0 : Euclid n) R) := by
    have hA : ContDiff ℝ 2 (fun z : Euclid n => x - s • z) :=
      contDiff_const.sub (contDiff_id.const_smul s)
    exact hh.comp hA.contDiffOn (fun z hz => hVmaps z hz)
  have hsuppV : tsupport Ψ ⊆ ball (0 : Euclid n) R := hΨsupp.trans (closedBall_subset_ball hrR)
  -- Green's identity: `∫ Σᵢ DΨ eᵢ · DG eᵢ = −∫ Ψ ΔG`
  have hgreen := Submission.dorag_ha_mv_green_identity n (ball (0 : Euclid n) R) G Ψ isOpen_ball
    hGC hΨC hΨc hsuppV
  -- `Ψ ΔG = 0`: on `V`, `ΔG(z) = s² Δh(x − s z) = 0`; off `V`, `Ψ(z) = 0`
  have hRHS : ∀ z, Ψ z * ∑ i : Fin n, iteratedFDeriv ℝ 2 G z
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
    intro z
    by_cases hz : z ∈ ball (0 : Euclid n) R
    · have hsum : ∑ i : Fin n, iteratedFDeriv ℝ 2 G z
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
        simp_rw [hG, (Submission.dorag_ha_mv_affine_comp_deriv n h x s z _ _).2]
        rw [← Finset.mul_sum, hΔ _ (hVmaps z hz), mul_zero]
      rw [hsum, mul_zero]
    · have : Ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hz (hsuppV h'))
      rw [this, zero_mul]
  -- `Σᵢ (z · eᵢ) L eᵢ = L z` for linear `L`
  have hexp : ∀ (L : Euclid n →L[ℝ] ℝ) (z : Euclid n),
      ∑ i : Fin n, inner ℝ z (EuclideanSpace.single i (1 : ℝ)) * L (EuclideanSpace.single i 1) =
        L z := by
    intro L z
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [EuclideanSpace.inner_single_right, map_smul]
  -- `Σᵢ DΨ(z)eᵢ · DG(z)eᵢ = −s Dh(x − s z)(z) g(|z|²)`, as `DG(z) = −s Dh(x − s z)`
  have hLHS : ∀ z, ∑ i : Fin n, fderiv ℝ Ψ z (EuclideanSpace.single i (1 : ℝ)) *
      fderiv ℝ G z (EuclideanSpace.single i (1 : ℝ)) =
      -s * (fderiv ℝ h (x - s • z) z * g (‖z‖ ^ 2)) := by
    intro z
    have hGd : ∀ a, fderiv ℝ G z a = -(s * fderiv ℝ h (x - s • z) a) := fun a =>
      (Submission.dorag_ha_mv_affine_comp_deriv n h x s z a a).1
    simp_rw [hΨd, hGd]
    rw [← hexp (fderiv ℝ h (x - s • z)) z, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- so `−s ∫ Dh(x − s y)(y) g(|y|²) dy = 0`, and `s ≠ 0`
  simp_rw [hLHS, hRHS, integral_zero, neg_zero, integral_const_mul] at hgreen
  exact (mul_eq_zero.1 hgreen).resolve_left (neg_ne_zero.2 hs0.ne')
/-- **Ball mean value from the radial kernel identity.**  Let `r > 0`, let `h` be continuous on
`B̄_r(x)`, and suppose `∫ h(x - y) g(|y|²) dy = h(x) ∫ g(|y|²) dy` for every continuous `g`
vanishing on `[r², ∞)`.  Then `∫_{B_r(x)} h = |B_r(x)| h(x)`.  The proof applies the identity to
`g_k(t) = min{1, max{0, (k + 1)(r² - t)}}`, which tend pointwise to `1_{[0, r²)}`.  Dominated
convergence passes to the limit, with bounds `A₀ 1_{B̄_r(0)}` and `1_{B̄_r(0)}`.  The reflection
`y ↦ x - y` then turns `B_r(0)` into `B_r(x)`. -/
theorem Submission.dorag_ha_mv_ball_of_kernel : ∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (r : ℝ), 0 < r → ContinuousOn h (closedBall x r) → (∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2)) → ∫ y in ball x r, h y = (volume (ball x r)).toReal * h x := by
  intro n h x r hr hhc hker
  -- the profiles `g_k`: continuous, `0 ≤ g_k ≤ 1`, zero on `[r², ∞)`
  set gk : ℕ → ℝ → ℝ := fun k t => min 1 (max 0 (((k : ℝ) + 1) * (r ^ 2 - t))) with hgk
  have gk_cont : ∀ k, Continuous (gk k) := fun k => by
    simp only [hgk]; fun_prop
  have gk_zero : ∀ k t, r ^ 2 ≤ t → gk k t = 0 := by
    intro k t ht
    simp only [hgk]
    have : ((k : ℝ) + 1) * (r ^ 2 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rw [max_eq_left this, min_eq_right zero_le_one]
  have gk_nonneg : ∀ k t, 0 ≤ gk k t := fun k t => le_min zero_le_one (le_max_left _ _)
  have gk_le : ∀ k t, gk k t ≤ 1 := fun k t => min_le_left _ _
  have gkz : ∀ k (y : Euclid n), r ≤ ‖y‖ → gk k (‖y‖ ^ 2) = 0 := fun k y hy =>
    gk_zero k _ (pow_le_pow_left₀ hr.le hy 2)
  have gk_cont' : ∀ k, Continuous fun y : Euclid n => gk k (‖y‖ ^ 2) := fun k =>
    (gk_cont k).comp (by fun_prop : Continuous fun y : Euclid n => ‖y‖ ^ 2)
  -- `g_k(|y|²) → 1_{B_r(0)}(y)`: eventually `1` inside the ball, always `0` outside
  have gk_lim : ∀ y : Euclid n, Tendsto (fun k => gk k (‖y‖ ^ 2)) atTop
      (𝓝 ((ball (0 : Euclid n) r).indicator 1 y)) := by
    intro y
    by_cases hy : ‖y‖ < r
    · rw [indicator_of_mem (by rwa [mem_ball, dist_zero_right]), Pi.one_apply]
      have hpos : 0 < r ^ 2 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      obtain ⟨K, hK⟩ := exists_nat_ge (1 / (r ^ 2 - ‖y‖ ^ 2))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      simp only [hgk]
      have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
      rw [div_le_iff₀ hpos] at hK
      have : 1 ≤ ((k : ℝ) + 1) * (r ^ 2 - ‖y‖ ^ 2) := by nlinarith
      rw [max_eq_right (by linarith), min_eq_left this]
    · push Not at hy
      rw [indicator_of_notMem (by rwa [mem_ball, dist_zero_right, not_lt])]
      exact tendsto_const_nhds.congr' (Eventually.of_forall fun k => (gkz k y hy).symm)
  -- `|h| ≤ A₀` on the compact ball `B̄_r(x)`, which contains `x - y` for `|y| ≤ r`
  obtain ⟨A₀, hA₀⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hhc
  have hmem : ∀ y : Euclid n, ‖y‖ ≤ r → x - y ∈ closedBall x r := by
    intro y hy; rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hy
  have hcb : ∀ y : Euclid n, y ∈ closedBall (0 : Euclid n) r ↔ ‖y‖ ≤ r := fun y => by
    rw [mem_closedBall, dist_zero_right]
  -- the integrands vanish off `B̄_r(0)` and are continuous on it
  have hF_meas : ∀ k,
      AEStronglyMeasurable (fun y : Euclid n => h (x - y) * gk k (‖y‖ ^ 2)) volume := by
    intro k
    have : (fun y : Euclid n => h (x - y) * gk k (‖y‖ ^ 2)) =
        (closedBall (0 : Euclid n) r).indicator (fun y => h (x - y) * gk k (‖y‖ ^ 2)) := by
      funext y
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem ((hcb y).2 hy)]
      · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), mul_zero]
    rw [this, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_closedBall
    refine ContinuousOn.mul ?_ (gk_cont' k).continuousOn
    exact hhc.comp (by fun_prop : Continuous fun y : Euclid n => x - y).continuousOn
      (fun y hy => hmem y ((hcb y).1 hy))
  have hbint : ∀ c : ℝ, Integrable ((closedBall (0 : Euclid n) r).indicator fun _ => c) := fun c =>
    IntegrableOn.integrable_indicator
      (integrableOn_const (measure_closedBall_lt_top (x := (0 : Euclid n)) (r := r)).ne)
      measurableSet_closedBall
  -- dominated convergence for both sides of the kernel identity
  have lim1 : Tendsto (fun k => ∫ y : Euclid n, h (x - y) * gk k (‖y‖ ^ 2)) atTop
      (𝓝 (∫ y : Euclid n, h (x - y) * (ball (0 : Euclid n) r).indicator 1 y)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : Euclid n) r).indicator fun _ => A₀) hF_meas (hbint A₀) ?_ ?_
    · intro k
      refine Eventually.of_forall fun y => ?_
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem ((hcb y).2 hy), norm_mul]
        have h1 := hA₀ _ (hmem y hy)
        have h2 : ‖gk k (‖y‖ ^ 2)‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (gk_nonneg _ _)]; exact gk_le _ _
        nlinarith [norm_nonneg (h (x - y)), norm_nonneg (gk k (‖y‖ ^ 2))]
      · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), mul_zero,
          norm_zero]
    · exact Eventually.of_forall fun y => (gk_lim y).const_mul (h (x - y))
  have lim2 : Tendsto (fun k => ∫ y : Euclid n, gk k (‖y‖ ^ 2)) atTop
      (𝓝 (∫ y : Euclid n, (ball (0 : Euclid n) r).indicator 1 y)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : Euclid n) r).indicator fun _ => 1)
      (fun k => (gk_cont' k).aestronglyMeasurable)
      (hbint 1) ?_ (Eventually.of_forall gk_lim)
    intro k
    refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ r
    · rw [indicator_of_mem ((hcb y).2 hy), Real.norm_eq_abs, abs_of_nonneg (gk_nonneg _ _)]
      exact gk_le _ _
    · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), norm_zero]
  -- the hypothesis identifies the two sequences, so the limits agree
  have heq : (fun k => ∫ y : Euclid n, h (x - y) * gk k (‖y‖ ^ 2)) =
      fun k => h x * ∫ y : Euclid n, gk k (‖y‖ ^ 2) :=
    funext fun k => hker (gk k) (gk_cont k) (gk_zero k)
  rw [heq] at lim1
  have hlim := tendsto_nhds_unique lim1 (lim2.const_mul (h x))
  -- left limit: the reflection `y ↦ x - y` preserves volume and maps `B_r(0)` onto `B_r(x)`
  have e1 : ∫ y : Euclid n, h (x - y) * (ball (0 : Euclid n) r).indicator 1 y =
      ∫ y in ball x r, h y := by
    have : (fun y : Euclid n => h (x - y) * (ball (0 : Euclid n) r).indicator 1 y) =
        (ball (0 : Euclid n) r).indicator (fun y => h (x - y)) := by
      funext y; by_cases hy : y ∈ ball (0 : Euclid n) r <;> simp [hy]
    rw [this, integral_indicator measurableSet_ball]
    have hmp : MeasurePreserving (fun y : Euclid n => x - y) volume volume :=
      Measure.measurePreserving_sub_left volume x
    have hpre : (fun y : Euclid n => x - y) ⁻¹' (ball x r) = ball 0 r := by
      ext y; simp [mem_ball, dist_eq_norm]
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb (MeasurableEquiv.subLeft x).measurableEmbedding h (ball x r)
  -- right limit: `∫ 1_{B_r(0)} = |B_r(0)| = |B_r(x)|` by translation invariance
  have e2 : ∫ y : Euclid n, (ball (0 : Euclid n) r).indicator 1 y = (volume (ball x r)).toReal := by
    rw [integral_indicator_one measurableSet_ball, Measure.addHaar_ball_center volume x r]
    rfl
  rw [← e1, hlim, e2, mul_comm]

/-- **Mean value property of harmonic functions** (Simon Ch. 5, 3.2–3.4; Evans, PDE, §2.2.2).
Let `h` be `C²` on the open set `U ⊇ B̄_r(x)`, `r > 0`, with `Σᵢ D²h(eᵢ, eᵢ) = 0` on `U`.  Then
(i) `∫ h(x - y) g(|y|²) dy = h(x) ∫ g(|y|²) dy` for every continuous `g` vanishing on `[r², ∞)`,
and (ii) `∫_{B_r(x)} h = |B_r(x)| h(x)`.  For (i), choose `η > 0` with `B̄_{η + r}(x) ⊆ U`.  Then
`M(σ) = ∫ h(x - σy) g(|y|²) dy` has derivative `M'(s) = -∫ Dh(x - sy)(y) g(|y|²) dy` for
`s ∈ [0, 1]`, and `M'` vanishes on `(0, 1)` (zero flux).  The mean value theorem gives
`M(1) = M(0) = h(x) ∫ g(|y|²) dy`.  Part (ii) follows from (i) by approximating `1_{[0, r²)}`. -/
theorem Submission.dorag_ha_mean_value : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ), 0 < n → IsOpen U → ContDiffOn ℝ 2 h U → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → ∀ (x : Euclid n) (r : ℝ), 0 < r → closedBall x r ⊆ U → (∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2)) ∧ ∫ y in ball x r, h y = (volume (ball x r)).toReal * h x := by
  intro n U h _hn hU hh hΔ x r hr hxr
  -- room around the ball: `B̄_{η + r}(x) ⊆ U` for some `η > 0`
  obtain ⟨η, hη, hηU⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU hxr
  rw [cthickening_closedBall hη.le hr.le] at hηU
  have hrR : r < η + r := by linarith
  -- (i): `M(σ) = ∫ h(x - σy) g(|y|²) dy` is constant on `[0, 1]`
  have hker : ∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) →
      ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2) := by
    intro g hg hgr
    set M : ℝ → ℝ := fun σ => ∫ y : Euclid n, h (x - σ • y) * g (‖y‖ ^ 2) with hM
    set M' : ℝ → ℝ := fun s => -∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2)
      with hM'
    -- differentiation under the integral sign, valid while `|s| r < η + r`
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt M (M' s) s := by
      intro s hs
      refine Submission.dorag_ha_mv_deriv_under_integral n U h x r (η + r) g hU
        (hh.of_le (by norm_num)) hηU hr hg hgr s ?_
      rw [abs_of_nonneg hs.1]
      nlinarith [hs.2]
    -- zero flux: `M' = 0` on `(0, 1)`
    have hzero : ∀ s ∈ Ioo (0 : ℝ) 1, M' s = 0 := by
      intro s hs
      simp only [hM']
      rw [Submission.dorag_ha_mv_flux_zero n U h hU hh hΔ x r (η + r) hr hrR hηU g hg hgr s hs.1
        hs.2.le, neg_zero]
    -- the mean value theorem on `[0, 1]` gives `M(1) = M(0)`
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope M M' (by norm_num : (0 : ℝ) < 1)
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => hderiv s (Ioo_subset_Icc_self hs))
    rw [hzero c hc, sub_zero, div_one, eq_comm, sub_eq_zero] at hc'
    simp only [hM, one_smul, zero_smul, sub_zero] at hc'
    rw [hc', integral_const_mul]
  -- (ii): the ball average, from the kernel identity (i)
  exact ⟨hker, Submission.dorag_ha_mv_ball_of_kernel n h x r hr (hh.continuousOn.mono hxr) hker⟩

/-- Interior estimates for harmonic functions (Simon Ch. 5, 3.2–3.4, the standard estimates that
"follow directly from the mean-value property").  If `h` is smooth and harmonic on
`B = B̆_R(0) ⊂ ℝⁿ` with `∫_B ‖Dh‖² ≤ Rⁿ`, then with `ω = Lⁿ(B̆₁(0))`, `K₁ = 2ⁿ/√ω` and
`C_H = 4nK₁`: (a) `|h(0)| ≤ C_H √(R⁻ⁿ∫_B h²)`, (b) `‖Dh(0)‖ ≤ C_H`, and
(c) `|h(v) − h(0) − Dh(0)v| ≤ C_H‖v‖²/R` for `‖v‖ ≤ R/4`.  The directional derivatives `Dh(·)e`
are again harmonic, so the ball mean value property and Cauchy–Schwarz give (a), (b) on
`B̆_{R/2}(0)` and `‖Dh‖ ≤ K₁` on `B̄_{5R/8}(0)` (balls of radius `R/4`); comparing the means of
`Dh(·)v` over shifted balls gives `|D²h(x)(v, v)| ≤ 8nK₁‖v‖²/R` for `‖x‖ ≤ R/4`, and (c) follows
by second-order Taylor expansion. -/
theorem Submission.dorag_ha_interior_estimates : ∀ n : ℕ, 0 < n → ∃ CH : ℝ, 0 < CH ∧ ∀ (R : ℝ) (h : Euclid n → ℝ), 0 < R → (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) → (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R) → ∫ y in ball (0 : Euclid n) R, ‖fderiv ℝ h y‖ ^ 2 ≤ R ^ n → IntegrableOn (fun y => h y ^ 2) (ball (0 : Euclid n) R) → |h 0| ≤ CH * Real.sqrt ((∫ y in ball (0 : Euclid n) R, h y ^ 2) / R ^ n) ∧ ‖fderiv ℝ h 0‖ ≤ CH ∧ ∀ v : Euclid n, ‖v‖ ≤ R / 4 → |h v - h 0 - fderiv ℝ h 0 v| ≤ CH * ‖v‖ ^ 2 / R := by
  intro n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  -- `ω = Lⁿ(B̆₁(0)) ∈ (0, ∞)` and `Lⁿ(B̆_r(y)) = rⁿω`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, (volume (ball (0 : Euclid n) 1)).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := hω_def ▸ ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  have hvol : ∀ (y : Euclid n) (r : ℝ), 0 < r → (volume (ball y r)).toReal = r ^ n * ω := by
    intro y r hr
    rw [Measure.addHaar_ball_of_pos volume y hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hω_def]
  -- `K₁ = 2ⁿ/√ω`, so that `K₁²ω = 4ⁿ`, and `C_H = 4nK₁ ≥ K₁`
  obtain ⟨K₁, hK₁_def⟩ : ∃ K₁ : ℝ, 2 ^ n / Real.sqrt ω = K₁ := ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := hK₁_def ▸ div_pos (pow_pos two_pos n) (Real.sqrt_pos.2 hω)
  have hK₁sq : K₁ ^ 2 * ω = 4 ^ n := by
    rw [← hK₁_def, div_pow, Real.sq_sqrt hω.le, div_mul_cancel₀ _ hω.ne', ← pow_mul, mul_comm,
      pow_mul]
    norm_num
  have hle_K₁ : ∀ a : ℝ, 0 ≤ a → a ^ 2 * ω ≤ 4 ^ n → a ≤ K₁ := by
    intro a ha haK
    rw [← hK₁sq] at haK
    exact (pow_le_pow_iff_left₀ ha hK₁.le two_ne_zero).1 (le_of_mul_le_mul_right haK hω)
  have hCH : 0 < 4 * (n : ℝ) * K₁ := mul_pos (mul_pos four_pos hn') hK₁
  have hK₁CH : K₁ ≤ 4 * n * K₁ :=
    le_mul_of_one_le_left hK₁.le (by have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn; linarith)
  refine ⟨4 * n * K₁, hCH, ?_⟩
  intro R h hR hcd hlap hgradint hgrad hint
  have hB : IsOpen (ball (0 : Euclid n) R) := isOpen_ball
  have h2 : ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) := by exact_mod_cast hcd 2
  have hDh : ContDiffOn ℝ 1 (fderiv ℝ h) (ball (0 : Euclid n) R) :=
    h2.fderiv_of_isOpen hB (by norm_num)
  -- `B̄_r(y) ⊆ B` as soon as `‖y‖ + r < R`
  have hsub : ∀ (y : Euclid n) (r : ℝ), ‖y‖ + r < R → closedBall y r ⊆ ball (0 : Euclid n) R :=
    fun y r hyr => closedBall_subset_ball' (by rw [dist_zero_right]; linarith)
  -- step 1: every `u_e = Dh(·)e` is smooth and harmonic on `B`
  have hA := fun e => Submission.dorag_ha_ie_fderiv_apply_harmonic n _ h e hB hcd hlap
  -- the mean value identities for `h` and for every `u_e` on balls `B̄_r(y) ⊆ B`
  have hmv : ∀ (y : Euclid n) (r : ℝ), 0 < r → closedBall y r ⊆ ball (0 : Euclid n) R →
      ∫ z in ball y r, h z = (volume (ball y r)).toReal * h y :=
    fun y r hr hyr => (Submission.dorag_ha_mean_value n _ h hn hB h2 hlap y r hr hyr).2
  have hmvD : ∀ (e y : Euclid n) (r : ℝ), 0 < r → closedBall y r ⊆ ball (0 : Euclid n) R →
      ∫ z in ball y r, fderiv ℝ h z e = (volume (ball y r)).toReal * fderiv ℝ h y e :=
    fun e y r hr hyr => (Submission.dorag_ha_mean_value n _ _ hn hB
      (by exact_mod_cast (hA e).1 2) (hA e).2 y r hr hyr).2
  -- step 2 (2b): `‖Dh(y)‖²ω ≤ cⁿ` whenever `B̄_{R/c}(y) ⊆ B`, since `∫_B ‖Dh‖² ≤ Rⁿ`
  have hgrad_le : ∀ (y : Euclid n) (c : ℝ), 0 < c →
      closedBall y (R / c) ⊆ ball (0 : Euclid n) R → ‖fderiv ℝ h y‖ ^ 2 * ω ≤ c ^ n := by
    intro y c hc hyc
    have hRc : 0 < R / c := div_pos hR hc
    have h1 := Submission.dorag_ha_ie_opNorm_sq_mul_volume_le_of_mean_value n (fderiv ℝ h) y
      (R / c) hRc (hDh.continuousOn.mono hyc) fun e => hmvD e y (R / c) hRc hyc
    have h2 : ∫ z in ball y (R / c), ‖fderiv ℝ h z‖ ^ 2 ≤ R ^ n :=
      (setIntegral_mono_set hgradint (Eventually.of_forall fun _ => sq_nonneg _)
        (ball_subset_closedBall.trans hyc).eventuallyLE).trans hgrad
    rw [hvol y _ hRc, div_pow] at h1
    have hRn : 0 < R ^ n := pow_pos hR n
    calc ‖fderiv ℝ h y‖ ^ 2 * ω
        = ‖fderiv ℝ h y‖ ^ 2 * (R ^ n / c ^ n * ω) * (c ^ n / R ^ n) := by field_simp
      _ ≤ R ^ n * (c ^ n / R ^ n) := by gcongr; exact h1.trans h2
      _ = c ^ n := by field_simp
  -- (a): the mean value bound (2a) on `B̆_{R/2}(0)`
  have ha : |h 0| ≤ 4 * n * K₁ * Real.sqrt ((∫ y in ball (0 : Euclid n) R, h y ^ 2) / R ^ n) := by
    have hR2 : 0 < R / 2 := half_pos hR
    have hsub0 := hsub 0 (R / 2) (by rw [norm_zero]; linarith)
    have h1 := Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value n h 0 (R / 2) hR2
      ((hcd 0).continuousOn.mono hsub0) (hmv 0 _ hR2 hsub0)
    have h2 : ∫ z in ball (0 : Euclid n) (R / 2), h z ^ 2 ≤ ∫ y in ball (0 : Euclid n) R, h y ^ 2 :=
      setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
        (ball_subset_closedBall.trans hsub0).eventuallyLE
    rw [hvol 0 _ hR2, div_pow] at h1
    obtain ⟨I, hI_def⟩ : ∃ I : ℝ, ∫ y in ball (0 : Euclid n) R, h y ^ 2 = I := ⟨_, rfl⟩
    rw [hI_def] at h2 ⊢
    have hRn : 0 < R ^ n := pow_pos hR n
    have hI : 0 ≤ I := le_trans (by positivity) (h1.trans h2)
    have hconst : 2 ^ n / ω ≤ (4 * n * K₁) ^ 2 := by
      rw [div_le_iff₀ hω]
      calc (2 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
        _ ≤ 16 * n ^ 2 * 4 ^ n := le_mul_of_one_le_left (by positivity) (by
            have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
            nlinarith)
        _ = (4 * n * K₁) ^ 2 * ω := by rw [← hK₁sq]; ring
    have hsq : h 0 ^ 2 ≤ (4 * n * K₁) ^ 2 * (I / R ^ n) :=
      calc h 0 ^ 2 = h 0 ^ 2 * (R ^ n / 2 ^ n * ω) * (2 ^ n / ω / R ^ n) := by field_simp
        _ ≤ I * (2 ^ n / ω / R ^ n) := by gcongr; exact h1.trans h2
        _ = 2 ^ n / ω * (I / R ^ n) := by ring
        _ ≤ (4 * n * K₁) ^ 2 * (I / R ^ n) := mul_le_mul_of_nonneg_right hconst (by positivity)
    calc |h 0| ≤ Real.sqrt ((4 * n * K₁) ^ 2 * (I / R ^ n)) := Real.abs_le_sqrt hsq
      _ = 4 * n * K₁ * Real.sqrt (I / R ^ n) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCH.le]
  -- (b): the mean value bound (2b) on `B̆_{R/2}(0)`
  have hb : ‖fderiv ℝ h 0‖ ≤ 4 * n * K₁ :=
    (hle_K₁ _ (norm_nonneg _) ((hgrad_le 0 2 two_pos (hsub 0 _ (by rw [norm_zero]; linarith))).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) n))).trans hK₁CH
  -- step 4: `‖Dh‖ ≤ K₁` on `B̄_{5R/8}(0)`, by (2b) on balls of radius `R/4`
  have hstep4 : ∀ z : Euclid n, ‖z‖ ≤ 5 * R / 8 → ‖fderiv ℝ h z‖ ≤ K₁ := fun z hz =>
    hle_K₁ _ (norm_nonneg _) (hgrad_le z 4 four_pos (hsub z _ (by linarith)))
  -- step 5: `|D²h(x)(v, v)| ≤ 8nK₁‖v‖²/R` for `‖x‖ ≤ R/4`, by the shifted-ball comparison
  -- for the harmonic function `u_v = Dh(·)v`, bounded by `K₁‖v‖` on `B̄_{3R/8}(x)`
  have hstep5 : ∀ v x : Euclid n, ‖v‖ ≤ R / 4 → ‖x‖ ≤ R / 4 →
      |iteratedFDeriv ℝ 2 h x ![v, v]| ≤ 2 * n * (K₁ * ‖v‖) / (R / 4) * ‖v‖ := by
    intro v x hv hx
    have hR4 : 0 < R / 4 := by positivity
    have hxB : x ∈ ball (0 : Euclid n) R := mem_ball_zero_iff.2 (by linarith)
    have hu := (hA v).1
    have hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ h y v) x :=
      ((hu 1).differentiableOn (by norm_num)).differentiableAt (hB.mem_nhds hxB)
    have hD := Submission.dorag_ha_ie_norm_fderiv_le_of_mean_value n (fun y => fderiv ℝ h y v) x
      (R / 4) (K₁ * ‖v‖) hn hR4 hdiff ((hu 0).continuousOn.mono (hsub x _ (by linarith)))
      (fun z hz => by
        have hz' : ‖z‖ ≤ 5 * R / 8 := by linarith [norm_le_of_mem_closedBall hz]
        show |fderiv ℝ h z v| ≤ K₁ * ‖v‖
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ h z).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hstep4 z hz') (norm_nonneg v)))
      (fun z hz => hmvD v z (R / 4) hR4
        (hsub z _ (by linarith [norm_le_of_mem_closedBall hz])))
    have hDhx : DifferentiableAt ℝ (fderiv ℝ h) x :=
      (hDh.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hxB)
    have hiter : iteratedFDeriv ℝ 2 h x ![v, v] = fderiv ℝ (fun y => fderiv ℝ h y v) x v := by
      rw [iteratedFDeriv_two_apply, fderiv_clm_apply hDhx (differentiableAt_const v)]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply]
    rw [hiter, ← Real.norm_eq_abs]
    exact ((fderiv ℝ _ x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg v))
  -- step 6 and (c): second-order Taylor expansion along `τ ↦ h(τv)`
  refine ⟨ha, hb, fun v hv => ?_⟩
  have hT := Submission.dorag_ha_ie_taylor_two_le n h R (2 * n * (K₁ * ‖v‖) / (R / 4) * ‖v‖) v
    h2 (by linarith [norm_nonneg v]) fun τ hτ => hstep5 v (τ • v) hv (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      exact (mul_le_of_le_one_left (norm_nonneg v) hτ.2).trans hv)
  calc |h v - h 0 - fderiv ℝ h 0 v| ≤ 2 * n * (K₁ * ‖v‖) / (R / 4) * ‖v‖ / 2 := hT
    _ = 4 * n * K₁ * ‖v‖ ^ 2 / R := by field_simp
/-- **Weyl's lemma** (used without proof in Simon Ch. 5, Lemma 3.1: "thus `w` is harmonic in
`B`").  If `W` is integrable on `B = B̆_R(0)` and weakly harmonic there (`∫_B W Δζ = 0` for every
`C²` function `ζ` with compact support in `B`), then `W` agrees a.e. on `B` with a function `h`
that is `C^m` on `B` for every `m` and harmonic in `B`.  Mollify `W̃ = 1_B W` with the radial
kernels `φ_ε(y) = g_ε(|y|²)`: `F_ε = φ_ε ⋆ W̃` is smooth and harmonic on `B̆_{R−ε}(0)`, the mean
value property and `φ_ε ⋆ φ_δ = φ_δ ⋆ φ_ε` give `F_ε = F_δ` on `B̆_{R−ε−δ}(0)`, the `F_ε` patch to
`h`, and `F_ε → W̃` a.e. by Lebesgue differentiation. -/
theorem Submission.dorag_ha_weyl_lemma : ∀ (n : ℕ) (R : ℝ) (W : Euclid n → ℝ), 0 < n → 0 < R → IntegrableOn W (ball (0 : Euclid n) R) → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) ∧ (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ ∀ᵐ y ∂(volume.restrict (ball (0 : Euclid n) R)), h y = W y := by
  intro n R W hn hR hW hweak
  -- the radial mollifiers `φ_ε(y) = g ε (|y|²)`: smooth, `spt φ_ε ⊆ B̄_ε(0)`, `∫ φ_ε = 1`
  obtain ⟨C, g, hg⟩ := Submission.dorag_ha_weyl_radial_mollifier n hn
  have hφ0 : ∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, ε ≤ ‖y‖ → g ε (‖y‖ ^ 2) = 0 := fun ε hε y hy =>
    (hg ε hε).2.1 _ (pow_le_pow_left₀ hε.le hy 2)
  have hφc : ∀ ε : ℝ, 0 < ε → Continuous fun y : Euclid n => g ε (‖y‖ ^ 2) := fun ε hε =>
    ((hg ε hε).2.2.2.1 0).continuous
  have hφs : ∀ ε : ℝ, 0 < ε → HasCompactSupport fun y : Euclid n => g ε (‖y‖ ^ 2) :=
    fun ε hε => HasCompactSupport.intro (isCompact_closedBall 0 ε) fun y hy =>
      hφ0 ε hε y (not_le.1 (mt mem_closedBall_zero_iff.2 hy)).le
  -- the mollifications `F ε = φ_ε ⋆ W̃` of `W̃ = 1_B W ∈ L¹(ℝⁿ)`
  have hWt : Integrable ((ball (0 : Euclid n) R).indicator W) :=
    hW.integrable_indicator measurableSet_ball
  set F : ℝ → Euclid n → ℝ :=
    fun ε x => ∫ y, (ball (0 : Euclid n) R).indicator W y * g ε (‖x - y‖ ^ 2)
  -- `F ε` is smooth, and harmonic on `B̆_{R−ε}(0)`
  have hmoll : ∀ ε : ℝ, 0 < ε → (∀ m : ℕ, ContDiff ℝ m (F ε)) ∧
      ∀ x ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (F ε) x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := fun ε hε =>
    Submission.dorag_ha_weyl_mollify_harmonic n R ε W (fun y => g ε (‖y‖ ^ 2)) hε hW hweak
      (hg ε hε).2.2.2.1 (hφ0 ε hε)
  -- mean value property of the harmonic `F a`: `∫ F a (x − z) φ_b(z) dz = F a x`
  have hmv : ∀ a b : ℝ, 0 < a → 0 < b → ∀ x : Euclid n, ‖x‖ + a + b < R →
      ∫ z, F a (x - z) * g b (‖z‖ ^ 2) = F a x := by
    intro a b ha hb x hx
    have hsub : closedBall x b ⊆ ball (0 : Euclid n) (R - a) :=
      closedBall_subset_ball' (by rw [dist_zero_right]; linarith)
    rw [(Submission.dorag_ha_mean_value n _ (F a) hn isOpen_ball ((hmoll a ha).1 2).contDiffOn
      (hmoll a ha).2 x b hb hsub).1 (g b) (hg b hb).1 (hg b hb).2.1, (hg b hb).2.2.2.2, mul_one]
  -- hence `F ε = F δ` on `B̆_{R−ε−δ}(0)`, since `(F ε ⋆ φ_δ)(x)` is symmetric in `ε, δ`
  have hcons : ∀ (ε δ : ℝ) (x : Euclid n), 0 < ε → 0 < δ → ‖x‖ + ε + δ < R → F ε x = F δ x := by
    intro ε δ x hε hδ hx
    rw [← hmv ε δ hε hδ x hx, ← hmv δ ε hδ hε x (by linarith)]
    exact Submission.dorag_ha_weyl_conv_swap n ((ball (0 : Euclid n) R).indicator W)
      (fun y => g ε (‖y‖ ^ 2)) (fun y => g δ (‖y‖ ^ 2)) x hWt (hφc ε hε) (hφs ε hε) (hφc δ hδ)
      (hφs δ hδ)
  -- patch the `F ε` into `h`
  obtain ⟨h, hh, hΔh, hFh⟩ := Submission.dorag_ha_weyl_glue n R F hR
    (fun ε hε _ m => ((hmoll ε hε).1 m).contDiffOn) (fun ε hε _ => (hmoll ε hε).2) hcons
  refine ⟨h, hh, hΔh, ?_⟩
  -- `F ε → W̃` a.e. (Lebesgue differentiation), and on `B` also `F ε x = h x` for small `ε`
  have hlim := Submission.dorag_ha_weyl_ae_tendsto n _ C (fun ε y => g ε (‖y‖ ^ 2)) hn hWt hφc
    hφ0 (fun ε hε y => (hg ε hε).2.2.1 _) fun ε hε => (hg ε hε).2.2.2.2
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hlim] with x hx hxB
  have hxh : Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 (h x)) :=
    tendsto_const_nhds.congr' ((hFh x hxB).mono fun ε hε => hε.symm)
  rw [tendsto_nhds_unique hxh hx, indicator_of_mem hxB]
/-- **FTC along a segment for a Lipschitz function** (step 1 of the Poincaré inequality on the unit
ball invoked in the proof of Simon Ch. 5, Lemma 3.1; Gilbarg–Trudinger, Lemma 7.16).  The
restriction `φ(t) = u((1 − t)y + tx)` is Lipschitz, so `∫₀¹ φ' = φ(1) − φ(0) = u(x) − u(y)`: the
difference quotients `∫₀¹ (φ(s + t) − φ(s))/t ds` tend, as `t → 0⁺`, to `φ(1) − φ(0)` by continuity
of `φ` and to `∫₀¹ φ'` by dominated convergence.  Wherever `u` is differentiable at `(1 − t)y + tx`
the chain rule gives `φ'(t) = Du((1 − t)y + tx)(x − y)`, and this holds for a.e. `t ∈ (0, 1]`. -/
theorem Submission.dorag_ha_pb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (x y : Euclid n), LipschitzWith L u → (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ u ((1 - t) • y + t • x)) → u x - u y = ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • y + t • x) (x - y) := by
  intro n u L x y hu hdiff
  -- Step 1: `γ(t) = (1 − t)y + tx` is `‖x − y‖`-Lipschitz, so `φ = u ∘ γ` is Lipschitz
  have hγ : LipschitzWith ‖x - y‖₊ (fun t : ℝ => (1 - t) • y + t • x) := by
    refine LipschitzWith.of_dist_le_mul fun s t => le_of_eq ?_
    have h : (1 - s) • y + s • x - ((1 - t) • y + t • x) = (s - t) • (x - y) := by module
    rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, ← Real.dist_eq, coe_nnnorm, mul_comm]
  -- Step 2: `∫₀¹ φ' = φ(1) − φ(0)` for every Lipschitz `φ : ℝ → ℝ`, with `φ' = lineDeriv ℝ φ · 1`
  have ftc : ∀ (φ : ℝ → ℝ) (K : NNReal), LipschitzWith K φ →
      ∫ s in (0 : ℝ)..1, lineDeriv ℝ φ s 1 = φ 1 - φ 0 := by
    intro φ K hφ
    have hφc : Continuous φ := hφ.continuous
    have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b :=
      fun a b => hφc.intervalIntegrable a b
    -- with `Φ(c) = ∫₀ᶜ φ`, `∫₀¹ (φ(s + t) − φ(s))/t ds = (Φ(1 + t) − Φ(1))/t − (Φ(t) − Φ(0))/t`,
    -- which tends to `φ(1) − φ(0)` as `t → 0⁺` since `Φ' = φ`
    have hlim : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..1, t⁻¹ • (φ (s + t • 1) - φ s)) (𝓝[>] 0)
        (𝓝 (φ 1 - φ 0)) := by
      have hΦ : ∀ b, HasDerivAt (fun c => ∫ s in (0 : ℝ)..c, φ s) (φ b) b :=
        fun b => (hφc.integral_hasStrictDerivAt 0 b).hasDerivAt
      refine ((hΦ 1).tendsto_slope_zero_right.sub (hΦ 0).tendsto_slope_zero_right).congr
        fun t => ?_
      have hshift : ∫ s in (0 : ℝ)..1, φ (s + t) =
          (∫ s in (0 : ℝ)..1 + t, φ s) - ∫ s in (0 : ℝ)..0 + t, φ s := by
        rw [intervalIntegral.integral_comp_add_right,
          intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
      simp only [smul_eq_mul, mul_one]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun s => φ (s + t)).intervalIntegrable 0 1) (hint 0 1),
        hshift, intervalIntegral.integral_same]
      ring
    -- by dominated convergence (Rademacher, against the weight `1_{(0, 1]}`) the same quotients
    -- tend to `∫₀¹ φ'`
    have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const measure_Ioc_lt_top.ne
    have hind : ∀ h : ℝ → ℝ, ∫ s, h s * (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s =
        ∫ s in (0 : ℝ)..1, h s := by
      intro h
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
      congr 1
      ext s
      by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [hs]
    have hdom := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hg (1 : ℝ)
    simp only [hind] at hdom
    exact tendsto_nhds_unique hdom hlim
  -- `φ(1) = u(x)` and `φ(0) = u(y)`
  have key := ftc _ _ (hu.comp hγ)
  simp only [Function.comp_apply, sub_self, zero_smul, one_smul, zero_add, sub_zero,
    add_zero] at key
  rw [← key]
  -- Step 3: `γ' = x − y`, so `φ'(t) = Du(γ(t))(x − y)` wherever `u` is differentiable at `γ(t)`
  have hγ' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 - t) • y + t • x) (x - y) t := by
    intro t
    have h := (((hasDerivAt_id' t).const_sub 1).smul_const y).add ((hasDerivAt_id' t).smul_const x)
    convert h using 1
    rw [neg_one_smul, one_smul, neg_add_eq_sub]
  -- Step 4: that is the case for a.e. `t ∈ Ι 0 1 = (0, 1] ⊆ [0, 1]`
  apply intervalIntegral.integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Icc] at hdiff
  filter_upwards [hdiff] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have hd := (ht (Ioc_subset_Icc_self hmem)).hasFDerivAt.comp_hasDerivAt t (hγ' t)
  exact (hd.hasFDerivAt.hasLineDerivAt 1).lineDeriv.trans (by simp)
/-- Almost every segment meets a Lebesgue-null set `N ⊆ ℝⁿ` in a null set of parameters: for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, `(1 - t) y + t x ∉ N` for `L¹`-a.e. `t ∈ [0, 1]`.  Every `t`-slice
`{(x, y) : (1 - t) y + t x ∈ N}` is `Lⁿ ⊗ Lⁿ`-null: it is `ℝⁿ × N` for `t = 0`, and for `t ≠ 0`
each `x`-section is the preimage of a translate of `N` under `x ↦ t x`.  By Tonelli the set
`{((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ L¹⌞[0, 1]`, so almost all of its
sections in `t` are null. -/
theorem Submission.dorag_ha_pb_segment_null : ∀ (n : ℕ) (N : Set (Euclid n)), MeasurableSet N → volume N = 0 → ∀ᵐ p : Euclid n × Euclid n, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), (1 - t) • p.2 + t • p.1 ∉ N := by
  intro n N hNm hN0
  -- every `t`-slice `{(x, y) : (1 - t) y + t x ∈ N}` is null for `volume = Lⁿ ⊗ Lⁿ`
  have hslice : ∀ t : ℝ, (volume : Measure (Euclid n × Euclid n))
      {p | (1 - t) • p.2 + t • p.1 ∈ N} = 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · -- `t = 0`: the slice is `ℝⁿ × N`, of measure `Lⁿ(ℝⁿ) · 0 = 0`
      have h0 : {p : Euclid n × Euclid n | (1 - 0 : ℝ) • p.2 + (0 : ℝ) • p.1 ∈ N} = univ ×ˢ N := by
        ext p
        simp
      rw [h0, Measure.volume_eq_prod, Measure.prod_prod, hN0, mul_zero]
    · -- `t ≠ 0`: for each `y`, the `x`-section is the preimage of a translate of `N` under `x ↦ t x`
      have hm : MeasurableSet {p : Euclid n × Euclid n | (1 - t) • p.2 + t • p.1 ∈ N} :=
        hNm.preimage (by fun_prop)
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      change (volume : Measure (Euclid n)) ((t • ·) ⁻¹' ((fun z => (1 - t) • y + z) ⁻¹' N)) = 0
      rw [Measure.addHaar_preimage_smul volume ht, measure_preimage_add, hN0, mul_zero]
  -- Tonelli: `E = {((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ ν`
  have hEm : MeasurableSet {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} :=
    hNm.preimage (by fun_prop)
  have hE : ((volume : Measure (Euclid n × Euclid n)).prod (volume.restrict (Icc (0 : ℝ) 1)))
      {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} = 0 := by
    rw [Measure.prod_apply_symm hEm]
    exact (lintegral_congr fun t => hslice t).trans lintegral_zero
  -- sections in `t`: for a.e. `(x, y)`, `ν`-a.e. `t` has `(1 - t) y + t x ∉ N`
  refine Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume.restrict (Icc (0 : ℝ) 1))
    (p := fun q : (Euclid n × Euclid n) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1 ∉ N) ?_
  rw [ae_iff]
  simpa using hE
/-- Cauchy–Schwarz for the integral over a finite measure space, `(∫ h dμ)² ≤ μ(α) ∫ h² dμ` for
`h ∈ L²(μ)`: used twice in the Poincaré inequality on a ball that Simon's proof of Ch. 5,
Lemma 3.1 cites ("by the Poincaré inequality (see e.g. [GT01])").  `h ∈ L¹` (`L² ⊆ L¹` on a finite
measure space) and `h² = ‖h‖² ∈ L¹`.  If `m = μ(α) = 0` then `μ = 0` and both sides vanish;
otherwise, with `c = ∫ h dμ`, `0 ≤ ∫ (h − c/m)² dμ = ∫ h² dμ − c²/m`, and multiplying by `m > 0`
gives the claim. -/
theorem Submission.dorag_ha_pb_sq_integral_le : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ), μ univ ≠ ∞ → MemLp h 2 μ → (∫ x, h x ∂μ) ^ 2 ≤ (μ univ).toReal * ∫ x, h x ^ 2 ∂μ := by
  intro α _ μ h hμ hh
  -- Step 1: `μ` is finite; `h ∈ L¹` (`L² ⊆ L¹` on a finite measure space) and `h² = ‖h‖² ∈ L¹`
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hμ⟩
  have hint : Integrable h μ := hh.integrable one_le_two
  have hint2 : Integrable (fun x => h x ^ 2) μ := by
    simpa [Real.norm_eq_abs, sq_abs] using hh.integrable_norm_pow (p := 2) two_ne_zero
  rcases (ENNReal.toReal_nonneg (a := μ univ)).eq_or_lt with hm0 | hmpos
  · -- Step 2: `μ(α) = 0`, so `μ = 0` and both sides vanish
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1 <|
      ((ENNReal.toReal_eq_zero_iff _).1 hm0.symm).resolve_right hμ
    simp [hμ0]
  · -- Step 3: `m = μ(α) > 0`, `c = ∫ h dμ`; `0 ≤ ∫ (h - c/m)² dμ = ∫ h² dμ - c²/m`
    set m := (μ univ).toReal with hm
    set c := ∫ x, h x ∂μ with hc
    have hint1 : Integrable (fun x => h x ^ 2 - 2 * (c / m) * h x) μ :=
      hint2.sub (hint.const_mul _)
    have hexp : ∫ x, (h x - c / m) ^ 2 ∂μ = ∫ x, h x ^ 2 ∂μ - c ^ 2 / m := by
      have e : ∀ x, (h x - c / m) ^ 2 = h x ^ 2 - 2 * (c / m) * h x + (c / m) ^ 2 :=
        fun x => by ring
      simp_rw [e]
      rw [integral_add hint1 (integrable_const _), integral_sub hint2 (hint.const_mul _),
        integral_const_mul, integral_const, smul_eq_mul, ← hc, measureReal_def, ← hm]
      field_simp
      ring
    have hnn : 0 ≤ ∫ x, (h x - c / m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    -- Step 4: `c²/m ≤ ∫ h² dμ`; multiply by `m > 0`
    rw [hexp, sub_nonneg, div_le_iff₀ hmpos] at hnn
    linarith

/-- **Segment bound for a Lipschitz function at almost every pair** (steps 0, 2 and 3 of the
Poincaré inequality on the ball, written out for all pairs `(x, y)`).  By Rademacher the set `N`
where `u` is not differentiable is Borel and `Lⁿ`-null, so `segment_null` gives, for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, differentiability of `u` at `γ(t) = (1 − t)y + tx` for a.e.
`t ∈ [0, 1]`.  For such a pair `segment_ftc` gives `u(x) − u(y) = ∫₀¹ Du(γ(t))(x − y) dt`, hence
`|u(x) − u(y)| ≤ ∫₀¹ g` with `g(t) = ‖Du(γ(t))‖‖x − y‖ ≤ L‖x − y‖`, and `sq_integral_le` for
`L¹⌞(0, 1]` (total mass `1`) gives `(∫₀¹ g)² ≤ ∫₀¹ g² = ‖x − y‖² ∫₀¹ ‖Du(γ(t))‖² dt`. -/
theorem Submission.dorag_ha_pb_pair_sq_bound : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ p : Euclid n × Euclid n, (u p.1 - u p.2) ^ 2 ≤ ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2 := by
  intro n u L hu
  -- Step 1: the non-differentiability set of `u` is Borel and `Lⁿ`-null (Rademacher).
  have hNmeas : MeasurableSet {z : Euclid n | ¬DifferentiableAt ℝ u z} :=
    (measurableSet_of_differentiableAt ℝ u).compl
  have hNnull : volume {z : Euclid n | ¬DifferentiableAt ℝ u z} = 0 :=
    ae_iff.mp hu.ae_differentiableAt
  -- Step 2: for a.e. pair, `u` is differentiable at a.e. point of the segment.
  filter_upwards [Submission.dorag_ha_pb_segment_null n _ hNmeas hNnull] with p hp
  have hdiff : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      DifferentiableAt ℝ u ((1 - t) • p.2 + t • p.1) := by
    filter_upwards [hp] with t ht
    simpa only [mem_ofPred_eq, not_not] using ht
  -- Step 3: the fundamental theorem of calculus along the segment.
  have hftc : u p.1 - u p.2 =
      ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • p.2 + t • p.1) (p.1 - p.2) :=
    Submission.dorag_ha_pb_segment_ftc n u L p.1 p.2 hu hdiff
  -- Step 4: `|u x - u y| ≤ ∫₀¹ g` with `g t = ‖Du(γ t)‖ ‖x - y‖`, a bounded measurable function.
  have hDmeas : Measurable fun t : ℝ => fderiv ℝ u ((1 - t) • p.2 + t • p.1) :=
    (measurable_fderiv ℝ u).comp
      (by fun_prop : Continuous fun t : ℝ => (1 - t) • p.2 + t • p.1).measurable
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      g = fun t => ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ * ‖p.1 - p.2‖ := ⟨_, rfl⟩
  have hgmeas : Measurable g := by
    rw [hg]
    exact hDmeas.norm.mul_const _
  have hgbound : ∀ t, ‖g t‖ ≤ L * ‖p.1 - p.2‖ := by
    intro t
    simp only [hg, norm_mul, norm_norm]
    exact mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _)
  have hgint : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_const (c := (L : ℝ) * ‖p.1 - p.2‖)).mono_fun'
      hgmeas.aestronglyMeasurable (ae_of_all _ hgbound)
  have hfirst : |u p.1 - u p.2| ≤ ∫ t in (0 : ℝ)..1, g t := by
    rw [hftc, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (ae_of_all _ fun t _ => ?_) hgint
    simp only [hg]
    exact (fderiv ℝ u ((1 - t) • p.2 + t • p.1)).le_opNorm (p.1 - p.2)
  -- Step 5: Cauchy–Schwarz (`sq_integral_le`) on `(0, 1]`, which has total mass `1`.
  have hμ : volume.restrict (Ioc (0 : ℝ) 1) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    simp
  have hmem : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hgmeas.aestronglyMeasurable _ (ae_of_all _ hgbound)
  have hcs : (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    have h := Submission.dorag_ha_pb_sq_integral_le (volume.restrict (Ioc (0 : ℝ) 1)) g
      (by rw [hμ]; exact ENNReal.one_ne_top) hmem
    rw [hμ, ENNReal.toReal_one, one_mul] at h
    rwa [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  -- Step 6: combine, and pull the constant `‖x - y‖²` out of the integral.
  calc (u p.1 - u p.2) ^ 2 = |u p.1 - u p.2| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ t in (0 : ℝ)..1, g t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfirst 2
    _ ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := hcs
    _ = ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      simp only [hg]
      ring
/-- **Slice bound on the unit ball.**  For measurable `g ≥ 0` and `t ∈ [0, 1]`,
`∫_B ∫_B g((1 − t)y + tx) dy dx ≤ 2ⁿ Lⁿ(B) ∫_B g`, `B = B₁(0) ⊂ ℝⁿ`.  If `s ≥ 1/2` and
`c + sB ⊆ B`, the Haar scaling `v ↦ sv` and translation invariance give
`∫_B g(c + sv) dv ≤ ∫ (1_B g)(c + sv) dv = s⁻ⁿ ∫_B g ≤ 2ⁿ ∫_B g`.  By convexity of `B`, this applies
in `y` (`c = tx`, `s = 1 − t`) when `t ≤ 1/2`, and in `x` after Tonelli (`c = (1 − t)y`, `s = t`)
when `t ≥ 1/2`; integrating the constant bound over `B` gives the claim. -/
theorem Submission.dorag_ha_pb_slice_bound : ∀ (n : ℕ) (g : Euclid n → ℝ≥0∞), Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
  intro n g hg t ht
  obtain ⟨ht0, ht1⟩ := ht
  -- One-variable bound: if `s ≥ 1/2` and `c + s • B ⊆ B`, then `∫_B g(c + s v) dv ≤ 2ⁿ ∫_B g`.
  have key : ∀ (c : Euclid n) (s : ℝ), 1 / 2 ≤ s →
      (∀ v ∈ ball (0 : Euclid n) 1, c + s • v ∈ ball (0 : Euclid n) 1) →
      ∫⁻ v in ball (0 : Euclid n) 1, g (c + s • v) ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
    intro c s hs hcs
    have hs0 : 0 < s := by linarith
    obtain ⟨F, hFdef⟩ : ∃ F : Euclid n → ℝ≥0∞, F = (ball (0 : Euclid n) 1).indicator g := ⟨_, rfl⟩
    have hF : Measurable F := hFdef ▸ hg.indicator measurableSet_ball
    -- change of variables `v ↦ s • v` (Haar scaling) followed by translation invariance
    have hcv : ∫⁻ v, F (c + s • v) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, F z := by
      have h1 : ∫⁻ w, F (c + w) ∂(Measure.map (fun v : Euclid n => s • v) volume)
          = ∫⁻ v, F (c + s • v) :=
        lintegral_map (hF.comp (measurable_const_add c)) (measurable_const_smul s)
      rw [← h1, Measure.map_addHaar_smul volume hs0.ne', lintegral_smul_measure,
        lintegral_add_left_eq_self F c, finrank_euclideanSpace_fin, smul_eq_mul]
    have hs2 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 two_pos]
      linarith
    calc ∫⁻ v in ball (0 : Euclid n) 1, g (c + s • v)
        = ∫⁻ v in ball (0 : Euclid n) 1, F (c + s • v) := by
          refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
          rw [hFdef, Set.indicator_of_mem (hcs v hv)]
      _ ≤ ∫⁻ v, F (c + s • v) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [hcv, hFdef, lintegral_indicator measurableSet_ball]
      _ ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          gcongr
          calc ENNReal.ofReal |(s ^ n)⁻¹| = ENNReal.ofReal s⁻¹ ^ n := by
                rw [abs_of_pos (by positivity), ← inv_pow, ENNReal.ofReal_pow (by positivity)]
            _ ≤ ENNReal.ofReal 2 ^ n := by gcongr
            _ = 2 ^ n := by rw [ENNReal.ofReal_ofNat]
  -- the integrand is jointly measurable
  have hmeas : Measurable (fun p : Euclid n × Euclid n => g ((1 - t) • p.2 + t • p.1)) :=
    hg.comp (by fun_prop)
  rcases le_total (1 / 2 : ℝ) t with h | h
  · -- `t ≥ 1/2`: Tonelli, then change variables in `x` with `c = (1 - t) • y`, `s = t`
    rw [lintegral_lintegral_swap (f := fun x y => g ((1 - t) • y + t • x)) hmeas.aemeasurable]
    calc ∫⁻ y in ball (0 : Euclid n) 1, ∫⁻ x in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in ball (0 : Euclid n) 1, 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          refine key ((1 - t) • y) t h fun v hv => ?_
          exact convex_ball (0 : Euclid n) 1 hy hv (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const]
          ring
  · -- `t ≤ 1/2`: change variables in `y` with `c = t • x`, `s = 1 - t`
    calc ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in ball (0 : Euclid n) 1, 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
          calc ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
              = ∫⁻ y in ball (0 : Euclid n) 1, g (t • x + (1 - t) • y) :=
                lintegral_congr fun y => by rw [add_comm]
            _ ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
                refine key (t • x) (1 - t) (by linarith) fun v hv => ?_
                rw [add_comm]
                exact convex_ball (0 : Euclid n) 1 hv hx (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const]
          ring

/-- **Poincaré inequality on the unit ball, double-integral step** (the convex-domain argument of
Gilbarg–Trudinger, Lemma 7.16, cited in Simon's proof of Lemma 5.3.1).  For Lipschitz `u` on
`ℝⁿ` and `B = B₁(0)`, `∫_B ∫_B (u(x) - u(y))² ≤ 2ⁿ⁺² ωₙ ∫_B ‖Du‖²`.  For a.e. `x, y ∈ B`,
`dorag_ha_pb_pair_sq_bound` and `‖x - y‖ < 2` give
`(u(x) - u(y))² ≤ 4 ∫₀¹ ‖Du((1 - t)y + tx)‖² dt`.  Integrate over `B × B` and move the
`t`-integral outside (Tonelli); then `dorag_ha_pb_slice_bound` bounds each slice by
`2ⁿ ωₙ ∫_B ‖Du‖²`.  As `‖Du‖ ≤ Lip(u)`, the bound is finite, so it passes from `ℝ≥0∞` to `ℝ`. -/
theorem Submission.dorag_ha_pb_double_integral_bound : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∫ x in ball (0 : Euclid n) 1, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2 ≤ 2 ^ (n + 2) * (volume (ball (0 : Euclid n) 1)).toReal * ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 := by
  intro n u L hu
  have hpair := Submission.dorag_ha_pb_pair_sq_bound n u L hu
  have hslice := Submission.dorag_ha_pb_slice_bound n
  have hcont : Continuous u := hu.continuous
  -- Step 1: `g = ofReal ‖Du‖²` is measurable, and `∫_B g < ∞` since `‖Du‖ ≤ L`
  have hD : Measurable fun z => ‖fderiv ℝ u z‖ ^ 2 := (measurable_fderiv ℝ u).norm.pow_const 2
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hD.ennreal_ofReal
  have hJ : ∫⁻ z in ball (0 : Euclid n) 1, g z ≠ ∞ := by
    have h1 : ∫⁻ z in ball (0 : Euclid n) 1, g z ≤
        ∫⁻ _ in ball (0 : Euclid n) 1, ENNReal.ofReal ((L : ℝ) ^ 2) :=
      lintegral_mono fun z => by
        rw [hgx]
        gcongr
        exact norm_fderiv_le_of_lipschitz ℝ hu
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)).ne
  -- Step 2: for a.e. `x, y ∈ B`, `(u x - u y)² ≤ 4 ∫_(0,1] ‖Du((1 - t) y + t x)‖² dt`
  have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) 1)),
      ∀ᵐ y ∂(volume.restrict (ball (0 : Euclid n) 1)),
        ENNReal.ofReal ((u x - u y) ^ 2) ≤ 4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair),
      ae_restrict_mem measurableSet_ball] with x hx hxB
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem measurableSet_ball] with y hy hyB
    rw [mem_ball_zero_iff] at hxB hyB
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2 with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have hxy : ‖x - y‖ ^ 2 ≤ 4 := by
      have h2 : ‖x - y‖ < 2 := by linarith [norm_sub_le x y]
      nlinarith [norm_nonneg (x - y)]
    have h4 : (u x - u y) ^ 2 ≤ 4 * G := hy.trans (mul_le_mul_of_nonneg_right hxy hG)
    -- `G` is the integral over `(0, 1]` of a nonnegative function
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hD.comp h.measurable).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => sq_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal ((u x - u y) ^ 2) ≤ ENNReal.ofReal (4 * G) := ENNReal.ofReal_le_ofReal h4
      _ = 4 * ENNReal.ofReal G := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ 4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by gcongr
  -- Step 3: integrate over `B × B`, move the `t`-integral outside (Tonelli), apply the slice bound
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  have hI : ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        ENNReal.ofReal ((u x - u y) ^ 2) ≤
      2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
    calc ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          ENNReal.ofReal ((u x - u y) ^ 2)
        ≤ ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          lintegral_mono_ae (hae.mono fun x hx => lintegral_mono_ae hx)
      _ = 4 * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1,
          ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)]
          rw [hswap]
      _ ≤ 4 * ∫⁻ _ in Ioc (0 : ℝ) 1,
          2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          gcongr 4 * ?_
          exact setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hg t (Ioc_subset_Icc_self ht)
      _ = 2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one, pow_add]
          ring
  -- Step 4: back to Bochner integrals; the bound is finite since `∫_B g < ∞`
  have hK : Measurable fun x : Euclid n =>
      ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2) := by
    have h : Continuous fun p : Euclid n × Euclid n => (u p.1 - u p.2) ^ 2 := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal ((u p.1 - u p.2) ^ 2))
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2 =
      (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _)
      (by fun_prop : Continuous fun y => (u x - u y) ^ 2).aestronglyMeasurable
  have hrhs : ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 =
      (∫⁻ z in ball (0 : Euclid n) 1, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      hD.aestronglyMeasurable]
    simp only [hgx]
  have hfin : (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Euclid n) 1) *
      ∫⁻ z in ball (0 : Euclid n) 1, g z ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      measure_ball_lt_top.ne) hJ
  calc ∫ x in ball (0 : Euclid n) 1, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2
      = ∫ x in ball (0 : Euclid n) 1,
          (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal := by
        simp only [hinner]
    _ = (∫⁻ x in ball (0 : Euclid n) 1, ENNReal.ofReal
          (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) *
          ∫⁻ z in ball (0 : Euclid n) 1, g z).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ (n + 2) * (volume (ball (0 : Euclid n) 1)).toReal *
          ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- **Poincaré inequality on a ball** (Simon Ch. 5, proof of Lemma 3.1; Gilbarg–Trudinger,
Lemma 7.16), the averaging step, for any `s ⊆ ℝⁿ` with `ω = Lⁿ(s) < ∞` and `f ∈ L²(s)`:
`∫_s (f − f̄)² ≤ ω⁻¹ ∫_s ∫_s (f(x) − f(y))² dy dx`, `f̄ = ω⁻¹ ∫_s f` (both sides vanish if
`ω = 0`).  For each `x`, `f(x) − f̄ = ω⁻¹ ∫_s (f(x) − f(y)) dy`, so Cauchy–Schwarz
(`dorag_ha_pb_sq_integral_le`) gives `(f(x) − f̄)² ≤ ω⁻¹ ∫_s (f(x) − f(y))² dy`.  This is
integrated over `s`; the right side is integrable since `(f(x) − f(y))² ≤ 2f(x)² + 2f(y)²`. -/
theorem Submission.dorag_ha_pb_variance_bound : ∀ (n : ℕ) (s : Set (Euclid n)) (f : Euclid n → ℝ), volume s ≠ ∞ → MemLp f 2 (volume.restrict s) → ∫ x in s, (f x - (∫ y in s, f y) / (volume s).toReal) ^ 2 ≤ ((volume s).toReal)⁻¹ * ∫ x in s, ∫ y in s, (f x - f y) ^ 2 := by
  intro n s f hs hf
  set μ : Measure (Euclid n) := volume.restrict s
  set ω : ℝ := (volume s).toReal
  -- Step 1: `μ` is finite with `μ(ℝⁿ).toReal = ω`, and `f, f² ∈ L¹(μ)`
  have hμuniv : μ univ = volume s := Measure.restrict_apply_univ s
  have hμfin : μ univ ≠ ∞ := hμuniv ▸ hs
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hs
  have hf1 : Integrable f μ := hf.integrable one_le_two
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hf.integrable_norm_pow two_ne_zero
  -- Step 2: if `ω = 0` then `μ = 0` and both sides vanish
  rcases eq_or_ne ω 0 with hω0 | hω0
  · have hμ0 : μ = 0 :=
      Measure.restrict_eq_zero.2 (((ENNReal.toReal_eq_zero_iff _).1 hω0).resolve_right hs)
    rw [hω0, inv_zero, zero_mul, hμ0, integral_zero_measure]
  -- Step 3: the pointwise bound `(f(x) − f̄)² ≤ ω⁻¹ ∫_s (f(x) − f(y))² dy`
  have hpt : ∀ x, (f x - (∫ y, f y ∂μ) / ω) ^ 2 ≤ ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ := by
    intro x
    have hmem : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
    have hCS := Submission.dorag_ha_pb_sq_integral_le μ (fun y => f x - f y) hμfin hmem
    rw [hμuniv] at hCS
    have hI : ∫ y, (f x - f y) ∂μ = ω * f x - ∫ y, f y ∂μ := by
      rw [integral_sub (integrable_const (f x)) hf1, integral_const, smul_eq_mul, measureReal_def,
        hμuniv]
    have hdiff : f x - (∫ y, f y ∂μ) / ω = ω⁻¹ * ∫ y, (f x - f y) ∂μ := by
      rw [hI]
      field_simp
    rw [hdiff, mul_pow]
    calc (ω⁻¹) ^ 2 * (∫ y, (f x - f y) ∂μ) ^ 2
        ≤ (ω⁻¹) ^ 2 * (ω * ∫ y, (f x - f y) ^ 2 ∂μ) := by gcongr
      _ = ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ := by field_simp
  -- Step 4: `(x, y) ↦ (f(x) − f(y))²` is `μ ⊗ μ`-integrable, being `≤ 2f(x)² + 2f(y)²`
  have hprod : Integrable (fun p : Euclid n × Euclid n => (f p.1 - f p.2) ^ 2) (μ.prod μ) := by
    have hm := hf.aestronglyMeasurable
    refine Integrable.mono' (((hf2.comp_fst μ).const_mul 2).add ((hf2.comp_snd μ).const_mul 2))
      ((hm.comp_fst.sub hm.comp_snd).pow 2) (ae_of_all _ fun p => ?_)
    show ‖(f p.1 - f p.2) ^ 2‖ ≤ 2 * f p.1 ^ 2 + 2 * f p.2 ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f p.1 + f p.2)]
  have hinner : Integrable (fun x => ∫ y, (f x - f y) ^ 2 ∂μ) μ := hprod.integral_prod_left
  -- Step 5: integrate the pointwise bound over `s`
  calc ∫ x, (f x - (∫ y, f y ∂μ) / ω) ^ 2 ∂μ
      ≤ ∫ x, ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hinner.const_mul ω⁻¹)
          (ae_of_all _ hpt)
    _ = ω⁻¹ * ∫ x, ∫ y, (f x - f y) ^ 2 ∂μ ∂μ := integral_const_mul _ _

/-- **Poincaré inequality on the unit ball** for Lipschitz `u : ℝⁿ → ℝ` (the inequality cited in
Simon's proof of 5.3.1, "by the Poincaré inequality (see e.g. [GT01])"; Gilbarg–Trudinger,
Lemma 7.16 and (7.45)).  With `B = B̆₁(0)`, `ω = Lⁿ(B) ∈ (0, ∞)` and `ū = ω⁻¹∫_B u`,
`∫_B (u − ū)² ≤ ω⁻¹∫_B∫_B (u(x) − u(y))² dy dx ≤ ω⁻¹ · 2ⁿ⁺²ω∫_B ‖Du‖² = 2ⁿ⁺²∫_B ‖Du‖²`:
the first step is the variance bound (`u ∈ L²(B)`, being continuous with `|u| ≤ |u(0)| + L` on
`B`), the second the double-integral bound (FTC along segments and the affine change of
variables).  So `C_P = 2ⁿ⁺²`. -/
theorem Submission.dorag_ha_poincare_ball : ∀ n : ℕ, 0 < n → ∃ CP : ℝ, 0 < CP ∧ ∀ (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∫ x in ball (0 : Euclid n) 1, (u x - (∫ y in ball (0 : Euclid n) 1, u y) / (volume (ball (0 : Euclid n) 1)).toReal) ^ 2 ≤ CP * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n _
  refine ⟨2 ^ (n + 2), by positivity, fun u L hu => ?_⟩
  -- `ω = Lⁿ(B) ∈ (0, ∞)`
  have hBfin : volume (ball (0 : Euclid n) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hω : 0 < (volume (ball (0 : Euclid n) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclid n) one_pos).ne' hBfin
  -- `u ∈ L²(B)`: `u` is continuous and `‖u x‖ ≤ ‖u 0‖ + L` on `B`
  have hmem : MemLp u 2 (volume.restrict (ball (0 : Euclid n) 1)) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) 1)) :=
      isFiniteMeasure_restrict.mpr hBfin
    refine MemLp.of_bound hu.continuous.aestronglyMeasurable (‖u 0‖ + L) ?_
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    have hux : dist (u x) (u 0) ≤ L * 1 := hu.dist_le_mul_of_le (mem_ball.mp hx).le
    calc ‖u x‖ = dist (u x) 0 := (dist_zero_right _).symm
      _ ≤ dist (u x) (u 0) + dist (u 0) 0 := dist_triangle _ _ _
      _ ≤ ‖u 0‖ + L := by rw [dist_zero_right]; linarith
  -- the variance bound, then the double-integral bound multiplied by `ω⁻¹ ≥ 0`
  calc _ ≤ _ := Submission.dorag_ha_pb_variance_bound n (ball (0 : Euclid n) 1) u hBfin hmem
    _ ≤ _ := mul_le_mul_of_nonneg_left
          (Submission.dorag_ha_pb_double_integral_bound n u L hu) (inv_nonneg.mpr hω.le)
    _ = _ := by rw [mul_comm (2 ^ (n + 2) : ℝ), mul_assoc, inv_mul_cancel_left₀ hω.ne']
namespace Submission

/-- Fundamental theorem of calculus for a Lipschitz `u` along the line `τ ↦ p + τ v`: if `u` is
differentiable at `p + τ v` for a.e. `τ ∈ [a, b]`, then
`u(p + b v) − u(p + a v) = ∫_a^b Du(p + τ v) v dτ`.  The difference quotients of
`φ(τ) = u(p + τ v)` are bounded by `L ‖v‖`, so dominated convergence takes their integrals to
`∫_a^b Du(p + τ v) v`; the same integrals are boundary averages of `φ`, which tend to
`φ(b) − φ(a)`. -/
theorem dorag_ha_rb_line_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (p v : Euclid n) (a b : ℝ), LipschitzWith L u → (∀ᵐ τ : ℝ, τ ∈ Set.uIcc a b → DifferentiableAt ℝ u (p + τ • v)) → u (p + b • v) - u (p + a • v) = ∫ τ in a..b, fderiv ℝ u (p + τ • v) v := by
  intro n u L p v a b hu hdiff
  -- `φ τ = u (p + τ • v)` is continuous and `L ‖v‖`-Lipschitz
  set φ : ℝ → ℝ := fun τ => u (p + τ • v) with hφ
  have hφcont : Continuous φ :=
    hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hφlip : ∀ s t : ℝ, |φ s - φ t| ≤ L * ‖v‖ * |s - t| := by
    intro s t
    have h := hu.dist_le_mul (p + s • v) (p + t • v)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs] at h
    calc |φ s - φ t| ≤ L * (|s - t| * ‖v‖) := h
      _ = L * ‖v‖ * |s - t| := by ring
  -- chain rule along the line
  have hderiv : ∀ τ : ℝ, DifferentiableAt ℝ u (p + τ • v) →
      HasDerivAt φ (fderiv ℝ u (p + τ • v) v) τ := by
    intro τ hτ
    have hγ : HasDerivAt (fun t : ℝ => p + t • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add p
    exact hτ.hasFDerivAt.comp_hasDerivAt τ hγ
  -- dominated convergence for the difference quotients
  have hlim1 : Tendsto (fun h : ℝ => ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)) (𝓝[>] 0)
      (𝓝 (∫ τ in a..b, fderiv ℝ u (p + τ • v) v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (L : ℝ) * ‖v‖) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards with h
      exact (((hφcont.comp (continuous_id.add continuous_const)).sub hφcont).const_smul
        h⁻¹).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      filter_upwards with τ _
      have hh' : (0 : ℝ) < h := hh
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hh']
      have := hφlip (τ + h) τ
      rw [add_sub_cancel_left, abs_of_pos hh'] at this
      calc h⁻¹ * |φ (τ + h) - φ τ| ≤ h⁻¹ * (L * ‖v‖ * h) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hh'.le)
        _ = L * ‖v‖ := by field_simp
    · filter_upwards [hdiff] with τ hτ hτ'
      exact (hderiv τ (hτ (uIoc_subset_uIcc hτ'))).tendsto_slope_zero_right
  -- the difference quotients integrate to boundary averages
  set F : ℝ → ℝ := fun x => ∫ τ in (0 : ℝ)..x, φ τ with hF
  have hFint : ∀ s t : ℝ, ∫ τ in s..t, φ τ = F t - F s := by
    intro s t
    exact (intervalIntegral.integral_interval_sub_left (hφcont.intervalIntegrable _ _)
      (hφcont.intervalIntegrable _ _)).symm
  have hkey : ∀ h : ℝ, ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)
      = h⁻¹ • (F (b + h) - F b) - h⁻¹ • (F (a + h) - F a) := by
    intro h
    have hi : IntervalIntegrable (fun τ => φ (τ + h)) volume a b :=
      (hφcont.comp (continuous_id.add continuous_const)).intervalIntegrable a b
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_sub hi
      (hφcont.intervalIntegrable a b), intervalIntegral.integral_comp_add_right (fun τ => φ τ) h,
      hFint, hFint]
    simp only [smul_eq_mul]
    ring
  have hFd : ∀ x : ℝ, HasDerivAt F (φ x) x := fun x =>
    (hφcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hlim2 : Tendsto (fun h : ℝ => ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)) (𝓝[>] 0)
      (𝓝 (φ b - φ a)) := by
    simp_rw [hkey]
    exact (hFd b).tendsto_slope_zero_right.sub (hFd a).tendsto_slope_zero_right
  exact tendsto_nhds_unique hlim2 hlim1


end Submission

/-- **FTC along translates of a Lipschitz function, for a.e. base point.**  If `u : ℝⁿ → ℝ` is
`L`-Lipschitz and `z ∈ ℝⁿ`, then `u(p + z) − u(p) = ∫₀¹ Du(p + τz)z dτ` for a.e. `p ∈ ℝⁿ`.  By
Rademacher's theorem the measurable set `D` of differentiability points of `u` is conull, so by
translation invariance `p + τz ∈ D` for a.e. `p`, for every `τ`.  Fubini for the null set of the
measurable set `{(p, τ) : p + τz ∈ D}` then gives, for a.e. `p`, `p + τz ∈ D` for a.e. `τ`: the
hypothesis of the line FTC `Submission.dorag_ha_rb_line_ftc` with `v = z`, `a = 0`, `b = 1`. -/
theorem Submission.dorag_ha_rb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (z : Euclid n), LipschitzWith L u → ∀ᵐ p : Euclid n, u (p + z) - u p = ∫ τ in (0 : ℝ)..1, fderiv ℝ u (p + τ • z) z := by
  intro n u L z hu
  -- step 1: the set `D` of differentiability points of `u` is measurable and conull (Rademacher)
  have hD : MeasurableSet {y : Euclid n | DifferentiableAt ℝ u y} :=
    measurableSet_of_differentiableAt ℝ u
  have hae : ∀ᵐ y : Euclid n, DifferentiableAt ℝ u y := hu.ae_differentiableAt
  -- step 2: for every `τ`, `p ↦ p + τz` preserves Lebesgue measure, so `p + τz ∈ D` for a.e. `p`
  have hτ : ∀ τ : ℝ, ∀ᵐ p : Euclid n, DifferentiableAt ℝ u (p + τ • z) := fun τ =>
    (measurePreserving_add_right volume (τ • z)).quasiMeasurePreserving.ae hae
  -- step 3: `{(p, τ) : p + τz ∈ D}` is measurable, so Fubini lets us swap the a.e. quantifiers
  have hmeas : MeasurableSet {q : Euclid n × ℝ | DifferentiableAt ℝ u (q.1 + q.2 • z)} :=
    hD.preimage (measurable_fst.add (measurable_snd.smul_const z))
  have hp : ∀ᵐ p : Euclid n, ∀ᵐ τ : ℝ, DifferentiableAt ℝ u (p + τ • z) :=
    (Measure.ae_ae_comm (p := fun p τ => DifferentiableAt ℝ u (p + τ • z)) hmeas).2
      (Eventually.of_forall hτ)
  -- step 4: the line FTC with `v = z`, `a = 0`, `b = 1`, and `1 • z = z`, `p + 0 • z = p`
  filter_upwards [hp] with p hp
  have h := Submission.dorag_ha_rb_line_ftc n u L p z 0 1 hu (hp.mono fun τ hτ _ => hτ)
  rwa [one_smul, zero_smul, add_zero] at h
/-- FTC along rays through the origin: for an `L`-Lipschitz `u` and a.e. `x`,
`u(x) − u(tx) = ∫_t^1 Du(σx)x dσ` for every `t`.  By Rademacher the differentiability set `D` of
`u` is measurable and conull.  For `σ ≠ 0` the dilation `x ↦ σx` pulls null sets back to null sets
(Haar scaling), so a.e. `x` has `σx ∈ D`; `σ = 0` is a null exception in `ℝ`.  Swapping the two
a.e. quantifiers (`Measure.ae_ae_comm`, `{(σ, x) : σx ∈ D}` being measurable) gives a.e. `x` with
`σx ∈ D` for a.e. `σ`, and for such `x` the line FTC `Submission.dorag_ha_rb_line_ftc` with
`p = 0`, `v = x` applies for every `t`. -/
theorem Submission.dorag_ha_rb_ray_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ x : Euclid n, ∀ t : ℝ, u x - u (t • x) = ∫ σ in t..1, fderiv ℝ u (σ • x) x := by
  intro n u L hu
  -- for `σ ≠ 0`, a.e. `x` has `σ • x` in the (conull) differentiability set
  have hσ : ∀ᵐ σ : ℝ, ∀ᵐ x : Euclid n, DifferentiableAt ℝ u (σ • x) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with σ hσ
    exact (Measure.quasiMeasurePreserving_smul volume hσ).ae hu.ae_differentiableAt
  -- swap the quantifiers: `{(σ, x) | DifferentiableAt ℝ u (σ • x)}` is measurable
  have hx : ∀ᵐ x : Euclid n, ∀ᵐ σ : ℝ, DifferentiableAt ℝ u (σ • x) :=
    (Measure.ae_ae_comm (p := fun (σ : ℝ) (x : Euclid n) => DifferentiableAt ℝ u (σ • x))
      ((continuous_smul (M := ℝ) (X := Euclid n)).measurable
        (measurableSet_of_differentiableAt ℝ u))).1 hσ
  filter_upwards [hx] with x hx t
  have h := Submission.dorag_ha_rb_line_ftc n u L 0 x t 1 hu (by
    filter_upwards [hx] with σ hσ _
    rwa [zero_add])
  simpa only [zero_add, one_smul] using h

namespace Submission

/-- Dilation averaging on the boundary annulus `A_s = B₁(0) \ B_{1-s}(0)`: for measurable
`F ≥ 0` integrable on `B₁(0)` and `0 < s ≤ 1/2`,
`∫_{A_s} ∫_{1/2}^1 F(t x) dt dx ≤ 2^(n+1) s ∫_{B₁(0)} F`.  In lower integrals: Tonelli, the
substitution `y = t x` (Jacobian `t⁻ⁿ ≤ 2ⁿ`), Tonelli again, and for each `y` the admissible
`t` lie in `(‖y‖, ‖y‖ / (1 - s)]`, of length `≤ 2 s`, and only when `‖y‖ < 1`. -/
theorem dorag_ha_rb_dilation_average : ∀ (n : ℕ) (F : Euclid n → ℝ) (s : ℝ), Measurable F → (∀ y, 0 ≤ F y) → IntegrableOn F (ball (0 : Euclid n) 1) → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), (∫ t in (1 / 2 : ℝ)..1, F (t • x)) ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y := by
  intro n F s hF hF0 hFi hs hs2
  have hC0 : 0 ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y :=
    mul_nonneg (mul_nonneg (by positivity) hs.le) (integral_nonneg hF0)
  rw [← ENNReal.ofReal_le_ofReal_iff hC0]
  -- `ofReal` of a Bochner integral is at most the lower integral of `ofReal`
  have step1 : ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
      ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
    calc ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
        ≤ ‖∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          (∫ t in (1 / 2 : ℝ)..1, F (t • x))‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ‖∫ t in (1 / 2 : ℝ)..1, F (t • x)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
          refine lintegral_mono fun x => ?_
          rw [intervalIntegral.integral_of_le (by norm_num)]
          calc ‖∫ t in Ioc (1 / 2 : ℝ) 1, F (t • x)‖ₑ
              ≤ ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ‖F (t • x)‖ₑ := enorm_integral_le_lintegral_enorm _
            _ = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
              congr 1; ext t; exact Real.enorm_eq_ofReal (hF0 _)
  -- Tonelli
  have hmeas : Measurable (fun p : Euclid n × ℝ => ENNReal.ofReal (F (p.2 • p.1))) :=
    (hF.comp (measurable_snd.smul measurable_fst)).ennreal_ofReal
  have step2 : ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x))
      = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x)) :=
    lintegral_lintegral_swap hmeas.aemeasurable
  -- the region `{(t, y) : t (1 - s) ≤ ‖y‖ < t}` and the integrand on it
  obtain ⟨T, hT⟩ : ∃ T : Set (ℝ × Euclid n), T = {p | p.1 * (1 - s) ≤ ‖p.2‖ ∧ ‖p.2‖ < p.1} :=
    ⟨_, rfl⟩
  have hTm : MeasurableSet T := hT ▸
    (measurableSet_le (measurable_fst.mul_const _) measurable_snd.norm).inter
      (measurableSet_lt measurable_snd.norm measurable_fst)
  obtain ⟨H, hH⟩ : ∃ H : ℝ × Euclid n → ℝ≥0∞, H = T.indicator (fun p => ENNReal.ofReal (F p.2)) :=
    ⟨_, rfl⟩
  have hHm : Measurable H := hH ▸ (hF.comp measurable_snd).ennreal_ofReal.indicator hTm
  -- change of variables `y = t x`
  have step3 : ∀ t ∈ Ioc (1 / 2 : ℝ) 1,
      ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), ENNReal.ofReal (F (t • x))
        ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht.1
    have hmem : ∀ x : Euclid n,
        x ∈ ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s) ↔ (t, t • x) ∈ T := by
      intro x
      rw [hT]
      simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨mul_le_mul_of_nonneg_left h2 ht0.le, mul_lt_of_lt_one_right ht0 h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_mul_lt_mul_left (by linarith) ht0.le, le_of_mul_le_mul_left h1 ht0⟩
    have hind : (ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s)).indicator
        (fun x => ENNReal.ofReal (F (t • x))) = fun x => H (t, t • x) := by
      ext x
      rw [hH]
      by_cases hx : x ∈ ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s)
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hHt : Measurable fun y : Euclid n => H (t, y) := hHm.comp measurable_prodMk_left
    have hjac : ENNReal.ofReal |(t ^ Module.finrank ℝ (Euclid n))⁻¹| ≤ ENNReal.ofReal (2 ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity), ← inv_pow]
      have : t⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
      exact pow_le_pow_left₀ (by positivity) this n
    calc ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), ENNReal.ofReal (F (t • x))
        = ∫⁻ x, H (t, t • x) := by
          rw [← lintegral_indicator (measurableSet_ball.diff measurableSet_ball), hind]
      _ = ∫⁻ y, H (t, y) ∂(Measure.map (t • ·) volume) :=
          (lintegral_map hHt (measurable_const_smul t)).symm
      _ = ENNReal.ofReal |(t ^ Module.finrank ℝ (Euclid n))⁻¹| * ∫⁻ y, H (t, y) := by
          rw [Measure.map_addHaar_smul volume ht0.ne', lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) := by gcongr
  have step4 : ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x))
      ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := by
    calc ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ENNReal.ofReal (F (t • x))
        ≤ ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) :=
          setLIntegral_mono' measurableSet_Ioc step3
      _ = ENNReal.ofReal (2 ^ n) * ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ y, H (t, y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := by
          rw [lintegral_lintegral_swap (f := fun t y => H (t, y)) hHm.aemeasurable]
  -- length of the admissible parameter interval
  have step5 : ∀ y : Euclid n, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
      ≤ (ball (0 : Euclid n) 1).indicator
          (fun y => ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y)) y := by
    intro y
    have hSm : MeasurableSet {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} :=
      (measurableSet_le (measurable_id.mul_const _) measurable_const).inter
        (measurableSet_lt measurable_const measurable_id)
    have hHy : (fun t => H (t, y)) = {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t}.indicator
        (fun _ => ENNReal.ofReal (F y)) := by
      ext t
      rw [hH, hT]
      simp only [indicator, mem_ofPred_eq]
    rw [hHy, lintegral_indicator_const hSm, Measure.restrict_apply hSm]
    by_cases hy : ‖y‖ < 1
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), mul_comm]
      gcongr
      have h1s : 0 < 1 - s := by linarith
      calc volume ({t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} ∩ Ioc (1 / 2 : ℝ) 1)
          ≤ volume (Ioc ‖y‖ (‖y‖ / (1 - s))) := by
            apply measure_mono
            rintro t ⟨⟨h1, h2⟩, -⟩
            exact ⟨h2, (le_div_iff₀ h1s).2 h1⟩
        _ = ENNReal.ofReal (‖y‖ / (1 - s) - ‖y‖) := Real.volume_Ioc
        _ ≤ ENNReal.ofReal (2 * s) := by
            apply ENNReal.ofReal_le_ofReal
            rw [sub_le_iff_le_add, div_le_iff₀ h1s]
            nlinarith [mul_pos hs (show 0 < 2 - 2 * s - ‖y‖ by linarith)]
    · rw [indicator_of_notMem (by simpa using hy)]
      have hempty : {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} ∩ Ioc (1 / 2 : ℝ) 1 = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, h2⟩, -, h4⟩
        exact hy (h2.trans_le h4)
      rw [hempty, measure_empty, mul_zero]
  have step6 : ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
      ≤ ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y) := by
    calc ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
        ≤ ∫⁻ y, (ball (0 : Euclid n) 1).indicator
          (fun y => ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y)) y := lintegral_mono step5
      _ = ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y) :=
          lintegral_indicator measurableSet_ball _
      _ = ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hBeq : ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y)
      = ENNReal.ofReal (∫ y in ball (0 : Euclid n) 1, F y) :=
    (ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF0)).symm
  calc ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
      ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := step1
    _ = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x)) := step2
    _ ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := step4
    _ ≤ ENNReal.ofReal (2 ^ n) *
        (ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y)) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y) := by
        rw [hBeq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Submission

/-- **`L²` translation estimate** (cf. Gilbarg–Trudinger, Lemma 7.23; Evans, §5.8.2, Theorem 3),
for Rellich's theorem in the proof of the harmonic approximation lemma (Simon Ch. 5, 3.1, p. 114:
"by Rellich's theorem (see [GT01])").  If `u` is Lipschitz on `ℝⁿ` and `r + ‖w‖ ≤ R`, then
`∫_{B_r} (u(x) − u(x − w))² ≤ ‖w‖² ∫_{B_R} ‖Du‖²`: for a.e. `x`,
`u(x) − u(x − w) = ∫₀¹ Du(x − w + τw)w dτ`; Cauchy–Schwarz on `(0, 1]` bounds its square by
`‖w‖² ∫₀¹ ‖Du(x − w + τw)‖² dτ`; for `x ∈ B_r` the segment lies in `B_R`; integrating over `B_r`,
Fubini and translation invariance of Lebesgue measure give the bound. -/
theorem Submission.dorag_ha_rb_translation_l2 : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (w : Euclid n) (r R : ℝ), LipschitzWith L u → r + ‖w‖ ≤ R → ∫ x in ball (0 : Euclid n) r, (u x - u (x - w)) ^ 2 ≤ ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n u L w r R hu hrR
  -- Step 1: `G_R = 1_{B_R} ‖Du‖²`: measurable, `0 ≤ G_R ≤ L²`, integrable, `∫ G_R = ∫_{B_R} ‖Du‖²`
  obtain ⟨GR, hGR⟩ : ∃ GR : Euclid n → ℝ,
      GR = (ball (0 : Euclid n) R).indicator fun y => ‖fderiv ℝ u y‖ ^ 2 := ⟨_, rfl⟩
  have hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ L := fun y => norm_fderiv_le_of_lipschitz ℝ hu
  have hG_meas : Measurable fun y => ‖fderiv ℝ u y‖ ^ 2 := (measurable_fderiv ℝ u).norm.pow_const 2
  have hG_le : ∀ y, ‖fderiv ℝ u y‖ ^ 2 ≤ (L : ℝ) ^ 2 := fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (hDu y) 2
  have hGR_meas : Measurable GR := by
    rw [hGR]; exact hG_meas.indicator measurableSet_ball
  have hGR_nonneg : ∀ y, 0 ≤ GR y := fun y => by
    rw [hGR]; exact indicator_nonneg (fun y _ => sq_nonneg _) y
  have hGR_le : ∀ y, GR y ≤ (L : ℝ) ^ 2 := fun y => by
    by_cases hy : y ∈ ball (0 : Euclid n) R
    · rw [hGR, indicator_of_mem hy]; exact hG_le y
    · rw [hGR, indicator_of_notMem hy]; positivity
  have hGR_int : Integrable GR := by
    rw [hGR, integrable_indicator_iff measurableSet_ball]
    refine IntegrableOn.of_bound measure_ball_lt_top hG_meas.aestronglyMeasurable ((L : ℝ) ^ 2)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hG_le y
  have hGR_eq : ∫ y, GR y = ∫ y in ball (0 : Euclid n) R, ‖fderiv ℝ u y‖ ^ 2 := by
    rw [hGR]; exact integral_indicator measurableSet_ball
  -- Step 2: the segment FTC transported by `x ↦ x − w`: for a.e. `x`,
  -- `u x − u (x − w) = ∫_{(0, 1]} Du(x − w + τw)w dτ`
  have hftc : ∀ᵐ x : Euclid n, u x - u (x - w) =
      ∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w := by
    filter_upwards [(measurePreserving_sub_right volume w).quasiMeasurePreserving.ae
      (Submission.dorag_ha_rb_segment_ftc n u L w hu)] with x hx
    have hx' : u (x - w + w) - u (x - w) = ∫ τ in (0 : ℝ)..1, fderiv ℝ u (x - w + τ • w) w := hx
    rwa [sub_add_cancel, intervalIntegral.integral_of_le zero_le_one] at hx'
  -- Step 3: Cauchy–Schwarz on `(0, 1]`, via `0 ≤ ∫ (h − c)² = ∫ h² − c²` for `c = ∫ h`
  have hvol : volume.real (Ioc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  have hCS : ∀ h : ℝ → ℝ, IntegrableOn h (Ioc (0 : ℝ) 1) →
      IntegrableOn (fun τ => h τ ^ 2) (Ioc (0 : ℝ) 1) →
      (∫ τ in Ioc (0 : ℝ) 1, h τ) ^ 2 ≤ ∫ τ in Ioc (0 : ℝ) 1, h τ ^ 2 := by
    intro h hi hi2
    set c := ∫ τ in Ioc (0 : ℝ) 1, h τ with hc
    have i1 : Integrable (fun τ => 2 * c * h τ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      Integrable.const_mul hi _
    have i2 : Integrable (fun τ => h τ ^ 2 - 2 * c * h τ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      Integrable.sub hi2 i1
    have hexp : ∫ τ in Ioc (0 : ℝ) 1, (h τ - c) ^ 2 = (∫ τ in Ioc (0 : ℝ) 1, h τ ^ 2) - c ^ 2 := by
      have e : (fun τ => (h τ - c) ^ 2) = fun τ => (h τ ^ 2 - 2 * c * h τ) + c ^ 2 := by
        funext τ; ring
      rw [e, integral_add i2 (integrable_const _), integral_sub hi2 i1, integral_const_mul,
        setIntegral_const, hvol, one_smul, ← hc]
      ring
    have h0 : 0 ≤ ∫ τ in Ioc (0 : ℝ) 1, (h τ - c) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc fun τ _ => sq_nonneg _
    linarith
  -- pointwise bounds `|Du(y)w| ≤ ‖Du(y)‖‖w‖` and `(Du(y)w)² ≤ ‖w‖² ‖Du(y)‖²`
  have hDuw : ∀ y, |fderiv ℝ u y w| ≤ ‖fderiv ℝ u y‖ * ‖w‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact (fderiv ℝ u y).le_opNorm w
  have hsq : ∀ y, fderiv ℝ u y w ^ 2 ≤ ‖w‖ ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := fun y => by
    calc fderiv ℝ u y w ^ 2 = |fderiv ℝ u y w| ^ 2 := (sq_abs _).symm
      _ ≤ (‖fderiv ℝ u y‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hDuw y) 2
      _ = ‖w‖ ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := by ring
  -- Step 4: for `x ∈ B_r` and `τ ∈ (0, 1]`, `x − w + τw = x − (1 − τ)w ∈ B_R`
  have hseg : ∀ x ∈ ball (0 : Euclid n) r, ∀ τ ∈ Ioc (0 : ℝ) 1,
      x - w + τ • w ∈ ball (0 : Euclid n) R := by
    intro x hx τ hτ
    rw [mem_ball_zero_iff] at hx ⊢
    have e : x - w + τ • w = x - (1 - τ) • w := by rw [sub_smul, one_smul]; abel
    have h1 : (1 - τ) * ‖w‖ ≤ ‖w‖ :=
      mul_le_of_le_one_left (norm_nonneg w) (by linarith [hτ.1])
    rw [e]
    calc ‖x - (1 - τ) • w‖ ≤ ‖x‖ + ‖(1 - τ) • w‖ := norm_sub_le _ _
      _ = ‖x‖ + (1 - τ) * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hτ.2)]
      _ < r + ‖w‖ := by linarith
      _ ≤ R := hrR
  -- the integrand `F(x, τ) = G_R(x − w + τw)` on `B_r × (0, 1]`
  have hF_meas : Measurable fun p : Euclid n × ℝ => GR (p.1 - w + p.2 • w) :=
    hGR_meas.comp ((measurable_fst.sub_const w).add (measurable_snd.smul_const w))
  have hint01 : ∀ x : Euclid n, IntegrableOn (fun τ : ℝ => GR (x - w + τ • w)) (Ioc (0 : ℝ) 1) :=
    fun x => IntegrableOn.of_bound measure_Ioc_lt_top
      (hGR_meas.comp ((measurable_id.smul_const w).const_add (x - w))).aestronglyMeasurable
      ((L : ℝ) ^ 2) (ae_of_all _ fun τ => by
        rw [Real.norm_of_nonneg (hGR_nonneg _)]; exact hGR_le _)
  -- Steps 3 and 4: for a.e. `x ∈ B_r`, `(u x − u (x − w))² ≤ ‖w‖² ∫_{(0, 1]} F(x, τ) dτ`
  have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) r)), (u x - u (x - w)) ^ 2 ≤
      ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hftc] with x hx hxr
    have hm : Measurable fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w :=
      (measurable_fderiv_apply_const ℝ u w).comp ((measurable_id.smul_const w).const_add (x - w))
    have hi : IntegrableOn (fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w) (Ioc (0 : ℝ) 1) :=
      IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable ((L : ℝ) * ‖w‖)
        (ae_of_all _ fun τ => (Real.norm_eq_abs _).le.trans ((hDuw _).trans
          (mul_le_mul_of_nonneg_right (hDu _) (norm_nonneg w))))
    have hi2 : IntegrableOn (fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w ^ 2) (Ioc (0 : ℝ) 1) :=
      IntegrableOn.of_bound measure_Ioc_lt_top (hm.pow_const 2).aestronglyMeasurable
        (‖w‖ ^ 2 * (L : ℝ) ^ 2) (ae_of_all _ fun τ => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact (hsq _).trans (mul_le_mul_of_nonneg_left (hG_le _) (sq_nonneg _)))
    rw [hx]
    calc (∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w) ^ 2
        ≤ ∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w ^ 2 := hCS _ hi hi2
      _ ≤ ∫ τ in Ioc (0 : ℝ) 1, ‖w‖ ^ 2 * GR (x - w + τ • w) := by
          refine setIntegral_mono_on hi2 (Integrable.const_mul (hint01 x) _) measurableSet_Ioc
            fun τ hτ => ?_
          rw [hGR, indicator_of_mem (hseg x hxr τ hτ)]
          exact hsq _
      _ = ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) := integral_const_mul _ _
  -- Step 5: `F` is bounded on the finite measure space `B_r × (0, 1]`, hence integrable
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hF_int : Integrable (fun p : Euclid n × ℝ => GR (p.1 - w + p.2 • w))
      ((volume.restrict (ball (0 : Euclid n) r)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable ((L : ℝ) ^ 2)
      (ae_of_all _ fun p => by rw [Real.norm_of_nonneg (hGR_nonneg _)]; exact hGR_le _)
  have hΦ_int : Integrable (fun x => ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w))
      (volume.restrict (ball (0 : Euclid n) r)) := hF_int.integral_prod_left
  -- Step 6: Fubini and translation invariance: `∫_{B_r} ∫_{(0, 1]} F ≤ ∫ G_R`
  have hΦ_le : ∫ x in ball (0 : Euclid n) r, ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) ≤
      ∫ y, GR y := by
    rw [integral_integral_swap (f := fun x τ => GR (x - w + τ • w)) hF_int]
    calc ∫ τ in Ioc (0 : ℝ) 1, ∫ x in ball (0 : Euclid n) r, GR (x - w + τ • w)
        ≤ ∫ τ in Ioc (0 : ℝ) 1, ∫ y, GR y := by
          refine integral_mono_of_nonneg
            (ae_of_all _ fun τ => integral_nonneg fun x => hGR_nonneg _) (integrable_const _)
            (ae_of_all _ fun τ => ?_)
          have e : (fun x => GR (x - w + τ • w)) = fun x => GR (x + (τ • w - w)) := by
            funext x; congr 1; abel
          calc ∫ x in ball (0 : Euclid n) r, GR (x - w + τ • w) ≤ ∫ x, GR (x - w + τ • w) :=
                setIntegral_le_integral (by rw [e]; exact hGR_int.comp_add_right _)
                  (ae_of_all _ fun x => hGR_nonneg _)
            _ = ∫ y, GR y := by rw [e, integral_add_right_eq_self]
      _ = ∫ y, GR y := by rw [setIntegral_const, hvol, one_smul]
  -- Step 7: combine
  calc ∫ x in ball (0 : Euclid n) r, (u x - u (x - w)) ^ 2
      ≤ ∫ x in ball (0 : Euclid n) r, ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hΦ_int.const_mul _) hpt
    _ = ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) r, ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) :=
        integral_const_mul _ _
    _ ≤ ‖w‖ ^ 2 * ∫ y, GR y := mul_le_mul_of_nonneg_left hΦ_le (sq_nonneg _)
    _ = ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ u x‖ ^ 2 := by rw [hGR_eq]

/-- Step 3 (boundary layer) of the Rellich compactness argument on the unit ball, used for the
harmonic approximation in Allard's theorem (Simon 7.4.3): for `L`-Lipschitz `u : ℝⁿ → ℝ` and
`0 < s ≤ 1/2`, the annulus `A_s = B₁ \ B_{1-s}` satisfies
`∫_{A_s} u² ≤ 2^{n+3} s (∫_{B₁} u² + ∫_{B₁} ‖Du‖²)`.  Along a.e. ray
`u(x) - u(tx) = ∫_t^1 Du(σx)x dσ` (`Submission.dorag_ha_rb_ray_ftc`), so Cauchy–Schwarz on
`[1/2, 1]` gives `u(x)² ≤ 4 ∫_{1/2}^1 u(tx)² dt + ∫_{1/2}^1 ‖Du(tx)‖² dt` for `x ∈ B₁`;
integrate over `A_s` and average over dilations (`Submission.dorag_ha_rb_dilation_average`). -/
theorem Submission.dorag_ha_rb_boundary_layer : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (s : ℝ), LipschitzWith L u → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), u x ^ 2 ≤ 2 ^ (n + 3) * s * ((∫ x in ball (0 : Euclid n) 1, u x ^ 2) + ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) := by
  intro n u L s hu hs hs2
  set B : Set (Euclid n) := ball (0 : Euclid n) 1
  set A : Set (Euclid n) := B \ ball (0 : Euclid n) (1 - s)
  have hBm : MeasurableSet B := measurableSet_ball
  have hAm : MeasurableSet A := hBm.diff measurableSet_ball
  have hBfin : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hcont : Continuous u := hu.continuous
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- `‖Du‖ ≤ L` everywhere and `|u| ≤ |u 0| + L` on the closed unit ball
  have hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ L := fun y => norm_fderiv_le_of_lipschitz ℝ hu
  have hu_bd : ∀ y : Euclid n, ‖y‖ ≤ 1 → |u y| ≤ |u 0| + L := by
    intro y hy
    have h1 : dist (u y) (u 0) ≤ L * dist y 0 := hu.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at h1
    have h2 : (L : ℝ) * ‖y‖ ≤ L := mul_le_of_le_one_right L.coe_nonneg hy
    have h3 := abs_sub_abs_le_abs_sub (u y) (u 0)
    linarith
  have hsq_bd : ∀ y : Euclid n, ‖y‖ ≤ 1 → ‖u y ^ 2‖ ≤ (|u 0| + L) ^ 2 := fun y hy => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu_bd y hy) 2
  have hDsq_bd : ∀ y : Euclid n, ‖‖fderiv ℝ u y‖ ^ 2‖ ≤ (L : ℝ) ^ 2 := fun y => by
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDu y) 2
  -- a bounded measurable function is interval integrable
  have hii : ∀ (f : ℝ → ℝ) (C : ℝ) (a b : ℝ), Measurable f → (∀ σ, ‖f σ‖ ≤ C) →
      IntervalIntegrable f volume a b := fun f C a b hf hC =>
    (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
      (Eventually.of_forall hC)
  -- `u²` and `‖Du‖²` are measurable, nonnegative and integrable on `B`
  have hmF₁ : Measurable fun y => u y ^ 2 := (hcont.pow 2).measurable
  have hmF₂ : Measurable fun y => ‖fderiv ℝ u y‖ ^ 2 := by fun_prop
  have hiF₁ : IntegrableOn (fun y => u y ^ 2) B := by
    refine Measure.integrableOn_of_bounded (M := (|u 0| + L) ^ 2) hBfin
      hmF₁.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hBm] with y hy
    exact hsq_bd y (mem_ball_zero_iff.mp hy).le
  have hiF₂ : IntegrableOn (fun y => ‖fderiv ℝ u y‖ ^ 2) B :=
    Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2) hBfin hmF₂.aestronglyMeasurable
      (Eventually.of_forall hDsq_bd)
  -- the dilation averages `I₁(x) = ∫_{1/2}^1 u(tx)² dt` and `J(x) = ∫_{1/2}^1 ‖Du(tx)‖² dt`
  set I₁ : Euclid n → ℝ := fun x => ∫ t in (1 / 2 : ℝ)..1, u (t • x) ^ 2
  set J : Euclid n → ℝ := fun x => ∫ t in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (t • x)‖ ^ 2
  -- the pointwise estimate on a ray along which the fundamental theorem of calculus holds
  have key : ∀ x : Euclid n, ‖x‖ ≤ 1 →
      (∀ t : ℝ, u x - u (t • x) = ∫ σ in t..1, fderiv ℝ u (σ • x) x) →
      u x ^ 2 ≤ 4 * I₁ x + J x := by
    intro x hx hray
    have hgm : Measurable fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖ := by fun_prop
    have hgi : ∀ a b : ℝ, IntervalIntegrable (fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖) volume a b :=
      fun a b => hii _ L a b hgm fun σ => by rw [norm_norm]; exact hDu _
    have hg2i : IntervalIntegrable (fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖ ^ 2) volume (1 / 2) 1 :=
      hii _ ((L : ℝ) ^ 2) _ _ (hgm.pow_const 2) fun σ => hDsq_bd _
    set γ : ℝ := ∫ σ in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (σ • x)‖ with hγ
    -- (a) `|u(x) - u(tx)| ≤ ∫_t^1 ‖Du(σx)‖ dσ ≤ γ` for `t ∈ [1/2, 1]`
    have ha : ∀ t ∈ Icc (1 / 2 : ℝ) 1, |u x - u (t • x)| ≤ γ := by
      intro t ht
      rw [hray t, ← Real.norm_eq_abs]
      calc ‖∫ σ in t..1, fderiv ℝ u (σ • x) x‖
          ≤ ∫ σ in t..1, ‖fderiv ℝ u (σ • x)‖ :=
            intervalIntegral.norm_integral_le_of_norm_le ht.2
              (Eventually.of_forall fun σ _ => ((fderiv ℝ u (σ • x)).le_opNorm x).trans
                (mul_le_of_le_one_right (norm_nonneg _) hx)) (hgi t 1)
        _ ≤ γ := intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
              (Eventually.of_forall fun σ => norm_nonneg _) (hgi _ _)
    -- (b) `u(x)² ≤ 2u(tx)² + 2γ²`
    have hb : ∀ t ∈ Icc (1 / 2 : ℝ) 1, u x ^ 2 ≤ 2 * u (t • x) ^ 2 + 2 * γ ^ 2 := by
      intro t ht
      have h1 := abs_le.mp (ha t ht)
      have h2 : (u x - u (t • x)) ^ 2 ≤ γ ^ 2 := sq_le_sq' h1.1 h1.2
      linarith [sq_nonneg (2 * u (t • x) - u x)]
    -- (c) Cauchy–Schwarz on `[1/2, 1]`: integrating `4γ‖Du(σx)‖ ≤ ‖Du(σx)‖² + 4γ²` gives
    -- `4γ² ≤ J(x) + 2γ²`
    have hc : 2 * γ ^ 2 ≤ J x := by
      have h1 : ∫ σ in (1 / 2 : ℝ)..1, 4 * γ * ‖fderiv ℝ u (σ • x)‖ ≤
          ∫ σ in (1 / 2 : ℝ)..1, (‖fderiv ℝ u (σ • x)‖ ^ 2 + 4 * γ ^ 2) :=
        intervalIntegral.integral_mono_on hhalf ((hgi _ _).const_mul _)
          (hg2i.add intervalIntegrable_const)
          fun σ _ => by linarith [sq_nonneg (‖fderiv ℝ u (σ • x)‖ - 2 * γ)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hg2i
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, ← hγ] at h1
      have hJx : J x = ∫ σ in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (σ • x)‖ ^ 2 := rfl
      linarith
    -- (d) averaging (b) over `t ∈ [1/2, 1]` gives `u(x)² ≤ 4I₁(x) + 2γ²`
    have hd : (1 - 1 / 2 : ℝ) * u x ^ 2 ≤ 2 * I₁ x + (1 - 1 / 2) * (2 * γ ^ 2) := by
      have hcu : Continuous fun t : ℝ => u (t • x) ^ 2 := by fun_prop
      have h1 : ∫ t in (1 / 2 : ℝ)..1, u x ^ 2 ≤
          ∫ t in (1 / 2 : ℝ)..1, (2 * u (t • x) ^ 2 + 2 * γ ^ 2) :=
        intervalIntegral.integral_mono_on hhalf intervalIntegrable_const
          (((hcu.intervalIntegrable _ _).const_mul 2).add intervalIntegrable_const) hb
      rw [intervalIntegral.integral_const, intervalIntegral.integral_add
        ((hcu.intervalIntegrable _ _).const_mul 2) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
        smul_eq_mul] at h1
      have hI₁x : I₁ x = ∫ t in (1 / 2 : ℝ)..1, u (t • x) ^ 2 := rfl
      linarith
    linarith
  -- `I₁` and `J` are strongly measurable (Fubini) and bounded on `B`, hence integrable on `A`
  have hI₁m : StronglyMeasurable I₁ := by
    have h : Measurable fun p : Euclid n × ℝ => u (p.2 • p.1) ^ 2 := by fun_prop
    convert h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (1 / 2 : ℝ) 1))
      using 1
    funext x
    exact intervalIntegral.integral_of_le hhalf
  have hJm : StronglyMeasurable J := by
    have h : Measurable fun p : Euclid n × ℝ => ‖fderiv ℝ u (p.2 • p.1)‖ ^ 2 := by fun_prop
    convert h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (1 / 2 : ℝ) 1))
      using 1
    funext x
    exact intervalIntegral.integral_of_le hhalf
  have hI₁A : IntegrableOn I₁ A := by
    refine (Measure.integrableOn_of_bounded (M := (|u 0| + L) ^ 2 * |1 - 1 / 2|) hBfin
      hI₁m.aestronglyMeasurable ?_).mono_set sdiff_subset
    filter_upwards [ae_restrict_mem hBm] with x hx
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hsq_bd _ ?_
    rw [uIoc_of_le hhalf] at ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    nlinarith [ht.2, norm_nonneg x]
  have hJA : IntegrableOn J A :=
    (Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2 * |1 - 1 / 2|) hBfin
      hJm.aestronglyMeasurable (Eventually.of_forall fun x =>
        intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hDsq_bd _)).mono_set
      sdiff_subset
  -- integrate the pointwise estimate over `A`
  have hae : ∀ᵐ x ∂(volume.restrict A), u x ^ 2 ≤ 4 * I₁ x + J x := by
    filter_upwards [ae_restrict_mem hAm,
      ae_restrict_of_ae (Submission.dorag_ha_rb_ray_ftc n u L hu)] with x hxA hray
    exact key x (mem_ball_zero_iff.mp hxA.1).le hray
  have hmain : ∫ x in A, u x ^ 2 ≤ ∫ x in A, (4 * I₁ x + J x) :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg (u x))
      ((hI₁A.const_mul 4).add hJA) hae
  rw [integral_add (hI₁A.const_mul 4) hJA, integral_const_mul] at hmain
  -- average over dilations, then `4 · 2^{n+1} = 2^{n+3}`
  have hdil₁ : ∫ x in A, I₁ x ≤ 2 ^ (n + 1) * s * ∫ y in B, u y ^ 2 :=
    Submission.dorag_ha_rb_dilation_average n (fun y => u y ^ 2) s hmF₁ (fun y => sq_nonneg _)
      hiF₁ hs hs2
  have hdil₂ : ∫ x in A, J x ≤ 2 ^ (n + 1) * s * ∫ y in B, ‖fderiv ℝ u y‖ ^ 2 :=
    Submission.dorag_ha_rb_dilation_average n (fun y => ‖fderiv ℝ u y‖ ^ 2) s hmF₂
      (fun y => sq_nonneg _) hiF₂ hs hs2
  have hJB : 0 ≤ 2 ^ (n + 1) * s * ∫ y in B, ‖fderiv ℝ u y‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hs.le) (setIntegral_nonneg hBm fun y _ => sq_nonneg _)
  have h2 : (2 : ℝ) ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
  rw [h2]
  linarith
/-- **Interior `L²` error of a mollification** (step (2a) of the Rellich ball argument): if
`u : ℝⁿ → ℝ` is Lipschitz, `ρ ≥ 0` is continuous, vanishes where `‖z‖ ≥ 1` and has `∫ ρ = 1`,
and `0 < ε ≤ s`, then `v(x) = ∫ u(x − εz) ρ(z) dz` satisfies
`∫_{B_{1−s}} (u − v)² ≤ ε² ∫_{B_1} ‖Du‖²`.  Weighted Jensen gives
`(u(x) − v(x))² ≤ ∫ (u(x) − u(x − εz))² ρ(z) dz`; the integrand is dominated by `(Lε‖z‖)² ρ(z)`,
so Fubini swaps the integrals, and `Submission.dorag_ha_rb_translation_l2` (`r = 1 − s`, `R = 1`,
`w = εz`, `‖εz‖ ≤ ε ≤ s` where `ρ(z) ≠ 0`) bounds each inner integral by `ε² ∫_{B_1} ‖Du‖²`. -/
theorem Submission.dorag_ha_rb_mollify_l2 : ∀ (n : ℕ) (u ρ : Euclid n → ℝ) (L : NNReal) (ε s : ℝ), LipschitzWith L u → Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → 0 < ε → ε ≤ s → ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n u ρ L ε s hu hρc hρ0 hρ1 hρint hε hεs
  have huc : Continuous u := hu.continuous
  -- step 1: `ρ` vanishes off `closedBall 0 1`, so `g ρ` is integrable for every continuous `g`
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz =>
      hρ1 z (not_le.mp (by simpa using hz)).le
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  have hgρ : ∀ g : Euclid n → ℝ, Continuous g → Integrable fun z => g z * ρ z := fun g hg =>
    (hg.mul hρc).integrable_of_hasCompactSupport (hρcs.mul_left (f := g))
  -- step 2: `u(x) − v(x) = ∫ (u(x) − u(x − εz)) ρ(z) dz`, as `∫ ρ = 1`
  have hrep : ∀ x, u x - ∫ z, u (x - ε • z) * ρ z = ∫ z, (u x - u (x - ε • z)) * ρ z := by
    intro x
    simp_rw [sub_mul]
    rw [integral_sub (hρi.const_mul (u x)) (hgρ (fun z => u (x - ε • z)) (by fun_prop)),
      integral_const_mul, hρint, mul_one]
  -- step 3: weighted Jensen, `(∫ g ρ)² ≤ ∫ g² ρ`, from `0 ≤ ∫ (g − c)² ρ = ∫ g² ρ − c²`
  have hjensen : ∀ g : Euclid n → ℝ, Continuous g →
      (∫ z, g z * ρ z) ^ 2 ≤ ∫ z, g z ^ 2 * ρ z := by
    intro g hg
    obtain ⟨c, hc⟩ : ∃ c, ∫ z, g z * ρ z = c := ⟨_, rfl⟩
    have h0 : 0 ≤ ∫ z, (g z - c) ^ 2 * ρ z :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hρ0 z)
    have e : (fun z => (g z - c) ^ 2 * ρ z) =
        fun z => g z ^ 2 * ρ z - 2 * c * (g z * ρ z) + c ^ 2 * ρ z := by
      funext z
      ring
    have i1 : Integrable fun z => g z ^ 2 * ρ z := hgρ (fun z => g z ^ 2) (hg.pow 2)
    have i2 : Integrable fun z => 2 * c * (g z * ρ z) := (hgρ g hg).const_mul (2 * c)
    have i3 : Integrable fun z => g z ^ 2 * ρ z - 2 * c * (g z * ρ z) := i1.sub i2
    rw [e, integral_add i3 (hρi.const_mul (c ^ 2)), integral_sub i1 i2, integral_const_mul,
      integral_const_mul, hc, hρint] at h0
    rw [hc]
    nlinarith
  -- step 4: `|u(x) − u(x − εz)| ≤ Lε‖z‖`, so the integrand is dominated by `(Lε‖z‖)² ρ(z)`,
  -- which is integrable on `B_{1−s} × ℝⁿ`
  have hlip : ∀ x z : Euclid n, |u x - u (x - ε • z)| ≤ L * (ε * ‖z‖) := by
    intro x z
    have h := hu.dist_le_mul x (x - ε • z)
    rwa [Real.dist_eq, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg hε.le] at h
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) (1 - s))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (uncurry fun x z => (u x - u (x - ε • z)) ^ 2 * ρ z)
      ((volume.restrict (ball (0 : Euclid n) (1 - s))).prod volume) := by
    refine ((hgρ (fun z => (L * (ε * ‖z‖)) ^ 2) (by fun_prop)).comp_snd
      (volume.restrict (ball (0 : Euclid n) (1 - s)))).mono'
      (show Continuous fun p : Euclid n × Euclid n => (u p.1 - u (p.1 - ε • p.2)) ^ 2 * ρ p.2
        by fun_prop).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    show ‖(u p.1 - u (p.1 - ε • p.2)) ^ 2 * ρ p.2‖ ≤ (L * (ε * ‖p.2‖)) ^ 2 * ρ p.2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ0 _))]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.2 ((hlip _ _).trans (le_abs_self _))) (hρ0 _)
  -- step 5: Jensen pointwise, then Fubini; step 6: the translation estimate for `‖z‖ < 1`
  -- (`ρ(z) = 0` otherwise); step 7: `∫ ρ = 1`
  calc ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2
      ≤ ∫ x in ball (0 : Euclid n) (1 - s), ∫ z, (u x - u (x - ε • z)) ^ 2 * ρ z := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          hint.integral_prod_left (ae_of_all _ fun x => ?_)
        show (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ∫ z, (u x - u (x - ε • z)) ^ 2 * ρ z
        rw [hrep x]
        exact hjensen (fun z => u x - u (x - ε • z)) (by fun_prop)
    _ = ∫ z, ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2 * ρ z :=
        integral_integral_swap hint
    _ ≤ ∫ z, ε ^ 2 * (∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) * ρ z := by
        refine integral_mono hint.integral_prod_right (hρi.const_mul _) fun z => ?_
        show ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2 * ρ z ≤
          ε ^ 2 * (∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) * ρ z
        rw [integral_mul_const]
        rcases le_or_gt 1 ‖z‖ with hz | hz
        · simp [hρ1 z hz]
        have hw : ‖ε • z‖ ≤ ε := by
          rw [norm_smul, Real.norm_of_nonneg hε.le]
          exact mul_le_of_le_one_right hε.le hz.le
        refine mul_le_mul_of_nonneg_right ?_ (hρ0 z)
        calc ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2
            ≤ ‖ε • z‖ ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 :=
              Submission.dorag_ha_rb_translation_l2 n u L (ε • z) (1 - s) 1 hu (by linarith)
          _ ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw 2)
                (integral_nonneg fun x => sq_nonneg _)
    _ = ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
        rw [integral_const_mul, hρint, mul_one]
/-- **Uniform bounds for mollifications** (Rellich compactness step of the harmonic approximation
lemma, Simon 5.3.1–5.3.4).  Let `ρ` be continuous, zero for `‖z‖ ≥ 1`, bounded by `C` and
`C`-Lipschitz, `0 < ε ≤ s / 2`, and `v(x) = ∫ u(x − εz)ρ(z) dz`.  On `K = closedBall(0, 1 − s)`
we have `|v| ≤ ε⁻ⁿC∫_{B₁(0)}|u|` and `v` is `ε⁻⁽ⁿ⁺¹⁾C∫_{B₁(0)}|u|`-Lipschitz.  Substituting
`y = x − εz` gives `v(x) = ε⁻ⁿ∫ u(y)ρ(ε⁻¹(x − y)) dy`, and for `x ∈ K`, `‖y‖ ≥ 1` we have
`‖x − y‖ ≥ s ≥ ε`, so the integrand vanishes off `B₁(0)`; the bounds follow from `|ρ| ≤ C` and
`|ρ(ε⁻¹(x − y)) − ρ(ε⁻¹(x' − y))| ≤ Cε⁻¹‖x − x'‖`. -/
theorem Submission.dorag_ha_rb_mollify_bounds : ∀ (n : ℕ) (u ρ : Euclid n → ℝ) (C ε s : ℝ), Continuous u → Continuous ρ → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → (∀ z, |ρ z| ≤ C) → (∀ z z', |ρ z - ρ z'| ≤ C * ‖z - z'‖) → 0 < ε → ε ≤ s / 2 → (∀ x ∈ closedBall (0 : Euclid n) (1 - s), |∫ z, u (x - ε • z) * ρ z| ≤ (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u y|) ∧ ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ x' ∈ closedBall (0 : Euclid n) (1 - s), |(∫ z, u (x - ε • z) * ρ z) - ∫ z, u (x' - ε • z) * ρ z| ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u y| := by
  intro n u ρ C ε s hu hρ hsupp hbd hlip hε hεs
  have hεn : 0 < (ε ^ n)⁻¹ := inv_pos.mpr (pow_pos hε n)
  -- (1) support: for `x ∈ K` and `y ∉ B₁(0)`, `‖ε⁻¹(x − y)‖ ≥ 1`, so `ρ(ε⁻¹(x − y)) = 0`
  have hzero : ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ y ∉ ball (0 : Euclid n) 1,
      ρ (ε⁻¹ • (x - y)) = 0 := by
    intro x hx y hy
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_ball_zero_iff, not_lt] at hy
    apply hsupp
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le), one_le_inv_mul₀ hε]
    calc ε ≤ ‖y‖ - ‖x‖ := by linarith
      _ ≤ ‖y - x‖ := norm_sub_norm_le _ _
      _ = ‖x - y‖ := norm_sub_rev _ _
  -- (2) continuous functions are integrable on `B₁(0)`
  have hint : ∀ f : Euclid n → ℝ, Continuous f → IntegrableOn f (ball (0 : Euclid n) 1) :=
    fun f hf => (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  have hcf : ∀ x : Euclid n, Continuous fun y => u y * ρ (ε⁻¹ • (x - y)) := fun x =>
    hu.mul (hρ.comp ((continuous_const.sub continuous_id).const_smul ε⁻¹))
  -- (3) change of variables `y = x − εz`: `v(x) = ε⁻ⁿ∫_{B₁(0)} u(y)ρ(ε⁻¹(x − y)) dy`
  have hcov : ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∫ z, u (x - ε • z) * ρ z =
      (ε ^ n)⁻¹ * ∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y)) := by
    intro x hx
    have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euclid n))
      (fun w => u (x - w) * ρ (ε⁻¹ • w)) ε (hR := hε.le)
    simp only [inv_smul_smul₀ hε.ne', finrank_euclideanSpace_fin, smul_eq_mul] at h1
    rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [hzero x hx y hy, mul_zero]]
    congr 1
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self (fun y => u y * ρ (ε⁻¹ • (x - y))) volume x
  refine ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩
  -- (4) sup bound from `|ρ| ≤ C`
  · have hb : |∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y))| ≤
        ∫ y in ball (0 : Euclid n) 1, |u y| * C := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hint _ hu.abs).mul_const C)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hbd _) (abs_nonneg _)
    rw [integral_mul_const] at hb
    rw [hcov x hx, abs_mul, abs_of_pos hεn]
    calc (ε ^ n)⁻¹ * |∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y))|
        ≤ (ε ^ n)⁻¹ * ((∫ y in ball (0 : Euclid n) 1, |u y|) * C) :=
          mul_le_mul_of_nonneg_left hb hεn.le
      _ = (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u y| := by ring
  -- (5) Lipschitz bound from `|ρ(ε⁻¹(x − y)) − ρ(ε⁻¹(x' − y))| ≤ Cε⁻¹‖x − x'‖`
  · have hb : |∫ y in ball (0 : Euclid n) 1,
          (u y * ρ (ε⁻¹ • (x - y)) - u y * ρ (ε⁻¹ • (x' - y)))| ≤
        ∫ y in ball (0 : Euclid n) 1, |u y| * (C * ε⁻¹ * ‖x - x'‖) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hint _ hu.abs).mul_const _)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |ρ (ε⁻¹ • (x - y)) - ρ (ε⁻¹ • (x' - y))|
          ≤ C * ‖ε⁻¹ • (x - y) - ε⁻¹ • (x' - y)‖ := hlip _ _
        _ = C * ε⁻¹ * ‖x - x'‖ := by
          rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.mpr hε.le), mul_assoc]
    rw [integral_mul_const, integral_sub (hint _ (hcf x)) (hint _ (hcf x'))] at hb
    rw [hcov x hx, hcov x' hx', ← mul_sub, abs_mul, abs_of_pos hεn]
    calc (ε ^ n)⁻¹ * |(∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y))) -
          ∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x' - y))|
        ≤ (ε ^ n)⁻¹ * ((∫ y in ball (0 : Euclid n) 1, |u y|) * (C * ε⁻¹ * ‖x - x'‖)) :=
          mul_le_mul_of_nonneg_left hb hεn.le
      _ = (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u y| := by
          rw [pow_succ, mul_inv]
          ring
/-- **Mollifier kernel** for the Rellich compactness step of the harmonic approximation lemma
(Simon 5.3.1–5.3.4): a continuous probability density `ρ ≥ 0` on `ℝⁿ`, vanishing for `‖z‖ ≥ 1`,
bounded by `C` and `C`-Lipschitz.  Take the tent `ρ₀(z) = (1 − ‖z‖)₊`, which is continuous, `0 ≤ ρ₀ ≤ 1`, zero off
`B_1(0)` and `1`-Lipschitz; `c₀ = ∫ ρ₀ > 0` since `ρ₀` is compactly supported, nonnegative and
`ρ₀(0) = 1`; then `ρ = c₀⁻¹ρ₀` and `C = c₀⁻¹`. -/
theorem Submission.dorag_ha_rb_kernel : ∀ (n : ℕ), ∃ (ρ : Euclid n → ℝ) (C : ℝ), Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧ (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) ∧ ∫ z, ρ z = 1 ∧ (∀ z, |ρ z| ≤ C) ∧ ∀ z z', |ρ z - ρ z'| ≤ C * ‖z - z'‖ := by
  intro n
  -- the tent `ρ₀(z) = (1 − ‖z‖)₊`: continuous, `0 ≤ ρ₀ ≤ 1`, zero off `B_1(0)`, `1`-Lipschitz
  set ρ₀ : Euclid n → ℝ := fun z => max (1 - ‖z‖) 0 with hρ₀
  have hcont : Continuous ρ₀ := (continuous_const.sub continuous_norm).max continuous_const
  have hnonneg : ∀ z, 0 ≤ ρ₀ z := fun z => le_max_right _ _
  have hle : ∀ z, ρ₀ z ≤ 1 := fun z => max_le (by linarith [norm_nonneg z]) zero_le_one
  have hvanish : ∀ z : Euclid n, 1 ≤ ‖z‖ → ρ₀ z = 0 := fun z hz => max_eq_right (by linarith)
  have hlip : ∀ z z', |ρ₀ z - ρ₀ z'| ≤ ‖z - z'‖ := fun z z' =>
    calc |ρ₀ z - ρ₀ z'| ≤ |(1 - ‖z‖) - (1 - ‖z'‖)| := abs_max_sub_max_le_abs _ _ _
      _ = |‖z'‖ - ‖z‖| := by ring_nf
      _ ≤ ‖z' - z‖ := abs_norm_sub_norm_le _ _
      _ = ‖z - z'‖ := norm_sub_rev _ _
  -- `c₀ = ∫ ρ₀ > 0`: `ρ₀` is continuous, compactly supported, nonnegative and `ρ₀(0) = 1`
  have hsupp : HasCompactSupport ρ₀ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz =>
      hvanish z (by simpa using (not_le.mp (by simpa using hz)).le)
  have hpos : 0 < ∫ z, ρ₀ z :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg (x := 0) (by simp [hρ₀])
  -- `ρ = c₀⁻¹ ρ₀` and `C = c₀⁻¹`
  have hC : 0 ≤ (∫ z, ρ₀ z)⁻¹ := inv_nonneg.mpr hpos.le
  refine ⟨fun z => (∫ z, ρ₀ z)⁻¹ * ρ₀ z, (∫ z, ρ₀ z)⁻¹, continuous_const.mul hcont,
    fun z => mul_nonneg hC (hnonneg z), fun z hz => by simp [hvanish z hz], ?_, fun z => ?_,
    fun z z' => ?_⟩
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · rw [abs_of_nonneg (mul_nonneg hC (hnonneg z))]
    exact mul_le_of_le_one_right hC (hle z)
  · rw [← mul_sub, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (hlip z z') hC
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
/-- **Rellich on `B̆₁(0)`, total boundedness** (parent proof, step 4).  Let the `uⱼ` be Lipschitz
on `ℝⁿ` with `∫_B uⱼ² ≤ M` and `∫_B ‖Duⱼ‖² ≤ M`, `B = B̆₁(0)`.  Then for every `η > 0` finitely
many `uₖ` form an `η`-net for `∫_B (uⱼ − uₖ)²`.  Choose `s`, `ε ≤ s/2`, `δ` with `2^{n+6}sM`,
`6ε²M`, `3δ²Lⁿ(B) ≤ η/3` and mollify, `vⱼ(x) = ∫ uⱼ(x − εz)ρ(z) dz` with the kernel of
`dorag_ha_rb_kernel`.  As `∫_B |uⱼ| ≤ (Lⁿ(B) + M)/2` (`|a| ≤ (1 + a²)/2`), the `vⱼ` are uniformly
bounded and uniformly Lipschitz on `B_{1−s}(0)` (`dorag_ha_rb_mollify_bounds`), so finitely many
`vₖ` are a `δ`-net in the sup norm there (`dorag_ha_rb_sup_net`).  On `B \ B̆_{1−s}(0)` use
`(a − b)² ≤ 2a² + 2b²` and `dorag_ha_rb_boundary_layer`; on `B̆_{1−s}(0)` use
`(a + b + c)² ≤ 3(a² + b² + c²)` and `dorag_ha_rb_mollify_l2`. -/
theorem Submission.dorag_ha_rb_total_bounded : ∀ (n : ℕ) (M : ℝ) (u : ℕ → Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) 1, u j x ^ 2 ≤ M) → (∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ M) → ∀ η : ℝ, 0 < η → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∫ x in ball (0 : Euclid n) 1, (u j x - u k x) ^ 2 ≤ η := by
  intro n M u hLip hu hDu η hη
  choose L hL using hLip
  have hc : ∀ j, Continuous (u j) := fun j => (hL j).continuous
  -- a function continuous on `B_r(0)` is integrable on `B̆_r(0)`
  have hint : ∀ (f : Euclid n → ℝ) (r : ℝ), ContinuousOn f (closedBall 0 r) →
      IntegrableOn f (ball 0 r) := fun f r hf =>
    (hf.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hM : 0 ≤ M := (integral_nonneg fun x => sq_nonneg (u 0 x)).trans (hu 0)
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = volume.real (ball (0 : Euclid n) 1) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hω]; exact measureReal_nonneg
  -- Step 1: the constants `s`, `ε ≤ s/2` and `δ`
  obtain ⟨s, hs0, hs1, hsη⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ s * (3 * 2 ^ (n + 6) * (M + 1)) ≤ η :=
    ⟨min (1 / 2) (η / (3 * 2 ^ (n + 6) * (M + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  obtain ⟨ε, hε0, hεs2, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ s / 2 ∧ ε * (18 * (M + 1)) ≤ η :=
    ⟨min (s / 2) (η / (18 * (M + 1))), lt_min (by positivity) (by positivity), min_le_left _ _,
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  obtain ⟨δ, hδ0, hδ1, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ * (9 * (ω + 1)) ≤ η :=
    ⟨min 1 (η / (9 * (ω + 1))), lt_min one_pos (by positivity), min_le_left _ _,
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  have hεs : ε ≤ s := by linarith
  have hε2 : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε0.le (by linarith)
  have hδ2 : δ ^ 2 ≤ δ := by rw [sq]; exact mul_le_of_le_one_left hδ0.le hδ1
  -- Step 2: the mollifications `vⱼ(x) = ∫ uⱼ(x − εz)ρ(z) dz`
  obtain ⟨ρ, C, hρc, hρ0, hρ1, hρint, hρC, hρL⟩ := Submission.dorag_ha_rb_kernel n
  have hC : 0 ≤ C := (abs_nonneg _).trans (hρC 0)
  set v : ℕ → Euclid n → ℝ := fun j x => ∫ z, u j (x - ε • z) * ρ z
  -- Step 3: `∫_B |uⱼ| ≤ (Lⁿ(B) + M)/2`
  have hL1 : ∀ j, ∫ x in ball (0 : Euclid n) 1, |u j x| ≤ (ω + M) / 2 := by
    intro j
    have i1 : IntegrableOn (fun _ => (1 / 2 : ℝ)) (ball (0 : Euclid n) 1) := integrableOn_const
    have i2 : IntegrableOn (fun x => u j x ^ 2 / 2) (ball (0 : Euclid n) 1) :=
      (hint _ 1 ((hc j).pow 2).continuousOn).div_const 2
    have i12 : IntegrableOn (fun x => 1 / 2 + u j x ^ 2 / 2) (ball (0 : Euclid n) 1) := i1.add i2
    calc ∫ x in ball (0 : Euclid n) 1, |u j x|
        ≤ ∫ x in ball (0 : Euclid n) 1, (1 / 2 + u j x ^ 2 / 2) :=
          setIntegral_mono_on (hint _ 1 (hc j).abs.continuousOn) i12 measurableSet_ball
            fun x _ => by linarith [sq_abs (u j x), sq_nonneg (|u j x| - 1)]
      _ = ω / 2 + (∫ x in ball (0 : Euclid n) 1, u j x ^ 2) / 2 := by
          rw [integral_add i1 i2, setIntegral_const, integral_div, smul_eq_mul, hω]
          ring
      _ ≤ (ω + M) / 2 := by linarith [hu j]
  -- Step 4: the `vⱼ` are uniformly bounded and uniformly Lipschitz on `B_{1−s}(0)`
  set D : ℝ := (ε ^ n)⁻¹ * C * ((ω + M) / 2) + (ε ^ (n + 1))⁻¹ * C * ((ω + M) / 2)
  have hvb : ∀ j, ∀ x ∈ closedBall (0 : Euclid n) (1 - s), |v j x| ≤ D := by
    intro j x hx
    calc |v j x| ≤ (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u j y| :=
          (Submission.dorag_ha_rb_mollify_bounds n (u j) ρ C ε s (hc j) hρc hρ1 hρC hρL hε0
            hεs2).1 x hx
      _ ≤ (ε ^ n)⁻¹ * C * ((ω + M) / 2) := mul_le_mul_of_nonneg_left (hL1 j) (by positivity)
      _ ≤ D := le_add_of_nonneg_right (by positivity)
  have hvl : ∀ j, ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ x' ∈ closedBall (0 : Euclid n) (1 - s),
      |v j x - v j x'| ≤ D * ‖x - x'‖ := by
    intro j x hx x' hx'
    calc |v j x - v j x'|
        ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u j y| :=
          (Submission.dorag_ha_rb_mollify_bounds n (u j) ρ C ε s (hc j) hρc hρ1 hρC hρL hε0
            hεs2).2 x hx x' hx'
      _ ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ((ω + M) / 2) :=
          mul_le_mul_of_nonneg_left (hL1 j) (by positivity)
      _ = (ε ^ (n + 1))⁻¹ * C * ((ω + M) / 2) * ‖x - x'‖ := by ring
      _ ≤ D * ‖x - x'‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (norm_nonneg _)
  have hvc : ∀ j, ContinuousOn (v j) (closedBall (0 : Euclid n) (1 - s)) := by
    intro j
    refine (LipschitzOnWith.of_dist_le' (f := v j) (s := closedBall (0 : Euclid n) (1 - s))
      (K := D) fun x hx x' hx' => ?_).continuousOn
    rw [Real.dist_eq, dist_eq_norm]
    exact hvl j x hx x' hx'
  -- Step 5: finitely many `vₖ` form a `δ`-net in the sup norm on `B_{1−s}(0)`
  obtain ⟨S, hS⟩ := Submission.dorag_ha_rb_sup_net n (closedBall (0 : Euclid n) (1 - s)) v D
    (isCompact_closedBall 0 (1 - s)) hvb hvl δ hδ0
  refine ⟨S, fun j => ?_⟩
  obtain ⟨k, hkS, hjk⟩ := hS j
  refine ⟨k, hkS, ?_⟩
  -- Step 6: split `B` into `B̆_{1−s}(0)` and the annulus `B \ B̆_{1−s}(0)`
  have hsub : ball (0 : Euclid n) (1 - s) ⊆ ball 0 1 := ball_subset_ball (by linarith)
  have ijk : IntegrableOn (fun x => (u j x - u k x) ^ 2) (ball (0 : Euclid n) 1) :=
    hint _ 1 (((hc j).sub (hc k)).pow 2).continuousOn
  have hsplit := setIntegral_sdiff measurableSet_ball ijk hsub
  -- Step 7: the annulus, by `dorag_ha_rb_boundary_layer`
  have hann : ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), (u j x - u k x) ^ 2 ≤ η / 3 := by
    have iA : ∀ i, IntegrableOn (fun x => 2 * u i x ^ 2) (ball (0 : Euclid n) 1 \ ball 0 (1 - s)) :=
      fun i => ((hint _ 1 ((hc i).pow 2).continuousOn).mono_set sdiff_subset).const_mul 2
    have iAA : IntegrableOn (fun x => 2 * u j x ^ 2 + 2 * u k x ^ 2)
        (ball (0 : Euclid n) 1 \ ball 0 (1 - s)) := (iA j).add (iA k)
    have hbl : ∀ i, ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), u i x ^ 2 ≤
        2 ^ (n + 3) * s * (M + M) := fun i =>
      (Submission.dorag_ha_rb_boundary_layer n (u i) (L i) s (hL i) hs0 hs1).trans
        (mul_le_mul_of_nonneg_left (add_le_add (hu i) (hDu i)) (by positivity))
    calc ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), (u j x - u k x) ^ 2
        ≤ ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), (2 * u j x ^ 2 + 2 * u k x ^ 2) :=
          setIntegral_mono_on (ijk.mono_set sdiff_subset) iAA
            (measurableSet_ball.diff measurableSet_ball) fun x _ => by
              linarith [sq_nonneg (u j x + u k x)]
      _ = 2 * (∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), u j x ^ 2) +
            2 * ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), u k x ^ 2 := by
          rw [integral_add (iA j) (iA k), integral_const_mul, integral_const_mul]
      _ ≤ 2 * (2 ^ (n + 3) * s * (M + M)) + 2 * (2 ^ (n + 3) * s * (M + M)) := by
          linarith [hbl j, hbl k]
      _ = 2 ^ (n + 6) * s * M := by ring
      _ ≤ η / 3 := by
          have : 0 < 2 ^ (n + 6) * s := by positivity
          linarith
  -- Step 8: the interior, by `dorag_ha_rb_mollify_l2` and the sup-net
  have hin : ∫ x in ball (0 : Euclid n) (1 - s), (u j x - u k x) ^ 2 ≤ 2 * η / 3 := by
    have i1 : ∀ i, IntegrableOn (fun x => 3 * (u i x - v i x) ^ 2) (ball (0 : Euclid n) (1 - s)) :=
      fun i => (hint _ _ (((hc i).continuousOn.sub (hvc i)).pow 2)).const_mul 3
    have i2 : IntegrableOn (fun _ => 3 * δ ^ 2) (ball (0 : Euclid n) (1 - s)) := integrableOn_const
    have i12 : IntegrableOn (fun x => 3 * (u j x - v j x) ^ 2 + 3 * δ ^ 2)
        (ball (0 : Euclid n) (1 - s)) := (i1 j).add i2
    have i123 : IntegrableOn
        (fun x => 3 * (u j x - v j x) ^ 2 + 3 * δ ^ 2 + 3 * (u k x - v k x) ^ 2)
        (ball (0 : Euclid n) (1 - s)) := i12.add (i1 k)
    have hl2 : ∀ i, ∫ x in ball (0 : Euclid n) (1 - s), (u i x - v i x) ^ 2 ≤ ε ^ 2 * M := fun i =>
      (Submission.dorag_ha_rb_mollify_l2 n (u i) ρ (L i) ε s (hL i) hρc hρ0 hρ1 hρint hε0
        hεs).trans (mul_le_mul_of_nonneg_left (hDu i) (sq_nonneg ε))
    have hvol : volume.real (ball (0 : Euclid n) (1 - s)) ≤ ω := by
      rw [hω]; exact measureReal_mono hsub
    calc ∫ x in ball (0 : Euclid n) (1 - s), (u j x - u k x) ^ 2
        ≤ ∫ x in ball (0 : Euclid n) (1 - s),
            (3 * (u j x - v j x) ^ 2 + 3 * δ ^ 2 + 3 * (u k x - v k x) ^ 2) := by
          refine setIntegral_mono_on (ijk.mono_set hsub) i123 measurableSet_ball fun x hx => ?_
          have h1 := abs_le.mp (hjk x (ball_subset_closedBall hx))
          have h2 : (v j x - v k x) ^ 2 ≤ δ ^ 2 := sq_le_sq' h1.1 h1.2
          linarith [sq_nonneg (u j x - v j x - (v j x - v k x)),
            sq_nonneg (v j x - v k x - (v k x - u k x)),
            sq_nonneg (u j x - v j x - (v k x - u k x))]
      _ = 3 * (∫ x in ball (0 : Euclid n) (1 - s), (u j x - v j x) ^ 2) +
            3 * δ ^ 2 * volume.real (ball (0 : Euclid n) (1 - s)) +
            3 * ∫ x in ball (0 : Euclid n) (1 - s), (u k x - v k x) ^ 2 := by
          rw [integral_add i12 (i1 k), integral_add (i1 j) i2, setIntegral_const,
            integral_const_mul, integral_const_mul, smul_eq_mul]
          ring
      _ ≤ 3 * (ε ^ 2 * M) + 3 * δ ^ 2 * ω + 3 * (ε ^ 2 * M) := by
          have := mul_le_mul_of_nonneg_left hvol (by positivity : (0 : ℝ) ≤ 3 * δ ^ 2)
          linarith [hl2 j, hl2 k]
      _ ≤ 2 * η / 3 := by
          linarith [mul_le_mul_of_nonneg_right hε2 hM, mul_le_mul_of_nonneg_right hδ2 hω0]
  linarith
/-- Extraction step of the Rellich argument (step 5 of its proof).  If `f j ∈ L²(μ)` and for every
`η > 0` finitely many `f k` form an `η`-net for `∫ (f j - f k) ^ 2`, then a subsequence converges
in `L²(μ)`: the classes of the `f j` form a totally bounded set in the complete space `L²(μ)`. -/
theorem Submission.dorag_ha_rb_l2_subseq : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ), (∀ j, MemLp (f j) 2 μ) → (∀ η : ℝ, 0 < η → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∫ x, (f j x - f k x) ^ 2 ∂μ ≤ η) → ∃ (φ : ℕ → ℕ) (W : α → ℝ), StrictMono φ ∧ MemLp W 2 μ ∧ Tendsto (fun j => ∫ x, (f (φ j) x - W x) ^ 2 ∂μ) atTop (𝓝 0) := by
  intro α _ μ f hf hnet
  -- Step 2: for `h ∈ L²`, `‖toLp h‖ ^ 2 = ∫ h ^ 2`
  have hnorm : ∀ (h : α → ℝ) (hh : MemLp h 2 μ), ‖hh.toLp h‖ ^ 2 = ∫ x, h x ^ 2 ∂μ := by
    intro h hh
    have h0 : 0 ≤ ∫ x, h x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (h x)
    rw [Lp.norm_toLp, hh.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  -- Step 1: the classes `F j ∈ L²`, with `dist (F j) (F k) ^ 2 = ∫ (f j - f k) ^ 2`
  set F : ℕ → Lp ℝ 2 μ := fun j => (hf j).toLp (f j) with hF
  have hdist : ∀ j k, dist (F j) (F k) ^ 2 = ∫ x, (f j x - f k x) ^ 2 ∂μ := by
    intro j k
    rw [dist_eq_norm, hF, ← MemLp.toLp_sub (hf j) (hf k)]
    exact hnorm _ _
  -- Step 3: the hypothesis with `η = ε ^ 2 / 2` gives a finite `ε`-net of `range F`
  have htb : TotallyBounded (range F) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨S, hS⟩ := hnet (ε ^ 2 / 2) (by positivity)
    refine ⟨F '' (S : Set ℕ), S.finite_toSet.image F, ?_⟩
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk, hjk⟩ := hS j
    refine mem_iUnion₂.2 ⟨F k, mem_image_of_mem F hk, ?_⟩
    rw [mem_ball]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [hdist]
    have : 0 < ε ^ 2 := by positivity
    linarith
  -- Steps 4–5: `closure (range F)` is compact in the complete space `L²`, so a subsequence
  -- `F ∘ φ` converges to some `G`
  obtain ⟨G, -, φ, hφ, hlim⟩ :=
    (htb.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
      (x := F) fun j => subset_closure (mem_range_self j)
  -- Step 6: `W = ⇑G`, and `∫ (f (φ j) - W) ^ 2 = ‖F (φ j) - G‖ ^ 2 → 0`
  refine ⟨φ, G, hφ, Lp.memLp G, ?_⟩
  have heq : ∀ j, ‖F (φ j) - G‖ ^ 2 = ∫ x, (f (φ j) x - G x) ^ 2 ∂μ := by
    intro j
    have := hnorm _ ((hf (φ j)).sub (Lp.memLp G))
    rw [MemLp.toLp_sub (hf (φ j)) (Lp.memLp G), Lp.toLp_coeFn] at this
    exact this
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 hlim).pow 2
  rw [zero_pow two_ne_zero] at h2
  exact h2.congr heq

/-- **Rellich compactness in `L²(B̆₁(0))` for Lipschitz functions** (Gilbarg–Trudinger Thm 7.22,
Evans §5.7 Thm 1; used in Simon Ch. 5, Lemma 3.1).  If the `uⱼ : ℝⁿ → ℝ` are Lipschitz with
`∫_B uⱼ² ≤ M` and `∫_B ‖Duⱼ‖² ≤ M`, `B = B̆₁(0)`, then a subsequence converges in `L²(B)` to some
`W ∈ L²(B)`.  Each `uⱼ` is continuous and bounded on `B`, which has finite measure, so
`uⱼ ∈ L²(B)`.  `dorag_ha_rb_total_bounded` gives finite `L²(B)`-nets of `(uⱼ)` of every radius,
and `dorag_ha_rb_l2_subseq` extracts the convergent subsequence in the complete space `L²(B)`.
The hypothesis `n ≥ 1` is not needed. -/
theorem Submission.dorag_ha_rellich_ball : ∀ (n : ℕ) (M : ℝ) (u : ℕ → Euclid n → ℝ), 0 < n → (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) 1, u j x ^ 2 ≤ M) → (∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ M) → ∃ (φ : ℕ → ℕ) (W : Euclid n → ℝ), StrictMono φ ∧ MemLp W 2 (volume.restrict (ball (0 : Euclid n) 1)) ∧ Tendsto (fun j => ∫ x in ball (0 : Euclid n) 1, (u (φ j) x - W x) ^ 2) atTop (𝓝 0) := by
  intro n M u _hn hLip hu hDu
  -- step 1: `B̆₁(0)` has finite Lebesgue measure
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_ne_top
  -- step 2: an `L`-Lipschitz `uⱼ` is continuous with `|uⱼ| ≤ |uⱼ(0)| + L` on `B̆₁(0)`, so `uⱼ ∈ L²`
  have hmem : ∀ j, MemLp (u j) 2 (volume.restrict (ball (0 : Euclid n) 1)) := by
    intro j
    obtain ⟨L, hL⟩ := hLip j
    refine MemLp.of_bound hL.continuous.aestronglyMeasurable (|u j 0| + L) ?_
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    have h1 : |u j x - u j 0| ≤ L * ‖x‖ := by
      simpa only [Real.dist_eq, dist_zero_right] using hL.dist_le_mul x 0
    have h2 : (L : ℝ) * ‖x‖ ≤ L := mul_le_of_le_one_right L.coe_nonneg (mem_ball_zero_iff.1 hx).le
    rw [Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (u j x) (u j 0)]
  -- step 3: finite `L²(B̆₁(0))`-nets of `(uⱼ)` and extraction of a convergent subsequence
  exact Submission.dorag_ha_rb_l2_subseq (Euclid n) (volume.restrict (ball (0 : Euclid n) 1)) u
    hmem (Submission.dorag_ha_rb_total_bounded n M u hLip hu hDu)
/-- **Gradient length of a linear functional on `ℝⁿ`** (the identities `‖Du‖ = |∇u|` and
`|∇u · Φ| ≤ ‖Du‖ |Φ|` behind the energy bound in Simon Ch. 5, 3.1, p. 114):
`‖L‖² = Σᵢ L(eᵢ)²` and `|Σᵢ L(eᵢ) aᵢ| ≤ ‖L‖ √(Σᵢ aᵢ²)`.  The Riesz representative
`g = toDual⁻¹ L` has `‖g‖ = ‖L‖` and coordinates `gᵢ = ⟪eᵢ, g⟫ = L(eᵢ)`; the bound is the
finite Cauchy–Schwarz inequality applied to `a` and to `-a`. -/
theorem Submission.dorag_ha_lsc_grad_norm_sq : ∀ (n : ℕ) (L : Euclid n →L[ℝ] ℝ), ‖L‖ ^ 2 = ∑ i : Fin n, L (EuclideanSpace.single i (1 : ℝ)) ^ 2 ∧ ∀ a : Fin n → ℝ, |∑ i : Fin n, L (EuclideanSpace.single i (1 : ℝ)) * a i| ≤ ‖L‖ * Real.sqrt (∑ i : Fin n, a i ^ 2) := by
  intro n L
  -- the Riesz representative `g` of `L`: `⟪g, v⟫ = L v` and `‖g‖ = ‖L‖`
  set g : Euclid n := (InnerProductSpace.toDual ℝ (Euclid n)).symm L with hg
  have hgL : ∀ v, inner ℝ g v = L v := fun v => InnerProductSpace.toDual_symm_apply
  have hnorm : ‖g‖ = ‖L‖ := by simp [hg]
  -- `L(eᵢ) = ⟪eᵢ, g⟫ = gᵢ`
  have hcoord : ∀ i, L (EuclideanSpace.single i (1 : ℝ)) = g i := by
    intro i
    rw [← hgL, real_inner_comm, EuclideanSpace.inner_single_left]; simp
  -- (i) `‖L‖² = ‖g‖² = Σᵢ gᵢ²`
  have hid : ‖L‖ ^ 2 = ∑ i : Fin n, L (EuclideanSpace.single i (1 : ℝ)) ^ 2 := by
    rw [← hnorm, EuclideanSpace.real_norm_sq_eq]; simp_rw [hcoord]
  refine ⟨hid, fun a => ?_⟩
  -- (ii) `‖L‖ = √(Σᵢ L(eᵢ)²)`; Cauchy–Schwarz for `-a` gives the lower bound, for `a` the upper
  have hL : ‖L‖ = Real.sqrt (∑ i, L (EuclideanSpace.single i (1 : ℝ)) ^ 2) := by
    rw [← hid, Real.sqrt_sq (norm_nonneg _)]
  rw [hL, abs_le]
  constructor
  · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => L (EuclideanSpace.single i (1 : ℝ))) (fun i => -a i)
    simp only [neg_sq, mul_neg, Finset.sum_neg_distrib] at this
    linarith
  · exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
/-- Integration by parts for a Lipschitz `u` against `C¹` fields `Φᵢ` with compact support in
`B = B_R(0)`: `∫_B Σᵢ Du(x)eᵢ Φᵢ(x) dx = −∫_B u(x) Σᵢ DΦᵢ(x)eᵢ dx`.  Each `Φᵢ` is Lipschitz, so
Lipschitz integration by parts in direction `eᵢ` (`LipschitzWith.integral_lineDeriv_mul_eq`) applies
on `ℝⁿ`; by Rademacher, `lineDeriv u x eᵢ = Du(x)eᵢ` for a.e. `x`.  Both integrands are integrable
(`Du` is bounded by the Lipschitz constant) and vanish off `B`, so summing over `i` concludes. -/
theorem Submission.dorag_ha_lsc_ibp_lipschitz : ∀ (n : ℕ) (R : ℝ) (u : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∃ L : NNReal, LipschitzWith L u) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R u Φ ⟨L, hu⟩ hΦ hΦc hΦs
  set e : Fin n → Euclid n := fun i => EuclideanSpace.single i (1 : ℝ)
  have hΦL : ∀ i, ∃ C, LipschitzWith C (Φ i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hΦc i) (hΦ i) one_ne_zero
  choose C hC using hΦL
  -- integrability of the two families of integrands
  have hint1 : ∀ i, Integrable (fun x => fderiv ℝ u x (e i) * Φ i x) := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hΦ i).continuous.integrable_of_hasCompactSupport (hΦc i))
      (measurable_fderiv_apply_const ℝ u (e i)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    exact ((fderiv ℝ u x).le_opNorm (e i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))
  have hcontd : ∀ i, Continuous fun x => fderiv ℝ (Φ i) x (e i) := fun i =>
    ((hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint2 : ∀ i, Integrable (fun x => u x * fderiv ℝ (Φ i) x (e i)) := by
    intro i
    refine (hu.continuous.mul (hcontd i)).integrable_of_hasCompactSupport ?_
    exact ((hΦc i).fderiv_apply (𝕜 := ℝ) (e i)).mul_left
  -- per-coordinate identity on the whole space
  have key : ∀ i, ∫ x, fderiv ℝ u x (e i) * Φ i x = -∫ x, u x * fderiv ℝ (Φ i) x (e i) := by
    intro i
    have h1 :=
      hu.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid n))) (hC i) (hΦc i) (e i)
    have h2 : (fun x => lineDeriv ℝ u x (e i) * Φ i x) =ᵐ[volume]
        fun x => fderiv ℝ u x (e i) * Φ i x := by
      filter_upwards [hu.ae_differentiableAt] with x hx
      rw [hx.lineDeriv_eq_fderiv]
    have h3 : (fun x => lineDeriv ℝ (Φ i) x (-e i) * u x) =
        fun x => -(u x * fderiv ℝ (Φ i) x (e i)) := by
      funext x
      rw [(((hΦ i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
      ring
    rw [integral_congr_ae h2, h3, integral_neg] at h1
    exact h1
  -- integrands vanish off the ball
  have hzero1 : ∀ x, x ∉ ball (0 : Euclid n) R →
      ∑ i : Fin n, fderiv ℝ u x (e i) * Φ i x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  have hzero2 : ∀ x, x ∉ ball (0 : Euclid n) R →
      u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (e i) = 0 := by
    intro x hx
    rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => key i

namespace Submission

/-- Integration by parts on `B = B_R(0)` for `h` that is only `C¹` on `B`, against `C¹` fields
`Φᵢ` with compact support in `B`: `∫_B Σᵢ Dᵢh Φᵢ = -∫_B h Σᵢ DᵢΦᵢ`.  The supports of the `Φᵢ` lie
in some `B_{r₁}(0)`, `r₁ < R`.  A bump `χ` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ ⊆ B` makes
`h̃ = χh` a compactly supported `C¹`, hence Lipschitz, function, so `dorag_ha_lsc_ibp_lipschitz`
applies to `h̃`; both integrands only see `B_{r₁}(0)`, where `h̃ = h`. -/
theorem dorag_ha_lsc_ibp_c1_ball : ∀ (n : ℕ) (R : ℝ) (h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R h Φ hh hΦ hΦc hΦs
  -- `R ≤ 0`: the ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR]; simp
  -- The supports of the `Φᵢ` lie in a smaller ball `B_{r₁}(0)`, `0 < r₁ < R`.
  set K := ⋃ i, tsupport (Φ i)
  have hKc : IsClosed K := isClosed_iUnion_of_finite fun i => isClosed_tsupport _
  have hKB : K ⊆ ball 0 R := iUnion_subset hΦs
  obtain ⟨r₁, ⟨hr₁0, hr₁R⟩, hK₁⟩ := exists_pos_lt_subset_ball hR hKc hKB
  -- `h̃ = χh` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ = B̄_{(r₁+R)/2}(0) ⊆ B` is `C¹_c`.
  let χ : ContDiffBump (0 : Euclid n) := ⟨r₁, (r₁ + R) / 2, hr₁0, by linarith⟩
  set ht : Euclid n → ℝ := fun x => χ x * h x
  have hχsupp : tsupport χ ⊆ ball 0 R := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (show (r₁ + R) / 2 < R by linarith)
  have htC : ContDiff ℝ 1 ht := by
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · exact ((χ.contDiff.contDiffOn).mul hh).contDiffAt (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : ht =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [ht, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have htc : HasCompactSupport ht := χ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport htc htC one_ne_zero
  have key := Submission.dorag_ha_lsc_ibp_lipschitz n R ht Φ ⟨C, hC⟩ hΦ hΦc hΦs
  -- On `B_{r₁}(0)`, `h̃ = h` near each point; off it, every `Φᵢ` and `DΦᵢ` vanishes.
  have hone : ∀ y ∈ ball (0 : Euclid n) r₁, ht y = h y := by
    intro y hy
    simp [ht, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hEq : ∀ x ∈ ball (0 : Euclid n) r₁, ht =ᶠ[𝓝 x] h := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using hone y hy
  have hout : ∀ x, x ∉ ball (0 : Euclid n) r₁ → ∀ i, x ∉ tsupport (Φ i) :=
    fun x hx i h' => hx (hK₁ (mem_iUnion.2 ⟨i, h'⟩))
  have h1 : ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x =
      ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ ht x (EuclideanSpace.single i (1 : ℝ)) * Φ i x := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [(hEq x hx).fderiv_eq]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [image_eq_zero_of_notMem_tsupport (hout x hx i)]
  have h2 : ∫ x in ball (0 : Euclid n) R,
        h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ x in ball (0 : Euclid n) R,
        ht x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [hone x hx]
    · have : ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [fderiv_of_notMem_tsupport ℝ (hout x hx i)]; rfl
      simp only [this, mul_zero]
  rw [h1, h2, key]

end Submission

/-- **Duality bound for `Dh`** (the step "`∇f_{k'} ⇀ ∇w` weakly in `L²`, `∫_B |∇w|² ≤ 1`" of
Simon Ch. 5, Lemma 3.1, p. 114, in the Lipschitz/`L²` setting): if Lipschitz `uⱼ` with
`∫_B ‖Duⱼ‖² ≤ E` satisfy `∫_B (uⱼ - cⱼ - W)² → 0`, and `h` is `C¹` on `B = B_R(0)` with `h = W`
a.e. on `B`, then `∫_B Σᵢ Dh(eᵢ) Φᵢ ≤ √E √(∫_B Σᵢ Φᵢ²)` for `C¹` fields `Φᵢ` with compact
support in `B`.  By `dorag_ha_lsc_ibp_c1_ball`, `dorag_ha_lsc_ibp_lipschitz` and `∫_B div Φ = 0`,
the pairings `aⱼ = ∫_B Σᵢ Duⱼ(eᵢ) Φᵢ` differ from the left side by `-∫_B (uⱼ - cⱼ - W) div Φ`,
which tends to `0` by Cauchy–Schwarz; and `aⱼ ≤ √E √(∫_B Σᵢ Φᵢ²)` by
`dorag_ha_lsc_grad_norm_sq` and Cauchy–Schwarz. -/
theorem Submission.dorag_ha_lsc_duality_bound : ∀ (n : ℕ) (R E : ℝ) (u : ℕ → Euclid n → ℝ) (c : ℕ → ℝ) (W h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ E) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) R)), h x = W x) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x ≤ Real.sqrt E * Real.sqrt (∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2) := by
  intro n R E u c W h Φ hu hE hW hconv hh hae hΦ hΦc hΦs
  set B := ball (0 : Euclid n) R
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- `d = div Φ` and `G = |Φ|²` are continuous with compact support, hence bounded
  set d : Euclid n → ℝ := fun x =>
    ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ))
  set G : Euclid n → ℝ := fun x => ∑ i : Fin n, Φ i x ^ 2
  have hdC : Continuous d := continuous_finsetSum _ fun i _ =>
    ((hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport d := by
    refine HasCompactSupport.intro (isCompact_iUnion fun i => hΦc i) fun x hx => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h' => hx (mem_iUnion.2 ⟨i, h'⟩)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  obtain ⟨Cd, hCd⟩ := hdC.bounded_above_of_compact_support hdc
  have hGC : Continuous G := continuous_finsetSum _ fun i _ => (hΦ i).continuous.pow 2
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_iUnion fun i => hΦc i) fun x hx => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h' => hx (mem_iUnion.2 ⟨i, h'⟩)
    rw [image_eq_zero_of_notMem_tsupport this]; ring
  obtain ⟨CG, hCG⟩ := hGC.bounded_above_of_compact_support hGc
  have hG0 : ∀ x, 0 ≤ G x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hGle : ∀ x, Real.sqrt (G x) ≤ Real.sqrt CG := fun x =>
    Real.sqrt_le_sqrt ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (hCG x)))
  -- Cauchy–Schwarz on `B`: Hölder with `p = q = 2` applied to `|f|` and `|g|`
  have CS : ∀ f g : Euclid n → ℝ, MemLp f 2 (volume.restrict B) →
      MemLp g 2 (volume.restrict B) →
      |∫ x in B, f x * g x| ≤ Real.sqrt (∫ x in B, f x ^ 2) * Real.sqrt (∫ x in B, g x ^ 2) := by
    intro f g hf hg
    have hf' : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict B) := by
      simpa [Real.norm_eq_abs] using hf.norm
    have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict B) := by
      simpa [Real.norm_eq_abs] using hg.norm
    have H := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun x => abs_nonneg (f x)) (ae_of_all _ fun x => abs_nonneg (g x)) hf' hg'
    calc |∫ x in B, f x * g x| ≤ ∫ x in B, |f x * g x| := abs_integral_le_integral_abs
      _ = ∫ x in B, |f x| * |g x| := by simp_rw [abs_mul]
      _ ≤ _ := H
      _ = _ := by simp_rw [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  have hdL2 : MemLp d 2 (volume.restrict B) :=
    MemLp.of_bound hdC.aestronglyMeasurable Cd (ae_of_all _ hCd)
  -- integrability of `W d`, `uⱼ d` and `cⱼ d` on `B`
  have hW1 : Integrable W (volume.restrict B) := hW.integrable one_le_two
  have hWd : Integrable (fun x => W x * d x) (volume.restrict B) :=
    hW1.mul_bdd hdC.aestronglyMeasurable (ae_of_all _ hCd)
  have hud : ∀ j, Integrable (fun x => u j x * d x) (volume.restrict B) := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    exact ((hL.continuous.mul hdC).integrable_of_hasCompactSupport hdc.mul_left).integrableOn
  have hcd : ∀ j, Integrable (fun x => c j * d x) (volume.restrict B) := fun j =>
    ((continuous_const.mul hdC).integrable_of_hasCompactSupport hdc.mul_left).integrableOn
  -- `∫_B d = 0`: Lipschitz integration by parts with `u ≡ 1`
  have hdiv0 : ∫ x in B, d x = 0 := by
    have := Submission.dorag_ha_lsc_ibp_lipschitz n R (fun _ => (1 : ℝ)) Φ
      ⟨0, LipschitzWith.const 1⟩ hΦ hΦc hΦs
    simp only [fderiv_const_apply, FunLike.coe_zero, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, integral_zero, one_mul] at this
    linarith
  -- `T = -∫_B W d` and `aⱼ = -∫_B uⱼ d`
  set T := ∫ x in B, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x
    with hTdef
  have hT : T = -∫ x in B, W x * d x := by
    rw [hTdef, Submission.dorag_ha_lsc_ibp_c1_ball n R h Φ hh hΦ hΦc hΦs]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  set a : ℕ → ℝ := fun j =>
    ∫ x in B, ∑ i : Fin n, fderiv ℝ (u j) x (EuclideanSpace.single i (1 : ℝ)) * Φ i x
  have ha : ∀ j, a j = -∫ x in B, u j x * d x := fun j =>
    Submission.dorag_ha_lsc_ibp_lipschitz n R (u j) Φ (hu j) hΦ hΦc hΦs
  -- `uⱼ - cⱼ - W ∈ L²(B)`: `uⱼ - cⱼ` is bounded on `B`
  have hfL2 : ∀ j, MemLp (fun x => u j x - c j - W x) 2 (volume.restrict B) := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    have hb : MemLp (fun x => u j x - c j) 2 (volume.restrict B) := by
      refine MemLp.of_bound ((hL.continuous.sub continuous_const).aestronglyMeasurable)
        (|u j 0| + L * R + |c j|) ?_
      refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx => ?_)
      have hx' : ‖x‖ < R := mem_ball_zero_iff.1 hx
      have h1 : |u j x - u j 0| ≤ L * ‖x‖ := by
        simpa [Real.dist_eq, dist_zero_right] using hL.dist_le_mul x 0
      have h2 : (L : ℝ) * ‖x‖ ≤ L * R := mul_le_mul_of_nonneg_left hx'.le L.coe_nonneg
      rw [Real.norm_eq_abs]
      calc |u j x - c j| ≤ |u j x - u j 0| + |u j 0| + |c j| := by
              have := abs_sub (u j x) (c j)
              have := abs_sub_abs_le_abs_sub (u j x) (u j 0)
              have := abs_add_le (u j x - u j 0) (u j 0)
              simp only [sub_add_cancel] at this
              linarith
        _ ≤ |u j 0| + L * R + |c j| := by linarith
    exact hb.sub hW
  -- `aⱼ - T = -∫_B (uⱼ - cⱼ - W) d`, so `|aⱼ - T| ≤ ‖uⱼ - cⱼ - W‖_{L²(B)} ‖d‖_{L²(B)} → 0`
  have hdiff : ∀ j, a j - T = -∫ x in B, (u j x - c j - W x) * d x := by
    intro j
    rw [ha j, hT]
    have e1 : ∫ x in B, (u j x - c j - W x) * d x
        = (∫ x in B, u j x * d x) - c j * (∫ x in B, d x) - ∫ x in B, W x * d x := by
      have hI1 : Integrable (fun x => u j x * d x - c j * d x) (volume.restrict B) :=
        (hud j).sub (hcd j)
      simp_rw [sub_mul]
      rw [integral_sub hI1 hWd, integral_sub (hud j) (hcd j), integral_const_mul]
    rw [e1, hdiv0]; ring
  have hbound : ∀ j, |a j - T| ≤
      Real.sqrt (∫ x in B, (u j x - c j - W x) ^ 2) * Real.sqrt (∫ x in B, d x ^ 2) := by
    intro j
    rw [hdiff j, abs_neg]
    exact CS _ _ (hfL2 j) hdL2
  have hlim : Tendsto a atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _)
      (fun j => (Real.norm_eq_abs _).trans_le (hbound j)) ?_
    have := (hconv.sqrt).mul_const (Real.sqrt (∫ x in B, d x ^ 2))
    simpa using this
  -- uniform bound `aⱼ ≤ √E √(∫_B G)`: pointwise Cauchy–Schwarz, then Cauchy–Schwarz on `B`
  have hGsqrt : MemLp (fun x => Real.sqrt (G x)) 2 (volume.restrict B) :=
    MemLp.of_bound (hGC.sqrt.aestronglyMeasurable) (Real.sqrt CG) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hGle x)
  have habound : ∀ j, a j ≤ Real.sqrt E * Real.sqrt (∫ x in B, G x) := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    have hDuL2 : MemLp (fun x => ‖fderiv ℝ (u j) x‖) 2 (volume.restrict B) :=
      MemLp.of_bound ((measurable_fderiv ℝ (u j)).norm.aestronglyMeasurable) L
        (ae_of_all _ fun x => by rw [norm_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL)
    have hprodI : Integrable (fun x => ‖fderiv ℝ (u j) x‖ * Real.sqrt (G x))
        (volume.restrict B) :=
      Integrable.of_bound ((measurable_fderiv ℝ (u j)).norm.aestronglyMeasurable.mul
        hGC.sqrt.aestronglyMeasurable) (L * Real.sqrt CG) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
          exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hGle x) (Real.sqrt_nonneg _)
            L.coe_nonneg)
    have h1 : |a j| ≤ ∫ x in B, ‖fderiv ℝ (u j) x‖ * Real.sqrt (G x) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hprodI (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact (Submission.dorag_ha_lsc_grad_norm_sq n (fderiv ℝ (u j) x)).2 (fun i => Φ i x)
    have h2 : ∫ x in B, ‖fderiv ℝ (u j) x‖ * Real.sqrt (G x)
        ≤ Real.sqrt (∫ x in B, ‖fderiv ℝ (u j) x‖ ^ 2) * Real.sqrt (∫ x in B, G x) := by
      have := CS _ _ hDuL2 hGsqrt
      have hG2 : ∀ x, Real.sqrt (G x) ^ 2 = G x := fun x => Real.sq_sqrt (hG0 x)
      simp_rw [hG2] at this
      exact (le_abs_self _).trans this
    have h3 : Real.sqrt (∫ x in B, ‖fderiv ℝ (u j) x‖ ^ 2) ≤ Real.sqrt E :=
      Real.sqrt_le_sqrt (hE j)
    calc a j ≤ |a j| := le_abs_self _
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ Real.sqrt E * Real.sqrt (∫ x in B, G x) :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  -- pass to the limit
  exact le_of_tendsto' hlim habound

/-- **Simon 5.3.1, proof (weak lower semicontinuity of the energy), on interior balls.**
Let `χ` be a bump with `χ = 1` on `B̄_r(0)` and `tsupport χ = B̄_s(0)`, `s = (r + R)/2`.  The
field `Φᵢ = χ ∂ᵢh` is `C¹` and compactly supported in `B_R(0)`.  By
`‖Dh‖² = ∑ᵢ (∂ᵢh)²` (`Submission.dorag_ha_lsc_grad_norm_sq`), `∑ᵢ ∂ᵢh Φᵢ = χ‖Dh‖² =: g` and
`∑ᵢ Φᵢ² = χ²‖Dh‖² ≤ g`.  The duality bound then gives `X ≤ √E √X` for `X = ∫_{B_R} g`, so
`X ≤ E`, and `∫_{B_r} ‖Dh‖² = ∫_{B_r} g ≤ X`. -/
theorem Submission.dorag_ha_lsc_interior_energy : ∀ (n : ℕ) (R E r : ℝ) (h : Euclid n → ℝ), 0 < r → r < R → 0 ≤ E → ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) → (∀ Φ : Fin n → Euclid n → ℝ, (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x ≤ Real.sqrt E * Real.sqrt (∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2)) → ∫ x in ball (0 : Euclid n) r, ‖fderiv ℝ h x‖ ^ 2 ≤ E := by
  intro n R E r h hr hrR hE hh hdual
  -- the cutoff `χ`: `χ = 1` on `B̄_r(0)`, `tsupport χ = B̄_s(0) ⊆ B_R(0)`
  set s := (r + R) / 2 with hs
  have hrs : r < s := by linarith
  have hsR : s < R := by linarith
  let χ : ContDiffBump (0 : Euclid n) := ⟨r, s, hr, hrs⟩
  have hχsupp : tsupport χ ⊆ ball (0 : Euclid n) R := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball hsR
  -- the test field `Φᵢ = χ ∂ᵢh` is admissible
  set Φ : Fin n → Euclid n → ℝ :=
    fun i x => χ x * fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) with hΦdef
  have hDh : ContDiffOn ℝ 1 (fderiv ℝ h) (ball (0 : Euclid n) R) :=
    hh.fderiv_of_isOpen isOpen_ball (by norm_num)
  have hΦC : ∀ i, ContDiff ℝ 1 (Φ i) := by
    intro i
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · exact (χ.contDiff.contDiffOn.mul (hDh.clm_apply contDiffOn_const)).contDiffAt
        (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : Φ i =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [Φ, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hΦsupp : ∀ i, support (Φ i) ⊆ closedBall 0 s := by
    intro i x hx
    have hχx : χ x ≠ 0 := left_ne_zero_of_mul hx
    have hmem := subset_tsupport χ hχx
    rwa [χ.tsupport_eq] at hmem
  have hΦc : ∀ i, HasCompactSupport (Φ i) := fun i =>
    HasCompactSupport.intro (isCompact_closedBall 0 s) fun x hx =>
      notMem_support.1 fun h' => hx (hΦsupp i h')
  have hΦs : ∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R := fun i =>
    (closure_minimal (hΦsupp i) isClosed_closedBall).trans (closedBall_subset_ball hsR)
  -- pointwise: `∑ᵢ ∂ᵢh Φᵢ = g` and `∑ᵢ Φᵢ² ≤ g`, where `g = χ ‖Dh‖²`
  have hgrad : ∀ x, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) ^ 2 =
      ‖fderiv ℝ h x‖ ^ 2 :=
    fun x => ((Submission.dorag_ha_lsc_grad_norm_sq n (fderiv ℝ h x)).1).symm
  set g : Euclid n → ℝ := fun x => χ x * ‖fderiv ℝ h x‖ ^ 2 with hgdef
  have hpt1 : ∀ x, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = g x := by
    intro x
    simp only [Φ, g]
    rw [← hgrad x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hpt2 : ∀ x, ∑ i : Fin n, Φ i x ^ 2 ≤ g x := by
    intro x
    have h0 : 0 ≤ χ x := χ.nonneg' x
    have h1 : χ x ≤ 1 := χ.le_one
    calc ∑ i : Fin n, Φ i x ^ 2 = χ x ^ 2 * ‖fderiv ℝ h x‖ ^ 2 := by
            simp only [Φ]; rw [← hgrad x, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ χ x * ‖fderiv ℝ h x‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            nlinarith
      _ = g x := rfl
  -- integrability: `g` is continuous with compact support, and `0 ≤ ∑ᵢ Φᵢ² ≤ g`
  have hgC : Continuous g := by
    rw [continuous_iff_continuousAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · have hcont : ContinuousOn g (ball (0 : Euclid n) R) :=
        χ.continuous.continuousOn.mul
          ((hh.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).norm.pow 2)
      exact hcont.continuousAt (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [g, hy]
      exact continuousAt_const.congr hev.symm
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgI : Integrable g := hgC.integrable_of_hasCompactSupport hgc
  have hΦ2I : Integrable fun x => ∑ i : Fin n, Φ i x ^ 2 := by
    refine hgI.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (continuous_finsetSum _ fun i _ => ((hΦC i).continuous.pow 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      exact hpt2 x
  -- duality: `X ≤ √E √X` for `X = ∫_{B_R} g`, hence `X ≤ E`
  set X := ∫ x in ball (0 : Euclid n) R, g x with hXdef
  have hX0 : 0 ≤ X := setIntegral_nonneg measurableSet_ball fun x _ =>
    mul_nonneg (χ.nonneg' x) (sq_nonneg _)
  have hLHS : ∫ x in ball (0 : Euclid n) R,
      ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = X := by
    simp_rw [hpt1]; rfl
  have hRHS : ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, Φ i x ^ 2 ≤ X :=
    setIntegral_mono hΦ2I.integrableOn hgI.integrableOn hpt2
  have hd := hdual Φ hΦC hΦc hΦs
  rw [hLHS] at hd
  have h1 : X ≤ Real.sqrt E * Real.sqrt X :=
    hd.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRHS) (Real.sqrt_nonneg E))
  have hXE : X ≤ E := by
    rcases hX0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact hE
    · have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hpos
      have h2 : Real.sqrt X * Real.sqrt X ≤ Real.sqrt E * Real.sqrt X := by
        rw [Real.mul_self_sqrt hX0]; exact h1
      have h3 : Real.sqrt X ≤ Real.sqrt E := le_of_mul_le_mul_right h2 hsX
      calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
        _ ≤ Real.sqrt E ^ 2 := by gcongr
        _ = E := Real.sq_sqrt hE
  -- the interior ball: `‖Dh‖² = g` on `B_r(0)` and `B_r(0) ⊆ B_R(0)`
  have hball : ∫ x in ball (0 : Euclid n) r, ‖fderiv ℝ h x‖ ^ 2 =
      ∫ x in ball (0 : Euclid n) r, g x := by
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    simp [g, χ.one_of_mem_closedBall (ball_subset_closedBall hx)]
  have hmono : ∫ x in ball (0 : Euclid n) r, g x ≤ X :=
    setIntegral_mono_set hgI.integrableOn
      (ae_of_all _ fun x => mul_nonneg (χ.nonneg' x) (sq_nonneg _))
      (Filter.EventuallySubset.of_subset (ball_subset_ball hrR.le))
  linarith

namespace Submission

/-- Exhaustion of `B_R(0)` by concentric balls: if `f ≥ 0` is continuous on `B_R(0)` and
`∫_{B_r(0)} f ≤ E` for every `0 < r < R`, then `f` is integrable on `B_R(0)` and
`∫_{B_R(0)} f ≤ E`.  Monotone convergence along the radii `r_k = R (k + 1) / (k + 2) ↑ R`
bounds `∫⁻_{B_R(0)} f` by `E`. -/
theorem dorag_ha_lsc_exhaustion : ∀ (n : ℕ) (R E : ℝ) (f : Euclid n → ℝ), 0 < R → ContinuousOn f (ball (0 : Euclid n) R) → (∀ x ∈ ball (0 : Euclid n) R, 0 ≤ f x) → (∀ r, 0 < r → r < R → ∫ x in ball (0 : Euclid n) r, f x ≤ E) → IntegrableOn f (ball (0 : Euclid n) R) ∧ ∫ x in ball (0 : Euclid n) R, f x ≤ E := by
  intro n R E f hR hf hf0 hbd
  -- integrability on interior balls
  have hint : ∀ r, 0 < r → r < R → IntegrableOn f (ball (0 : Euclid n) r) := by
    intro r _ hrR
    exact ((hf.mono (closedBall_subset_ball hrR)).integrableOn_compact
      (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hnn : ∀ r, r ≤ R → 0 ≤ᵐ[volume.restrict (ball (0 : Euclid n) r)] f := by
    intro r hrR
    exact (ae_restrict_iff' measurableSet_ball).2
      (Eventually.of_forall fun x hx => hf0 x (ball_subset_ball hrR hx))
  have hE0 : 0 ≤ E := (setIntegral_nonneg measurableSet_ball fun x hx =>
      hf0 x (ball_subset_ball (half_le_self hR.le) hx)).trans (hbd (R / 2) (half_pos hR) (half_lt_self hR))
  -- exhausting sequence of radii
  set r : ℕ → ℝ := fun k => R * ((k + 1) / (k + 2)) with hr
  have hr_pos : ∀ k, 0 < r k := fun k => by positivity
  have hr_lt : ∀ k, r k < R := fun k => by
    have : ((k:ℝ) + 1) / (k + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    calc r k = R * ((k + 1) / (k + 2)) := rfl
      _ < R * 1 := by gcongr
      _ = R := mul_one R
  have hr_mono : Monotone r := by
    intro k l hkl
    have hkl' : (k:ℝ) ≤ l := by exact_mod_cast hkl
    have hfrac : ((k:ℝ) + 1) / (k + 2) ≤ ((l:ℝ) + 1) / (l + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    exact mul_le_mul_of_nonneg_left hfrac hR.le
  have hunion : (⋃ k, ball (0 : Euclid n) (r k)) = ball (0 : Euclid n) R := by
    apply Subset.antisymm
    · exact iUnion_subset fun k => ball_subset_ball (hr_lt k).le
    · intro x hx
      rw [mem_ball_zero_iff] at hx
      obtain ⟨k, hk⟩ := exists_nat_gt (R / (R - ‖x‖))
      refine mem_iUnion.2 ⟨k, mem_ball_zero_iff.2 ?_⟩
      have hpos : 0 < R - ‖x‖ := by linarith
      have hk2 : R < (k + 2) * (R - ‖x‖) := by
        rw [div_lt_iff₀ hpos] at hk; nlinarith
      show ‖x‖ < R * ((k + 1) / (k + 2))
      rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
      nlinarith
  have hdir : Directed (· ⊆ ·) fun k => ball (0 : Euclid n) (r k) :=
    Monotone.directed_le fun a b hab => ball_subset_ball (hr_mono hab)
  -- lintegral bound
  have hlin : ∫⁻ x in ball (0 : Euclid n) R, ENNReal.ofReal (f x) ≤ ENNReal.ofReal E := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hdir]
    refine iSup_le fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hint _ (hr_pos k) (hr_lt k)) (hnn _ (hr_lt k).le)]
    exact ENNReal.ofReal_le_ofReal (hbd _ (hr_pos k) (hr_lt k))
  have hmeas : AEStronglyMeasurable f (volume.restrict (ball (0 : Euclid n) R)) :=
    hf.aestronglyMeasurable measurableSet_ball
  have hI : IntegrableOn f (ball (0 : Euclid n) R) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (hnn R le_rfl)]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  have := (ofReal_integral_eq_lintegral_ofReal hI (hnn R le_rfl)).trans_le hlin
  exact (ENNReal.ofReal_le_ofReal_iff hE0).1 this

end Submission

/-- **Lower semicontinuity of the Dirichlet energy** (the step "`∇f_{k'} ⇀ ∇w` weakly in `L²`, with
`∫_B |∇w|² ≤ 1`" of Simon's proof of Lemma 5.3.1, p. 114, in a Lipschitz/`L²` setting).  Let
`B = B̆_R(0) ⊆ ℝⁿ`, let `u_j` be Lipschitz with `∫_B ‖Du_j‖² ≤ E` and `u_j - c_j → W` in `L²(B)`,
and let `h` be `C²` on `B` with `h = W` a.e. on `B`.  Then `‖Dh‖²` is integrable on `B` and
`∫_B ‖Dh‖² ≤ E`.  Duality against `C¹` vector fields `Φ` compactly supported in `B` gives
`∫_B ∇h·Φ ≤ √E ‖Φ‖_{L²(B)}`; testing with `Φ = χ_r ∇h` bounds the energy of `h` on each `B̆_r(0)`,
`r < R`, by `E`, and exhausting `B` by these balls gives the claim. -/
theorem Submission.dorag_ha_energy_lsc : ∀ (n : ℕ) (R E : ℝ) (u : ℕ → Euclid n → ℝ) (c : ℕ → ℝ) (W h : Euclid n → ℝ), 0 < n → 0 < R → (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ E) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) → (∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) R)), h x = W x) → IntegrableOn (fun x => ‖fderiv ℝ h x‖ ^ 2) (ball (0 : Euclid n) R) ∧ ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ h x‖ ^ 2 ≤ E := by
  intro n R E u c W h _ hR hu hE hW hconv hh hhW
  -- Step 0: `E ≥ 0`, from the energy bound for `u₀`
  have hE0 : 0 ≤ E := (integral_nonneg fun x => sq_nonneg _).trans (hE 0)
  -- Step 3: the duality bound `∫_B ∇h·Φ ≤ √E ‖Φ‖_{L²(B)}`, `h` being in particular `C¹` on `B`
  have hdual := fun Φ => Submission.dorag_ha_lsc_duality_bound n R E u c W h Φ hu hE hW hconv
    (hh.of_le one_le_two) hhW
  -- Step 5: exhaust `B` by the balls `B̆_r(0)`, `r < R`, on which Step 4 bounds the energy by `E`
  refine Submission.dorag_ha_lsc_exhaustion n R E (fun x => ‖fderiv ℝ h x‖ ^ 2) hR
    ((hh.continuousOn_fderiv_of_isOpen isOpen_ball one_le_two).norm.fun_pow 2)
    (fun x _ => sq_nonneg _) fun r hr hrR => ?_
  exact Submission.dorag_ha_lsc_interior_energy n R E r h hr hrR hE0 hh hdual

/-- **Harmonic approximation lemma** (Simon Ch. 5, Lemma 3.1, for Lipschitz `w`).  Given `n ≥ 1`
and `ε > 0` there is `δ > 0` such that: if `w` is Lipschitz, `∫_{B_{R₀}} ‖Dw‖² ≤ R₀ⁿ` and
`|∫_{B_{R₀}} ∇w·∇ζ| ≤ δ R₀ⁿ G` for every `C¹` function `ζ` with compact support in
`B_{R₀} = B̆_{R₀}(0)` and `‖Dζ‖ ≤ G`, then some `h`, smooth and harmonic on `B_{R₀}`, has
`∫_{B_{R₀}} ‖Dh‖² ≤ R₀ⁿ` and `∫_{B_{R₀}} (h − w)² ≤ ε R₀^{n+2}`.
*Unit scale* (`R₀ = 1`), by contradiction: otherwise for each `j` some `w_j` satisfies the
hypotheses with `δ = 1/(j+1)` but has no such `h`.  With `c_j` the mean of `w_j` over `B_1`,
Poincaré bounds `∫_{B_1} (w_j − c_j)²` and Rellich gives `W ∈ L²(B_1)` with
`∫_{B_1} (w_{φ(j)} − c_{φ(j)} − W)² → 0`.  Then `∫_{B_1} W Δζ = 0` for `C²` test functions `ζ`;
Weyl's lemma gives a smooth harmonic `g = W` a.e. on `B_1`, and lower semicontinuity of the
energy gives `∫_{B_1} ‖Dg‖² ≤ 1`.  For large `j`, `g + c_{φ(j)}` is admissible for `w_{φ(j)}`, a
contradiction.  *Scaling*: `w₁(y) = R₀⁻¹ w(R₀y)` satisfies the unit-scale hypotheses, and an
admissible `h₁` for `w₁` rescales to `h(x) = R₀ h₁(x/R₀)`. -/
theorem Submission.dorag_ha_approximation : ∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * R₀ ^ n * G) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R₀)) ∧ (∀ y ∈ ball (0 : Euclid n) R₀, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2 ≤ R₀ ^ n ∧ IntegrableOn (fun y => (h y - w y) ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2 ≤ ε * R₀ ^ (n + 2) := by
  intro n hn ε hε
  -- Unit scale: the statement for `R₀ = 1`
  have hunit : ∃ δ : ℝ, 0 < δ ∧ ∀ (w : Euclid n → ℝ) (Lw : NNReal), LipschitzWith Lw w →
      ∫ v in ball (0 : Euclid n) 1, ‖fderiv ℝ w v‖ ^ 2 ≤ 1 →
      (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball (0 : Euclid n) 1 → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
        |∫ v in ball (0 : Euclid n) 1, ∑ i : Fin n,
          fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) *
            fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * G) →
      ∃ h₁ : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h₁ (ball (0 : Euclid n) 1)) ∧
        (∀ y ∈ ball (0 : Euclid n) 1, ∑ i : Fin n, iteratedFDeriv ℝ 2 h₁ y
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧
        IntegrableOn (fun y => ‖fderiv ℝ h₁ y‖ ^ 2) (ball (0 : Euclid n) 1) ∧
        ∫ y in ball (0 : Euclid n) 1, ‖fderiv ℝ h₁ y‖ ^ 2 ≤ 1 ∧
        IntegrableOn (fun y => (h₁ y - w y) ^ 2) (ball (0 : Euclid n) 1) ∧
        ∫ y in ball (0 : Euclid n) 1, (h₁ y - w y) ^ 2 ≤ ε := by
    by_contra hcon
    -- for each `j`, a counterexample `w j` to the unit-scale statement with `δ = 1/(j+1)`
    have hbad : ∀ j : ℕ, ∃ (w : Euclid n → ℝ) (Lw : NNReal), LipschitzWith Lw w ∧
        ∫ v in ball (0 : Euclid n) 1, ‖fderiv ℝ w v‖ ^ 2 ≤ 1 ∧
        (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
          tsupport ζ ⊆ ball (0 : Euclid n) 1 → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
          |∫ v in ball (0 : Euclid n) 1, ∑ i : Fin n,
            fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) *
              fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ 1 / ((j : ℝ) + 1) * G) ∧
        ¬∃ h₁ : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h₁ (ball (0 : Euclid n) 1)) ∧
          (∀ y ∈ ball (0 : Euclid n) 1, ∑ i : Fin n, iteratedFDeriv ℝ 2 h₁ y
            ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧
          IntegrableOn (fun y => ‖fderiv ℝ h₁ y‖ ^ 2) (ball (0 : Euclid n) 1) ∧
          ∫ y in ball (0 : Euclid n) 1, ‖fderiv ℝ h₁ y‖ ^ 2 ≤ 1 ∧
          IntegrableOn (fun y => (h₁ y - w y) ^ 2) (ball (0 : Euclid n) 1) ∧
          ∫ y in ball (0 : Euclid n) 1, (h₁ y - w y) ^ 2 ≤ ε := by
      intro j
      by_contra hj
      refine hcon ⟨1 / ((j : ℝ) + 1), by positivity, fun w Lw hLw hE hH => ?_⟩
      by_contra hno
      exact hj ⟨w, Lw, hLw, hE, hH, hno⟩
    choose w Lw hLw hE hH hno using hbad
    -- `c j` is the mean of `w j` over `B_1`; Poincaré bounds `∫_{B_1} (w j - c j)²`
    obtain ⟨CP, hCP, hP⟩ := Submission.dorag_ha_poincare_ball n hn
    obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ j, c j = (∫ y in ball (0 : Euclid n) 1, w j y) /
        (volume (ball (0 : Euclid n) 1)).toReal := ⟨_, fun _ => rfl⟩
    have hu2 : ∀ j, ∫ x in ball (0 : Euclid n) 1, (w j x - c j) ^ 2 ≤ max CP 1 := by
      intro j
      have hPj := hP (w j) (Lw j) (hLw j)
      rw [← hc j] at hPj
      calc ∫ x in ball (0 : Euclid n) 1, (w j x - c j) ^ 2
          ≤ CP * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (w j) x‖ ^ 2 := hPj
        _ ≤ CP * 1 := mul_le_mul_of_nonneg_left (hE j) hCP.le
        _ ≤ max CP 1 := (mul_one CP).le.trans (le_max_left _ _)
    -- `D(w j - c j) = D(w j)`
    have hDu2 : ∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (fun x => w j x - c j) x‖ ^ 2 ≤
        max CP 1 := by
      intro j
      simp only [fderiv_sub_const]
      exact (hE j).trans (le_max_right _ _)
    -- Rellich: `w (φ j) - c (φ j) → W` in `L²(B_1)` along a subsequence `φ`
    obtain ⟨φ, W, hφ, hW, hconv⟩ := Submission.dorag_ha_rellich_ball n (max CP 1)
      (fun j x => w j x - c j) hn (fun j => ⟨_, (hLw j).sub (LipschitzWith.const (c j))⟩)
      hu2 hDu2
    -- `∫_{B_1} W Δζ = 0` for every `C²` test function `ζ` compactly supported in `B_1`
    have hharm := Submission.dorag_haa_weakly_harmonic_limit n 1 (fun j => w (φ j))
      (fun j => c (φ j)) (fun j => 1 / ((φ j : ℝ) + 1)) W (fun j => ⟨_, hLw (φ j)⟩)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop) hW hconv
      (fun j => hH (φ j))
    -- Weyl: a smooth harmonic `g` with `g = W` a.e. on `B_1`
    have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) 1)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    obtain ⟨g, hgC, hgΔ, hgW⟩ := Submission.dorag_ha_weyl_lemma n 1 W hn one_pos
      (hW.integrable one_le_two) hharm
    -- lower semicontinuity of the energy: `∫_{B_1} ‖Dg‖² ≤ 1`
    obtain ⟨hgI, hgE⟩ := Submission.dorag_ha_energy_lsc n 1 1 (fun j => w (φ j))
      (fun j => c (φ j)) W g hn one_pos (fun j => ⟨_, hLw (φ j)⟩) (fun j => hE (φ j)) hW hconv
      (hgC 2) hgW
    -- pick `j` with `∫_{B_1} (w (φ j) - c (φ j) - W)² ≤ ε`
    obtain ⟨j, hj⟩ := (hconv.eventually (Iic_mem_nhds hε)).exists
    have hj' : ∫ x in ball (0 : Euclid n) 1, (w (φ j) x - c (φ j) - W x) ^ 2 ≤ ε := hj
    -- `w (φ j) - c (φ j)` is continuous, hence bounded on `B_1`, so it lies in `L²(B_1)`
    have hcont : Continuous fun x => w (φ j) x - c (φ j) :=
      (hLw (φ j)).continuous.sub continuous_const
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid n) 1).exists_bound_of_continuousOn
      hcont.continuousOn
    have hmem : MemLp (fun x => w (φ j) x - c (φ j)) 2 (volume.restrict (ball (0 : Euclid n) 1)) :=
      MemLp.of_bound hcont.aestronglyMeasurable C
        (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hC x (ball_subset_closedBall hx))
    have hd := hmem.sub hW
    have hsq : IntegrableOn (fun y => (w (φ j) y - c (φ j) - W y) ^ 2) (ball (0 : Euclid n) 1) :=
      (hd.integrable_mul hd).congr
        (ae_of_all _ fun y => by simp only [Pi.mul_apply, Pi.sub_apply, sq])
    -- `g + c (φ j) - w (φ j) = W - (w (φ j) - c (φ j))` a.e. on `B_1`
    have hae : (fun y => (w (φ j) y - c (φ j) - W y) ^ 2)
        =ᵐ[volume.restrict (ball (0 : Euclid n) 1)] fun y => (g y + c (φ j) - w (φ j) y) ^ 2 := by
      filter_upwards [hgW] with y hy
      rw [hy]
      ring
    -- `g + c (φ j)` is admissible for `w (φ j)`: adding a constant leaves `Dg`, `D²g` unchanged
    have hgD : fderiv ℝ (fun x => g x + c (φ j)) = fderiv ℝ g :=
      funext fun x => fderiv_add_const _
    refine hno (φ j) ⟨fun x => g x + c (φ j), fun m => (hgC m).add contDiffOn_const,
      fun y hy => ?_, ?_, ?_, hsq.congr hae, (integral_congr_ae hae).symm.trans_le hj'⟩
    · have h2 : iteratedFDeriv ℝ 2 (fun x => g x + c (φ j)) y = iteratedFDeriv ℝ 2 g y := by
        ext m
        rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hgD]
      rw [h2]
      exact hgΔ y hy
    · rw [hgD]
      exact hgI
    · rw [hgD]
      exact hgE
  -- Scaling: `w₁(y) = R₀⁻¹ w(R₀y)` satisfies the unit-scale hypotheses, and an admissible `h₁`
  -- for `w₁` rescales to `h(x) = R₀ h₁(x/R₀)`
  obtain ⟨δ, hδ, hA⟩ := hunit
  refine ⟨δ, hδ, fun R₀ w Lw hR₀ hLw hE hH => ?_⟩
  obtain ⟨hLw₁, hE₁, hH₁⟩ := Submission.dorag_haa_rescale_hypotheses n δ R₀ w Lw hR₀ hLw hE hH
  obtain ⟨h₁, hC₁, hΔ₁, hI₁, hD₁, hI₂, hε₁⟩ := hA _ Lw hLw₁ hE₁ hH₁
  exact Submission.dorag_haa_rescale_conclusion n ε R₀ w h₁ hR₀ hC₁ hΔ₁ hI₁ hD₁ hI₂ hε₁

/-- **Harmonic approximation with affine decay** (Simon Ch. 5, Lemma 3.1 and estimates 3.2–3.4, as
used in (17')–(19') of the Allard graph proof).  Take the harmonic approximation `h` of `w` on
`B̆_{R₀}(0)` (`dorag_ha_approximation`), `a = h(0)` and `b = Dh(0)`.  The interior estimates
(`dorag_ha_interior_estimates`, constant `C_H`) give `‖b‖ ≤ C_H`, `|a| ≤ C_H (R₀⁻ⁿ∫h²)^{1/2}` and
`|h(v) − a − b(v)| ≤ C_H|v|²/R₀` for `|v| ≤ R₀/4`; with `h² ≤ 2w² + 2(h − w)²` and
`(w − a − b)² ≤ 2(h − w)² + 2(h − a − b)²` this gives the claim for `C = max(√2·C_H, 2, 2ωₙC_H²)`
and `δ_h = δ(ε')`. -/
theorem Submission.dorag_harmonic_affine_approximation : ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧ ∀ ε' : ℝ, 0 < ε' → ∃ δh : ℝ, 0 < δh ∧ ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) → ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ C ∧ |a| ≤ C * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) + C * Real.sqrt ε' * R₀ ∧ ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤ C * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2) := by
  intro n hn
  obtain ⟨CH, hCH, hest⟩ := Submission.dorag_ha_interior_estimates n hn
  -- `C = max(√2·C_H, 2, 2ωₙC_H²)` with `ωₙ = Lⁿ(B̆₁(0))`
  obtain ⟨C, hC1, hC2, hC3⟩ : ∃ C : ℝ, Real.sqrt 2 * CH ≤ C ∧ 2 ≤ C ∧
      2 * (volume (ball (0 : Euclid n) 1)).toReal * CH ^ 2 ≤ C :=
    ⟨max (Real.sqrt 2 * CH) (max 2 (2 * (volume (ball (0 : Euclid n) 1)).toReal * CH ^ 2)),
      le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hCHC : CH ≤ C := le_trans (by nlinarith) hC1
  refine ⟨C, by linarith, fun ε' hε' => ?_⟩
  obtain ⟨δ, hδ, happrox⟩ := Submission.dorag_ha_approximation n hn ε' hε'
  refine ⟨δ, hδ, fun R₀ w Lw hR₀ hLw hEw hζ => ?_⟩
  -- the harmonic approximation `h` of `w` on `B̆_{R₀}(0)`
  obtain ⟨h, hsmooth, hharm, hDhint, hDh, hdint, hdist⟩ := happrox R₀ w Lw hR₀ hLw hEw hζ
  -- `w` is continuous, so `w²` is integrable on the bounded ball; `h² ≤ 2w² + 2(h − w)²`
  have hwint : IntegrableOn (fun v => w v ^ 2) (ball (0 : Euclid n) R₀) :=
    ((hLw.continuous.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R₀)).mono_set ball_subset_closedBall
  have hbound : ∀ v, h v ^ 2 ≤ 2 * w v ^ 2 + 2 * (h v - w v) ^ 2 := fun v => by
    nlinarith [sq_nonneg (h v - 2 * w v)]
  have hgint : IntegrableOn (fun v => 2 * w v ^ 2 + 2 * (h v - w v) ^ 2)
      (ball (0 : Euclid n) R₀) :=
    (hwint.const_mul 2).add (hdint.const_mul 2)
  have hhint : IntegrableOn (fun v => h v ^ 2) (ball (0 : Euclid n) R₀) := by
    refine hgint.mono' (((hsmooth 0).continuousOn.pow 2).aestronglyMeasurable measurableSet_ball)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound v
  obtain ⟨ha, hb, htaylor⟩ := hest R₀ h hR₀ hsmooth hharm hDhint hDh hhint
  refine ⟨h 0, fderiv ℝ h 0, hb.trans hCHC, ?_, ?_⟩
  · -- `|a| ≤ C_H (R₀⁻ⁿ∫h²)^{1/2} ≤ √2·C_H ((R₀⁻ⁿ∫w²)^{1/2} + √ε'·R₀)`
    set X := (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n with hX
    have hX0 : 0 ≤ X :=
      div_nonneg (setIntegral_nonneg measurableSet_ball fun v _ => sq_nonneg _) (by positivity)
    have hIh : ∫ v in ball (0 : Euclid n) R₀, h v ^ 2 ≤
        2 * (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) +
          2 * ∫ v in ball (0 : Euclid n) R₀, (h v - w v) ^ 2 := by
      calc ∫ v in ball (0 : Euclid n) R₀, h v ^ 2
          ≤ ∫ v in ball (0 : Euclid n) R₀, (2 * w v ^ 2 + 2 * (h v - w v) ^ 2) :=
            setIntegral_mono hhint hgint hbound
        _ = 2 * (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) +
              2 * ∫ v in ball (0 : Euclid n) R₀, (h v - w v) ^ 2 := by
            rw [integral_add (hwint.const_mul 2) (hdint.const_mul 2), integral_const_mul,
              integral_const_mul]
    have hquot : (∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n ≤
        2 * X + 2 * (ε' * R₀ ^ 2) := by
      rw [div_le_iff₀ (by positivity), hX]
      calc ∫ v in ball (0 : Euclid n) R₀, h v ^ 2
          ≤ 2 * (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) + 2 * (ε' * R₀ ^ (n + 2)) := by
            linarith
        _ = (2 * ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) + 2 * (ε' * R₀ ^ 2)) *
              R₀ ^ n := by
            field_simp
            ring
    -- `√(x + y) ≤ √x + √y`
    have hsqrt_add : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y :=
      fun x y hx hy => by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
    have hsqrt : Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n) ≤
        Real.sqrt 2 * Real.sqrt X + Real.sqrt 2 * (Real.sqrt ε' * R₀) := by
      calc Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n)
          ≤ Real.sqrt (2 * X + 2 * (ε' * R₀ ^ 2)) := Real.sqrt_le_sqrt hquot
        _ ≤ Real.sqrt (2 * X) + Real.sqrt (2 * (ε' * R₀ ^ 2)) :=
            hsqrt_add _ _ (by positivity) (by positivity)
        _ = Real.sqrt 2 * Real.sqrt X + Real.sqrt 2 * (Real.sqrt ε' * R₀) := by
            rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul zero_le_two, Real.sqrt_mul hε'.le,
              Real.sqrt_sq hR₀.le]
    calc |h 0| ≤ CH * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n) := ha
      _ ≤ CH * (Real.sqrt 2 * Real.sqrt X + Real.sqrt 2 * (Real.sqrt ε' * R₀)) :=
          mul_le_mul_of_nonneg_left hsqrt hCH.le
      _ = Real.sqrt 2 * CH * Real.sqrt X + Real.sqrt 2 * CH * Real.sqrt ε' * R₀ := by ring
      _ ≤ C * Real.sqrt X + C * Real.sqrt ε' * R₀ := by gcongr
  · -- `∫_{B̆_{θ'R₀}} (w − a − b)² ≤ 2∫_{B̆_{R₀}} (h − w)² + 2 Lⁿ(B̆_{θ'R₀}) (C_H (θ'R₀)²/R₀)²`
    intro θ' hθ' hθ'4
    have hr : 0 < θ' * R₀ := mul_pos hθ' hR₀
    have hsub : ball (0 : Euclid n) (θ' * R₀) ⊆ ball 0 R₀ := ball_subset_ball (by nlinarith)
    have hpt : ∀ v ∈ ball (0 : Euclid n) (θ' * R₀), (w v - h 0 - fderiv ℝ h 0 v) ^ 2 ≤
        2 * (h v - w v) ^ 2 + 2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 := by
      intro v hv
      have hv' : ‖v‖ ≤ θ' * R₀ := (mem_ball_zero_iff.mp hv).le
      have h1 : |h v - h 0 - fderiv ℝ h 0 v| ≤ CH * (θ' * R₀) ^ 2 / R₀ :=
        (htaylor v (by nlinarith)).trans (by gcongr)
      have h2 : (h v - h 0 - fderiv ℝ h 0 v) ^ 2 ≤ (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [sq_nonneg ((h v - w v) + (h v - h 0 - fderiv ℝ h 0 v))]
    have hdint' : IntegrableOn (fun v => (h v - w v) ^ 2) (ball (0 : Euclid n) (θ' * R₀)) :=
      hdint.mono_set hsub
    have hcint : IntegrableOn (fun _ : Euclid n => 2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2)
        (ball (0 : Euclid n) (θ' * R₀)) :=
      integrableOn_const measure_ball_lt_top.ne
    have hvol : volume.real (ball (0 : Euclid n) (θ' * R₀)) =
        (θ' * R₀) ^ n * (volume (ball (0 : Euclid n) 1)).toReal := by
      rw [measureReal_def, Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hsmall : ∫ v in ball (0 : Euclid n) (θ' * R₀), (h v - w v) ^ 2 ≤ ε' * R₀ ^ (n + 2) :=
      (setIntegral_mono_set hdint (Eventually.of_forall fun v => sq_nonneg _)
        hsub.eventuallyLE).trans hdist
    calc ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - h 0 - fderiv ℝ h 0 v) ^ 2
        ≤ ∫ v in ball (0 : Euclid n) (θ' * R₀),
            (2 * (h v - w v) ^ 2 + 2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun v => sq_nonneg _)
            ((hdint'.const_mul 2).add hcint) (ae_restrict_of_forall_mem measurableSet_ball hpt)
      _ = 2 * (∫ v in ball (0 : Euclid n) (θ' * R₀), (h v - w v) ^ 2) +
            2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 *
              ((θ' * R₀) ^ n * (volume (ball (0 : Euclid n) 1)).toReal) := by
          rw [integral_add (hdint'.const_mul 2) hcint, setIntegral_const, integral_const_mul, hvol,
            smul_eq_mul]
          ring
      _ ≤ 2 * (ε' * R₀ ^ (n + 2)) +
            2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 *
              ((θ' * R₀) ^ n * (volume (ball (0 : Euclid n) 1)).toReal) := by
          gcongr
      _ = 2 * (ε' / θ' ^ (n + 2)) * (θ' * R₀) ^ (n + 2) +
            2 * (volume (ball (0 : Euclid n) 1)).toReal * CH ^ 2 * θ' ^ 2 *
              (θ' * R₀) ^ (n + 2) := by
          field_simp
          ring
      _ ≤ C * (ε' / θ' ^ (n + 2)) * (θ' * R₀) ^ (n + 2) + C * θ' ^ 2 * (θ' * R₀) ^ (n + 2) := by
          gcongr
      _ = C * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2) := by ring
/-- **Standing density bounds for the Allard graph construction** (Simon Ch. 5, 2.3–2.4,
chapter-05.txt lines 266–288, with radii `4δρ` and `(1 − 4δ)ρ`).  Choose `δ₁ ≤ 1/8` and `C₁`
with `K(δ) := e^δ(1 + δ)(1 − 4δ)^{−n} ≤ 1 + C₁δ ≤ 3/2` on `[0, δ₁]`, and `C₂ = max(1, C₁ωₙ)`.
For `y ∈ B_{4δρ}(z)` and `0 < t ≤ (1 − 4δ)ρ`, monotonicity (Ch. 4, 4.7) and
`μ(B_ρ(z)) ≤ (1 + δ)ωₙρⁿ` give `e^{κt}t^{−n}μ(B_t(y)) ≤ K(δ)ωₙ`, hence (a).  At `y ∈ spt μ` the
density bound `∫_{B_t(y)} F_y dμ + ωₙ ≤ e^{κt}t^{−n}μ(B_t(y))` gives (b), as `e^{κt} ≤ 2`, and
(c), after cancelling `ωₙ < ∞`.  The mass ratio stays `≤ 3/2 < 2` near every point of
`B_{4δρ}(z)`, so `θ = 1` `μ`-a.e. there, which is (d). -/
theorem Submission.dorag_standing_density_bounds : ∀ (n k : ℕ), 0 < n → ∃ δ₁ C₂ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 8 ∧ 0 < C₂ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → (∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → R.measure (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) ∧ (∀ y ∈ R.measure.support ∩ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * R.measure (closedBall y t)) ∧ (∀ y ∈ R.measure.support ∩ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → ∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure ≤ ENNReal.ofReal (C₂ * δ)) ∧ (∀ᵐ x ∂R.measure, x ∈ closedBall z (4 * δ * ρ) → R.mult x = 1) := by
  intro n k hn
  -- Step 0: `K(δ) ≤ 1 + C₁δ` on `[0, δ₁]`, `C₁δ₁ ≤ 1/2`, and `C₂ = max(1, C₁ωₙ)`
  obtain ⟨δ₁, C₁, hδ₁, hδ₁8, hC₁, hC₁δ₁, hK⟩ := Submission.dorag_dbs_density_constants n
  have hω_top : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  refine ⟨δ₁, max 1 (C₁ * (unitBallVolume n).toReal), hδ₁, hδ₁8,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro δ hδ hδδ₁ U W R H κ ρ z hW hWU hρ hball hH hHκ hfv hz hmass hκρ
  have hδ8 : δ ≤ 1 / 8 := hδδ₁.trans hδ₁8
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- monotonicity: `(M1)` without its tilt term, and the density bound `(D)`
  obtain ⟨hmono, hD⟩ := Submission.dorag_monotonicity_density n k hn U W R H κ hW hWU hH hHκ hfv
  have hmono' : ∀ (y : Euclid (n + k)) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W →
      ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
    fun y s t hs hst hy => le_trans le_add_self (hmono y s t hs hst hy).1
  -- Step 2: `e^{κt}t^{−n}μ(B_t(y)) ≤ K(δ)ωₙ` and `μ(B_t(y)) ≤ K(δ)ωₙtⁿ` with `K(δ) ≤ 3/2`
  have hsharp := Submission.dorag_dbs_sharp_mass_ratio (n + k) n R.measure W κ δ ρ z hρ hδ.le
    hδ8 hκ hκρ hball hmass hmono'
  have hK1 : Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 1 + C₁ * δ := hK δ hδ.le hδδ₁
  have hCδ : C₁ * δ ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hδδ₁ hC₁.le) hC₁δ₁
  have hK32 : Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 3 / 2 := by linarith
  -- Step 1: `B_t(y) ⊆ B_ρ(z) ⊆ W` for `y ∈ B_{4δρ}(z)`, `t ≤ (1 − 4δ)ρ`
  have hsub : ∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, t ≤ (1 - 4 * δ) * ρ →
      closedBall y t ⊆ W := by
    intro y hy t ht
    refine Subset.trans ?_ hball
    intro p hp
    rw [mem_closedBall] at hp hy ⊢
    calc dist p z ≤ dist p y + dist y z := dist_triangle p y z
      _ ≤ (1 - 4 * δ) * ρ + 4 * δ * ρ := add_le_add (hp.trans ht) hy
      _ = ρ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a): `K(δ) ≤ 3/2 ≤ 2`
    intro y hy t ht htle
    calc R.measure (closedBall y t)
        ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n *
            ENNReal.ofReal (t ^ n) := (hsharp y hy t ht htle).2
      _ ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n) := by
        gcongr
        calc ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n)
            ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
          _ = 2 := by norm_num
  · -- (b): `ωₙtⁿ ≤ e^{κt}μ(B_t(y))` by `(D)`, and `e^{κt} ≤ 2` as `κt ≤ δ ≤ 1/8`
    rintro y ⟨hysupp, hy⟩ t ht htle
    have hDy := hD y hysupp t ht (hsub y hy t htle)
    have h1 : unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
      le_trans le_add_self hDy
    have htn : 0 < t ^ n := pow_pos ht n
    have h2 : unitBallVolume n * ENNReal.ofReal (t ^ n) ≤
        ENNReal.ofReal (Real.exp (κ * t)) * R.measure (closedBall y t) := by
      calc unitBallVolume n * ENNReal.ofReal (t ^ n)
          ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) *
              ENNReal.ofReal (t ^ n) := by gcongr
        _ = ENNReal.ofReal (Real.exp (κ * t) / t ^ n * t ^ n) * R.measure (closedBall y t) := by
          rw [ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le htn.le)]; ring
        _ = ENNReal.ofReal (Real.exp (κ * t)) * R.measure (closedBall y t) := by
          rw [div_mul_cancel₀ _ htn.ne']
    have hκt : κ * t ≤ 1 / 8 := by
      have h1' : t ≤ ρ := htle.trans (by nlinarith)
      have : κ * t ≤ κ * ρ := mul_le_mul_of_nonneg_left h1' hκ
      linarith
    have hexp : Real.exp (κ * t) ≤ 2 := by
      have hlow := Real.add_one_le_exp (-(κ * t))
      have hprod : Real.exp (κ * t) * Real.exp (-(κ * t)) = 1 := by
        rw [← Real.exp_add]; simp
      have hpos := Real.exp_pos (κ * t)
      nlinarith
    have h3 : ENNReal.ofReal (Real.exp (κ * t)) ≤ 2 := by
      calc ENNReal.ofReal (Real.exp (κ * t)) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hexp
        _ = 2 := by norm_num
    calc unitBallVolume n * ENNReal.ofReal (t ^ n)
        ≤ ENNReal.ofReal (Real.exp (κ * t)) * R.measure (closedBall y t) := h2
      _ ≤ 2 * R.measure (closedBall y t) := by gcongr
  · -- (c): `∫ F_y + ωₙ ≤ K(δ)ωₙ ≤ (1 + C₁δ)ωₙ`; cancel `ωₙ < ∞`
    rintro y ⟨hysupp, hy⟩ t ht htle
    have hDy := hD y hysupp t ht (hsub y hy t htle)
    have hC₁δ0 : 0 ≤ C₁ * δ := mul_nonneg hC₁.le hδ.le
    have h2 : (∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) -
          (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2))
          ∂R.measure) + unitBallVolume n ≤
        ENNReal.ofReal (C₁ * δ) * unitBallVolume n + unitBallVolume n := by
      calc _ ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := hDy
        _ ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n :=
          (hsharp y hy t ht htle).1
        _ ≤ ENNReal.ofReal (1 + C₁ * δ) * unitBallVolume n := by gcongr
        _ = ENNReal.ofReal (C₁ * δ) * unitBallVolume n + unitBallVolume n := by
          rw [ENNReal.ofReal_add (by norm_num) hC₁δ0, ENNReal.ofReal_one, add_mul, one_mul,
            add_comm]
    have h3 := ENNReal.le_of_add_le_add_right hω_top h2
    calc _ ≤ ENNReal.ofReal (C₁ * δ) * unitBallVolume n := h3
      _ = ENNReal.ofReal (C₁ * δ * (unitBallVolume n).toReal) := by
        rw [ENNReal.ofReal_mul hC₁δ0, ENNReal.ofReal_toReal hω_top]
      _ ≤ ENNReal.ofReal (max 1 (C₁ * (unitBallVolume n).toReal) * δ) := by
        apply ENNReal.ofReal_le_ofReal
        have := le_max_right 1 (C₁ * (unitBallVolume n).toReal)
        nlinarith
  · -- (d): on `B_{4δρ}(z)` the mass ratio is `≤ 3/2 < 2` for `0 < t ≤ (1 − 4δ)ρ`
    have hSW : closedBall z (4 * δ * ρ) ⊆ W :=
      (closedBall_subset_closedBall (by nlinarith)).trans hball
    have ht' : 0 < (1 - 4 * δ) * ρ := mul_pos (by linarith) hρ
    refine Submission.dorag_dbs_mult_eq_one_of_density_lt_two (n + k) n U W
      (closedBall z (4 * δ * ρ)) R (3 / 2) hn hW hWU hSW (by norm_num) ?_
    intro x hx
    filter_upwards [Ioc_mem_nhdsGT ht'] with t ht
    calc R.measure (closedBall x t)
        ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n *
            ENNReal.ofReal (t ^ n) := (hsharp x hx t ht.1 ht.2).2
      _ ≤ ENNReal.ofReal (3 / 2) * unitBallVolume n * ENNReal.ofReal (t ^ n) := by gcongr

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)** under the standing
assumptions `(SA_δ)`, with `α = 1/(2n+2)`: for `ξ ∈ spt μ ∩ B̄_{2δρ}(z)` and `r ∈ (0, 2δρ]` some
`n`-plane `S` has `|p_S^⊥(x − ξ)| ≤ C₃δ^α r` on `spt μ ∩ B̄_r(ξ)` and
`∫_{B̄_{r/2}(ξ)} |p_x − p_S|² dμ ≤ C₃δ^{2α}(r/2)ⁿ`.  With `e = δ^α`, a maximal `er`-separated net
`F` of `spt μ ∩ B̄_r(ξ)` has `#F·eⁿ ≤ 2^{2n+2}` by the density bounds; Chebyshev's inequality and
the weighted tilt bounds at the points of `F` give `x₀ ∈ B̄_{er}(ξ)` with `dim T_{x₀}M = n` and
`|p^⊥_{T_{x₀}M}(y − x₀)| ≤ C_λ e r` for `y ∈ F`; `S = T_{x₀}M` then satisfies the height bound,
which the tilt-height estimate turns into the tilt bound. -/
theorem Submission.dorag_affine_approximation : ∀ (n k : ℕ), 0 < n → ∃ δ₃ C₃ : ℝ, 0 < δ₃ ∧ δ₃ ≤ 1 / 8 ∧ 1 ≤ C₃ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₃ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (2 * δ * ρ), ∀ r : ℝ, 0 < r → r ≤ 2 * δ * ρ → ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ C₃ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * r) ∧ ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (C₃ * (δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))) ^ 2 * (r / 2) ^ n) := by
  intro n k hn
  -- Step 0: constants `δ₁, C₂` (density bounds), `C_T` (tilt-height), `w = ωₙ`,
  -- `C_Ψ = 2^{2n+2}·2^{n+2}·C₂` and `C_λ = (4C_Ψ/w)^{1/2}`; `δ₃ = δ₁`
  obtain ⟨δ₁, C₂, hδ₁, hδ₁8, hC₂, hdens⟩ := Submission.dorag_standing_density_bounds n k hn
  obtain ⟨CT, hCT, htilt⟩ := Submission.dorag_tilt_height_estimate n k
  obtain ⟨w, hw, hωw⟩ : ∃ w : ℝ, 0 < w ∧ unitBallVolume n = ENNReal.ofReal w := by
    have hωT : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    exact ⟨(unitBallVolume n).toReal,
      ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclid n) one_pos).ne' hωT,
      (ENNReal.ofReal_toReal hωT).symm⟩
  obtain ⟨CΨ, hCΨ⟩ : ∃ C : ℝ, C = 2 ^ (2 * n + 2) * 2 ^ (n + 2) * C₂ := ⟨_, rfl⟩
  have hCΨ0 : 0 < CΨ := by rw [hCΨ]; positivity
  obtain ⟨CL, hCL0, hCLsq⟩ : ∃ C : ℝ, 0 < C ∧ C ^ 2 = 4 * CΨ / w :=
    ⟨√(4 * CΨ / w), Real.sqrt_pos.mpr (by positivity), Real.sq_sqrt (by positivity)⟩
  refine ⟨δ₁, max 1 (max (CL + 2) (2 ^ n * 2 * w * CT * ((CL + 2) ^ 2 + 1))), hδ₁, hδ₁8,
    le_max_left _ _, ?_⟩
  intro δ hδ hδδ₁ U W R H κ ρ z hW hWU hρ hzW hH hHκ hfv hz hmass hκρ ξ hξ r hr hrδ
  set C₃ := max 1 (max (CL + 2) (2 ^ n * 2 * w * CT * ((CL + 2) ^ 2 + 1)))
  obtain ⟨ha, hb, hc, -⟩ := hdens δ hδ hδδ₁ U W R H κ ρ z hW hWU hρ hzW hH hHκ hfv hz hmass hκρ
  -- the exponent `e = δ^α`: `0 < e ≤ 1` and `δ = e^{2n+2} ≤ e`
  obtain ⟨e, he⟩ : ∃ e : ℝ, δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) = e := ⟨_, rfl⟩
  rw [he]
  have he0 : 0 < e := by rw [← he]; exact Real.rpow_pos_of_pos hδ _
  have hepow : e ^ (2 * n + 2) = δ := by
    rw [← he, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    have h1 : (1 : ℝ) / (2 * (n : ℝ) + 2) * ((2 * n + 2 : ℕ) : ℝ) = 1 := by
      push_cast
      exact one_div_mul_cancel (by positivity)
    rw [h1, Real.rpow_one]
  have hδ8 : δ ≤ 1 / 8 := hδδ₁.trans hδ₁8
  have he1 : e ≤ 1 := by rw [← he]; exact Real.rpow_le_one hδ.le (by linarith) (by positivity)
  have hδe : δ ≤ e := hepow ▸ pow_le_of_le_one he0.le he1 (by omega)
  -- Step 1: radii.  Centres lie in `B̄_{4δρ}(z)` and radii are `≤ 2r ≤ (1 - 4δ)ρ`
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have h8 : 0 ≤ (1 - 8 * δ) * ρ := mul_nonneg (by linarith) hρ.le
  have hξz : dist ξ z ≤ 2 * δ * ρ := mem_closedBall.mp hξ.2
  have hr2 : 2 * r ≤ (1 - 4 * δ) * ρ := by linarith
  have hrρ : r ≤ ρ := by linarith
  have hcen : ∀ y ∈ closedBall ξ r, y ∈ closedBall z (4 * δ * ρ) := fun y hy =>
    mem_closedBall.mpr ((dist_triangle y ξ z).trans (by linarith [mem_closedBall.mp hy]))
  have hξ4 : ξ ∈ R.measure.support ∩ closedBall z (4 * δ * ρ) :=
    ⟨hξ.1, hcen ξ (mem_closedBall_self hr.le)⟩
  -- (a) at `ξ` and (b) at points of `spt μ ∩ B̄_r(ξ)`, as real bounds
  have hup : ∀ t : ℝ, 0 < t → t ≤ 2 * r →
      R.measure (closedBall ξ t) ≤ ENNReal.ofReal (2 * w * t ^ n) := by
    intro t ht htr
    calc R.measure (closedBall ξ t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n) :=
          ha ξ hξ4.2 t ht (htr.trans hr2)
      _ = ENNReal.ofReal (2 * w * t ^ n) := by
          rw [hωw, ENNReal.ofReal_mul (p := 2 * w) (by positivity),
            ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
  have hlow : ∀ y ∈ R.measure.support ∩ closedBall ξ r, ∀ t : ℝ, 0 < t → t ≤ r →
      ENNReal.ofReal (w * t ^ n / 2) ≤ R.measure (closedBall y t) := by
    intro y hy t ht htr
    have h := hb y ⟨hy.1, hcen y hy.2⟩ t ht (by linarith)
    rw [hωw, ← ENNReal.ofReal_mul hw.le] at h
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul (h.trans_eq (mul_comm _ _))
  -- Step 2: a maximal `er`-separated net `F` of `spt μ ∩ B̄_r(ξ)`, with `#F·eⁿ ≤ 2^{2n+2}`
  have hs0 : 0 < e * r := mul_pos he0 hr
  have hsr : e * r ≤ r := mul_le_of_le_one_left hr.le he1
  obtain ⟨F, hFK, hFcard, hFnet⟩ := Submission.dorag_aa_finite_separated_net (n + k) R.measure
    (R.measure.support ∩ closedBall ξ r) (closedBall ξ (2 * r)) (e * r)
    (ENNReal.ofReal (w * (e * r / 2) ^ n / 2)) hs0 (ENNReal.ofReal_pos.mpr (by positivity))
    ((hup (2 * r) (by positivity) le_rfl).trans_lt ENNReal.ofReal_lt_top).ne
    (fun y hy x hx => mem_closedBall.mpr ((dist_triangle x y ξ).trans
      (by linarith [mem_closedBall.mp hx, mem_closedBall.mp hy.2])))
    (fun y hy => hlow y hy _ (by positivity) (by linarith))
  have hcard : (F.card : ℝ) * e ^ n ≤ 2 ^ (2 * n + 2) := by
    have h := hFcard.trans (hup (2 * r) (by positivity) le_rfl)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < w * r ^ n)
    calc (F.card : ℝ) * e ^ n * (w * r ^ n)
        = (F.card : ℝ) * (w * (e * r / 2) ^ n / 2) * (2 ^ n * 2) := by
          rw [div_pow, mul_pow]
          field_simp
      _ ≤ 2 * w * (2 * r) ^ n * (2 ^ n * 2) := by gcongr
      _ = 2 ^ (2 * n + 2) * (w * r ^ n) := by rw [mul_pow]; ring
  -- Steps 3–5: Chebyshev selection of `x₀ ∈ B̄_{er}(ξ)` with `dim T_{x₀}M = n` and
  -- `|p^⊥_{T_{x₀}M}(y − x₀)|² ≤ (C_λ e r)²` for `y ∈ F`
  have hiii : (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ (n + 2) * (C₂ * δ)) <
      ENNReal.ofReal ((CL * e * r) ^ 2) * R.measure (closedBall ξ (e * r)) := by
    have hE : 0 < e ^ (n + 2) * r ^ (n + 2) := by positivity
    have hX : (F.card : ℝ) * ((2 * r) ^ (n + 2) * (C₂ * δ)) ≤
        CΨ * (e ^ (n + 2) * r ^ (n + 2)) := by
      rw [← hepow, hCΨ]
      calc (F.card : ℝ) * ((2 * r) ^ (n + 2) * (C₂ * e ^ (2 * n + 2)))
          = (F.card : ℝ) * e ^ n * (2 ^ (n + 2) * C₂ * (e ^ (n + 2) * r ^ (n + 2))) := by ring
        _ ≤ 2 ^ (2 * n + 2) * (2 ^ (n + 2) * C₂ * (e ^ (n + 2) * r ^ (n + 2))) := by gcongr
        _ = 2 ^ (2 * n + 2) * 2 ^ (n + 2) * C₂ * (e ^ (n + 2) * r ^ (n + 2)) := by ring
    have hY : (CL * e * r) ^ 2 * (w * (e * r) ^ n / 2) =
        2 * CΨ * (e ^ (n + 2) * r ^ (n + 2)) := by
      simp only [mul_pow]
      rw [hCLsq]
      field_simp
      ring
    -- `g + c (φ j)` is admissible for `w (φ j)`: adding a constant leaves `Dg`, `D²g` unchanged
    have hgD : fderiv ℝ (fun x => g x + c (φ j)) = fderiv ℝ g :=
      funext fun x => fderiv_add_const _
    refine hno (φ j) ⟨fun x => g x + c (φ j), fun m => (hgC m).add contDiffOn_const,
      fun y hy => ?_, ?_, ?_, hsq.congr hae, (integral_congr_ae hae).symm.trans_le hj'⟩
    · have h2 : iteratedFDeriv ℝ 2 (fun x => g x + c (φ j)) y = iteratedFDeriv ℝ 2 g y := by
        ext m
        rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hgD]
      rw [h2]
      exact hgΔ y hy
    · rw [hgD]
      exact hgI
    · rw [hgD]
      exact hgE
  -- Scaling: `w₁(y) = R₀⁻¹ w(R₀y)` satisfies the unit-scale hypotheses, and an admissible `h₁`
  -- for `w₁` rescales to `h(x) = R₀ h₁(x/R₀)`
  obtain ⟨δ, hδ, hA⟩ := hunit
  refine ⟨δ, hδ, fun R₀ w Lw hR₀ hLw hE hH => ?_⟩
  obtain ⟨hLw₁, hE₁, hH₁⟩ := Submission.dorag_haa_rescale_hypotheses n δ R₀ w Lw hR₀ hLw hE hH
  obtain ⟨h₁, hC₁, hΔ₁, hI₁, hD₁, hI₂, hε₁⟩ := hA _ Lw hLw₁ hE₁ hH₁
  exact Submission.dorag_haa_rescale_conclusion n ε R₀ w h₁ hR₀ hC₁ hΔ₁ hI₁ hD₁ hI₂ hε₁

/-- **Harmonic approximation with affine decay** (Simon Ch. 5, Lemma 3.1 and estimates 3.2–3.4, as
used in (17')–(19') of the Allard graph proof).  Take the harmonic approximation `h` of `w` on
`B̆_{R₀}(0)` (`dorag_ha_approximation`), `a = h(0)` and `b = Dh(0)`.  The interior estimates
(`dorag_ha_interior_estimates`, constant `C_H`) give `‖b‖ ≤ C_H`, `|a| ≤ C_H (R₀⁻ⁿ∫h²)^{1/2}` and
`|h(v) − a − b(v)| ≤ C_H|v|²/R₀` for `|v| ≤ R₀/4`; with `h² ≤ 2w² + 2(h − w)²` and
`(w − a − b)² ≤ 2(h − w)² + 2(h − a − b)²` this gives the claim for `C = max(√2·C_H, 2, 2ωₙC_H²)`
and `δ_h = δ(ε')`. -/
theorem Submission.dorag_harmonic_affine_approximation : ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧ ∀ ε' : ℝ, 0 < ε' → ∃ δh : ℝ, 0 < δh ∧ ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) → ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ C ∧ |a| ≤ C * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) + C * Real.sqrt ε' * R₀ ∧ ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤ C * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2) := by
  intro n hn
  obtain ⟨CH, hCH, hest⟩ := Submission.dorag_ha_interior_estimates n hn
  -- `C = max(√2·C_H, 2, 2ωₙC_H²)` with `ωₙ = Lⁿ(B̆₁(0))`
  obtain ⟨C, hC1, hC2, hC3⟩ : ∃ C : ℝ, Real.sqrt 2 * CH ≤ C ∧ 2 ≤ C ∧
      2 * (volume (ball (0 : Euclid n) 1)).toReal * CH ^ 2 ≤ C :=
    ⟨max (Real.sqrt 2 * CH) (max 2 (2 * (volume (ball (0 : Euclid n) 1)).toReal * CH ^ 2)),
      le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have hCHC : CH ≤ C := le_trans (by nlinarith) hC1
  refine ⟨C, by linarith, fun ε' hε' => ?_⟩
  obtain ⟨δ, hδ, happrox⟩ := Submission.dorag_ha_approximation n hn ε' hε'
  refine ⟨δ, hδ, fun R₀ w Lw hR₀ hLw hEw hζ => ?_⟩
  -- the harmonic approximation `h` of `w` on `B̆_{R₀}(0)`
  obtain ⟨h, hsmooth, hharm, hDhint, hDh, hdint, hdist⟩ := happrox R₀ w Lw hR₀ hLw hEw hζ
  -- `w` is continuous, so `w²` is integrable on the bounded ball; `h² ≤ 2w² + 2(h − w)²`
  have hwint : IntegrableOn (fun v => w v ^ 2) (ball (0 : Euclid n) R₀) :=
    ((hLw.continuous.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R₀)).mono_set ball_subset_closedBall
  have hbound : ∀ v, h v ^ 2 ≤ 2 * w v ^ 2 + 2 * (h v - w v) ^ 2 := fun v => by
    nlinarith [sq_nonneg (h v - 2 * w v)]
  have hgint : IntegrableOn (fun v => 2 * w v ^ 2 + 2 * (h v - w v) ^ 2)
      (ball (0 : Euclid n) R₀) :=
    (hwint.const_mul 2).add (hdint.const_mul 2)
  have hhint : IntegrableOn (fun v => h v ^ 2) (ball (0 : Euclid n) R₀) := by
    refine hgint.mono' (((hsmooth 0).continuousOn.pow 2).aestronglyMeasurable measurableSet_ball)
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound v
  obtain ⟨ha, hb, htaylor⟩ := hest R₀ h hR₀ hsmooth hharm hDhint hDh hhint
  refine ⟨h 0, fderiv ℝ h 0, hb.trans hCHC, ?_, ?_⟩
  · -- `|a| ≤ C_H (R₀⁻ⁿ∫h²)^{1/2} ≤ √2·C_H ((R₀⁻ⁿ∫w²)^{1/2} + √ε'·R₀)`
    set X := (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n with hX
    have hX0 : 0 ≤ X :=
      div_nonneg (setIntegral_nonneg measurableSet_ball fun v _ => sq_nonneg _) (by positivity)
    have hIh : ∫ v in ball (0 : Euclid n) R₀, h v ^ 2 ≤
        2 * (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) +
          2 * ∫ v in ball (0 : Euclid n) R₀, (h v - w v) ^ 2 := by
      calc ∫ v in ball (0 : Euclid n) R₀, h v ^ 2
          ≤ ∫ v in ball (0 : Euclid n) R₀, (2 * w v ^ 2 + 2 * (h v - w v) ^ 2) :=
            setIntegral_mono hhint hgint hbound
        _ = 2 * (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) +
              2 * ∫ v in ball (0 : Euclid n) R₀, (h v - w v) ^ 2 := by
            rw [integral_add (hwint.const_mul 2) (hdint.const_mul 2), integral_const_mul,
              integral_const_mul]
    have hquot : (∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n ≤
        2 * X + 2 * (ε' * R₀ ^ 2) := by
      rw [div_le_iff₀ (by positivity), hX]
      calc ∫ v in ball (0 : Euclid n) R₀, h v ^ 2
          ≤ 2 * (∫ v in ball (0 : Euclid n) R₀, w v ^ 2) + 2 * (ε' * R₀ ^ (n + 2)) := by
            linarith
        _ = (2 * ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) + 2 * (ε' * R₀ ^ 2)) *
              R₀ ^ n := by
            field_simp
            ring
    -- `√(x + y) ≤ √x + √y`
    have hsqrt_add : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y :=
      fun x y hx hy => by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
    have hsqrt : Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n) ≤
        Real.sqrt 2 * Real.sqrt X + Real.sqrt 2 * (Real.sqrt ε' * R₀) := by
      calc Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n)
          ≤ Real.sqrt (2 * X + 2 * (ε' * R₀ ^ 2)) := Real.sqrt_le_sqrt hquot
        _ ≤ Real.sqrt (2 * X) + Real.sqrt (2 * (ε' * R₀ ^ 2)) :=
            hsqrt_add _ _ (by positivity) (by positivity)
        _ = Real.sqrt 2 * Real.sqrt X + Real.sqrt 2 * (Real.sqrt ε' * R₀) := by
            rw [Real.sqrt_mul zero_le_two, Real.sqrt_mul zero_le_two, Real.sqrt_mul hε'.le,
              Real.sqrt_sq hR₀.le]
    calc |h 0| ≤ CH * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, h v ^ 2) / R₀ ^ n) := ha
      _ ≤ CH * (Real.sqrt 2 * Real.sqrt X + Real.sqrt 2 * (Real.sqrt ε' * R₀)) :=
          mul_le_mul_of_nonneg_left hsqrt hCH.le
      _ = Real.sqrt 2 * CH * Real.sqrt X + Real.sqrt 2 * CH * Real.sqrt ε' * R₀ := by ring
      _ ≤ C * Real.sqrt X + C * Real.sqrt ε' * R₀ := by gcongr
  · -- `∫_{B̆_{θ'R₀}} (w − a − b)² ≤ 2∫_{B̆_{R₀}} (h − w)² + 2 Lⁿ(B̆_{θ'R₀}) (C_H (θ'R₀)²/R₀)²`
    intro θ' hθ' hθ'4
    have hr : 0 < θ' * R₀ := mul_pos hθ' hR₀
    have hsub : ball (0 : Euclid n) (θ' * R₀) ⊆ ball 0 R₀ := ball_subset_ball (by nlinarith)
    have hpt : ∀ v ∈ ball (0 : Euclid n) (θ' * R₀), (w v - h 0 - fderiv ℝ h 0 v) ^ 2 ≤
        2 * (h v - w v) ^ 2 + 2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 := by
      intro v hv
      have hv' : ‖v‖ ≤ θ' * R₀ := (mem_ball_zero_iff.mp hv).le
      have h1 : |h v - h 0 - fderiv ℝ h 0 v| ≤ CH * (θ' * R₀) ^ 2 / R₀ :=
        (htaylor v (by nlinarith)).trans (by gcongr)
      have h2 : (h v - h 0 - fderiv ℝ h 0 v) ^ 2 ≤ (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith [sq_nonneg ((h v - w v) + (h v - h 0 - fderiv ℝ h 0 v))]
    have hdint' : IntegrableOn (fun v => (h v - w v) ^ 2) (ball (0 : Euclid n) (θ' * R₀)) :=
      hdint.mono_set hsub
    have hcint : IntegrableOn (fun _ : Euclid n => 2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2)
        (ball (0 : Euclid n) (θ' * R₀)) :=
      integrableOn_const measure_ball_lt_top.ne
    have hvol : volume.real (ball (0 : Euclid n) (θ' * R₀)) =
        (θ' * R₀) ^ n * (volume (ball (0 : Euclid n) 1)).toReal := by
      rw [measureReal_def, Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    have hsmall : ∫ v in ball (0 : Euclid n) (θ' * R₀), (h v - w v) ^ 2 ≤ ε' * R₀ ^ (n + 2) :=
      (setIntegral_mono_set hdint (Eventually.of_forall fun v => sq_nonneg _)
        hsub.eventuallyLE).trans hdist
    calc ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - h 0 - fderiv ℝ h 0 v) ^ 2
        ≤ ∫ v in ball (0 : Euclid n) (θ' * R₀),
            (2 * (h v - w v) ^ 2 + 2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall fun v => sq_nonneg _)
            ((hdint'.const_mul 2).add hcint) (ae_restrict_of_forall_mem measurableSet_ball hpt)
      _ = 2 * (∫ v in ball (0 : Euclid n) (θ' * R₀), (h v - w v) ^ 2) +
            2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 *
              ((θ' * R₀) ^ n * (volume (ball (0 : Euclid n) 1)).toReal) := by
          rw [integral_add (hdint'.const_mul 2) hcint, setIntegral_const, integral_const_mul, hvol,
            smul_eq_mul]
          ring
      _ ≤ 2 * (ε' * R₀ ^ (n + 2)) +
            2 * (CH * (θ' * R₀) ^ 2 / R₀) ^ 2 *
              ((θ' * R₀) ^ n * (volume (ball (0 : Euclid n) 1)).toReal) := by
          gcongr
      _ = 2 * (ε' / θ' ^ (n + 2)) * (θ' * R₀) ^ (n + 2) +
            2 * (volume (ball (0 : Euclid n) 1)).toReal * CH ^ 2 * θ' ^ 2 *
              (θ' * R₀) ^ (n + 2) := by
          field_simp
          ring
      _ ≤ C * (ε' / θ' ^ (n + 2)) * (θ' * R₀) ^ (n + 2) + C * θ' ^ 2 * (θ' * R₀) ^ (n + 2) := by
          gcongr
      _ = C * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2) := by ring
/-- **Standing density bounds for the Allard graph construction** (Simon Ch. 5, 2.3–2.4,
chapter-05.txt lines 266–288, with radii `4δρ` and `(1 − 4δ)ρ`).  Choose `δ₁ ≤ 1/8` and `C₁`
with `K(δ) := e^δ(1 + δ)(1 − 4δ)^{−n} ≤ 1 + C₁δ ≤ 3/2` on `[0, δ₁]`, and `C₂ = max(1, C₁ωₙ)`.
For `y ∈ B_{4δρ}(z)` and `0 < t ≤ (1 − 4δ)ρ`, monotonicity (Ch. 4, 4.7) and
`μ(B_ρ(z)) ≤ (1 + δ)ωₙρⁿ` give `e^{κt}t^{−n}μ(B_t(y)) ≤ K(δ)ωₙ`, hence (a).  At `y ∈ spt μ` the
density bound `∫_{B_t(y)} F_y dμ + ωₙ ≤ e^{κt}t^{−n}μ(B_t(y))` gives (b), as `e^{κt} ≤ 2`, and
(c), after cancelling `ωₙ < ∞`.  The mass ratio stays `≤ 3/2 < 2` near every point of
`B_{4δρ}(z)`, so `θ = 1` `μ`-a.e. there, which is (d). -/
theorem Submission.dorag_standing_density_bounds : ∀ (n k : ℕ), 0 < n → ∃ δ₁ C₂ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 8 ∧ 0 < C₂ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → (∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → R.measure (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) ∧ (∀ y ∈ R.measure.support ∩ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * R.measure (closedBall y t)) ∧ (∀ y ∈ R.measure.support ∩ closedBall z (4 * δ * ρ), ∀ t : ℝ, 0 < t → t ≤ (1 - 4 * δ) * ρ → ∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure ≤ ENNReal.ofReal (C₂ * δ)) ∧ (∀ᵐ x ∂R.measure, x ∈ closedBall z (4 * δ * ρ) → R.mult x = 1) := by
  intro n k hn
  -- Step 0: `K(δ) ≤ 1 + C₁δ` on `[0, δ₁]`, `C₁δ₁ ≤ 1/2`, and `C₂ = max(1, C₁ωₙ)`
  obtain ⟨δ₁, C₁, hδ₁, hδ₁8, hC₁, hC₁δ₁, hK⟩ := Submission.dorag_dbs_density_constants n
  have hω_top : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  refine ⟨δ₁, max 1 (C₁ * (unitBallVolume n).toReal), hδ₁, hδ₁8,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro δ hδ hδδ₁ U W R H κ ρ z hW hWU hρ hball hH hHκ hfv hz hmass hκρ
  have hδ8 : δ ≤ 1 / 8 := hδδ₁.trans hδ₁8
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- monotonicity: `(M1)` without its tilt term, and the density bound `(D)`
  obtain ⟨hmono, hD⟩ := Submission.dorag_monotonicity_density n k hn U W R H κ hW hWU hH hHκ hfv
  have hmono' : ∀ (y : Euclid (n + k)) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W →
      ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
    fun y s t hs hst hy => le_trans le_add_self (hmono y s t hs hst hy).1
  -- Step 2: `e^{κt}t^{−n}μ(B_t(y)) ≤ K(δ)ωₙ` and `μ(B_t(y)) ≤ K(δ)ωₙtⁿ` with `K(δ) ≤ 3/2`
  have hsharp := Submission.dorag_dbs_sharp_mass_ratio (n + k) n R.measure W κ δ ρ z hρ hδ.le
    hδ8 hκ hκρ hball hmass hmono'
  have hK1 : Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 1 + C₁ * δ := hK δ hδ.le hδδ₁
  have hCδ : C₁ * δ ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hδδ₁ hC₁.le) hC₁δ₁
  have hK32 : Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n ≤ 3 / 2 := by linarith
  -- Step 1: `B_t(y) ⊆ B_ρ(z) ⊆ W` for `y ∈ B_{4δρ}(z)`, `t ≤ (1 − 4δ)ρ`
  have hsub : ∀ y ∈ closedBall z (4 * δ * ρ), ∀ t : ℝ, t ≤ (1 - 4 * δ) * ρ →
      closedBall y t ⊆ W := by
    intro y hy t ht
    refine Subset.trans ?_ hball
    intro p hp
    rw [mem_closedBall] at hp hy ⊢
    calc dist p z ≤ dist p y + dist y z := dist_triangle p y z
      _ ≤ (1 - 4 * δ) * ρ + 4 * δ * ρ := add_le_add (hp.trans ht) hy
      _ = ρ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a): `K(δ) ≤ 3/2 ≤ 2`
    intro y hy t ht htle
    calc R.measure (closedBall y t)
        ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n *
            ENNReal.ofReal (t ^ n) := (hsharp y hy t ht htle).2
      _ ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n) := by
        gcongr
        calc ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n)
            ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal (by linarith)
          _ = 2 := by norm_num
  · -- (b): `ωₙtⁿ ≤ e^{κt}μ(B_t(y))` by `(D)`, and `e^{κt} ≤ 2` as `κt ≤ δ ≤ 1/8`
    rintro y ⟨hysupp, hy⟩ t ht htle
    have hDy := hD y hysupp t ht (hsub y hy t htle)
    have h1 : unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
      le_trans le_add_self hDy
    have htn : 0 < t ^ n := pow_pos ht n
    have h2 : unitBallVolume n * ENNReal.ofReal (t ^ n) ≤
        ENNReal.ofReal (Real.exp (κ * t)) * R.measure (closedBall y t) := by
      calc unitBallVolume n * ENNReal.ofReal (t ^ n)
          ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) *
              ENNReal.ofReal (t ^ n) := by gcongr
        _ = ENNReal.ofReal (Real.exp (κ * t) / t ^ n * t ^ n) * R.measure (closedBall y t) := by
          rw [ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le htn.le)]; ring
        _ = ENNReal.ofReal (Real.exp (κ * t)) * R.measure (closedBall y t) := by
          rw [div_mul_cancel₀ _ htn.ne']
    have hκt : κ * t ≤ 1 / 8 := by
      have h1' : t ≤ ρ := htle.trans (by nlinarith)
      have : κ * t ≤ κ * ρ := mul_le_mul_of_nonneg_left h1' hκ
      linarith
    have hexp : Real.exp (κ * t) ≤ 2 := by
      have hlow := Real.add_one_le_exp (-(κ * t))
      have hprod : Real.exp (κ * t) * Real.exp (-(κ * t)) = 1 := by
        rw [← Real.exp_add]; simp
      have hpos := Real.exp_pos (κ * t)
      nlinarith
    have h3 : ENNReal.ofReal (Real.exp (κ * t)) ≤ 2 := by
      calc ENNReal.ofReal (Real.exp (κ * t)) ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hexp
        _ = 2 := by norm_num
    calc unitBallVolume n * ENNReal.ofReal (t ^ n)
        ≤ ENNReal.ofReal (Real.exp (κ * t)) * R.measure (closedBall y t) := h2
      _ ≤ 2 * R.measure (closedBall y t) := by gcongr
  · -- (c): `∫ F_y + ωₙ ≤ K(δ)ωₙ ≤ (1 + C₁δ)ωₙ`; cancel `ωₙ < ∞`
    rintro y ⟨hysupp, hy⟩ t ht htle
    have hDy := hD y hysupp t ht (hsub y hy t htle)
    have hC₁δ0 : 0 ≤ C₁ * δ := mul_nonneg hC₁.le hδ.le
    have h2 : (∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) -
          (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2))
          ∂R.measure) + unitBallVolume n ≤
        ENNReal.ofReal (C₁ * δ) * unitBallVolume n + unitBallVolume n := by
      calc _ ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := hDy
        _ ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n :=
          (hsharp y hy t ht htle).1
        _ ≤ ENNReal.ofReal (1 + C₁ * δ) * unitBallVolume n := by gcongr
        _ = ENNReal.ofReal (C₁ * δ) * unitBallVolume n + unitBallVolume n := by
          rw [ENNReal.ofReal_add (by norm_num) hC₁δ0, ENNReal.ofReal_one, add_mul, one_mul,
            add_comm]
    have h3 := ENNReal.le_of_add_le_add_right hω_top h2
    calc _ ≤ ENNReal.ofReal (C₁ * δ) * unitBallVolume n := h3
      _ = ENNReal.ofReal (C₁ * δ * (unitBallVolume n).toReal) := by
        rw [ENNReal.ofReal_mul hC₁δ0, ENNReal.ofReal_toReal hω_top]
      _ ≤ ENNReal.ofReal (max 1 (C₁ * (unitBallVolume n).toReal) * δ) := by
        apply ENNReal.ofReal_le_ofReal
        have := le_max_right 1 (C₁ * (unitBallVolume n).toReal)
        nlinarith
  · -- (d): on `B_{4δρ}(z)` the mass ratio is `≤ 3/2 < 2` for `0 < t ≤ (1 − 4δ)ρ`
    have hSW : closedBall z (4 * δ * ρ) ⊆ W :=
      (closedBall_subset_closedBall (by nlinarith)).trans hball
    have ht' : 0 < (1 - 4 * δ) * ρ := mul_pos (by linarith) hρ
    refine Submission.dorag_dbs_mult_eq_one_of_density_lt_two (n + k) n U W
      (closedBall z (4 * δ * ρ)) R (3 / 2) hn hW hWU hSW (by norm_num) ?_
    intro x hx
    filter_upwards [Ioc_mem_nhdsGT ht'] with t ht
    calc R.measure (closedBall x t)
        ≤ ENNReal.ofReal (Real.exp δ * (1 + δ) / (1 - 4 * δ) ^ n) * unitBallVolume n *
            ENNReal.ofReal (t ^ n) := (hsharp x hx t ht.1 ht.2).2
      _ ≤ ENNReal.ofReal (3 / 2) * unitBallVolume n * ENNReal.ofReal (t ^ n) := by gcongr

/-- **Simon Ch. 5, Lemma 2.5 (Affine Approximation Lemma, p. 108)** under the standing
assumptions `(SA_δ)`, with `α = 1/(2n+2)`: for `ξ ∈ spt μ ∩ B̄_{2δρ}(z)` and `r ∈ (0, 2δρ]` some
`n`-plane `S` has `|p_S^⊥(x − ξ)| ≤ C₃δ^α r` on `spt μ ∩ B̄_r(ξ)` and
`∫_{B̄_{r/2}(ξ)} |p_x − p_S|² dμ ≤ C₃δ^{2α}(r/2)ⁿ`.  With `e = δ^α`, a maximal `er`-separated net
`F` of `spt μ ∩ B̄_r(ξ)` has `#F·eⁿ ≤ 2^{2n+2}` by the density bounds; Chebyshev's inequality and
the weighted tilt bounds at the points of `F` give `x₀ ∈ B̄_{er}(ξ)` with `dim T_{x₀}M = n` and
`|p^⊥_{T_{x₀}M}(y − x₀)| ≤ C_λ e r` for `y ∈ F`; `S = T_{x₀}M` then satisfies the height bound,
which the tilt-height estimate turns into the tilt bound. -/
theorem Submission.dorag_affine_approximation : ∀ (n k : ℕ), 0 < n → ∃ δ₃ C₃ : ℝ, 0 < δ₃ ∧ δ₃ ≤ 1 / 8 ∧ 1 ≤ C₃ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₃ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (2 * δ * ρ), ∀ r : ℝ, 0 < r → r ≤ 2 * δ * ρ → ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ C₃ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * r) ∧ ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (C₃ * (δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))) ^ 2 * (r / 2) ^ n) := by
  intro n k hn
  -- Step 0: constants `δ₁, C₂` (density bounds), `C_T` (tilt-height), `w = ωₙ`,
  -- `C_Ψ = 2^{2n+2}·2^{n+2}·C₂` and `C_λ = (4C_Ψ/w)^{1/2}`; `δ₃ = δ₁`
  obtain ⟨δ₁, C₂, hδ₁, hδ₁8, hC₂, hdens⟩ := Submission.dorag_standing_density_bounds n k hn
  obtain ⟨CT, hCT, htilt⟩ := Submission.dorag_tilt_height_estimate n k
  obtain ⟨w, hw, hωw⟩ : ∃ w : ℝ, 0 < w ∧ unitBallVolume n = ENNReal.ofReal w := by
    have hωT : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    exact ⟨(unitBallVolume n).toReal,
      ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclid n) one_pos).ne' hωT,
      (ENNReal.ofReal_toReal hωT).symm⟩
  obtain ⟨CΨ, hCΨ⟩ : ∃ C : ℝ, C = 2 ^ (2 * n + 2) * 2 ^ (n + 2) * C₂ := ⟨_, rfl⟩
  have hCΨ0 : 0 < CΨ := by rw [hCΨ]; positivity
  obtain ⟨CL, hCL0, hCLsq⟩ : ∃ C : ℝ, 0 < C ∧ C ^ 2 = 4 * CΨ / w :=
    ⟨√(4 * CΨ / w), Real.sqrt_pos.mpr (by positivity), Real.sq_sqrt (by positivity)⟩
  refine ⟨δ₁, max 1 (max (CL + 2) (2 ^ n * 2 * w * CT * ((CL + 2) ^ 2 + 1))), hδ₁, hδ₁8,
    le_max_left _ _, ?_⟩
  intro δ hδ hδδ₁ U W R H κ ρ z hW hWU hρ hzW hH hHκ hfv hz hmass hκρ ξ hξ r hr hrδ
  set C₃ := max 1 (max (CL + 2) (2 ^ n * 2 * w * CT * ((CL + 2) ^ 2 + 1)))
  obtain ⟨ha, hb, hc, -⟩ := hdens δ hδ hδδ₁ U W R H κ ρ z hW hWU hρ hzW hH hHκ hfv hz hmass hκρ
  -- the exponent `e = δ^α`: `0 < e ≤ 1` and `δ = e^{2n+2} ≤ e`
  obtain ⟨e, he⟩ : ∃ e : ℝ, δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) = e := ⟨_, rfl⟩
  rw [he]
  have he0 : 0 < e := by rw [← he]; exact Real.rpow_pos_of_pos hδ _
  have hepow : e ^ (2 * n + 2) = δ := by
    rw [← he, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    have h1 : (1 : ℝ) / (2 * (n : ℝ) + 2) * ((2 * n + 2 : ℕ) : ℝ) = 1 := by
      push_cast
      exact one_div_mul_cancel (by positivity)
    rw [h1, Real.rpow_one]
  have hδ8 : δ ≤ 1 / 8 := hδδ₁.trans hδ₁8
  have he1 : e ≤ 1 := by rw [← he]; exact Real.rpow_le_one hδ.le (by linarith) (by positivity)
  have hδe : δ ≤ e := hepow ▸ pow_le_of_le_one he0.le he1 (by omega)
  -- Step 1: radii.  Centres lie in `B̄_{4δρ}(z)` and radii are `≤ 2r ≤ (1 - 4δ)ρ`
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have h8 : 0 ≤ (1 - 8 * δ) * ρ := mul_nonneg (by linarith) hρ.le
  have hξz : dist ξ z ≤ 2 * δ * ρ := mem_closedBall.mp hξ.2
  have hr2 : 2 * r ≤ (1 - 4 * δ) * ρ := by linarith
  have hrρ : r ≤ ρ := by linarith
  have hcen : ∀ y ∈ closedBall ξ r, y ∈ closedBall z (4 * δ * ρ) := fun y hy =>
    mem_closedBall.mpr ((dist_triangle y ξ z).trans (by linarith [mem_closedBall.mp hy]))
  have hξ4 : ξ ∈ R.measure.support ∩ closedBall z (4 * δ * ρ) :=
    ⟨hξ.1, hcen ξ (mem_closedBall_self hr.le)⟩
  -- (a) at `ξ` and (b) at points of `spt μ ∩ B̄_r(ξ)`, as real bounds
  have hup : ∀ t : ℝ, 0 < t → t ≤ 2 * r →
      R.measure (closedBall ξ t) ≤ ENNReal.ofReal (2 * w * t ^ n) := by
    intro t ht htr
    calc R.measure (closedBall ξ t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n) :=
          ha ξ hξ4.2 t ht (htr.trans hr2)
      _ = ENNReal.ofReal (2 * w * t ^ n) := by
          rw [hωw, ENNReal.ofReal_mul (p := 2 * w) (by positivity),
            ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_ofNat]
  have hlow : ∀ y ∈ R.measure.support ∩ closedBall ξ r, ∀ t : ℝ, 0 < t → t ≤ r →
      ENNReal.ofReal (w * t ^ n / 2) ≤ R.measure (closedBall y t) := by
    intro y hy t ht htr
    have h := hb y ⟨hy.1, hcen y hy.2⟩ t ht (by linarith)
    rw [hωw, ← ENNReal.ofReal_mul hw.le] at h
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul (h.trans_eq (mul_comm _ _))
  -- Step 2: a maximal `er`-separated net `F` of `spt μ ∩ B̄_r(ξ)`, with `#F·eⁿ ≤ 2^{2n+2}`
  have hs0 : 0 < e * r := mul_pos he0 hr
  have hsr : e * r ≤ r := mul_le_of_le_one_left hr.le he1
  obtain ⟨F, hFK, hFcard, hFnet⟩ := Submission.dorag_aa_finite_separated_net (n + k) R.measure
    (R.measure.support ∩ closedBall ξ r) (closedBall ξ (2 * r)) (e * r)
    (ENNReal.ofReal (w * (e * r / 2) ^ n / 2)) hs0 (ENNReal.ofReal_pos.mpr (by positivity))
    ((hup (2 * r) (by positivity) le_rfl).trans_lt ENNReal.ofReal_lt_top).ne
    (fun y hy x hx => mem_closedBall.mpr ((dist_triangle x y ξ).trans
      (by linarith [mem_closedBall.mp hx, mem_closedBall.mp hy.2])))
    (fun y hy => hlow y hy _ (by positivity) (by linarith))
  have hcard : (F.card : ℝ) * e ^ n ≤ 2 ^ (2 * n + 2) := by
    have h := hFcard.trans (hup (2 * r) (by positivity) le_rfl)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < w * r ^ n)
    calc (F.card : ℝ) * e ^ n * (w * r ^ n)
        = (F.card : ℝ) * (w * (e * r / 2) ^ n / 2) * (2 ^ n * 2) := by
          rw [div_pow, mul_pow]
          field_simp
      _ ≤ 2 * w * (2 * r) ^ n * (2 ^ n * 2) := by gcongr
      _ = 2 ^ (2 * n + 2) * (w * r ^ n) := by rw [mul_pow]; ring
  -- Steps 3–5: Chebyshev selection of `x₀ ∈ B̄_{er}(ξ)` with `dim T_{x₀}M = n` and
  -- `|p^⊥_{T_{x₀}M}(y − x₀)|² ≤ (C_λ e r)²` for `y ∈ F`
  have hiii : (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ (n + 2) * (C₂ * δ)) <
      ENNReal.ofReal ((CL * e * r) ^ 2) * R.measure (closedBall ξ (e * r)) := by
    have hE : 0 < e ^ (n + 2) * r ^ (n + 2) := by positivity
    have hX : (F.card : ℝ) * ((2 * r) ^ (n + 2) * (C₂ * δ)) ≤
        CΨ * (e ^ (n + 2) * r ^ (n + 2)) := by
      rw [← hepow, hCΨ]
      calc (F.card : ℝ) * ((2 * r) ^ (n + 2) * (C₂ * e ^ (2 * n + 2)))
          = (F.card : ℝ) * e ^ n * (2 ^ (n + 2) * C₂ * (e ^ (n + 2) * r ^ (n + 2))) := by ring
        _ ≤ 2 ^ (2 * n + 2) * (2 ^ (n + 2) * C₂ * (e ^ (n + 2) * r ^ (n + 2))) := by gcongr
        _ = 2 ^ (2 * n + 2) * 2 ^ (n + 2) * C₂ * (e ^ (n + 2) * r ^ (n + 2)) := by ring
    have hY : (CL * e * r) ^ 2 * (w * (e * r) ^ n / 2) =
        2 * CΨ * (e ^ (n + 2) * r ^ (n + 2)) := by
      simp only [mul_pow]
      rw [hCLsq]
      field_simp
      ring
    calc (F.card : ℝ≥0∞) * ENNReal.ofReal ((2 * r) ^ (n + 2) * (C₂ * δ))
        = ENNReal.ofReal ((F.card : ℝ) * ((2 * r) ^ (n + 2) * (C₂ * δ))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ < ENNReal.ofReal ((CL * e * r) ^ 2 * (w * (e * r) ^ n / 2)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith [mul_pos hCΨ0 hE])
      _ = ENNReal.ofReal ((CL * e * r) ^ 2) * ENNReal.ofReal (w * (e * r) ^ n / 2) :=
          ENNReal.ofReal_mul (sq_nonneg _)
      _ ≤ ENNReal.ofReal ((CL * e * r) ^ 2) * R.measure (closedBall ξ (e * r)) := by
          gcongr
          exact hlow ξ ⟨hξ.1, mem_closedBall_self hr.le⟩ _ hs0 hsr
  obtain ⟨x₀, hx₀, hx₀n, hx₀F⟩ := Submission.dorag_aa_exists_low_height_point (n + k) (n + 2)
    R.measure (approxTangentPlane n R.carrier)
    (fun x => Module.finrank ℝ (approxTangentPlane n R.carrier x) = n) F ξ r (e * r) (C₂ * δ)
    ((CL * e * r) ^ 2) (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R)
    (Submission.dorag_aa_ae_finrank_approxTangentPlane (n + k) n U R) hr hsr
    (fun y hy => mem_closedBall.mp (hFK hy).2)
    (fun y hy => hc y ⟨(hFK hy).1, hcen y (hFK hy).2⟩ (2 * r) (by positivity) hr2) hiii
  -- Steps 6–7: `S = T_{x₀}M`; every point of `spt μ ∩ B̄_r(ξ)` is within `(2 + C_λ)er` of `ξ + S`
  obtain ⟨h4a, hint⟩ := Submission.dorag_aa_height_bounds_of_net (n + k) R.measure
    (approxTangentPlane n R.carrier x₀) F ξ x₀ r (e * r) (CL * e * r) hFnet
    (fun y hy => le_of_sq_le_sq (hx₀F y hy) (by positivity)) (mem_closedBall.mp hx₀)
  refine ⟨approxTangentPlane n R.carrier x₀, hx₀n, fun x hx => (h4a x hx).trans ?_, ?_⟩
  · calc 2 * (e * r) + CL * e * r = (CL + 2) * (e * r) := by ring
      _ ≤ C₃ * (e * r) := by gcongr; exact le_max_of_le_right (le_max_left _ _)
      _ = C₃ * e * r := by ring
  -- Step 8: the tilt-height estimate at `(ξ, r, S)`, with `μ(B̄_r(ξ)) ≤ 2wrⁿ` and `κr ≤ δ ≤ e`
  · have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
    have hκr : κ * r ≤ e := (mul_le_mul_of_nonneg_left hrρ hκ0).trans (hκρ.trans hδe)
    have hBW : closedBall ξ r ⊆ W := fun x hx => hzW (mem_closedBall.mpr
      ((dist_triangle x ξ z).trans (by linarith [mem_closedBall.mp hx])))
    have hμr := hup r hr (by linarith)
    have hA : 0 ≤ 1 / r ^ 2 * ((2 * (e * r) + CL * e * r) ^ 2 * (2 * w * r ^ n)) := by
      positivity
    have hB : 0 ≤ κ ^ 2 * r ^ 2 * (2 * w * r ^ n) := by positivity
    calc _ ≤ _ := htilt U W R H κ ξ r _ hW hWU hH hHκ hfv hr hBW hx₀n
      _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal (1 / r ^ 2) *
            (ENNReal.ofReal ((2 * (e * r) + CL * e * r) ^ 2) * ENNReal.ofReal (2 * w * r ^ n)) +
            ENNReal.ofReal (κ ^ 2 * r ^ 2) * ENNReal.ofReal (2 * w * r ^ n)) := by
          gcongr
          exact hint.trans (by gcongr)
      _ = ENNReal.ofReal (CT * (1 / r ^ 2 * ((2 * (e * r) + CL * e * r) ^ 2 * (2 * w * r ^ n)) +
            κ ^ 2 * r ^ 2 * (2 * w * r ^ n))) := by
          rw [ENNReal.ofReal_mul hCT.le, ENNReal.ofReal_add hA hB,
            ENNReal.ofReal_mul (p := 1 / r ^ 2) (by positivity),
            ENNReal.ofReal_mul (p := (2 * (e * r) + CL * e * r) ^ 2) (sq_nonneg _),
            ENNReal.ofReal_mul (p := κ ^ 2 * r ^ 2) (by positivity)]
      _ ≤ ENNReal.ofReal (C₃ * e ^ 2 * (r / 2) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have hκ2 : κ ^ 2 * r ^ 2 ≤ e ^ 2 := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) hκr 2
          have hrn : r ^ n = 2 ^ n * (r / 2) ^ n := by
            rw [div_pow]
            field_simp
          calc CT * (1 / r ^ 2 * ((2 * (e * r) + CL * e * r) ^ 2 * (2 * w * r ^ n)) +
                κ ^ 2 * r ^ 2 * (2 * w * r ^ n))
              = CT * ((CL + 2) ^ 2 * e ^ 2 * (2 * w * r ^ n) +
                  κ ^ 2 * r ^ 2 * (2 * w * r ^ n)) := by
                field_simp
                ring
            _ ≤ CT * ((CL + 2) ^ 2 * e ^ 2 * (2 * w * r ^ n) + e ^ 2 * (2 * w * r ^ n)) := by
                gcongr
            _ = 2 ^ n * 2 * w * CT * ((CL + 2) ^ 2 + 1) * (e ^ 2 * (r / 2) ^ n) := by
                rw [hrn]
                ring
            _ ≤ C₃ * (e ^ 2 * (r / 2) ^ n) := by
                gcongr
                exact le_max_of_le_right (le_max_right _ _)
            _ = C₃ * e ^ 2 * (r / 2) ^ n := by ring

/-- **Lipschitz approximation** (Simon Ch. 5, Lemma 2.6 and Corollary 2.7, with the corrections of
the accepted proof: the `Hⁿ`-estimate is on `B_{σ₀/4}(ξ)`, the graph conclusion on `B_{σ₀/8}(ξ)`,
and `sup |f|` carries the factor `σ₀`).  Write `μ = μ_V`, `P = p_{T₀}`, `Q = I − P`,
`ε = δ^{1/(2n+2)}` and `e(x) = |p_x − P|²`.  Take `δ₅ = min(δ₁, δ₃)` from the density bounds and the
affine approximation, `C₈` from the good-set cone estimate, `λ₀, C₉` from the off-support estimate,
`β = min(1/4, 1/(2C₈), 1/D, λ₀/D)` with `D = 2√k C₈ + 1`, and `β' = min(β, 1/(2·5ⁿC₉))`.

The good set `G = {y ∈ spt μ ∩ B_{3σ₀/4}(ξ) : ∫_{B_{t/2}(y)} e dμ ≤ β²L²tⁿ for t ∈ (0, σ₀/2]}`
satisfies `|Q(y₂ − y₁)| ≤ C₈βL|y₂ − y₁|` (cone estimate, fed by the affine approximation and the
lower density bound), so it lies in the graph `F` of some `f` with `Lip f ≤ 2√k C₈βL ≤ L` and
`|f| ≤ √k C₆εσ₀` (graph extension).  The bad-set bound gives
`μ(B_{3σ₀/4}(ξ) ∖ G) ≤ 2(5/2)ⁿωₙ(βL)⁻² ∫_{B_{σ₀}(ξ)} e dμ`, and the off-support estimate (from the
monotonicity identity `(M2)` and the density bounds) with the hole-measure bound gives
`Hⁿ((F ∖ spt μ) ∩ B_{σ₀/4}(ξ)) ≤ 2^{n/2}ωₙ15ⁿC₉(μ(B_{3σ₀/4}(ξ) ∖ F) + ∫_{B_{3σ₀/4}(ξ)} e dμ)`;
adding these gives 5A.  Under the hypothesis of 5B, `spt μ ∩ B_{σ₀/2}(ξ) ⊆ G ⊆ F`, and a point of
`(F ∖ spt μ) ∩ B_{σ₀/8}(ξ)` would give `sⁿ ≤ C₉5ⁿβ'²L²sⁿ ≤ sⁿ/2` in the off-support estimate. -/
theorem Submission.dorag_lipschitz_approximation : ∀ (n k : ℕ), 0 < n → ∀ C₆ : ℝ, 1 ≤ C₆ → ∃ δ₅ β β' C₇ : ℝ, 0 < δ₅ ∧ δ₅ ≤ 1 / 8 ∧ 0 < β' ∧ β' ≤ β ∧ β ≤ 1 / 4 ∧ 0 < C₇ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₅ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ₀ L : ℝ) (T₀ : Submodule ℝ (Euclid (n + k))), 0 < σ₀ → σ₀ ≤ δ * ρ → Module.finrank ℝ T₀ = n → 0 < L → L ≤ 1 → δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ≤ β * L → ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (C₆ * (δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))) ^ 2 * σ₀ ^ n) → (∀ x ∈ R.measure.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * σ₀) → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ v, ι v ∈ T₀) ∧ (∀ v w, ‖f v - f w‖ ≤ L * ‖v - w‖) ∧ (∀ v, ‖f v‖ ≤ C₇ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * σ₀) ∧ R.measure (closedBall ξ (σ₀ / 2) \ range (fun v => ξ + ι v + ι' (f v))) + μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤ ENNReal.ofReal (C₇ / L ^ 2) * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ∧ ((∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y t, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n)) → R.measure.support ∩ closedBall ξ (σ₀ / 8) = range (fun v => ξ + ι v + ι' (f v)) ∩ closedBall ξ (σ₀ / 8)) := by
  intro n k hn C₆ hC₆
  obtain ⟨δ₁, C₂, hδ₁, hδ₁8, -, hdens⟩ := Submission.dorag_standing_density_bounds n k hn
  obtain ⟨δ₃, C₃, hδ₃, -, hC₃, haff⟩ := Submission.dorag_affine_approximation n k hn
  obtain ⟨C₈, hC₈, hcone⟩ := Submission.dorag_lip_good_set_cone_estimate n k C₃ C₆ hC₃ hC₆
  obtain ⟨lam₀, C₉, hlam₀, hC₉, hoff⟩ := Submission.dorag_lip_off_support_estimate n k
  -- `ωₙ = ω` with `0 < ω < ∞`
  obtain ⟨ω, hω, hωeq⟩ : ∃ ω : ℝ, 0 < ω ∧ unitBallVolume n = ENNReal.ofReal ω := by
    have h1 : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    have h2 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
    exact ⟨_, ENNReal.toReal_pos h2 h1, (ENNReal.ofReal_toReal h1).symm⟩
  -- `β = min(1/4, 1/(2C₈), 1/D, λ₀/D)` with `D = 2√k C₈ + 1`
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  obtain ⟨β, hβ, hβ4, hβC₈, hβk, hβlam⟩ : ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧ C₈ * β ≤ 1 / 2 ∧
      2 * Real.sqrt k * C₈ * β ≤ 1 ∧ 2 * Real.sqrt k * C₈ * β ≤ lam₀ := by
    obtain ⟨D, hD, hD_def⟩ : ∃ D : ℝ, 0 < D ∧ D = 2 * Real.sqrt k * C₈ + 1 :=
      ⟨_, by positivity, rfl⟩
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : ℝ, β₀ = min (min (1 / 4) (1 / (2 * C₈))) (min (1 / D) (lam₀ / D)) :=
      ⟨_, rfl⟩
    have h0 : 0 < β₀ := by rw [hβ₀]; positivity
    have ha : β₀ ≤ 1 / 4 := by rw [hβ₀]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hb : β₀ ≤ 1 / (2 * C₈) := by rw [hβ₀]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hc : β₀ ≤ 1 / D := by rw [hβ₀]; exact (min_le_right _ _).trans (min_le_left _ _)
    have hd : β₀ ≤ lam₀ / D := by rw [hβ₀]; exact (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hb
    rw [le_div_iff₀ hD, hD_def] at hc hd
    exact ⟨β₀, h0, ha, by linarith only [hb], by linarith only [hc, h0], by linarith only [hd, h0]⟩
  -- `β' = min(β, 1/(2·5ⁿC₉))`, so that `C₉5ⁿβ'² ≤ 1/2`
  obtain ⟨β', hβ', hβ'β, hβ'C₉⟩ : ∃ β' : ℝ, 0 < β' ∧ β' ≤ β ∧ C₉ * 5 ^ n * β' ^ 2 ≤ 1 / 2 := by
    refine ⟨min β (1 / (2 * 5 ^ n * C₉)), by positivity, min_le_left _ _, ?_⟩
    have h0 : 0 < min β (1 / (2 * 5 ^ n * C₉)) := by positivity
    have h1 : min β (1 / (2 * 5 ^ n * C₉)) ≤ 1 := (min_le_left _ _).trans (by linarith only [hβ4])
    have h2 := min_le_right β (1 / (2 * 5 ^ n * C₉))
    rw [le_div_iff₀ (by positivity)] at h2
    linarith only [mul_le_mul h2 h1 h0.le zero_le_one]
  -- `C₇ = max(√k C₆, (C_b + 2^{n/2}ω15ⁿC₉(C_b + 1))/β²)` with `C_b = 2(5/2)ⁿω`
  obtain ⟨C₇, hC₇, hC₇k, hC₇b⟩ : ∃ C₇ : ℝ, 0 < C₇ ∧ Real.sqrt k * C₆ ≤ C₇ ∧
      (2 * (5 / 2) ^ n * ω + 2 ^ ((n : ℝ) / 2) * ω * (15 ^ n * C₉) * (2 * (5 / 2) ^ n * ω + 1)) /
        β ^ 2 ≤ C₇ :=
    ⟨max _ _, lt_max_of_lt_right (by positivity), le_max_left _ _, le_max_right _ _⟩
  refine ⟨min δ₁ δ₃, β, β', C₇, lt_min hδ₁ hδ₃, (min_le_left _ _).trans hδ₁8, hβ', hβ'β, hβ4, hC₇,
    ?_⟩
  intro δ hδ hδ₅ U W R H κ ρ z hW hWU hρ hzW hH hHκ hvar hz hmass hκρ ξ hξ σ₀ L T₀ hσ₀ hσ₀δ hT₀
    hL hL1 hεβ _ hii
  have hδ₁' : δ ≤ δ₁ := hδ₅.trans (min_le_left _ _)
  have hδ₃' : δ ≤ δ₃ := hδ₅.trans (min_le_right _ _)
  have hδ8 : δ ≤ 1 / 8 := hδ₁'.trans hδ₁8
  obtain ⟨hDa, hDb, -, -⟩ :=
    hdens δ hδ hδ₁' U W R H κ ρ z hW hWU hρ hzW hH hHκ hvar hz hmass hκρ
  have haffδ := haff δ hδ hδ₃' U W R H κ ρ z hW hWU hρ hzW hH hHκ hvar hz hmass hκρ
  have hmono := (Submission.dorag_monotonicity_density n k hn U W R H κ hW hWU hH hHκ hvar).1
  obtain ⟨ι, ι', hιι', hιT₀, hspan, hproj⟩ :=
    Submission.dorag_lip_orthonormal_coordinates n k T₀ hT₀
  set ε : ℝ := δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))
  have hε : 0 ≤ ε := Real.rpow_nonneg hδ.le _
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  obtain ⟨hξs, hξz⟩ := hξ
  rw [mem_closedBall] at hξz
  -- radius bookkeeping: `σ₀ ≤ δρ ≤ ρ/8`, `B_{3σ₀/4}(ξ) ⊆ B_{2δρ}(z)` and `5σ₀/4 ≤ (1 − 4δ)ρ`
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hδρ8 : δ * ρ ≤ ρ / 8 := by linarith only [mul_le_mul_of_nonneg_right hδ8 hρ.le]
  have hnear : ∀ y ∈ closedBall ξ (3 * σ₀ / 4), dist y z ≤ 2 * δ * ρ := fun y hy => by
    linarith only [dist_triangle y ξ z, mem_closedBall.mp hy, hξz, hσ₀δ, hδρ]
  have hfar : 5 * σ₀ / 4 ≤ (1 - 4 * δ) * ρ := by linarith only [hσ₀δ, hδρ8, hρ]
  have h34 : 3 * σ₀ / 4 ≤ σ₀ := by linarith only [hσ₀]
  have h24 : σ₀ / 2 ≤ 3 * σ₀ / 4 := by linarith only [hσ₀]
  -- the density bounds (a), (b) at points of `B_{3σ₀/4}(ξ)` and radii `≤ 5σ₀/4`
  have hDa' : ∀ y ∈ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 4 →
      R.measure (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n) :=
    fun y hy t ht ht' =>
      hDa y (mem_closedBall.mpr (by linarith only [hnear y hy, hδρ])) t ht (ht'.trans hfar)
  have hDb' : ∀ y ∈ R.measure.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t →
      t ≤ 5 * σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * R.measure (closedBall y t) :=
    fun y hy t ht ht' =>
      hDb y ⟨hy.1, mem_closedBall.mpr (by linarith only [hnear y hy.2, hδρ])⟩ t ht (ht'.trans hfar)
  -- the tilt-excess density `e(x) = |p_x − p_{T₀}|²`
  set e : Euclid (n + k) → ℝ := fun x => ∑ i : Fin (n + k),
    ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
      T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  -- (c) the cone condition on the good set, from the affine approximation and the density bounds
  have hconeX := hcone R.measure (approxTangentPlane n R.carrier) T₀ ξ σ₀ ε β L
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hσ₀ hε hβ hL hεβ
    (fun y hy t ht ht' => by
      obtain ⟨S, -, hS⟩ := haffδ y ⟨hy.1, mem_closedBall.mpr (hnear y hy.2)⟩ t ht
        (by linarith only [ht', hσ₀δ, hδρ])
      exact ⟨S, hS⟩)
    (fun y hy t ht ht' => hDb' y hy t ht (by linarith only [ht', hσ₀])) hii
  -- (a) the good set `G = B_{3σ₀/4}(ξ) ∩ G'`
  set G' : Set (Euclid (n + k)) := {y | y ∈ R.measure.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
    ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂R.measure ≤
      ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)}
  have hconeG : ∀ y₁ ∈ closedBall ξ (3 * σ₀ / 4) ∩ G', ∀ y₂ ∈ closedBall ξ (3 * σ₀ / 4) ∩ G',
      ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖ := by
    rintro y₁ ⟨hy₁B, hy₁s, hy₁t⟩ y₂ ⟨hy₂B, hy₂s, -⟩
    exact hconeX y₁ ⟨hy₁s, hy₁B⟩ y₂ ⟨hy₂s, hy₂B⟩ hy₁t
  -- (d) the Lipschitz graph `F ⊇ G`, `Lip f ≤ Λ := 2√k C₈βL ≤ L`
  have hlam : C₈ * β * L ≤ 1 / 2 := (mul_le_of_le_one_right (by positivity) hL1).trans hβC₈
  obtain ⟨f, hfLip, hfbd, hGF⟩ := Submission.dorag_lip_cone_set_graph_extension n k T₀ ι ι' ξ
    (closedBall ξ (3 * σ₀ / 4) ∩ G') (C₈ * β * L) (C₆ * ε * σ₀) hspan hproj (by positivity) hlam
    (by positivity) hconeG (fun y hy => hii y ⟨hy.2.1, closedBall_subset_closedBall h34 hy.1⟩)
  set F : Set (Euclid (n + k)) := range (fun v => ξ + ι v + ι' (f v))
  have hΛ : 2 * Real.sqrt k * (C₈ * β * L) = (2 * Real.sqrt k * C₈ * β) * L := by ring
  have hΛ0 : 0 ≤ 2 * Real.sqrt k * (C₈ * β * L) := by positivity
  have hΛL : 2 * Real.sqrt k * (C₈ * β * L) ≤ L := by
    rw [hΛ]
    exact mul_le_of_le_one_left hL.le hβk
  have hΛlam : 2 * Real.sqrt k * (C₈ * β * L) ≤ lam₀ := by
    rw [hΛ]
    exact (mul_le_of_le_one_right (by positivity) hL1).trans hβlam
  obtain ⟨hFcone, hFH⟩ := Submission.dorag_lip_graph_cone_hausdorff_bound n k T₀ ι ι' ξ f _ hιι'
    hproj hΛ0 (hΛL.trans hL1) hfLip
  -- (f) the off-support estimate (10') at the points of `(F ∖ spt μ) ∩ B_{σ₀/4}(ξ)`
  have hκσ₀ : κ * σ₀ ≤ 1 := by
    have hσρ : σ₀ ≤ ρ := by linarith only [hσ₀δ, hδρ8, hρ]
    linarith only [mul_le_mul_of_nonneg_left hσρ hκ, hκρ, hδ8]
  have hoffX := hoff R.measure (approxTangentPlane n R.carrier) T₀ F ξ σ₀ κ _ hσ₀ hκ hκσ₀ hΛ0
    hΛlam hξs hFcone
    (fun y hy t ht ht' =>
      hDa' y (closedBall_subset_closedBall h24 hy) t ht (by linarith only [ht', hσ₀]))
    (fun y hy t ht ht' =>
      hDb' y ⟨hy.1, closedBall_subset_closedBall h24 hy.2⟩ t ht (by linarith only [ht', hσ₀]))
    (fun y s t hy hs hst ht => (hmono y s t hs hst ((closedBall_subset_closedBall' (by
      linarith only [dist_triangle y ξ z, mem_closedBall.mp hy, ht, hξz, hσ₀δ, hδρ8, hρ])).trans
        hzW)).2)
  -- (b) the bad set `B_{3σ₀/4}(ξ) ∖ G`, and the holes `(F ∖ spt μ) ∩ B_{σ₀/4}(ξ)` of the graph
  have hbad := Submission.dorag_lip_bad_set_measure_bound n k R.measure e ξ σ₀ (β ^ 2 * L ^ 2) hσ₀
    (by positivity) hDa'
  have hhole := Submission.dorag_lip_graph_hole_measure_bound n k R.measure e F
    ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) (closedBall ξ (3 * σ₀ / 4))
    (ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n) C₉ (σ₀ / 8)
    isClosed_closedBall.measurableSet (fun η hη => hη.1.1) (fun η hη r hr => hFH η hη.1.1 r hr)
    (fun η hη => by
      obtain ⟨s, y, -, hs, h2s, -, hsn⟩ := hoffX η hη
      have hηξ : dist η ξ ≤ σ₀ / 4 := hη.2
      exact ⟨s, hs, by linarith only [h2s, hηξ],
        closedBall_subset_closedBall' (by linarith only [h2s, hηξ, hσ₀]), hsn⟩)
  -- 5A: `μ(B_{σ₀/2}(ξ) ∖ F) ≤ μ(B_{3σ₀/4}(ξ) ∖ G)`, plus the hole estimate
  have h5A : R.measure (closedBall ξ (σ₀ / 2) \ F) +
      μHE[n] ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤
      ENNReal.ofReal (C₇ / L ^ 2) * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂R.measure := by
    set X : ℝ≥0∞ := ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂R.measure
    obtain ⟨cb, hcb, hcb_def⟩ : ∃ cb : ℝ, 0 ≤ cb ∧ cb = 2 * (5 / 2) ^ n / (β ^ 2 * L ^ 2) * ω :=
      ⟨_, by positivity, rfl⟩
    obtain ⟨K₁, hK₁, hK₁_def⟩ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ K₁ = 2 ^ ((n : ℝ) / 2) * ω * (15 ^ n * C₉) :=
      ⟨_, by positivity, rfl⟩
    have hbad' : R.measure (closedBall ξ (3 * σ₀ / 4) \ G') ≤ ENNReal.ofReal cb * X := by
      have h : ENNReal.ofReal cb = ENNReal.ofReal (2 * (5 / 2) ^ n / (β ^ 2 * L ^ 2)) *
          unitBallVolume n := by
        rw [hcb_def, hωeq, ENNReal.ofReal_mul (by positivity)]
      rw [h]
      exact hbad
    have h1 : R.measure (closedBall ξ (σ₀ / 2) \ F) ≤ ENNReal.ofReal cb * X := by
      refine (measure_mono ?_).trans hbad'
      rintro x ⟨hx, hxF⟩
      have hx' : x ∈ closedBall ξ (3 * σ₀ / 4) := closedBall_subset_closedBall h24 hx
      exact ⟨hx', fun hxG => hxF (hGF ⟨hx', hxG⟩)⟩
    have h2 : R.measure (closedBall ξ (3 * σ₀ / 4) \ F) ≤ ENNReal.ofReal cb * X := by
      refine (measure_mono ?_).trans hbad'
      rintro x ⟨hx, hxF⟩
      exact ⟨hx, fun hxG => hxF (hGF ⟨hx, hxG⟩)⟩
    have h3 : ∫⁻ x in closedBall ξ (3 * σ₀ / 4), ENNReal.ofReal (e x) ∂R.measure ≤ X :=
      lintegral_mono_set (closedBall_subset_closedBall h34)
    have h4 : μHE[n] ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤
        ENNReal.ofReal K₁ * (ENNReal.ofReal cb * X + X) := by
      have h : ENNReal.ofReal K₁ = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n *
          ENNReal.ofReal (15 ^ n * C₉) := by
        rw [hK₁_def, hωeq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      rw [h]
      exact hhole.trans (by gcongr)
    -- `C_b/(βL)² + 2^{n/2}ω15ⁿC₉(C_b/(βL)² + 1) ≤ C₇/L²`, as `(βL)² ≤ 1`
    have hreal : cb + K₁ * (cb + 1) ≤ C₇ / L ^ 2 := by
      have ha : 0 < β ^ 2 * L ^ 2 := by positivity
      have ha1 : β ^ 2 * L ^ 2 ≤ 1 :=
        (mul_le_mul (pow_le_one₀ hβ.le (by linarith only [hβ4])) (pow_le_one₀ hL.le hL1)
          (by positivity) zero_le_one).trans_eq (one_mul 1)
      have h1a : 1 ≤ 1 / (β ^ 2 * L ^ 2) := by
        rw [le_div_iff₀ ha]
        linarith only [ha1]
      calc cb + K₁ * (cb + 1) ≤ cb + K₁ * (cb + 1 / (β ^ 2 * L ^ 2)) := by gcongr
        _ = (2 * (5 / 2) ^ n * ω + 2 ^ ((n : ℝ) / 2) * ω * (15 ^ n * C₉) *
              (2 * (5 / 2) ^ n * ω + 1)) / β ^ 2 / L ^ 2 := by
          rw [hcb_def, hK₁_def]
          gcongr
          exact hlow ξ ⟨hξ.1, mem_closedBall_self hr.le⟩ _ hs0 hsr
  obtain ⟨x₀, hx₀, hx₀n, hx₀F⟩ := Submission.dorag_aa_exists_low_height_point (n + k) (n + 2)
    R.measure (approxTangentPlane n R.carrier)
    (fun x => Module.finrank ℝ (approxTangentPlane n R.carrier x) = n) F ξ r (e * r) (C₂ * δ)
    ((CL * e * r) ^ 2) (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R)
    (Submission.dorag_aa_ae_finrank_approxTangentPlane (n + k) n U R) hr hsr
    (fun y hy => mem_closedBall.mp (hFK hy).2)
    (fun y hy => hc y ⟨(hFK hy).1, hcen y (hFK hy).2⟩ (2 * r) (by positivity) hr2) hiii
  -- Steps 6–7: `S = T_{x₀}M`; every point of `spt μ ∩ B̄_r(ξ)` is within `(2 + C_λ)er` of `ξ + S`
  obtain ⟨h4a, hint⟩ := Submission.dorag_aa_height_bounds_of_net (n + k) R.measure
    (approxTangentPlane n R.carrier x₀) F ξ x₀ r (e * r) (CL * e * r) hFnet
    (fun y hy => le_of_sq_le_sq (hx₀F y hy) (by positivity)) (mem_closedBall.mp hx₀)
  refine ⟨approxTangentPlane n R.carrier x₀, hx₀n, fun x hx => (h4a x hx).trans ?_, ?_⟩
  · calc 2 * (e * r) + CL * e * r = (CL + 2) * (e * r) := by ring
      _ ≤ C₃ * (e * r) := by gcongr; exact le_max_of_le_right (le_max_left _ _)
      _ = C₃ * e * r := by ring
  -- Step 8: the tilt-height estimate at `(ξ, r, S)`, with `μ(B̄_r(ξ)) ≤ 2wrⁿ` and `κr ≤ δ ≤ e`
  · have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
    have hκr : κ * r ≤ e := (mul_le_mul_of_nonneg_left hrρ hκ0).trans (hκρ.trans hδe)
    have hBW : closedBall ξ r ⊆ W := fun x hx => hzW (mem_closedBall.mpr
      ((dist_triangle x ξ z).trans (by linarith [mem_closedBall.mp hx])))
    have hμr := hup r hr (by linarith)
    have hA : 0 ≤ 1 / r ^ 2 * ((2 * (e * r) + CL * e * r) ^ 2 * (2 * w * r ^ n)) := by
      positivity
    have hB : 0 ≤ κ ^ 2 * r ^ 2 * (2 * w * r ^ n) := by positivity
    calc _ ≤ _ := htilt U W R H κ ξ r _ hW hWU hH hHκ hfv hr hBW hx₀n
      _ ≤ ENNReal.ofReal CT * (ENNReal.ofReal (1 / r ^ 2) *
            (ENNReal.ofReal ((2 * (e * r) + CL * e * r) ^ 2) * ENNReal.ofReal (2 * w * r ^ n)) +
            ENNReal.ofReal (κ ^ 2 * r ^ 2) * ENNReal.ofReal (2 * w * r ^ n)) := by
          gcongr
          exact hint.trans (by gcongr)
      _ = ENNReal.ofReal (CT * (1 / r ^ 2 * ((2 * (e * r) + CL * e * r) ^ 2 * (2 * w * r ^ n)) +
            κ ^ 2 * r ^ 2 * (2 * w * r ^ n))) := by
          rw [ENNReal.ofReal_mul hCT.le, ENNReal.ofReal_add hA hB,
            ENNReal.ofReal_mul (p := 1 / r ^ 2) (by positivity),
            ENNReal.ofReal_mul (p := (2 * (e * r) + CL * e * r) ^ 2) (sq_nonneg _),
            ENNReal.ofReal_mul (p := κ ^ 2 * r ^ 2) (by positivity)]
      _ ≤ ENNReal.ofReal (C₃ * e ^ 2 * (r / 2) ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have hκ2 : κ ^ 2 * r ^ 2 ≤ e ^ 2 := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) hκr 2
          have hrn : r ^ n = 2 ^ n * (r / 2) ^ n := by
            rw [div_pow]
            field_simp
          calc CT * (1 / r ^ 2 * ((2 * (e * r) + CL * e * r) ^ 2 * (2 * w * r ^ n)) +
                κ ^ 2 * r ^ 2 * (2 * w * r ^ n))
              = CT * ((CL + 2) ^ 2 * e ^ 2 * (2 * w * r ^ n) +
                  κ ^ 2 * r ^ 2 * (2 * w * r ^ n)) := by
                field_simp
                ring
            _ ≤ CT * ((CL + 2) ^ 2 * e ^ 2 * (2 * w * r ^ n) + e ^ 2 * (2 * w * r ^ n)) := by
                gcongr
            _ = 2 ^ n * 2 * w * CT * ((CL + 2) ^ 2 + 1) * (e ^ 2 * (r / 2) ^ n) := by
                rw [hrn]
                ring
            _ ≤ C₃ * (e ^ 2 * (r / 2) ^ n) := by
                gcongr
                exact le_max_of_le_right (le_max_right _ _)
            _ = C₃ * e ^ 2 * (r / 2) ^ n := by ring

/-- **Lipschitz approximation** (Simon Ch. 5, Lemma 2.6 and Corollary 2.7, with the corrections of
the accepted proof: the `Hⁿ`-estimate is on `B_{σ₀/4}(ξ)`, the graph conclusion on `B_{σ₀/8}(ξ)`,
and `sup |f|` carries the factor `σ₀`).  Write `μ = μ_V`, `P = p_{T₀}`, `Q = I − P`,
`ε = δ^{1/(2n+2)}` and `e(x) = |p_x − P|²`.  Take `δ₅ = min(δ₁, δ₃)` from the density bounds and the
affine approximation, `C₈` from the good-set cone estimate, `λ₀, C₉` from the off-support estimate,
`β = min(1/4, 1/(2C₈), 1/D, λ₀/D)` with `D = 2√k C₈ + 1`, and `β' = min(β, 1/(2·5ⁿC₉))`.

The good set `G = {y ∈ spt μ ∩ B_{3σ₀/4}(ξ) : ∫_{B_{t/2}(y)} e dμ ≤ β²L²tⁿ for t ∈ (0, σ₀/2]}`
satisfies `|Q(y₂ − y₁)| ≤ C₈βL|y₂ − y₁|` (cone estimate, fed by the affine approximation and the
lower density bound), so it lies in the graph `F` of some `f` with `Lip f ≤ 2√k C₈βL ≤ L` and
`|f| ≤ √k C₆εσ₀` (graph extension).  The bad-set bound gives
`μ(B_{3σ₀/4}(ξ) ∖ G) ≤ 2(5/2)ⁿωₙ(βL)⁻² ∫_{B_{σ₀}(ξ)} e dμ`, and the off-support estimate (from the
monotonicity identity `(M2)` and the density bounds) with the hole-measure bound gives
`Hⁿ((F ∖ spt μ) ∩ B_{σ₀/4}(ξ)) ≤ 2^{n/2}ωₙ15ⁿC₉(μ(B_{3σ₀/4}(ξ) ∖ F) + ∫_{B_{3σ₀/4}(ξ)} e dμ)`;
adding these gives 5A.  Under the hypothesis of 5B, `spt μ ∩ B_{σ₀/2}(ξ) ⊆ G ⊆ F`, and a point of
`(F ∖ spt μ) ∩ B_{σ₀/8}(ξ)` would give `sⁿ ≤ C₉5ⁿβ'²L²sⁿ ≤ sⁿ/2` in the off-support estimate. -/
theorem Submission.dorag_lipschitz_approximation : ∀ (n k : ℕ), 0 < n → ∀ C₆ : ℝ, 1 ≤ C₆ → ∃ δ₅ β β' C₇ : ℝ, 0 < δ₅ ∧ δ₅ ≤ 1 / 8 ∧ 0 < β' ∧ β' ≤ β ∧ β ≤ 1 / 4 ∧ 0 < C₇ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₅ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ₀ L : ℝ) (T₀ : Submodule ℝ (Euclid (n + k))), 0 < σ₀ → σ₀ ≤ δ * ρ → Module.finrank ℝ T₀ = n → 0 < L → L ≤ 1 → δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ≤ β * L → ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (C₆ * (δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))) ^ 2 * σ₀ ^ n) → (∀ x ∈ R.measure.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * σ₀) → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ v, ι v ∈ T₀) ∧ (∀ v w, ‖f v - f w‖ ≤ L * ‖v - w‖) ∧ (∀ v, ‖f v‖ ≤ C₇ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * σ₀) ∧ R.measure (closedBall ξ (σ₀ / 2) \ range (fun v => ξ + ι v + ι' (f v))) + μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤ ENNReal.ofReal (C₇ / L ^ 2) * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ∧ ((∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y t, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n)) → R.measure.support ∩ closedBall ξ (σ₀ / 8) = range (fun v => ξ + ι v + ι' (f v)) ∩ closedBall ξ (σ₀ / 8)) := by
  intro n k hn C₆ hC₆
  obtain ⟨δ₁, C₂, hδ₁, hδ₁8, -, hdens⟩ := Submission.dorag_standing_density_bounds n k hn
  obtain ⟨δ₃, C₃, hδ₃, -, hC₃, haff⟩ := Submission.dorag_affine_approximation n k hn
  obtain ⟨C₈, hC₈, hcone⟩ := Submission.dorag_lip_good_set_cone_estimate n k C₃ C₆ hC₃ hC₆
  obtain ⟨lam₀, C₉, hlam₀, hC₉, hoff⟩ := Submission.dorag_lip_off_support_estimate n k
  -- `ωₙ = ω` with `0 < ω < ∞`
  obtain ⟨ω, hω, hωeq⟩ : ∃ ω : ℝ, 0 < ω ∧ unitBallVolume n = ENNReal.ofReal ω := by
    have h1 : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
    have h2 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
    exact ⟨_, ENNReal.toReal_pos h2 h1, (ENNReal.ofReal_toReal h1).symm⟩
  -- `β = min(1/4, 1/(2C₈), 1/D, λ₀/D)` with `D = 2√k C₈ + 1`
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  obtain ⟨β, hβ, hβ4, hβC₈, hβk, hβlam⟩ : ∃ β : ℝ, 0 < β ∧ β ≤ 1 / 4 ∧ C₈ * β ≤ 1 / 2 ∧
      2 * Real.sqrt k * C₈ * β ≤ 1 ∧ 2 * Real.sqrt k * C₈ * β ≤ lam₀ := by
    obtain ⟨D, hD, hD_def⟩ : ∃ D : ℝ, 0 < D ∧ D = 2 * Real.sqrt k * C₈ + 1 :=
      ⟨_, by positivity, rfl⟩
    obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : ℝ, β₀ = min (min (1 / 4) (1 / (2 * C₈))) (min (1 / D) (lam₀ / D)) :=
      ⟨_, rfl⟩
    have h0 : 0 < β₀ := by rw [hβ₀]; positivity
    have ha : β₀ ≤ 1 / 4 := by rw [hβ₀]; exact (min_le_left _ _).trans (min_le_left _ _)
    have hb : β₀ ≤ 1 / (2 * C₈) := by rw [hβ₀]; exact (min_le_left _ _).trans (min_le_right _ _)
    have hc : β₀ ≤ 1 / D := by rw [hβ₀]; exact (min_le_right _ _).trans (min_le_left _ _)
    have hd : β₀ ≤ lam₀ / D := by rw [hβ₀]; exact (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hb
    rw [le_div_iff₀ hD, hD_def] at hc hd
    exact ⟨β₀, h0, ha, by linarith only [hb], by linarith only [hc, h0], by linarith only [hd, h0]⟩
  -- `β' = min(β, 1/(2·5ⁿC₉))`, so that `C₉5ⁿβ'² ≤ 1/2`
  obtain ⟨β', hβ', hβ'β, hβ'C₉⟩ : ∃ β' : ℝ, 0 < β' ∧ β' ≤ β ∧ C₉ * 5 ^ n * β' ^ 2 ≤ 1 / 2 := by
    refine ⟨min β (1 / (2 * 5 ^ n * C₉)), by positivity, min_le_left _ _, ?_⟩
    have h0 : 0 < min β (1 / (2 * 5 ^ n * C₉)) := by positivity
    have h1 : min β (1 / (2 * 5 ^ n * C₉)) ≤ 1 := (min_le_left _ _).trans (by linarith only [hβ4])
    have h2 := min_le_right β (1 / (2 * 5 ^ n * C₉))
    rw [le_div_iff₀ (by positivity)] at h2
    linarith only [mul_le_mul h2 h1 h0.le zero_le_one]
  -- `C₇ = max(√k C₆, (C_b + 2^{n/2}ω15ⁿC₉(C_b + 1))/β²)` with `C_b = 2(5/2)ⁿω`
  obtain ⟨C₇, hC₇, hC₇k, hC₇b⟩ : ∃ C₇ : ℝ, 0 < C₇ ∧ Real.sqrt k * C₆ ≤ C₇ ∧
      (2 * (5 / 2) ^ n * ω + 2 ^ ((n : ℝ) / 2) * ω * (15 ^ n * C₉) * (2 * (5 / 2) ^ n * ω + 1)) /
        β ^ 2 ≤ C₇ :=
    ⟨max _ _, lt_max_of_lt_right (by positivity), le_max_left _ _, le_max_right _ _⟩
  refine ⟨min δ₁ δ₃, β, β', C₇, lt_min hδ₁ hδ₃, (min_le_left _ _).trans hδ₁8, hβ', hβ'β, hβ4, hC₇,
    ?_⟩
  intro δ hδ hδ₅ U W R H κ ρ z hW hWU hρ hzW hH hHκ hvar hz hmass hκρ ξ hξ σ₀ L T₀ hσ₀ hσ₀δ hT₀
    hL hL1 hεβ _ hii
  have hδ₁' : δ ≤ δ₁ := hδ₅.trans (min_le_left _ _)
  have hδ₃' : δ ≤ δ₃ := hδ₅.trans (min_le_right _ _)
  have hδ8 : δ ≤ 1 / 8 := hδ₁'.trans hδ₁8
  obtain ⟨hDa, hDb, -, -⟩ :=
    hdens δ hδ hδ₁' U W R H κ ρ z hW hWU hρ hzW hH hHκ hvar hz hmass hκρ
  have haffδ := haff δ hδ hδ₃' U W R H κ ρ z hW hWU hρ hzW hH hHκ hvar hz hmass hκρ
  have hmono := (Submission.dorag_monotonicity_density n k hn U W R H κ hW hWU hH hHκ hvar).1
  obtain ⟨ι, ι', hιι', hιT₀, hspan, hproj⟩ :=
    Submission.dorag_lip_orthonormal_coordinates n k T₀ hT₀
  set ε : ℝ := δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))
  have hε : 0 ≤ ε := Real.rpow_nonneg hδ.le _
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  obtain ⟨hξs, hξz⟩ := hξ
  rw [mem_closedBall] at hξz
  -- radius bookkeeping: `σ₀ ≤ δρ ≤ ρ/8`, `B_{3σ₀/4}(ξ) ⊆ B_{2δρ}(z)` and `5σ₀/4 ≤ (1 − 4δ)ρ`
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hδρ8 : δ * ρ ≤ ρ / 8 := by linarith only [mul_le_mul_of_nonneg_right hδ8 hρ.le]
  have hnear : ∀ y ∈ closedBall ξ (3 * σ₀ / 4), dist y z ≤ 2 * δ * ρ := fun y hy => by
    linarith only [dist_triangle y ξ z, mem_closedBall.mp hy, hξz, hσ₀δ, hδρ]
  have hfar : 5 * σ₀ / 4 ≤ (1 - 4 * δ) * ρ := by linarith only [hσ₀δ, hδρ8, hρ]
  have h34 : 3 * σ₀ / 4 ≤ σ₀ := by linarith only [hσ₀]
  have h24 : σ₀ / 2 ≤ 3 * σ₀ / 4 := by linarith only [hσ₀]
  -- the density bounds (a), (b) at points of `B_{3σ₀/4}(ξ)` and radii `≤ 5σ₀/4`
  have hDa' : ∀ y ∈ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 4 →
      R.measure (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n) :=
    fun y hy t ht ht' =>
      hDa y (mem_closedBall.mpr (by linarith only [hnear y hy, hδρ])) t ht (ht'.trans hfar)
  have hDb' : ∀ y ∈ R.measure.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t →
      t ≤ 5 * σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * R.measure (closedBall y t) :=
    fun y hy t ht ht' =>
      hDb y ⟨hy.1, mem_closedBall.mpr (by linarith only [hnear y hy.2, hδρ])⟩ t ht (ht'.trans hfar)
  -- the tilt-excess density `e(x) = |p_x − p_{T₀}|²`
  set e : Euclid (n + k) → ℝ := fun x => ∑ i : Fin (n + k),
    ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
      T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  -- (c) the cone condition on the good set, from the affine approximation and the density bounds
  have hconeX := hcone R.measure (approxTangentPlane n R.carrier) T₀ ξ σ₀ ε β L
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hσ₀ hε hβ hL hεβ
    (fun y hy t ht ht' => by
      obtain ⟨S, -, hS⟩ := haffδ y ⟨hy.1, mem_closedBall.mpr (hnear y hy.2)⟩ t ht
        (by linarith only [ht', hσ₀δ, hδρ])
      exact ⟨S, hS⟩)
    (fun y hy t ht ht' => hDb' y hy t ht (by linarith only [ht', hσ₀])) hii
  -- (a) the good set `G = B_{3σ₀/4}(ξ) ∩ G'`
  set G' : Set (Euclid (n + k)) := {y | y ∈ R.measure.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
    ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂R.measure ≤
      ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)}
  have hconeG : ∀ y₁ ∈ closedBall ξ (3 * σ₀ / 4) ∩ G', ∀ y₂ ∈ closedBall ξ (3 * σ₀ / 4) ∩ G',
      ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖ := by
    rintro y₁ ⟨hy₁B, hy₁s, hy₁t⟩ y₂ ⟨hy₂B, hy₂s, -⟩
    exact hconeX y₁ ⟨hy₁s, hy₁B⟩ y₂ ⟨hy₂s, hy₂B⟩ hy₁t
  -- (d) the Lipschitz graph `F ⊇ G`, `Lip f ≤ Λ := 2√k C₈βL ≤ L`
  have hlam : C₈ * β * L ≤ 1 / 2 := (mul_le_of_le_one_right (by positivity) hL1).trans hβC₈
  obtain ⟨f, hfLip, hfbd, hGF⟩ := Submission.dorag_lip_cone_set_graph_extension n k T₀ ι ι' ξ
    (closedBall ξ (3 * σ₀ / 4) ∩ G') (C₈ * β * L) (C₆ * ε * σ₀) hspan hproj (by positivity) hlam
    (by positivity) hconeG (fun y hy => hii y ⟨hy.2.1, closedBall_subset_closedBall h34 hy.1⟩)
  set F : Set (Euclid (n + k)) := range (fun v => ξ + ι v + ι' (f v))
  have hΛ : 2 * Real.sqrt k * (C₈ * β * L) = (2 * Real.sqrt k * C₈ * β) * L := by ring
  have hΛ0 : 0 ≤ 2 * Real.sqrt k * (C₈ * β * L) := by positivity
  have hΛL : 2 * Real.sqrt k * (C₈ * β * L) ≤ L := by
    rw [hΛ]
    exact mul_le_of_le_one_left hL.le hβk
  have hΛlam : 2 * Real.sqrt k * (C₈ * β * L) ≤ lam₀ := by
    rw [hΛ]
    exact (mul_le_of_le_one_right (by positivity) hL1).trans hβlam
  obtain ⟨hFcone, hFH⟩ := Submission.dorag_lip_graph_cone_hausdorff_bound n k T₀ ι ι' ξ f _ hιι'
    hproj hΛ0 (hΛL.trans hL1) hfLip
  -- (f) the off-support estimate (10') at the points of `(F ∖ spt μ) ∩ B_{σ₀/4}(ξ)`
  have hκσ₀ : κ * σ₀ ≤ 1 := by
    have hσρ : σ₀ ≤ ρ := by linarith only [hσ₀δ, hδρ8, hρ]
    linarith only [mul_le_mul_of_nonneg_left hσρ hκ, hκρ, hδ8]
  have hoffX := hoff R.measure (approxTangentPlane n R.carrier) T₀ F ξ σ₀ κ _ hσ₀ hκ hκσ₀ hΛ0
    hΛlam hξs hFcone
    (fun y hy t ht ht' =>
      hDa' y (closedBall_subset_closedBall h24 hy) t ht (by linarith only [ht', hσ₀]))
    (fun y hy t ht ht' =>
      hDb' y ⟨hy.1, closedBall_subset_closedBall h24 hy.2⟩ t ht (by linarith only [ht', hσ₀]))
    (fun y s t hy hs hst ht => (hmono y s t hs hst ((closedBall_subset_closedBall' (by
      linarith only [dist_triangle y ξ z, mem_closedBall.mp hy, ht, hξz, hσ₀δ, hδρ8, hρ])).trans
        hzW)).2)
  -- (b) the bad set `B_{3σ₀/4}(ξ) ∖ G`, and the holes `(F ∖ spt μ) ∩ B_{σ₀/4}(ξ)` of the graph
  have hbad := Submission.dorag_lip_bad_set_measure_bound n k R.measure e ξ σ₀ (β ^ 2 * L ^ 2) hσ₀
    (by positivity) hDa'
  have hhole := Submission.dorag_lip_graph_hole_measure_bound n k R.measure e F
    ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) (closedBall ξ (3 * σ₀ / 4))
    (ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n) C₉ (σ₀ / 8)
    isClosed_closedBall.measurableSet (fun η hη => hη.1.1) (fun η hη r hr => hFH η hη.1.1 r hr)
    (fun η hη => by
      obtain ⟨s, y, -, hs, h2s, -, hsn⟩ := hoffX η hη
      have hηξ : dist η ξ ≤ σ₀ / 4 := hη.2
      exact ⟨s, hs, by linarith only [h2s, hηξ],
        closedBall_subset_closedBall' (by linarith only [h2s, hηξ, hσ₀]), hsn⟩)
  -- 5A: `μ(B_{σ₀/2}(ξ) ∖ F) ≤ μ(B_{3σ₀/4}(ξ) ∖ G)`, plus the hole estimate
  have h5A : R.measure (closedBall ξ (σ₀ / 2) \ F) +
      μHE[n] ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤
      ENNReal.ofReal (C₇ / L ^ 2) * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂R.measure := by
    set X : ℝ≥0∞ := ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂R.measure
    obtain ⟨cb, hcb, hcb_def⟩ : ∃ cb : ℝ, 0 ≤ cb ∧ cb = 2 * (5 / 2) ^ n / (β ^ 2 * L ^ 2) * ω :=
      ⟨_, by positivity, rfl⟩
    obtain ⟨K₁, hK₁, hK₁_def⟩ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ K₁ = 2 ^ ((n : ℝ) / 2) * ω * (15 ^ n * C₉) :=
      ⟨_, by positivity, rfl⟩
    have hbad' : R.measure (closedBall ξ (3 * σ₀ / 4) \ G') ≤ ENNReal.ofReal cb * X := by
      have h : ENNReal.ofReal cb = ENNReal.ofReal (2 * (5 / 2) ^ n / (β ^ 2 * L ^ 2)) *
          unitBallVolume n := by
        rw [hcb_def, hωeq, ENNReal.ofReal_mul (by positivity)]
      rw [h]
      exact hbad
    have h1 : R.measure (closedBall ξ (σ₀ / 2) \ F) ≤ ENNReal.ofReal cb * X := by
      refine (measure_mono ?_).trans hbad'
      rintro x ⟨hx, hxF⟩
      have hx' : x ∈ closedBall ξ (3 * σ₀ / 4) := closedBall_subset_closedBall h24 hx
      exact ⟨hx', fun hxG => hxF (hGF ⟨hx', hxG⟩)⟩
    have h2 : R.measure (closedBall ξ (3 * σ₀ / 4) \ F) ≤ ENNReal.ofReal cb * X := by
      refine (measure_mono ?_).trans hbad'
      rintro x ⟨hx, hxF⟩
      exact ⟨hx, fun hxG => hxF (hGF ⟨hx, hxG⟩)⟩
    have h3 : ∫⁻ x in closedBall ξ (3 * σ₀ / 4), ENNReal.ofReal (e x) ∂R.measure ≤ X :=
      lintegral_mono_set (closedBall_subset_closedBall h34)
    have h4 : μHE[n] ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤
        ENNReal.ofReal K₁ * (ENNReal.ofReal cb * X + X) := by
      have h : ENNReal.ofReal K₁ = ENNReal.ofReal (2 ^ ((n : ℝ) / 2)) * unitBallVolume n *
          ENNReal.ofReal (15 ^ n * C₉) := by
        rw [hK₁_def, hωeq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      rw [h]
      exact hhole.trans (by gcongr)
    -- `C_b/(βL)² + 2^{n/2}ω15ⁿC₉(C_b/(βL)² + 1) ≤ C₇/L²`, as `(βL)² ≤ 1`
    have hreal : cb + K₁ * (cb + 1) ≤ C₇ / L ^ 2 := by
      have ha : 0 < β ^ 2 * L ^ 2 := by positivity
      have ha1 : β ^ 2 * L ^ 2 ≤ 1 :=
        (mul_le_mul (pow_le_one₀ hβ.le (by linarith only [hβ4])) (pow_le_one₀ hL.le hL1)
          (by positivity) zero_le_one).trans_eq (one_mul 1)
      have h1a : 1 ≤ 1 / (β ^ 2 * L ^ 2) := by
        rw [le_div_iff₀ ha]
        linarith only [ha1]
      calc cb + K₁ * (cb + 1) ≤ cb + K₁ * (cb + 1 / (β ^ 2 * L ^ 2)) := by gcongr
        _ = (2 * (5 / 2) ^ n * ω + 2 ^ ((n : ℝ) / 2) * ω * (15 ^ n * C₉) *
              (2 * (5 / 2) ^ n * ω + 1)) / β ^ 2 / L ^ 2 := by
          rw [hcb_def, hK₁_def]
          field_simp
        _ ≤ C₇ / L ^ 2 := by gcongr
    calc R.measure (closedBall ξ (σ₀ / 2) \ F) +
          μHE[n] ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4))
        ≤ ENNReal.ofReal cb * X + ENNReal.ofReal K₁ * (ENNReal.ofReal cb * X + X) :=
          add_le_add h1 h4
      _ = ENNReal.ofReal (cb + K₁ * (cb + 1)) * X := by
          rw [ENNReal.ofReal_add hcb (by positivity), ENNReal.ofReal_mul hK₁,
            ENNReal.ofReal_add hcb zero_le_one, ENNReal.ofReal_one]
          ring
      _ ≤ ENNReal.ofReal (C₇ / L ^ 2) * X := by gcongr
  -- 5B: under the small-tilt hypothesis `spt μ ∩ B_{σ₀/2}(ξ) ⊆ G ⊆ F`, and (10') excludes holes
  have h5B : (∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
      ∫⁻ x in closedBall y t, ENNReal.ofReal (e x) ∂R.measure ≤
        ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n)) →
      R.measure.support ∩ closedBall ξ (σ₀ / 8) = F ∩ closedBall ξ (σ₀ / 8) := by
    intro hB
    have h82 : σ₀ / 8 ≤ σ₀ / 2 := by linarith only [hσ₀]
    have h84 : σ₀ / 8 ≤ σ₀ / 4 := by linarith only [hσ₀]
    have hsG : ∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), y ∈ F := by
      rintro y ⟨hys, hyB⟩
      refine hGF ⟨closedBall_subset_closedBall h24 hyB, hys, fun t ht ht' => ?_⟩
      calc ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂R.measure
          ≤ ∫⁻ x in closedBall y t, ENNReal.ofReal (e x) ∂R.measure :=
            lintegral_mono_set (closedBall_subset_closedBall (by linarith only [ht]))
        _ ≤ ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n) := hB y ⟨hys, hyB⟩ t ht ht'
        _ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n) := by gcongr
    ext x
    refine ⟨fun hx => ⟨hsG x ⟨hx.1, closedBall_subset_closedBall h82 hx.2⟩, hx.2⟩,
      fun hx => ⟨?_, hx.2⟩⟩
    by_contra hxs
    have hxξ : dist x ξ ≤ σ₀ / 8 := hx.2
    obtain ⟨s, y, hys, hs, h2s, hyx, hsn⟩ :=
      hoffX x ⟨⟨hx.1, hxs⟩, closedBall_subset_closedBall h84 hx.2⟩
    -- `B_{3s}(x) ⊆ B_{σ₀/2}(ξ)`, so `μ(B_{3s}(x) ∖ F) = 0`
    have h0 : R.measure (closedBall x (3 * s) \ F) = 0 := by
      refine measure_mono_null (fun w hw hws => hw.2 (hsG w ⟨hws, ?_⟩))
        Measure.measure_compl_support
      rw [mem_closedBall]
      linarith only [dist_triangle w x ξ, mem_closedBall.mp hw.1, h2s, hxξ, hσ₀]
    -- `B_{3s}(x) ⊆ B_{5s}(y)`, `y ∈ spt μ ∩ B_{σ₀/2}(ξ)` and `5s ≤ σ₀/2`
    have hI : ∫⁻ w in closedBall x (3 * s), ENNReal.ofReal (e w) ∂R.measure ≤
        ENNReal.ofReal (β' ^ 2 * L ^ 2 * (5 * s) ^ n) := by
      have hyξ : dist y ξ ≤ σ₀ / 2 := by
        linarith only [dist_triangle y x ξ, hyx, h2s, hxξ, hσ₀]
      calc ∫⁻ w in closedBall x (3 * s), ENNReal.ofReal (e w) ∂R.measure
          ≤ ∫⁻ w in closedBall y (5 * s), ENNReal.ofReal (e w) ∂R.measure :=
            lintegral_mono_set
              (closedBall_subset_closedBall' (by rw [dist_comm]; linarith only [hyx]))
        _ ≤ _ := hB y ⟨hys, mem_closedBall.mpr hyξ⟩ (5 * s) (by positivity)
            (by linarith only [h2s, hxξ, hσ₀])
    rw [h0, zero_add] at hsn
    have hlt : ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal (C₉ * (β' ^ 2 * L ^ 2 * (5 * s) ^ n)) := by
      rw [ENNReal.ofReal_mul hC₉.le]
      exact hsn.trans (by gcongr)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hlt
    have hsn0 : 0 < s ^ n := by positivity
    have hL2 : L ^ 2 ≤ 1 := pow_le_one₀ hL.le hL1
    have hsmall : C₉ * (β' ^ 2 * L ^ 2 * (5 * s) ^ n) ≤ s ^ n / 2 := by
      calc C₉ * (β' ^ 2 * L ^ 2 * (5 * s) ^ n) = (C₉ * 5 ^ n * β' ^ 2) * L ^ 2 * s ^ n := by
            rw [mul_pow]
            ring
        _ ≤ (1 / 2) * 1 * s ^ n := by gcongr
        _ = s ^ n / 2 := by ring
    linarith only [hlt, hsmall, hsn0]
  refine ⟨ι, ι', f, hιι', hιT₀, fun v w => (hfLip v w).trans
    (mul_le_mul_of_nonneg_right hΛL (norm_nonneg _)), fun v => (hfbd v).trans ?_, h5A, h5B⟩
  calc Real.sqrt k * (C₆ * ε * σ₀) = (Real.sqrt k * C₆) * (ε * σ₀) := by ring
    _ ≤ C₇ * (ε * σ₀) := by gcongr
    _ = C₇ * ε * σ₀ := by ring
/-- Facts about `D = δ^{1/(2n+2)}` used in the tilt-excess decay step: if `δ ≤ min(1, η^{2n+2})`
then `0 < D ≤ η`, `δ ≤ D` and `√δ ≤ D`. -/
theorem Submission.dorag_tesDecay_rpow (n : ℕ) (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hδη : δ ≤ η ^ (2 * n + 2)) :
    0 < δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ∧ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ≤ η ∧
      δ ≤ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ∧ Real.sqrt δ ≤ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) := by
  have hα : (1 : ℝ) / (2 * (n : ℝ) + 2) = (((2 * n + 2 : ℕ) : ℝ))⁻¹ := by
    push_cast
    ring
  have hαpos : 0 < (1 : ℝ) / (2 * (n : ℝ) + 2) := by positivity
  have hα2 : (1 : ℝ) / (2 * (n : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine ⟨Real.rpow_pos_of_pos hδ _, ?_, ?_, ?_⟩
  · calc δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))
        ≤ (η ^ (2 * n + 2)) ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) :=
          Real.rpow_le_rpow hδ.le hδη hαpos.le
      _ = η := by rw [hα, Real.pow_rpow_inv_natCast hη.le (by omega)]
  · calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hα2

/-- The height bound produced by the plane reduction of Step 1:
`2C₃Dσ + (4a/M)^{1/2}σ = C₁₁Dσ` for `a = C₃D²σⁿ`, `M = ω_nσⁿ/2`. -/
theorem Submission.dorag_tesDecay_height_const (n : ℕ) (C₃ ω D σ : ℝ) (hC₃ : 0 ≤ C₃) (hω : 0 < ω)
    (hD : 0 ≤ D) (hσ : 0 < σ) :
    C₃ * D * (2 * σ) + Real.sqrt (4 * (C₃ * D ^ 2 * σ ^ n) / (ω * σ ^ n / 2)) * σ =
      (2 * C₃ + Real.sqrt (8 * C₃ / ω)) * D * σ := by
  have hσn : 0 < σ ^ n := pow_pos hσ n
  have h1 : 4 * (C₃ * D ^ 2 * σ ^ n) / (ω * σ ^ n / 2) = 8 * C₃ / ω * D ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hD]
  ring

/-- A finite `[0, ∞]` quantity bounded by `ofReal a` is `ofReal I` for a real `0 ≤ I ≤ a`. -/
theorem Submission.dorag_tesDecay_real_of_le {J : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a)
    (h : J ≤ ENNReal.ofReal a) : ∃ I : ℝ, 0 ≤ I ∧ ENNReal.ofReal I = J ∧ I ≤ a :=
  ⟨J.toReal, ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h),
    ENNReal.toReal_le_of_le_ofReal ha h⟩

/-- Step 1, the normalised excess `E₀ = max(σ⁻ⁿI, κ²σ²/δ)` (`I = ∫_{B_σ(ξ)}|p_x − p_{T'}|² dμ`):
`I ≤ σⁿE₀`, `κ²σ² ≤ δE₀`, `E₀ ≤ C₃D²` (as `κσ ≤ δ²`) and `κσ ≤ D E₀^{1/2}` (as `δ^{1/2} ≤ D`). -/
theorem Submission.dorag_tesDecay_excess_facts (n : ℕ) (C₃ D δ E₀ I κ ρ σ : ℝ) (hδ : 0 < δ)
    (hδ8 : δ ≤ 1 / 8) (hσ : 0 < σ) (hσδρ : σ ≤ δ * ρ) (hκ : 0 ≤ κ) (hκρ : κ * ρ ≤ δ)
    (hC₃ : 1 ≤ C₃) (hδD : δ ≤ D) (hsδD : Real.sqrt δ ≤ D)
    (hIa : I ≤ C₃ * D ^ 2 * σ ^ n) (hE₀def : E₀ = max (1 / σ ^ n * I) (κ ^ 2 * σ ^ 2 / δ)) :
    0 ≤ E₀ ∧ I ≤ σ ^ n * E₀ ∧ κ ^ 2 * σ ^ 2 ≤ δ * E₀ ∧ E₀ ≤ C₃ * D ^ 2 ∧
      κ * σ ≤ D * Real.sqrt E₀ := by
  have hE₀1 : 1 / σ ^ n * I ≤ E₀ := hE₀def ▸ le_max_left _ _
  have hE₀2 : κ ^ 2 * σ ^ 2 / δ ≤ E₀ := hE₀def ▸ le_max_right _ _
  have hσn : 0 < σ ^ n := pow_pos hσ n
  have hκE : κ ^ 2 * σ ^ 2 ≤ δ * E₀ := by
    calc κ ^ 2 * σ ^ 2 = δ * (κ ^ 2 * σ ^ 2 / δ) := by field_simp
      _ ≤ δ * E₀ := by gcongr
  refine ⟨le_trans (by positivity) hE₀2, ?_, hκE, ?_, ?_⟩
  · calc I = σ ^ n * (1 / σ ^ n * I) := by field_simp
      _ ≤ σ ^ n * E₀ := by gcongr
  · rw [hE₀def]
    apply max_le
    · calc 1 / σ ^ n * I ≤ 1 / σ ^ n * (C₃ * D ^ 2 * σ ^ n) := by gcongr
        _ = C₃ * D ^ 2 := by field_simp
    · have hκσ : κ * σ ≤ δ * δ := by
        calc κ * σ ≤ κ * (δ * ρ) := by gcongr
          _ = δ * (κ * ρ) := by ring
          _ ≤ δ * δ := by gcongr
      have h1 : κ ^ 2 * σ ^ 2 ≤ δ ^ 4 := by
        calc κ ^ 2 * σ ^ 2 = (κ * σ) ^ 2 := by ring
          _ ≤ (δ * δ) ^ 2 := pow_le_pow_left₀ (mul_nonneg hκ hσ.le) hκσ 2
          _ = δ ^ 4 := by ring
      have h3 : δ ^ 3 ≤ D ^ 2 := by
        calc δ ^ 3 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le (by linarith) (by norm_num)
          _ ≤ D ^ 2 := pow_le_pow_left₀ hδ.le hδD 2
      rw [div_le_iff₀ hδ]
      calc κ ^ 2 * σ ^ 2 ≤ δ ^ 4 := h1
        _ = δ ^ 3 * δ := by ring
        _ ≤ D ^ 2 * δ := by gcongr
        _ = 1 * (D ^ 2 * δ) := by ring
        _ ≤ C₃ * (D ^ 2 * δ) := by gcongr
        _ = C₃ * D ^ 2 * δ := by ring
  · rw [← Real.sqrt_sq (mul_nonneg hκ hσ.le)]
    calc Real.sqrt ((κ * σ) ^ 2) ≤ Real.sqrt (δ * E₀) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact hκE)
      _ = Real.sqrt δ * Real.sqrt E₀ := Real.sqrt_mul hδ.le _
      _ ≤ D * Real.sqrt E₀ := by gcongr

/-- Step 11: `θE₀ = θE_*(ξ, σ, T')` is at most `θE_*(ξ, σ, T)` when `E(ξ, σ, T') ≤ E(ξ, σ, T)`. -/
theorem Submission.dorag_tesDecay_rhs (θ E₀ a b I : ℝ) (J : ℝ≥0∞) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hE₀ : E₀ = max (a * I) b) (hI : ENNReal.ofReal I ≤ J) :
    ENNReal.ofReal (θ * E₀) ≤ ENNReal.ofReal θ * max (ENNReal.ofReal a * J) (ENNReal.ofReal b) := by
  rw [ENNReal.ofReal_mul hθ, hE₀, ENNReal.ofReal_max, ENNReal.ofReal_mul ha]
  gcongr

/-- `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`: an `Hⁿ⌞(M ∩ W)`-a.e. property holds `μ_V`-a.e. on `W`. -/
theorem Submission.dorag_tesDecay_ae_of_carrier {P n : ℕ} {U W : Set (Euclid P)} (R : IMRep U n)
    (hW : MeasurableSet W) {p : Euclid P → Prop}
    (h : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), p x) : ∀ᵐ x ∂R.measure, x ∈ W → p x := by
  have h1 : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ W → p x := by
    rw [← ae_restrict_iff' hW, Measure.restrict_restrict hW, Set.inter_comm]
    exact h
  exact (withDensity_absolutelyContinuous _ _).ae_le h1

/-- The energy normalisation of Step 7: `s⁻²(2 + C₇)I ≤ (σ/8)ⁿ` for `s² = (2 + C₇)8ⁿE₀`. -/
theorem Submission.dorag_tesDecay_energy_real (n : ℕ) (C₇ E₀ I σ : ℝ) (hC₇ : 0 < C₇) (hE₀ : 0 < E₀)
    (hσ : 0 < σ) (hIle : I ≤ σ ^ n * E₀) :
    (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ ^ 2 * (2 * I + C₇ * I) ≤ (σ / 4 / 2) ^ n := by
  have hpos : 0 < (2 + C₇) * 8 ^ n * E₀ := by positivity
  rw [inv_pow, Real.sq_sqrt hpos.le]
  have h8 : (σ / 4 / 2) ^ n = σ ^ n / 8 ^ n := by
    rw [show σ / 4 / 2 = σ / 8 by ring, div_pow]
  rw [h8, inv_mul_le_iff₀ hpos]
  have h8pos : (0 : ℝ) < 8 ^ n := by positivity
  calc 2 * I + C₇ * I = (2 + C₇) * I := by ring
    _ ≤ (2 + C₇) * (σ ^ n * E₀) := by gcongr
    _ = (2 + C₇) * 8 ^ n * E₀ * (σ ^ n / 8 ^ n) := by field_simp

/-- The weak-form normalisation of Step 7 (Simon (15)–(17)): the right side of the weak equation
for `fʲ`, divided by `s = ((2 + C₇)8ⁿE₀)^{1/2}`, is at most `δ_h(σ/8)ⁿG`. -/
theorem Submission.dorag_tesDecay_weak_real (n k : ℕ) (C₃ C₇ ω D δh E₀ I κ σ G : ℝ)
    (hC₃ : 1 ≤ C₃) (hC₇ : 0 < C₇) (hω : 0 < ω) (hD : 0 ≤ D) (hE₀ : 0 < E₀) (hσ : 0 < σ)
    (hG : 0 ≤ G) (hIle : I ≤ σ ^ n * E₀) (hE₀le : E₀ ≤ C₃ * D ^ 2)
    (hκσ : κ * σ ≤ D * Real.sqrt E₀)
    (hδh : 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ + 2 * ω / 4 ^ (n + 1)) /
      Real.sqrt ((2 + C₇) * 8 ^ n) * D ≤ δh) :
    (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ *
        (G * ((2 + 2 ^ (n + 1) * k) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n))) ≤
      δh * (σ / 4 / 2) ^ n * G := by
  set r := Real.sqrt E₀ with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hE₀
  have hrr : r * r = E₀ := Real.mul_self_sqrt hE₀.le
  have hC₁₃ : 0 < (2 + C₇) * 8 ^ n := by positivity
  have hsC : 0 < Real.sqrt ((2 + C₇) * 8 ^ n) := Real.sqrt_pos.mpr hC₁₃
  have hs : Real.sqrt ((2 + C₇) * 8 ^ n * E₀) = Real.sqrt ((2 + C₇) * 8 ^ n) * r := by
    rw [Real.sqrt_mul hC₁₃.le]
  have hsC₃ : 1 ≤ Real.sqrt C₃ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hC₃
  -- `√E₀ ≤ √C₃ D`
  have hrD : r ≤ Real.sqrt C₃ * D := by
    rw [hr, ← Real.sqrt_sq hD, ← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hE₀le
  -- `I ≤ σⁿ √E₀ √C₃ D`
  have hI' : I ≤ σ ^ n * r * (Real.sqrt C₃ * D) := by
    calc I ≤ σ ^ n * E₀ := hIle
      _ = σ ^ n * r * r := by rw [← hrr]; ring
      _ ≤ σ ^ n * r * (Real.sqrt C₃ * D) := by gcongr
  set B := (2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ + 2 * ω / 4 ^ (n + 1) with hB
  have hX : (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n) ≤
      σ ^ n * r * D * B := by
    have h1 : (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) ≤
        (2 + 2 ^ (n + 1) * (k : ℝ)) * (1 + C₇) * (σ ^ n * r * (Real.sqrt C₃ * D)) := by
      have : (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) =
          (2 + 2 ^ (n + 1) * (k : ℝ)) * (1 + C₇) * I := by
        ring
      rw [this]
      gcongr
    have h2 : κ * (σ / 4) * (2 * ω * (σ / 4) ^ n) = (κ * σ) * (2 * ω * σ ^ n / 4 ^ (n + 1)) := by
      rw [div_pow, pow_succ]
      field_simp
    have h3 : (κ * σ) * (2 * ω * σ ^ n / 4 ^ (n + 1)) ≤ (D * r) * (2 * ω * σ ^ n / 4 ^ (n + 1)) := by
      gcongr
    calc (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n)
        ≤ (2 + 2 ^ (n + 1) * (k : ℝ)) * (1 + C₇) * (σ ^ n * r * (Real.sqrt C₃ * D)) +
            (D * r) * (2 * ω * σ ^ n / 4 ^ (n + 1)) := by rw [h2]; exact add_le_add h1 h3
      _ = σ ^ n * r * D * B := by rw [hB]; ring
  have h8 : (σ / 4 / 2) ^ n = σ ^ n / 8 ^ n := by
    rw [show σ / 4 / 2 = σ / 8 by ring, div_pow]
  have hB0 : 0 ≤ B := by positivity
  calc (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ *
        (G * ((2 + 2 ^ (n + 1) * k) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n)))
      ≤ (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ * (G * (σ ^ n * r * D * B)) := by gcongr
    _ = (8 ^ n * B / Real.sqrt ((2 + C₇) * 8 ^ n) * D) * (σ / 4 / 2) ^ n * G := by
      rw [hs, h8]
      field_simp
    _ ≤ δh * (σ / 4 / 2) ^ n * G := by gcongr

/-- Step 7 (Simon (17)–(18)): for each component `fʲ` of the Lipschitz approximation, the
harmonic approximation lemma applied to `w = s⁻¹fʲ` on `Bⁿ_{σ/8}` gives an affine
`a + b` with `‖b‖ ≤ C_H`, `|a| ≤ C_H s⁻¹C₇Dσω^{1/2} + C_Hε'^{1/2}σ/8` and the `L²` decay
on `Bⁿ_{θ'σ/8}`. -/
theorem Submission.dorag_tesDecay_harmonic_step (n k : ℕ) (f : Euclid n → Euclid k)
    (C₃ C₇ CH ω D δh ε' E₀ I κ σ s θ' : ℝ)
    (hHA' : ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w →
      ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n →
      (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
        |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) →
      ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ CH ∧
        |a| ≤ CH * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) +
          CH * Real.sqrt ε' * R₀ ∧
        ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤
          CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2))
    (hGE : ∀ j : Fin k, ∫ v in ball (0 : Euclid n) (σ / 4 / 2),
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 ≤ 2 * I + C₇ * I)
    (hGW : ∀ (j : Fin k) (ζ : Euclid n → ℝ) (G : ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Euclid n) (σ / 4 / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
      |∫ v in ball (0 : Euclid n) (σ / 4 / 2), ∑ i : Fin n,
        fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤
        G * ((2 + 2 ^ (n + 1) * k) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n)))
    (hf1 : ∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) (hfb : ∀ v, ‖f v‖ ≤ C₇ * D * σ)
    (hsdef : s = Real.sqrt ((2 + C₇) * 8 ^ n * E₀))
    (hC₃ : 1 ≤ C₃) (hC₇ : 0 < C₇) (hCH : 0 < CH) (hω : 0 < ω) (hD : 0 ≤ D) (hE₀ : 0 < E₀)
    (hσ : 0 < σ) (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4)
    (hIE : I ≤ σ ^ n * E₀) (hE₀le : E₀ ≤ C₃ * D ^ 2) (hκσE : κ * σ ≤ D * Real.sqrt E₀)
    (hD14 : 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ + 2 * ω / 4 ^ (n + 1)) /
      Real.sqrt ((2 + C₇) * 8 ^ n) * D ≤ δh)
    (hvol : volume.real (ball (0 : Euclid n) (σ / 4 / 2)) = (σ / 4 / 2) ^ n * ω) :
    ∀ j : Fin k, ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ CH ∧
      |a| ≤ CH * (s⁻¹ * (C₇ * D * σ) * Real.sqrt ω) + CH * Real.sqrt ε' * (σ / 4 / 2) ∧
      ∫ v in ball (0 : Euclid n) (θ' * (σ / 4 / 2)),
          (s⁻¹ * EuclideanSpace.proj j (f v) - a - b v) ^ 2 ≤
        CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * (σ / 4 / 2)) ^ (n + 2) := by
  intro j
  have hs : 0 < s := hsdef ▸ Real.sqrt_pos.mpr (by positivity)
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hR₀ : 0 < σ / 4 / 2 := by positivity
  have hderiv : ∀ v, fderiv ℝ (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) v =
      s⁻¹ • fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v := by
    intro v
    have : (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) =
        s⁻¹ • fun v => EuclideanSpace.proj j (f v) := rfl
    rw [this, fderiv_const_smul_field]
    rfl
  have hproj : ∀ y : Euclid k, |EuclideanSpace.proj j y| ≤ ‖y‖ := fun y => by
    simpa using PiLp.norm_apply_le y j
  -- `w = s⁻¹fʲ` is `s⁻¹`-Lipschitz
  have hwLip : LipschitzWith (Real.toNNReal s⁻¹) (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.coe_toNNReal _ hsi.le, Real.dist_eq, dist_eq_norm, ← mul_sub, ← map_sub, abs_mul,
      abs_of_pos hsi]
    gcongr
    exact (hproj _).trans (hf1 v w)
  -- the energy of `w` on `Bⁿ_{σ/8}` is at most `(σ/8)ⁿ`
  have hwE : ∫ v in ball (0 : Euclid n) (σ / 4 / 2),
      ‖fderiv ℝ (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) v‖ ^ 2 ≤ (σ / 4 / 2) ^ n := by
    simp_rw [hderiv, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos hsi]
    rw [integral_const_mul]
    refine le_trans ?_ (Submission.dorag_tesDecay_energy_real n C₇ E₀ I σ hC₇ hE₀ hσ hIE)
    rw [← hsdef]
    exact mul_le_mul_of_nonneg_left (hGE j) (by positivity)
  -- `w` is weakly `δ_h`-harmonic on `Bⁿ_{σ/8}`
  have hwW : ∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Euclid n) (σ / 4 / 2) → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
      |∫ v in ball (0 : Euclid n) (σ / 4 / 2), ∑ i : Fin n,
        fderiv ℝ (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * (σ / 4 / 2) ^ n * G := by
    intro ζ hζ hζc hζs G hG
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    have h1 := hGW j ζ G hζ hζc hζs hG
    simp_rw [hderiv, smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [integral_const_mul, abs_mul, abs_of_pos hsi]
    refine le_trans (mul_le_mul_of_nonneg_left h1 hsi.le) ?_
    rw [hsdef]
    exact (Submission.dorag_tesDecay_weak_real n k C₃ C₇ ω D δh E₀ I κ σ G hC₃ hC₇ hω hD hE₀
      hσ hG0 hIE hE₀le hκσE hD14).trans_eq (mul_assoc _ _ _)
  obtain ⟨a, b, hb, ha, hab⟩ := hHA' (σ / 4 / 2) (fun v => s⁻¹ * EuclideanSpace.proj j (f v))
    (Real.toNNReal s⁻¹) hR₀ hwLip hwE hwW
  refine ⟨a, b, hb, ha.trans ?_, hab θ' hθ' hθ'4⟩
  -- `|a| ≤ A`, from `|w| ≤ s⁻¹C₇Dσ` on `Bⁿ_{σ/8}`
  gcongr
  have hw2 : ∫ v in ball (0 : Euclid n) (σ / 4 / 2), (s⁻¹ * EuclideanSpace.proj j (f v)) ^ 2 ≤
      (s⁻¹ * (C₇ * D * σ)) ^ 2 * ((σ / 4 / 2) ^ n * ω) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← hvol]
    refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top fun v _ => ?_
    rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hsi]
    gcongr
    exact (hproj _).trans (hfb v)
  calc Real.sqrt ((∫ v in ball (0 : Euclid n) (σ / 4 / 2),
        (s⁻¹ * EuclideanSpace.proj j (f v)) ^ 2) / (σ / 4 / 2) ^ n)
      ≤ Real.sqrt ((s⁻¹ * (C₇ * D * σ)) ^ 2 * ω) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ (by positivity)]
        exact hw2.trans_eq (by ring)
    _ = s⁻¹ * (C₇ * D * σ) * Real.sqrt ω := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- Bounds on the affine data `c, Λ` of Step 8 (Simon (18)): `|c| ≤ C₁₅DR₀` and
`‖Λ‖ ≤ kC_H(C₁₃C₃)^{1/2}D`, `R₀ = σ/8`. -/
theorem Submission.dorag_tesDecay_affine_consts (k : ℕ) (C₃ C₁₃ C₇ CH ω D E₀ ε' σ s A c Λ : ℝ)
    (hs : s = Real.sqrt (C₁₃ * E₀)) (hE₀ : 0 < E₀) (hE₀le : E₀ ≤ C₃ * D ^ 2) (hC₃ : 0 ≤ C₃)
    (hC₁₃ : 0 < C₁₃) (hD : 0 ≤ D) (hε'1 : ε' ≤ 1) (hCH : 0 < CH) (hC₇ : 0 < C₇) (hω : 0 < ω)
    (hσ : 0 < σ)
    (hA : A = CH * (s⁻¹ * (C₇ * D * σ) * Real.sqrt ω) + CH * Real.sqrt ε' * (σ / 4 / 2))
    (hc : c ≤ k * s * A) (hΛ : Λ ≤ k * s * CH) :
    c ≤ (k + 1) * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)) * D * (σ / 4 / 2) ∧
      Λ ≤ k * CH * Real.sqrt (C₁₃ * C₃) * D := by
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (mul_pos hC₁₃ hE₀)
  have hsle : s ≤ Real.sqrt (C₁₃ * C₃) * D := by
    rw [hs, ← Real.sqrt_sq hD, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by rw [mul_assoc]; gcongr)
  have hε's : Real.sqrt ε' ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hε'1
  have hkA : (k : ℝ) * s * A ≤
      k * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)) * D * (σ / 4 / 2) := by
    have h1 : (k : ℝ) * s * A =
        k * (CH * (C₇ * D * σ) * Real.sqrt ω + s * (CH * Real.sqrt ε' * (σ / 4 / 2))) := by
      rw [hA]
      field_simp
    rw [h1]
    have h3 : (k : ℝ) * (CH * (C₇ * D * σ) * Real.sqrt ω + s * (CH * Real.sqrt ε' * (σ / 4 / 2))) ≤
        k * (CH * (C₇ * D * σ) * Real.sqrt ω +
          (Real.sqrt (C₁₃ * C₃) * D) * (CH * 1 * (σ / 4 / 2))) := by
      gcongr
    refine h3.trans (le_of_eq ?_)
    ring
  constructor
  · refine hc.trans (hkA.trans ?_)
    gcongr
    linarith
  · refine hΛ.trans ?_
    calc (k : ℝ) * s * CH ≤ k * (Real.sqrt (C₁₃ * C₃) * D) * CH := by gcongr
      _ = k * CH * Real.sqrt (C₁₃ * C₃) * D := by ring

/-- The final real inequality of Steps 9–10 (Simon (20)–(23)), with `R₀ = σ/8`, `t = θ'R₀`:
`(θ₀σ)^{-n}C_T(t^{-2}((1 + n2ⁿ)ks²Q + K²C₇I) + κ²t²·2ωtⁿ) ≤ θ₀E₀`, `θ₀ = θ'/32`. -/
theorem Submission.dorag_tesDecay_final_real (n k : ℕ)
    (CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ' ε' D δ E₀ I s Q K σ R₀ t κ : ℝ)
    (hCT : 0 < CT) (hCH : 0 < CH) (hC₇ : 0 < C₇) (hC₁₃ : 0 < C₁₃) (hω : 0 < ω)
    (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4) (hε' : 0 ≤ ε') (hδ : 0 ≤ δ) (hE₀ : 0 ≤ E₀)
    (hR₀ : 0 < R₀) (hσ : σ = 8 * R₀) (ht : t = θ' * R₀) (hs : s ^ 2 = C₁₃ * E₀)
    (hQ : Q = CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2))
    (hK : 0 ≤ K) (hKle : K ≤ C₁₇ * D * R₀) (hI : 0 ≤ I) (hIle : I ≤ σ ^ n * E₀)
    (hκ : κ ^ 2 * σ ^ 2 ≤ δ * E₀)
    (hC₁₆ : C₁₆ = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ + C₁₇ ^ 2 * C₇ * 8 ^ n +
      2 * ω))
    (h1 : C₁₆ * θ' ^ 2 ≤ θ' / 128) (h2 : C₁₆ * (ε' / θ' ^ (n + 2)) ≤ θ' / 128)
    (h3 : C₁₆ * (D ^ 2 / θ' ^ (n + 2)) ≤ θ' / 128) (h4 : C₁₆ * δ ≤ θ' / 128) :
    1 / (θ' / 32 * σ) ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q) +
      K ^ 2 * (C₇ * I)) + κ ^ 2 * t ^ 2 * (2 * ω * t ^ n))) ≤ θ' / 32 * E₀ := by
  subst hσ ht
  set t := θ' * R₀ with ht
  have htpos : 0 < t := mul_pos hθ' hR₀
  have hθ'pos : 0 < θ' ^ (n + 2) := pow_pos hθ' _
  have hpre : 1 / (θ' / 32 * (8 * R₀)) ^ n = 4 ^ n / t ^ n := by
    rw [show θ' / 32 * (8 * R₀) = t / 4 by rw [ht]; ring, div_pow]
    field_simp
  have htn : 0 < t ^ n := pow_pos htpos n
  set a := ε' / θ' ^ (n + 2) with ha
  set b := D ^ 2 / θ' ^ (n + 2) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  -- the three terms
  have hT1 : 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q)))) =
      4 ^ n * CT * ((1 + n * 2 ^ n) * k * CH * C₁₃) * (a + θ' ^ 2) * E₀ := by
    rw [hs, hQ]
    field_simp
    ring
  have hT2 : 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * (K ^ 2 * (C₇ * I)))) ≤
      4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) * b * E₀ := by
    have hK2 : K ^ 2 ≤ (C₁₇ * D * R₀) ^ 2 := pow_le_pow_left₀ hK hKle 2
    calc 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * (K ^ 2 * (C₇ * I))))
        ≤ 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((C₁₇ * D * R₀) ^ 2 * (C₇ * ((8 * R₀) ^ n * E₀))))) := by
          gcongr
      _ = 4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) * b * E₀ := by
          rw [hb, ht]
          field_simp
        _ ≤ C₇ / L ^ 2 := by gcongr
    calc R.measure (closedBall ξ (σ₀ / 2) \ F) +
          μHE[n] ((F \ R.measure.support) ∩ closedBall ξ (σ₀ / 4))
        ≤ ENNReal.ofReal cb * X + ENNReal.ofReal K₁ * (ENNReal.ofReal cb * X + X) :=
          add_le_add h1 h4
      _ = ENNReal.ofReal (cb + K₁ * (cb + 1)) * X := by
          rw [ENNReal.ofReal_add hcb (by positivity), ENNReal.ofReal_mul hK₁,
            ENNReal.ofReal_add hcb zero_le_one, ENNReal.ofReal_one]
          ring
      _ ≤ ENNReal.ofReal (C₇ / L ^ 2) * X := by gcongr
  -- 5B: under the small-tilt hypothesis `spt μ ∩ B_{σ₀/2}(ξ) ⊆ G ⊆ F`, and (10') excludes holes
  have h5B : (∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 →
      ∫⁻ x in closedBall y t, ENNReal.ofReal (e x) ∂R.measure ≤
        ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n)) →
      R.measure.support ∩ closedBall ξ (σ₀ / 8) = F ∩ closedBall ξ (σ₀ / 8) := by
    intro hB
    have h82 : σ₀ / 8 ≤ σ₀ / 2 := by linarith only [hσ₀]
    have h84 : σ₀ / 8 ≤ σ₀ / 4 := by linarith only [hσ₀]
    have hsG : ∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), y ∈ F := by
      rintro y ⟨hys, hyB⟩
      refine hGF ⟨closedBall_subset_closedBall h24 hyB, hys, fun t ht ht' => ?_⟩
      calc ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂R.measure
          ≤ ∫⁻ x in closedBall y t, ENNReal.ofReal (e x) ∂R.measure :=
            lintegral_mono_set (closedBall_subset_closedBall (by linarith only [ht]))
        _ ≤ ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n) := hB y ⟨hys, hyB⟩ t ht ht'
        _ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n) := by gcongr
    ext x
    refine ⟨fun hx => ⟨hsG x ⟨hx.1, closedBall_subset_closedBall h82 hx.2⟩, hx.2⟩,
      fun hx => ⟨?_, hx.2⟩⟩
    by_contra hxs
    have hxξ : dist x ξ ≤ σ₀ / 8 := hx.2
    obtain ⟨s, y, hys, hs, h2s, hyx, hsn⟩ :=
      hoffX x ⟨⟨hx.1, hxs⟩, closedBall_subset_closedBall h84 hx.2⟩
    -- `B_{3s}(x) ⊆ B_{σ₀/2}(ξ)`, so `μ(B_{3s}(x) ∖ F) = 0`
    have h0 : R.measure (closedBall x (3 * s) \ F) = 0 := by
      refine measure_mono_null (fun w hw hws => hw.2 (hsG w ⟨hws, ?_⟩))
        Measure.measure_compl_support
      rw [mem_closedBall]
      linarith only [dist_triangle w x ξ, mem_closedBall.mp hw.1, h2s, hxξ, hσ₀]
    -- `B_{3s}(x) ⊆ B_{5s}(y)`, `y ∈ spt μ ∩ B_{σ₀/2}(ξ)` and `5s ≤ σ₀/2`
    have hI : ∫⁻ w in closedBall x (3 * s), ENNReal.ofReal (e w) ∂R.measure ≤
        ENNReal.ofReal (β' ^ 2 * L ^ 2 * (5 * s) ^ n) := by
      have hyξ : dist y ξ ≤ σ₀ / 2 := by
        linarith only [dist_triangle y x ξ, hyx, h2s, hxξ, hσ₀]
      calc ∫⁻ w in closedBall x (3 * s), ENNReal.ofReal (e w) ∂R.measure
          ≤ ∫⁻ w in closedBall y (5 * s), ENNReal.ofReal (e w) ∂R.measure :=
            lintegral_mono_set
              (closedBall_subset_closedBall' (by rw [dist_comm]; linarith only [hyx]))
        _ ≤ _ := hB y ⟨hys, mem_closedBall.mpr hyξ⟩ (5 * s) (by positivity)
            (by linarith only [h2s, hxξ, hσ₀])
    rw [h0, zero_add] at hsn
    have hlt : ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal (C₉ * (β' ^ 2 * L ^ 2 * (5 * s) ^ n)) := by
      rw [ENNReal.ofReal_mul hC₉.le]
      exact hsn.trans (by gcongr)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hlt
    have hsn0 : 0 < s ^ n := by positivity
    have hL2 : L ^ 2 ≤ 1 := pow_le_one₀ hL.le hL1
    have hsmall : C₉ * (β' ^ 2 * L ^ 2 * (5 * s) ^ n) ≤ s ^ n / 2 := by
      calc C₉ * (β' ^ 2 * L ^ 2 * (5 * s) ^ n) = (C₉ * 5 ^ n * β' ^ 2) * L ^ 2 * s ^ n := by
            rw [mul_pow]
            ring
        _ ≤ (1 / 2) * 1 * s ^ n := by gcongr
        _ = s ^ n / 2 := by ring
    linarith only [hlt, hsmall, hsn0]
  refine ⟨ι, ι', f, hιι', hιT₀, fun v w => (hfLip v w).trans
    (mul_le_mul_of_nonneg_right hΛL (norm_nonneg _)), fun v => (hfbd v).trans ?_, h5A, h5B⟩
  calc Real.sqrt k * (C₆ * ε * σ₀) = (Real.sqrt k * C₆) * (ε * σ₀) := by ring
    _ ≤ C₇ * (ε * σ₀) := by gcongr
    _ = C₇ * ε * σ₀ := by ring
  have hT3 : 4 ^ n / t ^ n * (CT * (κ ^ 2 * t ^ 2 * (2 * ω * t ^ n))) ≤
      4 ^ n * CT * (2 * ω) * δ * E₀ := by
    have htσ : t ^ 2 ≤ (8 * R₀) ^ 2 := by
      have : t ≤ 8 * R₀ := by rw [ht]; nlinarith
      exact pow_le_pow_left₀ htpos.le this 2
    have hκt : κ ^ 2 * t ^ 2 ≤ δ * E₀ := le_trans (by gcongr) hκ
    calc 4 ^ n / t ^ n * (CT * (κ ^ 2 * t ^ 2 * (2 * ω * t ^ n)))
        = 4 ^ n * CT * (2 * ω) * (κ ^ 2 * t ^ 2) := by field_simp
      _ ≤ 4 ^ n * CT * (2 * ω) * (δ * E₀) := by gcongr
      _ = 4 ^ n * CT * (2 * ω) * δ * E₀ := by ring
  -- coefficient comparisons with `C₁₆`
  have hc1 : 4 ^ n * CT * ((1 + n * 2 ^ n) * k * CH * C₁₃) ≤ C₁₆ := by
    rw [hC₁₆]
    have : (1 + n * 2 ^ n) * (k : ℝ) * CH * C₁₃ ≤
        (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ + C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω := by
      have h0 : (0 : ℝ) ≤ C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω := by positivity
      have h1' : (1 + n * 2 ^ n) * (k : ℝ) * CH * C₁₃ ≤ (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ := by
        gcongr
        linarith
      linarith
    gcongr
  have hc2 : 4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) ≤ C₁₆ := by
    rw [hC₁₆]
    gcongr
    have : (0 : ℝ) ≤ (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ := by positivity
    linarith
  have hc3 : 4 ^ n * CT * (2 * ω) ≤ C₁₆ := by
    rw [hC₁₆]
    gcongr
    have : (0 : ℝ) ≤ (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ := by positivity
    have : (0 : ℝ) ≤ C₁₇ ^ 2 * C₇ * 8 ^ n := by positivity
    linarith
  rw [hpre]
  calc 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q) + K ^ 2 * (C₇ * I)) +
        κ ^ 2 * t ^ 2 * (2 * ω * t ^ n)))
      = 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q)))) +
          4 ^ n / t ^ n * (CT * (1 / t ^ 2 * (K ^ 2 * (C₇ * I)))) +
          4 ^ n / t ^ n * (CT * (κ ^ 2 * t ^ 2 * (2 * ω * t ^ n))) := by ring
    _ ≤ 4 ^ n * CT * ((1 + n * 2 ^ n) * k * CH * C₁₃) * (a + θ' ^ 2) * E₀ +
          4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) * b * E₀ + 4 ^ n * CT * (2 * ω) * δ * E₀ := by
          rw [hT1]
          exact add_le_add (add_le_add le_rfl hT2) hT3
    _ ≤ C₁₆ * (a + θ' ^ 2) * E₀ + C₁₆ * b * E₀ + C₁₆ * δ * E₀ := by
          gcongr
    _ = (C₁₆ * a + C₁₆ * θ' ^ 2 + C₁₆ * b + C₁₆ * δ) * E₀ := by ring
    _ ≤ (θ' / 128 + θ' / 128 + θ' / 128 + θ' / 128) * E₀ := by gcongr
    _ = θ' / 32 * E₀ := by ring

/-- Steps 9–10, `ENNReal` form: the chain of the tilt-height, graph-height, affine-assembly and
density estimates gives `(θ₀σ)^{-n}∫_{B_{θ₀σ}(ξ)}|p_x − p_S|² dμ ≤ θ₀E₀`. -/
theorem Submission.dorag_tesDecay_conclude (n k : ℕ) (X J L MF Mt : ℝ≥0∞)
    (CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ' ε' D δ E₀ I s Q K σ R₀ t κ : ℝ)
    (hX : X ≤ ENNReal.ofReal CT * (ENNReal.ofReal (1 / t ^ 2) * J +
      ENNReal.ofReal (κ ^ 2 * t ^ 2) * Mt))
    (hJ : J ≤ ENNReal.ofReal (1 + n * 2 ^ n) * L + ENNReal.ofReal (K ^ 2) * MF)
    (hL : L ≤ ENNReal.ofReal (k * s ^ 2 * Q)) (hMF : MF ≤ ENNReal.ofReal (C₇ * I))
    (hMt : Mt ≤ ENNReal.ofReal (2 * ω * t ^ n))
    (hCT : 0 < CT) (hCH : 0 < CH) (hC₇ : 0 < C₇) (hC₁₃ : 0 < C₁₃) (hω : 0 < ω)
    (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4) (hε' : 0 ≤ ε') (hδ : 0 ≤ δ) (hE₀ : 0 ≤ E₀)
    (hR₀ : 0 < R₀) (hσ : σ = 8 * R₀) (ht : t = θ' * R₀) (hs : s ^ 2 = C₁₃ * E₀)
    (hQ : Q = CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2))
    (hK : 0 ≤ K) (hKle : K ≤ C₁₇ * D * R₀) (hI : 0 ≤ I) (hIle : I ≤ σ ^ n * E₀)
    (hκ : κ ^ 2 * σ ^ 2 ≤ δ * E₀)
    (hC₁₆ : C₁₆ = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ + C₁₇ ^ 2 * C₇ * 8 ^ n +
      2 * ω))
    (h1 : C₁₆ * θ' ^ 2 ≤ θ' / 128) (h2 : C₁₆ * (ε' / θ' ^ (n + 2)) ≤ θ' / 128)
    (h3 : C₁₆ * (D ^ 2 / θ' ^ (n + 2)) ≤ θ' / 128) (h4 : C₁₆ * δ ≤ θ' / 128) :
    ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * X ≤ ENNReal.ofReal (θ' / 32 * E₀) := by
  have htpos : 0 < t := ht ▸ mul_pos hθ' hR₀
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  calc ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * X
      ≤ ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * (ENNReal.ofReal CT * (ENNReal.ofReal (1 / t ^ 2) *
        (ENNReal.ofReal (1 + n * 2 ^ n) * ENNReal.ofReal (k * s ^ 2 * Q) +
          ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C₇ * I)) +
        ENNReal.ofReal (κ ^ 2 * t ^ 2) * ENNReal.ofReal (2 * ω * t ^ n))) := by
        gcongr
        refine hX.trans ?_
        gcongr
        refine hJ.trans ?_
        gcongr
    _ = ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) *
          (k * s ^ 2 * Q) + K ^ 2 * (C₇ * I)) + κ ^ 2 * t ^ 2 * (2 * ω * t ^ n)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (θ' / 32 * E₀) :=
        ENNReal.ofReal_le_ofReal (Submission.dorag_tesDecay_final_real n k CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ'
          ε' D δ E₀ I s Q K σ R₀ t κ hCT hCH hC₇ hC₁₃ hω hθ' hθ'4 hε' hδ hE₀ hR₀ hσ ht hs hQ hK
          hKle hI hIle hκ hC₁₆ h1 h2 h3 h4)

/-- Steps 3–9 of the tilt-excess decay (Simon Ch. 5, proof of 4.5, (5)–(22)).  Let `f` be the
`1`-Lipschitz approximation over the plane `T'` (tilt `I ≤ σⁿE₀` and height `≤ C₁₁Dσ` on `B_σ(ξ)`)
with the estimate (4′) for the non-graph part.  Then (Steps 3–6) every component `fʲ` has energy
`≤ (2 + C₇)I` and is weakly harmonic up to an error, on `Bⁿ_{σ/8}`; (Step 7) the harmonic
approximation lemma applies to `(C₁₃E₀)^{-1/2}fʲ`; (Step 8) the components assemble to an affine
map `c + Λ`; (Step 9) the height about `S = graph Λ` at `τ = ξ + ι'c` is controlled, and the
tilt-height estimate at `(τ, θ'σ/8)` gives `(θ₀σ)^{-n}∫_{B_{θ₀σ}(ξ)}|p_x − p_S|² dμ ≤ θ₀E₀`,
`θ₀ = θ'/32`. -/
theorem Submission.dorag_tesDecay_core (n k : ℕ) (hn : 0 < n) (U W : Set (Euclid (n + k)))
    (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (σ : ℝ)
    (T' : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k))
    (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k)
    (C₃ C₇ C₁₁ C₁₃ C₁₄ C₁₅ C₁₆ C₁₇ CT CH ω θ' ε' δh D δ E₀ I : ℝ)
    (hW : IsOpen W) (hWU : W ⊆ U) (hH : AEStronglyMeasurable H R.measure)
    (hHκ : ∀ x, ‖H x‖ ≤ κ)
    (hMC : ∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X →
      tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure)
    (hTH : ∀ (ξ : Euclid (n + k)) (r : ℝ) (S : Submodule ℝ (Euclid (n + k))), 0 < r →
      closedBall ξ r ⊆ W → Module.finrank ℝ S = n →
      ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k),
        ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤
        ENNReal.ofReal CT * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r,
          ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure +
          ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r)))
    (hHA' : ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w →
      ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n →
      (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
        |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) →
      ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ CH ∧
        |a| ≤ CH * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) +
          CH * Real.sqrt ε' * R₀ ∧
        ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤
          CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2))
    (hσ : 0 < σ) (hBW : closedBall ξ σ ⊆ W)
    (hμ : ∀ y ∈ closedBall ξ σ, ∀ t : ℝ, 0 < t → t ≤ σ →
      R.measure (closedBall y t) ≤ ENNReal.ofReal (2 * ω * t ^ n))
    (hmult : ∀ᵐ x ∂R.measure, x ∈ closedBall ξ σ → R.mult x = 1)
    (hT'n : Module.finrank ℝ T' = n)
    (hT'h : ∀ x ∈ R.measure.support ∩ closedBall ξ σ,
      ‖(x - ξ) - T'.starProjection (x - ξ)‖ ≤ C₁₁ * D * σ)
    (hItilt : ∫⁻ x in closedBall ξ (σ / 4), ENNReal.ofReal (∑ i : Fin (n + k),
      ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T'.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal I)
    (hιι' : ∀ v w, inner ℝ (ι v) (ι' w) = 0) (hιT : ∀ v, ι v ∈ T')
    (hfL : ∀ v w, ‖f v - f w‖ ≤ 1 * ‖v - w‖) (hfb : ∀ v, ‖f v‖ ≤ C₇ * D * σ)
    (h5A : R.measure (closedBall ξ (σ / 2) \ range (fun v => ξ + ι v + ι' (f v))) +
      μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ (σ / 4)) ≤
        ENNReal.ofReal (C₇ * I))
    (hωeq : unitBallVolume n = ENNReal.ofReal ω)
    (hC₃ : 1 ≤ C₃) (hC₇ : 0 < C₇) (hC₁₁ : 0 < C₁₁) (hCT : 0 < CT) (hCH : 0 < CH) (hω : 0 < ω)
    (hC₁₃def : C₁₃ = (2 + C₇) * 8 ^ n)
    (hC₁₄def : C₁₄ = 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ +
      2 * ω / 4 ^ (n + 1)) / Real.sqrt ((2 + C₇) * 8 ^ n))
    (hC₁₅def : C₁₅ = (k + 1) * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)))
    (hC₁₇def : C₁₇ = 8 * C₁₁ + C₁₅ + k * CH * Real.sqrt (C₁₃ * C₃))
    (hC₁₆def : C₁₆ = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ +
      C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω))
    (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4) (hθ'C : θ' * C₁₆ ≤ 1 / 128) (hε' : 0 < ε')
    (hε'1 : ε' ≤ 1) (hε'C : ε' * C₁₆ ≤ θ' ^ (n + 3) / 128)
    (hD : 0 < D) (hD1 : D ≤ 1) (hD7 : D * C₇ ≤ 1 / 16) (hD11 : D * C₁₁ ≤ 1 / 16)
    (hD14 : D * C₁₄ ≤ δh) (hD15 : D * C₁₅ ≤ θ' / 4) (hD16a : D * C₁₆ ≤ θ' ^ (n + 3) / 128)
    (hD16b : D * C₁₆ ≤ θ' / 128) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hI0 : 0 ≤ I) (hE₀p : 0 < E₀) (hIE : I ≤ σ ^ n * E₀) (hκE : κ ^ 2 * σ ^ 2 ≤ δ * E₀)
    (hE₀le : E₀ ≤ C₃ * D ^ 2) (hκσE : κ * σ ≤ D * Real.sqrt E₀) :
    ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧
      ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * ∫⁻ x in closedBall ξ (θ' / 32 * σ),
        ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
          (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
          ∂R.measure ≤ ENNReal.ofReal (θ' / 32 * E₀) := by
  have hC₁₃ : 0 < C₁₃ := by rw [hC₁₃def]; positivity
  have hC₁₆ : 0 < C₁₆ := by rw [hC₁₆def]; positivity
  have hE₀0 : 0 ≤ E₀ := hE₀p.le
  have hAESM := Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R
  have hnull := Submission.dorag_support_sdiff_carrier_null n k hn U W R H κ hW hWU hH hHκ hMC
  have hf1 : ∀ v w, ‖f v - f w‖ ≤ ‖v - w‖ := fun v w => by simpa using hfL v w
  have hfLip : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun v w => by
    simpa [dist_eq_norm] using hfL v w
  /- Steps 3–6: energy bound and weak harmonic equation for `fʲ` on `Bⁿ_{σ/8}`. -/
  have hGT := Submission.dorag_tesDecay_ae_of_carrier R hW.measurableSet
    (Submission.dorag_lipschitz_graph_approxTangent n k hn U W R ι ι' ξ f 1 hW hWU hιι' hfLip)
  have hσ4 : σ / 4 ≤ σ := by linarith only [hσ]
  have hsmall : ∀ C : ℝ, D * C ≤ 1 / 16 → C * D * σ ≤ σ / 4 / 4 := fun C hC => by
    calc C * D * σ = (D * C) * σ := by ring
      _ ≤ 1 / 16 * σ := by gcongr
      _ = σ / 4 / 4 := by ring
  have hμσ4 : R.measure (closedBall ξ (σ / 4)) ≤ ENNReal.ofReal (2 * ω * (σ / 4) ^ n) :=
    hμ ξ (mem_closedBall_self hσ.le) (σ / 4) (by positivity) hσ4
  obtain ⟨hGE, hGW⟩ := Submission.dorag_tes_graph_weak_harmonic n k hn U W R H κ ξ (σ / 4) I (C₇ * I)
    (2 * ω * (σ / 4) ^ n) T' ι ι' f hW hWU hH hHκ hMC hAESM (by positivity)
    ((closedBall_subset_closedBall hσ4).trans hBW) hI0 (by positivity) (by positivity) hT'n hιι' hιT
    hf1 (fun v => (hfb v).trans (hsmall C₇ hD7))
    (fun x hx => (hT'h x ⟨hx.1, closedBall_subset_closedBall hσ4 hx.2⟩).trans (hsmall C₁₁ hD11))
    (by
      filter_upwards [hGT] with x hx hxB using hx (hBW (closedBall_subset_closedBall hσ4 hxB)))
    (by filter_upwards [hmult] with x hx hxB using hx (closedBall_subset_closedBall hσ4 hxB))
    hnull hItilt
    ((add_le_add (measure_mono (sdiff_subset_sdiff_left (closedBall_subset_closedBall
      (by linarith only [hσ] : σ / 4 ≤ σ / 2)))) le_rfl).trans h5A)
    hμσ4
  /- Step 7: harmonic approximation of `w = s⁻¹fʲ`, `s = (C₁₃E₀)^{1/2}`, on `Bⁿ_{R₀}`, `R₀ = σ/8`. -/
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (C₁₃ * E₀) := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ Real.sqrt_pos.mpr (mul_pos hC₁₃ hE₀p)
  have hs2 : s ^ 2 = C₁₃ * E₀ := by rw [hsdef, Real.sq_sqrt (by positivity)]
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hR₀ : 0 < σ / 4 / 2 := by positivity
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = θ' * (σ / 4 / 2) := ⟨_, rfl⟩
  have ht : 0 < t := htdef ▸ mul_pos hθ' hR₀
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = CH * (s⁻¹ * (C₇ * D * σ) * Real.sqrt ω) + CH * Real.sqrt ε' * (σ / 4 / 2) := ⟨_, rfl⟩
  have hvol : volume.real (ball (0 : Euclid n) (σ / 4 / 2)) = (σ / 4 / 2) ^ n * ω := by
    rw [Measure.real, Measure.addHaar_ball_of_pos volume 0 hR₀, finrank_euclideanSpace_fin]
    change (ENNReal.ofReal ((σ / 4 / 2) ^ n) * unitBallVolume n).toReal = _
    rw [hωeq, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hwj := Submission.dorag_tesDecay_harmonic_step n k f C₃ C₇ CH ω D δh ε' E₀ I κ σ s θ' hHA'
    hGE hGW hf1 hfb (by rw [hsdef, hC₁₃def]) hC₃ hC₇ hCH hω hD.le hE₀p hσ hθ' hθ'4 hIE hE₀le hκσE
    (by rw [← hC₁₄def, mul_comm]; exact hD14) hvol
  clear hHA' hGE hGW
  rw [← hAdef, ← htdef] at hwj
  /- Step 8: the affine map `c + Λ`. -/
  obtain ⟨c, Λ, hc, hΛ, hfcΛ⟩ := Submission.dorag_tes_componentwise_affine_assembly n k f s A CH
    (CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2)) t hfLip.continuous hs hwj
  obtain ⟨hc', hΛ'⟩ := Submission.dorag_tesDecay_affine_consts k C₃ C₁₃ C₇ CH ω D E₀ ε' σ s A ‖c‖ ‖Λ‖
    hsdef hE₀p hE₀le (by linarith only [hC₃]) hC₁₃ hD.le hε'1 hCH hC₇ hω hσ hAdef hc hΛ
  rw [← hC₁₅def] at hc'
  /- Step 9: height about `S = graph Λ` at `τ = ξ + ι'c`, then tilt via the tilt-height estimate. -/
  have hcR : ‖c‖ ≤ t / 4 := by
    calc ‖c‖ ≤ C₁₅ * D * (σ / 4 / 2) := hc'
      _ = (D * C₁₅) * (σ / 4 / 2) := by ring
      _ ≤ θ' / 4 * (σ / 4 / 2) := by gcongr
      _ = t / 4 := by rw [htdef]; ring
  have hτξ : dist (ξ + ι' c) ξ = ‖c‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, LinearIsometry.norm_map]
  have htσ : t ≤ σ / 32 := by
    calc t = θ' * (σ / 4 / 2) := htdef
      _ ≤ 1 / 4 * (σ / 4 / 2) := by gcongr
      _ = σ / 32 := by ring
  have hBt2 : closedBall (ξ + ι' c) t ⊆ closedBall ξ (σ / 2) :=
    closedBall_subset_closedBall' (by rw [hτξ]; linarith only [hcR, htσ, ht, hσ])
  have hBtσ : closedBall (ξ + ι' c) t ⊆ closedBall ξ σ :=
    hBt2.trans (closedBall_subset_closedBall (by linarith only [hσ]))
  obtain ⟨hSn, hSh⟩ := Submission.dorag_tes_graph_affine_height n k hn U R ξ T' ι ι' f c Λ t
    (C₁₁ * D * σ) ht (by positivity) hT'n hιι' hιT hf1
    (by filter_upwards [hmult] with x hx hxB using hx (hBtσ hxB))
    (fun x hx => hT'h x ⟨hx.1, hBtσ hx.2⟩)
  have hTHS := hTH (ξ + ι' c) t _ ht (hBtσ.trans hBW) hSn
  have hμt : R.measure (closedBall (ξ + ι' c) t) ≤ ENNReal.ofReal (2 * ω * t ^ n) :=
    hμ (ξ + ι' c) (hBtσ (mem_closedBall_self ht.le)) t ht (htσ.trans (by linarith only [hσ]))
  have hμtF : R.measure (closedBall (ξ + ι' c) t \ range fun v => ξ + ι v + ι' (f v)) ≤
      ENNReal.ofReal (C₇ * I) :=
    (measure_mono (sdiff_subset_sdiff_left hBt2)).trans (le_self_add.trans h5A)
  have hθσ : θ' / 32 * σ = t / 4 := by rw [htdef]; ring
  have hBsub : closedBall ξ (θ' / 32 * σ) ⊆ closedBall (ξ + ι' c) (t / 2) :=
    closedBall_subset_closedBall' (by rw [hθσ, dist_comm, hτξ]; linarith only [hcR])
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = C₁₁ * D * σ + ‖c‖ + ‖Λ‖ * t := ⟨_, rfl⟩
  rw [← hKdef] at hSh
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hKle : K ≤ C₁₇ * D * (σ / 4 / 2) := by
    have htR : t ≤ σ / 4 / 2 := by
      rw [htdef]
      exact mul_le_of_le_one_left hR₀.le (by linarith only [hθ'4])
    calc K = C₁₁ * D * σ + ‖c‖ + ‖Λ‖ * t := hKdef
      _ ≤ C₁₁ * D * σ + C₁₅ * D * (σ / 4 / 2) +
          (k * CH * Real.sqrt (C₁₃ * C₃) * D) * (σ / 4 / 2) := by gcongr
      _ = C₁₇ * D * (σ / 4 / 2) := by rw [hC₁₇def]; ring
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2) := ⟨_, rfl⟩
  rw [← hQdef] at hfcΛ
  refine ⟨_, hSn, ?_⟩
  -- Step 10: the choice of `θ'`, `ε'` and `δ₂`
  have hc1 : C₁₆ * θ' ^ 2 ≤ θ' / 128 := by
    calc C₁₆ * θ' ^ 2 = (θ' * C₁₆) * θ' := by ring
      _ ≤ 1 / 128 * θ' := by gcongr
      _ = θ' / 128 := by ring
  have hc2 : C₁₆ * (ε' / θ' ^ (n + 2)) ≤ θ' / 128 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    calc C₁₆ * ε' = ε' * C₁₆ := by ring
      _ ≤ θ' ^ (n + 3) / 128 := hε'C
      _ = θ' / 128 * θ' ^ (n + 2) := by ring
  have hc3 : C₁₆ * (D ^ 2 / θ' ^ (n + 2)) ≤ θ' / 128 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    calc C₁₆ * D ^ 2 = (D * C₁₆) * D := by ring
      _ ≤ θ' ^ (n + 3) / 128 * 1 := by gcongr
      _ = θ' / 128 * θ' ^ (n + 2) := by ring
  have hc4 : C₁₆ * δ ≤ θ' / 128 := by
    calc C₁₆ * δ ≤ C₁₆ * D := by gcongr
      _ = D * C₁₆ := by ring
      _ ≤ θ' / 128 := hD16b
  exact Submission.dorag_tesDecay_conclude n k _ _ _ _ _ CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ' ε' D δ E₀ I s Q K σ
    (σ / 4 / 2) t κ ((lintegral_mono_set hBsub).trans hTHS) hSh hfcΛ hμtF hμt hCT hCH hC₇ hC₁₃ hω
    hθ' hθ'4 hε'.le hδ.le hE₀0 hR₀ (by ring) htdef hs2 hQdef hK0 hKle hI0 hIE hκE hC₁₆def hc1 hc2 hc3
    hc4

/-- **Tilt-excess decay, one step** (Simon Ch. 5, Theorem 4.5 with `p = 2n`, bounded `H`; parent
proof Part 7, Claim 7A, Steps 0–11).  There are `θ₀ ∈ (0, 1/4]` and `δ₂ ∈ (0, 1/8]` such that under
(SA_δ), `δ ≤ δ₂`, for every `ξ ∈ spt μ ∩ B_{δρ}(z)`, `σ ∈ (0, δρ]` and `n`-plane `T` there is an
`n`-plane `S` with `E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T)`.
Step 1 replaces `T` by a plane `T'` with `E(ξ, σ, T') ≤ C₃δ^{2α}` and height `≤ C₁₁δ^ασ`
(affine approximation and plane reduction).  Step 2 is the Lipschitz approximation `f` over `T'`;
Steps 3–6 give the energy bound and the weak harmonic equation for `fʲ` on `Bⁿ_{σ/8}`; Step 7 is
the harmonic approximation of `(C₁₃E₀)^{-1/2}fʲ`; Step 8 assembles the affine map `c + Λ`; Step 9
bounds the height about `S = graph Λ` at `τ = ξ + ι'c` and converts it to tilt; Step 10 fixes
`θ' = 32θ₀`, `ε'` and `δ₂` in this order. -/
theorem Submission.dorag_tilt_excess_one_step_decay : ∀ (n k : ℕ), 0 < n → ∃ θ₀ δ₂ : ℝ, 0 < θ₀ ∧ θ₀ ≤ 1 / 4 ∧ 0 < δ₂ ∧ δ₂ ≤ 1 / 8 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ : ℝ) (T : Submodule ℝ (Euclid (n + k))), 0 < σ → σ ≤ δ * ρ → Module.finrank ℝ T = n → ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ max (ENNReal.ofReal (1 / (θ₀ * σ) ^ n) * ∫⁻ x in closedBall ξ (θ₀ * σ), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * (θ₀ * σ) ^ 2 / δ)) ≤ ENNReal.ofReal θ₀ * max (ENNReal.ofReal (1 / σ ^ n) * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * σ ^ 2 / δ)) := by
  intro n k hn
  /- Step 0: the constants.  Sibling constants first. -/
  obtain ⟨δ₁, C₂, hδ₁, hδ₁8, -, hDB⟩ := Submission.dorag_standing_density_bounds n k hn
  obtain ⟨δ₃, C₃, hδ₃, hδ₃8, hC₃, hAA⟩ := Submission.dorag_affine_approximation n k hn
  obtain ⟨CT, hCT, hTH⟩ := Submission.dorag_tilt_height_estimate n k
  obtain ⟨CH, hCH, hHA⟩ := Submission.dorag_harmonic_affine_approximation n hn
  -- `ω = ω_n ∈ (0, ∞)`
  have hωfin : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ ENNReal.toReal_pos hω0 hωfin
  have hωeq : unitBallVolume n = ENNReal.ofReal ω := by rw [hωdef, ENNReal.ofReal_toReal hωfin]
  have h2ω : ∀ x : ℝ, 0 ≤ x → 2 * unitBallVolume n * ENNReal.ofReal x = ENNReal.ofReal (2 * ω * x) := by
    intro x hx
    rw [hωeq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- `C₁₁ = 2C₃ + (8C₃/ω)^{1/2}` and the Lipschitz approximation constants for `C₆ = C₁₁`
  obtain ⟨C₁₁, hC₁₁def⟩ : ∃ C : ℝ, C = 2 * C₃ + Real.sqrt (8 * C₃ / ω) := ⟨_, rfl⟩
  have hC₃C₁₁ : C₃ ≤ C₁₁ := by
    rw [hC₁₁def]
    have := Real.sqrt_nonneg (8 * C₃ / ω)
    linarith only [this, hC₃]
  have hC₁₁ : 1 ≤ C₁₁ := hC₃.trans hC₃C₁₁
  have hC₁₁0 : 0 < C₁₁ := by linarith only [hC₁₁]
  obtain ⟨δ₅, β, β', C₇, hδ₅, -, hβ', hβ'β, -, hC₇, hLA⟩ :=
    Submission.dorag_lipschitz_approximation n k hn C₁₁ hC₁₁
  have hβ : 0 < β := hβ'.trans_le hβ'β
  -- `C₁₃, …, C₁₆` (Steps 6–9)
  obtain ⟨C₁₃, hC₁₃def⟩ : ∃ C : ℝ, C = (2 + C₇) * 8 ^ n := ⟨_, rfl⟩
  obtain ⟨C₁₄, hC₁₄def⟩ : ∃ C : ℝ, C = 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ +
      2 * ω / 4 ^ (n + 1)) / Real.sqrt ((2 + C₇) * 8 ^ n) := ⟨_, rfl⟩
  obtain ⟨C₁₅, hC₁₅def⟩ : ∃ C : ℝ,
      C = (k + 1) * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)) := ⟨_, rfl⟩
  obtain ⟨C₁₇, hC₁₇def⟩ : ∃ C : ℝ, C = 8 * C₁₁ + C₁₅ + k * CH * Real.sqrt (C₁₃ * C₃) := ⟨_, rfl⟩
  obtain ⟨C₁₆, hC₁₆def⟩ : ∃ C : ℝ, C = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ +
      C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω) := ⟨_, rfl⟩
  have hC₁₃ : 0 < C₁₃ := by rw [hC₁₃def]; positivity
  have hC₁₄ : 0 < C₁₄ := by rw [hC₁₄def]; positivity
  have hC₁₅ : 0 < C₁₅ := by rw [hC₁₅def]; positivity
  have hC₁₆ : 0 < C₁₆ := by rw [hC₁₆def]; positivity
  -- Step 10: `θ'` with `C₁₆θ'² ≤ θ'/128`, then `ε'` with `C₁₆θ'^{-n-2}ε' ≤ θ'/128`
  obtain ⟨θ', hθ'def⟩ : ∃ θ : ℝ, θ = min (1 / 4) (1 / 128 / C₁₆) := ⟨_, rfl⟩
  have hθ' : 0 < θ' := by rw [hθ'def]; positivity
  have hθ'4 : θ' ≤ 1 / 4 := hθ'def ▸ min_le_left _ _
  have hθ'C : θ' * C₁₆ ≤ 1 / 128 :=
    (le_div_iff₀ hC₁₆).mp (hθ'def ▸ min_le_right _ _)
  obtain ⟨ε', hε'def⟩ : ∃ ε : ℝ, ε = min 1 (θ' ^ (n + 3) / 128 / C₁₆) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by rw [hε'def]; positivity
  have hε'1 : ε' ≤ 1 := hε'def ▸ min_le_left _ _
  have hε'C : ε' * C₁₆ ≤ θ' ^ (n + 3) / 128 :=
    (le_div_iff₀ hC₁₆).mp (hε'def ▸ min_le_right _ _)
  obtain ⟨δh, hδh, hHA'⟩ := hHA ε' hε'
  -- the smallness threshold for `D = δ^{1/(2n+2)}`, and `δ₂`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (min (min β (1 / 16 / C₁₁)) (min (1 / 16 / C₇) (δh / C₁₄)))
      (min (min (θ' / 4 / C₁₅) (θ' ^ (n + 3) / 128 / C₁₆)) (min (θ' / 128 / C₁₆) 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηs : η ≤ β ∧ η ≤ 1 / 16 / C₁₁ ∧ η ≤ 1 / 16 / C₇ ∧ η ≤ δh / C₁₄ ∧ η ≤ θ' / 4 / C₁₅ ∧
      η ≤ θ' ^ (n + 3) / 128 / C₁₆ ∧ η ≤ θ' / 128 / C₁₆ ∧ η ≤ 1 := by
    rw [hηdef]
    simp only [min_le_iff, le_refl, true_or, or_true, and_self]
  obtain ⟨hηβ, hη11, hη7, hη14, hη15, hη16a, hη16b, hη1⟩ := hηs
  obtain ⟨δ₂, hδ₂def⟩ : ∃ d : ℝ, d = min (min (min (min (1 / 8) δ₁) δ₃) δ₅) (η ^ (2 * n + 2)) :=
    ⟨_, rfl⟩
  have hδ₂ : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hδ₂8 : δ₂ ≤ 1 / 8 := by
    rw [hδ₂def]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_left _ _)))
  refine ⟨θ' / 32, δ₂, by positivity, by linarith only [hθ'4], hδ₂, hδ₂8, ?_⟩
  intro δ hδ hδδ₂ U W R H κ ρ z hW hWU hρ hzρ hH hHκ hMC hz hdens hκρ ξ hξ σ T hσ hσδρ hT
  have hδs : δ ≤ 1 / 8 ∧ δ ≤ δ₁ ∧ δ ≤ δ₃ ∧ δ ≤ δ₅ ∧ δ ≤ η ^ (2 * n + 2) := by
    rw [hδ₂def] at hδδ₂
    simp only [le_min_iff] at hδδ₂
    tauto
  obtain ⟨hδ8, hδ₁', hδ₃', hδ₅', hδη⟩ := hδs
  -- `D = δ^α`, `α = 1/(2n+2)`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) := ⟨_, rfl⟩
  obtain ⟨hD, hDη, hδD, hsδD⟩ :=
    Submission.dorag_tesDecay_rpow n δ η hδ (by linarith only [hδ8]) hη hδη
  rw [← hDdef] at hD hDη hδD hsδD
  have hDβ : D ≤ β := hDη.trans hηβ
  have hD11 : D * C₁₁ ≤ 1 / 16 := (le_div_iff₀ hC₁₁0).mp (hDη.trans hη11)
  have hD7 : D * C₇ ≤ 1 / 16 := (le_div_iff₀ hC₇).mp (hDη.trans hη7)
  have hD14 : D * C₁₄ ≤ δh := (le_div_iff₀ hC₁₄).mp (hDη.trans hη14)
  have hD15 : D * C₁₅ ≤ θ' / 4 := (le_div_iff₀ hC₁₅).mp (hDη.trans hη15)
  have hD16a : D * C₁₆ ≤ θ' ^ (n + 3) / 128 := (le_div_iff₀ hC₁₆).mp (hDη.trans hη16a)
  have hD16b : D * C₁₆ ≤ θ' / 128 := (le_div_iff₀ hC₁₆).mp (hDη.trans hη16b)
  have hD1 : D ≤ 1 := hDη.trans hη1
  -- elementary facts about the data
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hξz : dist ξ z ≤ δ * ρ := mem_closedBall.mp hξ.2
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hδρ8 : δ * ρ ≤ ρ / 8 := by
    calc δ * ρ ≤ 1 / 8 * ρ := mul_le_mul_of_nonneg_right hδ8 hρ.le
      _ = ρ / 8 := by ring
  have hBz : closedBall ξ σ ⊆ closedBall z (4 * δ * ρ) :=
    closedBall_subset_closedBall' (by linarith only [hσδρ, hξz, hδρ])
  have hBW : closedBall ξ σ ⊆ W :=
    (closedBall_subset_closedBall' (by linarith only [hσδρ, hξz, hδρ8, hρ])).trans hzρ
  have hσρ : σ ≤ (1 - 4 * δ) * ρ := by linarith only [hσδρ, hδρ8, hρ]
  obtain ⟨hDBa, hDBb, -, hDBd⟩ :=
    hDB δ hδ hδ₁' U W R H κ ρ z hW hWU hρ hzρ hH hHκ hMC hz hdens hκρ
  clear hDB
  have hAESM := Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R
  /- Step 1: affine approximation at `(ξ, 2σ)` and reduction to a plane `T'` with small tilt and
  height. -/
  obtain ⟨T₁, hT₁n, hT₁h, hT₁t⟩ := hAA δ hδ hδ₃' U W R H κ ρ z hW hWU hρ hzρ hH hHκ hMC hz hdens hκρ ξ
    ⟨hξ.1, mem_closedBall.mpr (by linarith only [hξz, hδρ])⟩ (2 * σ) (by linarith only [hσ])
    (by linarith only [hσδρ])
  clear hAA
  rw [← hDdef] at hT₁h hT₁t
  rw [show 2 * σ / 2 = σ by ring] at hT₁t
  have hμσ : ENNReal.ofReal (ω * σ ^ n / 2) ≤ R.measure (closedBall ξ σ) := by
    have h := hDBb ξ ⟨hξ.1, hBz (mem_closedBall_self hσ.le)⟩ σ hσ hσρ
    rw [hωeq, ← ENNReal.ofReal_mul hω.le] at h
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul (h.trans_eq (mul_comm _ _))
  obtain ⟨T', hT'TT, hT'a, hT'T, hT'h⟩ := Submission.dorag_tes_plane_reduction (n + k) R.measure
    (approxTangentPlane n R.carrier) ξ σ (C₃ * D ^ 2 * σ ^ n) (ω * σ ^ n / 2) (C₃ * D * (2 * σ)) T T₁
    hσ (by positivity) (by positivity) hAESM hμσ hT₁t
    (fun x hx => hT₁h x ⟨hx.1, closedBall_subset_closedBall (by linarith only [hσ]) hx.2⟩)
  rw [Submission.dorag_tesDecay_height_const n C₃ ω D σ (by linarith only [hC₃]) hω hD.le hσ,
    ← hC₁₁def]
    at hT'h
  have hT'n : Module.finrank ℝ T' = n := by
    rcases hT'TT with rfl | rfl <;> assumption
  -- `I = ∫_{B_σ(ξ)} |p_x − p_{T'}|² dμ` and `E₀ = E_*(ξ, σ, T')`
  obtain ⟨I, hI0, hIeq, hIa⟩ := Submission.dorag_tesDecay_real_of_le (by positivity) hT'a
  rw [← hIeq] at hT'T
  obtain ⟨E₀, hE₀def⟩ : ∃ E : ℝ, E = max (1 / σ ^ n * I) (κ ^ 2 * σ ^ 2 / δ) := ⟨_, rfl⟩
  obtain ⟨hE₀0, hIE, hκE, hE₀le, hκσE⟩ := Submission.dorag_tesDecay_excess_facts n C₃ D δ E₀ I κ ρ σ
    hδ hδ8 hσ hσδρ hκ hκρ hC₃ hδD hsδD hIa hE₀def
  have hE₀2 : κ ^ 2 * σ ^ 2 / δ ≤ E₀ := hE₀def ▸ le_max_right _ _
  -- it suffices to prove `E_*(ξ, θ₀σ, S) ≤ θ₀E₀`
  have hRHS := Submission.dorag_tesDecay_rhs (θ' / 32) E₀ (1 / σ ^ n) (κ ^ 2 * σ ^ 2 / δ) I _
    (by positivity) (by positivity) hE₀def hT'T
  have hθ32 : θ' / 32 ≤ 1 := by linarith only [hθ'4]
  have hsecond : ENNReal.ofReal (κ ^ 2 * (θ' / 32 * σ) ^ 2 / δ) ≤ ENNReal.ofReal (θ' / 32 * E₀) := by
    apply ENNReal.ofReal_le_ofReal
    rw [show κ ^ 2 * (θ' / 32 * σ) ^ 2 / δ = (θ' / 32) ^ 2 * (κ ^ 2 * σ ^ 2 / δ) by ring]
    calc (θ' / 32) ^ 2 * (κ ^ 2 * σ ^ 2 / δ) ≤ (θ' / 32) ^ 2 * E₀ := by gcongr
      _ ≤ θ' / 32 * E₀ := by
        gcongr
        rw [sq]
        exact mul_le_of_le_one_left (by positivity) hθ32
  rcases hE₀0.eq_or_lt with hE₀z | hE₀p
  · /- `E₀ = 0`: `S = T'` works. -/
    have hIz : I = 0 := by
      have := hIE
      rw [← hE₀z, mul_zero] at this
      exact le_antisymm this hI0
    refine ⟨T', hT'n, le_trans (max_le ?_ hsecond) hRHS⟩
    refine (mul_le_mul_right (lintegral_mono_set (closedBall_subset_closedBall
      (mul_le_of_le_one_left hσ.le hθ32))) _).trans ?_
    rw [← hIeq, hIz, ENNReal.ofReal_zero, mul_zero]
    exact zero_le
  /- `E₀ > 0`.  Step 2: Lipschitz approximation over `T'` with `L = 1`. -/
  obtain ⟨ι, ι', f, hιι', hιT, hfL, hfb, h5A, -⟩ := hLA δ hδ hδ₅' U W R H κ ρ z hW hWU hρ hzρ hH hHκ
    hMC hz hdens hκρ ξ hξ σ 1 T' hσ hσδρ hT'n one_pos le_rfl (by rw [← hDdef, mul_one]; exact hDβ)
    (by rw [← hDdef, ← hIeq]; exact ENNReal.ofReal_le_ofReal (hIa.trans (by gcongr)))
    (by rw [← hDdef]; exact hT'h)
  clear hLA
  rw [← hDdef] at hfb
  rw [one_pow, div_one, ← hIeq, ← ENNReal.ofReal_mul hC₇.le] at h5A
  /- Steps 3–9: the core estimate. -/
  obtain ⟨S, hSn, hS⟩ := Submission.dorag_tesDecay_core n k hn U W R H κ ξ σ T' ι ι' f C₃ C₇ C₁₁ C₁₃
    C₁₄ C₁₅ C₁₆ C₁₇ CT CH ω θ' ε' δh D δ E₀ I hW hWU hH hHκ hMC
    (fun ξ' r S' => hTH U W R H κ ξ' r S' hW hWU hH hHκ hMC) hHA' hσ hBW
    (fun y hy t ht htσ => (hDBa y (hBz hy) t ht (htσ.trans hσρ)).trans_eq (h2ω _ (by positivity)))
    (by filter_upwards [hDBd] with x hx hxB using hx (hBz hxB)) hT'n hT'h
    (by rw [hIeq]; exact lintegral_mono_set (closedBall_subset_closedBall (by linarith only [hσ])))
    hιι' hιT hfL hfb h5A hωeq hC₃ hC₇ hC₁₁0 hCT hCH hω hC₁₃def hC₁₄def hC₁₅def hC₁₇def hC₁₆def hθ'
    hθ'4 hθ'C hε' hε'1 hε'C hD hD1 hD7 hD11 hD14 hD15 hD16a hD16b hδ hδD hI0 hE₀p hIE hκE hE₀le hκσE
  exact ⟨S, hSn, le_trans (max_le hS hsecond) hRHS⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
