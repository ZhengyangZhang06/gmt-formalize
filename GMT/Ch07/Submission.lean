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

/-- **Smooth affine homotopy on `ℝ × ℝᴺ` and its differential** (Simon 6.2.26, and the
differential used in the proof of 6.2.27).  For smooth `F, G : ℝᴺ → ℝ^{N'}` let
`tail y = (y₁, …, y_N)` and `π₀ y = y₀` on `ℝ^{N+1}`, both continuous linear, and
`H(y) = F(tail y) + π₀(y) (G(tail y) − F(tail y))`.  Then `H` is smooth and
`H(ι(t, x)) = F(x) + t (G(x) − F(x))` for `ι(t, x) = (t, x)`.  By the chain and product rules
`DH(y)h = DF(tail y)(tail h) + π₀(y) (DG(tail y) − DF(tail y))(tail h) + π₀(h) (G − F)(tail y)`;
with `tail e₀ = 0`, `π₀ e₀ = 1`, `tail (0, v) = v` and `π₀ (0, v) = 0` this gives
`DH(ι(t, x))e₀ = G(x) − F(x)` and `DH(ι(t, x))(0, v) = DF(x)v + t (DG(x)v − DF(x)v)`. -/
theorem Submission.cmcdt_lpo_she_affine_homotopy : ∀ (N N' : ℕ) (F G : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → ∃ H : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) H ∧ (∀ (t : ℝ) (x : Euclid N), H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = G x - F x) ∧ ∀ (t : ℝ) (x v : Euclid N), fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ F x v + t • (fderiv ℝ G x v - fderiv ℝ F x v) := by
  intro N N' F G hF hG
  -- Step 1: the continuous linear coordinate maps `tail y = (y₁, …, y_N)` and `π₀ y = y₀`
  let tail : Euclid (N + 1) →L[ℝ] Euclid N := LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
      map_add' := fun y z => by ext i; simp [Fin.tail]
      map_smul' := fun c y => by ext i; simp [Fin.tail] }
  let π₀ : Euclid (N + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  -- Step 2: their values at `ι(t, x)` and at `e₀`
  have htail : ∀ (t : ℝ) (x : Euclid N), tail (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x :=
    fun t x => rfl
  have hπ : ∀ (t : ℝ) (x : Euclid N), π₀ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = t :=
    fun t x => rfl
  have htail₀ : tail (EuclideanSpace.single 0 1) = 0 := by
    ext i; simp [tail, Fin.tail, EuclideanSpace.single, Fin.succ_ne_zero]
  have hπ₀ : π₀ (EuclideanSpace.single 0 1) = 1 := by simp [π₀]
  -- Steps 3–4: `H y = F (tail y) + π₀ y • (G (tail y) - F (tail y))` is smooth
  have hFt : ContDiff ℝ (⊤ : ℕ∞) (fun y => F (tail y)) := hF.comp tail.contDiff
  have hGt : ContDiff ℝ (⊤ : ℕ∞) (fun y => G (tail y)) := hG.comp tail.contDiff
  -- Step 6: the chain and product rules give `DH(y)`
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hder : ∀ y, HasFDerivAt (fun y => F (tail y) + π₀ y • (G (tail y) - F (tail y)))
      ((fderiv ℝ F (tail y)).comp tail + (π₀ y • ((fderiv ℝ G (tail y)).comp tail -
        (fderiv ℝ F (tail y)).comp tail) + π₀.smulRight (G (tail y) - F (tail y)))) y := by
    intro y
    have h₁ : HasFDerivAt (fun y => F (tail y)) ((fderiv ℝ F (tail y)).comp tail) y :=
      (hFd (tail y)).hasFDerivAt.comp y tail.hasFDerivAt
    have h₂ : HasFDerivAt (fun y => G (tail y)) ((fderiv ℝ G (tail y)).comp tail) y :=
      (hGd (tail y)).hasFDerivAt.comp y tail.hasFDerivAt
    exact h₁.add (π₀.hasFDerivAt.fun_smul (h₂.sub h₁))
  refine ⟨fun y => F (tail y) + π₀ y • (G (tail y) - F (tail y)),
    hFt.add (π₀.contDiff.smul (hGt.sub hFt)), fun t x => ?_, fun t x => ?_, fun t x v => ?_⟩
  -- Step 5: formula (i)
  · simp only [htail, hπ]
  -- Step 7: formula (ii), from `tail e₀ = 0` and `π₀ e₀ = 1`
  · rw [(hder _).fderiv]
    simp [htail, hπ, htail₀, hπ₀]
  -- Step 8: formula (iii), from `tail (0, v) = v` and `π₀ (0, v) = 0`
  · rw [(hder _).fderiv]
    simp [htail, hπ]
/-- **Coefficient bounds for the cylinder `[[(0,1)]] × T`** (Simon 6.2.17, 6.2.25): with
`J v = ι(0, v)` the inclusion `ℝᴺ → ℝᴺ⁺¹`, `x ↦ (0, x)`, and `e₀ = EuclideanSpace.single 0 1`, the
`dt`-part `Φ γ (v₁, …, v_k) = γ(e₀, J v₁, …, J v_k)` and the spatial part
`Ψ γ (v₁, …, v_k) = γ(J v₁, …, J v_k)` of a covector `γ` on `ℝᴺ⁺¹` are continuous linear in `γ` and
do not increase the Euclidean coefficient norm.  Indeed `Φ γ = (ι_{e₀} γ) ∘ J` and `Ψ γ = γ ∘ J`, so
the pullback bound (L1) `|β ∘ A|_E ≤ ‖A‖ᵏ |β|_E` and the interior product bound (L2)
`|ι_v β|_E ≤ ‖v‖ |β|_E` apply, with `‖J‖ ≤ 1` (`J` preserves norms) and `‖e₀‖ = 1`. -/
theorem Submission.cmcdt_lpo_cyl_restriction_bounds : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ N k : ℕ, ∃ Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N), Φ γ v = γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∀ γ : Covector (Euclid (N + 1)) (k + 1), covectorEuclideanNorm (Φ γ) ≤ covectorEuclideanNorm γ) ∧ (∀ N k : ℕ, ∃ Ψ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) k) (v : Fin k → Euclid N), Ψ γ v = γ (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ γ : Covector (Euclid (N + 1)) k, covectorEuclideanNorm (Ψ γ) ≤ covectorEuclideanNorm γ) := by
  intro hL1 hL2
  -- `J v = ι(0, v)`: a continuous linear map `ℝᴺ → ℝᴺ⁺¹` with `‖J v‖ = ‖v‖`, so `‖J‖ ≤ 1`
  have hJ : ∀ N : ℕ, ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧ ‖J‖ ≤ 1 := by
    intro N
    let L : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun u v => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun a v => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    have hLv : ∀ v, LinearMap.toContinuousLinearMap L v =
        WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) := fun v => rfl
    refine ⟨LinearMap.toContinuousLinearMap L, hLv,
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_⟩
    rw [hLv, one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
    simp
  refine ⟨fun N k => ?_, fun N k => ?_⟩
  · -- `Φ γ = (ι_{e₀} γ) ∘ J`, i.e. `Φ = J^* ∘ (evaluation at e₀) ∘ curryLeft`
    obtain ⟨J, hJv, hJ1⟩ := hJ N
    refine ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k)
          (EuclideanSpace.single 0 1)).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap), fun γ v => ?_, fun γ => ?_⟩
    · simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        ContinuousAlternatingMap.curryLeftLI_apply, ContinuousLinearMap.apply_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply,
        ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 1
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      simp [hJv]
    · -- (L1) with `A = J`, then (L2) with `v = e₀`, `‖e₀‖ = 1`
      have he : ‖(EuclideanSpace.single 0 1 : Euclid (N + 1))‖ = 1 := by simp
      calc _ = covectorEuclideanNorm
              ((γ.curryLeft (EuclideanSpace.single 0 1)).compContinuousLinearMap J) := rfl
        _ ≤ ‖J‖ ^ k * covectorEuclideanNorm (γ.curryLeft (EuclideanSpace.single 0 1)) :=
          hL1 N (N + 1) k J _
        _ ≤ covectorEuclideanNorm (γ.curryLeft (EuclideanSpace.single 0 1)) :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (pow_le_one₀ (norm_nonneg J) hJ1)
        _ ≤ ‖(EuclideanSpace.single 0 1 : Euclid (N + 1))‖ * covectorEuclideanNorm γ :=
          hL2 (N + 1) k _ γ
        _ = covectorEuclideanNorm γ := by rw [he, one_mul]
  · -- `Ψ γ = γ ∘ J`, the pullback by `J`
    obtain ⟨J, hJv, hJ1⟩ := hJ N
    refine ⟨ContinuousAlternatingMap.compContinuousLinearMapCLM J, fun γ v => ?_, fun γ => ?_⟩
    · simp only [ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      congr 1
      funext i
      exact hJv (v i)
    · calc _ = covectorEuclideanNorm (γ.compContinuousLinearMap J) := rfl
        _ ≤ ‖J‖ ^ k * covectorEuclideanNorm γ := hL1 N (N + 1) k J γ
        _ ≤ covectorEuclideanNorm γ :=
          mul_le_of_le_one_left (covectorEuclideanNorm_nonneg γ) (pow_le_one₀ (norm_nonneg J) hJ1)
/-- **The slice operator `S ω = ∫₀¹ ω(ι(t, ·))(e₀, J ·) dt`** (the operator behind the cylinder
`[[(0, 1)]] × X` of Simon Ch. 6, 2.18–2.21 and the homotopy formula 2.25, as used for the
Lipschitz push-forward in the deformation theorem).  Choose for every `ω` the slice `η ω` given by
(SA).  Since `t ↦ ω(ι(t, x))` is continuous, every evaluated integrand is interval integrable, and
a test form with the slice formula of `ω` equals `η ω` (`ContinuousAlternatingMap.ext`,
`Subtype.ext`); linearity of the interval integral then makes `S = η` additive and homogeneous.
(i) and (ii) are the chosen properties of `η ω`, and (iii) is (SE) for the continuous
`f t = Φ (ω (ι(t, x)))`, `Φ` from (R1), whose bound `|Φ γ| ≤ |γ|` gives `|f t| ≤ c`. -/
theorem Submission.cmcdt_lpo_cyl_slice_operator : (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) → (∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c) → (∀ N k : ℕ, ∃ Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N), Φ γ v = γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∀ γ : Covector (Euclid (N + 1)) (k + 1), covectorEuclideanNorm (Φ γ) ≤ covectorEuclideanNorm γ) → ∀ N k : ℕ, ∃ S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] TestFormOn (univ : Set (Euclid N)) k, (∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N) (v : Fin k → Euclid N), (S ω : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), tsupport (S ω : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S ω : DifferentialForm (Euclid N) k) x) ≤ c := by
  intro hSA hSE hR1 N k
  -- Step 2: choose a slice `η ω` for every `ω`, with the formula (i) and the support bound (ii)
  choose η hηf hηs using hSA N k
  -- Step 1: `t ↦ ω(ι(t, x))` is continuous, so every evaluated integrand is interval integrable
  have hcont : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N),
      Continuous fun t : ℝ => (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) := by
    intro ω x
    have hι : Continuous fun t : ℝ =>
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) := by
      fun_prop
    exact ω.property.1.1.continuous.comp hι
  have hint : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (x : Euclid N)
      (w : Fin (k + 1) → Euclid (N + 1)),
      IntervalIntegrable (fun t : ℝ => (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) w) volume 0 1 :=
    fun ω x w => ((continuous_eval_const w).comp (hcont ω x)).intervalIntegrable 0 1
  -- Step 3: a test form satisfying the slice formula of `ω` is `η ω`
  have huniq : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
      (θ : TestFormOn (univ : Set (Euclid N)) k),
      (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v =
        ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
          (Fin.cons (EuclideanSpace.single 0 1)
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → θ = η ω := by
    intro ω θ hθ
    refine Subtype.ext (funext fun x => ContinuousAlternatingMap.ext fun v => ?_)
    rw [hθ, hηf]
  -- Step 4: `S ω := η ω` is additive and homogeneous
  have hadd : ∀ ω₁ ω₂ : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1),
      η (ω₁ + ω₂) = η ω₁ + η ω₂ := by
    intro ω₁ ω₂
    refine (huniq (ω₁ + ω₂) (η ω₁ + η ω₂) fun x v => ?_).symm
    simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
    rw [hηf, hηf, ← intervalIntegral.integral_add (hint _ _ _) (hint _ _ _)]
  have hsmul : ∀ (a : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)),
      η (a • ω) = a • η ω := by
    intro a ω
    refine (huniq (a • ω) (a • η ω) fun x v => ?_).symm
    simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [hηf, ← intervalIntegral.integral_const_mul]
  refine ⟨{ toFun := η, map_add' := hadd, map_smul' := hsmul }, fun ω x v => hηf ω x v,
    fun ω => hηs ω, fun ω c hc x => ?_⟩
  -- Step 6: (iii) from (SE) applied to `f t = Φ (ω (ι(t, x)))`
  obtain ⟨Φ, hΦ, hΦb⟩ := hR1 N k
  refine hSE N k _ (fun t => Φ ((ω : DifferentialForm (Euclid (N + 1)) (k + 1))
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) c (Φ.continuous.comp (hcont ω x))
      (fun v => ?_) fun t _ => (hΦb _).trans (hc _)
  change (η ω : DifferentialForm (Euclid N) k) x v = _
  rw [hηf]
  simp only [hΦ]
/-- **Simon 6.2.17, 2.20** (the cylinder `[[(0, 1)]] × X` as `X ∘ S`): given the mass bound (MSB)
`|X(ψ)| ≤ c M(X)` for `|ψ| ≤ c` on `spt X` and the bounded-current constructor (BC), a linear
`S : 𝒟^{k+1}(ℝ^{N+1}) → 𝒟^k(ℝ^N)` with `|S ω| ≤ c` whenever `|ω| ≤ c` induces
`cyl : 𝒟_k(ℝ^N) → 𝒟_{k+1}(ℝ^{N+1})` with `cyl X = X ∘ S` and `M(cyl X) ≤ M(X)` if `M(X) < ∞`,
and `cyl (X − Y) = cyl X − cyl Y` if `M(X), M(Y) < ∞`.  (MSB) bounds `X ∘ S` by `M(X)` and (BC)
realizes it as a current; `M(X − Y) < ∞` by (MSB) with `c = 1`. -/
theorem Submission.cmcdt_lpo_cyl_current : (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) → (∀ (N k : ℕ) (T₀ : TestFormOn (univ : Set (Euclid N)) k →ₗ[ℝ] ℝ) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T₀ ω| ≤ C * c) → ∃ T : GeometricCurrentOn (univ : Set (Euclid N)) k, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal C) → ∀ (N k : ℕ) (S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] TestFormOn (univ : Set (Euclid N)) k), (∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S ω : DifferentialForm (Euclid N) k) x) ≤ c) → ∃ cyl : GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1), (∀ X : GeometricCurrentOn (univ : Set (Euclid N)) k, X.mass < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), cyl X ω = X (S ω)) ∧ (cyl X).mass ≤ X.mass) ∧ ∀ X Y : GeometricCurrentOn (univ : Set (Euclid N)) k, X.mass < ∞ → Y.mass < ∞ → cyl (X - Y) = cyl X - cyl Y := by
  intro hMSB hBC N k S hS
  -- `X ∘ S` is a current of mass `≤ M(X)` when `M(X) < ∞`
  have hT : ∀ X : GeometricCurrentOn (univ : Set (Euclid N)) k, X.mass < ∞ →
      ∃ T : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1),
        (∀ ω, T ω = X (S ω)) ∧ T.mass ≤ X.mass := by
    intro X hX
    obtain ⟨T, hTω, hTM⟩ := hBC (N + 1) (k + 1) (X.toCurrent ∘ₗ S) X.mass.toReal
      fun ω c hω => (hMSB N k X (S ω) c hX fun x _ => hS ω c hω x).trans_eq (mul_comm _ _)
    exact ⟨T, hTω, by rwa [ENNReal.ofReal_toReal hX.ne] at hTM⟩
  choose! cyl hcylω hcylM using hT
  refine ⟨cyl, fun X hX => ⟨hcylω X hX, hcylM X hX⟩, fun X Y hX hY => ?_⟩
  -- `M(X − Y) ≤ M(X) + M(Y) < ∞`, by (MSB) with `c = 1` on each admissible form
  have hXY : (X - Y).mass < ∞ := by
    refine lt_of_le_of_lt (sSup_le ?_) (ENNReal.ofReal_lt_top (r := X.mass.toReal + Y.mass.toReal))
    rintro _ ⟨ω, hω, rfl⟩
    have h1 := hMSB N k X ω 1 hX fun x _ => hω.2 x
    have h2 := hMSB N k Y ω 1 hY fun x _ => hω.2 x
    rw [one_mul] at h1 h2
    apply ENNReal.ofReal_le_ofReal
    show X ω - Y ω ≤ _
    linarith [le_abs_self (X ω), neg_abs_le (Y ω)]
  ext ω
  rw [hcylω _ hXY]
  show X (S ω) - Y (S ω) = cyl X ω - cyl Y ω
  rw [hcylω X hX, hcylω Y hY]
/-- The support of `Z = X ∘ S` lies in the cylinder `C = ι([0, 1] × spt X)`, `ι(t, x) = (t, x)`,
and is compact (step 7 of the cylinder construction, Simon 6.2.17–2.21).  `C` is the continuous
image of the compact `[0, 1] × spt X`, hence compact and closed.  For `y ∉ C` pick
`B(y, r) ⊆ Cᶜ`; it is open with compact closure, and if `tsupport ω ⊆ B(y, r)` then
`tsupport S(ω)` misses `spt X` (a point `x` of both gives `ι(t, x) ∈ tsupport ω ∩ C`), so (VO)
gives `Z(ω) = X(S(ω)) = 0`.  Hence `y` lies in the zero region of `Z`, i.e. `spt Z ⊆ C`, and
`spt Z = (zero region)ᶜ` is closed, so compact. -/
theorem Submission.cmcdt_lpo_cyl_support : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (Z : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (S : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) → TestFormOn (univ : Set (Euclid N)) k), IsCompact X.support → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), tsupport (S ω : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), Z ω = X (S ω)) → IsCompact Z.support ∧ Z.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
  intro hVO N k X Z S hXc hS hZ
  set C : Set (Euclid (N + 1)) := {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
    y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}
  -- `C = ι([0, 1] × spt X)` is compact
  have hCc : IsCompact C := by
    have hCι : C = (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
          (Icc (0 : ℝ) 1 ×ˢ X.support) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [hCι]
    exact (isCompact_Icc.prod hXc).image (by fun_prop)
  -- `spt Z ⊆ C`: a ball `B(y, r) ⊆ Cᶜ` lies in the zero region of `Z`
  have hsub : Z.support ⊆ C := by
    intro y hy
    by_contra hyC
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hCc.isClosed.isOpen_compl y hyC
    refine hy.2 (Set.mem_sUnion.mpr ⟨ball y r, ⟨isOpen_ball, ?_, subset_univ _, ?_⟩,
      mem_ball_self hr⟩)
    · exact (isCompact_closedBall y r).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · intro ω hω
      rw [hZ ω]
      refine hVO N k univ X (S ω) (Set.disjoint_left.mpr fun x hx hxX => ?_)
      obtain ⟨t, ht, hmem⟩ := hS ω hx
      exact hball (hω hmem) ⟨t, ht, x, hxX, rfl⟩
  -- `spt Z = (zero region)ᶜ` is closed, so compact
  exact ⟨hCc.of_isClosed_subset (isClosed_univ.sdiff Z.isOpen_zeroRegion) hsub, hsub⟩
/-- **Simon 6.2.21** (mass form): `Z = [[(0, 1)]] × X` acts by `Z(ω) = X(S_k ω)`, where
`S_m ω(x) = ∫₀¹ ω(t, x)(e₀, ·) dt` integrates out the first coordinate of `ℝ^{N+1} = ℝ × ℝᴺ`.
If `M(X) < ∞` and `M(∂X) < ∞` then `M(∂Z) < ∞`.  For admissible `ω`, `∂Z(ω) = X(S_k dω)`, and the
slice identities give `S_k dω = ρ₁ − ρ₀ − dθ`, where `ρ_s` is the slice of `ω` at height `s`
and `θ = S_{k−1} ω` (no `dθ` term for `k = 0`).  So `∂Z(ω) ≤ 2 M(X) + M(∂X)`. -/
theorem Submission.cmcdt_lpo_cyl_boundary_mass : (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) → (∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v) → (∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ N k : ℕ, ∃ Ψ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k, (∀ (γ : Covector (Euclid (N + 1)) k) (v : Fin k → Euclid N), Ψ γ v = γ (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ γ : Covector (Euclid (N + 1)) k, covectorEuclideanNorm (Ψ γ) ≤ covectorEuclideanNorm γ) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (Z : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)) (S : ∀ m : ℕ, TestFormOn (univ : Set (Euclid (N + 1))) (m + 1) → TestFormOn (univ : Set (Euclid N)) m), X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ (m : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (m + 1)) (x : Euclid N) (v : Fin m → Euclid N), (S m ω : DifferentialForm (Euclid N) m) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (m + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ (m : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (m + 1)) (c : ℝ), (∀ y : Euclid (N + 1), covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (m + 1)) y) ≤ c) → ∀ x : Euclid N, covectorEuclideanNorm ((S m ω : DifferentialForm (Euclid N) m) x) ≤ c) → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), Z ω = X (S k ω)) → Z.boundary.mass < ∞ := by
  intro hMSB hSLB hSLC hSLD hR2 N k X Z S hXm hXb hS hSb hZ
  obtain ⟨Ψ, hΨ, hΨn⟩ := hR2 N k
  -- every admissible evaluation of `∂Z` is at most `2 M(X) + M(∂X)`
  have key : ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid (N + 1))) k univ,
      Z.boundary ω ≤ 2 * X.mass.toReal + (boundaryMassOn X univ).toReal := by
    intro ω hω
    -- the end slice `ρ_s(x) = Ψ(ω(s, x))` has norm `≤ 1`, so `|X(ρ_s)| ≤ M(X)`
    have hend : ∀ s : ℝ, ∃ ρ : TestFormOn (univ : Set (Euclid N)) k,
        (∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧
        |X ρ| ≤ X.mass.toReal := by
      intro s
      obtain ⟨ρ, hρ⟩ := hSLB N k s ω
      refine ⟨ρ, hρ, ?_⟩
      have h := hMSB N k X ρ 1 hXm fun x _ => by
        have hx : (ρ : DifferentialForm (Euclid N) k) x =
            Ψ ((ω : DifferentialForm (Euclid (N + 1)) k)
              (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) := by
          ext v
          rw [hρ, hΨ]
        rw [hx]
        exact (hΨn _).trans (hω.2 _)
      rwa [one_mul] at h
    obtain ⟨ρ₀, hρ₀, h₀⟩ := hend 0
    obtain ⟨ρ₁, hρ₁, h₁⟩ := hend 1
    rw [(GeometricCurrentOn.boundary_apply Z ω).trans (hZ _)]
    cases k with
    | zero =>
      -- `S₀(dω) = ρ₁ - ρ₀`
      have hSd : S 0 (exteriorDerivativeTestOn univ 0 ω) = ρ₁ - ρ₀ := by
        apply Subtype.ext
        funext x
        ext v
        rw [hS 0 _ x v]
        simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
        rw [hρ₁, hρ₀]
        exact hSLD N ω x v
      have hlin : X (ρ₁ - ρ₀) = X ρ₁ - X ρ₀ := map_sub X.toCurrent ρ₁ ρ₀
      have hb : 0 ≤ (boundaryMassOn X univ).toReal := ENNReal.toReal_nonneg
      rw [hSd, hlin]
      linarith [le_abs_self (X ρ₁), neg_abs_le (X ρ₀)]
    | succ k' =>
      -- `S_{k'+1}(dω) = ρ₁ - ρ₀ - dθ` with `θ = S_{k'}(ω)`
      have hSd : S (k' + 1) (exteriorDerivativeTestOn univ (k' + 1) ω) =
          ρ₁ - ρ₀ - exteriorDerivativeTestOn univ k' (S k' ω) := by
        apply Subtype.ext
        funext x
        ext v
        rw [hS (k' + 1) _ x v]
        simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
        rw [hρ₁, hρ₀]
        exact hSLC N k' ω (S k' ω) (hS k' ω) x v
      have hlin₁ : X (ρ₁ - ρ₀ - exteriorDerivativeTestOn univ k' (S k' ω)) =
          X (ρ₁ - ρ₀) - X.boundary (S k' ω) := map_sub X.toCurrent _ _
      have hlin₀ : X (ρ₁ - ρ₀) = X ρ₁ - X ρ₀ := map_sub X.toCurrent ρ₁ ρ₀
      -- `|θ| ≤ 1`, so `|∂X(θ)| ≤ M(∂X)`
      have hθ := hMSB N k' X.boundary (S k' ω) 1 hXb fun x _ => hSb k' ω 1 hω.2 x
      have hbm : (boundaryMassOn X univ).toReal = X.boundary.mass.toReal := rfl
      rw [hSd, hlin₁, hlin₀, hbm]
      linarith [le_abs_self (X ρ₁), neg_abs_le (X ρ₀), neg_abs_le (X.boundary (S k' ω))]
  -- hence `M(∂Z) ≤ 2 M(X) + M(∂X) < ∞`
  have hle : Z.boundary.mass ≤
      ENNReal.ofReal (2 * X.mass.toReal + (boundaryMassOn X univ).toReal) := by
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal (key ω hω)
  exact hle.trans_lt ENNReal.ofReal_lt_top
/-- Coordinates for the products `[[(0,1)]] × T` and `{p} × T` (Simon 6.2.17, 6.2.21–2.22),
`ℝ × ℝᴺ ≅ ℝᴺ⁺¹`, `(t, x) ↦ (t, x₁, …, x_N)`: the composite of `id × ofLp`, `Fin.consLinearEquiv`
and `toLp` is a linear equivalence, continuous in finite dimension, with `L(1, 0) = e₀` and
`‖L(0, x)‖ = ‖x‖`. -/
theorem Submission.cmcdt_lpo_slice_coords : ∀ N : ℕ, ∃ L : (ℝ × Euclid N) ≃L[ℝ] Euclid (N + 1), (∀ (t : ℝ) (x : Euclid N), L (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∧ L (1, 0) = EuclideanSpace.single 0 1 ∧ ∀ x : Euclid N, ‖L (0, x)‖ = ‖x‖ := by
  intro N
  -- `(t, x) ↦ (t, ofLp x) ↦ Fin.cons t (ofLp x) ↦ toLp 2 (Fin.cons t (ofLp x))`
  let e : (ℝ × Euclid N) ≃ₗ[ℝ] Euclid (N + 1) :=
    ((LinearEquiv.refl ℝ ℝ).prodCongr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))).trans
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (N + 1) => ℝ)).trans
        (WithLp.linearEquiv 2 ℝ (Fin (N + 1) → ℝ)).symm)
  -- `e` is continuous in finite dimension; (i) holds by unfolding the three maps
  have hL : ∀ (t : ℝ) (x : Euclid N),
      e.toContinuousLinearEquiv (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) :=
    fun _ _ => rfl
  refine ⟨e.toContinuousLinearEquiv, hL, ?_, fun x => ?_⟩
  · -- (ii): compare coordinates, splitting the index into `0` and `j.succ`
    rw [hL]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  · -- (iii): `‖L (0, x)‖² = ‖0‖² + ∑ⱼ ‖xⱼ‖² = ‖x‖²`
    rw [hL, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq x, Fin.sum_univ_succ]
    simp
/-- Smoothness of parametric integrals over `[0, 1]`, used for the slice form of `[[0, 1]] × T`
(Simon 6.2.17–2.22).  If `h : ℝ × ℝᴺ → V` is `C^∞`, then `x ↦ ∫₀¹ h(t, x) dt` is `C^∞` and its
derivative at `x` is `∫₀¹ D[x' ↦ h(t, x')](x) dt`.  The derivative formula is differentiation under
the integral sign, with the partial derivative bounded on `[0, 1] × closedBall x 1`; `C^n` follows
by induction on `n` over all value spaces, the derivative being a parametric integral of the
`C^∞` map `(t, x) ↦ D[x' ↦ h(t, x')](x)` with values in `L(ℝᴺ, V)`. -/
theorem Submission.cmcdt_lpo_slice_param_integral : ∀ (N : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (h : ℝ × Euclid N → V), ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x)) ∧ ∀ x : Euclid N, HasFDerivAt (fun x' : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x')) (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x) x := by
  intro N
  -- Steps 1–2: `x' ↦ h (t, x')` has derivative `(fderiv ℝ h (t, x)).comp inr` at `x`, so the
  -- partial derivative `h₁ p = fderiv ℝ (fun x' => h (p.1, x')) p.2` is `C^∞` in `p`.
  have hsmooth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h →
        ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Euclid N => fderiv ℝ (fun x' : Euclid N => h (p.1, x')) p.2) := by
    intro V _ _ h hh
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ h) := (contDiff_infty_iff_fderiv.1 hh).2
    have hpart : (fun p : ℝ × Euclid N => fderiv ℝ (fun x' : Euclid N => h (p.1, x')) p.2) =
        fun p => (fderiv ℝ h p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)) := by
      funext p
      exact (((contDiff_infty_iff_fderiv.1 hh).1 p).hasFDerivAt.comp p.2
        (hasFDerivAt_prodMk_right p.1 p.2)).fderiv
    rw [hpart]
    exact hd.clm_comp contDiff_const
  -- Step 3: differentiation under the integral sign, with a uniform bound on the partial
  -- derivative over the compact set `[0, 1] × closedBall x₀ 1`.
  have hderiv : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h → ∀ x₀ : Euclid N,
        HasFDerivAt (fun x' : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x'))
          (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x₀) x₀ := by
    intro V _ _ h hh x₀
    have hdiff : Differentiable ℝ h := (contDiff_infty_iff_fderiv.1 hh).1
    have hc : Continuous h := hh.continuous
    have h₁c := (hsmooth V h hh).continuous
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      h₁c.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => h (t, x)) (F' := fun x t => fderiv ℝ (fun x' : Euclid N => h (t, x')) x)
      (bound := fun _ => B) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun x =>
        (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (h₁c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_uIoc).mono fun t ht x hx => ?_
      rw [uIoc_of_le zero_le_one] at ht
      exact hB (t, x) (Set.mk_mem_prod (Ioc_subset_Icc_self ht) (ball_subset_closedBall hx))
    · exact Eventually.of_forall fun t x _ =>
        ((hdiff (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).differentiableAt.hasFDerivAt
  -- Step 4: `C^n` for every `n`, by induction over all value spaces at once.
  have hind : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ n (fun x : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x)) := by
    intro n
    induction n with
    | zero =>
      intro V _ _ h hh
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x => (hderiv V h hh x).continuousAt
    | succ n ih =>
      intro V _ _ h hh
      rw [Nat.cast_add_one, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x,
        ih (Euclid N →L[ℝ] V) _ (hsmooth V h hh), hderiv V h hh⟩
  -- Step 5.
  intro V _ _ _ h hh
  exact ⟨contDiff_infty.2 fun n => hind n V h hh, hderiv V h hh⟩

/-- **Coordinate splitting of `dβ` along `ℝ × ℝᴺ`** (pointwise form of Simon 6.2.17–2.21,
`∂([[0,1]] × T) = {1} × T − {0} × T − [[0,1]] × ∂T`).  Write `ι(s, y) = (s, y)`, `Jy = ι(0, y)` and
`e₀ = ι(1, 0)`; by `cmcdt_lpo_slice_coords`, `ι = L` for a continuous linear equivalence `L`.
Expand `dβ(ι(t, x))(e₀, Jv₀, …, Jvₖ) = Σᵢ (−1)ⁱ D[y ↦ β(y)(Ŵᵢ)](ι(t, x))(Wᵢ)` by
`exteriorDerivative_apply`, where `W = (e₀, Jv₀, …, Jvₖ)` and `Ŵᵢ` omits `Wᵢ`, and split off
`i = 0`.  As `y ↦ β(y)(u)` has derivative `m ↦ Dβ(y)(m)(u)`, the chain rule along `s ↦ ι(s, x)`
(derivative `e₀`) turns the `0`-th term into `d/ds|_{s=t} β(ι(s, x))(Jv)`.  For `i = j + 1`,
`Ŵᵢ = (e₀, J(removeNth j v))` and `Wᵢ = Jvⱼ`, and the chain rule along `x' ↦ ι(t, x')` (derivative
`J`) together with `(−1)^{j+1} = −(−1)^j` turns the term into
`−(−1)^j D[x' ↦ β(ι(t, x'))(e₀, J(removeNth j v))](x)(vⱼ)`. -/
theorem Submission.cmcdt_lpo_slice_extDeriv_split : ∀ (N k : ℕ) (β : DifferentialForm (Euclid (N + 1)) (k + 1)), Differentiable ℝ β → ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N), exteriorDerivative β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = deriv (fun s : ℝ => β (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) t - ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) • fderiv ℝ (fun x' : Euclid N => β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) := by
  intro N k β hβ t x v
  -- Step 1: the coordinate map `ι(s, y)` is `L (s, y)`, and `e₀ = L (1, 0)` (sibling `coords`)
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  simp only [← hL, ← hL1]
  -- Step 2: `y ↦ β y u` has derivative `m ↦ Dβ(y)(m)(u)`
  have hβu : ∀ (u : Fin (k + 1) → Euclid (N + 1)) (y : Euclid (N + 1)),
      HasFDerivAt (fun z => β z u) (fderiv ℝ (fun z => β z u) y) y := fun u y =>
    ((hβ y).continuousAlternatingMap_apply_const u).hasFDerivAt
  -- Step 3: derivatives of the coordinate paths `s ↦ L (s, x)` and `x' ↦ L (t, x')`
  have hpath₁ : HasDerivAt (fun s : ℝ => L (s, x)) (L (1, 0)) t :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hpath₂ : HasFDerivAt (fun x' : Euclid N => L (t, x'))
      ((L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N))) x :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have hslice : ∀ (u : Fin (k + 1) → Euclid (N + 1)) (y : Euclid N),
      fderiv ℝ (fun x' : Euclid N => β (L (t, x')) u) x y =
        fderiv ℝ (fun z => β z u) (L (t, x)) (L (0, y)) := by
    intro u y
    have h := (hβu u (L (t, x))).comp x hpath₂
    simp only [Function.comp_def] at h
    rw [h.fderiv]
    rfl
  -- Step 4: expand `dβ` and split off the index `0`
  rw [exteriorDerivative_apply (hβ _), Fin.sum_univ_succ, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · -- Step 5: the `0`-th term is `deriv φ t`, `φ s = β (L (s, x)) (Jv)`
    have h := (hβu (fun i => L (0, v i)) (L (t, x))).comp_hasDerivAt t hpath₁
    simp only [Function.comp_def] at h
    rw [h.deriv, Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero, Fin.tail_cons,
      Fin.cons_zero]
  · -- Step 6: the `(j + 1)`-st term, with `Ŵ = (e₀, J(removeNth j v))` and sign `−(−1)^j`
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrem : Fin.removeNth j.succ
        (Fin.cons (L (1, 0)) (fun i => L (0, v i)) : Fin (k + 1 + 1) → Euclid (N + 1)) =
        Fin.cons (L (1, 0)) (fun i => L (0, Fin.removeNth j v i)) :=
      Fin.cons_comp_succ_succAbove (L (1, 0)) (fun i => L (0, v i)) j
    rw [hslice, hrem, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
/-- **Simon 6.2.17** (the slice form of `[[0, 1]] × T`): for `ω ∈ 𝒟^{k+1}(ℝ^{N+1})` the fibre
integral `η(x)(v) = ∫₀¹ ω(t, x)(e₀, (0, v₁), …, (0, vₖ)) dt` is a test `k`-form on `ℝᴺ` with
`spt η ⊆ {x : (t, x) ∈ spt ω for some t ∈ [0, 1]}`.  In the coordinates `L (t, x) = (t, x)`,
`η` integrates `g (t, x) = Φ (ω (L (t, x)))` for the contraction
`Φ γ = γ (L (1, 0), J ·, …, J ·)`, `J y = L (0, y)`; it is smooth by the parametric integral
lemma and vanishes off the compact set `snd '' (L⁻¹ (spt ω) ∩ [0, 1] × ℝᴺ)`. -/
theorem Submission.cmcdt_lpo_slice_fiber_form : ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))} := by
  intro N k ω
  set ω' : DifferentialForm (Euclid (N + 1)) (k + 1) :=
    (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω' := ω.property.1.1
  have hωc : HasCompactSupport ω' := ω.property.1.2
  -- coordinates `L (t, y) = (t, y)` with `L (1, 0) = e₀`, and `J y = L (0, y)`
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  let J : Euclid N →L[ℝ] Euclid (N + 1) :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N))
  -- the contraction `Φ γ = γ (L (1, 0), J ·, …, J ·)` is continuous linear
  let Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k) (L (1, 0))).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap)
  have hΦ : ∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N),
      Φ γ v = γ (Fin.cons (L (1, 0)) fun i => L (0, v i)) := fun _ _ => rfl
  -- `g (t, x) = Φ (ω (L (t, x)))` is smooth, hence so is `η x = ∫₀¹ g (t, x) dt`
  let g : ℝ × Euclid N → Covector (Euclid N) k := fun p => Φ (ω' (L p))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Φ.contDiff.comp (hωs.comp L.contDiff)
  let η : DifferentialForm (Euclid N) k := fun x => ∫ t in (0 : ℝ)..1, g (t, x)
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η :=
    (Submission.cmcdt_lpo_slice_param_integral N (Covector (Euclid N) k) g hg).1
  -- `η` vanishes off the compact set `snd '' (L⁻¹ (spt ω) ∩ [0, 1] × ℝᴺ)`
  have hS : IsCompact (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) :=
    (L.toHomeomorph.isCompact_preimage.2 hωc.isCompact).inter_right
      (isClosed_Icc.prod isClosed_univ)
  have hsupp : support η ⊆ Prod.snd '' (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) := by
    intro x hx
    by_contra hxS
    refine mem_support.1 hx ?_
    have h0 : EqOn (fun t => g (t, x)) (fun _ => 0) (uIcc 0 1) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hnot : L (t, x) ∉ tsupport ω' := fun hmem =>
        hxS ⟨(t, x), ⟨hmem, ht, mem_univ _⟩, rfl⟩
      show Φ (ω' (L (t, x))) = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, map_zero]
    exact (intervalIntegral.integral_congr h0).trans intervalIntegral.integral_zero
  have hηt : tsupport η ⊆ Prod.snd '' (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) :=
    closure_minimal hsupp (hS.image continuous_snd).isClosed
  refine ⟨⟨η, ⟨hηs, (hS.image continuous_snd).of_isClosed_subset (isClosed_tsupport η) hηt⟩,
    subset_univ _⟩, fun x v => ?_, hηt.trans ?_⟩
  · -- evaluation at `v` commutes with the integral
    have hint : IntervalIntegrable (fun t => g (t, x)) volume 0 1 :=
      (hg.continuous.comp (Continuous.prodMk_left x)).intervalIntegrable 0 1
    let ev : Covector (Euclid N) k →L[ℝ] ℝ := ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ v
    calc η x v = ev (∫ t in (0 : ℝ)..1, g (t, x)) := rfl
      _ = ∫ t in (0 : ℝ)..1, ev (g (t, x)) := (ev.intervalIntegral_comp_comm hint).symm
      _ = _ := intervalIntegral.integral_congr fun t _ => by
        change Φ (ω' (L (t, x))) v = _
        rw [hΦ, hL1]
        simp only [hL]
  · rintro _ ⟨⟨t, y⟩, ⟨hmem, ht, -⟩, rfl⟩
    rw [mem_preimage, hL] at hmem
    exact ⟨t, ht, hmem⟩

/-- **End slices of `[[0, 1]] × T`** (Simon Ch. 6, 2.22: `{p} × T(ω) = T(Σ_β ω_{0β}(p, ·) dy^β)`).
Write `ι(t, x) = (t, x₁, …, x_N)` and `Jv = ι(0, v)`.  For `ω ∈ 𝒟ᵏ(ℝ^{N+1})` and `s ∈ ℝ`, the
form `ρ(x)(v₁, …, vₖ) = ω(ι(s, x))(Jv₁, …, Jvₖ)` lies in `𝒟ᵏ(ℝ^N)`.  With the coordinates
`L(t, y) = ι(t, y)` of `cmcdt_lpo_slice_coords`, `ρ` is the pull-back of `ω` by the affine map
`x ↦ L(s, 0) + L(0, x)`, which is proper since `‖x‖ = ‖L(0, x)‖ ≤ ‖L(s, 0) + L(0, x)‖ + ‖L(s, 0)‖`.
-/
theorem Submission.cmcdt_lpo_slice_end_form : ∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
  intro N k s ω
  obtain ⟨L, hL, -, hLn⟩ := Submission.cmcdt_lpo_slice_coords N
  -- `J y = L(0, y)`, so that `L(s, 0) + J x = L(s, x)`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1), ∀ y, J y = L (0, y) :=
    ⟨(L : (ℝ × Euclid N) →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)),
      fun _ => rfl⟩
  have hsJ : ∀ x, L (s, 0) + J x = L (s, x) := fun x => by
    rw [hJ, ← map_add L, Prod.mk_add_mk, add_zero, zero_add]
  -- `x ↦ L(s, 0) + J x` is proper: `‖x‖ = ‖J x‖ ≤ ‖L(s, 0) + J x‖ + ‖L(s, 0)‖`
  have hcont : Continuous fun x => L (s, 0) + J x := continuous_const.add J.continuous
  have hproper : IsProperMap fun x => L (s, 0) + J x := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine isCompact_of_isClosed_isBounded (hK.isClosed.preimage hcont)
      ((isBounded_closedBall (x := (0 : Euclid N)) (r := R + ‖L (s, 0)‖)).subset fun x hx => ?_)
    have hxR : ‖L (s, 0) + J x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖L (s, 0) + J x - L (s, 0)‖ := by rw [add_sub_cancel_left, hJ, hLn]
      _ ≤ ‖L (s, 0) + J x‖ + ‖L (s, 0)‖ := norm_sub_le _ _
      _ ≤ R + ‖L (s, 0)‖ := by linarith
  -- `ρ` is the affine pull-back of `ω`, a test form on `ℝ^N` by properness
  refine ⟨⟨affinePullbackForm J (L (s, 0)) (ω : DifferentialForm (Euclid (N + 1)) k), ?_⟩,
    fun x v => ?_⟩
  · exact show IsTestForm _ ∧ _ from
      ⟨affinePullbackForm_isTestForm J (L (s, 0)) hproper ω.property.1, subset_univ _⟩
  · show affinePullbackForm J (L (s, 0)) (ω : DifferentialForm (Euclid (N + 1)) k) x v = _
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hsJ, hL]
    congr 1
    funext i
    rw [Function.comp_apply, hJ, hL]

/-- **Slice homotopy identity in degree `k + 1`** (Simon 6.2.19, 6.2.21 at the level of forms:
`S_{dβ} = i₁^#β − i₀^#β − dS_β`).  Write `ι(t, x) = (t, x)`, `Jv = ι(0, v)` and `e₀ = ι(1, 0)`.
If `θ(x)(u) = ∫₀¹ β(ι(t, x))(e₀, Ju) dt` for all `x` and `u`, then
`∫₀¹ dβ(ι(t, x))(e₀, Jv) dt = β(ι(1, x))(Jv) − β(ι(0, x))(Jv) − dθ(x)(v)`.

By `cmcdt_lpo_slice_extDeriv_split` the integrand is `∂ₜ[β(ι(t, x))(Jv)]` minus the alternating
sum of the `x`-derivatives of the slices `β(ι(t, ·))(e₀, J v̂ⱼ)`.  The first term integrates to
the boundary terms (fundamental theorem of calculus).  Differentiating the hypothesis under the
integral sign (`cmcdt_lpo_slice_param_integral`; smoothness via the linear coordinates of
`cmcdt_lpo_slice_coords`) and expanding `dθ` identifies the integral of the second term with
`dθ(x)(v)`. -/
theorem Submission.cmcdt_lpo_slice_homotopy_succ : ∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v := by
  intro N k β θ hθ x v
  set B := (β : DifferentialForm (Euclid (N + 1)) (k + 1))
  set Θ := (θ : DifferentialForm (Euclid N) k)
  have hBs : ContDiff ℝ (⊤ : ℕ∞) B := β.property.1.1
  have hΘd : Differentiable ℝ Θ := θ.property.1.1.differentiable (by simp)
  -- (1) `p ↦ B(ι p)(w)` is smooth for each fixed tuple `w`, as `ι` is the linear equivalence `L`
  obtain ⟨L, hL, -, -⟩ := Submission.cmcdt_lpo_slice_coords N
  have hG : ∀ w : Fin (k + 1) → Euclid (N + 1), ContDiff ℝ (⊤ : ℕ∞)
      fun p : ℝ × Euclid N => B (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))) w := by
    intro w
    have hfun : (fun p : ℝ × Euclid N => B (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))) w) =
        ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w ∘ B ∘ L := by
      funext p
      simp only [Function.comp_apply, ContinuousAlternatingMap.apply_apply, ← hL, Prod.mk.eta]
    rw [hfun]
    exact (ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w).contDiff.comp
      (hBs.comp L.contDiff)
  -- (2) the `x`-derivative of each slice is continuous in `t`
  have hD : ∀ w : Fin (k + 1) → Euclid (N + 1), Continuous fun t : ℝ =>
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) w) x :=
    fun w => Continuous.fderiv
      (f := fun (t : ℝ) (x' : Euclid N) => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) w)
      (hG w) continuous_const (by simp)
  -- (3) differentiate the hypothesis on `θ` under the integral sign
  have hΘD : ∀ u : Fin k → Euclid N, fderiv ℝ (fun x' : Euclid N => Θ x' u) x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t
        (WithLp.ofLp x'))) (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i)))))) x := by
    intro u
    rw [show (fun x' : Euclid N => Θ x' u) = _ from funext fun x' => hθ x' u]
    exact ((Submission.cmcdt_lpo_slice_param_integral N ℝ _ (hG _)).2 x).fderiv
  -- (4) split the integrand into a `t`-derivative and the alternating sum of `x`-derivatives
  simp only [Submission.cmcdt_lpo_slice_extDeriv_split N k B (hBs.differentiable (by simp))]
  -- (5) fundamental theorem of calculus for `φ(s) = B(ι(s, x))(Jv)`
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => B (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
      (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :=
    (hG _).comp (contDiff_id.prodMk contDiff_const)
  have hFTC := intervalIntegral.integral_deriv_eq_sub (fun s _ => hφ.differentiable (by simp) s)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
  -- (6) the integral of the alternating sum is `dΘ(x)(v)`
  have hcont : ∀ j : Fin (k + 1), Continuous fun t : ℝ => (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x')))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) :=
    fun j => ((hD _).clm_apply continuous_const).fun_const_smul ((-1 : ℤ) ^ (j : ℕ))
  have hsum : ∫ t in (0 : ℝ)..1, ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x')))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) =
      exteriorDerivative Θ x v := by
    rw [exteriorDerivative_apply (hΘd x) v,
      intervalIntegral.integral_finsetSum fun j _ => (hcont j).intervalIntegrable 0 1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΘD, ContinuousLinearMap.intervalIntegral_apply ((hD _).intervalIntegrable 0 1)]
    simp only [zsmul_eq_mul, intervalIntegral.integral_const_mul]
  -- (7) linearity of the integral
  rw [intervalIntegral.integral_sub ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
    ((continuous_finsetSum _ fun j _ => hcont j).intervalIntegrable 0 1), hFTC, hsum]

/-- **Slice homotopy identity in degree `0`** (Simon 6.2.21 without the `∂T` term).  For
`β ∈ 𝒟⁰(ℝ^{N+1})`, `x ∈ ℝ^N` and the empty tuple `w = J ∘ v`,
`∫₀¹ dβ(ι(t, x))(e₀) dt = β(ι(1, x))(w) − β(ι(0, x))(w)`, where `ι(t, x) = (t, x)`.
With the coordinates `L(t, x) = ι(t, x)`, `L(1, 0) = e₀` of `cmcdt_lpo_slice_coords`, the path
`φ(s) = β(L(s, x))(w)` is smooth with `φ′(s) = D[y ↦ β(y)(w)](L(s, x))(e₀)`, the single term
`i = 0` of `exteriorDerivative_apply` (as `removeNth 0 (e₀, w) = w`); the fundamental theorem of
calculus concludes. -/
theorem Submission.cmcdt_lpo_slice_homotopy_zero : ∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
  intro N β x v
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  set ω : DifferentialForm (Euclid (N + 1)) 0 := (β : DifferentialForm (Euclid (N + 1)) 0)
  set w : Fin 0 → Euclid (N + 1) := fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω := β.property.1.1
  -- `y ↦ ω y w` is `ω` followed by the continuous linear evaluation at `w`
  have hωw : ContDiff ℝ (⊤ : ℕ∞) (fun y => ω y w) :=
    (ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w).contDiff.comp hω
  -- chain rule along the path `s ↦ L (s, x)`, whose velocity is `L (1, 0)`
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => L (s, x)) (L (1, 0)) s := fun s =>
    L.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ω (L (s, x)) w)
      (fderiv ℝ (fun y => ω y w) (L (s, x)) (L (1, 0))) s := fun s =>
    ((hωw.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s (hpath s)
  -- in degree `0` the exterior derivative is the single term `i = 0`
  have hpt : ∀ s : ℝ, exteriorDerivative ω (L (s, x)) (Fin.cons (L (1, 0)) w) =
      fderiv ℝ (fun y => ω y w) (L (s, x)) (L (1, 0)) := by
    intro s
    rw [exteriorDerivative_apply ((hω.differentiable (by simp)) _)]
    simp only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Int.reduceNeg,
      Fin.val_eq_zero, pow_zero, one_smul, Finset.sum_singleton, Fin.removeNth_zero,
      Fin.tail_cons, Fin.cons_zero]
  have hderiv : deriv (fun s : ℝ => ω (L (s, x)) w) =
      fun s => exteriorDerivative ω (L (s, x)) (Fin.cons (L (1, 0)) w) := by
    funext s
    rw [(hφ s).deriv, hpt]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ω (L (s, x)) w) :=
    hωw.comp (L.contDiff.comp (contDiff_id.prodMk contDiff_const))
  -- fundamental theorem of calculus, then back to the coordinates of the statement
  have key := intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1) _ hderiv
    (fun s _ => (hφ s).differentiableAt)
    (hderiv ▸ (hsmooth.continuous_deriv (by simp)).continuousOn)
  rw [hL1] at key
  simpa only [hL] using key
/-- **Simon 6.1.15, 6.2.17** (Minkowski's integral inequality for the Euclidean coefficient norm
`|·|` of 6.1.15, used for the slice forms defining `[[(0, 1)]] × T`): if `α(v) = ∫₀¹ f(t)(v) dt`
for all `v` and `|f(t)| ≤ c` on `[0, 1]`, then `|α| ≤ c`.  The coefficient vector
`κ(γ) = (γ(e_I))_{I strictly increasing} ∈ ℓ²` has `‖κ(γ)‖ = |γ|`, is continuous, and commutes
with the integral coordinatewise; hence `|α| = ‖∫₀¹ κ(f t) dt‖ ≤ c`. -/
theorem Submission.cmcdt_lpo_slice_covector_bound : ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c := by
  intro N k α f c hf hα hc
  classical
  -- the coefficient vector `κ γ = (γ(e_I))_I`, with `γ(e_I)` replaced by `0` unless `I` is
  -- strictly increasing
  let e : Fin N → Euclid N := fun j => EuclideanSpace.basisFun (Fin N) ℝ j
  let κ : Covector (Euclid N) k → EuclideanSpace ℝ (Fin k → Fin N) := fun γ =>
    WithLp.toLp 2 fun I => if StrictMono I then γ (fun i => e (I i)) else 0
  have hκnorm : ∀ γ, ‖κ γ‖ = covectorEuclideanNorm γ := by
    intro γ
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [κ, e, hI]
  have hκcont : Continuous κ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun I => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ite_true]
      exact continuous_eval_const _
    · simp only [hI, ite_false]
      exact continuous_const
  have hint : IntervalIntegrable (fun t => κ (f t)) volume 0 1 :=
    (hκcont.comp hf).intervalIntegrable 0 1
  -- `κ α = ∫₀¹ κ (f t) dt`, coordinatewise
  have hκα : κ α = ∫ t in (0 : ℝ)..1, κ (f t) := by
    ext I
    refine Eq.trans ?_ ((EuclideanSpace.proj I :
      EuclideanSpace ℝ (Fin k → Fin N) →L[ℝ] ℝ).intervalIntegral_comp_comm hint)
    by_cases hI : StrictMono I
    · simp only [κ, EuclideanSpace.coe_proj, hI, ite_true]
      exact hα _
    · simp only [κ, EuclideanSpace.coe_proj, hI, ite_false, intervalIntegral.integral_zero]
  rw [← hκnorm, hκα]
  calc ‖∫ t in (0 : ℝ)..1, κ (f t)‖ ≤ c * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
          rw [hκnorm]
          exact hc t (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le zero_le_one] using ht))
    _ = c := by simp

/-- **Slices of forms on `[0, 1] × ℝᴺ`** (Simon Ch. 6, 2.17–2.22, and the homotopy formula
2.25–2.27).  Write `ι(t, x) = (t, x₁, …, x_N)`, `Jv = ι(0, v)` and `e₀ = EuclideanSpace.single 0 1`.
(a) `η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt` is a test form on `ℝᴺ`, supported in the set of `x`
with `ι(t, x) ∈ spt ω` for some `t ∈ [0, 1]` (`cmcdt_lpo_slice_fiber_form`); (b) the end slice
`ρ(x)(v) = ω(ι(s, x))(Jv)` is a test form (`cmcdt_lpo_slice_end_form`); (c) if `θ` is the
slice (a) of `β`, then `∫₀¹ dβ(ι(t, x))(e₀, Jv) dt = β(ι(1, x))(Jv) − β(ι(0, x))(Jv) − dθ(x)(v)`
(`cmcdt_lpo_slice_homotopy_succ`); (d) in degree `0` the same identity holds without `dθ`
(`cmcdt_lpo_slice_homotopy_zero`); (e) `|α| ≤ c` when `α = ∫₀¹ f(t) dt` for continuous `f` with
`|f(t)| ≤ c` on `[0, 1]` (`cmcdt_lpo_slice_covector_bound`).  The statement is the conjunction
of these five children. -/
theorem Submission.cmcdt_lpo_slice_forms : (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ (∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v) ∧ (∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c :=
  ⟨Submission.cmcdt_lpo_slice_fiber_form, Submission.cmcdt_lpo_slice_end_form,
    Submission.cmcdt_lpo_slice_homotopy_succ, Submission.cmcdt_lpo_slice_homotopy_zero,
    Submission.cmcdt_lpo_slice_covector_bound⟩

/-- **Slice bound for the homotopy integrand** (Simon 6.2.27, the pointwise estimate of the
integrand of the homotopy formula).  Write `ι(t, x) = (t, x₁, …, x_N)`,
`e₀ = EuclideanSpace.single 0 1`, `Jv = ι(0, v)` and `|·|` for the Euclidean coefficient norm.
Given (L1) `|β ∘ A| ≤ ‖A‖ᵏ |β|` and (L2) `|β ⌟ v| ≤ ‖v‖ |β|`, if `α(v) = ∫₀¹ σ(ι(t, x))(e₀, Jv) dt`
and for each `t ∈ [0, 1]` the integrand is `γ(u, Av)` with `‖A‖ ≤ Λ`, `‖u‖ ≤ δ` and `|γ| ≤ c`,
then `|α| ≤ Λᵐ δ c`.  The integrand is `f(t) = (σ(ι(t, x)) ⌟ e₀) ∘ J`, continuous in `t`; on
`[0, 1]` it equals `(γ ⌟ u) ∘ A`, so `|f(t)| ≤ ‖A‖ᵐ ‖u‖ |γ| ≤ Λᵐ δ c` by (L1) and (L2), and the
Minkowski bound (conjunct (e) of `cmcdt_lpo_slice_forms`) concludes. -/
theorem Submission.cmcdt_lpo_she_slice_bound : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' m : ℕ) (σ : DifferentialForm (Euclid (N + 1)) (m + 1)) (x : Euclid N) (α : Covector (Euclid N) m) (Λ δ c : ℝ), Continuous σ → (∀ v : Fin m → Euclid N, α v = ∫ t in (0 : ℝ)..1, σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ t ∈ Icc (0 : ℝ) 1, ∃ (γ : Covector (Euclid N') (m + 1)) (u : Euclid N') (A : Euclid N →L[ℝ] Euclid N'), ‖A‖ ≤ Λ ∧ ‖u‖ ≤ δ ∧ covectorEuclideanNorm γ ≤ c ∧ ∀ v : Fin m → Euclid N, σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = γ (Fin.cons u (fun i => A (v i)))) → covectorEuclideanNorm α ≤ Λ ^ m * δ * c := by
  intro hcomp hcurry N N' m σ x α Λ δ c hσ hα hγ
  -- (1) `Λ, δ ≥ 0`, from the hypothesis at `t = 0`
  obtain ⟨-, u₀, A₀, hA₀, hu₀, -, -⟩ := hγ 0 ⟨le_rfl, zero_le_one⟩
  have hΛ : 0 ≤ Λ := (norm_nonneg _).trans hA₀
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hu₀
  -- (2) the embedding `J v = ι(0, v)` is continuous linear (finite dimension)
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun r v => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  -- (3) the integrand `f t = (σ(ι(t, x)) ⌟ e₀) ∘ J`, so `f t v = σ(ι(t, x))(e₀, Jv₁, …, Jvₘ)`
  let f : ℝ → Covector (Euclid N) m := fun t =>
    ((σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))).curryLeft
      (EuclideanSpace.single 0 1)).compContinuousLinearMap J
  have hfv : ∀ (t : ℝ) (v : Fin m → Euclid N), f t v =
      σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1)
        (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
    intro t v
    simp only [f, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    rfl
  -- (4) `f` is continuous
  have hι : Continuous fun t : ℝ =>
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) :=
    (PiLp.continuous_toLp 2 _).comp
      (Continuous.finCons (A := fun _ => ℝ) continuous_id continuous_const)
  have hf : Continuous f :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM J).continuous.comp
      ((ContinuousAlternatingMap.curryLeftLI.continuous.comp (hσ.comp hι)).clm_apply
        continuous_const)
  -- (5) `α v = ∫₀¹ f t v dt`, and (7) the Minkowski bound (conjunct (e) of `slice_forms`)
  refine Submission.cmcdt_lpo_slice_forms.2.2.2.2 N m α f (Λ ^ m * δ * c) hf
    (fun v => (hα v).trans (intervalIntegral.integral_congr fun t _ => (hfv t v).symm)) ?_
  -- (6) `f t = (γ ⌟ u) ∘ A`, so `|f t| ≤ ‖A‖ᵐ ‖u‖ |γ| ≤ Λᵐ δ c` on `[0, 1]`
  intro t ht
  obtain ⟨γ, u, A, hA, hu, hγc, hγv⟩ := hγ t ht
  have hft : f t = (γ.curryLeft u).compContinuousLinearMap A := by
    ext v
    rw [hfv, hγv]
    rfl
  rw [hft]
  calc covectorEuclideanNorm ((γ.curryLeft u).compContinuousLinearMap A)
      ≤ ‖A‖ ^ m * covectorEuclideanNorm (γ.curryLeft u) := hcomp N N' m A _
    _ ≤ ‖A‖ ^ m * (‖u‖ * covectorEuclideanNorm γ) :=
        mul_le_mul_of_nonneg_left (hcurry N' m u γ) (pow_nonneg (norm_nonneg A) m)
    _ ≤ Λ ^ m * (δ * c) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg A) hA m)
          (mul_le_mul hu hγc (covectorEuclideanNorm_nonneg γ) hδ)
          (mul_nonneg (norm_nonneg u) (covectorEuclideanNorm_nonneg γ)) (pow_nonneg hΛ m)
    _ = Λ ^ m * δ * c := (mul_assoc _ _ _).symm
/-- **Cylinder homotopy formula** (Simon 6.2.25 for `[[0, 1]] × X`, through
`∂([[0, 1]] × X) = {1} × X − {0} × X − [[0, 1]] × ∂X`, 6.2.21–2.22).  Write
`ι(t, x) = (t, x₁, …, x_N)`, `Jv = ι(0, v)` and `e₀ = EuclideanSpace.single 0 1`, and assume the
locality property (LOC) of currents.  If `η₁(x)(v) = β(ι(1, x))(Jv)` and `η₀(x)(v) = β(ι(0, x))(Jv)`
for `x` in an open `W ⊇ spt X`, then `X(η₁) − X(η₀) = X(η) + ∂X(θ)` for the slice forms
`η(x)(v) = ∫₀¹ dβ(ι(t, x))(e₀, Jv) dt` and `θ(x)(u) = ∫₀¹ β(ι(t, x))(e₀, Ju) dt`
(`cmcdt_lpo_slice_forms` (a)); in degree `0`, `X(η₁) − X(η₀) = X(η)`.  By the slice identities
(c), (d) of `cmcdt_lpo_slice_forms`, `η = η₁ − η₀ − dθ` (resp. `η₁ − η₀`) on `W`; (LOC), linearity
of `X` and `∂X(θ) = X(dθ)` conclude. -/
theorem Submission.cmcdt_lpo_she_cylinder_homotopy : (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η') → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1)) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, ∀ v : Fin (k + 1) → Euclid N, (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) ∧ (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∃ (η : TestFormOn (univ : Set (Euclid N)) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η : DifferentialForm (Euclid N) (k + 1)) x v = ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ (∀ (x : Euclid N) (u : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x u = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i)))))) ∧ X η₁ - X η₀ = X η + X.boundary θ) ∧ ∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, ∀ v : Fin 0 → Euclid N, (η₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) ∧ (η₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∃ η : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η : DifferentialForm (Euclid N) 0) x v = ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ X η₁ - X η₀ = X η := by
  intro hloc
  -- the slice forms (a) and the slice homotopy identities (c), (d) of `cmcdt_lpo_slice_forms`
  obtain ⟨hA, -, hC, hD, -⟩ := Submission.cmcdt_lpo_slice_forms
  refine ⟨fun N k X β η₀ η₁ W hW hXW hend => ?_, fun N X β η₀ η₁ W hW hXW hend => ?_⟩
  · -- (1), steps 1–2: `η = S_{dβ}` and `θ = S_β` by (a); the coercion of the test form
    -- `exteriorDerivativeTestOn univ (k + 1) β` is definitionally `exteriorDerivative β`
    obtain ⟨η, hη, -⟩ := hA N (k + 1) (exteriorDerivativeTestOn univ (k + 1) β)
    obtain ⟨θ, hθ, -⟩ := hA N k β
    refine ⟨η, θ, hη, hθ, ?_⟩
    -- steps 3–4: by (c) and the end-slice hypotheses, `η = η₁ − η₀ − dθ` on `W`, so (LOC) applies
    have hX : X η = X (η₁ - η₀ - exteriorDerivativeTestOn univ k θ) := by
      refine hloc N (k + 1) X _ _ W hW hXW fun x hx => ?_
      ext v
      rw [hη x v]
      refine (hC N k β θ hθ x v).trans ?_
      obtain ⟨h₁, h₀⟩ := hend x hx v
      rw [← h₁, ← h₀]
      rfl
    -- step 5: linearity of `X` and `∂X(θ) = X(dθ)`
    have hsub : X (η₁ - η₀ - exteriorDerivativeTestOn univ k θ) =
        X η₁ - X η₀ - X (exteriorDerivativeTestOn univ k θ) :=
      (X.toCurrent.map_sub (η₁ - η₀) _).trans (congrArg (· - _) (X.toCurrent.map_sub η₁ η₀))
    rw [GeometricCurrentOn.boundary_apply, hX, hsub]
    ring
  · -- (2), step 6: `η = S_{dβ}` by (a) in degree `0`
    obtain ⟨η, hη, -⟩ := hA N 0 (exteriorDerivativeTestOn univ 0 β)
    refine ⟨η, hη, ?_⟩
    -- step 7: by (d) and the end-slice hypotheses, `η = η₁ − η₀` on `W`, so (LOC) applies
    have hX : X η = X (η₁ - η₀) := by
      refine hloc N 0 X _ _ W hW hXW fun x hx => ?_
      ext v
      rw [hη x v]
      refine (hD N β x v).trans ?_
      obtain ⟨h₁, h₀⟩ := hend x hx v
      rw [← h₁, ← h₀]
      rfl
    -- step 8: linearity of `X`
    rw [hX]
    exact (X.toCurrent.map_sub η₁ η₀).symm
/-- The cut-off pull-back of Simon 6.2.23: for a `C^∞` map `F : ℝᴺ → ℝ^{N'}`, `ω ∈ 𝒟ᵏ(ℝ^{N'})` and
a compact `K ⊆ ℝᴺ`, some `η = ζ F^#ω ∈ 𝒟ᵏ(ℝᴺ)` agrees with `F^#ω` on an open `W ⊇ K`, and
`dη = F^#(dω)` on `W` (as used in 6.2.24(1)).  Here `ζ` is a smooth bump equal to `1` on a ball
`W ⊇ K`.  `F^#ω` is smooth: as a multilinear map, `F^#ω(x) = ω(F x) ∘ (DF(x), …, DF(x))` depends
smoothly on `x`, and `γ ↦ (γ(e_{I 1}, …, e_{I k}))_I` is linear and injective into a
finite-dimensional space, so it has a continuous linear left inverse.  On `W`, `η = F^#ω` near
each point, so `dη = d(F^#ω) = F^#(dω)` (`extDeriv_pullback`). -/
theorem Submission.cmcdt_lpo_cutoff_pullback : ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
  intro N N' k F ω K hF hK
  set ω₀ : DifferentialForm (Euclid N') k := (ω : DifferentialForm (Euclid N') k)
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω₀ := ω.2.1.1
  have hDF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right le_rfl
  -- the pull-back `P = F^#ω` is smooth
  set P : DifferentialForm (Euclid N) k :=
    fun x => (ω₀ (F x)).compContinuousLinearMap (fderiv ℝ F x)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := by
    let ι : Covector (Euclid N) k →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclid N) ℝ :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x => ι (P x) := by
      have h := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => Euclid N) (fun _ : Fin k => Euclid N') ℝ).contDiff.comp
          (contDiff_pi.2 fun _ => hDF)).clm_apply
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp (hω.comp hF))
      convert h using 1
      funext x
      ext v
      simp [ι, P, Function.comp_def]
    -- the values on basis tuples determine a covector
    let e := EuclideanSpace.basisFun (Fin N) ℝ
    let ev' : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclid N) ℝ →L[ℝ]
        ((Fin k → Fin N) → ℝ) :=
      ContinuousLinearMap.pi fun I =>
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclid N) ℝ fun i => e (I i)
    let ev : Covector (Euclid N) k →ₗ[ℝ] ((Fin k → Fin N) → ℝ) := (ev'.comp ι).toLinearMap
    have hev : LinearMap.ker ev = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro γ hγ
      have h' : γ.toAlternatingMap = (0 : Covector (Euclid N) k).toAlternatingMap := by
        refine e.toBasis.ext_alternating fun I _ => ?_
        have := congrFun hγ I
        simpa [ev, ev', ι, e] using this
      exact ContinuousAlternatingMap.toAlternatingMap_injective h'
    obtain ⟨ℓ, hℓ⟩ := ev.exists_leftInverse_of_injective hev
    have hPℓ : P = fun x => LinearMap.toContinuousLinearMap ℓ (ev' (ι (P x))) := by
      funext x
      exact (LinearMap.congr_fun hℓ (P x)).symm
    rw [hPℓ]
    exact (LinearMap.toContinuousLinearMap ℓ).contDiff.comp (ev'.contDiff.comp h1)
  -- a smooth bump `b`, equal to `1` on a ball `W ⊇ K`
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Euclid N)
  let b : ContDiffBump (0 : Euclid N) := ⟨R, R + 1, hR, by linarith⟩
  have hb1 : ∀ x ∈ ball (0 : Euclid N) R, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hη : (fun x => b x • P x) ∈ TestFormOn (univ : Set (Euclid N)) k :=
    ⟨⟨b.contDiff.smul hP, b.hasCompactSupport.smul_right⟩, subset_univ _⟩
  refine ⟨⟨fun x => b x • P x, hη⟩, ball 0 R, isOpen_ball, hKR, fun x hx => ?_, fun x hx => ?_⟩
  · show b x • P x = P x
    rw [hb1 x hx, one_smul]
  · have heq : (fun x => b x • P x) =ᶠ[𝓝 x] P := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [hb1 y hy, one_smul]
    show extDeriv (fun x => b x • P x) x = _
    rw [heq.extDeriv_eq]
    exact extDeriv_pullback ((hω.differentiable (by simp)).differentiableAt) hF.contDiffAt
      (by simp)
/-- The affine homotopy `h(t, x) = f(x) + t (g(x) − f(x))` from `f` to `g` (Simon 6.2.26, p. 140)
for smooth `f, g : ℝᴺ → ℝᴺ'`, with `(t, x) ∈ ℝ^{N+1}` written `ι(t, x)`, and the derivative facts
used for 2.27: `h` is `C^∞`, `dh_{ι(t,x)} e₀ = g(x) − f(x)`,
`dh_{ι(t,x)} ι(0, v) = df_x v + t (dg_x v − df_x v)` and
`‖dh_{ι(t,x)}‖ ≤ |g(x) − f(x)| + ‖df_x‖ + |t| (‖dg_x‖ + ‖df_x‖)`.  With `tl y = (y₁, …, y_N)` and
`hd y = y₀`, both continuous linear with `‖tl w‖, |hd w| ≤ ‖w‖`, `h = f ∘ tl + hd • (g ∘ tl − f ∘ tl)`
and the chain and product rules give
`dh_y w = df_{tl y} (tl w) + hd y (dg_{tl y} (tl w) − df_{tl y} (tl w)) + hd w (g(tl y) − f(tl y))`. -/
theorem Submission.cmcdt_lpoh_interp_calculus : ∀ (N N' : ℕ) (f g : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g → ∃ h : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ (t : ℝ) (x : Euclid N), h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = f x + t • (g x - f x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = g x - f x) ∧ (∀ (t : ℝ) (x v : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ f x v + t • (fderiv ℝ g x v - fderiv ℝ f x v)) ∧ ∀ (t : ℝ) (x : Euclid N), ‖fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖) := by
  intro N N' f g hf hg
  -- the coordinate maps `tl y = (y₁, …, y_N)` and `hd y = y₀`
  let tlL : Euclid (N + 1) →ₗ[ℝ] Euclid N :=
    { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
      map_add' := by intro y z; rfl
      map_smul' := by intro r y; rfl }
  let tl : Euclid (N + 1) →L[ℝ] Euclid N := LinearMap.toContinuousLinearMap tlL
  let hd : Euclid (N + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (N + 1))
  have htl : ∀ y, tl y = WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) := fun y => rfl
  have hhd : ∀ y : Euclid (N + 1), hd y = WithLp.ofLp y 0 := fun y => rfl
  have htlι : ∀ (t : ℝ) (x : Euclid N), tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x := by
    intro t x; rw [htl]; simp
  have hhdι : ∀ (t : ℝ) (x : Euclid N), hd (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = t := by
    intro t x; rw [hhd]; simp
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  set h : Euclid (N + 1) → Euclid N' := fun y => f (tl y) + hd y • (g (tl y) - f (tl y)) with hh
  -- `dh_y = df_{tl y} ∘ tl + hd y • (dg_{tl y} ∘ tl − df_{tl y} ∘ tl) + hd ⊗ (g(tl y) − f(tl y))`
  have hderiv : ∀ y, HasFDerivAt h ((fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y)))) y := by
    intro y
    have h1 : HasFDerivAt (fun y => f (tl y)) ((fderiv ℝ f (tl y)).comp tl) y :=
      (hfd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    have h2 : HasFDerivAt (fun y => g (tl y)) ((fderiv ℝ g (tl y)).comp tl) y :=
      (hgd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    exact h1.add (hd.hasFDerivAt.smul (h2.sub h1))
  have hfd' : ∀ y, fderiv ℝ h y = (fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y))) := fun y => (hderiv y).fderiv
  have htle : tl (EuclideanSpace.single 0 1) = 0 := by
    rw [htl]; ext i; simp [Fin.tail]
  have hhde : hd (EuclideanSpace.single 0 1 : Euclid (N + 1)) = 1 := by
    rw [hhd]; simp
  have htlJ : ∀ v : Euclid N, tl (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = v := fun v => htlι 0 v
  have hhdJ : ∀ v : Euclid N, hd (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = 0 := fun v => hhdι 0 v
  -- `‖tl w‖ ≤ ‖w‖` and `|hd w| ≤ ‖w‖`
  have htln : ∀ w : Euclid (N + 1), ‖tl w‖ ≤ ‖w‖ := by
    intro w
    rw [htl, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    rw [Fin.sum_univ_succ]
    simp only [Fin.tail]
    have : 0 ≤ ‖WithLp.ofLp w 0‖ ^ 2 := by positivity
    linarith
  have hhdn : ∀ w : Euclid (N + 1), |hd w| ≤ ‖w‖ := by
    intro w
    rw [hhd, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le w 0
  refine ⟨h, (hf.comp tl.contDiff).add (hd.contDiff.smul ((hg.comp tl.contDiff).sub (hf.comp tl.contDiff))),
    ?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [hh, htlι, hhdι]
  · intro t x
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htle, hhde, map_zero, sub_self, smul_zero, zero_add, one_smul,
      htlι]
  · intro t x v
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlJ, hhdJ, zero_smul, add_zero, htlι, hhdι]
  · intro t x
    rw [hfd']
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlι, hhdι]
    have e1 : ‖fderiv ℝ f x (tl w)‖ ≤ ‖fderiv ℝ f x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e2 : ‖fderiv ℝ g x (tl w)‖ ≤ ‖fderiv ℝ g x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e3 : ‖hd w • (g x - f x)‖ ≤ ‖g x - f x‖ * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      gcongr
      exact hhdn w
    calc ‖fderiv ℝ f x (tl w) + (t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w)) + hd w • (g x - f x))‖
        ≤ ‖fderiv ℝ f x (tl w)‖ + (‖t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w))‖ + ‖hd w • (g x - f x)‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ‖fderiv ℝ f x‖ * ‖w‖ + (|t| * (‖fderiv ℝ g x‖ * ‖w‖ + ‖fderiv ℝ f x‖ * ‖w‖) + ‖g x - f x‖ * ‖w‖) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add e2 e1)
      _ = (‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖)) * ‖w‖ := by ring
/-- **Mollification of Lipschitz maps**: a `Λ`-Lipschitz `F : ℝᴺ → ℝᴺ'` has `C^∞`,
`Λ`-Lipschitz approximants `Fⱼ` with `|Fⱼ − F| ≤ Λ/(j + 1)`.  For `σ > 0` normalize the bump `b`
of a `ContDiffBump` at `0` with `rOut = σ` to `ϕ = b/∫b` (`∫b > 0` as `volume (B_σ(0)) > 0`), so
`ϕ ≥ 0`, `∫ϕ = 1` and `support ϕ ⊆ B_σ(0)`, and put `G = ϕ ⋆ F`.  Then `G` is `C^∞`,
`G x − G y = ∫ ϕ(t)(F(x − t) − F(y − t)) dt` gives the constant `Λ`, and `|G − F| ≤ Λσ` since
`|F y − F x| ≤ Λσ` on `B_σ(x)`.  Take `σ = 1/(j + 1)`. -/
theorem Submission.cmcdt_lpo_mollify_lipschitz : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ ∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := by
  intro N N' Λ F hF
  -- For each `σ > 0`: a `C^∞`, `Λ`-Lipschitz `G` with `|G − F| ≤ Λσ`
  have key : ∀ σ : ℝ, 0 < σ → ∃ G : Euclid N → Euclid N', ContDiff ℝ (⊤ : ℕ∞) G ∧
      LipschitzWith Λ G ∧ ∀ x, dist (G x) (F x) ≤ (Λ : ℝ) * σ := by
    intro σ hσ
    -- Step 1: the bump `b`: `C^∞`, `b ≥ 0`, `support b = B_σ(0)`, compact support
    let b : ContDiffBump (0 : Euclid N) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
    have hbi : Integrable (b : Euclid N → ℝ) :=
      b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    -- Step 2: `∫ b > 0`, and the normalized bump `ϕ = (∫ b)⁻¹ b`
    have hIpos : 0 < ∫ t, b t := by
      rw [integral_pos_iff_support_of_nonneg (fun t => b.nonneg) hbi, b.support_eq]
      exact measure_ball_pos _ _ hσ
    set ϕ : Euclid N → ℝ := fun t => (∫ s, b s)⁻¹ * b t with hϕ
    have hϕd : ContDiff ℝ (⊤ : ℕ∞) ϕ := contDiff_const.mul b.contDiff
    have hϕs : HasCompactSupport ϕ := b.hasCompactSupport.mul_left
    have hϕn : ∀ t, 0 ≤ ϕ t := fun t => mul_nonneg (inv_nonneg.2 hIpos.le) b.nonneg
    have hϕ1 : ∫ t, ϕ t = 1 := by
      rw [hϕ, integral_const_mul]
      exact inv_mul_cancel₀ hIpos.ne'
    have hϕb : support ϕ ⊆ ball 0 σ := by
      intro t ht
      have : t ∈ support (b : Euclid N → ℝ) := Function.support_mul_subset_right _ _ ht
      rwa [b.support_eq] at this
    have hϕi : Integrable ϕ := hϕd.continuous.integrable_of_hasCompactSupport hϕs
    -- Step 3: `G = ϕ ⋆ F` is `C^∞`; its integrands `t ↦ ϕ t • F (x - t)` are integrable
    have hFc : Continuous F := hF.continuous
    have hex : ∀ x, Integrable (fun t => ϕ t • F (x - t)) := by
      intro x
      have := (hϕs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hϕd.continuous
        hFc.locallyIntegrable (μ := volume)) x
      simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using this
    refine ⟨convolution ϕ F (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_⟩
    · exact hϕs.contDiff_convolution_left _ hϕd hFc.locallyIntegrable
    -- Step 4: `‖G x − G y‖ ≤ ∫ ϕ(t) Λ‖x − y‖ dt = Λ‖x − y‖`
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
      rw [dist_eq_norm, ← integral_sub (hex x) (hex y)]
      calc ‖∫ t, (ϕ t • F (x - t) - ϕ t • F (y - t))‖
          ≤ ∫ t, ϕ t * ((Λ : ℝ) * dist x y) := by
            refine norm_integral_le_of_norm_le (hϕi.mul_const _) (Eventually.of_forall fun t => ?_)
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hϕn t), ← dist_eq_norm]
            refine mul_le_mul_of_nonneg_left ?_ (hϕn t)
            calc dist (F (x - t)) (F (y - t)) ≤ (Λ : ℝ) * dist (x - t) (y - t) :=
                  hF.dist_le_mul _ _
              _ = (Λ : ℝ) * dist x y := by rw [dist_sub_right]
        _ = (Λ : ℝ) * dist x y := by rw [integral_mul_const, hϕ1, one_mul]
    -- Step 5: `|F y − F x| ≤ Λσ` on `B_σ(x)`, so `|G x − F x| ≤ Λσ` (`ϕ ≥ 0`, `∫ϕ = 1`)
    · intro x
      refine dist_convolution_le (by positivity) hϕb hϕn hϕ1 hFc.aestronglyMeasurable
        fun y hy => ?_
      calc dist (F y) (F x) ≤ (Λ : ℝ) * dist y x := hF.dist_le_mul _ _
        _ ≤ (Λ : ℝ) * σ := mul_le_mul_of_nonneg_left (mem_ball.1 hy).le Λ.coe_nonneg
  -- Step 6: `σ = 1/(j + 1)`
  choose G hG using fun j : ℕ => key (1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨G, fun j => (hG j).1, fun j => (hG j).2.1, fun j x => ?_⟩
  calc dist (G j x) (F x) ≤ (Λ : ℝ) * (1 / ((j : ℝ) + 1)) := (hG j).2.2 x
    _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring

/-- **Smooth approximants of a Lipschitz map with cut-off pull-backs** (the data of Simon 6.2.29):
for a `Λ`-Lipschitz `F : ℝᴺ → ℝ^{N'}` and a compact `K ⊆ ℝᴺ`, the mollified maps `Fⱼ` of
`cmcdt_lpo_mollify_lipschitz` are `C^∞` and `Λ`-Lipschitz, hence `‖DFⱼ‖ ≤ Λ`, and
`|Fⱼ − F| ≤ Λ/(j + 1) → 0` gives `Fⱼ → F` uniformly.  For `ω ∈ 𝒟ᵏ(ℝ^{N'})`,
`cmcdt_lpo_cutoff_pullback` applied to each `Fⱼ` gives `ηⱼ ∈ 𝒟ᵏ(ℝᴺ)` and an open `W ⊇ K` with
`ηⱼ = Fⱼ^#ω` and `dηⱼ = Fⱼ^#(dω)` on `W`. -/
theorem Submission.cmcdt_lpo_pf_approx_data : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (K : Set (Euclid N)), LipschitzWith Λ F → IsCompact K → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ)) ∧ (∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) ∧ TendstoUniformly Fs F atTop ∧ ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid N')) k), ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ ∀ x ∈ W, exteriorDerivative (ηs j : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x) := by
  intro N N' Λ F K hF hK
  obtain ⟨Fs, hFs, hLip, hdist⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ F hF
  refine ⟨Fs, hFs, hLip, fun j x => norm_fderiv_le_of_lipschitz ℝ (hLip j), hdist, ?_, ?_⟩
  -- `Λ/(j + 1) → 0`, so `Fⱼ → F` uniformly
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have h0 : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
      rw [mul_zero] at this
      exact this.congr (fun j => mul_one_div _ _)
    filter_upwards [h0.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_comm]
    exact lt_of_le_of_lt (hdist j x) hj
  -- the cut-off pull-backs `ηⱼ`, chosen for each `j`
  · intro k ω
    choose ηs W hW using fun j =>
      Submission.cmcdt_lpo_cutoff_pullback N N' k (Fs j) ω K (hFs j) hK
    exact ⟨ηs, fun j => ⟨W j, hW j⟩⟩
/-- **Test forms and their exterior derivatives are bounded** in the Euclidean coefficient norm
`|α|` of Simon (6.1.15), as used for the Lipschitz push-forward (Simon Ch. 6, 2.28–2.29).  For a
test form `θ ∈ 𝒟ᵐ(ℝᴺ)`, `y ↦ |θ(y)|` is the square root of a finite sum of squares of the
continuous evaluations `y ↦ θ(y)(e_{I 1}, …, e_{I m})`, hence continuous, and has compact support
since `|0| = 0`; so it is bounded.  Apply this to `ω` and to `dω`, a test form by
`exteriorDerivative_isTestForm`. -/
theorem Submission.cmcdt_lpo_pf_form_bounds : ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid N)) k), (∃ a : ℝ, ∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) y) ≤ a) ∧ ∃ b : ℝ, ∀ y, covectorEuclideanNorm (exteriorDerivative (ω : DifferentialForm (Euclid N) k) y) ≤ b := by
  intro N k ω
  -- a test form has bounded Euclidean coefficient norm
  have hbd : ∀ (m : ℕ) (θ : DifferentialForm (Euclid N) m), IsTestForm θ →
      ∃ a : ℝ, ∀ y, covectorEuclideanNorm (θ y) ≤ a := by
    intro m θ hθ
    have hθc : Continuous θ := hθ.1.continuous
    have hcont : Continuous (covectorEuclideanNorm ∘ θ) := by
      show Continuous fun y => covectorEuclideanNorm (θ y)
      unfold covectorEuclideanNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => (hθc.eval_const _).pow 2) (fun _ => continuous_const)
    have hsupp : HasCompactSupport (covectorEuclideanNorm ∘ θ) :=
      HasCompactSupport.comp_left (g := covectorEuclideanNorm) hθ.2 (covectorEuclideanNorm_zero N m)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hsupp
    refine ⟨C, fun y => (le_abs_self _).trans ?_⟩
    have := hC y
    rwa [Real.norm_eq_abs] at this
  exact ⟨hbd k _ ω.property.1, hbd (k + 1) _ (exteriorDerivative_isTestForm ω.property.1)⟩
/-- Compactly supported normal currents in `ℝᴺ` are closed under differences and boundaries.
(a) If `X, Y ∈ 𝒟ₖ(ℝᴺ)` have compact support, finite mass and finite boundary mass, then
`spt(X − Y) ⊆ spt X ∪ spt Y` is compact and `X − Y` has finite mass and boundary mass.
(b) If `X ∈ 𝒟ₖ₊₁(ℝᴺ)` has compact support, then `spt ∂X ⊆ spt X` is compact and `M(∂∂X) = 0`.
Mass is subadditive on differences since `−ω` is admissible with `ω`; supports are closed;
`X − Y` vanishes where `X` and `Y` both vanish; `spt dω ⊆ spt ω`; and `∂∂ = 0`. -/
theorem Submission.cmcdt_lpo_pf_normal_closure : (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → (X - Y).support ⊆ X.support ∪ Y.support ∧ IsCompact (X - Y).support ∧ (X - Y).mass < ∞ ∧ boundaryMassOn (X - Y) univ < ∞) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.boundary.support ⊆ X.support ∧ IsCompact X.boundary.support ∧ boundaryMassOn X.boundary univ = 0 := by
  -- `M(A − B) ≤ M(A) + M(B)`: `(A − B)(ω) = A(ω) + B(−ω)` and `−ω` is admissible with `ω`
  have key : ∀ (N m : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid N)) m),
      (A - B).massOn univ ≤ A.massOn univ + B.massOn univ := by
    intro N m A B
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    have hneg : -ω ∈ massAdmissibleOn univ m univ :=
      ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
    have hval : (A - B) ω = A ω + B (-ω) := by
      show A ω - B ω = A ω + B (-ω)
      have h := B.toCurrent.map_neg ω
      linarith
    dsimp only
    rw [hval]
    exact ENNReal.ofReal_add_le.trans (add_le_add (A.le_massOn hω) (B.le_massOn hneg))
  -- supports in `ℝᴺ` are closed: `spt T` is the complement of the open zero region
  have hclosed : ∀ (N m : ℕ) (A : GeometricCurrentOn (univ : Set (Euclid N)) m),
      IsClosed A.support := by
    intro N m A
    rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
    exact A.isOpen_zeroRegion.isClosed_compl
  refine ⟨?_, ?_⟩
  · intro N k X Y hX1 hX2 hX3 hY1 hY2 hY3
    -- `X − Y` vanishes on `W₁ ∩ W₂` when `X` vanishes on `W₁` and `Y` on `W₂`
    have hsupp : (X - Y).support ⊆ X.support ∪ Y.support := by
      rintro x ⟨-, hx⟩
      by_contra hxy
      simp only [mem_union, not_or] at hxy
      obtain ⟨W₁, ⟨hW₁o, hW₁c, -, hW₁v⟩, hxW₁⟩ : x ∈ X.zeroRegion :=
        not_not.1 fun h => hxy.1 ⟨mem_univ x, h⟩
      obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hxW₂⟩ : x ∈ Y.zeroRegion :=
        not_not.1 fun h => hxy.2 ⟨mem_univ x, h⟩
      refine hx ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o, ?_, subset_univ _, fun ω hω => ?_⟩, hxW₁, hxW₂⟩
      · exact hW₁c.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
      · show X ω - Y ω = 0
        rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
    refine ⟨hsupp, (hX1.union hY1).of_isClosed_subset (hclosed N k _) hsupp,
      (key N k X Y).trans_lt (ENNReal.add_lt_top.2 ⟨hX2, hY2⟩), ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k' =>
      -- `∂(X − Y) = ∂X − ∂Y`
      have hb : (X - Y).boundary = X.boundary - Y.boundary := by
        ext ω
        rfl
      show (X - Y).boundary.massOn univ < ∞
      rw [hb]
      exact (key N k' _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hX3, hY3⟩)
  · intro N k X hX
    -- `∂X` vanishes wherever `X` does, since `spt dω ⊆ spt ω`
    have hsupp : X.boundary.support ⊆ X.support := by
      rintro x ⟨-, hx⟩
      refine ⟨mem_univ x, fun hxX => hx ?_⟩
      obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxX
      exact ⟨W, ⟨hWo, hWc, hWU, fun ω hω =>
        hWv _ ((tsupport_exteriorDerivative_subset _).trans hω)⟩, hxW⟩
    refine ⟨hsupp, hX.of_isClosed_subset (hclosed N k _) hsupp, ?_⟩
    cases k with
    | zero => rfl
    | succ k' =>
      -- `∂∂X = 0`, and the zero current has zero mass
      show X.boundary.boundary.massOn univ = 0
      rw [X.boundary_boundary]
      refine le_antisymm (sSup_le ?_) bot_le
      rintro r ⟨ω, -, rfl⟩
      simp
/-- **Simon Ch. 6, 2.7–2.8 with 2.12** (mass–support bound).  Let `X ∈ 𝒟ₖ(ℝᴺ)` have
`M(X) < ∞` and let `|ψ(x)| ≤ c` on `spt X`.  The representation `X(ω) = ∫ ⟨ω, ξ⟩ dμ` with
`M_W(X) = μ(W)` (`W` open) and `|ξ| ≤ 1` makes `μ` finite with `μ(ℝᴺ) = M(X)`.  `X` kills every
test form supported in the open zero region `ℝᴺ \ spt X`, so `μ` gives it measure zero; hence
`|ξ(x)(ψ(x))| ≤ c` for `μ`-a.e. `x`, and `|X(ψ)| ≤ c μ(ℝᴺ) = c M(X)`. -/
theorem Submission.cmcdt_lpo_tk_mass_support_bound : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal := by
  intro hVO hREP N k X ψ c hX hψ
  -- the representation of `X`: every local mass is at most `M(X) < ∞`
  obtain ⟨μ, ξ, -, -, hμ, -, hξ, hrep, -⟩ := hREP N k univ X isOpen_univ
    fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX
  -- `μ(ℝᴺ) = M(X)`, so `μ` is finite
  have hμuniv : μ univ = X.mass := (hμ univ isOpen_univ).symm
  have : IsFiniteMeasure μ := ⟨hμuniv ▸ hX⟩
  -- the zero region is `μ`-null: `X` kills every admissible form supported in it
  have hZ : μ X.zeroRegion = 0 := by
    rw [← hμ _ X.isOpen_zeroRegion]
    refine le_antisymm (sSup_le ?_) bot_le
    rintro r ⟨ω, hω, rfl⟩
    have hω0 : X ω = 0 := hVO N k univ X ω <| Set.disjoint_left.2 fun x hx hxS => hxS.2 (hω.1 hx)
    simp [hω0]
  -- hence `μ`-a.e. `x` lies in `spt X`, where `|ξ(x)(ψ(x))| ≤ |ψ(x)| ≤ c`
  have hbound : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
    have hae : ∀ᵐ x ∂μ, x ∈ X.support :=
      measure_mono_null (fun x hx => by_contra fun hxZ => hx ⟨mem_univ x, hxZ⟩) hZ
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    exact (hξ x _).trans (hψ x hx)
  rw [hrep ψ, ← Real.norm_eq_abs, ← hμuniv, ← measureReal_def]
  exact norm_integral_le_of_norm_le_const hbound
/-- **Simon 6.2.1, 6.2.4** (bounded functionals are currents): a linear functional `T₀` on
`𝒟ᵏ(ℝᴺ)` with `|T₀(ω)| ≤ C c` whenever `|ω(x)| ≤ c` for all `x` (Euclidean coefficient norm) is
a current `T ∈ 𝒟ₖ(ℝᴺ)` with `M(T) ≤ C`.  Each coefficient of a covector `α` is its value on unit
vectors, so `|α| ≤ √(Nᵏ) ‖α‖`; hence `ωⱼ → 0` uniformly (supports in a fixed compact set) forces
`T₀(ωⱼ) → 0`.  The zero form gives `C ≥ 0`, and admissible forms give `T(ω) ≤ C`. -/
theorem Submission.cmcdt_lpo_tk_bounded_current : ∀ (N k : ℕ) (T₀ : TestFormOn (univ : Set (Euclid N)) k →ₗ[ℝ] ℝ) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T₀ ω| ≤ C * c) → ∃ T : GeometricCurrentOn (univ : Set (Euclid N)) k, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal C := by
  intro N k T₀ C hT
  -- `|α| ≤ √(Nᵏ) ‖α‖`: each of the `Nᵏ` summands is at most `‖α‖²`
  have hA : 0 ≤ Real.sqrt (Fintype.card (Fin k → Fin N)) := Real.sqrt_nonneg _
  have hcoef : ∀ α : Covector (Euclid N) k,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin k → Fin N)) * ‖α‖ := by
    intro α
    unfold covectorEuclideanNorm
    calc _ ≤ Real.sqrt (∑ _I : Fin k → Fin N, ‖α‖ ^ 2) := by
          apply Real.sqrt_le_sqrt
          apply Finset.sum_le_sum
          intro I _
          split_ifs
          · have h2 := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin N) ℝ (I i))
            simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
              Real.norm_eq_abs] at h2
            exact sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
          · positivity
      _ = Real.sqrt (Fintype.card (Fin k → Fin N)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- the zero form gives `0 ≤ C`
  have hC : 0 ≤ C := by
    have h := hT 0 1 (fun x => by simp)
    simpa using h
  -- continuity: only the uniform convergence of the forms themselves (`m = 0`) is needed
  have hcont : ∀ (omegaSeq : ℕ → TestFormOn (univ : Set (Euclid N)) k),
      TestFormOnConverges omegaSeq 0 → Tendsto (fun j ↦ T₀ (omegaSeq j)) atTop (𝓝 0) := by
    intro omegaSeq hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
    have hsmall : ∀ δ > 0, ∀ᶠ j in atTop,
        ∀ x, ‖(omegaSeq j : DifferentialForm (Euclid N) k) x‖ ≤ δ := by
      intro δ hδ
      filter_upwards [h0 δ hδ] with j hj
      intro x
      by_cases hx : x ∈ K
      · have hz : iteratedFDeriv ℝ 0
            ((0 : TestFormOn (univ : Set (Euclid N)) k) : DifferentialForm (Euclid N) k) x = 0 := by
          rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
          simp
        have h1 := hj x hx
        rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h1
        exact h1.le
      · rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsupp j hx')), norm_zero]
        exact hδ.le
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCA : 0 ≤ C * Real.sqrt (Fintype.card (Fin k → Fin N)) := mul_nonneg hC hA
    have hδ : 0 < ε / (C * Real.sqrt (Fintype.card (Fin k → Fin N)) + 1) :=
      div_pos hε (by linarith)
    filter_upwards [hsmall _ hδ] with j hj
    have hb := hT (omegaSeq j) _
      (fun x => (hcoef _).trans (mul_le_mul_of_nonneg_left (hj x) hA))
    rw [Real.dist_eq, sub_zero]
    refine hb.trans_lt ?_
    rw [← mul_assoc, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  -- the current, and its mass bound from admissible forms
  refine ⟨⟨T₀, hcont⟩, fun ω => rfl, ?_⟩
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  have h := hT ω 1 hω.2
  rw [mul_one] at h
  exact (le_abs_self _).trans h
/-- **Simon 6.2.3 and 6.2.11**: `spt ∂X ⊆ spt X` for `X ∈ 𝒟_{k+1}(ℝᴺ)`.  If `x ∉ spt X`, then
`x` lies in an open `W` with compact closure on which `X` vanishes.  For a test `k`-form `ω` with
`spt ω ⊆ W`, `∂X(ω) = X(dω) = 0`, as `spt dω ⊆ spt ω ⊆ W`.  So `W` is also a zero region of `∂X`,
and `x ∉ spt ∂X`. -/
theorem Submission.cmcdt_lpo_tk_boundary_support_subset : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), X.boundary.support ⊆ X.support := by
  intro N k X x hx
  -- `x ∈ spt ∂X = univ \ (∂X).zeroRegion`; it remains to show `x ∉ X.zeroRegion`
  refine ⟨hx.1, ?_⟩
  -- step 1: otherwise `x` lies in a zero region `W` of `X`
  rintro ⟨W, ⟨hWo, hWc, hWU, hXW⟩, hxW⟩
  -- steps 2–3: `W` is a zero region of `∂X` as well, so `x ∈ (∂X).zeroRegion`
  refine hx.2 ⟨W, ⟨hWo, hWc, hWU, fun ω hω => ?_⟩, hxW⟩
  -- `∂X(ω) = X(dω)` and `spt dω ⊆ spt ω ⊆ W`
  rw [GeometricCurrentOn.boundary_apply]
  exact hXW (exteriorDerivativeTestOn univ k ω)
    ((tsupport_exteriorDerivative_subset (ω : DifferentialForm (Euclid N) k)).trans hω)
/-- **Locality of a current** (Simon 6.2.11, chapter-06.txt lines 296–303): if every current
`S ∈ 𝒟ₙ(U)` kills the test forms whose support misses `spt S`, then `X ∈ 𝒟ₖ(ℝᴺ)` takes the same
value on test forms `η`, `η'` that agree on an open set `W ⊇ spt X`.  The difference
`ψ = η − η'` vanishes on `W`, so `tsupport ψ` lies in the closed set `Wᶜ`, which misses
`spt X ⊆ W`; hence `X(η) − X(η') = X(ψ) = 0`. -/
theorem Submission.cmcdt_lpo_tk_locality : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η' := by
  intro hVO N k X η η' W hW hXW hηη'
  -- Step 1: `ψ = η − η'` vanishes on `W`, so `tsupport ψ` lies in the closed set `Wᶜ`.
  have hψ : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
      DifferentialForm (Euclid N) k) ⊆ Wᶜ := by
    refine closure_minimal (fun x hx hxW => hx ?_) hW.isClosed_compl
    rw [Submodule.coe_sub, Pi.sub_apply, hηη' x hxW, sub_self]
  -- Step 2: `tsupport ψ ⊆ Wᶜ` misses `spt X ⊆ W`, so `X(ψ) = 0` by the vanishing hypothesis.
  have h0 : X (η - η') = 0 := hVO N k univ X (η - η') (disjoint_compl_left.mono hψ hXW)
  -- Step 3: `X(ψ) = X(η) − X(η')` by linearity of `X`.
  rw [map_sub X.toCurrent] at h0
  exact sub_eq_zero.mp h0
/-- **Smooth approximation of a Lipschitz straight-line homotopy**: for `Λ`-Lipschitz
`F, G : ℝᴺ → ℝᴺ'` and `H(t, x) = F x + t(G x − F x)` on `[0, 1] × K` (`K` compact), take the
mollifications `Fⱼ, Gⱼ` of `F, G` (`|Fⱼ − F|, |Gⱼ − G| ≤ Λ/(j + 1)`, so `|DFⱼ|, |DGⱼ| ≤ Λ`) and
let `Hⱼ` be the `C^∞` interpolation `Hⱼ(t, x) = Fⱼ x + t(Gⱼ x − Fⱼ x)`.  Then
`|∂ₜHⱼ| = |Gⱼ − Fⱼ| ≤ |F − G| + 2Λ/(j + 1)`, `DHⱼ(Jv) = (1 − t) DFⱼ v + t DGⱼ v` for
`t ∈ [0, 1]`, `|DHⱼ| ≤ sup_K |F − G| + 5Λ` on `[0, 1] × K`, and `Hⱼ → H` uniformly on
`[0, 1] × K` as `H − Hⱼ = (1 − t)(F − Fⱼ) + t(G − Gⱼ)` there. -/
theorem Submission.cmcdt_lpoh_smooth_approx : ∀ (N N' : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (Fs Gs : ℕ → Euclid N → Euclid N') (Hs : ℕ → Euclid (N + 1) → Euclid N') (Λ' : ℝ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Gs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Hs j)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ)) ∧ TendstoUniformly Fs F atTop ∧ TendstoUniformly Gs G atTop ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) = Gs j x) ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) = Fs j x) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Gs j) x v) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Fs j) x v) ∧ (∀ (j : ℕ) (t : ℝ) (x : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ (x v : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ Λ') ∧ TendstoUniformlyOn Hs H atTop {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
  intro N N' Λ F G H K hF hG hK hHK
  -- Step 1: mollify `F, G`; for each `j` interpolate `Fⱼ, Gⱼ` by the `C^∞` map `Hⱼ`
  obtain ⟨Fs, hFs, hFL, hFd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ F hF
  obtain ⟨Gs, hGs, hGL, hGd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ G hG
  choose Hs hHs hHι hHe hHJ hHn using
    fun j => Submission.cmcdt_lpoh_interp_calculus N N' (Fs j) (Gs j) (hFs j) (hGs j)
  -- `M` bounds `|F − G|` on the compact `K`
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ K, dist (F x) (G x) ≤ M := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      ((hF.continuous.dist hG.continuous).continuousOn)
    exact ⟨M, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x hx)⟩
  -- Step 2: `Λ`-Lipschitz maps have `|DFⱼ|, |DGⱼ| ≤ Λ`
  have hDF : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hFL j)
  have hDG : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hGL j)
  -- Step 3: `Λ/(j + 1) → 0`, so a uniform error `Λ/(j + 1)` gives uniform convergence
  have hsmall : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Λ : ℝ)
    rw [mul_zero] at h
    refine h.congr (fun j => ?_)
    rw [mul_one_div]
  have hunif : ∀ (Es : ℕ → Euclid N → Euclid N') (E : Euclid N → Euclid N'),
      (∀ (j : ℕ) (x : Euclid N), dist (Es j x) (E x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) →
      TendstoUniformly Es E atTop := by
    intro Es E hE
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_comm]
    exact (hE j x).trans_lt hj
  -- Step 6: `|Gⱼ − Fⱼ| ≤ |F − G| + 2Λ/(j + 1)`
  have hGF : ∀ (j : ℕ) (x : Euclid N),
      ‖Gs j x - Fs j x‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by
    intro j x
    rw [← dist_eq_norm]
    calc dist (Gs j x) (Fs j x) ≤ dist (Gs j x) (G x) + dist (G x) (F x) + dist (F x) (Fs j x) :=
          dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) / ((j : ℝ) + 1) + dist (F x) (G x) + (Λ : ℝ) / ((j : ℝ) + 1) := by
          gcongr
          · exact hGd j x
          · rw [dist_comm]
          · rw [dist_comm]; exact hFd j x
      _ = dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by ring
  refine ⟨Fs, Gs, Hs, M + 5 * (Λ : ℝ), hFs, hGs, hHs, hDF, hDG, hunif Fs F hFd, hunif Gs G hGd,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Steps 4, 5: end values and end derivatives at `t = 1, 0`
  · intro j x; rw [hHι]; simp
  · intro j x; rw [hHι]; simp
  · intro j x v; rw [hHJ]; simp
  · intro j x v; rw [hHJ]; simp
  -- Step 7: `DHⱼ e₀ = Gⱼ − Fⱼ`
  · intro j t x; rw [hHe]; exact hGF j x
  -- Step 8: `DHⱼ(Jv) = (1 − t) DFⱼ v + t DGⱼ v` has norm `≤ Λ|v|` for `t ∈ [0, 1]`
  · intro j t ht x v
    rw [hHJ]
    have h1 : fderiv ℝ (Fs j) x v + t • (fderiv ℝ (Gs j) x v - fderiv ℝ (Fs j) x v) =
        (1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have hF' : ‖fderiv ℝ (Fs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDF j x)
    have hG' : ‖fderiv ℝ (Gs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDG j x)
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v‖
        ≤ ‖(1 - t) • fderiv ℝ (Fs j) x v‖ + ‖t • fderiv ℝ (Gs j) x v‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ (Fs j) x v‖ + t * ‖fderiv ℝ (Gs j) x v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) * ‖v‖) + t * ((Λ : ℝ) * ‖v‖) := by gcongr
      _ = (Λ : ℝ) * ‖v‖ := by ring
  -- Step 9: `|DHⱼ| ≤ (M + 2Λ) + Λ + 1 · (Λ + Λ) = M + 5Λ` on `[0, 1] × K`
  · intro j t ht x hx
    refine (hHn j t x).trans ?_
    have h2 : 2 * (Λ : ℝ) / ((j : ℝ) + 1) ≤ 2 * (Λ : ℝ) :=
      div_le_self (by positivity) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    have habs : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc ‖Gs j x - Fs j x‖ + ‖fderiv ℝ (Fs j) x‖ + |t| * (‖fderiv ℝ (Gs j) x‖ + ‖fderiv ℝ (Fs j) x‖)
        ≤ (M + 2 * (Λ : ℝ)) + (Λ : ℝ) + 1 * ((Λ : ℝ) + (Λ : ℝ)) := by
          gcongr
          · exact (hGF j x).trans (by linarith [hM x hx])
          · exact hDF j x
          · exact hDG j x
          · exact hDF j x
      _ = M + 5 * (Λ : ℝ) := by ring
  -- Step 10: `H − Hⱼ = (1 − t)(F − Fⱼ) + t(G − Gⱼ)` has norm `≤ Λ/(j + 1)` on `[0, 1] × K`
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj y hy
    obtain ⟨t, ht, x, hx, rfl⟩ := hy
    rw [hHK x hx t ht, hHι, dist_eq_norm]
    have h1 : F x + t • (G x - F x) - (Fs j x + t • (Gs j x - Fs j x)) =
        (1 - t) • (F x - Fs j x) + t • (G x - Gs j x) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • (F x - Fs j x) + t • (G x - Gs j x)‖
        ≤ ‖(1 - t) • (F x - Fs j x)‖ + ‖t • (G x - Gs j x)‖ := norm_add_le _ _
      _ = (1 - t) * ‖F x - Fs j x‖ + t * ‖G x - Gs j x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) / ((j : ℝ) + 1)) + t * ((Λ : ℝ) / ((j : ℝ) + 1)) := by
          gcongr
          · rw [← dist_eq_norm, dist_comm]; exact hFd j x
          · rw [← dist_eq_norm, dist_comm]; exact hGd j x
      _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring
      _ < ε := hj
/-- **Covector bound for the `e₀`-slice of a pulled-back covector.**  Given the bounds
(L1) `|β ∘ A| ≤ ‖A‖ᵏ |β|` and (L2) `|β(v, ·)| ≤ ‖v‖ |β|` for the Euclidean coefficient norm
`|·| = covectorEuclideanNorm`, let `φ(v₁, …, v_k) = (D^#γ)(e₀, Jv₁, …, Jv_k)` with
`J v = (0, v)`, `‖D e₀‖ ≤ a` and `‖D (J v)‖ ≤ b ‖v‖`.  Then `φ = γ(D e₀, ·) ∘ (D ∘ J)`, so
`|φ| ≤ ‖D ∘ J‖ᵏ ‖D e₀‖ |γ| ≤ bᵏ a |γ|`. -/
theorem Submission.cmcdt_lpoh_phi_bound : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (γ : Covector (Euclid N') (k + 1)) (D : Euclid (N + 1) →L[ℝ] Euclid N') (φ : Covector (Euclid N) k) (a b : ℝ), 0 ≤ b → ‖D (EuclideanSpace.single 0 1)‖ ≤ a → (∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ b * ‖v‖) → (∀ v : Fin k → Euclid N, φ v = (γ.compContinuousLinearMap D) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → covectorEuclideanNorm φ ≤ b ^ k * a * covectorEuclideanNorm γ := by
  intro hL1 hL2 N N' k γ D φ a b hb hDe hDJ hφ
  /- Step 1: `J v = (0, v)` is linear (check coordinatewise), hence continuous linear. -/
  let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro r v
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jl
  /- Step 2: `φ = γ(D e₀, ·) ∘ (D ∘ J)`, since `D ∘ (e₀, Jv) = (D e₀, D (J v))`. -/
  have hφeq : φ = (γ.curryLeft (D (EuclideanSpace.single 0 1))).compContinuousLinearMap
      (D.comp J) := by
    ext v
    rw [hφ v]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousLinearMap.coe_comp]
    congr 1
    rw [Fin.comp_cons]
    rfl
  /- Step 3: `‖D ∘ J‖ ≤ b`. -/
  have hA : ‖D.comp J‖ ≤ b := ContinuousLinearMap.opNorm_le_bound _ hb hDJ
  /- Step 4: (L1) for `D ∘ J`, then (L2) for `D e₀`. -/
  rw [hφeq]
  calc covectorEuclideanNorm ((γ.curryLeft (D (EuclideanSpace.single 0 1))).compContinuousLinearMap
        (D.comp J))
      ≤ ‖D.comp J‖ ^ k * covectorEuclideanNorm (γ.curryLeft (D (EuclideanSpace.single 0 1))) :=
        hL1 N N' k (D.comp J) _
    _ ≤ b ^ k * (‖D (EuclideanSpace.single 0 1)‖ * covectorEuclideanNorm γ) := by
        gcongr
        · exact covectorEuclideanNorm_nonneg _
        · exact hL2 N' k _ γ
    _ ≤ b ^ k * (a * covectorEuclideanNorm γ) := by
        gcongr
        exact covectorEuclideanNorm_nonneg γ
    _ = b ^ k * a * covectorEuclideanNorm γ := by ring
/-- **Current toolkit** (Simon 6.2.1–2.12), for currents in `ℝᴺ`.  Assume (VO): a current
kills every test form supported off its support; and (REP): a current of locally finite mass
is integration against a measure `μ` with `M_W(T) = μ(W)` and a pointwise bounded `ξ`.  Then:
(MSB) `|X(ψ)| ≤ c M(X)` if `M(X) < ∞` and `|ψ| ≤ c` on `spt X`; (BC) a linear `T₀` with
`|T₀(ω)| ≤ C c` whenever `|ω| ≤ c` is a current of mass `≤ C`; (SB) `spt ∂X ⊆ spt X`;
(LOC) `X(η) = X(η')` if `η = η'` on an open set containing `spt X`.  The four parts are
independent: (MSB) uses (VO) and (REP), (LOC) uses only (VO), and (BC), (SB) use neither. -/
theorem Submission.cmcdt_lpo_current_toolkit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) ∧ (∀ (N k : ℕ) (T₀ : TestFormOn (univ : Set (Euclid N)) k →ₗ[ℝ] ℝ) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T₀ ω| ≤ C * c) → ∃ T : GeometricCurrentOn (univ : Set (Euclid N)) k, (∀ ω, T ω = T₀ ω) ∧ T.mass ≤ ENNReal.ofReal C) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), X.boundary.support ⊆ X.support) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η' :=
  fun hVO hREP => ⟨Submission.cmcdt_lpo_tk_mass_support_bound hVO hREP,
    Submission.cmcdt_lpo_tk_bounded_current, Submission.cmcdt_lpo_tk_boundary_support_subset,
    Submission.cmcdt_lpo_tk_locality hVO⟩

/-- Simon 6.2.25–6.2.27 for smooth maps (the estimate in the proof of 6.2.28): if `F, G` are
`C^∞`, `‖DF‖, ‖DG‖ ≤ Λ` and `|F − G| ≤ δ` on `spt X`, then
`|X(G^#ω) − X(F^#ω)| ≤ δ (Λᵏ M(X) sup |dω| + Λ^{k−1} M(∂X) sup |ω|)`.  The affine homotopy
`H(t, x) = F(x) + t (G(x) − F(x))` is cut off near `[0, 1] × spt X`, giving `β = H^#ω` there.  The
cylinder homotopy formula gives `X(η_G) − X(η_F) = X(S_{dβ}) + ∂X(S_β)`, and over `spt X` the
slice integrands are `dω(H)(G − F, A_t ·)` and `ω(H)(G − F, A_t ·)`, `A_t = DF + t (DG − DF)`,
`‖A_t‖ ≤ Λ`. -/
theorem Submission.cmcdt_lpo_smooth_homotopy_estimate : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (N N' k : ℕ) (Λ δ a b : ℝ) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηF ηG : TestFormOn (univ : Set (Euclid N)) k), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ‖fderiv ℝ F x‖ ≤ Λ ∧ ‖fderiv ℝ G x‖ ≤ Λ) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) y) ≤ a) → (∀ y, covectorEuclideanNorm (exteriorDerivative (ω : DifferentialForm (Euclid N') k) y) ≤ b) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηF : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) → (∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηG : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → |X ηG - X ηF| ≤ δ * (Λ ^ k * X.mass.toReal * b + Λ ^ (k - 1) * (boundaryMassOn X univ).toReal * a) := by
  intro hVO hREP hLB N N' k Λ δ a b F G X ω ηF ηG hF hG hXc hXm hXbm hD hFG ha hb hηF hηG
  obtain ⟨hMSB, -, hSB, hLOC⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  obtain ⟨hL1, hL2, -⟩ := hLB
  obtain ⟨WF, hWFo, hXWF, hWF⟩ := hηF
  obtain ⟨WG, hWGo, hXWG, hWG⟩ := hηG
  obtain ⟨H, hH, hHval, hHe, hHJ⟩ := Submission.cmcdt_lpo_she_affine_homotopy N N' F G hF hG
  -- cut off `H^#ω` near the compact set `ι([0, 1] × spt X)`, `ι(t, x) = (t, x)`
  have hι : Continuous fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1)) := by
    fun_prop
  obtain ⟨β, W', hW'o, hKW', hβ, hdβ⟩ := Submission.cmcdt_lpo_cutoff_pullback (N + 1) N' k H ω
    ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
      (Icc (0 : ℝ) 1 ×ˢ X.support)) hH ((isCompact_Icc.prod hXc).image hι)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ X.support,
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ W' :=
    fun t ht x hx => hKW' ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  -- `DH(ι(t, x))` maps `e₀` to `G x − F x` and `ι(0, v)` to `A_t v`, `A_t = DF + t (DG − DF)`
  have hDH : ∀ (m : ℕ) (t : ℝ) (x : Euclid N) (v : Fin m → Euclid N),
      ⇑(fderiv ℝ H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) ∘
          (Fin.cons (EuclideanSpace.single 0 1)
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :
            Fin (m + 1) → Euclid (N + 1)) =
        Fin.cons (G x - F x) fun i => (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) (v i) := by
    intro m t x v
    rw [Fin.comp_cons, hHe]
    congr 1
    funext i
    simp only [Function.comp_apply, hHJ, add_apply, smul_apply, sub_apply]
  have hA : ∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖ ≤ Λ := by
    intro x hx t ht
    obtain ⟨hDF, hDG⟩ := hD x hx
    have h1t : 0 ≤ 1 - t := sub_nonneg.2 ht.2
    calc ‖fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)‖
        = ‖(1 - t) • fderiv ℝ F x + t • fderiv ℝ G x‖ := by congr 1; module
      _ ≤ ‖(1 - t) • fderiv ℝ F x‖ + ‖t • fderiv ℝ G x‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ F x‖ + t * ‖fderiv ℝ G x‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg h1t, Real.norm_of_nonneg ht.1]
      _ ≤ (1 - t) * Λ + t * Λ :=
        add_le_add (mul_le_mul_of_nonneg_left hDF h1t) (mul_le_mul_of_nonneg_left hDG ht.1)
      _ = Λ := by ring
  -- over `x ∈ spt X`, the slice of a form `σ = H^#γ` (near `ι([0, 1] × spt X)`) has norm
  -- `≤ Λᵐ δ sup |γ|` (Simon 6.2.27)
  have hslice : ∀ (m : ℕ) (σ : DifferentialForm (Euclid (N + 1)) (m + 1))
      (γ : DifferentialForm (Euclid N') (m + 1)) (c : ℝ) (α : DifferentialForm (Euclid N) m),
      Continuous σ → (∀ y ∈ W', σ y = (γ (H y)).compContinuousLinearMap (fderiv ℝ H y)) →
      (∀ y, covectorEuclideanNorm (γ y) ≤ c) →
      (∀ (x : Euclid N) (v : Fin m → Euclid N), α x v = ∫ t in (0 : ℝ)..1,
        σ (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
          (Fin.cons (EuclideanSpace.single 0 1)
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) →
      ∀ x ∈ X.support, covectorEuclideanNorm (α x) ≤ Λ ^ m * δ * c := by
    intro m σ γ c α hσ hσW hγ hα x hx
    refine Submission.cmcdt_lpo_she_slice_bound hL1 hL2 N N' m σ x (α x) Λ δ c hσ (hα x)
      fun t ht => ⟨γ (H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))), G x - F x,
        fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x), hA x hx t ht, ?_, hγ _, fun v => ?_⟩
    · rw [← dist_eq_norm, dist_comm]
      exact hFG x hx
    · rw [hσW _ (hmem t ht x hx), ContinuousAlternatingMap.compContinuousLinearMap_apply, hDH]
  -- the end slices of `β` are `G^#ω = η_G` and `F^#ω = η_F` near `spt X`
  obtain ⟨V, hVo, hXV, hV⟩ : ∃ V : Set (Euclid N), IsOpen V ∧ X.support ⊆ V ∧
      ∀ x ∈ V, ∀ v : Fin k → Euclid N,
        (ηG : DifferentialForm (Euclid N) k) x v = (β : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) ∧
          (ηF : DifferentialForm (Euclid N) k) x v = (β : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
    have hs : ∀ s : ℝ, Continuous fun x : Euclid N =>
        (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)) := fun s => by fun_prop
    refine ⟨{x | (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)) : Euclid (N + 1)) ∈ W'} ∩
        {x | (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x)) : Euclid (N + 1)) ∈ W'} ∩ WF ∩ WG,
      (((hW'o.preimage (hs 0)).inter (hW'o.preimage (hs 1))).inter hWFo).inter hWGo,
      fun x hx => ⟨⟨⟨hmem 0 ⟨le_rfl, zero_le_one⟩ x hx, hmem 1 ⟨zero_le_one, le_rfl⟩ x hx⟩,
        hXWF hx⟩, hXWG hx⟩, ?_⟩
    rintro x ⟨⟨⟨h0, h1⟩, hxF⟩, hxG⟩ v
    constructor
    · rw [hWG x hxG, hβ _ h1]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hHval,
        one_smul, add_sub_cancel, hHJ]
    · rw [hWF x hxF, hβ _ h0]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hHval,
        zero_smul, add_zero, hHJ]
  cases k with
  | zero =>
    obtain ⟨η, hηf, hid⟩ :=
      (Submission.cmcdt_lpo_she_cylinder_homotopy hLOC).2 N X β ηF ηG V hVo hXV hV
    have hη : |X η| ≤ Λ ^ 0 * δ * b * X.mass.toReal :=
      hMSB N 0 X η _ hXm (hslice 0 (exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0))
        (exteriorDerivative (ω : DifferentialForm (Euclid N') 0)) b
        (η : DifferentialForm (Euclid N) 0)
        (ContDiff.continuous (exteriorDerivative_isTestForm β.2.1).1) hdβ hb hηf)
    have hbm : boundaryMassOn X univ = 0 := rfl
    rw [hid, hbm, ENNReal.toReal_zero]
    calc |X η| ≤ Λ ^ 0 * δ * b * X.mass.toReal := hη
      _ = δ * (Λ ^ 0 * X.mass.toReal * b + Λ ^ (0 - 1) * 0 * a) := by ring
  | succ k =>
    obtain ⟨η, θ, hηf, hθf, hid⟩ :=
      (Submission.cmcdt_lpo_she_cylinder_homotopy hLOC).1 N k X β ηF ηG V hVo hXV hV
    have hη : |X η| ≤ Λ ^ (k + 1) * δ * b * X.mass.toReal :=
      hMSB N (k + 1) X η _ hXm
        (hslice (k + 1) (exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)))
          (exteriorDerivative (ω : DifferentialForm (Euclid N') (k + 1))) b
          (η : DifferentialForm (Euclid N) (k + 1))
          (ContDiff.continuous (exteriorDerivative_isTestForm β.2.1).1) hdβ hb hηf)
    -- `spt ∂X ⊆ spt X`, and `M(∂X) = boundaryMassOn X univ`
    have hbm : boundaryMassOn X univ = X.boundary.mass := rfl
    have hθ : |X.boundary θ| ≤ Λ ^ k * δ * a * X.boundary.mass.toReal :=
      hMSB N k X.boundary θ _ (hbm ▸ hXbm) fun x hx =>
        hslice k (β : DifferentialForm (Euclid (N + 1)) (k + 1))
          (ω : DifferentialForm (Euclid N') (k + 1)) a (θ : DifferentialForm (Euclid N) k)
          (ContDiff.continuous β.2.1.1) hβ ha hθf x (hSB N k X hx)
    rw [hid, hbm, Nat.add_sub_cancel]
    calc |X η + X.boundary θ| ≤ |X η| + |X.boundary θ| := abs_add_le _ _
      _ ≤ Λ ^ (k + 1) * δ * b * X.mass.toReal + Λ ^ k * δ * a * X.boundary.mass.toReal :=
        add_le_add hη hθ
      _ = δ * (Λ ^ (k + 1) * X.mass.toReal * b + Λ ^ k * X.boundary.mass.toReal * a) := by ring

/-- Simon 6.2.29, existence of the limit: for `X ∈ 𝒟ₖ(ℝᴺ)` with `spt X` compact and
`M(X), M(∂X) < ∞`, a Lipschitz `F : ℝᴺ → ℝᴺ'` and `ω ∈ 𝒟ᵏ(ℝᴺ')`, the evaluations `X(Fⱼ^#ω)`
converge to one limit `L` for every sequence of `C^∞` maps `Fⱼ → F` (uniformly on `spt X`, with
`|DFⱼ|` bounded there).  By the homotopy estimate 2.27, the evaluations on the mollified
approximants `Gᵢ` are Cauchy; comparing any admissible `Fⱼ` with `Gᵢ` gives the same limit. -/
theorem Submission.cmcdt_lpo_pf_pointwise_limit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ L : ℝ, ∀ (Λ' : ℝ) (Fs : ℕ → Euclid N → Euclid N') (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 L) := by
  intro hVO hREP hLB N N' k Λ F X ω hF hX1 hX2 hX3
  have hE := Submission.cmcdt_lpo_smooth_homotopy_estimate hVO hREP hLB
  -- step 1: bounds `a`, `b` for `|ω|`, `|dω|`; step 2: mollified `Gᵢ` and `θᵢ = Gᵢ^#ω` near `spt X`
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := Submission.cmcdt_lpo_pf_form_bounds N' k ω
  obtain ⟨G, hG, -, hDG, hdistG, -, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨θ, hθs⟩ := hηG k ω
  have hθ : ∀ i, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ i : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G i x)).compContinuousLinearMap
          (fderiv ℝ (G i) x) := fun i => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs i
    exact ⟨W, hW, hKW, h1⟩
  let Cf : ℝ → ℝ := fun μ =>
    μ ^ k * X.mass.toReal * b + μ ^ (k - 1) * (boundaryMassOn X univ).toReal * a
  have ha0 : 0 ≤ a := (covectorEuclideanNorm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (covectorEuclideanNorm_nonneg _).trans (hb 0)
  have hC0 : ∀ μ : ℝ, 0 ≤ μ → 0 ≤ Cf μ := fun μ hμ => by
    simp only [Cf]
    positivity
  have hΛ0 : (0 : ℝ) ≤ Λ := Λ.2
  have hrate : Tendsto (fun i : ℕ => (Λ : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
    rw [mul_zero] at this
    exact this.congr (fun j => mul_one_div _ _)
  -- step 3: the homotopy estimate makes `X(θᵢ)` Cauchy; `L` is its limit
  have hcauchy : CauchySeq (fun i => X (θ i)) := by
    refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => 2 * ((Λ : ℝ) / ((n : ℝ) + 1)) * Cf Λ) ?_ ?_
    · intro n m M hn hm
      rw [Real.dist_eq, abs_sub_comm]
      have hest := hE N N' k Λ ((Λ : ℝ) / ((n : ℝ) + 1) + (Λ : ℝ) / ((m : ℝ) + 1)) a b (G n) (G m)
        X ω (θ n) (θ m) (hG n) (hG m) hX1 hX2 hX3 (fun x _ => ⟨hDG n x, hDG m x⟩)
        (fun x _ => (dist_triangle _ (F x) _).trans
          (add_le_add (hdistG n x) (by rw [dist_comm]; exact hdistG m x))) ha hb (hθ n) (hθ m)
      refine hest.trans (mul_le_mul_of_nonneg_right ?_ (hC0 _ hΛ0))
      have h1 : (Λ : ℝ) / ((n : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΛ0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      have h2 : (Λ : ℝ) / ((m : ℝ) + 1) ≤ (Λ : ℝ) / ((M : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΛ0 (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
      linarith
    · have := (hrate.const_mul 2).mul_const (Cf Λ)
      simpa using this
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- step 4: any admissible `Fⱼ`, `ηⱼ` give `|X(ηⱼ) − L| ≤ ε'·C(Λ'') < ε` for large `j`
  refine ⟨L, fun Λ' Fs ηs hFs hD hU hη => ?_⟩
  set Λ'' : ℝ := max (Λ : ℝ) Λ'
  have hΛ'' : 0 ≤ Λ'' := le_trans hΛ0 (le_max_left _ _)
  have hC'' := hC0 Λ'' hΛ''
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' : ℝ := ε / (Cf Λ'' + 1) with hε'eq
  have hε'pos : 0 < ε' := div_pos hε (by linarith)
  rw [Metric.tendstoUniformlyOn_iff] at hU
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 (hU ε' hε'pos)
  refine ⟨j₀, fun j hj => ?_⟩
  have hbound : ∀ i : ℕ, |X (ηs j) - X (θ i)| ≤ ((Λ : ℝ) / ((i : ℝ) + 1) + ε') * Cf Λ'' := by
    intro i
    exact hE N N' k Λ'' _ a b (G i) (Fs j) X ω (θ i) (ηs j) (hG i) (hFs j) hX1 hX2 hX3
      (fun x hx => ⟨(hDG i x).trans (le_max_left _ _), (hD j x hx).trans (le_max_right _ _)⟩)
      (fun x hx => (dist_triangle _ (F x) _).trans (add_le_add (hdistG i x) (hj₀ j hj x hx).le))
      ha hb (hθ i) (hη j)
  have hlim : |X (ηs j) - L| ≤ ε' * Cf Λ'' := by
    have h1 : Tendsto (fun i => |X (ηs j) - X (θ i)|) atTop (𝓝 |X (ηs j) - L|) :=
      (tendsto_const_nhds.sub hL).abs
    have h2 : Tendsto (fun i : ℕ => ((Λ : ℝ) / ((i : ℝ) + 1) + ε') * Cf Λ'') atTop
        (𝓝 ((0 + ε') * Cf Λ'')) := (hrate.add_const ε').mul_const _
    rw [zero_add] at h2
    exact le_of_tendsto_of_tendsto' h1 h2 hbound
  rw [Real.dist_eq]
  calc |X (ηs j) - L| ≤ ε' * Cf Λ'' := hlim
    _ < ε := by
      rw [hε'eq, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- The Lipschitz push-forward of a normal current is a current (Simon 6.2.28–2.29).  For every
`ω`, `L ω` is the common limit of `X(ηⱼ)` over admissible data for `ω`
(`cmcdt_lpo_pf_pointwise_limit`).  The common approximants `Gⱼ` and forms `θⱼ^ω = Gⱼ^#ω` near
`spt X` of `cmcdt_lpo_pf_approx_data` are admissible for every `ω`; sums and scalar multiples of
them are admissible for `ω₁ + ω₂` and `c • ω`, so `L` is linear by uniqueness of limits.  By (L1)
and the mass–support bound, `|L ω| ≤ Λᵏ M(X) c` whenever `|ω| ≤ c`, so `L` is a current `T`
(`cmcdt_lpo_current_toolkit`), and `X(ηⱼ) → T(ω)` for all admissible data. -/
theorem Submission.cmcdt_lpo_pf_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ T : GeometricCurrentOn (univ : Set (Euclid N')) k, ∀ (Λ' : ℝ) (Fs : ℕ → Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (T ω)) := by
  intro hVO hREP hLB N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨hMSB, hBC, -, -⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  have hL1 := hLB.1
  -- the common limit `L ω` of `X(ηⱼ)` over all admissible data for `ω`
  choose L hL using fun ω =>
    Submission.cmcdt_lpo_pf_pointwise_limit hVO hREP hLB N N' k Λ F X ω hF hX1 hX2 hX3
  -- common approximants `Gⱼ` and pulled-back forms `θⱼ^ω`, admissible for every `ω`
  obtain ⟨G, hG, -, hDG, -, hUG, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  choose θ hθs using hηG k
  have hθ : ∀ ω j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ ω j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G j x)).compContinuousLinearMap
          (fderiv ℝ (G j) x) := fun ω j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs ω j
    exact ⟨W, hW, hKW, h1⟩
  have hconv : ∀ ω, Tendsto (fun j => X (θ ω j)) atTop (𝓝 (L ω)) := fun ω =>
    hL ω Λ G (θ ω) hG (fun j x _ => hDG j x) hUG.tendstoUniformlyOn (hθ ω)
  -- additivity: `θⱼ^{ω₁} + θⱼ^{ω₂}` is admissible for `ω₁ + ω₂`
  have hadd : ∀ ω₁ ω₂, L (ω₁ + ω₂) = L ω₁ + L ω₂ := by
    intro ω₁ ω₂
    have hdata : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        ((θ ω₁ j + θ ω₂ j : TestFormOn (univ : Set (Euclid N)) k) :
          DifferentialForm (Euclid N) k) x =
        (((ω₁ + ω₂ : TestFormOn (univ : Set (Euclid N')) k) : DifferentialForm (Euclid N') k)
          (G j x)).compContinuousLinearMap (fderiv ℝ (G j) x) := by
      intro j
      obtain ⟨W₁, hW₁, hK₁, h₁⟩ := hθ ω₁ j
      obtain ⟨W₂, hW₂, hK₂, h₂⟩ := hθ ω₂ j
      refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, subset_inter hK₁ hK₂, fun x hx => ?_⟩
      rw [Submodule.coe_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, h₁ x hx.1, h₂ x hx.2]
      ext v
      simp
    have h1 := hL (ω₁ + ω₂) Λ G (fun j => θ ω₁ j + θ ω₂ j) hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn hdata
    have h2 : Tendsto (fun j => X (θ ω₁ j + θ ω₂ j)) atTop (𝓝 (L ω₁ + L ω₂)) := by
      have := (hconv ω₁).add (hconv ω₂)
      refine this.congr (fun j => ?_)
      exact (X.toCurrent.map_add _ _).symm
    exact tendsto_nhds_unique h1 h2
  -- homogeneity: `c • θⱼ^ω` is admissible for `c • ω`
  have hsmul : ∀ (c : ℝ) ω, L (c • ω) = c * L ω := by
    intro c ω
    have hdata : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        ((c • θ ω j : TestFormOn (univ : Set (Euclid N)) k) :
          DifferentialForm (Euclid N) k) x =
        (((c • ω : TestFormOn (univ : Set (Euclid N')) k) : DifferentialForm (Euclid N') k)
          (G j x)).compContinuousLinearMap (fderiv ℝ (G j) x) := by
      intro j
      obtain ⟨W, hW, hK, h⟩ := hθ ω j
      refine ⟨W, hW, hK, fun x hx => ?_⟩
      rw [Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, h x hx]
      ext v
      simp
    have h1 := hL (c • ω) Λ G (fun j => c • θ ω j) hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn hdata
    have h2 : Tendsto (fun j => X (c • θ ω j)) atTop (𝓝 (c * L ω)) := by
      have := (hconv ω).const_mul c
      refine this.congr (fun j => ?_)
      exact (X.toCurrent.map_smul c _).symm
    exact tendsto_nhds_unique h1 h2
  let T₀ : TestFormOn (univ : Set (Euclid N')) k →ₗ[ℝ] ℝ :=
    { toFun := L
      map_add' := hadd
      map_smul' := hsmul }
  -- `|T₀ ω| ≤ Λᵏ M(X) c` whenever `|ω| ≤ c`, by (L1) and the mass–support bound
  have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid N')) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') k) x) ≤ c) →
        |T₀ ω| ≤ ((Λ : ℝ) ^ k * X.mass.toReal) * c := by
    intro ω c hc
    have hj : ∀ j, |X (θ ω j)| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal := by
      intro j
      apply hMSB N k X (θ ω j) ((Λ : ℝ) ^ k * c) hX2
      intro x hx
      obtain ⟨W, -, hKW, h⟩ := hθ ω j
      rw [h x (hKW hx)]
      refine (hL1 N N' k (fderiv ℝ (G j) x) _).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDG j x) k) (hc _)
        (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.2 k)
    have hlim : |L ω| ≤ (Λ : ℝ) ^ k * c * X.mass.toReal :=
      le_of_tendsto' (hconv ω).abs hj
    show |L ω| ≤ _
    linarith
  -- the bounded linear functional `T₀` is a current `T`, with `T ω = L ω`
  obtain ⟨T, hT, -⟩ := hBC N' k T₀ ((Λ : ℝ) ^ k * X.mass.toReal) hbound
  refine ⟨T, fun Λ' Fs ω ηs hFs hD hU hη => ?_⟩
  rw [hT ω]
  exact hL ω Λ' Fs ηs hFs hD hU hη
/-- **Mass bound and support of the Lipschitz push-forward** (Simon 6.2.29).  Assume (VO), (REP)
and the covector bounds, and let `lpush` be any family satisfying the approximation property (PA):
`X(G_j^# ω) → lpush(F, X)(ω)` along smooth `G_j → F` uniformly on `spt X` with bounded derivatives.
Then `M(lpush(F, X)) ≤ Λᵏ M(X)` and `spt lpush(F, X) ⊆ F(spt X)` for `Λ`-Lipschitz `F` and
compactly supported `X` with `M(X) + M(∂X) < ∞`.  The approximations come from
`cmcdt_lpo_pf_approx_data`; locality (LOC) and the support mass bound (MSB) are derived from (VO)
and (REP) as in Simon 6.2.7–2.12. -/
theorem Submission.cmcdt_lpo_pf_mass_support : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support := by
  intro hVO hREP hLB lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  -- (LOC), Simon 6.2.11 with (VO): `X(η) = X(η')` if `η = η'` on an open set containing `spt X`.
  have hLOC : ∀ (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W →
      X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x =
        (η' : DifferentialForm (Euclid N) k) x) → X η = X η' := by
    intro η η' W hW hXW hηη'
    have hsub : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
        DifferentialForm (Euclid N) k) ⊆ Wᶜ := by
      refine closure_minimal (fun x hx hxW => hx ?_) hW.isClosed_compl
      simp [hηη' x hxW]
    have h0 := hVO N k univ X (η - η') (Disjoint.mono hsub hXW disjoint_compl_left)
    rw [show X (η - η') = X η - X η' from map_sub X.toCurrent η η'] at h0
    linarith
  -- (MSB), Simon 6.2.7–2.12 with (VO), (REP): `|X(ψ)| ≤ c M(X)` if `|ψ| ≤ c` on `spt X`.
  have hMSB : ∀ (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ),
      (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) →
        |X ψ| ≤ c * X.mass.toReal := by
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hXμ, -⟩ := hREP N k univ X isOpen_univ
      (fun W _ _ => lt_of_le_of_lt (X.massOn_mono (subset_univ W)) hX2)
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨hμ ▸ hX2⟩
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, hω, rfl⟩
      dsimp only
      rw [hVO N k univ X ω (disjoint_left.2 fun x hx hxs => hxs.2 (hω.1 hx)),
        ENNReal.ofReal_zero]
    intro ψ c hψ
    have hae : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
      rw [ae_iff]
      refine measure_mono_null (fun x hx => ?_) hZ
      by_contra hxZ
      exact hx ((Real.norm_eq_abs _).le.trans
        ((hξ x _).trans (hψ x (mem_sdiff_of_mem (mem_univ x) hxZ))))
    have h := norm_integral_le_of_norm_le_const hae
    rwa [Real.norm_eq_abs, ← hXμ ψ, measureReal_def, hμ] at h
  have hL1 := hLB.1
  obtain ⟨G, hG, -, hDG, hdistG, hUG, hηG⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  choose θ hθs using hηG k
  have hθ : ∀ ω j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (θ ω j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (G j x)).compContinuousLinearMap
          (fderiv ℝ (G j) x) := fun ω j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hθs ω j
    exact ⟨W, hW, hKW, h1⟩
  have hconv : ∀ ω, Tendsto (fun j => X (θ ω j)) atTop (𝓝 (lpush N N' k F X ω)) := fun ω =>
    hPA N N' k Λ Λ F G X ω (θ ω) hF hX1 hX2 hX3 hG (fun j x _ => hDG j x)
      hUG.tendstoUniformlyOn (hθ ω)
  have hrate : Tendsto (fun i : ℕ => (Λ : ℝ) / ((i : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Λ : ℝ)
    rw [mul_zero] at this
    exact this.congr (fun j => mul_one_div _ _)
  refine ⟨?_, ?_⟩
  · apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    have hj : ∀ j, |X (θ ω j)| ≤ (Λ : ℝ) ^ k * 1 * X.mass.toReal := by
      intro j
      apply hMSB (θ ω j) ((Λ : ℝ) ^ k * 1)
      intro x hx
      obtain ⟨W, -, hKW, h⟩ := hθ ω j
      rw [h x (hKW hx)]
      refine (hL1 N N' k (fderiv ℝ (G j) x) _).trans ?_
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hDG j x) k) (hω.2 _)
        (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.2 k)
    have hlim : lpush N N' k F X ω ≤ (Λ : ℝ) ^ k * 1 * X.mass.toReal :=
      (le_abs_self _).trans (le_of_tendsto' (hconv ω).abs hj)
    dsimp only
    calc ENNReal.ofReal (lpush N N' k F X ω)
        ≤ ENNReal.ofReal ((Λ : ℝ) ^ k * 1 * X.mass.toReal) := ENNReal.ofReal_le_ofReal hlim
      _ = ENNReal.ofReal (((Λ ^ k : NNReal) : ℝ) * X.mass.toReal) := by
        rw [NNReal.coe_pow, mul_one]
      _ = ((Λ ^ k : NNReal) : ℝ≥0∞) * X.mass := by
        rw [ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_toReal hX2.ne]
      _ = (Λ : ℝ≥0∞) ^ k * X.mass := by
        rw [ENNReal.coe_pow]
  · rintro y ⟨-, hy⟩
    by_contra hyF
    apply hy
    by_cases hXe : X.support = ∅
    · have hX0 : ∀ η : TestFormOn (univ : Set (Euclid N)) k, X η = 0 := by
        intro η
        rw [hLOC η 0 ∅ isOpen_empty (by rw [hXe]) (fun x hx => hx.elim), map_zero]
      have hT0 : ∀ ω, lpush N N' k F X ω = 0 := by
        intro ω
        have h := hconv ω
        simp only [hX0] at h
        exact tendsto_nhds_unique h tendsto_const_nhds
      refine ⟨ball y 1, ⟨isOpen_ball, ?_, subset_univ _, fun ω _ => hT0 ω⟩, mem_ball_self one_pos⟩
      exact (isCompact_closedBall y 1).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · have hne : (F '' X.support).Nonempty := (nonempty_iff_ne_empty.2 hXe).image F
      have hcpt : IsCompact (F '' X.support) := hX1.image hF.continuous
      have hr : 0 < infDist y (F '' X.support) :=
        (hcpt.isClosed.notMem_iff_infDist_pos hne).1 hyF
      set r := infDist y (F '' X.support) with hrdef
      refine ⟨ball y (r / 3), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self (by linarith)⟩
      · exact (isCompact_closedBall y (r / 3)).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
      · intro ω hω
        have hev : ∀ᶠ j in atTop, X (θ ω j) = 0 := by
          filter_upwards [hrate.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 3))]
            with j hj
          obtain ⟨W, hW, hKW, h⟩ := hθ ω j
          have hO : IsOpen {x | r / 3 < dist (G j x) y} :=
            isOpen_lt continuous_const ((hG j).continuous.dist continuous_const)
          have hKO : X.support ⊆ {x | r / 3 < dist (G j x) y} := by
            intro x hx
            have h1 : r ≤ dist (F x) y := by
              rw [dist_comm]
              exact infDist_le_dist_of_mem (mem_image_of_mem F hx)
            have h2 : dist (G j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := hdistG j x
            have h3 := dist_triangle (F x) (G j x) y
            rw [dist_comm (F x) (G j x)] at h3
            show r / 3 < dist (G j x) y
            linarith
          have hzero : ∀ x ∈ {x | r / 3 < dist (G j x) y} ∩ W,
              (θ ω j : DifferentialForm (Euclid N) k) x =
                ((0 : TestFormOn (univ : Set (Euclid N)) k) : DifferentialForm (Euclid N) k) x := by
            intro x hx
            rw [h x hx.2]
            have h0 : (ω : DifferentialForm (Euclid N') k) (G j x) = 0 := by
              apply image_eq_zero_of_notMem_tsupport
              intro hmem
              have hb := hω hmem
              rw [mem_ball] at hb
              exact absurd hb (not_lt.2 hx.1.le)
            rw [h0]
            ext v
            simp
          rw [hLOC (θ ω j) 0 _ (hO.inter hW) (subset_inter hKO hKW) hzero, map_zero]
        have h0 : Tendsto (fun j => X (θ ω j)) atTop (𝓝 0) :=
          tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm)
        exact tendsto_nhds_unique (hconv ω) h0
/-- **Simon 6.2.29** (Lipschitz push-forward, normalization): push-forward by the identity is the
identity.  Let `lpush` satisfy the approximation property (PA): if `F` is Lipschitz, the `Fⱼ` are
`C^∞` with `‖DFⱼ‖ ≤ Λ'` on `spt X`, `Fⱼ → F` uniformly on `spt X`, and `ηⱼ = Fⱼ^# ω` on an open
`W ⊇ spt X`, then `X(ηⱼ) → lpush(F, X)(ω)`.  For `X` with compact support, `M(X) < ∞` and
`M(∂X) < ∞`, take `F = Fⱼ = id`, `Λ = Λ' = 1` and `ηⱼ = ω` (`id^# ω = ω`): the constant sequence
`X(ω)` tends to `lpush(id, X)(ω)`, so the two agree for every `ω`. -/
theorem Submission.cmcdt_lpo_pf_identity : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X := by
  intro lpush hPA N k X hX1 hX2 hX3
  ext ω
  -- the constant sequence `Fⱼ = id` converges uniformly to `id`
  have hU : TendstoUniformlyOn (fun (_ : ℕ) (x : Euclid N) => x) (fun x => x) atTop X.support := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun j x _ => by simpa using hε
  -- (PA) with `F = Fⱼ = id`, `Λ = Λ' = 1`, `ηⱼ = ω`, since `id^# ω = ω` on `W = ℝᴺ`
  have hT := hPA N N k 1 1 (fun x => x) (fun _ => fun x => x) X ω (fun _ => ω) LipschitzWith.id
    hX1 hX2 hX3 (fun _ => contDiff_id)
    (fun j x _ => by rw [fderiv_fun_id]; exact ContinuousLinearMap.norm_id_le) hU
    (fun j => ⟨univ, isOpen_univ, subset_univ _, fun x _ => by
      rw [fderiv_fun_id]
      ext v
      simp⟩)
  -- the constant sequence `X(ω)` tends to `lpush(id, X)(ω)` and to `X(ω)`
  exact tendsto_nhds_unique hT tendsto_const_nhds

/-- **Simon 6.2.29: the Lipschitz push-forward is additive** on currents `X` with `spt X` compact
and `M(X), M(∂X) < ∞`.  Suppose `lpush` has the approximation property (PA): `X(ηⱼ) → f#X(ω)`
whenever smooth `Fⱼ → F` uniformly on `spt X`, `‖DFⱼ‖ ≤ Λ'` there, and `ηⱼ = Fⱼ^#ω` on an open
`W ⊇ spt X`.  Then `f#(X − Y) = f#X − f#Y`.  `X − Y` is again such a current, with
`spt(X − Y) ⊆ spt X ∪ spt Y` (`cmcdt_lpo_pf_normal_closure`).  So one approximating sequence
`Fⱼ`, `ηⱼ` for `K = spt X ∪ spt Y` (`cmcdt_lpo_pf_approx_data`, `Λ' = Λ`) serves `X`, `Y` and
`X − Y`, and `(X − Y)(ηⱼ) = X(ηⱼ) − Y(ηⱼ)`.  Apply (PA) three times; limits are unique. -/
theorem Submission.cmcdt_lpo_pf_sub : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y := by
  intro lpush hPA N N' k Λ F X Y hF hX1 hX2 hX3 hY1 hY2 hY3
  -- `X − Y` is normal, with `spt(X − Y) ⊆ spt X ∪ spt Y`
  obtain ⟨hsupp, hZ1, hZ2, hZ3⟩ :=
    Submission.cmcdt_lpo_pf_normal_closure.1 N k X Y hX1 hX2 hX3 hY1 hY2 hY3
  ext ω
  -- one approximation `Fⱼ → F`, `ηⱼ = Fⱼ^#ω` near `K = spt X ∪ spt Y`
  obtain ⟨Fs, hFs, -, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F (X.support ∪ Y.support) hF (hX1.union hY1)
  obtain ⟨ηs, hηs⟩ := hη k ω
  have hη' : ∀ (S : Set (Euclid N)), S ⊆ X.support ∪ Y.support → ∀ j, ∃ W : Set (Euclid N),
      IsOpen W ∧ S ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun S hS j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hS.trans hKW, h1⟩
  -- (PA) for `X`, `Y` and `X − Y`, all with `Λ' = Λ`
  have hX := hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (hη' _ subset_union_left)
  have hY := hPA N N' k Λ Λ F Fs Y ω ηs hF hY1 hY2 hY3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (hη' _ subset_union_right)
  have hZ := hPA N N' k Λ Λ F Fs (X - Y) ω ηs hF hZ1 hZ2 hZ3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (hη' _ hsupp)
  -- `(X − Y)(ηⱼ) = X(ηⱼ) − Y(ηⱼ)` by definition of the difference
  have hXY : Tendsto (fun j => (X - Y) (ηs j)) atTop
      (𝓝 (lpush N N' k F X ω - lpush N N' k F Y ω)) := hX.sub hY
  exact tendsto_nhds_unique hZ hXY

/-- **The Lipschitz push-forward depends only on `F|spt X`** (Simon Ch. 6, 2.28–2.29).  Suppose
`lpush` has the approximation property (PA): whenever `F` is `Λ`-Lipschitz, the `Fⱼ` are `C^∞`
with `‖DFⱼ‖ ≤ Λ'` on `spt X`, `Fⱼ → F` uniformly on `spt X`, and `ηⱼ = Fⱼ^#ω` on an open set
containing `spt X`, then `X(ηⱼ) → lpush(F, X)(ω)` (`spt X` compact, `M(X), M(∂X) < ∞`).  If the
`Λ`-Lipschitz maps `F`, `G` agree on `spt X`, then `lpush(F, X) = lpush(G, X)`.

Fix `ω ∈ 𝒟ᵏ(ℝ^{N'})`.  The approximation data for `F` on `K = spt X` give `C^∞` maps `Fⱼ` with
`‖DFⱼ‖ ≤ Λ` and `Fⱼ → F` uniformly, and test forms `ηⱼ` equal to `Fⱼ^#ω` on open `Wⱼ ⊇ spt X`.
As `F = G` on `spt X`, also `Fⱼ → G` uniformly on `spt X`.  So (PA) for `F` and for `G`, with the
same `Fⱼ` and `ηⱼ`, gives `X(ηⱼ) → lpush(F, X)(ω)` and `X(ηⱼ) → lpush(G, X)(ω)`, and limits in
`ℝ` are unique.  This is 2.28 (`f#T = g#T` for `C¹` maps with `f = g` on `spt T`) for the
Lipschitz push-forward of 2.29, the limit of push-forwards by smooth approximations of `f`. -/
theorem Submission.cmcdt_lpo_pf_congr : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X := by
  intro lpush hPA N N' k Λ F G X hF hG hX1 hX2 hX3 hFG
  -- currents are determined by their values on test forms: fix `ω ∈ 𝒟ᵏ(ℝ^{N'})`
  ext ω
  -- `C^∞` maps `Fⱼ → F` with `‖DFⱼ‖ ≤ Λ`, and forms `ηⱼ = Fⱼ^#ω` on open `Wⱼ ⊇ spt X`
  obtain ⟨Fs, hFs, -, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨ηs, hηs⟩ := hη k ω
  have hη' : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hKW, h1⟩
  -- `Fⱼ → F` uniformly on `spt X`, hence `Fⱼ → G` there, as `F = G` on `spt X`
  have hUF : TendstoUniformlyOn Fs F atTop X.support := hU.tendstoUniformlyOn
  have hUG : TendstoUniformlyOn Fs G atTop X.support := hUF.congr_right hFG
  -- (PA) for `F` and for `G` with the same data (`Λ' = Λ`); limits in `ℝ` are unique
  have h1 := hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x) hUF hη'
  have h2 := hPA N N' k Λ Λ G Fs X ω ηs hG hX1 hX2 hX3 hFs (fun j x _ => hD j x) hUG hη'
  exact tendsto_nhds_unique h1 h2

/-- **Simon 6.2.24(1) and 6.2.29: the Lipschitz push-forward commutes with the boundary** on
currents `X` with `spt X` compact and `M(X), M(∂X) < ∞`.  Suppose `lpush` has the approximation
property (PA): `X(ηⱼ) → f#X(ω)` whenever smooth `Fⱼ → F` uniformly on `spt X`, `‖DFⱼ‖ ≤ Λ'`
there, and `ηⱼ = Fⱼ^#ω` on an open `W ⊇ spt X`.  Then `∂f#X = f#∂X`.  `∂X` is again such a
current, with `spt ∂X ⊆ spt X` (`cmcdt_lpo_pf_normal_closure`).  One approximating sequence
`Fⱼ`, `ηⱼ` for `K = spt X` (`cmcdt_lpo_pf_approx_data`, `Λ' = Λ`) also has `dηⱼ = Fⱼ^#(dω)` near
`spt X`.  So (PA) for `∂X` with `ω` and for `X` with `dω` concern the same sequence
`∂X(ηⱼ) = X(dηⱼ)`; its limits `f#∂X(ω)` and `f#X(dω) = ∂f#X(ω)` agree. -/
theorem Submission.cmcdt_lpo_pf_boundary : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary := by
  intro lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  -- `∂X` is normal, with `spt ∂X ⊆ spt X`; `boundaryMassOn X univ` is `M(∂X)`
  obtain ⟨hbsupp, hbX1, hbX3⟩ := Submission.cmcdt_lpo_pf_normal_closure.2 N k X hX1
  have hX3' : boundaryMassOn X univ < ∞ := hX3
  have hbX3' : boundaryMassOn X.boundary univ < ∞ := by
    rw [hbX3]
    exact ENNReal.zero_lt_top
  ext ω
  -- one approximation `Fⱼ → F` with `ηⱼ = Fⱼ^#ω` and `dηⱼ = Fⱼ^#(dω)` near `K = spt X`
  obtain ⟨Fs, hFs, -, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  obtain ⟨ηs, hηs⟩ := hη k ω
  -- (PA) for `∂X` with `ω`, `ηⱼ` and for `X` with `dω`, `dηⱼ`, both with `Λ' = Λ`
  have h1 := hPA N N' k Λ Λ F Fs X.boundary ω ηs hF hbX1 hX3 hbX3' hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn (fun j => by
      obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
      exact ⟨W, hW, hbsupp.trans hKW, h1⟩)
  have h2 := hPA N N' (k + 1) Λ Λ F Fs X (exteriorDerivativeTestOn univ k ω)
    (fun j => exteriorDerivativeTestOn univ k (ηs j)) hF hX1 hX2 hX3' hFs
    (fun j x _ => hD j x) hU.tendstoUniformlyOn (fun j => by
      obtain ⟨W, hW, hKW, -, h2⟩ := hηs j
      exact ⟨W, hW, hKW, h2⟩)
  -- `∂X(ηⱼ) = X(dηⱼ)` and `∂(f#X)(ω) = f#X(dω)` by definition; limits are unique
  exact tendsto_nhds_unique h2 h1

/-- **Push-forward as a limit of smooth push-forwards** (Simon 6.2.28–2.29).  Suppose `lpush`
has the approximation property (PA): `X(ηⱼ) → lpush(F, X)(ω)` whenever the `Fⱼ` are `C^∞` with
`‖DFⱼ‖ ≤ Λ'` on `spt X`, `Fⱼ → F` uniformly on `spt X` and `ηⱼ = Fⱼ^#ω` on an open set
containing `spt X`.  Then a single sequence of `C^∞`, `Λ`-Lipschitz `Fⱼ → F` (uniformly on `ℝᴺ`)
serves every `ω ∈ 𝒟ᵏ(ℝ^{N'})`: take the approximants and cut-off pull-backs of
`cmcdt_lpo_pf_approx_data` for `K = spt X` (so `‖DFⱼ‖ ≤ Λ` everywhere), drop the `dηⱼ` clause
and apply (PA) with `Λ' = Λ`. -/
theorem Submission.cmcdt_lpo_pf_smooth_approx : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω)) := by
  intro lpush hPA N N' k Λ F X hF hX1 hX2 hX3
  obtain ⟨Fs, hFs, hLip, hD, -, hU, hη⟩ :=
    Submission.cmcdt_lpo_pf_approx_data N N' Λ F X.support hF hX1
  refine ⟨Fs, hFs, hLip, hU, fun ω => ?_⟩
  obtain ⟨ηs, hηs⟩ := hη k ω
  -- `ηⱼ = Fⱼ^#ω` on an open `W ⊇ spt X` (the `dηⱼ` clause is not needed)
  have hη' : ∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
      (ηs j : DifferentialForm (Euclid N) k) x =
        ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
          (fderiv ℝ (Fs j) x) := fun j => by
    obtain ⟨W, hW, hKW, h1, -⟩ := hηs j
    exact ⟨W, hW, hKW, h1⟩
  -- (PA) with `Λ' = Λ`, and uniform convergence on `ℝᴺ` restricted to `spt X`
  exact ⟨ηs, hη', hPA N N' k Λ Λ F Fs X ω ηs hF hX1 hX2 hX3 hFs (fun j x _ => hD j x)
    hU.tendstoUniformlyOn hη'⟩

/-- **The Lipschitz push-forward** (Simon 6.2.28–2.29).  For `F` Lipschitz and `X` with compact
support, `M(X) < ∞` and `M(∂X) < ∞`, `lpush F X` is the current `T` of `cmcdt_lpo_pf_current`:
`T(ω) = lim X(ηⱼ)` whenever `Fⱼ` are `C^∞`, `Fⱼ → F` uniformly on `spt X` with `‖DFⱼ‖` bounded
there, and `ηⱼ = Fⱼ^#ω` near `spt X`; otherwise `lpush F X = 0`.  This limit property (PA) does not
mention the Lipschitz constant used to build `T`, so it holds for every `Λ`.  Conjuncts (1)–(6) are
derived from (PA) for an arbitrary family `lpush` (the mass bound also uses (VO), (REP), (LB)). -/
theorem Submission.cmcdt_lpo_lipschitz_pushforward : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) ∧ ∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω)) := by
  intro hVO hREP hLB
  classical
  choose T hT using Submission.cmcdt_lpo_pf_current hVO hREP hLB
  -- `lpush F X = T` if `F` is Lipschitz and `X` is normal with compact support, `0` otherwise
  obtain ⟨lpush, hlpush⟩ : ∃ lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') →
      GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k,
      ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k)
        (h : (∃ Λ : NNReal, LipschitzWith Λ F) ∧ IsCompact X.support ∧ X.mass < ∞ ∧
          boundaryMassOn X univ < ∞),
        lpush N N' k F X = T N N' k h.1.choose F X h.1.choose_spec h.2.1 h.2.2.1 h.2.2.2 :=
    ⟨fun N N' k F X => if h : (∃ Λ : NNReal, LipschitzWith Λ F) ∧ IsCompact X.support ∧
        X.mass < ∞ ∧ boundaryMassOn X univ < ∞ then
        T N N' k h.1.choose F X h.1.choose_spec h.2.1 h.2.2.1 h.2.2.2 else 0,
      fun N N' k F X h => dite_eq_left h⟩
  -- (PA): the limit property of `T` holds for any Lipschitz constant of `F`
  have hPA : ∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N')
      (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k)
      (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k),
      LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ →
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') →
      TendstoUniformlyOn Fs F atTop X.support →
      (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W,
        (ηs j : DifferentialForm (Euclid N) k) x =
          ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap
            (fderiv ℝ (Fs j) x)) →
      Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω)) := by
    intro N N' k Λ Λ' F Fs X ω ηs hF hXc hXm hXb hFs hDF hU hη
    rw [hlpush N N' k F X ⟨⟨Λ, hF⟩, hXc, hXm, hXb⟩]
    exact hT _ _ _ _ _ _ _ _ _ _ Λ' Fs ω ηs hFs hDF hU hη
  -- conjuncts (1)–(6) from (PA)
  exact ⟨lpush, Submission.cmcdt_lpo_pf_identity lpush hPA,
    Submission.cmcdt_lpo_pf_sub lpush hPA, Submission.cmcdt_lpo_pf_congr lpush hPA,
    Submission.cmcdt_lpo_pf_mass_support hVO hREP hLB lpush hPA,
    Submission.cmcdt_lpo_pf_boundary lpush hPA, Submission.cmcdt_lpo_pf_smooth_approx lpush hPA,
    hPA⟩
/-- **The cylinder `[[0, 1]] × X`** (Simon 6.2.17–2.21): conjuncts (7)–(9) of the operator
package.  With `ι(t, x) = (t, x)`, `J v = ι(0, v)` and `e₀` the first unit vector,
`cyl X (ω) = X(S ω)` for the slice `S ω (x)(v) = ∫₀¹ ω(ι(t, x))(e₀, J v) dt`.  The covector maps
`γ ↦ γ(e₀, J ·)` and `γ ↦ γ(J ·)` do not increase the Euclidean norm, so `S` is linear,
support-controlled and bounded in the sup of the covector norm; the bounded-current constructor
gives `cyl X` with `M(cyl X) ≤ M(X)`, additive in `X`.  Its support lies in the compact set
`ι([0, 1] × spt X)`, and the homotopy identities
`S(dω) = ω(ι(1, ·))(J ·) − ω(ι(0, ·))(J ·) − d(S ω)` (Simon 6.2.21) make `M(∂ cyl X)` finite. -/
theorem Submission.cmcdt_lpo_cylinder : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∃ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η := by
  intro hVO hREP hLB
  obtain ⟨hL1, hL2, -⟩ := hLB
  -- slices (a)–(e) of test forms, and the bounds (MSB), (BC) of the current toolkit
  obtain ⟨hSA, hSB, hSC, hSD, hSE⟩ := Submission.cmcdt_lpo_slice_forms
  obtain ⟨hMSB, hBC, -, -⟩ := Submission.cmcdt_lpo_current_toolkit hVO hREP
  -- step 1: `γ ↦ γ(e₀, J ·)` and `γ ↦ γ(J ·)` do not increase the covector norm
  obtain ⟨hR1, hR2⟩ := Submission.cmcdt_lpo_cyl_restriction_bounds hL1 hL2
  -- step 2: the linear slice operators `S N k : 𝒟^{k+1}(ℝ^{N+1}) → 𝒟^k(ℝ^N)`
  choose S hSf hSs hSb using Submission.cmcdt_lpo_cyl_slice_operator hSA hSE hR1
  -- step 3: `cyl X (ω) = X(S ω)` with `M(cyl X) ≤ M(X)`, additive on finite-mass currents
  choose cyl hcyl hsub using fun N k : ℕ =>
    Submission.cmcdt_lpo_cyl_current hMSB hBC N k (S N k) (hSb N k)
  refine ⟨cyl, fun N k X hXc hXm hXb => ?_,
    fun N k X Y _ hXm _ _ hYm _ => hsub N k X Y hXm hYm,
    fun N k X _ hXm _ ω => ⟨S N k ω, hSf N k ω, (hcyl N k X hXm).1 ω⟩⟩
  -- conjunct (7): compact support in `ι([0, 1] × spt X)`, finite mass and boundary mass
  obtain ⟨happ, hmass⟩ := hcyl N k X hXm
  obtain ⟨hcpt, hspt⟩ :=
    Submission.cmcdt_lpo_cyl_support hVO N k X (cyl N k X) (S N k) hXc (hSs N k) happ
  exact ⟨hcpt, hmass.trans_lt hXm,
    Submission.cmcdt_lpo_cyl_boundary_mass hMSB hSB hSC hSD hR2 N k X (cyl N k X)
      (fun m => S N m) hXm hXb (fun m => hSf N m) (fun m => hSb N m) happ, hspt⟩

/-- **Cut-off pull-backs along the smoothed homotopy and their limits** (Simon Ch. 6, §2: the
homotopy formula for Lipschitz maps via smooth approximation).  Write `ι(t, x) = (t, x₁, …, x_N)`,
`Jv = ι(0, v)` and `C = {ι(t, x) : t ∈ [0, 1], x ∈ K}` (compact).  With the smooth approximations
`F_j, G_j, H_j` of `cmcdt_lpoh_smooth_approx`, `β_j` is the cut-off pull-back of
`cmcdt_lpo_cutoff_pullback`, equal to `H_j^#ω` (and `dβ_j` to `H_j^#(dω)`) on an open `W_j ⊇ C`,
and `ρ_{s,j}(x) = β_j(ι(s, x)) ∘ J` is the affine pull-back of `β_j` by the isometric embedding
`ι(s, ·)`, a test form since `ι(s, ·)` is proper.  As `H_j ∘ ι(1, ·) = G_j` and
`H_j ∘ ι(0, ·) = F_j` with matching derivatives along `J`, `ρ_{1,j} = G_j^#ω` and
`ρ_{0,j} = F_j^#ω` near `K`, so (PA) gives the limits; the pointwise description of `β_j` on `C`
carries the derivative bounds of `cmcdt_lpoh_smooth_approx`. -/
theorem Submission.cmcdt_lpoh_pullback_limits : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' m : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)) (ω : TestFormOn (univ : Set (Euclid N')) m), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (β : ℕ → TestFormOn (univ : Set (Euclid (N + 1))) m) (ρ₁ ρ₀ : ℕ → TestFormOn (univ : Set (Euclid N)) m), (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₁ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₀ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid N)) m, IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → X.support ⊆ K → Tendsto (fun j => X (ρ₁ j)) atTop (𝓝 (lpush N N' m G X ω)) ∧ Tendsto (fun j => X (ρ₀ j)) atTop (𝓝 (lpush N N' m F X ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) m, IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (β j)) atTop (𝓝 (lpush (N + 1) N' m H Y ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (m + 1), IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j))) atTop (𝓝 (lpush (N + 1) N' (m + 1) H Y (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)))) ∧ ∀ (j : ℕ), ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∃ (p : Euclid N') (D : Euclid (N + 1) →L[ℝ] Euclid N'), (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((ω : DifferentialForm (Euclid N') m) p).compContinuousLinearMap D ∧ ‖D (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) ∧ ∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖ := by
  intro lpush hPA N N' m Λ L F G H K ω hF hG hH hK hHK
  obtain ⟨Fs, Gs, Hs, Λ', hFs, hGs, hHs, hDF, hDG, hFu, hGu, hH1, hH0, hDH1, hDH0, hDe, hDJ, hDHb,
    hHu⟩ := Submission.cmcdt_lpoh_smooth_approx N N' Λ F G H K hF hG hK hHK
  -- `C = {ι(t, x) : t ∈ [0, 1], x ∈ K}` is compact
  set C : Set (Euclid (N + 1)) := {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
    y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}
  have hιc : ∀ s : ℝ, Continuous
      (fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) :=
    fun s => (PiLp.continuous_toLp 2 _).comp (continuous_const.finCons (PiLp.continuous_ofLp 2 _))
  have hCc : IsCompact C := by
    have : C = (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
          (Icc (0 : ℝ) 1 ×ˢ K) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [this]
    exact (isCompact_Icc.prod hK).image (by fun_prop)
  -- cut-off pull-backs `β_j = H_j^#ω` and `dβ_j = H_j^#(dω)` on an open `W_j ⊇ C`
  have hCP := fun j => Submission.cmcdt_lpo_cutoff_pullback (N + 1) N' m (Hs j) ω C (hHs j) hCc
  choose β W hWo hCW hβW hdβW using hCP
  -- end slices `ρ(x)(v) = β(ι(s, x))(Jv)`: the affine pull-back by the isometry `ι(s, ·)`
  have hslice : ∀ (s : ℝ) (β' : TestFormOn (univ : Set (Euclid (N + 1))) m),
      ∃ ρ : TestFormOn (univ : Set (Euclid N)) m, ∀ (x : Euclid N) (v : Fin m → Euclid N),
        (ρ : DifferentialForm (Euclid N) m) x v =
          (β' : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
    intro s β'
    let Jₗ : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun v w => by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp
        map_smul' := fun c v => by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp }
    let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jₗ
    have hJ : ∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) := fun _ => rfl
    set b : Euclid (N + 1) := WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (0 : Euclid N))) with hb
    have hbJ : ∀ x, b + J x = WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) := by
      intro x
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [hb, hJ]
    have hproper : IsProperMap fun x => b + J x := by
      refine (Isometry.isClosedEmbedding (Isometry.of_dist_eq fun x y => ?_)).isProperMap
      rw [hbJ, hbJ, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succ]
      simp
    refine ⟨⟨affinePullbackForm J b (β' : DifferentialForm (Euclid (N + 1)) m),
      affinePullbackForm_isTestForm J b hproper β'.property.1, subset_univ _⟩, fun x v => ?_⟩
    show affinePullbackForm J b (β' : DifferentialForm (Euclid (N + 1)) m) x v = _
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hbJ]
    rfl
  choose ρ hρ using fun (s : ℝ) (j : ℕ) => hslice s (β j)
  refine ⟨β, ρ 1, ρ 0, fun j x v => hρ 1 j x v, fun j x v => hρ 0 j x v, ?_, ?_, ?_, ?_⟩
  · -- (ii): near `K`, `ρ_{1,j} = G_j^#ω` and `ρ_{0,j} = F_j^#ω`
    intro X hXc hXm hXb hXK
    have hend : ∀ (s : ℝ) (Es : ℕ → Euclid N → Euclid N'),
        (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) = Es j x) →
        (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
          (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Es j) x v) →
        s ∈ Icc (0 : ℝ) 1 → ∀ j, ∃ W' : Set (Euclid N), IsOpen W' ∧ X.support ⊆ W' ∧ ∀ x ∈ W',
          (ρ s j : DifferentialForm (Euclid N) m) x =
            ((ω : DifferentialForm (Euclid N') m) (Es j x)).compContinuousLinearMap
              (fderiv ℝ (Es j) x) := by
      intro s Es hE hDE hs j
      refine ⟨(fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)))
        ⁻¹' W j, (hWo j).preimage (hιc s), fun x hx => hCW j ⟨s, hs, x, hXK hx, rfl⟩,
        fun x hx => ?_⟩
      ext v
      rw [hρ s j x v, hβW j _ hx]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hE]
      congr 1
      funext i
      exact hDE j x (v i)
    constructor
    · exact hPA N N' m Λ Λ G Gs X ω (ρ 1) hG hXc hXm hXb hGs (fun j x _ => hDG j x)
        hGu.tendstoUniformlyOn (hend 1 Gs hH1 hDH1 ⟨zero_le_one, le_rfl⟩)
    · exact hPA N N' m Λ Λ F Fs X ω (ρ 0) hF hXc hXm hXb hFs (fun j x _ => hDF j x)
        hFu.tendstoUniformlyOn (hend 0 Fs hH0 hDH0 ⟨le_rfl, zero_le_one⟩)
  · -- (iii): (PA) for `H` with the approximations `H_j`
    intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' m L Λ' H Hs Y ω β hH hYc hYm hYb hHs ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hβW j⟩
  · -- (iv): the same in degree `m + 1` for `dβ_j` and `dω`
    intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' (m + 1) L Λ' H Hs Y
      (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)
      (fun j => exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j)) hH hYc hYm hYb hHs
      ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hdβW j⟩
  · -- (v): on `C`, `β_j = H_j^#ω` with the derivative bounds of the smoothed homotopy
    intro j x hx t ht
    exact ⟨Hs j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      hβW j _ (hCW j ⟨t, ht, x, hx, rfl⟩), hDe j t x, hDJ j t ht x⟩

/-- **Homotopy identity for a cylinder operator** (Simon Ch. 6, 2.17–2.22, and the homotopy
formula 2.25–2.27).  Let `cyl` take `X ∈ 𝒟ₖ(ℝᴺ)` to `cyl X ∈ 𝒟ₖ₊₁(ℝᴺ⁺¹)` with the slice property
(9): for `X` with compact support, `M(X) < ∞` and `M(∂X) < ∞`, and `ω ∈ 𝒟ᵏ⁺¹(ℝᴺ⁺¹)`,
`cyl X (ω) = X(η)` with `η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt`.  (a) In degree `0`, where
`boundaryMassOn X univ = 0`, (9) for `dβ` and the slice identity (d) of `cmcdt_lpo_slice_forms`
give `η = ρ₁ − ρ₀`, so `cyl X (dβ) = X(ρ₁) − X(ρ₀)`.  (b) In degree `k + 1`, (9) for `X` and `dβ`
gives `η`, (9) for `∂X` and `β` gives `θ` with `cyl ∂X (β) = ∂X(θ) = X(dθ)`, and the slice
identity (c) gives `η = ρ₁ − ρ₀ − dθ`; by linearity of `X`,
`cyl X (dβ) = X(ρ₁) − X(ρ₀) − cyl ∂X (β)`. -/
theorem Submission.cmcdt_lpoh_cyl_identity : ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (ρ₁ ρ₀ : TestFormOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (ρ₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (ρ₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 β) = X ρ₁ - X ρ₀) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (ρ₁ ρ₀ : TestFormOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → IsCompact X.boundary.support → boundaryMassOn X.boundary univ < ∞ → (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (ρ₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (ρ₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → cyl N (k + 1) X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) β) = X ρ₁ - X ρ₀ - cyl N k X.boundary β := by
  intro cyl h9
  -- the slice identities (c) and (d) of `cmcdt_lpo_slice_forms`
  obtain ⟨-, -, hc, hd, -⟩ := Submission.cmcdt_lpo_slice_forms
  refine ⟨?_, ?_⟩
  · intro N X β ρ₁ ρ₀ hXc hXm hρ₁ hρ₀
    -- Step 1: `boundaryMassOn X univ = 0` in degree `0`, so `X` is normal
    have hXb : boundaryMassOn X univ < ∞ := by
      show (0 : ℝ≥0∞) < ∞
      exact ENNReal.zero_lt_top
    -- Step 2: (9) for `X` and `dβ`
    obtain ⟨η, hη, hcyl⟩ := h9 N 0 X hXc hXm hXb
      (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 β)
    -- Step 3: `η = ρ₁ − ρ₀` by the slice identity (d); then linearity of `X`
    have hηeq : η = ρ₁ - ρ₀ := by
      apply Subtype.ext
      funext x
      ext v
      rw [hη x v]
      have := hd N β x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hρ₁, hρ₀]
      exact this
    rw [hcyl, hηeq]
    exact map_sub X.toCurrent ρ₁ ρ₀
  · intro N k X β ρ₁ ρ₀ hXc hXm hXbm hbc hbb hρ₁ hρ₀
    -- Steps 4–5: `boundaryMassOn X univ = M(∂X)`; (9) for `X` and `dβ`, and for `∂X` and `β`
    obtain ⟨η, hη, hcyl⟩ := h9 N (k + 1) X hXc hXm hXbm
      (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) β)
    obtain ⟨θ, hθ, hcylb⟩ := h9 N k X.boundary hbc hXbm hbb β
    -- Step 6: `η = ρ₁ − ρ₀ − dθ` by the slice identity (c)
    have hηeq : η = ρ₁ - ρ₀ - exteriorDerivativeTestOn (univ : Set (Euclid N)) k θ := by
      apply Subtype.ext
      funext x
      ext v
      rw [hη x v]
      have := hc N k β θ hθ x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hρ₁, hρ₀]
      exact this
    -- Step 7: `cyl ∂X (β) = ∂X(θ) = X(dθ)`, and linearity of `X`
    rw [hcyl, hcylb, hηeq]
    exact (map_sub X.toCurrent _ _).trans (by rw [map_sub X.toCurrent ρ₁ ρ₀]; rfl)
/-- **Evaluation bound for the cylinder on a pulled-back test form** (parent proof step 7).  By (9),
`cyl(X)(β) = X(θ)` with `θ(x)(v) = ∫₀¹ β(ι(t, x))(e₀, Jv) dt`, so by the mass-support bound it is
enough that `|θ(x)| ≤ bᵏ·a·c` on `spt X`.  For fixed `x` the integrand is the continuous
`f(t) = (β(ι(t, x)) ⌟ e₀) ∘ J`, and `|f(t)| ≤ bᵏ·a·|γ| ≤ bᵏ·a·c` for `t ∈ [0, 1]` by
`cmcdt_lpoh_phi_bound`; the Minkowski bound for coefficient norms gives `|θ(x)| ≤ bᵏ·a·c`. -/
theorem Submission.cmcdt_lpoh_cyl_eval_bound : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → ∀ (N N' k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (a b c : ℝ), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → 0 ≤ b → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, ∃ (γ : Covector (Euclid N') (k + 1)) (D : Euclid (N + 1) →L[ℝ] Euclid N'), (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = γ.compContinuousLinearMap D ∧ covectorEuclideanNorm γ ≤ c ∧ ‖D (EuclideanSpace.single 0 1)‖ ≤ a ∧ ∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ b * ‖v‖) → |cyl N k X β| ≤ b ^ k * a * c * X.mass.toReal := by
  intro hVO hREP hL1 hL2 cyl h9 N N' k X β a b c hXc hXm hXb hb hβ
  -- Mass-support bound: `|X(ψ)| ≤ c'·M(X)` when `|ψ(x)| ≤ c'` on `spt X`.  By (REP) on `univ`,
  -- `X(ψ) = ∫ ξ(x)(ψ(x)) dμ` with `μ(univ) = M(X)`, and the zero region of `X` is `μ`-null by (VO).
  have hMSB : ∀ (ψ : TestFormOn (univ : Set (Euclid N)) k) (c' : ℝ),
      (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c') →
        |X ψ| ≤ c' * X.mass.toReal := by
    intro ψ c' hψ
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hXμ, -⟩ := hREP N k univ X isOpen_univ
      fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hXm
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨by rw [hμ]; exact hXm⟩
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, hω, rfl⟩
      simp only [hVO N k univ X ω (disjoint_sdiff_right.mono_left hω.1), ENNReal.ofReal_zero,
        le_refl]
    have hae : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c' := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with x hx
      rw [Real.norm_eq_abs]
      exact (hξ x _).trans (hψ x ⟨mem_univ x, hx⟩)
    rw [hXμ ψ, ← hμ, ← Real.norm_eq_abs, ← measureReal_def]
    exact norm_integral_le_of_norm_le_const hae
  -- Minkowski bound for the coefficient norm: if `α(v) = ∫₀¹ f(t)(v) dt` with `f` continuous and
  -- `|f(t)| ≤ C` on `[0, 1]`, Cauchy–Schwarz gives `|α|² = ∫₀¹ ⟨α, f(t)⟩ dt ≤ |α|·C`, so `|α| ≤ C`.
  have hMink : ∀ (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (C : ℝ),
      Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) →
        (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ C) → covectorEuclideanNorm α ≤ C := by
    intro α f C hf hα hfC
    let s : Finset (Fin k → Fin N) := Finset.univ.filter fun I => StrictMono I
    let e : (Fin k → Fin N) → Fin k → Euclid N := fun I i => EuclideanSpace.basisFun (Fin N) ℝ (I i)
    have hnorm : ∀ γ : Covector (Euclid N) k,
        covectorEuclideanNorm γ = Real.sqrt (∑ I ∈ s, γ (e I) ^ 2) := by
      intro γ
      rw [covectorEuclideanNorm, Finset.sum_filter]
    have hcont : ∀ v : Fin k → Euclid N, Continuous fun t => f t v :=
      fun v => (continuous_eval_const v).comp hf
    have hC : 0 ≤ C := (covectorEuclideanNorm_nonneg _).trans (hfC 0 ⟨le_rfl, zero_le_one⟩)
    have hcont' : ∀ I, Continuous fun t => α (e I) * f t (e I) :=
      fun I => continuous_const.mul (hcont (e I))
    have hsq : covectorEuclideanNorm α ^ 2 = ∫ t in (0 : ℝ)..1, ∑ I ∈ s, α (e I) * f t (e I) := by
      rw [intervalIntegral.integral_finsetSum fun I _ => (hcont' I).intervalIntegrable 0 1, hnorm,
        Real.sq_sqrt (Finset.sum_nonneg fun I _ => sq_nonneg _)]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [intervalIntegral.integral_const_mul, ← hα, sq]
    have hle : covectorEuclideanNorm α ^ 2 ≤ covectorEuclideanNorm α * C := by
      rw [hsq]
      calc ∫ t in (0 : ℝ)..1, ∑ I ∈ s, α (e I) * f t (e I)
          ≤ ∫ t in (0 : ℝ)..1, covectorEuclideanNorm α * C := by
            refine intervalIntegral.integral_mono_on zero_le_one
              ((continuous_finsetSum _ fun I _ => hcont' I).intervalIntegrable 0 1)
              intervalIntegrable_const fun t ht => ?_
            calc ∑ I ∈ s, α (e I) * f t (e I)
                ≤ Real.sqrt (∑ I ∈ s, α (e I) ^ 2) * Real.sqrt (∑ I ∈ s, f t (e I) ^ 2) :=
                  Real.sum_mul_le_sqrt_mul_sqrt s _ _
              _ = covectorEuclideanNorm α * covectorEuclideanNorm (f t) := by rw [hnorm, hnorm]
              _ ≤ covectorEuclideanNorm α * C :=
                  mul_le_mul_of_nonneg_left (hfC t ht) (covectorEuclideanNorm_nonneg _)
        _ = covectorEuclideanNorm α * C := by simp
    rcases (covectorEuclideanNorm_nonneg α).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact hC
    · exact le_of_mul_le_mul_left (by rwa [sq] at hle) hpos
  -- Step 1: the slice `θ` with `cyl(X)(β) = X(θ)`; step 2: reduce to `|θ(x)| ≤ bᵏ·a·c` on `spt X`
  obtain ⟨θ, hθ, hcyl⟩ := h9 N k X hXc hXm hXb β
  rw [hcyl]
  refine hMSB θ (b ^ k * a * c) fun x hx => ?_
  -- Step 3: the continuous integrand `f(t) = (β(ι(t, x)) ⌟ e₀) ∘ J`
  let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro r v
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jl
  let f : ℝ → Covector (Euclid N) k := fun t =>
    (((β : DifferentialForm (Euclid (N + 1)) (k + 1))
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))).curryLeft
        (EuclideanSpace.single 0 1)).compContinuousLinearMap J
  have hf : Continuous f := by
    have hι : Continuous fun t : ℝ =>
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) := by
      fun_prop
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM J).continuous.comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single 0 1 : Euclid (N + 1))).continuous.comp
        ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid (N + 1)) (F := ℝ)
          (n := k)).continuous.comp (β.property.1.1.continuous.comp hι)))
  have hfv : ∀ (t : ℝ) (v : Fin k → Euclid N), f t v =
      (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) :=
    fun _ _ => rfl
  -- Steps 4–5: `|f(t)| ≤ bᵏ·a·c` on `[0, 1]` by `cmcdt_lpoh_phi_bound`, then the Minkowski bound
  refine hMink ((θ : DifferentialForm (Euclid N) k) x) f (b ^ k * a * c) hf
    (fun v => by rw [hθ x v]; simp only [hfv]) fun t ht => ?_
  obtain ⟨γ, D, hβeq, hγ, hDe, hDJ⟩ := hβ x hx t ht
  have ha : 0 ≤ a := (norm_nonneg _).trans hDe
  calc covectorEuclideanNorm (f t) ≤ b ^ k * a * covectorEuclideanNorm γ :=
        Submission.cmcdt_lpoh_phi_bound hL1 hL2 N N' k γ D (f t) a b hb hDe hDJ
          fun v => by rw [hfv, hβeq]
    _ ≤ b ^ k * a * c := mul_le_mul_of_nonneg_left hγ (mul_nonneg (pow_nonneg hb k) ha)
/-- **Lipschitz homotopy formula** (Simon 6.2.25 for the affine homotopy 6.2.26, with the
Lipschitz push-forward of 6.2.29), conjuncts (10) and (11): for `Λ`-Lipschitz `F, G` and an
`L`-Lipschitz `H` with `H(t, x) = F(x) + t(G(x) − F(x))` on `[0, 1] × spt X`,
`G_#X − F_#X = ∂H_#(cyl X)` in degree `0`, and `G_#X − F_#X − H_#(cyl ∂X) = ∂H_#(cyl X)` in
positive degree.  For a test form `ω`, `Submission.cmcdt_lpoh_pullback_limits` (with
`K = spt X`) gives forms `β_j` whose end slices `ρ_{1,j}, ρ_{0,j}` give `X(ρ_{1,j}) → G_#X(ω)`,
`X(ρ_{0,j}) → F_#X(ω)`, while `cyl(X)(dβ_j) → H_#(cyl X)(dω)` and
`cyl(∂X)(β_j) → H_#(cyl ∂X)(ω)`; `Submission.cmcdt_lpoh_cyl_identity` gives
`cyl(X)(dβ_j) = X(ρ_{1,j}) − X(ρ_{0,j}) [− cyl(∂X)(β_j)]`, and limits are unique.  `∂X` is
normal: `spt ∂X ⊆ spt X` because `d` does not enlarge supports, and `∂∂X = 0`. -/
theorem Submission.cmcdt_lpoh_homotopy_formula : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) := by
  intro _hVO _hREP lpush cyl hPA h7 h9
  have hID := Submission.cmcdt_lpoh_cyl_identity cyl h9
  refine ⟨?_, ?_⟩
  · intro N N' Λ L F G H X hF hG hH hXc hXm hHX
    -- in degree `0`, `M(∂X) = 0` by convention
    have hXb : boundaryMassOn X univ < ∞ := by
      show (0 : ℝ≥0∞) < ∞
      exact ENNReal.zero_lt_top
    obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N 0 X hXc hXm hXb
    apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨β, ρ₁, ρ₀, hρ₁, hρ₀, hlimX, -, hlimY', -⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' 0 Λ L F G H X.support ω hF hG hH hXc
        hHX
    have h1 := hlimY' (cyl N 0 X) hc1 hc2 hc3 hc4
    obtain ⟨h2, h3⟩ := hlimX X hXc hXm hXb subset_rfl
    have h4 : Tendsto
        (fun j => cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 (β j)))
        atTop (𝓝 (lpush N N' 0 G X ω - lpush N N' 0 F X ω)) :=
      (h2.sub h3).congr fun j => (hID.1 N X (β j) (ρ₁ j) (ρ₀ j) hXc hXm (hρ₁ j) (hρ₀ j)).symm
    exact tendsto_nhds_unique h4 h1
  · intro N N' k Λ L F G H X hF hG hH hXc hXm hXbm hHX
    have hXb : boundaryMassOn X univ < ∞ := hXbm
    -- `spt ∂X ⊆ spt X`: `d` does not enlarge supports
    have hSBX : X.boundary.support ⊆ X.support := by
      intro x hx
      simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_univ, true_and] at hx ⊢
      intro hxz
      apply hx
      obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxz
      exact ⟨W, ⟨hWo, hWc, hWU, fun ω hω => hWv (exteriorDerivativeTestOn univ k ω)
        ((tsupport_exteriorDerivative_subset _).trans hω)⟩, hxW⟩
    have hbc : IsCompact X.boundary.support :=
      hXc.of_isClosed_subset (isClosed_univ.sdiff X.boundary.isOpen_zeroRegion) hSBX
    -- `M(∂∂X) = 0`
    have hbb : boundaryMassOn X.boundary univ < ∞ := by
      cases k with
      | zero =>
        show (0 : ℝ≥0∞) < ∞
        exact ENNReal.zero_lt_top
      | succ k' =>
        show X.boundary.boundary.massOn univ < ∞
        rw [GeometricCurrentOn.boundary_boundary]
        refine lt_of_le_of_lt ?_ ENNReal.zero_lt_top
        apply sSup_le
        rintro _ ⟨ω', -, rfl⟩
        simp
    obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N (k + 1) X hXc hXm hXb
    obtain ⟨hd1, hd2, hd3, hd4⟩ := h7 N k X.boundary hbc hXbm hbb
    have hd4' : (cyl N k X.boundary).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1,
        ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      intro y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hd4 hy
      exact ⟨t, ht, x, hSBX hx, rfl⟩
    apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨β, ρ₁, ρ₀, hρ₁, hρ₀, hlimX, hlimY, hlimY', -⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' (k + 1) Λ L F G H X.support ω hF hG hH
        hXc hHX
    have h1 := hlimY' (cyl N (k + 1) X) hc1 hc2 hc3 hc4
    have h5 := hlimY (cyl N k X.boundary) hd1 hd2 hd3 hd4'
    obtain ⟨h2, h3⟩ := hlimX X hXc hXm hXb subset_rfl
    have h4 : Tendsto (fun j => cyl N (k + 1) X
        (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) (β j)))
        atTop (𝓝 (lpush N N' (k + 1) G X ω - lpush N N' (k + 1) F X ω -
          lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) ω)) :=
      ((h2.sub h3).sub h5).congr fun j => (hID.2 N k X (β j) (ρ₁ j) (ρ₀ j) hXc hXm hXbm hbc hbb
        (hρ₁ j) (hρ₀ j)).symm
    exact tendsto_nhds_unique h4 h1

/-- Mass bound for the Lipschitz homotopy, conjunct (12): `M(lpush(H, cyl X)) ≤ δ (2Λ)ᵏ M(X)`.
For an admissible `ω`, `cmcdt_lpoh_pullback_limits` (with `K = spt X`) gives forms `βⱼ` with
`cyl(X)(βⱼ) → lpush(H, cyl X)(ω)` and `βⱼ(ι(t, x)) = ω(p) ∘ D`, `‖De₀‖ ≤ δ + 2Λ/(j + 1)`,
`‖D(Jv)‖ ≤ Λ‖v‖`; so `cmcdt_lpoh_cyl_eval_bound` gives `|cyl(X)(βⱼ)| ≤ Λᵏ (δ + 2Λ/(j + 1)) M(X)`.
Letting `j → ∞`, `|lpush(H, cyl X)(ω)| ≤ Λᵏ δ M(X)`; taking the supremum over admissible `ω`
(using `Λᵏ ≤ (2Λ)ᵏ`, and `ofReal δ = 0` if `δ < 0`) gives the claim. -/
theorem Submission.cmcdt_lpoh_mass_bound : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP hLB lpush cyl hPA h7 h9 N N' k Λ L F G H X δ hF hG hH hXc hXm hXb hHX hδ
  -- `cyl X` has compact support in `[0, 1] × spt X`, finite mass and finite boundary mass.
  obtain ⟨hc1, hc2, hc3, hc4⟩ := h7 N k X hXc hXm hXb
  -- Key estimate: `|lpush(H, cyl X)(ω)| ≤ Λᵏ δ M(X)` for every admissible `ω`.
  have key : ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1),
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) ≤ 1) →
      |lpush (N + 1) N' (k + 1) H (cyl N k X) ω| ≤ (Λ : ℝ) ^ k * δ * X.mass.toReal := by
    intro ω hω
    obtain ⟨β, -, -, -, -, -, hlimY, -, hβ⟩ :=
      Submission.cmcdt_lpoh_pullback_limits lpush hPA N N' (k + 1) Λ L F G H X.support ω hF hG hH
        hXc hHX
    have hlim := hlimY (cyl N k X) hc1 hc2 hc3 hc4
    have hbound : ∀ j : ℕ, |cyl N k X (β j)| ≤
        (Λ : ℝ) ^ k * (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * 1 * X.mass.toReal := by
      intro j
      refine Submission.cmcdt_lpoh_cyl_eval_bound hVO hREP hLB.1 hLB.2.1 cyl h9 N N' k X (β j)
        (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) Λ 1 hXc hXm hXb Λ.coe_nonneg ?_
      intro x hx t ht
      obtain ⟨p, D, hpD, hDe, hDJ⟩ := hβ j x hx t ht
      exact ⟨(ω : DifferentialForm (Euclid N') (k + 1)) p, D, hpD, hω p,
        hDe.trans (by linarith [hδ x hx]), hDJ⟩
    have hl1 : Tendsto (fun j => |cyl N k X (β j)|) atTop
        (𝓝 |lpush (N + 1) N' (k + 1) H (cyl N k X) ω|) := hlim.abs
    have hsmall : Tendsto (fun j : ℕ => 2 * (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (Λ : ℝ))
      rw [mul_zero] at h
      refine h.congr fun j => ?_
      rw [mul_one_div]
    have hl2 : Tendsto
        (fun j : ℕ => (Λ : ℝ) ^ k * (δ + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) * 1 * X.mass.toReal)
        atTop (𝓝 ((Λ : ℝ) ^ k * (δ + 0) * 1 * X.mass.toReal)) :=
      ((tendsto_const_nhds.mul (tendsto_const_nhds.add hsmall)).mul tendsto_const_nhds).mul
        tendsto_const_nhds
    simpa using le_of_tendsto_of_tendsto' hl1 hl2 hbound
  -- Supremum over the admissible forms `ω` defining `M(lpush(H, cyl X))`.
  apply sSup_le
  rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
  dsimp only
  have h := key ω hω
  have hM : X.mass ≠ ∞ := hXm.ne
  set T := lpush (N + 1) N' (k + 1) H (cyl N k X)
  rcases le_or_gt 0 δ with hδ0 | hδ0
  · calc ENNReal.ofReal (T ω) ≤ ENNReal.ofReal (δ * (2 * (Λ : ℝ)) ^ k * X.mass.toReal) := by
          apply ENNReal.ofReal_le_ofReal
          have hΛ : (Λ : ℝ) ^ k ≤ (2 * (Λ : ℝ)) ^ k :=
            pow_le_pow_left₀ Λ.coe_nonneg (by linarith [Λ.coe_nonneg]) k
          calc T ω ≤ |T ω| := le_abs_self _
            _ ≤ (Λ : ℝ) ^ k * δ * X.mass.toReal := h
            _ ≤ (2 * (Λ : ℝ)) ^ k * δ * X.mass.toReal := by gcongr
            _ = δ * (2 * (Λ : ℝ)) ^ k * X.mass.toReal := by ring
      _ = ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hδ0, ENNReal.ofReal_toReal hM,
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp
  · -- `δ < 0`: then `T ω ≤ 0`, so `ofReal (T ω) = 0`.
    have hle : T ω ≤ 0 := by
      have h0 : (Λ : ℝ) ^ k * δ * X.mass.toReal ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ0.le) ENNReal.toReal_nonneg
      linarith [le_abs_self (T ω)]
    rw [ENNReal.ofReal_of_nonpos hle]
    exact bot_le

/-- **Homotopy formula for Lipschitz maps** (Simon 6.2.25–6.2.27, with 6.2.29): for `lpush`, `cyl`
with (PA), (7) and (9), `Λ`-Lipschitz `F`, `G` and an `L`-Lipschitz `H` with
`H(t, x) = F x + t (G x − F x)` on `[0, 1] × spt X`, we have
`G_# X − F_# X − H_#([[0, 1]] × ∂X) = ∂ H_#([[0, 1]] × X)` (no middle term in degree `0`), and
`M(H_#([[0, 1]] × X)) ≤ δ (2Λ)^k M(X)` if `|F − G| ≤ δ` on `spt X`.  The two identities are
`Submission.cmcdt_lpoh_homotopy_formula` and the mass bound is `Submission.cmcdt_lpoh_mass_bound`;
both pass to the limit along the smooth affine homotopies `H_j` between mollifications of `F`, `G`. -/
theorem Submission.cmcdt_lpo_lipschitz_homotopy : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP hLB lpush cyl hPA h7 h9
  obtain ⟨h10, h11⟩ := Submission.cmcdt_lpoh_homotopy_formula hVO hREP lpush cyl hPA h7 h9
  exact ⟨h10, h11, Submission.cmcdt_lpoh_mass_bound hVO hREP hLB lpush cyl hPA h7 h9⟩
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
/-- Fubini–Tonelli on the cylinder `Â = {z ∈ ℝ^{n+1} : z₀ ∈ (0, 1), tail z ∈ A}` for Borel
`A ⊆ ℝⁿ`.  The map `e(u, t) = (t, u₁, …, uₙ)`, the composite of the swap `ℝⁿ × ℝ ≃ ℝ × ℝⁿ`,
`id × ofLp`, the inverse of `piFinSuccAbove · 0` (i.e. `Fin.cons`) and `toLp`, is a
measure-preserving measurable equivalence `ℝⁿ × ℝ ≃ᵐ ℝ^{n+1}` with `e⁻¹(Â) = A × (0, 1)`.  Hence
`Â` is Borel, and change of variables along `e` followed by Tonelli (resp. Fubini) on the product
set `A × (0, 1)` gives the iterated lower Lebesgue (resp. Bochner) integrals. -/
theorem Submission.cmcdt_lpi_cyl_fubini : ∀ (n : ℕ) (A : Set (Euclid n)), MeasurableSet A → MeasurableSet {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} ∧ (∀ f : Euclid (n + 1) → ℝ≥0∞, Measurable f → ∫⁻ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))) ∧ ∀ f : Euclid (n + 1) → ℝ, IntegrableOn f {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → ∫ z in {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A}, f z = ∫ u in A, ∫ t in Ioo (0 : ℝ) 1, f (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) := by
  intro n A hA
  set Ah := {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
    (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} with hAh_def
  -- the measurable equivalence `e : ℝⁿ × ℝ ≃ᵐ ℝ^{n+1}`, `(u, t) ↦ (t, u)`
  let e : (Euclid n × ℝ) ≃ᵐ Euclid (n + 1) :=
    (MeasurableEquiv.prodComm.trans
      ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm)).trans
      (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ))
  have he : ∀ p : Euclid n × ℝ, e p = WithLp.toLp 2 (Fin.cons p.2 (WithLp.ofLp p.1)) := by
    rintro ⟨u, t⟩
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
    exact ⟨rfl, rfl⟩
  -- each factor of `e` preserves Lebesgue measure
  have hmp : MeasurePreserving e volume volume := by
    have h1 : MeasurePreserving
        (MeasurableEquiv.prodComm : (Euclid n × ℝ) ≃ᵐ (ℝ × Euclid n)) volume volume :=
      Measure.measurePreserving_swap
    have h2 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm) volume volume :=
      (MeasurePreserving.id volume).prod
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))
    have h3 : MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm volume volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
    have h4 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)) volume volume := by
      have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))).symm _
      simpa using this
    exact h4.comp (h3.comp (h2.comp h1))
  -- `e⁻¹(Â) = A × (0, 1)`
  have hpre : e ⁻¹' Ah = A ×ˢ Ioo (0 : ℝ) 1 := by
    ext ⟨u, t⟩
    simp [Ah, he, and_comm]
  have hAhm : MeasurableSet Ah := by
    have : Ah = e.symm ⁻¹' (A ×ˢ Ioo (0 : ℝ) 1) := by
      rw [← hpre]; ext z; simp
    rw [this]
    exact e.symm.measurable (hA.prod measurableSet_Ioo)
  refine ⟨hAhm, ?_, ?_⟩
  · intro f hf
    rw [← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding f Ah, hpre]
    rw [Measure.volume_eq_prod, setLIntegral_prod]
    · simp only [he]
    · exact (hf.comp e.measurable).aemeasurable
  · intro f hf
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding f Ah, hpre]
    rw [Measure.volume_eq_prod, setIntegral_prod]
    · simp only [he]
    · rw [← Measure.volume_eq_prod, ← hpre]
      exact (hmp.integrableOn_comp_preimage e.measurableEmbedding).2 hf
/-- The suspension `Ĝ(t, u) = (t, G(u))` of `G : ℝⁿ → ℝᴺ` (deformation theorem, Lipschitz
push-forward integrality, cylinder step).  If `Ĝ z = (z₀, G(tail z))` for every `z ∈ ℝⁿ⁺¹`, then
(a) `Ĝ` is `max 1 L`-Lipschitz whenever `G` is `L`-Lipschitz, (b) `Ĝ(t, u) = (t, G(u))`, and
(c) if `G` is differentiable at `u`, then `DĜ(t, u)` maps `ê₀` to `e₀` and `ê_{b+1}` to
`(0, DG(u) e_b)`.  Write `Ĝ = Φ ∘ (π₀, G ∘ T)` with the continuous linear maps `T = tail`,
`π₀ z = z₀` and `Φ(s, x) = (s, x)`; then `‖(s, x)‖² = s² + ‖x‖²` gives (a), and the chain rule
gives `DĜ(t, u) ζ = (ζ₀, DG(u)(T ζ))`, hence (c). -/
theorem Submission.cmcdt_lpi_cyl_suspension_map : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (Gh : Euclid (n + 1) → Euclid (N + 1)), (∀ z, Gh z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))))) → (∀ L : NNReal, LipschitzWith L G → LipschitzWith (max 1 L) Gh) ∧ (∀ (t : ℝ) (u : Euclid n), Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp (G u)))) ∧ ∀ (t : ℝ) (u : Euclid n), DifferentiableAt ℝ G u → (fun a => fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single a 1)) = Fin.cons (EuclideanSpace.single 0 1) (fun b => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (fderiv ℝ G u (EuclideanSpace.single b 1))))) := by
  intro N n G Gh hGh
  -- the continuous linear maps `T z = tail z` and `Φ(s, x) = (s, x)`
  let T : Euclid (n + 1) →L[ℝ] Euclid n := LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
      map_add' := fun x y => by ext i; simp [Fin.tail]
      map_smul' := fun c x => by ext i; simp [Fin.tail] }
  let Φ : ℝ × Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
      map_add' := fun x y => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun c x => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  have hT : ∀ z, T z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) := fun z => rfl
  have hΦ : ∀ p, Φ p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) := fun p => rfl
  -- `Ĝ = Φ ∘ (π₀, G ∘ T)`
  have hGh' : Gh = fun z => Φ (EuclideanSpace.proj (0 : Fin (n + 1)) z, G (T z)) := by
    funext z; rw [hGh]; rfl
  -- `‖(s, x)‖² = s² + ‖x‖²`, and `z = (z₀, T z)`
  have hnorm : ∀ (m : ℕ) (t : ℝ) (x : Euclid m),
      ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (m + 1))‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
    intro m t x
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    simp
  have hsplit : ∀ z : Euclid (n + 1),
      z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (T z))) := by
    intro z; simp [hT]
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `‖Ĝ x - Ĝ y‖² = (x₀ - y₀)² + ‖G(T x) - G(T y)‖² ≤ M² ‖x - y‖²`, `M = max 1 L`
    intro L hL
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    have hxy : ‖x - y‖ ^ 2 = (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 + ‖T x - T y‖ ^ 2 := by
      rw [hsplit (x - y), hnorm]; simp [map_sub]
    have hG2 : ‖Gh x - Gh y‖ ^ 2 =
        (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 + ‖G (T x) - G (T y)‖ ^ 2 := by
      rw [hGh x, hGh y, ← hT, ← hT]
      have : (WithLp.toLp 2 (Fin.cons (WithLp.ofLp x 0) (WithLp.ofLp (G (T x)))) :
            Euclid (N + 1)) - WithLp.toLp 2 (Fin.cons (WithLp.ofLp y 0) (WithLp.ofLp (G (T y)))) =
          WithLp.toLp 2 (Fin.cons (WithLp.ofLp x 0 - WithLp.ofLp y 0)
            (WithLp.ofLp (G (T x) - G (T y)))) := by
        ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      rw [this, hnorm]
    have hGL : ‖G (T x) - G (T y)‖ ≤ L * ‖T x - T y‖ := by
      have := hL.dist_le_mul (T x) (T y); rwa [dist_eq_norm, dist_eq_norm] at this
    have h1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have h2 : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have hM0 : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hsq : ‖Gh x - Gh y‖ ^ 2 ≤ (((max 1 L : NNReal) : ℝ) * ‖x - y‖) ^ 2 := by
      rw [hG2, mul_pow, hxy]
      have hA : (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 ≤
          ((max 1 L : NNReal) : ℝ) ^ 2 * (WithLp.ofLp x 0 - WithLp.ofLp y 0) ^ 2 := by
        have : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) ^ 2 := one_le_pow₀ h1
        nlinarith [sq_nonneg (WithLp.ofLp x 0 - WithLp.ofLp y 0)]
      have hB : ‖G (T x) - G (T y)‖ ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * ‖T x - T y‖ ^ 2 := by
        have h0 : 0 ≤ ‖G (T x) - G (T y)‖ := norm_nonneg _
        have h3 : ‖G (T x) - G (T y)‖ ≤ ((max 1 L : NNReal) : ℝ) * ‖T x - T y‖ :=
          hGL.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
        calc ‖G (T x) - G (T y)‖ ^ 2 ≤ (((max 1 L : NNReal) : ℝ) * ‖T x - T y‖) ^ 2 :=
              pow_le_pow_left₀ h0 h3 2
          _ = _ := by ring
      nlinarith [hA, hB]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _))
      two_ne_zero).1 hsq
  · -- (b) `(t, u)₀ = t` and `tail (t, u) = u`
    intro t u
    rw [hGh]; simp
  · -- (c) chain rule: `DĜ(z) ζ = (ζ₀, DG(u)(T ζ))` at `z = (t, u)`; evaluate on `ê₀`, `ê_{b+1}`
    intro t u hG
    set z : Euclid (n + 1) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))
    have hTz : T z = u := by simp [hT, z]
    have h1 : HasFDerivAt (fun z => G (T z)) ((fderiv ℝ G u).comp T) z := by
      have := hG.hasFDerivAt
      rw [← hTz] at this
      exact this.comp z T.hasFDerivAt
    have hd : HasFDerivAt Gh
        (Φ.comp ((EuclideanSpace.proj (0 : Fin (n + 1))).prod ((fderiv ℝ G u).comp T))) z := by
      rw [hGh']
      exact Φ.hasFDerivAt.comp z ((EuclideanSpace.proj (0 : Fin (n + 1))).hasFDerivAt.prodMk h1)
    rw [hd.fderiv]
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · -- `ê₀ ↦ (1, DG(u) 0) = e₀`
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, hΦ, hT,
        Fin.cons_zero]
      have h0 : (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
          (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)))) : Euclid n) = 0 := by
        ext j; simp [Fin.tail, Fin.succ_ne_zero]
      rw [h0, map_zero]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    · -- `ê_{b+1} ↦ (0, DG(u) e_b)`
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, hΦ, hT,
        Fin.cons_succ]
      have : (WithLp.toLp 2 (Fin.tail (WithLp.ofLp (EuclideanSpace.single b.succ (1 : ℝ)))) :
          Euclid n) = EuclideanSpace.single b 1 := by
        ext j; simp [Fin.tail]
      rw [this]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
/-- Covector estimate for the cylinder slice (deformation theorem, Lipschitz push-forward
integrality).  Given the norm bounds `|β ∘ A| ≤ ‖A‖ᵏ |β|` (pull-back) and `|β ⌟ v| ≤ ‖v‖ |β|`
(contraction), let `J x = (0, x)` embed `ℝᴺ` into `ℝᴺ⁺¹` and `e₀ = (1, 0, …, 0)`.  If
`|α(v)| ≤ c |α|` for every `n`-covector `α` on `ℝᴺ`, then `|γ(e₀, Jv₁, …, Jvₙ)| ≤ c |γ|` for every
`(n + 1)`-covector `γ` on `ℝᴺ⁺¹`: the left side is `β(v)` for `β = (γ ⌟ e₀) ∘ J`, and `‖J‖ ≤ 1`,
`‖e₀‖ = 1` give `|β| ≤ |γ|`. -/
theorem Submission.cmcdt_lpi_cyl_slice_covector_bound : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N n : ℕ) (γ : Covector (Euclid (N + 1)) (n + 1)) (v : Fin n → Euclid N) (c : ℝ), 0 ≤ c → (∀ α : Covector (Euclid N) n, |α v| ≤ c * covectorEuclideanNorm α) → |γ (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))| ≤ c * covectorEuclideanNorm γ := by
  intro hL1 hL2 N n γ v c hc hv
  -- the isometric embedding `J x = (0, x)` of `ℝᴺ` into `ℝᴺ⁺¹`
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))
      map_add' := fun x y => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun a x => by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  have hJx : ∀ x, J x = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x)) := fun x => rfl
  -- `‖J x‖² = 0² + ‖x‖²`, so `‖J‖ ≤ 1`
  have hJ : ‖J‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have h : ‖J x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [hJx, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
      simp
    rw [pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero] at h
    rw [h, one_mul]
  -- `β = (γ ⌟ e₀) ∘ J`, so `β(v) = γ(e₀, Jv₁, …, Jvₙ)`
  set β : Covector (Euclid N) n :=
    (γ.curryLeft (EuclideanSpace.single 0 1)).compContinuousLinearMap J with hβdef
  have hβv : β v = γ (Fin.cons (EuclideanSpace.single 0 1)
      (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
    rw [hβdef, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply]
    rfl
  -- `|β| ≤ ‖J‖ⁿ |γ ⌟ e₀| ≤ |γ ⌟ e₀| ≤ ‖e₀‖ |γ| = |γ|`
  have hβ : covectorEuclideanNorm β ≤ covectorEuclideanNorm γ := by
    have h1 := hL1 N (N + 1) n J (γ.curryLeft (EuclideanSpace.single 0 1))
    have h2 := hL2 (N + 1) n (EuclideanSpace.single 0 1) γ
    have he : ‖(EuclideanSpace.single (0 : Fin (N + 1)) (1 : ℝ))‖ = 1 := by simp
    rw [he, one_mul] at h2
    have hJn : ‖J‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) hJ
    calc covectorEuclideanNorm β
        ≤ ‖J‖ ^ n * covectorEuclideanNorm (γ.curryLeft (EuclideanSpace.single 0 1)) := h1
      _ ≤ 1 * covectorEuclideanNorm (γ.curryLeft (EuclideanSpace.single 0 1)) :=
          mul_le_mul_of_nonneg_right hJn (covectorEuclideanNorm_nonneg _)
      _ ≤ covectorEuclideanNorm γ := by rw [one_mul]; exact h2
  rw [← hβv]
  exact (hv β).trans (mul_le_mul_of_nonneg_left hβ hc)
/-- **Lipschitz pull-back of a test form against an integrable weight** (supplied step 3 of the
cylinder construction, third item).  `ω` is smooth with compact support, so `‖ω(y)‖ ≤ M` for all
`y`; an `L`-Lipschitz `H` has `‖DH(z)‖ ≤ L` at every `z` (`fderiv` is `0` where `H` is not
differentiable), so `|ω(H z)(DH(z)e₁, …, DH(z)eₙ)| ≤ ‖ω(H z)‖ ∏ₐ ‖DH(z)eₐ‖ ≤ M Lⁿ`.  The integrand
is Borel: `z ↦ DH(z)eₐ` is measurable and `(x, w) ↦ ω(H x)(w)` is continuous.  An integrable
function times a bounded a.e. strongly measurable function is integrable. -/
theorem Submission.cmcdt_lpi_cyl_pullback_integrable : ∀ (Q n : ℕ) (L : NNReal) (H : Euclid n → Euclid Q) (S : Set (Euclid n)) (g : Euclid n → ℝ) (ω : TestFormOn (univ : Set (Euclid Q)) n), LipschitzWith L H → IntegrableOn g S → IntegrableOn (fun z => g z * (ω : DifferentialForm (Euclid Q) n) (H z) (fun a => fderiv ℝ H z (EuclideanSpace.single a 1))) S := by
  intro Q n L H S g ω hH hg
  -- `ω` is continuous with compact support, hence bounded: `‖ω(y)‖ ≤ M`
  have hωc : Continuous (ω : DifferentialForm (Euclid Q) n) := ω.2.1.1.continuous
  obtain ⟨M, hM⟩ := hωc.bounded_above_of_compact_support ω.2.1.2
  -- the integrand is Borel: `z ↦ (DH(z)eₐ)ₐ` is measurable and `(x, w) ↦ ω(H x)(w)` continuous
  have hmeas : Measurable fun z => (ω : DifferentialForm (Euclid Q) n) (H z)
      (fun a => fderiv ℝ H z (EuclideanSpace.single a 1)) := by
    have hv : Measurable fun z => fun a : Fin n => fderiv ℝ H z (EuclideanSpace.single a 1) :=
      measurable_pi_iff.mpr fun a => measurable_fderiv_apply_const ℝ H _
    have hc : Continuous fun p : Euclid n × (Fin n → Euclid Q) =>
        (ω : DifferentialForm (Euclid Q) n) (H p.1) p.2 :=
      (hωc.comp (hH.continuous.comp continuous_fst)).eval continuous_snd
    exact hc.measurable.comp (measurable_id.prodMk hv)
  -- `|ω(H z)(DH(z)e)| ≤ ‖ω(H z)‖ ∏ₐ ‖DH(z)eₐ‖ ≤ M Lⁿ`, since `‖DH(z)eₐ‖ ≤ ‖DH(z)‖ ≤ L`
  have hbd : ∀ z, ‖(ω : DifferentialForm (Euclid Q) n) (H z)
      (fun a => fderiv ℝ H z (EuclideanSpace.single a 1))‖ ≤ M * (L : ℝ) ^ n := by
    intro z
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (H z))
    have hcomp : ∀ a : Fin n, ‖fderiv ℝ H z (EuclideanSpace.single a 1)‖ ≤ L := fun a =>
      calc ‖fderiv ℝ H z (EuclideanSpace.single a 1)‖
          ≤ ‖fderiv ℝ H z‖ * ‖(EuclideanSpace.single a (1 : ℝ))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ H z‖ := by simp
        _ ≤ L := norm_fderiv_le_of_lipschitz ℝ hH
    calc _ ≤ ‖(ω : DifferentialForm (Euclid Q) n) (H z)‖ *
            ∏ a, ‖fderiv ℝ H z (EuclideanSpace.single a 1)‖ :=
          ContinuousAlternatingMap.le_opNorm _ _
      _ ≤ M * ∏ _a : Fin n, (L : ℝ) := by
          gcongr with a
          · exact hM _
          · exact hcomp a
      _ = M * (L : ℝ) ^ n := by simp
  exact hg.mul_bdd hmeas.aestronglyMeasurable (Eventually.of_forall hbd)

/-- **Simon Ch. 6, 2.17 and 2.24(3)**, one piece of the cylinder `[[(0, 1)]] × T`: if `(G, A, w)`
is a Lipschitz piece (`G` `L`-Lipschitz and differentiable on the Borel set `A`, `w` integrable on
`A`), then so is its suspension `Ĝ(t, u) = (t, G u)` on `Â = (0, 1) × A` with weight
`ŵ(t, u) = w(u)` (`Ĝ` is `max(1, L)`-Lipschitz), and it acts on `ω` as `(G, A, w)` acts on the
slice form `η(x) = ∫₀¹ ⟨ω(t, x), e₀ ∧ J ·⟩ dt` (2.17 with `S = [[(0, 1)]]`).  Tonelli gives
`∫⁻_Â |ŵ| = ∫⁻_A |w| < ∞`; Fubini gives `∫_Â = ∫_A ∫₀¹`, and on each fibre `ŵ = w(u)`,
`Ĝ(t, u) = (t, G u)` and `DĜ(t, u)ê = (e₀, J ∘ DG(u)e)`. -/
theorem Submission.cmcdt_lpi_cyl_piece_action : ∀ (N n : ℕ) (L : NNReal) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (w : Euclid n → ℤ) (Gh : Euclid (n + 1) → Euclid (N + 1)) (Ah : Set (Euclid (n + 1))) (wh : Euclid (n + 1) → ℤ), LipschitzWith L G → MeasurableSet A → Measurable w → IntegrableOn (fun u => (w u : ℝ)) A → (∀ u ∈ A, DifferentiableAt ℝ G u) → (∀ z, Gh z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))))) → Ah = {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → (∀ z, wh z = w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) → LipschitzWith (max 1 L) Gh ∧ MeasurableSet Ah ∧ Measurable wh ∧ IntegrableOn (fun z => (wh z : ℝ)) Ah ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (n + 1)) (η : DifferentialForm (Euclid N) n), (∀ (x : Euclid N) (v : Fin n → Euclid N), η x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (n + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∫ u in A, (w u : ℝ) * η (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) = ∫ z in Ah, (wh z : ℝ) * (ω : DifferentialForm (Euclid (N + 1)) (n + 1)) (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1)) := by
  intro N n L G A w Gh Ah wh hGL hA hw hwi hGd hGh hAh hwh
  obtain ⟨hAhm, hTon, hFub⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  obtain ⟨hLip, hval, hder⟩ := Submission.cmcdt_lpi_cyl_suspension_map N n G Gh hGh
  -- `ŵ = w ∘ tail` is measurable, `tail` being continuous
  have htail : Continuous fun z : Euclid (n + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) := by
    fun_prop
  have hwh' : wh = fun z => w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) := funext hwh
  have hwhm : Measurable wh := by
    rw [hwh']
    exact hw.comp htail.measurable
  -- Tonelli: `∫⁻_Â |ŵ| = ∫⁻_A ∫⁻_{(0,1)} |w(u)| dt du = ∫⁻_A |w| < ∞`
  have hwhi : IntegrableOn (fun z => (wh z : ℝ)) Ah := by
    have hm : Measurable fun z => ‖((wh z : ℤ) : ℝ)‖ₑ :=
      (measurable_from_top (f := fun k : ℤ => ‖(k : ℝ)‖ₑ)).comp hwhm
    refine ⟨((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hwhm).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hAh, hTon _ hm]
    have hfib : ∀ u : Euclid n, (∫⁻ t in Ioo (0 : ℝ) 1,
        ‖((wh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) : ℤ) : ℝ)‖ₑ) = ‖((w u : ℤ) : ℝ)‖ₑ := by
      intro u
      simp [hwh, Real.volume_Ioo]
    simp_rw [hfib]
    exact hwi.2
  refine ⟨hLip L hGL, hAh ▸ hAhm, hwhm, hwhi, ?_⟩
  intro ω η hη
  -- the integrand is integrable on `Â`, so Fubini gives `∫_Â = ∫_A ∫_{(0,1)}`
  have hint := Submission.cmcdt_lpi_cyl_pullback_integrable (N + 1) (n + 1) (max 1 L) Gh Ah
    (fun z => (wh z : ℝ)) ω (hLip L hGL) hwhi
  rw [hAh] at hint ⊢
  rw [hFub _ hint]
  apply setIntegral_congr_fun hA
  intro u hu
  -- `w(u) η(Gu)(DG(u)e) = ∫_{(0,1)} w(u) ω(t, Gu)(e₀, J ∘ DG(u)e) dt` by the slice formula
  simp only
  rw [hη (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)),
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _
  -- on the fibre: `ŵ(t, u) = w(u)`, `Ĝ(t, u) = (t, G u)`, `DĜ(t, u)ê = (e₀, J ∘ DG(u)e)`
  simp only
  rw [hwh, hval, hder t u (hGd u hu)]
  simp

/-- **Simon Ch. 6, 2.18–2.20 and 2.27**, one product piece of the cylinder `[[(0, 1)]] × G_#τ(A, w)`:
with `Ĝ(z) = (z₀, G(tail z))`, `Â = (0, 1) × A` and `ŵ(z) = w(tail z)`, if `c ≥ 0` bounds the action
of `DG(u)` on `n`-covectors at every `u ∈ A`, then `∫_Â ŵ ⟨ω ∘ Ĝ, DĜ ê⟩ ≤ ∫_A |w| c` for every form
`ω` with `|ω| ≤ 1`.  At `z = (t, u) ∈ Â` the frame `DĜ(z) ê` is `(e₀, (0, DG(u) e))`, so the slice
covector bound gives `|ŵ ⟨ω ∘ Ĝ, DĜ ê⟩| ≤ |w(u)| c(u)`; Tonelli on `(0, 1) × A` and
`λ¹((0, 1)) = 1` evaluate the integral of this majorant (as in `M([[(0, 1)]] × T) = M(T)`). -/
theorem Submission.cmcdt_lpi_cyl_piece_mass : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (w : Euclid n → ℤ) (c : Euclid n → ℝ) (Gh : Euclid (n + 1) → Euclid (N + 1)) (Ah : Set (Euclid (n + 1))) (wh : Euclid (n + 1) → ℤ), MeasurableSet A → Measurable w → Measurable c → (∀ u ∈ A, DifferentiableAt ℝ G u) → (∀ u ∈ A, 0 ≤ c u ∧ ∀ α : Covector (Euclid N) n, |α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))| ≤ c u * covectorEuclideanNorm α) → (∀ z, Gh z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0) (WithLp.ofLp (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))))))) → Ah = {z : Euclid (n + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) ∈ A} → (∀ z, wh z = w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) → ∀ ω : DifferentialForm (Euclid (N + 1)) (n + 1), (∀ y, covectorEuclideanNorm (ω y) ≤ 1) → ENNReal.ofReal (∫ z in Ah, (wh z : ℝ) * ω (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1))) ≤ ∫⁻ u in A, ENNReal.ofReal (|(w u : ℝ)| * c u) := by
  intro hL1 hL2 N n G A w c Gh Ah wh hA hw hc hGd hcb hGh hAh hwh ω hω
  -- `Â` is Borel with Tonelli on `(0, 1) × A`, and `DĜ(t, u) ê = (e₀, (0, DG(u) e))`
  obtain ⟨hAhm, hTon, -⟩ := Submission.cmcdt_lpi_cyl_fubini n A hA
  obtain ⟨-, -, hder⟩ := Submission.cmcdt_lpi_cyl_suspension_map N n G Gh hGh
  have htail : Continuous fun z : Euclid (n + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid n) := by
    fun_prop
  -- the measurable majorant `g(z) = |w(tail z)| c(tail z)`
  set g : Euclid (n + 1) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (|((w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℤ) : ℝ)| *
      c (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))) with hg_def
  have hg : Measurable g := by
    have h1 : Measurable fun z : Euclid (n + 1) =>
        ((w (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) : ℤ) : ℝ) :=
      (measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp (hw.comp htail.measurable)
    exact ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp h1).mul (hc.comp htail.measurable))
  -- on `Â`, the slice covector bound and `|ω| ≤ 1` bound the integrand by `g`
  have hpt : ∀ z ∈ Ah,
      ‖(wh z : ℝ) * ω (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1))‖ₑ ≤ g z := by
    intro z hz
    rw [hAh] at hz
    obtain ⟨-, hu⟩ := hz
    set u : Euclid n := WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) with hu_def
    set t : ℝ := WithLp.ofLp z 0 with ht_def
    have hz' : z = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) := by
      simp [hu_def, ht_def]
    have hb := Submission.cmcdt_lpi_cyl_slice_covector_bound hL1 hL2 N n (ω (Gh z))
      (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) (c u) (hcb u hu).1 (hcb u hu).2
    have hD : (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1)) =
        Fin.cons (EuclideanSpace.single 0 1) (fun b => WithLp.toLp 2 (Fin.cons 0
          (WithLp.ofLp (fderiv ℝ G u (EuclideanSpace.single b 1))))) := by
      rw [hz']
      exact hder t u (hGd u hu)
    rw [Real.enorm_eq_ofReal_abs, hg_def]
    apply ENNReal.ofReal_le_ofReal
    rw [hwh, abs_mul, hD]
    calc |((w u : ℤ) : ℝ)| * |ω (Gh z) (Fin.cons (EuclideanSpace.single 0 1) (fun b =>
          WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (fderiv ℝ G u (EuclideanSpace.single b 1))))))|
        ≤ |((w u : ℤ) : ℝ)| * (c u * covectorEuclideanNorm (ω (Gh z))) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |((w u : ℤ) : ℝ)| * (c u * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hω _) (hcb u hu).1)
            (abs_nonneg _)
      _ = _ := by ring
  -- `ofReal ∫_Â F ≤ ∫⁻_Â ‖F‖ₑ ≤ ∫⁻_Â g = ∫⁻_A ∫⁻_(0,1) |w| c = ∫⁻_A |w| c`
  calc ENNReal.ofReal (∫ z in Ah, (wh z : ℝ) * ω (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1)))
      ≤ ‖∫ z in Ah, (wh z : ℝ) * ω (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1))‖ₑ :=
        Real.ofReal_le_enorm _
    _ ≤ ∫⁻ z in Ah, ‖(wh z : ℝ) * ω (Gh z) (fun a => fderiv ℝ Gh z (EuclideanSpace.single a 1))‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z in Ah, g z := setLIntegral_mono' (hAh ▸ hAhm) hpt
    _ = ∫⁻ u in A, ∫⁻ t in Ioo (0 : ℝ) 1, g (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) := by
        rw [hAh]; exact hTon g hg
    _ = ∫⁻ u in A, ENNReal.ofReal (|((w u : ℤ) : ℝ)| * c u) := by
        congr 1; funext u
        simp [hg_def, Real.volume_Ioo]
/-- **Bi-Lipschitz images** (Simon Ch. 2, 1.8(i), applied to `χ` and to its inverse): if
`c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b|` on `E ⊆ ℝⁿ`, then `c₁ⁿ Lⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿ Lⁿ(E)`.
`Hⁿ = μHE[n]` is `c · μH[n]` with one constant `c` on every metric space and equals `volume` on
`ℝⁿ`; `χ` is `c₂`-Lipschitz on `E`, and it is injective there with `c₁⁻¹`-Lipschitz inverse on
`χ(E)`. -/
theorem Submission.dimred_rpd_bilipschitz_image_measure : ∀ (P n : ℕ) (χ : Euclid n → Euclid P) (E : Set (Euclid n)) (c₁ c₂ : ℝ), 0 < c₁ → 0 ≤ c₂ → (∀ a ∈ E, ∀ b ∈ E, c₁ * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ c₂ * ‖a - b‖) → ENNReal.ofReal (c₁ ^ n) * volume E ≤ μHE[n] (χ '' E) ∧ μHE[n] (χ '' E) ≤ ENNReal.ofReal (c₂ ^ n) * volume E := by
  intro P n χ E c₁ c₂ hc₁ hc₂ h
  -- `Lⁿ = Hⁿ` on `ℝⁿ`, and `Hⁿ = c · μH[n]` on every metric space
  have hvol : (volume : Measure (Euclid n)) = μHE[n] :=
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).symm
  have hscale : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
      (μHE[n] : Measure X) S = (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) * μH[(n : ℝ)] S := by
    intro X _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  constructor
  · -- lower bound: `χ` is injective on `E` and its inverse on `χ(E)` is `c₁⁻¹`-Lipschitz
    have hinj : InjOn χ E := by
      intro a ha b hb hab
      have := (h a ha b hb).1
      rw [hab, sub_self, norm_zero] at this
      have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    set g := Function.invFunOn χ E
    have hleft : LeftInvOn g χ E := hinj.leftInvOn_invFunOn
    have hgL : LipschitzOnWith (Real.toNNReal c₁⁻¹) g (χ '' E) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hleft ha, hleft hb, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le)]
      have := (h a ha b hb).1
      rw [inv_mul_eq_div, le_div_iff₀ hc₁]
      linarith
    have himg : g '' (χ '' E) = E := hleft.image_image
    have hle := hgL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [himg] at hle
    rw [hvol, hscale, hscale (χ '' E)]
    set c : ℝ≥0∞ := (Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞)
    have hK : ((Real.toNNReal c₁⁻¹ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₁ ^ n)⁻¹ := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le), ← ENNReal.ofReal_pow (inv_nonneg.2 hc₁.le),
        inv_pow]
    rw [hK] at hle
    have hpos : ENNReal.ofReal (c₁ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hc₁ n)).ne'
    have hinv : ENNReal.ofReal (c₁ ^ n)⁻¹ = (ENNReal.ofReal (c₁ ^ n))⁻¹ :=
      ENNReal.ofReal_inv_of_pos (pow_pos hc₁ n)
    rw [hinv] at hle
    calc ENNReal.ofReal (c₁ ^ n) * (c * μH[(n : ℝ)] E)
        ≤ ENNReal.ofReal (c₁ ^ n) * (c * ((ENNReal.ofReal (c₁ ^ n))⁻¹ * μH[(n : ℝ)] (χ '' E))) := by
          gcongr
      _ = c * μH[(n : ℝ)] (χ '' E) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal (c₁ ^ n)) c, mul_assoc,
            ← mul_assoc (ENNReal.ofReal (c₁ ^ n)), ENNReal.mul_inv_cancel hpos ENNReal.ofReal_ne_top,
            one_mul]
  · -- upper bound: `χ` is `c₂`-Lipschitz on `E`
    have hL : LipschitzOnWith (Real.toNNReal c₂) χ E := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc₂]
      exact (h a ha b hb).2
    have hle := hL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [hvol, hscale, hscale E]
    have hK : ((Real.toNNReal c₂ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₂ ^ n) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc₂,
        ← ENNReal.ofReal_pow hc₂]
    rw [hK] at hle
    calc _ ≤ (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
          (ENNReal.ofReal (c₂ ^ n) * μH[(n : ℝ)] E) := by gcongr
      _ = _ := by ring
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

/-- **Simon 6.2.11, 6.3.2(3)**: assuming (IMC b), that an integer multiplicity triple in an open
`U` restricts to every Borel `E` (carrier `M ∩ E`, same `θ` and `ξ`), an integer multiplicity
current `X = τ(M₀, θ, ξ)` in `U` has a representation carried by `spt X`.  `spt X = U ∖ Z` is
Borel (`Z` open), and `Hⁿ(M₀ ∖ spt X) = 0` (`imrep_carrier_sdiff_support_null`), so
`M₀ ∩ spt X = M₀` `Hⁿ`-a.e.  (IMC b) with `E = spt X` gives `R' = (M₀ ∩ spt X, θ, ξ)`; set
integrals over a.e.-equal sets agree, so `R'` has the action of `R`, i.e. represents `X`. -/
theorem Submission.cmcdt_lpi_pr_imrep_in_support : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → ∀ (N n : ℕ) (U : Set (Euclid N)) (X : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity X → ∃ R : IMRep U n, R.Represents X ∧ R.carrier ⊆ X.support := by
  intro hIMCb N n U X hU hXim
  obtain ⟨R, hR⟩ := hXim
  -- `spt X = U ∖ Z` is Borel, the zero region `Z` being open
  have hSm : MeasurableSet X.support := by
    rw [show X.support = U \ X.zeroRegion from rfl]
    exact hU.measurableSet.diff X.isOpen_zeroRegion.measurableSet
  -- `Hⁿ(M₀ ∖ spt X) = 0`
  have hnull : μHE[n] (R.carrier \ X.support) = 0 :=
    Submission.imrep_carrier_sdiff_support_null N n U X R hU hR
  -- restrict the representation to `spt X`: `R' = (M₀ ∩ spt X, θ, ξ)`
  obtain ⟨_, R', -, hcar, hmult, hor⟩ := hIMCb N n U R X.support hU hSm
  refine ⟨R', fun ω => ?_, hcar ▸ inter_subset_right⟩
  -- `M₀ ∩ spt X = M₀` `Hⁿ`-a.e., so the two actions agree
  rw [hR ω]
  unfold IMRep.action
  rw [hcar, hmult, hor]
  refine setIntegral_congr_set (ae_eq_set.mpr ⟨measure_mono_null ?_ hnull, ?_⟩)
  · rintro x ⟨hxM, hxMS⟩
    exact ⟨hxM, fun hxS => hxMS ⟨hxM, hxS⟩⟩
  · rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty]

/-- **Pulling back integrals from a Lipschitz piece** (Simon Ch. 6, 3.6–3.9, using Ch. 2,
1.8(i)): if `G` is `L`-Lipschitz and `m|a − a'| ≤ |G(a) − G(a')|` on a Borel set `A ⊆ ℝⁿ`,
`m > 0`, then the image of `Lⁿ⌞A` under `G` is at most `m⁻ⁿ Hⁿ⌞G(A)`, so
`∫_A f ∘ G dLⁿ ≤ m⁻ⁿ ∫_{G(A)} f dHⁿ` for every Borel `f ≥ 0`.  The bound
`Lⁿ(E) ≤ m⁻ⁿ Hⁿ(G(E))` for `E ⊆ A` is the lower half of
`Submission.dimred_rpd_bilipschitz_image_measure`. -/
theorem Submission.cmcdt_lpi_pr_lintegral_pullback : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L G → MeasurableSet A → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → ∀ f : Euclid P → ℝ≥0∞, Measurable f → ∫⁻ u in A, f (G u) ≤ ENNReal.ofReal ((m ^ n)⁻¹) * ∫⁻ x in G '' A, f x ∂μHE[n] := by
  intro P n G A L m hL hA hm hlow f hf
  have hGm : Measurable G := hL.continuous.measurable
  -- `Lⁿ(E) ≤ m⁻ⁿ Hⁿ(G(E))` for `E ⊆ A`
  have hbound : ∀ E ⊆ A, volume E ≤ ENNReal.ofReal ((m ^ n)⁻¹) * μHE[n] (G '' E) := by
    intro E hE
    have h := (Submission.dimred_rpd_bilipschitz_image_measure P n G E m L hm L.coe_nonneg
      (fun a ha b hb => ⟨hlow a (hE ha) b (hE hb), by
        have := hL.dist_le_mul a b
        rwa [dist_eq_norm, dist_eq_norm] at this⟩)).1
    have hpos : (0 : ℝ) < m ^ n := pow_pos hm n
    calc volume E = ENNReal.ofReal ((m ^ n)⁻¹) * (ENNReal.ofReal (m ^ n) * volume E) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le),
            inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal ((m ^ n)⁻¹) * μHE[n] (G '' E) := by gcongr
  -- the image of `Lⁿ⌞A` under `G` is at most `m⁻ⁿ Hⁿ⌞G(A)`
  have hle : Measure.map G (volume.restrict A) ≤
      ENNReal.ofReal ((m ^ n)⁻¹) • μHE[n].restrict (G '' A) := by
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.map_apply hGm hS, Measure.restrict_apply' hA, Measure.smul_apply,
      Measure.restrict_apply hS, smul_eq_mul]
    refine (hbound _ inter_subset_right).trans ?_
    gcongr
    rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨hu1, mem_image_of_mem G hu2⟩
  calc ∫⁻ u in A, f (G u) = ∫⁻ x, f x ∂(Measure.map G (volume.restrict A)) :=
        (lintegral_map hf hGm).symm
    _ ≤ ∫⁻ x, f x ∂(ENNReal.ofReal ((m ^ n)⁻¹) • μHE[n].restrict (G '' A)) :=
        lintegral_mono' hle le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
/-- Regular part of a Lipschitz parametrization (steps 1–2 of the proof that the Lipschitz
push-forward of an integer multiplicity current is integer multiplicity, Simon 6.3.6–3.9).  Let
`H : ℝⁿ → ℝᴾ` be `L`-Lipschitz, `A ⊆ ℝⁿ` Borel and `g : ℝⁿ → ℤ` measurable and integrable on `A`.
Then `A⁺ = {u ∈ A : DH(u) exists and is injective, g(u) ≠ 0}` is Borel, and for every test form
`ω` the function `Ψ_ω(u) = g(u) ω(H(u))(DH(u)e₁, …, DH(u)eₙ)` is integrable on `A` with
`∫_A Ψ_ω = ∫_{A⁺} Ψ_ω`.  Injective linear maps form an open set, so `A⁺` is Borel;
`|Ψ_ω| ≤ (sup ‖ω‖) Lⁿ |g|`; and by Rademacher `Ψ_ω = 0` a.e. on `A \ A⁺`: where `DH(u)` is not
injective, `(DH(u)eₐ)ₐ` is linearly dependent and the alternating map `ω(H(u))` vanishes on it. -/
theorem Submission.cmcdt_lpi_pc_regular_part_reduction : ∀ (P n : ℕ) (L : NNReal) (H : Euclid n → Euclid P) (A : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet A → Measurable g → IntegrableOn (fun u => (g u : ℝ)) A → MeasurableSet {u | u ∈ A ∧ DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u) ∧ g u ≠ 0} ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, IntegrableOn (fun u => (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) A ∧ ∫ u in A, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) = ∫ u in {u | u ∈ A ∧ DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u) ∧ g u ≠ 0}, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
  intro P n L H A g hH hA hg hgi
  -- `eₐ = EuclideanSpace.single a 1` spans `ℝⁿ`
  have hspan :
      Submodule.span ℝ (range fun a : Fin n => (EuclideanSpace.single a 1 : Euclid n)) = ⊤ := by
    have he : (fun a : Fin n => (EuclideanSpace.single a 1 : Euclid n)) =
        ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis := by
      ext1 a
      simp [EuclideanSpace.basisFun_apply]
    rw [he]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
  -- step 1: `T` is injective if `(T eₐ)ₐ` is linearly independent
  have hinj : ∀ T : Euclid n →L[ℝ] Euclid P,
      LinearIndependent ℝ (fun a => T (EuclideanSpace.single a 1)) → Injective T := fun T h =>
    LinearMap.injective_of_linearIndependent (f := T.toLinearMap) hspan h
  -- step 2: injective maps form an open set, so `A⁺` is Borel
  have hS : MeasurableSet
      {u | u ∈ A ∧ DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u) ∧ g u ≠ 0} :=
    hA.inter ((measurableSet_of_differentiableAt ℝ H).inter
      ((measurable_fderiv ℝ H ContinuousLinearMap.isOpen_injective.measurableSet).inter
        (hg (measurableSet_singleton 0).compl)))
  refine ⟨hS, fun ω => ?_⟩
  obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
  have hwc : Continuous (ω : DifferentialForm (Euclid P) n) := hsmooth.continuous
  obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support hcpt
  -- step 3: `u ↦ ω(H(u))(DH(u)e₁, …, DH(u)eₙ)` is Borel
  have hF : StronglyMeasurable fun u => (ω : DifferentialForm (Euclid P) n) (H u)
      (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
    have h1 : StronglyMeasurable fun u => (ω : DifferentialForm (Euclid P) n) (H u) :=
      (hwc.comp hH.continuous).stronglyMeasurable
    have h2 : StronglyMeasurable fun u => fun a : Fin n =>
        fderiv ℝ H u (EuclideanSpace.single a 1) :=
      (Measurable.of_eval fun a => measurable_fderiv_apply_const ℝ H _).stronglyMeasurable
    exact continuous_eval.comp_stronglyMeasurable (h1.prodMk h2)
  -- step 4: `|Ψ_ω| ≤ C Lⁿ |g|`, as `‖ω‖ ≤ C` and `‖DH‖ ≤ L`
  have hbound : ∀ u, ‖(ω : DifferentialForm (Euclid P) n) (H u)
      (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))‖ ≤ C * ∏ _a : Fin n, (L : ℝ) := by
    intro u
    refine ((ω : DifferentialForm (Euclid P) n) (H u)).le_mul_prod_of_opNorm_le_of_le (hC (H u))
      fun a => ?_
    calc ‖fderiv ℝ H u (EuclideanSpace.single a 1)‖
        ≤ ‖fderiv ℝ H u‖ * ‖(EuclideanSpace.single a 1 : Euclid n)‖ := (fderiv ℝ H u).le_opNorm _
      _ ≤ L * 1 := by
        gcongr
        · exact norm_fderiv_le_of_lipschitz ℝ hH
        · simp
      _ = L := mul_one _
  refine ⟨hgi.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hbound), ?_⟩
  -- steps 5–6: by Rademacher, `Ψ_ω = 0` a.e. on `A \ A⁺`
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hA.nullMeasurableSet (fun u hu => hu.1) ?_
  filter_upwards [hH.ae_differentiableAt (μ := volume)] with u hdiff hu
  by_cases hgu : g u = 0
  · simp [hgu]
  · have hni : ¬LinearIndependent ℝ fun a => fderiv ℝ H u (EuclideanSpace.single a 1) :=
      fun h => hu.2 ⟨hu.1, hdiff, hinj _ h, hgu⟩
    rw [← ContinuousAlternatingMap.coe_toAlternatingMap,
      AlternatingMap.map_linearDependent _ _ hni, mul_zero]
/-- Countable bi-Lipschitz partition: if `H : ℝⁿ → ℝᴾ` is differentiable with injective derivative
at every point of the Borel set `B`, then `B` is the disjoint union of countably many Borel pieces
`C l` with `κ l ‖a - a'‖ ≤ ‖H a - H a'‖` on `C l`, `κ l > 0`.  For injective `A` pick `c(A) > 0`
with `2 c(A) ‖v‖ ≤ ‖A v‖` (an antilipschitz constant), else `c(A) = 1`.  Mathlib's partition of `B`
into Borel `t l` with `‖H a - H a' - A l (a - a')‖ ≤ c(A l) ‖a - a'‖` on `B ∩ t l`, where
`A l = DH(y)` for some `y ∈ B`, gives `κ l = c(A l)` by the triangle inequality. -/
theorem Submission.cmcdt_lpi_pc_bilipschitz_partition : ∀ (P n : ℕ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → ∃ (C : ℕ → Set (Euclid n)) (κ : ℕ → ℝ), (∀ l, MeasurableSet (C l)) ∧ Pairwise (fun l l' => Disjoint (C l) (C l')) ∧ (⋃ l, C l) = B ∧ (∀ l, 0 < κ l) ∧ ∀ l, ∀ a ∈ C l, ∀ a' ∈ C l, κ l * ‖a - a'‖ ≤ ‖H a - H a'‖ := by
  intro P n H B hB hH
  -- coercivity constants: `2 c(A) ‖v‖ ≤ ‖A v‖` for injective `A`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ v, 2 * (c : ℝ) * ‖v‖ ≤ ‖A v‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨K, hK, hKA⟩ := LinearMap.exists_antilipschitzWith (A : Euclid n →ₗ[ℝ] Euclid P)
        (LinearMap.ker_eq_bot.mpr hA)
      refine ⟨K⁻¹ / 2, div_pos (inv_pos.mpr hK) two_pos, fun _ v => ?_⟩
      have hK' : (0 : ℝ) < K := hK
      have hv : ‖v‖ ≤ K * ‖A v‖ := by
        simpa using hKA.le_mul_dist v 0
      calc 2 * ((K⁻¹ / 2 : NNReal) : ℝ) * ‖v‖ = (K : ℝ)⁻¹ * ‖v‖ := by push_cast; ring
        _ ≤ (K : ℝ)⁻¹ * (K * ‖A v‖) := by gcongr
        _ = ‖A v‖ := by rw [← mul_assoc, inv_mul_cancel₀ hK'.ne', one_mul]
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- pieces `B ∩ t l` on which `H` is `c(A l)`-close to the linear map `A l = DH(y_l)`
  obtain ⟨t, A, htdisj, htmeas, hBt, hAapprox, hAder⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt H B (fderiv ℝ H)
      (fun x hx => (hH x hx).1.hasFDerivAt.hasFDerivWithinAt) c fun A => (hcpos A).ne'
  refine ⟨fun l => B ∩ t l, fun l => c (A l), fun l => hB.inter (htmeas l), ?_, ?_,
    fun l => hcpos (A l), ?_⟩
  · intro l l' hll'
    exact (htdisj hll').mono inter_subset_right inter_subset_right
  · show (⋃ l, B ∩ t l) = B
    rw [← inter_iUnion]
    exact inter_eq_left.mpr hBt
  · intro l a ha a' ha'
    show (c (A l) : ℝ) * ‖a - a'‖ ≤ ‖H a - H a'‖
    obtain ⟨y, hy, hAy⟩ := hAder ⟨a, ha.1⟩ l
    have hinj : Injective (A l) := by
      rw [hAy]
      exact (hH y hy).2
    have h1 := hc (A l) hinj (a - a')
    have h2 := hAapprox l a ha a' ha'
    have h3 := norm_sub_le (H a - H a') (H a - H a' - A l (a - a'))
    rw [sub_sub_cancel] at h3
    linarith
/-- **Lusin–Souslin**: if `H : ℝⁿ → ℝᴾ` is continuous and injective on a Borel set `B`, then
`H(B)` is Borel and `H` has a Borel left inverse on `B`.  The restriction `B.domRestrict H` is a
measurable embedding (`ℝⁿ` is Polish), so its inverse on `H(B)`, extended by `0`, is Borel. -/
theorem Submission.cmcdt_lpi_pc_measurable_inverse : ∀ (P n : ℕ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), ContinuousOn H B → MeasurableSet B → InjOn H B → MeasurableSet (H '' B) ∧ ∃ h : Euclid P → Euclid n, Measurable h ∧ ∀ u ∈ B, h (H u) = u := by
  intro P n H B hH hB hinj
  refine ⟨hB.image_of_continuousOn_injOn hH hinj, ?_⟩
  -- `h` inverts `B.domRestrict H` on its range and is `0` off it
  obtain ⟨h, hh, hcomp⟩ := (hH.measurableEmbedding hB hinj).exists_measurable_extend
    measurable_subtype_coe fun _ => ⟨0⟩
  exact ⟨h, hh, fun u hu => congrFun hcomp ⟨u, hu⟩⟩
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
/-- Orientation along a bi-Lipschitz piece: assume the locality (IMC a) of approximate tangent
planes.  Let `M ⊆ ℝᴺ` be Borel with `Hⁿ(M ∩ K) < ∞` for compact `K`, and let `ξ` be
`Hⁿ⌞M`-measurable and orient `TₓM` for `Hⁿ`-a.e. `x ∈ M` (Simon Ch. 6, 3.1).  If `G : ℝⁿ → ℝᴺ`
is Lipschitz, `A ⊆ ℝⁿ` is Borel with `G(A) ⊆ M`, `m‖a − a'‖ ≤ ‖G a − G a'‖` on `A` (`m > 0`),
and `DG(a)` exists and is injective for `a ∈ A`, then `ξ ∘ G` is `λ⌞A`-measurable and, for
`λ`-a.e. `u ∈ A`, `ξ(G u)` orients `span{DG(u)e_a} = range DG(u)`: this plane is the approximate
tangent plane of `G(A)` at `G u`, hence (by locality) of `M`, and approximate tangent planes are
unique (Ch. 3, 1.5(1)). -/
theorem Submission.cmcdt_lpi_pr_piece_orientation_ae : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (N n : ℕ) (M : Set (Euclid N)) (ξ : Euclid N → MultiVector N n) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (L : NNReal) (m : ℝ), MeasurableSet M → (∀ K : Set (Euclid N), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → AEStronglyMeasurable ξ (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid N), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ξ x) Q) → LipschitzWith L G → MeasurableSet A → 0 < m → (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ M → AEStronglyMeasurable (fun u => ξ (G u)) (volume.restrict A) ∧ ∀ᵐ u ∂(volume.restrict A), IsUnitOrientationOf (ξ (G u)) (Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)))) := by
  intro hIMCa N n M ξ G A L m hM hloc hξ hor hL hA hm hlow hdiff hGAsub
  obtain ⟨hGAm, hpull⟩ :=
    Submission.ptd_piece_image_measurable_ae_pullback N n G A L m hL hA hm hlow
  -- (a) the piece has tangent plane `range DG(u)`
  have htan := Submission.ptd_piece_image_approxTangent_ae N n G A L m hL hA hm hlow hdiff
  -- (b) locality of approximate tangent planes, pulled back
  have hlocal := hIMCa N n univ (G '' A) M isOpen_univ hGAm hM hGAsub (subset_univ _)
    (fun K hK _ => hloc K hK)
  have hlocal' := hpull _ hlocal
  -- (c) the orientation property, pulled back
  have hor' := hpull _ (ae_restrict_of_ae_restrict_of_subset hGAsub hor)
  -- (d) a strongly measurable version of `ξ`, pulled back
  have hξ' := hpull _ (ae_restrict_of_ae_restrict_of_subset hGAsub hξ.ae_eq_mk)
  refine ⟨⟨fun u => hξ.mk ξ (G u),
    hξ.stronglyMeasurable_mk.comp_measurable hL.continuous.measurable, ?_⟩, ?_⟩
  · filter_upwards [hξ'] with u hu using hu
  · filter_upwards [htan, hlocal', hor'] with u h1 h2 h3
    obtain ⟨Q, hQ, hQor⟩ := h3
    -- uniqueness of approximate tangent planes: `Q = range DG(u)`
    have hQeq := hQ.unique ((h2 _).mp h1)
    -- `range DG(u) = span{DG(u)e_a}`, the `e_a` spanning `ℝⁿ`
    have hrange : LinearMap.range (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N) =
        Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))) := by
      rw [LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq,
        Submodule.map_span, ← Set.range_comp]
      congr 2
      funext a
      simp
    rw [← hrange, ← hQeq]
    exact hQor
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

/-- **Simon Ch. 6, 2.4** (the `M`-absolutely convergent series in the proof of 7.2): assume (VO),
that a current vanishes on test forms supported off its support.  If `U` is open and
`X_r ∈ 𝒟ₙ(U)` with `∑ᵣ M(X_r) < ∞`, then `Y(ω) = ∑ᵣ X_r(ω)` is a current `Y ∈ 𝒟ₙ(U)` with
`M(Y) ≤ ∑ᵣ M(X_r)` and `spt Y ⊆ closure (⋃ᵣ spt X_r)`.  Admissibility of `±c⁻¹ω` gives
`|Z(ω)| ≤ c M(Z)` whenever `|ω(x)| ≤ c`, so the series converges absolutely; uniform smallness of
test forms tending to `0` makes the sum sequentially continuous; for admissible `ω`,
`ofReal(Y(ω)) ≤ ∑ᵣ ofReal(X_r(ω)) ≤ ∑ᵣ M(X_r)`; and (VO) makes `Y` vanish on a small ball around
each point of `U ∖ closure (⋃ᵣ spt X_r)`. -/
theorem Submission.cmcdt_ims_series_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U n), IsOpen U → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass ∧ Y.support ⊆ closure (⋃ r, (X r).support) := by
  intro hVO P n U X hU hX
  -- Step 1 (reused rsd_mw_tfa_norm_props): `|t α| = |t| |α|`, `|α| ≤ C ‖α‖`, `|·|` continuous
  have hhom := (Submission.rsd_mw_tfa_norm_props P n).2.1
  -- Step 3: `|Z(ω)| ≤ c M(Z)` whenever `|ω(x)| ≤ c` for all `x`
  have h3 : ∀ (Z : GeometricCurrentOn U n) (ω : TestFormOn U n) (c : ℝ), 0 < c → Z.mass ≠ ∞ →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      |Z ω| ≤ c * Z.mass.toReal := by
    intro Z ω c hc hZ hω
    have key : ∀ s : ℝ, |s| = c⁻¹ → s * Z ω ≤ Z.mass.toReal := by
      intro s hs
      have hadm : s • ω ∈ massAdmissibleOn U n U := by
        refine ⟨(s • ω).property.2, fun x => ?_⟩
        have hx : ((s • ω : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
            s • ((ω : DifferentialForm (Euclid P) n) x) := rfl
        rw [hx, hhom, hs]
        calc c⁻¹ * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
            ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (hω x) (inv_nonneg.mpr hc.le)
          _ = 1 := inv_mul_cancel₀ hc.ne'
      have h1 : ENNReal.ofReal (Z (s • ω)) ≤ Z.mass := Z.le_massOn hadm
      rw [ENNReal.ofReal_le_iff_le_toReal hZ] at h1
      have hlin : Z (s • ω) = s * Z ω := by
        rw [map_smul, smul_eq_mul]
      rwa [hlin] at h1
    have hp := key c⁻¹ (abs_of_pos (inv_pos.mpr hc))
    have hn := key (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc)])
    rw [abs_le]
    constructor
    · have h' : c * (-c⁻¹ * Z ω) ≤ c * Z.mass.toReal := mul_le_mul_of_nonneg_left hn hc.le
      have : c * (-c⁻¹ * Z ω) = -(Z ω) := by field_simp
      linarith
    · have h' : c * (c⁻¹ * Z ω) ≤ c * Z.mass.toReal := mul_le_mul_of_nonneg_left hp hc.le
      have : c * (c⁻¹ * Z ω) = Z ω := by field_simp
      linarith
  -- Step 2: every test form has bounded coefficient norm
  have h4 : ∀ ω : TestFormOn U n, ∃ c : ℝ, 0 < c ∧
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c := by
    intro ω
    have hsmooth : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
    have hcont : Continuous (fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)) :=
      (Submission.rsd_mw_tfa_norm_props P n).2.2.2.comp (ContDiff.continuous hsmooth)
    have hcs : HasCompactSupport (fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)) :=
      HasCompactSupport.comp_left (g := covectorEuclideanNorm) ω.property.1.2 (covectorEuclideanNorm_zero P n)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
    refine ⟨max C 0 + 1, by positivity, fun x => ?_⟩
    have h := hC x
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)), le_max_left C 0]
  -- Step 7: a linear functional with `|L(ω)| ≤ c A` whenever `|ω| ≤ c` is a current
  have h5 : ∀ (L : TestFormOn U n →ₗ[ℝ] ℝ) (A : ℝ), (∀ (ω : TestFormOn U n) (c : ℝ), 0 < c →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |L ω| ≤ c * A) →
      ∃ Y : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, Y ω = L ω := by
    intro L A hL
    obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P n).2.2.1
    have hA : 0 ≤ A := by
      have h0 := hL 0 1 one_pos (fun x => by simp)
      simpa using h0
    refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => rfl⟩
    obtain ⟨K, -, -, -, hunif⟩ := Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
    rw [Metric.tendsto_atTop]
    intro η hη
    set ε : ℝ := η / (2 * (C + 1) * (A + 1)) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hεpos)
    refine ⟨N, fun j hj => ?_⟩
    have hb : ∀ x, covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x) ≤ (C + 1) * ε := by
      intro x
      calc covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x)
          ≤ C * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := hC _
        _ ≤ C * ε := mul_le_mul_of_nonneg_left (hN j hj x) hC0
        _ ≤ (C + 1) * ε := by nlinarith
    have hLj := hL (ωs j) ((C + 1) * ε) (by positivity) hb
    rw [Real.dist_eq, sub_zero]
    have hkey : (C + 1) * ε * A < η := by
      have h1 : (C + 1) * ε * (A + 1) = η / 2 := by
        rw [hε]; field_simp
      nlinarith
    exact lt_of_le_of_lt hLj hkey
  -- Steps 4-6: absolute summability, the linear functional `L = Σ X_r`, its bound
  have hXr : ∀ r, (X r).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hX
  have hm : Summable (fun r => (X r).mass.toReal) := ENNReal.summable_toReal hX
  have hms : (∑' r, (X r).mass).toReal = ∑' r, (X r).mass.toReal := ENNReal.tsum_toReal_eq hXr
  have hbound : ∀ (ω : TestFormOn U n) (c : ℝ), 0 < c →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      ∀ r, |X r ω| ≤ c * (X r).mass.toReal :=
    fun ω c hc hω r => h3 (X r) ω c hc (hXr r) hω
  have hsumm_abs : ∀ ω : TestFormOn U n, Summable (fun r => |X r ω|) := by
    intro ω
    obtain ⟨c, hc, hω⟩ := h4 ω
    exact Summable.of_nonneg_of_le (fun r => abs_nonneg _) (hbound ω c hc hω) (hm.mul_left c)
  have hsumm : ∀ ω : TestFormOn U n, Summable (fun r => X r ω) := fun ω =>
    Summable.of_norm_bounded (hsumm_abs ω) (fun r => by rw [Real.norm_eq_abs])
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑' r, X r ω
      map_add' := fun ω ω' => by
        simp only [map_add]
        exact (hsumm ω).tsum_add (hsumm ω')
      map_smul' := fun t ω => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
  have hLbound : ∀ (ω : TestFormOn U n) (c : ℝ), 0 < c →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      |L ω| ≤ c * (∑' r, (X r).mass).toReal := by
    intro ω c hc hω
    show |∑' r, X r ω| ≤ _
    rw [hms]
    calc |∑' r, X r ω| ≤ ∑' r, |X r ω| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun r => X r ω) (by simpa [Real.norm_eq_abs] using hsumm_abs ω)
      _ ≤ ∑' r, c * (X r).mass.toReal :=
          Summable.tsum_le_tsum (hbound ω c hc hω) (hsumm_abs ω) (hm.mul_left c)
      _ = c * ∑' r, (X r).mass.toReal := tsum_mul_left
  obtain ⟨Y, hY⟩ := h5 L _ hLbound
  have hYsum : ∀ ω : TestFormOn U n, HasSum (fun r => X r ω) (Y ω) := by
    intro ω
    rw [hY ω]
    exact (hsumm ω).hasSum
  refine ⟨Y, hYsum, ?_, ?_⟩
  · -- Step 8: the mass bound
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    have hpos_summ : Summable (fun r => max (X r ω) 0) :=
      Summable.of_nonneg_of_le (fun r => le_max_right _ _)
        (fun r => max_le (le_abs_self _) (abs_nonneg _)) (hsumm_abs ω)
    calc ENNReal.ofReal (Y ω) = ENNReal.ofReal (∑' r, X r ω) := by rw [(hYsum ω).tsum_eq]
      _ ≤ ENNReal.ofReal (∑' r, max (X r ω) 0) :=
          ENNReal.ofReal_le_ofReal
            (Summable.tsum_le_tsum (fun r => le_max_left _ _) (hsumm ω) hpos_summ)
      _ = ∑' r, ENNReal.ofReal (max (X r ω) 0) :=
          ENNReal.ofReal_tsum_of_nonneg (fun r => le_max_right _ _) hpos_summ
      _ = ∑' r, ENNReal.ofReal (X r ω) := by
          congr 1
          funext r
          rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
      _ ≤ ∑' r, (X r).mass := ENNReal.tsum_le_tsum (fun r => (X r).le_massOn hω)
  · -- Step 9: the support bound, from (VO)
    intro x hx
    by_contra hxE
    set E := closure (⋃ r, (X r).support) with hEdef
    have hxU : x ∈ U := Y.support_subset_domain hx
    have hopen : IsOpen (U \ E) := hU.sdiff isClosed_closure
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨hxU, hxE⟩
    set W := ball x (ε / 2) with hWdef
    have hclW : closure W ⊆ ball x ε :=
      (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by linarith))
    have hWzero : W ⊆ Y.zeroRegion := by
      refine subset_sUnion_of_mem ⟨isOpen_ball, ?_, ?_, ?_⟩
      · exact isBounded_ball.isCompact_closure
      · exact hclW.trans (hball.trans sdiff_subset)
      · intro ω hω
        have hX0 : ∀ r, X r ω = 0 := by
          intro r
          apply hVO
          rw [Set.disjoint_iff]
          intro y ⟨hy1, hy2⟩
          have hyE : y ∈ E := subset_closure (mem_iUnion.mpr ⟨r, hy2⟩)
          have hyW : y ∈ U \ E := hball (hclW (subset_closure (hω hy1)))
          exact hyW.2 hyE
        have h0 : HasSum (fun r => X r ω) 0 := by
          simp only [hX0]; exact hasSum_zero
        exact (hYsum ω).unique h0
    exact hx.2 (hWzero (mem_ball_self (by linarith)))
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
/-- **Pull-back of a covector, summed over all index tuples** (the coefficient bound behind the
push-forward mass estimates of Simon Ch. 6, 2.24(2) and 2.27): for a continuous linear
`A : ℝᴺ → ℝᴺ'` and an `m`-covector `γ` on `ℝᴺ'`, with `e`, `e'` the standard bases,
`Σ_j (A^#γ)(e_{j(0)}, …, e_{j(m−1)})² ≤ (‖A‖²)ᵐ Σ_j γ(e'_{j(0)}, …, e'_{j(m−1)})²`, both sums over
all index maps `j`.  Induction on `m`, peeling off the first slot with `curryLeft`: for fixed `j`,
`μ(u) = γ(u, e'_{j(0)}, …, e'_{j(m−1)})` is a linear functional, and
`Σ_a μ(A e_a)² = ‖μ ∘ A‖² ≤ ‖A‖² ‖μ‖² = ‖A‖² Σ_b μ(e'_b)²` (Parseval,
`dorag_ha_lsc_grad_norm_sq`). -/
theorem Submission.cmcdt_lp_pullback_basis_sq_sum_le : ∀ (N N' m : ℕ) (A : Euclid N →L[ℝ] Euclid N') (γ : Covector (Euclid N') m), ∑ j : Fin m → Fin N, ((γ.compContinuousLinearMap A) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (j i))) ^ 2 ≤ (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N', (γ (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 := by
  intro N N' m A γ
  -- Parseval for functionals: `Σ_c μ(e_c)² = ‖μ‖²` (`grad_norm_sq`, with `e_c = single c 1`)
  have hpars : ∀ (M : ℕ) (μ : Euclid M →L[ℝ] ℝ),
      ∑ c : Fin M, μ (EuclideanSpace.basisFun (Fin M) ℝ c) ^ 2 = ‖μ‖ ^ 2 := by
    intro M μ
    rw [(Submission.dorag_ha_lsc_grad_norm_sq M μ).1]
    simp only [EuclideanSpace.basisFun_apply]
  -- one-slot estimate: `Σ_a μ(A e_a)² = ‖μ ∘ A‖² ≤ ‖A‖² ‖μ‖² = ‖A‖² Σ_b μ(e'_b)²`
  have hone : ∀ μ : Euclid N' →L[ℝ] ℝ,
      ∑ a : Fin N, μ (A (EuclideanSpace.basisFun (Fin N) ℝ a)) ^ 2 ≤
        ‖A‖ ^ 2 * ∑ b : Fin N', μ (EuclideanSpace.basisFun (Fin N') ℝ b) ^ 2 := by
    intro μ
    have h := hpars N (μ.comp A)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, hpars N' μ]
    calc ‖μ.comp A‖ ^ 2 ≤ (‖μ‖ * ‖A‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le μ A) 2
      _ = ‖A‖ ^ 2 * ‖μ‖ ^ 2 := by ring
  -- induction on the degree, for all covectors `γ` of that degree
  induction m with
  | zero =>
    -- one (empty) index tuple on each side, and the two empty tuples of vectors agree
    rw [pow_zero, one_mul, Fintype.sum_unique, Fintype.sum_unique,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact le_of_eq (congrArg (· ^ 2) (congrArg γ (Subsingleton.elim _ _)))
  | succ m ih =>
    -- first-slot reindexing `J = Fin.cons c j`
    have hsplit : ∀ (M : ℕ) (F : (Fin (m + 1) → Fin M) → ℝ),
        ∑ J : Fin (m + 1) → Fin M, F J = ∑ c : Fin M, ∑ j : Fin m → Fin M, F (Fin.cons c j) := by
      intro M F
      rw [← (Fin.consEquiv fun _ => Fin M).sum_comp, Fintype.sum_prod_type]
      rfl
    -- `δ(e ∘ Fin.cons c j) = (ι_{e_c} δ)(e ∘ j)`
    have hcons : ∀ (M : ℕ) (δ : Covector (Euclid M) (m + 1)) (c : Fin M) (j : Fin m → Fin M),
        δ (fun i => EuclideanSpace.basisFun (Fin M) ℝ ((Fin.cons c j : Fin (m + 1) → Fin M) i)) =
          δ.curryLeft (EuclideanSpace.basisFun (Fin M) ℝ c)
            (fun i => EuclideanSpace.basisFun (Fin M) ℝ (j i)) := by
      intro M δ c j
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 1
      ext i : 1
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    -- the one-slot estimate for `μ_j(u) = (ι_u γ)(e' ∘ j)`, continuous linear in `u`
    have hμ : ∀ j : Fin m → Fin N',
        ∑ a : Fin N, (γ.curryLeft (A (EuclideanSpace.basisFun (Fin N) ℝ a))
            (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 ≤
          ‖A‖ ^ 2 * ∑ b : Fin N', (γ.curryLeft (EuclideanSpace.basisFun (Fin N') ℝ b)
            (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 :=
      fun j => hone ((ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ
        (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))).comp γ.curryLeft)
    calc ∑ J : Fin (m + 1) → Fin N,
          ((γ.compContinuousLinearMap A) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (J i))) ^ 2
        = ∑ a : Fin N, ∑ j : Fin m → Fin N,
            (((γ.curryLeft (A (EuclideanSpace.basisFun (Fin N) ℝ a))).compContinuousLinearMap A)
              (fun i => EuclideanSpace.basisFun (Fin N) ℝ (j i))) ^ 2 := by
          rw [hsplit N]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hcons, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap]
      _ ≤ ∑ a : Fin N, (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N',
            (γ.curryLeft (A (EuclideanSpace.basisFun (Fin N) ℝ a))
              (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 :=
          Finset.sum_le_sum fun a _ => ih _
      _ = (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N', ∑ a : Fin N,
            (γ.curryLeft (A (EuclideanSpace.basisFun (Fin N) ℝ a))
              (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N', ‖A‖ ^ 2 * ∑ b : Fin N',
            (γ.curryLeft (EuclideanSpace.basisFun (Fin N') ℝ b)
              (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 := by
          gcongr with j
          exact hμ j
      _ = (‖A‖ ^ 2) ^ (m + 1) * ∑ J : Fin (m + 1) → Fin N',
            (γ (fun i => EuclideanSpace.basisFun (Fin N') ℝ (J i))) ^ 2 := by
          -- reindex back with `Fin.cons` and collect `(‖A‖²)ᵐ ‖A‖² = (‖A‖²)ᵐ⁺¹`
          rw [hsplit N', Finset.sum_comm, ← Finset.mul_sum, ← mul_assoc, ← pow_succ]
          simp only [hcons]

/-- **Pull-back bound for the Euclidean coefficient norm** (Simon 6.1, the pointwise pull-back
`f^#ω` of (6.1.13)): for a continuous linear `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β` on `ℝᴺ'`, the
pull-back `A^#β = β.compContinuousLinearMap A`, `A^#β(w₁, …, w_k) = β(Aw₁, …, Aw_k)`, satisfies
`|A^#β|_E ≤ ‖A‖ᵏ |β|_E`.  Over all index tuples, `Σ_j (A^#β)(e ∘ j)² ≤ (‖A‖²)ᵏ Σ_j β(e' ∘ j)²` for
the standard bases `e`, `e'` (`cmcdt_lp_pullback_basis_sq_sum_le`), and both sums are `k!` times
the squared coefficient norms (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `k! > 0` and
take square roots. -/
theorem Submission.cmcdt_lp_covector_pullback_norm_le : ∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β := by
  intro N N' k A β
  -- `k! |A^#β|_E² = Σ_j (A^#β)(e ∘ j)² ≤ (‖A‖²)ᵏ Σ_j β(e' ∘ j)² = (‖A‖²)ᵏ k! |β|_E²`
  have key : (k.factorial : ℝ) * covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2 ≤
      (k.factorial : ℝ) * (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 :=
    calc (k.factorial : ℝ) * covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2
        = ∑ j : Fin k → Fin N,
            ((β.compContinuousLinearMap A) (fun i => EuclideanSpace.basisFun (Fin N) ℝ (j i))) ^ 2 :=
          (Submission.regcomp_covector_sq_sum_orthonormalBasis N k _
            (EuclideanSpace.basisFun (Fin N) ℝ)).symm
      _ ≤ (‖A‖ ^ 2) ^ k *
            ∑ j : Fin k → Fin N', (β (fun i => EuclideanSpace.basisFun (Fin N') ℝ (j i))) ^ 2 :=
          Submission.cmcdt_lp_pullback_basis_sq_sum_le N N' k A β
      _ = (‖A‖ ^ 2) ^ k * ((k.factorial : ℝ) * covectorEuclideanNorm β ^ 2) := by
          rw [Submission.regcomp_covector_sq_sum_orthonormalBasis N' k β
            (EuclideanSpace.basisFun (Fin N') ℝ)]
      _ = (k.factorial : ℝ) * (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 := by ring
  -- cancel `k! > 0` and take square roots of nonnegative quantities
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (pow_nonneg (norm_nonneg A) k) (covectorEuclideanNorm_nonneg β)) two_ne_zero).mp
    (le_of_mul_le_mul_left key (by exact_mod_cast Nat.factorial_pos _))
/-- **Interior product bound for the Euclidean coefficient norm** (Simon 6.1): for `v ∈ ℝᴺ` and a
`(k+1)`-covector `β` on `ℝᴺ`, the interior product `ι_v β = β.curryLeft v`,
`ι_v β(w₁, …, w_k) = β(v, w₁, …, w_k)`, satisfies `|ι_v β|_E ≤ ‖v‖ |β|_E`.  By homogeneity it
suffices to treat `u = v / ‖v‖ = f_{i₀}` for an orthonormal basis `f` of `ℝᴺ`.  The position sums
`R_p = Σ_{J(p) = i₀} β(f ∘ J)²` all equal `R_0 = k! |ι_u β|_E²` (transpose `0 ↔ p`), and
`Σ_p R_p ≤ Σ_J β(f ∘ J)² = (k+1)! |β|_E²` because tuples with `i₀` in two slots vanish
(`regcomp_covector_sq_sum_orthonormalBasis` evaluates both sums). -/
theorem Submission.cmcdt_lp_covector_curryLeft_norm_le : ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
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
/-- **The unit orientation of the span of an independent family** (Simon Ch. 6, 3.4–3.5:
`D₁f ∧ ⋯ ∧ Dₙf = det(Dᵢf · τⱼ) τ₁ ∧ ⋯ ∧ τₙ` and `J = |det(Dᵢf · τⱼ)|`, for one linearly
independent family).  Let `v` be linearly independent in `ℝᴾ`, `V = span v`,
`G = (⟨vₐ, v_b⟩)` and `J = √det G`.  Then `det G > 0`, `J ≤ ∏ₐ |vₐ|`, and some unit orientation
`ξ` of `V` has `α(v) = J ⟨α, ξ⟩` for every `n`-covector `α`; every unit orientation of `V` is
`±ξ`.  For the Gram–Schmidt frame `σ` of `V` and `A = (⟨σₐ, v_b⟩)`, `det G = (det A)²`,
`det A ≠ 0`, `|det A| ≤ ∏ₐ |vₐ|` and `α(v) = det A · α(σ)`; so `ξ = sign(det A) σ₁ ∧ ⋯ ∧ σₙ`
works, and two unit orientations of `V` differ by a sign. -/
theorem Submission.cmcdt_lpi_unit_orientation_span : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → 0 < Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b)) ∧ Real.sqrt (Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b))) ≤ ∏ a, ‖v a‖ ∧ ∃ ξ : MultiVector P n, IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range v)) ∧ (∀ α : Covector (Euclid P) n, α v = Real.sqrt (Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b))) * ξ α) ∧ ∀ ζ : MultiVector P n, IsUnitOrientationOf ζ (Submodule.span ℝ (Set.range v)) → ζ = ξ ∨ ζ = -ξ := by
  intro P n v hv
  -- Steps 1–4: the Gram–Schmidt frame `σ` of `V = span v`, and `d = det A`
  obtain ⟨σ, hσ, hspan, hG, hd0, hHad⟩ :=
    Submission.dpf_exists_orthonormal_frame_det_gram P n v hv
  set d := Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) with hd
  -- `J = √((det A)²) = |det A|`
  have hJ : Real.sqrt (Matrix.det (Matrix.of fun a b => inner ℝ (v a) (v b))) = |d| := by
    rw [hG, Real.sqrt_sq_eq_abs]
  refine ⟨hG ▸ sq_pos_of_ne_zero hd0, hJ ▸ hHad, ?_⟩
  -- Step 6: `ε = sign(det A)` and `ξ = ε σ₁ ∧ ⋯ ∧ σₙ`, i.e. `ξ(α) = ε α(σ)`
  obtain ⟨ε, hε, hdε⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ |d| * ε = d := by
    rcases hd0.lt_or_gt with h | h
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h, mul_neg_one, neg_neg]⟩
    · exact ⟨1, Or.inl rfl, by rw [abs_of_pos h, mul_one]⟩
  let ξ : MultiVector P n := ε • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ σ
  have hξ : ∀ α : Covector (Euclid P) n, ξ α = ε * α σ := fun α => rfl
  -- `ξ` is a unit orientation of `V`, witnessed by the orthonormal basis `σ` of `V`
  have hunit : IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range v)) := by
    refine ⟨σ, hσ, hspan, ?_⟩
    rcases hε with h | h
    · exact Or.inl fun α => by rw [hξ, h, one_mul]
    · exact Or.inr fun α => by rw [hξ, h, neg_one_mul]
  refine ⟨ξ, hunit, fun α => ?_, fun ζ hζ => ?_⟩
  · -- Step 5: every `v_b` lies in `span σ`, so `α(v) = det A · α(σ) = |det A| · ε α(σ)`
    have hmem : ∀ j, v j ∈ Submodule.span ℝ (Set.range σ) := fun j =>
      hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    rw [Submission.dgoj_covector_eq_det_mul_of_mem_span P n σ v hσ hmem α, ← hd, hJ, hξ,
      ← mul_assoc, hdε]
  · -- Step 7: two unit orientations of `V` differ by a sign
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n ξ ζ _ hunit hζ
/-- **The sign between an orientation field and the oriented Jacobian** (step 5 (B2′) of the
integrality of Lipschitz push-forwards, for one piece; Simon Ch. 6, 3.4–3.5).  Let
`G : ℝⁿ → ℝᴺ`, `A ⊆ ℝⁿ` Borel with `DG(u)` injective for `u ∈ A`, `v(u) = (DG(u)eₐ)ₐ` and
`J(u) = √det(⟨vₐ(u), v_b(u)⟩)`.  If `ζ` is `λ⌞A`-a.e. strongly measurable and, `λ⌞A`-a.e., a unit
orientation of `span v(u)`, then some Borel `s = ±1` has `J(u) ⟨α, ζ(u)⟩ = s(u) α(v(u))` for
`λ⌞A`-a.e. `u` and every `n`-covector `α`.  The evaluation `ev_z(α) = α(z)` is continuous in `z`,
so `g(u) = J(u)⁻¹ ev_{v(u)}` is Borel; for a Borel version `ζ'` of `ζ` take `s = 1` on
`{ζ' = g}` and `s = -1` off it.  At a.e. `u ∈ A`, `cmcdt_lpi_unit_orientation_span` gives
`J(u) > 0` and a unit orientation `ξᵤ = g(u)` of `span v(u)` with `α(v(u)) = J(u) ⟨α, ξᵤ⟩`, and
`ζ(u) = ±ξᵤ`. -/
theorem Submission.cmcdt_lpi_pr_orientation_sign : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (ζ : Euclid n → MultiVector N n), MeasurableSet A → (∀ u ∈ A, Injective (fderiv ℝ G u)) → AEStronglyMeasurable ζ (volume.restrict A) → (∀ᵐ u ∂(volume.restrict A), IsUnitOrientationOf (ζ u) (Submodule.span ℝ (Set.range (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))))) → ∃ s : Euclid n → ℤ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧ ∀ᵐ u ∂(volume.restrict A), ∀ α : Covector (Euclid N) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1)) (fderiv ℝ G u (EuclideanSpace.single b 1)))) * ζ u α = (s u : ℝ) * α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
  intro N n G A ζ hA hinj hζ hor
  classical
  -- Step 1: the evaluation functional `ev_z(α) = α(z)` depends continuously on `z`
  let ev : (Fin n → Euclid N) → MultiVector N n := fun z =>
    ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ z
  have hevb : ∀ z z₀ : Fin n → Euclid N,
      ‖ev z - ev z₀‖ ≤ n * (max ‖z‖ ‖z₀‖) ^ (n - 1) * ‖z - z₀‖ := by
    intro z z₀
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro α
    have h := α.norm_image_sub_le z z₀
    simp only [Fintype.card_fin] at h
    calc ‖(ev z - ev z₀) α‖ = ‖α z - α z₀‖ := rfl
      _ ≤ ‖α‖ * n * max ‖z‖ ‖z₀‖ ^ (n - 1) * ‖z - z₀‖ := h
      _ = _ := by ring
  -- continuity for the operator-norm topology, which is the topology of `MultiVector N n`
  have hev : Continuous ev := by
    have hc : @Continuous _ _ _ (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) ev := by
      rw [Metric.continuous_iff]
      intro z₀ ε hε
      have hcb : Continuous fun z : Fin n → Euclid N =>
          (n : ℝ) * (max ‖z‖ ‖z₀‖) ^ (n - 1) * ‖z - z₀‖ := by fun_prop
      obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.mp hcb z₀ ε hε
      refine ⟨δ, hδ, fun z hz => ?_⟩
      have h1 := hδε z hz
      simp only [sub_self, norm_zero, mul_zero, Real.dist_eq, sub_zero] at h1
      have h2 : dist (ev z) (ev z₀) = ‖ev z - ev z₀‖ := dist_eq_norm (E := MultiVector N n) _ _
      rw [h2]
      exact lt_of_le_of_lt (hevb z z₀) (lt_of_le_of_lt (le_abs_self _) h1)
    exact hc
  -- `MultiVector N n` is metrizable; instance search does not see its norm topology
  have : TopologicalSpace.MetrizableSpace (MultiVector N n) := by
    let : MetricSpace (MultiVector N n) := inferInstance
    exact inferInstance
  -- Step 2: `v(u) = (DG(u)eₐ)ₐ` and `J(u)` are Borel
  have hvm : Measurable fun u => (fun a => fderiv ℝ G u (EuclideanSpace.single a 1) :
      Fin n → Euclid N) := by
    exact Measurable.of_eval fun a => measurable_fderiv_apply_const ℝ G _
  have hJm : Measurable fun u => Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
      inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
        (fderiv ℝ G u (EuclideanSpace.single b 1)))) := by
    have hc : Continuous fun z : Fin n → Euclid N =>
        Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (z a) (z b))) := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
      refine continuous_matrix fun a b => ?_
      fun_prop
    exact hc.measurable.comp hvm
  -- Step 3: `g(u) = J(u)⁻¹ ev_{v(u)}` is strongly measurable
  have hgm : StronglyMeasurable fun u =>
      (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
        inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
          (fderiv ℝ G u (EuclideanSpace.single b 1)))))⁻¹ •
        ev (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) :=
    hJm.inv.stronglyMeasurable.smul (hev.comp_stronglyMeasurable hvm.stronglyMeasurable)
  -- Step 4: `S = {ζ' = g}` is Borel for the strongly measurable version `ζ'` of `ζ`;
  -- `s = 1` on `S` and `s = -1` off `S`
  have hset := hζ.stronglyMeasurable_mk.measurableSet_eq_fun hgm
  refine ⟨fun u => if hζ.mk ζ u = (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
        inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
          (fderiv ℝ G u (EuclideanSpace.single b 1)))))⁻¹ •
        ev (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) then 1 else -1, ?_, ?_, ?_⟩
  · exact Measurable.ite hset measurable_const measurable_const
  · intro u
    dsimp only
    split_ifs <;> simp
  · -- Step 5: for a.e. `u`, `ζ(u) = ζ'(u)`, `ζ(u)` orients `span v(u)` and `u ∈ A`
    filter_upwards [hζ.ae_eq_mk, hor, ae_restrict_mem hA] with u h1 h2 h3
    -- Step 6: `v(u) = DG(u) ∘ e` is linearly independent
    have hli : LinearIndependent ℝ (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
      have h0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
      have h4 := h0.map' (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N)
        (LinearMap.ker_eq_bot.mpr (hinj u h3))
      convert h4 using 1
      funext a
      simp
    -- Step 7: `J(u) > 0`, `α(v(u)) = J(u) ξᵤ(α)`, and the unit orientations are `±ξᵤ`
    obtain ⟨hdet, -, ξu, -, hξu, huniq⟩ := Submission.cmcdt_lpi_unit_orientation_span N n _ hli
    set J := Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n =>
        inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1))
          (fderiv ℝ G u (EuclideanSpace.single b 1))))
    have hJpos : 0 < J := Real.sqrt_pos.mpr hdet
    -- so `ξᵤ = g(u)`
    have hξeq : ξu = J⁻¹ • ev (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) := by
      ext α
      simp only [smul_apply, smul_eq_mul, ev,
        ContinuousAlternatingMap.apply_apply, hξu α]
      field_simp
    intro α
    split_ifs with h
    · -- Step 8: `u ∈ S`, so `ζ(u) = g(u)` and `s(u) = 1`
      rw [h1, h]
      simp only [smul_apply, smul_eq_mul, ev,
        ContinuousAlternatingMap.apply_apply]
      field_simp
      push_cast
      ring
    · -- Step 9: `u ∉ S`, so `ζ(u) ≠ ξᵤ`; hence `ζ(u) = -ξᵤ` and `s(u) = -1`
      rcases huniq (ζ u) h2 with h4 | h4
      · exact absurd (by rw [← h1, h4, hξeq]) h
      · rw [h4, neg_apply, hξu α]
        push_cast
        ring
/-- **A common Borel orientation for countably many integer multiplicity pieces** (countable
form of the orientation argument behind Simon Ch. 6, Remark 3.2(1); chapter-06.txt lines
733–756, with Ch. 3, 1.4–1.5, chapter-03.txt lines 77–89).  Let `Rᵢ = (Mᵢ, θᵢ, ξᵢ)` be
`IMRep`s in an open `U` whose union `N = ⋃ᵢ Mᵢ` is locally `Hⁿ`-finite in `U`.  Then there are
a Borel `η` and Borel signs `sᵢ = ±1` such that, for `Hⁿ`-a.e. `x ∈ N`, `η(x)` orients an
approximate tangent space of `N` at `x`, and `ξᵢ = sᵢ η` for `Hⁿ`-a.e. `x ∈ Mᵢ`.

Proof sketch:
* Replace `ξᵢ` by a Borel `ξ'ᵢ` with `ξ'ᵢ = ξᵢ` `Hⁿ`-a.e. on `Mᵢ`, and disjointify the
  carriers: `Dᵢ = Mᵢ \ ⋃_{j<i} Mⱼ`.
* `η = Σᵢ 1_{Dᵢ} ξ'ᵢ` equals `ξ'ⱼ` on `Dⱼ` and `0` off `N`; it is Borel as the pointwise limit
  of the finite-stage approximants `gₖ₊₁ = ξ'ₖ` on `Dₖ`, `gₖ₊₁ = gₖ` elsewhere.
* Tangent transfer for `Mⱼ ⊆ N`: `Hⁿ`-a.e. on `N`, for every `j` with `x ∈ Mⱼ`, `ξ'ⱼ(x)`
  orients an approximate tangent space of `N` at `x`.
* Approximate tangent spaces are unique (Remark 1.5(1)), so `η(x)` and every `ξ'ᵢ(x)` with
  `x ∈ Mᵢ` orient the same `TₓN`, and the sign rule gives `ξ'ᵢ(x) = ±η(x)`.  With `sᵢ = 1`
  where `ξ'ᵢ = η` and `sᵢ = -1` elsewhere, `ξᵢ = ξ'ᵢ = sᵢ η` `Hⁿ`-a.e. on `Mᵢ`. -/
theorem Submission.cmcdt_ims_common_orientation : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] ((⋃ i, (R i).carrier) ∩ K) ≠ ∞) → ∃ (η : Euclid P → MultiVector P n) (s : ℕ → Euclid P → ℝ), StronglyMeasurable η ∧ (∀ i, Measurable (s i)) ∧ (∀ i x, s i x = 1 ∨ s i x = -1) ∧ (∀ᵐ x ∂(μHE[n].restrict (⋃ i, (R i).carrier)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (⋃ i, (R i).carrier) x Q ∧ IsUnitOrientationOf (η x) Q) ∧ ∀ i, ∀ᵐ x ∂(μHE[n].restrict (R i).carrier), (R i).orient x = s i x • η x := by
  intro P n U R hU hfin
  classical
  set M : ℕ → Set (Euclid P) := fun i => (R i).carrier with hMdef
  set N : Set (Euclid P) := ⋃ i, M i with hNdef
  have hMmeas : ∀ i, MeasurableSet (M i) := fun i => (R i).measurableSet_carrier
  have hNmeas : MeasurableSet N := MeasurableSet.iUnion hMmeas
  have hNU : N ⊆ U := iUnion_subset fun i => (R i).carrier_subset
  -- Borel versions `ξ'ᵢ` of the orientations, `ξ'ᵢ = ξᵢ` a.e. on `Mᵢ`
  set ξ' : ℕ → Euclid P → MultiVector P n :=
    fun i => (R i).aestronglyMeasurable_orient.mk (R i).orient
  have hξ'sm : ∀ i, StronglyMeasurable (ξ' i) :=
    fun i => (R i).aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξ'ae : ∀ i, ∀ᵐ x ∂(μHE[n].restrict (M i)), (R i).orient x = ξ' i x :=
    fun i => (R i).aestronglyMeasurable_orient.ae_eq_mk
  -- the disjoint pieces `Dᵢ = Mᵢ \ ⋃_{j<i} Mⱼ`
  set D : ℕ → Set (Euclid P) := disjointed M with hDdef
  have hDmeas : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hMmeas
  have hDsub : ∀ i, D i ⊆ M i := disjointed_subset M
  have hDdisj : Pairwise (Disjoint on D) := disjoint_disjointed M
  have hDunion : ⋃ i, D i = N := iUnion_disjointed
  -- the reference orientation `η = Σᵢ 1_{Dᵢ} ξ'ᵢ`: `η = ξ'ⱼ` on `Dⱼ`, `η = 0` off `N`
  set η : Euclid P → MultiVector P n := fun x => ∑' i, (D i).indicator (ξ' i) x with hηdef
  have hη_eq : ∀ j x, x ∈ D j → η x = ξ' j x := by
    intro j x hx
    simp only [hηdef]
    rw [tsum_eq_single j]
    · exact indicator_of_mem hx _
    · intro i hij
      exact indicator_of_notMem (fun hxi => (hDdisj hij).ne_of_mem hxi hx rfl) _
  have hη_zero : ∀ x, (∀ i, x ∉ D i) → η x = 0 := by
    intro x hx
    simp only [hηdef]
    have h0 : ∀ i, (D i).indicator (ξ' i) x = 0 := fun i => indicator_of_notMem (hx i) _
    simp [h0]
  -- `MultiVector P n` is metrizable: its operator-norm topology is the strong topology
  have hmetr : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
    { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
        Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
      toT0Space := inferInstance }
  -- finite-stage approximants `gₖ₊₁ = ξ'ₖ` on `Dₖ`, `gₖ₊₁ = gₖ` elsewhere (`ite` only)
  let g : ℕ → Euclid P → MultiVector P n := fun k => Nat.rec (fun _ => 0)
    (fun j gj => fun x => if x ∈ D j then ξ' j x else gj x) k
  have hg_succ : ∀ k x, g (k + 1) x = if x ∈ D k then ξ' k x else g k x := fun k x => rfl
  have hg_sm : ∀ k, StronglyMeasurable (g k) := by
    intro k
    induction k with
    | zero => exact stronglyMeasurable_const
    | succ k ih =>
      have : g (k + 1) = fun x => if x ∈ D k then ξ' k x else g k x := funext (hg_succ k)
      rw [this]
      exact StronglyMeasurable.ite (hDmeas k) (hξ'sm k) ih
  have hg_eq : ∀ k x, (∀ i, i < k → x ∉ D i) → g k x = 0 := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
      intro x hx
      rw [hg_succ, ite_eq_right (hx k (Nat.lt_succ_self k))]
      exact ih x fun i hi => hx i (Nat.lt_succ_of_lt hi)
  have hg_mem : ∀ j x, x ∈ D j → ∀ k, j < k → g k x = ξ' j x := by
    intro j x hj k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro hk
      rw [hg_succ]
      by_cases hjk : j = k
      · subst hjk; rw [ite_eq_left hj]
      · have hxk : x ∉ D k := fun hxk => (hDdisj (Ne.symm hjk)).ne_of_mem hxk hj rfl
        rw [ite_eq_right hxk]
        exact ih (by omega)
  -- `gₖ → η` pointwise, so `η` is Borel
  have hη_sm : StronglyMeasurable η := by
    refine stronglyMeasurable_of_tendsto atTop hg_sm ?_
    rw [tendsto_pi_nhds]
    intro x
    by_cases hx : ∃ j, x ∈ D j
    · obtain ⟨j, hj⟩ := hx
      apply tendsto_atTop_of_eventually_const (i₀ := j + 1)
      intro k hk
      rw [hη_eq j x hj]
      exact hg_mem j x hj k (by omega)
    · have hx' : ∀ i, x ∉ D i := fun i hi => hx ⟨i, hi⟩
      rw [hη_zero x hx']
      apply tendsto_atTop_of_eventually_const (i₀ := 0)
      intro k _
      exact hg_eq k x fun i _ => hx' i
  -- the signs `sᵢ = 1` where `ξ'ᵢ = η`, `sᵢ = -1` elsewhere
  set s : ℕ → Euclid P → ℝ := fun i x => if ξ' i x = η x then 1 else -1 with hsdef
  have hs_meas : ∀ i, Measurable (s i) := fun i =>
    Measurable.ite ((hξ'sm i).measurableSet_eq_fun hη_sm) measurable_const measurable_const
  have hs_val : ∀ i x, s i x = 1 ∨ s i x = -1 := by
    intro i x
    by_cases h : ξ' i x = η x
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  -- tangent transfer for `Mⱼ ⊆ N`: a.e. on `Mⱼ`, `ξ'ⱼ(x)` orients a tangent space of `N`
  have hP : ∀ j, ∀ᵐ x ∂(μHE[n].restrict (M j)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (ξ' j x) Q := by
    intro j
    have h1 := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M j) N (R j) hU
      (hMmeas j) hNmeas subset_rfl (subset_iUnion M j) hNU hfin
    filter_upwards [h1, hξ'ae j] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx1
    exact ⟨Q, hQ1, hx2 ▸ hQ2⟩
  -- the same, for every `j` at once, `Hⁿ`-a.e. on `N`
  have hPN : ∀ᵐ x ∂(μHE[n].restrict N), ∀ j, x ∈ M j → ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (ξ' j x) Q := by
    rw [ae_all_iff]
    intro j
    exact ae_restrict_of_ae ((ae_restrict_iff' (hMmeas j)).mp (hP j))
  -- uniqueness of `TₓN` and the sign rule: `η(x)` orients `TₓN`, `ξ'ᵢ(x) = ±η(x)` on `Mᵢ`
  have hgood : ∀ᵐ x ∂(μHE[n].restrict N), (∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) ∧
      ∀ i, x ∈ M i → (ξ' i x = η x ∨ ξ' i x = -η x) := by
    filter_upwards [hPN, ae_restrict_mem hNmeas] with x hx hxN
    rw [← hDunion] at hxN
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxN
    obtain ⟨Qj, hQj1, hQj2⟩ := hx j (hDsub j hj)
    rw [← hη_eq j x hj] at hQj2
    refine ⟨⟨Qj, hQj1, hQj2⟩, fun i hi => ?_⟩
    obtain ⟨Qi, hQi1, hQi2⟩ := hx i hi
    rw [hQi1.unique hQj1] at hQi2
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (η x) (ξ' i x) Qj hQj2 hQi2
  refine ⟨η, s, hη_sm, hs_meas, hs_val, hgood.mono fun x hx => hx.1, fun i => ?_⟩
  -- `ξᵢ = ξ'ᵢ = sᵢ η` a.e. on `Mᵢ ⊆ N`
  have hgoodi : ∀ᵐ x ∂(μHE[n].restrict (M i)), x ∈ M i → (ξ' i x = η x ∨ ξ' i x = -η x) :=
    ae_restrict_of_ae_restrict_of_subset (subset_iUnion M i) (hgood.mono fun x hx => hx.2 i)
  filter_upwards [hgoodi, ae_restrict_mem (hMmeas i), hξ'ae i] with x hx hxM hxe
  rw [hxe]
  by_cases h : ξ' i x = η x
  · rw [show s i x = 1 from ite_eq_left h, one_smul, h]
  · rw [show s i x = -1 from ite_eq_right h, (hx hxM).resolve_left h]
    exact (neg_one_smul ℝ (η x)).symm
/-- **Simon Ch. 6, Definition 3.1, from an integer density**: let `N ⊆ U` be Borel and countably
`n`-rectifiable with `Hⁿ(N ∩ K) < ∞` for compact `K ⊆ U`, let `η` orient the approximate tangent
spaces of `N` `Hⁿ`-a.e. on `N`, and let `m` be integer-valued with `∫_{N ∩ K} |m| dHⁿ < ∞` for
compact `K ⊆ U`.  Then `(N', |m|, sign(m) η)`, `N' = N ∩ {m ≠ 0}`, is an `IMRep` in `U` acting by
`ω ↦ ∫_N m ⟨ω, η⟩ dHⁿ`.

Proof sketch:
* `N' ⊆ N` is Borel and countably `n`-rectifiable; `⌊|m|⌋₊ = |m|` is measurable, positive on `N'`
  and locally integrable; `sign(m) η` is strongly measurable.
* By locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)), for `Hⁿ`-a.e.
  `x ∈ N'` a tangent space `Q` of `N` at `x` is one of `N'`, and `±η(x)` still orients `Q`.
* Pointwise on `N`, `1_{N'} |m| ⟨ω, sign(m) η⟩ = m ⟨ω, η⟩`, so the two integrals agree. -/
theorem Submission.cmcdt_ims_imrep_of_int_density : ∀ (P n : ℕ) (U N : Set (Euclid P)) (η : Euclid P → MultiVector P n) (m : Euclid P → ℝ), IsOpen U → MeasurableSet N → N ⊆ U → CountablyRectifiable n N → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (N ∩ K) ≠ ∞) → StronglyMeasurable η → Measurable m → (∀ x, ∃ z : ℤ, m x = z) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict N), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) → ∃ R : IMRep U n, ∀ ω : DifferentialForm (Euclid P) n, R.action ω = ∫ x in N, m x * η x (ω x) ∂μHE[n] := by
  intro P n U N η m hU hN hNU hrect hfin hη hm hint hloc hor
  classical
  -- Step 1: the carrier `N' = N ∩ {m ≠ 0}`
  set N' : Set (Euclid P) := N ∩ {x | m x ≠ 0}
  have hN'meas : MeasurableSet N' :=
    hN.inter ((measurableSet_singleton (0 : ℝ)).preimage hm).compl
  have hN'N : N' ⊆ N := inter_subset_left
  -- Steps 2–3: the multiplicity `⌊|m|⌋₊ = |m|` and the orientation `sign(m) η`
  set mult : Euclid P → ℕ := fun x => ⌊|m x|⌋₊ with hmultdef
  set orient : Euclid P → MultiVector P n := fun x => if m x < 0 then -η x else η x with horientdef
  have hmult_cast : ∀ x, ((mult x : ℕ) : ℝ) = |m x| := by
    intro x
    obtain ⟨z, hz⟩ := hint x
    simp only [hmultdef, hz]
    rw [show |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) by simp [Nat.cast_natAbs]]
    rw [Nat.floor_natCast]
  have hmult_meas : Measurable mult :=
    (Nat.floor_mono.measurable).comp (continuous_abs.measurable.comp hm)
  have hmult_pos : ∀ x ∈ N', 0 < mult x := by
    intro x hx
    have hx0 : m x ≠ 0 := hx.2
    have h1 : (0 : ℝ) < ((mult x : ℕ) : ℝ) := by
      rw [hmult_cast]; exact abs_pos.mpr hx0
    exact_mod_cast h1
  have horient_sm : StronglyMeasurable orient := by
    have hset : MeasurableSet {x | m x < 0} := measurableSet_lt hm measurable_const
    have hneg : StronglyMeasurable (fun x => -η x) := by
      have := hη.const_smul (-1 : ℝ)
      convert this using 1
      funext x
      exact (neg_one_smul ℝ (η x)).symm
    exact StronglyMeasurable.ite hset hneg hη
  -- Step 4: local integrability, `∫_{N' ∩ K} ⌊|m|⌋₊ ≤ ∫_{N ∩ K} |m| < ∞`
  have hloc' : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hloc K hK hKU) ?_
    calc ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in N ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left _ hN'N)
      _ ≤ ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs, ← hmult_cast x, ENNReal.ofReal_natCast]
  -- Step 5: tangent spaces of `N` are tangent spaces of `N'` a.e. on `N'`, and `±η` orients them
  have hor' : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N' x Q ∧ IsUnitOrientationOf (orient x) Q := by
    have h1 := Submission.rsdic_ae_tangent_iff_of_subset P n U N' N hU hN'meas hN hN'N hNU hfin
    have h2 : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q :=
      ae_restrict_of_ae_restrict_of_subset hN'N hor
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx2
    refine ⟨Q, (hx1 Q).1 hQ1, ?_⟩
    simp only [horientdef]
    split_ifs
    · obtain ⟨τ, hτ, hspan, hξ⟩ := hQ2
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hξ with h | h
      · right; intro α; simp [h]
      · left; intro α; simp [h]
    · exact hQ2
  -- Step 6: the `IMRep`
  let R : IMRep U n :=
    { carrier := N'
      mult := mult
      orient := orient
      measurableSet_carrier := hN'meas
      carrier_subset := hN'N.trans hNU
      rectifiable := hrect.mono hN'N
      measurable_mult := hmult_meas
      mult_pos := hmult_pos
      locallyIntegrable_mult := hloc'
      aestronglyMeasurable_orient := horient_sm.aestronglyMeasurable
      orients := hor' }
  refine ⟨R, ?_⟩
  -- Step 7: the action, from `1_{N'} ⌊|m|⌋₊ ⟨ω, sign(m) η⟩ = m ⟨ω, η⟩` pointwise on `N`
  intro ω
  show ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] = ∫ x in N, m x * η x (ω x) ∂μHE[n]
  have hpt : ∀ x ∈ N,
      N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x = m x * η x (ω x) := by
    intro x hx
    by_cases hx0 : m x = 0
    · have : x ∉ N' := fun h => h.2 hx0
      simp [this, hx0]
    · have hxN' : x ∈ N' := ⟨hx, hx0⟩
      rw [indicator_of_mem hxN', hmult_cast]
      simp only [horientdef]
      split_ifs with hneg
      · rw [abs_of_neg hneg]; simp
      · rw [abs_of_nonneg (not_lt.mp hneg)]
  calc ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n]
      = ∫ x in N ∩ N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] := by
        rw [inter_eq_right.mpr hN'N]
    _ = ∫ x in N, N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x ∂μHE[n] :=
        (setIntegral_indicator hN'meas).symm
    _ = ∫ x in N, m x * η x (ω x) ∂μHE[n] := setIntegral_congr_fun hN hpt

/-- A countable family of integer multiplicity triples `Rᵢ = (Mᵢ, θᵢ, ξᵢ)` in `U` with
`Σᵢ μ_{Rᵢ}(U) < ∞` is summed by one triple `R'`: `Σᵢ Rᵢ(ω) = R'(ω)` for every `ω ∈ 𝒟ⁿ(U)`.
On `N = ⋃ᵢ Mᵢ` take a common orientation `η` with `ξᵢ = sᵢ η` a.e. on `Mᵢ` (`sᵢ = ±1`); `R'`
represents `ω ↦ ∫_N m ⟨ω, η⟩ dHⁿ` for the integer density `m = Σᵢ sᵢ θᵢ 1_{Mᵢ}`, and the series
converges by dominated convergence, as `|m| ≤ Θ := Σᵢ θᵢ 1_{Mᵢ}` and `∫ Θ dHⁿ = Σᵢ μ_{Rᵢ}(U)`. -/
theorem Submission.cmcdt_ims_imrep_tsum : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : ℕ → IMRep U n), IsOpen U → ∑' i, (R i).measure U ≠ ∞ → ∃ R' : IMRep U n, ∀ ω : TestFormOn U n, HasSum (fun i => (R i).action (ω : DifferentialForm (Euclid P) n)) (R'.action (ω : DifferentialForm (Euclid P) n)) := by
  intro P n U R hU hA
  classical
  set M : ℕ → Set (Euclid P) := fun i => (R i).carrier
  set N : Set (Euclid P) := ⋃ i, M i
  have hMmeas : ∀ i, MeasurableSet (M i) := fun i => (R i).measurableSet_carrier
  have hNmeas : MeasurableSet N := MeasurableSet.iUnion hMmeas
  have hNU : N ⊆ U := iUnion_subset fun i => (R i).carrier_subset
  -- Step 1: `Θᵢ = θᵢ 1_{Mᵢ}` has `∫ Θᵢ dHⁿ = μ_{Rᵢ}(U)`, so `Θ = Σᵢ Θᵢ` has finite integral
  set Θi : ℕ → Euclid P → ℝ≥0∞ := fun i => (M i).indicator (fun y => ((R i).mult y : ℝ≥0∞))
    with hΘidef
  have hΘi_meas : ∀ i, Measurable (Θi i) := fun i =>
    (measurable_from_nat.comp (R i).measurable_mult).indicator (hMmeas i)
  have hΘi_ne_top : ∀ i x, Θi i x ≠ ∞ := by
    intro i x
    simp only [hΘidef]
    by_cases hx : x ∈ M i
    · rw [indicator_of_mem hx]; exact ENNReal.natCast_ne_top _
    · rw [indicator_of_notMem hx]; exact ENNReal.zero_ne_top
  have hmeasU : ∀ i, (R i).measure U = ∫⁻ x, Θi i x ∂μHE[n] := by
    intro i
    simp only [IMRep.measure, hΘidef]
    rw [withDensity_apply _ hU.measurableSet, Measure.restrict_restrict hU.measurableSet,
      inter_eq_right.mpr (R i).carrier_subset, lintegral_indicator (hMmeas i)]
  set Θ : Euclid P → ℝ≥0∞ := fun x => ∑' i, Θi i x with hΘdef
  have hΘ_meas : Measurable Θ := Measurable.tsum hΘi_meas
  have hΘ_int : ∫⁻ x, Θ x ∂μHE[n] = ∑' i, (R i).measure U := by
    rw [lintegral_tsum (fun i => (hΘi_meas i).aemeasurable)]
    simp_rw [hmeasU]
  have hΘ_fin : ∫⁻ x, Θ x ∂μHE[n] ≠ ∞ := hΘ_int ▸ hA
  -- Step 2: `Hⁿ(N) ≤ Σᵢ μ_{Rᵢ}(U)`, as `θᵢ ≥ 1` on `Mᵢ`
  have hN_le : μHE[n] N ≤ ∑' i, (R i).measure U := by
    refine (measure_iUnion_le M).trans (ENNReal.tsum_le_tsum fun i => ?_)
    rw [hmeasU i, hΘidef]
    simp only
    rw [lintegral_indicator (hMmeas i), ← setLIntegral_one]
    refine setLIntegral_mono' (hMmeas i) fun x hx => ?_
    have := (R i).mult_pos x hx
    exact_mod_cast this
  have hNfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (N ∩ K) ≠ ∞ := by
    intro K _ _
    exact ne_top_of_le_ne_top hA ((measure_mono inter_subset_left).trans hN_le)
  -- Step 3: the common orientation `η` of `N`, with `ξᵢ = sᵢ η` a.e. on `Mᵢ`
  obtain ⟨η, s, hη, hs_meas, hs_val, hor, hrel⟩ :=
    Submission.cmcdt_ims_common_orientation P n U R hU hNfin
  -- Step 4: the integer density `m = Σᵢ aᵢ`, `aᵢ = sᵢ θᵢ 1_{Mᵢ}`, with `|m| ≤ Θ`
  set a : ℕ → Euclid P → ℝ := fun i => (M i).indicator (fun y => s i y * ((R i).mult y : ℝ))
    with hadef
  have ha_meas : ∀ i, Measurable (a i) := fun i =>
    ((hs_meas i).mul (measurable_from_nat.comp (R i).measurable_mult)).indicator (hMmeas i)
  have ha_norm : ∀ i x, ‖a i x‖ = (Θi i x).toReal := by
    intro i x
    simp only [hadef, hΘidef]
    by_cases hx : x ∈ M i
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      rcases hs_val i x with h | h <;> simp [h]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]; simp
  have ha_enorm : ∀ i x, ‖a i x‖ₑ = Θi i x := by
    intro i x
    rw [← ofReal_norm, ha_norm, ENNReal.ofReal_toReal (hΘi_ne_top i x)]
  have ha_int : ∀ i x, ∃ z : ℤ, a i x = z := by
    intro i x
    simp only [hadef]
    by_cases hx : x ∈ M i
    · rw [indicator_of_mem hx]
      rcases hs_val i x with h | h
      · exact ⟨(R i).mult x, by simp [h]⟩
      · exact ⟨-((R i).mult x : ℤ), by simp [h]⟩
    · exact ⟨0, by simp [indicator_of_notMem hx]⟩
  choose z hz using ha_int
  set m : Euclid P → ℝ := fun x => ∑' i, a i x with hmdef
  have hm_meas : Measurable m := Measurable.tsum ha_meas
  -- a summable series of integers has finitely many nonzero terms; `m = 0` if not summable
  have hm_int : ∀ x, ∃ k : ℤ, m x = k := by
    intro x
    by_cases hsum : Summable (fun i => a i x)
    · have hfin : {i | a i x ≠ 0}.Finite := by
        have ht := hsum.tendsto_cofinite_zero
        have hev : ∀ᶠ i in cofinite, a i x ∈ ball (0 : ℝ) 1 := ht (ball_mem_nhds 0 one_pos)
        refine (Filter.eventually_cofinite.mp hev).subset fun i hi => ?_
        simp only [mem_ofPred_eq, mem_ball, dist_zero_right] at hi ⊢
        intro hlt
        apply hi
        rw [hz i x] at hlt ⊢
        have : z i x = 0 := by
          rw [Real.norm_eq_abs] at hlt
          have h1 : |(z i x : ℝ)| < 1 := hlt
          have h2 : |z i x| < 1 := by exact_mod_cast h1
          exact Int.abs_lt_one_iff.mp h2
        simp [this]
      refine ⟨∑ i ∈ hfin.toFinset, z i x, ?_⟩
      simp only [hmdef]
      rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => by simpa using hi)]
      push_cast
      exact Finset.sum_congr rfl fun i _ => hz i x
    · exact ⟨0, by simp [hmdef, tsum_eq_zero_of_not_summable hsum]⟩
  have hm_le : ∀ x, ‖m x‖ₑ ≤ Θ x := by
    intro x
    calc ‖m x‖ₑ ≤ ∑' i, ‖a i x‖ₑ := enorm_tsum_le_tsum_enorm
      _ = Θ x := by simp only [hΘdef, ha_enorm]
  have hloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top hΘ_fin ?_
    exact (setLIntegral_le_lintegral _ _).trans (lintegral_mono hm_le)
  have hrect : CountablyRectifiable n N :=
    Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion M fun i => (R i).rectifiable
  -- Step 5: the triple `(N, m, η)` gives `R'` with `R'(ω) = ∫_N m ⟨ω, η⟩ dHⁿ`
  obtain ⟨R', hR'⟩ := Submission.cmcdt_ims_imrep_of_int_density P n U N η m hU hNmeas hNU hrect
    hNfin hη hm_meas hm_int hloc hor
  refine ⟨R', fun ω => ?_⟩
  -- Step 6: dominated convergence for the series `Σᵢ aᵢ ⟨ω, η⟩`, dominated by `B Θᵢ`
  have hsmooth : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨B, hB⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
  have hev_sm : StronglyMeasurable (fun x => η x ((ω : DifferentialForm (Euclid P) n) x)) := by
    have hcont : Continuous (fun p : MultiVector P n × Euclid P =>
        p.1 ((ω : DifferentialForm (Euclid P) n) p.2)) :=
      isBoundedBilinearMap_apply.continuous.comp (continuous_fst.prodMk (hωc.comp continuous_snd))
    exact hcont.comp_stronglyMeasurable (hη.prodMk stronglyMeasurable_id)
  set F : ℕ → Euclid P → ℝ := fun i x => a i x * η x ((ω : DifferentialForm (Euclid P) n) x)
    with hFdef
  set bound : ℕ → Euclid P → ℝ := fun i x => B * (Θi i x).toReal with hbounddef
  have hF_sm : ∀ i, AEStronglyMeasurable (F i) (μHE[n].restrict N) := fun i =>
    ((ha_meas i).stronglyMeasurable.mul hev_sm).aestronglyMeasurable
  have hηnorm : ∀ᵐ x ∂(μHE[n].restrict N), ‖η x‖ ≤ 1 := by
    filter_upwards [hor] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q (η x) hQ
  have hF_le : ∀ i, ∀ᵐ x ∂(μHE[n].restrict N), ‖F i x‖ ≤ bound i x := by
    intro i
    filter_upwards [hηnorm] with x hx
    simp only [hFdef, hbounddef, norm_mul, ha_norm]
    have h1 : ‖η x ((ω : DifferentialForm (Euclid P) n) x)‖ ≤ B := by
      calc ‖η x ((ω : DifferentialForm (Euclid P) n) x)‖
          ≤ ‖η x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (η x).le_opNorm _
        _ ≤ 1 * B := mul_le_mul hx (hB x) (norm_nonneg _) zero_le_one
        _ = B := one_mul B
    calc (Θi i x).toReal * ‖η x ((ω : DifferentialForm (Euclid P) n) x)‖
        ≤ (Θi i x).toReal * B := mul_le_mul_of_nonneg_left h1 ENNReal.toReal_nonneg
      _ = B * (Θi i x).toReal := mul_comm _ _
  have hΘ_lt : ∀ᵐ x ∂(μHE[n].restrict N), Θ x < ∞ :=
    ae_restrict_of_ae (ae_lt_top hΘ_meas hΘ_fin)
  have hsumΘ : ∀ x, Θ x < ∞ → Summable (fun i => (Θi i x).toReal) :=
    fun x hx => ENNReal.summable_toReal hx.ne
  have hbound_sum : ∀ᵐ x ∂(μHE[n].restrict N), Summable (fun i => bound i x) := by
    filter_upwards [hΘ_lt] with x hx
    exact (hsumΘ x hx).mul_left B
  have hbound_int : Integrable (fun x => ∑' i, bound i x) (μHE[n].restrict N) := by
    have hmeas : Measurable (fun x => ∑' i, bound i x) :=
      Measurable.tsum fun i => measurable_const.mul (hΘi_meas i).ennreal_toReal
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hle : ∀ x, ‖∑' i, bound i x‖ₑ ≤ ‖B‖ₑ * Θ x := by
      intro x
      calc ‖∑' i, bound i x‖ₑ ≤ ∑' i, ‖bound i x‖ₑ := enorm_tsum_le_tsum_enorm
        _ = ∑' i, ‖B‖ₑ * Θi i x := by
            congr 1; funext i
            simp only [hbounddef]
            rw [enorm_mul, ← ofReal_norm (Θi i x).toReal, Real.norm_eq_abs,
              abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hΘi_ne_top i x)]
        _ = ‖B‖ₑ * Θ x := ENNReal.tsum_mul_left
    calc ∫⁻ x, ‖∑' i, bound i x‖ₑ ∂(μHE[n].restrict N)
        ≤ ∫⁻ x, ‖B‖ₑ * Θ x ∂(μHE[n].restrict N) := lintegral_mono hle
      _ = ‖B‖ₑ * ∫⁻ x, Θ x ∂(μHE[n].restrict N) := lintegral_const_mul _ hΘ_meas
      _ ≤ ‖B‖ₑ * ∫⁻ x, Θ x ∂μHE[n] := by gcongr; exact Measure.restrict_le_self
      _ < ∞ := ENNReal.mul_lt_top enorm_lt_top hΘ_fin.lt_top
  have hF_sum : ∀ᵐ x ∂(μHE[n].restrict N),
      HasSum (fun i => F i x) (m x * η x ((ω : DifferentialForm (Euclid P) n) x)) := by
    filter_upwards [hΘ_lt] with x hx
    have hs : Summable (fun i => a i x) :=
      Summable.of_norm_bounded (hsumΘ x hx) fun i => (ha_norm i x).le
    exact hs.hasSum.mul_right _
  have hmain :=
    hasSum_integral_of_dominated_convergence bound hF_sm hF_le hbound_sum hbound_int hF_sum
  -- Step 7: `∫_N Fᵢ dHⁿ = Rᵢ(ω)`, as `ξᵢ = sᵢ η` a.e. on `Mᵢ ⊆ N`
  have hterm : ∀ i, ∫ x, F i x ∂(μHE[n].restrict N) =
      (R i).action (ω : DifferentialForm (Euclid P) n) := by
    intro i
    have h1 : ∀ᵐ x ∂(μHE[n].restrict (M i)),
        ((R i).mult x : ℝ) * (R i).orient x ((ω : DifferentialForm (Euclid P) n) x) =
          s i x * ((R i).mult x : ℝ) * η x ((ω : DifferentialForm (Euclid P) n) x) := by
      filter_upwards [hrel i] with x hx
      rw [hx, smul_apply, smul_eq_mul]
      ring
    have h2 : ∀ x, F i x = (M i).indicator (fun y => s i y * ((R i).mult y : ℝ) *
        η y ((ω : DifferentialForm (Euclid P) n) y)) x := by
      intro x
      simp only [hFdef, hadef]
      by_cases hx : x ∈ M i
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    simp only [IMRep.action]
    rw [setIntegral_congr_ae (hMmeas i) ((ae_restrict_iff' (hMmeas i)).mp h1)]
    simp_rw [h2]
    rw [setIntegral_indicator (hMmeas i), inter_eq_right.mpr (subset_iUnion M i)]
  simp_rw [hterm] at hmain
  rw [hR' (ω : DifferentialForm (Euclid P) n)]
  exact hmain
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2
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

/-- **Simon Ch. 6, 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U`, then
`M_W(T) = μ_R(W) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  The upper bound
`dor_ims_massOn_le_measure` and the lower bound `dor_ims_measure_le_massOn` give equality by
antisymmetry. -/
theorem Submission.cmc_massOn_eq_imRep_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := by
  intro P n U T R hU hR W hW
  exact le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
    (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)

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

/-- **Series of currents of finite total mass** (the closing step of B3 in the proof of the
deformation theorem, Simon 6.5.1, where it replaces the completeness theorem 6.3.13).
Let `Wᵢ ∈ 𝒟ₖ₊₁(ℝᴾ)` with `Σᵢ M(Wᵢ) < ∞`.  The series `S(ω) = Σᵢ Wᵢ(ω)` defines a current with
`M(S) ≤ Σᵢ M(Wᵢ)` and, by (VO), `spt S ⊆ closure ⋃ᵢ spt Wᵢ`.  If every `Wᵢ = τ(Mᵢ, θᵢ, ξᵢ)` is
integer multiplicity, then (MR) with `U = W = ℝᴾ` gives `∫_{Mᵢ} θᵢ dH^{k+1} = M(Wᵢ)`, so the
representations have finite total weight and their actions sum to the action of one `IMRep`
`R'`; by uniqueness of sums `S(ω) = R'(ω)` for every test form `ω`.  (IMC) is not used: the
tangent locality and orientation bound it provides enter the series of `IMRep`s through the
accepted lemmas `rsdic_ae_tangent_iff_of_subset` and `unit_orientation_norm_le_one`. -/
theorem Submission.cmcdt_im_series : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S) := by
  intro hVO hMR _hIMC P k W hW
  -- Steps 1–4: the series current `S`, `M(S) ≤ Σᵢ M(Wᵢ)` and `spt S ⊆ closure ⋃ᵢ spt Wᵢ`
  obtain ⟨S, hS, hmass, hsupp⟩ :=
    Submission.cmcdt_ims_series_current hVO P (k + 1) univ W isOpen_univ hW.ne
  refine ⟨S, hS, hmass, hsupp, ?_⟩
  -- Step 5: choose representations `Wᵢ = τ(Mᵢ, θᵢ, ξᵢ)`
  intro hIM
  choose R hR using hIM
  -- (MR) with `U = W = ℝᴾ`: `M(Wᵢ) = ∫_{Mᵢ} θᵢ dH^{k+1}`, so the total weight is finite
  have hmeas : ∀ i, (W i).mass = (R i).measure univ := fun i =>
    hMR P (k + 1) univ (W i) (R i) isOpen_univ (hR i) univ isOpen_univ
  have hsum : ∑' i, (R i).measure univ ≠ ∞ := by
    simp_rw [← hmeas]
    exact hW.ne
  -- one `IMRep` `R'` whose action is the sum of the actions of the `Rᵢ`
  obtain ⟨R', hR'⟩ := Submission.cmcdt_ims_imrep_tsum P (k + 1) univ R isOpen_univ hsum
  -- `Σᵢ Wᵢ(ω) = Σᵢ τ(Mᵢ, θᵢ, ξᵢ)(ω)` has the two sums `S(ω)` and `R'(ω)`
  refine ⟨R', fun ω => (hS ω).unique ?_⟩
  have hWR : (fun i => W i ω) =
      fun i => (R i).action (ω : DifferentialForm (Euclid P) (k + 1)) :=
    funext fun i => hR i ω
  rw [hWR]
  exact hR' ω
/-- **Area formulas for an integer-weighted oriented piece** (Simon Ch. 6, 3.1 (‡), via Ch. 2,
(3.3)-(3.5)).  Let `G : ℝⁿ → ℝᴺ` be differentiable with injective `DG(u)` at every point of the
Borel set `A` and injective on `A`, `J(u) = √det(⟨DG(u)e_a, DG(u)e_b⟩)`, `s = ±1`, and suppose
`J(u) ⟨α, ξ(G u)⟩ = s(u) α(DG(u)e₁, …, DG(u)eₙ)` for a.e. `u ∈ A` and every `n`-covector `α`.
With `w = (θ ∘ G) s`: (i) `∫_A |w| J = ∫_{G(A)} θ dHⁿ`; (ii) every `n`-form `ω` has
`∫_A w ω(G u)(DG(u)e₁, …, DG(u)eₙ) du = ∫_{G(A)} θ ⟨ω, ξ⟩ dHⁿ`.  Since `|w| = θ ∘ G`, (i) is the
area formula `codim1_lura_gram_area_formula` with `g = θ`; (ii) is
`codim1_lur_cd_injective_area_formula_gram` with `h = θ ⟨ω, ξ⟩`, whose integrand `J · h ∘ G`
equals `w ω(G u)(DG(u)e)` a.e. on `A` by the orientation identity with `α = ω(G u)`. -/
theorem Submission.cmcdt_lpi_pr_oriented_piece_area : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (θ : Euclid N → ℕ) (ξ : Euclid N → MultiVector N n) (s : Euclid n → ℤ), MeasurableSet A → (∀ u ∈ A, DifferentiableAt ℝ G u) → (∀ u ∈ A, Injective (fderiv ℝ G u)) → InjOn G A → (∀ u, s u = 1 ∨ s u = -1) → (∀ᵐ u ∂(volume.restrict A), ∀ α : Covector (Euclid N) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1)) (fderiv ℝ G u (EuclideanSpace.single b 1)))) * ξ (G u) α = (s u : ℝ) * α (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))) → ∫⁻ u in A, ENNReal.ofReal (|(((θ (G u) : ℤ) * s u : ℤ) : ℝ)| * Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single a 1)) (fderiv ℝ G u (EuclideanSpace.single b 1))))) = ∫⁻ x in G '' A, (θ x : ℝ≥0∞) ∂μHE[n] ∧ ∀ ω : DifferentialForm (Euclid N) n, ∫ u in A, (((θ (G u) : ℤ) * s u : ℤ) : ℝ) * ω (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) = ∫ x in G '' A, (θ x : ℝ) * ξ x (ω x) ∂μHE[n] := by
  intro N n G A θ ξ s hA hdiff hinj hInjOn hs hstar
  constructor
  · rw [(Submission.codim1_lura_gram_area_formula n N G).2 A hA hdiff hinj hInjOn
      (fun x => (θ x : ℝ≥0∞))]
    apply lintegral_congr
    intro u
    have habs : |((((θ (G u) : ℤ) * s u : ℤ)) : ℝ)| = (θ (G u) : ℝ) := by
      rcases hs u with h | h <;> simp [h]
    rw [habs, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_comm]
  · intro ω
    rw [Submission.codim1_lur_cd_injective_area_formula_gram N n G A hA hdiff hinj hInjOn]
    refine integral_congr_ae ?_
    filter_upwards [hstar] with u hu
    have h1 := hu (ω (G u))
    push_cast
    calc ((θ (G u) : ℝ) * (s u : ℝ)) * ω (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))
        = (θ (G u) : ℝ) * ((s u : ℝ) * ω (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1))) := by ring
      _ = _ := by rw [← h1]; ring
/-- **Covector norm bounds: pull-back, interior product, orthonormal evaluation** (Simon Ch. 6, §1;
the pointwise estimates behind the homotopy and Lipschitz push-forward mass bounds 6.2.27, 6.2.29
used in the deformation theorem 6.5.1).  With `|α|` the Euclidean coefficient norm
`covectorEuclideanNorm α` (Simon 6.1.5):
(L1) `|A^#β| ≤ ‖A‖ᵏ |β|` for a linear map `A : ℝᴺ → ℝᴺ'` and the pull-back
`A^#β(w₁, …, w_k) = β(Aw₁, …, Aw_k)` (`cmcdt_lp_covector_pullback_norm_le`);
(L2) `|ι_v β| ≤ ‖v‖ |β|` for the interior product `ι_v β(w₁, …, w_k) = β(v, w₁, …, w_k)`
(`cmcdt_lp_covector_curryLeft_norm_le`);
(L3) `|α(τ₁, …, τ_k)| ≤ |α|` for an orthonormal family `τ` in `ℝᴺ`
(`regcomp_covector_eval_orthonormal_le`). -/
theorem Submission.cmcdt_lp_covector_norm_bounds : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α :=
  ⟨Submission.cmcdt_lp_covector_pullback_norm_le, Submission.cmcdt_lp_covector_curryLeft_norm_le,
    Submission.regcomp_covector_eval_orthonormal_le⟩

/-- **Lipschitz push-forward and the cylinder `[[0, 1]] × X`** (Simon Ch. 6, 2.17–2.29: products
with `[[0, 1]]` (2.17–2.22), the homotopy formula and its mass estimate (2.25–2.27) and the
Lipschitz push-forward (2.29), for currents `X` with compact support, `M(X) < ∞` and
`M(∂X) < ∞`).  `cmcdt_lpo_lipschitz_pushforward` gives `lpush` with conjuncts (1)–(6) and the
approximation property (PA): `X(ηⱼ) → lpush(F, X)(ω)` whenever the `Fⱼ` are `C^∞` with
`‖DFⱼ‖ ≤ Λ'` on `spt X` and converge to `F` uniformly on `spt X`, and `ηⱼ = Fⱼ^#ω` near
`spt X`.  `cmcdt_lpo_cylinder` gives `cyl = [[0, 1]] × ·` with conjuncts (7)–(9).
`cmcdt_lpo_lipschitz_homotopy` holds for all operators with (PA), (7) and (9) and gives the
homotopy formulas (10), (11) and the mass bound (12).  The covector bounds (L1)–(L3) of
`cmcdt_lp_covector_norm_bounds` are the remaining antecedent of all three. -/
theorem Submission.cmcdt_lp_pushforward_operators : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∃ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k) (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass < ∞ ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) ∧ (∀ (N N' : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' 0 G X - lpush N N' 0 F X = (lpush (N + 1) N' (0 + 1) H (cyl N 0 X)).boundary) ∧ (∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → lpush N N' (k + 1) G X - lpush N N' (k + 1) F X - lpush (N + 1) N' (k + 1) H (cyl N k X.boundary) = (lpush (N + 1) N' (k + 1 + 1) H (cyl N (k + 1) X)).boundary) ∧ ∀ (N N' k : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (δ : ℝ), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ x ∈ X.support, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → (∀ x ∈ X.support, dist (F x) (G x) ≤ δ) → (lpush (N + 1) N' (k + 1) H (cyl N k X)).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hVO hREP
  -- (1)–(6) and the approximation property (PA) of the Lipschitz push-forward
  obtain ⟨lpush, h1, h2, h3, h4, h5, h6, hPA⟩ :=
    Submission.cmcdt_lpo_lipschitz_pushforward hVO hREP Submission.cmcdt_lp_covector_norm_bounds
  -- (7)–(9): the cylinder `[[0, 1]] × X`
  obtain ⟨cyl, h7, h8, h9⟩ :=
    Submission.cmcdt_lpo_cylinder hVO hREP Submission.cmcdt_lp_covector_norm_bounds
  -- (10)–(12): the homotopy formulas and the mass bound, from (PA), (7) and (9)
  obtain ⟨h10, h11, h12⟩ :=
    Submission.cmcdt_lpo_lipschitz_homotopy hVO hREP Submission.cmcdt_lp_covector_norm_bounds
      lpush cyl hPA h7 h9
  exact ⟨lpush, cyl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
/-- **Lipschitz pieces of an integer multiplicity current** (Simon Ch. 6, 3.3–3.5; steps B1, B2,
B2′ of the Lipschitz push-forward integrality in the deformation theorem 6.5.1).
Let `X = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴺ)`, `n = k + 1`, be integer multiplicity with `M(X) < ∞`.  The carrier
may be taken inside `spt X` (`cmcdt_lpi_pr_imrep_in_support`), and then (MR) gives
`M(X) = ∫_M θ dHⁿ`.  Up to an `Hⁿ`-null set, `M` is the disjoint union of bi-Lipschitz images
`Gᵢ(Aᵢ)` (`dpf_rectifiable_bilipschitz_pieces`).  On each piece `ξ ∘ Gᵢ` orients
`span{DGᵢ eₐ}` a.e. (`cmcdt_lpi_pr_piece_orientation_ae`), so a Borel sign `sᵢ = ±1` has
`J_{Gᵢ} ξ(Gᵢ) = sᵢ DGᵢ e₀ ∧ ⋯ ∧ DGᵢ eₙ₋₁` a.e. (`cmcdt_lpi_pr_orientation_sign`).  With
`wᵢ = θ ∘ Gᵢ · sᵢ` and `cᵢ = J_{Gᵢ}`, the area formula (`cmcdt_lpi_pr_oriented_piece_area`) gives
`Σᵢ ∫_{Aᵢ} |wᵢ| cᵢ = ∫_{⋃ᵢ Gᵢ(Aᵢ)} θ dHⁿ ≤ M(X)` and `X(η) = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)`;
`∫_{Aᵢ} |wᵢ| ≤ mᵢ⁻ⁿ M(X)` (`cmcdt_lpi_pr_lintegral_pullback`) and, by
`cmcdt_lpi_unit_orientation_span` and (L3), `|α(DGᵢ e)| ≤ cᵢ |α|`. -/
theorem Submission.cmcdt_lpi_piece_representation : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsIntegerMultiplicity X → X.mass < ∞ → ∃ (G : ℕ → Euclid (k + 1) → Euclid N) (A : ℕ → Set (Euclid (k + 1))) (w : ℕ → Euclid (k + 1) → ℤ) (c : ℕ → Euclid (k + 1) → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (G i)) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i, Measurable (w i)) ∧ (∀ i, Measurable (c i)) ∧ (∀ i, ∀ u ∈ A i, DifferentiableAt ℝ (G i) u) ∧ (∀ i, G i '' A i ⊆ X.support) ∧ (∀ i, IntegrableOn (fun u => (w i u : ℝ)) (A i)) ∧ (∀ i, ∀ u ∈ A i, 0 ≤ c i u ∧ ∀ α : Covector (Euclid N) (k + 1), |α (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))| ≤ c i u * covectorEuclideanNorm α) ∧ ∑' i, ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) ≤ X.mass ∧ ∀ η : TestFormOn (univ : Set (Euclid N)) (k + 1), HasSum (fun i => ∫ u in A i, (w i u : ℝ) * (η : DifferentialForm (Euclid N) (k + 1)) (G i u) (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1))) (X η) := by
  intro hCB _hVO hMR hIMC N k X hXim hXmass
  -- Step 1: a representation `X = τ(M, θ, ξ)` with `M ⊆ spt X`, and `M(X) = ∫_M θ dHⁿ < ∞`
  obtain ⟨R, hRrep, hRsupp⟩ := Submission.cmcdt_lpi_pr_imrep_in_support hIMC.2.1 N (k + 1)
    univ X isOpen_univ hXim
  have hmassR : X.mass = R.measure univ :=
    hMR N (k + 1) univ X R isOpen_univ hRrep univ isOpen_univ
  have hRuniv : R.measure univ = ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] := by
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hθfin : ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] ≠ ∞ := by
    rw [← hRuniv, ← hmassR]
    exact hXmass.ne
  have hθmeas : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    measurable_from_top.comp R.measurable_mult
  -- `θ ≥ 1` on `M`, so `Hⁿ(M) < ∞`
  have hMfin : μHE[k + 1] R.carrier ≠ ∞ := by
    refine ne_top_of_le_ne_top hθfin ?_
    calc μHE[k + 1] R.carrier = ∫⁻ x in R.carrier, (1 : ℝ≥0∞) ∂μHE[k + 1] := by simp
      _ ≤ ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] := by
        apply setLIntegral_mono hθmeas
        intro x hx
        exact_mod_cast R.mult_pos x hx
  have hloc : ∀ K : Set (Euclid N), IsCompact K → μHE[k + 1] (R.carrier ∩ K) ≠ ∞ :=
    fun K _ => ne_top_of_le_ne_top hMfin (measure_mono inter_subset_left)
  -- Step 2: bi-Lipschitz pieces `Gᵢ(Aᵢ)` of `M`
  obtain ⟨F, B, m, hLip, hBm, hmpos, hlow, hdiff, hFBm, hFBsub, hdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces N (k + 1) R.carrier R.measurableSet_carrier
      R.rectifiable
  -- Steps 3–5: `ξ ∘ Gᵢ` orients `span{DGᵢ eₐ}` a.e., with a Borel sign `sᵢ`
  have hsign : ∀ i, ∃ s : Euclid (k + 1) → ℤ, Measurable s ∧ (∀ u, s u = 1 ∨ s u = -1) ∧
      ∀ᵐ u ∂(volume.restrict (B i)), ∀ α : Covector (Euclid N) (k + 1),
        Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) =>
          inner ℝ (fderiv ℝ (F i) u (EuclideanSpace.single a 1))
            (fderiv ℝ (F i) u (EuclideanSpace.single b 1)))) * R.orient (F i u) α =
          (s u : ℝ) * α (fun a => fderiv ℝ (F i) u (EuclideanSpace.single a 1)) := by
    intro i
    obtain ⟨L, hL⟩ := hLip i
    obtain ⟨hae, hor⟩ := Submission.cmcdt_lpi_pr_piece_orientation_ae hIMC.1 N (k + 1)
      R.carrier R.orient (F i) (B i) L (m i) R.measurableSet_carrier hloc
      R.aestronglyMeasurable_orient R.orients hL (hBm i) (hmpos i) (hlow i) (hdiff i) (hFBsub i)
    exact Submission.cmcdt_lpi_pr_orientation_sign N (k + 1) (F i) (B i)
      (fun u => R.orient (F i u)) (hBm i) (fun u hu => (hdiff i u hu).2) hae hor
  choose s hsm hspm hstar using hsign
  have hinjOn : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have h1 := hlow i a ha a' ha'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖a - a'‖ ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos (hmpos i) hc
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- Step 8: the area formulas on each piece, for the weight `wᵢ = θ ∘ Gᵢ · sᵢ`
  have harea := fun i => Submission.cmcdt_lpi_pr_oriented_piece_area N (k + 1) (F i) (B i)
    R.mult R.orient (s i) (hBm i) (fun u hu => (hdiff i u hu).1) (fun u hu => (hdiff i u hu).2)
    (hinjOn i) (hspm i) (hstar i)
  have hwm : ∀ i, Measurable fun u => ((R.mult (F i u) : ℤ) * s i u) := by
    intro i
    obtain ⟨L, hL⟩ := hLip i
    have h1 : Measurable fun u => (R.mult (F i u) : ℤ) :=
      measurable_from_top.comp (R.measurable_mult.comp hL.continuous.measurable)
    exact (measurable_of_countable (fun p : ℤ × ℤ => p.1 * p.2)).comp (h1.prodMk (hsm i))
  -- Step 6: the weights `wᵢ` and the Jacobians `cᵢ = J_{Gᵢ}`
  refine ⟨F, B, fun i u => (R.mult (F i u) : ℤ) * s i u,
    fun i u => Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) =>
      inner ℝ (fderiv ℝ (F i) u (EuclideanSpace.single a 1))
        (fderiv ℝ (F i) u (EuclideanSpace.single b 1)))),
    hLip, hBm, hwm, fun i => (Submission.codim1_lura_gram_area_formula (k + 1) N (F i)).1,
    fun i u hu => (hdiff i u hu).1, fun i => (hFBsub i).trans hRsupp, ?_, ?_, ?_, ?_⟩
  · -- Step 10: `∫_{Aᵢ} |wᵢ| ≤ mᵢ⁻ⁿ ∫_M θ dHⁿ < ∞`
    intro i
    obtain ⟨L, hL⟩ := hLip i
    have hpull := Submission.cmcdt_lpi_pr_lintegral_pullback N (k + 1) (F i) (B i) L (m i) hL
      (hBm i) (hmpos i) (hlow i) (fun x => (R.mult x : ℝ≥0∞)) hθmeas
    refine ⟨(measurable_from_top.comp (hwm i)).aestronglyMeasurable, ?_⟩
    have habs : ∀ u, ‖((((R.mult (F i u) : ℤ) * s i u : ℤ)) : ℝ)‖ₑ =
        (R.mult (F i u) : ℝ≥0∞) := by
      intro u
      rcases hspm i u with h | h <;> simp [h]
    simp only [HasFiniteIntegral, habs]
    calc ∫⁻ u in B i, (R.mult (F i u) : ℝ≥0∞)
        ≤ ENNReal.ofReal ((m i ^ (k + 1))⁻¹) *
            ∫⁻ x in F i '' B i, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] := hpull
      _ ≤ ENNReal.ofReal ((m i ^ (k + 1))⁻¹) *
            ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] := by
          gcongr
          exact hFBsub i
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hθfin.lt_top
  · -- Step 7: `α(DGᵢ e) = J_{Gᵢ} ξᵤ(α)` with `ξᵤ` a unit orientation, so `|α(DGᵢ e)| ≤ cᵢ |α|`
    intro i u hu
    refine ⟨Real.sqrt_nonneg _, fun α => ?_⟩
    have hli : LinearIndependent ℝ (fun a => fderiv ℝ (F i) u (EuclideanSpace.single a 1)) := by
      have h0 := (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.linearIndependent
      have h1 := h0.map' (fderiv ℝ (F i) u : Euclid (k + 1) →ₗ[ℝ] Euclid N)
        (LinearMap.ker_eq_bot.mpr (hdiff i u hu).2)
      convert h1 using 1
      funext a
      simp
    obtain ⟨-, -, ξu, ⟨τ, hτ, -, hτs⟩, hξu, -⟩ :=
      Submission.cmcdt_lpi_unit_orientation_span N (k + 1) _ hli
    rw [hξu α, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    rcases hτs with h | h
    · rw [h α]
      exact hCB.2.2 N (k + 1) α τ hτ
    · rw [h α, abs_neg]
      exact hCB.2.2 N (k + 1) α τ hτ
  · -- Step 9: `Σᵢ ∫_{Aᵢ} |wᵢ| cᵢ = Σᵢ ∫_{Gᵢ(Aᵢ)} θ dHⁿ ≤ ∫_M θ dHⁿ = M(X)`
    calc ∑' i, ∫⁻ u in B i, ENNReal.ofReal (|((((R.mult (F i u) : ℤ) * s i u : ℤ)) : ℝ)| *
          Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) =>
            inner ℝ (fderiv ℝ (F i) u (EuclideanSpace.single a 1))
              (fderiv ℝ (F i) u (EuclideanSpace.single b 1)))))
        = ∑' i, ∫⁻ x in F i '' B i, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] := by
          congr 1
          funext i
          exact (harea i).1
      _ = ∫⁻ x in ⋃ i, F i '' B i, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] :=
          (lintegral_iUnion hFBm hdisj _).symm
      _ ≤ ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k + 1] :=
          lintegral_mono_set (iUnion_subset hFBsub)
      _ = X.mass := by rw [hmassR, hRuniv]
  · -- Step 11: `X(η) = ∫_M θ ξ(η) dHⁿ = Σᵢ ∫_{Gᵢ(Aᵢ)} θ ξ(η) dHⁿ = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)`
    intro η
    have hηc : Continuous (η : DifferentialForm (Euclid N) (k + 1)) := η.2.1.1.continuous
    have hηs : HasCompactSupport (η : DifferentialForm (Euclid N) (k + 1)) := η.2.1.2
    have hnc : Continuous fun x =>
        covectorEuclideanNorm ((η : DifferentialForm (Euclid N) (k + 1)) x) := by
      unfold covectorEuclideanNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
      split_ifs
      · exact ((continuous_eval_const _).comp hηc).pow 2
      · exact continuous_const
    have hcs : HasCompactSupport fun x =>
        covectorEuclideanNorm ((η : DifferentialForm (Euclid N) (k + 1)) x) :=
      hηs.comp_left (g := covectorEuclideanNorm) (covectorEuclideanNorm_zero N (k + 1))
    obtain ⟨C, hC⟩ := hnc.bounded_above_of_compact_support hcs
    set f : Euclid N → ℝ := fun x => (R.mult x : ℝ) *
      R.orient x ((η : DifferentialForm (Euclid N) (k + 1)) x) with hf
    have hXη : X η = ∫ x in R.carrier, f x ∂μHE[k + 1] := hRrep η
    have hθint : IntegrableOn (fun x => (R.mult x : ℝ)) R.carrier μHE[k + 1] := by
      refine ⟨(measurable_from_top.comp R.measurable_mult).aestronglyMeasurable, ?_⟩
      simp only [HasFiniteIntegral, Real.enorm_natCast]
      exact hθfin.lt_top
    have hfm : AEStronglyMeasurable f (μHE[k + 1].restrict R.carrier) := by
      refine (measurable_from_top.comp R.measurable_mult).aestronglyMeasurable.mul ?_
      exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid N) (k + 1))
        (F := ℝ)).continuous.comp_aestronglyMeasurable₂ R.aestronglyMeasurable_orient
        hηc.aestronglyMeasurable
    -- `|θ ξ(η)| ≤ C θ` a.e. on `M` by (IMC d), so `θ ξ(η)` is integrable on `M`
    have hint : IntegrableOn f R.carrier μHE[k + 1] := by
      refine (hθint.mul_const C).mono' hfm ?_
      filter_upwards [hIMC.2.2.2 N (k + 1) univ R] with x hx
      have h1 := hx ((η : DifferentialForm (Euclid N) (k + 1)) x)
      have h2 : covectorEuclideanNorm ((η : DifferentialForm (Euclid N) (k + 1)) x) ≤ C :=
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC x)
      rw [hf, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      gcongr
      exact h1.trans h2
    -- `Hⁿ(M ∖ ⋃ᵢ Gᵢ(Aᵢ)) = 0`
    have hcover : (⋃ i, F i '' B i) =ᵐ[μHE[k + 1]] R.carrier := by
      rw [ae_eq_set]
      refine ⟨?_, hnull⟩
      rw [sdiff_eq_empty.mpr (iUnion_subset hFBsub)]
      exact measure_empty
    have hsum := hasSum_integral_iUnion hFBm hdisj (hint.mono_set (iUnion_subset hFBsub))
    rw [setIntegral_congr_set hcover, ← hXη] at hsum
    convert hsum using 1
    funext i
    exact (harea i).2 η

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
/-- **Jacobian minors of a Lipschitz map**: for an `L`-Lipschitz `v : ℝᵐ → ℝᵖ`, rows
`a : Fin r → Fin p` and columns `b : Fin r → Fin m`, the minor
`M(u) = det ((Dv(u) e_{b t})_{a s})_{s,t}` is Borel measurable in `u` and `|M(u)| ≤ r! Lʳ`.
`u ↦ Dv(u)` is measurable and `A ↦ det ((A e_{b t})_{a s})` is continuous; every entry is bounded
by `‖Dv(u)‖ ≤ L`, and the Leibniz formula has `r!` terms of absolute value at most `Lʳ`. -/
theorem Submission.cmcdt_lpi_pc_minor_measurable_bound : ∀ (m p r : ℕ) (L : NNReal) (v : Euclid m → Euclid p) (a : Fin r → Fin p) (b : Fin r → Fin m), LipschitzWith L v → Measurable (fun u => Matrix.det (Matrix.of fun s t => fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s))) ∧ ∀ u, |Matrix.det (Matrix.of fun s t => fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s))| ≤ (r.factorial : ℝ) * (L : ℝ) ^ r := by
  intro m p r L v a b hv
  constructor
  · -- `u ↦ Dv(u)` is measurable and `A ↦ det ((A e_{b t})_{a s})` is continuous
    have hcont : Continuous fun A : Euclid m →L[ℝ] Euclid p =>
        Matrix.det (Matrix.of fun s t => A (EuclideanSpace.single (b t) 1) (a s)) := by
      refine Continuous.matrix_det (continuous_matrix fun s t => ?_)
      exact (continuous_apply (a s)).comp
        ((PiLp.continuous_ofLp 2 _).comp (continuous_eval_const _))
    exact hcont.measurable.comp (measurable_fderiv ℝ v)
  · intro u
    -- entry bound `|(Dv(u) e_{b t})_{a s}| ≤ ‖Dv(u)‖ ≤ L`
    have hentry : ∀ s t, |fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s)| ≤ (L : ℝ) := by
      intro s t
      calc |fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s)|
          = ‖fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ v u (EuclideanSpace.single (b t) 1)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖fderiv ℝ v u‖ * ‖EuclideanSpace.single (b t) (1 : ℝ)‖ := (fderiv ℝ v u).le_opNorm _
        _ = ‖fderiv ℝ v u‖ := by simp
        _ ≤ L := norm_fderiv_le_of_lipschitz ℝ hv
    -- Leibniz formula: `r!` terms, each of absolute value at most `Lʳ`
    rw [Matrix.det_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ σ : Equiv.Perm (Fin r), |Equiv.Perm.sign σ • ∏ i, Matrix.of
            (fun s t => fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s)) (σ i) i|
        ≤ ∑ _σ : Equiv.Perm (Fin r), (L : ℝ) ^ r := by
          refine Finset.sum_le_sum fun σ _ => ?_
          rw [Units.smul_def, zsmul_eq_mul, abs_mul, Finset.abs_prod]
          have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [hsign, one_mul]
          calc ∏ i, |Matrix.of (fun s t => fderiv ℝ v u (EuclideanSpace.single (b t) 1) (a s))
                (σ i) i|
              ≤ ∏ _i : Fin r, (L : ℝ) :=
                Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hentry _ _
            _ = (L : ℝ) ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (r.factorial : ℝ) * (L : ℝ) ^ r := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
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

/-- **Integration by parts for Jacobian minors** (formula (∗) of the weak continuity of Jacobian
minors, for `C²` maps): for `C²` functions `g₀, …, g_r` on `ℝᵏ`, directions `V₀, …, V_r` and a
compactly supported `C¹` function `ψ`, with `A = (Dg_c V_b)_{c,b}` and `M_b` the minor of `A`
without row `0` and column `b`, `∫ ψ det A = −Σ_b (−1)^b ∫ (Dψ V_b) g₀ M_b`.  Laplace expansion
along row `0`, the product rule for `F_b = ψ g₀ M_b` and the Piola identity
`Σ_b (−1)^b ∂_{V_b} M_b = 0` give `ψ det A = Σ_b (−1)^b ∂_{V_b} F_b − Σ_b (−1)^b (∂_{V_b} ψ) g₀ M_b`
pointwise, and `∫ ∂_W F = 0` for every compactly supported `C¹` function `F` (integration by
parts of the Lipschitz functions `1` and `F`). -/
theorem Submission.dor_lmb_fcd_jwc_smooth_minor_ibp : ∀ (k r : ℕ) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, ContDiff ℝ 2 (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
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
/-- **Derivative of the mollification of a Lipschitz function**: for an `L`-Lipschitz `f` and a
`C¹` kernel `ρ` with compact support, `D(ρ ⋆ f)(x) v = ∫ ρ(t) Df(x − t) v dt`.  Differentiating
under the integral (`HasCompactSupport.hasFDerivAt_convolution_left`) gives
`D(ρ ⋆ f)(x) v = ∫ Dρ(t) v · f(x − t) dt`.  With `t = x − s` and the reflected kernel
`h(s) = ρ(x − s)` (`C¹` with compact support, hence Lipschitz, and `∂_{−v} h(s) = Dρ(x − s) v`)
the two sides become `∫ ∂_{−v} h · f` and `∫ h · Df(·) v`; they agree by integration by parts for
Lipschitz functions (`LipschitzWith.integral_lineDeriv_mul_eq`: `∫ ∂_v f · h = ∫ ∂_{−v} h · f`)
and Rademacher (`∂_v f = Df · v` a.e.). -/
theorem Submission.dor_lmb_fcd_jwc_mollify_fderiv_eq : ∀ (k : ℕ) (L : NNReal) (f ρ : Euclid k → ℝ), LipschitzWith L f → ContDiff ℝ 1 ρ → HasCompactSupport ρ → ∀ x v : Euclid k, fderiv ℝ (fun y => ∫ t, ρ t * f (y - t)) x v = ∫ t, ρ t * fderiv ℝ f (x - t) v := by
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

/-- **Smooth approximation of a Lipschitz function** (step 4 of the weak continuity of Jacobians):
an `L`-Lipschitz `f : ℝᵏ → ℝ` is the uniform limit of `C^∞`, `L`-Lipschitz functions `f_n` with
`Df_n(x) → Df(x)` in operator norm for a.e. `x`.  Take `f_n = ρ_n ⋆ f`, where `ρ_n = φ_n / ∫ φ_n`
normalizes a bump `φ_n` equal to `1` on `B(0, 1/(n+2))` and supported in `B(0, 2/(n+2))`.  Then
`f_n` is smooth, `L`-Lipschitz (`cmcs_ls_mollify_lipschitz`) and `|f_n - f| ≤ 2L/(n+2)`.  By
`dor_lmb_fcd_jwc_mollify_fderiv_eq`, `Df_n(x) eᵢ = (ρ_n ⋆ Df(·) eᵢ)(x)`; as `∫ φ_n ≥ |B(0, 1/(n+2))|`
gives `0 ≤ ρ_n ≤ 2ᵈ / |B(0, 2/(n+2))|`, this tends to `Df(x) eᵢ` at every Lebesgue point of the
bounded function `Df(·) eᵢ`, and `‖T‖ ≤ ∑ᵢ |T eᵢ|` gives convergence in operator norm. -/
theorem Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx : ∀ (k : ℕ) (L : NNReal) (f : Euclid k → ℝ), LipschitzWith L f → ∃ fs : ℕ → Euclid k → ℝ, (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fs n)) ∧ (∀ n, LipschitzWith L (fs n)) ∧ TendstoUniformly fs f atTop ∧ ∀ᵐ x ∂(volume : Measure (Euclid k)), Tendsto (fun n => fderiv ℝ (fs n) x) atTop (𝓝 (fderiv ℝ f x)) := by
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
      Submission.dor_lmb_fcd_jwc_mollify_fderiv_eq k L f (ρ n) hf (hρc1 n) (hρs n) x v
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
/-- **Integration by parts for Jacobian minors of Lipschitz maps** (the step "`(∗)` holds for
Lipschitz `v`" in the weak continuity of Jacobian minors): for `L`-Lipschitz `g₀, …, g_r` on `ℝᵏ`,
vectors `V₀, …, V_r` and `ψ ∈ C¹_c(ℝᵏ)`,
`∫ ψ det A = −Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`, where `A = (Dg_c V_b)_{c,b}` and `M_b` is the minor
`det (Dg_{c+1} V_{s_b(b')})_{c,b'}`, `s_b = b.succAbove`.  Mollify every `g_c`: `C^∞`, `L`-Lipschitz
`g^n_c → g_c` uniformly with `Dg^n_c → Dg_c` a.e.  The identity holds for every `n` (smooth case);
the determinants converge a.e. and are bounded by `(r+1)! (L Σ_b ‖V_b‖)^(r+1)`, resp.
`r! (L Σ_b' ‖V_{s_b(b')}‖)^r`, so both sides converge by dominated convergence (on the right with
`|g^n_0| ≤ |g_0| + 1` for large `n`), and the limits agree. -/
theorem Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp : ∀ (k r : ℕ) (L : NNReal) (g : Fin (r + 1) → Euclid k → ℝ) (V : Fin (r + 1) → Euclid k) (ψ : Euclid k → ℝ), (∀ c, LipschitzWith L (g c)) → ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∫ x, ψ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)) = -∑ b : Fin (r + 1), (-1 : ℝ) ^ (b : ℕ) * ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) => fderiv ℝ (g c.succ) x (V (b.succAbove b'))) := by
  intro k r L g V ψ hg hψ hψs
  -- step 1: smooth `L`-Lipschitz approximants `fs c n` of every component `g c`
  choose fs hfs_smooth hfs_lip hfs_unif hfs_ae using
    fun c => Submission.dor_lmb_fcd_jwc_lipschitz_smooth_approx k L (g c) (hg c)
  -- step 2: the identity for the smooth maps `fs · n`
  have hid := fun n => Submission.dor_lmb_fcd_jwc_smooth_minor_ibp k r (fun c => fs c n) V ψ
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

/-- **Weak continuity of Jacobian minors of Lipschitz maps** (the induction `P(r)` of the weak
continuity of minors; Reshetnyak, Ball 1977, Ball–Currie–Olver 1981): if `gʲ_c, g_c` (`c < r`)
are `L`-Lipschitz on `ℝᵏ` with `gʲ_c → g_c` uniformly, `V_b ∈ ℝᵏ` and `φ` is integrable, then
`∫ φ det (Dgʲ_c V_b) → ∫ φ det (Dg_c V_b)`.  Induction on `r`, for all `L`, rows, directions and
weights; `r = 0` is trivial (the empty determinant is `1`).  For `r + 1` the minors are measurable
and bounded by `(r+1)! (L Σ_b ‖V_b‖)^(r+1)`, so by the weak-* upgrade it suffices to test against
`ψ ∈ C^∞_c`, and integration by parts gives `∫ ψ det = −Σ_b (−1)^b ∫ ∂_{V_b}ψ · g₀ · M_b`.  Split
`gʲ₀ = (gʲ₀ − g₀) + g₀`: the error term is at most `sup |gʲ₀ − g₀| · Br ∫ |∂_{V_b}ψ| → 0`, where
`Br` bounds the `r × r` minors `Mʲ_b`, and the main term converges by the induction hypothesis
with the integrable weight `∂_{V_b}ψ · g₀`. -/
theorem Submission.cmcdt_lpi_mwc_coordinate_minor_continuity : ∀ (k r : ℕ) (L : NNReal) (gs : ℕ → Fin r → Euclid k → ℝ) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k) (φ : Euclid k → ℝ), Integrable φ → (∀ j c, LipschitzWith L (gs j c)) → (∀ c, LipschitzWith L (g c)) → (∀ c, TendstoUniformly (fun j => gs j c) (g c) atTop) → Tendsto (fun j => ∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b))) atTop (𝓝 (∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
  intro k r
  induction r with
  | zero =>
    -- step 1: the empty determinant is `1`, so the sequence is constant
    intro L gs g V φ _ _ _ _
    simp only [Matrix.det_isEmpty, mul_one]
    exact tendsto_const_nhds
  | succ r ih =>
    intro L gs g V φ hφ hgs hg hconv
    -- step 2: the minors are measurable and bounded, so `C^∞_c` weights `ψ` suffice
    have hMs := fun j =>
      Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L (gs j) V (hgs j)
    have hM := Submission.dor_lmb_fcd_jwc_minor_measurable_bound k (r + 1) L g V hg
    refine Submission.dor_lmb_fcd_jwc_weak_star_l1_upgrade k _
      (fun j x => Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b)))
      (fun x => Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))
      (fun j => (hMs j).1.aestronglyMeasurable) hM.1.aestronglyMeasurable (fun j => (hMs j).2)
      hM.2 ?_ φ hφ
    intro ψ hψ hψs
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    -- step 3: integrate by parts (for every `j` and for the limit); it suffices to treat each `b`
    suffices hR : ∀ b : Fin (r + 1), Tendsto (fun j => ∫ x, fderiv ℝ ψ x (V b) * gs j 0 x *
        Matrix.det (Matrix.of fun (c b' : Fin r) =>
          fderiv ℝ (gs j c.succ) x (V (b.succAbove b')))) atTop
        (𝓝 (∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of fun (c b' : Fin r) =>
          fderiv ℝ (g c.succ) x (V (b.succAbove b'))))) by
      rw [Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L g V ψ hg hψ1 hψs]
      refine Tendsto.congr (fun j => (Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L (gs j)
        V ψ (hgs j) hψ1 hψs).symm) ?_
      exact Tendsto.neg (tendsto_finsetSum _ fun b _ => (hR b).const_mul _)
    intro b
    -- step 4: `χ = ∂_{V_b}ψ` and `θ = χ · g 0` are continuous with compact support, hence
    -- integrable; the minors `M j` are measurable and bounded by `Br`
    have hχc : Continuous (fun x => fderiv ℝ ψ x (V b)) :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hχs : HasCompactSupport (fun x => fderiv ℝ ψ x (V b)) :=
      hψs.fderiv_apply (𝕜 := ℝ) (V b)
    have hχi : Integrable (fun x => fderiv ℝ ψ x (V b)) :=
      hχc.integrable_of_hasCompactSupport hχs
    have hθi : Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x) :=
      (hχc.mul (hg 0).continuous).integrable_of_hasCompactSupport hχs.mul_right
    have hMb := fun j => Submission.dor_lmb_fcd_jwc_minor_measurable_bound k r L
      (fun c => gs j c.succ) (fun b' => V (b.succAbove b')) (fun c => hgs j c.succ)
    obtain ⟨Br, hBr0, hBr⟩ : ∃ Br : ℝ, 0 ≤ Br ∧ ∀ j x, ‖Matrix.det (Matrix.of fun (c b' : Fin r) =>
        fderiv ℝ (gs j c.succ) x (V (b.succAbove b')))‖ ≤ Br :=
      ⟨(r.factorial : ℝ) * ((L : ℝ) * ∑ b', ‖V (b.succAbove b')‖) ^ r, by positivity,
        fun j x => by rw [Real.norm_eq_abs]; exact (hMb j).2 x⟩
    have hI1 : ∀ j, Integrable (fun x => fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) *
        Matrix.det (Matrix.of fun (c b' : Fin r) =>
          fderiv ℝ (gs j c.succ) x (V (b.succAbove b')))) := fun j =>
      ((hχc.mul ((hgs j 0).continuous.sub (hg 0).continuous)).integrable_of_hasCompactSupport
        hχs.mul_right).mul_bdd (hMb j).1.aestronglyMeasurable (Eventually.of_forall (hBr j))
    have hI2 : ∀ j, Integrable (fun x => fderiv ℝ ψ x (V b) * g 0 x *
        Matrix.det (Matrix.of fun (c b' : Fin r) =>
          fderiv ℝ (gs j c.succ) x (V (b.succAbove b')))) := fun j =>
      hθi.mul_bdd (hMb j).1.aestronglyMeasurable (Eventually.of_forall (hBr j))
    -- split `gs j 0 = (gs j 0 - g 0) + g 0`
    have hsplit : ∀ j, ∫ x, fderiv ℝ ψ x (V b) * gs j 0 x * Matrix.det (Matrix.of
        fun (c b' : Fin r) => fderiv ℝ (gs j c.succ) x (V (b.succAbove b'))) =
        (∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) * Matrix.det (Matrix.of
          fun (c b' : Fin r) => fderiv ℝ (gs j c.succ) x (V (b.succAbove b')))) +
        ∫ x, fderiv ℝ ψ x (V b) * g 0 x * Matrix.det (Matrix.of
          fun (c b' : Fin r) => fderiv ℝ (gs j c.succ) x (V (b.succAbove b'))) := by
      intro j
      rw [← integral_add (hI1 j) (hI2 j)]
      congr 1
      funext x
      ring
    -- step 5: the error term tends to `0` by the uniform convergence `gs j 0 → g 0`
    have hT1 : Tendsto (fun j => ∫ x, fderiv ℝ ψ x (V b) * (gs j 0 x - g 0 x) *
        Matrix.det (Matrix.of fun (c b' : Fin r) =>
          fderiv ℝ (gs j c.succ) x (V (b.succAbove b')))) atTop (𝓝 0) := by
      obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∫ x, ‖fderiv ℝ ψ x (V b)‖ = A :=
        ⟨∫ x, ‖fderiv ℝ ψ x (V b)‖, integral_nonneg fun x => norm_nonneg _, rfl⟩
      have hBA : 0 ≤ Br * A := mul_nonneg hBr0 hA0
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hδ : 0 < ε / (Br * A + 1) := by positivity
      obtain ⟨N, hN⟩ := (Metric.tendstoUniformly_iff.1 (hconv 0) _ hδ).exists_forall_of_atTop
      refine ⟨N, fun j hj => ?_⟩
      rw [dist_zero_right]
      calc _ ≤ ∫ x, ε / (Br * A + 1) * Br * ‖fderiv ℝ ψ x (V b)‖ := by
            refine norm_integral_le_of_norm_le (hχi.norm.const_mul _)
              (Eventually.of_forall fun x => ?_)
            have h1 : ‖gs j 0 x - g 0 x‖ ≤ ε / (Br * A + 1) := by
              have := hN j hj x
              rw [dist_comm, dist_eq_norm] at this
              exact this.le
            have h2 := hBr j x
            rw [norm_mul, norm_mul]
            calc _ ≤ ‖fderiv ℝ ψ x (V b)‖ * (ε / (Br * A + 1)) * Br := by gcongr
              _ = ε / (Br * A + 1) * Br * ‖fderiv ℝ ψ x (V b)‖ := by ring
        _ = ε / (Br * A + 1) * (Br * A) := by rw [integral_const_mul, hA]; ring
        _ < ε / (Br * A + 1) * (Br * A + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
        _ = ε := div_mul_cancel₀ ε (by positivity)
    -- step 6: the main term converges by the induction hypothesis with the weight `θ`
    have hT2 := ih L (fun j c => gs j c.succ) (fun c => g c.succ) (fun b' => V (b.succAbove b'))
      (fun x => fderiv ℝ ψ x (V b) * g 0 x) hθi (fun j c => hgs j c.succ) (fun c => hg c.succ)
      (fun c => hconv c.succ)
    -- step 7: add the two limits
    have hsum := hT1.add hT2
    rw [zero_add] at hsum
    exact hsum.congr fun j => (hsplit j).symm

/-- **Weak continuity of Jacobian minors of Lipschitz maps** (step 6(v) of the integrality of
Lipschitz push-forwards; Simon Ch. 6, 2.29): if `v_j, v₀ : ℝᵐ → ℝᵖ` are `L`-Lipschitz, `v_j → v₀`
uniformly and `c ∈ L¹`, then `∫ c M^{a,b}(v_j) → ∫ c M^{a,b}(v₀)`, where
`M^{a,b}(v)(u) = det ((Dv(u) e_{b_t})_{a_s})_{s,t}`.  The coordinate projection `p_i y = y_i` is
`1`-Lipschitz, so the rows `v^{a_s} = p_{a_s} ∘ v` are `L`-Lipschitz and `v_j^{a_s} → v₀^{a_s}`
uniformly; the coordinate version `cmcdt_lpi_mwc_coordinate_minor_continuity` (with
`V_t = e_{b_t}`, `φ = c`) gives the convergence for the minors `det (D(v^{a_s}) e_{b_t})_{s,t}`.
At every point where `v` is differentiable, hence a.e. by Rademacher,
`D(v^{a_s})(u) = p_{a_s} ∘ Dv(u)`, so these minors have the same integrals as `M^{a,b}(v)`. -/
theorem Submission.cmcdt_lpi_minor_weak_continuity : ∀ (m p r : ℕ) (L : NNReal) (v : ℕ → Euclid m → Euclid p) (v₀ : Euclid m → Euclid p) (a : Fin r → Fin p) (b : Fin r → Fin m) (c : Euclid m → ℝ), (∀ j, LipschitzWith L (v j)) → LipschitzWith L v₀ → TendstoUniformly v v₀ atTop → Integrable c → Tendsto (fun j => ∫ u, c u * Matrix.det (Matrix.of fun s t => fderiv ℝ (v j) u (EuclideanSpace.single (b t) 1) (a s))) atTop (𝓝 (∫ u, c u * Matrix.det (Matrix.of fun s t => fderiv ℝ v₀ u (EuclideanSpace.single (b t) 1) (a s)))) := by
  intro m p r L v v₀ a b c hv hv₀ hvv₀ hc
  -- step 1: the coordinate projection `y ↦ y i` is `1`-Lipschitz, so the rows
  -- `v^{a_s} = (· (a s)) ∘ v` are `L`-Lipschitz and converge uniformly
  have hproj : ∀ i : Fin p, LipschitzWith 1 (fun y : Euclid p => y i) := fun i =>
    LipschitzWith.of_dist_le_mul fun y y' => by
      rw [NNReal.coe_one, one_mul]
      exact PiLp.dist_apply_le y y' i
  have hrow : ∀ f : Euclid m → Euclid p, LipschitzWith L f → ∀ s,
      LipschitzWith L (fun u => f u (a s)) := fun f hf s => by
    have h := (hproj (a s)).comp hf
    rw [one_mul] at h
    exact h
  -- step 2: by Rademacher, a.e. `D(v^{a_s})(u) e_{b_t} = (Dv(u) e_{b_t})_{a_s}`, so the
  -- coordinate minors have the same integrals as the minors of the statement
  have hcoord : ∀ f : Euclid m → Euclid p, LipschitzWith L f →
      ∫ u, c u * Matrix.det (Matrix.of fun s t =>
        fderiv ℝ (fun y => f y (a s)) u (EuclideanSpace.single (b t) 1)) =
      ∫ u, c u * Matrix.det (Matrix.of fun s t =>
        fderiv ℝ f u (EuclideanSpace.single (b t) 1) (a s)) := by
    intro f hf
    refine integral_congr_ae ?_
    filter_upwards [hf.ae_differentiableAt] with u hu
    have hent : ∀ (i : Fin p) (w : Euclid m),
        fderiv ℝ (fun y => f y i) u w = fderiv ℝ f u w i := by
      intro i w
      have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (f u) i).comp u hu.hasFDerivAt
      rw [show (fun y => f y i) = (fun g : Euclid p => g i) ∘ f from rfl, h.fderiv]
      rfl
    simp only [hent]
  -- step 3: the coordinate statement for `g_s = v^{a_s}`, `V_t = e_{b_t}` and `φ = c`
  have h := Submission.cmcdt_lpi_mwc_coordinate_minor_continuity m r L
    (fun j s u => v j u (a s)) (fun s u => v₀ u (a s)) (fun t => EuclideanSpace.single (b t) 1) c
    hc (fun j => hrow (v j) (hv j)) (hrow v₀ hv₀)
    (fun s => (hproj (a s)).uniformContinuous.comp_tendstoUniformly hvv₀)
  rw [hcoord v₀ hv₀] at h
  exact h.congr fun j => hcoord (v j) (hv j)

/-- **Weak continuity of `f(v_j) · M(v_j)` against `L¹` weights.**  Let `v_j → v₀` uniformly,
all `L`-Lipschitz, `w ∈ L¹(ℝ^m)`, `f` continuous with compact support, and
`M(v)(u) = det((Dv(u) e_{b t})_{a s})_{s,t}`.  Then `∫ w f(v_j) M(v_j) → ∫ w f(v₀) M(v₀)`.  Split
`w f(v_j) M_j = w (f(v_j) - f(v₀)) M_j + c M_j` with `c = w f(v₀) ∈ L¹`.  Since `|M_j| ≤ K = r! Lʳ`
and `f ∘ v_j → f ∘ v₀` uniformly, the first integral is eventually at most `η K ‖w‖₁` for any
`η > 0`; the second converges by the weak continuity of Jacobian minors. -/
theorem Submission.cmcdt_lpi_pc_scalar_weak_continuity : ∀ (m p r : ℕ) (L : NNReal) (v : ℕ → Euclid m → Euclid p) (v₀ : Euclid m → Euclid p) (a : Fin r → Fin p) (b : Fin r → Fin m) (w : Euclid m → ℝ) (f : Euclid p → ℝ), (∀ j, LipschitzWith L (v j)) → LipschitzWith L v₀ → TendstoUniformly v v₀ atTop → Integrable w → Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ u, w u * (f (v j u) * Matrix.det (Matrix.of fun s t => fderiv ℝ (v j) u (EuclideanSpace.single (b t) 1) (a s)))) atTop (𝓝 (∫ u, w u * (f (v₀ u) * Matrix.det (Matrix.of fun s t => fderiv ℝ v₀ u (EuclideanSpace.single (b t) 1) (a s))))) := by
  intro m p r L v v₀ a b w f hv hv₀ hunif hw hf hfc
  -- `f` is bounded by `C`, so the weight `c = w · f(v₀)` is integrable
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hc : Integrable (fun u => w u * f (v₀ u)) :=
    hw.mul_bdd (hf.comp hv₀.continuous).aestronglyMeasurable (Eventually.of_forall fun u => hC (v₀ u))
  -- the minors are measurable and bounded by `r! Lʳ`, and their `c`-integrals converge
  suffices key : ∀ (M : ℕ → Euclid m → ℝ) (M₀ : Euclid m → ℝ) (K : ℝ), (∀ j, Measurable (M j)) →
      (∀ j u, |M j u| ≤ K) →
      Tendsto (fun j => ∫ u, w u * f (v₀ u) * M j u) atTop (𝓝 (∫ u, w u * f (v₀ u) * M₀ u)) →
      Tendsto (fun j => ∫ u, w u * (f (v j u) * M j u)) atTop (𝓝 (∫ u, w u * (f (v₀ u) * M₀ u))) from
    key (fun j u => Matrix.det (Matrix.of fun s t => fderiv ℝ (v j) u (EuclideanSpace.single (b t) 1) (a s)))
      (fun u => Matrix.det (Matrix.of fun s t => fderiv ℝ v₀ u (EuclideanSpace.single (b t) 1) (a s)))
      ((r.factorial : ℝ) * (L : ℝ) ^ r)
      (fun j => (Submission.cmcdt_lpi_pc_minor_measurable_bound m p r L (v j) a b (hv j)).1)
      (fun j => (Submission.cmcdt_lpi_pc_minor_measurable_bound m p r L (v j) a b (hv j)).2)
      (Submission.cmcdt_lpi_minor_weak_continuity m p r L v v₀ a b (fun u => w u * f (v₀ u)) hv hv₀
        hunif hc)
  intro M M₀ K hM hMK hS
  have hK : 0 ≤ K := (abs_nonneg _).trans (hMK 0 0)
  have hfv : ∀ j, Continuous (fun u => f (v j u)) := fun j => hf.comp (hv j).continuous
  have hfv₀ : Continuous (fun u => f (v₀ u)) := hf.comp hv₀.continuous
  -- split `w f(v_j) M_j = w (f(v_j) - f(v₀)) M_j + c M_j`; both pieces are integrable
  have hI₁ : ∀ j, Integrable (fun u => w u * ((f (v j u) - f (v₀ u)) * M j u)) := fun j =>
    hw.mul_bdd (c := (C + C) * K) (((hfv j).sub hfv₀).measurable.mul (hM j)).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [norm_mul, Real.norm_eq_abs (M j u)]
        exact mul_le_mul ((norm_sub_le _ _).trans (add_le_add (hC _) (hC _))) (hMK j u)
          (abs_nonneg _) (by linarith))
  have hI₂ : ∀ j, Integrable (fun u => w u * f (v₀ u) * M j u) := fun j =>
    hc.mul_bdd (c := K) (hM j).aestronglyMeasurable
      (Eventually.of_forall fun u => (Real.norm_eq_abs _).le.trans (hMK j u))
  have hsplit : ∀ j, (∫ u, w u * (f (v j u) * M j u)) =
      (∫ u, w u * ((f (v j u) - f (v₀ u)) * M j u)) + ∫ u, w u * f (v₀ u) * M j u := by
    intro j
    rw [← integral_add (hI₁ j) (hI₂ j)]
    congr 1
    funext u
    ring
  -- the first piece tends to `0`
  have hT : Tendsto (fun j => ∫ u, w u * ((f (v j u) - f (v₀ u)) * M j u)) atTop (𝓝 0) := by
    have hU := (hfc.uniformContinuous_of_continuous hf).comp_tendstoUniformly hunif
    have hW : 0 ≤ ∫ u, ‖w u‖ := integral_nonneg fun u => norm_nonneg (w u)
    have hD : 0 < K * (∫ u, ‖w u‖) + 1 := by nlinarith [mul_nonneg hK hW]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η * K * (∫ u, ‖w u‖) < ε := by
      refine ⟨ε / (K * (∫ u, ‖w u‖) + 1), div_pos hε hD, ?_⟩
      rw [mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hK hW]
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hU η hη)
    refine ⟨N, fun n hn => ?_⟩
    have hpt : ∀ u, ‖w u * ((f (v n u) - f (v₀ u)) * M n u)‖ ≤ η * K * ‖w u‖ := by
      intro u
      have h₁ : ‖f (v n u) - f (v₀ u)‖ ≤ η := by
        rw [← dist_eq_norm, dist_comm]
        exact (hN n hn u).le
      calc ‖w u * ((f (v n u) - f (v₀ u)) * M n u)‖
          = ‖w u‖ * (‖f (v n u) - f (v₀ u)‖ * |M n u|) := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs (M n u)]
        _ ≤ ‖w u‖ * (η * K) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h₁ (hMK n u) (abs_nonneg _) hη.le) (norm_nonneg _)
        _ = η * K * ‖w u‖ := mul_comm _ _
    rw [dist_zero_right]
    calc ‖∫ u, w u * ((f (v n u) - f (v₀ u)) * M n u)‖ ≤ ∫ u, η * K * ‖w u‖ :=
          norm_integral_le_of_norm_le (hw.norm.const_mul _) (Eventually.of_forall hpt)
      _ = η * K * (∫ u, ‖w u‖) := integral_const_mul _ _
      _ < ε := hηε
  -- the second piece converges to `∫ c M₀`; add the limits
  have hlim := hT.add hS
  rw [zero_add] at hlim
  have e : (∫ u, w u * (f (v₀ u) * M₀ u)) = ∫ u, w u * f (v₀ u) * M₀ u := by
    congr 1
    funext u
    ring
  rw [e]
  exact hlim.congr fun j => (hsplit j).symm

/-- **Weak continuity of pull-backs under uniformly convergent Lipschitz maps** (step 6 (B4) of
the proof that Lipschitz push-forwards of integer multiplicity currents are integer multiplicity;
Simon Ch. 6, 2.29 and 3.6).  Let `Hⱼ, H₀ : ℝᵐ → ℝ^{N'}` be `L`-Lipschitz with `Hⱼ → H₀`
uniformly, `w ∈ L¹(ℝᵐ)` and `ω` a continuous, compactly supported `m`-form on `ℝ^{N'}`.  Then
`∫ w ω(Hⱼ)(DHⱼ e) → ∫ w ω(H₀)(DH₀ e)`.  For `I : Fin m → Fin N'` let
`ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (m-1)})` and `M_I(H)(u) = det ((DH(u) e_t)_{I s})_{s,t}`.
The coordinate expansion of `m`-covectors gives `w ω(H)(DH e) = (m!)⁻¹ Σ_I w ω_I(H) M_I(H)`
pointwise.  Every summand is integrable (`M_I(H)` is measurable and bounded by `m! Lᵐ`, and `ω_I`
is bounded), so the integral splits over `I`; each summand converges by the scalar weak continuity
with the continuous, compactly supported coefficient `ω_I`. -/
theorem Submission.cmcdt_lpi_pullback_weak_continuity : ∀ (m N' : ℕ) (L : NNReal) (H : ℕ → Euclid m → Euclid N') (H₀ : Euclid m → Euclid N') (w : Euclid m → ℝ) (ω : DifferentialForm (Euclid N') m), (∀ j, LipschitzWith L (H j)) → LipschitzWith L H₀ → TendstoUniformly H H₀ atTop → Integrable w → Continuous ω → HasCompactSupport ω → Tendsto (fun j => ∫ u, w u * ω (H j u) (fun a => fderiv ℝ (H j) u (EuclideanSpace.single a 1))) atTop (𝓝 (∫ u, w u * ω (H₀ u) (fun a => fderiv ℝ H₀ u (EuclideanSpace.single a 1)))) := by
  intro m N' L H H₀ w ω hH hH₀ hHH₀ hw hωc hωs
  -- the coefficients `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (m-1)})` are continuous with compact support
  have hωIc : ∀ I : Fin m → Fin N',
      Continuous fun y => ω y (fun c => EuclideanSpace.single (I c) (1 : ℝ)) := fun I =>
    hωc.eval_const _
  have hωIs : ∀ I : Fin m → Fin N',
      HasCompactSupport fun y => ω y (fun c => EuclideanSpace.single (I c) (1 : ℝ)) := fun I =>
    hωs.comp_left (g := fun α : Covector (Euclid N') m =>
      α (fun c => EuclideanSpace.single (I c) (1 : ℝ))) (by simp)
  -- step 1: `w ω(G)(DG e) = (m!)⁻¹ Σ_I w ω_I(G) M_I(G)` pointwise (coordinate expansion)
  have hexp : ∀ (G : Euclid m → Euclid N') (u : Euclid m),
      w u * ω (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) =
        (m.factorial : ℝ)⁻¹ * ∑ I : Fin m → Fin N',
          w u * (ω (G u) (fun c => EuclideanSpace.single (I c) (1 : ℝ)) *
            Matrix.det (Matrix.of fun s t => fderiv ℝ G u (EuclideanSpace.single t 1) (I s))) := by
    intro G u
    have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    rw [← Finset.mul_sum, ← Submission.dor_lmb_fcd_jwc_covector_det_expansion N' m (ω (G u))
      (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)), mul_left_comm (w u),
      inv_mul_cancel_left₀ hm]
  -- step 2: the minors are measurable and bounded by `m! Lᵐ` and `ω_I` is bounded, so every
  -- summand is integrable and the integral splits over `I`
  have hint : ∀ G : Euclid m → Euclid N', LipschitzWith L G →
      ∫ u, w u * ω (G u) (fun a => fderiv ℝ G u (EuclideanSpace.single a 1)) =
        (m.factorial : ℝ)⁻¹ * ∑ I : Fin m → Fin N', ∫ u,
          w u * (ω (G u) (fun c => EuclideanSpace.single (I c) (1 : ℝ)) *
            Matrix.det (Matrix.of fun s t => fderiv ℝ G u (EuclideanSpace.single t 1) (I s))) := by
    intro G hG
    have hI : ∀ I : Fin m → Fin N', Integrable fun u =>
        w u * (ω (G u) (fun c => EuclideanSpace.single (I c) (1 : ℝ)) *
          Matrix.det (Matrix.of fun s t => fderiv ℝ G u (EuclideanSpace.single t 1) (I s))) := by
      intro I
      obtain ⟨hmeas, hbd⟩ :=
        Submission.cmcdt_lpi_pc_minor_measurable_bound m N' m L G I (fun t => t) hG
      obtain ⟨C, hC⟩ := (hωIc I).bounded_above_of_compact_support (hωIs I)
      refine hw.mul_bdd (c := C * ((m.factorial : ℝ) * (L : ℝ) ^ m))
        (((hωIc I).comp hG.continuous).measurable.mul hmeas).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [norm_mul]
      exact mul_le_mul (hC _) ((Real.norm_eq_abs _).trans_le (hbd u)) (norm_nonneg _)
        ((norm_nonneg _).trans (hC 0))
    rw [← integral_finsetSum _ fun I _ => hI I, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall (hexp G))
  -- step 3: each summand converges by the scalar weak continuity with coefficient `ω_I`
  have hlim := (tendsto_finsetSum (Finset.univ : Finset (Fin m → Fin N')) fun I _ =>
    Submission.cmcdt_lpi_pc_scalar_weak_continuity m N' m L H H₀ I (fun t => t) w
      (fun y => ω y (fun c => EuclideanSpace.single (I c) (1 : ℝ))) hH hH₀ hHH₀ hw (hωIc I)
      (hωIs I)).const_mul ((m.factorial : ℝ)⁻¹)
  rw [hint H₀ hH₀]
  exact hlim.congr fun j => (hint (H j) (hH j)).symm

/-- **Integer density on one injective Lipschitz piece** (Simon Ch. 6, 3.6–3.9: the multiplicity
of `f#T` on a piece where `f` is injective).  Let `H : ℝⁿ → ℝᴾ` be `L`-Lipschitz, injective on the
Borel set `B` with injective `DH(u)` at every `u ∈ B`, and let `g : ℝⁿ → ℤ` be integrable and
nonzero on `B`.  With `h` a Borel inverse of `H|B` (Lusin–Souslin), `m = 1_{H(B)} · (g ∘ h)` is
Borel, integer-valued and `m ∘ H = g` on `B`.  For injective linear `A`, the area formula on the
unit ball and `Hⁿ(A(S)) ≤ ‖A‖ⁿ Hⁿ(S)` give `JA ≤ ‖A‖ⁿ`; as `‖DH‖ ≤ L`, `JH ≤ Lⁿ` on `B`, and the
area formula gives `∫_{H(B)} |m| dHⁿ = ∫_B JH |g| ≤ Lⁿ ∫_B |g|`.  Since `|m| ≥ 1` on `H(B)`, this
bounds `Hⁿ(H(B)) < ∞`. -/
theorem Submission.cmcdt_lpi_pc_piece_multiplicity : ∀ (P n : ℕ) (L : NNReal) (H : Euclid n → Euclid P) (B : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet B → InjOn H B → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → IntegrableOn (fun u => (g u : ℝ)) B → (∀ u ∈ B, g u ≠ 0) → ∃ m : Euclid P → ℝ, Measurable m ∧ (∀ y, ∃ z : ℤ, m y = z) ∧ (∀ u ∈ B, m (H u) = g u) ∧ μHE[n] (H '' B) ≠ ∞ ∧ ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n] ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ := by
  intro P n L H B g hH hB hinj hdiff hg hgi hg0
  -- `G A = √det(⟨A eₖ, A eₗ⟩)`, the Gram-determinant Jacobian of a linear `A : ℝⁿ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid n →L[ℝ] Euclid P) → ℝ, ∀ A, G A = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))) :=
    ⟨_, fun A => rfl⟩
  -- Lusin–Souslin: `H(B)` is Borel and `h ∘ H = id` on `B` for a Borel `h`
  obtain ⟨hN, h, hh, hhH⟩ := Submission.cmcdt_lpi_pc_measurable_inverse P n H B
    hH.continuous.continuousOn hB hinj
  -- the density `m = 1_{H(B)} · (g ∘ h)`
  obtain ⟨m, hm⟩ : ∃ m : Euclid P → ℝ, m = (H '' B).indicator fun y => (g (h y) : ℝ) := ⟨_, rfl⟩
  have hmH : ∀ u ∈ B, m (H u) = g u := fun u hu => by
    simp only [hm, indicator_of_mem (mem_image_of_mem H hu), hhH u hu]
  -- `G A ≤ ‖A‖ⁿ`: the area formula for `A` on the unit ball `B₁` gives `Hⁿ(A(B₁)) = G A · |B₁|`,
  -- while `A` is `‖A‖`-Lipschitz, so `Hⁿ(A(B₁)) ≤ ‖A‖ⁿ Hⁿ(B₁) = ‖A‖ⁿ |B₁|`
  have hGle : ∀ A : Euclid n →L[ℝ] Euclid P, Injective A →
      ENNReal.ofReal (G A) ≤ (‖A‖₊ : ℝ≥0∞) ^ n := by
    intro A hA
    have harea := (Submission.codim1_lura_gram_area_formula n P A).2 (ball 0 1) measurableSet_ball
      (fun x _ => A.differentiableAt) (fun x _ => by rw [A.fderiv]; exact hA) hA.injOn
      (fun _ => 1)
    simp only [A.fderiv, ← hG, mul_one, setLIntegral_one, setLIntegral_const] at harea
    have hlip := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (A.lipschitzWith.lipschitzOnWith (s := ball (0 : Euclid n) 1))
    rw [harea, EuclideanSpace.euclideanHausdorffMeasure_eq_volume n] at hlip
    exact (ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
      measure_ball_lt_top.ne).1 hlip
  -- the Jacobian bound `JH ≤ Lⁿ` on `B`, from `‖DH(u)‖ ≤ L`
  have hJ : ∀ u ∈ B, ENNReal.ofReal (G (fderiv ℝ H u)) ≤ (L : ℝ≥0∞) ^ n := by
    intro u hu
    refine (hGle _ (hdiff u hu).2).trans ?_
    have hle : ‖fderiv ℝ H u‖ ≤ L := norm_fderiv_le_of_lipschitz ℝ hH
    gcongr
    exact_mod_cast hle
  -- the area formula for `H` on `B` with weight `|m|`, and `m ∘ H = g` on `B`
  have hbound : ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n] ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ := by
    have hareaH := (Submission.codim1_lura_gram_area_formula n P H).2 B hB
      (fun u hu => (hdiff u hu).1) (fun u hu => (hdiff u hu).2) hinj fun y => ‖m y‖ₑ
    simp only [← hG] at hareaH
    calc ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n]
        = ∫⁻ u in B, ENNReal.ofReal (G (fderiv ℝ H u)) * ‖m (H u)‖ₑ := hareaH
      _ ≤ ∫⁻ u in B, (L : ℝ≥0∞) ^ n * ‖(g u : ℝ)‖ₑ := by
          refine setLIntegral_mono' hB fun u hu => ?_
          rw [hmH u hu]
          gcongr
          exact hJ u hu
      _ = (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  -- `|m| ≥ 1` on `H(B)` (`g` is a nonzero integer on `B`), so `Hⁿ(H(B)) ≤ ∫_{H(B)} |m| dHⁿ`
  have hmeasN : μHE[n] (H '' B) ≤ ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n] := by
    rw [← setLIntegral_one]
    refine setLIntegral_mono' hN ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [hmH u hu, Real.enorm_eq_ofReal_abs, ENNReal.one_le_ofReal, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (hg0 u hu)
  refine ⟨m, ?_, fun y => ?_, hmH, ?_, hbound⟩
  · rw [hm]
    exact ((measurable_of_countable fun z : ℤ => (z : ℝ)).comp (hg.comp hh)).indicator hN
  · by_cases hy : y ∈ H '' B
    · exact ⟨g (h y), by rw [hm, indicator_of_mem hy]⟩
    · exact ⟨0, by rw [hm, indicator_of_notMem hy, Int.cast_zero]⟩
  · exact (hmeasN.trans_lt (hbound.trans_lt (ENNReal.mul_lt_top
      (ENNReal.pow_lt_top ENNReal.coe_lt_top) hgi.2))).ne
/-- **Simon Ch. 6, 3.5 and 3.7** (the induced orientation of a bi-Lipschitz piece): let
`H : ℝⁿ → ℝᴾ` be `L`-Lipschitz, `B ⊆ ℝⁿ` Borel and `κ > 0` with `κ|a − a'| ≤ |H a − H a'|` on
`B`, and let `H` be differentiable with injective derivative at every point of `B`.  With
`v(u) = (DH(u)e₁, …, DH(u)eₙ)` and `J(u) = √det(⟨vₐ(u), v_b(u)⟩)`, the field
`η = 1_{H(B)} · ξ ∘ H⁻¹`, `ξ(u) = J(u)⁻¹ (α ↦ α(v(u)))`, is strongly measurable; for `u ∈ B`,
`η(H u)` is a unit orientation of `range DH(u)` with `J(u) η(H u)(α) = α(v(u))`; and `η` orients
the approximate tangent space of `H(B)` at `Hⁿ`-a.e. point of `H(B)`.
For an orthonormal basis `τ` of `range DH(u)` and the coordinate matrix `M` of `v(u)` in `τ`,
`α(v(u)) = det M · α(τ)` and `⟨vₐ, v_b⟩ = (MᵀM)ₐ_b`, so `J(u) = |det M| > 0` and
`η(H u) = ±(α ↦ α(τ))`.  The tangent planes `range DH(u)` exist at `H u` for a.e. `u ∈ B`, and
the area formula sends the exceptional `λ`-null set to an `Hⁿ`-null set. -/
theorem Submission.cmcdt_lpi_pc_piece_orientation : ∀ (P n : ℕ) (L : NNReal) (κ : ℝ) (H : Euclid n → Euclid P) (B : Set (Euclid n)), LipschitzWith L H → MeasurableSet B → 0 < κ → (∀ a ∈ B, ∀ a' ∈ B, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧ (∀ u ∈ B, IsUnitOrientationOf (η (H u)) (LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)) ∧ ∀ α : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (fderiv ℝ H u (EuclideanSpace.single a 1)) (fderiv ℝ H u (EuclideanSpace.single b 1)))) * η (H u) α = α (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) ∧ ∀ᵐ y ∂(μHE[n].restrict (H '' B)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (H '' B) y Q ∧ IsUnitOrientationOf (η y) Q := by
  intro P n L κ H B hH hB hκ hcolip hreg
  -- `H` is injective on `B`, so `H(B)` is Borel with a Borel left inverse `h`
  have hinjOn : InjOn H B := by
    intro a ha a' ha' hHa
    have h := hcolip a ha a' ha'
    rw [hHa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hκ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  obtain ⟨hN, h, hh, hhH⟩ := Submission.cmcdt_lpi_pc_measurable_inverse P n H B
    hH.continuous.continuousOn hB hinjOn
  -- `v(u) = (DH(u)eₐ)ₐ`, `J(u) = √det(⟨vₐ(u), v_b(u)⟩)`, `ev z = (α ↦ α(z))`, `ξ(u) = J(u)⁻¹ ev(v(u))`
  let v : Euclid n → Fin n → Euclid P := fun u a => fderiv ℝ H u (EuclideanSpace.single a 1)
  let J : Euclid n → ℝ := fun u =>
    Real.sqrt (Matrix.det (Matrix.of fun a b : Fin n => inner ℝ (v u a) (v u b)))
  let ev : (Fin n → Euclid P) → MultiVector P n := fun z =>
    ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ z
  let ξ : Euclid n → MultiVector P n := fun u => (J u)⁻¹ • ev (v u)
  have hξ : ∀ u (α : Covector (Euclid P) n), ξ u α = (J u)⁻¹ * α (v u) := fun _ _ => rfl
  -- `ev z = ∑_f (∏ₐ z_{a, f(a)}) ev(e_{f(0)}, …, e_{f(n-1)})`, a finite sum of constant vectors
  have hexp : ∀ z : Fin n → Euclid P, ev z = ∑ f : Fin n → Fin P,
      (∏ a, z a (f a)) • ev (fun a => EuclideanSpace.single (f a) (1 : ℝ)) := by
    intro z
    ext α
    have hz : z = fun a => ∑ i, z a i • EuclideanSpace.single i (1 : ℝ) := by
      funext a
      have h := (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (z a)
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
      exact h.symm
    have hα : α z = α (fun a => ∑ i, z a i • EuclideanSpace.single i (1 : ℝ)) := congrArg α hz
    simp only [ev, ContinuousAlternatingMap.apply_apply, _root_.sum_apply, _root_.smul_apply,
      smul_eq_mul]
    rw [hα, α.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [α.map_smul_univ, smul_eq_mul]
  -- strong measurability: `J` is Borel and every coefficient `∏ₐ (DH(u)eₐ)_{f(a)}` is Borel
  -- (instance search misses `ContinuousAdd (MultiVector P n)`: the `Add` of the `Covector`-domain
  -- operator space does not unify with that of its `AddGroup` at instance transparency)
  have : ContinuousAdd (MultiVector P n) :=
    (inferInstance : IsTopologicalAddGroup (MultiVector P n)).toContinuousAdd
  have hevm : StronglyMeasurable fun u => ev (v u) := by
    have h : (fun u => ev (v u)) = fun u => ∑ f : Fin n → Fin P,
        (∏ a, v u a (f a)) • ev (fun a => EuclideanSpace.single (f a) (1 : ℝ)) :=
      funext fun u => hexp (v u)
    rw [h]
    refine Finset.stronglyMeasurable_fun_sum Finset.univ fun f _ => ?_
    refine (Measurable.stronglyMeasurable ?_).smul_const _
    refine Finset.measurable_prod Finset.univ fun a _ => ?_
    exact (PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (f a)).measurable.comp
      (measurable_fderiv_apply_const ℝ H (EuclideanSpace.single a 1))
  have hJm : Measurable J := (Submission.codim1_lura_gram_area_formula n P H).1
  have hξm : StronglyMeasurable ξ := hJm.inv.stronglyMeasurable.smul hevm
  -- `η = 1_{H(B)} · ξ ∘ h`
  refine ⟨(H '' B).indicator (fun y => ξ (h y)), (hξm.comp_measurable hh).indicator hN, ?_⟩
  have hηH : ∀ u ∈ B, (H '' B).indicator (fun y => ξ (h y)) (H u) = ξ u := fun u hu =>
    (Set.indicator_of_mem (Set.mem_image_of_mem H hu) _).trans (congrArg ξ (hhH u hu))
  -- `ξ(u)` is a unit orientation of `range DH(u)` and `J(u) ξ(u)(α) = α(v(u))`
  have hi : ∀ u ∈ B, IsUnitOrientationOf (ξ u)
      (LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)) ∧
      ∀ α : Covector (Euclid P) n, J u * ξ u α = α (v u) := by
    intro u hu
    have hinj := (hreg u hu).2
    set W := LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)
    have hWdim : Module.finrank ℝ W = n := by
      rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
    -- an orthonormal basis `τ` of `W` and the coordinate matrix `M` of `v(u)` in it
    let b : OrthonormalBasis (Fin n) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hWdim)
    let τ : Fin n → Euclid P := fun i => (b i : Euclid P)
    let w : Fin n → W := fun a =>
      ⟨v u a, LinearMap.mem_range_self (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P)
        (EuclideanSpace.single a 1)⟩
    let M : Matrix (Fin n) (Fin n) ℝ := b.toBasis.toMatrix w
    have hτ : Orthonormal ℝ τ := b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hτspan : Submodule.span ℝ (Set.range τ) = W := by
      have hr : Set.range τ = W.subtype '' Set.range b := Set.range_comp _ _
      rw [hr, Submodule.span_image, ← OrthonormalBasis.coe_toBasis, b.toBasis.span_eq,
        Submodule.map_subtype_top]
    -- `α(v(u)) = det M · α(τ)`: restrict `α` to `W` and compare with the basis determinant
    have hαv : ∀ α : Covector (Euclid P) n, α (v u) = M.det * α τ := by
      intro α
      have h := (α.toAlternatingMap.compLinearMap W.subtype).eq_smul_basis_det b.toBasis
      calc α (v u) = (α.toAlternatingMap.compLinearMap W.subtype) w := rfl
        _ = ((α.toAlternatingMap.compLinearMap W.subtype) b.toBasis • b.toBasis.det) w := by
          rw [← h]
        _ = M.det * α τ := by
          simp only [AlternatingMap.smul_apply, b.toBasis.det_apply, smul_eq_mul]
          exact mul_comm _ _
    -- `⟨vₐ, v_c⟩ = (MᵀM)ₐ_c` because `τ` is orthonormal, so `J(u) = |det M|`
    have hgram : (Matrix.of fun a c : Fin n => inner ℝ (v u a) (v u c)) = M.transpose * M := by
      ext a c
      have h1 : inner ℝ (v u a) (v u c) = inner ℝ (w a) (w c) :=
        (Submodule.coe_inner W (w a) (w c)).symm
      rw [Matrix.of_apply, Matrix.mul_apply, h1, ← b.sum_inner_mul_inner (w a) (w c)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.transpose_apply, real_inner_comm (b i) (w a)]
      simp only [M, b.toBasis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply]
    have hJM : J u = |M.det| := by
      show Real.sqrt (Matrix.det (Matrix.of fun a c : Fin n => inner ℝ (v u a) (v u c))) = |M.det|
      rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
    -- `v(u)` is linearly independent (`DH(u)` is injective), so `det M ≠ 0`
    have hw : LinearIndependent ℝ w := by
      have h0 : LinearIndependent ℝ
          (fun a : Fin n => (EuclideanSpace.single a (1 : ℝ) : Euclid n)) := by
        have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
        have he : ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis =
            fun a : Fin n => (EuclideanSpace.single a (1 : ℝ) : Euclid n) := by
          funext a
          rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
        rwa [he] at h
      have h1 : LinearIndependent ℝ (v u) := h0.map' _ (LinearMap.ker_eq_bot.2 hinj)
      exact LinearIndependent.of_comp W.subtype h1
    have hdet : M.det ≠ 0 := by
      have hspan : Submodule.span ℝ (Set.range w) = ⊤ :=
        hw.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, hWdim])
      exact ((b.toBasis.is_basis_iff_det).1 ⟨hw, hspan⟩).ne_zero
    have hJpos : 0 < J u := by
      rw [hJM]
      exact abs_pos.2 hdet
    refine ⟨⟨τ, hτ, hτspan, ?_⟩, fun α => ?_⟩
    · rcases hdet.lt_or_gt with hneg | hpos
      · right
        intro α
        rw [hξ, hαv, hJM, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel_left₀ hdet]
      · left
        intro α
        rw [hξ, hαv, hJM, abs_of_pos hpos, inv_mul_cancel_left₀ hdet]
    · rw [hξ, mul_inv_cancel_left₀ hJpos.ne']
  refine ⟨fun u hu => ?_, ?_⟩
  · rw [hηH u hu]
    exact hi u hu
  · -- the tangent planes `range DH(u)` exist off a `λ`-null set `E ∩ B`, whose image is `Hⁿ`-null
    have htan := Submission.ptd_piece_image_approxTangent_ae P n H B L κ hH hB hκ hcolip hreg
    rw [ae_iff] at htan
    obtain ⟨E, hEsub, hEmeas, hE0⟩ := exists_measurable_superset_of_null htan
    rw [Measure.restrict_apply hEmeas] at hE0
    have hnull : μHE[n] (H '' (E ∩ B)) = 0 := by
      have harea := (Submission.codim1_lura_gram_area_formula n P H).2 (E ∩ B)
        (hEmeas.inter hB) (fun x hx => (hreg x hx.2).1) (fun x hx => (hreg x hx.2).2)
        (hinjOn.mono inter_subset_right) (fun _ => 1)
      rwa [setLIntegral_one, Measure.restrict_eq_zero.2 hE0, lintegral_zero_measure] at harea
    filter_upwards [ae_restrict_mem hN, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)]
      with y hyN hyE
    obtain ⟨u, hu, rfl⟩ := hyN
    refine ⟨LinearMap.range (fderiv ℝ H u : Euclid n →ₗ[ℝ] Euclid P), ?_, ?_⟩
    · by_contra hc
      have huE : u ∈ E := hEsub hc
      exact hyE ⟨u, ⟨huE, hu⟩, rfl⟩
    · rw [hηH u hu]
      exact (hi u hu).1

/-- **The Lipschitz image of an integer-weighted bi-Lipschitz piece** (Simon Ch. 6, 3.5–3.9).
Let `H : ℝⁿ → ℝᴾ` be `L`-Lipschitz, let `B ⊆ ℝⁿ` be Borel with `κ |a − a'| ≤ |H a − H a'|` on `B`
(`κ > 0`), `H` differentiable with injective `DH` at every point of `B`, and let `g : ℝⁿ → ℤ` be
measurable, integrable and nonzero on `B`.
Assume (L3) `|α(τ)| ≤ |α|` for orthonormal `τ`, and (IMC)(b): the restriction of an `IMRep` to
a Borel set represents a current.  Then `H_♯(g [[B]])` is an integer multiplicity current `Φ`
with `M(Φ) ≤ Lⁿ ∫_B |g|` and `Φ(ω) = ∫_B g ω(H)(DH e₀, …, DH eₙ₋₁)`.

Proof sketch:
* `H` is injective on `B`, so `N = H(B)` is Borel; `m = g ∘ H⁻¹` is an integer density with
  `∫_N |m| dHⁿ ≤ Lⁿ ∫_B |g|`, and `η` orients `N` `Hⁿ`-a.e. with `J η(H) = DH e₀ ∧ ⋯ ∧ DH eₙ₋₁`
  on `B`, `J` the Gram Jacobian.
* `(N, m, η)` is an `IMRep` acting by `ω ↦ ∫_N m ⟨ω, η⟩ dHⁿ` (`N ⊆ range H` is rectifiable), and
  (IMC)(b) with `E = ℝᴾ` makes it represent a current `Φ`.
* The Gram area formula gives `Φ(ω) = ∫_B J g ⟨ω(H), η(H)⟩ = ∫_B g ω(H)(DH e)`.
* For admissible `ω`, (L3) and the unit orientation give `|⟨ω, η⟩| ≤ 1` on `N`, so
  `M(Φ) ≤ ∫_N |m| dHⁿ ≤ Lⁿ ∫_B |g|`. -/
theorem Submission.cmcdt_lpi_pc_piece_current : (∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → ∀ (P n : ℕ) (L : NNReal) (κ : ℝ) (H : Euclid n → Euclid P) (B : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet B → 0 < κ → (∀ a ∈ B, ∀ a' ∈ B, κ * ‖a - a'‖ ≤ ‖H a - H a'‖) → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → IntegrableOn (fun u => (g u : ℝ)) B → (∀ u ∈ B, g u ≠ 0) → ∃ Φ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsIntegerMultiplicity Φ ∧ Φ.mass ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, Φ ω = ∫ u in B, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
  intro hL3 hIMC P n L κ H B g hH hB hκ hbilip hdiff hg hgint hg0
  -- Step 1: `H` is injective on `B`, so `N = H(B)` is Borel
  have hinj : InjOn H B := by
    intro a ha a' ha' haa'
    have h := hbilip a ha a' ha'
    rw [haa', sub_self, norm_zero] at h
    have h0 : ‖a - a'‖ ≤ 0 := by
      by_contra hpos
      exact absurd h (not_le.mpr (mul_pos hκ (not_le.mp hpos)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  have hNmeas : MeasurableSet (H '' B) :=
    (Submission.cmcdt_lpi_pc_measurable_inverse P n H B hH.continuous.continuousOn hB hinj).1
  -- Step 2: the integer density `m = g ∘ H⁻¹` and the orientation `η` of `N`
  obtain ⟨m, hm, hmint, hmH, hNfin, hmle⟩ :=
    Submission.cmcdt_lpi_pc_piece_multiplicity P n L H B g hH hB hinj hdiff hg hgint hg0
  obtain ⟨η, hη, hηH, hηae⟩ :=
    Submission.cmcdt_lpi_pc_piece_orientation P n L κ H B hH hB hκ hbilip hdiff
  have hmfin : ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n] ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (ne_of_lt hgint.hasFiniteIntegral)) hmle
  -- Step 3: the `IMRep` `(N, m, η)` in `ℝᴾ`
  obtain ⟨R, hR⟩ := Submission.cmcdt_ims_imrep_of_int_density P n univ (H '' B) η m isOpen_univ
    hNmeas (subset_univ _)
    ((Poincare.SimonGMT.Chapter03.countablyRectifiable_range hH).mono (image_subset_range H B))
    (fun K _ _ => ne_top_of_le_ne_top hNfin (measure_mono inter_subset_left)) hη hm hmint
    (fun K _ _ => ne_top_of_le_ne_top hmfin (lintegral_mono_set inter_subset_left)) hηae
  -- Step 4: (IMC)(b) with `E = ℝᴾ` gives the current `Φ`, acting by `∫_N m ⟨ω, η⟩ dHⁿ`
  obtain ⟨Φ, R', hR', hcar, hmult, horient⟩ :=
    hIMC P n univ R univ isOpen_univ MeasurableSet.univ
  have hΦ : ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
      Φ ω = ∫ y in H '' B, m y * η y ((ω : DifferentialForm (Euclid P) n) y) ∂μHE[n] := by
    intro ω
    rw [hR' ω, ← hR (ω : DifferentialForm (Euclid P) n)]
    simp only [IMRep.action]
    rw [hcar, inter_univ, hmult, horient]
  -- Step 5: the formula, from the Gram area formula and `J η(H) = DH e₀ ∧ ⋯ ∧ DH eₙ₋₁` on `B`
  have hformula : ∀ ω : TestFormOn (univ : Set (Euclid P)) n, Φ ω = ∫ u in B,
      (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u)
        (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
    intro ω
    rw [hΦ ω, Submission.codim1_lur_cd_injective_area_formula_gram P n H B hB
      (fun v hv => (hdiff v hv).1) (fun v hv => (hdiff v hv).2) hinj]
    refine setIntegral_congr_fun hB fun u hu => ?_
    have hJ := (hηH u hu).2 ((ω : DifferentialForm (Euclid P) n) (H u))
    rw [hmH u hu, ← hJ]
    ring
  refine ⟨Φ, ⟨R', hR'⟩, ?_, hformula⟩
  -- Step 6: the mass bound, from `|⟨ω, η⟩| ≤ 1` on `N` for admissible `ω`
  rw [GeometricCurrentOn.mass, GeometricCurrentOn.massOn]
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  have hle : ∀ y ∈ H '' B,
      ‖m y * η y ((ω : DifferentialForm (Euclid P) n) y)‖ₑ ≤ ‖m y‖ₑ := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨τ, hτ, -, hητ⟩ := (hηH u hu).1
    have h1 : |η (H u) ((ω : DifferentialForm (Euclid P) n) (H u))| ≤ 1 := by
      refine le_trans ?_ ((hL3 P n _ τ hτ).trans (hω.2 (H u)))
      rcases hητ with h | h <;> simp [h]
    rw [enorm_mul]
    calc ‖m (H u)‖ₑ * ‖η (H u) ((ω : DifferentialForm (Euclid P) n) (H u))‖ₑ
        ≤ ‖m (H u)‖ₑ * 1 := by
          gcongr
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_one.mpr h1
      _ = ‖m (H u)‖ₑ := mul_one _
  calc ENNReal.ofReal (Φ ω)
      ≤ ‖Φ ω‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ‖∫ y in H '' B, m y * η y ((ω : DifferentialForm (Euclid P) n) y) ∂μHE[n]‖ₑ := by
        rw [hΦ ω]
    _ ≤ ∫⁻ y in H '' B, ‖m y * η y ((ω : DifferentialForm (Euclid P) n) y)‖ₑ ∂μHE[n] :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n] := setLIntegral_mono' hNmeas hle
    _ ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ := hmle

/-- **Integer multiplicity push-forward of a weighted Lipschitz piece** (step B3 of the
deformation theorem, Simon 6.5.1; Simon 6.3.5–3.9 for `H_#τ(M, θ, ξ)`).  Let `n = k + 1`,
`H : ℝⁿ → ℝ^{N'}` be `L`-Lipschitz, `A ⊆ ℝⁿ` Borel and `g : ℝⁿ → ℤ` integrable on `A`.  Then
`ω ↦ ∫_A g(u)·ω(H(u))(DH(u)e₀, …, DH(u)eₙ₋₁) du` is an integer multiplicity current.
Write `Ψ_ω` for this integrand.  By `cmcdt_lpi_pc_regular_part_reduction`, `∫_A Ψ_ω = ∫_{A⁺} Ψ_ω`
with `A⁺ = {u ∈ A : DH(u) exists and is injective, g(u) ≠ 0}`.  `cmcdt_lpi_pc_bilipschitz_partition`
splits `A⁺` into disjoint Borel pieces `C_l` on which `H` is bi-Lipschitz, and
`cmcdt_lpi_pc_piece_current` (with (L3) of (CB) and part (b) of (IMC)) gives integer multiplicity
currents `Φ_l` with `M(Φ_l) ≤ Lⁿ ∫_{C_l} |g|` and `Φ_l(ω) = ∫_{C_l} Ψ_ω`.  Hence
`Σ_l M(Φ_l) ≤ Lⁿ ∫_A |g| < ∞`, (IMSc) sums the `Φ_l` to an integer multiplicity `S`, and countable
additivity of the integral over `A⁺ = ⋃_l C_l` gives `S(ω) = ∫_{A⁺} Ψ_ω = ∫_A Ψ_ω`. -/
theorem Submission.cmcdt_lpi_lipschitz_piece_im : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (N' k : ℕ) (L : NNReal) (H : Euclid (k + 1) → Euclid N') (A : Set (Euclid (k + 1))) (g : Euclid (k + 1) → ℤ), LipschitzWith L H → MeasurableSet A → Measurable g → IntegrableOn (fun u => (g u : ℝ)) A → ∃ S : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1), IsIntegerMultiplicity S ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), S ω = ∫ u in A, (g u : ℝ) * (ω : DifferentialForm (Euclid N') (k + 1)) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) := by
  intro hCB hIMC hIMSc N' k L H A g hH hA hg hgi
  -- Steps 1–2: `Ψ_ω` is integrable on `A` and `∫_A Ψ_ω = ∫_{A⁺} Ψ_ω`
  obtain ⟨hAp, hΨ⟩ :=
    Submission.cmcdt_lpi_pc_regular_part_reduction N' (k + 1) L H A g hH hA hg hgi
  set Ap : Set (Euclid (k + 1)) :=
    {u | u ∈ A ∧ DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u) ∧ g u ≠ 0}
  -- Step 3: disjoint Borel pieces `C_l` with `⋃_l C_l = A⁺`, on which `H` is bi-Lipschitz
  obtain ⟨C, κ, hCm, hCd, hCU, hκ, hCbil⟩ :=
    Submission.cmcdt_lpi_pc_bilipschitz_partition N' (k + 1) H Ap hAp
      fun a ha => ⟨ha.2.1, ha.2.2.1⟩
  have hCA : ∀ l, C l ⊆ Ap := fun l => (subset_iUnion C l).trans hCU.subset
  -- Steps 5–7: an integer multiplicity current `Φ_l` for each piece, with
  -- `M(Φ_l) ≤ Lⁿ ∫_{C_l} |g|` and `Φ_l(ω) = ∫_{C_l} Ψ_ω`
  choose Φ hΦim hΦmass hΦω using fun l =>
    Submission.cmcdt_lpi_pc_piece_current hCB.2.2 hIMC.2.1 N' (k + 1) L (κ l) H (C l) g hH
      (hCm l) (hκ l) (hCbil l) (fun a ha => ⟨(hCA l ha).2.1, (hCA l ha).2.2.1⟩) hg
      (hgi.mono_set fun u hu => (hCA l hu).1) fun u hu => (hCA l hu).2.2.2
  -- Step 8: `Σ_l M(Φ_l) ≤ Lⁿ Σ_l ∫_{C_l} |g| = Lⁿ ∫_{A⁺} |g| ≤ Lⁿ ∫_A |g| < ∞`
  have hsum : ∑' l, (Φ l).mass < ∞ :=
    calc ∑' l, (Φ l).mass ≤ ∑' l, (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in C l, ‖(g u : ℝ)‖ₑ :=
          ENNReal.tsum_le_tsum hΦmass
      _ = (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in Ap, ‖(g u : ℝ)‖ₑ := by
          rw [ENNReal.tsum_mul_left, ← lintegral_iUnion hCm hCd, hCU]
      _ ≤ (L : ℝ≥0∞) ^ (k + 1) * ∫⁻ u in A, ‖(g u : ℝ)‖ₑ :=
          mul_le_mul_right (lintegral_mono_set fun u hu => hu.1) _
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hgi.2
  -- (IMSc): the series `S = Σ_l Φ_l` is an integer multiplicity current
  obtain ⟨S, hS, -, -, hSim⟩ := hIMSc N' k Φ hsum
  refine ⟨S, hSim hΦim, fun ω => ?_⟩
  -- countable additivity over `A⁺ = ⋃_l C_l` and uniqueness of sums
  obtain ⟨hint, heq⟩ := hΨ ω
  rw [heq]
  refine (hS ω).unique ?_
  simp only [hΦω]
  rw [← hCU]
  exact hasSum_integral_iUnion hCm hCd
    (hint.mono_set (iUnion_subset fun l => (hCA l).trans fun u hu => hu.1))

/-- **Integrality of the Lipschitz push-forward** (Simon Ch. 6, 2.29 and 3.6–3.9; step 7 of the
proof of the Lipschitz push-forward used by the deformation theorem 6.5.1).  Assume (CB), (VO),
(MR), (IMC) and (IMS).  Let `X ∈ 𝒟ₖ₊₁(ℝᴺ)` be integer multiplicity with `M(X) < ∞`, `F`
`Λ`-Lipschitz, and `S ∈ 𝒟ₖ₊₁(ℝᴺ')` with `X(ηⱼ) → S(ω)`, where `ηⱼ = Fⱼ^#ω` near `spt X` for
smooth `Λ`-Lipschitz `Fⱼ → F` uniformly.  Then `S` is integer multiplicity.
* piece_representation: `X(η) = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)` with `Σᵢ ∫_{Aᵢ} |wᵢ| cᵢ ≤ M(X)`.
* On `Aᵢ ⊆ Gᵢ⁻¹(spt X)` the chain rule turns the `i`-th term of `X(ηⱼ)` into
  `Tᵢⱼ(ω) = ∫_{Aᵢ} wᵢ ω(Fⱼ ∘ Gᵢ)(D(Fⱼ ∘ Gᵢ) e)`, and (L1) bounds it by `Λⁿ C ∫_{Aᵢ} |wᵢ| cᵢ`
  when `|ω| ≤ C`.
* pullback_continuity gives `Tᵢⱼ(ω) → Tᵢ(ω) = ∫_{Aᵢ} wᵢ ω(F ∘ Gᵢ)(D(F ∘ Gᵢ) e)`, and Tannery's
  theorem gives `S(ω) = Σᵢ Tᵢ(ω)`.
* piece_current makes each `Tᵢ` an integer multiplicity `Sᵢ` with `M(Sᵢ) ≤ Λⁿ ∫_{Aᵢ} |wᵢ| cᵢ`;
  (IMS) sums the `Sᵢ` to an integer multiplicity current, which equals `S`. -/
theorem Submission.cmcdt_lpi_pushforward_im : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ((∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (S : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1)), LipschitzWith Λ F → IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (S ω))) → IsIntegerMultiplicity S := by
  intro hCB hVO hMR hIMC hIMS N N' k Λ F X S hF hX _hXc hXm hFs
  obtain ⟨Fs, hFs_smooth, hFs_lip, hFs_tend, hη⟩ := hFs
  -- (IMSc): (IMS) applied to (VO), (MR) and (IMC)
  have hIMSc := hIMS hVO hMR hIMC
  -- Step 1: `X(η) = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)`, with `Bᵢ = ∫_{Aᵢ} |wᵢ| cᵢ` and `Σᵢ Bᵢ ≤ M(X) < ∞`
  obtain ⟨G, A, w, c, hG_lip, hA, hw, -, hG_diff, hG_spt, hw_int, hc, hB, hXsum⟩ :=
    Submission.cmcdt_lpi_piece_representation hCB hVO hMR hIMC N k X hX hXm
  choose L hL using hG_lip
  obtain ⟨B, hBeq⟩ : ∃ B : ℕ → ℝ≥0∞,
      ∀ i, B i = ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) := ⟨_, fun _ => rfl⟩
  have hBsum : ∑' i, B i ≠ ∞ := by
    simp only [hBeq]
    exact (hB.trans_lt hXm).ne
  have hBi : ∀ i, B i ≠ ∞ := fun i => ne_top_of_le_ne_top hBsum (ENNReal.le_tsum i)
  -- Step 2: the `Fⱼ` are differentiable everywhere
  have hFs_diff : ∀ j, Differentiable ℝ (Fs j) := fun j =>
    (hFs_smooth j).differentiable (by simp)
  -- Step 3 (chain rule): on `Aᵢ`, `ω(Fⱼ ∘ Gᵢ)(D(Fⱼ ∘ Gᵢ) e) = βᵢⱼ(DGᵢ e)`,
  -- where `βᵢⱼ = ω(Fⱼ ∘ Gᵢ) ∘ DFⱼ(Gᵢ)`
  have hchain : ∀ i j, ∀ u ∈ A i, ∀ ω : DifferentialForm (Euclid N') (k + 1),
      ω (Fs j (G i u)) (fun a => fderiv ℝ (fun v => Fs j (G i v)) u (EuclideanSpace.single a 1)) =
        ((ω (Fs j (G i u))).compContinuousLinearMap (fderiv ℝ (Fs j) (G i u)))
          (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1)) := by
    intro i j u hu ω
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      fderiv_fun_comp u (hFs_diff j (G i u)) (hG_diff i u hu)]
    rfl
  -- Step 6 (pointwise): if `|ω| ≤ C`, then `|ω(Fⱼ ∘ Gᵢ)(D(Fⱼ ∘ Gᵢ) e)| ≤ cᵢ Λⁿ C` on `Aᵢ`, by (L1)
  have hpt : ∀ i j, ∀ u ∈ A i, ∀ (ω : DifferentialForm (Euclid N') (k + 1)) (C : ℝ),
      (∀ y, covectorEuclideanNorm (ω y) ≤ C) →
      |ω (Fs j (G i u)) (fun a => fderiv ℝ (fun v => Fs j (G i v)) u (EuclideanSpace.single a 1))|
        ≤ c i u * ((Λ : ℝ) ^ (k + 1) * C) := by
    intro i j u hu ω C hC
    rw [hchain i j u hu ω]
    obtain ⟨hc0, hcα⟩ := hc i u hu
    refine (hcα _).trans (mul_le_mul_of_nonneg_left ?_ hc0)
    refine (hCB.1 N N' (k + 1) (fderiv ℝ (Fs j) (G i u)) (ω (Fs j (G i u)))).trans ?_
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ (hFs_lip j)) _) (hC _)
      (covectorEuclideanNorm_nonneg _) (by positivity)
  -- Step 6 (integrated): `|Tᵢⱼ(ω)| ≤ Bᵢ Λⁿ C`, uniformly in `j`
  have hTij : ∀ i j (ω : DifferentialForm (Euclid N') (k + 1)) (C : ℝ), 0 ≤ C →
      (∀ y, covectorEuclideanNorm (ω y) ≤ C) →
      ‖∫ u in A i, (w i u : ℝ) * ω (Fs j (G i u))
          (fun a => fderiv ℝ (fun v => Fs j (G i v)) u (EuclideanSpace.single a 1))‖ ≤
        (B i).toReal * ((Λ : ℝ) ^ (k + 1) * C) := by
    intro i j ω C hC0 hC
    have hK : 0 ≤ (Λ : ℝ) ^ (k + 1) * C := by positivity
    have hfin : B i * ENNReal.ofReal ((Λ : ℝ) ^ (k + 1) * C) ≠ ∞ :=
      ENNReal.mul_ne_top (hBi i) ENNReal.ofReal_ne_top
    have hval : (B i * ENNReal.ofReal ((Λ : ℝ) ^ (k + 1) * C)).toReal =
        (B i).toReal * ((Λ : ℝ) ^ (k + 1) * C) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]
    refine (norm_integral_le_lintegral_norm _).trans ((ENNReal.toReal_mono hfin ?_).trans_eq hval)
    rw [hBeq i, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' (hA i) fun u hu => ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (hc i u hu).1)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpt i j u hu ω C hC) (abs_nonneg _)
  -- Step 7 (termwise limit): `Tᵢⱼ(ω) → Tᵢ(ω)`, by pullback_continuity with the weight `1_{Aᵢ} wᵢ`
  have hlim : ∀ i (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)),
      Tendsto (fun j => ∫ u in A i, (w i u : ℝ) *
          (ω : DifferentialForm (Euclid N') (k + 1)) (Fs j (G i u))
            (fun a => fderiv ℝ (fun v => Fs j (G i v)) u (EuclideanSpace.single a 1))) atTop
        (𝓝 (∫ u in A i, (w i u : ℝ) * (ω : DifferentialForm (Euclid N') (k + 1)) (F (G i u))
          (fun a => fderiv ℝ (fun v => F (G i v)) u (EuclideanSpace.single a 1)))) := by
    intro i ω
    have hind : ∀ f : Euclid (k + 1) → ℝ,
        ∫ u, (A i).indicator (fun u => (w i u : ℝ)) u * f u = ∫ u in A i, (w i u : ℝ) * f u := by
      intro f
      rw [← integral_indicator (hA i)]
      congr 1
      funext u
      exact (Set.indicator_mul_left _ _ _).symm
    have h := Submission.cmcdt_lpi_pullback_weak_continuity (k + 1) N' (Λ * L i)
      (fun j v => Fs j (G i v)) (fun v => F (G i v)) ((A i).indicator fun u => (w i u : ℝ))
      (ω : DifferentialForm (Euclid N') (k + 1)) (fun j => (hFs_lip j).comp (hL i))
      (hF.comp (hL i)) (hFs_tend.comp (G i)) ((hw_int i).integrable_indicator (hA i))
      (ContDiff.continuous ω.property.1.1) ω.property.1.2
    simpa only [hind] using h
  -- every test form has bounded coefficient norm: `|·|` is continuous and `ω` has compact support
  have hNcont : Continuous fun α : Covector (Euclid N') (k + 1) => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ↓reduceIte]
      exact (continuous_eval_const _).pow 2
    · simp only [hI, ↓reduceIte]
      exact continuous_const
  have hbound : ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) ≤ C := by
    intro ω
    have hcs : HasCompactSupport fun y =>
        covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) :=
      HasCompactSupport.comp_left (g := covectorEuclideanNorm) ω.property.1.2
        (covectorEuclideanNorm_zero N' (k + 1))
    obtain ⟨C, hC⟩ :=
      (hNcont.comp (ContDiff.continuous ω.property.1.1)).bounded_above_of_compact_support hcs
    exact ⟨max C 0, le_max_right _ _, fun y =>
      ((Real.le_norm_self _).trans (hC y)).trans (le_max_left _ _)⟩
  -- Tannery's theorem (dominated convergence for series): if `|fⱼ(i)| ≤ bᵢ` with `Σᵢ bᵢ < ∞`
  -- and `fⱼ(i) → g(i)` for every `i`, then `Σᵢ fⱼ(i) → Σᵢ g(i)`; an `ε/3` argument
  have htannery : ∀ (f : ℕ → ℕ → ℝ) (g bound : ℕ → ℝ), Summable bound →
      (∀ i, Tendsto (fun j => f j i) atTop (𝓝 (g i))) → (∀ j i, ‖f j i‖ ≤ bound i) →
      Tendsto (fun j => ∑' i, f j i) atTop (𝓝 (∑' i, g i)) := by
    intro f g bound h_sum hab h_bound
    have h_g_le : ∀ i, ‖g i‖ ≤ bound i := fun i =>
      le_of_tendsto' (tendsto_norm.comp (hab i)) fun j => h_bound j i
    have h_sumg : Summable fun i => ‖g i‖ :=
      h_sum.of_norm_bounded fun i => (norm_norm (g i)).symm ▸ h_g_le i
    have h_suma : ∀ j, Summable fun i => ‖f j i‖ := fun j =>
      h_sum.of_norm_bounded fun i => by simpa only [norm_norm] using h_bound j i
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- a finite set `T` carrying all but `ε/3` of `Σᵢ bᵢ`
    obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, dist (∑ i ∈ T, bound i) (∑' i, bound i) < ε / 3 := by
      have hS := h_sum.hasSum
      rw [HasSum, Metric.tendsto_nhds] at hS
      exact Eventually.exists <| hS _ (by positivity)
    have h1 : ∑' i : (Tᶜ : Set ℕ), bound i < ε / 3 := by
      calc _ ≤ ‖∑' i : (Tᶜ : Set ℕ), bound i‖ := Real.le_norm_self _
        _ = ‖∑' i, bound i - ∑ i ∈ T, bound i‖ := congrArg _ ?_
        _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT
      rw [eq_sub_iff_add_eq']
      exact h_sum.sum_add_tsum_compl
    have h2 : Tendsto (fun j => ∑ i ∈ T, f j i) atTop (𝓝 (∑ i ∈ T, g i)) :=
      tendsto_finsetSum _ fun i _ => hab i
    rw [Metric.tendsto_nhds] at h2
    filter_upwards [h2 (ε / 3) (by positivity)] with j hj
    rw [dist_eq_norm, ← (h_suma j).of_norm.tsum_sub h_sumg.of_norm,
      ← ((h_suma j).of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T),
      (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
    refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
    · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hj
    · rw [((h_suma j).subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
      refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
      · refine ((norm_tsum_le_tsum_norm ((h_suma j).subtype _)).trans ?_).trans_lt h1
        exact ((h_suma j).subtype _).tsum_le_tsum (fun i => h_bound j i) (h_sum.subtype _)
      · refine ((norm_tsum_le_tsum_norm (h_sumg.subtype _)).trans ?_).trans_lt h1
        exact (h_sumg.subtype _).tsum_le_tsum (fun i => h_g_le i) (h_sum.subtype _)
  -- Step 8 (☆): `S(ω) = Σᵢ Tᵢ(ω)`, and `|Tᵢ(ω)| ≤ Bᵢ Λⁿ C` when `|ω| ≤ C`
  have hstar : ∀ (ω : TestFormOn (univ : Set (Euclid N')) (k + 1)) (C : ℝ), 0 ≤ C →
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N') (k + 1)) y) ≤ C) →
      HasSum (fun i => ∫ u in A i, (w i u : ℝ) *
          (ω : DifferentialForm (Euclid N') (k + 1)) (F (G i u))
            (fun a => fderiv ℝ (fun v => F (G i v)) u (EuclideanSpace.single a 1))) (S ω) ∧
      ∀ i, ‖∫ u in A i, (w i u : ℝ) * (ω : DifferentialForm (Euclid N') (k + 1)) (F (G i u))
          (fun a => fderiv ℝ (fun v => F (G i v)) u (EuclideanSpace.single a 1))‖ ≤
        (B i).toReal * ((Λ : ℝ) ^ (k + 1) * C) := by
    intro ω C hC0 hC
    -- the limits `Tᵢ(ω)` inherit the bound of the `Tᵢⱼ(ω)`
    have hTi : ∀ i, ‖∫ u in A i, (w i u : ℝ) *
        (ω : DifferentialForm (Euclid N') (k + 1)) (F (G i u))
          (fun a => fderiv ℝ (fun v => F (G i v)) u (EuclideanSpace.single a 1))‖ ≤
        (B i).toReal * ((Λ : ℝ) ^ (k + 1) * C) := fun i =>
      le_of_tendsto' (hlim i ω).norm fun j => hTij i j ω C hC0 hC
    have hbsum : Summable fun i => (B i).toReal * ((Λ : ℝ) ^ (k + 1) * C) :=
      (ENNReal.summable_toReal hBsum).mul_right _
    refine ⟨?_, hTi⟩
    obtain ⟨ηs, hηW, hηlim⟩ := hη ω
    -- Step 5: `X(ηⱼ) = Σᵢ Tᵢⱼ(ω)`, since `ηⱼ = Fⱼ^#ω` on a neighbourhood of `Gᵢ(Aᵢ) ⊆ spt X`
    have hXj : ∀ j, HasSum (fun i => ∫ u in A i, (w i u : ℝ) *
        (ω : DifferentialForm (Euclid N') (k + 1)) (Fs j (G i u))
          (fun a => fderiv ℝ (fun v => Fs j (G i v)) u (EuclideanSpace.single a 1)))
        (X (ηs j)) := by
      intro j
      obtain ⟨W, -, hXW, hW⟩ := hηW j
      convert hXsum (ηs j) using 1
      funext i
      refine setIntegral_congr_fun (hA i) fun u hu => ?_
      rw [hW (G i u) (hXW (hG_spt i (mem_image_of_mem (G i) hu))),
        hchain i j u hu (ω : DifferentialForm (Euclid N') (k + 1))]
    -- Step 8: Tannery's theorem, `X(ηⱼ) = Σᵢ Tᵢⱼ(ω) → Σᵢ Tᵢ(ω)`; also `X(ηⱼ) → S(ω)`
    have htan := htannery _ _ _ hbsum (fun i => hlim i ω) fun j i =>
      hTij i j (ω : DifferentialForm (Euclid N') (k + 1)) C hC0 hC
    rw [tendsto_nhds_unique hηlim (Tendsto.congr (fun j => (hXj j).tsum_eq) htan)]
    exact (hbsum.of_norm_bounded hTi).hasSum
  -- Step 9: integer multiplicity pieces `Sᵢ` with `Sᵢ(ω) = Tᵢ(ω)`
  choose Sp hSp_im hSp using fun i => Submission.cmcdt_lpi_lipschitz_piece_im hCB hIMC hIMSc N'
    k (Λ * L i) (fun v => F (G i v)) (A i) (w i) (hF.comp (hL i)) (hA i) (hw i) (hw_int i)
  -- Step 10: `M(Sᵢ) ≤ Λⁿ Bᵢ`, so `Σᵢ M(Sᵢ) < ∞`
  have hSp_mass : ∀ i,
      (Sp i).mass ≤ ENNReal.ofReal ((B i).toReal * ((Λ : ℝ) ^ (k + 1) * 1)) := by
    intro i
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hSp i ω]
    exact (Real.le_norm_self _).trans ((hstar ω 1 zero_le_one hω.2).2 i)
  have hSp_sum : ∑' i, (Sp i).mass < ∞ := by
    have hbsum1 : Summable fun i => (B i).toReal * ((Λ : ℝ) ^ (k + 1) * 1) :=
      (ENNReal.summable_toReal hBsum).mul_right _
    calc ∑' i, (Sp i).mass
        ≤ ∑' i, ENNReal.ofReal ((B i).toReal * ((Λ : ℝ) ^ (k + 1) * 1)) :=
          ENNReal.tsum_le_tsum hSp_mass
      _ = ENNReal.ofReal (∑' i, (B i).toReal * ((Λ : ℝ) ^ (k + 1) * 1)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hbsum1).symm
      _ < ∞ := ENNReal.ofReal_lt_top
  -- Step 11: `Ŝ = Σᵢ Sᵢ` is integer multiplicity, and `Ŝ(ω) = Σᵢ Tᵢ(ω) = S(ω)`
  obtain ⟨Shat, hShat, -, -, hShat_im⟩ := hIMSc N' k Sp hSp_sum
  obtain ⟨R, hR⟩ := hShat_im hSp_im
  refine ⟨R, fun ω => ?_⟩
  rw [← hR ω]
  obtain ⟨C, hC0, hC⟩ := hbound ω
  refine (hstar ω C hC0 hC).1.unique ?_
  simpa only [hSp] using hShat ω
/-- **The cylinder over an integer multiplicity current is integer multiplicity** (step 8 (B5) of
the proof of the deformation theorem, Simon 6.5.1; Simon Ch. 6, 2.18–2.20 and 3.2(2):
`[[(0,1)]] × τ(M, θ, ξ) = τ((0,1) × M, θ, e₁ ∧ ξ)`).  Write `ι(t, x) = (t, x) ∈ ℝᴺ⁺¹`,
`e₀ = ι(1, 0)` and `Jv = ι(0, v)`.  Let `X ∈ 𝒟ₖ₊₁(ℝᴺ)` be integer multiplicity with `M(X) < ∞`,
and let `C ∈ 𝒟ₖ₊₂(ℝᴺ⁺¹)` satisfy `C(ω) = X(η)` for a test form `η` with
`η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt`.  By `cmcdt_lpi_piece_representation`,
`X(η) = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)` with Lipschitz `Gᵢ` and `Σᵢ ∫_{Aᵢ} |wᵢ| cᵢ ≤ M(X)`.  The product
pieces `Ĝᵢ(z) = ι(z₀, Gᵢ(tail z))` on `Âᵢ = (0, 1) × Aᵢ` with weights `ŵᵢ = wᵢ ∘ tail` turn each
term into `∫_{Âᵢ} ŵᵢ ω(Ĝᵢ)(DĜᵢ ê)` (`cmcdt_lpi_cyl_piece_action`), the action of an integer
multiplicity current `Ŝᵢ` (`cmcdt_lpi_lipschitz_piece_im`) of mass `M(Ŝᵢ) ≤ ∫_{Aᵢ} |wᵢ| cᵢ`
(`cmcdt_lpi_cyl_piece_mass`).  So `Σᵢ M(Ŝᵢ) ≤ M(X) < ∞`, (IMS) sums the `Ŝᵢ` to an integer
multiplicity current `Ĉ`, and `C(ω) = Σᵢ Ŝᵢ(ω) = Ĉ(ω)` for every test form `ω`. -/
theorem Submission.cmcdt_lpi_cylinder_im : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (τ : Fin k → Euclid N), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ((∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)), IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η : DifferentialForm (Euclid N) (k + 1)) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = X η) → IsIntegerMultiplicity C := by
  intro hCB hVO hMR hIMC hIMS N k X C hX _hXc hXm hslice
  -- (IMSc): (IMS) applied to (VO), (MR), (IMC)
  have hIMSc := hIMS hVO hMR hIMC
  -- Step 1: pieces `(Gᵢ, Aᵢ, wᵢ, cᵢ)` with `X(η) = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)`
  obtain ⟨G, A, w, c, hGL, hA, hw, hc, hGd, -, hwi, hcb, hsum, hrep⟩ :=
    Submission.cmcdt_lpi_piece_representation hCB hVO hMR hIMC N k X hX hXm
  choose L hL using hGL
  -- Step 2: the product pieces `Ĝᵢ(z) = ι(z₀, Gᵢ(tail z))`, `Âᵢ = (0, 1) × Aᵢ`, `ŵᵢ = wᵢ ∘ tail`
  obtain ⟨Gh, hGh⟩ : ∃ Gh : ℕ → Euclid (k + 1 + 1) → Euclid (N + 1), ∀ i z,
      Gh i z = WithLp.toLp 2 (Fin.cons (WithLp.ofLp z 0)
        (WithLp.ofLp (G i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)))))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Ah, hAh⟩ : ∃ Ah : ℕ → Set (Euclid (k + 1 + 1)), ∀ i,
      Ah i = {z : Euclid (k + 1 + 1) | WithLp.ofLp z 0 ∈ Ioo (0 : ℝ) 1 ∧
        (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) : Euclid (k + 1)) ∈ A i} :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨wh, hwh⟩ : ∃ wh : ℕ → Euclid (k + 1 + 1) → ℤ, ∀ i z,
      wh i z = w i (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) :=
    ⟨_, fun _ _ => rfl⟩
  -- Steps 2–3 for each piece: `Ĝᵢ` Lipschitz, `Âᵢ` Borel, `ŵᵢ` integrable, and the slice identity
  -- `∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e) = ∫_{Âᵢ} ŵᵢ ω(Ĝᵢ)(DĜᵢ ê)`
  have hact := fun i => Submission.cmcdt_lpi_cyl_piece_action N (k + 1) (L i) (G i) (A i) (w i)
    (Gh i) (Ah i) (wh i) (hL i) (hA i) (hw i) (hwi i) (hGd i) (hGh i) (hAh i) (hwh i)
  -- Step 4: integer multiplicity pieces `Ŝᵢ(ω) = ∫_{Âᵢ} ŵᵢ ω(Ĝᵢ)(DĜᵢ ê)`
  have hS : ∀ i, ∃ S : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1),
      IsIntegerMultiplicity S ∧ ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1),
        S ω = ∫ z in Ah i, (wh i z : ℝ) *
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) (Gh i z)
            (fun a => fderiv ℝ (Gh i) z (EuclideanSpace.single a 1)) := by
    intro i
    obtain ⟨hGhL, hAhm, hwhm, hwhi, -⟩ := hact i
    exact Submission.cmcdt_lpi_lipschitz_piece_im hCB hIMC hIMSc (N + 1) (k + 1) (max 1 (L i))
      (Gh i) (Ah i) (wh i) hGhL hAhm hwhm hwhi
  choose S hSim hSrep using hS
  -- Step 5: `M(Ŝᵢ) = sup {Ŝᵢ(ω) : |ω| ≤ 1} ≤ ∫_{Aᵢ} |wᵢ| cᵢ`, so `Σᵢ M(Ŝᵢ) ≤ M(X) < ∞`
  have hmass : ∀ i, (S i).mass ≤ ∫⁻ u in A i, ENNReal.ofReal (|(w i u : ℝ)| * c i u) := by
    intro i
    unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    dsimp only
    rw [hSrep i ω]
    exact Submission.cmcdt_lpi_cyl_piece_mass hCB.1 hCB.2.1 N (k + 1) (G i) (A i) (w i) (c i)
      (Gh i) (Ah i) (wh i) (hA i) (hw i) (hc i) (hGd i) (hcb i) (hGh i) (hAh i) (hwh i) _ hω.2
  have hfin : ∑' i, (S i).mass < ∞ :=
    lt_of_le_of_lt ((ENNReal.tsum_le_tsum hmass).trans hsum) hXm
  -- Step 6: (IMSc) sums the `Ŝᵢ` to an integer multiplicity `Ĉ = τ(R)`
  obtain ⟨Ch, hChsum, -, -, hChim⟩ := hIMSc (N + 1) (k + 1) S hfin
  obtain ⟨R, hR⟩ := hChim hSim
  -- `C(ω) = X(η) = Σᵢ Ŝᵢ(ω) = Ĉ(ω)`, so `R` also represents `C`
  refine ⟨R, fun ω => ?_⟩
  obtain ⟨η, hη, hCω⟩ := hslice ω
  have hSη : (fun i => S i ω) = fun i => ∫ u in A i, (w i u : ℝ) *
      (η : DifferentialForm (Euclid N) (k + 1)) (G i u)
        (fun a => fderiv ℝ (G i) u (EuclideanSpace.single a 1)) := by
    funext i
    rw [hSrep i ω]
    exact ((hact i).2.2.2.2 ω η hη).symm
  have hCsum : HasSum (fun i => S i ω) (C ω) := by
    rw [hSη, hCω]
    exact hrep η
  rw [hCsum.unique (hChsum ω)]
  exact hR ω

/-- **Integrality of Lipschitz push-forwards and of cylinders** (Simon Ch. 6, 2.25, 2.29 and
3.3–3.9; Part B of the Lipschitz push-forward step of the deformation theorem 6.5.1).  Assume
(VO), (MR), (IMC) and (IMS), and let `X ∈ 𝒟ₖ₊₁(ℝᴺ)` be integer multiplicity with compact
support and `M(X) < ∞`.
(I) If `Fⱼ → F` uniformly, the `Fⱼ` smooth and all maps `Λ`-Lipschitz, then a weak limit
`S(ω) = limⱼ X(Fⱼ^#ω)` is integer multiplicity: `X(η) = Σᵢ ∫_{Aᵢ} wᵢ η(Gᵢ)(DGᵢ e)` over
integer-weighted Lipschitz pieces, `X(Fⱼ^#ω) → Σᵢ ∫_{Aᵢ} wᵢ ω(F ∘ Gᵢ)(D(F ∘ Gᵢ) e)` by weak
continuity of pull-backs, and the limit is a series of integer multiplicity currents
`(F ∘ Gᵢ)_#(wᵢ [[Aᵢ]])` (`cmcdt_lpi_pushforward_im`).
(II) The cylinder `C = [[0, 1]] × X`, `C(ω) = X(∫₀¹ ω(t, ·)(e₀, ·) dt)`, is integer multiplicity,
by the product pieces `(t, u) ↦ (t, Gᵢ(u))` and Fubini (`cmcdt_lpi_cylinder_im`).
Both use the covector bounds `|A^#β| ≤ ‖A‖ᵏ|β|`, `|ι_vβ| ≤ |v||β|` and `|α(τ)| ≤ |α|` for
orthonormal `τ` (`cmcdt_lp_covector_norm_bounds`). -/
theorem Submission.cmcdt_lp_integer_multiplicity : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ((∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)), ∑' i, (W i).mass < ∞ → ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), HasSum (fun i => W i ω) (S ω)) ∧ S.mass ≤ ∑' i, (W i).mass ∧ S.support ⊆ closure (⋃ i, (W i).support) ∧ ((∀ i, IsIntegerMultiplicity (W i)) → IsIntegerMultiplicity S)) → (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (S : GeometricCurrentOn (univ : Set (Euclid N')) (k + 1)), LipschitzWith Λ F → IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) (k + 1), ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) (k + 1)) x = ((ω : DifferentialForm (Euclid N') (k + 1)) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (S ω))) → IsIntegerMultiplicity S) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (C : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1 + 1)), IsIntegerMultiplicity X → IsCompact X.support → X.mass < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1 + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η : DifferentialForm (Euclid N) (k + 1)) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1 + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ C ω = X η) → IsIntegerMultiplicity C := by
  intro hVO hMR hIMC hIMS
  -- (I) the limit of the smooth push-forwards `(Fⱼ)_# X`; (II) the cylinder `[[0, 1]] × X`
  exact ⟨Submission.cmcdt_lpi_pushforward_im Submission.cmcdt_lp_covector_norm_bounds hVO hMR
      hIMC hIMS,
    Submission.cmcdt_lpi_cylinder_im Submission.cmcdt_lp_covector_norm_bounds hVO hMR hIMC hIMS⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
