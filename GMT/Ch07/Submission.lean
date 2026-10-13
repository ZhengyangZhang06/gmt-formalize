import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

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

/-- **Constancy on a plane** (Simon Ch. 6, 2.34; the planar step of 7.3.3(1)): let `T ∈ 𝒟ₙ(U)`,
`n ≥ 1`, be integer multiplicity with `∂T = 0`, let `Q` be an `n`-plane, `p ∈ Q`, `B = B_r(p) ⊆ U`
and `spt T ∩ B ⊆ Q`.  If `Θⁿ(μ_T, p) = k`, then `M_W(T) = k Hⁿ(W ∩ Q)` for every open `W ⊆ B`.
Write `T = τ(M, θ, ξ)`.  `T` vanishes on the open zero region, so `Hⁿ((M ∩ B) ∖ Q) = 0`; the
approximate tangent plane of `M` at points of `Q ∩ B` is then `Q`, so `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an
orthonormal basis `τ` of `Q`.  Parametrizing `Q` by the isometry `Φ v = p + L v`, this gives
`T(ω) = ∫ G(v) ⟨ω(Φ v), τ⟩ dv` on `B` with `G` integer valued and locally integrable.  Testing
`∂T = 0` on `d(f βⱼ)` shows `∫ G ∂ⱼa = 0` for smooth `a` with compact support in `B_r(0)`, and
mollification with Lebesgue differentiation gives `G = c ∈ ℤ` a.e.  Then `|⟨α, τ⟩| ≤ |α|` and a
unit covector `β` with `⟨β, τ⟩ = 1` give `M_W(T) = |c| Hⁿ(W ∩ Q)`, and the density at `p` forces
`|c| = k`. -/
theorem Submission.idtp_ccd_planar_support_mass : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (Q : Submodule ℝ (Euclid P)) (p : Euclid P) (r : ℝ) (k : ℕ), 1 ≤ n → IsOpen U → IsIntegerMultiplicity T → BoundaryVanishes T → Module.finrank ℝ Q = n → p ∈ Q → 0 < r → ball p r ⊆ U → T.support ∩ ball p r ⊆ (Q : Set (Euclid P)) → HasMassDensity T p k → ∀ W : Set (Euclid P), IsOpen W → W ⊆ ball p r → T.massOn W = (k : ℝ≥0∞) * μHE[n] (W ∩ (Q : Set (Euclid P))) := by
  intro P n U T Q p r k hn _hU hIM hbd hQ hpQ hr hBU hspt hdens W hW hWB
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨R, hR⟩ := hIM
  -- Step 1 (frame)
  let b : OrthonormalBasis (Fin (m + 1)) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
  let τ : Fin (m + 1) → Euclid P := fun i => (b i : Euclid P)
  have hτ : Orthonormal ℝ τ := b.orthonormal.comp_linearIsometry Q.subtypeₗᵢ
  let L : Euclid (m + 1) →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  have hLe : ∀ i, L (EuclideanSpace.single i 1) = τ i := fun i => by
    simp only [L, τ, LinearIsometry.coe_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, OrthonormalBasis.repr_symm_single,
      Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype]
  have hLQ : ∀ v, L v ∈ Q := fun v => (b.repr.symm v).2
  have hQL : ∀ x ∈ Q, ∃ v, L v = x := fun x hx => ⟨b.repr ⟨x, hx⟩, by
    simp only [L, LinearIsometry.coe_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
      Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype]⟩
  let Φ : Euclid (m + 1) → Euclid P := fun v => p + L v
  have hΦiso : Isometry Φ := fun v w => by
    simp only [Φ, edist_dist, dist_add_left, L.dist_map]
  have hΦrange : range Φ = (Q : Set (Euclid P)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact Q.add_mem hpQ (hLQ v)
    · intro hx
      obtain ⟨v, hv⟩ := hQL (x - p) (Q.sub_mem hx hpQ)
      exact ⟨v, by simp only [Φ, hv, add_sub_cancel]⟩
  have hΦemb : MeasurableEmbedding Φ := hΦiso.isClosedEmbedding.measurableEmbedding
  have hmap : Measure.map Φ volume = μHE[m + 1].restrict (Q : Set (Euclid P)) := by
    rw [← hΦrange, ← hΦiso.map_euclideanHausdorffMeasure,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hΦball : ∀ s, Φ ⁻¹' ball p s = ball 0 s := fun s => by
    ext v
    simp only [Φ, mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
      L.norm_map]
  -- Step 2 (covectors)
  have hcov : ∀ τ' : Fin (m + 1) → Euclid P, Orthonormal ℝ τ' →
      (∃ β : Covector (Euclid P) (m + 1), covectorEuclideanNorm β ≤ 1 ∧ β τ' = 1) ∧
      ∀ α : Covector (Euclid P) (m + 1), |α τ'| ≤ covectorEuclideanNorm α := by
    intro τ' hτ'
    -- (a) `Σ_j α(f ∘ j)² = Σ_j α(f' ∘ j)²` for orthonormal bases `f`, `f'` of `ℝᴾ`
    have hinv : ∀ (α : Covector (Euclid P) (m + 1)) (f f' : OrthonormalBasis (Fin P) ℝ (Euclid P)),
        ∑ j : Fin (m + 1) → Fin P, (α (fun k => f (j k))) ^ 2 =
          ∑ j : Fin (m + 1) → Fin P, (α (fun k => f' (j k))) ^ 2 := by
      intro α f f'
      set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (f' s) (f i) with hc
      have hexp : ∀ j : Fin (m + 1) → Fin P, α (fun k => f (j k)) =
          ∑ a : Fin (m + 1) → Fin P, (∏ k, c (j k) (a k)) * α (fun k => f' (a k)) := by
        intro j
        have hb : (fun k => f (j k)) = fun k => ∑ s, c (j k) s • f' s :=
          funext fun k => (f'.sum_repr' (f (j k))).symm
        rw [hb, α.map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← smul_eq_mul, ← α.map_smul_univ]
      have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
        intro s t
        have h1 : ∑ i, c i s * c i t = inner ℝ (f' s) (f' t) := by
          rw [← f.sum_inner_mul_inner (f' s) (f' t)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hc, real_inner_comm (f' t) (f i)]
        rw [h1]
        exact (orthonormal_iff_ite.mp f'.orthonormal) s t
      have hT : ∀ a a' : Fin (m + 1) → Fin P,
          ∑ j : Fin (m + 1) → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) =
            if a = a' then 1 else 0 := by
        intro a a'
        rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
        simp_rw [hdelta]
        split_ifs with h
        · subst h
          simp
        · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
          exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
      calc ∑ j : Fin (m + 1) → Fin P, (α (fun k => f (j k))) ^ 2
          = ∑ j : Fin (m + 1) → Fin P, ∑ a : Fin (m + 1) → Fin P, ∑ a' : Fin (m + 1) → Fin P,
              (α (fun k => f' (a k)) * α (fun k => f' (a' k))) *
                ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hexp j, sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
            rw [Finset.prod_mul_distrib]
            ring
        _ = ∑ a : Fin (m + 1) → Fin P, ∑ a' : Fin (m + 1) → Fin P,
              (α (fun k => f' (a k)) * α (fun k => f' (a' k))) *
                ∑ j : Fin (m + 1) → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a' _ => ?_
            rw [Finset.mul_sum]
        _ = ∑ a : Fin (m + 1) → Fin P, (α (fun k => f' (a k))) ^ 2 := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp_rw [hT]
            rw [Finset.sum_eq_single a]
            · simp [sq]
            · intro a' _ hne
              simp [Ne.symm hne]
            · intro h
              exact absurd (Finset.mem_univ a) h
    -- (b) in the standard basis `e`: `Σ_j α(e ∘ j)² = (m+1)! ‖α‖_E²`
    have hstd : ∀ α : Covector (Euclid P) (m + 1),
        ∑ j : Fin (m + 1) → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 =
          ((m + 1).factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
      intro α
      unfold covectorEuclideanNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
        Finset.mul_sum]
      have hcard : ∀ x : ℝ, ((m + 1).factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin (m + 1)), x :=
        fun x => by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      simp only [hcard]
      rw [← Finset.sum_product']
      have hzero : ∀ j : Fin (m + 1) → Fin P, ¬ Injective j →
          α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
        α.map_eq_zero_of_not_injective _
          fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
      rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
        by_contra hj
        exact hne (by rw [hzero j hj]; norm_num)]
      symm
      refine Finset.sum_bij (fun ij _ => fun k => ij.1 (ij.2 k)) ?_ ?_ ?_ ?_
      · intro ij hij
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
          and_true] at hij ⊢
        exact hij.injective.comp ij.2.injective
      · intro ij hij ij' hij' hpq
        simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
          and_true] at hij hij'
        have hrange : Set.range ij.1 = Set.range ij'.1 := by
          rw [← EquivLike.range_comp ij.1 ij.2, ← EquivLike.range_comp ij'.1 ij'.2]
          exact congrArg Set.range hpq
        have hI : ij.1 = ij'.1 := (StrictMono.range_inj_of_wellFoundedLT hij hij').mp hrange
        have hσ : ij.2 = ij'.2 := by
          ext k
          have := congr_fun hpq k
          rw [hI] at this
          exact congrArg Fin.val (hij'.injective this)
        exact Prod.ext hI hσ
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
        · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
          exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
        · funext k
          simp
      · intro ij _
        have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (ij.1 (ij.2 k))) =
            Equiv.Perm.sign ij.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (ij.1 k)) :=
          α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (ij.1 k)) ij.2
        dsimp only
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign ij.2) with h | h <;> simp [h]
    -- (c) extend `τ'` to an orthonormal basis `f` of `ℝᴾ`, `f (ι k) = τ' k`
    have hnP : m + 1 ≤ P := by
      simpa [finrank_euclideanSpace_fin] using hτ'.linearIndependent.fintype_card_le_finrank
    let ι : Fin (m + 1) → Fin P := Fin.castLE hnP
    have hι : Injective ι := Fin.castLE_injective hnP
    let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < m + 1 then τ' ⟨i, h⟩ else 0
    let s : Set (Fin P) := {i | (i : ℕ) < m + 1}
    have hvs : Orthonormal ℝ (s.domRestrict v) := by
      let e : s → Fin (m + 1) := fun i => ⟨i.1, i.2⟩
      have he : Injective e := fun a b hab =>
        Subtype.ext (Fin.ext (congrArg (Fin.val : Fin (m + 1) → ℕ) hab))
      have hve : s.domRestrict v = τ' ∘ e := funext fun i => dite_eq_left i.2
      rw [hve]
      exact hτ'.comp e he
    obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
    have hfι : ∀ k, f (ι k) = τ' k := by
      intro k
      rw [hf (ι k) k.2]
      exact dite_eq_left k.2
    have hsqf : ∀ α : Covector (Euclid P) (m + 1),
        ∑ j : Fin (m + 1) → Fin P, (α (fun k => f (j k))) ^ 2 =
          ((m + 1).factorial : ℝ) * covectorEuclideanNorm α ^ 2 := fun α => by
      rw [hinv α f (EuclideanSpace.basisFun (Fin P) ℝ)]
      exact hstd α
    let Ψ : Equiv.Perm (Fin (m + 1)) → (Fin (m + 1) → Fin P) := fun π => ι ∘ π
    have hΨ : Injective Ψ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
    have hfac : (0 : ℝ) < (m + 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hpermsq : ∀ (α : Covector (Euclid P) (m + 1)) (π : Equiv.Perm (Fin (m + 1))),
        α (fun k => f (Ψ π k)) ^ 2 = α τ' ^ 2 := by
      intro α π
      have h1 : (fun k => f (Ψ π k)) = τ' ∘ π := funext fun k => hfι (π k)
      have h2 : α (τ' ∘ π) = Equiv.Perm.sign π • α τ' := α.toAlternatingMap.map_perm τ' π
      rw [h1, h2]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
    refine ⟨?_, fun α => ?_⟩
    · -- the wedge `β(w) = det(⟨τ'ᵢ, w_k⟩)`
      obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) (m + 1), ∀ w : Fin (m + 1) → Euclid P,
          β w = Matrix.det (Matrix.of fun i k => inner ℝ (τ' i) (w k)) := by
        let Lm : Euclid P →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
          LinearMap.pi fun i => (innerSL ℝ (τ' i) : Euclid P →L[ℝ] ℝ).toLinearMap
        let g : Euclid P [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap Lm
        have hg : ∀ w, g w = Matrix.det (Matrix.of fun i k => inner ℝ (τ' i) (w k)) := by
          intro w
          rw [← Matrix.det_transpose]
          show Matrix.det (Matrix.of fun a b => Lm (w a) b) = _
          congr 1
        have hcont : Continuous fun w : Fin (m + 1) → Euclid P =>
            Matrix.det (Matrix.of fun i k => inner ℝ (τ' i) (w k)) := by
          apply Continuous.matrix_det
          apply continuous_matrix
          intro i k
          exact Continuous.inner (f := fun _ => τ' i) (g := fun w : Fin (m + 1) → Euclid P => w k)
            continuous_const (continuous_apply k)
        refine ⟨{ g with cont := ?_ }, hg⟩
        have : (g : (Fin (m + 1) → Euclid P) → ℝ) =
            fun w => Matrix.det (Matrix.of fun i k => inner ℝ (τ' i) (w k)) := funext hg
        simpa [this] using hcont
      have hβτ : β τ' = 1 := by
        have hone : (Matrix.of fun i k => inner ℝ (τ' i) (τ' k) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 1 := by
          ext i k
          rw [Matrix.of_apply, Matrix.one_apply]
          exact orthonormal_iff_ite.mp hτ' i k
        rw [hβ, hone, Matrix.det_one]
      have hzero : ∀ j : Fin (m + 1) → Fin P, j ∉ Finset.univ.image Ψ →
          β (fun k => f (j k)) ^ 2 = 0 := by
        intro j hj
        have hj' : ∀ π, Ψ π ≠ j := fun π hπ => hj (Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ⟩)
        rw [sq_eq_zero_iff]
        by_cases hr : ∀ k, j k ∈ range ι
        · choose ρ hρ using hr
          have hρ' : ¬ Injective ρ := fun hinj =>
            hj' (Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hinj)) (funext hρ)
          refine β.map_eq_zero_of_not_injective _ fun hinj => hρ' fun a b hab => hinj ?_
          exact congrArg f ((hρ a).symm.trans ((congrArg ι hab).trans (hρ b)))
        · obtain ⟨k₀, hk₀⟩ := not_forall.mp hr
          rw [hβ]
          refine Matrix.det_eq_zero_of_column_eq_zero k₀ fun i => ?_
          rw [Matrix.of_apply, ← hfι i, f.inner_eq_ite, ite_eq_right fun h => hk₀ ⟨i, h⟩]
      have hsum : ∑ j : Fin (m + 1) → Fin P, β (fun k => f (j k)) ^ 2 = (m + 1).factorial := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Ψ)) fun j _ hj => hzero j hj,
          Finset.sum_image fun π _ π' _ h => hΨ h]
        simp only [hpermsq, hβτ, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul, one_pow, mul_one]
      have hsq := hsqf β
      rw [hsum] at hsq
      refine ⟨β, le_of_eq ((pow_eq_one_iff_of_nonneg (covectorEuclideanNorm_nonneg β)
        two_ne_zero).mp ?_), hβτ⟩
      exact mul_left_cancel₀ hfac.ne' (by rw [← hsq, mul_one])
    · have hle : ((m + 1).factorial : ℝ) * α τ' ^ 2 ≤
          ∑ j : Fin (m + 1) → Fin P, α (fun k => f (j k)) ^ 2 :=
        calc ((m + 1).factorial : ℝ) * α τ' ^ 2
            = ∑ j ∈ Finset.univ.image Ψ, α (fun k => f (j k)) ^ 2 := by
              rw [Finset.sum_image fun π _ π' _ h => hΨ h]
              simp only [hpermsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
                Fintype.card_fin, nsmul_eq_mul]
          _ ≤ ∑ j : Fin (m + 1) → Fin P, α (fun k => f (j k)) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
      rw [hsqf α] at hle
      exact abs_le_of_sq_le_sq (le_of_mul_le_mul_left hle hfac) (covectorEuclideanNorm_nonneg α)
  obtain ⟨β, hβE, hβτ⟩ := (hcov τ hτ).1
  -- Step 3 (support null)
  have hnull : μHE[m + 1] ((R.carrier ∩ ball p r) \ (Q : Set (Euclid P))) = 0 := by
    -- the zero region `Z = ⋃₀ 𝒲` is the union of a countable subfamily `𝒮 ⊆ 𝒲`
    obtain ⟨𝒮, h𝒮c, h𝒮W, h𝒮⟩ := TopologicalSpace.isOpen_sUnion_countable
      {W : Set (Euclid P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
      fun W hW => hW.1
    -- a point of `(M ∩ B) ∖ Q` is outside `spt T`, hence in `Z`
    have hsub : (R.carrier ∩ ball p r) \ (Q : Set (Euclid P)) ⊆ ⋃ W ∈ 𝒮, R.carrier ∩ W := by
      rintro x ⟨⟨hxM, hxB⟩, hxQ⟩
      have hxZ : x ∈ ⋃₀ 𝒮 := by
        rw [h𝒮]
        by_contra hxZ
        exact hxQ (hspt ⟨⟨hBU hxB, hxZ⟩, hxB⟩)
      obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxZ
      exact mem_biUnion hW ⟨hxM, hxW⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff h𝒮c).mpr fun W hW => ?_)
    obtain ⟨hWo, hWc, hWU, hTW⟩ := h𝒮W hW
    -- `Λⁿ` is finite-dimensional: `α ↦ (α(e ∘ I))_I` is injective
    obtain ⟨N, ⟨bc⟩⟩ : ∃ N, Nonempty (Module.Basis (Fin N) ℝ (Covector (Euclid P) (m + 1))) := by
      have hfin : FiniteDimensional ℝ (Covector (Euclid P) (m + 1)) := by
        let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
        let Ψ : Covector (Euclid P) (m + 1) →ₗ[ℝ] ((Fin (m + 1) → Fin P) → ℝ) :=
          { toFun := fun α I => α fun i => e (I i)
            map_add' := fun α β => rfl
            map_smul' := fun c α => rfl }
        exact FiniteDimensional.of_injective Ψ fun α β h =>
          ContinuousAlternatingMap.toAlternatingMap_injective
            (e.ext_alternating fun v _ => congr_fun h v)
      exact ⟨_, ⟨Module.finBasis ℝ _⟩⟩
    -- `Hⁿ`-a.e. on `M`: `|ξ(α)| ≤ ‖α‖_E` and `ξ ≠ 0`
    have hξ : ∀ᵐ x ∂(μHE[m + 1].restrict R.carrier),
        (∀ α, |R.orient x α| ≤ covectorEuclideanNorm α) ∧ R.orient x ≠ 0 := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q', -, τ', hτ', -, hs⟩ := hx
      obtain ⟨⟨β', -, hβ'⟩, hle⟩ := hcov τ' hτ'
      rcases hs with hs | hs
      · refine ⟨fun α => by rw [hs]; exact hle α, fun h0 => ?_⟩
        have h1 := hs β'
        rw [h0, hβ'] at h1
        exact zero_ne_one h1
      · refine ⟨fun α => by rw [hs, abs_neg]; exact hle α, fun h0 => ?_⟩
        have h1 := hs β'
        rw [h0, hβ'] at h1
        norm_num at h1
    -- for each basis covector `α`: `θ ξ(α) = 0` a.e. on `M ∩ W` (fundamental lemma on `W`)
    have hle : μHE[m + 1].restrict (R.carrier ∩ W) ≤ μHE[m + 1].restrict (R.carrier ∩ closure W) :=
      Measure.restrict_mono (inter_subset_inter_right _ subset_closure) le_rfl
    have h0 : ∀ᵐ x ∂(μHE[m + 1].restrict (R.carrier ∩ W)), ∀ k, R.orient x (bc k) = 0 := by
      refine ae_all_iff.mpr fun k => ?_
      set α := bc k
      -- `f = θ ξ(α)` is integrable for `ν = Hⁿ⌞(M ∩ closure W)`
      have hf : Integrable (fun x => (R.mult x : ℝ) * R.orient x α)
          (μHE[m + 1].restrict (R.carrier ∩ closure W)) := by
        have hμ : μHE[m + 1].restrict (R.carrier ∩ closure W) ≤ μHE[m + 1].restrict R.carrier :=
          Measure.restrict_mono inter_subset_left le_rfl
        have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
        have hmaj : Integrable (fun x => covectorEuclideanNorm α * (R.mult x : ℝ))
            (μHE[m + 1].restrict (R.carrier ∩ closure W)) :=
          (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
            (R.locallyIntegrable_mult _ hWc hWU)).const_mul _
        refine hmaj.mono' ((measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul
          ((ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
            (R.aestronglyMeasurable_orient.mono_measure hμ))) ?_
        filter_upwards [ae_mono hμ hξ] with x hx
        rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_comm]
        exact mul_le_mul_of_nonneg_right (hx.1 α) (Nat.cast_nonneg _)
      have hae : ∀ᵐ x ∂(μHE[m + 1].restrict (R.carrier ∩ closure W)), x ∈ W →
          (R.mult x : ℝ) * R.orient x α = 0 := by
        refine hWo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
          (hf.locallyIntegrable.locallyIntegrableOn W) fun g hg hgc hgW => ?_
        have hωW : tsupport (fun x => g x • α) ⊆ W := (tsupport_smul_subset_left g _).trans hgW
        have hω : (fun x => g x • α) ∈ TestFormOn U (m + 1) :=
          ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, hωW.trans (subset_closure.trans hWU)⟩
        calc ∫ x, g x • ((R.mult x : ℝ) * R.orient x α) ∂(μHE[m + 1].restrict (R.carrier ∩ closure W))
            = ∫ x in R.carrier ∩ closure W, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[m + 1] := by
              refine integral_congr_ae (Eventually.of_forall fun x => ?_)
              show g x • ((R.mult x : ℝ) * R.orient x α) = (R.mult x : ℝ) * R.orient x (g x • α)
              rw [map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]
          _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[m + 1] := by
              refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
                inter_subset_left fun x hx => ?_).symm
              rw [image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, subset_closure (hgW h)⟩,
                zero_smul, map_zero, mul_zero]
          _ = T ⟨_, hω⟩ := (hR ⟨_, hω⟩).symm
          _ = 0 := hTW ⟨_, hω⟩ hωW
      filter_upwards [ae_mono hle hae,
        ae_restrict_mem (R.measurableSet_carrier.inter hWo.measurableSet)] with x hx hxMW
      exact (mul_eq_zero.mp (hx hxMW.2)).resolve_left (Nat.cast_ne_zero.mpr (R.mult_pos x hxMW.1).ne')
    -- `ξ ≠ 0` a.e. on `M`, so `Hⁿ(M ∩ W) = 0`
    have h2 : ∀ᵐ x ∂(μHE[m + 1].restrict (R.carrier ∩ W)), False := by
      filter_upwards [h0, ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hξ] with x hx hne
      exact hne.2 (ContinuousLinearMap.coe_injective (bc.ext fun k => hx k))
    exact Measure.restrict_eq_zero.mp (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp h2))
  -- Step 4 (approximate tangent planes)
  have htan : ∀ x ∈ ball p r, x ∈ Q → ∀ Q' : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt (m + 1) R.carrier x Q' → Q' = Q := by
    intro x hxB hxQ Q' hQ'
    refine Submodule.eq_of_le_of_finrank_eq (fun y hyQ' => ?_) (hQ'.1.trans hQ.symm)
    by_contra hyQ
    -- `δ = dist(y, Q) > 0`; `ball x r₀ ⊆ B`
    have hδ : 0 < infDist y (Q : Set (Euclid P)) :=
      (Q.closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, Q.zero_mem⟩).1 hyQ
    set δ := infDist y (Q : Set (Euclid P)) with hδdef
    obtain ⟨r₀, hr₀, hr₀B⟩ := Metric.isOpen_iff.1 isOpen_ball x hxB
    have hR₀ : 0 < ‖y‖ + δ := by positivity
    -- the test function `f = max(0, δ/2 - dist(·, y))`, supported in `B̄(y, δ/2)`
    have hf0 : ∀ w ∉ closedBall y (δ / 2), max 0 (δ / 2 - dist w y) = 0 := fun w hw =>
      max_eq_left (by rw [mem_closedBall, not_le] at hw; linarith)
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      ⟨⟨fun w => max 0 (δ / 2 - dist w y), by fun_prop⟩,
        HasCompactSupport.intro (isCompact_closedBall y (δ / 2)) hf0⟩
    -- for `0 < λ < r₀ / (‖y‖ + δ)` the blow-up integral vanishes
    have hzero : ∀ lam ∈ Ioo 0 (r₀ / (‖y‖ + δ)),
        ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x lam '' R.carrier, f w ∂μHE[m + 1] = 0 := by
      rintro lam ⟨hlam, hlamR⟩
      have hsub : closedBall y (δ / 2) ∩ Poincare.SimonGMT.Chapter03.blowUpMap x lam '' R.carrier ⊆
          Poincare.SimonGMT.Chapter03.blowUpMap x lam '' ((R.carrier ∩ ball p r) \ (Q : Set (Euclid P))) := by
        rintro _ ⟨hw, a, ha, rfl⟩
        have hwa : a - x = lam • Poincare.SimonGMT.Chapter03.blowUpMap x lam a :=
          (smul_inv_smul₀ hlam.ne' (a - x)).symm
        rw [mem_closedBall] at hw
        have hwR : ‖Poincare.SimonGMT.Chapter03.blowUpMap x lam a‖ < ‖y‖ + δ := by
          have := norm_sub_norm_le (Poincare.SimonGMT.Chapter03.blowUpMap x lam a) y
          rw [← dist_eq_norm] at this
          linarith
        refine ⟨a, ⟨⟨ha, hr₀B ?_⟩, fun haQ => ?_⟩, rfl⟩
        · rw [mem_ball, dist_eq_norm, hwa, norm_smul_of_nonneg hlam.le]
          calc lam * ‖Poincare.SimonGMT.Chapter03.blowUpMap x lam a‖ < lam * (‖y‖ + δ) :=
                mul_lt_mul_of_pos_left hwR hlam
            _ < r₀ := (lt_div_iff₀ hR₀).1 hlamR
        · have hwQ : Poincare.SimonGMT.Chapter03.blowUpMap x lam a ∈ Q :=
            Q.smul_mem _ (Q.sub_mem haQ hxQ)
          have := infDist_le_dist_of_mem (x := y) hwQ
          rw [dist_comm] at this
          linarith
      have hlip : LipschitzWith ‖lam⁻¹‖₊ (Poincare.SimonGMT.Chapter03.blowUpMap x lam) :=
        LipschitzWith.of_dist_le_mul fun a b => by
          show dist (lam⁻¹ • (a - x)) (lam⁻¹ • (b - x)) ≤ _
          rw [dist_smul₀, dist_sub_right, coe_nnnorm]
      have hnull' : μHE[m + 1] (Poincare.SimonGMT.Chapter03.blowUpMap x lam ''
          ((R.carrier ∩ ball p r) \ (Q : Set (Euclid P)))) = 0 := by
        have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
          (A := (R.carrier ∩ ball p r) \ (Q : Set (Euclid P))) (m + 1) hlip.lipschitzOnWith
        rw [hnull, mul_zero] at h
        exact le_antisymm h zero_le
      have hball : ((μHE[m + 1] : Measure (Euclid P)).restrict
          (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' R.carrier)) (closedBall y (δ / 2)) = 0 := by
        rw [Measure.restrict_apply measurableSet_closedBall]
        exact measure_mono_null hsub hnull'
      refine integral_eq_zero_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hball] with w hw
      exact hf0 w hw
    have hQ0 : ∫ w in (Q' : Set (Euclid P)), f w ∂μHE[m + 1] = 0 :=
      tendsto_nhds_unique (hQ'.2 f) (tendsto_const_nhds.congr' (by
        filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR₀)] with lam hlam
        exact (hzero lam hlam).symm))
    -- but `∫_{Q'} f dHⁿ > 0`: `y ∈ Q' = spt Hⁿ⌞Q'` and `f > 0` near `y`
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ'.1
    have hy : y ∈ ((μHE[m + 1] : Measure (Euclid P)).restrict (Q' : Set (Euclid P))).support := by
      rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ'.1]
      exact hyQ'
    have hpos : 0 < ∫ w in (Q' : Set (Euclid P)), f w ∂μHE[m + 1] := by
      have hnn : 0 ≤ ⇑f := fun w => show (0 : ℝ) ≤ max 0 (δ / 2 - dist w y) from le_max_left _ _
      rw [integral_pos_iff_support_of_nonneg hnn
        ((map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport)]
      refine (Measure.mem_support_iff_forall y).1 hy _
        (mem_of_superset (ball_mem_nhds y (half_pos hδ)) fun w hw => ?_)
      rw [mem_ball] at hw
      exact (lt_max_of_lt_right (show (0 : ℝ) < δ / 2 - dist w y by linarith)).ne'
    exact hpos.ne' hQ0
  -- Step 5 (orientation sign)
  have hsign : ∀ ξ : MultiVector P (m + 1), IsUnitOrientationOf ξ Q →
      (∀ α, ξ α = ξ β * α τ) ∧ (ξ β = 1 ∨ ξ β = -1) := by
    rintro ξ ⟨τ', hτ', hspan, hs⟩
    -- `α(τ') = d α(τ)` for all `α`, with `d = ±1` (the frames `τ`, `τ'` of `Q` are orthonormal)
    obtain ⟨d, hd, hkey⟩ : ∃ d : ℝ, (d = 1 ∨ d = -1) ∧
        ∀ α : Covector (Euclid P) (m + 1), α τ' = d * α τ := by
      have hmem : ∀ i, τ' i ∈ Q := fun i => hspan ▸ Submodule.subset_span (mem_range_self i)
      let u : Fin (m + 1) → Q := fun i => ⟨τ' i, hmem i⟩
      have hu : Orthonormal ℝ u := (Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)).1 hτ'
      have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
        rintro ⟨y, hy⟩ -
        rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hy
        obtain ⟨c, hc⟩ := hy
        rw [Submodule.mem_span_range_iff_exists_fun]
        exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
      let b' := OrthonormalBasis.mk hu huspan
      refine ⟨b.toBasis.det b', b.det_to_matrix_orthonormalBasis_real b', fun α => ?_⟩
      let F : Q [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
      have h := congrArg (fun g : Q [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ => g b') (F.eq_smul_basis_det b.toBasis)
      simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
      have h1 : F b' = α τ' := by
        show α (fun i => ((b' i : Q) : Euclid P)) = α τ'
        congr 1
        funext i
        rw [OrthonormalBasis.coe_mk]
      rw [mul_comm, ← h1]
      exact h
    obtain ⟨e, he, hξe⟩ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ α, ξ α = e * α τ' := by
      rcases hs with h | h
      · exact ⟨1, Or.inl rfl, fun α => (h α).trans (one_mul _).symm⟩
      · exact ⟨-1, Or.inr rfl, fun α => (h α).trans (neg_one_mul _).symm⟩
    have hξα : ∀ α, ξ α = (e * d) * α τ := fun α => by
      rw [hξe, hkey, mul_assoc]
    have hξβ : ξ β = e * d := by rw [hξα, hβτ, mul_one]
    refine ⟨fun α => by rw [hξβ, hξα], ?_⟩
    rw [hξβ]
    rcases he with rfl | rfl <;> rcases hd with rfl | rfl
    · exact Or.inl (mul_one 1)
    · exact Or.inr (one_mul (-1))
    · exact Or.inr (mul_one (-1))
    · exact Or.inl (by rw [neg_one_mul, neg_neg])
  have hξτ : ∀ᵐ x ∂μHE[m + 1], x ∈ R.carrier → x ∈ ball p r → x ∈ Q →
      (∀ α, R.orient x α = R.orient x β * α τ) ∧ (R.orient x β = 1 ∨ R.orient x β = -1) := by
    filter_upwards [(ae_restrict_iff' R.measurableSet_carrier).1 R.orients] with x hx hxM hxB hxQ
    obtain ⟨Q', hQ', hξ⟩ := hx hxM
    rw [htan x hxB hxQ Q' hQ'] at hξ
    exact hsign _ hξ
  -- Step 6 (representation): `g = 1_M θ ξ(β)` and `T ω = ∫ g(Φ v) ω(Φ v)(τ) dv` if `spt ω ⊆ B`
  set g : Euclid P → ℝ := R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) with hgdef
  have hS : MeasurableSet (R.carrier ∩ ball p r ∩ (Q : Set (Euclid P))) :=
    (R.measurableSet_carrier.inter measurableSet_ball).inter
      Q.closed_of_finiteDimensional.measurableSet
  have hrep : ∀ ω : TestFormOn U (m + 1),
      tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball p r →
        T ω = ∫ v, g (Φ v) * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ v) τ := by
    intro ω hω
    have hω0 : ∀ x, x ∉ ball p r → (ω : DifferentialForm (Euclid P) (m + 1)) x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport fun h => hx (hω h)
    have e1 : ∫ x in R.carrier, (R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
        ∫ x in R.carrier ∩ ball p r ∩ (Q : Set (Euclid P)), (R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] := by
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero R.measurableSet_carrier.nullMeasurableSet
        (inter_subset_left.trans inter_subset_left) ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hxN hx
      by_cases hxB : x ∈ ball p r
      · exact absurd ⟨⟨hx.1, hxB⟩, fun hxQ => hx.2 ⟨⟨hx.1, hxB⟩, hxQ⟩⟩ hxN
      · rw [hω0 x hxB, map_zero, mul_zero]
    have e2 : ∫ x in R.carrier ∩ ball p r ∩ (Q : Set (Euclid P)), (R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
        ∫ x in R.carrier ∩ ball p r ∩ (Q : Set (Euclid P)),
          g x * (ω : DifferentialForm (Euclid P) (m + 1)) x τ ∂μHE[m + 1] := by
      refine setIntegral_congr_ae hS ?_
      filter_upwards [hξτ] with x hx hxS
      rw [hgdef, indicator_of_mem hxS.1.1, mul_assoc, ← (hx hxS.1.1 hxS.1.2 hxS.2).1]
    have e3 : ∫ x in (Q : Set (Euclid P)), g x * (ω : DifferentialForm (Euclid P) (m + 1)) x τ
          ∂μHE[m + 1] =
        ∫ x in R.carrier ∩ ball p r ∩ (Q : Set (Euclid P)),
          g x * (ω : DifferentialForm (Euclid P) (m + 1)) x τ ∂μHE[m + 1] := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        Q.closed_of_finiteDimensional.measurableSet inter_subset_right fun x hx => ?_
      by_cases hxM : x ∈ R.carrier
      · have hxB : x ∉ ball p r := fun hxB => hx.2 ⟨⟨hxM, hxB⟩, hx.1⟩
        rw [hω0 x hxB, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero]
      · rw [hgdef, indicator_of_notMem hxM, zero_mul]
    rw [hR ω, IMRep.action, e1, e2, ← e3, ← hmap, hΦemb.integral_map]
  -- Step 7 (`G = g ∘ Φ`): integer values and local integrability on `B(0, r)`
  have hgZ : ∀ᵐ x ∂(μHE[m + 1].restrict (Q : Set (Euclid P))), x ∈ ball p r → ∃ z : ℤ, g x = z := by
    filter_upwards [ae_restrict_of_ae hξτ, ae_restrict_mem Q.closed_of_finiteDimensional.measurableSet]
      with x hx hxQ hxB
    by_cases hxM : x ∈ R.carrier
    · rw [hgdef, indicator_of_mem hxM]
      rcases (hx hxM hxB hxQ).2 with h | h
      · exact ⟨R.mult x, by rw [h, mul_one]; rfl⟩
      · exact ⟨-(R.mult x : ℤ), by rw [h, mul_neg_one]; push_cast; rfl⟩
    · exact ⟨0, by rw [hgdef, indicator_of_notMem hxM]; simp⟩
  have hGZ : ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid (m + 1)) r)), ∃ z : ℤ, g (Φ v) = z := by
    rw [← hmap] at hgZ
    filter_upwards [ae_restrict_of_ae (ae_of_ae_map hΦemb.measurable.aemeasurable hgZ),
      ae_restrict_mem measurableSet_ball] with v hv hvB
    exact hv (by rw [← mem_preimage, hΦball]; exact hvB)
  have hgm : AEStronglyMeasurable g μHE[m + 1] := by
    rw [hgdef, aestronglyMeasurable_indicator_iff R.measurableSet_carrier]
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul
      ((ContinuousLinearMap.apply ℝ ℝ β).continuous.comp_aestronglyMeasurable
        R.aestronglyMeasurable_orient)
  have hGint : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ ball 0 r →
      IntegrableOn (fun v => g (Φ v)) K := by
    intro K hK hKB
    have hKB' : Φ '' K ⊆ ball p r := by
      rintro _ ⟨v, hv, rfl⟩
      rw [← mem_preimage, hΦball]
      exact hKB hv
    have hcK : IsCompact (Φ '' K) := hK.image hΦiso.continuous
    have hmapK : Measure.map Φ (volume.restrict K) = μHE[m + 1].restrict (Φ '' K) := by
      have h1 := hΦemb.restrict_map volume (Φ '' K)
      rw [hΦemb.injective.preimage_image, hmap, Measure.restrict_restrict hcK.measurableSet,
        inter_eq_left.2 (hΦrange ▸ image_subset_range Φ K)] at h1
      exact h1.symm
    show Integrable (g ∘ Φ) (volume.restrict K)
    rw [← hΦemb.integrable_map_iff, hmapK]
    refine Integrable.mono' (g := R.carrier.indicator fun x => (R.mult x : ℝ)) ?_ hgm.restrict ?_
    · rw [integrable_indicator_iff R.measurableSet_carrier, IntegrableOn,
        Measure.restrict_restrict R.measurableSet_carrier]
      exact integrable_toReal_of_lintegral_ne_top
        (measurable_from_nat.comp R.measurable_mult).aemeasurable
        (R.locallyIntegrable_mult _ hcK (hKB'.trans hBU))
    · filter_upwards [ae_restrict_of_ae hξτ, ae_restrict_mem hcK.measurableSet] with x hx hxK
      by_cases hxM : x ∈ R.carrier
      · have hxQ : x ∈ Q := by
          rw [← SetLike.mem_coe, ← hΦrange]
          exact image_subset_range Φ K hxK
        rw [hgdef, indicator_of_mem hxM, indicator_of_mem hxM, Real.norm_eq_abs, abs_mul,
          Nat.abs_cast]
        rcases (hx hxM (hKB' hxK) hxQ).2 with h | h <;> rw [h] <;> simp
      · rw [hgdef, indicator_of_notMem hxM, indicator_of_notMem hxM, norm_zero]
  -- Step 8 (smooth Urysohn): `χ ∈ C^∞_c(V)`, `0 ≤ χ ≤ 1`, `χ = 1` near the compact `K ⊆ V`
  have hury : ∀ K V : Set (Euclid P), IsCompact K → IsOpen V → K ⊆ V →
      ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, ∀ᶠ y in 𝓝 x, χ y = 1 := by
    intro K V hK hV hKV
    obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open hV hKV
    obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := δ / 4) (by positivity)
    -- `F = Σ_{x ∈ t} c_x`, `c_x` the bump at `x` with radii `δ/2 < 3δ/4`
    let c : ∀ x : Euclid P, ContDiffBump x := fun x => ⟨δ / 2, 3 * δ / 4, by positivity, by linarith⟩
    let F : Euclid P → ℝ := fun y => ∑ x ∈ htf.toFinset, c x y
    have hF0 : ∀ y, 0 ≤ F y := fun y => Finset.sum_nonneg fun x _ => (c x).nonneg
    have hF1 : ∀ y ∈ thickening (δ / 4) K, 1 ≤ F y := by
      intro y hy
      obtain ⟨z, hzK, hyz⟩ := mem_thickening_iff.1 hy
      obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcov hzK)
      have h1 : (c x) y = 1 := (c x).one_of_mem_closedBall (by
        rw [mem_closedBall]
        have := dist_triangle y z x
        rw [mem_ball] at hzx
        show dist y x ≤ δ / 2
        linarith)
      rw [← h1]
      exact Finset.single_le_sum (fun x _ => (c x).nonneg) (htf.mem_toFinset.2 hxt)
    have hsuppF : support F ⊆ ⋃ x ∈ t, closedBall x (3 * δ / 4) := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      have h2 := (c x).support_eq ▸ (Function.mem_support.2 hxy)
      exact mem_iUnion₂.2 ⟨x, htf.mem_toFinset.1 hx, ball_subset_closedBall h2⟩
    have hKc : IsCompact (⋃ x ∈ t, closedBall x (3 * δ / 4)) :=
      htf.isCompact_biUnion fun x _ => isCompact_closedBall x _
    refine ⟨fun y => Real.smoothTransition (F y),
      Real.smoothTransition.contDiff.comp (ContDiff.sum fun x _ => (c x).contDiff), ?_, ?_,
      fun y => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, ?_⟩
    · have hsub : tsupport (fun y => Real.smoothTransition (F y)) ⊆
          ⋃ x ∈ t, closedBall x (3 * δ / 4) := by
        refine closure_minimal (fun y hy => hsuppF fun hFy => hy ?_) hKc.isClosed
        show Real.smoothTransition (F y) = 0
        rw [show F y = 0 from hFy, Real.smoothTransition.zero]
      exact hKc.of_isClosed_subset (isClosed_tsupport _) hsub
    · refine (closure_minimal (fun y hy => ?_) hKc.isClosed).trans ?_
      · refine hsuppF fun hFy => hy ?_
        show Real.smoothTransition (F y) = 0
        rw [show F y = 0 from hFy, Real.smoothTransition.zero]
      · refine iUnion₂_subset fun x hx => fun y hy => hδV (mem_thickening_iff.2 ⟨x, htK hx, ?_⟩)
        rw [mem_closedBall] at hy
        linarith
    · intro x hx
      filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening (show (0 : ℝ) < δ / 4 by positivity) K hx)]
        with y hy
      exact Real.smoothTransition.one_of_one_le (hF1 y hy)
  -- Step 9 (weak derivatives): `∫ G ∂ⱼa = 0` for smooth `a` with compact support in `B(0, r)`
  let Ls : Euclid P →L[ℝ] Euclid (m + 1) := ContinuousLinearMap.adjoint L.toContinuousLinearMap
  have hLs : ∀ v, Ls (L v) = v := fun v => by
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact L.inner_map_map v y
  have hweak : ∀ a : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a →
      tsupport a ⊆ ball 0 r → ∀ j : Fin (m + 1),
        ∫ v, g (Φ v) * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro a ha hac has j
    -- the cut-off `χ = 1` near `Φ(spt a)`, `spt χ ⊆ B`
    obtain ⟨χ, hχs, hχc, hχB, -, hχ1⟩ := hury (Φ '' tsupport a) (ball p r)
      (hac.image hΦiso.continuous) isOpen_ball (by
        rintro _ ⟨v, hv, rfl⟩
        rw [← mem_preimage, hΦball]
        exact has hv)
    -- `f = χ · a(L*(· - p))` and the `m`-form `ψ = f βⱼ`, `βⱼ = β(τⱼ, ·)`
    let f : Euclid P → ℝ := fun x => χ x * a (Ls (x - p))
    have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
      hχs.mul (ha.comp (Ls.contDiff.comp (contDiff_id.sub contDiff_const)))
    let βj : Covector (Euclid P) m := β.curryLeft (τ j)
    let ψ : DifferentialForm (Euclid P) m := fun x => f x • βj
    have hψt : tsupport ψ ⊆ tsupport χ :=
      (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_left)
    have hψ : ψ ∈ TestFormOn U m :=
      ⟨⟨hfs.smul contDiff_const, hχc.mono' ((subset_tsupport _).trans hψt)⟩,
        hψt.trans (hχB.trans hBU)⟩
    -- `0 = ∂T(ψ) = T(dψ) = ∫ G(v) dψ(Φ v)(τ) dv`
    have h0 : T (exteriorDerivativeTestOn U m ⟨ψ, hψ⟩) = 0 := by
      have hT' : T.boundary = 0 := hbd
      rw [← GeometricCurrentOn.boundary_apply, hT', GeometricCurrentOn.zero_apply]
    rw [hrep (exteriorDerivativeTestOn U m ⟨ψ, hψ⟩)
      ((tsupport_exteriorDerivative_subset ψ).trans (hψt.trans hχB))] at h0
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun v => ?_)) h0
    show g (Φ v) * fderiv ℝ a v (EuclideanSpace.single j 1) = g (Φ v) * exteriorDerivative ψ (Φ v) τ
    congr 1
    -- `βⱼ(τ without τⱼ) = (-1)ʲ` and `βⱼ(τ without τᵢ) = 0` for `i ≠ j`
    have hβjj : βj (j.removeNth τ) = (-1 : ℝ) ^ (j : ℕ) := by
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      have hc : (Matrix.vecCons (τ j) (j.removeNth τ) : Fin (m + 1) → Euclid P) =
          τ ∘ ⇑(Equiv.symm j.cycleRange) := Fin.cons_removeNth_eq_comp_cycleRange_symm τ j
      rw [hc, show β (τ ∘ ⇑(Equiv.symm j.cycleRange)) =
          Equiv.Perm.sign (Equiv.symm j.cycleRange) • β τ from β.toAlternatingMap.map_perm τ _,
        hβτ, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
      simp [Units.smul_def]
    have hβji : ∀ i, i ≠ j → βj (i.removeNth τ) = 0 := by
      intro i hij
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
      apply β.map_eq_zero_of_eq _ (i := 0) (j := l.succ)
      · simp [Fin.removeNth_apply, hl]
      · exact (Fin.succ_ne_zero l).symm
    -- `dψ(x)(τ) = ∂_{τⱼ} f(x)`
    have hfd : DifferentiableAt ℝ f (Φ v) := (hfs.differentiable (by simp)) (Φ v)
    have hdψ : exteriorDerivative ψ (Φ v) τ = fderiv ℝ f (Φ v) (τ j) := by
      rw [exteriorDerivative_apply (hfd.smul_const βj) τ, Finset.sum_eq_single j]
      · have h1 : (fun y => ψ y (j.removeNth τ)) = fun y => f y * βj (j.removeNth τ) := rfl
        rw [h1, fderiv_mul_const hfd, hβjj, smul_apply, smul_eq_mul, zsmul_eq_mul, ← mul_assoc,
          Int.cast_pow, Int.cast_neg, Int.cast_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
          one_pow, one_mul]
      · intro i _ hij
        have h1 : (fun y => ψ y (i.removeNth τ)) = fun _ => (0 : ℝ) := by
          funext y
          show f y * βj (i.removeNth τ) = 0
          rw [hβji i hij, mul_zero]
        rw [h1, fderiv_const_apply, zero_apply, smul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    -- `f = a ∘ L*(· - p)` near `Φ v`
    have hfev : f =ᶠ[𝓝 (Φ v)] fun x => a (Ls (x - p)) := by
      have hPv : Ls (Φ v - p) = v := by rw [add_sub_cancel_left, hLs]
      by_cases hv : v ∈ tsupport a
      · filter_upwards [hχ1 (Φ v) ⟨v, hv, rfl⟩] with x hx
        show χ x * a (Ls (x - p)) = a (Ls (x - p))
        rw [hx, one_mul]
      · have hopen : IsOpen {x : Euclid P | Ls (x - p) ∉ tsupport a} :=
          (isClosed_tsupport a).isOpen_compl.preimage
            (Ls.continuous.comp (continuous_id.sub continuous_const))
        filter_upwards [hopen.mem_nhds (show Ls (Φ v - p) ∉ tsupport a by rw [hPv]; exact hv)]
          with x hx
        show χ x * a (Ls (x - p)) = a (Ls (x - p))
        rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hchain : fderiv ℝ (fun x => a (Ls (x - p))) (Φ v) =
        (fderiv ℝ a v).comp Ls := by
      have hPv : Ls (Φ v - p) = v := by rw [add_sub_cancel_left, hLs]
      have h1 : HasFDerivAt (fun x => Ls (x - p)) Ls (Φ v) :=
        (Ls.hasFDerivAt.sub_const (Ls p)).congr_of_eventuallyEq
          (Eventually.of_forall fun x => map_sub Ls x p)
      have h2 : HasFDerivAt a (fderiv ℝ a v) (Ls (Φ v - p)) := by
        rw [hPv]
        exact ((ha.differentiable (by simp)) v).hasFDerivAt
      exact (HasFDerivAt.comp (f := fun x => Ls (x - p)) (g := a) (Φ v) h2 h1).fderiv
    rw [hdψ, hfev.fderiv_eq, hchain, ContinuousLinearMap.comp_apply, ← hLe, hLs]
  -- Step 10 (constancy): `G = c` a.e. on `B(0, r)` for an integer `c`
  have hconstancy : ∀ G : Euclid (m + 1) → ℝ,
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ ball 0 r → IntegrableOn G K) →
      (∀ a : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a →
        tsupport a ⊆ ball 0 r → ∀ j : Fin (m + 1),
          ∫ v, G v * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0) →
      ∃ c : ℝ, ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid (m + 1)) r)), G v = c := by
    intro G hGi hw
    -- `|B̄(x, s)| = sⁿ V`, `V = |B(0, 1)| > 0`
    obtain ⟨V, hV, hvol⟩ : ∃ V : ℝ, 0 < V ∧ ∀ (x : Euclid (m + 1)) (s : ℝ), 0 ≤ s →
        volume.real (closedBall x s) = s ^ (m + 1) * V :=
      ⟨volume.real (ball (0 : Euclid (m + 1)) 1),
        ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclid (m + 1)) one_pos).ne'
        measure_ball_lt_top.ne, fun x s hs => by
          rw [Measure.addHaar_real_closedBall volume x hs, finrank_euclideanSpace_fin]⟩
    -- Step 1: `G` is a.e. constant on each `B(0, ρ)`, `ρ < r`
    have hloc : ∀ ρ, 0 < ρ → ρ < r →
        ∃ c : ℝ, ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid (m + 1)) ρ)), G v = c := by
      intro ρ hρ hρr
      obtain ⟨δ, hδ, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ ρ + δ < r := ⟨(r - ρ) / 2, by linarith, by linarith⟩
      -- an integrable `F` with `F = G` on `B̄(0, ρ + δ)`
      obtain ⟨F, hFG, hF⟩ : ∃ F : Euclid (m + 1) → ℝ,
          (∀ t ∈ closedBall (0 : Euclid (m + 1)) (ρ + δ), F t = G t) ∧ Integrable F :=
        ⟨_, fun t ht => indicator_of_mem ht G,
          (hGi _ (isCompact_closedBall _ _) (closedBall_subset_ball hδr)).integrable_indicator
            measurableSet_closedBall⟩
      have hFl : LocallyIntegrable F := hF.locallyIntegrable
      -- radii `ε k ↓ 0`, `ε k ≤ δ`
      obtain ⟨ε, hε, hεδ, hεt⟩ : ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ (∀ k, ε k ≤ δ) ∧
          Tendsto ε atTop (𝓝[>] 0) := by
        refine ⟨fun k => δ / (k + 1), fun k => div_pos hδ (Nat.cast_add_one_pos k), fun k =>
          div_le_self hδ.le (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith),
          tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k =>
            div_pos hδ (Nat.cast_add_one_pos k)⟩⟩
        simpa only [mul_one_div, mul_zero] using
          (tendsto_const_nhds (x := δ)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      -- normalized mollifiers `φ k`, supported in `B̄(0, ε k)`, `φ k ≤ 2ⁿ / |B̄(0, ε k)|`
      obtain ⟨φ, hφs, hφc, hφsupp, hφ0, hφ1, hφb⟩ : ∃ φ : ℕ → Euclid (m + 1) → ℝ,
          (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) ∧ (∀ k, HasCompactSupport (φ k)) ∧
          (∀ k, tsupport (φ k) ⊆ closedBall 0 (ε k)) ∧ (∀ k z, 0 ≤ φ k z) ∧
          (∀ k, ∫ z, φ k z = 1) ∧ (∀ k z, φ k z ≤ 2 ^ (m + 1) / (ε k ^ (m + 1) * V)) := by
        let b : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
          ⟨ε k / 2, ε k, half_pos (hε k), half_lt_self (hε k)⟩
        have hIge : ∀ k, (ε k / 2) ^ (m + 1) * V ≤ ∫ x, b k x := by
          intro k
          rw [← hvol 0 _ (half_pos (hε k)).le, ← integral_indicator_one measurableSet_closedBall]
          refine integral_mono ((integrable_indicator_iff measurableSet_closedBall).2
            (integrableOn_const measure_closedBall_lt_top.ne))
            ((b k).continuous.integrable_of_hasCompactSupport (b k).hasCompactSupport) fun x => ?_
          by_cases hx : x ∈ closedBall (0 : Euclid (m + 1)) (ε k / 2)
          · rw [indicator_of_mem hx]
            exact ((b k).one_of_mem_closedBall hx).ge
          · rw [indicator_of_notMem hx]
            exact (b k).nonneg
        have hIpos : ∀ k, 0 < ∫ x, b k x := fun k =>
          (mul_pos (pow_pos (half_pos (hε k)) _) hV).trans_le (hIge k)
        refine ⟨fun k x => (∫ x, b k x)⁻¹ * b k x, fun k => contDiff_const.mul (b k).contDiff,
          fun k => (b k).hasCompactSupport.mul_left, fun k => ?_, fun k z =>
            mul_nonneg (inv_nonneg.2 (hIpos k).le) (b k).nonneg, fun k => ?_, fun k z => ?_⟩
        · exact (tsupport_mul_subset_right).trans (b k).tsupport_eq.subset
        · rw [integral_const_mul, inv_mul_cancel₀ (hIpos k).ne']
        · calc (∫ x, b k x)⁻¹ * b k z ≤ (∫ x, b k x)⁻¹ * 1 :=
                mul_le_mul_of_nonneg_left (b k).le_one (inv_nonneg.2 (hIpos k).le)
            _ ≤ ((ε k / 2) ^ (m + 1) * V)⁻¹ := by
                rw [mul_one]
                exact inv_anti₀ (mul_pos (pow_pos (half_pos (hε k)) _) hV) (hIge k)
            _ = 2 ^ (m + 1) / (ε k ^ (m + 1) * V) := by
                rw [div_pow, div_mul_eq_mul_div, inv_div]
      have hφ1' : ∀ k, ContDiff ℝ 1 (φ k) := fun k => (hφs k).of_le (by exact_mod_cast le_top)
      -- the derivative of `F ⋆ φ k` vanishes on `B(0, ρ)`: the weak equation with `a = φ k (x - ·)`
      have hd : ∀ k, ∀ x ∈ ball (0 : Euclid (m + 1)) ρ,
          fderiv ℝ (convolution F (φ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x = 0 := by
        intro k x hx
        have hasupp : tsupport (fun t => φ k (x - t)) ⊆ ball 0 (ρ + δ) := by
          intro t ht
          have h1 : ‖x - t‖ ≤ ε k := mem_closedBall_zero_iff.1 (hφsupp k
            (tsupport_comp_subset_preimage (φ k) (continuous_const.sub continuous_id) ht))
          rw [mem_ball_zero_iff] at hx ⊢
          have h2 := norm_sub_le x (x - t)
          rw [sub_sub_cancel] at h2
          linarith [hεδ k]
        have hda : ∀ t, fderiv ℝ (fun t => φ k (x - t)) t = -fderiv ℝ (φ k) (x - t) := fun t => by
          have h := (HasFDerivAt.comp (f := fun t => x - t) (g := φ k) t
            (((hφ1' k).differentiable one_ne_zero (x - t)).hasFDerivAt)
            ((hasFDerivAt_id t).const_sub x)).fderiv
          rw [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] at h
          exact h
        rw [((hφc k).hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hFl
          (hφ1' k) x).fderiv]
        apply ContinuousLinearMap.coe_injective
        refine (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis.ext fun j => ?_
        rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
          convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) hFl
            ((hφc k).fderiv ℝ) ((hφ1' k).continuous_fderiv one_ne_zero),
          zero_apply, convolution_def, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          ← neg_eq_zero, ← integral_neg, ← hw _ ((hφs k).comp (contDiff_const.sub contDiff_id))
            ((hφc k).comp_homeomorph (Homeomorph.subLeft x))
            (hasupp.trans (ball_subset_ball hδr.le)) j]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show -((ContinuousLinearMap.lsmul ℝ ℝ) (F t)) (fderiv ℝ (φ k) (x - t)
          (EuclideanSpace.single j 1)) = G t * fderiv ℝ (fun t => φ k (x - t)) t
            (EuclideanSpace.single j 1)
        rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hda, neg_apply, mul_neg]
        by_cases ht : t ∈ closedBall (0 : Euclid (m + 1)) (ρ + δ)
        · rw [hFG t ht]
        · have hta : t ∉ tsupport (fun t => φ k (x - t)) :=
            fun h => ht (ball_subset_closedBall (hasupp h))
          have h0 := fderiv_of_notMem_tsupport ℝ hta
          rw [hda, neg_eq_zero] at h0
          rw [h0, zero_apply, mul_zero, mul_zero]
      -- hence `F ⋆ φ k` is constant on `B(0, ρ)`
      have hconst : ∀ k, ∀ x ∈ ball (0 : Euclid (m + 1)) ρ,
          convolution F (φ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x =
            convolution F (φ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 := fun k x hx =>
        isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball _ _).isPreconnected
          (((hφc k).contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hFl
            (hφ1' k)).differentiable one_ne_zero).differentiableOn (hd k) hx (mem_ball_self hρ)
      -- Lebesgue differentiation: `F ⋆ φ k → F` a.e.
      have hlim : ∀ᵐ x ∂volume, Tendsto (fun k =>
          convolution F (φ k) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop (𝓝 (F x)) := by
        filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Euclid (m + 1)))).ae_tendsto_average_norm_sub
          hFl] with x₀ h₀
        refine (tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
          (g := fun k y => φ k (x₀ - y)) (2 ^ (m + 1))
          ((h₀.comp (Besicovitch.tendsto_filterAt volume x₀)).comp hεt)
          (Eventually.of_forall fun k => hF.integrableOn) (tendsto_const_nhds.congr fun k => ?_)
          (Eventually.of_forall fun k y hy => ?_) (Eventually.of_forall fun k y => ?_)).congr
          fun k => ?_
        · rw [integral_sub_left_eq_self (fun y => φ k y) volume x₀, hφ1 k]
        · have h1 := hφsupp k (subset_tsupport _ hy)
          rw [mem_closedBall_zero_iff, ← norm_neg, neg_sub] at h1
          exact mem_closedBall_iff_norm.2 h1
        · rw [hvol x₀ _ (hε k).le, abs_of_nonneg (hφ0 k _)]
          exact hφb k _
        · rw [convolution_def]
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          show φ k (x₀ - t) • F t = (ContinuousLinearMap.lsmul ℝ ℝ) (F t) (φ k (x₀ - t))
          rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
      -- conclusion: `F x = F x₀` for a.e. `x ∈ B(0, ρ)`, and `F = G` there
      obtain ⟨x₀, hx₀, h₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (measure_ball_pos volume (0 : Euclid (m + 1)) hρ).ne' (ae_restrict_of_ae hlim)
      refine ⟨F x₀, ?_⟩
      filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_ball] with x hx hxb
      rw [← hFG x (ball_subset_closedBall (ball_subset_ball (by linarith) hxb))]
      exact tendsto_nhds_unique hx
        (h₀.congr fun k => (hconst k x₀ hx₀).trans (hconst k x hxb).symm)
    -- Step 2: the constants agree, and `B(0, r) = ⋃_q B(0, r - r/(q+2))`
    obtain ⟨c, hc⟩ := hloc (r / 2) (half_pos hr) (half_lt_self hr)
    refine ⟨c, ?_⟩
    have hU : ball (0 : Euclid (m + 1)) r = ⋃ q : ℕ, ball 0 (r - r / (q + 2)) := by
      refine Subset.antisymm (fun x hx => ?_)
        (iUnion_subset fun q => ball_subset_ball (by
          have h : (0 : ℝ) ≤ r / (q + 2) := by positivity
          linarith))
      rw [mem_ball_zero_iff] at hx
      obtain ⟨q, hq⟩ := exists_nat_gt (r / (r - ‖x‖))
      refine mem_iUnion.2 ⟨q, mem_ball_zero_iff.2 ?_⟩
      have h1 : 0 < r - ‖x‖ := by linarith
      rw [div_lt_iff₀ h1] at hq
      have h3 : r / (q + 2) < r - ‖x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        linarith
      linarith
    rw [hU, ae_restrict_iUnion_iff]
    intro q
    have hρq : r / 2 ≤ r - r / (q + 2) := by
      have h1 : r / (q + 2) ≤ r / 2 :=
        div_le_div_of_nonneg_left hr.le two_pos (by have := (Nat.cast_nonneg q : (0 : ℝ) ≤ q); linarith)
      linarith
    obtain ⟨c', hc'⟩ := hloc (r - r / (q + 2)) (by linarith) (by
      have : 0 < r / (q + 2) := by positivity
      linarith)
    have hcc : c' = c := by
      obtain ⟨v, -, hv1, hv2⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (measure_ball_pos volume (0 : Euclid (m + 1)) (half_pos hr)).ne'
        ((ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρq) hc').and hc)
      exact hv1.symm.trans hv2
    rwa [hcc] at hc'
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid (m + 1)) r)), g (Φ v) = c :=
    hconstancy (fun v => g (Φ v)) hGint hweak
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid (m + 1)) r)), g (Φ v) = c := by
    obtain ⟨v, -, hv1, z, hz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (measure_ball_pos volume (0 : Euclid (m + 1)) hr).ne' (hc₀.and hGZ)
    refine ⟨z, ?_⟩
    rw [← hz, hv1]
    exact hc₀
  -- Step 11: `T ω = c ∫ ω(Φ v)(τ) dv` for `spt ω ⊆ B`
  have hTc : ∀ ω : TestFormOn U (m + 1),
      tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ ball p r →
        T ω = c * ∫ v, (ω : DifferentialForm (Euclid P) (m + 1)) (Φ v) τ := by
    intro ω hω
    rw [hrep ω hω, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hc] with v hv
    by_cases hvB : v ∈ ball (0 : Euclid (m + 1)) r
    · rw [hv hvB]
    · have hΦv : Φ v ∉ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) := fun h => hvB (by
        rw [← hΦball]
        exact hω h)
      rw [image_eq_zero_of_notMem_tsupport hΦv, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
        mul_zero, mul_zero]
  -- Step 12 (mass): `M_{W'}(T) = |c| |Φ⁻¹ W'|` for open `W' ⊆ B`
  have hcE : ‖((c : ℤ) : ℝ)‖ₑ = (c.natAbs : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal_abs, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast,
      ENNReal.ofReal_natCast]
  have hmassW : ∀ W' : Set (Euclid P), IsOpen W' → W' ⊆ ball p r →
      T.massOn W' = (c.natAbs : ℝ≥0∞) * volume (Φ ⁻¹' W') := by
    intro W' hW' hW'B
    apply le_antisymm
    · -- `T ω ≤ |c| ∫ |ω(Φ v)(τ)| dv ≤ |c| |Φ⁻¹ W'|` for admissible `ω`
      refine sSup_le ?_
      rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
      show ENNReal.ofReal (T ω) ≤ _
      rw [hTc ω (hωW.trans hW'B)]
      refine ((ENNReal.ofReal_le_ofReal (le_abs_self _)).trans_eq
        (Real.enorm_eq_ofReal_abs _).symm).trans ?_
      rw [enorm_mul, hcE]
      gcongr
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_indicator_one ((hW'.preimage hΦiso.continuous).measurableSet)]
      refine lintegral_mono fun v => ?_
      by_cases hv : Φ v ∈ W'
      · rw [indicator_of_mem (show v ∈ Φ ⁻¹' W' from hv), Pi.one_apply, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2 (((hcov τ hτ).2 _).trans (hω1 _))
      · rw [image_eq_zero_of_notMem_tsupport fun h => hv (hωW h), ContinuousAlternatingMap.coe_zero,
          Pi.zero_apply, enorm_zero]
        exact zero_le
    · -- `|c| |K| ≤ T((sgn c) χ β)` for compact `K ⊆ Φ⁻¹ W'`, `χ = 1` near `Φ(K)`
      rw [(hW'.preimage hΦiso.continuous).measure_eq_iSup_isCompact, ENNReal.mul_iSup]
      refine iSup_le fun K => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun hKW => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun hK => ?_
      obtain ⟨χ, hχs, hχc, hχW, hχ01, hχ1⟩ := hury (Φ '' K) W' (hK.image hΦiso.continuous) hW'
        (image_subset_iff.2 hKW)
      obtain ⟨σ, hσ, hcσ⟩ : ∃ σ : ℝ, |σ| = 1 ∧ (c : ℝ) * σ = (c.natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        rcases le_or_gt 0 (c : ℝ) with h | h
        · exact ⟨1, abs_one, by rw [mul_one, abs_of_nonneg h]⟩
        · exact ⟨-1, by rw [abs_neg, abs_one], by rw [mul_neg_one, abs_of_neg h]⟩
      let ω' : DifferentialForm (Euclid P) (m + 1) := fun x => (σ * χ x) • β
      have hω'χ : tsupport ω' ⊆ tsupport χ :=
        (tsupport_smul_subset_left _ _).trans tsupport_mul_subset_right
      have hω't : tsupport ω' ⊆ W' := hω'χ.trans hχW
      have hω' : ω' ∈ TestFormOn U (m + 1) :=
        ⟨⟨(contDiff_const.mul hχs).smul contDiff_const, hχc.mono' ((subset_tsupport _).trans hω'χ)⟩,
          hω't.trans (hW'B.trans hBU)⟩
      have hadm : (⟨ω', hω'⟩ : TestFormOn U (m + 1)) ∈ massAdmissibleOn U (m + 1) W' := by
        refine ⟨hω't, fun x => ?_⟩
        show covectorEuclideanNorm ((σ * χ x) • β) ≤ 1
        have hsm : covectorEuclideanNorm ((σ * χ x) • β) = |σ * χ x| * covectorEuclideanNorm β := by
          unfold covectorEuclideanNorm
          rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun I _ => ?_
          split_ifs
          · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
          · rw [mul_zero]
        rw [hsm, abs_mul, hσ, one_mul, abs_of_nonneg (hχ01 x).1]
        calc χ x * covectorEuclideanNorm β ≤ 1 * 1 :=
              mul_le_mul (hχ01 x).2 hβE (covectorEuclideanNorm_nonneg β) zero_le_one
          _ = 1 := one_mul 1
      refine le_trans ?_ (T.le_massOn hadm)
      rw [hTc ⟨ω', hω'⟩ (hω't.trans hW'B)]
      have hint : ∫ v, (ω' (Φ v)) τ = σ * ∫ v, χ (Φ v) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        show ((σ * χ (Φ v)) • β) τ = σ * χ (Φ v)
        rw [ContinuousAlternatingMap.smul_apply, hβτ, smul_eq_mul, mul_one]
      have hχΦ : Integrable (fun v => χ (Φ v)) := by
        have h1 : Continuous fun v => χ (Φ v) := hχs.continuous.comp hΦiso.continuous
        refine h1.integrable_of_hasCompactSupport ?_
        exact (hχc.comp_isClosedEmbedding hΦiso.isClosedEmbedding)
      rw [hint, ← mul_assoc, hcσ, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ofReal_integral_eq_lintegral_ofReal hχΦ (Eventually.of_forall fun v => (hχ01 _).1)]
      gcongr
      rw [← lintegral_indicator_one hK.measurableSet]
      refine lintegral_mono fun v => ?_
      by_cases hv : v ∈ K
      · rw [indicator_of_mem hv, Pi.one_apply, (hχ1 (Φ v) ⟨v, hv, rfl⟩).self_of_nhds,
          ENNReal.ofReal_one]
      · rw [indicator_of_notMem hv]
        exact zero_le
  -- Step 13 (density): `|c| = k`
  have hck : (c.natAbs : ℝ≥0∞) = k := by
    have hU1 : unitBallVolume (m + 1) ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
    have hU2 : unitBallVolume (m + 1) ≠ ⊤ := measure_ball_lt_top.ne
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), (c.natAbs : ℝ≥0∞) = T.massOn (ball p s) /
        (unitBallVolume (m + 1) * ENNReal.ofReal (s ^ (m + 1))) := by
      filter_upwards [Ioo_mem_nhdsGT hr] with s hs
      rw [hmassW _ isOpen_ball (ball_subset_ball hs.2.le), hΦball,
        Measure.addHaar_ball_of_pos volume 0 hs.1, finrank_euclideanSpace_fin, mul_comm
          (ENNReal.ofReal _)]
      exact (ENNReal.mul_div_cancel_right
        (mul_ne_zero hU1 (ENNReal.ofReal_pos.2 (pow_pos hs.1 _)).ne')
        (ENNReal.mul_ne_top hU2 ENNReal.ofReal_ne_top)).symm
    have h := tendsto_nhds_unique hdens.2 (tendsto_const_nhds.congr' hev)
    rw [ENNReal.ofReal_natCast] at h
    exact h.symm
  -- Step 14: `M_W(T) = k |Φ⁻¹ W| = k Hⁿ(W ∩ Q)`
  rw [hmassW W hW hWB, hck, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    ← hΦiso.euclideanHausdorffMeasure_image, image_preimage_eq_inter_range, hΦrange]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
