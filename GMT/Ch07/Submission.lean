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
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl
/-- **Every current in `η(U)` is a blow-up**, `η = η_{x,λ}`, `λ > 0` (Simon Ch. 6, 2.23 and 3.9
for `η⁻¹`; used for the minimality of `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt
lines 326–338): every `S' ∈ 𝒟ₙ(η(U))` is `η_{x,λ#}S''` for some `S'' ∈ 𝒟ₙ(U)`, integer
multiplicity whenever `S'` is.  `κ = η_{−λ⁻¹x,λ⁻¹}` inverts `η`, so `κ(η(U)) = U`, and `S''` is
`κ_#S'` restricted to `U`: `dtc_blowUp_testForm_corr` for `η` and for `κ` gives
`η_#S''(ω) = λ⁻ⁿ κ_#S'(ω ∘ η) = λ⁻ⁿ λⁿ S'(ω)`, and a representation of `κ_#S'` in
`κ(η(U)) = U` (`dtc_blowUp_imrep`) represents `S''`. -/
theorem Submission.dtc_blowUp_preimage : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (S' : GeometricCurrentOn (dilation x lam '' U) n), ∃ S'' : GeometricCurrentOn U n, blowUp S'' x lam hlam.ne' = S' ∧ (IsIntegerMultiplicity S' → IsIntegerMultiplicity S'') := by
  intro P n U x lam hlam S'
  have hlam' : 0 < lam⁻¹ := inv_pos.mpr hlam
  -- `κ = η_{−λ⁻¹x,λ⁻¹}`, `κ(z) = x + λz`, is a two-sided inverse of `η = η_{x,λ}`
  have hκη : ∀ y, dilation (-(lam⁻¹ • x)) lam⁻¹ (dilation x lam y) = y := fun y => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hηκ : ∀ z, dilation x lam (dilation (-(lam⁻¹ • x)) lam⁻¹ z) = z := fun z => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hdom : dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) = U := by
    rw [image_image]
    simp only [hκη, image_id']
  have hUV : U ⊆ dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) := hdom.superset
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hblow' := (Submission.dtc_blowUp_testForm_corr P n (dilation x lam '' U)
    (-(lam⁻¹ • x)) lam⁻¹ hlam').2.2
  -- `S'' := κ_#S'`, restricted from `κ(η(U)) = U` to `U`
  refine ⟨(blowUp S' (-(lam⁻¹ • x)) lam⁻¹ hlam'.ne').restrictDomain hUV, ?_, ?_⟩
  · -- `η_#S''(ω) = λ⁻ⁿ S''(ω ∘ η)` and `κ_#S'(ω ∘ η) = λⁿ S'(ω)`, as `ω ∘ η ∘ κ = ω`
    ext ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow _ ω ω' hω', GeometricCurrentOn.restrictDomain_apply,
      hblow' S' (testFormOnInclusion hUV n ω') ω fun z => by
        rw [testFormOnInclusion_coe, hω', hηκ],
      ← mul_assoc, ← mul_pow, inv_inv, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]
  · -- a representation of `κ_#S'` in `κ(η(U)) = U` is one in `U`, and it represents `S''`
    rintro ⟨R₁, hR₁⟩
    obtain ⟨R₂, hR₂, -⟩ := Submission.dtc_blowUp_imrep P n (dilation x lam '' U) S'
      (-(lam⁻¹ • x)) lam⁻¹ hlam' R₁ hR₁
    exact ⟨{ R₂ with
        carrier_subset := R₂.carrier_subset.trans hdom.subset
        locallyIntegrable_mult := fun K hK hKU =>
          R₂.locallyIntegrable_mult K hK (hKU.trans hUV) },
      fun ω => hR₂ (testFormOnInclusion hUV n ω)⟩

/-- **Blow-ups preserve minimality** (Simon 7.1.1, chapter-07.txt lines 12–18, for `η = η_{x,λ}`,
`λ > 0`; used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337): if `T` is
minimizing in `A`, then `η_#T` is minimizing in `η(A)`.

`η_#T` is integer multiplicity (`dtc_blowUp_imrep`).  A competitor `S'` for `η_#T` on
`W' ⊂⊂ η(U)` is `η_#S''` with `S''` integer multiplicity (`dtc_blowUp_preimage`), and `S''` is a
competitor for `T` on `W = η⁻¹(W') ⊂⊂ U`: `∂S'' = ∂T` and
`spt(S'' − T) = η⁻¹(spt(S' − η_#T)) ⊆ A ∩ W` (`dtc_blowUp_algebra`).  So
`M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')` (`dtc_blowUp_massOn_image`). -/
theorem Submission.dtc_blowUp_isMinimizingIn : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A) := by
  intro P n U A T x lam hlam hT
  obtain ⟨⟨R, hR⟩, hmin⟩ := hT
  obtain ⟨hsub, hinj, hspt, hbdry⟩ := Submission.dtc_blowUp_algebra P U x lam hlam
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨?_, fun W' S' hW'o hW'c hS'im hS'bd hS'c hS'A => ?_⟩
  · -- `η_#T` is integer multiplicity
    obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P n U T x lam hlam R hR
    exact ⟨R', hR'⟩
  -- `S' = η_#S''` with `S''` integer multiplicity
  obtain ⟨S'', rfl, hS''im⟩ := Submission.dtc_blowUp_preimage P n U x lam hlam S'
  -- `W = η⁻¹(W')` is open and `W ⊂⊂ U`, since `closure W = η⁻¹(closure W')` and `η⁻¹(η(U)) = U`
  have hWo : IsOpen (dilation x lam ⁻¹' W') := by
    rw [← he]
    exact hW'o.preimage e.continuous
  have hWc : CompactlyContained (dilation x lam ⁻¹' W') U := by
    obtain ⟨hc, hsub'⟩ := hW'c
    rw [← he] at hsub' ⊢
    refine ⟨?_, ?_⟩ <;> rw [← e.preimage_closure]
    · exact e.isCompact_preimage.2 hc
    · exact (preimage_mono hsub').trans (e.preimage_image U).subset
  -- `∂S'' = ∂T`: `η_#(∂S'') = ∂S' = ∂(η_#T) = η_#(∂T)` and `η_#` is injective
  have hbd : SameBoundary S'' T := by
    cases n with
    | zero => trivial
    | succ m =>
      show S''.boundary = T.boundary
      apply hinj
      rw [← hbdry, ← hbdry]
      exact hS'bd
  -- `spt(S' − η_#T) = η(spt(S'' − T))`, so `spt(S'' − T)` is compact and lies in `A ∩ W`
  have hspt' : (blowUp S'' x lam hlam.ne' - blowUp T x lam hlam.ne').support =
      dilation x lam '' (S'' - T).support := by
    rw [← hsub, hspt]
  rw [hspt', ← he] at hS'c hS'A
  have hc : IsCompact (S'' - T).support := e.isCompact_image.1 hS'c
  have hA : (S'' - T).support ⊆ A ∩ dilation x lam ⁻¹' W' := by
    intro y hy
    obtain ⟨⟨a, ha, hay⟩, hyW'⟩ := hS'A (mem_image_of_mem e hy)
    rw [← he]
    exact ⟨e.injective hay ▸ ha, hyW'⟩
  -- `M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')`, as `η(W) = W'`
  have hle := hmin _ S'' hWo hWc (hS''im hS'im) hbd hc hA
  have hW' : dilation x lam '' (dilation x lam ⁻¹' W') = W' := by
    rw [← he]
    exact e.image_preimage W'
  have hmT := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W')
  have hmS := Submission.dtc_blowUp_massOn_image P n U S'' x lam hlam (dilation x lam ⁻¹' W')
  rw [hW'] at hmT hmS
  rw [hmT, hmS]
  gcongr

/-- **Scaling of blow-ups** `η_{x,λ#}T`, `η = η_{x,λ}`, `λ > 0` (proof of Simon 7.3.1,
chapter-07.txt lines 326–338; push-forward 6.2.23 and 6.3.3–6.3.9): (1) the mass scaling
`M_{η(W)}(η_#T) = λ⁻ⁿ M_W(T)` of (1) there (`dtc_blowUp_massOn_image`); (2) a representation
`(M, θ, ξ)` of `T` pushes forward to one of `η_#T` with `μ_{η_#T}(B) = λ⁻ⁿ μ_T(η⁻¹(B))`
(`dtc_blowUp_imrep`); (3) `η_#T` is minimizing in `η(A)` if `T` is minimizing in `A`
(`dtc_blowUp_isMinimizingIn`).  The hypotheses `U` open and `n > 0` are not needed. -/
theorem Submission.dtc_blowUp_scaling : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsOpen U → 0 < n → (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W) ∧ (∀ R : IMRep U n, R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) ∧ (IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A)) := by
  intro P n U A T x lam hlam _ _
  exact ⟨Submission.dtc_blowUp_massOn_image P n U T x lam hlam,
    Submission.dtc_blowUp_imrep P n U T x lam hlam,
    Submission.dtc_blowUp_isMinimizingIn P n U A T x lam hlam⟩

/-- **Blow-ups at a point of finite density have locally bounded mass** (proof of Simon 7.3.1,
display (1), chapter-07.txt lines 329–335): if `Θⁿ(μ_T, x) = θ` and `λⱼ > 0`, `λⱼ → 0`, then
for each `R` there is `c < ∞` with `M_{B_R(0)}(η_{x,λⱼ#}T) ≤ c` for all large `j`.  For `R ≤ 0`
the ball is empty and the mass is `0`.  For `R > 0`, `M_{B_ρ(x)}(T) ≤ (θ + 1) ωₙ ρⁿ` for small
`ρ > 0`; since `η_{x,λ}(B_{λR}(x)) = B_R(0)`, the scaling `Submission.dtc_blowUp_scaling` gives
`M_{B_R(0)}(η_{x,λⱼ#}T) = λⱼ⁻ⁿ M_{B_{λⱼR}(x)}(T) ≤ (θ + 1) ωₙ Rⁿ` once `λⱼR` is small. -/
theorem Submission.dtc_bc_bh_blowUp_massOn_ball_bounded : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ), IsOpen U → 0 < n → HasMassDensity T x θ → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T x (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c := by
  intro P n U T x θ hU hn hθ lams hlams hlim R
  obtain ⟨hθ0, hlimθ⟩ := hθ
  by_cases hR : 0 < R
  swap
  · -- `R ≤ 0`: `B_R(0) = ∅`, the only admissible form is `0`, so the mass is `0`
    refine ⟨0, ENNReal.zero_ne_top, Eventually.of_forall fun j => ?_⟩
    have hempty : ball (0 : Euclid P) R = ∅ := ball_eq_empty.2 (not_lt.1 hR)
    rw [hempty]
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    have hω0 : ω = 0 := by
      apply Subtype.ext
      funext y
      by_contra hy
      have : y ∈ tsupport (ω : DifferentialForm (Euclid P) n) := subset_tsupport _ hy
      exact (hω.1 this).elim
    simp only [hω0, map_zero, ENNReal.ofReal_zero, le_refl]
  -- `ωₙ ∈ (0, ∞)`
  have hω0 : unitBallVolume n ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- the density ratio is eventually `< ofReal (θ + 1)` as `ρ ↓ 0`
  have hlt : ENNReal.ofReal θ < ENNReal.ofReal (θ + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  obtain ⟨s₀, hs₀, hs₀ev⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    ((tendsto_order.1 hlimθ).2 _ hlt)
  -- hence `M_{B_ρ(x)}(T) ≤ ofReal (θ + 1) ωₙ ρⁿ` for `0 < ρ < s₀`
  have hmass : ∀ ρ : ℝ, 0 < ρ → ρ < s₀ →
      T.massOn (ball x ρ) ≤ ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
    intro ρ hρ hρs
    have h := hs₀ev ⟨hρ, hρs⟩
    have hb0 : unitBallVolume n * ENNReal.ofReal (ρ ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne'
    have hbtop : unitBallVolume n * ENNReal.ofReal (ρ ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    exact ((ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbtop)).1 h).le
  refine ⟨ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal (R ^ n)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top), ?_⟩
  have hsmall : ∀ᶠ j in atTop, lams j * R < s₀ := by
    have h0 : Tendsto (fun j => lams j * R) atTop (𝓝 0) := by
      simpa using hlim.mul_const R
    exact (tendsto_order.1 h0).2 s₀ hs₀
  filter_upwards [hsmall] with j hj
  have hlam := hlams j
  -- `η_j(B_{λⱼR}(x)) = B_R(0)`
  have himg : dilation x (lams j) '' ball x (lams j * R) = ball 0 R := by
    have hdil : ∀ y : Euclid P, dilation x (lams j) y = (lams j)⁻¹ • (y - x) := by
      intro y
      simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
        ContinuousLinearMap.coe_id', id_eq, smul_sub]
      abel
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_ball, dist_zero_right, hdil, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
      calc (lams j)⁻¹ * ‖y - x‖ < (lams j)⁻¹ * (lams j * R) :=
            mul_lt_mul_of_pos_left hy (inv_pos.2 hlam)
        _ = R := by field_simp
    · intro hz
      rw [mem_ball, dist_zero_right] at hz
      refine ⟨x + lams j • z, ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
        exact mul_lt_mul_of_pos_left hz hlam
      · rw [hdil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  rw [← himg, (Submission.dtc_blowUp_scaling P n U U T x (lams j) hlam hU hn).1 (ball x (lams j * R))]
  calc ENNReal.ofReal ((lams j)⁻¹ ^ n) * T.massOn (ball x (lams j * R))
      ≤ ENNReal.ofReal ((lams j)⁻¹ ^ n) *
          (ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal ((lams j * R) ^ n))) := by
        gcongr
        exact hmass _ (mul_pos hlam hR) hj
    _ = ENNReal.ofReal (θ + 1) * (unitBallVolume n * ENNReal.ofReal (R ^ n)) := by
        rw [mul_left_comm]
        congr 1
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]

/-- **Blow-up domains and boundaries near `x ∉ spt ∂T`** (Simon 7.3.1, proof, chapter-07.txt
lines 334–335: "`∂η_{x,λⱼ#}T = 0` in `B_R(0)` for sufficiently large `j` (because
`x ∉ spt ∂T`)").  `ηⱼ = η_{x,λⱼ}` is an affine homeomorphism with `ηⱼ(x + λⱼz) = z`, so (1) `ηⱼ(U)`
is open.  As `x ∈ U ∩ Z(∂T)` (`Z` the zero region, `spt ∂T = U \ Z(∂T)`), some `B_r(x)` lies in
`U ∩ Z(∂T)`, and `λⱼR < r` for all large `j`; then (2) `B̄_R(0) ⊆ ηⱼ(B_r(x)) ⊆ ηⱼ(U)`, and (3)
`∂(ηⱼ#T) = ηⱼ#(∂T)` has support `ηⱼ(spt ∂T)`, which misses `B_R(0) ⊆ ηⱼ(B_r(x))`, so `∂(ηⱼ#T)`
annihilates every test form supported in `B_R(0)` (`dtc_blowUp_algebra`,
`dtc_vanish_off_support`). -/
theorem Submission.dtc_bc_bh_blowUp_domain_boundary : ∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (x : Euclid P), IsOpen U → x ∈ U → x ∉ boundarySupport T → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → (∀ j, IsOpen (dilation x (lams j) '' U)) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ dilation x (lams j) '' U) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, ∀ ω : TestFormOn (dilation x (lams j) '' U) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → (blowUp T x (lams j) (hlams j).ne').boundary ω = 0) := by
  intro P m U T x hU hxU hxb lams hlams hlim
  -- `η_{x,λ}(y) = λ⁻¹ • (y - x)`
  have hdil : ∀ (lam : ℝ) (y : Euclid P), dilation x lam y = lam⁻¹ • (y - x) := by
    intro lam y
    simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_sub]
    abel
  -- `η_{x,λ}(x + λz) = z`, and `η_{x,λ}(y) = z` forces `y = x + λz`
  have hdil_inv : ∀ (lam : ℝ) (z : Euclid P), lam ≠ 0 → dilation x lam (x + lam • z) = z := by
    intro lam z hlam
    rw [hdil, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hdil_eq : ∀ (lam : ℝ) (y z : Euclid P), lam ≠ 0 → dilation x lam y = z →
      y = x + lam • z := by
    intro lam y z hlam h
    rw [← h, hdil, smul_smul, mul_inv_cancel₀ hlam, one_smul, add_sub_cancel]
  -- `λⱼR` is eventually below any positive bound
  have hsmall : ∀ (R t : ℝ), 0 < t → ∀ᶠ j in atTop, lams j * R < t := by
    intro R t ht
    have h0 : Tendsto (fun j => lams j * R) atTop (𝓝 0) := by
      simpa using hlim.mul_const R
    exact (tendsto_order.1 h0).2 t ht
  -- (1) `ηⱼ(U)` is the image of the open `U` under a homeomorphism
  have hopen : ∀ j, IsOpen (dilation x (lams j) '' U) := by
    intro j
    have hlam : lams j ≠ 0 := (hlams j).ne'
    have hfun : dilation x (lams j) =
        ((Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero (lams j)⁻¹ (inv_ne_zero hlam)) :
          Euclid P → Euclid P) := by
      funext y
      rw [hdil]
      rfl
    rw [hfun]
    exact ((Homeomorph.subRight x).trans
      (Homeomorph.smulOfNeZero (lams j)⁻¹ (inv_ne_zero hlam))).isOpenMap U hU
  -- a ball `B_r(x)` inside `U` and inside the zero region of `∂T`
  have hxZ : x ∈ T.boundary.zeroRegion := by
    by_contra h
    exact hxb ⟨hxU, h⟩
  obtain ⟨r, hr, hrU⟩ :=
    Metric.isOpen_iff.1 (hU.inter T.boundary.isOpen_zeroRegion) x ⟨hxU, hxZ⟩
  refine ⟨hopen, ?_, ?_⟩
  · -- (2) `B̄_R(0) ⊆ ηⱼ(U)` once `λⱼR < r`
    intro R
    filter_upwards [hsmall R r hr] with j hj
    intro z hz
    have hlam := hlams j
    refine ⟨x + lams j • z, (hrU ?_).1, hdil_inv (lams j) z hlam.ne'⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
    rw [mem_closedBall, dist_zero_right] at hz
    calc lams j * ‖z‖ ≤ lams j * R := mul_le_mul_of_nonneg_left hz hlam.le
      _ < r := hj
  · -- (3) `∂(ηⱼ#T)(ω) = 0` for `spt ω ⊆ B_R(0)` once `λⱼR < r`
    intro R
    filter_upwards [hsmall R r hr] with j hj ω hω
    have hlam := hlams j
    have hALG := Submission.dtc_blowUp_algebra P U x (lams j) hlam
    rw [hALG.2.2.2 m T]
    apply Submission.dtc_vanish_off_support
    rw [hALG.2.2.1 m T.boundary, Set.disjoint_left]
    rintro z hz ⟨y, hy, hyz⟩
    have hyx : y = x + lams j • z := hdil_eq (lams j) y z hlam.ne' hyz
    have hzR := hω hz
    rw [mem_ball, dist_zero_right] at hzR
    have hyball : y ∈ ball x r := by
      rw [hyx, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hlam.le]
      calc lams j * ‖z‖ ≤ lams j * R := mul_le_mul_of_nonneg_left hzR.le hlam.le
        _ < r := hj
    exact hy.2 (hrU hyball).2
/-- **Rescaled retractions** (Simon 7.2.4 and Remark 7.2.5(2), rescaled for the blow-ups of
7.3.1).  Let `π` be a `C¹` retraction of `B_δ(x)` onto `N` (`π(B_δ(x)) ⊆ N`, `π = id` on
`N ∩ B_δ(x)`) whose Lipschitz constant on `B_s(x)` is at most `1 + η` for small `s`.  Then
`πⱼ(z) = η_{x,λⱼ}(π(x + λⱼz)) = λⱼ⁻¹(π(x + λⱼz) − x)` is, for all large `j`, a `C¹` map of
`B_G(0)` into `η_{x,λⱼ}(U ∩ N)` which is the identity on `η_{x,λⱼ}(U ∩ N) ∩ B_G(0)` and satisfies
`|πⱼ(z)| ≤ 2|z|`; and for every `η > 0`, eventually `πⱼ` is `(1 + η)`-Lipschitz on `B_G(0)`.
Once `λⱼG` is below a radius `s₁` on which `π` is `2`-Lipschitz and below half the radius of a
ball `B_{r₀}(x) ⊆ U`, `x + λⱼz ∈ B_{s₁}(x)` and `|π(x + λⱼz) − x| ≤ 2λⱼ|z| < r₀` (`π(x) = x`). -/
theorem Submission.dtc_bc_bh_rescaled_retraction : ∀ (P : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (δ : ℝ) (π : Euclid P → Euclid P), IsOpen U → x ∈ U → x ∈ N → 0 < δ → ContDiffOn ℝ 1 π (ball x δ) → MapsTo π (ball x δ) N → (∀ y ∈ N ∩ ball x δ, π y = y) → (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖) → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∀ G : ℝ, 0 < G → ∃ πs : ℕ → Euclid P → Euclid P, (∀ᶠ j in atTop, ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation x (lams j) '' (U ∩ N)) ∧ (∀ y ∈ dilation x (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y) ∧ ∀ y ∈ ball 0 G, ‖πs j y‖ ≤ 2 * ‖y‖) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖ := by
  intro P U N x δ π hU hxU hxN hδ hC hmaps hid hlip lams hlams hlim G hG
  -- a ball `B_{r₀}(x) ⊆ U`
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hU x hxU
  -- `π` is `2`-Lipschitz on `B_{s₁}(x)`
  obtain ⟨s₁, hs₁, hs₁δ, hlip1⟩ := hlip 1 one_pos
  have hπx : π x = x := hid x ⟨hxN, mem_ball_self hδ⟩
  -- `η_{x,λ}(y) = λ⁻¹ • (y - x)`
  have hdil : ∀ (lam : ℝ) (y : Euclid P), dilation x lam y = lam⁻¹ • (y - x) := by
    intro lam y
    simp only [dilation, dilationCLM, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.coe_id', id_eq, smul_sub]
    abel
  -- `x + λ • z ∈ B_t(x)` when `z ∈ B_G(0)` and `λ G ≤ t`
  have hmem : ∀ (lam t : ℝ) (z : Euclid P), 0 < lam → lam * G ≤ t → z ∈ ball (0 : Euclid P) G →
      x + lam • z ∈ ball x t := by
    intro lam t z hlam hlt hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
    rw [mem_ball, dist_zero_right] at hz
    calc lam * ‖z‖ < lam * G := mul_lt_mul_of_pos_left hz hlam
      _ ≤ t := hlt
  -- `λⱼ G < t` for all large `j`
  have hsmall : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, lams j * G < t := by
    intro t ht
    have h0 : Tendsto (fun j => lams j * G) atTop (𝓝 0) := by
      simpa using hlim.mul_const G
    exact (tendsto_order.1 h0).2 t ht
  refine ⟨fun j z => dilation x (lams j) (π (x + lams j • z)), ?_, ?_⟩
  · filter_upwards [hsmall (min s₁ (r₀ / 2)) (lt_min hs₁ (half_pos hr₀))] with j hj
    have hlam := hlams j
    have hj₁ : lams j * G ≤ s₁ := hj.le.trans (min_le_left _ _)
    have hj₂ : lams j * G ≤ r₀ / 2 := hj.le.trans (min_le_right _ _)
    have hjδ : lams j * G ≤ δ := hj₁.trans hs₁δ
    -- the affine map `z ↦ x + λⱼ z` maps `B_G(0)` into `B_δ(x)`
    have hmapsδ : MapsTo (fun z : Euclid P => x + lams j • z) (ball 0 G) (ball x δ) :=
      fun z hz => hmem (lams j) δ z hlam hjδ hz
    -- `π(x + λⱼ z) ∈ U ∩ N` and `|π(x + λⱼ z) - x| ≤ 2 λⱼ |z|`
    have hkey : ∀ z ∈ ball (0 : Euclid P) G, π (x + lams j • z) ∈ U ∩ N ∧
        ‖π (x + lams j • z) - x‖ ≤ 2 * (lams j * ‖z‖) := by
      intro z hz
      have hy : x + lams j • z ∈ ball x s₁ := hmem (lams j) s₁ z hlam hj₁ hz
      have hbd : ‖π (x + lams j • z) - x‖ ≤ 2 * (lams j * ‖z‖) := by
        have := hlip1 _ hy x (mem_ball_self hs₁)
        rw [hπx] at this
        calc ‖π (x + lams j • z) - x‖ ≤ (1 + 1) * ‖x + lams j • z - x‖ := this
          _ = 2 * (lams j * ‖z‖) := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]; norm_num
      refine ⟨⟨hr₀U ?_, hmaps (hmapsδ hz)⟩, hbd⟩
      rw [mem_ball, dist_eq_norm]
      rw [mem_ball, dist_zero_right] at hz
      calc ‖π (x + lams j • z) - x‖ ≤ 2 * (lams j * ‖z‖) := hbd
        _ < 2 * (lams j * G) := by
          have := mul_lt_mul_of_pos_left hz hlam
          linarith
        _ ≤ r₀ := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `C¹` on `B_G(0)`
      have hdilC : ContDiff ℝ 1 (dilation x (lams j)) := by
        unfold dilation
        exact contDiff_const.add (dilationCLM P (lams j)).contDiff
      have haff : ContDiff ℝ 1 (fun z : Euclid P => x + lams j • z) :=
        contDiff_const.add (contDiff_id.const_smul (lams j))
      exact hdilC.comp_contDiffOn (hC.comp haff.contDiffOn hmapsδ)
    · -- maps `B_G(0)` into `η_j(U ∩ N)`
      intro z hz
      exact ⟨π (x + lams j • z), (hkey z hz).1, rfl⟩
    · -- identity on `η_j(U ∩ N) ∩ B_G(0)`
      rintro z ⟨⟨y', hy', rfl⟩, hz⟩
      have hinv : x + lams j • dilation x (lams j) y' = y' := by
        rw [hdil, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
      show dilation x (lams j) (π (x + lams j • dilation x (lams j) y')) = dilation x (lams j) y'
      rw [hinv, hid y' ⟨hy'.2, ?_⟩]
      rw [← hinv]
      exact hmapsδ hz
    · -- `|π_j(z)| ≤ 2|z|`
      intro z hz
      show ‖dilation x (lams j) (π (x + lams j • z))‖ ≤ 2 * ‖z‖
      rw [hdil, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
      calc (lams j)⁻¹ * ‖π (x + lams j • z) - x‖ ≤ (lams j)⁻¹ * (2 * (lams j * ‖z‖)) :=
            mul_le_mul_of_nonneg_left (hkey z hz).2 (inv_nonneg.2 hlam.le)
        _ = 2 * ‖z‖ := by field_simp
  · intro η hη
    obtain ⟨s, hs, hsδ, hlipη⟩ := hlip η hη
    filter_upwards [hsmall s hs] with j hj y hy z hz
    have hlam := hlams j
    have hy' := hmem (lams j) s y hlam hj.le hy
    have hz' := hmem (lams j) s z hlam hj.le hz
    show ‖dilation x (lams j) (π (x + lams j • y)) - dilation x (lams j) (π (x + lams j • z))‖ ≤
      (1 + η) * ‖y - z‖
    rw [hdil, hdil, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
    have h1 := hlipη _ hy' _ hz'
    have h2 : ‖x + lams j • y - (x + lams j • z)‖ = lams j * ‖y - z‖ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg hlam.le]
    have h3 : π (x + lams j • y) - x - (π (x + lams j • z) - x) =
        π (x + lams j • y) - π (x + lams j • z) := by abel
    rw [h3]
    calc (lams j)⁻¹ * ‖π (x + lams j • y) - π (x + lams j • z)‖
        ≤ (lams j)⁻¹ * ((1 + η) * (lams j * ‖y - z‖)) := by
          rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hlam.le)
      _ = (1 + η) * ‖y - z‖ := by field_simp
/-- Local `C¹` retraction onto `N` (proof of Simon 7.3.1), Lipschitz bound near a point: if `f` is
`C¹` on `B_δ(x)` and `‖Df(x)‖ ≤ c`, then for every `η > 0`, `f` is `(c + η)`-Lipschitz on some
`B_s(x)`, `0 < s ≤ δ`.  `Df` is continuous at `x`, so `‖Df(y)‖ ≤ ‖Df(x)‖ + η ≤ c + η` on a small
ball `B_s(x)`; the mean value inequality on the convex ball `B_s(x)` gives the bound. -/
theorem Submission.dtc_bc_lr_lipschitz_near_point : ∀ (P : ℕ) (f : Euclid P → Euclid P) (x : Euclid P) (δ c : ℝ), 0 < δ → ContDiffOn ℝ 1 f (ball x δ) → ‖fderiv ℝ f x‖ ≤ c → ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖f y - f z‖ ≤ (c + η) * ‖y - z‖ := by
  intro P f x δ c hδ hf hc η hη
  -- `f` is differentiable at every point of the open ball `B_δ(x)`, and `Df` is continuous there
  have hdiff : ∀ y ∈ ball x δ, DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn one_ne_zero y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  have hcont : ContinuousOn (fderiv ℝ f) (ball x δ) :=
    hf.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  -- continuity of `Df` at `x`: `‖Df(y) - Df(x)‖ < η` for `|y - x| < s₁`; take `s = min s₁ δ`
  obtain ⟨s₁, hs₁, hDf⟩ := Metric.continuousAt_iff.1
    (hcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))) η hη
  refine ⟨min s₁ δ, lt_min hs₁ hδ, min_le_right _ _, ?_⟩
  -- `‖Df(y)‖ ≤ ‖Df(x)‖ + ‖Df(y) - Df(x)‖ ≤ c + η` on `B_s(x)`
  have hbound : ∀ y ∈ ball x (min s₁ δ), ‖fderiv ℝ f y‖ ≤ c + η := by
    intro y hy
    have hy₁ : ‖fderiv ℝ f y - fderiv ℝ f x‖ < η := by
      rw [← dist_eq_norm]
      exact hDf ((mem_ball.1 hy).trans_le (min_le_left _ _))
    exact (norm_le_norm_add_norm_sub' _ _).trans (add_le_add hc hy₁.le)
  -- mean value inequality on the convex ball `B_s(x)`
  intro y hy z hz
  exact (convex_ball x (min s₁ δ)).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => hdiff w (ball_subset_ball (min_le_right _ _) hw)) hbound hz hy
/-- **Simon 7.3.1** (proof; local retraction onto `N`, step 1): an injective linear map
`L : ℝᵈ → ℝᴾ` has a left inverse `A` with `‖L ∘ A‖ ≤ 1`.  With `Q = L(ℝᵈ)`, `p` the orthogonal
projection of `ℝᴾ` onto `Q` and `e : ℝᵈ ≃ Q`, `e w = L w`, take `A = e⁻¹ ∘ p`: then `A ∘ L = id`,
and `L ∘ A` is the orthogonal projection of `ℝᴾ` onto `Q`, of norm `≤ 1`. -/
theorem Submission.dtc_bc_lr_left_inverse_projection : ∀ (P d : ℕ) (L : Euclid d →L[ℝ] Euclid P), Injective L → ∃ A : Euclid P →L[ℝ] Euclid d, A.comp L = ContinuousLinearMap.id ℝ (Euclid d) ∧ ‖L.comp A‖ ≤ 1 := by
  intro P d L hL
  -- `Q = L(ℝᵈ)` and the isomorphism `e : ℝᵈ ≃ Q`, `e w = L w`
  let Q : Submodule ℝ (Euclid P) := LinearMap.range (L : Euclid d →ₗ[ℝ] Euclid P)
  let e : Euclid d ≃L[ℝ] Q :=
    (LinearEquiv.ofInjective (L : Euclid d →ₗ[ℝ] Euclid P) hL).toContinuousLinearEquiv
  have he : ∀ w, (e w : Euclid P) = L w := fun w => rfl
  -- `A = e⁻¹ ∘ p`, `p` the orthogonal projection onto `Q`
  refine ⟨(e.symm : Q →L[ℝ] Euclid d).comp Q.orthogonalProjectionOnto, ?_, ?_⟩
  · -- `p (L w) = e w`, so `A (L w) = w`
    refine ContinuousLinearMap.ext fun w => ?_
    have hp : Q.orthogonalProjectionOnto (L w) = e w := by
      rw [← he]
      exact Q.orthogonalProjectionOnto_mem_subspace_eq_self (e w)
    simp [hp]
  · -- `L ∘ A = ι ∘ p` is the orthogonal projection of `ℝᴾ` onto `Q`
    have hLA : L.comp ((e.symm : Q →L[ℝ] Euclid d).comp Q.orthogonalProjectionOnto) =
        Q.starProjection := by
      refine ContinuousLinearMap.ext fun y => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, ← he, ContinuousLinearEquiv.apply_symm_apply,
        Submodule.starProjection_apply]
    rw [hLA]
    exact Q.starProjection_norm_le
/-- **Local `C¹` inverse** (inverse function theorem, step 2 of the local retraction in the proof
of Simon 7.3.1).  If `h` is `C¹` on the open set `V ∋ v₀` with `Dh(v₀) = id`, there are open
`V₀ ⊆ V` with `v₀ ∈ V₀` and `O`, and `k`, `C¹` on `O`, such that `h : V₀ → O` and `k : O → V₀` are
mutually inverse, and `Dk(h(v₀)) = id`.  The inverse function theorem gives a partial
homeomorphism `e` with `⇑e = h`, source `S ∋ v₀` and target `T`; on the open set
`G = {v ∈ V : ‖Dh(v) − 1‖ < 1}` (which contains `v₀`) `Dh(v)` is invertible (Neumann series).  Take
`V₀ = S ∩ G`, `O = T ∩ e.symm⁻¹(V₀)`, `k = e.symm`; the `C¹` inverse rule at each `u ∈ O` makes
`k` `C¹` on `O`, and `k` has derivative `id⁻¹ = id` at `h(v₀)`. -/
theorem Submission.dtc_bc_lr_local_inverse : ∀ (d : ℕ) (h : Euclid d → Euclid d) (V : Set (Euclid d)) (v₀ : Euclid d), IsOpen V → v₀ ∈ V → ContDiffOn ℝ 1 h V → fderiv ℝ h v₀ = ContinuousLinearMap.id ℝ (Euclid d) → ∃ (V₀ O : Set (Euclid d)) (k : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ V₀ ⊆ V ∧ v₀ ∈ V₀ ∧ MapsTo h V₀ O ∧ MapsTo k O V₀ ∧ (∀ v ∈ V₀, k (h v) = v) ∧ (∀ u ∈ O, h (k u) = u) ∧ ContDiffOn ℝ 1 k O ∧ fderiv ℝ k (h v₀) = ContinuousLinearMap.id ℝ (Euclid d) := by
  intro d h V v₀ hV hv₀ hh hd
  -- Step 1: `h` is `C¹` at every point of `V`, `Dh` is continuous on `V`, and `h` has strict
  -- derivative `id` at `v₀`
  have hca : ∀ v ∈ V, ContDiffAt ℝ 1 h v := fun v hv => hh.contDiffAt (hV.mem_nhds hv)
  have hcont : ContinuousOn (fderiv ℝ h) V := hh.continuousOn_fderiv_of_isOpen hV le_rfl
  have hfd : HasFDerivAt h
      ((ContinuousLinearEquiv.refl ℝ (Euclid d) : Euclid d ≃L[ℝ] Euclid d) :
        Euclid d →L[ℝ] Euclid d) v₀ := by
    rw [ContinuousLinearEquiv.coe_refl, ← hd]
    exact ((hca v₀ hv₀).differentiableAt one_ne_zero).hasFDerivAt
  have hs := (hca v₀ hv₀).hasStrictFDerivAt' hfd one_ne_zero
  -- Step 2: the inverse function theorem gives a partial homeomorphism `e` with `⇑e = h`, and
  -- its inverse has derivative `id⁻¹ = id` at `h(v₀)`
  obtain ⟨e, he⟩ : ∃ e : OpenPartialHomeomorph (Euclid d) (Euclid d),
      e = hs.toOpenPartialHomeomorph h := ⟨_, rfl⟩
  have hecoe : (e : Euclid d → Euclid d) = h := by
    rw [he]; exact hs.toOpenPartialHomeomorph_coe
  have hv₀e : v₀ ∈ e.source := by
    rw [he]; exact hs.mem_toOpenPartialHomeomorph_source
  have hk : HasFDerivAt (e.symm : Euclid d → Euclid d) (ContinuousLinearMap.id ℝ (Euclid d))
      (h v₀) := by
    have h7 := hs.to_localInverse
    rw [hs.localInverse_def, ← he, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl] at h7
    exact h7.hasFDerivAt
  -- Step 3: `G = {v ∈ V : ‖Dh(v) − 1‖ < 1}` is open, contains `v₀`, and `Dh(v)` is invertible
  -- for `v ∈ G`
  obtain ⟨G, hG⟩ : ∃ G : Set (Euclid d), G = V ∩ fderiv ℝ h ⁻¹' ball 1 1 := ⟨_, rfl⟩
  have hGo : IsOpen G := hG ▸ hcont.isOpen_inter_preimage hV isOpen_ball
  have hGV : G ⊆ V := hG ▸ inter_subset_left
  have hv₀G : v₀ ∈ G := by
    rw [hG]
    refine ⟨hv₀, ?_⟩
    show fderiv ℝ h v₀ ∈ ball 1 1
    rw [hd, ← ContinuousLinearMap.one_def]
    exact mem_ball_self one_pos
  have hGu : ∀ v ∈ G, ∃ L : Euclid d ≃L[ℝ] Euclid d,
      (L : Euclid d →L[ℝ] Euclid d) = fderiv ℝ h v := by
    intro v hv
    rw [hG] at hv
    have hu : IsUnit (fderiv ℝ h v) := by
      by_contra hnu
      exact nonunits.subset_compl_ball (mem_nonunits_iff.mpr hnu) hv.2
    obtain ⟨u, hu⟩ := hu
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ (Euclid d) u, ?_⟩
    ext x
    simp [ContinuousLinearEquiv.unitsEquiv_apply, ← hu]
  -- Step 4: `V₀ = S ∩ G`, `O = T ∩ e.symm⁻¹(V₀)`, `k = e.symm`
  refine ⟨e.source ∩ G, e.target ∩ e.symm ⁻¹' (e.source ∩ G), e.symm,
    e.open_source.inter hGo, e.isOpen_inter_preimage_symm (e.open_source.inter hGo),
    fun v hv => hGV hv.2, ⟨hv₀e, hv₀G⟩, ?_, fun u hu => hu.2, fun v hv => ?_, fun u hu => ?_,
    ?_, ?_⟩
  -- Step 5: mapping and inverse identities
  · intro v hv
    have h1 := e.map_source hv.1
    have h2 := e.left_inv hv.1
    rw [hecoe] at h1 h2
    exact ⟨h1, by rw [mem_preimage, h2]; exact hv⟩
  · have h2 := e.left_inv hv.1
    rwa [hecoe] at h2
  · have h2 := e.right_inv hu.1
    rwa [hecoe] at h2
  -- Step 6: `k` is `C¹` on `O`, by the `C¹` inverse rule at each `u ∈ O`
  · intro u hu
    obtain ⟨L, hL⟩ := hGu _ hu.2.2
    have ha : e.symm u ∈ V := hGV hu.2.2
    have hfa : HasFDerivAt (e : Euclid d → Euclid d) (L : Euclid d →L[ℝ] Euclid d)
        (e.symm u) := by
      rw [hL, hecoe]
      exact ((hca _ ha).differentiableAt one_ne_zero).hasFDerivAt
    have hca' : ContDiffAt ℝ 1 (e : Euclid d → Euclid d) (e.symm u) := by
      rw [hecoe]; exact hca _ ha
    exact (e.contDiffAt_symm hu.1 hfa hca').contDiffWithinAt
  -- Step 7: `Dk(h(v₀)) = id`
  · exact hk.fderiv
/-- **Simon 7.3.1** (proof of (2), local retraction onto `N`, chart step): if `W` is open, `ψ` is
continuous and injective on `V`, `ψ(V) = W ∩ N` and `ψ` is proper over `W` (`V ∩ ψ⁻¹(K)` is
compact for compact `K ⊆ W`), then `N ∩ B_ρ(ψ(v₀)) ⊆ ψ(V₀)` for some `ρ > 0`, whenever `V₀ ⊆ V`
is open and `v₀ ∈ V₀`.  Otherwise there are `yᵢ = ψ(fᵢ) ∈ N` with `fᵢ ∈ V \ V₀` and
`yᵢ → ψ(v₀)`; the `fᵢ` lie in the compact set `V ∩ ψ⁻¹({ψ(v₀)} ∪ {yᵢ})`, so a subsequence
converges to some `a ∈ V \ V₀` with `ψ(a) = ψ(v₀)`, contradicting injectivity. -/
theorem Submission.dtc_bc_lr_chart_image_nhds : ∀ (P d : ℕ) (N W : Set (Euclid P)) (V V₀ : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen W → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → IsOpen V₀ → V₀ ⊆ V → v₀ ∈ V₀ → ∃ ρ : ℝ, 0 < ρ ∧ N ∩ ball (ψ v₀) ρ ⊆ ψ '' V₀ := by
  intro P d N W V V₀ ψ v₀ hW hψc hψi hψV hprop hV₀ hV₀V hv₀
  -- Step 1: `x := ψ v₀ ∈ W` and `B_{r_W}(x) ⊆ W`
  have hv₀V : v₀ ∈ V := hV₀V hv₀
  have hxW : ψ v₀ ∈ W := (hψV ▸ mem_image_of_mem ψ hv₀V : ψ v₀ ∈ W ∩ N).1
  obtain ⟨rW, hrW, hballW⟩ := Metric.isOpen_iff.1 hW _ hxW
  -- Step 2: otherwise pick `yᵢ ∈ N ∩ B_{min(r_W, 1/(i+1))}(x) \ ψ(V₀)`, so `yᵢ ∈ W` and `yᵢ → x`
  by_contra hcon
  have hseq : ∀ i : ℕ, ∃ y, y ∈ N ∧ dist y (ψ v₀) < min rW (1 / ((i : ℝ) + 1)) ∧ y ∉ ψ '' V₀ := by
    intro i
    obtain ⟨y, ⟨hyN, hyb⟩, hy⟩ := not_subset.1 fun h =>
      hcon ⟨min rW (1 / ((i : ℝ) + 1)), lt_min hrW (by positivity), h⟩
    exact ⟨y, hyN, hyb, hy⟩
  choose y hyN hyd hyV₀ using hseq
  have hyW : ∀ i, y i ∈ W := fun i => hballW ((hyd i).trans_le (min_le_left _ _))
  have hylim : Tendsto y atTop (𝓝 (ψ v₀)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun i => dist_nonneg)
      (fun i => ((hyd i).trans_le (min_le_right _ _)).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  -- Step 3: `yᵢ = ψ(fᵢ)` with `fᵢ ∈ V \ V₀`
  have hf : ∀ i, ∃ f, f ∈ V ∧ ψ f = y i := fun i => (hψV.symm ▸ ⟨hyW i, hyN i⟩ : y i ∈ ψ '' V)
  choose f hfV hfy using hf
  have hfV₀ : ∀ i, f i ∉ V₀ := fun i hi => hyV₀ i ⟨f i, hi, hfy i⟩
  -- Step 4: `K := {x} ∪ {yᵢ}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K) ∋ fᵢ` is compact
  have hKW : insert (ψ v₀) (range y) ⊆ W := by
    rintro z (rfl | ⟨i, rfl⟩)
    exacts [hxW, hyW i]
  have hfK : ∀ i, f i ∈ V ∩ ψ ⁻¹' insert (ψ v₀) (range y) := fun i =>
    ⟨hfV i, Or.inr ⟨i, (hfy i).symm⟩⟩
  -- Step 5: a subsequence `f_{φ(i)} → a ∈ V`
  obtain ⟨a, ⟨haV, -⟩, φ, hφ, hfa⟩ :=
    (hprop _ hKW hylim.isCompact_insert_range).tendsto_subseq hfK
  -- Step 6: `a ∉ V₀`, as `V₀ᶜ` is closed
  have haV₀ : a ∉ V₀ :=
    hV₀.isClosed_compl.mem_of_tendsto hfa (Eventually.of_forall fun i => hfV₀ (φ i))
  -- Step 7: `ψ(a) = x` by continuity of `ψ` on `V` and uniqueness of limits
  have h₁ : Tendsto (ψ ∘ (f ∘ φ)) atTop (𝓝 (ψ a)) :=
    (hψc a haV).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hfa, Eventually.of_forall fun i => hfV (φ i)⟩)
  have h₂ : Tendsto (ψ ∘ (f ∘ φ)) atTop (𝓝 (ψ v₀)) := by
    have hcomp : ψ ∘ (f ∘ φ) = y ∘ φ := funext fun i => hfy (φ i)
    rw [hcomp]
    exact hylim.comp hφ.tendsto_atTop
  -- Step 8: injectivity gives `a = v₀ ∈ V₀`, a contradiction
  exact haV₀ (hψi haV hv₀V (tendsto_nhds_unique h₁ h₂) ▸ hv₀)

/-- **Local `C¹` retraction onto an embedded `C²` submanifold** (proof of Simon 7.3.1; it stands
in for the nearest-point projection onto `N`, cf. Simon 7.5).  For `x ∈ N` there are `δ > 0` and
`π`, `C¹` on `B_δ(x)`, with `π(B_δ(x)) ⊆ N`, `π = id` on `N ∩ B_δ(x)`, and, for every `η > 0`,
`π` is `(1 + η)`-Lipschitz on some `B_s(x)`, `0 < s ≤ δ`.

* A chart `ψ` with `ψ(v₀) = x`, and a left inverse `A` of `L = Dψ(v₀)` with `‖L ∘ A‖ ≤ 1`.
* Inverse function theorem for `h = A(ψ − x)`, `Dh(v₀) = A ∘ L = id`: a `C¹` inverse
  `k : O → V₀` with `Dk(h(v₀)) = id`.
* Properness of the chart: `N ∩ B_ρ(x) ⊆ ψ(V₀)`.
* `π(y) = ψ(k(A(y − x)))`, `δ = min(ρ, r₀/(‖A‖ + 1))` with `B_{r₀}(0) ⊆ O`; `π` fixes
  `N ∩ B_δ(x)` because `A(ψ(v) − x) = h(v)`, and `Dπ(x) = L ∘ A` has norm `≤ 1`. -/
theorem Submission.dtc_bc_local_retraction : ∀ (P d : ℕ) (N : Set (Euclid P)) (x : Euclid P), IsEmbeddedSubmanifold 2 d N → x ∈ N → ∃ (δ : ℝ) (π : Euclid P → Euclid P), 0 < δ ∧ ContDiffOn ℝ 1 π (ball x δ) ∧ MapsTo π (ball x δ) N ∧ (∀ y ∈ N ∩ ball x δ, π y = y) ∧ ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖ := by
  intro P d N x hN hx
  -- Step 1: a chart `ψ` at `x = ψ v₀`, `L = Dψ(v₀)` and a left inverse `A` of `L`
  obtain ⟨V, W, ψ, hVo, hWo, hxW, hψ2, hψinj, hψV, hψK, hψD⟩ := hN x hx
  obtain ⟨v₀, hv₀V, hψv₀⟩ : x ∈ ψ '' V := hψV ▸ ⟨hxW, hx⟩
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ2.of_le (by norm_num)
  have hψv₀D : HasFDerivAt ψ (fderiv ℝ ψ v₀) v₀ :=
    ((hψ1.contDiffAt (hVo.mem_nhds hv₀V)).differentiableAt one_ne_zero).hasFDerivAt
  obtain ⟨A, hAL, hLA⟩ :=
    Submission.dtc_bc_lr_left_inverse_projection P d (fderiv ℝ ψ v₀) (hψD v₀ hv₀V)
  -- Step 2: the local inverse `k` of `h = A (ψ - x)` near `v₀`
  set h : Euclid d → Euclid d := fun v => A (ψ v - x) with hh_def
  have hh1 : ContDiffOn ℝ 1 h V := A.contDiff.comp_contDiffOn (hψ1.sub contDiffOn_const)
  have hhD : fderiv ℝ h v₀ = ContinuousLinearMap.id ℝ (Euclid d) := by
    rw [← hAL]
    exact (A.hasFDerivAt.comp v₀ (hψv₀D.sub_const x)).fderiv
  obtain ⟨V₀, O, k, hV₀o, hOo, hV₀V, hv₀V₀, hhV₀, hkO, hkh, -, hk1, hkD⟩ :=
    Submission.dtc_bc_lr_local_inverse d h V v₀ hVo hv₀V hh1 hhD
  have hh0 : h v₀ = 0 := by simp [hh_def, hψv₀]
  -- Step 3: `ψ(V₀)` is a neighbourhood of `x` in `N`
  obtain ⟨ρ, hρ, hρV₀⟩ := Submission.dtc_bc_lr_chart_image_nhds P d N W V V₀ ψ v₀ hWo
    hψ1.continuousOn hψinj hψV hψK hV₀o hV₀V hv₀V₀
  rw [hψv₀] at hρV₀
  -- Step 4: `δ` and `π(y) = ψ (k (A (y - x)))`
  obtain ⟨r₀, hr₀, hr₀O⟩ := Metric.isOpen_iff.1 hOo 0 (by rw [← hh0]; exact hhV₀ hv₀V₀)
  have hA1 : 0 < ‖A‖ + 1 := by positivity
  set δ : ℝ := min ρ (r₀ / (‖A‖ + 1))
  have hδ : 0 < δ := lt_min hρ (div_pos hr₀ hA1)
  have hAO : MapsTo (fun y => A (y - x)) (ball x δ) O := by
    intro y hy
    apply hr₀O
    rw [mem_ball_zero_iff]
    have hy' : ‖y - x‖ < r₀ / (‖A‖ + 1) := (mem_ball_iff_norm.1 hy).trans_le (min_le_right _ _)
    calc ‖A (y - x)‖ ≤ ‖A‖ * ‖y - x‖ := A.le_opNorm _
      _ ≤ (‖A‖ + 1) * ‖y - x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖A‖ + 1) * (r₀ / (‖A‖ + 1)) := mul_lt_mul_of_pos_left hy' hA1
      _ = r₀ := by field_simp
  -- (i) `π` is `C¹` on `B_δ(x)`
  have hπ1 : ContDiffOn ℝ 1 (fun y => ψ (k (A (y - x)))) (ball x δ) :=
    hψ1.comp (hk1.comp (A.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn hAO)
      ((hkO.comp hAO).mono_right hV₀V)
  -- (ii) `π(B_δ(x)) ⊆ N`
  have hπN : MapsTo (fun y => ψ (k (A (y - x)))) (ball x δ) N := by
    intro y hy
    have hy' : ψ (k (A (y - x))) ∈ ψ '' V := mem_image_of_mem ψ (hV₀V (hkO (hAO hy)))
    rw [hψV] at hy'
    exact hy'.2
  -- (iii) `π` fixes `N ∩ B_δ(x)`
  have hπfix : ∀ y ∈ N ∩ ball x δ, ψ (k (A (y - x))) = y := by
    rintro y ⟨hyN, hy⟩
    obtain ⟨v, hv, rfl⟩ := hρV₀ ⟨hyN, ball_subset_ball (min_le_left _ _) hy⟩
    exact congrArg ψ (hkh v hv)
  -- `Dπ(x) = L ∘ Dk(h(v₀)) ∘ A = L ∘ A` has norm `≤ 1`
  have hπD : ‖fderiv ℝ (fun y => ψ (k (A (y - x)))) x‖ ≤ 1 := by
    have hg : HasFDerivAt (fun y => A (y - x)) A x := by
      have := A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    have hgx : A (x - x) = h v₀ := by rw [hh0, sub_self, map_zero]
    have hk : HasFDerivAt k (ContinuousLinearMap.id ℝ (Euclid d)) (A (x - x)) := by
      rw [hgx, ← hkD]
      exact ((hk1.contDiffAt (hOo.mem_nhds (hhV₀ hv₀V₀))).differentiableAt
        one_ne_zero).hasFDerivAt
    have hψ' : HasFDerivAt ψ (fderiv ℝ ψ v₀) (k (A (x - x))) := by
      rw [hgx, hkh v₀ hv₀V₀]
      exact hψv₀D
    have hπx : HasFDerivAt (fun y => ψ (k (A (y - x))))
        ((fderiv ℝ ψ v₀).comp ((ContinuousLinearMap.id ℝ (Euclid d)).comp A)) x :=
      hψ'.comp x (hk.comp x hg)
    rw [hπx.fderiv, ContinuousLinearMap.id_comp]
    exact hLA
  -- (iv) Lipschitz constant `1 + η` near `x`
  exact ⟨δ, fun y => ψ (k (A (y - x))), hδ, hπ1, hπN, hπfix,
    fun η hη => Submission.dtc_bc_lr_lipschitz_near_point P _ x δ 1 hδ hπ1 hπD η hη⟩

/-- **The blow-ups satisfy the hypotheses of the compactness theorem** (proof of Simon 7.3.1,
display (1), chapter-07.txt lines 326–337; compactness theorem 7.2.4 in the form of
Remark 7.2.5(2)).  Let `T` be minimizing in `U ∩ N`, `spt T ⊆ U ∩ N`, `x ∈ spt T \ spt ∂T`,
`Θⁿ(μ_T, x) = θ`, and `λⱼ > 0`, `λⱼ → 0`; put `ηⱼ = η_{x,λⱼ}` and `Sⱼ = η_{x,λⱼ#}T`.  Then
(1) `ηⱼ(U)` is open; (2) `B̄_R(0) ⊆ ηⱼ(U)` for large `j`; (3) `Sⱼ` is minimizing in
`ηⱼ(U ∩ N)`; (4) `spt Sⱼ ⊆ ηⱼ(U ∩ N)`; (5) `M_{B_R(0)}(Sⱼ)` is bounded for large `j`;
(6) `∂Sⱼ = 0` in `B_R(0)` for large `j`; (7) there are `C¹` retractions `πⱼ` of `B_G(0)` onto
`ηⱼ(U ∩ N)` with `|πⱼ(y)| ≤ 2|y|` and Lipschitz constants tending to `1`.

* (1), (2), (6): `dtc_bc_bh_blowUp_domain_boundary`, as `x ∈ U` and `x ∉ spt ∂T`.
* (3): `dtc_blowUp_scaling` with `A = U ∩ N`.
* (4): `spt Sⱼ = ηⱼ(spt T)` (`dtc_blowUp_algebra`) and `spt T ⊆ U ∩ N`.
* (5): `dtc_bc_bh_blowUp_massOn_ball_bounded`, from the finite density at `x`.
* (7): a local retraction `π` onto `N` at `x ∈ N` (`dtc_bc_local_retraction`), rescaled to
  `πⱼ = ηⱼ ∘ π ∘ ηⱼ⁻¹` by `dtc_bc_bh_rescaled_retraction`. -/
theorem Submission.dtc_bc_blowUp_hypotheses : ∀ (m k ℓ : ℕ) (U N : Set (Euclid (m + 1 + k))) (T : GeometricCurrentOn U (m + 1)) (x : Euclid (m + 1 + k)) (θ : ℝ), IsOpen U → IsEmbeddedSubmanifold 2 (m + 1 + ℓ) N → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → x ∈ T.support \ boundarySupport T → HasMassDensity T x θ → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → (∀ j, IsOpen (dilation x (lams j) '' U)) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid (m + 1 + k)) R ⊆ dilation x (lams j) '' U) ∧ (∀ j, IsMinimizingIn (blowUp T x (lams j) (hlams j).ne') (dilation x (lams j) '' (U ∩ N))) ∧ (∀ j, (blowUp T x (lams j) (hlams j).ne').support ⊆ dilation x (lams j) '' (U ∩ N)) ∧ (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T x (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, ∀ ω : TestFormOn (dilation x (lams j) '' U) m, tsupport (ω : DifferentialForm (Euclid (m + 1 + k)) m) ⊆ ball 0 R → (blowUp T x (lams j) (hlams j).ne').boundary ω = 0) ∧ (∀ G : ℝ, 0 < G → ∃ πs : ℕ → Euclid (m + 1 + k) → Euclid (m + 1 + k), (∀ᶠ j in atTop, ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation x (lams j) '' (U ∩ N)) ∧ (∀ y ∈ dilation x (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y) ∧ ∀ y ∈ ball 0 G, ‖πs j y‖ ≤ 2 * ‖y‖) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖) := by
  intro m k ℓ U N T x θ hU hN hmin hspt hx hθ lams hlams hlim
  -- `x ∈ spt T ⊆ U ∩ N`
  have hxU : x ∈ U := (hspt hx.1).1
  have hxN : x ∈ N := (hspt hx.1).2
  -- (1), (2), (6): the blown-up domains exhaust `ℝᴾ`, and `∂Sⱼ = 0` on growing balls
  obtain ⟨h1, h2, h6⟩ := Submission.dtc_bc_bh_blowUp_domain_boundary (m + 1 + k) m U T x hU hxU
    hx.2 lams hlams hlim
  refine ⟨h1, h2, ?_, ?_, ?_, h6, ?_⟩
  · -- (3) minimality in `U ∩ N` is carried to `ηⱼ(U ∩ N)`
    intro j
    exact (Submission.dtc_blowUp_scaling (m + 1 + k) (m + 1) U (U ∩ N) T x (lams j) (hlams j) hU
      (Nat.succ_pos m)).2.2 hmin
  · -- (4) `spt Sⱼ = ηⱼ(spt T) ⊆ ηⱼ(U ∩ N)`
    intro j
    rw [(Submission.dtc_blowUp_algebra (m + 1 + k) U x (lams j) (hlams j)).2.2.1 (m + 1) T]
    exact image_mono hspt
  · -- (5) local mass bounds from `Θⁿ(μ_T, x) = θ`
    exact Submission.dtc_bc_bh_blowUp_massOn_ball_bounded (m + 1 + k) (m + 1) U T x θ hU
      (Nat.succ_pos m) hθ lams hlams hlim
  · -- (7) rescale a local `C¹` retraction onto `N` at `x`
    intro G hG
    obtain ⟨δ, π, hδ, hC, hmaps, hid, hlip⟩ :=
      Submission.dtc_bc_local_retraction (m + 1 + k) (m + 1 + ℓ) N x hN hxN
    exact Submission.dtc_bc_bh_rescaled_retraction (m + 1 + k) U N x δ π hU hxU hxN hδ hC hmaps
      hid hlip lams hlams hlim G hG

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
