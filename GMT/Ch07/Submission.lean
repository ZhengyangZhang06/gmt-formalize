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

/-- **Lipschitz order statistic** (proof of Simon Ch. 6, Lemma 5.4, the retraction of the
deformation theorem): for `m + 1 < P` the `ℓ`-th largest entry
`κ u = max_{|I| = ℓ} min_{i ∈ I} u i`, `ℓ = P − (m + 1)`, of `u : Fin P → ℝ` is `≤` at least `ℓ`
entries of `u`, `≥` at least `m + 2` entries, and is `1`-Lipschitz for the sup norm.  A maximizing
`I` gives the first property; if at most `m + 1` entries were `≤ κ u`, then `ℓ` entries `> κ u`
would form an `I` with `min_I u > κ u`; and each `min_I` is `1`-Lipschitz for the sup norm, hence
so is their maximum. -/
theorem Submission.dor_lmb_fcdr_order_stat : ∀ (P m : ℕ), m + 1 < P → ∃ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) ∧ (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, u i ≤ κ u) ∧ ∀ u v : Fin P → ℝ, ∀ t : ℝ, (∀ i, |u i - v i| ≤ t) → |κ u - κ v| ≤ t := by
  intro P m hmP
  classical
  -- `𝓕` = the `ℓ`-element index sets, `ℓ = P − (m + 1) ≥ 1`; `𝓕` and its members are nonempty
  let F : Finset (Finset (Fin P)) := Finset.powersetCard (P - (m + 1)) Finset.univ
  have hF : F.Nonempty := Finset.powersetCard_nonempty.2 (by rw [Finset.card_fin]; omega)
  have hFI : ∀ I ∈ F, I.Nonempty ∧ I.card = P - (m + 1) := fun I hI => by
    have hc := (Finset.mem_powersetCard.1 hI).2
    exact ⟨Finset.card_pos.1 (by omega), hc⟩
  -- `g u I = min_{i ∈ I} u i` (the empty set, not in `𝓕`, gets `0`); `κ u = max_{I ∈ 𝓕} g u I`
  let g : (Fin P → ℝ) → Finset (Fin P) → ℝ := fun u I => if h : I.Nonempty then I.inf' h u else 0
  have hg : ∀ u I (hI : I ∈ F), g u I = I.inf' (hFI I hI).1 u := fun u I hI =>
    dite_eq_left (hFI I hI).1
  refine ⟨fun u => F.sup' hF (g u), fun u => ?_, fun u => ?_, fun u v t huv => ?_⟩
  · -- (1): a maximizing `I` has `ℓ` indices with `κ u ≤ u i`
    obtain ⟨I, hI, hIu⟩ := Finset.exists_mem_eq_sup' hF (g u)
    refine ⟨I, by have := (hFI I hI).2; omega, fun i hi => ?_⟩
    show F.sup' hF (g u) ≤ u i
    rw [hIu, hg u I hI]
    exact Finset.inf'_le u hi
  · -- (2): otherwise `ℓ` entries `> κ u` would form `I ∈ 𝓕` with `g u I > κ u`
    refine ⟨Finset.univ.filter (fun i => u i ≤ F.sup' hF (g u)), ?_,
      fun i hi => (Finset.mem_filter.1 hi).2⟩
    by_contra hlt
    have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i => u i ≤ F.sup' hF (g u))
    rw [Finset.card_fin] at hsum
    obtain ⟨I, hIB, hIc⟩ := Finset.exists_subset_card_eq
      (s := Finset.univ.filter (fun i => ¬ u i ≤ F.sup' hF (g u))) (n := P - (m + 1)) (by omega)
    have hI : I ∈ F := Finset.mem_powersetCard.2 ⟨Finset.subset_univ I, hIc⟩
    have h1 : g u I ≤ F.sup' hF (g u) := Finset.le_sup' (g u) hI
    have h2 : F.sup' hF (g u) < g u I := by
      rw [hg u I hI, Finset.lt_inf'_iff]
      exact fun i hi => lt_of_not_ge (Finset.mem_filter.1 (hIB hi)).2
    exact absurd h1 (not_le.2 h2)
  · -- (3): each `g · I`, hence `κ`, is `1`-Lipschitz for the sup norm
    have key : ∀ u v : Fin P → ℝ, (∀ i, |u i - v i| ≤ t) →
        F.sup' hF (g u) ≤ F.sup' hF (g v) + t := by
      intro u v huv
      refine Finset.sup'_le hF (g u) fun I hI => ?_
      obtain ⟨i₀, hi₀, hv⟩ := Finset.exists_mem_eq_inf' (hFI I hI).1 v
      have h1 : g u I ≤ u i₀ := by rw [hg u I hI]; exact Finset.inf'_le u hi₀
      have h2 : g v I = v i₀ := by rw [hg v I hI]; exact hv
      have h3 : g v I ≤ F.sup' hF (g v) := Finset.le_sup' (g v) hI
      have h4 := (abs_le.1 (huv i₀)).2
      linarith
    have hvu : ∀ i, |v i - u i| ≤ t := fun i => by rw [abs_sub_comm]; exact huv i
    show |F.sup' hF (g u) - F.sup' hF (g v)| ≤ t
    rw [abs_sub_le_iff]
    constructor <;> linarith [key u v huv, key v u hvu]
/-- **Distance to `L*(a)` from an integer translate** (Simon Ch. 6, 5.4, closed-form retraction,
Claim C).  Let `|aᵢ - 1/2| < 1/4` for all `i`, and let `κ(u) ≥ uᵢ` for at least `m + 2` indices `i`
(every `u`).  If `x - y ∈ ℤᴾ` then `dist(x, L*(a)) ≤ √(m + 2) κ(r(y))`, where
`r_j(y) = max((y_j - a_j)/(1 - a_j), (a_j - y_j)/a_j)` and `L*(a)` is the set of points with at least
`m + 2` coordinates in `aᵢ + ℤ`.  As `0 < a_j, 1 - a_j ≤ 1`, `|y_j - a_j| ≤ r_j(y)`.  On a set `J`
of `m + 2` indices with `r_i(y) ≤ κ(r(y))` put `x*_i = x_i - y_i + a_i` (`i ∈ J`), `x*_i = x_i`
(`i ∉ J`); then `x* ∈ L*(a)` and `|x - x*|² = Σ_{i ∈ J} (y_i - a_i)² ≤ (m + 2) κ(r(y))²`. -/
theorem Submission.dor_lmb_fcdr_dual_dist : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, u i ≤ κ u) → ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) → infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} ≤ Real.sqrt (m + 2) * κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) := by
  intro P m a ha κ hκ x y hxy
  set u : Fin P → ℝ := fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j) with hu_def
  -- Steps 1–2: `1/4 < a_j < 3/4`, so `|y_j - a_j| ≤ r_j(y) = u j`
  have hbound : ∀ j, |y j - a j| ≤ u j := by
    intro j
    obtain ⟨h1l, h1r⟩ := abs_lt.mp (ha j)
    have ha0 : 0 < a j := by linarith
    have ha1 : 0 < 1 - a j := by linarith
    rcases le_total (a j) (y j) with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have hle : y j - a j ≤ (y j - a j) / (1 - a j) := by
        rw [le_div_iff₀ ha1]
        nlinarith
      exact hle.trans (le_max_left _ _)
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
      have hle : a j - y j ≤ (a j - y j) / a j := by
        rw [le_div_iff₀ ha0]
        nlinarith
      exact hle.trans (le_max_right _ _)
  -- Step 3: a set `J` of exactly `m + 2` indices with `|y_i - a_i| ≤ u i ≤ κ u`, so `κ u ≥ 0`
  obtain ⟨s, hs_card, hs⟩ := hκ u
  obtain ⟨J, hJs, hJcard⟩ := Finset.exists_subset_card_eq hs_card
  choose k hk using hxy
  have hJbound : ∀ i ∈ J, |y i - a i| ≤ κ u := fun i hi =>
    (hbound i).trans (hs i (hJs hi))
  have hκ_nonneg : 0 ≤ κ u := by
    have hJne : J.Nonempty := by
      rw [← Finset.card_pos, hJcard]; omega
    obtain ⟨i, hi⟩ := hJne
    exact (abs_nonneg _).trans (hJbound i hi)
  -- Step 4: the shifted point `x*` lies in `L*(a)`
  let xs : Euclid P := WithLp.toLp 2 (fun i => if i ∈ J then x i - y i + a i else x i)
  have hxs_mem : xs ∈ {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} := by
    refine ⟨J, hJcard.ge, fun i hi => ⟨k i, ?_⟩⟩
    show (if i ∈ J then x i - y i + a i else x i) - a i = k i
    rw [ite_eq_left hi, ← hk i]
    ring
  -- Step 5: `dist(x, L*(a)) ≤ |x - x*| = (Σ_{i ∈ J} (y_i - a_i)²)^{1/2} ≤ √(m + 2) κ u`
  refine (infDist_le_dist_of_mem hxs_mem).trans ?_
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (xs i) ^ 2 ≤ ((m : ℝ) + 2) * (κ u) ^ 2 := by
    have h1 : ∑ i, dist (x i) (xs i) ^ 2 = ∑ i ∈ J, dist (x i) (xs i) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ J)
      intro i _ hi
      show dist (x i) (if i ∈ J then x i - y i + a i else x i) ^ 2 = 0
      rw [ite_eq_right hi, dist_self]
      ring
    rw [h1]
    have h2 : ∑ i ∈ J, dist (x i) (xs i) ^ 2 ≤ J.card • (κ u ^ 2) := by
      apply Finset.sum_le_card_nsmul
      intro i hi
      show dist (x i) (if i ∈ J then x i - y i + a i else x i) ^ 2 ≤ κ u ^ 2
      rw [ite_eq_left hi, Real.dist_eq]
      have hxy' : x i - (x i - y i + a i) = y i - a i := by ring
      rw [hxy']
      exact pow_le_pow_left₀ (abs_nonneg _) (hJbound i hi) 2
    rw [hJcard, nsmul_eq_mul] at h2
    push_cast at h2
    exact h2
  calc Real.sqrt (∑ i, dist (x i) (xs i) ^ 2)
      ≤ Real.sqrt (((m : ℝ) + 2) * (κ u) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((m : ℝ) + 2) * κ u := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hκ_nonneg]
/-- **Simon Ch. 6, Lemma 5.4** (step 4(i) of the closed-form retraction): with
`r_j(y) = max((y_j − a_j)/(1 − a_j), (a_j − y_j)/a_j)` and `κ(r(y)) > 0`, the point
`Φ(y)_i = a_i + (y_i − a_i)/max(r_i(y), κ(r(y)))` lies in the cube `[0, 1]ᴾ`, and `Φ(y)_i ∈ {0, 1}`
on an index set `s` with `P ≤ m + 1 + |s|`.  As `1/4 < a_i < 3/4`, `μ_i = max(r_i(y), κ(r(y)))` is
positive and dominates `(y_i − a_i)/(1 − a_i)` and `(a_i − y_i)/a_i`, so
`−a_i ≤ (y_i − a_i)/μ_i ≤ 1 − a_i`.  On the indices with `κ(r(y)) ≤ r_i(y)` given by the hypothesis
on `κ`, `μ_i = r_i(y)` and the quotient is exactly `1 − a_i` (`y_i ≥ a_i`) or `−a_i` (`y_i < a_i`). -/
theorem Submission.dor_lmb_fcdr_cube_skeleton : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y : Euclid P, 0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) → (∀ i, 0 ≤ Φ y i ∧ Φ y i ≤ 1) ∧ ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, Φ y i = 0 ∨ Φ y i = 1 := by
  intro P m a ha κ hκ Φ hΦ y hy
  -- `|a_i − 1/2| < 1/4` gives `0 < a_i < 1`
  have ha' : ∀ i, 0 < a i ∧ a i < 1 := fun i => by
    obtain ⟨h1, h2⟩ := abs_lt.mp (ha i)
    constructor <;> linarith
  -- if `μ > 0` dominates `(z − b)/(1 − b)` and `(b − z)/b`, then `0 ≤ b + (z − b)/μ ≤ 1`
  have bounds : ∀ b z μ : ℝ, 0 < b → b < 1 → 0 < μ → (z - b) / (1 - b) ≤ μ → (b - z) / b ≤ μ →
      0 ≤ b + (z - b) / μ ∧ b + (z - b) / μ ≤ 1 := by
    intro b z μ hb0 hb1 hμ h1 h2
    rw [div_le_iff₀ (by linarith)] at h1
    rw [div_le_iff₀ hb0] at h2
    constructor
    · have : -b ≤ (z - b) / μ := by
        rw [le_div_iff₀ hμ]
        linarith
      linarith
    · have : (z - b) / μ ≤ 1 - b := by
        rw [div_le_iff₀ hμ]
        linarith
      linarith
  -- if moreover `0 < k ≤ r = max((z − b)/(1 − b), (b − z)/b)`, then `max(r, k) = r` and the
  -- coordinate is `b + (1 − b) = 1` (`z ≥ b`) or `b − b = 0` (`z < b`)
  have skel : ∀ b z k : ℝ, 0 < b → b < 1 → 0 < k → k ≤ max ((z - b) / (1 - b)) ((b - z) / b) →
      b + (z - b) / max (max ((z - b) / (1 - b)) ((b - z) / b)) k = 0 ∨
        b + (z - b) / max (max ((z - b) / (1 - b)) ((b - z) / b)) k = 1 := by
    intro b z k hb0 hb1 hk hkr
    have h1b : 0 < 1 - b := by linarith
    rw [max_eq_left hkr]
    rcases le_or_gt b z with h | h
    · right
      have e1 : (b - z) / b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hb0.le
      have e2 : 0 ≤ (z - b) / (1 - b) := div_nonneg (by linarith) h1b.le
      rw [max_eq_left (e1.trans e2)] at hkr ⊢
      have hzb : z - b ≠ 0 := by
        intro h0
        rw [h0, zero_div] at hkr
        linarith
      rw [div_div_cancel₀ hzb]
      ring
    · left
      have e1 : (z - b) / (1 - b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h1b.le
      have e2 : 0 ≤ (b - z) / b := div_nonneg (by linarith) hb0.le
      rw [max_eq_right (e1.trans e2), ← neg_sub b z, neg_div, div_div_cancel₀ (sub_pos.mpr h).ne']
      ring
  -- `μ_i = max(r_i(y), κ(r(y))) ≥ κ(r(y)) > 0` dominates both quotients in `r_i(y)`
  refine ⟨fun i => ?_, ?_⟩
  · rw [hΦ y i]
    exact bounds (a i) (y i) _ (ha' i).1 (ha' i).2 (hy.trans_le (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
  · -- the indices with `κ(r(y)) ≤ r_i(y)` land on a face: `Φ(y)_i ∈ {0, 1}`
    obtain ⟨s, hs, hsκ⟩ := hκ fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)
    refine ⟨s, hs, fun i hi => ?_⟩
    rw [hΦ y i]
    exact skel (a i) (y i) _ (ha' i).1 (ha' i).2 hy (hsκ i hi)
/-- **Simon Ch. 6, Lemma 5.4** (retraction onto the `n`-skeleton), integer-translation
compatibility of the cube map `Φ(y)ᵢ = aᵢ + (yᵢ − aᵢ)/max(rᵢ(y), κ(r(y)))`, where
`rⱼ(y) = max((yⱼ − aⱼ)/(1 − aⱼ), (aⱼ − yⱼ)/aⱼ)`: if `y, y' ∈ [0, 1]ᴾ` and `y' − y ∈ ℤᴾ`, then
`Φ(y') = Φ(y) + (y' − y)`.  Each coordinate has `y'ⱼ = yⱼ` or `{yⱼ, y'ⱼ} = {0, 1}`, where
`rⱼ = 1`; so `r(y') = r(y)`, `κ(r(y)) ≤ rᵢ₀(y) ≤ 1` for some `i₀` (as `m + 1 < P`), and `Φ` is the
identity on the moved coordinates. -/
theorem Submission.dor_lmb_fcdr_cube_periodic : ∀ (P m : ℕ), m + 1 < P → ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u : Fin P → ℝ, ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, κ u ≤ u i) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y y' : Euclid P, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → (∀ i, ∃ k : ℤ, y' i - y i = k) → ∀ i, Φ y' i = Φ y i + (y' i - y i) := by
  intro P m hmP a ha κ hκ Φ hΦ y y' hy hy' hint i
  -- `0 < aⱼ < 1`
  have ha0 : ∀ j, 0 < a j := fun j => by linarith [(abs_lt.mp (ha j)).1]
  have ha1 : ∀ j, 0 < 1 - a j := fun j => by linarith [(abs_lt.mp (ha j)).2]
  -- `ρⱼ(t) = max((t − aⱼ)/(1 − aⱼ), (aⱼ − t)/aⱼ)` has `ρⱼ(0) = ρⱼ(1) = 1` and `ρⱼ ≤ 1` on `[0, 1]`
  have hρ0 : ∀ j, max ((0 - a j) / (1 - a j)) ((a j - 0) / a j) = 1 := fun j => by
    rw [sub_zero, div_self (ha0 j).ne']
    exact max_eq_right ((div_le_one (ha1 j)).mpr (by linarith))
  have hρ1 : ∀ j, max ((1 - a j) / (1 - a j)) ((a j - 1) / a j) = 1 := fun j => by
    rw [div_self (ha1 j).ne']
    exact max_eq_left ((div_le_one (ha0 j)).mpr (by linarith))
  have hρle : ∀ j, max ((y j - a j) / (1 - a j)) ((a j - y j) / a j) ≤ 1 := fun j =>
    max_le ((div_le_one (ha1 j)).mpr (by linarith [(hy j).2]))
      ((div_le_one (ha0 j)).mpr (by linarith [(hy j).1]))
  -- `y'ⱼ − yⱼ ∈ ℤ ∩ [−1, 1]`, so `y'ⱼ = yⱼ` or `{yⱼ, y'ⱼ} = {0, 1}`
  have hcase : ∀ j, y' j = y j ∨ (y j = 0 ∧ y' j = 1) ∨ (y j = 1 ∧ y' j = 0) := by
    intro j
    obtain ⟨k, hk⟩ := hint j
    obtain ⟨h₀, h₁⟩ := hy j
    obtain ⟨h₀', h₁'⟩ := hy' j
    have hk1 : k ≤ 1 := by
      have : (k : ℝ) ≤ 1 := by linarith
      exact_mod_cast this
    have hk2 : -1 ≤ k := by
      have : (-1 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    rcases (show k = -1 ∨ k = 0 ∨ k = 1 by omega) with rfl | rfl | rfl <;> push_cast at hk
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  -- hence `r(y') = r(y)` and `κ(r(y')) = κ(r(y))`
  have hr : ∀ j, max ((y' j - a j) / (1 - a j)) ((a j - y' j) / a j)
      = max ((y j - a j) / (1 - a j)) ((a j - y j) / a j) := by
    intro j
    rcases hcase j with h | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h]
    · rw [h0, h1, hρ0 j, hρ1 j]
    · rw [h0, h1, hρ0 j, hρ1 j]
  have hκeq : κ (fun j => max ((y' j - a j) / (1 - a j)) ((a j - y' j) / a j))
      = κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) :=
    congrArg κ (funext hr)
  -- `κ(r(y)) ≤ 1`: `s` is nonempty as `P ≤ m + 1 + |s|` and `m + 1 < P`
  have hκle : κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) ≤ 1 := by
    obtain ⟨s, hs, hsκ⟩ := hκ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i₀, hi₀⟩ := hne
    exact (hsκ i₀ hi₀).trans (hρle i₀)
  -- coordinates with `y'ᵢ = yᵢ` agree; on `{yᵢ, y'ᵢ} = {0, 1}`, `max(rᵢ, κ) = 1` and `Φ` fixes `yᵢ`
  rw [hΦ y' i, hΦ y i, hκeq, hr i]
  rcases hcase i with h | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h]
    ring
  · rw [h0, h1, hρ0 i, max_eq_left hκle]
    ring
  · rw [h0, h1, hρ1 i, max_eq_left hκle]
    ring
/-- **Claim B** (Simon Ch. 6, Lemma 5.4, step 6 of the corrected closed-form proof: Lipschitz bound
for the cube retraction `Φ`).  Let `|aᵢ − 1/2| < 1/4`, let `κ` be `1`-Lipschitz for the sup norm,
`rⱼ(y) = max((yⱼ − aⱼ)/(1 − aⱼ), (aⱼ − yⱼ)/aⱼ)` and `Φ(y)ᵢ = aᵢ + (yᵢ − aᵢ)/max(rᵢ(y), κ(r(y)))`.
If `κ(r(y)) > 0` then `|Φ(y) − Φ(y')| ≤ 4√P |y − y'| / κ(r(y))`: each `rⱼ` is `4`-Lipschitz, so the
denominators `μ = max(rᵢ(y), κ(r(y)))` and `μ'` differ by at most `4|y − y'|`; `|y'ᵢ − aᵢ| ≤ (3/4)μ'`,
and `u/μ − u'/μ' = (u − u')/μ + (u'/μ')(μ' − μ)/μ` bounds each coordinate by
`4|y − y'|/κ(r(y))`. -/
theorem Submission.dor_lmb_fcdr_cube_lipschitz : ∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ κ : (Fin P → ℝ) → ℝ, (∀ u v : Fin P → ℝ, ∀ t : ℝ, (∀ i, |u i - v i| ≤ t) → |κ u - κ v| ≤ t) → ∀ Φ : Euclid P → Euclid P, (∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) / max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i)) (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))) → ∀ y y' : Euclid P, 0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) → dist (Φ y) (Φ y') ≤ 4 * Real.sqrt P / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) * dist y y' := by
  intro P a ha κ hκ Φ hΦ y y' hk
  -- Step 1: `1/4 < aᵢ < 3/4`, and `|yⱼ − y'ⱼ| ≤ dist y y'`
  have a_bounds : ∀ c : ℝ, |c - 1 / 2| < 1 / 4 → 1 / 4 < c ∧ c < 3 / 4 := fun c hc => by
    rcases abs_lt.mp hc with ⟨h1, h2⟩
    constructor <;> linarith
  have hcoord : ∀ j, |y j - y' j| ≤ dist y y' := fun j => by
    have := PiLp.dist_apply_le y y' j
    rwa [Real.dist_eq] at this
  -- Step 2: `rⱼ` is `4`-Lipschitz in `yⱼ`, so `|κ(r(y)) − κ(r(y'))| ≤ 4 dist y y'`
  have div_lip : ∀ s x x' δ : ℝ, 1 / 4 < s → |x - x'| ≤ δ → |x / s - x' / s| ≤ 4 * δ := by
    intro s x x' δ hs h
    have hs0 : (0 : ℝ) < s := by linarith
    have hδ : 0 ≤ δ := le_trans (abs_nonneg _) h
    rw [← sub_div, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    nlinarith [mul_nonneg hδ (by linarith : (0 : ℝ) ≤ 4 * s - 1)]
  have r_lip : ∀ c b b' δ : ℝ, |c - 1 / 2| < 1 / 4 → |b - b'| ≤ δ →
      |max ((b - c) / (1 - c)) ((c - b) / c) - max ((b' - c) / (1 - c)) ((c - b') / c)|
        ≤ 4 * δ := by
    intro c b b' δ hc h
    obtain ⟨hc1, hc2⟩ := a_bounds c hc
    refine le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le ?_ ?_)
    · apply div_lip _ _ _ _ (by linarith)
      rwa [sub_sub_sub_cancel_right]
    · apply div_lip _ _ _ _ hc1
      rw [sub_sub_sub_cancel_left, abs_sub_comm]
      exact h
  have hkk : |κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))
      - κ (fun j => max ((y' j - a j) / (1 - a j)) ((a j - y' j) / a j))| ≤ 4 * dist y y' :=
    hκ _ _ _ (fun j => r_lip _ _ _ _ (ha j) (hcoord j))
  -- Step 3: `|b − c| ≤ (3/4) r(b)`; in particular `r(b) ≥ 0`, and `r(b) = 0` forces `b = c`
  have abs_le_r : ∀ c b : ℝ, |c - 1 / 2| < 1 / 4 →
      |b - c| ≤ 3 / 4 * max ((b - c) / (1 - c)) ((c - b) / c) := by
    intro c b hc
    obtain ⟨hc1, hc2⟩ := a_bounds c hc
    have h1c : (0 : ℝ) < 1 - c := by linarith
    have hc0 : (0 : ℝ) < c := by linarith
    rcases le_total c b with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have hq : 0 ≤ (b - c) / (1 - c) := div_nonneg (sub_nonneg.mpr h) h1c.le
      have he : (b - c) / (1 - c) * (1 - c) = b - c := div_mul_cancel₀ _ h1c.ne'
      have hm := le_max_left ((b - c) / (1 - c)) ((c - b) / c)
      nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ c - 1 / 4)]
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      have hq : 0 ≤ (c - b) / c := div_nonneg (sub_nonneg.mpr h) hc0.le
      have he : (c - b) / c * c = c - b := div_mul_cancel₀ _ hc0.ne'
      have hm := le_max_right ((b - c) / (1 - c)) ((c - b) / c)
      nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ 3 / 4 - c)]
  -- Step 4: `|u/μ − u'/μ'| ≤ 4δ/μ`
  have key : ∀ u u' μ μ' δ : ℝ, 0 < μ → 0 ≤ μ' → |u'| ≤ 3 / 4 * μ' → |u - u'| ≤ δ →
      |μ - μ'| ≤ 4 * δ → |u / μ - u' / μ'| ≤ 4 * δ / μ := by
    intro u u' μ μ' δ hμ hμ'0 hu' huu hμμ
    have hX : u / μ * μ = u := div_mul_cancel₀ u hμ.ne'
    have hX' : u' / μ' * μ' = u' ∧ |u' / μ'| ≤ 3 / 4 := by
      rcases hμ'0.eq_or_lt with h | h
      · -- (b) `μ' = 0` forces `u' = 0`
        subst h
        have hu0 : u' = 0 := abs_nonpos_iff.mp (by linarith)
        subst hu0
        norm_num
      · -- (a) `μ' > 0` gives `|u'|/μ' ≤ 3/4`
        refine ⟨div_mul_cancel₀ u' h.ne', ?_⟩
        rw [abs_div, abs_of_pos h, div_le_iff₀ h]
        exact hu'
    rw [le_div_iff₀ hμ]
    have hsplit : (u / μ - u' / μ') * μ = (u - u') - u' / μ' * (μ - μ') := by
      linear_combination hX - hX'.1
    have habs : |u / μ - u' / μ'| * μ = |(u / μ - u' / μ') * μ| := by
      rw [abs_mul, abs_of_pos hμ]
    rw [habs, hsplit]
    have h1 : |u' / μ' * (μ - μ')| ≤ 3 / 4 * (4 * δ) := by
      rw [abs_mul]
      exact mul_le_mul hX'.2 hμμ (abs_nonneg _) (by norm_num)
    have h2 := abs_le.mp h1
    have h3 := abs_le.mp huu
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
  -- Steps 3–5 for one coordinate: `|Φ(y)ᵢ − Φ(y')ᵢ| ≤ 4δ/κ(r(y))`
  have coord_bound : ∀ c b b' k k' δ : ℝ, |c - 1 / 2| < 1 / 4 → 0 < k → |b - b'| ≤ δ →
      |k - k'| ≤ 4 * δ →
      |(c + (b - c) / max (max ((b - c) / (1 - c)) ((c - b) / c)) k) -
        (c + (b' - c) / max (max ((b' - c) / (1 - c)) ((c - b') / c)) k')| ≤ 4 * δ / k := by
    intro c b b' k k' δ hc hk hbb hkk
    have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hbb
    have hr' : |b' - c| ≤ 3 / 4 * max ((b' - c) / (1 - c)) ((c - b') / c) := abs_le_r c b' hc
    have hr'0 : 0 ≤ max ((b' - c) / (1 - c)) ((c - b') / c) := by
      have := abs_nonneg (b' - c)
      linarith
    have hμk : k ≤ max (max ((b - c) / (1 - c)) ((c - b) / c)) k := le_max_right _ _
    have hμ : 0 < max (max ((b - c) / (1 - c)) ((c - b) / c)) k := lt_of_lt_of_le hk hμk
    have hμ' : max ((b' - c) / (1 - c)) ((c - b') / c)
        ≤ max (max ((b' - c) / (1 - c)) ((c - b') / c)) k' := le_max_left _ _
    have huu : |(b - c) - (b' - c)| ≤ δ := by
      rw [sub_sub_sub_cancel_right]
      exact hbb
    have hμμ : |max (max ((b - c) / (1 - c)) ((c - b) / c)) k
        - max (max ((b' - c) / (1 - c)) ((c - b') / c)) k'| ≤ 4 * δ :=
      le_trans (abs_max_sub_max_le_max _ _ _ _) (max_le (r_lip c b b' δ hc hbb) hkk)
    have hu' : |b' - c| ≤ 3 / 4 * max (max ((b' - c) / (1 - c)) ((c - b') / c)) k' := by
      linarith
    rw [add_sub_add_left_eq_sub]
    exact le_trans (key _ _ _ _ _ hμ (le_trans hr'0 hμ') hu' huu hμμ)
      (div_le_div_of_nonneg_left (by linarith) hk hμk)
  have hi : ∀ i, |Φ y i - Φ y' i|
      ≤ 4 * dist y y' / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) := by
    intro i
    rw [hΦ y i, hΦ y' i]
    exact coord_bound _ _ _ _ _ _ (ha i) hk (hcoord i) hkk
  -- Step 5: sum the squares over the `P` coordinates
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i, dist (Φ y i) (Φ y' i) ^ 2)
      ≤ Real.sqrt (∑ _i : Fin P,
          (4 * dist y y' / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))) ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro i _
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (hi i) 2
    _ = 4 * Real.sqrt P / κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))
          * dist y y' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _),
          Real.sqrt_sq (div_nonneg (by positivity) hk.le)]
        ring
/-- **Lipschitz on every closed unit grid cube implies Lipschitz along segments** (Simon Ch. 6,
5.4, closed-form retraction, step 7(i)).  If `|f x − f y| ≤ K |x − y|` whenever `x, y ∈ S` lie in
a common closed cube `z + [0, 1]ᴾ` (`z ∈ ℤᴾ`), then `|f x − f y| ≤ K |x − y|` whenever
`[x, y] ⊆ S`.  With `γ(t) = x + t (y − x)`, the parameters `t ∈ [0, 1]` at which a non-constant
coordinate `γᵢ(t)` is an integer, together with `0` and `1`, are finitely many,
`0 = t₀ < ⋯ < t_N = 1`.  Between consecutive breakpoints no coordinate crosses an integer, so
`γ(t_k)` and `γ(t_{k+1})` lie in the cube `⌊γ(s)⌋ + [0, 1]ᴾ`, `s = (t_k + t_{k+1})/2`; the cube
estimates `K (t_{k+1} − t_k) |x − y|` telescope along the triangle inequality to `K |x − y|`. -/
theorem Submission.dor_lmb_fcdr_grid_segment : ∀ (P : ℕ) (f : Euclid P → Euclid P) (S : Set (Euclid P)) (K : ℝ), 0 ≤ K → (∀ (z : Fin P → ℤ) (x y : Euclid P), x ∈ S → y ∈ S → (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) → (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) → dist (f x) (f y) ≤ K * dist x y) → ∀ x y : Euclid P, segment ℝ x y ⊆ S → dist (f x) (f y) ≤ K * dist x y := by
  intro P f S K hK hcube x y hseg
  -- Step 1: `γ t = x + t (y − x)`, `t ∈ [0, 1]`, parametrises `[x, y] ⊆ S`, and
  -- `|γ a − γ b| = |a − b| |x − y|`
  let γ : ℝ → Euclid P := fun t => x + t • (y - x)
  have hγi : ∀ t i, γ t i = x i + t * (y i - x i) := fun t i => by simp [γ]
  have hγS : ∀ t, 0 ≤ t → t ≤ 1 → γ t ∈ S := fun t h0 h1 =>
    hseg (by rw [segment_eq_image']; exact ⟨t, ⟨h0, h1⟩, rfl⟩)
  have hγdist : ∀ a b, dist (γ a) (γ b) = |a - b| * dist x y := by
    intro a b
    have h : γ a - γ b = (a - b) • (y - x) := by
      simp only [γ]; rw [add_sub_add_left_eq_sub, sub_smul]
    rw [dist_eq_norm (γ a) (γ b), h, norm_smul, Real.norm_eq_abs, ← dist_eq_norm y x,
      dist_comm y x]
  have hγ0 : γ 0 = x := by simp [γ]
  have hγ1 : γ 1 = y := by simp [γ]
  -- Step 2: the breakpoints `T ⊆ [0, 1]`: `0`, `1` and every `t` with `γᵢ(t) = m ∈ ℤ`,
  -- `xᵢ ≠ yᵢ`, i.e. `t = (m − xᵢ)/(yᵢ − xᵢ)` with `m ∈ [⌊min(xᵢ, yᵢ)⌋, ⌈max(xᵢ, yᵢ)⌉]` (for
  -- `xᵢ = yᵢ` this quotient is `0 ∈ T`) ...
  let B : Finset ℝ := Finset.univ.biUnion fun i : Fin P =>
    (Finset.Icc ⌊min (x i) (y i)⌋ ⌈max (x i) (y i)⌉).image fun m : ℤ =>
      ((m : ℝ) - x i) / (y i - x i)
  let T : Finset ℝ := (insert 0 (insert 1 B)).filter fun t => 0 ≤ t ∧ t ≤ 1
  have hmemT : ∀ u, u ∈ T ↔ (u = 0 ∨ u = 1 ∨ u ∈ B) ∧ 0 ≤ u ∧ u ≤ 1 := fun u =>
    Finset.mem_filter.trans <|
      and_congr_left' (Finset.mem_insert.trans (or_congr_right Finset.mem_insert))
  have hmemB : ∀ (i : Fin P) (m : ℤ), min (x i) (y i) < m → (m : ℝ) < max (x i) (y i) →
      ((m : ℝ) - x i) / (y i - x i) ∈ B := fun i m h1 h2 =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2 ⟨m,
      Finset.mem_Icc.2 ⟨Int.floor_le_iff.2 (by linarith), Int.le_ceil_iff.2 (by linarith)⟩, rfl⟩⟩
  have hT : ∀ u ∈ T, 0 ≤ u ∧ u ≤ 1 := fun u hu => ((hmemT u).1 hu).2
  have h0T : (0 : ℝ) ∈ T := (hmemT 0).2 ⟨Or.inl rfl, le_rfl, zero_le_one⟩
  have h1T : (1 : ℝ) ∈ T := (hmemT 1).2 ⟨Or.inr (Or.inl rfl), zero_le_one, le_rfl⟩
  -- ... listed increasingly as `0 = t 0 < t 1 < ⋯ < t N = 1`, `N = card T − 1`
  have hcard : 2 ≤ T.card := by
    have h := Finset.card_le_card (show ({0, 1} : Finset ℝ) ⊆ T by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact h0T
      · rw [Finset.mem_singleton.1 hu]; exact h1T)
    rwa [Finset.card_pair zero_ne_one] at h
  let e := T.orderEmbOfFin rfl
  let t : ℕ → ℝ := fun k => if h : k < T.card then e ⟨k, h⟩ else 1
  let N := T.card - 1
  have h0 : 0 < T.card := lt_of_lt_of_le two_pos hcard
  have hNlt : N < T.card := Nat.sub_lt h0 one_pos
  have ht0 : t 0 = 0 := by
    have : t 0 = e ⟨0, h0⟩ := dite_eq_left h0
    rw [this, Finset.orderEmbOfFin_zero rfl h0]
    exact le_antisymm (Finset.min'_le T 0 h0T) (Finset.le_min' T _ 0 fun u hu => (hT u hu).1)
  have htN : t N = 1 := by
    have : t N = e ⟨T.card - 1, hNlt⟩ := dite_eq_left hNlt
    rw [this, Finset.orderEmbOfFin_last rfl h0]
    exact le_antisymm (Finset.max'_le T _ 1 fun u hu => (hT u hu).2) (Finset.le_max' T 1 h1T)
  -- `t k < t (k + 1)` are consecutive breakpoints
  have hstep : ∀ k < N, t k ∈ T ∧ t (k + 1) ∈ T ∧ t k < t (k + 1) ∧
      ∀ u ∈ T, ¬(t k < u ∧ u < t (k + 1)) := by
    intro k hk
    have hk1 : k < T.card := hk.trans hNlt
    have hk2 : k + 1 < T.card := Nat.add_lt_of_lt_sub hk
    have htk : t k = e ⟨k, hk1⟩ := dite_eq_left hk1
    have htk' : t (k + 1) = e ⟨k + 1, hk2⟩ := dite_eq_left hk2
    rw [htk, htk']
    refine ⟨T.orderEmbOfFin_mem rfl _, T.orderEmbOfFin_mem rfl _,
      e.strictMono (Fin.mk_lt_mk.2 k.lt_succ_self), ?_⟩
    rintro u hu ⟨h1, h2⟩
    have hu' : u ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hu
    obtain ⟨j, rfl⟩ := hu'
    have h1' : k < j.val := Fin.lt_def.1 (e.lt_iff_lt.1 h1)
    have h2' : j.val < k + 1 := Fin.lt_def.1 (e.lt_iff_lt.1 h2)
    exact absurd h1' (not_lt.2 (Nat.lt_add_one_iff.1 h2'))
  -- Step 3: if no breakpoint lies strictly between `a < b`, no coordinate of `γ` passes strictly
  -- across an integer `m` on `[a, b]`: otherwise `(m − xᵢ)/(yᵢ − xᵢ)` would be such a breakpoint
  have hcross : ∀ a b, 0 ≤ a → b ≤ 1 → a < b → (∀ u ∈ T, ¬(a < u ∧ u < b)) →
      ∀ (i : Fin P) (m : ℤ), ¬(γ a i < m ∧ (m : ℝ) < γ b i) ∧ ¬(γ b i < m ∧ (m : ℝ) < γ a i) := by
    intro a b ha hb hab hgap i m
    have hbreak : a < ((m : ℝ) - x i) / (y i - x i) → ((m : ℝ) - x i) / (y i - x i) < b →
        min (x i) (y i) < m → (m : ℝ) < max (x i) (y i) → False := fun h1 h2 h3 h4 =>
      hgap _ ((hmemT _).2 ⟨Or.inr (Or.inr (hmemB i m h3 h4)), by linarith, by linarith⟩) ⟨h1, h2⟩
    simp only [hγi]
    constructor
    · rintro ⟨h1, h2⟩
      have hd : 0 < y i - x i := not_le.1 fun hd =>
        by linarith [mul_le_mul_of_nonpos_right hab.le hd]
      exact hbreak ((lt_div_iff₀ hd).2 (by linarith)) ((div_lt_iff₀ hd).2 (by linarith))
        (by linarith [min_le_left (x i) (y i), mul_nonneg ha hd.le])
        (by linarith [le_max_right (x i) (y i), mul_le_of_le_one_left hd.le hb])
    · rintro ⟨h1, h2⟩
      have hd : y i - x i < 0 := not_le.1 fun hd =>
        by linarith [mul_le_mul_of_nonneg_right hab.le hd]
      exact hbreak ((lt_div_iff_of_neg hd).2 (by linarith)) ((div_lt_iff_of_neg hd).2 (by linarith))
        (by linarith [min_le_right (x i) (y i), mul_nonneg (sub_nonneg.2 hb) (neg_nonneg.2 hd.le)])
        (by linarith [le_max_left (x i) (y i), mul_nonneg ha (neg_nonneg.2 hd.le)])
  -- Steps 3–4: each piece `γ(t k), γ(t (k + 1))` lies in the closed cube `z + [0, 1]ᴾ`,
  -- `z = ⌊γ(midpoint)⌋`, so the cube estimate bounds it by `K (t (k + 1) − t k) |x − y|`
  have key : ∀ k < N,
      dist (f (γ (t k))) (f (γ (t (k + 1)))) ≤ K * dist x y * (t (k + 1) - t k) := by
    intro k hk
    obtain ⟨haT, hbT, hab, hgap⟩ := hstep k hk
    set a := t k
    set b := t (k + 1)
    obtain ⟨ha0, ha1⟩ := hT a haT
    obtain ⟨hb0, hb1⟩ := hT b hbT
    let z : Fin P → ℤ := fun i => ⌊γ ((a + b) / 2) i⌋
    have hz : ∀ i, ((z i : ℝ) ≤ γ a i ∧ γ a i ≤ z i + 1) ∧
        ((z i : ℝ) ≤ γ b i ∧ γ b i ≤ z i + 1) := by
      intro i
      have hmid : γ ((a + b) / 2) i = (γ a i + γ b i) / 2 := by rw [hγi, hγi, hγi]; ring
      have hz1 : (z i : ℝ) ≤ (γ a i + γ b i) / 2 := hmid ▸ Int.floor_le _
      have hz2 : (γ a i + γ b i) / 2 < z i + 1 := hmid ▸ Int.lt_floor_add_one _
      obtain ⟨hc1, hc2⟩ := hcross a b ha0 hb1 hab hgap i (z i)
      obtain ⟨hd1, hd2⟩ := hcross a b ha0 hb1 hab hgap i (z i + 1)
      rw [Int.cast_add, Int.cast_one] at hd1 hd2
      exact ⟨⟨not_lt.1 fun h => hc1 ⟨h, by linarith⟩, not_lt.1 fun h => hd2 ⟨by linarith, h⟩⟩,
        not_lt.1 fun h => hc2 ⟨h, by linarith⟩, not_lt.1 fun h => hd1 ⟨by linarith, h⟩⟩
    calc dist (f (γ a)) (f (γ b)) ≤ K * dist (γ a) (γ b) :=
          hcube z (γ a) (γ b) (hγS a ha0 ha1) (hγS b hb0 hb1) (fun i => (hz i).1) fun i => (hz i).2
      _ = K * dist x y * (b - a) := by
          rw [hγdist, abs_sub_comm, abs_of_pos (sub_pos.2 hab)]; ring
  -- Step 5: triangle inequality along `γ(t 0), …, γ(t N)`, then telescoping
  calc dist (f x) (f y) = dist (f (γ (t 0))) (f (γ (t N))) := by rw [ht0, htN, hγ0, hγ1]
    _ ≤ ∑ k ∈ Finset.range N, dist (f (γ (t k))) (f (γ (t (k + 1)))) :=
        dist_le_range_sum_dist (fun k => f (γ (t k))) N
    _ ≤ ∑ k ∈ Finset.range N, K * dist x y * (t (k + 1) - t k) :=
        Finset.sum_le_sum fun k hk => key k (Finset.mem_range.1 hk)
    _ = K * dist x y * (t N - t 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ = K * dist x y := by rw [ht0, htN]; ring
/-- **Simon Ch. 6, Lemma 5.4** (retraction onto the `n`-skeleton, `n = m + 1 < P`; the printed
construction, with the derivative bound proved directly).  Let `|aᵢ − 1/2| < 1/4`, `L*(a)` the set
of points with at least `m + 2` coordinates in `aᵢ + ℤ`, `rⱼ(y) = max((yⱼ − aⱼ)/(1 − aⱼ),
(aⱼ − yⱼ)/aⱼ)`, `κ` the `ℓ`-th largest entry (`ℓ = P − (m + 1)`),
`Φ(y)ᵢ = aᵢ + (yᵢ − aᵢ)/max(rᵢ(y), κ(r(y)))` the closed form of the composed radial retractions of
`[0, 1]ᴾ`, and `ψ(x) = ⌊x⌋ + Φ(x − ⌊x⌋)`.  Off `L*(a)`, `κ(r(x − ⌊x⌋)) > 0` (Claim C), so `ψ(x)`
has `ℓ` integer coordinates and `|ψ(x) − x| ≤ √P`.  On a grid cube `z + [0, 1]ᴾ`,
`ψ = z + Φ(· − z)` by periodicity, and Claims B and C bound its Lipschitz constant on
`{dist(·, L*(a)) ≥ r/2}` by `4√P/κ ≤ 2c₁/r`, `c₁ = 4√P √(m + 2)`.  If `|x − y| < r`, the segment
`[x, y]` stays in `{dist(·, L*(a)) ≥ r/2}` and cutting it at the grid gives `(2c₁/r)|x − y|`; if
`|x − y| ≥ r`, then `|ψ(x) − ψ(y)| ≤ |x − y| + 2√P ≤ ((1/4 + 2√P)/r)|x − y|`.  So
`c = 2c₁ + 2√P + 1/4` works. -/
theorem Submission.dor_lmb_fcd_retraction : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y := by
  intro P m hmP
  -- Step 2: `κ`, the `ℓ`-th largest entry, `ℓ = P − (m + 1)`
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := Submission.dor_lmb_fcdr_order_stat P m hmP
  -- `c = 2c₁ + 2√P + 1/4 ≥ max(2c₁, 1/4 + 2√P)`, `c₁ = 4√P √(m + 2)`
  refine ⟨8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4, by positivity,
    fun a ha => ?_⟩
  set L : Set (Euclid P) := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
    ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  have hsP := Real.sqrt_nonneg (P : ℝ)
  have hsm := Real.sqrt_nonneg ((m : ℝ) + 2)
  -- Step 3: the closed-form cube map `Φ`
  let Φ : Euclid P → Euclid P := fun y => WithLp.toLp 2 fun i => a i + (y i - a i) /
    max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i))
      (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)))
  have hΦ : ∀ (y : Euclid P) (i : Fin P), Φ y i = a i + (y i - a i) /
      max (max ((y i - a i) / (1 - a i)) ((a i - y i) / a i))
        (κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j))) := fun _ _ => rfl
  -- integer points `z ∈ ℤᴾ` of `ℝᴾ`, and Step 5: `ψ(x) = ⌊x⌋ + Φ(x − ⌊x⌋)`
  let zv : (Fin P → ℤ) → Euclid P := fun z => WithLp.toLp 2 fun i => (z i : ℝ)
  let ψ : Euclid P → Euclid P := fun x => zv (fun j => ⌊x j⌋) + Φ (x - zv (fun j => ⌊x j⌋))
  have hψ : ∀ x i, ψ x i = ⌊x i⌋ + Φ (x - zv (fun j => ⌊x j⌋)) i := fun _ _ => rfl
  have hint : ∀ (z : Fin P → ℤ) (x : Euclid P) (i : Fin P), ∃ k : ℤ, x i - (x - zv z) i = k :=
    fun z x i => ⟨z i, show x i - (x i - z i) = z i by ring⟩
  -- Claim C: `dist(x, L*(a)) ≤ √(m + 2) κ(r(y))` if `x − y ∈ ℤᴾ`; so `κ(r(y)) > 0` off `L*(a)`
  have hdual : ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) →
      infDist x L ≤ Real.sqrt (m + 2) *
        κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) :=
    Submission.dor_lmb_fcdr_dual_dist P m a ha κ hκ2
  have hκpos : ∀ x y : Euclid P, (∀ i, ∃ k : ℤ, x i - y i = k) → 0 < infDist x L →
      0 < κ (fun j => max ((y j - a j) / (1 - a j)) ((a j - y j) / a j)) := by
    intro x y hxy hx
    by_contra hneg
    have h := mul_nonpos_of_nonneg_of_nonpos hsm (not_lt.1 hneg)
    linarith [hdual x y hxy]
  -- Step 5: on a grid cube `z + [0, 1]ᴾ`, `ψ = z + Φ(· − z)` (periodicity of `Φ`)
  have hψcube : ∀ (z : Fin P → ℤ) (x : Euclid P), (∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) →
      ψ x = zv z + Φ (x - zv z) := by
    intro z x hx
    have hper := Submission.dor_lmb_fcdr_cube_periodic P m hmP a ha κ hκ1 Φ hΦ
      (x - zv (fun j => ⌊x j⌋)) (x - zv z)
      (fun j => show 0 ≤ x j - ⌊x j⌋ ∧ x j - ⌊x j⌋ ≤ 1 from
        ⟨by linarith [Int.floor_le (x j)], by linarith [Int.lt_floor_add_one (x j)]⟩)
      (fun j => show 0 ≤ x j - z j ∧ x j - z j ≤ 1 from
        ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩)
      (fun j => ⟨⌊x j⌋ - z j, show (x j - z j) - (x j - ⌊x j⌋) = ((⌊x j⌋ - z j : ℤ) : ℝ) by
        push_cast; ring⟩)
    ext i
    show (⌊x i⌋ : ℝ) + Φ (x - zv (fun j => ⌊x j⌋)) i = z i + Φ (x - zv z) i
    rw [hper i]
    show (⌊x i⌋ : ℝ) + Φ (x - zv (fun j => ⌊x j⌋)) i
      = z i + (Φ (x - zv (fun j => ⌊x j⌋)) i + ((x i - z i) - (x i - ⌊x i⌋)))
    ring
  -- Step 5: the first conclusion
  have hfirst : ∀ x : Euclid P, 0 < infDist x L →
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧
        dist (ψ x) x ≤ Real.sqrt P := by
    intro x hx
    obtain ⟨h01, s, hs, hs01⟩ := Submission.dor_lmb_fcdr_cube_skeleton P m a ha κ hκ1 Φ hΦ
      (x - zv (fun j => ⌊x j⌋)) (hκpos x _ (hint _ x) hx)
    refine ⟨⟨s, hs, fun i hi => ?_⟩, ?_⟩
    · -- `Φ(x − ⌊x⌋)ᵢ ∈ {0, 1}` on `s`
      rcases hs01 i hi with h | h
      · exact ⟨⌊x i⌋, by rw [hψ, h, add_zero]⟩
      · exact ⟨⌊x i⌋ + 1, by rw [hψ, h]; push_cast; ring⟩
    · -- `|ψ(x)ᵢ − xᵢ| = |Φ(x − ⌊x⌋)ᵢ − (xᵢ − ⌊xᵢ⌋)| ≤ 1`
      rw [EuclideanSpace.dist_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, dist (ψ x i) (x i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h1 := h01 i
            have h2 := Int.floor_le (x i)
            have h3 := Int.lt_floor_add_one (x i)
            have h5 : |ψ x i - x i| ≤ 1 := by
              rw [hψ, abs_le]
              constructor <;> linarith [h1.1, h1.2]
            rw [Real.dist_eq]
            calc |ψ x i - x i| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
              _ = 1 := one_pow 2
        _ = P := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Claims B and C on a grid cube: `|ψ(p) − ψ(q)| ≤ (4√P/κ) |p − q| ≤ (c/r) |p − q|` when
  -- `dist(p, L*(a)) ≥ r/2`
  have hcubeLip : ∀ r : ℝ, 0 < r → ∀ (z : Fin P → ℤ) (p q : Euclid P), r / 2 ≤ infDist p L →
      (∀ i, (z i : ℝ) ≤ p i ∧ p i ≤ z i + 1) → (∀ i, (z i : ℝ) ≤ q i ∧ q i ≤ z i + 1) →
      dist (ψ p) (ψ q) ≤
        (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r * dist p q := by
    intro r hr z p q hp hpz hqz
    have hk := hκpos p (p - zv z) (hint z p) (by linarith)
    have hd := hdual p (p - zv z) (hint z p)
    have hB := Submission.dor_lmb_fcdr_cube_lipschitz P a ha κ hκ3 Φ hΦ (p - zv z) (q - zv z) hk
    rw [dist_sub_right p q (zv z)] at hB
    rw [hψcube z p hpz, hψcube z q hqz, dist_add_left]
    refine hB.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
    -- `4√P/κ ≤ 8√P√(m + 2)/r ≤ c/r`, as `r ≤ 2√(m + 2) κ`
    have key : ∀ k : ℝ, 0 < k → r / 2 ≤ Real.sqrt (m + 2) * k →
        4 * Real.sqrt P / k ≤
          (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r := by
      intro k hk hrk
      rw [div_le_div_iff₀ hk hr]
      nlinarith [mul_nonneg hsP (by linarith : (0 : ℝ) ≤ 2 * (Real.sqrt (m + 2) * k) - r),
        mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt P + 1 / 4) hk.le]
    exact key _ hk (hp.trans hd)
  -- `[x, y] ⊆ ℝᴾ`: `|x − p| + |y − p| ≤ |x − y|` for `p ∈ [x, y]`
  have hseg : ∀ x y p : Euclid P, p ∈ segment ℝ x y → dist x p + dist y p ≤ dist x y := by
    intro x y p hp
    rw [segment_eq_image'] at hp
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hθ⟩ := hp
    have hθ' : x + θ • (y - x) = p := hθ
    have e1 : x - p = (-θ) • (y - x) := by rw [← hθ', neg_smul]; abel
    have e2 : y - p = (1 - θ) • (y - x) := by rw [← hθ', sub_smul, one_smul]; abel
    rw [dist_eq_norm x p, dist_eq_norm y p, e1, e2, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg hθ0, abs_of_nonneg (sub_nonneg.2 hθ1),
      dist_comm, dist_eq_norm]
    linarith
  refine ⟨ψ, hfirst, fun r hr hr4 x y hx hy => ?_⟩
  have hc0 : 0 ≤ (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r := by
    positivity
  rcases lt_or_ge (dist x y) r with hxy | hxy
  · -- Step 7(i): `|x − y| < r`, so `dist(·, L*(a)) ≥ r/2` on `[x, y]`; cut `[x, y]` at the grid
    refine Submission.dor_lmb_fcdr_grid_segment P ψ {p | r / 2 ≤ infDist p L} _ hc0
      (fun z p q hp _ hpz hqz => hcubeLip r hr z p q hp hpz hqz) x y fun p hp => ?_
    show r / 2 ≤ infDist p L
    have h1 : infDist x L ≤ infDist p L + dist x p := infDist_le_infDist_add_dist
    have h2 : infDist y L ≤ infDist p L + dist y p := infDist_le_infDist_add_dist
    linarith [hseg x y p hp]
  · -- Step 7(ii): `|x − y| ≥ r`, so `|ψ(x) − ψ(y)| ≤ |x − y| + 2√P ≤ (c/r)|x − y|`
    have h1 := (hfirst x (by linarith)).2
    have h2 := (hfirst y (by linarith)).2
    have h3 := dist_triangle4 (ψ x) x y (ψ y)
    rw [dist_comm y (ψ y)] at h3
    have hd : 0 ≤ dist x y := dist_nonneg
    calc dist (ψ x) (ψ y) ≤ dist x y + 2 * Real.sqrt P := by linarith
      _ ≤ (8 * Real.sqrt P * Real.sqrt (m + 2) + 2 * Real.sqrt P + 1 / 4) / r * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        nlinarith [mul_nonneg hsP (sub_nonneg.2 hxy),
          mul_nonneg hd (by linarith : (0 : ℝ) ≤ 1 / 4 - r), mul_nonneg (mul_nonneg hsP hsm) hd]
/-- **Tube about the shifted dual skeleton** (Simon Ch. 6, proof of 5.1, the identity before
display (6), inclusion `⊆`).  Let `L*(a)` be the set of `w` with `w_i − a_i ∈ ℤ` for at least
`m + 2` indices `i`.  It contains `a`, so `infDist x L*(a) < r` gives `w ∈ L*(a)` with
`|x − w| < r`.  Enumerate `m + 2` of the indices of `w` by `e`, and put
`z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`.  Then
`Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k (x_{e(k)} − w_{e(k)})² ≤ |x − w|² < r²`. -/
theorem Submission.dor_lmb_fcd_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
  classical
  intro P m hPm a x r hx
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- Steps 1–2: `a ∈ L*(a)` (all `P ≥ m + 2` indices), so some `w ∈ L*(a)` has `|x − w| < r`
  have hne : L.Nonempty := ⟨a, Finset.univ, by simp; omega, fun i _ => ⟨0, by simp⟩⟩
  obtain ⟨w, ⟨s, hs, hsz⟩, hxw⟩ := (infDist_lt_iff hne).1 hx
  -- Step 3: `m + 2` of the indices in `s`, enumerated injectively by `e`
  obtain ⟨J, hJs, hJ⟩ := Finset.exists_subset_card_eq hs
  let e : Fin (m + 2) → Fin P := fun k => J.orderEmbOfFin hJ k
  have he : Function.Injective e := (J.orderEmbOfFin hJ).injective
  have hes : ∀ k, e k ∈ s := fun k => hJs (J.orderEmbOfFin_mem hJ k)
  -- Step 4: `z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`
  choose z hz using fun k => hsz (e k) (hes k)
  refine ⟨e, he, z, ?_⟩
  have hterm : ∀ k, x (e k) - a (e k) - z k = x (e k) - w (e k) := fun k => by
    rw [← hz k]; ring
  -- Step 5: the `m + 2` selected squares are among the `P` nonnegative squares
  have hsub : ∑ k, (x (e k) - w (e k)) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    have := Finset.sum_map Finset.univ ⟨e, he⟩ (fun i => (x i - w i) ^ 2)
    simp only [Function.Embedding.coeFn_mk] at this
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  -- Step 6: `Σ_i (x_i − w_i)² = |x − w|²`
  have hdist : ∑ i, (x i - w i) ^ 2 = dist x w ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.dist_eq, sq_abs]
  have h0 : 0 ≤ dist x w := dist_nonneg
  -- Step 7
  calc ∑ k, (x (e k) - a (e k) - z k) ^ 2 = ∑ k, (x (e k) - w (e k)) ^ 2 := by
        simp_rw [hterm]
    _ ≤ ∑ i, (x i - w i) ^ 2 := hsub
    _ = dist x w ^ 2 := hdist
    _ < r ^ 2 := by nlinarith
/-- **Simon, Ch. 6, proof of 5.1** ((1)–(4) and the summation after them: the bad set of centres
is small).  Let `ρ` be a finite measure on `ℝᵈ` and `β > 0`.  Call a centre `g` of the open cube
`(1/4, 3/4)ᵈ` bad if `β rᵈ ρ(ℝᵈ) < ρ(O_r(g))` for some `r ∈ (0, 1/4]`, where
`O_r(g) = {y : |y − g − z| < r for some z ∈ ℤᵈ}` is the open `r`-neighbourhood of `g + ℤᵈ`.  Then
the bad set has Lebesgue measure at most `10ᵈ/β`.  Vitali's covering lemma gives bad centres `b`
with pairwise disjoint sup-metric balls `B(b, r_b)` such that the balls `B(b, 3r_b)` cover the bad
set.  The sets `O_{r_b}(b)` are then pairwise disjoint as well, so `Σ_b β r_bᵈ ≤ 1`, and the
bad set has measure at most `Σ_b (6r_b)ᵈ ≤ 6ᵈ/β`. -/
theorem Submission.dor_lmb_fcd_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)}
  -- step 1: the periodic sets `O_r(g)` are open
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- step 2: if `ρ(ℝᵈ) = 0` the bad set is empty
  by_cases h0 : ρ univ = 0
  · have : Bad = ∅ := by
      ext g
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨-, r, -, -, hr⟩
      rw [h0, mul_zero, measure_mono_null (subset_univ _) h0] at hr
      exact lt_irrefl _ hr
    rw [this, measure_empty]
    exact bot_le
  have hfin : ρ univ ≠ ∞ := measure_ne_top ρ univ
  -- step 3: a radius `r_g` for every bad centre `g`
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- step 4: Vitali's covering lemma for the balls `B(g, r_g)`, with `τ = 2`
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- step 5: `u` is countable
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- step 6: the balls `B(b, 3 r_b)`, `b ∈ u`, cover the bad set
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- step 7: the periodic sets `O_{r_b}(b)`, `b ∈ u`, are pairwise disjoint
  have hcoord : ∀ (y g : Fin d → ℝ) (r : ℝ) (z : Fin d → ℤ),
      ∑ k, (y k - g k - z k) ^ 2 < r ^ 2 → 0 < r → ∀ k, |y k - g k - z k| < r := by
    intro y g r z h hr k
    have hk : (y k - g k - z k) ^ 2 < r ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (y i - g i - z i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)) h
    exact abs_lt_of_sq_lt_sq hk hr.le
  have hOdisj : u.PairwiseDisjoint fun b => O b (rad b) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨z', hz'⟩
    have hb0 := hrad0 b (huBad hb)
    have hb'0 := hrad0 b' (huBad hb')
    have h1 := hcoord y b (rad b) z hz hb0
    have h2 := hcoord y b' (rad b') z' hz' hb'0
    have hr1 := hrad1 b (huBad hb)
    have hr2 := hrad1 b' (huBad hb')
    -- the centres lie in `(1/4, 3/4)ᵈ` and the radii are `≤ 1/4`, so the integer shifts agree
    have hzz : z = z' := by
      funext k
      have a1 := abs_lt.1 (h1 k)
      have a2 := abs_lt.1 (h2 k)
      have a3 := abs_lt.1 ((huBad hb).1 k)
      have a4 := abs_lt.1 ((huBad hb').1 k)
      have c1 : (z k : ℝ) < z' k + 1 := by linarith
      have c2 : (z' k : ℝ) < z k + 1 := by linarith
      have c1' : z k < z' k + 1 := by exact_mod_cast c1
      have c2' : z' k < z k + 1 := by exact_mod_cast c2
      omega
    subst hzz
    -- then `y − z` lies in both balls `B(b, r_b)` and `B(b', r_{b'})`
    have hv : (fun k => y k - z k) ∈ ball b (rad b) ∩ ball b' (rad b') := by
      constructor
      · rw [mem_ball, dist_pi_lt_iff hb0]
        intro k
        rw [Real.dist_eq]
        have := h1 k
        rwa [show y k - z k - b k = y k - b k - z k by ring]
      · rw [mem_ball, dist_pi_lt_iff hb'0]
        intro k
        rw [Real.dist_eq]
        have := h2 k
        rwa [show y k - z k - b' k = y k - b' k - z k by ring]
    exact (Set.disjoint_left.1 (hudisj hb hb' hne)) hv.1 hv.2
  -- step 8: `S = Σ_{b ∈ u} β r_bᵈ ≤ 1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d)
  have hSle : S ≤ 1 := by
    have hsum : S * ρ univ ≤ 1 * ρ univ := by
      calc S * ρ univ = ∑' b : u, ENNReal.ofReal (β * rad b ^ d) * ρ univ :=
            (ENNReal.tsum_mul_right).symm
        _ ≤ ∑' b : u, ρ (O b (rad b)) :=
            ENNReal.tsum_le_tsum fun b => (hradlt b (huBad b.2)).le
        _ = ρ (⋃ b ∈ u, O b (rad b)) :=
            (measure_biUnion hucount hOdisj fun b _ => (hOopen _ _).measurableSet).symm
        _ ≤ ρ univ := measure_mono (subset_univ _)
        _ = 1 * ρ univ := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left h0 hfin).1 hsum
  -- step 9: the volume estimate
  calc volume Bad ≤ volume (⋃ b ∈ u, ball b (3 * rad b)) := measure_mono hBadsub
    _ ≤ ∑' b : u, volume (ball (b : Fin d → ℝ) (3 * rad b)) := measure_biUnion_le _ hucount _
    _ = ∑' b : u, ENNReal.ofReal (6 ^ d / β) * ENNReal.ofReal (β * rad b ^ d) := by
        refine tsum_congr fun b => ?_
        have hb0 := hrad0 b (huBad b.2)
        rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (6 ^ d / β) * S := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (6 ^ d / β) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (10 ^ d / β) := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        norm_num
/-- **Simon, Ch. 6, proof of 5.1** ((5) and the choice of `a`, cube version).  If sets
`E_e ⊆ ℝ^d`, one for each map `e : Fin d → Fin P`, have total Lebesgue outer measure
`< (1/2)^P`, then some `a` in the open cube `(1/4, 3/4)^P` has `(a_{e(k)})_k ∉ E_e` for every
injective `e`.  By Fubini over the coordinates in `range e` and the rest, the centres in the cube
whose `e`-projection lies in `E_e` have volume `≤ L^d(E_e)`; the cube has volume `(1/2)^P`, so the
union bound leaves a good centre. -/
theorem Submission.dor_lmb_fcd_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
  classical
  intro P d E hsum
  -- Step 2 (Fubini): for injective `e`, the points of the cube whose `e`-projection lies in `F`
  -- have volume at most `volume F`
  have fubini : ∀ e : Fin d → Fin P, Function.Injective e → ∀ F : Set (Fin d → ℝ),
      volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ≤
        volume F := by
    intro e he F
    let p : Fin P → Prop := fun i => i ∈ range e
    let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    have hΦ : MeasurePreserving Φ := by
      convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    let σ : Fin d ≃ {i // p i} := Equiv.ofInjective e he
    let ψ := (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm
    have hψ : MeasurePreserving ψ :=
      (volume_measurePreserving_piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm _
    have hψapp : ∀ u k, ψ u k = u (σ k) := by
      intro u k
      simp [ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    let G : Set ({i // p i} → ℝ) := ψ ⁻¹' F
    let H : Set ({i // ¬ p i} → ℝ) := Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)
    have hsub : {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ⊆
        Φ ⁻¹' (G ×ˢ H) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, fun i _ => hx1 i⟩
      show ψ (fun i => x i) ∈ F
      have : ψ (fun i : {i // p i} => x i) = fun k => x (e k) := by
        funext k; rw [hψapp]; rfl
      rw [this]; exact hx2
    have hG : volume G = volume F := hψ.measure_preimage_equiv F
    have hH : volume H ≤ 1 := by
      rw [Real.volume_pi_Ioo]
      refine Finset.prod_le_one fun i _ => ?_
      rw [ENNReal.ofReal_le_one]; norm_num
    calc volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F}
        ≤ volume (Φ ⁻¹' (G ×ˢ H)) := measure_mono hsub
      _ = volume (G ×ˢ H) := hΦ.measure_preimage_equiv _
      _ = volume G * volume H := by
          rw [Measure.volume_eq_prod]; exact Measure.prod_prod G H
      _ ≤ volume G * 1 := by gcongr
      _ = volume F := by rw [mul_one, hG]
  have hI : ∀ t : ℝ, |t - 1 / 2| < 1 / 4 ↔ t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro t
    rw [abs_sub_lt_iff, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- Step 1: the open cube `Q` in `Euclid P` has volume `(1/2)^P`
  let Q : Set (Euclid P) := {a | ∀ i, a i ∈ Ioo (1 / 4 : ℝ) (3 / 4)}
  have hofLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin P)
  have hQ : volume Q = ENNReal.ofReal ((1 / 2) ^ P) := by
    have : Q = (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
        (Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext a; simp [Q, Set.mem_pi]
    rw [this, hofLp.measure_preimage_equiv, Real.volume_pi_Ioo, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  -- Step 3: the sets of centres with a bad projection
  let A : (Fin d → Fin P) → Set (Euclid P) := fun e =>
    {a | Function.Injective e ∧ a ∈ Q ∧ (fun k => a (e k)) ∈ E e}
  have hA : ∀ e, volume (A e) ≤ volume (E e) := by
    intro e
    by_cases he : Function.Injective e
    · have hsub : A e ⊆ (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
          {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ E e} := by
        rintro a ⟨-, haQ, haE⟩
        exact ⟨haQ, haE⟩
      calc volume (A e) ≤ _ := measure_mono hsub
        _ = _ := hofLp.measure_preimage_equiv _
        _ ≤ volume (E e) := fubini e he (E e)
    · have : A e = ∅ := by
        ext a; simp only [mem_empty_iff_false, iff_false]; exact fun h => he h.1
      rw [this, measure_empty]; exact bot_le
  -- Steps 4–5: union bound and choice of `a`
  by_contra hcon
  push Not at hcon
  have hcov : Q ⊆ ⋃ e, A e := by
    intro a haQ
    obtain ⟨e, he, haE⟩ := hcon a fun i => (hI _).2 (haQ i)
    exact mem_iUnion.2 ⟨e, he, haQ, haE⟩
  have : volume Q < volume Q :=
    calc volume Q ≤ volume (⋃ e, A e) := measure_mono hcov
      _ ≤ ∑ e, volume (A e) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ e, volume (E e) := Finset.sum_le_sum fun e _ => hA e
      _ < ENNReal.ofReal ((1 / 2) ^ P) := hsum
      _ = volume Q := hQ.symm
  exact lt_irrefl _ this
/-- **Simon, Ch. 6, proof of 5.1** (choice of the centre `a`, (5)–(7)).  Put `d = m + 2`,
`K = #(Fin d → Fin P)`, `β = 2K·10ᵈ·2ᴾ + 1` and `C = Kβ`.  For each `e : Fin d → Fin P` let
`E_e` be the union of the bad sets of centres of the image measures of `μ` and `μ'` under
`x ↦ (x_{e(k)})_k`.  Each bad set has volume `≤ 10ᵈ/β`, so `Σ_e |E_e| < (1/2)ᴾ` and the cube
selection gives `a` with `(a_{e(k)})_k ∉ E_e` for every injective `e`.  The `r`-tube about
`L*(a)` lies in the union over injective `e` of the preimages of the periodic
`r`-neighbourhoods of `(a_{e(k)})_k`, each of `ν`-measure `≤ β rᵈ ν(ℝᴾ)` for `ν = μ, μ'`; hence
`ν(tube) ≤ Kβ rᵈ ν(ℝᴾ)`. -/
theorem Submission.dor_lmb_fcd_good_center : ∀ (P m : ℕ), m + 1 < P → ∃ C : NNReal, ∀ μ μ' : Measure (Euclid P), IsFiniteMeasure μ → IsFiniteMeasure μ' → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ univ ∧ μ' {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ' univ := by
  have c1 := Submission.dor_lmb_fcd_gc_tube_cover
  have c2 := Submission.dor_lmb_fcd_gc_bad_set_volume
  have c3 := Submission.dor_lmb_fcd_gc_cube_selection
  classical
  intro P m hPm
  -- Step 4: the constants `β` and `C = Kβ`, depending only on `P` and `m`
  set K : ℕ := Fintype.card (Fin (m + 2) → Fin P) with hK
  set β : ℝ := 2 * K * 10 ^ (m + 2) * 2 ^ P + 1 with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨Real.toNNReal (K * β), ?_⟩
  intro μ μ' hμ hμ'
  -- the coordinate projections `x ↦ (x_{e(k)})_k`
  let prj : (Fin (m + 2) → Fin P) → Euclid P → (Fin (m + 2) → ℝ) := fun e x k => x (e k)
  have hprj : ∀ e, Measurable (prj e) := fun e =>
    (continuous_pi fun k => PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (e k)).measurable
  -- the bad sets of centres of the projected measures (steps 2–3)
  let Bad : Measure (Fin (m + 2) → ℝ) → Set (Fin (m + 2) → ℝ) := fun ρ =>
    {g | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ (m + 2)) * ρ univ <
        ρ {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}}
  let E : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
    Bad (μ.map (prj e)) ∪ Bad (μ'.map (prj e))
  have hE : ∀ e, volume (E e) ≤ 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := by
    intro e
    calc volume (E e) ≤ volume (Bad (μ.map (prj e))) + volume (Bad (μ'.map (prj e))) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (10 ^ (m + 2) / β) + ENNReal.ofReal (10 ^ (m + 2) / β) :=
          add_le_add (c2 (m + 2) _ inferInstance β hβpos) (c2 (m + 2) _ inferInstance β hβpos)
      _ = 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := (two_mul _).symm
  -- the exceptional sets do not exhaust the cube
  have hsum : ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) := by
    calc ∑ e, volume (E e) ≤ ∑ _e : Fin (m + 2) → Fin P, 2 * ENNReal.ofReal (10 ^ (m + 2) / β) :=
          Finset.sum_le_sum fun e _ => hE e
      _ = ENNReal.ofReal (2 * K * 10 ^ (m + 2) / β) := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal ((1 / 2) ^ P) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), div_lt_iff₀ hβpos, hβ]
          have h2 : ((1 : ℝ) / 2) ^ P * 2 ^ P = 1 := by
            rw [← mul_pow]; norm_num
          have h3 : (0 : ℝ) < (1 / 2) ^ P := by positivity
          have h4 : ((1 : ℝ) / 2) ^ P * (2 * K * 10 ^ (m + 2) * 2 ^ P + 1) =
              2 * K * 10 ^ (m + 2) * ((1 / 2) ^ P * 2 ^ P) + (1 / 2) ^ P := by ring
          rw [h4, h2]
          linarith
  -- choice of a good centre `a` for both measures
  obtain ⟨a, ha, hgood⟩ := c3 P (m + 2) E hsum
  refine ⟨a, ha, ?_⟩
  intro r hr0 hr1
  -- Step 5: the estimate for any finite `ν` for which `a` is good
  have key : ∀ ν : Measure (Euclid P), IsFiniteMeasure ν →
      (∀ e : Fin (m + 2) → Fin P, Function.Injective e → prj e a ∉ Bad (ν.map (prj e))) →
      ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤
        (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
    intro ν hν hνgood
    let O : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
      {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - prj e a k - z k) ^ 2 < r ^ 2}
    let T : (Fin (m + 2) → Fin P) → Set (Euclid P) := fun e =>
      {x | Function.Injective e ∧ prj e x ∈ O e}
    -- step 1: the `r`-tube about `L*(a)` lies in the periodic coordinate cylinders
    have hcover : {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ⊆ ⋃ e, T e := by
      intro x hx
      obtain ⟨e, he, z, hz⟩ := c1 P m hPm a x r hx
      exact mem_iUnion.2 ⟨e, he, z, hz⟩
    -- each cylinder family has `ν`-measure `≤ β rᵈ ν(ℝᴾ)`, since `a` is good
    have hT : ∀ e, ν (T e) ≤ ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
      intro e
      by_cases he : Function.Injective e
      · have hsub : T e ⊆ prj e ⁻¹' O e := fun x hx => hx.2
        have hcube : ∀ k, |prj e a k - 1 / 2| < 1 / 4 := fun k => ha (e k)
        have hnot := hνgood e he
        have hle : (ν.map (prj e)) (O e) ≤
            ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := by
          by_contra hlt
          exact hnot ⟨hcube, r, hr0, hr1, not_le.1 hlt⟩
        calc ν (T e) ≤ ν (prj e ⁻¹' O e) := measure_mono hsub
          _ ≤ (ν.map (prj e)) (O e) := Measure.le_map_apply (hprj e).aemeasurable _
          _ ≤ ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := hle
          _ = ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
              rw [Measure.map_apply (hprj e) MeasurableSet.univ, preimage_univ]
      · have : T e = ∅ := by
          ext x
          simp only [mem_empty_iff_false, iff_false]
          exact fun hx => he hx.1
        rw [this, measure_empty]
        exact bot_le
    -- subadditivity over the `K` maps `e`
    calc ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
          ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ ν (⋃ e, T e) := measure_mono hcover
      _ ≤ ∑ e, ν (T e) := measure_iUnion_fintype_le ν T
      _ ≤ ∑ _e : Fin (m + 2) → Fin P, ENNReal.ofReal (β * r ^ (m + 2)) * ν univ :=
          Finset.sum_le_sum fun e _ => hT e
      _ = (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            show ((Real.toNNReal (K * β) : ℝ≥0∞)) = ENNReal.ofReal (K * β) from rfl,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact ⟨key μ hμ fun e he h => hgood e he (Or.inl h),
    key μ' hμ' fun e he h => hgood e he (Or.inr h)⟩
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
theorem Submission.dor_lmb_fcd_jwc_minor_weak_continuity : ∀ (k r : ℕ) (L : NNReal) (gs : ℕ → Fin r → Euclid k → ℝ) (g : Fin r → Euclid k → ℝ) (V : Fin r → Euclid k) (φ : Euclid k → ℝ), Integrable φ → (∀ j c, LipschitzWith L (gs j c)) → (∀ c, LipschitzWith L (g c)) → (∀ c, TendstoUniformly (fun j => gs j c) (g c) atTop) → Tendsto (fun j => ∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (gs j c) x (V b))) atTop (𝓝 (∫ x, φ x * Matrix.det (Matrix.of fun c b => fderiv ℝ (g c) x (V b)))) := by
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
      Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L (gs j) V ψ (hgs j) hψ1 hψs
    have hIBP := Submission.dor_lmb_fcd_jwc_lipschitz_minor_ibp k r L g V ψ hg hψ1 hψs
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

/-- **Weak continuity of pulled-back `k`-forms** (the identification of Simon 2.29 with 3.6): if
the `L`-Lipschitz `H_j : ℝᵏ → ℝ^{N'}` converge uniformly to the `L`-Lipschitz `H`, `w ∈ L¹(A)` and
`ω ∈ 𝒟ᵏ(ℝ^{N'})`, then `∫_A w H_j^#ω(e) → ∫_A w H^#ω(e)`, where
`H^#ω(u)(e) = ω(H(u))(DH(u)e₁, …, DH(u)e_k)`.  Where `G` is differentiable (a.e., by Rademacher)
`D(G^i)(u) v = (DG(u) v) i`, so the covector expansion gives `k! G^#ω(e) = Σ_I ω_I(G) D_I(G)` a.e.,
with coefficients `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (k-1)})` continuous with compact support and
minors `D_I(G) = det (D(G^{I c}) e_b)_{c,b}` measurable and bounded by `Cb = k! (L Σ_b ‖e_b‖)ᵏ`.
For each `I` split `ω_I(H_j) = (ω_I(H_j) − ω_I(H)) + ω_I(H)`: the first part contributes at most
`Cb sup |ω_I(H_j) − ω_I(H)| ∫_A |w| → 0` (`ω_I` is uniformly continuous), and
`∫_A w ω_I(H) D_I(H_j) → ∫_A w ω_I(H) D_I(H)` is the weak continuity of Jacobian minors with the
weight `1_A w ω_I(H) ∈ L¹`.  Summing over `I` and dividing by `k!` concludes. -/
theorem Submission.dor_lmb_fcd_jacobian_weak_continuity : ∀ (k N' : ℕ) (A : Set (Euclid k)) (w : Euclid k → ℝ) (L : NNReal) (Hs : ℕ → Euclid k → Euclid N') (H : Euclid k → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k), MeasurableSet A → IntegrableOn w A → (∀ j, LipschitzWith L (Hs j)) → LipschitzWith L H → TendstoUniformly Hs H atTop → Tendsto (fun j => ∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (Hs j u) (fun i => fderiv ℝ (Hs j) u (EuclideanSpace.single i (1 : ℝ)))) atTop (𝓝 (∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (H u) (fun i => fderiv ℝ H u (EuclideanSpace.single i (1 : ℝ))))) := by
  intro k N' A w L Hs H ω hA hw hHs hH hU
  have hw' : Integrable w (volume.restrict A) := hw
  -- step 1: `ω` is continuous with compact support, hence so are its coefficients
  -- `ω_I(y) = ω(y)(e'_{I 0}, …, e'_{I (k-1)})`, which are therefore bounded
  obtain ⟨⟨hωsm, hωs⟩, -⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid N') k) := ContDiff.continuous hωsm
  obtain ⟨ωI, hωI⟩ : ∃ f : (Fin k → Fin N') → Euclid N' → ℝ, ∀ I y,
      f I y = (ω : DifferentialForm (Euclid N') k) y
        (fun c => EuclideanSpace.single (I c) (1 : ℝ)) :=
    ⟨fun I y => (ω : DifferentialForm (Euclid N') k) y
      (fun c => EuclideanSpace.single (I c) (1 : ℝ)), fun _ _ => rfl⟩
  have hωIc : ∀ I, Continuous (ωI I) := by
    intro I
    have h : ωI I = fun y => ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ
        (fun c => EuclideanSpace.single (I c) (1 : ℝ)) ((ω : DifferentialForm (Euclid N') k) y) := by
      funext y; rw [hωI]; rfl
    rw [h]
    exact (ContinuousLinearMap.continuous _).comp hωc
  have hωIs : ∀ I, HasCompactSupport (ωI I) := by
    intro I
    have h : ωI I = (fun f : Covector (Euclid N') k =>
        f (fun c => EuclideanSpace.single (I c) (1 : ℝ))) ∘ (ω : DifferentialForm (Euclid N') k) := by
      funext y; rw [hωI]; rfl
    rw [h]
    exact hωs.comp_left (by simp)
  have hωIG : ∀ I (G : Euclid k → Euclid N'), Continuous G →
      Continuous (fun u => ωI I (G u)) ∧ ∃ M, ∀ u, ‖ωI I (G u)‖ ≤ M := fun I G hG =>
    ⟨(hωIc I).comp hG, ((hωIc I).bounded_above_of_compact_support (hωIs I)).imp
      fun _ hM u => hM (G u)⟩
  -- step 2: coordinates of `L`-Lipschitz maps are `L`-Lipschitz, and the minors
  -- `D_I(G) = det (D(G^{I c}) e_b)_{c,b}` are measurable and bounded by `Cb`
  have hcoordL : ∀ G : Euclid k → Euclid N', LipschitzWith L G → ∀ i,
      LipschitzWith L (fun y => G y i) :=
    fun G hG i => LipschitzWith.of_dist_le_mul fun x y =>
      (PiLp.dist_apply_le (G x) (G y) i).trans (hG.dist_le_mul x y)
  obtain ⟨D, hD⟩ : ∃ D : (Euclid k → Euclid N') → (Fin k → Fin N') → Euclid k → ℝ, ∀ G I x,
      D G I x = Matrix.det (Matrix.of fun c b =>
        fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))) :=
    ⟨fun G I x => Matrix.det (Matrix.of fun c b =>
      fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))), fun _ _ _ => rfl⟩
  set Cb : ℝ := (k.factorial : ℝ) *
    ((L : ℝ) * ∑ b : Fin k, ‖EuclideanSpace.single b (1 : ℝ)‖) ^ k
  have hDmb : ∀ G : Euclid k → Euclid N', LipschitzWith L G → ∀ I,
      Measurable (D G I) ∧ ∀ x, |D G I x| ≤ Cb := by
    intro G hG I
    have h := Submission.dor_lmb_fcd_jwc_minor_measurable_bound k k L (fun c y => G y (I c))
      (fun b => EuclideanSpace.single b (1 : ℝ)) (fun c => hcoordL G hG (I c))
    have hDe : D G I = fun x => Matrix.det (Matrix.of fun c b =>
        fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))) := funext (hD G I)
    rw [hDe]
    exact h
  -- `w F D_I(G)` is integrable on `A` for continuous bounded `F`
  have hint : ∀ F : Euclid k → ℝ, Continuous F → (∃ M, ∀ u, ‖F u‖ ≤ M) →
      ∀ G : Euclid k → Euclid N', LipschitzWith L G → ∀ I,
      Integrable (fun u => w u * F u * D G I u) (volume.restrict A) := by
    rintro F hF ⟨M, hM⟩ G hG I
    refine (hw'.mul_bdd hF.aestronglyMeasurable (Eventually.of_forall hM)).mul_bdd (c := Cb)
      (hDmb G hG I).1.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]
    exact (hDmb G hG I).2 u
  -- step 3: where `G` is differentiable, `D(G^i)(u) v = (DG(u) v) i`, so the covector expansion
  -- gives `k! G^#ω(e) = Σ_I ω_I(G) D_I(G)`
  have hpt : ∀ (G : Euclid k → Euclid N') (u : Euclid k), DifferentiableAt ℝ G u →
      (k.factorial : ℝ) * (ω : DifferentialForm (Euclid N') k) (G u)
          (fun i => fderiv ℝ G u (EuclideanSpace.single i (1 : ℝ))) =
        ∑ I, ωI I (G u) * D G I u := by
    intro G u hGu
    rw [Submission.dor_lmb_fcd_jwc_covector_det_expansion]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hωI, hD]
    congr 2
    ext c b
    simp only [Matrix.of_apply]
    have h : HasFDerivAt (PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c) ∘ G)
        ((PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c)).comp (fderiv ℝ G u)) u :=
      (PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c)).hasFDerivAt.comp u hGu.hasFDerivAt
    have h' : HasFDerivAt (fun y => G y (I c))
        ((PiLp.proj 2 (fun _ : Fin N' => ℝ) (I c)).comp (fderiv ℝ G u)) u := h
    rw [h'.fderiv]
    rfl
  -- Rademacher: the expansion holds a.e., so `∫_A w G^#ω(e) = (k!)⁻¹ Σ_I ∫_A w ω_I(G) D_I(G)`
  have hexp : ∀ G : Euclid k → Euclid N', LipschitzWith L G →
      ∫ u in A, w u * (ω : DifferentialForm (Euclid N') k) (G u)
          (fun i => fderiv ℝ G u (EuclideanSpace.single i (1 : ℝ))) =
        (k.factorial : ℝ)⁻¹ * ∑ I, ∫ u in A, w u * ωI I (G u) * D G I u := by
    intro G hG
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    rw [← integral_finsetSum (f := fun I u => w u * ωI I (G u) * D G I u) Finset.univ
      fun I _ => hint _ (hωIG I G hG.continuous).1 (hωIG I G hG.continuous).2 G hG I,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hG.ae_differentiableAt (μ := volume))] with u hu
    have h2 : ∑ I, w u * ωI I (G u) * D G I u = w u * ∑ I, ωI I (G u) * D G I u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun I _ => mul_assoc _ _ _
    rw [h2, ← hpt G u hu, mul_left_comm, inv_mul_cancel_left₀ hk]
  -- step 4: the coordinates `H_j^i` converge uniformly to `H^i`
  have hcoordU : ∀ i, TendstoUniformly (fun j y => Hs j y i) (fun y => H y i) atTop := by
    intro i
    have hl : LipschitzWith 1 (fun x : Euclid N' => x i) :=
      LipschitzWith.of_dist_le_mul fun x y => by
        rw [NNReal.coe_one, one_mul]
        exact PiLp.dist_apply_le x y i
    exact hl.uniformContinuous.comp_tendstoUniformly hU
  -- step 5: for each `I`, `∫_A w ω_I(H_j) D_I(H_j) → ∫_A w ω_I(H) D_I(H)`
  have hconvI : ∀ I, Tendsto (fun j => ∫ u in A, w u * ωI I (Hs j u) * D (Hs j) I u) atTop
      (𝓝 (∫ u in A, w u * ωI I (H u) * D H I u)) := by
    intro I
    obtain ⟨hωHc, M, hM⟩ := hωIG I H hH.continuous
    -- weak continuity of Jacobian minors, with the fixed weight `φ = 1_A w ω_I(H) ∈ L¹`
    have hφ : Integrable (A.indicator fun u => w u * ωI I (H u)) := by
      rw [integrable_indicator_iff hA]
      exact hw'.mul_bdd hωHc.aestronglyMeasurable (Eventually.of_forall hM)
    have hmain := Submission.dor_lmb_fcd_jwc_minor_weak_continuity k k L
      (fun j c y => Hs j y (I c)) (fun c y => H y (I c)) (fun b => EuclideanSpace.single b (1 : ℝ))
      _ hφ (fun j c => hcoordL (Hs j) (hHs j) (I c)) (fun c => hcoordL H hH (I c))
      (fun c => hcoordU (I c))
    have hind : ∀ G : Euclid k → Euclid N',
        ∫ x, A.indicator (fun u => w u * ωI I (H u)) x * Matrix.det (Matrix.of fun c b =>
          fderiv ℝ (fun y => G y (I c)) x (EuclideanSpace.single b (1 : ℝ))) =
        ∫ u in A, w u * ωI I (H u) * D G I u := by
      intro G
      rw [← integral_indicator hA]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Set.indicator_mul_left A (fun u => w u * ωI I (H u)) (D G I), hD]
    have hmain' : Tendsto (fun j => ∫ u in A, w u * ωI I (H u) * D (Hs j) I u) atTop
        (𝓝 (∫ u in A, w u * ωI I (H u) * D H I u)) := by
      rw [← hind H]
      exact hmain.congr fun j => hind (Hs j)
    -- the error `|∫_A w (ω_I(H_j) − ω_I(H)) D_I(H_j)| ≤ Cb sup |ω_I(H_j) − ω_I(H)| ∫_A |w| → 0`
    have hωU : TendstoUniformly (fun j u => ωI I (Hs j u)) (fun u => ωI I (H u)) atTop :=
      ((hωIs I).uniformContinuous_of_continuous (hωIc I)).comp_tendstoUniformly hU
    have herr : Tendsto (fun j => ∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u)
        atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set K : ℝ := Cb * (∫ u in A, ‖w u‖) + 1
      have hCb0 : 0 ≤ Cb := by positivity
      have hK0 : 0 < K := by
        have : 0 ≤ ∫ u in A, ‖w u‖ := integral_nonneg fun _ => norm_nonneg _
        positivity
      have hδ : 0 < ε / (2 * K) := by positivity
      obtain ⟨N, hN⟩ :=
        (Metric.tendstoUniformly_iff.1 hωU (ε / (2 * K)) hδ).exists_forall_of_atTop
      refine ⟨N, fun j hj => ?_⟩
      rw [Real.dist_eq, sub_zero]
      have hbd : ∀ u, ‖w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u‖ ≤
          (ε / (2 * K) * Cb) * ‖w u‖ := by
        intro u
        have h1 : |ωI I (Hs j u) - ωI I (H u)| ≤ ε / (2 * K) := by
          have := hN j hj u
          rw [dist_comm, Real.dist_eq] at this
          exact this.le
        have h2 : |D (Hs j) I u| ≤ Cb := (hDmb (Hs j) (hHs j) I).2 u
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
        calc |w u| * |ωI I (Hs j u) - ωI I (H u)| * |D (Hs j) I u|
            ≤ |w u| * (ε / (2 * K)) * Cb := by gcongr
          _ = (ε / (2 * K) * Cb) * |w u| := by ring
      calc |∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u|
          = ‖∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ u in A, (ε / (2 * K) * Cb) * ‖w u‖ :=
            norm_integral_le_of_norm_le (hw'.norm.const_mul _) (Eventually.of_forall hbd)
        _ = (ε / (2 * K)) * (Cb * ∫ u in A, ‖w u‖) := by
            rw [integral_const_mul]; ring
        _ ≤ (ε / (2 * K)) * K := by gcongr; linarith
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    -- `∫_A w ω_I(H_j) D_I(H_j) = (error) + ∫_A w ω_I(H) D_I(H_j)`
    have heq : ∀ j, (∫ u in A, w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u) +
        ∫ u in A, w u * ωI I (H u) * D (Hs j) I u =
        ∫ u in A, w u * ωI I (Hs j u) * D (Hs j) I u := by
      intro j
      have i1 := hint _ (hωIG I (Hs j) (hHs j).continuous).1 (hωIG I (Hs j) (hHs j).continuous).2
        (Hs j) (hHs j) I
      have i2 := hint _ hωHc ⟨M, hM⟩ (Hs j) (hHs j) I
      have i3 : Integrable (fun u => w u * (ωI I (Hs j u) - ωI I (H u)) * D (Hs j) I u)
          (volume.restrict A) :=
        (i1.sub i2).congr (Eventually.of_forall fun u => by simp only [Pi.sub_apply]; ring)
      rw [← integral_add i3 i2]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only
      ring
    have hsum := herr.add hmain'
    rw [zero_add] at hsum
    exact hsum.congr heq
  -- step 6: sum over `I` and divide by `k!`
  have hlim := (tendsto_finsetSum (Finset.univ : Finset (Fin k → Fin N'))
    fun I _ => hconvI I).const_mul ((k.factorial : ℝ)⁻¹)
  rw [hexp H hH]
  exact hlim.congr fun j => (hexp (Hs j) (hHs j)).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
