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

/-- **Simon Ch. 6, Lemma 5.4** (retraction onto the `n`-skeleton away from the dual skeleton,
`n = m + 1 < P`; chapter-06.txt lines 1493–1650).  `L*(a)` is the set of points with at least
`m + 2` coordinates in `a + ℤ`, and `d(x) := dist(x, L*(a))`.  The face
`F(b, J) = {x : bᵢ ≤ xᵢ ≤ bᵢ + 1 (i ∈ J), xᵢ = bᵢ (i ∉ J)}` has centre `a_F` (`bᵢ + aᵢ` on `J`),
and `ψ_F(x) = a_F + (x − a_F)/N_F(x)`, `N_F` the gauge of `x − a_F`, retracts `F \ {a_F}` radially
onto `∂F` with `|ψ_F(y) − ψ_F(x)| ≤ (1 + 4√|J|)/N_F(x) · |y − x|`.  Retractions of two faces of
the same dimension agree where the faces meet, so `Ψ_{m+1} = id` and `Ψ_j = Ψ_{j−1} ∘ ψ_F` on
each `j`-face `F` define `ψ := Ψ_P`.  By induction on `j`, if at most `m + 1` coordinates of
`x ∈ F(b, J)` are `ρ`-close to the centre, then `Ψ_j(x) ∈ F(b, J)` has `P − m − 1` integer
coordinates and `Ψ_j` is `(1 + 4√P)ᴾ/ρ`-Lipschitz at `x` on `F(b, J)`.  If `d(x) > 0`, this holds
with `ρ = d(x)/√(m + 2)` on every unit cube through `x` (moving `m + 2` coordinates to `b + a`
would reach `L*(a)`), and these cubes cover a neighbourhood of `x`: this gives (i) and
`D̄ψ(x) ≤ √(m + 2)(1 + 4√P)ᴾ/d(x)`.  For `d(x), d(y) ≥ r`, a segment argument applies if
`|x − y| < r/2` (then `d > r/2` on `[x, y]`); otherwise `|ψ(x) − ψ(y)| ≤ 2√P + |x − y|`. -/
theorem Submission.dtc_bc_lc_fd_dfm_skeleton_retraction : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y := by
  -- Each step clears the earlier general statements it does not use, so that every proof
  -- runs in a small local context.
  -- Steps 1–3 (centres of faces, radial retractions): for `x ∈ F(b, J) \ {a_F}`,
  -- `|x_k − b_k − a_k| ≤ N(x)` (`k ∈ J`), `0 < N(x) ≤ 1`, `ψ_F(x) ∈ ∂F`, `ψ_F = id` on `∂F`, and
  -- `|ψ_F(y) − ψ_F(x)| ≤ (1 + 4√|J|)/N(x) · |y − x|`, since `N` is `4`-Lipschitz and
  -- `|y − a_F| ≤ √|J| N(y)`
  have face_radial : ∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) →
      ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (ψF : Euclid P → Euclid P),
      (∀ y : Euclid P, ∀ i, ψF y i = if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) /
        J.sup' hJ (fun k => max ((y k - b k - a k) / (1 - a k)) ((b k + a k - y k) / a k))
        else y i) →
      ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) →
      (∃ i ∈ J, x i ≠ b i + a i) →
      (∀ k ∈ J, |x k - b k - a k| ≤
        J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))) ∧
      0 < J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ∧
      J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ≤ 1 ∧
      (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧
      (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧
      ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧
      ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) →
        (∃ i ∈ J, y i ≠ b i + a i) →
        dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) /
          J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) *
            dist y x := by
    intro P a ha b J hJ ψF hψ x hx hne
    -- the gauge `N(u)` of `u − a_F`, kept opaque
    obtain ⟨N, hN⟩ : ∃ N : Euclid P → ℝ, ∀ u : Euclid P,
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) = N u :=
      ⟨fun u => J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)),
        fun _ => rfl⟩
    have hψN : ∀ u : Euclid P, ∀ i, ψF u i =
        if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N u else u i := by
      intro u i
      rw [hψ u i, hN u]
    rw [hN x]
    -- step 0: `1/4 < a_k < 3/4`
    have ha' : ∀ i, 1 / 4 < a i ∧ a i < 3 / 4 := by
      intro i
      have := abs_lt.mp (ha i)
      constructor <;> linarith [this.1, this.2]
    -- `N(u)` dominates each of its terms, and is the largest term
    have hterm : ∀ u : Euclid P, ∀ k ∈ J,
        max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k) ≤ N u := by
      intro u k hk
      rw [← hN u]
      exact Finset.le_sup'
        (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) hk
    -- step 1: `|u_k − b_k − a_k| ≤ N(u)` for `k ∈ J`
    have habs : ∀ u : Euclid P, ∀ k ∈ J, |u k - b k - a k| ≤ N u := by
      intro u k hk
      obtain ⟨h1, h2⟩ := ha' k
      refine le_trans ?_ (hterm u k hk)
      rcases le_or_gt 0 (u k - b k - a k) with ht | ht
      · rw [abs_of_nonneg ht]
        apply le_max_of_le_left
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_nonneg ht (by linarith : (0 : ℝ) ≤ a k)]
      · rw [abs_of_neg ht]
        apply le_max_of_le_right
        rw [le_div_iff₀ (by linarith)]
        nlinarith [mul_pos (neg_pos.mpr ht) (by linarith : (0 : ℝ) < 1 - a k)]
    -- step 2: `N ≤ 1` on `F`, and `N > 0` off the centre
    have hle1 : ∀ u : Euclid P,
        (∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i)) → N u ≤ 1 := by
      intro u hu
      rw [← hN u]
      refine Finset.sup'_le hJ _ (fun k hk => ?_)
      obtain ⟨h1, h2⟩ := ha' k
      obtain ⟨hu1, hu2⟩ := (hu k).1 hk
      apply max_le
      · rw [div_le_one (by linarith)]; linarith
      · rw [div_le_one (by linarith)]; linarith
    have hpos : ∀ u : Euclid P, (∃ i ∈ J, u i ≠ b i + a i) → 0 < N u := by
      rintro u ⟨i, hi, hui⟩
      have h0 : u i - b i - a i ≠ 0 := fun h => hui (by linarith)
      exact (abs_pos.mpr h0).trans_le (habs u i hi)
    have hNx := hpos x hne
    refine ⟨habs x, hNx, hle1 x hx, ?_, ?_, ?_, ?_⟩
    · -- step 3: `ψ_F(x) ∈ F`
      intro i
      refine ⟨fun hi => ?_, fun hi => ?_⟩
      · rw [hψN x i, ite_eq_left hi]
        obtain ⟨h1, h2⟩ := ha' i
        have hq := hterm x i hi
        have hp1 := (le_max_left _ _).trans hq
        have hp2 := (le_max_right _ _).trans hq
        rw [div_le_iff₀ (by linarith)] at hp1 hp2
        have e1 : -(a i) ≤ (x i - b i - a i) / N x := by
          rw [le_div_iff₀ hNx]; linarith
        have e2 : (x i - b i - a i) / N x ≤ 1 - a i := by
          rw [div_le_iff₀ hNx]; linarith
        constructor <;> linarith
      · rw [hψN x i, ite_eq_right hi]
        exact (hx i).2 hi
    · -- step 4: a coordinate attaining the maximum is pushed to `b_i` or `b_i + 1`
      obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hJ
        (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))
      have heq' : N x = max ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) := by
        rw [← hN x]; exact heq
      refine ⟨i, hi, ?_⟩
      rw [hψN x i, ite_eq_left hi]
      obtain ⟨h1, h2⟩ := ha' i
      rcases max_choice ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) with hm | hm
      · right
        rw [hm] at heq'
        have ht : x i - b i - a i = N x * (1 - a i) := by
          rw [heq', div_mul_cancel₀ _ (by linarith : (1 : ℝ) - a i ≠ 0)]
        have : (x i - b i - a i) / N x = 1 - a i := by
          rw [div_eq_iff hNx.ne']; linarith
        rw [this]; ring
      · left
        rw [hm] at heq'
        have ht : b i + a i - x i = N x * a i := by
          rw [heq', div_mul_cancel₀ _ (by linarith : a i ≠ 0)]
        have : (x i - b i - a i) / N x = -(a i) := by
          rw [div_eq_iff hNx.ne']; linarith
        rw [this]; ring
    · -- step 5: on `∂F`, `N(x) = 1` and `ψ_F(x) = x`
      rintro ⟨i, hi, hbi⟩
      obtain ⟨h1, h2⟩ := ha' i
      have hq := hterm x i hi
      have hN1 : N x = 1 := by
        apply le_antisymm (hle1 x hx)
        rcases hbi with h | h
        · have : (b i + a i - x i) / a i = 1 := by
            rw [h, div_eq_one_iff_eq (by linarith)]; ring
          linarith [le_max_right ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i)]
        · have : (x i - b i - a i) / (1 - a i) = 1 := by
            rw [h, div_eq_one_iff_eq (by linarith)]; ring
          linarith [le_max_left ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i)]
      ext k
      rw [hψN x k, hN1]
      split_ifs <;> ring
    · -- steps 6–8: the radial estimate
      intro y hy hney
      have hNy := hpos y hney
      have hNx0 : N x ≠ 0 := hNx.ne'
      have hNy0 : N y ≠ 0 := hNy.ne'
      -- step 6: `N` is `4`-Lipschitz
      have hlip : ∀ u v : Euclid P, N u ≤ N v + 4 * dist u v := by
        intro u v
        rw [← hN u]
        refine Finset.sup'_le hJ _ (fun k hk => ?_)
        obtain ⟨h1, h2⟩ := ha' k
        have hd : |u k - v k| ≤ dist u v := by
          have := PiLp.dist_apply_le u v k
          rwa [Real.dist_eq] at this
        have hdn : 0 ≤ dist u v := dist_nonneg
        have hq := hterm v k hk
        have hp1 := (le_max_left _ _).trans hq
        have hp2 := (le_max_right _ _).trans hq
        apply max_le
        · have e : (u k - b k - a k) / (1 - a k) =
              (v k - b k - a k) / (1 - a k) + (u k - v k) / (1 - a k) := by
            rw [← add_div]; congr 1; ring
          have : (u k - v k) / (1 - a k) ≤ 4 * dist u v := by
            rw [div_le_iff₀ (by linarith)]
            nlinarith [le_abs_self (u k - v k),
              mul_nonneg hdn (by linarith : (0 : ℝ) ≤ 4 * (1 - a k) - 1)]
          linarith
        · have e : (b k + a k - u k) / a k = (b k + a k - v k) / a k + (v k - u k) / a k := by
            rw [← add_div]; congr 1; ring
          have : (v k - u k) / a k ≤ 4 * dist u v := by
            rw [div_le_iff₀ (by linarith)]
            have : |v k - u k| ≤ dist u v := by rw [abs_sub_comm]; exact hd
            nlinarith [le_abs_self (v k - u k),
              mul_nonneg hdn (by linarith : (0 : ℝ) ≤ 4 * a k - 1)]
          linarith
      have hlipxy : |N x - N y| ≤ 4 * dist y x := by
        have l1 := hlip x y
        have l2 := hlip y x
        rw [dist_comm] at l1
        rw [abs_le]; constructor <;> linarith
      -- step 7: `w = y − a_F` (supported in `J`) has `|w| ≤ √|J| N(y)`
      let W : Euclid P := WithLp.toLp 2 (fun k => if k ∈ J then y k - b k - a k else 0)
      have hWk : ∀ k, W k = if k ∈ J then y k - b k - a k else 0 := fun k => rfl
      have hW : ‖W‖ ≤ Real.sqrt J.card * N y := by
        rw [EuclideanSpace.norm_eq]
        have h1 : ∑ k, ‖W k‖ ^ 2 = ∑ k ∈ J, ‖W k‖ ^ 2 :=
          (Finset.sum_subset (Finset.subset_univ J)
            (fun k _ hk => by rw [hWk k, ite_eq_right hk]; simp)).symm
        have h2 : ∑ k ∈ J, ‖W k‖ ^ 2 ≤ J.card • N y ^ 2 := by
          apply Finset.sum_le_card_nsmul
          intro k hk
          rw [hWk k, ite_eq_left hk, Real.norm_eq_abs, sq_abs]
          have := habs y k hk
          nlinarith [abs_nonneg (y k - b k - a k), sq_abs (y k - b k - a k)]
        rw [nsmul_eq_mul] at h2
        calc Real.sqrt (∑ k, ‖W k‖ ^ 2) ≤ Real.sqrt ((J.card : ℝ) * N y ^ 2) :=
              Real.sqrt_le_sqrt (h1 ▸ h2)
          _ = Real.sqrt J.card * N y := by
              rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hNy.le]
      -- step 8: `ψ_F(y) − ψ_F(x) = (y − x)/N(x) + (1/N(y) − 1/N(x)) w`
      have hdecomp : ψF y - ψF x = (1 / N x) • (y - x) + (1 / N y - 1 / N x) • W := by
        ext k
        rw [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply,
          hψN x k, hψN y k, hWk k, smul_eq_mul, smul_eq_mul]
        by_cases hk : k ∈ J
        · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk]
          field_simp
          ring
        · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, (hx k).2 hk, (hy k).2 hk]
          ring
      have hfrac : |1 / N y - 1 / N x| * N y = |N x - N y| / N x := by
        rw [div_sub_div _ _ hNy0 hNx0, abs_div, abs_of_pos (mul_pos hNy hNx)]
        field_simp
      rw [dist_eq_norm, hdecomp]
      calc ‖(1 / N x) • (y - x) + (1 / N y - 1 / N x) • W‖
          ≤ ‖(1 / N x) • (y - x)‖ + ‖(1 / N y - 1 / N x) • W‖ := norm_add_le _ _
        _ = (1 / N x) * dist y x + |1 / N y - 1 / N x| * ‖W‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (one_div_pos.mpr hNx), dist_eq_norm]
        _ ≤ (1 / N x) * dist y x + |1 / N y - 1 / N x| * (Real.sqrt J.card * N y) := by
            gcongr
        _ = (1 / N x) * dist y x + (|N x - N y| / N x) * Real.sqrt J.card := by
            rw [← hfrac]; ring
        _ ≤ (1 / N x) * dist y x + (4 * dist y x / N x) * Real.sqrt J.card := by
            gcongr
        _ = (1 + 4 * Real.sqrt J.card) / N x * dist y x := by ring
  -- Step 4 (definition of `ψ`): two distinct `j`-faces through `u` meet where `u` has a
  -- coordinate `uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, and there both retractions are the identity; so
  -- `Ψ_{m+1} = id`, `Ψ_j = Ψ_{j−1} ∘ ψ_F` on every `j`-face `F`, `m + 2 ≤ j ≤ P`, is well defined
  have face_retraction_family : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) →
      ∃ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) ∧
      ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty),
      J.card = j → ∀ x : Euclid P,
      (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) →
      ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) /
        J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))
        else x i) →
      Ψ j x = Ψ (j - 1) y := by
    classical
    intro P m a ha
    -- `u ∈ F(b, J)`
    let InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop := fun b J u =>
      ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i)
    -- the radial retraction `R_{b,J}` of `F(b, J)` from its centre onto `∂F(b, J)`
    -- (`id` if `J = ∅`)
    let R : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Euclid P := fun b J u =>
      if hJ : J.Nonempty then
        WithLp.toLp 2 fun i => if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
          J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
          else u i
      else u
    have hR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (u : Euclid P) (i : Fin P),
        R b J u i = if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
          J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
          else u i := by
      intro b J hJ u i
      simp only [R, dite_eq_left hJ, PiLp.toLp_apply]
    -- Step 1: if two distinct faces of the same dimension contain `u`, then `u` has a coordinate
    -- `uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, on the boundary of the first one
    have hbd : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
        InF b J u → InF b' J' u → (b, J) ≠ (b', J') → ∃ i ∈ J, u i = b i ∨ u i = b i + 1 := by
      intro b b' J J' u hcard hu hu' hne
      by_cases hJJ : J = J'
      · -- same free coordinates: `bᵢ ≠ b'ᵢ` for some `i ∈ J` and
        -- `uᵢ ∈ [bᵢ, bᵢ + 1] ∩ [b'ᵢ, b'ᵢ + 1]`
        subst hJJ
        obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h : b = b' => hne (by rw [h])
        by_cases hiJ : i ∈ J
        · refine ⟨i, hiJ, ?_⟩
          obtain ⟨h1, h2⟩ := (hu i).1 hiJ
          obtain ⟨h3, h4⟩ := (hu' i).1 hiJ
          rcases lt_or_gt_of_ne hi with hlt | hlt
          · have : (b i : ℝ) + 1 ≤ b' i := by exact_mod_cast hlt
            right; linarith
          · have : (b' i : ℝ) + 1 ≤ b i := by exact_mod_cast hlt
            left; linarith
        · exact absurd (Int.cast_injective (((hu i).2 hiJ).symm.trans ((hu' i).2 hiJ))) hi
      · -- `J ⊄ J'`: for `i ∈ J \ J'` the coordinate `uᵢ = b'ᵢ ∈ [bᵢ, bᵢ + 1]` is an integer
        obtain ⟨i, hiJ, hiJ'⟩ := Finset.not_subset.mp fun hsub =>
          hJJ (Finset.eq_of_subset_of_card_le hsub hcard.ge)
        refine ⟨i, hiJ, ?_⟩
        obtain ⟨h1, h2⟩ := (hu i).1 hiJ
        rw [(hu' i).2 hiJ'] at h1 h2 ⊢
        have h1' : b i ≤ b' i := Int.cast_le.mp h1
        have h2' : b' i ≤ b i + 1 := by
          rw [← Int.cast_le (R := ℝ), Int.cast_add, Int.cast_one]
          exact h2
        rcases h1'.eq_or_lt with h | h
        · left; rw [← h]
        · right; rw [le_antisymm h2' (Int.add_one_le_of_lt h), Int.cast_add, Int.cast_one]
    -- Step 2: at such points `R_{b,J}` is the identity (`face_radial`; `1/4 < aᵢ < 3/4`
    -- keeps `u` off the centre), so all faces of the same dimension through `u` agree
    have hfix : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P), InF b J u →
        (∃ i ∈ J, u i = b i ∨ u i = b i + 1) → R b J u = u := by
      rintro b J u hu ⟨i, hiJ, hbi⟩
      have hJ : J.Nonempty := ⟨i, hiJ⟩
      have hai := abs_lt.mp (ha i)
      have hne : ∃ i ∈ J, u i ≠ b i + a i := ⟨i, hiJ, by
        rcases hbi with h | h <;> rw [h] <;> intro h' <;> linarith [hai.1, hai.2]⟩
      exact (face_radial P a ha b J hJ (R b J) (hR b J hJ) u hu
        hne).2.2.2.2.2.1 ⟨i, hiJ, hbi⟩
    have hcons : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
        InF b J u → InF b' J' u → R b J u = R b' J' u := by
      intro b b' J J' u hcard hu hu'
      by_cases h : (b, J) = (b', J')
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rfl
      · rw [hfix b J u hu (hbd b b' J J' u hcard hu hu' h),
          hfix b' J' u hu' (hbd b' b J' J u hcard.symm hu' hu (Ne.symm h))]
    -- Step 3: the step map `φ_j` applies the retraction of a chosen `j`-face through `u`
    let φ : ℕ → Euclid P → Euclid P := fun j u =>
      if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = j ∧ InF p.1 p.2 u then
        R h.choose.1 h.choose.2 u
      else u
    -- Step 4: `Ψ_k = id` for `k ≤ m + 1` and `Ψ_k = Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`
    let Ψ : ℕ → Euclid P → Euclid P := fun k =>
      Nat.rec (motive := fun _ => Euclid P → Euclid P) id
        (fun k Ψk => if k + 1 ≤ m + 1 then id else Ψk ∘ φ (k + 1)) k
    refine ⟨Ψ, fun x => ?_, ?_⟩
    · show (if m + 1 ≤ m + 1 then id else Ψ m ∘ φ (m + 1)) x = x
      rw [ite_eq_left le_rfl]
      rfl
    -- Step 5: for `x ∈ F(b, J)` the chosen face gives `φ_j(x) = R_{b,J}(x) = y`
    · intro j hj _ b J hJ hcard x hx y hy
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr ((Nat.zero_lt_succ _).trans_le hj)
      have hk : ¬k + 1 ≤ m + 1 := Nat.not_le.mpr hj
      show (if k + 1 ≤ m + 1 then id else Ψ k ∘ φ (k + 1)) x = Ψ (k + 1 - 1) y
      rw [ite_eq_right hk, Nat.add_sub_cancel]
      have hex : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x :=
        ⟨(b, J), hcard, hx⟩
      show Ψ k (if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x then
        R h.choose.1 h.choose.2 x else x) = Ψ k y
      rw [dite_eq_left hex,
        hcons _ b _ J x (hex.choose_spec.1.trans hcard.symm) hex.choose_spec.2 hx]
      congr 1
      ext i
      rw [hR b J hJ x i, hy i]
  -- Step 5 (pointwise bound, induction on the face dimension `j`, constant `(1 + 4√P)^(j−m−1)`):
  -- if at most `m + 1` coordinates of `x ∈ F(b, J)` are `ρ`-close to the centre, then
  -- `N_F(x) ≥ ρ`, `Ψ_j(x) ∈ F(b, J)` has `P − m − 1` integer coordinates, and `Ψ_j` is
  -- `(1 + 4√P)ᴾ/ρ`-Lipschitz at `x` on `F(b, J)`; in the step, `ψ_F(x)` lies on the
  -- `(j − 1)`-faces through it with radius `ρ/N_F(x)`, and the factors `N_F(x)` cancel
  have face_count_induction : ∀ (P m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P,
      (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) →
      (∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty),
        J.card = j → ∀ x : Euclid P,
        (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) →
        ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) /
          J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))
          else x i) →
        Ψ j x = Ψ (j - 1) y) →
      ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j →
      ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) →
      ∀ ρ : ℝ, 0 < ρ → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      (∀ i, (i ∈ J → (b i : ℝ) ≤ Ψ j x i ∧ Ψ j x i ≤ b i + 1) ∧ (i ∉ J → Ψ j x i = b i)) ∧
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧
      ∀ᶠ y in 𝓝[{w : Euclid P | ∀ i, (i ∈ J → (b i : ℝ) ≤ w i ∧ w i ≤ b i + 1) ∧
        (i ∉ J → w i = b i)}] x, dist (Ψ j y) (Ψ j x) ≤ c / ρ * dist y x := by
    clear face_retraction_family
    intro P m
    have hK1 : (1 : ℝ) ≤ 1 + 4 * Real.sqrt P := by
      have := Real.sqrt_nonneg (P : ℝ); linarith
    have hc : ∀ n : ℕ, (0 : ℝ) < 1 + 4 * Real.sqrt n := fun n => by positivity
    refine ⟨(1 + 4 * Real.sqrt P) ^ P, by positivity, ?_⟩
    intro a ha Ψ hΨ0 hrec
    -- the face `F(b, J)`, its gauge `N_{b,J}` and its radial retraction `ψ_{b,J}`
    obtain ⟨InF, hInF⟩ : ∃ InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop, ∀ b J u,
        InF b J u ↔ ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i) :=
      ⟨fun b J u => ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i),
        fun _ _ _ => Iff.rfl⟩
    obtain ⟨N, hN⟩ : ∃ N : (Fin P → ℤ) → ∀ J : Finset (Fin P), J.Nonempty → Euclid P → ℝ,
        ∀ b J hJ u, N b J hJ u =
          J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) :=
      ⟨fun b J hJ u =>
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)),
        fun _ _ _ _ => rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : (Fin P → ℤ) → ∀ J : Finset (Fin P), J.Nonempty → Euclid P → Euclid P,
        ∀ b J hJ u i, R b J hJ u i =
          if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i :=
      ⟨fun b J hJ u => WithLp.toLp 2 fun i =>
        if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i,
        fun _ _ _ _ _ => rfl⟩
    -- the recursion: `Ψ_j = Ψ_{j−1} ∘ ψ_{b,J}` on `F(b, J)`
    have hrec' : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P))
        (hJ : J.Nonempty), J.card = j → ∀ u, InF b J u → Ψ j u = Ψ (j - 1) (R b J hJ u) :=
      fun j hj hjP b J hJ hcard u hu =>
        hrec j hj hjP b J hJ hcard u ((hInF b J u).1 hu) (R b J hJ u) fun i => by rw [hR, hN]
    -- `face_radial` for `ψ_{b,J}`
    have FR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (x : Euclid P),
        InF b J x → (∃ i ∈ J, x i ≠ b i + a i) →
        (∀ k ∈ J, |x k - b k - a k| ≤ N b J hJ x) ∧ 0 < N b J hJ x ∧ InF b J (R b J hJ x) ∧
        (∃ i ∈ J, R b J hJ x i = b i ∨ R b J hJ x i = b i + 1) ∧
        ∀ y, InF b J y → (∃ i ∈ J, y i ≠ b i + a i) →
          dist (R b J hJ y) (R b J hJ x) ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := by
      intro b J hJ x hx hne
      obtain ⟨h1, h2, -, h3, h4, -, h6⟩ := face_radial P a ha b J hJ (R b J hJ)
        (fun y i => by rw [hR, hN]) x ((hInF b J x).1 hx) hne
      rw [hN, hInF]
      exact ⟨h1, h2, h3, h4, fun y hy hne' => h6 y ((hInF b J y).1 hy) hne'⟩
    clear face_radial
    -- 1(a): `|J| ≥ m + 2` and the counting condition give a coordinate `ρ`-far from the centre
    have exists_far : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), m + 2 ≤ J.card →
        ∀ (u : Euclid P) (ρ : ℝ), (J.filter (fun i => |u i - b i - a i| < ρ)).card ≤ m + 1 →
        ∃ i ∈ J, ρ ≤ |u i - b i - a i| := by
      intro b J hJc u ρ hcount
      by_contra h
      have hall : ∀ i ∈ J, |u i - b i - a i| < ρ := fun i hi => not_le.mp fun h' => h ⟨i, hi, h'⟩
      rw [Finset.filter_true_of_mem hall] at hcount
      omega
    have ne_centre : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P) (ρ : ℝ), 0 < ρ →
        (∃ i ∈ J, ρ ≤ |u i - b i - a i|) → ∃ i ∈ J, u i ≠ b i + a i := by
      rintro b J u ρ hρ ⟨i, hi, hf⟩
      refine ⟨i, hi, fun he => ?_⟩
      rw [he, show (b i : ℝ) + a i - b i - a i = 0 by ring, abs_zero] at hf
      linarith
    have count_le : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u v : Euclid P) (ρ ρ' : ℝ),
        (∀ i ∈ J', |v i - b' i - a i| < ρ' → i ∈ J ∧ |u i - b i - a i| < ρ) →
        (J'.filter (fun i => |v i - b' i - a i| < ρ')).card ≤
          (J.filter (fun i => |u i - b i - a i| < ρ)).card := by
      intro b b' J J' u v ρ ρ' h
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact h i hi.1 hi.2
    -- 1(b): the counting condition passes to nearby points with radius `ρ / 2`
    have count_near : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (x y : Euclid P) (ρ : ℝ),
        dist y x < ρ / 2 → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
        (J.filter (fun i => |y i - b i - a i| < ρ / 2)).card ≤ m + 1 := by
      intro b J x y ρ hyx hcount
      refine (count_le b b J J x y ρ (ρ / 2) fun i hi h' => ⟨hi, ?_⟩).trans hcount
      have hd : |x i - y i| ≤ dist y x := by
        rw [dist_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le x y i
      calc |x i - b i - a i| = |(x i - y i) + (y i - b i - a i)| := by ring_nf
        _ ≤ |x i - y i| + |y i - b i - a i| := abs_add_le _ _
        _ < ρ := by linarith
    -- Claim(j), by induction on `j ≥ m + 2`, with constant `K ^ (j - m - 1)`, `K = 1 + 4√P`
    have hclaim : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j →
        ∀ x, InF b J x → ∀ ρ : ℝ, 0 < ρ → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
        InF b J (Ψ j x) ∧
        (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧
        ∃ δ > 0, ∀ y, InF b J y → dist y x < δ →
          dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        -- 2. base case: `Ψ_{m+2} = ψ_{b,J}` on `F(b, J)`
        intro hP b J hcard x hx ρ hρ hcount
        have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
        have hΨ : ∀ u, InF b J u → Ψ (m + 2) u = R b J hJ u := fun u hu => by
          rw [hrec' (m + 2) le_rfl hP b J hJ hcard u hu, show m + 2 - 1 = m + 1 by omega, hΨ0]
        obtain ⟨i, hi, hfar⟩ := exists_far b J (by omega) x ρ hcount
        obtain ⟨F1, -, F3, F4, F6⟩ := FR b J hJ x hx (ne_centre b J x ρ hρ ⟨i, hi, hfar⟩)
        have hNρ : ρ ≤ N b J hJ x := hfar.trans (F1 i hi)
        refine ⟨?_, ?_, ?_⟩
        · rw [hΨ x hx]; exact F3
        · -- the coordinates off `J` and one boundary coordinate in `J` are integers
          obtain ⟨i₀, hi₀, hbd⟩ := F4
          refine ⟨insert i₀ (Finset.univ \ J), ?_, fun k hk => ?_⟩
          · rw [Finset.card_insert_of_notMem (by simp [hi₀]),
              Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ,
              Fintype.card_fin, hcard]
            omega
          · rw [hΨ x hx]
            rcases Finset.mem_insert.mp hk with rfl | hk'
            · rcases hbd with h | h
              · exact ⟨b k, h⟩
              · exact ⟨b k + 1, by rw [h]; push_cast; ring⟩
            · exact ⟨b k, ((hInF b J _).1 F3 k).2 (Finset.mem_sdiff.mp hk').2⟩
        · refine ⟨ρ / 2, by positivity, fun y hy hyx => ?_⟩
          have hney := ne_centre b J y (ρ / 2) (by positivity)
            (exists_far b J (by omega) y (ρ / 2) (count_near b J x y ρ hyx hcount))
          have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
            Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
          rw [hΨ y hy, hΨ x hx, show m + 2 - m - 1 = 1 by omega, pow_one]
          calc dist (R b J hJ y) (R b J hJ x)
              ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := F6 y hy hney
            _ ≤ (1 + 4 * Real.sqrt P) / ρ * dist y x := by
              apply mul_le_mul_of_nonneg_right _ dist_nonneg
              exact div_le_div₀ (by positivity) (by linarith) hρ hNρ
      | succ j hj ih =>
        -- 3. inductive step `j → j + 1`
        intro hP b J hcard x hx ρ hρ hcount
        have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
        have hΨ : ∀ u, InF b J u → Ψ (j + 1) u = Ψ j (R b J hJ u) := fun u hu => by
          rw [hrec' (j + 1) (by omega) hP b J hJ hcard u hu, Nat.add_sub_cancel]
        obtain ⟨i, hi, hfar⟩ := exists_far b J (by omega) x ρ hcount
        obtain ⟨F1, Fpos, F3, F4, F6⟩ := FR b J hJ x hx (ne_centre b J x ρ hρ ⟨i, hi, hfar⟩)
        have hNρ : ρ ≤ N b J hJ x := hfar.trans (F1 i hi)
        have hy₀k : ∀ k ∈ J, R b J hJ x k - b k - a k = (x k - b k - a k) / N b J hJ x := by
          intro k hk
          rw [hR, ite_eq_left hk]; ring
        have hΨx : Ψ (j + 1) x = Ψ j (R b J hJ x) := hΨ x hx
        -- `y₀ = ψ_{b,J}(x) = a_F + (x − a_F) / N_{b,J}(x)`
        obtain ⟨Nx, hNx⟩ : ∃ t, N b J hJ x = t := ⟨_, rfl⟩
        obtain ⟨y₀, hy₀⟩ : ∃ y, R b J hJ x = y := ⟨_, rfl⟩
        rw [hNx] at Fpos hNρ hy₀k F6
        rw [hy₀] at F3 F4 hy₀k hΨx F6
        have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
          Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
        -- (i) the `j`-faces `F(b^{i,β}, J ∖ {i})`, `β ∈ {bᵢ, bᵢ + 1}`, lie in `F(b, J)` and contain
        -- the points of `F(b, J)` with `i`-th coordinate `β`
        have hGsub : ∀ i' ∈ J, ∀ β : ℤ, b i' ≤ β → β ≤ b i' + 1 → ∀ u,
            InF (Function.update b i' β) (J.erase i') u → InF b J u := by
          intro i' hi' β hβ1 hβ2 u hu
          rw [hInF] at hu ⊢
          intro k
          by_cases hk : k = i'
          · subst hk
            have hu2 := (hu k).2 (Finset.notMem_erase k J)
            rw [Function.update_self] at hu2
            refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hi' h⟩
            · rw [hu2]; exact_mod_cast hβ1
            · rw [hu2]
              have h2 : ((β : ℤ) : ℝ) ≤ ((b k + 1 : ℤ) : ℝ) := Int.cast_le.mpr hβ2
              push_cast at h2 ⊢
              linarith
          · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
            have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
            obtain ⟨h1, h2⟩ := hu k
            rw [hupd, hmem] at h1 h2
            exact ⟨h1, h2⟩
        have hGmem : ∀ i' u, InF b J u → ∀ β : ℤ, u i' = β →
            InF (Function.update b i' β) (J.erase i') u := by
          intro i' u hu β hβ
          rw [hInF] at hu ⊢
          intro k
          by_cases hk : k = i'
          · subst hk
            refine ⟨fun h => absurd h (Finset.notMem_erase k J), fun _ => ?_⟩
            rw [Function.update_self]; exact hβ
          · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
            have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
            rw [hupd, hmem]
            exact hu k
        -- (ii) at `y₀` the counting condition holds on these faces with radius `ρ / N_{b,J}(x)`
        have hρN : 0 < ρ / Nx := div_pos hρ Fpos
        have hGcount : ∀ i' (β : ℤ),
            ((J.erase i').filter (fun k => |y₀ k - Function.update b i' β k - a k| < ρ / Nx)).card
              ≤ m + 1 := by
          intro i' β
          refine (count_le b (Function.update b i' β) J (J.erase i') x y₀ ρ (ρ / Nx)
            fun k hk h' => ?_).trans hcount
          obtain ⟨hki, hkJ⟩ := Finset.mem_erase.mp hk
          refine ⟨hkJ, ?_⟩
          rw [Function.update_of_ne hki, hy₀k k hkJ, abs_div, abs_of_pos Fpos] at h'
          exact (div_lt_div_iff_of_pos_right Fpos).mp h'
        -- (iii) Claim(j) on every face through `y₀`
        have hIH : ∀ i' ∈ J, ∀ β : ℤ, y₀ i' = β →
            InF (Function.update b i' β) (J.erase i') (Ψ j y₀) ∧
            (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j y₀ i = z) ∧
            ∃ δ > 0, ∀ y', InF (Function.update b i' β) (J.erase i') y' → dist y' y₀ < δ →
              dist (Ψ j y') (Ψ j y₀) ≤
                (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀ :=
          fun i' hi' β hβ => ih (by omega) (Function.update b i' β) (J.erase i')
            (by rw [Finset.card_erase_of_mem hi', hcard, Nat.add_sub_cancel]) y₀
            (hGmem i' y₀ F3 β hβ) (ρ / Nx) hρN (hGcount i' β)
        -- (A) and (B) from a face through `y₀`
        obtain ⟨i₁, hi₁, hbd₁⟩ := F4
        obtain ⟨β₁, hβ₁a, hβ₁b, hβ₁e⟩ : ∃ β : ℤ, b i₁ ≤ β ∧ β ≤ b i₁ + 1 ∧ y₀ i₁ = β := by
          rcases hbd₁ with h | h
          · exact ⟨b i₁, le_rfl, by omega, h⟩
          · exact ⟨b i₁ + 1, by omega, le_rfl, by rw [h]; push_cast; ring⟩
        obtain ⟨hA₁, hB₁, -⟩ := hIH i₁ hi₁ β₁ hβ₁e
        refine ⟨?_, ?_, ?_⟩
        · rw [hΨx]; exact hGsub i₁ hi₁ β₁ hβ₁a hβ₁b _ hA₁
        · rw [hΨx]; exact hB₁
        -- (iv) one radius `η` serves every face through `y₀` and avoids the other faces
        have hev : ∀ᶠ y' in 𝓝 y₀, ∀ i' ∈ J, ∀ e : Bool,
            (y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
              InF (Function.update b i' (if e then b i' + 1 else b i')) (J.erase i') y' →
              dist (Ψ j y') (Ψ j y₀) ≤
                (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀) ∧
            (y₀ i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
              y' i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ)) := by
          rw [Filter.eventually_all_finset]
          intro i' hi'
          rw [Filter.eventually_all]
          intro e
          by_cases hβ : y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ)
          · obtain ⟨-, -, δ', hδ', hbd⟩ := hIH i' hi' _ hβ
            filter_upwards [Metric.ball_mem_nhds y₀ hδ'] with y' hy'
            exact ⟨fun _ hG => hbd y' hG (Metric.mem_ball.mp hy'), fun h => absurd hβ h⟩
          · have hpos : 0 < |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| :=
              abs_pos.mpr (sub_ne_zero.mpr hβ)
            filter_upwards [Metric.ball_mem_nhds y₀ hpos] with y' hy'
            refine ⟨fun h => absurd h hβ, fun _ heq => ?_⟩
            have h1 : |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| ≤ dist y' y₀ := by
              rw [← heq, abs_sub_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le _ _ _
            exact absurd (Metric.mem_ball.mp hy') (not_lt.mpr h1)
        obtain ⟨η, hη, hηQ⟩ := Metric.eventually_nhds_iff.mp hev
        -- (v), (vi): for `y` near `x`, `ψ_{b,J}(y)` is `η`-close to `y₀` on a face through `y₀`
        have hc1 := hc J.card
        refine ⟨min (ρ / 2) (η * Nx / (1 + 4 * Real.sqrt J.card)),
          lt_min (half_pos hρ) (div_pos (mul_pos hη Fpos) hc1), fun y hy hyx => ?_⟩
        have hyx1 : dist y x < ρ / 2 := lt_of_lt_of_le hyx (min_le_left _ _)
        have hyx2 : dist y x < η * Nx / (1 + 4 * Real.sqrt J.card) :=
          lt_of_lt_of_le hyx (min_le_right _ _)
        have hney := ne_centre b J y (ρ / 2) (by positivity)
          (exists_far b J (by omega) y (ρ / 2) (count_near b J x y ρ hyx1 hcount))
        obtain ⟨-, -, F3y, F4y, -⟩ := FR b J hJ y hy hney
        have hd := F6 y hy hney
        have hdη : dist (R b J hJ y) y₀ < η := by
          refine hd.trans_lt ?_
          rw [div_mul_eq_mul_div, div_lt_iff₀ Fpos, mul_comm (1 + 4 * Real.sqrt J.card)]
          exact (lt_div_iff₀ hc1).mp hyx2
        obtain ⟨i₂, hi₂, hbd₂⟩ := F4y
        obtain ⟨e, he⟩ : ∃ e : Bool,
            R b J hJ y i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
          rcases hbd₂ with h | h
          · exact ⟨false, by simp [h]⟩
          · exact ⟨true, by simp [h]⟩
        obtain ⟨hQ1, hQ2⟩ := hηQ hdη i₂ hi₂ e
        have hy₀β : y₀ i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
          by_contra hcon
          exact hQ2 hcon he
        have hbound := hQ1 hy₀β (hGmem i₂ _ F3y _ he)
        rw [hΨ y hy, hΨx]
        calc dist (Ψ j (R b J hJ y)) (Ψ j y₀)
            ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist (R b J hJ y) y₀ := hbound
          _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) *
                ((1 + 4 * Real.sqrt J.card) / Nx * dist y x) := by gcongr
          _ = (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt J.card) / ρ * dist y x *
                (Nx * Nx⁻¹) := by rw [div_div_eq_mul_div]; ring
          _ = (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt J.card) / ρ * dist y x := by
              rw [mul_inv_cancel₀ Fpos.ne', mul_one]
          _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt P) / ρ * dist y x := by
              gcongr
          _ = (1 + 4 * Real.sqrt P) ^ (j + 1 - m - 1) / ρ * dist y x := by
              rw [show j + 1 - m - 1 = j - m - 1 + 1 by omega, pow_succ]
    -- 0. `K ^ (j - m - 1) ≤ K ^ P = c`, and `𝓝[F(b, J)] x` contains a `δ`-ball of `F(b, J)`
    intro j hj hjP b J hcard x hx ρ hρ hcount
    obtain ⟨hA, hB, δ, hδ, hC⟩ := hclaim j hj hjP b J hcard x ((hInF b J x).2 hx) ρ hρ hcount
    refine ⟨(hInF b J _).1 hA, hB, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy hyF
    calc dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x :=
          hC y ((hInF b J y).2 hyF) (Metric.mem_ball.mp hy)
      _ ≤ (1 + 4 * Real.sqrt P) ^ P / ρ * dist y x := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        apply div_le_div_of_nonneg_right _ hρ.le
        exact pow_le_pow_right₀ hK1 (by omega)
  -- at most `m + 1` coordinates satisfy `|xᵢ − bᵢ − aᵢ| < d(x)/√(m + 2)`: moving `m + 2` of
  -- them to `bᵢ + aᵢ` gives `w ∈ L*(a)` with `|x − w| < d(x)`
  have dual_dist_count : ∀ (P m : ℕ) (a x : Euclid P) (b : Fin P → ℤ),
      (Finset.univ.filter (fun i => |x i - b i - a i| < infDist x
        {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} /
          Real.sqrt (m + 2))).card ≤ m + 1 := by
    clear face_radial face_retraction_family face_count_induction
    intro P m a x b
    set L : Set (Euclid P) :=
      {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
    set d := infDist x L
    -- otherwise keep exactly `m + 2` coordinates with `|xᵢ − bᵢ − aᵢ| < d/√(m + 2)`
    by_contra! hcon
    obtain ⟨s, hsS, hscard⟩ := Finset.exists_subset_card_eq (n := m + 2) hcon
    -- moving them to `bᵢ + aᵢ` gives a point `w ∈ L*(a)`, so `d ≤ |x − w|`
    let w : Euclid P := WithLp.toLp 2 fun i => if i ∈ s then (b i : ℝ) + a i else x i
    have hw : ∀ i, w i = if i ∈ s then (b i : ℝ) + a i else x i := fun i => rfl
    have hwL : w ∈ L := ⟨s, hscard.ge, fun i hi => ⟨b i, by rw [hw i, ite_eq_left hi]; ring⟩⟩
    have hdw : d ≤ dist x w := infDist_le_dist_of_mem hwL
    -- `|x − w|² = Σ_{i ∈ s} (xᵢ − bᵢ − aᵢ)² < (m + 2) d²/(m + 2) = d²`
    have hm : (0 : ℝ) < m + 2 := by positivity
    have hsum : ∑ i, dist (x i) (w i) ^ 2 = ∑ i ∈ s, (x i - b i - a i) ^ 2 := by
      rw [← Finset.sum_subset (f := fun i => dist (x i) (w i) ^ 2) (Finset.subset_univ s)
        fun i _ hi => by simp [hw i, hi]]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hw i, ite_eq_left hi, Real.dist_eq, sq_abs]
      ring
    have hlt : ∑ i ∈ s, (x i - b i - a i) ^ 2 < d ^ 2 :=
      calc ∑ i ∈ s, (x i - b i - a i) ^ 2 < ∑ _i ∈ s, (d / √(m + 2)) ^ 2 := by
            refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) fun i hi => ?_
            have hi' := (Finset.mem_filter.mp (hsS hi)).2
            rw [← sq_abs]
            gcongr
        _ = d ^ 2 := by
            rw [Finset.sum_const, hscard, nsmul_eq_mul, div_pow, Real.sq_sqrt hm.le]
            push_cast
            field_simp
    have hxw : dist x w < d := by
      rw [EuclideanSpace.dist_eq, hsum]
      calc √(∑ i ∈ s, (x i - b i - a i) ^ 2) < √(d ^ 2) :=
            Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _) hlt
        _ = d := Real.sqrt_sq infDist_nonneg
    exact lt_irrefl d (hdw.trans_lt hxw)
  -- the finitely many closed unit cubes `z + [0, 1]ᴾ` containing `x` cover a neighbourhood of
  -- `x` (corners in `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}`)
  have cube_cover : ∀ (P : ℕ) (x : Euclid P), ∃ Z : Finset (Fin P → ℤ),
      (∀ z ∈ Z, ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) ∧
      ∀ᶠ y : Euclid P in 𝓝 x, ∃ z ∈ Z, ∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1 := by
    clear face_radial face_retraction_family face_count_induction dual_dist_count
    intro P x
    classical
    -- step 2: the corners in `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`
    let T : Fin P → Finset ℤ := fun i => {⌊x i⌋ - 1, ⌊x i⌋}
    refine ⟨(Fintype.piFinset T).filter fun z => ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1,
      fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
    -- step 1: the intervals `[k, k + 1] ∋ xᵢ`, `k ∈ Tᵢ`, cover a neighbourhood of `xᵢ`
    have h1d : ∀ i, ∀ᶠ t in 𝓝 (x i), ∃ k ∈ T i,
        ((k : ℝ) ≤ x i ∧ x i ≤ k + 1) ∧ (k : ℝ) ≤ t ∧ t ≤ k + 1 := by
      intro i
      have hfl : (⌊x i⌋ : ℝ) ≤ x i := Int.floor_le (x i)
      have hfl' : x i < ⌊x i⌋ + 1 := Int.lt_floor_add_one (x i)
      have hk : ⌊x i⌋ ∈ T i := by simp [T]
      have hk' : ⌊x i⌋ - 1 ∈ T i := by simp [T]
      rcases hfl.lt_or_eq with hlt | heq
      · -- `xᵢ ∉ ℤ`: `[⌊xᵢ⌋, ⌊xᵢ⌋ + 1]` contains the neighbourhood `(⌊xᵢ⌋, ⌊xᵢ⌋ + 1)`
        filter_upwards [Ioo_mem_nhds hlt hfl'] with t ht
        exact ⟨⌊x i⌋, hk, ⟨hfl, hfl'.le⟩, ht.1.le, ht.2.le⟩
      · -- `xᵢ ∈ ℤ`: `[xᵢ − 1, xᵢ] ∪ [xᵢ, xᵢ + 1]` contains the neighbourhood `(xᵢ − 1, xᵢ + 1)`
        filter_upwards [Ioo_mem_nhds (sub_one_lt (x i)) (lt_add_one (x i))] with t ht
        rcases le_total t (x i) with hle | hge
        · refine ⟨⌊x i⌋ - 1, hk', ?_⟩
          push_cast
          exact ⟨⟨by linarith, by linarith⟩, by linarith [ht.1], by linarith⟩
        · exact ⟨⌊x i⌋, hk, ⟨hfl, hfl'.le⟩, by linarith, by linarith [ht.2]⟩
    -- step 3: pull back along the continuous coordinates and intersect the finitely many
    -- neighbourhoods
    have hall : ∀ᶠ y : Euclid P in 𝓝 x, ∀ i, ∃ k ∈ T i,
        ((k : ℝ) ≤ x i ∧ x i ≤ k + 1) ∧ (k : ℝ) ≤ y i ∧ y i ≤ k + 1 :=
      eventually_all.mpr fun i => ((PiLp.continuous_apply 2 _ i).tendsto x).eventually (h1d i)
    -- step 4: choose the corner coordinate by coordinate
    filter_upwards [hall] with y hy
    choose k hkT hk using hy
    exact ⟨k, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hkT, fun i => (hk i).1⟩,
      fun i => (hk i).2⟩
  -- Step (6a), segment argument: local `K`-Lipschitz bounds at the points of `[x, y]` give
  -- `|f(y) − f(x)| ≤ K|y − x|` (continuous induction on `[0, 1]`)
  have segment_lipschitz : ∀ (P : ℕ) (f : Euclid P → Euclid P) (x y : Euclid P) (K : ℝ), 0 ≤ K →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ w in 𝓝 (x + t • (y - x)),
        dist (f w) (f (x + t • (y - x))) ≤ K * dist w (x + t • (y - x))) →
      dist (f y) (f x) ≤ K * dist y x := by
    clear face_radial face_retraction_family face_count_induction dual_dist_count cube_cover
    intro P f x y K hK hloc
    -- the segment `g(t) = x + t(y − x)`, with `|g(s) − g(t)| = |s − t| |y − x|`
    let g : ℝ → Euclid P := fun t => x + t • (y - x)
    have hgcont : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
    have hgdist : ∀ s t : ℝ, dist (g s) (g t) = |s - t| * dist y x := by
      intro s t
      simp only [g, dist_eq_norm]
      rw [show x + s • (y - x) - (x + t • (y - x)) = (s - t) • (y - x) by rw [sub_smul]; abel,
        norm_smul, Real.norm_eq_abs]
    -- the local bounds make `f` continuous at each `g(t)`, hence `f ∘ g` continuous on `[0, 1]`
    have hfcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun s => f (g s)) t := by
      intro t ht
      have hft : ContinuousAt f (g t) := by
        rw [Metric.continuousAt_iff']
        intro ε hε
        have hball : ∀ᶠ w in 𝓝 (g t), dist w (g t) < ε / (K + 1) :=
          Metric.ball_mem_nhds _ (by positivity)
        filter_upwards [hloc t ht, hball] with w h1 h2
        calc dist (f w) (f (g t)) ≤ K * dist w (g t) := h1
          _ ≤ K * (ε / (K + 1)) := by gcongr
          _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
            nlinarith
      exact hft.comp hgcont.continuousAt
    have hcontOn : ContinuousOn (fun t => dist (f (g t)) (f x) - K * t * dist y x) (Icc 0 1) := by
      intro t ht
      apply ContinuousWithinAt.sub
      · have hca : ContinuousAt (fun s => dist (f (g s)) (f x)) t :=
          (hfcont t ht).dist continuousAt_const
        exact hca.continuousWithinAt
      · exact ((continuous_const.mul continuous_id).mul continuous_const).continuousWithinAt
    -- `S ∩ [0, 1]` is closed and `0 ∈ S`
    let S : Set ℝ := {t | dist (f (g t)) (f x) ≤ K * t * dist y x}
    have hS_closed : IsClosed (S ∩ Icc 0 1) := by
      have := hcontOn.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
      convert this using 1
      ext t
      simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, sub_nonpos]
      tauto
    have h0 : (0 : ℝ) ∈ S := by
      show dist (f (x + (0 : ℝ) • (y - x))) (f x) ≤ K * 0 * dist y x
      simp
    -- right extension: for `t ∈ S ∩ [0, 1)`, the local bound at `g(t)` gives `(t, t + δ) ⊆ S`
    have hstep : ∀ t ∈ S ∩ Ico (0 : ℝ) 1, S ∈ 𝓝[>] t := by
      rintro t ⟨htS, ht⟩
      have hev : ∀ᶠ s in 𝓝 t, dist (f (g s)) (f (g t)) ≤ K * dist (g s) (g t) :=
        (hgcont.tendsto t).eventually (hloc t ⟨ht.1, ht.2.le⟩)
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hst
      have hst' : t < s := hst
      have htS' : dist (f (g t)) (f x) ≤ K * t * dist y x := htS
      show dist (f (g s)) (f x) ≤ K * s * dist y x
      calc dist (f (g s)) (f x) ≤ dist (f (g s)) (f (g t)) + dist (f (g t)) (f x) :=
            dist_triangle _ _ _
        _ ≤ K * dist (g s) (g t) + K * t * dist y x := add_le_add hs htS'
        _ = K * s * dist y x := by rw [hgdist, abs_of_pos (sub_pos.mpr hst')]; ring
    -- continuous induction on `[0, 1]`, evaluated at `t = 1`
    have h1 : (1 : ℝ) ∈ S :=
      IsClosed.Icc_subset_of_forall_mem_nhdsWithin hS_closed h0 hstep ⟨zero_le_one, le_rfl⟩
    have h1' : dist (f (g 1)) (f x) ≤ K * 1 * dist y x := h1
    rwa [show g 1 = y by simp [g], mul_one] at h1'
  -- Assembly (steps 5–6): `ψ := Ψ_P`, `c = 2√(m + 2)·c₀ + 4√P + 1`
  clear face_radial
  intro P m hmP
  obtain ⟨c₀, hc₀, hind⟩ := face_count_induction P m
  clear face_count_induction
  have hs : 0 < Real.sqrt (m + 2) := Real.sqrt_pos.2 (by positivity)
  have hsc : 0 ≤ Real.sqrt (m + 2) * c₀ := by positivity
  refine ⟨2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1, by positivity, fun a ha => ?_⟩
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := face_retraction_family P m a ha
  clear face_retraction_family
  set L : Set (Euclid P) :=
    {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- the closed unit cube `z + [0,1]^P` is the `P`-face `F(z, univ)`
  have hface : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      ∀ i : Fin P, (i ∈ Finset.univ → (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) ∧
        (i ∉ Finset.univ → u i = z i) :=
    fun z u hu i => ⟨fun _ => hu i, fun h => absurd (Finset.mem_univ i) h⟩
  -- a closed unit cube has diameter `√P`
  have hdiam : ∀ (z : Fin P → ℤ) (u v : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      (∀ i, (z i : ℝ) ≤ v i ∧ v i ≤ z i + 1) → dist u v ≤ Real.sqrt P := by
    intro z u v hu hv
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (u i) (v i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : dist (u i) (v i) ≤ 1 := by
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
          nlinarith [dist_nonneg (x := u i) (y := v i)]
      _ = P := by simp
  -- step 5 on one cube: `face_count_induction` with `j = P`, `J = univ` and `ρ = d(u)/√(m+2)`
  have hcube : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      0 < infDist u L → (∀ i, (z i : ℝ) ≤ Ψ P u i ∧ Ψ P u i ≤ z i + 1) ∧
        (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ k : ℤ, Ψ P u i = k) ∧
        ∀ᶠ y : Euclid P in 𝓝 u, (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) →
          dist (Ψ P y) (Ψ P u) ≤ Real.sqrt (m + 2) * c₀ / infDist u L * dist y u := by
    intro z u hu hd
    obtain ⟨hA, hB, hC⟩ := hind a ha Ψ hΨ₀ hΨ P (by omega) le_rfl z Finset.univ (by simp) u
      (hface z u hu) _ (div_pos hd hs) (dual_dist_count P m a u z)
    refine ⟨fun i => (hA i).1 (Finset.mem_univ i), hB, ?_⟩
    filter_upwards [eventually_nhdsWithin_iff.1 hC] with y hy hyz
    exact (hy (hface z y hyz)).trans_eq (by rw [div_div_eq_mul_div, mul_comm c₀])
  clear dual_dist_count
  -- the pointwise bound `D̄ψ(u) ≤ √(m+2)·c₀/d(u)`: the cubes through `u` cover a neighbourhood
  have hloc : ∀ u : Euclid P, 0 < infDist u L → ∀ᶠ y : Euclid P in 𝓝 u,
      dist (Ψ P y) (Ψ P u) ≤ Real.sqrt (m + 2) * c₀ / infDist u L * dist y u := by
    intro u hu
    obtain ⟨Z, hZu, hZ⟩ := cube_cover P u
    have hall : ∀ᶠ y : Euclid P in 𝓝 u, ∀ z ∈ Z, (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) →
        dist (Ψ P y) (Ψ P u) ≤ Real.sqrt (m + 2) * c₀ / infDist u L * dist y u :=
      (eventually_all_finset Z).2 fun z hz => (hcube z u (hZu z hz) hu).2.2
    filter_upwards [hall, hZ] with y hy hyZ
    obtain ⟨z, hz, hyz⟩ := hyZ
    exact hy z hz hyz
  clear cube_cover
  -- (i): `x` and `ψ(x)` lie in the cube `⌊x⌋ + [0,1]^P`
  have hI : ∀ x : Euclid P, 0 < infDist x L →
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ P x i = z) ∧
        dist (Ψ P x) x ≤ Real.sqrt P := by
    intro x hx
    have hfl : ∀ i, ((⌊x i⌋ : ℤ) : ℝ) ≤ x i ∧ x i ≤ ⌊x i⌋ + 1 :=
      fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    obtain ⟨hA, hB, -⟩ := hcube (fun i => ⌊x i⌋) x hfl hx
    exact ⟨hB, hdiam (fun i => ⌊x i⌋) (Ψ P x) x hA hfl⟩
  refine ⟨Ψ P, hI, fun r hr hr4 x y hx hy => ?_⟩
  rcases lt_or_ge (dist x y) (r / 2) with hxy | hxy
  · -- (6a): `d > r/2` on `[x, y]`, where `ψ` is locally `(2√(m+2)·c₀/r)`-Lipschitz
    have hseg : dist (Ψ P y) (Ψ P x) ≤ 2 * Real.sqrt (m + 2) * c₀ / r * dist y x := by
      refine segment_lipschitz P (Ψ P) x y (2 * Real.sqrt (m + 2) * c₀ / r)
        (by positivity) fun t ht => ?_
      have hxw : dist x (x + t • (y - x)) ≤ dist x y := by
        calc dist x (x + t • (y - x)) = t * dist x y := by
              rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg ht.1, dist_comm, dist_eq_norm]
          _ ≤ dist x y := mul_le_of_le_one_left dist_nonneg ht.2
      have hdw : r / 2 < infDist (x + t • (y - x)) L := by
        linarith [infDist_le_infDist_add_dist (x := x) (y := x + t • (y - x)) (s := L)]
      have hdw₀ : 0 < infDist (x + t • (y - x)) L := by linarith
      filter_upwards [hloc (x + t • (y - x)) hdw₀] with w hw
      refine hw.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [div_le_div_iff₀ hdw₀ hr]
      nlinarith [mul_le_mul_of_nonneg_left hdw.le hsc]
    rw [dist_comm, dist_comm x]
    refine hseg.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hr.le)
      dist_nonneg)
    linarith [Real.sqrt_nonneg (P : ℝ)]
  · -- (6b): `|ψ(x) − ψ(y)| ≤ |ψ(x) − x| + |x − y| + |y − ψ(y)| ≤ 2√P + |x − y|`
    have h1 := (hI x (by linarith)).2
    have h2 := (hI y (by linarith)).2
    calc dist (Ψ P x) (Ψ P y) ≤ dist (Ψ P x) x + dist x y + dist y (Ψ P y) :=
          dist_triangle4 _ _ _ _
      _ ≤ 2 * Real.sqrt P + dist x y := by rw [dist_comm y]; linarith
      _ ≤ (2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1) / r * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        nlinarith [mul_nonneg hsc (dist_nonneg (x := x) (y := y)),
          mul_nonneg (Real.sqrt_nonneg (P : ℝ)) (by linarith : (0 : ℝ) ≤ 4 * dist x y - 2 * r),
          mul_nonneg (dist_nonneg (x := x) (y := y)) (by linarith : (0 : ℝ) ≤ 1 - r)]
/-- **Tube about the shifted dual skeleton** (Simon Ch. 6, proof of 5.1, the identity before
display (6), inclusion `⊆`).  Let `L*(a)` be the set of `w` with `w_i − a_i ∈ ℤ` for at least
`m + 2` indices `i`.  It contains `a`, so `infDist x L*(a) < r` gives `w ∈ L*(a)` with
`|x − w| < r`.  Enumerate `m + 2` of the indices of `w` by `e`, and put
`z_k = w_{e(k)} − a_{e(k)} ∈ ℤ`.  Then
`Σ_k (x_{e(k)} − a_{e(k)} − z_k)² = Σ_k (x_{e(k)} − w_{e(k)})² ≤ |x − w|² < r²`. -/
theorem Submission.cmcdt_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
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
theorem Submission.cmcdt_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
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
theorem Submission.cmcdt_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
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

/-- **Simon 6.5.1, proof, (1)–(7): a good centre for the shifted dual skeleton.**  For
`m + 1 < P` there is `C = C(P, m)` such that any two finite measures `μ, μ'` on `ℝᴾ` have a common
centre `a ∈ (1/4, 3/4)ᴾ` for which the `r`-tube about
`L*(a) = {w : wᵢ − aᵢ ∈ ℤ for at least m + 2 indices i}` has `μ`-measure `≤ C r^{m+2} μ(ℝᴾ)` and
`μ'`-measure `≤ C r^{m+2} μ'(ℝᴾ)` for every `r ∈ (0, 1/4]`.  Put `d = m + 2`,
`K = #(Fin d → Fin P)`, `β = 2K·10ᵈ·2ᴾ + 1` and `prj_e x = (x_{e k})_k`.  The bad centres `E_e` of
the image measures `prj_e#μ`, `prj_e#μ'` have volume `≤ 2·10ᵈ/β` (`cmcdt_gc_bad_set_volume`), so
`Σ_e |E_e| ≤ 2K·10ᵈ/β < (1/2)ᴾ` and `cmcdt_gc_cube_selection` gives `a` with `prj_e a ∉ E_e` for
every injective `e`.  The tube lies in `⋃_e prj_e⁻¹(O_r(prj_e a))` (`cmcdt_gc_tube_cover`), where
`O_r(g)` is the union of the balls `B_r(g + z)`, `z ∈ ℤᵈ`; each piece has `ν`-measure
`≤ β rᵈ ν(ℝᴾ)` because `prj_e a` is not bad for `prj_e#ν`, hence `C = Kβ`. -/
theorem Submission.cmcdt_good_center : ∀ (P m : ℕ), m + 1 < P → ∃ C : NNReal, ∀ μ μ' : Measure (Euclid P), IsFiniteMeasure μ → IsFiniteMeasure μ' → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ univ ∧ μ' {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ' univ := by
  classical
  intro P m hPm
  -- the constants `K = #(Fin (m + 2) → Fin P)`, `β = 2K·10^{m+2}·2ᴾ + 1` and `C = Kβ`
  set K : ℕ := Fintype.card (Fin (m + 2) → Fin P) with hK
  set β : ℝ := 2 * K * 10 ^ (m + 2) * 2 ^ P + 1 with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨Real.toNNReal (K * β), ?_⟩
  intro μ μ' hμ hμ'
  -- the coordinate projections `prj_e x = (x_{e k})_k`
  let prj : (Fin (m + 2) → Fin P) → Euclid P → (Fin (m + 2) → ℝ) := fun e x k => x (e k)
  have hprj : ∀ e, Measurable (prj e) := fun e =>
    (continuous_pi fun k => PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (e k)).measurable
  -- the bad centres `g ∈ (1/4, 3/4)^{m+2}` of `ρ`: `ρ(O_r(g)) > β r^{m+2} ρ(ℝ^{m+2})` for some
  -- `r ∈ (0, 1/4]`
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
          add_le_add (Submission.cmcdt_gc_bad_set_volume (m + 2) _ inferInstance β hβpos)
            (Submission.cmcdt_gc_bad_set_volume (m + 2) _ inferInstance β hβpos)
      _ = 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := (two_mul _).symm
  -- so the bad sets have total volume `≤ 2K·10^{m+2}/β < (1/2)ᴾ`
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
  -- a centre `a ∈ (1/4, 3/4)ᴾ` none of whose projections `prj_e a` (`e` injective) is bad
  obtain ⟨a, ha, hgood⟩ := Submission.cmcdt_gc_cube_selection P (m + 2) E hsum
  refine ⟨a, ha, ?_⟩
  intro r hr0 hr1
  have key : ∀ ν : Measure (Euclid P),
      (∀ e : Fin (m + 2) → Fin P, Function.Injective e → prj e a ∉ Bad (ν.map (prj e))) →
      ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤
        (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
    intro ν hνgood
    -- the periodic unions of balls `O_e = O_r(prj_e a)` and the pieces `T_e = prj_e⁻¹(O_e)`
    -- (`e` injective) of the tube
    let O : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
      {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - prj e a k - z k) ^ 2 < r ^ 2}
    let T : (Fin (m + 2) → Fin P) → Set (Euclid P) := fun e =>
      {x | Function.Injective e ∧ prj e x ∈ O e}
    have hcover : {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ⊆ ⋃ e, T e := by
      intro x hx
      obtain ⟨e, he, z, hz⟩ := Submission.cmcdt_gc_tube_cover P m hPm a x r hx
      exact mem_iUnion.2 ⟨e, he, z, hz⟩
    -- `ν(T_e) ≤ prj_e#ν(O_e) ≤ β r^{m+2} ν(ℝᴾ)`, since `prj_e a` is not bad for `prj_e#ν`
    have hT : ∀ e, ν (T e) ≤ ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
      intro e
      by_cases he : Function.Injective e
      · have hsub : T e ⊆ prj e ⁻¹' O e := fun x hx => hx.2
        have hcube : ∀ k, |prj e a k - 1 / 2| < 1 / 4 := fun k => ha (e k)
        have hle : (ν.map (prj e)) (O e) ≤
            ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := by
          by_contra hlt
          exact hνgood e he ⟨hcube, r, hr0, hr1, not_le.1 hlt⟩
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
    -- finite subadditivity over the `K` maps `e`
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
  exact ⟨key μ fun e he h => hgood e he (Or.inl h), key μ' fun e he h => hgood e he (Or.inr h)⟩
/-- Integer median of an integer-valued function of bounded variation on the open unit cube
(the BV facts used in Simon 6.5.1, (26)–(33)): the Poincaré inequality, the bound on the median
and the boundary estimate.  The proof works with translations: for a smooth `ψ` supported in an
open `S` whose segments `S + [0, 1] h` stay in the cube, the field `(∫₀¹ ψ(· - τh) dτ) h` is
admissible, which bounds `∫ (u(x + h) - u(x)) ψ(x) dx`; a duality argument (smooth cut-offs and
inner regularity) turns this into an `L¹` bound for translation differences.  Integrating over
`h` gives the Poincaré inequality, the least integer `β` with `|{u ≤ β}| ≥ 1/2` is a median, and
difference quotients of `G` together with slab estimates near the faces give the boundary bound. -/
theorem Submission.dtc_bc_lc_fd_dfm_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
  intro m
  /- Step 1: duality.  If `|∫ f ψ| ≤ B` for all smooth `ψ` with compact support in the open set
  `S` and `|ψ| ≤ 1`, then `∫_S |f| ≤ 2 B`: smooth cut-offs give `|∫_K f| ≤ B` for compact
  `K ⊆ S`, inner regularity extends this to measurable subsets, and we split `S` by the sign of
  `f`. -/
  have hdual : ∀ (f : Euclid (m + 1) → ℝ) (S : Set (Euclid (m + 1))) (B : ℝ), Integrable f →
      Measurable f → IsOpen S → volume S ≠ ⊤ →
      (∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
        (∀ x, |ψ x| ≤ 1) → |∫ x, f x * ψ x| ≤ B) → ∫ x in S, |f x| ≤ 2 * B := by
    intro f S B hf hfm hSo hSfin hB
    have H1 : ∀ K, IsCompact K → K ⊆ S → |∫ x in K, f x| ≤ B := by
      intro K hK hKS
      obtain ⟨δ, hδ, hδS⟩ := hK.exists_cthickening_subset_open hSo hKS
      have hr : ∀ k : ℕ, 0 < δ / (k + 2) := fun k => by positivity
      have hrδ : ∀ k : ℕ, δ / (k + 2) ≤ δ := fun k =>
        div_le_self hδ.le (by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)])
      choose ψ hψsm hψr hψs hψ1 using fun k : ℕ =>
        exists_contDiff_support_eq_eq_one_iff (n := ⊤)
          (isOpen_thickening : IsOpen (thickening (δ / (k + 2)) K))
          hK.isClosed (self_subset_thickening (hr k) K)
      have htsupp : ∀ k, tsupport (ψ k) ⊆ cthickening (δ / (k + 2)) K := fun k => by
        rw [tsupport, hψs k]; exact closure_thickening_subset_cthickening _ _
      have hψabs : ∀ k x, |ψ k x| ≤ 1 := fun k x => by
        have := hψr k (mem_range_self x)
        rw [abs_le]; exact ⟨by linarith only [this.1], this.2⟩
      have hbd : ∀ k, |∫ x, f x * ψ k x| ≤ B := fun k => hB (ψ k) (hψsm k)
          ((hK.cthickening).of_isClosed_subset (isClosed_tsupport _) (htsupp k))
          ((htsupp k).trans ((cthickening_mono (hrδ k) K).trans hδS)) (hψabs k)
      have hlim : Tendsto (fun k => ∫ x, f x * ψ k x) atTop (𝓝 (∫ x, K.indicator f x)) := by
        refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
          (fun k => hf.aestronglyMeasurable.mul (hψsm k).continuous.aestronglyMeasurable) hf.abs
          (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hψabs k x)
        · by_cases hx : x ∈ K
          · rw [indicator_of_mem hx]
            have : ∀ k, ψ k x = 1 := fun k => (hψ1 k x).1 hx
            simp only [this, mul_one, tendsto_const_nhds]
          · rw [indicator_of_notMem hx]
            obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hx
            have hev : ∀ᶠ k : ℕ in atTop, ψ k x = 0 := by
              obtain ⟨k₀, hk₀⟩ := exists_nat_gt (δ / ε)
              filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
              have hxt : x ∉ thickening (δ / (k + 2)) K := by
                intro hxt
                obtain ⟨y, hyK, hxy⟩ := mem_thickening_iff.1 hxt
                have hk2 : (k₀:ℝ) ≤ k := by exact_mod_cast hk
                have hk' : δ < ε * ((k:ℝ) + 2) := by
                  rw [div_lt_iff₀ hε] at hk₀
                  have := mul_le_mul_of_nonneg_right hk2 hε.le
                  linarith only [hk₀, this, hε]
                have : δ / (k + 2) < ε := by
                  rw [div_lt_iff₀ (by positivity)]; linarith only [hk']
                exact hball (mem_ball.2 (by rw [dist_comm]; linarith only [hxy, this])) hyK
              rw [← hψs k] at hxt
              exact notMem_support.1 hxt
            exact tendsto_const_nhds.congr' (by
              filter_upwards [hev] with k hk; rw [hk, mul_zero])
      rw [integral_indicator hK.isClosed.measurableSet] at hlim
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have H2 : ∀ T, MeasurableSet T → T ⊆ S → |∫ x in T, f x| ≤ B := by
      intro T hT hTS
      have hTfin : volume T ≠ ⊤ := ne_top_of_le_ne_top hSfin (measure_mono hTS)
      have : ∀ j : ℕ, ∃ K ⊆ T, IsCompact K ∧ volume T < volume K + ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
        fun j => hT.exists_isCompact_lt_add hTfin
          (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      choose K hKT hKc hKlt using this
      have hdiff : Tendsto (fun j => volume (T \ K j)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) (fun _ => bot_le)
          (fun j => ?_)
        rw [Function.comp_apply, measure_sdiff (hKT j)
          (hKc j).isClosed.measurableSet.nullMeasurableSet
          (ne_top_of_le_ne_top hTfin (measure_mono (hKT j)))]
        exact tsub_le_iff_left.2 (hKlt j).le
      have hconv := hf.tendsto_setIntegral_nhds_zero hdiff
      have hle : ∀ j, |∫ x in T, f x| ≤ B + |∫ x in T \ K j, f x| := fun j => by
        rw [← union_sdiff_cancel (hKT j), setIntegral_union disjoint_sdiff_right
          (hT.diff (hKc j).isClosed.measurableSet) hf.integrableOn hf.integrableOn,
          union_sdiff_cancel (hKT j)]
        have := H1 (K j) (hKc j) ((hKT j).trans hTS)
        exact (abs_add_le _ _).trans (by linarith only [this])
      have hconv' : Tendsto (fun j => B + |∫ x in T \ K j, f x|) atTop (𝓝 (B + |0|)) :=
        tendsto_const_nhds.add ((continuous_abs.tendsto 0).comp hconv)
      rw [abs_zero, add_zero] at hconv'
      exact ge_of_tendsto' hconv' hle
    have hP : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hfm
    have hSm := hSo.measurableSet
    have e : ∫ x in S, |f x| =
        (∫ x in S ∩ {x | 0 ≤ f x}, f x) - ∫ x in S \ {x | 0 ≤ f x}, f x := by
      rw [← integral_inter_add_sdiff hP hf.abs.integrableOn, sub_eq_add_neg, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun (hSm.inter hP) (fun x hx => abs_of_nonneg hx.2)
      · exact setIntegral_congr_fun (hSm.diff hP) (fun x hx => abs_of_neg (not_le.1 hx.2))
    rw [e]
    have h1 := H2 _ (hSm.inter hP) inter_subset_left
    have h2 := H2 _ (hSm.diff hP) sdiff_subset
    linarith only [h1, h2, le_abs_self (∫ x in S ∩ {x | 0 ≤ f x}, f x),
      neg_abs_le (∫ x in S \ {x | 0 ≤ f x}, f x)]
  /- Step 2: the segment average `Ψ z = ∫₀¹ ψ (z - τ h) dτ` of a smooth compactly supported `ψ`
  is smooth, and its derivative in the direction `h` is `ψ z - ψ (z - h)`. -/
  have hΨd : ∀ (h : Euclid (m + 1)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ z, HasFDerivAt (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h))
        (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) z := by
    intro h F _ _ _ ψ hψ hψc z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hψc.fderiv ℝ)
    have hsc : Continuous fun τ : ℝ => τ • h := continuous_id.smul continuous_const
    have hcont : ∀ x : Euclid (m + 1), Continuous fun τ : ℝ => ψ (x - τ • h) := fun x =>
      hψ.continuous.comp (continuous_const.sub hsc)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (μ := volume.restrict (Ioc (0:ℝ) 1)) (F := fun x τ => ψ (x - τ • h))
      (F' := fun x τ => fderiv ℝ ψ (x - τ • h)) (bound := fun _ => C) (s := univ)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable
    · exact (hcont z).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact ((hdc.comp (continuous_const.sub hsc)).stronglyMeasurable
        (h := secondCountableTopologyEither_of_left ℝ _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun τ x _ => hC _
    · exact integrableOn_const (by simp)
    · refine Filter.Eventually.of_forall fun τ x _ => ?_
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x - τ • h)) (x - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 := h1.comp x ((hasFDerivAt_id x).sub_const (τ • h))
      rwa [ContinuousLinearMap.comp_id] at h2
  have hΨs : ∀ (h : Euclid (m + 1)) (k : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ContDiff ℝ k (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) := by
    intro h k
    induction k with
    | zero =>
      intro F _ _ _ ψ hψ hψc
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
        (hΨd h F ψ hψ hψc z).continuousAt)
    | succ k ih =>
      intro F _ _ _ ψ hψ hψc
      have hfd : fderiv ℝ (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) =
          fun z => ∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h) :=
        funext fun z => (hΨd h F ψ hψ hψc z).fderiv
      refine contDiff_succ_iff_fderiv.2 ⟨fun z => (hΨd h F ψ hψ hψc z).differentiableAt,
        fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
      rw [hfd]
      exact ih (Euclid (m + 1) →L[ℝ] F) (fderiv ℝ ψ) (contDiff_infty_iff_fderiv.1 hψ).2
        (hψc.fderiv ℝ)
  have hΨh : ∀ (h : Euclid (m + 1)) (ψ : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ∀ z, (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) h = ψ z - ψ (z - h) := by
    intro h ψ hψ z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    have hLc : Continuous fun τ : ℝ => fderiv ℝ ψ (z - τ • h) :=
      hdc.comp (continuous_const.sub (continuous_id.smul continuous_const))
    rw [ContinuousLinearMap.integral_apply (hLc.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      ← intervalIntegral.integral_of_le zero_le_one]
    have hderiv : ∀ τ ∈ uIcc (0:ℝ) 1, HasDerivAt (fun τ : ℝ => ψ (z - τ • h))
        (-(fderiv ℝ ψ (z - τ • h) h)) τ := by
      intro τ _
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (z - τ • h)) (z - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 : HasDerivAt (fun τ : ℝ => z - τ • h) (-h) τ := by
        have := ((hasDerivAt_id τ).smul_const h).const_sub z
        rwa [one_smul] at this
      have := h1.comp_hasDerivAt τ h2
      rwa [map_neg] at this
    have hint : IntervalIntegrable (fun τ : ℝ => -(fderiv ℝ ψ (z - τ • h) h)) volume 0 1 :=
      (((ContinuousLinearMap.apply ℝ ℝ h).continuous.comp hLc).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_neg, one_smul, zero_smul, sub_zero] at this
    linarith only [this]
  /- Step 3: the constants: `R` bounds the diameter of the cube, `CP` is the Poincaré constant. -/
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = m + 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR_def]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨CP, hCP_def⟩ : ∃ CP : ℝ,
      CP = 4 * R * (volume (closedBall (0 : Euclid (m + 1)) R)).toReal := ⟨_, rfl⟩
  have hCP : 0 ≤ CP := by rw [hCP_def]; positivity
  refine ⟨CP + (m + 1) * (10 + 4 * CP) + 1, by positivity, ?_⟩
  intro u V hint huQ hV
  set Q := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} with hQ_def
  /- Step 4: the cube, `V ≥ 0`, and a measurable version `ub` of `u 1_Q`. -/
  have hQo : IsOpen Q := by
    have : Q = ⋂ i, {y : Euclid (m + 1) | 0 < y i ∧ y i < 1} := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_iInter]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQvol : volume Q = 1 := by
    have : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ => Ioo (0:ℝ) 1) := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_preimage, mem_univ_pi, mem_Ioo]
    rw [this, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hQfin : volume Q ≠ ⊤ := by rw [hQvol]; exact ENNReal.one_ne_top
  have hV0 : 0 ≤ V := by
    have := hV (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa using this
  obtain ⟨ub, hub_meas, hub_int, hub_zero, hub_ae⟩ : ∃ ub : Euclid (m + 1) → ℝ, Measurable ub ∧
      Integrable ub ∧ (∀ y ∉ Q, ub y = 0) ∧ ∀ᵐ y ∂(volume.restrict Q), ub y = u y := by
    refine ⟨Q.indicator (huQ.aestronglyMeasurable.mk u),
      huQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator hQm, ?_,
      fun y hy => indicator_of_notMem hy _, ?_⟩
    · rw [integrable_indicator_iff hQm]
      exact huQ.congr huQ.aestronglyMeasurable.ae_eq_mk
    · filter_upwards [huQ.aestronglyMeasurable.ae_eq_mk, ae_restrict_mem hQm] with y hy hyQ
      rw [indicator_of_mem hyQ, ← hy]
  /- Step 5: the weak translation estimate.  If `S` is open, `S + [0, 1] h ⊆ Q`, and every line
  parallel to `h` meets `S` in parameter length `≤ lam`, then the field
  `g = (lam ‖h‖)⁻¹ Ψ h` is admissible and `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`. -/
  have hweak : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam → h ≠ 0 →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      (∀ x, |ψ x| ≤ 1) → -∫ x, (ub (x + h) - ub x) * ψ x ≤ lam * ‖h‖ * V := by
    intro S h lam hSo hseg hlam hh0 hmult ψ hψ hψc hψS hψ1
    have hA : 0 < lam * ‖h‖ := mul_pos hlam (norm_pos_iff.2 hh0)
    obtain ⟨Ψ, hΨ_def⟩ : ∃ Ψ : Euclid (m + 1) → ℝ,
        Ψ = fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : Euclid (m + 1) → Euclid (m + 1),
        g = fun z => ((lam * ‖h‖)⁻¹ * Ψ z) • h := ⟨_, rfl⟩
    have hΨsm : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
      rw [hΨ_def]; exact contDiff_infty.2 fun k => hΨs h k ℝ ψ hψ hψc
    have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := by
      rw [hg_def]; exact (contDiff_const.mul hΨsm).smul contDiff_const
    -- `g` is supported in the compact set `spt ψ + [0, 1] h ⊆ Q`
    obtain ⟨K, hK_def⟩ : ∃ K : Set (Euclid (m + 1)),
        K = (fun p : Euclid (m + 1) × ℝ => p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0:ℝ) 1) :=
      ⟨_, rfl⟩
    have hKc : IsCompact K := by
      rw [hK_def]
      exact (hψc.isCompact.prod isCompact_Icc).image
        (continuous_fst.add (continuous_snd.smul continuous_const))
    have hKQ : K ⊆ Q := by
      rw [hK_def]
      rintro _ ⟨⟨x, τ⟩, ⟨hx, hτ⟩, rfl⟩
      exact hseg x (hψS hx) τ hτ
    have hgK : ∀ z ∉ K, g z = 0 := by
      intro z hz
      have : Ψ z = 0 := by
        rw [hΨ_def]
        refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
        by_contra hne
        refine hz (hK_def ▸ ⟨⟨z - τ • h, τ⟩, ⟨subset_tsupport _ hne, Ioc_subset_Icc_self hτ⟩, ?_⟩)
        exact sub_add_cancel z (τ • h)
      rw [hg_def]; simp only [this, mul_zero, zero_smul]
    have hgc : HasCompactSupport g := HasCompactSupport.intro hKc hgK
    have hgQ : tsupport g ⊆ Q := (closure_minimal (fun z hz => by
      by_contra hzK; exact hz (hgK z hzK)) hKc.isClosed).trans hKQ
    -- `|Ψ| ≤ lam`, hence `‖g‖ ≤ 1`
    have hΨb : ∀ z, |Ψ z| ≤ lam := by
      intro z
      have hmeas : MeasurableSet {τ : ℝ | z - τ • h ∈ S} :=
        (hSo.preimage (continuous_const.sub (continuous_id.smul continuous_const))).measurableSet
      rw [hΨ_def]
      calc |∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)| = ‖∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)‖ := rfl
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, ‖ψ (z - τ • h)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _)
            ((integrable_indicator_iff hmeas).2 (integrable_const (1:ℝ)).integrableOn) ?_
          refine Filter.Eventually.of_forall fun τ => ?_
          show ‖ψ (z - τ • h)‖ ≤ {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ
          by_cases hτ : z - τ • h ∈ S
          · rw [indicator_of_mem (show τ ∈ {τ : ℝ | z - τ • h ∈ S} from hτ), Pi.one_apply]
            exact hψ1 (z - τ • h)
          · rw [indicator_of_notMem (show τ ∉ {τ : ℝ | z - τ • h ∈ S} from hτ),
              image_eq_zero_of_notMem_tsupport (fun h' => hτ (hψS h')), norm_zero]
        _ = (volume.restrict (Ioc (0:ℝ) 1)).real {τ : ℝ | z - τ • h ∈ S} :=
          integral_indicator_one hmeas
        _ ≤ lam := by
          rw [Measure.real, Measure.restrict_apply hmeas]
          exact ENNReal.toReal_le_of_le_ofReal hlam.le (hmult z)
    have hgb : ∀ z, ‖g z‖ ≤ 1 := by
      intro z
      rw [hg_def, norm_smul, norm_mul, norm_inv, Real.norm_of_nonneg hA.le, Real.norm_eq_abs]
      calc (lam * ‖h‖)⁻¹ * |Ψ z| * ‖h‖ ≤ (lam * ‖h‖)⁻¹ * lam * ‖h‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΨb z) (inv_nonneg.2 hA.le))
              (norm_nonneg h)
        _ = 1 := by rw [mul_assoc, inv_mul_cancel₀ hA.ne']
    -- `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`
    have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z) =
        (lam * ‖h‖)⁻¹ * (ψ z - ψ (z - h)) := by
      intro z
      have hd : HasFDerivAt g (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
          fderiv ℝ ψ (z - τ • h)).smulRight h) z := by
        rw [hg_def, hΨ_def]
        exact ((hΨd h ℝ ψ hψ hψc z).const_mul (lam * ‖h‖)⁻¹).smul_const h
      rw [hd.fderiv]
      refine (LinearMap.trace_smulRight (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
        fderiv ℝ ψ (z - τ • h) : Euclid (m + 1) →L[ℝ] ℝ) : Euclid (m + 1) →ₗ[ℝ] ℝ) h).trans ?_
      rw [ContinuousLinearMap.coe_coe, smul_apply, hΨh h ψ hψ z, smul_eq_mul]
    -- the hypothesis applied to `g`
    have hψb : ∀ x, ‖ψ x‖ ≤ 1 := hψ1
    have hint1 : Integrable fun x => ub x * ψ x :=
      hub_int.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hψb)
    have hint2 : Integrable fun x => ub x * ψ (x - h) :=
      hub_int.mul_bdd (hψ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => hψb _)
    have hint3 : Integrable fun x => ub (x + h) * ψ x :=
      (hub_int.comp_add_right h).mul_bdd hψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hψb)
    have key := hV g hgsm hgc hgQ hgb
    have e1 : ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) =
        (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
      calc ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)
          = ∫ y in Q, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) := by
            refine integral_congr_ae ?_
            filter_upwards [hub_ae] with y hy
            rw [htr y, hy]
        _ = ∫ y, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
              rw [hub_zero y hy, zero_mul]
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ y, ub y * ψ (y - h)) := by
            rw [← integral_sub hint1 hint2, ← integral_const_mul]
            congr 1; funext y; ring
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ x, ub (x + h) * ψ x) := by
            congr 2
            rw [← integral_add_right_eq_self (fun y => ub y * ψ (y - h)) h]
            simp only [add_sub_cancel_right]
        _ = (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
            rw [← integral_sub hint1 hint3, ← integral_neg]
            congr 2; funext x; ring
    rw [e1] at key
    have := mul_le_mul_of_nonneg_left key hA.le
    rwa [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
  /- Step 6: the `L¹` translation estimate `∫_S |ub (x + h) - ub x| ≤ 2 lam ‖h‖ V`. -/
  have hGEN : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∫ x in S, |ub (x + h) - ub x| ≤ 2 * (lam * ‖h‖ * V) := by
    intro S h lam hSo hseg hlam hmult
    by_cases hh : h = 0
    · subst hh; simp
    have hSQ : S ⊆ Q := fun x hx => by
      have := hseg x hx 0 ⟨le_rfl, zero_le_one⟩; rwa [zero_smul, add_zero] at this
    have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hSQ)
    refine hdual (fun x => ub (x + h) - ub x) S (lam * ‖h‖ * V)
      ((hub_int.comp_add_right h).sub hub_int)
      ((hub_meas.comp (measurable_add_const h)).sub hub_meas) hSo hSfin ?_
    intro ψ hψ hψc hψS hψ1
    have h1 := hweak S h lam hSo hseg hlam hh hmult ψ hψ hψc hψS hψ1
    have h2 := hweak S h lam hSo hseg hlam hh hmult (-ψ) hψ.neg hψc.neg
      (by rwa [tsupport_neg]) (fun x => by rw [Pi.neg_apply, abs_neg]; exact hψ1 x)
    have e2 : ∫ x, (ub (x + h) - ub x) * (-ψ) x = -∫ x, (ub (x + h) - ub x) * ψ x := by
      rw [← integral_neg]; congr 1; funext x; rw [Pi.neg_apply]; ring
    rw [e2] at h2
    rw [abs_le]; constructor <;> linarith only [h1, h2]
  clear hweak hdual hΨh hΨs hΨd
  /- Step 7: the Poincaré inequality.  Translating `y = x + h` and swapping the integrals,
  `∫_Q ∫_Q |ub y - ub x| ≤ ∫_{‖h‖ ≤ R} 2 ‖h‖ V dh`. -/
  have hnormle : ∀ v : Euclid (m + 1), (∀ i, |v i| ≤ 1) → ‖v‖ ≤ R := by
    intro v hv
    have h1 : ‖v‖ ^ 2 ≤ R := by
      rw [EuclideanSpace.norm_sq_eq, hR_def]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1:ℝ) := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]; exact (sq_le_one_iff_abs_le_one _).2 (hv i)
        _ = m + 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
              Nat.cast_add, Nat.cast_one]
    exact (sq_le_sq₀ (norm_nonneg v) hR.le).1 (h1.trans (le_self_pow₀ hR1 two_ne_zero))
  have hnorm : ∀ x h : Euclid (m + 1), x ∈ Q → x + h ∈ Q → ‖h‖ ≤ R := fun x h hx hxh =>
    hnormle h fun i => by
      have h1 := hx i; have h2 := hxh i
      rw [PiLp.add_apply] at h2
      rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hnormQ : ∀ y ∈ Q, ‖y‖ ≤ R := fun y hy =>
    hnormle y fun i => abs_le.2 ⟨by linarith only [(hy i).1], (hy i).2.le⟩
  have hsegA : ∀ h : Euclid (m + 1), ∀ x ∈ (fun x => x + h) ⁻¹' Q ∩ Q,
      ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q := by
    rintro h x ⟨hxh, hx⟩ τ ⟨hτ0, hτ1⟩ i
    have h1 := hx i; have h2 := hxh i
    rw [PiLp.add_apply] at h2
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases le_total 0 (h i) with hhi | hhi
    · have p1 := mul_nonneg hτ0 hhi
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) hhi
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
    · have p1 := mul_nonneg hτ0 (neg_nonneg.2 hhi)
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) (neg_nonneg.2 hhi)
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
  have hAo : ∀ h : Euclid (m + 1), IsOpen ((fun x => x + h) ⁻¹' Q ∩ Q) := fun h =>
    (hQo.preimage (continuous_id.add continuous_const)).inter hQo
  have hTR : ∀ h : Euclid (m + 1),
      ∫ x in (fun x => x + h) ⁻¹' Q ∩ Q, |ub (x + h) - ub x| ≤ 2 * (‖h‖ * V) := by
    intro h
    have := hGEN _ h 1 (hAo h) (hsegA h) one_pos (fun z => by
      rw [ENNReal.ofReal_one]
      exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_one]))
    rwa [one_mul] at this
  have hJ : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| ≤
      ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) := by
    have hΦ : (Function.uncurry fun x h : Euclid (m + 1) =>
          Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) =
        {p : Euclid (m + 1) × Euclid (m + 1) | p.2 + p.1 ∈ Q}.indicator
          (fun p => ENNReal.ofReal |ub (p.2 + p.1) - ub p.1|) := by
      funext ⟨x, h⟩
      simp only [Function.uncurry_apply_pair, Set.indicator_apply, mem_ofPred_eq]
    have hΦm : Measurable (Function.uncurry fun x h : Euclid (m + 1) =>
        Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) := by
      rw [hΦ]
      exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        ((hub_meas.comp (measurable_snd.add measurable_fst)).sub
          (hub_meas.comp measurable_fst)))).indicator
        (hQm.preimage (measurable_snd.add measurable_fst))
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x|
        = ∫⁻ x in Q, ∫⁻ h, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_indicator hQm, lintegral_add_right_eq_self]
      _ = ∫⁻ h, ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) :=
          lintegral_lintegral_swap hΦm.aemeasurable
      _ ≤ ∫⁻ h, (closedBall (0 : Euclid (m + 1)) R).indicator
            (fun _ => ENNReal.ofReal (2 * (R * V))) h := by
          refine lintegral_mono fun h => ?_
          have hAm := (hAo h).measurableSet
          have e1 : ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) =
              ∫⁻ x in (fun x => x + h) ⁻¹' Q ∩ Q, ENNReal.ofReal |ub (x + h) - ub x| := by
            rw [← Measure.restrict_restrict (hQm.preimage (measurable_add_const h)),
              ← lintegral_indicator (hQm.preimage (measurable_add_const h))]
            refine lintegral_congr fun x => ?_
            rw [add_comm h x]
            by_cases hx : x + h ∈ Q
            · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ (fun x => x + h) ⁻¹' Q from hx)]
            · rw [indicator_of_notMem hx,
                indicator_of_notMem (show x ∉ (fun x => x + h) ⁻¹' Q from hx)]
          have hint : IntegrableOn (fun x => |ub (x + h) - ub x|) ((fun x => x + h) ⁻¹' Q ∩ Q) :=
            ((hub_int.comp_add_right h).sub hub_int).abs.integrableOn
          rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => abs_nonneg _)]
          by_cases hh : h ∈ closedBall (0 : Euclid (m + 1)) R
          · rw [indicator_of_mem hh]
            refine ENNReal.ofReal_le_ofReal ((hTR h).trans ?_)
            have : ‖h‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hh
            have := mul_le_mul_of_nonneg_right this hV0
            linarith only [this]
          · rw [indicator_of_notMem hh]
            have hempty : (fun x => x + h) ⁻¹' Q ∩ Q = ∅ := by
              refine Set.eq_empty_of_forall_notMem fun x hx => hh ?_
              rw [mem_closedBall, dist_zero_right]; exact hnorm x h hx.2 hx.1
            rw [hempty, Measure.restrict_empty, integral_zero_measure, ENNReal.ofReal_zero]
      _ = ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) :=
          lintegral_indicator_const measurableSet_closedBall _
  clear hsegA hAo hnormle
  /- Step 8: the integer median `β`: the least integer with `|{ub ≤ β} ∩ Q| ≥ 1/2`. -/
  have hμprob : IsProbabilityMeasure (volume.restrict Q) :=
    isProbabilityMeasure_iff.2 (by rw [Measure.restrict_apply_univ, hQvol])
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = ∫ y in Q, |ub y| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM_def ▸ integral_nonneg fun y => abs_nonneg _
  have hmarkov : ∀ ε : ℝ, ε * (volume.restrict Q).real {y | ε ≤ |ub y|} ≤ M := fun ε =>
    hM_def ▸ mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
      hub_int.integrableOn.abs ε
  have hmeasle : ∀ c : ℝ, MeasurableSet {y | ub y ≤ c} := fun c =>
    measurableSet_le hub_meas measurable_const
  have hmeasge : ∀ c : ℝ, MeasurableSet {y | c ≤ ub y} := fun c =>
    measurableSet_le measurable_const hub_meas
  have hlow : ∀ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} → -(2 * M) ≤ k := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (volume.restrict Q).real {y | ub y ≤ k} ≤
        (volume.restrict Q).real {y | -(k:ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y (hy : ub y ≤ k) => by
        show -(k:ℝ) ≤ |ub y|; linarith only [hy, neg_abs_le (ub y)])
    have h3 := mul_le_mul_of_nonneg_left (hk.trans h1)
      (by linarith only [hlt, hM0] : (0:ℝ) ≤ -(k:ℝ))
    linarith only [hmarkov (-(k:ℝ)), h3, hlt]
  have hex : ∃ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} := by
    refine ⟨⌊2 * M⌋ + 1, ?_⟩
    have hk₀ : 2 * M < ((⌊2 * M⌋ + 1 : ℤ) : ℝ) := by
      rw [Int.cast_add, Int.cast_one]; exact Int.lt_floor_add_one _
    have h2 : (volume.restrict Q).real {y | ub y ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y hy => by
        rw [mem_compl_iff, mem_ofPred_eq, not_le] at hy
        exact hy.le.trans (le_abs_self _))
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    by_contra h4
    rw [not_le] at h4
    have h5 := mul_le_mul_of_nonneg_left (show 1/2 ≤ (volume.restrict Q).real
      {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} by linarith only [h2, h3, h4])
      (by linarith only [hk₀, hM0] : (0:ℝ) ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    linarith only [h5, hmarkov ((⌊2 * M⌋ + 1 : ℤ) : ℝ), hk₀]
  obtain ⟨β, hβP, hβmin⟩ := Int.exists_least_of_bdd ⟨⌊-(2 * M)⌋, fun k hk =>
    Int.cast_le.1 ((Int.floor_le _).trans (hlow k hk))⟩ hex
  have hβge : 1/2 ≤ (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
    have hβ1 : ¬ (1/2 ≤ (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}) := fun h => by
      have := hβmin (β - 1) h; omega
    rw [not_le] at hβ1
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((β - 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    have h4 : (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
      rw [measureReal_def, measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hub_ae] with y hy
      intro hy'
      obtain ⟨z, hz⟩ := hint y
      rw [mem_compl_iff, mem_ofPred_eq, not_le, hy, hz] at hy'
      show (β:ℝ) ≤ ub y
      rw [hy, hz]
      have : β - 1 < z := by exact_mod_cast hy'
      exact_mod_cast (show β ≤ z by omega)
    linarith only [h3, h4, hβ1]
  have hβabs : |(β:ℝ)| ≤ 2 * M := by
    rcases le_or_gt 0 (β:ℝ) with h0 | h0
    · rw [abs_of_nonneg h0]
      have h2 : (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} ≤
          (volume.restrict Q).real {y | (β:ℝ) ≤ |ub y|} :=
        measureReal_mono fun y (hy : (β:ℝ) ≤ ub y) => hy.trans (le_abs_self _)
      linarith only [mul_le_mul_of_nonneg_left (hβge.trans h2) h0, hmarkov β]
    · rw [abs_of_neg h0]; linarith only [hlow β hβP]
  have hhalf : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → 1/2 ≤ (volume.restrict Q).real s →
      (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) := by
    intro s hs h
    rw [← Measure.restrict_apply hs, ← ofReal_measureReal (measure_ne_top _ _)]
    calc (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hhalf1 := hhalf _ (hmeasle β) hβP
  have hhalf2 := hhalf _ (hmeasge β) hβge
  -- `|ub x - β| ≤ 2 ∫_Q |ub y - ub x| dy`, since `β` is a median
  have hpt : ∀ x, ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
    intro x
    have hhalf' : ∀ a : ℝ≥0∞, a = 2 * (a * (1/2)) := fun a => by
      rw [one_div, mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
        mul_one]
    have hgm : Measurable fun y => ENNReal.ofReal |ub y - ub x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hub_meas.sub measurable_const))
    have key : ∀ s : Set (Euclid (m + 1)), (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) →
        (∀ y ∈ s, |ub x - β| ≤ |ub y - ub x|) →
        ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
      intro s hs hle
      rw [hhalf' (ENNReal.ofReal |ub x - β|)]
      refine mul_le_mul_right ?_ 2
      calc ENNReal.ofReal |ub x - β| * (1/2) ≤ ENNReal.ofReal |ub x - β| * volume (s ∩ Q) :=
            mul_le_mul_right hs _
        _ = ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub x - β| := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub y - ub x| :=
            setLIntegral_mono hgm fun y hy => ENNReal.ofReal_le_ofReal (hle y hy.1)
        _ ≤ ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono_set inter_subset_right
    rcases le_total (β:ℝ) (ub x) with hx | hx
    · refine key _ hhalf1 fun y (hy : ub y ≤ β) => ?_
      rw [abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm]
      exact (by linarith only [hy] : ub x - β ≤ ub x - ub y).trans (le_abs_self _)
    · refine key _ hhalf2 fun y (hy : (β:ℝ) ≤ ub y) => ?_
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx)]
      exact (by linarith only [hy] : β - ub x ≤ ub y - ub x).trans (le_abs_self _)
  have hP1 : ∫ y in Q, |ub y - β| ≤ CP * V := by
    have hlin : ∫⁻ x in Q, ENNReal.ofReal |ub x - β| ≤
        2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R)) := by
      calc ∫⁻ x in Q, ENNReal.ofReal |ub x - β|
          ≤ ∫⁻ x in Q, 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono hpt
        _ = 2 * ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| :=
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
        _ ≤ _ := mul_le_mul_right hJ 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => |ub y - (β:ℝ)|)
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (continuous_abs.measurable.comp (hub_meas.sub measurable_const)).aestronglyMeasurable]
    calc (∫⁻ x in Q, ENNReal.ofReal |ub x - β|).toReal
        ≤ (2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne)) hlin
      _ = CP * V := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofNat, hCP_def]; ring
  have hβM : |(β:ℝ)| ≤ 2 * ∫ y in Q, |u y| := by
    have : ∫ y in Q, |u y| = M := by
      rw [hM_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hβabs
  clear hpt hhalf hhalf1 hhalf2 hlow hex hβmin hβge hβP hβabs hmarkov hJ hmeasle hmeasge hμprob
    hM0 hM_def hint
  /- Step 9: slabs `{y ∈ Q | a < y i < a + s}`.  Translating along `e i` compares the integrals
  of `|ub - β|` over two slabs of width `s` up to `2 s V`; averaging over the `N` slabs of width
  `1/N` bounds a boundary slab by `(∫_Q |ub - β| + 2 V) / N`. -/
  have hcoord : ∀ (i j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
      (x + t • EuclideanSpace.single i (1:ℝ)) j = if j = i then x j + t else x j := by
    intro i j x t
    by_cases hj : j = i <;> simp [hj]
  have hslabo : ∀ (i : Fin (m + 1)) (a s : ℝ),
      IsOpen {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := by
    intro i a s
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact hQo.inter ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
  have hslab : ∀ (i : Fin (m + 1)) (s a a' : ℝ), 0 < s → 0 ≤ a → a + s ≤ 1 → 0 ≤ a' →
      a' + s ≤ 1 →
      ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s}, |ub y - β| ≤
        (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s}, |ub y - β|) +
          2 * (s * V) := by
    intro i s a a' hs ha has ha' has'
    rcases eq_or_ne a a' with haa | haa
    · subst haa; linarith only [mul_nonneg hs.le hV0]
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = a' - a := ⟨_, rfl⟩
    have ht : t ≠ 0 := by rw [ht_def]; exact sub_ne_zero.2 (Ne.symm haa)
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (r : ℝ),
        (x + r • e) j = if j = i then x j + r else x j := by
      subst he_def; exact fun j x r => hcoord i j x r
    obtain ⟨S, hS_def⟩ : ∃ S : Set (Euclid (m + 1)),
        S = {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := ⟨_, rfl⟩
    obtain ⟨S', hS'_def⟩ : ∃ S' : Set (Euclid (m + 1)),
        S' = {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s} := ⟨_, rfl⟩
    rw [← hS_def, ← hS'_def]
    have hSo : IsOpen S := hS_def ▸ hslabo i a s
    have hSm : MeasurableSet S := hSo.measurableSet
    have hS'm : MeasurableSet S' := (hS'_def ▸ hslabo i a' s).measurableSet
    have hSfin : volume S ≠ ⊤ := by
      refine ne_top_of_le_ne_top hQfin (measure_mono fun y hy => ?_)
      rw [hS_def] at hy; exact hy.1
    have hnh : ‖t • e‖ = |t| := by
      rw [he_def, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hmem : ∀ x, x ∈ S ↔ x + t • e ∈ S' := by
      intro x
      rw [hS_def, hS'_def]
      show (x ∈ Q ∧ a < x i ∧ x i < a + s) ↔
        (x + t • e ∈ Q ∧ a' < (x + t • e) i ∧ (x + t • e) i < a' + s)
      rw [hce, ite_eq_left rfl]
      constructor
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        rw [hce]; split_ifs with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha', has']
        · exact hxQ j
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        have := hxQ j
        rw [hce] at this
        split_ifs at this with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha, has]
        · exact this
    have hgen := hGEN S (t • e) (s / |t|) hSo (by
        rintro x hx τ ⟨hτ0, hτ1⟩ j
        rw [hS_def] at hx
        obtain ⟨hxQ, h1, h2⟩ := hx
        rw [smul_smul, hce]
        split_ifs with hj
        · subst hj
          have e1 : τ * t = τ * a' - τ * a := by rw [ht_def]; ring
          have p1 := mul_nonneg (sub_nonneg.2 hτ1) ha
          have p2 := mul_nonneg hτ0 ha'
          have p3 := mul_nonneg (sub_nonneg.2 hτ1) (by linarith only [has] : (0:ℝ) ≤ 1 - a - s)
          have p4 := mul_nonneg hτ0 (by linarith only [has'] : (0:ℝ) ≤ 1 - a' - s)
          constructor <;> linarith only [h1, h2, e1, p1, p2, p3, p4]
        · exact hxQ j) (div_pos hs (abs_pos.2 ht)) (fun z => by
        have hsub : {τ : ℝ | z - τ • (t • e) ∈ S} ∩ Ioc (0:ℝ) 1 ⊆
            (fun τ => t * τ) ⁻¹' Ioo (z i - a - s) (z i - a) := by
          rintro τ ⟨hτ, -⟩
          rw [mem_ofPred_eq, hS_def] at hτ
          have h1 := hτ.2
          have hzi : (z - τ • (t • e)) i = z i - τ * t := by
            rw [smul_smul, sub_eq_add_neg, ← neg_smul, hce, ite_eq_left rfl, ← sub_eq_add_neg]
          rw [hzi] at h1
          rw [mem_preimage, mem_Ioo, mul_comm]
          exact ⟨by linarith only [h1.2], by linarith only [h1.1]⟩
        refine (measure_mono hsub).trans (le_of_eq ?_)
        rw [Real.volume_preimage_mul_left ht, Real.volume_Ioo, ← ENNReal.ofReal_mul (abs_nonneg _),
          abs_inv, show z i - a - (z i - a - s) = s by ring, div_eq_inv_mul])
    rw [hnh, div_mul_cancel₀ s (abs_ne_zero.2 ht)] at hgen
    have htrans : ∫ x in S, |ub (x + t • e) - β| = ∫ y in S', |ub y - β| := by
      rw [← integral_indicator hSm, ← integral_indicator hS'm,
        ← integral_add_right_eq_self (fun y => S'.indicator (fun y => |ub y - β|) y) (t • e)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hi1 : IntegrableOn (fun x => |ub (x + t • e) - β|) S :=
      ((hub_int.comp_add_right (t • e)).integrableOn.sub (integrableOn_const hSfin)).abs
    have hi2 : IntegrableOn (fun x => |ub (x + t • e) - ub x|) S :=
      ((hub_int.comp_add_right (t • e)).sub hub_int).abs.integrableOn
    calc ∫ y in S, |ub y - β|
        ≤ ∫ x in S, (|ub (x + t • e) - ub x| + |ub (x + t • e) - β|) := by
          refine setIntegral_mono_on ((hub_int.integrableOn.sub (integrableOn_const hSfin)).abs)
            (hi2.add hi1) hSm fun x _ => ?_
          have := abs_sub_le (ub x) (ub (x + t • e)) β
          rwa [abs_sub_comm (ub x) (ub (x + t • e))] at this
      _ = (∫ x in S, |ub (x + t • e) - ub x|) + ∫ x in S, |ub (x + t • e) - β| :=
          integral_add hi2 hi1
      _ ≤ (∫ y in S', |ub y - β|) + 2 * (s * V) := by rw [htrans]; linarith only [hgen]
  have hstrip : ∀ (i : Fin (m + 1)) (N : ℕ), 1 ≤ N → ∀ a : ℝ, 0 ≤ a → a + 1 / N ≤ 1 →
      (N:ℝ) * ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
        (∫ y in Q, |ub y - β|) + 2 * V := by
    intro i N hN a ha haN
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    have hk : ∀ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
          (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N},
            |ub y - β|) + 2 * (1 / N * V) := fun k hk =>
      hslab i (1 / N) a (k / N) (one_div_pos.2 hNpos) ha haN
        (div_nonneg (Nat.cast_nonneg k) hNpos.le)
        (by rw [← add_div, div_le_one hNpos]
            exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hk))
    have hsum := Finset.sum_le_sum hk
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hsum
    have hdisj : (↑(Finset.range N) : Set ℕ).Pairwise (Disjoint on fun k : ℕ =>
        {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}) := by
      intro k _ k' _ hkk'
      rw [Function.onFun, Set.disjoint_left]
      rintro y ⟨_, h1, h2⟩ ⟨_, h1', h2'⟩
      rcases lt_or_gt_of_ne hkk' with hlt | hlt
      · have : (k:ℝ) / N + 1 / N ≤ k' / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2, h1']
      · have : (k':ℝ) / N + 1 / N ≤ k / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2', h1]
    have hint : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hunion : ∑ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}, |ub y - β|
          ≤ ∫ y in Q, |ub y - β| := by
      rw [← integral_biUnion_finset (Finset.range N) (fun k _ => (hslabo i _ _).measurableSet)
        hdisj (fun k _ => hint.mono_set (fun y hy => hy.1))]
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_
      refine LE.le.eventuallySubset ?_
      intro y hy
      rw [mem_iUnion₂] at hy
      obtain ⟨k, _, hy⟩ := hy
      exact hy.1
    have : (N:ℝ) * (2 * (1 / N * V)) = 2 * V := by
      rw [mul_left_comm, ← mul_assoc (N:ℝ), mul_one_div_cancel hNpos.ne', one_mul]
    linarith only [hsum, hunion, this]
  clear hslab hGEN
  /- Step 10: difference quotients.  For `F` continuous with `|F| ≤ 1` and `s = 1/(2N)`,
  `∫_Q (ub - β) (F (· + s e) - F) / s` is the integral of `F` against the difference
  `w (· - s e) - w` of `w = (ub - β) 1_Q`, which is controlled by a translation estimate and the
  two boundary slabs. -/
  have hDQ : ∀ (i : Fin (m + 1)) (F : Euclid (m + 1) → ℝ), Continuous F → (∀ y, |F y| ≤ 1) →
      ∀ N : ℕ, 1 ≤ N →
      |∫ y in Q, (ub y - β) * ((2 * N : ℝ) *
        (F (y + (2 * N : ℝ)⁻¹ • EuclideanSpace.single i (1:ℝ)) - F y))|
        ≤ 10 * V + 4 * ∫ y in Q, |ub y - β| := by
    intro i F hFc hF1 N hN
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
        (x + t • e) j = if j = i then x j + t else x j := by
      subst he_def; exact fun j x t => hcoord i j x t
    have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 * N := ⟨_, rfl⟩
    rw [← he_def, ← hc_def]
    have hc : 0 < c := hc_def ▸ mul_pos two_pos hNpos
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = c⁻¹ := ⟨_, rfl⟩
    rw [← hs_def]
    have hs : 0 < s := hs_def ▸ inv_pos.2 hc
    have hcs : c * s = 1 := hs_def ▸ mul_inv_cancel₀ hc.ne'
    have hsN : s < 1 / N := by
      rw [hs_def, hc_def, one_div]
      exact inv_strictAnti₀ hNpos (by linarith only [hNpos])
    have hcm : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)),
        (x - s • e) j = if j = i then x j - s else x j := by
      intro j x
      rw [sub_eq_add_neg, ← neg_smul, hce, ← sub_eq_add_neg]
    obtain ⟨wb, hwb_def⟩ : ∃ wb : Euclid (m + 1) → ℝ, wb = Q.indicator fun y => ub y - β :=
      ⟨_, rfl⟩
    have hwb_int : Integrable wb := hwb_def ▸
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).integrable_indicator hQm
    have hFb : ∀ y, ‖F y‖ ≤ 1 := hF1
    have hi1 : Integrable fun y => wb y * F (y + s • e) :=
      hwb_int.mul_bdd (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => hFb _)
    have hi2 : Integrable fun y => wb y * F y :=
      hwb_int.mul_bdd hFc.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
    have hi3 : Integrable fun x => wb (x - s • e) * F x :=
      (hwb_int.comp_sub_right (s • e)).mul_bdd hFc.aestronglyMeasurable
        (Filter.Eventually.of_forall hFb)
    have e1 : ∫ y in Q, (ub y - β) * (c * (F (y + s • e) - F y)) =
        c * ∫ x, (wb (x - s • e) - wb x) * F x := by
      rw [← integral_indicator hQm]
      have : ∀ y, Q.indicator (fun y => (ub y - β) * (c * (F (y + s • e) - F y))) y =
          c * (wb y * F (y + s • e) - wb y * F y) := fun y => by
        rw [indicator_mul_left, ← hwb_def]; ring
      simp only [this]
      rw [integral_const_mul, integral_sub hi1 hi2,
        ← integral_sub_right_eq_self (fun y => wb y * F (y + s • e)) (s • e)]
      simp only [sub_add_cancel]
      rw [← integral_sub hi3 hi2]
      simp only [sub_mul]
    -- the pointwise bound: interior differences and the two boundary slabs
    obtain ⟨A, hA_def⟩ : ∃ A : Set (Euclid (m + 1)), A = (fun x => x + s • e) ⁻¹' Q ∩ Q :=
      ⟨_, rfl⟩
    obtain ⟨S0, hS0_def⟩ : ∃ S0 : Set (Euclid (m + 1)),
        S0 = {y : Euclid (m + 1) | y ∈ Q ∧ (0:ℝ) < y i ∧ y i < 0 + 1 / N} := ⟨_, rfl⟩
    obtain ⟨S1, hS1_def⟩ : ∃ S1 : Set (Euclid (m + 1)),
        S1 = {y : Euclid (m + 1) | y ∈ Q ∧ (1 - 1 / N : ℝ) < y i ∧ y i < (1 - 1 / N) + 1 / N} :=
      ⟨_, rfl⟩
    have hAm : MeasurableSet A := hA_def ▸ (hQm.preimage (measurable_add_const _)).inter hQm
    have hS0m : MeasurableSet S0 := hS0_def ▸ (hslabo i _ _).measurableSet
    have hS1m : MeasurableSet S1 := hS1_def ▸ (hslabo i _ _).measurableSet
    have hpt : ∀ x, |wb (x - s • e) - wb x| ≤
        A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) +
          S0.indicator (fun y => |ub y - β|) x +
          S1.indicator (fun y => |ub y - β|) (x - s • e) := by
      intro x
      have n1 := indicator_nonneg (fun z _ => abs_nonneg (ub (z + s • e) - ub z)) (x - s • e)
        (s := A)
      have n2 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) x (s := S0)
      have n3 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) (x - s • e) (s := S1)
      rw [hwb_def]
      by_cases hx : x ∈ Q <;> by_cases hxs : x - s • e ∈ Q
      · have hA : x - s • e ∈ A := by rw [hA_def]; exact ⟨by rwa [mem_preimage, sub_add_cancel], hxs⟩
        rw [indicator_of_mem hx, indicator_of_mem hxs, indicator_of_mem hA, sub_add_cancel,
          show ub (x - s • e) - (β:ℝ) - (ub x - β) = -(ub x - ub (x - s • e)) by ring, abs_neg]
        linarith only [n2, n3]
      · have hS0 : x ∈ S0 := by
          rw [hS0_def]
          refine ⟨hx, (hx i).1, ?_⟩
          by_contra hge
          rw [not_lt] at hge
          apply hxs
          intro j
          rw [hcm]
          split_ifs with hj
          · subst hj; constructor <;> linarith only [(hx j).2, hge, hsN, hs]
          · exact hx j
        rw [indicator_of_mem hx, indicator_of_notMem hxs, indicator_of_mem hS0, zero_sub, abs_neg]
        linarith only [n1, n3]
      · have hS1 : x - s • e ∈ S1 := by
          rw [hS1_def]
          refine ⟨hxs, ?_, ?_⟩
          · by_contra hle
            rw [not_lt, hcm, ite_eq_left rfl] at hle
            apply hx
            intro j
            have := hxs j
            rw [hcm] at this
            split_ifs at this with hj
            · subst hj; constructor <;> linarith only [this.1, hle, hsN, hs]
            · exact this
          · have := (hxs i).2; linarith only [this]
        rw [indicator_of_notMem hx, indicator_of_mem hxs, indicator_of_mem hS1, sub_zero]
        linarith only [n1, n2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hxs, sub_zero, abs_zero]
        linarith only [n1, n2, n3]
    -- integrate the three terms
    have hg1 : Integrable fun z => |ub (z + s • e) - ub z| :=
      ((hub_int.comp_add_right _).sub hub_int).abs
    have hg2 : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hT1i : Integrable fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) :=
      (hg1.indicator hAm).comp_sub_right (s • e)
    have hT2i : Integrable (S0.indicator fun y => |ub y - β|) :=
      (hg2.mono_set (fun y hy => by rw [hS0_def] at hy; exact hy.1)).integrable_indicator hS0m
    have hT3i : Integrable fun x => S1.indicator (fun y => |ub y - β|) (x - s • e) :=
      ((hg2.mono_set (fun y hy => by rw [hS1_def] at hy; exact hy.1)).integrable_indicator
        hS1m).comp_sub_right (s • e)
    have hI1 : ∫ x, A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) ≤ 2 * (s * V) := by
      rw [integral_sub_right_eq_self (fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) x)
        (s • e), integral_indicator hAm, hA_def]
      have := hTR (s • e)
      rwa [norm_smul, hne, mul_one, Real.norm_of_nonneg hs.le] at this
    have hI3 : ∫ x, S1.indicator (fun y => |ub y - β|) (x - s • e) = ∫ y in S1, |ub y - β| := by
      rw [integral_sub_right_eq_self (fun x => S1.indicator (fun y => |ub y - β|) x) (s • e),
        integral_indicator hS1m]
    have hb2 : (N:ℝ) * ∫ y in S0, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS0_def ▸
      hstrip i N hN 0 le_rfl (by rw [zero_add, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
    have hb3 : (N:ℝ) * ∫ y in S1, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS1_def ▸
      hstrip i N hN (1 - 1 / N) (by rw [sub_nonneg, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
        (by rw [sub_add_cancel])
    have hmain : ∫ x, |wb (x - s • e) - wb x| ≤
        2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β| := by
      refine (integral_mono ((hwb_int.comp_sub_right _).sub hwb_int).abs
        ((hT1i.add hT2i).add hT3i) hpt).trans ?_
      rw [integral_add' (hT1i.add hT2i) hT3i, integral_add' hT1i hT2i, integral_indicator hS0m, hI3]
      linarith only [hI1]
    have hbound : |∫ x, (wb (x - s • e) - wb x) * F x| ≤ ∫ x, |wb (x - s • e) - wb x| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hwb_int.comp_sub_right _).sub hwb_int).abs
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF1 x)
    rw [e1, abs_mul, abs_of_pos hc]
    have h5 := mul_le_mul_of_nonneg_left (hbound.trans hmain) hc.le
    have h6 : c * (2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β|) =
        2 * (c * s) * V + 2 * ((N:ℝ) * ∫ y in S0, |ub y - β|) +
          2 * ((N:ℝ) * ∫ y in S1, |ub y - β|) := by
      rw [hc_def]; ring
    rw [h6, hcs] at h5
    linarith only [h5, hb2, hb3]
  clear hstrip hslabo hcoord hTR
  /- Step 11: the boundary estimate (3): write `div G = ∑ᵢ ∂ᵢ Gᵢ` and pass to the limit in the
  difference quotients by dominated convergence. -/
  obtain ⟨I, hI_def⟩ : ∃ I : ℝ, I = ∫ y in Q, |ub y - β| := ⟨_, rfl⟩
  rw [← hI_def] at hDQ hP1
  have hwi : IntegrableOn (fun y => ub y - β) Q :=
    hub_int.integrableOn.sub (integrableOn_const hQfin)
  have h3 : ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) →
      |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (m + 1) * (10 * V + 4 * I) := by
    intro G hG hG1
    have hG1' : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
    have hdG : Continuous (fderiv ℝ G) := hG1'.continuous_fderiv one_ne_zero
    have hGd : ∀ y, HasFDerivAt G (fderiv ℝ G y) y := fun y =>
      (hG1'.differentiable one_ne_zero y).hasFDerivAt
    have hterm : ∀ i : Fin (m + 1),
        |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| ≤
          10 * V + 4 * I := by
      intro i
      obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
      rw [← he_def]
      have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
      obtain ⟨Fi, hFi_def⟩ : ∃ Fi : Euclid (m + 1) → ℝ, Fi = fun y => G y i := ⟨_, rfl⟩
      have hFid : ∀ y, HasFDerivAt Fi ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y)) y :=
        fun y => by
          rw [hFi_def]; exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y (hGd y)
      have hFic : Continuous Fi := by
        rw [hFi_def]; exact (EuclideanSpace.proj i).continuous.comp hG.continuous
      have hFi1 : ∀ y, |Fi y| ≤ 1 := fun y => by
        rw [hFi_def, ← Real.norm_eq_abs]; exact (PiLp.norm_apply_le (G y) i).trans (hG1 y)
      have hdFc : Continuous fun y => (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y) :=
        continuous_const.clm_comp hdG
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) (R + 1)).exists_bound_of_continuousOn
        hdFc.continuousOn
      have hC' : ∀ y ∈ closedBall (0 : Euclid (m + 1)) (R + 1), ‖fderiv ℝ Fi y‖ ≤ C :=
        fun y hy => by rw [(hFid y).fderiv]; exact hC y hy
      have hmvt : ∀ y ∈ Q, ∀ t : ℝ, 0 < t → |Fi (y + t • e) - Fi y| ≤ C * t ∨ 1 < t := by
        intro y hy t ht0
        rcases le_or_gt t 1 with ht1 | ht1
        · left
          have hny := hnormQ y hy
          have hyK : y ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]; linarith only [hny]
          have hyK' : y + t • e ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le]
            linarith only [hny, ht1]
          have := (convex_closedBall (0 : Euclid (m + 1)) (R + 1)).norm_image_sub_le_of_norm_fderiv_le
            (fun z _ => (hFid z).differentiableAt) hC' hyK hyK'
          rwa [add_sub_cancel_left, norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le,
            Real.norm_eq_abs] at this
        · right; exact ht1
      obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun N => 2 * ((N + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
      have hcpos : ∀ N, 0 < c N := fun N => by
        rw [hc_def]; exact mul_pos two_pos (Nat.cast_pos.2 N.succ_pos)
      have hc1 : ∀ N, ¬ 1 < (c N)⁻¹ := fun N => by
        rw [not_lt, inv_le_one₀ (hcpos N), hc_def]
        have : (1:ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.one_le_cast.2 N.succ_pos
        linarith only [this]
      have hctend : Tendsto (fun N => ‖c N‖) atTop atTop := by
        have : (fun N => ‖c N‖) = fun N : ℕ => 2 * ((N + 1 : ℕ) : ℝ) := by
          funext N; rw [Real.norm_of_nonneg (hcpos N).le, hc_def]
        rw [this]
        exact Tendsto.const_mul_atTop two_pos
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have hlim : Tendsto
          (fun N => ∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y)))
          atTop (𝓝 (∫ y in Q, (ub y - β) * (fderiv ℝ G y e) i)) := by
        refine tendsto_integral_of_dominated_convergence (fun y => |ub y - β| * C) (fun N => ?_)
          (hwi.abs.mul_const C) (fun N => ?_) ?_
        · exact (hub_meas.sub measurable_const).aestronglyMeasurable.mul
            (continuous_const.mul ((hFic.comp (continuous_id.add continuous_const)).sub
              hFic)).aestronglyMeasurable
        · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun y hy => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hcpos N)]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := (hmvt y hy (c N)⁻¹ (inv_pos.2 (hcpos N))).resolve_right (hc1 N)
          calc c N * |Fi (y + (c N)⁻¹ • e) - Fi y| ≤ c N * (C * (c N)⁻¹) :=
                mul_le_mul_of_nonneg_left this (hcpos N).le
            _ = C := by rw [mul_comm C, ← mul_assoc, mul_inv_cancel₀ (hcpos N).ne', one_mul]
        · refine Filter.Eventually.of_forall fun y => ?_
          have := (hFid y).lim e hctend
          simp only [smul_eq_mul] at this
          exact this.const_mul _
      have hbd : ∀ N, |∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y))| ≤
          10 * V + 4 * I := fun N => by
        have := hDQ i Fi hFic hFi1 (N + 1) (by omega)
        rwa [← he_def, show (2 * ((N + 1 : ℕ) : ℝ)) = c N by rw [hc_def]] at this
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have htr : ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∑ i, (fderiv ℝ G y (EuclideanSpace.single i 1)) i := by
      intro y
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis]
      simp [Matrix.trace, LinearMap.toMatrix_apply]
    have hint_i : ∀ i : Fin (m + 1), Integrable
        (fun y => (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i) (volume.restrict Q) := by
      intro i
      have hcont : Continuous fun y => (fderiv ℝ G y (EuclideanSpace.single i 1)) i :=
        (EuclideanSpace.proj i).continuous.comp (hdG.clm_apply continuous_const)
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) R).exists_bound_of_continuousOn
        hcont.continuousOn
      refine hwi.mul_bdd hcont.aestronglyMeasurable ((ae_restrict_iff' hQm).2
        (Filter.Eventually.of_forall fun y hy => hC y ?_))
      rw [mem_closedBall, dist_zero_right]; exact hnormQ y hy
    calc |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)|
        = |∑ i, ∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| := by
          rw [← integral_finsetSum _ fun i _ => hint_i i]
          congr 2; funext y
          rw [htr y, Finset.mul_sum]
      _ ≤ ∑ i, |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), (10 * V + 4 * I) := Finset.sum_le_sum fun i _ => hterm i
      _ = (m + 1) * (10 * V + 4 * I) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
            Nat.cast_one]
  /- Conclusion. -/
  have hm0 : (0:ℝ) ≤ m + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
  have hcV : CP * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have := mul_nonneg hm0 (by linarith only [hCP] : (0:ℝ) ≤ 10 + 4 * CP)
    linarith only [this]
  refine ⟨β, ?_, hβM, ?_⟩
  · have : ∫ y in Q, |u y - β| = I := by
      rw [hI_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hP1.trans hcV
  · intro G hG hG1
    have : ∫ y in Q, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
      integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]
    refine (h3 G hG hG1).trans ?_
    have h1 : (m + 1) * (10 * V + 4 * I) ≤ (m + 1) * (10 * V + 4 * (CP * V)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP1]) hm0
    have h2 : (m + 1) * (10 * V + 4 * (CP * V)) = (m + 1) * (10 + 4 * CP) * V := by ring
    have h4 : (m + 1) * (10 + 4 * CP) * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V :=
      mul_le_mul_of_nonneg_right (by linarith only [hCP]) hV0
    linarith only [h1, h2, h4]
/-- **Dilation pull-back of a test form** (Simon 6.2.23 for `f = δ_λ`, `δ_λ(x) = λx`, `λ ≠ 0`):
`δ_λ^#ω = affinePullbackForm (λ·id) 0 ω` is again a test form on `ℝᴾ`, and
`(δ_λ^#ω)(x) = λᵏ ω(λx)` as `k`-covectors.  `x ↦ λx` is a homeomorphism, hence proper, so the
pull-back preserves compactly supported smooth forms; multilinearity of the covector `ω(λx)`
pulls `λ` out of each of its `k` slots. -/
theorem Submission.cmcdt_dil_pullback_testForm : ∀ (P k : ℕ) (lam : ℝ), lam ≠ 0 → ∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) ∧ ∀ x : Euclid P, (η : DifferentialForm (Euclid P) k) x = lam ^ k • (ω : DifferentialForm (Euclid P) k) (lam • x) := by
  intro P k lam hlam ω
  -- Step 1: `x ↦ 0 + (λ·id)x = λx` is a homeomorphism, hence a proper map.
  have hproper : IsProperMap
      (fun x : Euclid P => (0 : Euclid P) + (lam • ContinuousLinearMap.id ℝ (Euclid P)) x) := by
    convert (Homeomorph.smulOfNeZero (α := Euclid P) lam hlam).isProperMap using 1
    funext x
    simp
  -- Step 2: the pull-back along the proper map is a test form, trivially supported in `univ`.
  refine ⟨⟨affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0
      (ω : DifferentialForm (Euclid P) k),
    affinePullbackForm_isTestForm _ _ hproper ω.property.1, subset_univ _⟩, rfl, fun x => ?_⟩
  -- Steps 3–4: `η(x)(v) = ω(λx)(λv₁, …, λvₖ) = (∏ᵢ λ) ω(λx)(v) = λᵏ ω(λx)(v)` for every `v`.
  have hx : (0 : Euclid P) + (lam • ContinuousLinearMap.id ℝ (Euclid P)) x = lam • x := by
    simp
  ext v
  have hv : (lam • ContinuousLinearMap.id ℝ (Euclid P)) ∘ v = fun i => lam • v i := by
    funext i
    simp
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hx, hv,
    ContinuousAlternatingMap.map_smul_univ, Fin.prod_const, ContinuousAlternatingMap.smul_apply]

/-- **Mass under the dilation push-forward** (step 5 of the proof of
`Submission.cmcdt_dilation_pushforward`; Simon 6.5.3, chapter-06.txt lines 1458–1460: the changes
of scale `x ↦ λ⁻¹x` and `x ↦ λx` scale the masses of `k`-currents by `λ^{∓k}`).  Let `λ > 0` and
`X, Y ∈ 𝒟_k(ℝᴾ)` with `Y(ω) = X(η)` whenever `η = δ_λ^#ω`, i.e. `Y = δ_{λ#}X` for `δ_λ(x) = λx`
(6.2.23).  Then `M(Y) = λᵏ M(X)` in `[0, ∞]`, with no finiteness assumption.  By
`Submission.cmcdt_dil_pullback_testForm`, `δ_μ^#ω` is a test form with `(δ_μ^#ω)(x) = μᵏ ω(μx)`
for `μ ≠ 0`.  (1) For admissible `ω`, `η' = λ⁻ᵏ δ_λ^#ω` has `η'(x) = ω(λx)`, so it is admissible
and `Y(ω) = X(δ_λ^#ω) = λᵏ X(η') ≤ λᵏ M(X)`.  (2) For admissible `η`, `ω = λᵏ δ_{λ⁻¹}^#η` has
`ω(y) = η(λ⁻¹y)`, so it is admissible, and `δ_λ^#ω = λᵏ η`; thus `λᵏ X(η) = Y(ω) ≤ M(Y)`, and
`λᵏ M(X) ≤ M(Y)` because multiplication by `λᵏ` commutes with suprema in `[0, ∞]`. -/
theorem Submission.cmcdt_dil_mass_eq : ∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → Y.mass = ENNReal.ofReal (lam ^ k) * X.mass := by
  intro P k lam hlam X Y hXY
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hpow : 0 < lam ^ k := pow_pos hlam k
  apply le_antisymm
  -- Step 1: `M(Y) ≤ λᵏ M(X)`.  Fix an admissible `ω`.
  · refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (Y ω) ≤ ENNReal.ofReal (lam ^ k) * X.mass
    -- (a) `η = δ_λ^#ω` is a test form with `η(x) = λᵏ ω(λx)`, and `Y(ω) = X(η)`.
    obtain ⟨η, hηω, hη⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hlam0 ω
    -- (b) `η' = λ⁻ᵏ η` has `η'(x) = ω(λx)`, so it is admissible.
    have hη' : (lam ^ k)⁻¹ • η ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      change covectorEuclideanNorm ((lam ^ k)⁻¹ • (η : DifferentialForm (Euclid P) k) x) ≤ 1
      rw [hη x, smul_smul, inv_mul_cancel₀ hpow.ne', one_smul]
      exact hω.2 (lam • x)
    -- (c) `X(η) = λᵏ X(η')` by linearity.
    have hXη : X η = lam ^ k * X ((lam ^ k)⁻¹ • η) := by
      rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul]
    -- (d) `Y(ω) = λᵏ X(η') ≤ λᵏ M(X)`.
    rw [hXY ω η hηω, hXη, ENNReal.ofReal_mul hpow.le]
    exact mul_le_mul_right (X.le_massOn hη') _
  -- Step 2: `λᵏ M(X) ≤ M(Y)`, where `λᵏ M(X)` is the supremum of `λᵏ X(η)` over admissible `η`.
  · show ENNReal.ofReal (lam ^ k) * sSup ((fun ω => ENNReal.ofReal (X ω)) ''
      massAdmissibleOn (univ : Set (Euclid P)) k univ) ≤ Y.mass
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨η, hη, rfl⟩
    show ENNReal.ofReal (lam ^ k) * ENNReal.ofReal (X η) ≤ Y.mass
    -- (a) `ζ = δ_{λ⁻¹}^#η` and `ω = λᵏ ζ`, so `ω(y) = η(λ⁻¹y)`.
    obtain ⟨ζ, -, hζ⟩ := Submission.cmcdt_dil_pullback_testForm P k lam⁻¹ (inv_ne_zero hlam0) η
    have hω : ∀ y, ((lam ^ k • ζ : TestFormOn (univ : Set (Euclid P)) k) :
        DifferentialForm (Euclid P) k) y = (η : DifferentialForm (Euclid P) k) (lam⁻¹ • y) := by
      intro y
      change lam ^ k • (ζ : DifferentialForm (Euclid P) k) y = _
      rw [hζ y, smul_smul, ← mul_pow, mul_inv_cancel₀ hlam0, one_pow, one_smul]
    -- (b) `ω` is admissible.
    have hωadm : lam ^ k • ζ ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      refine ⟨subset_univ _, fun y => ?_⟩
      rw [hω y]
      exact hη.2 (lam⁻¹ • y)
    -- (c) `η₂ = δ_λ^#ω` satisfies `η₂(x) = λᵏ ω(λx) = λᵏ η(x)`, i.e. `η₂ = λᵏ η`.
    obtain ⟨η₂, hη₂ω, hη₂⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hlam0 (lam ^ k • ζ)
    have hη₂η : η₂ = lam ^ k • η := by
      refine Subtype.ext (funext fun x => ?_)
      change (η₂ : DifferentialForm (Euclid P) k) x = lam ^ k • (η : DifferentialForm (Euclid P) k) x
      rw [hη₂ x, hω, inv_smul_smul₀ hlam0]
    -- (d) `λᵏ X(η) = X(η₂) = Y(ω) ≤ M(Y)`.
    calc ENNReal.ofReal (lam ^ k) * ENNReal.ofReal (X η)
        = ENNReal.ofReal (Y (lam ^ k • ζ)) := by
          rw [hXY (lam ^ k • ζ) η₂ hη₂ω, hη₂η, map_smul, smul_eq_mul, ENNReal.ofReal_mul hpow.le]
      _ ≤ Y.mass := Y.le_massOn hωadm
/-- **Support of the dilation push-forward**: step 6 of the proof of `cmcdt_dilation_pushforward`
(`spt T` as in Simon 6.2.11, chapter-06.txt lines 296–302; change of scale as in 6.5.3, lines
1458–1460).  If `λ > 0` and `Y(ω) = X(δ_λ^#ω)` for all test forms `ω` (`Y = δ_{λ#}X`,
`δ_λ(x) = λx`), then `spt Y = λ spt X`.  As `δ_λ^#ω = λᵏ ω(λ·)`, `tsupport δ_λ^#ω ⊆
δ_λ⁻¹(tsupport ω)`, so `Y` vanishes on `λW` whenever `X` vanishes on `W`; as `δ_λ^#δ_{λ⁻¹}^#η = η`,
`X` vanishes on `λ⁻¹W` whenever `Y` vanishes on `W`.  Hence `Z_Y = λZ_X`, and `δ_λ` is a
bijection of `ℝᴾ`. -/
theorem Submission.cmcdt_dil_support_eq : ∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → Y.support = (fun x => lam • x) '' X.support := by
  intro P k lam hlam X Y hrel
  have hne : lam ≠ 0 := hlam.ne'
  have hne' : lam⁻¹ ≠ 0 := inv_ne_zero hne
  -- Step 0(b): if `η(x) = μᵏ ω(μx)` for all `x`, then `tsupport η ⊆ δ_μ⁻¹(tsupport ω)`.
  have htsupp : ∀ (μ : ℝ) (ω η : TestFormOn (univ : Set (Euclid P)) k),
      (∀ x, (η : DifferentialForm (Euclid P) k) x =
        μ ^ k • (ω : DifferentialForm (Euclid P) k) (μ • x)) →
      tsupport (η : DifferentialForm (Euclid P) k) ⊆
        (fun x => μ • x) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) k) := by
    intro μ ω η h
    refine closure_minimal (fun x hx => ?_)
      ((isClosed_tsupport _).preimage (continuous_const_smul μ))
    refine mem_preimage.2 (subset_tsupport _ fun h0 => hx ?_)
    rw [h x, h0, smul_zero]
  -- Step 0(c): each test form `η` has `ζ = δ_{λ⁻¹}^#η` with `X(η) = Y(ζ)`, since `δ_λ^#ζ = η`,
  -- and `tsupport ζ ⊆ δ_{λ⁻¹}⁻¹(tsupport η)` by Step 0(b).
  have hinv : ∀ η : TestFormOn (univ : Set (Euclid P)) k,
      ∃ ζ : TestFormOn (univ : Set (Euclid P)) k, X η = Y ζ ∧
        tsupport (ζ : DifferentialForm (Euclid P) k) ⊆
          (fun x => lam⁻¹ • x) ⁻¹' tsupport (η : DifferentialForm (Euclid P) k) := by
    intro η
    obtain ⟨ζ, -, hζ⟩ := Submission.cmcdt_dil_pullback_testForm P k lam⁻¹ hne' η
    obtain ⟨η₂, hη₂, hη₂ζ⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hne ζ
    have hη₂η : η₂ = η := by
      refine Subtype.ext (funext fun x => ?_)
      rw [hη₂ζ x, hζ, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul,
        inv_smul_smul₀ hne]
    exact ⟨ζ, by rw [hrel ζ η₂ hη₂, hη₂η], htsupp lam⁻¹ η ζ hζ⟩
  -- Steps 1 and 2 share one argument: if every `ω` has `η` with `A(ω) = B(η)` and
  -- `tsupport η ⊆ δ_μ⁻¹(tsupport ω)`, then `δ_μ(Z_B) ⊆ Z_A`.  For `x ∈ W` with `B` vanishing on
  -- `W`, `δ_μ(W)` is open with compact closure (Step 0(a)) and `A` vanishes on it, because
  -- `tsupport ω ⊆ δ_μ(W)` gives `tsupport η ⊆ δ_μ⁻¹(δ_μ(W)) = W`.
  have hzero : ∀ μ : ℝ, μ ≠ 0 → ∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) k,
      (∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ η : TestFormOn (univ : Set (Euclid P)) k,
        A ω = B η ∧ tsupport (η : DifferentialForm (Euclid P) k) ⊆
          (fun x => μ • x) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) k)) →
      (fun x => μ • x) '' B.zeroRegion ⊆ A.zeroRegion := by
    rintro μ hμ A B hAB _ ⟨x, ⟨W, ⟨hWo, hWc, -, hWv⟩, hxW⟩, rfl⟩
    have hK : IsCompact ((fun x => μ • x) '' closure W) := hWc.image (continuous_const_smul μ)
    refine ⟨(fun x => μ • x) '' W, ⟨isOpenMap_smul₀ hμ W hWo,
      hK.of_isClosed_subset isClosed_closure (closure_minimal (image_mono subset_closure)
        hK.isClosed), subset_univ _, fun ω hω => ?_⟩, mem_image_of_mem _ hxW⟩
    obtain ⟨η, hAB', hηω⟩ := hAB ω
    rw [hAB']
    exact hWv η (hηω.trans ((preimage_mono hω).trans
      ((smul_right_injective (Euclid P) hμ).preimage_image W).subset))
  -- Step 1: `δ_λ(Z_X) ⊆ Z_Y`, taking `η = δ_λ^#ω` from `cmcdt_dil_pullback_testForm`.
  have h1 : (fun x => lam • x) '' X.zeroRegion ⊆ Y.zeroRegion := by
    refine hzero lam hne Y X fun ω => ?_
    obtain ⟨η, hη, hηω⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hne ω
    exact ⟨η, hrel ω η hη, htsupp lam ω η hηω⟩
  -- Step 2: `δ_{λ⁻¹}(Z_Y) ⊆ Z_X` by Step 0(c), so `y = λ(λ⁻¹y) ∈ δ_λ(Z_X)` for `y ∈ Z_Y`.
  have h2 : (fun x => lam⁻¹ • x) '' Y.zeroRegion ⊆ X.zeroRegion := hzero lam⁻¹ hne' X Y hinv
  have hZ : Y.zeroRegion = (fun x => lam • x) '' X.zeroRegion :=
    Subset.antisymm
      (fun y hy => ⟨lam⁻¹ • y, h2 (mem_image_of_mem _ hy), smul_inv_smul₀ hne y⟩) h1
  -- Step 3: `δ_λ` is a bijection, so `spt Y = univ \ δ_λ(Z_X) = δ_λ(univ \ Z_X) = δ_λ(spt X)`.
  unfold GeometricCurrentOn.support
  rw [hZ, image_sdiff (smul_right_injective (Euclid P) hne),
    image_univ_of_surjective (f := fun x : Euclid P => lam • x)
      fun y => ⟨lam⁻¹ • y, smul_inv_smul₀ hne y⟩]
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
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

/-- **Integer multiplicity is preserved by the dilation push-forward** `δ_{λ#}`, `δ_λ(x) = λx`,
`λ > 0` (step 7 of the proof of `cmcdt_dilation_pushforward`; compare Simon 6.3.3).  If
`Y(ω) = X(δ_λ^#ω)` and `X = τ(M, θ, ξ)`, then `Y = τ(λM, θ(·/λ), ξ(·/λ))`, with
`λM = δ_{λ⁻¹}⁻¹(M)`.  The change of variables `(δ_λ)_#(Hᵏ⌞M) = λ⁻ᵏ Hᵏ⌞λM` transfers local
integrability, measurability and orientation (`T_{λx}(λM) = TₓM`), and `δ_λ^#ω(x) = λᵏω(λx)`
gives `Y(ω) = λᵏλ⁻ᵏ ∫_{λM} θ(·/λ) ⟨ω, ξ(·/λ)⟩ dHᵏ`.  This holds in every degree `k`. -/
theorem Submission.cmcdt_dil_isIntegerMultiplicity : ∀ (P k : ℕ) (lam : ℝ), 0 < lam → ∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, (∀ ω η : TestFormOn (univ : Set (Euclid P)) k, (η : DifferentialForm (Euclid P) k) = affinePullbackForm (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) → Y ω = X η) → IsIntegerMultiplicity X → IsIntegerMultiplicity Y := by
  intro P k lam hlam X Y hXY ⟨R, hR⟩
  have hlam0 : lam ≠ 0 := hlam.ne'
  -- `δ_λ` is a homeomorphism, hence a measurable embedding, and `δ_λ⁻¹(δ_{λ⁻¹}⁻¹(S)) = S`
  have hT : MeasurableEmbedding (fun x : Euclid P => lam • x) :=
    (Homeomorph.smulOfNeZero lam hlam0).measurableEmbedding
  have hpre : ∀ S : Set (Euclid P),
      (fun x : Euclid P => lam • x) ⁻¹' ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' S) = S := by
    intro S
    ext x
    simp only [mem_preimage, inv_smul_smul₀ hlam0]
  have hc0 : ENNReal.ofReal (lam⁻¹ ^ k) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 hlam) k)).ne'
  -- change of variables on `M' = δ_{λ⁻¹}⁻¹(M)`: `(δ_λ)_#(Hᵏ⌞M) = λ⁻ᵏ Hᵏ⌞M'` and
  -- `∫_M g(λz) dHᵏ(z) = λ⁻ᵏ ∫_{M'} g dHᵏ`
  obtain ⟨hcv1, -, hcv3⟩ := Submission.euclid_hausdorff_dilation_change_of_variables P k lam hlam
    ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier)
  rw [hpre] at hcv1 hcv3
  -- rectifiability: `M' ⊆ δ_{λ⁻¹}⁻¹(M₀) ∪ ⋃ⱼ range (λFⱼ)`, with `Hᵏ(δ_{λ⁻¹}⁻¹(M₀)) = λᵏHᵏ(M₀) = 0`
  have hrect : CountablyRectifiable k ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier) := by
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun y : Euclid P => lam⁻¹ • y) ⁻¹' M₀, ?_, fun j z => lam • F j z, fun j => ?_,
      fun y hy => ?_⟩
    · rw [preimage_smul₀ (inv_ne_zero hlam0),
        Measure.euclideanHausdorffMeasure_smul₀ k (inv_ne_zero (inv_ne_zero hlam0)), hM₀,
        smul_zero]
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨‖lam‖₊ * K, (lipschitzWith_smul lam).comp hK⟩
    · have hy' : lam⁻¹ • y ∈ R.carrier := hy
      rcases hcover hy' with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, z, hz⟩ := mem_iUnion.1 h1
        exact Or.inr (mem_iUnion.2 ⟨j, z, by simp only [hz, smul_inv_smul₀ hlam0]⟩)
  -- local integrability: `∫⁻_{M ∩ δ_λ⁻¹(K)} θ dHᵏ = λ⁻ᵏ ∫⁻_{M' ∩ K} θ(·/λ) dHᵏ`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier ∩ K,
        (R.mult (lam⁻¹ • x) : ℝ≥0∞) ∂μHE[k] ≠ ∞ := by
    intro K hK _ htop
    have hKc : IsCompact ((fun x : Euclid P => lam • x) ⁻¹' K) :=
      (Homeomorph.smulOfNeZero lam hlam0).isCompact_preimage.2 hK
    have h := (Submission.euclid_hausdorff_dilation_change_of_variables P k lam hlam
      ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier ∩ K)).2.1
      (fun y => (R.mult (lam⁻¹ • y) : ℝ≥0∞))
    rw [preimage_inter, hpre] at h
    simp only [inv_smul_smul₀ hlam0] at h
    rw [htop, ENNReal.mul_top hc0] at h
    exact R.locallyIntegrable_mult _ hKc (subset_univ _) h
  -- measurability: `ξ(·/λ) ∘ δ_λ = ξ`, and `Hᵏ⌞M' ≪ λ⁻ᵏ Hᵏ⌞M' = (δ_λ)_#(Hᵏ⌞M)`
  have hmeas : AEStronglyMeasurable (fun y : Euclid P => R.orient (lam⁻¹ • y))
      (μHE[k].restrict ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier)) := by
    have h : AEStronglyMeasurable (fun y : Euclid P => R.orient (lam⁻¹ • y))
        (Measure.map (fun x : Euclid P => lam • x) (μHE[k].restrict R.carrier)) := by
      rw [hT.aestronglyMeasurable_map_iff]
      have he : ((fun y : Euclid P => R.orient (lam⁻¹ • y)) ∘ fun x : Euclid P => lam • x) =
          R.orient := by
        funext x
        simp only [Function.comp_apply, inv_smul_smul₀ hlam0]
      rw [he]
      exact R.aestronglyMeasurable_orient
    rw [hcv1] at h
    exact h.mono_ac (Measure.absolutelyContinuous_smul hc0)
  -- orientation: `T_{λx}M' = TₓM` (dilation invariance, `dilation 0 λ⁻¹ = δ_λ`) and
  -- `ξ(λx/λ) = ξ(x)`, transferred from `Hᵏ⌞M`-a.e. `x` to `Hᵏ⌞M'`-a.e. `y = λx`
  have hdil : dilation (0 : Euclid P) lam⁻¹ = fun y => lam • y := by
    funext y
    simp [dilation, dilationCLM]
  have himg : (fun y : Euclid P => lam • y) '' R.carrier =
      (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_preimage, inv_smul_smul₀ hlam0] using hx
    · intro hy
      exact ⟨lam⁻¹ • y, hy, smul_inv_smul₀ hlam0 y⟩
  have hor : ∀ᵐ y ∂(μHE[k].restrict ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier)),
      ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt k ((fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier) y Q ∧
          IsUnitOrientationOf (R.orient (lam⁻¹ • y)) Q := by
    refine (Measure.ae_ennreal_smul_measure_iff hc0).1 ?_
    rw [← hcv1, hT.ae_map_iff]
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, hQ, hξ⟩ := hx
    refine ⟨Q, ?_, ?_⟩
    · have h := Submission.dtc_approxTangent_dilation P k R.carrier 0 x lam⁻¹ Q
        (inv_pos.2 hlam) hQ
      rwa [hdil, himg] at h
    · rwa [inv_smul_smul₀ hlam0]
  refine ⟨{ carrier := (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier
            mult := fun y => R.mult (lam⁻¹ • y)
            orient := fun y => R.orient (lam⁻¹ • y)
            measurableSet_carrier :=
              (continuous_const_smul lam⁻¹).measurable R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := hrect
            measurable_mult := R.measurable_mult.comp (continuous_const_smul lam⁻¹).measurable
            mult_pos := fun y hy => R.mult_pos _ hy
            locallyIntegrable_mult := hint
            aestronglyMeasurable_orient := hmeas
            orients := hor }, fun ω => ?_⟩
  -- representation: `Y(ω) = X(η)` with `η(x) = λᵏω(λx)` (pullback test form), then change of
  -- variables with `g(y) = θ(y/λ) ⟨ω(y), ξ(y/λ)⟩`
  obtain ⟨η, hη, hηx⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hlam0 ω
  rw [hXY ω η hη, hR η]
  show ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((η : DifferentialForm (Euclid P) k) x)
      ∂μHE[k] = ∫ y in (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier,
        (R.mult (lam⁻¹ • y) : ℝ) * R.orient (lam⁻¹ • y) ((ω : DifferentialForm (Euclid P) k) y)
          ∂μHE[k]
  have h3 := hcv3 fun y => (R.mult (lam⁻¹ • y) : ℝ) *
    R.orient (lam⁻¹ • y) ((ω : DifferentialForm (Euclid P) k) y)
  simp only [inv_smul_smul₀ hlam0] at h3
  calc ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((η : DifferentialForm (Euclid P) k) x)
        ∂μHE[k]
      = ∫ x in R.carrier, lam ^ k * ((R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) k) (lam • x))) ∂μHE[k] := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hηx x, map_smul, smul_eq_mul]
        ring
    _ = lam ^ k * ∫ x in R.carrier, (R.mult x : ℝ) *
          R.orient x ((ω : DifferentialForm (Euclid P) k) (lam • x)) ∂μHE[k] :=
        integral_const_mul _ _
    _ = lam ^ k * (lam⁻¹ ^ k * ∫ y in (fun y : Euclid P => lam⁻¹ • y) ⁻¹' R.carrier,
          (R.mult (lam⁻¹ • y) : ℝ) *
            R.orient (lam⁻¹ • y) ((ω : DifferentialForm (Euclid P) k) y) ∂μHE[k]) := by
        rw [h3]
    _ = _ := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlam0, one_pow, one_mul]

/-- **Push-forward by the dilations `δ_λ(x) = λx` of `ℝᴾ`** (Simon Ch. 6, 2.23–2.24, used for the
changes of scale in 5.3).  `dil_k(λ, X) = δ_{λ#}X`, `δ_{λ#}X(ω) = X(δ_λ^#ω)`, is the push-forward
along the proper affine map `x ↦ 0 + (λ·id)x`; for `λ = 0` it is `X` (never used).  For `λ > 0` it
is additive, is inverted by `dil(λ⁻¹, ·)` because `(δ_λ^#ω)(x) = λᵏω(λx)`, and commutes with `∂`
(2.24(1)).  Mass scales by `λᵏ`, supports scale by `λ` and integer multiplicity is preserved; the
three children prove these for every `Y` with `Y(ω) = X(δ_λ^#ω)`. -/
theorem Submission.cmcdt_dilation_pushforward : ∀ P : ℕ, ∃ dil : ∀ k : ℕ, ℝ → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (lam : ℝ), 0 < lam → (∀ X Y : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam (X - Y) = dil k lam X - dil k lam Y) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, dil k lam⁻¹ (dil k lam X) = X) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).mass = ENNReal.ofReal (lam ^ k) * X.mass) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, (dil k lam X).support = (fun x => lam • x) '' X.support) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) k, IsIntegerMultiplicity X → IsIntegerMultiplicity (dil k lam X)) ∧ ∀ X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), (dil (k + 1) lam X).boundary = dil k lam X.boundary := by
  intro P
  classical
  -- Step 1: for `λ ≠ 0`, `x ↦ 0 + (λ·id)x = λx` is a homeomorphism, hence proper.
  have hprop : ∀ lam : ℝ, lam ≠ 0 → IsProperMap
      (fun x : Euclid P => (0 : Euclid P) + (lam • ContinuousLinearMap.id ℝ (Euclid P)) x) := by
    intro lam h
    convert (Homeomorph.smulOfNeZero (α := Euclid P) lam h).isProperMap using 1
    funext x
    simp
  -- `dil_k(λ, X) := δ_{λ#}X`; the domain `(x ↦ 0 + λx)⁻¹' univ` of `δ_{λ#}` lies in `univ`
  let D : ∀ k : ℕ, ℝ → GeometricCurrentOn (univ : Set (Euclid P)) k →
      GeometricCurrentOn (univ : Set (Euclid P)) k := fun k lam X =>
    if h : lam ≠ 0 then
      GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid P)))
        (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (hprop lam h)
        (X.restrictDomain (subset_univ _))
    else X
  have hD : ∀ (k : ℕ) (lam : ℝ) (h : lam ≠ 0) (X : GeometricCurrentOn (univ : Set (Euclid P)) k),
      D k lam X = GeometricCurrentOn.affinePushforward (V := (univ : Set (Euclid P)))
        (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (hprop lam h)
        (X.restrictDomain (subset_univ _)) := by
    intro k lam h X
    exact dite_eq_left h
  -- `δ_{λ#}X(ω) = X(η)` whenever `η = δ_λ^#ω`: the hypothesis of the mass, support and integer
  -- multiplicity children
  have hrel : ∀ (k : ℕ) (lam : ℝ) (h : lam ≠ 0) (X : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (ω η : TestFormOn (univ : Set (Euclid P)) k),
      (η : DifferentialForm (Euclid P) k) = affinePullbackForm
        (lam • ContinuousLinearMap.id ℝ (Euclid P)) 0 (ω : DifferentialForm (Euclid P) k) →
      D k lam X ω = X η := by
    intro k lam h X ω η hη
    rw [hD k lam h X, GeometricCurrentOn.affinePushforward_apply,
      GeometricCurrentOn.restrictDomain_apply]
    congr 1
    apply Subtype.ext
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe, hη]
  refine ⟨D, fun k lam hlam => ?_⟩
  have hne : lam ≠ 0 := hlam.ne'
  have hne' : lam⁻¹ ≠ 0 := inv_ne_zero hne
  refine ⟨fun X Y => ?_, fun X => ?_, fun X => ?_, fun X => ?_, fun X hX => ?_, fun X => ?_⟩
  -- (1), step 2: linearity, since the difference of currents acts pointwise
  · apply GeometricCurrentOn.ext
    intro ω
    rw [hD k lam hne, hD k lam hne, hD k lam hne]
    rfl
  -- (2), step 3: `(δ_λ^#δ_{λ⁻¹}^#ω)(x) = λᵏ(λ⁻¹)ᵏ ω(λ⁻¹λx) = ω(x)`
  · apply GeometricCurrentOn.ext
    intro ω
    obtain ⟨η₁, hη₁, hη₁'⟩ := Submission.cmcdt_dil_pullback_testForm P k lam⁻¹ hne' ω
    obtain ⟨η₂, hη₂, hη₂'⟩ := Submission.cmcdt_dil_pullback_testForm P k lam hne η₁
    rw [hrel k lam⁻¹ hne' (D k lam X) ω η₁ hη₁, hrel k lam hne X η₁ η₂ hη₂]
    congr 1
    apply Subtype.ext
    funext x
    rw [hη₂', hη₁', smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul,
      inv_smul_smul₀ hne]
  -- (3), step 5: `M(δ_{λ#}X) = λᵏ M(X)`
  · exact Submission.cmcdt_dil_mass_eq P k lam hlam X (D k lam X) (hrel k lam hne X)
  -- (4), step 6: `spt δ_{λ#}X = λ spt X`
  · exact Submission.cmcdt_dil_support_eq P k lam hlam X (D k lam X) (hrel k lam hne X)
  -- (5), step 7: `δ_{λ#}X` is integer multiplicity, represented by `(λM, θ(·/λ), ξ(·/λ))`
  · exact Submission.cmcdt_dil_isIntegerMultiplicity P k lam hlam X (D k lam X)
      (hrel k lam hne X) hX
  -- (6), step 4: `∂δ_{λ#} = δ_{λ#}∂` (2.24(1)); restricting the domain commutes with `∂` by
  -- definition
  · rw [hD (k + 1) lam hne, hD k lam hne, GeometricCurrentOn.boundary_affinePushforward]
    congr 1
/-- Coordinate functionals of a locally bounded `L : C_c(X, ℝᵈ) → ℝ`: `Λᵢ(f) = L(f • eᵢ)` is
linear and locally bounded with the same constants.  `T f := f.compLeft (t ↦ t • eᵢ)` is linear
with `(T f)(x) = f(x) • eᵢ`, `tsupport (T f) ⊆ tsupport f` and `‖(T f)(x)‖ = |f(x)|`;
take `Λᵢ := L ∘ T`. -/
theorem Submission.cmr_vr_coordinate_functional : ∀ (X : Type) [TopologicalSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∀ i : Fin d, ∃ Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ, (∀ (f : CompactlySupportedContinuousMap X ℝ) (g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d))), (∀ x, g x = f x • EuclideanSpace.single i (1 : ℝ)) → L g = Λ f) ∧ ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M := by
  intro X _ d L hL i
  -- `c t = t • eᵢ` is continuous and `c 0 = 0`, so `T f := f.compLeft c` has `(T f) x = f x • eᵢ`
  let c : C(ℝ, EuclideanSpace ℝ (Fin d)) :=
    ⟨fun t => t • EuclideanSpace.single i (1 : ℝ), continuous_id.smul continuous_const⟩
  have hc0 : c 0 = 0 := zero_smul ℝ _
  have hT : ∀ (f : CompactlySupportedContinuousMap X ℝ) (x : X),
      f.compLeft c x = f x • EuclideanSpace.single i (1 : ℝ) :=
    fun f x => CompactlySupportedContinuousMap.compLeft_apply hc0 f x
  -- `T` is linear (pointwise, then extensionality); `Λ := L ∘ T`
  let T : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ]
      CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) :=
    { toFun := fun f => f.compLeft c
      map_add' := fun f₁ f₂ => CompactlySupportedContinuousMap.ext fun x => by
        simp only [hT, CompactlySupportedContinuousMap.add_apply, add_smul]
      map_smul' := fun r f => CompactlySupportedContinuousMap.ext fun x => by
        simp only [hT, CompactlySupportedContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul,
          mul_smul] }
  refine ⟨L ∘ₗ T, fun f g hg => ?_, fun K hK => ?_⟩
  · -- `g = T f` by extensionality
    exact congrArg L (CompactlySupportedContinuousMap.ext fun x => (hg x).trans (hT f x).symm)
  · -- `tsupport (T f) ⊆ tsupport f ⊆ K` and `‖(T f) x‖ = |f x| ≤ 1`: same constant `M`
    obtain ⟨M, hM⟩ := hL K hK
    refine ⟨M, fun f hf hf1 => hM (T f) ?_ fun x => ?_⟩
    · have hTf : ⇑(T f) = fun x => f x • EuclideanSpace.single i (1 : ℝ) := funext (hT f)
      rw [hTf]
      exact (tsupport_smul_subset_left _ _).trans hf
    · show ‖f.compLeft c x‖ ≤ 1
      rw [hT, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      exact hf1 x
/-- Jordan decomposition of a locally bounded `Λ : C_c(X, ℝ) → ℝ`.  For `f : C_c(X, ℝ≥0)` put
`V f := sup {Λ h : |h| ≤ f}` (bounded above by rescaling the local bound on `tsupport f`).  `V` is
additive (clamp `h₁ := (h ⊓ f) ⊔ (-f)`) and `ℝ≥0`-homogeneous, so `V̂ := toRealPositiveLinear V`
is positive; `V̂ + Λ` is positive since `-k` is admissible for `k ≥ 0`, and `Λ = (V̂ + Λ) - V̂`. -/
theorem Submission.cmr_vr_jordan_decomposition : ∀ (X : Type) [TopologicalSpace X] (Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M) → ∃ Λ₁ Λ₂ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, Λ f = Λ₁ f - Λ₂ f := by
  intro X _ Λ hΛ
  -- scaled bound: `tsupport f ⊆ K`, `|f| ≤ s` give `|Λ f| ≤ s * M_K` (`s = 0`, else rescale)
  have hscale : ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ (f : CompactlySupportedContinuousMap X ℝ)
      (s : ℝ), tsupport f ⊆ K → 0 ≤ s → (∀ x, |f x| ≤ s) → |Λ f| ≤ s * M := by
    intro K hK
    obtain ⟨M, hM⟩ := hΛ K hK
    refine ⟨M, fun f s hfK hs hfs => ?_⟩
    rcases hs.eq_or_lt with rfl | hspos
    · have hf0 : f = 0 := by
        ext x
        simpa using hfs x
      simp [hf0]
    · have hsub : tsupport (s⁻¹ • f) ⊆ K :=
        (tsupport_smul_subset_right (fun _ : X => s⁻¹) f).trans hfK
      have hbd : ∀ x, |(s⁻¹ • f) x| ≤ 1 := by
        intro x
        rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, abs_mul,
          abs_of_pos (inv_pos.mpr hspos)]
        calc s⁻¹ * |f x| ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left (hfs x) (inv_pos.mpr hspos).le
          _ = 1 := inv_mul_cancel₀ hspos.ne'
      have h1 := hM _ hsub hbd
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hspos)] at h1
      have := (inv_mul_le_iff₀ hspos).mp h1
      linarith
  -- `A f = {h : |h| ≤ f}` contains `0`, and `Λ '' A f` is bounded above: members of `A f` have
  -- `tsupport h ⊆ tsupport f` and `|h| ≤ max C 0` with `C` a bound for `f`
  let A : CompactlySupportedContinuousMap X NNReal → Set (CompactlySupportedContinuousMap X ℝ) :=
    fun f => {h | ∀ x, |h x| ≤ (f x : ℝ)}
  have hA0 : ∀ f, (0 : CompactlySupportedContinuousMap X ℝ) ∈ A f := by
    intro f x
    simp
  have hbdd : ∀ f, BddAbove (Λ '' A f) := by
    intro f
    obtain ⟨M, hM⟩ := hscale (tsupport f) f.hasCompactSupport.isCompact
    obtain ⟨C, hC⟩ := f.toReal.continuous.bounded_above_of_compact_support
      f.toReal.hasCompactSupport
    refine ⟨max C 0 * M, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have hsupp : tsupport h ⊆ tsupport f := by
      apply closure_mono
      intro x hx hfx
      apply hx
      have := hh x
      rw [hfx] at this
      simpa using this
    have hbd : ∀ x, |h x| ≤ max C 0 := by
      intro x
      refine (hh x).trans ((le_abs_self _).trans ?_)
      have h' : ‖f.toReal x‖ ≤ C := hC x
      rw [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    exact (le_abs_self _).trans (hM h _ hsupp (le_max_right _ _) hbd)
  -- the variation `V f = sup (Λ '' A f) ≥ Λ 0 = 0`
  let V : CompactlySupportedContinuousMap X NNReal → ℝ := fun f => sSup (Λ '' A f)
  have hle : ∀ f, ∀ h ∈ A f, Λ h ≤ V f := fun f h hh => le_csSup (hbdd f) ⟨h, hh, rfl⟩
  have hVle : ∀ f (c : ℝ), (∀ h ∈ A f, Λ h ≤ c) → V f ≤ c := by
    intro f c hc
    exact csSup_le ⟨0, 0, hA0 f, map_zero Λ⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
  have hV0 : ∀ f, 0 ≤ V f := fun f => by simpa using hle f 0 (hA0 f)
  -- additivity: `≤` by the clamp `h₁ = (h ⊓ f) ⊔ (-f)`, `h - h₁ ∈ A g`; `≥` by `h₁ + h₂ ∈ A (f + g)`
  have hadd : ∀ f g, V (f + g) = V f + V g := by
    intro f g
    apply le_antisymm
    · apply hVle
      intro h hh
      let h₁ : CompactlySupportedContinuousMap X ℝ := (h ⊓ f.toReal) ⊔ (-f.toReal)
      have hpt : ∀ x, |h₁ x| ≤ (f x : ℝ) ∧ |(h - h₁) x| ≤ (g x : ℝ) := by
        intro x
        have hx := hh x
        have hf0 : (0 : ℝ) ≤ f x := (f x).2
        have hg0 : (0 : ℝ) ≤ g x := (g x).2
        simp only [CompactlySupportedContinuousMap.add_apply, NNReal.coe_add] at hx
        simp only [h₁, CompactlySupportedContinuousMap.sub_apply,
          CompactlySupportedContinuousMap.sup_apply, CompactlySupportedContinuousMap.inf_apply,
          CompactlySupportedContinuousMap.neg_apply, CompactlySupportedContinuousMap.toReal_apply]
        rw [abs_le] at hx ⊢
        rw [abs_le]
        rcases le_total (h x) (f x) with h1 | h1
        · rw [min_eq_left h1]
          rcases le_total (h x) (-(f x : ℝ)) with h2 | h2
          · rw [max_eq_right h2]
            constructor <;> constructor <;> linarith
          · rw [max_eq_left h2]
            constructor <;> constructor <;> linarith
        · rw [min_eq_right h1, max_eq_left (by linarith)]
          constructor <;> constructor <;> linarith
      have h1mem : h₁ ∈ A f := fun x => (hpt x).1
      have h2mem : h - h₁ ∈ A g := fun x => (hpt x).2
      have e : Λ h = Λ h₁ + Λ (h - h₁) := by rw [map_sub]; ring
      rw [e]
      exact add_le_add (hle f h₁ h1mem) (hle g _ h2mem)
    · have key : V f ≤ V (f + g) - V g := by
        apply hVle
        intro h₁ hh₁
        have : V g ≤ V (f + g) - Λ h₁ := by
          apply hVle
          intro h₂ hh₂
          have hmem : h₁ + h₂ ∈ A (f + g) := by
            intro x
            simp only [CompactlySupportedContinuousMap.add_apply, NNReal.coe_add]
            exact (abs_add_le _ _).trans (add_le_add (hh₁ x) (hh₂ x))
          have := hle _ _ hmem
          rw [map_add] at this
          linarith
        linarith
      linarith
  -- homogeneity: `A 0 = {0}`; for `c > 0`, `h ↦ c⁻¹ • h` maps `A (c • f)` into `A f`
  have hzero : V 0 = 0 := by
    apply le_antisymm _ (hV0 0)
    apply hVle
    intro h hh
    have : h = 0 := by
      ext x
      simpa using hh x
    simp [this]
  have hsmul_le : ∀ (c : NNReal) f, V (c • f) ≤ c * V f := by
    intro c f
    rcases eq_or_ne c 0 with rfl | hc
    · simp [hzero]
    have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    apply hVle
    intro h hh
    have hmem : (c : ℝ)⁻¹ • h ∈ A f := by
      intro x
      have := hh x
      simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, NNReal.coe_mul] at this
      rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hcpos)]
      rw [inv_mul_le_iff₀ hcpos]
      exact this
    have := hle f _ hmem
    rw [map_smul, smul_eq_mul] at this
    exact (inv_mul_le_iff₀ hcpos).mp this
  have hsmul : ∀ (c : NNReal) f, V (c • f) = c * V f := by
    intro c f
    rcases eq_or_ne c 0 with rfl | hc
    · simp [hzero]
    have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    apply le_antisymm (hsmul_le c f)
    have h := hsmul_le c⁻¹ (c • f)
    rw [inv_smul_smul₀ hc, NNReal.coe_inv] at h
    exact (le_inv_mul_iff₀ hcpos).mp h
  -- `V` is `ℝ≥0`-linear; `V̂ := toRealPositiveLinear V` is a positive functional on `C_c(X, ℝ)`
  let W : CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    { toFun := fun f => ⟨V f, hV0 f⟩
      map_add' := fun f g => NNReal.eq (hadd f g)
      map_smul' := fun c f => NNReal.eq (hsmul c f) }
  let Vh := CompactlySupportedContinuousMap.toRealPositiveLinear W
  -- `V̂ + Λ` is positive: for `k ≥ 0`, `V̂ k = V k⁺` and `-k ∈ A k⁺`, so `-Λ k ≤ V̂ k`
  have hdom : ∀ k : CompactlySupportedContinuousMap X ℝ, 0 ≤ k → 0 ≤ Vh k + Λ k := by
    intro k hk
    have hkeq : k.nnrealPart.toReal = k := by
      ext x
      rw [CompactlySupportedContinuousMap.toReal_apply,
        CompactlySupportedContinuousMap.nnrealPart_apply]
      exact Real.coe_toNNReal _ (hk x)
    have hVk : Vh k = V k.nnrealPart := by
      have := CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal W k.nnrealPart
      rw [hkeq] at this
      exact this
    have hmem : -k ∈ A k.nnrealPart := by
      intro x
      rw [CompactlySupportedContinuousMap.neg_apply, abs_neg,
        CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal _ (hk x)]
      exact (abs_of_nonneg (hk x)).le
    have := hle _ _ hmem
    rw [map_neg] at this
    rw [hVk]
    linarith
  refine ⟨PositiveLinearMap.mk₀ (Vh.toLinearMap + Λ) hdom, Vh, fun f => ?_⟩
  show Λ f = (Vh f + Λ f) - Vh f
  ring
/-- Common dominating measure (the common density step of the vector Riesz representation behind
the mass representation of currents, Simon Ch. 6, 2.7–2.8, used for Simon 7.2.4): if every `aᵢ`
and `bᵢ` (`i ∈ Fin m`) is finite on compact sets, then so is `μ₀ := ∑ᵢ (aᵢ + bᵢ)`, and
`aᵢ ≪ μ₀`, `bᵢ ≪ μ₀`.  Indeed `μ₀(s) = ∑ᵢ (aᵢ(s) + bᵢ(s))` for every set `s`, so `μ₀(K)` is a
finite sum of finite terms for compact `K`, and `μ₀(s) = 0` forces `aᵢ(s) = bᵢ(s) = 0`. -/
theorem Submission.cmr_vr_cd_dominating_measure : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] (m : ℕ) (a b : Fin m → Measure X), (∀ i, IsFiniteMeasureOnCompacts (a i)) → (∀ i, IsFiniteMeasureOnCompacts (b i)) → ∃ μ₀ : Measure X, IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, a i ≪ μ₀) ∧ ∀ i, b i ≪ μ₀ := by
  intro X _ _ m a b ha hb
  -- Step 1: `μ₀ := ∑ᵢ (aᵢ + bᵢ)` has `μ₀(s) = ∑ᵢ (aᵢ(s) + bᵢ(s))` for every set `s`
  have hμ₀ : ∀ s : Set X, (∑ i, (a i + b i)) s = ∑ i, (a i s + b i s) := fun s => by
    simp only [Measure.finsetSum_apply, Measure.add_apply]
  refine ⟨∑ i, (a i + b i), ⟨fun K hK => ?_⟩, fun i s hs => ?_, fun i s hs => ?_⟩
  -- Step 2: for compact `K`, `μ₀(K)` is a finite sum of finite terms
  · rw [hμ₀, ENNReal.sum_lt_top]
    exact fun i _ =>
      ENNReal.add_lt_top.2 ⟨(ha i).lt_top_of_isCompact hK, (hb i).lt_top_of_isCompact hK⟩
  -- Step 3: if `μ₀(s) = 0`, every summand `aᵢ(s) + bᵢ(s)` vanishes
  · rw [hμ₀, Finset.sum_eq_zero_iff] at hs
    exact (add_eq_zero.1 (hs i (Finset.mem_univ i))).1
  · rw [hμ₀, Finset.sum_eq_zero_iff] at hs
    exact (add_eq_zero.1 (hs i (Finset.mem_univ i))).2
/-- **Radon–Nikodym density on `C_c`.**  If `μ₀`, `ξ` are finite on compact subsets of a locally
compact second countable space and `ξ ≪ μ₀`, then `ξ` has a measurable density `g`, `μ₀`-integrable
on compact sets, with `f·g` `μ₀`-integrable and `∫ f dξ = ∫ f g dμ₀` for every `f ∈ C_c(X, ℝ)`.
`X` is σ-compact, so `μ₀`, `ξ` are σ-finite and `ξ = μ₀.withDensity δ` for `δ = ξ.rnDeriv μ₀`
(the singular part vanishes since `ξ ≪ μ₀`), with `δ < ∞` `μ₀`-a.e.  Take `g = δ.toReal`: on a
compact `K`, `∫⁻_K δ dμ₀ < ∞` because `ξ(K) < ∞`.  A bounded `f` with compact support times `g` is
integrable on `tsupport f` and vanishes outside it.  The `T2Space` hypothesis is not used. -/
theorem Submission.cmr_vr_cd_density_representation : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ₀ ξ : Measure X), IsFiniteMeasureOnCompacts μ₀ → IsFiniteMeasureOnCompacts ξ → ξ ≪ μ₀ → ∃ g : X → ℝ, Measurable g ∧ (∀ K : Set X, IsCompact K → IntegrableOn g K μ₀) ∧ ∀ f : CompactlySupportedContinuousMap X ℝ, Integrable (fun x => f x * g x) μ₀ ∧ ∫ x, f x ∂ξ = ∫ x, f x * g x ∂μ₀ := by
  intro X _ _ _ _ _ _ μ₀ ξ hμ₀ hξ hac
  -- `X` is σ-compact, so both measures are σ-finite and `(ξ, μ₀)` has a Lebesgue decomposition
  have : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite μ₀ := SigmaFinite.of_isFiniteMeasureOnCompacts μ₀
  have : SigmaFinite ξ := SigmaFinite.of_isFiniteMeasureOnCompacts ξ
  -- `ξ = μ₀.withDensity δ` with `δ = dξ/dμ₀` measurable and `μ₀`-a.e. finite
  set δ : X → ℝ≥0∞ := ξ.rnDeriv μ₀
  have hδm : Measurable δ := Measure.measurable_rnDeriv ξ μ₀
  have hξδ : ξ = μ₀.withDensity δ := by
    have h := Measure.haveLebesgueDecomposition_add ξ μ₀
    rwa [Measure.singularPart_eq_zero_of_ac hac, zero_add] at h
  have hδlt : ∀ᵐ x ∂μ₀, δ x < ∞ := Measure.rnDeriv_lt_top ξ μ₀
  -- `g = δ.toReal` is integrable on compact sets: `∫⁻_K δ dμ₀ < ∞` since `ξ(K) < ∞`
  have hgK : ∀ K : Set X, IsCompact K → IntegrableOn (fun x => (δ x).toReal) K μ₀ := by
    intro K hK
    have hlin : ∫⁻ x in K, δ x ∂μ₀ < ∞ :=
      Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top μ₀ hK.measure_lt_top.ne
    exact integrable_toReal_of_lintegral_ne_top hδm.aemeasurable hlin.ne
  refine ⟨fun x => (δ x).toReal, hδm.ennreal_toReal, hgK, fun f => ⟨?_, ?_⟩⟩
  -- `f` is bounded, so `f·g` is integrable on `tsupport f`, and it vanishes outside
  · obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
    have hon : IntegrableOn (fun x => f x * (δ x).toReal) (tsupport f) μ₀ :=
      Integrable.bdd_mul (c := C) (hgK _ f.hasCompactSupport.isCompact)
        (map_continuous f).measurable.aestronglyMeasurable (Eventually.of_forall hC)
    refine hon.integrable_of_forall_notMem_eq_zero fun x hx => ?_
    simp [image_eq_zero_of_notMem_tsupport hx]
  -- `∫ f dξ = ∫ δ.toReal • f dμ₀`
  · rw [hξδ, integral_withDensity_eq_integral_toReal_smul hδm hδlt]
    congr 1
    funext x
    exact (smul_eq_mul _ _).trans (mul_comm _ _)

/-- Common dominating measure and densities for finitely many pairs of positive functionals
(Riesz–Markov–Kakutani; Rudin, *Real and Complex Analysis*, Thm 2.14 and 6.10).  Let `X` be
locally compact, Hausdorff and second countable with its Borel σ-algebra, and let `Λ₁ᵢ, Λ₂ᵢ`
(`i ∈ Fin m`) be positive linear functionals on `C_c(X, ℝ)`.  Then there are a measure `μ₀`,
finite on compact sets, and measurable `ρᵢ`, `μ₀`-integrable on compact sets, with
`Λ₁ᵢ f - Λ₂ᵢ f = ∫ f ρᵢ dμ₀` for all `f ∈ C_c(X, ℝ)`.

Proof sketch:
* `bᵢ := rieszMeasure Λ₁ᵢ` and `aᵢ := rieszMeasure Λ₂ᵢ` are regular, hence finite on compact
  sets, and `∫ f dbᵢ = Λ₁ᵢ f`, `∫ f daᵢ = Λ₂ᵢ f`.
* `cmr_vr_cd_dominating_measure` gives a compact-finite `μ₀` with `aᵢ ≪ μ₀` and `bᵢ ≪ μ₀`.
* `cmr_vr_cd_density_representation` gives locally integrable densities `gaᵢ`, `gbᵢ` with
  `∫ f daᵢ = ∫ f gaᵢ dμ₀`, `∫ f dbᵢ = ∫ f gbᵢ dμ₀`, both integrands integrable.
* With `ρᵢ := gbᵢ - gaᵢ`, linearity of the integral gives the representation. -/
theorem Submission.cmr_vr_common_density : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (Λ₁ Λ₂ : Fin m → (CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)), ∃ (μ₀ : Measure X) (ρ : Fin m → X → ℝ), IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, Measurable (ρ i)) ∧ (∀ i, ∀ K : Set X, IsCompact K → IntegrableOn (ρ i) K μ₀) ∧ ∀ (i : Fin m) (f : CompactlySupportedContinuousMap X ℝ), Λ₁ i f - Λ₂ i f = ∫ x, f x * ρ i x ∂μ₀ := by
  intro X _ _ _ _ _ _ m Λ₁ Λ₂
  -- Step 1 (RMK): the Riesz measures are regular, hence finite on compact sets
  have ha : ∀ i, IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure (Λ₂ i)) :=
    fun _ => inferInstance
  have hb : ∀ i, IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure (Λ₁ i)) :=
    fun _ => inferInstance
  -- Step 2: a common compact-finite measure `μ₀` with `aᵢ ≪ μ₀` and `bᵢ ≪ μ₀`
  obtain ⟨μ₀, hμ₀, hac_a, hac_b⟩ := Submission.cmr_vr_cd_dominating_measure X m
    (fun i => RealRMK.rieszMeasure (Λ₂ i)) (fun i => RealRMK.rieszMeasure (Λ₁ i)) ha hb
  -- Step 3: locally integrable densities `gaᵢ`, `gbᵢ` of `aᵢ`, `bᵢ` with respect to `μ₀`
  choose ga hga_meas hga_int hga_rep using fun i =>
    Submission.cmr_vr_cd_density_representation X μ₀ (RealRMK.rieszMeasure (Λ₂ i)) hμ₀ (ha i)
      (hac_a i)
  choose gb hgb_meas hgb_int hgb_rep using fun i =>
    Submission.cmr_vr_cd_density_representation X μ₀ (RealRMK.rieszMeasure (Λ₁ i)) hμ₀ (hb i)
      (hac_b i)
  -- Step 4: `ρᵢ := gbᵢ - gaᵢ` and linearity of the integral
  refine ⟨μ₀, fun i => gb i - ga i, hμ₀, fun i => (hgb_meas i).sub (hga_meas i),
    fun i K hK => (hgb_int i K hK).sub (hga_int i K hK), fun i f => ?_⟩
  obtain ⟨hgb_f, hgb_eq⟩ := hgb_rep i f
  obtain ⟨hga_f, hga_eq⟩ := hga_rep i f
  calc Λ₁ i f - Λ₂ i f
      = ∫ x, f x ∂(RealRMK.rieszMeasure (Λ₁ i)) - ∫ x, f x ∂(RealRMK.rieszMeasure (Λ₂ i)) := by
        rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    _ = ∫ x, f x * gb i x ∂μ₀ - ∫ x, f x * ga i x ∂μ₀ := by rw [hgb_eq, hga_eq]
    _ = ∫ x, (f x * gb i x - f x * ga i x) ∂μ₀ := (integral_sub hgb_f hga_f).symm
    _ = ∫ x, f x * (gb i - ga i) x ∂μ₀ := by simp only [Pi.sub_apply, mul_sub]
/-- Assembly of coordinate densities (vector Riesz representation, coordinate step): if the
`i`-th coordinate functional `f ↦ L(f eᵢ)` has density `ρᵢ` w.r.t. `μ₀` for each `i`, then `L` has
the vector density `ν = Σᵢ ρᵢ eᵢ`, i.e. `L g = ∫ ⟨g, ν⟩ dμ₀`.  Write `g = Σᵢ gᵢ eᵢ` with
`gᵢ = ⟨g, eᵢ⟩ ∈ C_c(X)`; each `gᵢ ρᵢ` is integrable (bounded continuous times integrable on the
compact `tsupport gᵢ`, zero outside it), so the finite sum and the integral commute. -/
theorem Submission.cmr_vr_coordinate_assembly : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ) (μ₀ : Measure X) (ρ : Fin d → X → ℝ), (∀ i, Measurable (ρ i)) → (∀ i, ∀ K : Set X, IsCompact K → IntegrableOn (ρ i) K μ₀) → (∀ (i : Fin d) (f : CompactlySupportedContinuousMap X ℝ) (g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d))), (∀ x, g x = f x • EuclideanSpace.single i (1 : ℝ)) → L g = ∫ x, f x * ρ i x ∂μ₀) → ∃ ν : X → EuclideanSpace ℝ (Fin d), Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀ := by
  intro X _ _ _ d L μ₀ ρ hρm hρi hL
  -- `ν = Σᵢ ρᵢ eᵢ`
  refine ⟨fun x => ∑ i, ρ i x • EuclideanSpace.single i (1 : ℝ),
    Finset.measurable_sum _ fun i _ => (hρm i).smul_const _,
    fun K hK => integrable_finsetSum _ fun i _ => (hρi i K hK).smul_const _, fun g => ?_⟩
  -- the coordinates `gᵢ = g(·)ᵢ ∈ C_c(X, ℝ)` and `Gᵢ = gᵢ eᵢ ∈ C_c(X, H)`
  obtain ⟨gc, hgc⟩ : ∃ gc : Fin d → CompactlySupportedContinuousMap X ℝ, ∀ i x, gc i x = g x i :=
    ⟨fun i => g.compLeft (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      fun i x => CompactlySupportedContinuousMap.compLeft_apply (by simp) g x⟩
  obtain ⟨G, hG⟩ : ∃ G : Fin d → CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)),
      ∀ i x, G i x = gc i x • EuclideanSpace.single i (1 : ℝ) :=
    ⟨fun i => (gc i).compLeft ⟨fun t => t • EuclideanSpace.single i (1 : ℝ), by fun_prop⟩,
      fun i x => CompactlySupportedContinuousMap.compLeft_apply (zero_smul ℝ _) (gc i) x⟩
  -- `g = Σᵢ Gᵢ`
  have hsum : g = ∑ i, G i := by
    ext x j
    simp [hG, hgc, Pi.single_apply]
  -- each `gᵢ ρᵢ` is integrable: bounded continuous times integrable on the compact `tsupport gᵢ`
  have hint : ∀ i, Integrable (fun x => gc i x * ρ i x) μ₀ := by
    intro i
    obtain ⟨C, hC⟩ := (gc i).continuous.bounded_above_of_compact_support (gc i).hasCompactSupport
    have hK : IntegrableOn (fun x => gc i x * ρ i x) (tsupport (gc i)) μ₀ :=
      Integrable.bdd_mul (hρi i _ (gc i).hasCompactSupport.isCompact)
        (gc i).continuous.aestronglyMeasurable (Eventually.of_forall hC)
    exact hK.integrable_of_forall_notMem_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  calc L g = ∑ i, L (G i) := (congrArg L hsum).trans (map_sum L G Finset.univ)
    _ = ∑ i, ∫ x, gc i x * ρ i x ∂μ₀ := Finset.sum_congr rfl fun i _ => hL i (gc i) (G i) (hG i)
    _ = ∫ x, ∑ i, gc i x * ρ i x ∂μ₀ := (integral_finsetSum _ fun i _ => hint i).symm
    _ = ∫ x, inner ℝ (g x) (∑ i, ρ i x • EuclideanSpace.single i (1 : ℝ)) ∂μ₀ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_right, EuclideanSpace.inner_single_right, hgc, conj_trivial, one_mul, mul_comm]

/-- **Riesz representation of locally bounded functionals on `C_c(X, ℝ^d)`** (Simon Ch. 1, 4.14,
in the form used for currents in Ch. 6, 2.7).  If `X` is locally compact Hausdorff and second
countable and `L : C_c(X, ℝ^d) → ℝ` is linear with `|L g| ≤ M_K` whenever `spt g ⊆ K` and
`|g| ≤ 1`, then `L g = ∫ ⟨g, ν⟩ dμ₀` for a Borel measure `μ₀` finite on compact sets and a
measurable `ν : X → ℝ^d` integrable on compact sets.  The coordinate functionals
`Λᵢ f = L(f eᵢ)` are locally bounded, each splits as a difference `Pᵢ − Nᵢ` of positive
functionals (total variation), the Riesz–Markov–Kakutani measures of all `Pᵢ, Nᵢ` have densities
`ρᵢ` against one common `μ₀`, and `ν = Σᵢ ρᵢ eᵢ`. -/
theorem Submission.cmr_vector_riesz_representation : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∃ (μ₀ : Measure X) (ν : X → EuclideanSpace ℝ (Fin d)), IsFiniteMeasureOnCompacts μ₀ ∧ Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀ := by
  intro X _ _ _ _ _ _ d L hL
  -- step 1: the coordinate functionals `Λᵢ f = L(f eᵢ)`, locally bounded
  choose Λ hΛL hΛbd using Submission.cmr_vr_coordinate_functional X d L hL
  -- steps 2–3: Jordan decomposition `Λᵢ = Pᵢ − Nᵢ` into positive functionals
  choose Pos Neg hΛ using fun i => Submission.cmr_vr_jordan_decomposition X (Λ i) (hΛbd i)
  -- steps 4–6 and 8: one measure `μ₀` with `Pᵢ f − Nᵢ f = ∫ f ρᵢ dμ₀`
  obtain ⟨μ₀, ρ, hμ₀, hρm, hρint, hρ⟩ := Submission.cmr_vr_common_density X d Pos Neg
  -- steps 7 and 9: `ν = Σᵢ ρᵢ eᵢ` and `L g = Σᵢ ∫ gᵢ ρᵢ dμ₀ = ∫ ⟨g, ν⟩ dμ₀`
  obtain ⟨ν, hνm, hνint, hν⟩ := Submission.cmr_vr_coordinate_assembly X d L μ₀ ρ hρm hρint
    fun i f g hg => by rw [hΛL i f g hg, hΛ i f, hρ i f]
  exact ⟨μ₀, ν, hμ₀, hνm, hνint, hν⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
