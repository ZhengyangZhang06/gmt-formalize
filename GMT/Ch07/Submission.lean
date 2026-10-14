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

/-- Reflection symmetries of the coordinate Steiner symmetrization (Simon, Ch. 1, proof of 2.10).
Write `y[i↦t]` for `y` with `i`-th coordinate replaced by `t`, `R_i(y) = y[i↦-y_i]`,
`A^j_y = {t : y[j↦t] ∈ A}` and `S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ L¹(A^j_y)/2}`.  Then (a) `S_j(A)`
is invariant under `R_j`, and (b) if `i ≠ j` and `A` is invariant under `R_i`, so is `S_j(A)`.
For (a), `R_j(y)[j↦t] = y[j↦t]`; for (b), `R_i(y)[j↦t] = R_i(y[j↦t])` and `R_i` is an involution,
so the `j`-slices of `y` and of its reflection agree, while `|(R_i y)_j| = |y_j|`. -/
theorem Submission.cbr_ci_iso_steiner_reflection : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), (∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}) ∧ ∀ i : Fin d, i ≠ j → (∀ x ∈ A, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ A) → ∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
  intro d j A
  refine ⟨fun x hx => ?_, fun i hij hA x hx => ?_⟩
  · -- (a) `R_j(x)[j↦t] = x[j↦t]`, so the `j`-slice is unchanged, and `|(R_j x)_j| = |x_j|`
    simpa using hx
  · -- (b) `R_i` is an involution and commutes with `y ↦ y[j↦t]`, so the `j`-slices of `x` and
    -- `R_i(x)` agree; moreover `(R_i x)_j = x_j` since `i ≠ j`
    have hR : ∀ z : Euclid d, WithLp.toLp 2 (update (WithLp.toLp 2 (update z.ofLp i (-z i))).ofLp i
        (-(WithLp.toLp 2 (update z.ofLp i (-z i))) i)) = z := by
      intro z
      ext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    have hcomm : ∀ t : ℝ, WithLp.toLp 2 (update (update x.ofLp i (-x i)) j t) =
        WithLp.toLp 2 (update (WithLp.toLp 2 (update x.ofLp j t)).ofLp i
          (-(WithLp.toLp 2 (update x.ofLp j t)) i)) := by
      intro t
      simp only [update_of_ne hij]
      rw [update_comm hij]
    have hslice : {t : ℝ | WithLp.toLp 2 (update (WithLp.toLp 2 (update x.ofLp i (-x i))).ofLp j t) ∈ A} =
        {t : ℝ | WithLp.toLp 2 (update x.ofLp j t) ∈ A} := by
      ext t
      simp only [Set.mem_ofPred_eq]
      rw [hcomm t]
      constructor
      · intro h
        have h' := hA _ h
        rwa [hR] at h'
      · exact hA _
    have hxj : (WithLp.toLp 2 (update x.ofLp i (-x i))) j = x j := by
      simp [hij.symm]
    show _ ∧ _
    rw [hslice, hxj]
    exact hx
/-- **Steiner symmetrization does not increase the diameter** (Simon 2.10, proof of the
isodiametric inequality).  For compact `A ⊆ ℝᵈ` and `j < d`, write `y[j↦t]` for `y` with its `j`-th
coordinate replaced by `t`, `A^j_y = {t : y[j↦t] ∈ A}`, `λ(y) = L¹(A^j_y)` and
`S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ λ(y)/2}`; then `ediam S_j(A) ≤ ediam A`.  Each slice `A^j_y` is
compact, so it contains `a_y = inf A^j_y` and `b_y = sup A^j_y`, and `λ(y) ≤ b_y - a_y`.  For
`x, y ∈ S_j(A)`, `|x_j - y_j| ≤ (λ(x) + λ(y))/2 ≤ max(b_y - a_x, b_x - a_y)`, and replacing the
`j`-th coordinates of `x, y` by the matching endpoints gives two points of `A` at distance at least
`|x - y|`. -/
theorem Submission.cbr_ci_iso_steiner_ediam_le : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → ediam {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} ≤ ediam A := by
  intro d j A hA
  -- (1) every slice `A^j_y` is compact: closed, and contained in the compact image of `A`
  -- under the `j`-th coordinate
  have hslice : ∀ y : Euclid d,
      IsCompact {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} := by
    intro y
    have hf : Continuous fun t : ℝ => WithLp.toLp 2 (Function.update y.ofLp j t) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_const.update j continuous_id)
    refine (hA.image (PiLp.continuous_apply 2 _ j)).of_isClosed_subset
      (hA.isClosed.preimage hf) fun t ht => ⟨_, ht, by simp⟩
  -- (2) a nonempty compact `P ⊆ ℝ` contains `inf P` and `sup P`, and `L¹(P) ≤ sup P - inf P`
  have hlen : ∀ P : Set ℝ, IsCompact P → P.Nonempty →
      sInf P ∈ P ∧ sSup P ∈ P ∧ (volume P).toReal ≤ sSup P - sInf P := by
    intro P hP hne
    refine ⟨hP.sInf_mem hne, hP.sSup_mem hne, ?_⟩
    refine ENNReal.toReal_le_of_le_ofReal
      (sub_nonneg.mpr (csInf_le_csSup hne hP.bddBelow hP.bddAbove)) ?_
    calc volume P ≤ volume (Icc (sInf P) (sSup P)) :=
          measure_mono fun t ht => ⟨csInf_le hP.bddBelow ht, le_csSup hP.bddAbove ht⟩
      _ = ENNReal.ofReal (sSup P - sInf P) := Real.volume_Icc
  -- (3) two-point estimate: replacing the `j`-th coordinates by `a, b` with
  -- `|x_j - y_j| ≤ |a - b|` does not decrease the distance
  have hpt : ∀ (x y : Euclid d) (a b : ℝ), WithLp.toLp 2 (Function.update x.ofLp j a) ∈ A →
      WithLp.toLp 2 (Function.update y.ofLp j b) ∈ A → |x j - y j| ≤ |a - b| →
      edist x y ≤ ediam A := by
    intro x y a b ha hb hab
    refine le_trans ?_ (edist_le_ediam_of_mem ha hb)
    rw [edist_dist, edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    · simp only [Function.update_of_ne hi, le_refl]
  -- (4) for `x, y ∈ S_j(A)`, `|x_j - y_j| ≤ (λ(x) + λ(y))/2` is realised by a pair of points of `A`
  refine ediam_le ?_
  rintro x ⟨hxne, hxj⟩ y ⟨hyne, hyj⟩
  obtain ⟨hax, hbx, hlx⟩ := hlen _ (hslice x) hxne
  obtain ⟨hay, hby, hly⟩ := hlen _ (hslice y) hyne
  have hx := abs_le.mp hxj
  have hy := abs_le.mp hyj
  rcases le_total
      (sSup {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A} -
        sInf {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A})
      (sSup {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} -
        sInf {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}) with h | h
  · refine hpt x y _ _ hax hby ?_
    rw [abs_sub_comm _ (sSup _)]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self _)
  · refine hpt x y _ _ hbx hay ?_
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self _)
/-- **Simon, Ch. 1, Note after the proof of 2.10** (p. 12): for compact `A ⊆ ℝᵈ` and a coordinate
`j`, the length `y ↦ L¹{t : y[j ↦ t] ∈ A}` of the slice of `A` along the `j`-th coordinate line
through `y` is upper semicontinuous.  Every slice lies in `[-R, R]` (`A ⊆ B_R(0)`), so has finite
length.  Given `L¹(A^j_x) < r`, outer regularity gives an open `U ⊇ A^j_x` with `L¹(U) < r`; the
compact set `C = A ∖ {z : z_j ∈ U}` has closed image under `π z = z[j ↦ 0]`, `π x ∉ π(C)`, and for
`y` in the neighbourhood `π⁻¹(π(C)ᶜ)` of `x` the slice `A^j_y` lies in `U`, so `L¹(A^j_y) < r`. -/
theorem Submission.cbr_ci_iso_slice_length_usc : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → UpperSemicontinuous (fun y : Euclid d => (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal) := by
  intro d j A hA
  -- every slice lies in `[-R, R]`, so it has finite length
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall (0 : Euclid d)
  have hfin : ∀ y : Euclid d,
      volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} ≠ ∞ := by
    intro y
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := -R) (b := R)).ne (measure_mono ?_)
    intro t ht
    have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Function.update y.ofLp j t) : Euclid d) j
    rw [WithLp.ofLp_toLp, Function.update_self, Real.norm_eq_abs] at h1
    exact abs_le.mp (h1.trans (mem_closedBall_zero_iff.mp (hR ht)))
  refine upperSemicontinuous_iff.mpr fun x => upperSemicontinuousAt_iff.mpr fun r hr => ?_
  -- outer regularity: an open `U` around the slice through `x` with `L¹(U) < r`
  obtain ⟨U, hxU, hUo, hUr⟩ := Set.exists_isOpen_lt_of_lt
    {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A} (ENNReal.ofReal r)
    ((ENNReal.lt_ofReal_iff_toReal_lt (hfin x)).mpr hr)
  -- the projection `z ↦ z[j ↦ 0]` and the compact part of `A` off `{z : z_j ∈ U}`
  let proj : Euclid d → Euclid d := fun z => WithLp.toLp 2 (Function.update z.ofLp j 0)
  have hproj : Continuous proj :=
    (PiLp.continuous_toLp 2 _).comp
      ((continuous_update j).comp ((PiLp.continuous_ofLp 2 _).prodMk continuous_const))
  have hC : IsCompact (A \ {z : Euclid d | z.ofLp j ∈ U}) :=
    hA.diff (hUo.preimage (PiLp.continuous_apply 2 _ j))
  -- `π x ∉ π(C)`: a point of `C` over `π x` would put its `j`-th coordinate in the slice at `x`
  have hx : proj x ∉ proj '' (A \ {z : Euclid d | z.ofLp j ∈ U}) := by
    rintro ⟨z, ⟨hzA, hzU⟩, hzx⟩
    have h : Function.update z.ofLp j 0 = Function.update x.ofLp j 0 := by
      simpa only [proj, WithLp.ofLp_toLp] using congrArg WithLp.ofLp hzx
    have hz : WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j)) = z := by
      calc WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j))
          = WithLp.toLp 2 (Function.update (Function.update x.ofLp j 0) j (z.ofLp j)) := by
            rw [Function.update_idem]
        _ = z := by rw [← h, Function.update_idem, Function.update_eq_self, WithLp.toLp_ofLp]
    exact hzU (hxU (show WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j)) ∈ A by
      rw [hz]; exact hzA))
  -- on the neighbourhood `π⁻¹(π(C)ᶜ)` of `x` every slice lies in `U`
  filter_upwards [((hC.image hproj).isClosed.isOpen_compl.preimage hproj).mem_nhds hx] with y hy
  have hy' : proj y ∉ proj '' (A \ {z : Euclid d | z.ofLp j ∈ U}) := hy
  have hyU : {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} ⊆ U := by
    intro t ht
    by_contra htU
    refine hy' ⟨WithLp.toLp 2 (Function.update y.ofLp j t), ⟨ht, ?_⟩, ?_⟩
    · show (WithLp.toLp 2 (Function.update y.ofLp j t)).ofLp j ∉ U
      rwa [WithLp.ofLp_toLp, Function.update_self]
    · simp only [proj, Function.update_idem]
  exact ENNReal.toReal_lt_of_lt_ofReal ((measure_mono hyU).trans_lt hUr)
/-- **Steiner symmetrization of a compact set is compact** (Simon Ch. 1, the Note after the proof
of 2.10: `S_j(A)` is compact because the slice length is upper semicontinuous).  Let `A ⊆ ℝ^d` be
compact, `A^j_y = {t : y[j ↦ t] ∈ A}` and `λ(y) = L¹(A^j_y)`.  If `λ` is upper semicontinuous,
then `S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ λ(y)/2}` is compact: `{y : A^j_y ≠ ∅} = π⁻¹(π(A))` for
`π z = z[j ↦ 0]`, `{y : |y_j| ≤ λ(y)/2}` is a superlevel set of the upper semicontinuous
`λ − 2|y_j|`, and `S_j(A) ⊆ closedBall(0, 3R)` whenever `A ⊆ closedBall(0, R)`. -/
theorem Submission.cbr_ci_iso_steiner_isCompact : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → UpperSemicontinuous (fun y : Euclid d => (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal) → IsCompact {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
  intro d j A hA hlen
  -- Step 1: `π z = z[j ↦ 0]` is continuous, and `π z = π y` forces `y[j ↦ z_j] = z`
  let π : Euclid d → Euclid d := fun z => WithLp.toLp 2 (Function.update z.ofLp j 0)
  have hπ : Continuous π :=
    (PiLp.continuous_toLp 2 _).comp ((PiLp.continuous_ofLp 2 _).update j continuous_const)
  have hπ_eq : ∀ y z : Euclid d, π z = π y →
      WithLp.toLp 2 (Function.update y.ofLp j (z j)) = z := by
    intro y z h
    ext i
    by_cases hi : i = j
    · subst hi
      simp
    · have := congrArg (fun w : Euclid d => w i) h
      simp only [π, Function.update_of_ne hi] at this ⊢
      exact this.symm
  -- Step 2: `{y : A^j_y ≠ ∅} = π⁻¹(π(A))` is closed, `π(A)` being compact
  have hN : IsClosed
      {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty} := by
    convert (hA.image hπ).isClosed.preimage hπ using 1
    ext y
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨_, ht, by simp [π]⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨z j, by rw [mem_ofPred_eq, hπ_eq y z h]; exact hz⟩
  -- Step 3: `{y : 0 ≤ λ(y) − 2|y_j|}` is closed, `λ − 2|y_j|` being upper semicontinuous
  have hM : IsClosed {y : Euclid d | 0 ≤
      (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal + -(2 * |y j|)} :=
    (hlen.add ((PiLp.continuous_apply 2 _ j).abs.const_mul 2).neg.upperSemicontinuous)
      |>.isClosed_preimage 0
  -- Step 4: `S_j(A)` is the intersection of these two closed sets
  have hS : IsClosed {y : Euclid d |
      {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧
        |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
    convert hN.inter hM using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr Iff.rfl ⟨fun h => by linarith, fun h => by linarith⟩
  -- Step 5: `S_j(A) ⊆ closedBall(0, 3R)` when `A ⊆ closedBall(0, R)`
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded hS
    ((isBounded_closedBall (x := (0 : Euclid d)) (r := 3 * R)).subset ?_)
  rintro y ⟨⟨t, ht⟩, hy⟩
  rw [mem_closedBall_zero_iff]
  -- every `s ∈ A^j_y` has `|s| ≤ ‖y[j ↦ s]‖ ≤ R`
  have hnorm : ∀ s : ℝ, WithLp.toLp 2 (Function.update y.ofLp j s) ∈ A → |s| ≤ R := by
    intro s hs
    have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Function.update y.ofLp j s)) j
    have h2 := mem_closedBall_zero_iff.1 (hR hs)
    simp only [Function.update_self, Real.norm_eq_abs] at h1
    linarith
  -- hence `A^j_y ⊆ [−R, R]` and `λ(y) ≤ 2R`
  have hR0 : 0 ≤ R := (abs_nonneg t).trans (hnorm t ht)
  have hvol : (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal ≤ 2 * R := by
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    calc volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}
        ≤ volume (Icc (-R) R) := measure_mono fun s hs => abs_le.1 (hnorm s hs)
      _ = ENNReal.ofReal (2 * R) := by rw [Real.volume_Icc]; ring_nf
  -- `y − y[j ↦ t] = (y_j − t) e_j`
  have hdiff : ‖y - WithLp.toLp 2 (Function.update y.ofLp j t)‖ = |y j - t| := by
    have : y - WithLp.toLp 2 (Function.update y.ofLp j t) = EuclideanSpace.single j (y j - t) := by
      ext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [hi]
    rw [this, PiLp.norm_single, Real.norm_eq_abs]
  have hz : ‖WithLp.toLp 2 (Function.update y.ofLp j t)‖ ≤ R := mem_closedBall_zero_iff.1 (hR ht)
  -- Step 6: `‖y‖ ≤ ‖y[j ↦ t]‖ + |y_j − t| ≤ R + |y_j| + |t| ≤ 3R`, using `|y_j| ≤ λ(y)/2 ≤ R`
  calc ‖y‖ = ‖WithLp.toLp 2 (Function.update y.ofLp j t) +
        (y - WithLp.toLp 2 (Function.update y.ofLp j t))‖ := by rw [add_sub_cancel]
    _ ≤ ‖WithLp.toLp 2 (Function.update y.ofLp j t)‖ +
        ‖y - WithLp.toLp 2 (Function.update y.ofLp j t)‖ := norm_add_le _ _
    _ ≤ R + (|y j| + |t|) := by
        rw [hdiff]
        gcongr
        exact abs_sub _ _
    _ ≤ 3 * R := by linarith [hnorm t ht]
/-- **Cavalieri's principle along a coordinate direction** (Simon Ch. 1, proof of 2.10: Steiner
symmetrization keeps Lebesgue measure "by Fubini").  If measurable `S, A ⊆ ℝᵈ` have line slices
`{t : y[j↦t] ∈ S}`, `{t : y[j↦t] ∈ A}` of equal `L¹`-measure through every `y`, then
`Lᵈ(S) = Lᵈ(A)`.  With `d = n + 1`, `φ(t, z) = Fin.insertNth j t z` is measure preserving from
`L¹ ⊗ Lⁿ` to `Lᵈ`; its fibre over `z` is the slice through `φ(0, z)`, and Tonelli
(`Measure.prod_apply_symm`) integrates the equal slice measures over `z`. -/
theorem Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq : ∀ (d : ℕ) (j : Fin d) (S A : Set (Euclid d)), MeasurableSet S → MeasurableSet A → (∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ S} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}) → volume S = volume A := by
  intro d j S A hS hA hslice
  cases d with
  | zero => exact Fin.elim0 j
  | succ n =>
    -- `φ(t, z) = Fin.insertNth j t z`, measure preserving from `L¹ ⊗ Lⁿ` to `Lᵈ`
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    let φ : ℝ × (Fin n → ℝ) → Euclid (n + 1) := fun p => WithLp.toLp 2 (e.symm p)
    have hφ : MeasurePreserving φ volume volume :=
      (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
        (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
    -- the fibre of `φ` over `z` is the coordinate slice through `φ(0, z)`
    have hfibre (B : Set (Euclid (n + 1))) (z : Fin n → ℝ) :
        (fun t => φ (t, z)) ⁻¹' B =
          {t : ℝ | WithLp.toLp 2 (Function.update (φ (0, z)).ofLp j t) ∈ B} := by
      ext t
      change WithLp.toLp 2 (j.insertNth t z) ∈ B ↔
        WithLp.toLp 2 (Function.update (j.insertNth 0 z) j t) ∈ B
      rw [Fin.update_insertNth]
    -- Tonelli: `Lᵈ(B) = (L¹ ⊗ Lⁿ)(φ⁻¹ B) = ∫⁻ z, L¹(fibre of φ⁻¹ B over z)`
    have hvol (B : Set (Euclid (n + 1))) (hB : MeasurableSet B) :
        volume B = ∫⁻ z : Fin n → ℝ, volume ((fun t => φ (t, z)) ⁻¹' B) :=
      (hφ.measure_preimage hB.nullMeasurableSet).symm.trans
        (Measure.prod_apply_symm (hB.preimage hφ.measurable))
    rw [hvol S hS, hvol A hA]
    refine lintegral_congr fun z => ?_
    rw [hfibre S z, hfibre A z]
    exact hslice (φ (0, z))
/-- Steiner symmetrization in direction `j` keeps the length of every line slice: for compact
`A ⊆ ℝᵈ` and `y ∈ ℝᵈ`, `L¹{t | y[j↦t] ∈ S_j(A)} = L¹(B)` with `B = {t | y[j↦t] ∈ A}`.  Each
point `y[j↦t]` of the line has `j`-th coordinate `t` and slice `B`, so the left set is
`{t | B ≠ ∅ ∧ |t| ≤ ℓ/2}`, `ℓ = L¹(B)`.  It is empty if `B = ∅` and `[-ℓ/2, ℓ/2]` otherwise, of
length `ℓ`, which is finite because `B` lies in the compact projection `π_j(A)`. -/
theorem Submission.cbr_ci_iso_svol_steiner_slice_volume_eq : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → ∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ {x : Euclid d | {s : ℝ | WithLp.toLp 2 (Function.update x.ofLp j s) ∈ A}.Nonempty ∧ |x j| ≤ (volume {s : ℝ | WithLp.toLp 2 (Function.update x.ofLp j s) ∈ A}).toReal / 2}} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} := by
  intro d j A hA y
  -- `B = A^j_y = {s | y[j↦s] ∈ A}`
  obtain ⟨B, hB⟩ : ∃ B : Set ℝ, {s : ℝ | WithLp.toLp 2 (update y.ofLp j s) ∈ A} = B :=
    ⟨_, rfl⟩
  -- steps 1–2: `(y[j↦t])_j = t` and `(y[j↦t])[j↦s] = y[j↦s]` (`WithLp.ofLp_toLp` is `rfl`), so
  -- `A^j_{y[j↦t]} = B` and the left set is `{t | B ≠ ∅ ∧ |t| ≤ ℓ/2}`, `ℓ = (L¹ B).toReal`
  simp only [mem_ofPred_eq, update_idem, update_self, hB]
  -- step 3: `B ⊆ π_j(A)`, which is compact, so `L¹(B) < ∞`
  have hBfin : volume B ≠ ∞ := by
    have hπ : IsCompact ((fun x : Euclid d => x j) '' A) := hA.image (PiLp.continuous_apply 2 _ j)
    refine (measure_lt_top_of_subset ?_ hπ.measure_lt_top.ne).ne
    rintro s hs
    rw [← hB] at hs
    exact ⟨_, hs, update_self j s y.ofLp⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  -- step 4: if `B = ∅`, the left set is empty
  · simp only [Set.not_nonempty_empty, false_and, ofPred_false]
  -- step 5: otherwise it is `[-ℓ/2, ℓ/2]`, of measure `ofReal ℓ = L¹(B)`
  · have hIcc : {t : ℝ | B.Nonempty ∧ |t| ≤ (volume B).toReal / 2} =
        Icc (-((volume B).toReal / 2)) ((volume B).toReal / 2) := by
      ext t
      rw [mem_ofPred_eq, mem_Icc, ← abs_le, and_iff_right hBne]
    rw [hIcc, Real.volume_Icc, sub_neg_eq_add, add_halves, ENNReal.ofReal_toReal hBfin]
/-- **Symmetric replacement** (Simon, Ch. 1, proof of 2.10): applying the coordinate Steiner
symmetrizations `S_i(B) = {y : B^i_y ≠ ∅, |y_i| ≤ L¹(B^i_y)/2}`, `B^i_y = {t : y[i↦t] ∈ B}`, for
`i = 1, …, d` to a compact `A ⊆ ℝᵈ` gives a compact `K` with `Lᵈ(K) = Lᵈ(A)`, `ediam K ≤ ediam A`
and `-K = K`.  Each `S_i` keeps compactness, Lebesgue measure (equal slice lengths and Cavalieri)
and the diameter bound, makes the set invariant under `R_i(y) = y[i↦-y_i]` and keeps the earlier
`R_k`-invariances; flipping the coordinates of `x ∈ K` one at a time then gives `-x ∈ K`. -/
theorem Submission.dmcbr_ci_iso_exists_symmetric_replacement : ∀ (d : ℕ) (A : Set (Euclid d)), IsCompact A → ∃ K : Set (Euclid d), IsCompact K ∧ volume K = volume A ∧ ediam K ≤ ediam A ∧ ∀ x ∈ K, -x ∈ K := by
  intro d A hA
  -- Step 0: for compact `B`, `S_i(B)` is compact (the slice length is upper semicontinuous) and
  -- `Lᵈ(S_i(B)) = Lᵈ(B)` (equal slice lengths and Cavalieri's principle)
  have hstep : ∀ (i : Fin d) (B : Set (Euclid d)), IsCompact B →
      IsCompact {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp i t) ∈ B}.Nonempty ∧
        |y i| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp i t) ∈ B}).toReal / 2} ∧
      volume {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp i t) ∈ B}.Nonempty ∧
        |y i| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp i t) ∈ B}).toReal / 2} =
        volume B := by
    intro i B hB
    have hS := Submission.cbr_ci_iso_steiner_isCompact d i B hB
      (Submission.cbr_ci_iso_slice_length_usc d i B hB)
    exact ⟨hS, Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq d i _ B hS.measurableSet
      hB.measurableSet (Submission.cbr_ci_iso_svol_steiner_slice_volume_eq d i B hB)⟩
  -- Steps 1–3: for every finite set `F` of coordinates there is a compact `K_F` with
  -- `Lᵈ(K_F) = Lᵈ(A)`, `ediam K_F ≤ ediam A` and `R_k(K_F) ⊆ K_F` for `k ∈ F`
  have hclaim : ∀ F : Finset (Fin d), ∃ K : Set (Euclid d), IsCompact K ∧ volume K = volume A ∧
      ediam K ≤ ediam A ∧
      ∀ k ∈ F, ∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp k (-x k)) ∈ K := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨A, hA, rfl, le_rfl, by simp⟩
    | insert i F hi ih =>
      -- `K_{insert i F} = S_i(K_F)`
      obtain ⟨K, hK, hvol, hdiam, hsym⟩ := ih
      obtain ⟨hSc, hSv⟩ := hstep i K hK
      refine ⟨_, hSc, hSv.trans hvol, (Submission.cbr_ci_iso_steiner_ediam_le d i K hK).trans hdiam,
        fun k hk x hx => ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (Submission.cbr_ci_iso_steiner_reflection d k K).1 x hx
      · exact (Submission.cbr_ci_iso_steiner_reflection d i K).2 k (fun h => hi (h ▸ hk))
          (hsym k hk) x hx
  -- Step 4: `K = K_univ` is invariant under every `R_i`
  obtain ⟨K, hK, hvol, hdiam, hsym⟩ := hclaim Finset.univ
  refine ⟨K, hK, hvol, hdiam, fun x hx => ?_⟩
  -- Step 5: `x^G ∈ K` for every `G`, where `x^G` negates the coordinates in `G`, since
  -- `x^{insert i G} = R_i(x^G)` for `i ∉ G`; and `x^univ = -x`
  have hflip : ∀ G : Finset (Fin d),
      (WithLp.toLp 2 (fun k => if k ∈ G then -x k else x k) : Euclid d) ∈ K := by
    intro G
    induction G using Finset.induction_on with
    | empty => simpa using hx
    | insert i G hi ih =>
      convert hsym i (Finset.mem_univ i) _ ih using 1
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hi]
      · simp [hk]
  convert hflip Finset.univ using 1
  ext k
  simp

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
