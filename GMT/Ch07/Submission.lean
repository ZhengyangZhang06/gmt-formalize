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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
