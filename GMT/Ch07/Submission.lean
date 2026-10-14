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
/-- **A unit covector attaining `1` on an orthonormal frame** (Simon (6.1.1); step 1(b) of the
mass formula, Remark 6.3.2(3)): every orthonormal `τ₁, …, τₙ` in `ℝᴾ` admits an `n`-covector `β`
with `|β|_E = 1` and `β(τ) = 1`.  Take the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors
`⟨τᵢ, ·⟩`, so `β(τ) = det 1 = 1`.  Extend `τ` to an orthonormal basis `f` of `ℝᴾ` with
`f ∘ ι = τ`, `ι = Fin.castLE`.  Then `β(f ∘ j) = sgn π` if `j = ι ∘ π` for a permutation `π`,
and `β(f ∘ j) = 0` otherwise (a zero column, or a repeated vector), so `Σ_j β(f ∘ j)² = n!`;
`regcomp_covector_sq_sum_orthonormalBasis` turns this into `n! = n! |β|_E²`. -/
theorem Submission.regcomp_exists_covector_eval_orthonormal_eq_one : ∀ (P n : ℕ) (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β = 1 ∧ β τ = 1 := by
  intro P n τ hτ
  classical
  -- Step 1: the wedge `β(v) = det(⟨τᵢ, v_k⟩)` of the covectors `⟨τᵢ, ·⟩` (Simon (6.1.1))
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) n, ∀ v : Fin n → Euclid P,
      β v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun i => (innerSL ℝ (τ i) : Euclid P →L[ℝ] ℝ).toLinearMap
    let g : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hg : ∀ v, g v = Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      intro v
      rw [← Matrix.det_transpose]
      show Matrix.det (Matrix.of fun a b => L (v a) b) = _
      congr 1
    have hcont : Continuous fun v : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro i k
      exact Continuous.inner (f := fun _ => τ i) (g := fun v : Fin n → Euclid P => v k)
        continuous_const (continuous_apply k)
    refine ⟨{ g with cont := ?_ }, hg⟩
    have : (g : (Fin n → Euclid P) → ℝ) =
        fun v => Matrix.det (Matrix.of fun i k => inner ℝ (τ i) (v k)) := funext hg
    simpa [this] using hcont
  -- Step 2: by orthonormality `(⟨τᵢ, τ_k⟩) = 1`, so `β(τ) = det 1 = 1`
  have hβτ : β τ = 1 := by
    have hone : (Matrix.of fun i k => inner ℝ (τ i) (τ k) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext i k
      rw [Matrix.of_apply, Matrix.one_apply]
      exact orthonormal_iff_ite.mp hτ i k
    rw [hβ, hone, Matrix.det_one]
  -- Step 3: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
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
  -- Step 4: `β(f ∘ j)² = 1` if `j = ι ∘ π` for a permutation `π`, and `0` otherwise
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), β (fun k => f (Φ π k)) ^ 2 = 1 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : β (τ ∘ π) = Equiv.Perm.sign π • β τ := β.toAlternatingMap.map_perm τ π
    rw [h1, h2, hβτ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hzero : ∀ j : Fin n → Fin P, j ∉ Finset.univ.image Φ → β (fun k => f (j k)) ^ 2 = 0 := by
    intro j hj
    have hj' : ∀ π, Φ π ≠ j := fun π hπ => hj (Finset.mem_image.mpr ⟨π, Finset.mem_univ _, hπ⟩)
    rw [sq_eq_zero_iff]
    by_cases hr : ∀ k, j k ∈ range ι
    · -- `j = ι ∘ ρ` with `ρ` not a permutation, hence not injective: `f ∘ j` repeats a vector
      choose ρ hρ using hr
      have hρ' : ¬ Injective ρ := fun hinj =>
        hj' (Equiv.ofBijective ρ (Finite.injective_iff_bijective.mp hinj)) (funext hρ)
      refine β.map_eq_zero_of_not_injective _ fun hinj => hρ' fun a b hab => hinj ?_
      exact congrArg f ((hρ a).symm.trans ((congrArg ι hab).trans (hρ b)))
    · -- some `j k₀ ∉ range ι`: column `k₀` of `(⟨τᵢ, f (j k)⟩)` vanishes
      obtain ⟨k₀, hk₀⟩ := not_forall.mp hr
      rw [hβ]
      refine Matrix.det_eq_zero_of_column_eq_zero k₀ fun i => ?_
      rw [Matrix.of_apply, ← hfι i, f.inner_eq_ite, ite_eq_right fun h => hk₀ ⟨i, h⟩]
  have hsum : ∑ j : Fin n → Fin P, β (fun k => f (j k)) ^ 2 = n.factorial := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) fun j _ hj => hzero j hj,
      Finset.sum_image fun π _ π' _ h => hΦ h]
    simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- Step 5: `n! = n! |β|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`, so `|β|_E = 1`
  have hsq := Submission.regcomp_covector_sq_sum_orthonormalBasis P n β f
  rw [hsum] at hsq
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  refine ⟨β, (pow_eq_one_iff_of_nonneg (covectorEuclideanNorm_nonneg β) two_ne_zero).mp ?_, hβτ⟩
  exact mul_left_cancel₀ hfac (by rw [← hsq, mul_one])
/-- `Hⁿ(Q ∩ B_ρ(y)) = ωₙρⁿ` for an `n`-dimensional linear subspace `Q` of `ℝᴾ`, `y ∈ Q` and
`ρ > 0` (used in the proof of Simon 7.3.3(1), p. 191, for the density of the planes of a
2-dimensional minimizing cone).  The inclusion `Q → ℝᴾ` is an isometry, so `Q ∩ B_ρ(y)` has the
measure of the ball `B_ρ(y)` of `Q`; on `Q`, `μHE[n]` is the volume, Haar scaling gives
`vol(B_ρ(y)) = ρⁿ vol(B_1(0))`, and orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume, so
`vol(B_1(0)) = ωₙ`. -/
theorem Submission.idtp_tdc_subspace_ball_measure : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (y : Euclid P) (ρ : ℝ), Module.finrank ℝ Q = n → y ∈ Q → 0 < ρ → μHE[n] ((Q : Set (Euclid P)) ∩ ball y ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) := by
  intro P n Q y ρ hn hy hρ
  subst hn
  -- the inclusion `Q → ℝᴾ` is an isometry with range `Q`; `B_ρ(y)` pulls back to the ball of `Q`
  have hball : μHE[Module.finrank ℝ Q] ((Q : Set (Euclid P)) ∩ ball y ρ) =
      μHE[Module.finrank ℝ Q] (ball (⟨y, hy⟩ : Q) ρ) := by
    rw [← isometry_subtype_coe.preimage_ball (⟨y, hy⟩ : Q) ρ,
      isometry_subtype_coe.euclideanHausdorffMeasure_preimage, Subtype.range_coe, Set.inter_comm]
  -- orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume and map `B_1(0)` onto `B_1(0)`
  have hunit := (stdOrthonormalBasis ℝ Q).measurePreserving_repr.measure_preimage
    (measurableSet_ball (x := (0 : Euclid (Module.finrank ℝ Q))) (ε := 1)).nullMeasurableSet
  rw [LinearIsometryEquiv.preimage_ball, map_zero] at hunit
  -- `μHE[n] = volume` on `Q`, then Haar scaling of balls
  rw [hball, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, hunit, mul_comm]
  rfl
/-- **Exterior derivative of a function times a constant covector** (used for the boundary weak
derivatives in the graph-cycle regularity step of Simon 7.4.3).  If `a : ℝᴾ → ℝ` is
differentiable at `x` and `β` is a fixed `m`-covector, then
`d(a β)(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ Da(x)wᵢ · β(w₀, …, ŵᵢ, …, w_m)`, i.e. `d(a β) = da ∧ β`:
each term of the alternating sum differentiates `y ↦ a(y) β(w₀, …, ŵᵢ, …, w_m)`. -/
theorem Submission.dgcr_bwd_extDeriv_smul_const : ∀ (P m : ℕ) (a : Euclid P → ℝ) (β : Covector (Euclid P) m) (x : Euclid P) (w : Fin (m + 1) → Euclid P), DifferentiableAt ℝ a x → exteriorDerivative (fun y => a y • β) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ a x (w i) * β (i.removeNth w)) := by
  intro P m a β x w ha
  rw [exteriorDerivative_apply (ha.smul_const β) w]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 : (fun y => (a y • β) (i.removeNth w)) = fun y => a y * β (i.removeNth w) := by
    funext y
    simp [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [h1, fderiv_mul_const ha]
  simp [zsmul_eq_mul, mul_comm]
/-- **Translation invariance on smooth tests** (steps 1–3 of the translation argument): if `ν` is
finite on compact sets and `∫ Dφ(y)[v] dν(y) = 0` for every `φ ∈ C_c^∞(ℝᴾ)`, then
`∫ φ(v + y) dν(y) = ∫ φ dν` for every `φ ∈ C_c^∞(ℝᴾ)`.  `F(s) = ∫ φ(y + sv) dν(y)` is
differentiable with `F'(s₀) = ∫ Dφ(y + s₀v)[v] dν(y)` (differentiation under the integral sign;
for `|s − s₀| < 1` the derivative is dominated by `C‖v‖ 1_{K₀}`, `K₀ = B̄_{R + (|s₀| + 1)‖v‖}(0)`,
`tsupport φ ⊆ B̄_R(0)`, `‖Dφ‖ ≤ C`), and `F'(s₀) = 0` by the hypothesis applied to the translate
`φ(· + s₀v)`.  So `F` is constant and `F(1) = F(0)`. -/
theorem Submission.cbr_ci_cp_tr_smooth_translate_integral_eq : ∀ (P : ℕ) (ν : Measure (Euclid P)) (v : Euclid P), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) → ∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, φ (v + y) ∂ν = ∫ y, φ y ∂ν := by
  intro P ν v hν hD φ hφ hφs
  -- step 1: `ν` is finite on compact sets
  have hνK : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν K hK⟩
  -- step 2: `Dφ` is continuous, vanishes off `tsupport φ` and is bounded by `C`;
  -- `tsupport φ ⊆ B̄_R(0)`
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hφc.bounded_above_of_compact_support (hφs.fderiv ℝ)
  obtain ⟨R, hR⟩ := hφs.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  -- step 5: `F(s) = ∫ φ(y + s v) dν` has derivative `∫ Dφ(y + s v)[v] dν` at every `s₀`
  have hF : ∀ s₀ : ℝ, HasDerivAt (fun s : ℝ => ∫ y, φ (y + s • v) ∂ν)
      (∫ y, fderiv ℝ φ (y + s₀ • v) v ∂ν) s₀ := by
    intro s₀
    have hK₀ : IsCompact (closedBall (0 : Euclid P) (R + (|s₀| + 1) * ‖v‖)) :=
      isCompact_closedBall _ _
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun (s : ℝ) (y : Euclid P) => φ (y + s • v))
      (F' := fun (s : ℝ) (y : Euclid P) => fderiv ℝ φ (y + s • v) v)
      (bound := (closedBall (0 : Euclid P) (R + (|s₀| + 1) * ‖v‖)).indicator fun _ => C * ‖v‖)
      (ball_mem_nhds s₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
    · -- (a) `y ↦ φ(y + s v)` is continuous
      exact Eventually.of_forall fun s =>
        (hφ.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · -- (b) `y ↦ φ(y + s₀ v)` is continuous with compact support
      exact (hφ.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        (hφs.comp_homeomorph (Homeomorph.addRight (s₀ • v)))
    · -- (c) `y ↦ Dφ(y + s₀ v)[v]` is continuous
      exact ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        (hφc.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    · -- (d) the domination `|Dφ(y + s v)[v]| ≤ C ‖v‖ 1_{K₀}(y)` for `|s - s₀| < 1`
      refine Eventually.of_forall fun y s hs => ?_
      by_cases hy : y ∈ closedBall (0 : Euclid P) (R + (|s₀| + 1) * ‖v‖)
      · rw [indicator_of_mem hy]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        -- step 4: `y ∉ K₀` forces `y + s v ∉ tsupport φ`
        have hys : y + s • v ∉ tsupport φ := by
          intro h
          apply hy
          have h1 := hR h
          rw [mem_closedBall_zero_iff] at h1 ⊢
          rw [mem_ball, Real.dist_eq] at hs
          have hs' : |s| ≤ |s₀| + 1 := by
            linarith [abs_sub_abs_le_abs_sub s s₀]
          calc ‖y‖ = ‖(y + s • v) - s • v‖ := by rw [add_sub_cancel_right]
            _ ≤ ‖y + s • v‖ + ‖s • v‖ := norm_sub_le _ _
            _ = ‖y + s • v‖ + |s| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ R + (|s₀| + 1) * ‖v‖ :=
              add_le_add h1 (mul_le_mul_of_nonneg_right hs' (norm_nonneg _))
        rw [fderiv_of_notMem_tsupport ℝ hys]
        simp
    · -- (e) `C ‖v‖ 1_{K₀}` is integrable since `ν(K₀) < ∞`
      exact IntegrableOn.integrable_indicator (integrableOn_const hK₀.measure_lt_top.ne)
        measurableSet_closedBall
    · -- (f) chain rule for `s ↦ φ(y + s v)`
      refine Eventually.of_forall fun y s _ => ?_
      have h1 : HasDerivAt (fun s : ℝ => y + s • v) v s := by
        simpa using ((hasDerivAt_id s).smul_const v).const_add y
      exact (hφd (y + s • v)).hasFDerivAt.comp_hasDerivAt s h1
  -- step 6: `F' ≡ 0`, by the hypothesis applied to the translate `φ(· + s₀ v)`
  have hF0 : ∀ s₀ : ℝ, ∫ y, fderiv ℝ φ (y + s₀ • v) v ∂ν = 0 := by
    intro s₀
    have h := hD (fun y => φ (y + s₀ • v)) (hφ.comp (contDiff_id.add contDiff_const))
      (hφs.comp_homeomorph (Homeomorph.addRight (s₀ • v)))
    simpa only [fderiv_comp_add_right] using h
  -- step 7: `F` is constant, so `F(1) = F(0)`
  have h := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => by rw [(hF s).deriv, hF0 s]) 1 0
  simpa [add_comm] using h
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset

/-- **Smooth approximation of `g ∈ C_c(ℝᴾ)`** (steps 4–5 of the translation-invariance proof):
mollify, `u_k = ρ_k ⋆ g` with `ρ_k` the normalized mollifier of radius `1/(k+1)`.  Each `u_k` is
`C^∞` (smooth compactly supported kernel against a locally integrable `g`), vanishes off
`K = B̄_{R₀+1}(0)` where `tsupport g ⊆ B̄_{R₀}(0)`, and the averaging estimate
`dist_convolution_le` gives `|u_k| ≤ M = sup ‖g‖` and, by continuity of `g`, `u_k(x) → g(x)`. -/
theorem Submission.cbr_ci_cp_tr_smooth_approx_of_continuous : ∀ (P : ℕ) (g : Euclid P → ℝ), Continuous g → HasCompactSupport g → ∃ (K : Set (Euclid P)) (C : ℝ) (u : ℕ → Euclid P → ℝ), IsCompact K ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (u k)) ∧ (∀ k x, x ∉ K → u k x = 0) ∧ (∀ k x, |u k x| ≤ C) ∧ ∀ x, Tendsto (fun k => u k x) atTop (𝓝 (g x)) := by
  intro P g hg hgc
  -- mollifiers `ρ k ≥ 0`, `∫ ρ k = 1`, supported in `B_{1/(k+1)}(0)`
  choose ρ hρs hρc hρn hρi hρb using fun k : ℕ =>
    Submission.dgcr_stc_exists_normalized_mollifier P (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  -- `tsupport g ⊆ B̄_{R₀}(0)` and `‖g‖ ≤ M`
  obtain ⟨R₀, hR₀⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hgm : AEStronglyMeasurable g volume := hg.aestronglyMeasurable
  refine ⟨closedBall 0 (R₀ + 1), M,
    fun k => convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
    isCompact_closedBall 0 (R₀ + 1),
    fun k => (hρc k).contDiff_convolution_left _ (hρs k) hg.locallyIntegrable, ?_, ?_, ?_⟩
  · -- vanishing off `K = B̄_{R₀+1}(0)`
    intro k x hx
    show convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0
    rw [convolution_def]
    have h0 : ∀ t, ContinuousLinearMap.lsmul ℝ ℝ (ρ k t) (g (x - t)) = 0 := by
      intro t
      by_cases ht : ρ k t = 0
      · simp [ht]
      · have ht' : ‖t‖ < 1 / ((k : ℝ) + 1) := mem_ball_zero_iff.1 (hρb k ht)
        have hk : 1 / ((k : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        have hxt : x - t ∉ tsupport g := by
          intro hmem
          have h1 : ‖x - t‖ ≤ R₀ := mem_closedBall_zero_iff.1 (hR₀ hmem)
          apply hx
          rw [mem_closedBall_zero_iff]
          calc ‖x‖ = ‖(x - t) + t‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - t‖ + ‖t‖ := norm_add_le _ _
            _ ≤ R₀ + 1 := by linarith
        simp [image_eq_zero_of_notMem_tsupport hxt]
    simp only [h0, integral_zero]
  · -- uniform bound `|u k| ≤ M`
    intro k x
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : ℝ))
      ((norm_nonneg _).trans (hM 0)) (hρb k) (hρn k) (hρi k) hgm
      (fun y _ => by rw [dist_zero_right]; exact hM y)
    rw [Real.dist_eq, sub_zero] at h
    exact h
  · -- pointwise convergence `u k x → g x`
    intro x
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hgδ⟩ := Metric.continuous_iff.1 hg x (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun k hk => ?_⟩
    have hkN : 1 / ((k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := Nat.one_div_le_one_div hk
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (half_pos hε).le (hρb k) (hρn k) (hρi k) hgm
      (fun y hy => (hgδ y ((mem_ball.1 hy).trans_le hkN |>.trans hN)).le)
    exact h.trans_lt (half_lt_self hε)

/-- **Smooth test functions determine measures finite on compacts** (steps 6–7 of the
translation-invariance argument): if `μ, ν` on `ℝᴾ` are finite on compact sets and
`∫ φ dμ = ∫ φ dν` for every `C^∞` `φ` with compact support, then `μ = ν`.  Both measures are
locally finite, hence regular on the `σ`-compact metric space `ℝᴾ`, so by Riesz uniqueness it
suffices to compare `∫ f` for `f ∈ C_c(ℝᴾ, ℝ)`.  Approximate `f` by `C^∞` functions `uₖ`
vanishing off a compact `K`, with `|uₖ| ≤ C` and `uₖ → f` pointwise
(`cbr_ci_cp_tr_smooth_approx_of_continuous`): then `∫ uₖ dμ = ∫ uₖ dν`, and dominated
convergence with the bound `C·1_K` gives `∫ uₖ dμ → ∫ f dμ` and `∫ uₖ dν → ∫ f dν`. -/
theorem Submission.cbr_ci_cp_tr_measure_eq_of_smooth_integral_eq : ∀ (P : ℕ) (μ ν : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, φ y ∂μ = ∫ y, φ y ∂ν) → μ = ν := by
  intro P μ ν hμ hν hφ
  -- step 1: `μ, ν` are finite on compacts, hence locally finite and regular on `ℝᴾ`
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ K hK⟩
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν K hK⟩
  -- step 2: by Riesz uniqueness it suffices to compare `∫ f` for `f ∈ C_c(ℝᴾ, ℝ)`
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  -- step 3: `C^∞` approximants `uₖ → f`, vanishing off a compact `K`, with `|uₖ| ≤ C`
  obtain ⟨K, C, u, hK, hu, huK, huC, hlim⟩ :=
    Submission.cbr_ci_cp_tr_smooth_approx_of_continuous P f f.continuous f.hasCompactSupport
  -- step 5: dominated convergence with the bound `C·1_K`, for `m = μ` and `m = ν`
  have hdom : ∀ m : Measure (Euclid P), m K < ∞ →
      Tendsto (fun k => ∫ x, u k x ∂m) atTop (𝓝 (∫ x, f x ∂m)) := fun m hm =>
    tendsto_integral_of_dominated_convergence (K.indicator fun _ => C)
      (fun k => (hu k).continuous.aestronglyMeasurable)
      ((integrableOn_const hm.ne).integrable_indicator hK.measurableSet)
      (fun k => Eventually.of_forall fun x => by
        by_cases hx : x ∈ K
        · rw [indicator_of_mem hx, Real.norm_eq_abs]
          exact huC k x
        · rw [indicator_of_notMem hx, huK k x hx, norm_zero])
      (Eventually.of_forall hlim)
  -- step 4: each `uₖ` is a `C^∞` test function, so `∫ uₖ dμ = ∫ uₖ dν`
  have heq : (fun k => ∫ x, u k x ∂μ) = fun k => ∫ x, u k x ∂ν :=
    funext fun k => hφ (u k) (hu k) (HasCompactSupport.intro hK (huK k))
  -- step 6: limits in `ℝ` are unique
  have hlimμ := hdom μ (hμ K hK)
  rw [heq] at hlimμ
  exact tendsto_nhds_unique hlimμ (hdom ν (hν K hK))

/-- **Translation invariance from vanishing directional derivatives** (step 2 of the
constant-planes argument): if `ν` on `ℝᴾ` is finite on compact sets and `∫ Dφ(y)[v] dν(y) = 0`
for every `C^∞` `φ` with compact support, then `ν(τ⁻¹A) = ν(A)` for every Borel `A`, where
`τ(x) = v + x`.  `τ` is a homeomorphism, so `τ_#ν` is finite on compact sets
(`τ_#ν(K) = ν(τ⁻¹K)`, `τ⁻¹K = K − v` compact) and `∫ φ d(τ_#ν) = ∫ φ(v + y) dν(y)`, which is
`∫ φ dν` for `φ ∈ C_c^∞(ℝᴾ)` (`cbr_ci_cp_tr_smooth_translate_integral_eq`).  Hence `τ_#ν = ν`
(`cbr_ci_cp_tr_measure_eq_of_smooth_integral_eq`), and `ν(τ⁻¹A) = τ_#ν(A) = ν(A)`. -/
theorem Submission.cbr_ci_cp_translation_invariant_of_fderiv : ∀ (P : ℕ) (ν : Measure (Euclid P)) (v : Euclid P), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) → ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => v + x) ⁻¹' A) = ν A := by
  intro P ν v hν hD A hA
  -- `τ(x) = v + x` is a homeomorphism of `ℝᴾ`, hence a measurable embedding
  have hτ : MeasurableEmbedding (fun x : Euclid P => v + x) :=
    (Homeomorph.addLeft v).measurableEmbedding
  -- steps 4–7: `τ_#ν = ν`, both being finite on compacts with equal `C_c^∞` integrals
  have hμ : Measure.map (fun x : Euclid P => v + x) ν = ν := by
    refine Submission.cbr_ci_cp_tr_measure_eq_of_smooth_integral_eq P
      (Measure.map (fun x : Euclid P => v + x) ν) ν (fun K hK => ?_) hν (fun φ hφ hφs => ?_)
    · -- `τ_#ν(K) = ν(τ⁻¹K) < ∞`, `τ⁻¹K = K − v` being compact
      rw [hτ.map_apply]
      exact hν _ ((Homeomorph.addLeft v).isCompact_preimage.2 hK)
    · -- steps 1–3: `∫ φ d(τ_#ν) = ∫ φ(v + y) dν(y) = ∫ φ dν` for `φ ∈ C_c^∞(ℝᴾ)`
      rw [hτ.integral_map]
      exact Submission.cbr_ci_cp_tr_smooth_translate_integral_eq P ν v hν hD φ hφ hφs
  -- step 8: `ν(τ⁻¹A) = τ_#ν(A) = ν(A)` for Borel `A`
  rw [← Measure.map_apply hτ.measurable hA, hμ]

/-- **Riesz vector of the wedge functional `w ↦ ζ₀(w♭ ∧ α)`** (used in the constant tangent plane
step of the compactness theorem, Simon 7.2.4).  For `ζ₀ ∈ Λ_{d+1}(ℝᴾ)` and a fixed `d`-covector
`α` there is `v ∈ ℝᴾ` with `ζ₀(γ) = ⟨v, w⟩` whenever `γ = w♭ ∧ α`, i.e.
`γ(u₀, …, u_d) = Σᵢ (−1)ⁱ ⟨w, uᵢ⟩ α(u₀, …, ûᵢ, …, u_d)`: such a `γ` is `d(⟨w, ·⟩ α)(0)`, which
is linear in `w`, and `v` is the Riesz representative of `w ↦ ζ₀(w♭ ∧ α)`. -/
theorem Submission.cbr_ci_cp_dir_wedge_riesz_vector : ∀ (P d : ℕ) (ζ₀ : MultiVector P (d + 1)) (α : Covector (Euclid P) d), ∃ v : Euclid P, ∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = inner ℝ v w := by
  intro P d ζ₀ α
  set W : Euclid P → Covector (Euclid P) (d + 1) :=
    fun w => exteriorDerivative (fun y => inner ℝ w y • α) 0 with hW
  have hWf : ∀ (w : Euclid P) (u : Fin (d + 1) → Euclid P), W w u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u)) := by
    intro w u
    have hd : DifferentiableAt ℝ (fun y => inner ℝ w y) (0 : Euclid P) :=
      (innerSL ℝ w).differentiableAt
    rw [hW, Submission.dgcr_bwd_extDeriv_smul_const P d (fun y => inner ℝ w y) α 0 u hd]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hf : fderiv ℝ (fun y => inner ℝ w y) (0 : Euclid P) = innerSL ℝ w :=
      (innerSL ℝ w).fderiv
    rw [hf, innerSL_apply_apply]
  have huniq : ∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → γ = W w := by
    intro w γ hγ
    ext u
    rw [hγ u, hWf w u]
  have hadd : ∀ w w' : Euclid P, W (w + w') = W w + W w' := by
    intro w w'
    ext u
    rw [ContinuousAlternatingMap.add_apply, hWf, hWf, hWf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_add_left]
    ring
  have hsmul : ∀ (c : ℝ) (w : Euclid P), W (c • w) = c • W w := by
    intro c w
    ext u
    rw [ContinuousAlternatingMap.smul_apply, hWf, hWf, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_left]
    ring
  let ℓ : Euclid P →ₗ[ℝ] ℝ :=
    { toFun := fun w => ζ₀ (W w)
      map_add' := by
        intro w w'
        simp only [hadd, map_add]
      map_smul' := by
        intro c w
        simp only [hsmul, map_smul, smul_eq_mul, RingHom.id_apply] }
  refine ⟨(InnerProductSpace.toDual ℝ (Euclid P)).symm (LinearMap.toContinuousLinearMap ℓ), ?_⟩
  intro w γ hγ
  rw [InnerProductSpace.toDual_symm_apply, huniq w γ hγ]
  rfl
/-- **Vanishing of `∫ Dφ[v] dν` on a set of directions extends to its span** (the linearity step
of the constant-planes argument for the closure and boundary rectifiability in the compactness
theorem).  If `ν` is finite on compact sets and `φ : ℝᴾ → ℝ` is `C^∞` with compact support, then
each `y ↦ Dφ(y)[v]` is continuous with compact support, hence `ν`-integrable, so
`v ↦ ∫ Dφ(y)[v] dν(y)` is linear; if it vanishes on `S`, it vanishes on `span S`. -/
theorem Submission.cbr_ci_cp_dir_integral_fderiv_span : ∀ (P : ℕ) (ν : Measure (Euclid P)) (φ : Euclid P → ℝ) (S : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ v ∈ S, ∫ y, fderiv ℝ φ y v ∂ν = 0) → ∀ v ∈ Submodule.span ℝ S, ∫ y, fderiv ℝ φ y v ∂ν = 0 := by
  intro P ν φ S hν hφ hφc hS
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν K hK⟩
  have hint : ∀ v, Integrable (fun y => fderiv ℝ φ y v) ν := by
    intro v
    have hc : Continuous (fun y => fderiv ℝ φ y v) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hc.integrable_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) v)
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add]
    rw [integral_add (hint x) (hint y), hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [map_smul, smul_eq_mul]
    rw [integral_const_mul, hx, mul_zero]
/-- **Testing a cycle condition on `φ α`** (used for the constant-plane step of White's
tangent-plane argument in the closure theorem behind Simon 7.2.4).  If `∫ ζ₀(dψ(y)) dν(y) = 0`
for every test `d`-form `ψ`, and `ζ₀(w♭ ∧ α) = v · w` for every `w`, where
`(w♭ ∧ α)(u₀, …, u_d) = Σᵢ (−1)ⁱ (w · uᵢ) α(u₀, …, ûᵢ, …, u_d)`, then `∫ Dφ(y)v dν(y) = 0`
for every compactly supported `C^∞` function `φ`: `φ α` is a test form with
`d(φ α)(y) = ∇φ(y)♭ ∧ α`, so `ζ₀(d(φ α)(y)) = v · ∇φ(y) = Dφ(y)v`. -/
theorem Submission.cbr_ci_cp_dir_cycle_fderiv_integral_zero : ∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)) (α : Covector (Euclid P) d) (v : Euclid P) (φ : Euclid P → ℝ), (∀ ψ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (ψ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → (∀ (w : Euclid P) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = inner ℝ v w) → ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0 := by
  intro P d ν ζ₀ α v φ hcyc hv hφ hφc
  have hmem : (fun y => φ y • α : DifferentialForm (Euclid P) d) ∈
      TestFormOn (univ : Set (Euclid P)) d :=
    ⟨⟨hφ.smul contDiff_const, hφc.smul_right⟩, subset_univ _⟩
  have h := hcyc ⟨_, hmem⟩
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hd : DifferentiableAt ℝ φ y := (hφ.differentiable (by simp)) y
  set g : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm (fderiv ℝ φ y) with hg
  have hγ : ∀ u : Fin (d + 1) → Euclid P, exteriorDerivative (fun y => φ y • α) y u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ g (u i) * α (i.removeNth u)) := by
    intro u
    rw [Submission.dgcr_bwd_extDeriv_smul_const P d φ α y u hd]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hg, InnerProductSpace.toDual_symm_apply]
  have hz := hv g _ hγ
  show fderiv ℝ φ y v = ζ₀ (exteriorDerivative (fun y => φ y • α) y)
  rw [hz, real_inner_comm, hg, InnerProductSpace.toDual_symm_apply]

/-- **Translation directions of a constant-orientation cycle** (the vectors `v_α` of the
tangent-plane step in the closure and boundary rectifiability part of Simon 7.2.4).  Let `ν` be a
Borel measure on `ℝᴾ`, finite on compact sets, and `ζ₀ ∈ Λ_{d+1}(ℝᴾ)` with `∫ ⟨dφ, ζ₀⟩ dν = 0` for
every test `d`-form `φ`.  For a `d`-covector `α` let `v_α` represent `w ↦ ⟨w♭ ∧ α, ζ₀⟩`, where
`(w♭ ∧ α)(u₀, …, u_d) = Σᵢ (−1)ⁱ ⟨w, uᵢ⟩ α(u₀, …, ûᵢ, …, u_d)`.  Then `V = span{v_α}` satisfies
`∫ Dψ[v] dν = 0` for `v ∈ V` and `ψ ∈ C_c^∞(ℝᴾ)` (test the cycle condition on `ψα`, using
`d(ψα) = (∇ψ)♭ ∧ α`), and `⟨w♭ ∧ α, ζ₀⟩ = ⟨v_α, w⟩ = 0` for `w ∈ Vᗮ`. -/
theorem Submission.cbr_ci_cp_wedge_annihilator_subspace : ∀ (P d : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P (d + 1)), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ φ : TestFormOn (univ : Set (Euclid P)) d, ∫ y, ζ₀ (exteriorDerivative (φ : DifferentialForm (Euclid P) d) y) ∂ν = 0) → ∃ V : Submodule ℝ (Euclid P), (∀ v ∈ V, ∀ φ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∫ y, fderiv ℝ φ y v ∂ν = 0) ∧ ∀ w ∈ Vᗮ, ∀ (α : Covector (Euclid P) d) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ₀ γ = 0 := by
  intro P d ν ζ₀ hν hcyc
  choose v hv using Submission.cbr_ci_cp_dir_wedge_riesz_vector P d ζ₀
  refine ⟨Submodule.span ℝ (range v), fun u hu φ hφ hφc => ?_, fun w hw α γ hγ => ?_⟩
  · refine Submission.cbr_ci_cp_dir_integral_fderiv_span P ν φ (range v) hν hφ hφc ?_ u hu
    rintro _ ⟨α, rfl⟩
    exact Submission.cbr_ci_cp_dir_cycle_fderiv_integral_zero P d ν ζ₀ α (v α) φ hcyc (hv α)
      hφ hφc
  · rw [hv α w γ hγ]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (mem_range_self α)) hw
/-- **An orthonormal basis of `ℝᴾ` adapted to a subspace `V`** (used to show that an `n`-vector
annihilating every `w♭ ∧ α` with `w ⊥ V` only sees `β ∘ p_V`): each basis vector lies in `V` or in
`Vᗮ`.  `V` and `Vᗮ` are orthogonal, and a vector orthogonal to `V + Vᗮ` lies in `Vᗮ ∩ Vᗮᗮ = 0`, so
`ℝᴾ` is the internal orthogonal direct sum of `V` and `Vᗮ`.  Concatenating orthonormal bases of
`V` and `Vᗮ` and re-indexing by `Fin P` (`finrank ℝ ℝᴾ = P`) gives the basis. -/
theorem Submission.cbr_ci_cp_pr_adapted_orthonormalBasis : ∀ (P : ℕ) (V : Submodule ℝ (Euclid P)), ∃ e : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, e i ∈ V ∨ e i ∈ Vᗮ := by
  intro P V
  -- Step 1: `b ↦ cond b V Vᗮ` is an orthogonal family of subspaces
  have hW' : OrthogonalFamily ℝ (fun b : Bool => ↥(cond b V Vᗮ))
      fun b => (cond b V Vᗮ).subtypeₗᵢ :=
    V.orthogonalFamily_self
  -- Step 2: it is internal, since `(V ⊔ Vᗮ)ᗮ ≤ Vᗮ ⊓ Vᗮᗮ = ⊥`
  have hW : DirectSum.IsInternal fun b : Bool => cond b V Vᗮ := by
    rw [hW'.isInternal_iff, Submodule.eq_bot_iff]
    intro x hx
    have h1 : x ∈ Vᗮ :=
      Submodule.orthogonal_le (le_iSup (fun b : Bool => cond b V Vᗮ) true) hx
    have h2 : x ∈ Vᗮᗮ :=
      Submodule.orthogonal_le (le_iSup (fun b : Bool => cond b V Vᗮ) false) hx
    exact Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint Vᗮ) x h1 h2
  -- Step 3: the orthonormal basis subordinate to this decomposition, indexed by `Fin P`; its
  -- `i`-th vector lies in the summand `cond b V Vᗮ` for some `b : Bool`
  refine ⟨hW.subordinateOrthonormalBasis finrank_euclideanSpace_fin hW', fun i => ?_⟩
  have hmem := hW.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace_fin i hW'
  revert hmem
  generalize hW.subordinateOrthonormalBasisIndex finrank_euclideanSpace_fin i hW' = b
  cases b
  · intro hmem
    exact Or.inr hmem
  · intro hmem
    exact Or.inl hmem
/-- The determinant `n`-covector of `g₀, …, g_{n-1} ∈ ℝᴾ`: `u ↦ det(⟨g_b, u_a⟩)_{a,b}`, with
`⟨g_b, u_a⟩` in row `a` and column `b` (for an orthonormal basis `e'`, the dual covectors `e'^I`
of the projection reduction in White's proof that limits are integer multiplicity, Simon 6.3.11).
Row `a` is `L u_a` for the linear map `L x = (⟨g_b, x⟩)_b`, so this is the row determinant
`detRowAlternating` composed with `L`, an alternating `n`-linear map.  It is continuous, the
determinant being a polynomial in the continuous entries `⟨g_b, u_a⟩`.  For `n = 0` it is the
constant `1`. -/
theorem Submission.cbr_ci_cp_pr_inner_det_covector : ∀ (P n : ℕ) (g : Fin n → Euclid P), ∃ γ : Covector (Euclid P) n, ∀ u : Fin n → Euclid P, γ u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := by
  intro P n g
  -- the alternating map `u ↦ D(L u₀, …, L u_{n-1})`, `D` the row determinant
  let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ :=
    Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun b => innerₛₗ ℝ (g b))
  have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := fun _ => rfl
  -- continuity: a polynomial in the continuous entries `⟨g_b, u_a⟩`
  have hc : Continuous fun u : Fin n → Euclid P =>
      Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a)) := by
    fun_prop
  exact ⟨⟨⟨f.toMultilinearMap, hc.congr fun u => (hf u).symm⟩, f.map_eq_zero_of_eq'⟩, hf⟩

/-- Laplace expansion of a determinant covector along column `k`.  If the `(d + 1)`-covector `γ`
is `u ↦ det (⟨g b, u a⟩)_{a b}`, then `γ u = ∑ᵢ (-1)ⁱ ⟨g k, u i⟩ α (u₀, …, ûᵢ, …, u_d)` with
`α = (-1)ᵏ γ'`, where `γ'` is the `d`-covector `v ↦ det (⟨g (k.succAbove b), v a⟩)_{a b}` of the
tuple `g` with `g k` deleted (`cbr_ci_cp_pr_inner_det_covector`): the `(i, k)` minor of
`(⟨g b, u a⟩)_{a b}` is that matrix for `v = i.removeNth u`. -/
theorem Submission.cbr_ci_cp_pr_det_covector_laplace : ∀ (P d : ℕ) (g : Fin (d + 1) → Euclid P) (k : Fin (d + 1)) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = Matrix.det (Matrix.of fun a b => inner ℝ (g b) (u a))) → ∃ α : Covector (Euclid P) d, ∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ (g k) (u i) * α (i.removeNth u)) := by
  intro P d g k γ hγ
  -- Step 1: the minor covector `γ'` of `g` with its `k`-th entry deleted, and `α = (-1)ᵏ γ'`.
  obtain ⟨γ', hγ'⟩ := Submission.cbr_ci_cp_pr_inner_det_covector P d (fun b => g (k.succAbove b))
  refine ⟨((-1 : ℝ) ^ (k : ℕ)) • γ', fun u => ?_⟩
  -- Step 2: Laplace expansion of `det (⟨g b, u a⟩)_{a b}` along column `k`.
  rw [hγ u, Matrix.det_succ_column _ k]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousAlternatingMap.smul_apply, hγ' (i.removeNth u), smul_eq_mul]
  -- Step 3: the `(i, k)` minor is the matrix of `i.removeNth u` against `g ∘ k.succAbove`.
  have hsub : (Matrix.of fun a b => inner ℝ (g b) (u a)).submatrix i.succAbove k.succAbove =
      Matrix.of fun a b => inner ℝ (g (k.succAbove b)) (i.removeNth u a) := by
    ext a b
    simp [Fin.removeNth]
  -- Step 4: `(-1) ^ (i + k) = (-1) ^ i * (-1) ^ k`.
  rw [hsub, Matrix.of_apply, pow_add]
  ring
/-- `n! · β(u) = ∑_I β(e_I) · det(⟨e_{I(b)}, u_a⟩)_{a,b}` for an `n`-covector `β` on `ℝᴾ`, an
orthonormal basis `e` of `ℝᴾ` and `u ∈ (ℝᴾ)ⁿ`, the sum running over all index maps
`I : Fin n → Fin P` (the expansion of `β` in the basis dual to `e`, used for the projection
reduction of constant plane currents in the integer multiplicity part of Simon 7.2.4, Remark
7.2.5(1)).  Expanding every argument in the basis `e` gives
`β(v) = ∑_I (∏_a ⟨e_{I(a)}, v_a⟩) β(e_I)`; as `β` is alternating,
`n! · β(u) = ∑_σ sign(σ) β(u ∘ σ)`; the Leibniz formula collects the sums over `σ` into the
determinants. -/
theorem Submission.cbr_ci_cp_pr_factorial_mul_eq_sum_det : ∀ (P n : ℕ) (e : OrthonormalBasis (Fin P) ℝ (Euclid P)) (β : Covector (Euclid P) n) (u : Fin n → Euclid P), (n.factorial : ℝ) * β u = ∑ I : Fin n → Fin P, β (fun a => e (I a)) * Matrix.det (Matrix.of fun a b => inner ℝ (e (I b)) (u a)) := by
  intro P n e β u
  classical
  -- multilinear expansion of `β` in the orthonormal basis `e`
  have hexp : ∀ v : Fin n → Euclid P, β v =
      ∑ I : Fin n → Fin P, (∏ a, inner ℝ (e (I a)) (v a)) * β (fun a => e (I a)) := by
    intro v
    have hv : v = fun a => ∑ m, inner ℝ (e m) (v a) • e m := by
      funext a
      exact (e.sum_repr' (v a)).symm
    conv_lhs => rw [hv]
    rw [β.map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [β.map_smul_univ (fun a => inner ℝ (e (I a)) (v a)) (fun a => e (I a)), smul_eq_mul]
  -- alternation: `sign(σ) β(u ∘ σ) = sign(σ)² β(u) = β(u)`, and there are `n!` permutations
  have halt : (n.factorial : ℝ) * β u =
      ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) := by
    have : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) = β u := by
      intro σ
      rw [show β (u ∘ σ) = Equiv.Perm.sign σ • β u from β.toAlternatingMap.map_perm u σ]
      rw [Units.smul_def, zsmul_eq_mul, ← mul_assoc]
      have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
      rw [hs, one_mul]
    rw [Finset.sum_congr rfl fun σ _ => this σ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [halt]
  -- expand only `β (u ∘ σ)` (the right side of `hexp` contains `β` again), then swap the sums
  have h2 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℝ) * β (u ∘ σ) =
      ∑ I : Fin n → Fin P, (Equiv.Perm.sign σ : ℝ) *
        ((∏ a, inner ℝ (e (I a)) ((u ∘ σ) a)) * β (fun a => e (I a))) := by
    intro σ
    rw [hexp (u ∘ σ), Finset.mul_sum]
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_comm]
  -- for fixed `I`, the sum over `σ` is the Leibniz formula for the determinant
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Matrix.det_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Matrix.of_apply, Function.comp_apply]
  ring

/-- Projection reduction for the constant-planes step of the cycle case of closure and boundary
rectifiability: if an `n`-vector `ζ` (`n = d + 1`) vanishes on every `n`-covector `w♭ ∧ α` with
`w ∈ Vᗮ` and `α` a `d`-covector, then `ζ(β) = ζ(β ∘ p_V)` for every `n`-covector `β`, where `p_V`
is the orthogonal projection onto `V`.  Take an orthonormal basis `e` of `ℝᴾ` with each `eᵢ` in
`V` or in `Vᗮ` (subordinate to `ℝᴾ = V ⊕ Vᗮ`) and the covectors `e^I(u) = det(⟨e_{I b}, u_a⟩)`,
`I : Fin n → Fin P` (`cbr_ci_cp_pr_inner_det_covector`), so that `n! β = ∑_I β(e_I) e^I`
(`cbr_ci_cp_pr_factorial_mul_eq_sum_det`).  If `e_{I k} ∈ Vᗮ` for some `k`, Laplace expansion along
column `k` writes `e^I = e_{I k}♭ ∧ α` (`cbr_ci_cp_pr_det_covector_laplace`), so `ζ(e^I) = 0`;
otherwise `p_V e_{I b} = e_{I b}` for every `b`, and `β ∘ p_V` has the same coefficient `β(e_I)`. -/
theorem Submission.cbr_ci_cp_eval_comp_starProjection_eq : ∀ (P d : ℕ) (ζ : MultiVector P (d + 1)) (V : Submodule ℝ (Euclid P)), (∀ w ∈ Vᗮ, ∀ (α : Covector (Euclid P) d) (γ : Covector (Euclid P) (d + 1)), (∀ u : Fin (d + 1) → Euclid P, γ u = ∑ i : Fin (d + 1), (-1 : ℝ) ^ (i : ℕ) * (inner ℝ w (u i) * α (i.removeNth u))) → ζ γ = 0) → ∀ β : Covector (Euclid P) (d + 1), ζ β = ζ (β.compContinuousLinearMap V.starProjection) := by
  have hdet := Submission.cbr_ci_cp_pr_inner_det_covector
  have hlap := Submission.cbr_ci_cp_pr_det_covector_laplace
  have hexp := Submission.cbr_ci_cp_pr_factorial_mul_eq_sum_det
  intro P d ζ V hζ β
  -- Step 1: an orthonormal basis of `ℝᴾ` subordinate to `ℝᴾ = V ⊕ Vᗮ`
  obtain ⟨e, he⟩ : ∃ e : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i, e i ∈ V ∨ e i ∈ Vᗮ := by
    have hV' := V.orthogonalFamily_self
    have hint : DirectSum.IsInternal (fun b : Bool => cond b V Vᗮ) := by
      refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV'.independent ?_
      rw [iSup_bool_eq]
      exact Submodule.sup_orthogonal_of_hasOrthogonalProjection
    refine ⟨hint.subordinateOrthonormalBasis finrank_euclideanSpace_fin hV', fun i => ?_⟩
    have hi := hint.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace_fin i hV'
    revert hi
    cases hint.subordinateOrthonormalBasisIndex finrank_euclideanSpace_fin i hV'
    · exact Or.inr
    · exact Or.inl
  -- Step 2: the determinant covectors `e^I(u) = det(⟨e_{I b}, u_a⟩)`
  choose γ hγ using fun I : Fin (d + 1) → Fin P => hdet P (d + 1) fun b => e (I b)
  -- Step 3: `(d+1)! ζ(β') = ∑_I β'(e_I) ζ(e^I)` for every `(d+1)`-covector `β'`
  have hsum : ∀ β' : Covector (Euclid P) (d + 1), ((d + 1).factorial : ℝ) * ζ β' =
      ∑ I : Fin (d + 1) → Fin P, β' (fun a => e (I a)) * ζ (γ I) := by
    intro β'
    have hcov : ((d + 1).factorial : ℝ) • β' =
        ∑ I : Fin (d + 1) → Fin P, β' (fun a => e (I a)) • γ I := by
      ext u
      rw [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply, smul_eq_mul,
        hexp P (d + 1) e β' u]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, hγ]
    have := congrArg ζ hcov
    rw [map_smul, map_sum, smul_eq_mul] at this
    rw [this]
    simp only [map_smul, smul_eq_mul]
  -- Step 4: `ζ(e^I) = 0` if some `e_{I k} ∈ Vᗮ` (Laplace expansion along column `k`)
  have hkill : ∀ (I : Fin (d + 1) → Fin P) (k : Fin (d + 1)), e (I k) ∈ Vᗮ → ζ (γ I) = 0 := by
    intro I k hk
    obtain ⟨α, hα⟩ := hlap P d (fun b => e (I b)) k (γ I) (hγ I)
    exact hζ (e (I k)) hk α (γ I) hα
  -- Step 5: `β ∘ p_V` and `β` agree on `e_I` if every `e_{I b} ∈ V`
  have hcoef : ∀ I : Fin (d + 1) → Fin P, (∀ b, e (I b) ∈ V) →
      β.compContinuousLinearMap V.starProjection (fun a => e (I a)) = β (fun a => e (I a)) := by
    intro I hI
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext a
    exact Submodule.starProjection_eq_self_iff.mpr (hI a)
  -- Step 6: compare the two expansions term by term
  have hfact : ((d + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply mul_left_cancel₀ hfact
  rw [hsum β, hsum (β.compContinuousLinearMap V.starProjection)]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : ∀ b, e (I b) ∈ V
  · rw [hcoef I hI]
  · obtain ⟨k, hk⟩ := not_forall.mp hI
    rw [hkill I k ((he (I k)).resolve_left hk), mul_zero, mul_zero]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
