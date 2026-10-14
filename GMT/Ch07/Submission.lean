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

/-- **Weighted line currents** (Simon 6.2.1).  For unit vectors `vₖ`, arbitrary parameter sets
`Iₖ ⊆ ℝ` and real weights `cₖ` (`k` in a finite type), `ω ↦ Σₖ cₖ ∫_{Iₖ} ω(pₖ + t vₖ)(vₖ) dt` is a
`1`-current in `ℝᴾ`.  Each `γₖ(t) = pₖ + t vₖ` is an isometry, hence a closed embedding, so each
integrand is continuous with compact support; a null sequence of test forms converges to `0`
uniformly on `ℝᴾ`, and dominated convergence with the indicator of the compact set `γₖ⁻¹(K)`
gives the sequential continuity of each piece. -/
theorem Submission.idtp_fons_odc_pc_line_current : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℝ), (∀ k, ‖v k‖ = 1) → ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1, ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω = ∑ k, c k * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) := by
  intro P ι hι p v I c hv
  -- test forms converging to `0` in `𝒟¹(ℝᴾ)` converge to `0` uniformly on all of `ℝᴾ`
  have hunif : ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) 1, TestFormOnConverges ωs 0 →
      TendstoUniformly (fun j => (ωs j : DifferentialForm (Euclid P) 1)) 0 atTop := by
    intro ωs h
    obtain ⟨K, -, -, hsupp, -, hderiv⟩ := h
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hderiv 0) ε hε] with j hj x
    by_cases hx : x ∈ K
    · simpa [iteratedFDeriv_zero_eq_comp] using hj x hx
    · simpa [image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')] using hε
  -- integration of `1`-forms along one unit-speed line `t ↦ q + t w`, `t ∈ J`, is a current
  have hline : ∀ (q w : Euclid P) (J : Set ℝ), ‖w‖ = 1 →
      ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1,
        ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
          X ω = ∫ t in J, (ω : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w) := by
    intro q w J hw
    have hγ : Isometry fun t : ℝ => q + t • w := by
      refine Isometry.of_dist_eq fun s t => ?_
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hw, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
    have hint (ω : TestFormOn (univ : Set (Euclid P)) 1) :
        Integrable fun t : ℝ => (ω : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w) :=
      ((continuous_eval_const (F := Covector (Euclid P) 1) fun _ : Fin 1 => w).comp
        (ω.2.1.1.continuous.comp hγ.continuous)).integrable_of_hasCompactSupport
        ((ω.2.1.2.comp_isClosedEmbedding hγ.isClosedEmbedding).comp_left
          (g := fun α : Covector (Euclid P) 1 => α fun _ => w) rfl)
    refine ⟨⟨{ toFun := fun ω =>
                 ∫ t in J, (ω : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w)
               map_add' := fun ω η => ?_
               map_smul' := fun a ω => ?_ }, fun ωs h => ?_⟩, fun ω => rfl⟩
    · simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
      exact integral_add (hint ω).restrict (hint η).restrict
    · simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      exact integral_const_mul a _
    · -- dominated convergence, dominated by the indicator of the compact set `γ⁻¹(K)`
      have hu := hunif ωs h
      obtain ⟨K, hK, -, hsupp, -, -⟩ := h
      have hS : IsCompact ((fun t : ℝ => q + t • w) ⁻¹' K) :=
        hγ.isClosedEmbedding.isCompact_preimage hK
      have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict J)
        (F := fun j t => (ωs j : DifferentialForm (Euclid P) 1) (q + t • w) (fun _ => w))
        (f := fun _ => 0) (((fun t : ℝ => q + t • w) ⁻¹' K).indicator fun _ => 1)
        (Eventually.of_forall fun j => (hint (ωs j)).aestronglyMeasurable.restrict) ?_
        ((integrableOn_const (C := (1 : ℝ)) hS.measure_lt_top.ne).integrable_indicator
          hS.isClosed.measurableSet).restrict
        (Eventually.of_forall fun t => by
          simpa [Function.comp_def] using ((continuous_eval_const (F := Covector (Euclid P) 1)
            fun _ : Fin 1 => w).tendsto 0).comp (hu.tendsto_at (q + t • w)))
      · simpa using key
      · filter_upwards [Metric.tendstoUniformly_iff.1 hu 1 one_pos] with j hj
        refine Eventually.of_forall fun t => ?_
        by_cases ht : q + t • w ∈ K
        · rw [indicator_of_mem (show t ∈ (fun t : ℝ => q + t • w) ⁻¹' K from ht)]
          calc _ ≤ ‖(ωs j : DifferentialForm (Euclid P) 1) (q + t • w)‖ * ∏ _i : Fin 1, ‖w‖ :=
                ContinuousAlternatingMap.le_opNorm _ _
            _ ≤ 1 := by simpa [hw] using (hj (q + t • w)).le
        · rw [indicator_of_notMem (show t ∉ (fun t : ℝ => q + t • w) ⁻¹' K from ht),
            image_eq_zero_of_notMem_tsupport fun h' => ht (hsupp j h')]
          simp
  -- the weighted finite sum of the line currents
  choose X hX using fun k => hline (p k) (v k) (I k) (hv k)
  refine ⟨⟨∑ k, c k • (X k).toCurrent, fun ωs h => ?_⟩, fun ω => ?_⟩
  · simpa using tendsto_finsetSum Finset.univ fun k _ => ((X k).continuous' ωs h).const_mul (c k)
  · simp [← hX]
/-- **Simon Ch. 3, 1.4** (local flat model): a measurable `M` that coincides near `x` with the
affine plane `x + Q` has `Q` as approximate tangent space at `x`.  If `spt f ⊆ closedBall 0 R`
and `0 < ρ < r / R`, then for `y ∈ spt f` the point `x + ρ y` lies in `B_r(x)`, so
`y ∈ η_{x,ρ}(M) ↔ x + ρ y ∈ M ↔ ρ y ∈ Q ↔ y ∈ Q`; hence the blown-up integrals equal
`∫_Q f dHⁿ` for all small `ρ > 0`. -/
theorem Submission.idtp_fons_odc_pc_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r : ℝ), MeasurableSet M → Module.finrank ℝ Q = n → 0 < r → M ∩ ball x r = {y | y - x ∈ Q} ∩ ball x r → HasApproximateTangentSpaceAt n M x Q := by
  intro P n M x Q r hM hQ hr hloc
  refine ⟨hQ, fun f => ?_⟩
  -- `spt f ⊆ closedBall 0 R` with `R > 0`
  obtain ⟨R, hR0, hR⟩ :=
    f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Euclid P)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr hR0)] with ρ ⟨hρ0, hρ⟩
  rw [lt_div_iff₀ hR0] at hρ
  -- `η_{x,ρ}(M) = {y | x + ρ y ∈ M}`
  have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' M =
      (fun y => x + ρ • y) ⁻¹' M := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ0.ne'] using hz
    · intro hy
      exact ⟨_, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ0.ne']⟩
  rw [himage, ← integral_indicator (hM.preimage (by fun_prop)),
    ← integral_indicator (Submodule.closed_of_finiteDimensional Q).measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ tsupport f
  · -- on `spt f`, `x + ρ y ∈ B_r(x)`, so `x + ρ y ∈ M ↔ ρ y ∈ Q ↔ y ∈ Q`
    have hball : x + ρ • y ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 (hR hy)) hρ0.le).trans_lt hρ
    have hiff : y ∈ (fun y => x + ρ • y) ⁻¹' M ↔ y ∈ Q := by
      have h := Set.ext_iff.1 hloc (x + ρ • y)
      simp only [mem_inter_iff, hball, and_true, mem_ofPred_eq, add_sub_cancel_left] at h
      show x + ρ • y ∈ M ↔ y ∈ Q
      rw [h, Q.smul_mem_iff hρ0.ne']
    by_cases hyQ : y ∈ Q
    · rw [indicator_of_mem hyQ, indicator_of_mem (hiff.2 hyQ)]
    · rw [indicator_of_notMem hyQ, indicator_of_notMem (mt hiff.1 hyQ)]
  · -- off `spt f` both integrands vanish
    have h0 : f y = 0 := image_eq_zero_of_notMem_tsupport hy
    rw [indicator_apply_eq_zero.2 fun _ => h0, indicator_apply_eq_zero.2 fun _ => h0]
/-- **Near an isolated point of an open line piece, a union of line pieces is the line**
(parent step 3e).  Let `S_j = {p_j + t v_j : t ∈ I_j}` for `j` in a finite `ι`.  If
`‖v_k‖ = 1`, `I_k` is open, `S_k ⊆ M ⊆ ⋃_j S_j`, `x ∈ S_k` and `x ∉ closure S_j` for all
`j ≠ k`, then `M ∩ B_r(x) = (x + span{v_k}) ∩ B_r(x)` for some `r > 0`.  Write
`x = p_k + t₀ v_k` with `(t₀ − ε, t₀ + ε) ⊆ I_k`; finiteness of `ι` gives `δ > 0` with
`B_δ(x) ∩ S_j = ∅` for `j ≠ k`; take `r = min ε δ`.  A point `y = x + s v_k` of the ball has
`|s| = ‖y − x‖ < ε` (as `‖v_k‖ = 1`), so `y = p_k + (t₀ + s) v_k ∈ S_k ⊆ M`. -/
theorem Submission.idtp_fons_odc_pc_piece_locally_line : ∀ (P : ℕ) (ι : Type) [Finite ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (M : Set (Euclid P)) (k : ι) (x : Euclid P), ‖v k‖ = 1 → IsOpen (I k) → M ⊆ (⋃ j, (fun t : ℝ => p j + t • v j) '' I j) → (fun t : ℝ => p k + t • v k) '' I k ⊆ M → x ∈ (fun t : ℝ => p k + t • v k) '' I k → (∀ j, j ≠ k → x ∉ closure ((fun t : ℝ => p j + t • v j) '' I j)) → ∃ r : ℝ, 0 < r ∧ M ∩ ball x r = {y | y - x ∈ Submodule.span ℝ {v k}} ∩ ball x r := by
  intro P ι _ p v I M k x hv hI hM hkM hx hcl
  -- Step 1: `x = p_k + t₀ v_k` with `t₀ ∈ I_k`, and `(t₀ − ε, t₀ + ε) ⊆ I_k`
  obtain ⟨t₀, ht₀, hx⟩ := hx
  change p k + t₀ • v k = x at hx
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 hI t₀ ht₀
  -- Step 2: as `ι` is finite, some `B_δ(x)` misses every piece `S_j` with `j ≠ k`
  obtain ⟨δ, hδ, hδS⟩ := Metric.eventually_nhds_iff.1 <| Filter.eventually_all.2 fun j =>
    Filter.eventually_imp_distrib_left.2 fun hj =>
      Filter.not_frequently.1 (mt mem_closure_iff_frequently.2 (hcl j hj))
  -- Step 3: `r := min ε δ`
  refine ⟨min ε δ, lt_min hε hδ, Set.ext fun y => ⟨fun hy => ⟨?_, hy.2⟩, fun hy => ⟨?_, hy.2⟩⟩⟩
  · -- (⊆): `y ∈ S_j` with `dist y x < δ` forces `j = k`, so `y − x = (t − t₀) v_k`
    obtain ⟨hyM, hyr⟩ := hy
    obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.1 (hM hyM)
    obtain rfl : j = k := by
      by_contra hj
      exact hδS ((Metric.mem_ball.1 hyr).trans_le (min_le_right _ _)) j hj ⟨t, ht, rfl⟩
    refine Submodule.mem_span_singleton.2 ⟨t - t₀, ?_⟩
    rw [← hx, sub_smul]
    dsimp only
    abel
  · -- (⊇): `y − x = s v_k` with `|s| = ‖y − x‖ < ε`, so `y = p_k + (t₀ + s) v_k ∈ S_k ⊆ M`
    obtain ⟨hy, hyr⟩ := hy
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hy
    have hsε : |s| < ε := by
      have h : ‖s • v k‖ < ε := by
        rw [hs, ← dist_eq_norm_sub]
        exact (Metric.mem_ball.1 hyr).trans_le (min_le_left _ _)
      rwa [norm_smul, hv, mul_one, Real.norm_eq_abs] at h
    refine hkM ⟨t₀ + s, hεI ?_, ?_⟩
    · rwa [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    · change p k + (t₀ + s) • v k = y
      rw [add_smul, ← add_assoc, hx, hs, add_sub_cancel]
/-- **Simon 7.3.3, proof of (2), formula (10)**: `ω₁ = 2`, and for `‖v‖ = 1` the line
`γ(t) = p + t v` is a measurable embedding with `H¹⌞γ(I) = γ_#(ℒ¹⌞I)` and `H¹(γ(I)) = ℒ¹(I)`
for every `I ⊆ ℝ`.  `γ` is an isometry, `μHE[1] = volume` on `ℝ` and `μHE[1]` is preserved by
isometries; the unit ball of `ℝ¹` is the image of `(-1, 1)` under `t ↦ 0 + t e₀`. -/
theorem Submission.idtp_fons_odc_line_hausdorff : unitBallVolume 1 = 2 ∧ ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → MeasurableEmbedding (fun t : ℝ => p + t • v) ∧ ∀ I : Set ℝ, (μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => p + t • v) '' I) = Measure.map (fun t : ℝ => p + t • v) (volume.restrict I) ∧ (μHE[1] : Measure (Euclid P)) ((fun t : ℝ => p + t • v) '' I) = volume I := by
  -- `H¹ = ℒ¹` on `ℝ`, since `finrank ℝ ℝ = 1`
  have hR : (μHE[1] : Measure ℝ) = volume := by
    simpa only [Module.finrank_self] using
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  -- `γ(t) = p + t v` is an isometry when `‖v‖ = 1`
  have hiso : ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → Isometry (fun t : ℝ => p + t • v) :=
    fun P p v hv => Isometry.of_dist_eq fun s t => by
      show dist (p + s • v) (p + t • v) = dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  refine ⟨?_, fun P p v hv => ?_⟩
  · -- `ω₁ = 2`: the unit ball of `ℝ¹` is the image of `(-1, 1)` under `t ↦ 0 + t e₀`
    set e : Euclid 1 := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have hball : ball (0 : Euclid 1) 1 = (fun t : ℝ => (0 : Euclid 1) + t • e) '' Ioo (-1) 1 := by
      ext x
      constructor
      · intro hx
        have hxe : x 0 • e = x := by
          ext i
          rw [Fin.fin_one_eq_zero i]
          simp [e]
        rw [mem_ball_zero_iff, ← hxe, norm_smul, he, mul_one, Real.norm_eq_abs] at hx
        exact ⟨x 0, abs_lt.mp hx, (zero_add _).trans hxe⟩
      · rintro ⟨t, ht, rfl⟩
        rw [mem_ball_zero_iff]
        show ‖(0 : Euclid 1) + t • e‖ < 1
        rw [zero_add, norm_smul, he, mul_one, Real.norm_eq_abs]
        exact abs_lt.mpr ht
    rw [unitBallVolume, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 1, hball,
      (hiso 1 0 e he).euclideanHausdorffMeasure_image, hR, Real.volume_Ioo]
    norm_num
  · have hemb : MeasurableEmbedding (fun t : ℝ => p + t • v) :=
      (hiso P p v hv).isClosedEmbedding.measurableEmbedding
    refine ⟨hemb, fun I => ⟨?_, ?_⟩⟩
    · -- `H¹⌞γ(I) = (H¹⌞range γ)⌞γ(I) = (γ_#ℒ¹)⌞γ(I) = γ_#(ℒ¹⌞γ⁻¹(γ(I))) = γ_#(ℒ¹⌞I)`
      rw [← Measure.restrict_restrict_of_subset (image_subset_range _ I),
        ← (hiso P p v hv).map_euclideanHausdorffMeasure, hR, hemb.restrict_map,
        hemb.injective.preimage_image]
    · rw [(hiso P p v hv).euclideanHausdorffMeasure_image, hR]

/-- **Weighted open line pieces carry an integer multiplicity triple** (Simon Ch. 6, 3.1; the
polygonal current in the proof of 7.3.3).  Let `Sₖ = γₖ(Iₖ)`, `γₖ(t) = pₖ + t vₖ` with `‖vₖ‖ = 1`
and `Iₖ` open, and let the overlaps `Sⱼ ∩ closure Sₖ` (`j ≠ k`) be `H¹`-null.  Then
`M = ⋃_{cₖ ≠ 0} Sₖ`, `θ = Σₖ |cₖ| 𝟙_{Sₖ}` and `ξ = Σₖ (cₖ 𝟙_{Sₖ} / θ) vₖ` form an `IMRep univ 1`
with `θ ξ(α) = Σₖ cₖ 𝟙_{Sₖ} α(vₖ)`.  The pieces are Borel and locally `H¹`-finite because `γₖ` is
an isometry; off the null overlap set `M` is locally the line `x + span {vₖ}`
(`idtp_fons_odc_pc_piece_locally_line`), whose approximate tangent space is `span {vₖ}`
(`idtp_fons_odc_pc_local_plane_tangent`), and there `ξ(x) = ±vₖ`. -/
theorem Submission.idtp_fons_odc_pc_imrep : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, IsOpen (I k)) → (∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p j + t • v j) '' I j) ∩ closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) → ∃ R : IMRep (univ : Set (Euclid P)) 1, R.carrier = (⋃ k, ⋃ (_ : c k ≠ 0), (fun t : ℝ => p k + t • v k) '' I k) ∧ (∀ x, R.mult x = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k).natAbs) x) ∧ ∀ (x : Euclid P) (α : Covector (Euclid P) 1), (R.mult x : ℝ) * R.orient x α = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k) := by
  intro P ι _ p v I c hv hI hdisj
  -- Tool (ii): `γₖ(t) = pₖ + t vₖ` is an isometry `ℝ → ℝᴾ`
  have hγ : ∀ k, Isometry (fun t : ℝ => p k + t • v k) := fun k =>
    Isometry.of_dist_eq fun s t => by
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv k, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  -- Step 1: the pieces `Sₖ = γₖ(Iₖ)` are Borel; the carrier `M = ⋃_{cₖ ≠ 0} Sₖ`
  obtain ⟨S, hSdef⟩ : ∃ S : ι → Set (Euclid P),
      ∀ k, S k = (fun t : ℝ => p k + t • v k) '' I k := ⟨_, fun _ => rfl⟩
  have hS : ∀ k, MeasurableSet (S k) := fun k => by
    rw [hSdef]
    exact (hγ k).isClosedEmbedding.measurableEmbedding.measurableSet_image.2 (hI k).measurableSet
  obtain ⟨M, hMdef⟩ : ∃ M : Set (Euclid P), M = ⋃ k, ⋃ (_ : c k ≠ 0), S k := ⟨_, rfl⟩
  have hmemM : ∀ x, x ∈ M ↔ ∃ k, c k ≠ 0 ∧ x ∈ S k := fun x => by simp [hMdef]
  have hM : MeasurableSet M :=
    hMdef ▸ MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hS k
  have hSM : ∀ k, c k ≠ 0 → S k ⊆ M := fun k hk x hx => (hmemM x).2 ⟨k, hk, hx⟩
  have hMS : M ⊆ ⋃ j, (fun t : ℝ => p j + t • v j) '' I j := fun y hy => by
    obtain ⟨j, -, hyj⟩ := (hmemM y).1 hy
    exact mem_iUnion.2 ⟨j, by rwa [← hSdef]⟩
  -- Step 2: the multiplicity `θ = Σₖ |cₖ| 𝟙_{Sₖ}` and `∫_B θ dH¹ = Σₖ |cₖ| H¹(Sₖ ∩ B)`
  obtain ⟨θ, hθdef⟩ : ∃ θ : Euclid P → ℕ,
      θ = fun x => ∑ k, (S k).indicator (fun _ => (c k).natAbs) x := ⟨_, rfl⟩
  have hθmeas : Measurable θ :=
    hθdef ▸ Finset.measurable_sum _ fun k _ => measurable_const.indicator (hS k)
  have hθlint : ∀ B, ∫⁻ x in B, (θ x : ℝ≥0∞) ∂μHE[1] =
      ∑ k, ((c k).natAbs : ℝ≥0∞) * μHE[1] (S k ∩ B) := fun B => by
    have h : ∀ x, (θ x : ℝ≥0∞) = ∑ k, (S k).indicator (fun _ => ((c k).natAbs : ℝ≥0∞)) x :=
      fun x => by
        rw [hθdef]
        push_cast
        exact Finset.sum_congr rfl fun k _ => by by_cases hx : x ∈ S k <;> simp [hx]
    simp_rw [h]
    rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hS k)]
    exact Finset.sum_congr rfl fun k _ => by
      rw [lintegral_indicator_const (hS k), Measure.restrict_apply (hS k)]
  -- Step 3: the orientation `ξ = Σₖ (cₖ 𝟙_{Sₖ} / θ) ev_{vₖ}` is strongly measurable
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : Euclid P → MultiVector P 1, ξ = fun x =>
      ∑ k, ((S k).indicator (fun _ => (c k : ℝ)) x / θ x) •
        ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v k) := ⟨_, rfl⟩
  have hξmeas : StronglyMeasurable ξ := by
    -- instance search does not find `ContinuousAdd` for this space of continuous linear maps
    have : ContinuousAdd (MultiVector P 1) :=
      (inferInstance : IsTopologicalAddGroup (MultiVector P 1)).toContinuousAdd
    rw [hξdef]
    exact Finset.stronglyMeasurable_fun_sum _ fun k _ =>
      (((measurable_const.indicator (hS k)).div
        (measurable_from_nat.comp hθmeas)).stronglyMeasurable).smul_const _
  -- Step 4: `θ(x) ξ(x)(α) = Σₖ cₖ 𝟙_{Sₖ}(x) α(vₖ)`
  have hθξ : ∀ x (α : Covector (Euclid P) 1), (θ x : ℝ) * ξ x α =
      ∑ k, (S k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k) := by
    intro x α
    rw [hξdef]
    simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.apply_apply]
    rcases eq_or_ne (θ x : ℝ) 0 with h | h
    · -- `θ(x) = 0` forces every `cₖ 𝟙_{Sₖ}(x)` to vanish
      have h0 : ∀ k, (S k).indicator (fun _ => (c k : ℝ)) x = 0 := by
        intro k
        rw [Nat.cast_eq_zero, hθdef] at h
        have hk := Finset.sum_eq_zero_iff.1 h k (Finset.mem_univ k)
        rw [indicator_apply_eq_zero] at hk ⊢
        exact fun hx => by simp [Int.natAbs_eq_zero.1 (hk hx)]
      simp [h, h0]
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by field_simp
  -- Step 5: `R = (M, θ, ξ)` is an integer multiplicity triple
  let R : IMRep (univ : Set (Euclid P)) 1 :=
    { carrier := M
      mult := θ
      orient := ξ
      measurableSet_carrier := hM
      carrier_subset := subset_univ M
      rectifiable := by
        -- each `Sₖ` lies in the range of the Lipschitz map `γₖ ∘ proj₀ : ℝ¹ → ℝᴾ`
        refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (countable_range S)
          (forall_mem_range.2 fun k => ?_)).mono ?_
        · rw [hSdef]
          refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_range
            ((hγ k).lipschitzWith.comp (EuclideanSpace.proj (0 : Fin 1) :
              EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).lipschitzWith)).mono ?_
          rintro _ ⟨t, -, rfl⟩
          exact ⟨EuclideanSpace.single 0 t, by simp⟩
        · intro x hx
          obtain ⟨k, -, hxk⟩ := (hmemM x).1 hx
          exact ⟨S k, mem_range_self k, hxk⟩
      measurable_mult := hθmeas
      mult_pos := fun x hx => by
        obtain ⟨k, hk, hxk⟩ := (hmemM x).1 hx
        rw [hθdef]
        refine (Int.natAbs_pos.2 hk).trans_le ?_
        calc (c k).natAbs = (S k).indicator (fun _ => (c k).natAbs) x :=
              (indicator_of_mem hxk fun _ => (c k).natAbs).symm
          _ ≤ _ := Finset.single_le_sum (f := fun j => (S j).indicator (fun _ => (c j).natAbs) x)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
      locallyIntegrable_mult := fun K hK _ => by
        rw [hθlint]
        refine ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
        refine ne_top_of_le_ne_top ?_ (measure_mono (inter_subset_inter_right _ inter_subset_right))
        -- `H¹(Sₖ ∩ K) = ℒ¹(Iₖ ∩ γₖ⁻¹K) ≤ ℒ¹(γₖ⁻¹K) < ∞`, `γₖ⁻¹K` being compact
        have hvol : (μHE[1] : Measure ℝ) = volume := by
          have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
          rwa [Module.finrank_self] at h
        rw [hSdef, ← image_inter_preimage, (hγ k).euclideanHausdorffMeasure_image, hvol]
        exact ne_top_of_le_ne_top
          ((hγ k).isClosedEmbedding.isCompact_preimage hK).measure_lt_top.ne
          (measure_mono inter_subset_right)
      aestronglyMeasurable_orient := hξmeas.aestronglyMeasurable
      orients := by
        -- off the `H¹`-null overlap set, `x` lies in exactly one piece `Sₖ`, away from the others
        have hB : (μHE[1] : Measure (Euclid P))
            (⋃ j, ⋃ k, ⋃ (_ : j ≠ k), S j ∩ closure (S k)) = 0 :=
          measure_iUnion_null fun j => measure_iUnion_null fun k => measure_iUnion_null fun h => by
            rw [hSdef, hSdef]
            exact hdisj j k h
        filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hB), ae_restrict_mem hM]
          with x hxB hxM
        obtain ⟨k, hk, hxk⟩ := (hmemM x).1 hxM
        have hxj : ∀ j, j ≠ k → x ∉ closure (S j) := fun j hjk h =>
          hxB (mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk.symm, hxk, h⟩⟩⟩)
        have hθx : θ x = (c k).natAbs := by
          rw [hθdef]
          dsimp only
          rw [Finset.sum_eq_single k (fun j _ hjk => indicator_of_notMem
              (fun h => hxj j hjk (subset_closure h)) _) (fun h => (h (Finset.mem_univ k)).elim),
            indicator_of_mem hxk]
        have hξx : ξ x = ((c k : ℝ) / |(c k : ℝ)|) •
            ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v k) := by
          rw [hξdef]
          dsimp only
          rw [Finset.sum_eq_single k (fun j _ hjk => by
              rw [indicator_of_notMem (fun h => hxj j hjk (subset_closure h)), zero_div, zero_smul])
            (fun h => (h (Finset.mem_univ k)).elim), indicator_of_mem hxk, hθx, Nat.cast_natAbs,
            Int.cast_abs]
        refine ⟨Submodule.span ℝ {v k}, ?_, ?_⟩
        · -- Tools (iii), (iv): near `x`, `M` is the line `x + span {vₖ}`
          obtain ⟨r, hr, hMr⟩ := Submission.idtp_fons_odc_pc_piece_locally_line P ι p v I M k x
            (hv k) (hI k) hMS (by rw [← hSdef]; exact hSM k hk) (by rw [← hSdef]; exact hxk)
            fun j hjk => by rw [← hSdef]; exact hxj j hjk
          exact Submission.idtp_fons_odc_pc_local_plane_tangent P 1 M x _ r hM
            (finrank_span_singleton (norm_ne_zero_iff.1 (by rw [hv k]; exact one_ne_zero))) hr hMr
        · -- `ξ(x) = ±vₖ` with `(vₖ)` orthonormal spanning `span {vₖ}`
          rw [hξx]
          refine ⟨fun _ => v k, ⟨fun _ => hv k, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩,
            by rw [range_const], ?_⟩
          have hck : (c k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
          rcases hck.lt_or_gt with h | h
          · exact Or.inr fun α => by simp [abs_of_neg h, div_neg, div_self hck]
          · exact Or.inl fun α => by simp [abs_of_pos h, div_self hck] }
  -- Step 6: the carrier, multiplicity and `θ ξ` formulas hold by construction
  refine ⟨R, ?_, fun x => ?_, fun x α => ?_⟩
  · show M = _
    rw [hMdef]
    simp_rw [hSdef]
  · show θ x = _
    rw [hθdef]
    simp_rw [hSdef]
  · show (θ x : ℝ) * ξ x α = _
    rw [hθξ x α]
    simp_rw [hSdef]
/-- **Simon 7.3.3, proof of (2)**, the polygonal integer multiplicity current (steps 4–5): let
`R` be a 1-dimensional integer multiplicity triple in `ℝᴾ` carried by `⋃_{cₖ ≠ 0} Sₖ`, where
`Sₖ = γₖ(Iₖ)`, `γₖ(t) = pₖ + t vₖ`, `‖vₖ‖ = 1`, with `θ = Σₖ |cₖ| 1_{Sₖ}` and
`θ ⟨α, ξ⟩ = Σₖ cₖ 1_{Sₖ} α(vₖ)`.  Then `τ(R)(ω) = Σₖ cₖ ∫_{Iₖ} ω(γₖ(t))(vₖ) dt` and
`μ_R(A) = Σₖ |cₖ| ℒ¹(Iₖ ∩ γₖ⁻¹(A))`, since `H¹⌞Sₖ = γₖ#(ℒ¹⌞Iₖ)` and `Sₖ ⊆ M` when `cₖ ≠ 0`. -/
theorem Submission.idtp_fons_odc_pc_imrep_formulas : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, MeasurableSet (I k)) → ∀ R : IMRep (univ : Set (Euclid P)) 1, R.carrier = (⋃ k, ⋃ (_ : c k ≠ 0), (fun t : ℝ => p k + t • v k) '' I k) → (∀ x, R.mult x = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k).natAbs) x) → (∀ (x : Euclid P) (α : Covector (Euclid P) 1), (R.mult x : ℝ) * R.orient x α = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k)) → (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ k, (c k : ℝ) * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| * volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A) := by
  intro P ι _ p v I c hv hI R hC hmult horient
  -- `γₖ(t) = pₖ + t vₖ` is a measurable embedding, `H¹⌞γₖ(J) = γₖ#(ℒ¹⌞J)` and `H¹(γₖ(J)) = ℒ¹(J)`
  have hline := fun k => Submission.idtp_fons_odc_line_hausdorff.2 P (p k) (v k) (hv k)
  -- `Sₖ = γₖ(Iₖ)` is measurable, and `Sₖ ⊆ C` when `cₖ ≠ 0`
  have hS : ∀ k, MeasurableSet ((fun t : ℝ => p k + t • v k) '' I k) := fun k =>
    (hline k).1.measurableSet_image.mpr (hI k)
  have hSC : ∀ k, c k ≠ 0 → (fun t : ℝ => p k + t • v k) '' I k ⊆ R.carrier := fun k hk => by
    rw [hC]
    exact Set.subset_iUnion₂ (s := fun k (_ : c k ≠ 0) => (fun t : ℝ => p k + t • v k) '' I k) k hk
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- `1_{Sₖ}(x) cₖ ω(x)(vₖ)` is the indicator of `x ↦ cₖ ω(x)(vₖ)`
    have hmul : ∀ k x, ((fun t : ℝ => p k + t • v k) '' I k).indicator (fun _ => (c k : ℝ)) x *
        (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k) =
        ((fun t : ℝ => p k + t • v k) '' I k).indicator
          (fun x => (c k : ℝ) * (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k)) x :=
      fun k x => (Set.indicator_mul_left _ (fun _ => (c k : ℝ))
        (fun x => (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k))).symm
    -- `x ↦ ω(x)(vₖ)` is continuous with compact support along `γₖ`, hence `H¹`-integrable on `Sₖ`
    have hint : ∀ k, Integrable (fun x => ((fun t : ℝ => p k + t • v k) '' I k).indicator
        (fun _ => (c k : ℝ)) x * (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k))
        (μHE[1].restrict R.carrier) := by
      intro k
      have hiso : Isometry (fun t : ℝ => p k + t • v k) := Isometry.of_dist_eq fun s t => by
        show dist (p k + s • v k) (p k + t • v k) = dist s t
        rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv k, mul_one, Real.dist_eq,
          Real.norm_eq_abs]
      have hcont : Continuous fun t : ℝ =>
          (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) :=
        (continuous_eval_const (fun _ : Fin 1 => v k)).comp (ω.2.1.1.continuous.comp hiso.continuous)
      have hcs : HasCompactSupport fun t : ℝ =>
          (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) :=
        (ω.2.1.2.comp_isClosedEmbedding hiso.isClosedEmbedding).comp_left
          (g := fun α : Covector (Euclid P) 1 => α (fun _ => v k)) rfl
      have h1 : Integrable (fun x => (ω : DifferentialForm (Euclid P) 1) x (fun _ => v k))
          (μHE[1].restrict ((fun t : ℝ => p k + t • v k) '' I k)) := by
        rw [((hline k).2 (I k)).1, (hline k).1.integrable_map_iff]
        exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
      simp only [hmul k]
      rw [integrable_indicator_iff (hS k)]
      refine (h1.const_mul (c k : ℝ)).mono_measure ?_
      rw [Measure.restrict_restrict (hS k)]
      exact Measure.restrict_mono Set.inter_subset_left le_rfl
    show ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x)
      ∂μHE[1] = _
    simp only [horient]
    rw [integral_finsetSum _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hmul k]
    rw [integral_indicator (hS k), Measure.restrict_restrict (hS k), integral_const_mul]
    by_cases hk : c k = 0
    · simp [hk]
    · rw [Set.inter_eq_left.mpr (hSC k hk), ((hline k).2 (I k)).1, (hline k).1.integral_map]
  · -- `θ = Σₖ |cₖ| 1_{Sₖ}` as `ℝ≥0∞`-valued functions
    have hθ : ∀ x, ((R.mult x : ℕ) : ℝ≥0∞) = ∑ k, ((fun t : ℝ => p k + t • v k) '' I k).indicator
        (fun _ => ((c k).natAbs : ℝ≥0∞)) x := by
      intro x
      rw [hmult x, Nat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hx : x ∈ (fun t : ℝ => p k + t • v k) '' I k
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Nat.cast_zero]
    rw [IMRep.measure, withDensity_apply _ hA, Measure.restrict_restrict hA]
    simp only [hθ]
    rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hS k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lintegral_indicator_const (hS k), Measure.restrict_apply (hS k)]
    by_cases hk : c k = 0
    · simp [hk]
    · rw [Set.inter_comm A, ← Set.inter_assoc, Set.inter_eq_left.mpr (hSC k hk),
        ← Set.image_inter_preimage, ((hline k).2 _).2, ← ENNReal.ofReal_natCast, Nat.cast_natAbs,
        Int.cast_abs]

/-- **Polygonal integer multiplicity 1-currents** (Simon Ch. 6, 3.1–3.2; used for the
1-dimensional minimizing cones `S₀ = m[[ℓ]]` in the proof of 7.3.3, (10)).  Finitely many
oriented open line pieces `S_k = γ_k(I_k)`, `γ_k(t) = p_k + t v_k` (`‖v_k‖ = 1`, `I_k` open),
with integer weights `c_k` and `H¹`-null overlaps `S_j ∩ closure S_k` (`j ≠ k`), define the
current `X(ω) = Σ_k c_k ∫_{I_k} ω(γ_k t)(v_k) dt`.  It is represented by the triple
`R = (⋃_{c_k ≠ 0} S_k, Σ_k 1_{S_k}|c_k|, ξ)` with `θξ(α) = Σ_k 1_{S_k} c_k α(v_k)`, whose
mass measure is `R.measure A = Σ_k |c_k| ℒ¹(I_k ∩ γ_k⁻¹A)`. -/
theorem Submission.idtp_fons_odc_polygonal_current : ∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, IsOpen (I k)) → (∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p j + t • v j) '' I j) ∩ closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) → ∃ (X : GeometricCurrentOn (univ : Set (Euclid P)) 1) (R : IMRep (univ : Set (Euclid P)) 1), R.Represents X ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω = ∑ k, (c k : ℝ) * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| * volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A) := by
  intro P ι hι p v I c hv hI hnull
  -- Step 1: the weighted line-integral current `X`, with real weights `(c k : ℝ)`.
  obtain ⟨X, hX⟩ := Submission.idtp_fons_odc_pc_line_current P ι p v I (fun k => (c k : ℝ)) hv
  -- Steps 2–3: the triple `R = (⋃_{c_k ≠ 0} S_k, Σ_k 1_{S_k}|c_k|, ξ)`.
  obtain ⟨R, hcar, hmult, hθξ⟩ := Submission.idtp_fons_odc_pc_imrep P ι p v I c hv hI hnull
  -- Steps 4–5: the action and the mass measure of `R`.
  obtain ⟨hact, hmeas⟩ := Submission.idtp_fons_odc_pc_imrep_formulas P ι p v I c hv
    (fun k => (hI k).measurableSet) R hcar hmult hθξ
  -- `R.Represents X` is `∀ ω, X ω = R.action ω`; both sides equal the weighted sum.
  exact ⟨X, R, fun ω => (hX ω).trans (hact ω).symm, hX, hmeas⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
