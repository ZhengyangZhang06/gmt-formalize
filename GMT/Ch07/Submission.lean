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

/-- **Simon Ch. 3, Definition 1.4 and Remark 1.5(1)**: an approximate tangent space of `M` at `x`
lies in every subspace `T` along which a set `N` carrying `Hⁿ`-almost all of `M` is flat at `x`
(for each `ε > 0` there is `ρ > 0` such that every `z ∈ N` with `|z − x| < ρ` has some `t ∈ T`
with `|z − x − t| ≤ ε|z − x|`).  If `q ∈ Q \ T`, put `δ = dist(q, T) > 0` and
`g = max(0, δ/2 − |· − q|) ∈ C_c(ℝᴾ)`; `∫_Q g dHⁿ > 0` because `spt(Hⁿ⌞Q) = Q`.  With
`ε = δ / (2(|q| + δ))` and `0 < r < ρ / (|q| + δ)`, flatness makes `g` vanish on `η_{x,r}(M ∩ N)`,
and `Hⁿ(η_{x,r}(M \ N)) = 0`; so `∫_{η_{x,r}(M)} g dHⁿ = 0` for all small `r`, contradicting
the defining limit. -/
theorem Submission.atsm_approxTangent_le_of_flat : ∀ (P n : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q T : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z x < ρ → ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → HasApproximateTangentSpaceAt n M x Q → Q ≤ T := by
  intro P n N M x Q T hnull hflat hQ q hq
  by_contra hqT
  -- `T` is closed, so `δ = dist(q, T) > 0`
  have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
  have hδ : 0 < infDist q (T : Set (Euclid P)) :=
    (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
  set δ := infDist q (T : Set (Euclid P)) with hδdef
  -- the bump `g = max(0, δ/2 − |· − q|)`, positive exactly on `B_{δ/2}(q)`
  set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg0 : 0 ≤ g := fun y => le_max_left _ _
  have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
    intro y hy
    by_contra h
    have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
    apply hy
    exact max_eq_left (by linarith)
  have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
    lt_max_of_lt_right (by linarith)
  have hgcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
    intro y hy
    by_contra h
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgsupp y h).le
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hgc⟩, hgcs⟩
  -- `∫_Q g dHⁿ > 0`: `Hⁿ⌞Q` is regular with support `Q ∋ q`
  have hQn : Module.finrank ℝ Q = n := hQ.1
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
  have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
  have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    hgc.integrable_of_hasCompactSupport hgcs
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
      rw [hsupp]
      exact hq
    have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
        (ball q (δ / 2)) :=
      (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
    refine hball.trans_le (measure_mono ?_)
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (hgpos y hy).ne'
  -- constants: `ε (|q| + δ) = δ / 2`
  have hqδ : 0 < ‖q‖ + δ := by positivity
  set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεq : ε * (‖q‖ + δ) = δ / 2 := by
    rw [hεdef]
    field_simp
  obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
  -- `∫_{η_{x,r}(M)} g dHⁿ = 0` for `0 < r < ρ / (|q| + δ)`
  have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = 0 := by
    intro r hr hrρ
    -- `η_{x,r}(M \ N) = r⁻¹ (M \ N − x)` is `Hⁿ`-null
    have hnull' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N)) = 0 := by
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) =
          (fun y => r⁻¹ • y) '' ((fun y => y - x) '' (M \ N)) := by
        rw [Set.image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq fun a b => dist_sub_right a b x
      rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, hnull, smul_zero]
    -- flatness: `g` vanishes on `η_{x,r}(M ∩ N)`
    have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) := by
      rintro y ⟨hgy, z, hzM, rfl⟩
      refine ⟨z, ⟨hzM, fun hzN => ?_⟩, rfl⟩
      have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
      set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
      have hy' : y = r⁻¹ • (z - x) := rfl
      have hzx : z - x = r • y := by
        rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
        calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
          _ < δ / 2 + ‖q‖ := by linarith
          _ = ‖q‖ + δ / 2 := by ring
      have hzxn : ‖z - x‖ = r * ‖y‖ := by
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
      have hdist : dist z x < ρ := by
        rw [dist_eq_norm, hzxn]
        calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
          _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
          _ = ρ := by field_simp
      obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
      have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
      have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
        rw [hy']
        exact (smul_sub _ _ _).symm
      have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
        rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
          _ = ε * ‖y‖ := by rw [hzxn]; field_simp
      have hle : δ ≤ ‖q - r⁻¹ • t‖ := by
        rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hrt
      have h2 : ε * ‖y‖ ≤ δ / 2 := by
        rw [← hεq]
        gcongr
        linarith
      have hlt : ‖q - r⁻¹ • t‖ < δ := by
        calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
          _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := by
            have h1 : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
            linarith
          _ = δ := by ring
      linarith
    -- so `g = 0` a.e. for `Hⁿ⌞η_{x,r}(M)`, evaluated on the open set `{g ≠ 0}`
    have hopen : MeasurableSet {y | g y ≠ 0} :=
      (isOpen_ne_fun hgc continuous_const).measurableSet
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_iff]
    change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) {y | g y ≠ 0} = 0
    rw [Measure.restrict_apply hopen]
    exact measure_mono_null hsub hnull'
  -- the blow-up integrals of `g` are eventually `0`, so their limit `∫_Q g dHⁿ` is `0`
  have hlim := hQ.2 f
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n])
      =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
    exact hvan r hr.1 hr.2
  have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have heq := tendsto_nhds_unique hlim hlim0
  have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
  linarith
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

/-- **Simon 7.3.5** (chapter-07.txt lines 410–418: `∂S₀ = 0`, and `S₀` is a cone if `S` is; the
book leaves the proof to the reader).  Let `S = [[L]] × S₀`, i.e. `S(ω) = ∫_L S₀(♭ω(t + ·)) dHᵈ(t)`
with `♭α(v) = α(f₁, …, f_d, v₁, …, vₘ)` for an orthonormal frame `f` of `L`, `d = dim L`, where
`S₀ = τ(M₀, θ₀, ζ₀)` and `μ₀(ℝᴾ ∖ L⊥) = 0`.  Then `∂S = 0 ⇒ ∂S₀ = 0` and `S` a cone `⇒ S₀` a cone.
`Hᵐ(M₀ ∖ L⊥) = 0`, so the approximate tangent planes of `M₀` lie in the flat `L⊥`
(`atsm_approxTangent_le_of_flat`) and `S₀(γ)` only depends on `γ(y)(w)`, `y ∈ L⊥`, `w ∈ (L⊥)ᵐ`.
For a test form `β` let `Ω_β(x) = ϕ(px) · (f¹ ∧ ⋯ ∧ fᵈ ∧ β)(x − px)`, `p` the projection onto `L`,
`ϕ ≥ 0` a bump with `ϕ(0) > 0`, the wedge being a normalized alternatization.  On `L⊥`,
`♭Ω_β(t + y) = ϕ(t) β(y)` and, expanding `d` by `alternatizeUncurryFin`,
`♭dΩ_β(t + y) = (−1)ᵈ ϕ(t) dβ(y)`; with `c = ∫_L ϕ dHᵈ > 0` (`Hᵈ⌞L` is the volume of `L`),
`0 = S(dΩ_β) = (−1)ᵈ c S₀(dβ)`.  Dilations preserve `L` and `L⊥` and scale `Hᵈ⌞L` by `λᵈ`, so
`c S₀(β) = S(Ω_β) = S(η_{0,λ}^# Ω_β) = c S₀(η_{0,λ}^# β)`. -/
theorem Submission.dimred_cs_sos_boundary_cone_transfer : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)) (f : Fin (Module.finrank ℝ L) → Euclid P) (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (hd : Module.finrank ℝ L < n), 0 < Module.finrank ℝ L → Orthonormal ℝ f → (∀ i, f i ∈ L) → R₀.Represents S₀ → R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ flat : Covector (Euclid P) n → Covector (Euclid P) (n - Module.finrank ℝ L), (∀ (α : Covector (Euclid P) n) (v : Fin (n - Module.finrank ℝ L) → Euclid P), flat α v = α (Fin.append f v ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (L : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[Module.finrank ℝ L]) → (BoundaryVanishes S → BoundaryVanishes S₀) ∧ (IsConeCurrent S → IsConeCurrent S₀) := by
  intro P n S L
  generalize hdL : Module.finrank ℝ L = d
  intro f S₀ R₀ hd _hd0 hf hfL hR₀ hnull hPF
  -- write `n = d + m`, `m = m' + 1`, with `m` a variable
  have hPF' : ∀ (h : n = d + (n - d))
      (flat : Covector (Euclid P) n → Covector (Euclid P) (n - d)),
      (∀ (α : Covector (Euclid P) n) (v : Fin (n - d) → Euclid P),
        flat α v = α (Fin.append f v ∘ Fin.cast h)) →
      ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
        S ω = ∫ t in (L : Set (Euclid P)),
          currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[d] :=
    fun _ => hPF
  clear hPF
  have hnm : n = d + (n - d) := (Nat.add_sub_of_le hd.le).symm
  revert S₀ R₀ hR₀ hnull hPF' hnm
  generalize n - d = k
  intro S₀ R₀ hR₀ hnull hPF' hnm
  subst hnm
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hLc : IsClosed (L : Set (Euclid P)) := L.closed_of_finiteDimensional
  have hLm : MeasurableSet (L : Set (Euclid P)) := hLc.measurableSet
  have hfperp : ∀ a, ∀ y ∈ Lᗮ, inner ℝ (f a) y = 0 := fun a y hy =>
    Submodule.inner_right_of_mem_orthogonal (hfL a) hy
  -- `p` is the orthogonal projection onto `L`
  obtain ⟨p, hpL, hpLp⟩ : ∃ p : Euclid P →L[ℝ] Euclid P, (∀ t ∈ L, p t = t) ∧
      ∀ y ∈ Lᗮ, p y = 0 :=
    ⟨L.starProjection, fun t ht => Submodule.starProjection_eq_self_iff.mpr ht,
      fun y hy => (Submodule.starProjection_apply_eq_zero_iff L).mpr hy⟩
  have hpsplit : ∀ t ∈ L, ∀ y ∈ Lᗮ, p (t + y) = t := fun t ht y hy => by
    rw [map_add, hpL t ht, hpLp y hy, add_zero]
  -- a bump `ϕ ≥ 0` with `ϕ(0) > 0`
  obtain ⟨ϕ, hϕs, hϕc, hϕn, hϕ0⟩ : ∃ ϕ : Euclid P → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϕ ∧ HasCompactSupport ϕ ∧ (∀ x, 0 ≤ ϕ x) ∧ 0 < ϕ 0 := by
    let b : ContDiffBump (0 : Euclid P) := ⟨1, 2, zero_lt_one, one_lt_two⟩
    refine ⟨b, b.contDiff, b.hasCompactSupport, fun x => b.nonneg, ?_⟩
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    exact one_pos
  -- `Hᵈ⌞L` is the volume of `L`; `cϕ = ∫_L ϕ dHᵈ > 0` is invariant under dilations
  have hint : ∀ g : Euclid P → ℝ,
      ∫ t in (L : Set (Euclid P)), g t ∂μHE[d] = ∫ x : L, g x := by
    intro g
    have hmap : (μHE[d] : Measure (Euclid P)).restrict (L : Set (Euclid P)) =
        Measure.map (Subtype.val : L → Euclid P) volume := by
      rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, hdL,
        isometry_subtype_coe.map_euclideanHausdorffMeasure, Subtype.range_coe_subtype]
      rfl
    rw [hmap]
    exact (MeasurableEmbedding.subtype_coe hLm).integral_map g
  obtain ⟨cϕ, hcϕ_eq⟩ : ∃ c : ℝ, ∫ x : L, ϕ x = c := ⟨_, rfl⟩
  have hcϕ : 0 < cϕ := by
    rw [← hcϕ_eq]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (hϕs.continuous.comp continuous_subtype_val)
      (hϕc.comp_isClosedEmbedding hLc.isClosedEmbedding_subtypeVal) (fun x => hϕn _) ?_
    simpa using hϕ0.ne'
  -- `μ₀(ℝᴾ ∖ L⊥) = 0` gives `Hᵐ⁺¹(M₀ ∖ L⊥) = 0`, since `θ₀ > 0` on `M₀`
  have hnull' : μHE[m + 1] (R₀.carrier \ (Lᗮ : Set (Euclid P))) = 0 := by
    have hθ : AEMeasurable (fun x => (R₀.mult x : ℝ≥0∞)) (μHE[m + 1].restrict R₀.carrier) :=
      (measurable_from_nat.comp R₀.measurable_mult).aemeasurable
    have h := (withDensity_apply_eq_zero' hθ).mp hnull
    rw [Measure.restrict_apply' R₀.measurableSet_carrier] at h
    refine measure_mono_null (fun x hx => ?_) h
    refine ⟨⟨?_, hx.2⟩, hx.1⟩
    simpa using (R₀.mult_pos x hx.1).ne'
  -- Step 1: `S₀(γ)` only depends on `γ(y)(w)` for `y ∈ L⊥`, `w ∈ (L⊥)ᵐ⁺¹`: the approximate
  -- tangent planes of `M₀` lie in the flat `L⊥` (`atsm_approxTangent_le_of_flat`)
  have hclaim1 : ∀ γ γ' : TestFormOn (univ : Set (Euclid P)) (m + 1),
      (∀ y ∈ Lᗮ, ∀ w : Fin (m + 1) → Euclid P, (∀ i, w i ∈ Lᗮ) →
        (γ : DifferentialForm (Euclid P) (m + 1)) y w =
          (γ' : DifferentialForm (Euclid P) (m + 1)) y w) →
      S₀ γ = S₀ γ' := by
    intro γ γ' hγ
    rw [hR₀ γ, hR₀ γ', IMRep.action, IMRep.action]
    refine integral_congr_ae ?_
    have hae : ∀ᵐ x ∂(μHE[m + 1].restrict R₀.carrier), x ∈ Lᗮ := by
      rw [ae_restrict_iff' R₀.measurableSet_carrier, ae_iff]
      refine measure_mono_null (fun x hx => ?_) hnull'
      simp only [Set.mem_ofPred_eq, not_imp] at hx
      exact hx
    filter_upwards [hae, R₀.orients] with x hxL hx
    obtain ⟨Q, hQ, τ, -, hspan, hξ⟩ := hx
    have hQL : Q ≤ Lᗮ :=
      Submission.atsm_approxTangent_le_of_flat P (m + 1) (Lᗮ : Set (Euclid P)) R₀.carrier x Q Lᗮ
        hnull' (fun ε hε => ⟨1, one_pos, fun z hz _ => ⟨z - x, Lᗮ.sub_mem hz hxL, by
          rw [sub_self, norm_zero]; positivity⟩⟩) hQ
    have hτL : ∀ i, τ i ∈ Lᗮ := fun i =>
      hQL (hspan ▸ Submodule.subset_span (Set.mem_range_self i))
    have h := hγ x hxL τ hτL
    rcases hξ with h' | h' <;> simp only [h', h]
  -- Step 0: the interior product `♭α(v) = α(f₁, …, f_d, v₁, …, vₘ₊₁)`, continuous linear in `α`
  obtain ⟨flat, hflat⟩ : ∃ flat : Covector (Euclid P) (d + (m + 1)) →L[ℝ] Covector (Euclid P) (m + 1),
      ∀ α v, flat α v = α (Fin.append f v) := by
    have happ : ∀ v : Fin (m + 1) → Euclid P,
        (fun i => Sum.elim f v (finSumFinEquiv.symm i)) = Fin.append f v := by
      intro v
      funext i
      refine Fin.addCases (fun a => ?_) (fun j => ?_) i
      · rw [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Fin.append_left]
      · rw [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Fin.append_right]
    let flat0 : Covector (Euclid P) (d + (m + 1)) → Covector (Euclid P) (m + 1) := fun α =>
      { toContinuousMultilinearMap :=
          (α.toContinuousMultilinearMap.domDomCongr finSumFinEquiv.symm).currySum f
        map_eq_zero_of_eq' := fun v i j hij hne => by
          change (α.toContinuousMultilinearMap.domDomCongr finSumFinEquiv.symm).currySum f v = 0
          rw [ContinuousMultilinearMap.currySum_apply, ContinuousMultilinearMap.domDomCongr_apply,
            happ v]
          exact α.map_eq_zero_of_eq (Fin.append f v) (i := Fin.natAdd d i) (j := Fin.natAdd d j)
            (by rw [Fin.append_right, Fin.append_right, hij])
            (fun h => hne (Fin.natAdd_inj d |>.mp h)) }
    have hflat0 : ∀ α v, flat0 α v = α (Fin.append f v) := by
      intro α v
      show (α.toContinuousMultilinearMap.domDomCongr finSumFinEquiv.symm).currySum f v = _
      rw [ContinuousMultilinearMap.currySum_apply, ContinuousMultilinearMap.domDomCongr_apply,
        happ]
      rfl
    have hadd : ∀ α β, flat0 (α + β) = flat0 α + flat0 β := fun α β => by
      ext v
      simp only [hflat0, ContinuousAlternatingMap.add_apply]
    have hsmul : ∀ (c : ℝ) α, flat0 (c • α) = c • flat0 α := fun c α => by
      ext v
      simp only [hflat0, ContinuousAlternatingMap.smul_apply]
    have := Submission.lcn_covector_finiteDimensional P (d + (m + 1))
    exact ⟨LinearMap.toContinuousLinearMap ⟨⟨flat0, hadd⟩, hsmul⟩, hflat0⟩
  have hS : ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + (m + 1)),
      S ω = ∫ t in (L : Set (Euclid P)), currentEval S₀
        (fun y => flat ((ω : DifferentialForm (Euclid P) (d + (m + 1))) (t + y))) ∂μHE[d] :=
    hPF' rfl flat (fun α v => by rw [hflat]; rfl)
  -- the slices `y ↦ ♭F(t + y)` of a test form `F` are test forms, and `S₀` evaluates them
  -- through any test form agreeing with them on `L⊥ × (L⊥)ᵐ⁺¹`
  have hslice : ∀ (F : DifferentialForm (Euclid P) (d + (m + 1))) (hF : IsTestForm F)
      (t : Euclid P) (G : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      (∀ y ∈ Lᗮ, ∀ w : Fin (m + 1) → Euclid P, (∀ i, w i ∈ Lᗮ) →
        F (t + y) (Fin.append f w) = (G : DifferentialForm (Euclid P) (m + 1)) y w) →
      currentEval S₀ (fun y => flat (F (t + y))) = S₀ G := by
    intro F hF t G hFG
    have hsl : IsTestForm (fun y => flat (F (t + y))) :=
      ⟨flat.contDiff.comp (hF.1.comp (contDiff_const.add contDiff_id)),
        (hF.2.comp_homeomorph (Homeomorph.addLeft t)).comp_left (map_zero flat)⟩
    rw [currentEval, dite_eq_left ⟨hsl, subset_univ _⟩]
    refine hclaim1 _ _ fun y hy w hw => ?_
    rw [← hFG y hy w hw]
    exact hflat _ _
  -- Step 2: the forms `Ω_β(x) = ϕ(p x) · lift(β(x − p x))` are test forms
  have hΩtest : ∀ (k k' : ℕ) (lift : Covector (Euclid P) k →L[ℝ] Covector (Euclid P) k')
      (β : DifferentialForm (Euclid P) k), IsTestForm β →
      IsTestForm (fun x => ϕ (p x) • lift (β (x - p x))) := by
    intro k k' lift β hβ
    refine ⟨(hϕs.comp p.contDiff).smul
      (lift.contDiff.comp (hβ.1.comp (contDiff_id.sub p.contDiff))), ?_⟩
    obtain ⟨R₁, hR₁⟩ := hϕc.isCompact.isBounded.subset_closedBall 0
    obtain ⟨R₂, hR₂⟩ := hβ.2.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (K := closedBall 0 (R₁ + R₂)) (isCompact_closedBall _ _)
      fun x hx => ?_
    by_cases h1 : p x ∈ tsupport ϕ
    · by_cases h2 : x - p x ∈ tsupport β
      · refine absurd ?_ hx
        rw [mem_closedBall_zero_iff]
        calc ‖x‖ = ‖p x + (x - p x)‖ := by rw [add_sub_cancel]
          _ ≤ ‖p x‖ + ‖x - p x‖ := norm_add_le _ _
          _ ≤ R₁ + R₂ := add_le_add (mem_closedBall_zero_iff.mp (hR₁ h1))
            (mem_closedBall_zero_iff.mp (hR₂ h2))
      · rw [image_eq_zero_of_notMem_tsupport h2, map_zero, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_smul]
  -- the lift `β ↦ f¹ ∧ ⋯ ∧ fᵈ ∧ β`, the normalized alternatization of `Π(u ∘ castAdd)·β(u ∘ natAdd)`:
  -- (L1) `lift β (f, w) = β(w)` for `w ∈ (L⊥)ᵏ`; (L2) `lift β u = 0` if some `fₐ ⊥ u`
  have hlift : ∀ k : ℕ, ∃ lift : Covector (Euclid P) k →L[ℝ] Covector (Euclid P) (d + k),
      (∀ (B : Covector (Euclid P) k) (w : Fin k → Euclid P), (∀ i, w i ∈ Lᗮ) →
        lift B (Fin.append f w) = B w) ∧
      (∀ (B : Covector (Euclid P) k) (u : Fin (d + k) → Euclid P) (a : Fin d),
        (∀ l, inner ℝ (f a) (u l) = 0) → lift B u = 0) := by
    intro k
    let Pm : ContinuousMultilinearMap ℝ (fun _ : Fin d => Euclid P) ℝ :=
      (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin d) ℝ).compContinuousLinearMap
        fun a => innerSL ℝ (f a)
    let M : Covector (Euclid P) k →
        ContinuousMultilinearMap ℝ (fun _ : Fin (d + k) => Euclid P) ℝ := fun B =>
      ((Pm.smulRight B.toContinuousMultilinearMap).uncurrySum).domDomCongr finSumFinEquiv
    have hM : ∀ B u, M B u =
        (∏ a, inner ℝ (f a) (u (Fin.castAdd k a))) * B (fun j => u (Fin.natAdd d j)) := by
      intro B u
      simp only [M, Pm, ContinuousMultilinearMap.domDomCongr_apply,
        ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.smulRight_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply,
        finSumFinEquiv_apply_left]
      rfl
    have hMadd : ∀ B B', M (B + B') = M B + M B' := fun B B' => by
      ext u
      simp only [hM, add_apply, ContinuousAlternatingMap.add_apply, mul_add]
    have hMsmul : ∀ (c : ℝ) B, M (c • B) = c • M B := fun c B => by
      ext u
      simp only [hM, smul_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul]
      ring
    have halt : ∀ (c : ℝ) (N : ContinuousMultilinearMap ℝ (fun _ : Fin (d + k) => Euclid P) ℝ),
        ContinuousMultilinearMap.alternatization (c • N) =
          c • ContinuousMultilinearMap.alternatization N := fun c N => by
      ext u
      simp only [ContinuousMultilinearMap.alternatization_apply_apply,
        smul_apply, ContinuousAlternatingMap.smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun σ _ => smul_comm _ _ _
    let lift0 : Covector (Euclid P) k → Covector (Euclid P) (d + k) := fun B =>
      ((k.factorial : ℝ)⁻¹) • ContinuousMultilinearMap.alternatization (M B)
    have hladd : ∀ B B', lift0 (B + B') = lift0 B + lift0 B' := fun B B' => by
      simp only [lift0, hMadd, map_add, smul_add]
    have hlsmul : ∀ (c : ℝ) B, lift0 (c • B) = c • lift0 B := fun c B => by
      simp only [lift0, hMsmul, halt, smul_comm c]
    have hlift0 : ∀ B u, lift0 B u =
        (k.factorial : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (d + k)), Equiv.Perm.sign σ • M B (u ∘ σ) := by
      intro B u
      simp only [lift0, ContinuousAlternatingMap.smul_apply,
        ContinuousMultilinearMap.alternatization_apply_apply, smul_eq_mul]
    have := Submission.lcn_covector_finiteDimensional P k
    refine ⟨LinearMap.toContinuousLinearMap ⟨⟨lift0, hladd⟩, hlsmul⟩, ?_, ?_⟩
    · -- (L1): only the permutations fixing `1, …, d` contribute, each `β(w)`
      intro B w hw
      show lift0 B (Fin.append f w) = B w
      rw [hlift0]
      -- `π ↦ id_d ⊕ π`
      let ι : Equiv.Perm (Fin k) → Equiv.Perm (Fin (d + k)) := fun π =>
        finSumFinEquiv.permCongr (Equiv.Perm.sumCongr 1 π)
      have hιc : ∀ π a, ι π (Fin.castAdd k a) = Fin.castAdd k a := by
        intro π a
        simp [ι, Equiv.permCongr_apply]
      have hιn : ∀ π j, ι π (Fin.natAdd d j) = Fin.natAdd d (π j) := by
        intro π j
        simp [ι, Equiv.permCongr_apply]
      have hιinj : Function.Injective ι := by
        intro π π' h
        ext j
        have h' := congrArg (fun σ : Equiv.Perm (Fin (d + k)) => σ (Fin.natAdd d j)) h
        simp only [hιn] at h'
        exact congrArg Fin.val ((Fin.natAdd_inj d).mp h')
      have hsum : ∑ σ : Equiv.Perm (Fin (d + k)), Equiv.Perm.sign σ • M B (Fin.append f w ∘ σ) =
          ∑ _π : Equiv.Perm (Fin k), B w := by
        symm
        refine Fintype.sum_of_injective ι hιinj _ _ (fun σ hσ => ?_) (fun π => ?_)
        · by_cases hfix : ∀ a, σ (Fin.castAdd k a) = Fin.castAdd k a
          · -- `σ` fixes `1, …, d`, so `σ = ι π`
            refine absurd ?_ hσ
            let τ := finSumFinEquiv.symm.permCongr σ
            have hτ : MapsTo τ (range Sum.inl) (range Sum.inl) := by
              rintro _ ⟨a, rfl⟩
              exact ⟨a, by simp [τ, Equiv.permCongr_apply, hfix]⟩
            obtain ⟨⟨σ₁, σ₂⟩, h12⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hτ
            refine ⟨σ₂, Equiv.ext fun i => ?_⟩
            refine Fin.addCases (fun a => ?_) (fun j => ?_) i
            · rw [hιc, hfix]
            · rw [hιn]
              have h' := congrArg (fun τ' : Equiv.Perm (Fin d ⊕ Fin k) => τ' (Sum.inr j)) h12
              simp only [Equiv.Perm.sumCongrHom_apply, Equiv.Perm.sumCongr_apply, Sum.map_inr,
                τ, Equiv.permCongr_apply, Equiv.symm_symm, finSumFinEquiv_apply_right] at h'
              rw [← finSumFinEquiv_apply_right, h', Equiv.apply_symm_apply]
          · -- some `σ(a) ≠ a`, `a ≤ d`: the factor `⟨fₐ, (f, w)_{σ(a)}⟩` vanishes
            push Not at hfix
            obtain ⟨a, ha⟩ := hfix
            rw [hM, Finset.prod_eq_zero (Finset.mem_univ a), zero_mul, smul_zero]
            show inner ℝ (f a) (Fin.append f w (σ (Fin.castAdd k a))) = 0
            revert ha
            generalize σ (Fin.castAdd k a) = i
            refine Fin.addCases (fun b hb => ?_) (fun j _ => ?_) i
            · rw [Fin.append_left]
              exact hf.2 fun h => hb (h ▸ rfl)
            · rw [Fin.append_right]
              exact hfperp a (w j) (hw j)
        · -- `ι π` contributes `sgn π · β(w ∘ π) = β(w)`
          rw [hM]
          have h1 : ∏ a, inner ℝ (f a) ((Fin.append f w ∘ ι π) (Fin.castAdd k a)) = 1 := by
            refine Finset.prod_eq_one fun a _ => ?_
            rw [Function.comp_apply, hιc, Fin.append_left, real_inner_self_eq_norm_sq, hf.1 a,
              one_pow]
          have h2 : (fun j => (Fin.append f w ∘ ι π) (Fin.natAdd d j)) = w ∘ π := by
            funext j
            rw [Function.comp_apply, hιn, Fin.append_right, Function.comp_apply]
          have h3 := B.toAlternatingMap.map_perm w π
          rw [ContinuousAlternatingMap.coe_toAlternatingMap] at h3
          rw [h1, one_mul, h2, h3, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
            Equiv.Perm.sign_one, one_mul, smul_smul, Int.units_mul_self, one_smul]
      rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    · -- (L2): every term has a factor `⟨fₐ, u_{σ(a)}⟩ = 0`
      intro B u a hu
      show lift0 B u = 0
      rw [hlift0, Finset.sum_eq_zero, mul_zero]
      intro σ _
      rw [hM, Finset.prod_eq_zero (Finset.mem_univ a) (hu _), zero_mul, smul_zero]
  refine ⟨fun hSb => ?_, fun hSc => ?_⟩
  · -- Step 3: `∂S = 0 ⇒ ∂S₀ = 0`
    obtain ⟨lift, hL1, hL2⟩ := hlift m
    have hSb' : (S : GeometricCurrentOn (univ : Set (Euclid P)) (d + m + 1)).boundary = 0 := hSb
    show S₀.boundary = 0
    ext β
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply]
    have hβ : IsTestForm (β : DifferentialForm (Euclid P) m) := β.property.1
    obtain ⟨Ω, hΩ_eq⟩ : ∃ Ω : DifferentialForm (Euclid P) (d + m),
        Ω = fun x => ϕ (p x) • lift ((β : DifferentialForm (Euclid P) m) (x - p x)) := ⟨_, rfl⟩
    have hΩ : IsTestForm Ω := hΩ_eq ▸ hΩtest m (d + m) lift _ hβ
    -- `DΩ(x)[h] = ϕ(px) lift(Dβ(qx)[qh]) + Dϕ(px)[ph] lift(β(qx))`, `q = I − p`
    have hderiv : ∀ x h, fderiv ℝ Ω x h =
        ϕ (p x) • lift (fderiv ℝ (β : DifferentialForm (Euclid P) m) (x - p x) (h - p h)) +
          (fderiv ℝ ϕ (p x) (p h)) • lift ((β : DifferentialForm (Euclid P) m) (x - p x)) := by
      intro x h
      have hc : HasFDerivAt (fun y => ϕ (p y)) ((fderiv ℝ ϕ (p x)).comp p) x :=
        (hϕs.differentiable (by simp) (p x)).hasFDerivAt.comp x p.hasFDerivAt
      have hq : HasFDerivAt (fun y : Euclid P => y - p y)
          (ContinuousLinearMap.id ℝ (Euclid P) - p) x :=
        (hasFDerivAt_id x).sub p.hasFDerivAt
      have hb : HasFDerivAt (fun y => lift ((β : DifferentialForm (Euclid P) m) (y - p y)))
          (lift.comp ((fderiv ℝ (β : DifferentialForm (Euclid P) m) (x - p x)).comp
            (ContinuousLinearMap.id ℝ (Euclid P) - p))) x :=
        lift.hasFDerivAt.comp x ((hβ.1.differentiable (by simp) (x - p x)).hasFDerivAt.comp x hq)
      have hΩd : HasFDerivAt (fun y => ϕ (p y) • lift ((β : DifferentialForm (Euclid P) m) (y - p y)))
          _ x := hc.smul hb
      rw [hΩ_eq, hΩd.fderiv]
      rfl
    -- `dΩ(x)(f, w) = (−1)ᵈ ϕ(px) dβ(qx)(w)` for `w ∈ (L⊥)ᵐ⁺¹`
    have hkey : ∀ x (w : Fin (m + 1) → Euclid P), (∀ i, w i ∈ Lᗮ) →
        exteriorDerivative Ω x (Fin.append f w : Fin (d + (m + 1)) → Euclid P) =
          (-1 : ℝ) ^ d * (ϕ (p x) *
            exteriorDerivative (β : DifferentialForm (Euclid P) m) (x - p x) w) := by
      intro x w hw
      have hsplit : ∀ F : Fin (d + m + 1) → ℝ, ∑ i, F i =
          ∑ a : Fin d, F (Fin.castAdd (m + 1) a) + ∑ j : Fin (m + 1), F (Fin.natAdd d j) :=
        fun F => Fin.sum_univ_add (a := d) (b := m + 1) F
      -- the terms `i = a ≤ d` vanish by (L2)
      have hterm_c : ∀ a : Fin d, (fderiv ℝ Ω x
          ((Fin.append f w : Fin (d + (m + 1)) → Euclid P) (Fin.castAdd (m + 1) a)))
          (Fin.removeNth (n := d + m) (Fin.castAdd (m + 1) a)
            (Fin.append f w : Fin (d + (m + 1)) → Euclid P)) = 0 := by
        intro a
        have hu : ∀ l, inner ℝ (f a)
            (Fin.removeNth (n := d + m) (Fin.castAdd (m + 1) a)
              (Fin.append f w : Fin (d + (m + 1)) → Euclid P) l) = 0 := by
          intro l
          have hne := Fin.succAbove_ne (Fin.castAdd (m + 1) a : Fin (d + m + 1)) l
          rw [Fin.removeNth]
          revert hne
          generalize (Fin.castAdd (m + 1) a : Fin (d + m + 1)).succAbove l = i
          refine Fin.addCases (m := d) (n := m + 1) (fun b hb => ?_) (fun j _ => ?_) i
          · rw [Fin.append_left]
            exact hf.2 fun h => hb (h ▸ rfl)
          · rw [Fin.append_right]
            exact hfperp a (w j) (hw j)
        rw [hderiv, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
          ContinuousAlternatingMap.smul_apply, hL2 _ _ a hu, hL2 _ _ a hu, smul_zero, smul_zero,
          add_zero]
      -- `(f, w)` with `w_j` removed is `(f, ŵ_j)`
      have hrem : ∀ j : Fin (m + 1), Fin.removeNth (n := d + m) (Fin.natAdd d j)
          (Fin.append f w : Fin (d + (m + 1)) → Euclid P) =
            (Fin.append f (Fin.removeNth j w) : Fin (d + m) → Euclid P) := by
        intro j
        funext l
        refine Fin.addCases (fun b => ?_) (fun l' => ?_) l
        · have h' : (Fin.natAdd d j : Fin (d + m + 1)).succAbove (Fin.castAdd m b) =
              Fin.castAdd (m + 1) b :=
            Fin.succAbove_of_castSucc_lt _ _
              (Fin.lt_def.mpr (Nat.lt_of_lt_of_le b.isLt (Nat.le_add_right _ _)))
          rw [Fin.removeNth, h', Fin.append_left, Fin.append_left]
        · have hlt : (Fin.natAdd d l' : Fin (d + m)).castSucc < (Fin.natAdd d j : Fin (d + m + 1)) ↔
              l'.castSucc < j := by
            rw [Fin.lt_def, Fin.lt_def]
            exact Nat.add_lt_add_iff_left
          have h' : (Fin.natAdd d j : Fin (d + m + 1)).succAbove (Fin.natAdd d l') =
              Fin.natAdd d (j.succAbove l') := by
            by_cases h : l'.castSucc < j
            · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.succAbove_of_castSucc_lt _ _ (hlt.mpr h)]
              rfl
            · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.mp h),
                Fin.succAbove_of_le_castSucc _ _ (not_lt.mp (mt hlt.mp h))]
              rfl
          rw [Fin.removeNth, h', Fin.append_right, Fin.append_right, Fin.removeNth]
      -- the terms `i = d + j` give `ϕ(px) Dβ(qx)[w_j](ŵ_j)` by (L1), as `p w_j = 0`
      have hterm_n : ∀ j : Fin (m + 1), (fderiv ℝ Ω x
          ((Fin.append f w : Fin (d + (m + 1)) → Euclid P) (Fin.natAdd d j)))
          (Fin.removeNth (n := d + m) (Fin.natAdd d j)
            (Fin.append f w : Fin (d + (m + 1)) → Euclid P)) =
            ϕ (p x) * (fderiv ℝ (β : DifferentialForm (Euclid P) m) (x - p x) (w j))
              (Fin.removeNth j w) := by
        intro j
        rw [Fin.append_right, hrem, hderiv, hpLp _ (hw j), sub_zero, map_zero, zero_smul,
          add_zero, ContinuousAlternatingMap.smul_apply, hL1 _ (Fin.removeNth j w) fun l => hw _,
          smul_eq_mul]
      show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ Ω x)
          (Fin.append f w : Fin (d + (m + 1)) → Euclid P) =
        (-1 : ℝ) ^ d * (ϕ (p x) * ContinuousAlternatingMap.alternatizeUncurryFin
          (fderiv ℝ (β : DifferentialForm (Euclid P) m) (x - p x)) w)
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        ContinuousAlternatingMap.alternatizeUncurryFin_apply, hsplit]
      simp only [hterm_c, hterm_n, smul_zero, Finset.sum_const_zero, zero_add, Fin.val_natAdd,
        zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    -- by Step 1, `S₀(♭dΩ(t + ·)) = (−1)ᵈ ϕ(t) S₀(dβ)`; integrate over `L`
    have hdΩ : IsTestForm (exteriorDerivative Ω) := exteriorDerivative_isTestForm hΩ
    have hsl_eq : ∀ t ∈ L, currentEval S₀ (fun y => flat (exteriorDerivative Ω (t + y))) =
        ϕ t * ((-1 : ℝ) ^ d * S₀ (exteriorDerivativeTestOn univ m β)) := by
      intro t ht
      rw [hslice _ hdΩ t (((-1 : ℝ) ^ d * ϕ t) • exteriorDerivativeTestOn univ m β)
        fun y hy w hw => ?_, map_smul, smul_eq_mul]
      · ring
      rw [hkey (t + y) w hw, hpsplit t ht y hy, add_sub_cancel_left]
      show _ = ((-1 : ℝ) ^ d * ϕ t) * exteriorDerivative (β : DifferentialForm (Euclid P) m) y w
      ring
    have h1 := hS (exteriorDerivativeTestOn univ (d + m) ⟨Ω, hΩ, subset_univ _⟩)
    have h0 : S (exteriorDerivativeTestOn univ (d + m) ⟨Ω, hΩ, subset_univ _⟩) = 0 := by
      have h := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) (d + m) =>
        T ⟨Ω, hΩ, subset_univ _⟩) hSb'
      exact h
    have h2 : (∫ t in (L : Set (Euclid P)),
        currentEval S₀ (fun y => flat (exteriorDerivative Ω (t + y))) ∂μHE[d]) =
          cϕ * ((-1 : ℝ) ^ d * S₀ (exteriorDerivativeTestOn univ m β)) := by
      rw [setIntegral_congr_fun hLm fun t ht => hsl_eq t ht, integral_mul_const, hint, hcϕ_eq]
    have h3 := h0.symm.trans (h1.trans h2)
    rcases mul_eq_zero.mp h3.symm with h | h
    · exact absurd h hcϕ.ne'
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      · exact h'
  · -- Step 4: cones
    obtain ⟨lift, hL1, -⟩ := hlift (m + 1)
    intro lam hlam β
    have hβ : IsTestForm (β : DifferentialForm (Euclid P) (m + 1)) := β.property.1
    have hprop : IsProperMap (fun x : Euclid P => -(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam x) := by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
        (Homeomorph.addLeft (-(lam⁻¹ • (0 : Euclid P))))).isProperMap using 1
      funext y
      simp [dilationCLM]
    -- `η^#γ(x)(v) = λ⁻ᵏ γ(λ⁻¹x)(v)`
    have hη : ∀ (k : ℕ) (γ : DifferentialForm (Euclid P) k) (x : Euclid P) (v : Fin k → Euclid P),
        affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • (0 : Euclid P))) γ x v =
          lam⁻¹ ^ k * γ (lam⁻¹ • x) v := by
      intro k γ x v
      simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
        dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_zero,
        neg_zero, zero_add, Function.comp_def]
      rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    -- `currentEval (η_{0,λ#}T) γ = T(η^#γ)`
    have hblow : ∀ (k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) k)
        (γ : TestFormOn (univ : Set (Euclid P)) k),
        currentEval (blowUp T 0 lam hlam.ne') (γ : DifferentialForm (Euclid P) k) =
          T ⟨affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • (0 : Euclid P)))
            (γ : DifferentialForm (Euclid P) k),
            affinePullbackForm_isTestForm _ _ hprop γ.property.1, subset_univ _⟩ := by
      intro k T γ
      have hsurj : tsupport (γ : DifferentialForm (Euclid P) k) ⊆ dilation 0 lam '' univ :=
        fun y _ => ⟨lam • y, mem_univ _, by simp [dilation, dilationCLM, hlam.ne']⟩
      rw [currentEval, dite_eq_left ⟨γ.property.1, hsurj⟩]
      rfl
    obtain ⟨Ω, hΩ_eq⟩ : ∃ Ω : DifferentialForm (Euclid P) (d + (m + 1)),
        Ω = fun x => ϕ (p x) • lift ((β : DifferentialForm (Euclid P) (m + 1)) (x - p x)) :=
      ⟨_, rfl⟩
    have hΩ : IsTestForm Ω := hΩ_eq ▸ hΩtest (m + 1) (d + (m + 1)) lift _ hβ
    have hΩev : ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ w : Fin (m + 1) → Euclid P, (∀ i, w i ∈ Lᗮ) →
        Ω (t + y) (Fin.append f w) = ϕ t * (β : DifferentialForm (Euclid P) (m + 1)) y w := by
      intro t ht y hy w hw
      rw [hΩ_eq, ContinuousAlternatingMap.smul_apply, hL1 _ w hw, hpsplit t ht y hy,
        add_sub_cancel_left, smul_eq_mul]
    -- `S(Ω) = cϕ S₀(β)`
    have hSΩ : S ⟨Ω, hΩ, subset_univ _⟩ = cϕ * S₀ β := by
      rw [hS]
      have hev : ∀ t ∈ L, currentEval S₀ (fun y => flat (Ω (t + y))) = ϕ t * S₀ β := by
        intro t ht
        rw [hslice Ω hΩ t (ϕ t • β) fun y hy w hw => ?_, map_smul, smul_eq_mul]
        rw [hΩev t ht y hy w hw]
        rfl
      rw [setIntegral_congr_fun hLm fun t ht => hev t ht, integral_mul_const, hint, hcϕ_eq]
    -- `S(η^#Ω) = cϕ S₀(η^#β)`, using `μHE[d](λA) = λᵈ μHE[d](A)` on `L`
    have hηΩ : IsTestForm (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • (0 : Euclid P))) Ω) :=
      affinePullbackForm_isTestForm _ _ hprop hΩ
    obtain ⟨ηβ, hηβ⟩ : ∃ ηβ : TestFormOn (univ : Set (Euclid P)) (m + 1),
        (ηβ : DifferentialForm (Euclid P) (m + 1)) =
          affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • (0 : Euclid P)))
            (β : DifferentialForm (Euclid P) (m + 1)) :=
      ⟨⟨_, affinePullbackForm_isTestForm _ _ hprop hβ, subset_univ _⟩, rfl⟩
    have hSηΩ : S ⟨_, hηΩ, subset_univ _⟩ = cϕ * S₀ ηβ := by
      rw [hS]
      have hev : ∀ t ∈ L, currentEval S₀ (fun y => flat
          (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • (0 : Euclid P))) Ω (t + y))) =
            (lam⁻¹ ^ d * ϕ (lam⁻¹ • t)) * S₀ ηβ := by
        intro t ht
        rw [hslice _ hηΩ t ((lam⁻¹ ^ d * ϕ (lam⁻¹ • t)) • ηβ) fun y hy w hw => ?_, map_smul,
          smul_eq_mul]
        rw [hη, smul_add, hΩev _ (L.smul_mem _ ht) _ (Lᗮ.smul_mem _ hy) w hw]
        show _ = (lam⁻¹ ^ d * ϕ (lam⁻¹ • t)) * (ηβ : DifferentialForm (Euclid P) (m + 1)) y w
        rw [hηβ, hη, pow_add]
        ring
      rw [setIntegral_congr_fun hLm fun t ht => hev t ht, integral_mul_const, hint]
      rw [show (∫ x : L, lam⁻¹ ^ d * ϕ (lam⁻¹ • (x : Euclid P))) = cϕ from ?_]
      have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure L)
        (fun x : L => ϕ x) hlam.le
      simp only [Submodule.coe_smul] at h
      rw [integral_const_mul, h, hdL, hcϕ_eq, smul_eq_mul, ← mul_assoc, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero _ hlam.ne'), one_mul]
    -- the cone property of `S` gives `cϕ S₀(η^#β) = cϕ S₀(β)`
    have hcone := hSc lam hlam ⟨Ω, hΩ, subset_univ _⟩
    rw [hblow] at hcone
    rw [hblow]
    have h : cϕ * S₀ ηβ = cϕ * S₀ β := by
      rw [← hSηΩ, ← hSΩ]
      exact hcone
    have h' : S₀ ηβ = S₀ β := mul_left_cancel₀ hcϕ.ne' h
    rw [← h']
    exact congrArg S₀ (Subtype.ext hηβ.symm)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
