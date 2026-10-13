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

/-- **FTC along a segment for a Lipschitz function** (step 1 of the Poincaré inequality on the unit
ball invoked in the proof of Simon Ch. 5, Lemma 3.1; Gilbarg–Trudinger, Lemma 7.16).  The
restriction `φ(t) = u((1 − t)y + tx)` is Lipschitz, so `∫₀¹ φ' = φ(1) − φ(0) = u(x) − u(y)`: the
difference quotients `∫₀¹ (φ(s + t) − φ(s))/t ds` tend, as `t → 0⁺`, to `φ(1) − φ(0)` by continuity
of `φ` and to `∫₀¹ φ'` by dominated convergence.  Wherever `u` is differentiable at `(1 − t)y + tx`
the chain rule gives `φ'(t) = Du((1 − t)y + tx)(x − y)`, and this holds for a.e. `t ∈ (0, 1]`. -/
theorem Submission.dorag_ha_pb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (x y : Euclid n), LipschitzWith L u → (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ u ((1 - t) • y + t • x)) → u x - u y = ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • y + t • x) (x - y) := by
  intro n u L x y hu hdiff
  -- Step 1: `γ(t) = (1 − t)y + tx` is `‖x − y‖`-Lipschitz, so `φ = u ∘ γ` is Lipschitz
  have hγ : LipschitzWith ‖x - y‖₊ (fun t : ℝ => (1 - t) • y + t • x) := by
    refine LipschitzWith.of_dist_le_mul fun s t => le_of_eq ?_
    have h : (1 - s) • y + s • x - ((1 - t) • y + t • x) = (s - t) • (x - y) := by module
    rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, ← Real.dist_eq, coe_nnnorm, mul_comm]
  -- Step 2: `∫₀¹ φ' = φ(1) − φ(0)` for every Lipschitz `φ : ℝ → ℝ`, with `φ' = lineDeriv ℝ φ · 1`
  have ftc : ∀ (φ : ℝ → ℝ) (K : NNReal), LipschitzWith K φ →
      ∫ s in (0 : ℝ)..1, lineDeriv ℝ φ s 1 = φ 1 - φ 0 := by
    intro φ K hφ
    have hφc : Continuous φ := hφ.continuous
    have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b :=
      fun a b => hφc.intervalIntegrable a b
    -- with `Φ(c) = ∫₀ᶜ φ`, `∫₀¹ (φ(s + t) − φ(s))/t ds = (Φ(1 + t) − Φ(1))/t − (Φ(t) − Φ(0))/t`,
    -- which tends to `φ(1) − φ(0)` as `t → 0⁺` since `Φ' = φ`
    have hlim : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..1, t⁻¹ • (φ (s + t • 1) - φ s)) (𝓝[>] 0)
        (𝓝 (φ 1 - φ 0)) := by
      have hΦ : ∀ b, HasDerivAt (fun c => ∫ s in (0 : ℝ)..c, φ s) (φ b) b :=
        fun b => (hφc.integral_hasStrictDerivAt 0 b).hasDerivAt
      refine ((hΦ 1).tendsto_slope_zero_right.sub (hΦ 0).tendsto_slope_zero_right).congr
        fun t => ?_
      have hshift : ∫ s in (0 : ℝ)..1, φ (s + t) =
          (∫ s in (0 : ℝ)..1 + t, φ s) - ∫ s in (0 : ℝ)..0 + t, φ s := by
        rw [intervalIntegral.integral_comp_add_right,
          intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
      simp only [smul_eq_mul, mul_one]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun s => φ (s + t)).intervalIntegrable 0 1) (hint 0 1),
        hshift, intervalIntegral.integral_same]
      ring
    -- by dominated convergence (Rademacher, against the weight `1_{(0, 1]}`) the same quotients
    -- tend to `∫₀¹ φ'`
    have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const measure_Ioc_lt_top.ne
    have hind : ∀ h : ℝ → ℝ, ∫ s, h s * (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s =
        ∫ s in (0 : ℝ)..1, h s := by
      intro h
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
      congr 1
      ext s
      by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [hs]
    have hdom := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hg (1 : ℝ)
    simp only [hind] at hdom
    exact tendsto_nhds_unique hdom hlim
  -- `φ(1) = u(x)` and `φ(0) = u(y)`
  have key := ftc _ _ (hu.comp hγ)
  simp only [Function.comp_apply, sub_self, zero_smul, one_smul, zero_add, sub_zero,
    add_zero] at key
  rw [← key]
  -- Step 3: `γ' = x − y`, so `φ'(t) = Du(γ(t))(x − y)` wherever `u` is differentiable at `γ(t)`
  have hγ' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 - t) • y + t • x) (x - y) t := by
    intro t
    have h := (((hasDerivAt_id' t).const_sub 1).smul_const y).add ((hasDerivAt_id' t).smul_const x)
    convert h using 1
    rw [neg_one_smul, one_smul, neg_add_eq_sub]
  -- Step 4: that is the case for a.e. `t ∈ Ι 0 1 = (0, 1] ⊆ [0, 1]`
  apply intervalIntegral.integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Icc] at hdiff
  filter_upwards [hdiff] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have hd := (ht (Ioc_subset_Icc_self hmem)).hasFDerivAt.comp_hasDerivAt t (hγ' t)
  exact (hd.hasFDerivAt.hasLineDerivAt 1).lineDeriv.trans (by simp)
/-- Almost every segment meets a Lebesgue-null set `N ⊆ ℝⁿ` in a null set of parameters: for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, `(1 - t) y + t x ∉ N` for `L¹`-a.e. `t ∈ [0, 1]`.  Every `t`-slice
`{(x, y) : (1 - t) y + t x ∈ N}` is `Lⁿ ⊗ Lⁿ`-null: it is `ℝⁿ × N` for `t = 0`, and for `t ≠ 0`
each `x`-section is the preimage of a translate of `N` under `x ↦ t x`.  By Tonelli the set
`{((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ L¹⌞[0, 1]`, so almost all of its
sections in `t` are null. -/
theorem Submission.dorag_ha_pb_segment_null : ∀ (n : ℕ) (N : Set (Euclid n)), MeasurableSet N → volume N = 0 → ∀ᵐ p : Euclid n × Euclid n, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), (1 - t) • p.2 + t • p.1 ∉ N := by
  intro n N hNm hN0
  -- every `t`-slice `{(x, y) : (1 - t) y + t x ∈ N}` is null for `volume = Lⁿ ⊗ Lⁿ`
  have hslice : ∀ t : ℝ, (volume : Measure (Euclid n × Euclid n))
      {p | (1 - t) • p.2 + t • p.1 ∈ N} = 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · -- `t = 0`: the slice is `ℝⁿ × N`, of measure `Lⁿ(ℝⁿ) · 0 = 0`
      have h0 : {p : Euclid n × Euclid n | (1 - 0 : ℝ) • p.2 + (0 : ℝ) • p.1 ∈ N} = univ ×ˢ N := by
        ext p
        simp
      rw [h0, Measure.volume_eq_prod, Measure.prod_prod, hN0, mul_zero]
    · -- `t ≠ 0`: for each `y`, the `x`-section is the preimage of a translate of `N` under `x ↦ t x`
      have hm : MeasurableSet {p : Euclid n × Euclid n | (1 - t) • p.2 + t • p.1 ∈ N} :=
        hNm.preimage (by fun_prop)
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      change (volume : Measure (Euclid n)) ((t • ·) ⁻¹' ((fun z => (1 - t) • y + z) ⁻¹' N)) = 0
      rw [Measure.addHaar_preimage_smul volume ht, measure_preimage_add, hN0, mul_zero]
  -- Tonelli: `E = {((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ ν`
  have hEm : MeasurableSet {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} :=
    hNm.preimage (by fun_prop)
  have hE : ((volume : Measure (Euclid n × Euclid n)).prod (volume.restrict (Icc (0 : ℝ) 1)))
      {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} = 0 := by
    rw [Measure.prod_apply_symm hEm]
    exact (lintegral_congr fun t => hslice t).trans lintegral_zero
  -- sections in `t`: for a.e. `(x, y)`, `ν`-a.e. `t` has `(1 - t) y + t x ∉ N`
  refine Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume.restrict (Icc (0 : ℝ) 1))
    (p := fun q : (Euclid n × Euclid n) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1 ∉ N) ?_
  rw [ae_iff]
  simpa using hE
/-- Cauchy–Schwarz for the integral over a finite measure space, `(∫ h dμ)² ≤ μ(α) ∫ h² dμ` for
`h ∈ L²(μ)`: used twice in the Poincaré inequality on a ball that Simon's proof of Ch. 5,
Lemma 3.1 cites ("by the Poincaré inequality (see e.g. [GT01])").  `h ∈ L¹` (`L² ⊆ L¹` on a finite
measure space) and `h² = ‖h‖² ∈ L¹`.  If `m = μ(α) = 0` then `μ = 0` and both sides vanish;
otherwise, with `c = ∫ h dμ`, `0 ≤ ∫ (h − c/m)² dμ = ∫ h² dμ − c²/m`, and multiplying by `m > 0`
gives the claim. -/
theorem Submission.dorag_ha_pb_sq_integral_le : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ), μ univ ≠ ∞ → MemLp h 2 μ → (∫ x, h x ∂μ) ^ 2 ≤ (μ univ).toReal * ∫ x, h x ^ 2 ∂μ := by
  intro α _ μ h hμ hh
  -- Step 1: `μ` is finite; `h ∈ L¹` (`L² ⊆ L¹` on a finite measure space) and `h² = ‖h‖² ∈ L¹`
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hμ⟩
  have hint : Integrable h μ := hh.integrable one_le_two
  have hint2 : Integrable (fun x => h x ^ 2) μ := by
    simpa [Real.norm_eq_abs, sq_abs] using hh.integrable_norm_pow (p := 2) two_ne_zero
  rcases (ENNReal.toReal_nonneg (a := μ univ)).eq_or_lt with hm0 | hmpos
  · -- Step 2: `μ(α) = 0`, so `μ = 0` and both sides vanish
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1 <|
      ((ENNReal.toReal_eq_zero_iff _).1 hm0.symm).resolve_right hμ
    simp [hμ0]
  · -- Step 3: `m = μ(α) > 0`, `c = ∫ h dμ`; `0 ≤ ∫ (h - c/m)² dμ = ∫ h² dμ - c²/m`
    set m := (μ univ).toReal with hm
    set c := ∫ x, h x ∂μ with hc
    have hint1 : Integrable (fun x => h x ^ 2 - 2 * (c / m) * h x) μ :=
      hint2.sub (hint.const_mul _)
    have hexp : ∫ x, (h x - c / m) ^ 2 ∂μ = ∫ x, h x ^ 2 ∂μ - c ^ 2 / m := by
      have e : ∀ x, (h x - c / m) ^ 2 = h x ^ 2 - 2 * (c / m) * h x + (c / m) ^ 2 :=
        fun x => by ring
      simp_rw [e]
      rw [integral_add hint1 (integrable_const _), integral_sub hint2 (hint.const_mul _),
        integral_const_mul, integral_const, smul_eq_mul, ← hc, measureReal_def, ← hm]
      field_simp
      ring
    have hnn : 0 ≤ ∫ x, (h x - c / m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    -- Step 4: `c²/m ≤ ∫ h² dμ`; multiply by `m > 0`
    rw [hexp, sub_nonneg, div_le_iff₀ hmpos] at hnn
    linarith
/-- **FTC along a segment for a Lipschitz function** (step 1 of the Poincaré inequality on the unit
ball invoked in the proof of Simon Ch. 5, Lemma 3.1; Gilbarg–Trudinger, Lemma 7.16).  The
restriction `φ(t) = u((1 − t)y + tx)` is Lipschitz, so `∫₀¹ φ' = φ(1) − φ(0) = u(x) − u(y)`: the
difference quotients `∫₀¹ (φ(s + t) − φ(s))/t ds` tend, as `t → 0⁺`, to `φ(1) − φ(0)` by continuity
of `φ` and to `∫₀¹ φ'` by dominated convergence.  Wherever `u` is differentiable at `(1 − t)y + tx`
the chain rule gives `φ'(t) = Du((1 − t)y + tx)(x − y)`, and this holds for a.e. `t ∈ (0, 1]`. -/
theorem Submission.dorag_ha_pb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (x y : Euclid n), LipschitzWith L u → (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ u ((1 - t) • y + t • x)) → u x - u y = ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • y + t • x) (x - y) := by
  intro n u L x y hu hdiff
  -- Step 1: `γ(t) = (1 − t)y + tx` is `‖x − y‖`-Lipschitz, so `φ = u ∘ γ` is Lipschitz
  have hγ : LipschitzWith ‖x - y‖₊ (fun t : ℝ => (1 - t) • y + t • x) := by
    refine LipschitzWith.of_dist_le_mul fun s t => le_of_eq ?_
    have h : (1 - s) • y + s • x - ((1 - t) • y + t • x) = (s - t) • (x - y) := by module
    rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, ← Real.dist_eq, coe_nnnorm, mul_comm]
  -- Step 2: `∫₀¹ φ' = φ(1) − φ(0)` for every Lipschitz `φ : ℝ → ℝ`, with `φ' = lineDeriv ℝ φ · 1`
  have ftc : ∀ (φ : ℝ → ℝ) (K : NNReal), LipschitzWith K φ →
      ∫ s in (0 : ℝ)..1, lineDeriv ℝ φ s 1 = φ 1 - φ 0 := by
    intro φ K hφ
    have hφc : Continuous φ := hφ.continuous
    have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b :=
      fun a b => hφc.intervalIntegrable a b
    -- with `Φ(c) = ∫₀ᶜ φ`, `∫₀¹ (φ(s + t) − φ(s))/t ds = (Φ(1 + t) − Φ(1))/t − (Φ(t) − Φ(0))/t`,
    -- which tends to `φ(1) − φ(0)` as `t → 0⁺` since `Φ' = φ`
    have hlim : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..1, t⁻¹ • (φ (s + t • 1) - φ s)) (𝓝[>] 0)
        (𝓝 (φ 1 - φ 0)) := by
      have hΦ : ∀ b, HasDerivAt (fun c => ∫ s in (0 : ℝ)..c, φ s) (φ b) b :=
        fun b => (hφc.integral_hasStrictDerivAt 0 b).hasDerivAt
      refine ((hΦ 1).tendsto_slope_zero_right.sub (hΦ 0).tendsto_slope_zero_right).congr
        fun t => ?_
      have hshift : ∫ s in (0 : ℝ)..1, φ (s + t) =
          (∫ s in (0 : ℝ)..1 + t, φ s) - ∫ s in (0 : ℝ)..0 + t, φ s := by
        rw [intervalIntegral.integral_comp_add_right,
          intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
      simp only [smul_eq_mul, mul_one]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun s => φ (s + t)).intervalIntegrable 0 1) (hint 0 1),
        hshift, intervalIntegral.integral_same]
      ring
    -- by dominated convergence (Rademacher, against the weight `1_{(0, 1]}`) the same quotients
    -- tend to `∫₀¹ φ'`
    have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const measure_Ioc_lt_top.ne
    have hind : ∀ h : ℝ → ℝ, ∫ s, h s * (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s =
        ∫ s in (0 : ℝ)..1, h s := by
      intro h
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
      congr 1
      ext s
      by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [hs]
    have hdom := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hg (1 : ℝ)
    simp only [hind] at hdom
    exact tendsto_nhds_unique hdom hlim
  -- `φ(1) = u(x)` and `φ(0) = u(y)`
  have key := ftc _ _ (hu.comp hγ)
  simp only [Function.comp_apply, sub_self, zero_smul, one_smul, zero_add, sub_zero,
    add_zero] at key
  rw [← key]
  -- Step 3: `γ' = x − y`, so `φ'(t) = Du(γ(t))(x − y)` wherever `u` is differentiable at `γ(t)`
  have hγ' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 - t) • y + t • x) (x - y) t := by
    intro t
    have h := (((hasDerivAt_id' t).const_sub 1).smul_const y).add ((hasDerivAt_id' t).smul_const x)
    convert h using 1
    rw [neg_one_smul, one_smul, neg_add_eq_sub]
  -- Step 4: that is the case for a.e. `t ∈ Ι 0 1 = (0, 1] ⊆ [0, 1]`
  apply intervalIntegral.integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Icc] at hdiff
  filter_upwards [hdiff] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have hd := (ht (Ioc_subset_Icc_self hmem)).hasFDerivAt.comp_hasDerivAt t (hγ' t)
  exact (hd.hasFDerivAt.hasLineDerivAt 1).lineDeriv.trans (by simp)
/-- Almost every segment meets a Lebesgue-null set `N ⊆ ℝⁿ` in a null set of parameters: for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, `(1 - t) y + t x ∉ N` for `L¹`-a.e. `t ∈ [0, 1]`.  Every `t`-slice
`{(x, y) : (1 - t) y + t x ∈ N}` is `Lⁿ ⊗ Lⁿ`-null: it is `ℝⁿ × N` for `t = 0`, and for `t ≠ 0`
each `x`-section is the preimage of a translate of `N` under `x ↦ t x`.  By Tonelli the set
`{((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ L¹⌞[0, 1]`, so almost all of its
sections in `t` are null. -/
theorem Submission.dorag_ha_pb_segment_null : ∀ (n : ℕ) (N : Set (Euclid n)), MeasurableSet N → volume N = 0 → ∀ᵐ p : Euclid n × Euclid n, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), (1 - t) • p.2 + t • p.1 ∉ N := by
  intro n N hNm hN0
  -- every `t`-slice `{(x, y) : (1 - t) y + t x ∈ N}` is null for `volume = Lⁿ ⊗ Lⁿ`
  have hslice : ∀ t : ℝ, (volume : Measure (Euclid n × Euclid n))
      {p | (1 - t) • p.2 + t • p.1 ∈ N} = 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · -- `t = 0`: the slice is `ℝⁿ × N`, of measure `Lⁿ(ℝⁿ) · 0 = 0`
      have h0 : {p : Euclid n × Euclid n | (1 - 0 : ℝ) • p.2 + (0 : ℝ) • p.1 ∈ N} = univ ×ˢ N := by
        ext p
        simp
      rw [h0, Measure.volume_eq_prod, Measure.prod_prod, hN0, mul_zero]
    · -- `t ≠ 0`: for each `y`, the `x`-section is the preimage of a translate of `N` under `x ↦ t x`
      have hm : MeasurableSet {p : Euclid n × Euclid n | (1 - t) • p.2 + t • p.1 ∈ N} :=
        hNm.preimage (by fun_prop)
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      change (volume : Measure (Euclid n)) ((t • ·) ⁻¹' ((fun z => (1 - t) • y + z) ⁻¹' N)) = 0
      rw [Measure.addHaar_preimage_smul volume ht, measure_preimage_add, hN0, mul_zero]
  -- Tonelli: `E = {((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ ν`
  have hEm : MeasurableSet {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} :=
    hNm.preimage (by fun_prop)
  have hE : ((volume : Measure (Euclid n × Euclid n)).prod (volume.restrict (Icc (0 : ℝ) 1)))
      {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} = 0 := by
    rw [Measure.prod_apply_symm hEm]
    exact (lintegral_congr fun t => hslice t).trans lintegral_zero
  -- sections in `t`: for a.e. `(x, y)`, `ν`-a.e. `t` has `(1 - t) y + t x ∉ N`
  refine Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume.restrict (Icc (0 : ℝ) 1))
    (p := fun q : (Euclid n × Euclid n) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1 ∉ N) ?_
  rw [ae_iff]
  simpa using hE

/-- **Segment bound for a Lipschitz function at almost every pair** (steps 0, 2 and 3 of the
Poincaré inequality on the ball, written out for all pairs `(x, y)`).  By Rademacher the set `N`
where `u` is not differentiable is Borel and `Lⁿ`-null, so `segment_null` gives, for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, differentiability of `u` at `γ(t) = (1 − t)y + tx` for a.e.
`t ∈ [0, 1]`.  For such a pair `segment_ftc` gives `u(x) − u(y) = ∫₀¹ Du(γ(t))(x − y) dt`, hence
`|u(x) − u(y)| ≤ ∫₀¹ g` with `g(t) = ‖Du(γ(t))‖‖x − y‖ ≤ L‖x − y‖`, and `sq_integral_le` for
`L¹⌞(0, 1]` (total mass `1`) gives `(∫₀¹ g)² ≤ ∫₀¹ g² = ‖x − y‖² ∫₀¹ ‖Du(γ(t))‖² dt`. -/
theorem Submission.dorag_ha_pb_pair_sq_bound : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ p : Euclid n × Euclid n, (u p.1 - u p.2) ^ 2 ≤ ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2 := by
  intro n u L hu
  -- Step 1: the non-differentiability set of `u` is Borel and `Lⁿ`-null (Rademacher).
  have hNmeas : MeasurableSet {z : Euclid n | ¬DifferentiableAt ℝ u z} :=
    (measurableSet_of_differentiableAt ℝ u).compl
  have hNnull : volume {z : Euclid n | ¬DifferentiableAt ℝ u z} = 0 :=
    ae_iff.mp hu.ae_differentiableAt
  -- Step 2: for a.e. pair, `u` is differentiable at a.e. point of the segment.
  filter_upwards [Submission.dorag_ha_pb_segment_null n _ hNmeas hNnull] with p hp
  have hdiff : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      DifferentiableAt ℝ u ((1 - t) • p.2 + t • p.1) := by
    filter_upwards [hp] with t ht
    simpa only [mem_ofPred_eq, not_not] using ht
  -- Step 3: the fundamental theorem of calculus along the segment.
  have hftc : u p.1 - u p.2 =
      ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • p.2 + t • p.1) (p.1 - p.2) :=
    Submission.dorag_ha_pb_segment_ftc n u L p.1 p.2 hu hdiff
  -- Step 4: `|u x - u y| ≤ ∫₀¹ g` with `g t = ‖Du(γ t)‖ ‖x - y‖`, a bounded measurable function.
  have hDmeas : Measurable fun t : ℝ => fderiv ℝ u ((1 - t) • p.2 + t • p.1) :=
    (measurable_fderiv ℝ u).comp
      (by fun_prop : Continuous fun t : ℝ => (1 - t) • p.2 + t • p.1).measurable
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      g = fun t => ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ * ‖p.1 - p.2‖ := ⟨_, rfl⟩
  have hgmeas : Measurable g := by
    rw [hg]
    exact hDmeas.norm.mul_const _
  have hgbound : ∀ t, ‖g t‖ ≤ L * ‖p.1 - p.2‖ := by
    intro t
    simp only [hg, norm_mul, norm_norm]
    exact mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _)
  have hgint : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_const (c := (L : ℝ) * ‖p.1 - p.2‖)).mono_fun'
      hgmeas.aestronglyMeasurable (ae_of_all _ hgbound)
  have hfirst : |u p.1 - u p.2| ≤ ∫ t in (0 : ℝ)..1, g t := by
    rw [hftc, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (ae_of_all _ fun t _ => ?_) hgint
    simp only [hg]
    exact (fderiv ℝ u ((1 - t) • p.2 + t • p.1)).le_opNorm (p.1 - p.2)
  -- Step 5: Cauchy–Schwarz (`sq_integral_le`) on `(0, 1]`, which has total mass `1`.
  have hμ : volume.restrict (Ioc (0 : ℝ) 1) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    simp
  have hmem : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hgmeas.aestronglyMeasurable _ (ae_of_all _ hgbound)
  have hcs : (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    have h := Submission.dorag_ha_pb_sq_integral_le (volume.restrict (Ioc (0 : ℝ) 1)) g
      (by rw [hμ]; exact ENNReal.one_ne_top) hmem
    rw [hμ, ENNReal.toReal_one, one_mul] at h
    rwa [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  -- Step 6: combine, and pull the constant `‖x - y‖²` out of the integral.
  calc (u p.1 - u p.2) ^ 2 = |u p.1 - u p.2| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ t in (0 : ℝ)..1, g t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfirst 2
    _ ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := hcs
    _ = ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      simp only [hg]
      ring
/-- **Slice bound on the unit ball.**  For measurable `g ≥ 0` and `t ∈ [0, 1]`,
`∫_B ∫_B g((1 − t)y + tx) dy dx ≤ 2ⁿ Lⁿ(B) ∫_B g`, `B = B₁(0) ⊂ ℝⁿ`.  If `s ≥ 1/2` and
`c + sB ⊆ B`, the Haar scaling `v ↦ sv` and translation invariance give
`∫_B g(c + sv) dv ≤ ∫ (1_B g)(c + sv) dv = s⁻ⁿ ∫_B g ≤ 2ⁿ ∫_B g`.  By convexity of `B`, this applies
in `y` (`c = tx`, `s = 1 − t`) when `t ≤ 1/2`, and in `x` after Tonelli (`c = (1 − t)y`, `s = t`)
when `t ≥ 1/2`; integrating the constant bound over `B` gives the claim. -/
theorem Submission.dorag_ha_pb_slice_bound : ∀ (n : ℕ) (g : Euclid n → ℝ≥0∞), Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
  intro n g hg t ht
  obtain ⟨ht0, ht1⟩ := ht
  -- One-variable bound: if `s ≥ 1/2` and `c + s • B ⊆ B`, then `∫_B g(c + s v) dv ≤ 2ⁿ ∫_B g`.
  have key : ∀ (c : Euclid n) (s : ℝ), 1 / 2 ≤ s →
      (∀ v ∈ ball (0 : Euclid n) 1, c + s • v ∈ ball (0 : Euclid n) 1) →
      ∫⁻ v in ball (0 : Euclid n) 1, g (c + s • v) ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
    intro c s hs hcs
    have hs0 : 0 < s := by linarith
    obtain ⟨F, hFdef⟩ : ∃ F : Euclid n → ℝ≥0∞, F = (ball (0 : Euclid n) 1).indicator g := ⟨_, rfl⟩
    have hF : Measurable F := hFdef ▸ hg.indicator measurableSet_ball
    -- change of variables `v ↦ s • v` (Haar scaling) followed by translation invariance
    have hcv : ∫⁻ v, F (c + s • v) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, F z := by
      have h1 : ∫⁻ w, F (c + w) ∂(Measure.map (fun v : Euclid n => s • v) volume)
          = ∫⁻ v, F (c + s • v) :=
        lintegral_map (hF.comp (measurable_const_add c)) (measurable_const_smul s)
      rw [← h1, Measure.map_addHaar_smul volume hs0.ne', lintegral_smul_measure,
        lintegral_add_left_eq_self F c, finrank_euclideanSpace_fin, smul_eq_mul]
    have hs2 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 two_pos]
      linarith
    calc ∫⁻ v in ball (0 : Euclid n) 1, g (c + s • v)
        = ∫⁻ v in ball (0 : Euclid n) 1, F (c + s • v) := by
          refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
          rw [hFdef, Set.indicator_of_mem (hcs v hv)]
      _ ≤ ∫⁻ v, F (c + s • v) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [hcv, hFdef, lintegral_indicator measurableSet_ball]
      _ ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          gcongr
          calc ENNReal.ofReal |(s ^ n)⁻¹| = ENNReal.ofReal s⁻¹ ^ n := by
                rw [abs_of_pos (by positivity), ← inv_pow, ENNReal.ofReal_pow (by positivity)]
            _ ≤ ENNReal.ofReal 2 ^ n := by gcongr
            _ = 2 ^ n := by rw [ENNReal.ofReal_ofNat]
  -- the integrand is jointly measurable
  have hmeas : Measurable (fun p : Euclid n × Euclid n => g ((1 - t) • p.2 + t • p.1)) :=
    hg.comp (by fun_prop)
  rcases le_total (1 / 2 : ℝ) t with h | h
  · -- `t ≥ 1/2`: Tonelli, then change variables in `x` with `c = (1 - t) • y`, `s = t`
    rw [lintegral_lintegral_swap (f := fun x y => g ((1 - t) • y + t • x)) hmeas.aemeasurable]
    calc ∫⁻ y in ball (0 : Euclid n) 1, ∫⁻ x in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in ball (0 : Euclid n) 1, 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          refine key ((1 - t) • y) t h fun v hv => ?_
          exact convex_ball (0 : Euclid n) 1 hy hv (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const]
          ring
  · -- `t ≤ 1/2`: change variables in `y` with `c = t • x`, `s = 1 - t`
    calc ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in ball (0 : Euclid n) 1, 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
          calc ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
              = ∫⁻ y in ball (0 : Euclid n) 1, g (t • x + (1 - t) • y) :=
                lintegral_congr fun y => by rw [add_comm]
            _ ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
                refine key (t • x) (1 - t) (by linarith) fun v hv => ?_
                rw [add_comm]
                exact convex_ball (0 : Euclid n) 1 hv hx (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const]
          ring

/-- **Poincaré inequality on the unit ball, double-integral step** (the convex-domain argument of
Gilbarg–Trudinger, Lemma 7.16, cited in Simon's proof of Lemma 5.3.1).  For Lipschitz `u` on
`ℝⁿ` and `B = B₁(0)`, `∫_B ∫_B (u(x) - u(y))² ≤ 2ⁿ⁺² ωₙ ∫_B ‖Du‖²`.  For a.e. `x, y ∈ B`,
`dorag_ha_pb_pair_sq_bound` and `‖x - y‖ < 2` give
`(u(x) - u(y))² ≤ 4 ∫₀¹ ‖Du((1 - t)y + tx)‖² dt`.  Integrate over `B × B` and move the
`t`-integral outside (Tonelli); then `dorag_ha_pb_slice_bound` bounds each slice by
`2ⁿ ωₙ ∫_B ‖Du‖²`.  As `‖Du‖ ≤ Lip(u)`, the bound is finite, so it passes from `ℝ≥0∞` to `ℝ`. -/
theorem Submission.dorag_ha_pb_double_integral_bound : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∫ x in ball (0 : Euclid n) 1, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2 ≤ 2 ^ (n + 2) * (volume (ball (0 : Euclid n) 1)).toReal * ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 := by
  intro n u L hu
  have hpair := Submission.dorag_ha_pb_pair_sq_bound n u L hu
  have hslice := Submission.dorag_ha_pb_slice_bound n
  have hcont : Continuous u := hu.continuous
  -- Step 1: `g = ofReal ‖Du‖²` is measurable, and `∫_B g < ∞` since `‖Du‖ ≤ L`
  have hD : Measurable fun z => ‖fderiv ℝ u z‖ ^ 2 := (measurable_fderiv ℝ u).norm.pow_const 2
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hD.ennreal_ofReal
  have hJ : ∫⁻ z in ball (0 : Euclid n) 1, g z ≠ ∞ := by
    have h1 : ∫⁻ z in ball (0 : Euclid n) 1, g z ≤
        ∫⁻ _ in ball (0 : Euclid n) 1, ENNReal.ofReal ((L : ℝ) ^ 2) :=
      lintegral_mono fun z => by
        rw [hgx]
        gcongr
        exact norm_fderiv_le_of_lipschitz ℝ hu
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)).ne
  -- Step 2: for a.e. `x, y ∈ B`, `(u x - u y)² ≤ 4 ∫_(0,1] ‖Du((1 - t) y + t x)‖² dt`
  have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) 1)),
      ∀ᵐ y ∂(volume.restrict (ball (0 : Euclid n) 1)),
        ENNReal.ofReal ((u x - u y) ^ 2) ≤ 4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair),
      ae_restrict_mem measurableSet_ball] with x hx hxB
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem measurableSet_ball] with y hy hyB
    rw [mem_ball_zero_iff] at hxB hyB
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2 with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have hxy : ‖x - y‖ ^ 2 ≤ 4 := by
      have h2 : ‖x - y‖ < 2 := by linarith [norm_sub_le x y]
      nlinarith [norm_nonneg (x - y)]
    have h4 : (u x - u y) ^ 2 ≤ 4 * G := hy.trans (mul_le_mul_of_nonneg_right hxy hG)
    -- `G` is the integral over `(0, 1]` of a nonnegative function
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hD.comp h.measurable).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => sq_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal ((u x - u y) ^ 2) ≤ ENNReal.ofReal (4 * G) := ENNReal.ofReal_le_ofReal h4
      _ = 4 * ENNReal.ofReal G := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ 4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by gcongr
  -- Step 3: integrate over `B × B`, move the `t`-integral outside (Tonelli), apply the slice bound
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  have hI : ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        ENNReal.ofReal ((u x - u y) ^ 2) ≤
      2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
    calc ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          ENNReal.ofReal ((u x - u y) ^ 2)
        ≤ ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          lintegral_mono_ae (hae.mono fun x hx => lintegral_mono_ae hx)
      _ = 4 * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1,
          ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)]
          rw [hswap]
      _ ≤ 4 * ∫⁻ _ in Ioc (0 : ℝ) 1,
          2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          gcongr 4 * ?_
          exact setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hg t (Ioc_subset_Icc_self ht)
      _ = 2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one, pow_add]
          ring
  -- Step 4: back to Bochner integrals; the bound is finite since `∫_B g < ∞`
  have hK : Measurable fun x : Euclid n =>
      ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2) := by
    have h : Continuous fun p : Euclid n × Euclid n => (u p.1 - u p.2) ^ 2 := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal ((u p.1 - u p.2) ^ 2))
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2 =
      (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _)
      (by fun_prop : Continuous fun y => (u x - u y) ^ 2).aestronglyMeasurable
  have hrhs : ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 =
      (∫⁻ z in ball (0 : Euclid n) 1, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      hD.aestronglyMeasurable]
    simp only [hgx]
  have hfin : (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Euclid n) 1) *
      ∫⁻ z in ball (0 : Euclid n) 1, g z ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      measure_ball_lt_top.ne) hJ
  calc ∫ x in ball (0 : Euclid n) 1, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2
      = ∫ x in ball (0 : Euclid n) 1,
          (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal := by
        simp only [hinner]
    _ = (∫⁻ x in ball (0 : Euclid n) 1, ENNReal.ofReal
          (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) *
          ∫⁻ z in ball (0 : Euclid n) 1, g z).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ (n + 2) * (volume (ball (0 : Euclid n) 1)).toReal *
          ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- **Poincaré inequality on a ball** (Simon Ch. 5, proof of Lemma 3.1; Gilbarg–Trudinger,
Lemma 7.16), the averaging step, for any `s ⊆ ℝⁿ` with `ω = Lⁿ(s) < ∞` and `f ∈ L²(s)`:
`∫_s (f − f̄)² ≤ ω⁻¹ ∫_s ∫_s (f(x) − f(y))² dy dx`, `f̄ = ω⁻¹ ∫_s f` (both sides vanish if
`ω = 0`).  For each `x`, `f(x) − f̄ = ω⁻¹ ∫_s (f(x) − f(y)) dy`, so Cauchy–Schwarz
(`dorag_ha_pb_sq_integral_le`) gives `(f(x) − f̄)² ≤ ω⁻¹ ∫_s (f(x) − f(y))² dy`.  This is
integrated over `s`; the right side is integrable since `(f(x) − f(y))² ≤ 2f(x)² + 2f(y)²`. -/
theorem Submission.dorag_ha_pb_variance_bound : ∀ (n : ℕ) (s : Set (Euclid n)) (f : Euclid n → ℝ), volume s ≠ ∞ → MemLp f 2 (volume.restrict s) → ∫ x in s, (f x - (∫ y in s, f y) / (volume s).toReal) ^ 2 ≤ ((volume s).toReal)⁻¹ * ∫ x in s, ∫ y in s, (f x - f y) ^ 2 := by
  intro n s f hs hf
  set μ : Measure (Euclid n) := volume.restrict s
  set ω : ℝ := (volume s).toReal
  -- Step 1: `μ` is finite with `μ(ℝⁿ).toReal = ω`, and `f, f² ∈ L¹(μ)`
  have hμuniv : μ univ = volume s := Measure.restrict_apply_univ s
  have hμfin : μ univ ≠ ∞ := hμuniv ▸ hs
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hs
  have hf1 : Integrable f μ := hf.integrable one_le_two
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hf.integrable_norm_pow two_ne_zero
  -- Step 2: if `ω = 0` then `μ = 0` and both sides vanish
  rcases eq_or_ne ω 0 with hω0 | hω0
  · have hμ0 : μ = 0 :=
      Measure.restrict_eq_zero.2 (((ENNReal.toReal_eq_zero_iff _).1 hω0).resolve_right hs)
    rw [hω0, inv_zero, zero_mul, hμ0, integral_zero_measure]
  -- Step 3: the pointwise bound `(f(x) − f̄)² ≤ ω⁻¹ ∫_s (f(x) − f(y))² dy`
  have hpt : ∀ x, (f x - (∫ y, f y ∂μ) / ω) ^ 2 ≤ ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ := by
    intro x
    have hmem : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
    have hCS := Submission.dorag_ha_pb_sq_integral_le μ (fun y => f x - f y) hμfin hmem
    rw [hμuniv] at hCS
    have hI : ∫ y, (f x - f y) ∂μ = ω * f x - ∫ y, f y ∂μ := by
      rw [integral_sub (integrable_const (f x)) hf1, integral_const, smul_eq_mul, measureReal_def,
        hμuniv]
    have hdiff : f x - (∫ y, f y ∂μ) / ω = ω⁻¹ * ∫ y, (f x - f y) ∂μ := by
      rw [hI]
      field_simp
    rw [hdiff, mul_pow]
    calc (ω⁻¹) ^ 2 * (∫ y, (f x - f y) ∂μ) ^ 2
        ≤ (ω⁻¹) ^ 2 * (ω * ∫ y, (f x - f y) ^ 2 ∂μ) := by gcongr
      _ = ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ := by field_simp
  -- Step 4: `(x, y) ↦ (f(x) − f(y))²` is `μ ⊗ μ`-integrable, being `≤ 2f(x)² + 2f(y)²`
  have hprod : Integrable (fun p : Euclid n × Euclid n => (f p.1 - f p.2) ^ 2) (μ.prod μ) := by
    have hm := hf.aestronglyMeasurable
    refine Integrable.mono' (((hf2.comp_fst μ).const_mul 2).add ((hf2.comp_snd μ).const_mul 2))
      ((hm.comp_fst.sub hm.comp_snd).pow 2) (ae_of_all _ fun p => ?_)
    show ‖(f p.1 - f p.2) ^ 2‖ ≤ 2 * f p.1 ^ 2 + 2 * f p.2 ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f p.1 + f p.2)]
  have hinner : Integrable (fun x => ∫ y, (f x - f y) ^ 2 ∂μ) μ := hprod.integral_prod_left
  -- Step 5: integrate the pointwise bound over `s`
  calc ∫ x, (f x - (∫ y, f y ∂μ) / ω) ^ 2 ∂μ
      ≤ ∫ x, ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hinner.const_mul ω⁻¹)
          (ae_of_all _ hpt)
    _ = ω⁻¹ * ∫ x, ∫ y, (f x - f y) ^ 2 ∂μ ∂μ := integral_const_mul _ _

/-- **Poincaré inequality on the unit ball** for Lipschitz `u : ℝⁿ → ℝ` (the inequality cited in
Simon's proof of 5.3.1, "by the Poincaré inequality (see e.g. [GT01])"; Gilbarg–Trudinger,
Lemma 7.16 and (7.45)).  With `B = B̆₁(0)`, `ω = Lⁿ(B) ∈ (0, ∞)` and `ū = ω⁻¹∫_B u`,
`∫_B (u − ū)² ≤ ω⁻¹∫_B∫_B (u(x) − u(y))² dy dx ≤ ω⁻¹ · 2ⁿ⁺²ω∫_B ‖Du‖² = 2ⁿ⁺²∫_B ‖Du‖²`:
the first step is the variance bound (`u ∈ L²(B)`, being continuous with `|u| ≤ |u(0)| + L` on
`B`), the second the double-integral bound (FTC along segments and the affine change of
variables).  So `C_P = 2ⁿ⁺²`. -/
theorem Submission.dorag_ha_poincare_ball : ∀ n : ℕ, 0 < n → ∃ CP : ℝ, 0 < CP ∧ ∀ (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∫ x in ball (0 : Euclid n) 1, (u x - (∫ y in ball (0 : Euclid n) 1, u y) / (volume (ball (0 : Euclid n) 1)).toReal) ^ 2 ≤ CP * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n _
  refine ⟨2 ^ (n + 2), by positivity, fun u L hu => ?_⟩
  -- `ω = Lⁿ(B) ∈ (0, ∞)`
  have hBfin : volume (ball (0 : Euclid n) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hω : 0 < (volume (ball (0 : Euclid n) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclid n) one_pos).ne' hBfin
  -- `u ∈ L²(B)`: `u` is continuous and `‖u x‖ ≤ ‖u 0‖ + L` on `B`
  have hmem : MemLp u 2 (volume.restrict (ball (0 : Euclid n) 1)) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) 1)) :=
      isFiniteMeasure_restrict.mpr hBfin
    refine MemLp.of_bound hu.continuous.aestronglyMeasurable (‖u 0‖ + L) ?_
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    have hux : dist (u x) (u 0) ≤ L * 1 := hu.dist_le_mul_of_le (mem_ball.mp hx).le
    calc ‖u x‖ = dist (u x) 0 := (dist_zero_right _).symm
      _ ≤ dist (u x) (u 0) + dist (u 0) 0 := dist_triangle _ _ _
      _ ≤ ‖u 0‖ + L := by rw [dist_zero_right]; linarith
  -- the variance bound, then the double-integral bound multiplied by `ω⁻¹ ≥ 0`
  calc _ ≤ _ := Submission.dorag_ha_pb_variance_bound n (ball (0 : Euclid n) 1) u hBfin hmem
    _ ≤ _ := mul_le_mul_of_nonneg_left
          (Submission.dorag_ha_pb_double_integral_bound n u L hu) (inv_nonneg.mpr hω.le)
    _ = _ := by rw [mul_comm (2 ^ (n + 2) : ℝ), mul_assoc, inv_mul_cancel_left₀ hω.ne']

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
