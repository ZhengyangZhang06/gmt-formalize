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
/-- **Coordinate projections of `Hⁿ`-null sets are Lebesgue-null** (parent step 3).  For
injective `I : Fin n → Fin P` the coordinate projection `q x = (x (I k))ₖ : ℝᴾ → ℝⁿ` is
`1`-Lipschitz (the squares summed over `image I` are among those summed over `Fin P`), so
`μH[n] (q '' C) ≤ μH[n] C`.  `μHE[n] = c • μH[n]` with one nonzero constant `c` on every space,
and `μHE[n] = volume` on `ℝⁿ`; hence `μHE[n] C = 0` gives `volume (q '' C) = 0`.  No compactness
of `C` is needed. -/
theorem Submission.cmr_volume_coordProj_image_null : ∀ (P n : ℕ) (I : Fin n → Fin P) (C : Set (Euclid P)), Function.Injective I → μHE[n] C = 0 → volume ((fun x : Euclid P => (WithLp.toLp 2 (fun k => x (I k)) : Euclid n)) '' C) = 0 := by
  intro P n I C hI hC
  set q : Euclid P → Euclid n := fun x => WithLp.toLp 2 (fun k => x (I k))
  -- `q` is 1-Lipschitz: the squares summed over `image I` are among those summed over `Fin P`
  have hq : LipschitzWith 1 q := by
    refine LipschitzWith.mk_one fun x y => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ k, dist ((q x).ofLp k) ((q y).ofLp k) ^ 2
        = ∑ k, dist (x.ofLp (I k)) (y.ofLp (I k)) ^ 2 := rfl
      _ = ∑ l ∈ Finset.univ.image I, dist (x.ofLp l) (y.ofLp l) ^ 2 := by
        rw [Finset.sum_image fun _ _ _ _ h => hI h]
      _ ≤ ∑ l, dist (x.ofLp l) (y.ofLp l) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  -- `μHE[n] = c • μH[n]` with `c ≠ 0`, so `μH[n] C = 0`
  have hc : (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
      μH[(n : ℝ)] : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at hC
  have hC' : μH[(n : ℝ)] C = 0 := (mul_eq_zero.mp hC).resolve_left hc
  -- `μH[n] (q '' C) ≤ 1 ^ n * μH[n] C = 0`
  have hqC : μH[(n : ℝ)] (q '' C) = 0 := by
    have h := hq.hausdorffMeasure_image_le (Nat.cast_nonneg n) C
    rw [hC', mul_zero] at h
    exact nonpos_iff_eq_zero.mp h
  -- on `ℝⁿ`, `volume = μHE[n] = c • μH[n]`
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hqC, smul_zero]
/-- **Simon 6.2.36** (`μ_T ≪ Hⁿ` for locally normal `T`; mass bound for the divergence
integral): let `T ∈ 𝒟_{m+1}(U)` satisfy `T(ω) = ∫ ⟨ω, ξ⟩ dμ`, and let `η`, `ζ` be test forms
supported in `spt b ⊆ W ⊆ U` with `|η|, |ζ| ≤ K` and `dη = b D θ + ζ`.  Then `ω = dη − ζ` is
a test form in `U` with `ω(x) = b(x) D(x) θ`, so `∫_W b ⟨θ, ξ⟩ D dμ = T(ω) = ∂T(η) − T(ζ)`,
and the evaluation bound gives `|∫_W b ⟨θ, ξ⟩ D dμ| ≤ K (M_W(∂T) + M_W(T))`. -/
theorem Submission.cmr_abs_integral_div_le_mass : ∀ (P m : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (m + 1)) (θ : Covector (Euclid P) (m + 1)) (b D : Euclid P → ℝ) (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)) (K : ℝ), W ⊆ U → T.massOn W ≠ ∞ → T.boundary.massOn W ≠ ∞ → (∀ ω : TestFormOn U (m + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μ) → (∀ (k : ℕ) (S : GeometricCurrentOn U k) (ω : TestFormOn U k) (r : ℝ), S.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) k) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ r) → |S ω| ≤ r * (S.massOn W).toReal) → tsupport b ⊆ W → IsTestForm η → IsTestForm ζ → tsupport η ⊆ tsupport b → tsupport ζ ⊆ tsupport b → (∀ x, covectorEuclideanNorm (η x) ≤ K) → (∀ x, covectorEuclideanNorm (ζ x) ≤ K) → (∀ x, exteriorDerivative η x = (b x * D x) • θ + ζ x) → |∫ x, b x * ξ x θ * D x ∂(μ.restrict W)| ≤ K * ((T.boundary.massOn W).toReal + (T.massOn W).toReal) := by
  intro P m U W T μ ξ θ b D η ζ K hWU hT hbT hrep hEB hb hη hζ hηb hζb hηK hζK hd
  -- `η`, `ζ` are test forms in `U`, supported in `spt b ⊆ W`
  have hηW : tsupport η ⊆ W := hηb.trans hb
  have hζW : tsupport ζ ⊆ W := hζb.trans hb
  let η' : TestFormOn U m := ⟨η, hη, hηW.trans hWU⟩
  let ζ' : TestFormOn U (m + 1) := ⟨ζ, hζ, hζW.trans hWU⟩
  -- `ω = dη − ζ` has `ω(x) = b(x) D(x) θ`
  have hω : ∀ x, ((exteriorDerivativeTestOn U m η' - ζ' : TestFormOn U (m + 1)) :
      DifferentialForm (Euclid P) (m + 1)) x = (b x * D x) • θ := by
    intro x
    change exteriorDerivative η x - ζ x = _
    rw [hd x, add_sub_cancel_right]
  -- `T(ω) = ∂T(η) − T(ζ)`, and the evaluation bound controls both terms
  have hTω : T (exteriorDerivativeTestOn U m η' - ζ') = T.boundary η' - T ζ' := by
    rw [GeometricCurrentOn.boundary_apply]
    exact map_sub T.toCurrent _ _
  have h1 : |T.boundary η'| ≤ K * (T.boundary.massOn W).toReal :=
    hEB m T.boundary η' K hbT hηW hηK
  have h2 : |T ζ'| ≤ K * (T.massOn W).toReal := hEB (m + 1) T ζ' K hT hζW hζK
  -- `b = 0` off `W`, so the integral over `W` is `T(ω)`
  have hint : ∫ x, b x * ξ x θ * D x ∂(μ.restrict W) =
      T (exteriorDerivativeTestOn U m η' - ζ') := by
    rw [hrep, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · congr 1
      funext x
      rw [hω x, map_smul, smul_eq_mul]
      ring
    · intro x hx
      have hbx : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hb h)
      rw [hbx, zero_mul, zero_mul]
  rw [hint, hTω, mul_add]
  exact (abs_sub _ _).trans (add_le_add h1 h2)
/-- Localization of the null-set argument (steps 5 and 6 of the null-set step of the mass
representation used for Simon 7.2.4): let `W ⊆ ℝᴾ` be open with `μ(W) < ∞`, `f` `μ`-a.e. strongly
measurable with `|f| ≤ c`, `q : ℝᴾ → ℝⁿ` measurable and `N ⊆ ℝⁿ` measurable.  Assume (TD): for a
finite `ν` and `ν`-integrable `h`, a bound `|∫ h · div g(q) dν| ≤ Λ` over all smooth compactly
supported `g` with `‖g‖ ≤ 1` forces `∫_{q⁻¹(N)} h dν = 0`; and (DB): for every smooth `b` compactly
supported in `W` such a bound holds for `h = b f` and `ν = μ⌞W`.  Then `f = 0` `μ`-a.e. on
`W ∩ q⁻¹(N)`.  The function `F := 1_{q⁻¹(N)} f` is bounded, hence locally integrable on `W`;
since `b` vanishes off `W`, (DB) and (TD) give `∫ b F dμ = ∫_{q⁻¹(N)} b f d(μ⌞W) = 0` for every
such `b`, and `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `F = 0` `μ`-a.e. on
`W`. -/
theorem Submission.cmr_ae_zero_of_div_bounds : ∀ (P n : ℕ) (W : Set (Euclid P)) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (q : Euclid P → Euclid n) (N : Set (Euclid n)) (c : ℝ), IsOpen W → μ W < ∞ → AEStronglyMeasurable f μ → (∀ x, |f x| ≤ c) → Measurable q → MeasurableSet N → (∀ (ν : Measure (Euclid P)) (h : Euclid P → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∫ x in q ⁻¹' N, h x ∂ν = 0) → (∀ b : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ W → ∃ Λ : ℝ, ∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, b x * f x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂(μ.restrict W)| ≤ Λ) → ∀ᵐ x ∂μ, x ∈ W → q x ∈ N → f x = 0 := by
  intro P n W μ f q N c hW hμW hf hfc hq hN hTD hDB
  -- Step 1: `A := q⁻¹(N)` is measurable, `μ⌞W` is finite, `c ≥ 0`
  have hA : MeasurableSet (q ⁻¹' N) := hq hN
  have : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.2 hμW.ne
  have hc : 0 ≤ c := (abs_nonneg _).trans (hfc 0)
  -- Step 2: `F := 1_A f` is bounded by `c`, hence locally integrable on `W`
  have hFb : ∀ x, ‖(q ⁻¹' N).indicator f x‖ ≤ c := by
    intro x
    by_cases hx : x ∈ q ⁻¹' N
    · rw [indicator_of_mem hx, Real.norm_eq_abs]
      exact hfc x
    · rw [indicator_of_notMem hx, norm_zero]
      exact hc
  have hFloc : LocallyIntegrableOn ((q ⁻¹' N).indicator f) W μ :=
    IntegrableOn.locallyIntegrableOn
      (Integrable.of_bound (hf.indicator hA).restrict c (Eventually.of_forall hFb))
  -- Step 4: localization, once the integrals of step 3 vanish
  have hF0 : ∀ᵐ x ∂μ, x ∈ W → (q ⁻¹' N).indicator f x = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hFloc ?_
    -- Step 3: `∫ b • F dμ = 0` for smooth `b` compactly supported in `W`
    intro b hb hbc hbW
    -- (a) `h := b f` is `μ⌞W`-integrable
    obtain ⟨B, hB⟩ := hb.continuous.bounded_above_of_compact_support hbc
    have hh : Integrable (fun x => b x * f x) (μ.restrict W) := by
      refine Integrable.of_bound (hb.continuous.aestronglyMeasurable.mul hf.restrict) (B * c)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs (f x)]
      exact mul_le_mul (hB x) (hfc x) (abs_nonneg _) ((norm_nonneg _).trans (hB x))
    -- (b) (DB) and (TD) give `∫_A b f d(μ⌞W) = 0`
    obtain ⟨Λ, hΛ⟩ := hDB b hb hbc hbW
    have h0 : ∫ x in q ⁻¹' N, b x * f x ∂(μ.restrict W) = 0 :=
      hTD (μ.restrict W) (fun x => b x * f x) Λ inferInstance hh hΛ
    -- (c) `b` vanishes off `W`, so `∫ b • F dμ = ∫ b • F d(μ⌞W)`
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (hbW hx'), zero_smul]]
    -- (d) `b • F = 1_A (b f)`, and (e) conclude
    have hbF : (fun x => b x • (q ⁻¹' N).indicator f x) =
        (q ⁻¹' N).indicator fun x => b x * f x := by
      funext x
      by_cases hx : x ∈ q ⁻¹' N
      · rw [indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    rw [hbF, integral_indicator hA]
    exact h0
  -- Step 5: on `W ∩ q⁻¹(N)`, `f = F = 0`
  filter_upwards [hF0] with x hx hxW hxN
  rw [← indicator_of_mem (show x ∈ q ⁻¹' N from hxN) f]
  exact hx hxW
/-- **The mass measure vanishes where the orientation vanishes** (parent step 8 of the
representation `T = μ_T ∧ ξ⃗`).  Let `W ⊇ C` be measurable with `μ(W) < ∞` and `M_W(T) = μ(W)`,
let `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x` and all covectors `α` (`|·|_E` is
`covectorEuclideanNorm`), and let `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)` for every test form `ω`.  If
`ξ = 0` `μ`-a.e. on `C`, then `μ(C) = 0`.  Fix an admissible `ω`, i.e. `tsupport ω ⊆ W` and
`|ω|_E ≤ 1`, and let `f(x) = ⟨ω(x), ξ(x)⟩`.  For `μ`-a.e. `x`, `|f(x)| ≤ 1_{W \ C}(x)`: `f = 0`
on `C` (where `ξ = 0`) and off `W` (where `ω = 0`), and `|f| ≤ |ω|_E ≤ 1` on `W \ C`.  Hence
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_{W \ C} dμ = μ(W \ C)`, whether or not `f` is integrable.
Taking the supremum gives `μ(W) = M_W(T) ≤ μ(W \ C)`, and `μ(W \ C) + μ(C) = μ(W)` with
`μ(W \ C) < ∞` forces `μ(C) = 0`. -/
theorem Submission.cmr_measure_null_of_orient_ae_zero : ∀ (P n : ℕ) (U W C : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), MeasurableSet W → MeasurableSet C → C ⊆ W → μ W < ∞ → T.massOn W = μ W → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → (∀ᵐ x ∂μ, x ∈ C → ξ x = 0) → μ C = 0 := by
  intro P n U W C T μ ξ hW hC hCW hμW hmass hξ hT hzero
  -- Step 1: `M_W(T) ≤ μ(W \ C)`; it suffices to bound `ofReal (T ω)` for each admissible `ω`
  have hle : T.massOn W ≤ μ (W \ C) := by
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    -- `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_{W \ C}(x)` for `μ`-a.e. `x`
    have hpt : ∀ᵐ x ∂μ,
        ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ (W \ C).indicator 1 x := by
      filter_upwards [hzero] with x hx
      by_cases hxC : x ∈ C
      · rw [hx hxC, zero_apply, enorm_zero]
        exact zero_le
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem (show x ∈ W \ C from ⟨hxW, hxC⟩), Pi.one_apply,
          Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
      · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hω.1 h), map_zero, enorm_zero]
        exact zero_le
    calc ENNReal.ofReal (T ω)
        = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
      _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, (W \ C).indicator 1 x ∂μ := lintegral_mono_ae hpt
      _ = μ (W \ C) := lintegral_indicator_one (hW.diff hC)
  -- Step 2: cancel the finite `μ(W \ C)` in `μ(W \ C) + μ(C) = μ(W) ≤ μ(W \ C) + 0`
  have hsplit : μ (W \ C) + μ C = μ W := by
    simpa only [inter_eq_right.mpr hCW] using measure_sdiff_add_inter (μ := μ) W hC
  have hfin : μ (W \ C) ≠ ∞ := ((measure_mono Set.sdiff_subset).trans_lt hμW).ne
  refine nonpos_iff_eq_zero.mp ((ENNReal.add_le_add_iff_left hfin).mp ?_)
  rw [hsplit, add_zero, ← hmass]
  exact hle
/-- Null sets from compact null sets (last step of the proof that the mass measure `μ_T` of a
locally normal current vanishes on `Hⁿ`-null sets, Simon 6.2.36, used for 7.2.4): let `U ⊆ ℝᴾ` be
open and `μ`, `ν` measures on `ℝᴾ` with `μ(ℝᴾ \ U) = 0`, `μ(K) < ∞` for compact `K ⊆ U`, and
`μ(C) = 0` for every compact `C ⊆ U` with `ν(C) = 0`.  Then every `ν`-null set is `μ`-null.
Take a measurable `ν`-null hull `E' ⊇ E` and exhaust `U` by the compact sets `Fᵢ ∩ B̄ⱼ(0)`,
`Fᵢ ⊆ U` closed.  Each `μ⌞(Fᵢ ∩ B̄ⱼ(0))` is finite, hence inner regular, so `μ(E' ∩ Fᵢ ∩ B̄ⱼ(0)) > 0`
would give a compact `C ⊆ E'` with `μ(C ∩ Fᵢ ∩ B̄ⱼ(0)) > 0`, contradicting the hypothesis. -/
theorem Submission.cmr_null_of_compact_null : ∀ (P : ℕ) (U : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ν C = 0 → μ C = 0) → ∀ E : Set (Euclid P), ν E = 0 → μ E = 0 := by
  intro P U μ ν hU hUc hfin hnull E hE
  -- Step 1: a measurable `ν`-null hull `E' ⊇ E`
  obtain ⟨E', hEE', hE'm, hE'⟩ := exists_measurable_superset_of_null hE
  -- Step 2: `U = ⋃ₚ Kₚ` with `K_{(i,j)} = Fᵢ ∩ B̄ⱼ(0)` compact, `Fᵢ ⊆ U` closed
  obtain ⟨F, hFc, hFU, hFun, -⟩ := hU.exists_iUnion_isClosed
  have hK : ∀ p : ℕ × ℕ, IsCompact (F p.1 ∩ closedBall (0 : Euclid P) p.2) := fun p =>
    (isCompact_closedBall _ _).inter_left (hFc p.1)
  have hKU : ∀ p : ℕ × ℕ, F p.1 ∩ closedBall (0 : Euclid P) p.2 ⊆ U := fun p =>
    inter_subset_left.trans (hFU p.1)
  have hcover : U ⊆ ⋃ p : ℕ × ℕ, F p.1 ∩ closedBall (0 : Euclid P) p.2 := by
    intro x hx
    rw [← hFun] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge (dist x 0)
    exact mem_iUnion.2 ⟨(i, j), hi, mem_closedBall.2 hj⟩
  -- Step 3: `μ(E' ∩ Kₚ) = 0` for every `p`, by inner regularity of the finite `μ⌞Kₚ`
  have hpiece : ∀ p : ℕ × ℕ, μ (E' ∩ (F p.1 ∩ closedBall (0 : Euclid P) p.2)) = 0 := by
    intro p
    set K := F p.1 ∩ closedBall (0 : Euclid P) p.2
    have : IsFiniteMeasure (μ.restrict K) :=
      isFiniteMeasure_restrict.2 (hfin K (hK p) (hKU p)).ne
    by_contra hne
    have hpos : 0 < μ.restrict K E' := by
      rw [Measure.restrict_apply hE'm]
      exact pos_iff_ne_zero.2 hne
    obtain ⟨C, hCE', hCc, hCpos⟩ := hE'm.exists_lt_isCompact_of_ne_top (measure_ne_top _ _) hpos
    rw [Measure.restrict_apply hCc.isClosed.measurableSet] at hCpos
    have hC0 : μ (C ∩ K) = 0 :=
      hnull (C ∩ K) (hCc.inter_right (hK p).isClosed) (inter_subset_right.trans (hKU p))
        (measure_mono_null (inter_subset_left.trans hCE') hE')
    exact hCpos.ne' hC0
  -- Step 4: `E ⊆ E' ⊆ Uᶜ ∪ ⋃ₚ (E' ∩ Kₚ)`, a `μ`-null set
  refine measure_mono_null hEE' (measure_mono_null (t := Uᶜ ∪
    ⋃ p : ℕ × ℕ, E' ∩ (F p.1 ∩ closedBall (0 : Euclid P) p.2)) ?_
    (measure_union_null hUc (measure_iUnion_null hpiece)))
  intro x hx
  by_cases hxU : x ∈ U
  · obtain ⟨p, hp⟩ := mem_iUnion.1 (hcover hxU)
    exact Or.inr (mem_iUnion.2 ⟨p, hx, hp⟩)
  · exact Or.inl hxU
/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))
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
/-- **Kronecker property of the determinant covectors** (Simon 6.1, chapter-06.txt lines 22–47:
`dxʲ(v) = vⱼ`, `dx^{i₁} ∧ ⋯ ∧ dx^{iₙ}(v₁, …, vₙ) = det(dx^{iₖ}(vⱼ))` (1.1), and
`ω_α = ω(e_{i₁}, …, e_{iₙ})` for the basis `{dx^α : α ∈ I_{n,P}}` (1.2)): if `I`, `J` are strictly
increasing and `θ(v) = det (v_j(I k))_{k,j}`, then `θ(e_{J 1}, …, e_{J n}) = δ_{IJ}`.  The matrix
of `θ(e_J)` has entries `[I k = J j]`.  It is the identity if `I = J`.  Otherwise some `I k₀` is
not a value of `J` (else `range I ⊆ range J`, both have `n` elements, so the ranges agree and the
strictly increasing maps agree), and row `k₀` vanishes. -/
theorem Submission.cmr_cc_det_covector_basis_kronecker : ∀ (P n : ℕ) (I J : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → StrictMono J → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → θ (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 := by
  intro P n I J θ hI hJ hθ
  -- Step 1: `θ(e_J) = det M` with `M k j = e_{J j}(I k)`
  rw [hθ]
  -- Step 2: `M k j = e_{J j}(I k) = if I k = J j then 1 else 0`
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hIJ : I = J
  · -- Step 3: if `I = J`, injectivity of `J` gives `M = 1`, so `det M = 1`
    rw [ite_eq_left hIJ]
    subst hIJ
    refine (congrArg Matrix.det ?_).trans Matrix.det_one
    ext k j
    simp only [Matrix.of_apply, Matrix.one_apply, hI.injective.eq_iff]
  · -- Step 4: if `I ≠ J`, some `I k₀` is not a value of `J`: otherwise `range I ⊆ range J`,
    -- both ranges have `n` elements, so they are equal and `I = J`
    rw [ite_eq_right hIJ]
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, I k₀ ∉ Set.range J := by
      by_contra hcon
      have hsub : Set.range I ⊆ Set.range J := by
        rintro _ ⟨k, rfl⟩
        by_contra hk
        exact hcon ⟨k, hk⟩
      have hcard : (Set.range J).ncard ≤ (Set.range I).ncard :=
        ((Set.ncard_range_of_injective hJ.injective).trans
          (Set.ncard_range_of_injective hI.injective).symm).le
      exact hIJ ((hI.range_inj_of_wellFoundedLT hJ).1 (Set.eq_of_subset_of_ncard_le hsub hcard))
    -- Step 5: row `k₀` of `M` vanishes, so `det M = 0`
    refine Matrix.det_eq_zero_of_row_eq_zero k₀ fun j => ?_
    simp only [Matrix.of_apply]
    exact ite_eq_right fun hEq => hk₀ ⟨j, hEq.symm⟩
/-- **Jacobi's trace identity for column replacement** (parent fact (F3) of the divergence form
of the mass representation).  Let `M = (u j k)_{k,j}` be the matrix with columns `u j`.
Replacing column `i` by `A (u i)` and summing the determinants over `i` gives `tr(A) · det M`.
With `B` the matrix of `A` in the standard basis `e` of `ℝⁿ`, column `i` of `B M` is `A (u i)`,
so by Cramer's rule the `i`-th determinant is `(adj M · B M)_{i,i}`; then
`tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr B = det M · tr A`. -/
theorem Submission.cmr_df_det_update_sum_trace : ∀ (n : ℕ) (A : Euclid n →ₗ[ℝ] Euclid n) (u : Fin n → Euclid n), ∑ i : Fin n, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) = LinearMap.trace ℝ (Euclid n) A * Matrix.det (Matrix.of fun k j => u j k) := by
  intro n A u
  -- the standard basis `e` of `ℝⁿ`, the matrix `M` with columns `u j`, the matrix `B` of `A`
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => u j k
  let B := LinearMap.toMatrix e e A
  -- Step 1: `A (u i) k = (B M)_{k,i}`, from `B *ᵥ e.repr x = e.repr (A x)` and `e.repr x = x`
  have hA : ∀ i k, A (u i) k = (B * M) k i := by
    intro i k
    have := congrFun (LinearMap.toMatrix_mulVec_repr e e A (u i)) k
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, e, B, M] using this.symm
  -- Step 2: the `i`-th summand is `det (M.updateCol i (B M)_{·,i}) = (adj M · B M)_{i,i}` (Cramer)
  have hcol : ∀ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
      (M.adjugate * (B * M)) i i := by
    intro i
    have h1 : (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
        M.updateCol i (fun k => (B * M) k i) := by
      ext k j
      by_cases hj : j = i
      · subst hj
        simp [hA]
      · simp [hj, M]
    rw [h1, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  -- Step 3: `tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr A`
  calc ∑ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k)
      = Matrix.trace (M.adjugate * (B * M)) := by
        simp only [hcol, Matrix.trace, Matrix.diag_apply]
    _ = Matrix.trace (B * (M * M.adjugate)) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = LinearMap.trace ℝ (Euclid n) A * M.det := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
          LinearMap.trace_eq_matrix_trace ℝ e A, mul_comm]

/-- **Coordinate form of `Σᵢ (-1)ⁱ θ(L wᵢ, w₀, …, ŵᵢ, …, w_m) = tr(A) θ(w)`** (the trace step of
the divergence-form computation behind the mass representation in Simon 7.2.4).  Let `θ` be the
`(m+1)`-covector `θ(v) = det (v j (I k))_{k,j}` on `ℝᴾ`, let `A` be linear on `ℝ^{m+1}`, and let
`L : ℝᴾ → ℝᴾ` satisfy `(L v)(I k) = (A (p v))_k` with `p v = (v (I k))_k`.  Moving `L wᵢ` from
the front to slot `i` costs `(-1)ⁱ`, so the `i`-th term is `θ(w)` with `wᵢ` replaced by `L wᵢ`.
In the coordinates `uⱼ = p wⱼ` it is the determinant of `u` with its `i`-th column replaced by
`A uᵢ`.  Jacobi's identity `Submission.cmr_df_det_update_sum_trace` sums these determinants to
`tr(A) det u`, and `det u = θ(w)`. -/
theorem Submission.cmr_df_cons_sum_trace : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (L : Euclid P → Euclid P), (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → (∀ (v : Euclid P) (k : Fin (m + 1)), L v (I k) = A (WithLp.toLp 2 (fun k' => v (I k'))) k) → ∀ w : Fin (m + 1) → Euclid P, ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons (L (w i)) (i.removeNth w)) = LinearMap.trace ℝ (Euclid (m + 1)) A * θ w := by
  intro P m I θ A L hθ hL w
  -- Step 1: sign rule, `(-1)ⁱ θ(x, w₀, …, ŵᵢ, …, w_m) = θ(w with wᵢ replaced by x)`
  have h1 : ∀ (i : Fin (m + 1)) (x : Euclid P),
      (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons x (i.removeNth w)) = θ (Function.update w i x) := by
    intro i x
    rw [← Fin.insertNth_removeNth, ContinuousAlternatingMap.map_insertNth, zsmul_eq_mul]
    push_cast
    rfl
  -- the coordinate columns `uⱼ = p wⱼ ∈ ℝ^{m+1}`
  let u : Fin (m + 1) → Euclid (m + 1) := fun j => WithLp.toLp 2 (fun k => w j (I k))
  -- Step 2: the `i`-th term is `det u` with its `i`-th column replaced by `A uᵢ`, entrywise
  have h2 : ∀ i : Fin (m + 1), θ (Function.update w i (L (w i))) =
      Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) := by
    intro i
    rw [hθ]
    congr 1
    ext k j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, u]
    · simp [Function.update_of_ne hj, u]
  -- Step 4: `det u = θ(w)`
  have h4 : Matrix.det (Matrix.of fun k j => u j k) = θ w := (hθ w).symm
  -- Step 3: Jacobi's identity
  simp_rw [h1, h2]
  rw [Submission.cmr_df_det_update_sum_trace (m + 1) A u, h4]
/-- **Exterior derivative of a function times a contracted covector** (used for the divergence
form in the mass-representation step of Simon 7.2.4).  If `b : ℝᴾ → ℝ` and `G : ℝᴾ → ℝᴾ` are
differentiable at `x` and `θ` is a fixed `(m+1)`-covector, then `η(y) = b(y) θ(G(y), ·)` has
`dη(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ (Db(x)wᵢ · θ(G(x), ŵᵢ) + b(x) · θ(DG(x)wᵢ, ŵᵢ))`, where `ŵᵢ` is
`(w₀, …, w_m)` with `wᵢ` removed: each term of the alternating sum differentiates
`y ↦ b(y) θ(G(y), ŵᵢ)` by the product and chain rules. -/
theorem Submission.cmr_df_extDeriv_smul_curryLeft : ∀ (P m : ℕ) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ) (G : Euclid P → Euclid P) (x : Euclid P), DifferentiableAt ℝ b x → DifferentiableAt ℝ G x → ∀ w : Fin (m + 1) → Euclid P, exteriorDerivative (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w))) := by
  intro P m θ b G x hb hG w
  have hc : DifferentiableAt ℝ (fun y => ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    (ContinuousAlternatingMap.curryLeft θ).differentiableAt.comp x hG
  have hη : DifferentiableAt ℝ (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    hb.smul hc
  rw [exteriorDerivative_apply hη w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_continuousAlternatingMap_apply_const_apply hη, fderiv_fun_smul hb hc,
    fderiv_fun_comp x (ContinuousAlternatingMap.curryLeft θ).differentiableAt hG,
    ContinuousLinearMap.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    smul_eq_mul, zsmul_eq_mul]
  simp only [Matrix.vecCons]
  push_cast
  ring
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
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]

/-- **Simon 6.1.2, 6.1.5, 6.1.15** (the coefficient norm is Euclidean): `n`-covectors on `ℝᴾ`
with `|α|_E = (Σ_I α(e_I)²)^{1/2}`, `I` strictly increasing, form a Euclidean space `ℝᵈ`.  The
coefficient map `A α = (α(e_I))_I` (zero off the increasing `I`) into `ℝ^{Fin n → Fin P}` has
`‖A α‖ = |α|_E`, and it is injective by the Gram bound `|α v| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}`.
An orthonormal basis of `range A` identifies it isometrically with `ℝᵈ`; then covectors are
finite-dimensional, so this linear equivalence is continuous. -/
theorem Submission.cmr_covector_euclidean_equiv : ∀ (P n : ℕ), ∃ (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖ := by
  intro P n
  -- the coefficient map `A α = (α(e_I))_I`, zero off the strictly increasing `I`
  let A : Covector (Euclid P) n →ₗ[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    { toFun := fun α => WithLp.toLp 2 (fun I => if StrictMono I then
        α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) else 0)
      map_add' := fun α β => by
        ext I
        simp only [PiLp.add_apply, ContinuousAlternatingMap.add_apply]
        split_ifs <;> simp
      map_smul' := fun t α => by
        ext I
        simp only [PiLp.smul_apply, ContinuousAlternatingMap.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        split_ifs <;> simp }
  -- `‖A α‖ = |α|_E`
  have hnorm : ∀ α, ‖A α‖ = covectorEuclideanNorm α := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [A, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    split_ifs <;> simp
  -- `A` is injective: `|α|_E = 0` forces `α v = 0` by the Gram bound
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have h0 : covectorEuclideanNorm α = 0 := by rw [← hnorm, hα, norm_zero]
    ext v
    have hv := (Submission.covectorEuclideanNorm_gram_bounds P n).1 α v
    rw [h0, zero_mul] at hv
    simpa using abs_nonpos_iff.mp hv
  -- identify `range A` isometrically with `ℝᵈ` through an orthonormal basis
  let S := LinearMap.range A
  let b := stdOrthonormalBasis ℝ S
  let e₀ : Covector (Euclid P) n ≃ₗ[ℝ] S := LinearEquiv.ofInjective A hinj
  let c₀ : Covector (Euclid P) n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S)) :=
    e₀.trans b.repr.toLinearEquiv
  have hc₀ : ∀ α, ‖c₀ α‖ = covectorEuclideanNorm α := by
    intro α
    have h1 : c₀ α = b.repr (e₀ α) := rfl
    rw [h1, LinearIsometryEquiv.norm_map, ← Submodule.norm_coe, LinearEquiv.ofInjective_apply,
      hnorm]
  -- covectors are finite-dimensional, so `c₀` is continuous
  have : FiniteDimensional ℝ (Covector (Euclid P) n) := LinearEquiv.finiteDimensional c₀.symm
  refine ⟨Module.finrank ℝ S, c₀.toContinuousLinearEquiv, fun α => ?_⟩
  rw [LinearEquiv.coe_toContinuousLinearEquiv', hc₀]
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
/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Radial retraction onto the unit ball of `N = covectorEuclideanNorm`** (step 4 of the
approximation of a unit covector field by admissible test forms, used for Simon Ch. 6,
Remark 3.2(3)).  `ρ(a) = max(1, N(a))⁻¹ a` is continuous, `ρ(0) = 0`, `N(ρ(a)) ≤ 1`, and
`N(ρ(a) − b) ≤ 2 N(a − b)` whenever `N(b) ≤ 1`: if `N(a) > 1` then
`N(a − ρ(a)) = N(a) − 1 ≤ N(a − b)`, and the triangle inequality gives the factor `2`. -/
theorem Submission.rsd_mw_tfa_retraction : ∀ (P n : ℕ), ∃ ρ : Covector (Euclid P) n → Covector (Euclid P) n, Continuous ρ ∧ ρ 0 = 0 ∧ (∀ a, covectorEuclideanNorm (ρ a) ≤ 1) ∧ ∀ a b, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm (ρ a - b) ≤ 2 * covectorEuclideanNorm (a - b) := by
  intro P n
  obtain ⟨htri, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- the rescaling factor `max 1 (N a) ≥ 1` never vanishes
  have hpos : ∀ a : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm a) :=
    fun a => one_pos.trans_le (le_max_left _ _)
  refine ⟨fun a => (max 1 (covectorEuclideanNorm a))⁻¹ • a,
    ((continuous_const.max hcont).inv₀ fun a => (hpos a).ne').smul continuous_id, by simp,
    fun a => ?_, fun a b hb => ?_⟩
  · -- `N (ρ a) = N a / max 1 (N a) ≤ 1`
    dsimp only
    rw [hsmul, abs_of_pos (inv_pos.mpr (hpos a)), inv_mul_le_iff₀ (hpos a), mul_one]
    exact le_max_right _ _
  dsimp only
  rcases le_or_gt (covectorEuclideanNorm a) 1 with ha | ha
  · -- `N a ≤ 1`: `ρ a = a`
    rw [max_eq_left ha, inv_one, one_smul]
    linarith [covectorEuclideanNorm_nonneg (a - b)]
  -- `r := N a > 1`: `ρ a = r⁻¹ a`
  set r := covectorEuclideanNorm a with hr
  rw [max_eq_right ha.le]
  -- `N (a - ρ a) = (1 - r⁻¹) r = r - 1`
  have h₁ : covectorEuclideanNorm (a - r⁻¹ • a) = r - 1 := by
    rw [show a - r⁻¹ • a = (1 - r⁻¹) • a by module, hsmul,
      abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ ha.le)), sub_mul, one_mul, ← hr,
      inv_mul_cancel₀ (one_pos.trans ha).ne']
  -- `r ≤ N (a - b) + N b ≤ N (a - b) + 1`
  have h₂ : r ≤ covectorEuclideanNorm (a - b) + 1 :=
    calc r = covectorEuclideanNorm (a - b + b) := by rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (a - b) + covectorEuclideanNorm b := htri _ _
      _ ≤ covectorEuclideanNorm (a - b) + 1 := by linarith
  calc covectorEuclideanNorm (r⁻¹ • a - b)
      = covectorEuclideanNorm (-(a - r⁻¹ • a) + (a - b)) := by congr 1; abel
    _ ≤ covectorEuclideanNorm (-(a - r⁻¹ • a)) + covectorEuclideanNorm (a - b) := htri _ _
    _ = r - 1 + covectorEuclideanNorm (a - b) := by rw [covectorEuclideanNorm_neg, h₁]
    _ ≤ 2 * covectorEuclideanNorm (a - b) := by linarith

/-- **`L¹(ν)` approximation of a unit covector field by continuous compactly supported unit
fields** (steps 3–4 of the `L¹(ν)` approximation of a unit covector field by admissible test
forms).  Let `ν` be a finite Borel measure on `ℝᴾ` and `β` a `ν`-integrable `n`-covector field
with `N(β) ≤ 1` `ν`-a.e., `N = covectorEuclideanNorm`.  Continuous compactly supported maps are
dense in `L¹(ν)` (`ν` is regular), so one of them, `g₀`, has `∫ ‖β − g₀‖ dν ≤ η`.  With `ρ` the
retraction onto `{N ≤ 1}`, `g = ρ ∘ g₀` is continuous, compactly supported (`ρ 0 = 0`), has
`N(g) ≤ 1`, and `N(g − β) ≤ 2 N(g₀ − β) ≤ 2C ‖β − g₀‖` a.e., so `∫ N(g − β) dν ≤ 2Cη < δ`. -/
theorem Submission.rsd_mw_tfa_continuous_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g x - β x)) ∂ν < ENNReal.ofReal δ := by
  intro P n ν β hν hβ hβ1 δ hδ
  -- Step 1: the constant `C` of `norm_props` (iii), the retraction `ρ`, and the tolerance `η`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨ρ, hρc, hρ0, hρ1, hρ2⟩ := Submission.rsd_mw_tfa_retraction P n
  set η : ℝ := δ / (2 * (2 * C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: continuous compactly supported maps are dense in `L¹(ν)` (`ν` is finite, hence
  -- regular).  The contract does not import `Integrable.exists_hasCompactSupport_lintegral_sub_le`,
  -- so this goes through `MemLp.induction_dense`: `c • 1_s` is approximated by `φ • c`, with `φ`
  -- a Urysohn function for compact `K ⊆ s ⊆ U` open, `ν (U \ K)` small.
  have hind : ∀ (c : Covector (Euclid P) n) ⦃s : Set (Euclid P)⦄, MeasurableSet s → ν s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : Euclid P → Covector (Euclid P) n,
        eLpNorm (g - s.indicator fun _ => c) 1 ν ≤ ε ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro c s hs hsν ε hε
    obtain ⟨t, ht0, htε⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (a := 2 * ‖c‖ₑ)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top) hε
    have ht : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht0.ne'
    -- compact `K ⊆ s ⊆ U` open with `ν (s \ K) < t` and `ν (U \ s) < t`
    obtain ⟨K, hKs, hK, hsK⟩ := hs.exists_isCompact_sdiff_lt hsν.ne ht
    obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hsν.ne ht
    -- Urysohn: `φ = 1` on `K`, `φ = 0` off `U`, `0 ≤ φ ≤ 1`, compact support
    obtain ⟨φ, hφK, hφU, hφs, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hgc : Continuous fun x => φ x • c := φ.continuous.smul continuous_const
    refine ⟨fun x => φ x • c, ?_, hgc, hφs.smul_right⟩
    -- pointwise `‖φ x • c - 1_s(x) c‖ₑ ≤ 1_{U \ K}(x) ‖c‖ₑ`
    have hle : ∀ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ≤
        (U \ K).indicator (fun _ => ‖c‖ₑ) x := by
      intro x
      rw [← ofReal_norm]
      by_cases hxK : x ∈ K
      · simp [hφK hxK, hKs hxK]
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxK), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨h0, h1⟩ := hφ01 x
        by_cases hxs : x ∈ s
        · rw [Pi.sub_apply, indicator_of_mem hxs, show φ x • c - c = (φ x - 1) • c by module,
            norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          nlinarith [norm_nonneg c]
        · rw [Pi.sub_apply, indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg h0]
          nlinarith [norm_nonneg c]
      · simp [hφU hxU, show x ∉ s from fun h => hxU (hsU h), hxU]
    rw [eLpNorm_one_eq_lintegral_enorm
      (hgc.aestronglyMeasurable.sub (stronglyMeasurable_const.indicator hs).aestronglyMeasurable)]
    calc ∫⁻ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ∂ν
        ≤ ∫⁻ x, (U \ K).indicator (fun _ => ‖c‖ₑ) x ∂ν := lintegral_mono hle
      _ = ‖c‖ₑ * ν (U \ K) := lintegral_indicator_const (hU.measurableSet.diff hK.measurableSet) _
      _ ≤ ‖c‖ₑ * (ν (U \ s) + ν (s \ K)) := by
          gcongr
          refine (measure_mono fun x hx => ?_).trans (measure_union_le (U \ s) (s \ K))
          by_cases hxs : x ∈ s
          · exact Or.inr ⟨hxs, hx.2⟩
          · exact Or.inl ⟨hx.1, hxs⟩
      _ ≤ ‖c‖ₑ * (t + t) := by gcongr
      _ = t * (2 * ‖c‖ₑ) := by ring
      _ ≤ ε := htε.le
  -- the density statement for `β`, with tolerance `η`
  obtain ⟨g₀, hg₀, hg₀c, hg₀s⟩ := (memLp_one_iff_integrable.2 hβ).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.mpr hη0).ne'
  rw [eLpNorm_one_eq_lintegral_enorm (hβ.aestronglyMeasurable.sub hg₀c.aestronglyMeasurable)] at hg₀
  -- Step 3: `g := ρ ∘ g₀`
  refine ⟨ρ ∘ g₀, hρc.comp hg₀c, hg₀s.comp_left hρ0, fun x => hρ1 _, ?_⟩
  -- Step 4: pointwise a.e. estimate
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x))
      ≤ ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ := by
    filter_upwards [hβ1] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc covectorEuclideanNorm ((ρ ∘ g₀) x - β x)
        ≤ 2 * covectorEuclideanNorm (g₀ x - β x) := hρ2 _ _ hx
      _ ≤ 2 * (C * ‖g₀ x - β x‖) := by gcongr; exact hC _
      _ = 2 * C * ‖β x - g₀ x‖ := by rw [norm_sub_rev]; ring
  -- Step 5: integration
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x)) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * C) * ∫⁻ x, ‖β x - g₀ x‖ₑ ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * C) * ENNReal.ofReal η := by gcongr; exact hg₀
    _ = ENNReal.ofReal (2 * C * η) := (ENNReal.ofReal_mul (by positivity)).symm
    -- Step 6: arithmetic
    _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hδ, hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Smooth uniform approximation keeping the unit bound** (smoothing step in the proof of
`M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is `covectorEuclideanNorm`).  Let
`η := δ/(2C + 1)`, where `|·|_E ≤ C‖·‖` (`Submission.rsd_mw_tfa_norm_props`).  A continuous
compactly supported covector field `g` with `|g|_E ≤ 1` is uniformly continuous, so
`‖g y − g x‖ < η` when `dist y x < r`.  Mollifying, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth
bump `φ ≥ 0` with `support φ = B_r(0)` is a `C^∞` field with `‖h' − g‖ ≤ η`; then
`|h' − g|_E ≤ Cη` and `|h'|_E ≤ 1 + Cη`.  The rescaled field `h = (1 + Cη)⁻¹h'` has `|h|_E ≤ 1`
and `|h − h'|_E = Cη(1 + Cη)⁻¹|h'|_E ≤ Cη`, hence `|h − g|_E ≤ 2Cη ≤ δ`. -/
theorem Submission.rsd_mw_tfa_smooth_uniform_approx : ∀ (P n : ℕ) (g : Euclid P → Covector (Euclid P) n), Continuous g → HasCompactSupport g → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ h : Euclid P → Covector (Euclid P) n, ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ x, covectorEuclideanNorm (h x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (h x - g x) ≤ δ := by
  intro P n g hgc hgs hg1 δ hδ
  -- `N := covectorEuclideanNorm` is subadditive, absolutely homogeneous and `N ≤ C ‖·‖`
  obtain ⟨htri, hsmul, ⟨C, hC0, hCle⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: the tolerance `η = δ / (2C + 1)`
  set η : ℝ := δ / (2 * C + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hCη : 0 ≤ C * η := mul_nonneg hC0 hη0.le
  -- Step 2: `g` is uniformly continuous: `‖g y - g x‖ < η` whenever `dist y x < r`
  obtain ⟨r, hr, hgr⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη0
  -- Step 3: mollify, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ`, `support φ = B_r(0)`
  let φ : ContDiffBump (0 : Euclid P) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hr
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 r := hψφ.trans φ.support_eq.subset
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  obtain ⟨h', hh's, hh'g⟩ : ∃ h' : Euclid P → Covector (Euclid P) n,
      ContDiff ℝ (⊤ : ℕ∞) h' ∧ ∀ x, dist (h' x) (g x) ≤ η :=
    ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      (φ.hasCompactSupport.mono hψφ).contDiff_convolution_left _ (φ.contDiff.div_const _)
        hgc.locallyIntegrable,
      fun x => dist_convolution_le hη0.le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgr (mem_ball.mp hy)).le⟩
  -- Step 4: `N(h' - g) ≤ Cη` and `N(h') ≤ 1 + Cη`
  have hdiff : ∀ x, covectorEuclideanNorm (h' x - g x) ≤ C * η := fun x =>
    (hCle _).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hh'g x) hC0)
  have hh'1 : ∀ x, covectorEuclideanNorm (h' x) ≤ 1 + C * η := fun x =>
    calc covectorEuclideanNorm (h' x) = covectorEuclideanNorm ((h' x - g x) + g x) := by
          rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (h' x - g x) + covectorEuclideanNorm (g x) := htri _ _
      _ ≤ C * η + 1 := add_le_add (hdiff x) (hg1 x)
      _ = 1 + C * η := add_comm _ _
  -- Step 5: rescale by `s = (1 + Cη)⁻¹ ∈ (0, 1]`
  have hpos : 0 < 1 + C * η := by linarith
  have hne : 1 + C * η ≠ 0 := hpos.ne'
  set s : ℝ := (1 + C * η)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr hpos
  refine ⟨fun x => s • h' x, hh's.const_smul s, fun x => ?_, fun x => ?_⟩
  · show covectorEuclideanNorm (s • h' x) ≤ 1
    rw [hsmul, abs_of_pos hs0, hs, inv_mul_le_iff₀ hpos, mul_one]
    exact hh'1 x
  · show covectorEuclideanNorm (s • h' x - g x) ≤ δ
    -- Step 6: `N(s h' - h') = |s - 1| N(h') = Cη s N(h') ≤ Cη`
    have hsh : s • h' x - h' x = (s - 1) • h' x := by module
    have hs1 : |s - 1| = C * η * s := by
      have hle : s ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      rw [abs_of_nonpos (by linarith), hs]
      field_simp
      ring
    have h6 : covectorEuclideanNorm (s • h' x - h' x) ≤ C * η := by
      rw [hsh, hsmul, hs1]
      calc C * η * s * covectorEuclideanNorm (h' x) ≤ C * η * s * (1 + C * η) :=
            mul_le_mul_of_nonneg_left (hh'1 x) (mul_nonneg hCη hs0.le)
        _ = C * η := by rw [hs]; field_simp
    -- Step 7: `N(s h' - g) ≤ N(s h' - h') + N(h' - g) ≤ 2Cη ≤ δ`
    calc covectorEuclideanNorm (s • h' x - g x)
        = covectorEuclideanNorm ((s • h' x - h' x) + (h' x - g x)) := by
          rw [sub_add_sub_cancel]
      _ ≤ covectorEuclideanNorm (s • h' x - h' x) + covectorEuclideanNorm (h' x - g x) :=
          htri _ _
      _ ≤ C * η + C * η := add_le_add h6 (hdiff x)
      _ ≤ δ := by
          have h2 : 0 < 2 * C + 1 := by linarith
          have h2C : C * η + C * η = 2 * C * δ / (2 * C + 1) := by rw [hη]; ring
          rw [h2C, div_le_iff₀ h2]
          nlinarith

/-- **Test forms approximating a unit-bounded integrable covector field in `L¹(ν)`** (the
approximation behind `M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is
`covectorEuclideanNorm`).  Let `m = ν(ℝᴾ)` and `δ = ε/(4(m + 1))`.  The smooth cut-off `χ` of
`Submission.rsd_mw_tfa_smooth_cutoff` satisfies `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`.  The
continuous field `g₁` of `Submission.rsd_mw_tfa_continuous_approx` satisfies `|g₁|_E ≤ 1` and
`∫ |g₁ − β|_E dν < ε/4`.  Its smoothing `g₂` (`Submission.rsd_mw_tfa_smooth_uniform_approx`)
satisfies `|g₂|_E ≤ 1` and `|g₂ − g₁|_E ≤ δ`.  Then `ω = χ g₂` is a test form, `tsupport ω ⊆ V`
and `|ω|_E ≤ 1`.  For a.e. `x`, `|ω − β|_E ≤ δ + |g₁ − β|_E` where `χ = 1`, and
`|ω − β|_E ≤ 2` where `χ ≠ 1`.  Integrating,
`∫ |ω − β|_E dν ≤ δm + ∫ |g₁ − β|_E dν + 2ν{χ ≠ 1} < ε/4 + ε/4 + ε/4 < ε`. -/
theorem Submission.rsd_mw_exists_testForm_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ ε : ℝ, 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε := by
  intro P n ν V β hν hV hVc hβ hβ1 ε hε
  -- `N := covectorEuclideanNorm` is subadditive and absolutely homogeneous
  obtain ⟨htri, hsmul, -, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: a smooth cut-off `χ` with `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`
  obtain ⟨χ, hχs, hχc, hχV, hχ01, hχν⟩ :=
    Submission.rsd_mw_tfa_smooth_cutoff P ν V hν hV hVc (ε / 8) (by positivity)
  -- Step 2: a continuous compactly supported `g₁` with `N(g₁) ≤ 1` and `∫ N(g₁ - β) dν < ε/4`
  obtain ⟨g₁, hg₁c, hg₁s, hg₁1, hg₁β⟩ :=
    Submission.rsd_mw_tfa_continuous_approx P n ν β hν hβ hβ1 (ε / 4) (by positivity)
  -- Step 3: a smooth `g₂` with `N(g₂) ≤ 1` and `N(g₂ - g₁) ≤ δ = ε/(4(m + 1))`, `m = ν(ℝᴾ)`
  set m : ℝ := (ν univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (4 * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g₂, hg₂s, hg₂1, hg₂g₁⟩ :=
    Submission.rsd_mw_tfa_smooth_uniform_approx P n g₁ hg₁c hg₁s hg₁1 δ hδ0
  -- Step 4: `ω = χ g₂` is a test form with `tsupport ω ⊆ V` and `N(ω) ≤ 1`
  have hω1 : ∀ x, covectorEuclideanNorm (χ x • g₂ x) ≤ 1 := fun x => by
    rw [hsmul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hg₂1 x)
  refine ⟨fun x => χ x • g₂ x, ⟨hχs.smul hg₂s, hχc.smul_right⟩,
    (tsupport_smul_subset_left χ g₂).trans hχV, hω1, ?_⟩
  -- Step 5: a.e., `N(ω - β) ≤ δ + N(g₁ - β)` where `χ = 1` and `N(ω - β) ≤ 2` on `S = {χ ≠ 1}`
  set S : Set (Euclid P) := {x | χ x ≠ 1}
  have hSm : MeasurableSet S := (isOpen_ne_fun hχs.continuous continuous_const).measurableSet
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ≤
      ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
        S.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    filter_upwards [hβ1] with x hx
    by_cases h1 : χ x = 1
    · rw [indicator_of_notMem (not_not.mpr h1), add_zero,
        ← ENNReal.ofReal_add hδ0.le (covectorEuclideanNorm_nonneg _), h1, one_smul]
      refine ENNReal.ofReal_le_ofReal ?_
      calc covectorEuclideanNorm (g₂ x - β x)
          = covectorEuclideanNorm ((g₂ x - g₁ x) + (g₁ x - β x)) := by rw [sub_add_sub_cancel]
        _ ≤ covectorEuclideanNorm (g₂ x - g₁ x) + covectorEuclideanNorm (g₁ x - β x) :=
          htri _ _
        _ ≤ δ + covectorEuclideanNorm (g₁ x - β x) := by linarith [hg₂g₁ x]
    · rw [indicator_of_mem h1]
      refine le_add_left (le_of_le_of_eq (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_ofNat 2))
      calc covectorEuclideanNorm (χ x • g₂ x - β x)
          = covectorEuclideanNorm (χ x • g₂ x + -β x) := by rw [sub_eq_add_neg]
        _ ≤ covectorEuclideanNorm (χ x • g₂ x) + covectorEuclideanNorm (-β x) := htri _ _
        _ ≤ 2 := by rw [covectorEuclideanNorm_neg]; linarith [hω1 x]
  -- Step 6: integrate, `∫ N(ω - β) dν ≤ δm + ∫ N(g₁ - β) dν + 2ν(S) < 3ε/4`
  have hδm : ENNReal.ofReal δ * ν univ ≤ ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← hm, ← ENNReal.ofReal_mul hδ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc δ * m ≤ δ * (m + 1) := by nlinarith
      _ = ε / 4 := by rw [hδ]; field_simp
  have hS2 : 2 * ν S < ENNReal.ofReal (ε / 4) := by
    calc 2 * ν S = ν S + ν S := two_mul _
      _ < ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) := ENNReal.add_lt_add hχν hχν
      _ = ENNReal.ofReal (ε / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
          S.indicator (fun _ => (2 : ℝ≥0∞)) x) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal δ * ν univ +
          ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) ∂ν + 2 * ν S := by
        rw [lintegral_add_right _ (measurable_const.indicator hSm),
          lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hSm]
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add_of_le_of_lt
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hδm hg₁β) hS2
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
/-- **Coordinate covectors `dx^I` exist and span** (Simon 6.1 (1.1)–(1.2); used for
`ω = Σ_α ω_α dx^α`): (a) for every `I : Fin n → Fin P` some `n`-covector `θ` has
`θ(v) = det (vⱼ(I k))_{k,j}`; (b) an `n`-vector `ζ` vanishing on these `θ` for every strictly
increasing `I` vanishes.  Fix `θ_I` by (a).  Since `θ_I(e_J) = δ_{IJ}` for strictly increasing
`I`, `J`, the remainder `α − Σ_I α(e_I) θ_I` of an `n`-covector `α` vanishes on every `e_J`.  So
its coefficient norm `|·|_E` is `0`, and as `|·|_E` is the norm of a linear isomorphism onto `ℝᵈ`,
`α = Σ_I α(e_I) θ_I`.  Hence `ζ α = Σ_I α(e_I) ζ θ_I = 0`. -/
theorem Submission.dimred_mbl_fnd_coordinate_covectors_span : ∀ (P n : ℕ), (∀ I : Fin n → Fin P, ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) ∧ ∀ ζ : MultiVector P n, (∀ (I : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ζ θ = 0) → ζ = 0 := by
  intro P n
  -- Step 1 (part (a)): the determinant covector exists for every `I`
  refine ⟨Submission.cmr_cc_det_covector_exists P n, fun ζ hζ => ?_⟩
  classical
  -- fix `θ I = dx^I` for every `I`
  choose θ hθ using Submission.cmr_cc_det_covector_exists P n
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- Step 2: `θ_I(e_J) = δ_{IJ}` for strictly increasing `I`, `J`
  have hδ : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      θ I (fun j => e (J j)) = if I = J then 1 else 0 :=
    fun I J hI hJ => Submission.cmr_cc_det_covector_basis_kronecker P n I J (θ I) hI hJ (hθ I)
  -- Step 3: `α = Σ_I α(e_I) θ_I` over strictly increasing `I`
  have hexp : ∀ α : Covector (Euclid P) n,
      α = ∑ I : Fin n → Fin P, if StrictMono I then α (fun i => e (I i)) • θ I else 0 := by
    intro α
    set α' := α - ∑ I : Fin n → Fin P, if StrictMono I then α (fun i => e (I i)) • θ I else 0
      with hα'
    -- `α'(e_J) = α(e_J) − Σ_I α(e_I) δ_{IJ} = 0` for strictly increasing `J`
    have hJ : ∀ J : Fin n → Fin P, StrictMono J → α' (fun j => e (J j)) = 0 := by
      intro J hJ
      rw [hα', ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.sum_apply,
        Finset.sum_eq_single J, ite_eq_left hJ, ContinuousAlternatingMap.smul_apply,
        hδ J J hJ hJ, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
      · intro I _ hIJ
        split_ifs with hI
        · rw [ContinuousAlternatingMap.smul_apply, hδ I J hI hJ, ite_eq_right hIJ, smul_zero]
        · rfl
      · intro h
        exact absurd (Finset.mem_univ J) h
    -- every term of `|α'|_E` vanishes, so `|α'|_E = 0`
    have hnorm : covectorEuclideanNorm α' = 0 := by
      unfold covectorEuclideanNorm
      rw [← he, Finset.sum_eq_zero fun I _ => ?_, Real.sqrt_zero]
      split_ifs with hI
      · rw [hJ I hI, sq, mul_zero]
      · rfl
    -- `|·|_E` is the norm of a linear isomorphism `c` onto `ℝᵈ`, so `c α' = 0` and `α' = 0`
    obtain ⟨d, c, hc⟩ := Submission.cmr_covector_euclidean_equiv P n
    have hc0 : c α' = 0 := norm_eq_zero.mp ((hc α').symm.trans hnorm)
    exact sub_eq_zero.mp (c.map_eq_zero_iff.mp hc0)
  -- Step 4 (part (b)): `ζ θ_I = 0` for strictly increasing `I`, so `ζ α = Σ_I α(e_I) ζ θ_I = 0`
  refine ContinuousLinearMap.ext fun α => ?_
  rw [zero_apply, hexp α, map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  split_ifs with hI
  · rw [map_smul, hζ I (θ I) hI (hθ I), smul_zero]
  · exact map_zero ζ
/-- **Test forms in `U` restrict to compactly supported continuous maps on `U`** (the maps
`g_ω(x) = c(ω(x))` to which the Riesz representation theorem is applied for
`T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T`, Simon Ch. 6, 2.7–2.8; here for any continuous `f` with `f 0 = 0`).
Let `val : U → ℝᴾ` be the inclusion and `K = tsupport ω`.  The map `G = f ∘ ω ∘ val` is
continuous, since `ω` is smooth.  `K` is compact and `K ⊆ U = range val`, so `val⁻¹(K)` is
compact because `val` is inducing.  Off `val⁻¹(K)`, `ω(val x) = 0` and `G x = f 0 = 0`.  So `G`
has compact support in the Hausdorff space `U`, and `g = G ∈ C_c(U, ℝᵈ)`. -/
theorem Submission.cmrc_testForm_restrict_cc : ∀ (P n d : ℕ) (U : Set (Euclid P)) (f : Covector (Euclid P) n → EuclideanSpace ℝ (Fin d)), Continuous f → f 0 = 0 → ∀ ω : TestFormOn U n, ∃ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)), ∀ x : U, g x = f ((ω : DifferentialForm (Euclid P) n) x) := by
  intro P n d U f hf hf0 ω
  -- `ω` is smooth with compact support `K = tsupport ω ⊆ U`
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
  -- Step 1: `G = f ∘ ω ∘ val` is continuous
  have hGc : Continuous fun x : U => f ((ω : DifferentialForm (Euclid P) n) x) :=
    hf.comp ((ContDiff.continuous hωs).comp continuous_subtype_val)
  -- Step 2: `val⁻¹(K)` is compact, as `val` is inducing and `K ⊆ U = range val`
  have hK : IsCompact ((↑) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) n) : Set U) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hωc.isCompact
      (by rwa [Subtype.range_coe])
  -- Step 3: `G x = f 0 = 0` for `x ∉ val⁻¹(K)`, so `G` has compact support
  have hGs : HasCompactSupport fun x : U => f ((ω : DifferentialForm (Euclid P) n) x) :=
    HasCompactSupport.intro hK fun x hx =>
      (congrArg f (image_eq_zero_of_notMem_tsupport
        (show (x : Euclid P) ∉ tsupport (ω : DifferentialForm (Euclid P) n) from hx))).trans hf0
  exact ⟨⟨⟨fun x => f ((ω : DifferentialForm (Euclid P) n) x), hGc⟩, hGs⟩, fun _ => rfl⟩
/-- **Polar normalization of a vector Riesz density and push-forward to `ℝᴾ`** (the normalization
`|T⃗| = 1` `μ_T`-a.e. in `T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T`, Simon Ch. 6, 2.7, via the Riesz Representation
Theorem, Ch. 1, 4.14).  Write `ρ = ‖ν‖` and `ν̂ = ρ⁻¹ν` (with `0⁻¹ = 0`), so `ν = ρν̂`,
`‖ν̂‖ ≤ 1`, and `‖ν̂‖ = 1` where `ρ ≠ 0`.  Let `u` be `ν̂` extended by `0` off `U`,
`μ = val_*(ρμ₀)`, `ξ(y) = ⟨u(y), c(·)⟩` and `β = c⁻¹ ∘ u`.  Then `μ(Uᶜ) = 0`;
`μ(K) = ∫_{val⁻¹K} ‖ν‖ dμ₀ < ∞` for compact `K ⊆ U`; `|ξ(y)(α)| ≤ ‖c α‖ = |α|` by
Cauchy–Schwarz; `|β(y)| = ‖u(y)‖ ≤ 1`; `ξ(β) = ‖u‖² = 1` wherever the density `ρ` is nonzero;
and `∫ ξ(ω) dμ = ∫ ρ⟨ν̂, c(ω)⟩ dμ₀ = ∫ ⟨c(ω), ν⟩ dμ₀` for every `ω`. -/
theorem Submission.cmrc_polar_pushforward : ∀ (P n d : ℕ) (U : Set (Euclid P)) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (μ₀ : Measure U) (ν : U → EuclideanSpace ℝ (Fin d)), IsOpen U → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → Measurable ν → (∀ K : Set U, IsCompact K → IntegrableOn ν K μ₀) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ AEStronglyMeasurable β μ ∧ (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) ∧ (∀ x, covectorEuclideanNorm (β x) ≤ 1) ∧ (∀ᵐ x ∂μ, ξ x (β x) = 1) ∧ ∀ ω : DifferentialForm (Euclid P) n, ∫ x, inner ℝ (c (ω x)) (ν x) ∂μ₀ = ∫ x, ξ x (ω x) ∂μ := by
  intro P n d U c μ₀ ν hU hc hν hloc
  -- Step 1: polar decomposition `ν = ρ • ν̂` with `ρ = ‖ν‖`
  set ρ : U → ℝ := fun x => ‖ν x‖ with hρ_def
  set νh : U → EuclideanSpace ℝ (Fin d) := fun x => (ρ x)⁻¹ • ν x with hνh_def
  have hρm : Measurable ρ := hν.norm
  have hνhm : Measurable νh := hρm.inv.smul hν
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => norm_nonneg _
  have hdecomp : ∀ x, ν x = ρ x • νh x := by
    intro x
    by_cases h : ρ x = 0
    · have h0 : ν x = 0 := norm_eq_zero.mp h
      simp [hνh_def, h0]
    · simp [hνh_def, smul_smul, mul_inv_cancel₀ h]
  have hνh_one : ∀ x, ρ x ≠ 0 → ‖νh x‖ = 1 := by
    intro x h
    simp only [hνh_def]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (hρ0 x), inv_mul_cancel₀ h]
  have hνh_le : ∀ x, ‖νh x‖ ≤ 1 := by
    intro x
    by_cases h : ρ x = 0
    · have h0 : ν x = 0 := norm_eq_zero.mp h
      simp [hνh_def, h0]
    · exact (hνh_one x h).le
  -- Step 2: `val` is a measurable embedding (`U` is open) and the density `ρ` is measurable
  have hval : MeasurableEmbedding (Subtype.val : U → Euclid P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have hdens : Measurable fun x => ENNReal.ofReal (ρ x) := hρm.ennreal_ofReal
  -- Step 3: the unit field `u`, i.e. `ν̂` extended by `0` off `U`
  set u : Euclid P → EuclideanSpace ℝ (Fin d) := Function.extend Subtype.val νh 0 with hu_def
  have hu_val : ∀ x : U, u x = νh x := fun x => Subtype.val_injective.extend_apply _ _ x
  have hu_notin : ∀ y, y ∉ U → u y = 0 := by
    intro y hy
    rw [hu_def, Function.extend_apply']
    · rfl
    · rintro ⟨x, rfl⟩
      exact hy x.2
  have hum : Measurable u := hval.measurable_extend hνhm measurable_const
  have hu_le : ∀ y, ‖u y‖ ≤ 1 := by
    intro y
    by_cases hy : y ∈ U
    · have := hu_val ⟨y, hy⟩
      simp only at this
      rw [this]
      exact hνh_le _
    · rw [hu_notin y hy, norm_zero]
      exact zero_le_one
  -- Step 4: `μ = val_*(ρ μ₀)`, `ξ(y) = ⟨u(y), c(·)⟩` and `β = c⁻¹ ∘ u`
  refine ⟨(μ₀.withDensity fun x => ENNReal.ofReal (ρ x)).map Subtype.val,
    fun y => (innerSL ℝ (u y)).comp (c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d)),
    fun y => c.symm (u y), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) `val⁻¹(Uᶜ) = ∅`
    rw [hval.map_apply]
    have hpre : (Subtype.val : U → Euclid P) ⁻¹' Uᶜ = ∅ := by
      ext x
      simp
    rw [hpre, measure_empty]
  · -- (b) `μ(K) = ∫⁻_{val⁻¹K} ‖ν‖ₑ dμ₀ < ∞`, as `val⁻¹K` is compact
    intro K hK hKU
    rw [hval.map_apply,
      withDensity_apply _ (hK.isClosed.measurableSet.preimage measurable_subtype_coe)]
    have hKc : IsCompact ((Subtype.val : U → Euclid P) ⁻¹' K) := by
      rw [Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
      · exact hK
      · simpa using hKU
    have hint := hloc _ hKc
    have heq : ∫⁻ x in Subtype.val ⁻¹' K, ENNReal.ofReal (ρ x) ∂μ₀ =
        ∫⁻ x in Subtype.val ⁻¹' K, ‖ν x‖ₑ ∂μ₀ := by
      congr 1
      funext x
      simp [hρ_def]
    rw [heq]
    exact hint.2
  · -- (c) `ξ` is a continuous function of the measurable `u`
    have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin d) =>
        (innerSL ℝ v).comp (c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d))) :=
      (innerSL ℝ).continuous.clm_comp continuous_const
    exact (hcont.comp_stronglyMeasurable hum.stronglyMeasurable).aestronglyMeasurable
  · -- (d) Cauchy–Schwarz and `‖u‖ ≤ 1`
    intro y α
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
    rw [hc]
    calc |inner ℝ (u y) (c α)| ≤ ‖u y‖ * ‖c α‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖c α‖ := by gcongr; exact hu_le y
      _ = ‖c α‖ := one_mul _
  · -- (e) `β` is a continuous function of the measurable `u`
    exact (c.symm.continuous.comp_stronglyMeasurable hum.stronglyMeasurable).aestronglyMeasurable
  · -- (f) `‖β(y)‖ ≤ ‖c⁻¹‖ ‖u(y)‖ ≤ ‖c⁻¹‖`
    refine ⟨‖(c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n)‖, fun y => ?_⟩
    calc ‖c.symm (u y)‖
        ≤ ‖(c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n)‖ * ‖u y‖ :=
          (c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n).le_opNorm _
      _ ≤ ‖(c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n)‖ * 1 := by
          gcongr
          exact hu_le y
      _ = _ := mul_one _
  · -- (g) `|β(y)| = ‖c(c⁻¹(u y))‖ = ‖u y‖ ≤ 1`
    intro y
    rw [hc, c.apply_symm_apply]
    exact hu_le y
  · -- (h) `ξ(β) = ‖u‖² = 1` wherever the density `ρ` is nonzero
    rw [hval.ae_map_iff, ae_withDensity_iff hdens]
    refine ae_of_all _ (fun x hx => ?_)
    have hρx : ρ x ≠ 0 := by
      intro h
      apply hx
      simp [h]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq, hu_val, hνh_one x hρx]
    norm_num
  · -- (i) push-forward, then the density, then `⟨c ω, ρ ν̂⟩ = ρ ⟨ν̂, c ω⟩` pointwise
    intro ω
    rw [hval.integral_map,
      integral_withDensity_eq_integral_toReal_smul hdens
        (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (hρ0 x), smul_eq_mul]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, innerSL_apply_apply,
      hu_val]
    rw [hdecomp x, inner_smul_right, real_inner_comm]
/-- **Mass upper bound from a representation by a unit-bounded multivector field** (Simon
6.2.5; step 10 of the representation `T = μ_T ∧ ξ⃗`).  Suppose `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x`
and all covectors `α` (`|·|_E` is `covectorEuclideanNorm`), and `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`
for every test form `ω`.  Then `M_W(T) ≤ μ(W)` for every set `W`.  Fix an admissible `ω`, i.e.
`tsupport ω ⊆ W` and `|ω|_E ≤ 1`, and let `K = tsupport ω` (closed, hence Borel) and
`f(x) = ⟨ω(x), ξ(x)⟩`.  Then `|f| ≤ |ω|_E ≤ 1` on `K` and `f = 0` off `K`, so
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_K dμ = μ(K) ≤ μ(W)`; the middle inequality holds whether
or not `f` is integrable.  Taking the supremum over admissible `ω` gives `M_W(T) ≤ μ(W)`. -/
theorem Submission.cmrc_massOn_le_of_repr : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ W : Set (Euclid P), T.massOn W ≤ μ W := by
  intro P n U T μ ξ hξ hT W
  -- Step 1: it suffices to bound `ofReal (T ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  set K : Set (Euclid P) := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  -- Step 2: `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_K(x)` for every `x`
  have hpt : ∀ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ K.indicator 1 x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Pi.one_apply, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
  -- Step 3: `T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ μ(K) ≤ μ(W)`
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
    _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, K.indicator 1 x ∂μ := lintegral_mono hpt
    _ = μ K := lintegral_indicator_one hKm
    _ ≤ μ W := measure_mono hω.1

/-- **A norming field bounds `μ(W')` by the mass `M_W(T)`** (the inequality `μ_T(W') ≤ M_W(T)`
behind Simon 6.2.8, `μ_T(W) = M_W(T)`, for the representation 6.2.7 `T(ω) = ∫ ⟨ω, ξ⟩ dμ`;
`|·|_E` is `covectorEuclideanNorm`).  Let `W' ⊂⊂ U` be open with `W' ⊆ W`.  Then `ν = μ⌞W'` is
finite, as `closure W'` is a compact subset of `U`, and the bounded field `β` is `ν`-integrable.
For `ε > 0`, `Submission.rsd_mw_exists_testForm_approx` gives a test form `ω` with
`tsupport ω ⊆ W'`, `|ω|_E ≤ 1` and `∫ |ω − β|_E dν < ε`, so `ω` is admissible for `M_W(T)`.
The function `f = ξ(ω)` vanishes off `W'`, so `T(ω) = ∫ f dν`; and `ν`-a.e.
`1 − f = ξ(β − ω) ≤ |ω − β|_E`, since `ξ(β) = 1` and `|ξ(α)| ≤ |α|_E`.  Hence
`μ(W') − T(ω) = ∫ (1 − f) dν < ε`, and `μ(W') ≤ M_W(T) + ε` for every `ε > 0`. -/
theorem Submission.cmrc_measure_le_massOn_of_norming : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → AEStronglyMeasurable β μ → (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) → (∀ x, covectorEuclideanNorm (β x) ≤ 1) → (∀ᵐ x ∂μ, ξ x (β x) = 1) → ∀ W W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ T.massOn W := by
  intro P n U T μ ξ β hμK hξm hξ1 hT hβm hβC hβ1 hξβ W W' hW' hW'U hW'W
  -- `N := covectorEuclideanNorm`, `ν := μ⌞W'`
  -- Step 1: `ν` is finite (`closure W'` is a compact subset of `U`) and `ν(W'ᶜ) = 0`
  have hμW' : μ W' < ∞ := (measure_mono subset_closure).trans_lt (hμK _ hW'U.1 hW'U.2)
  have : IsFiniteMeasure (μ.restrict W') := isFiniteMeasure_restrict.2 hμW'.ne
  have hνc : μ.restrict W' W'ᶜ = 0 := by
    rw [Measure.restrict_apply hW'.measurableSet.compl, compl_inter_self, measure_empty]
  -- Step 2: `β` is bounded, hence `ν`-integrable
  obtain ⟨C, hC⟩ := hβC
  have hβi : Integrable β (μ.restrict W') :=
    Integrable.of_bound hβm.restrict C (Eventually.of_forall hC)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- Step 3: a test form `ω₀` with `tsupport ω₀ ⊆ W'`, `N(ω₀) ≤ 1` and `∫ N(ω₀ - β) dν < ε`
  obtain ⟨ω₀, hω₀, hω₀W', hω₀1, hω₀β⟩ := Submission.rsd_mw_exists_testForm_approx P n
    (μ.restrict W') W' β inferInstance hW' hνc hβi (Eventually.of_forall hβ1) ε
    (NNReal.coe_pos.2 hε)
  -- Step 4: `ω₀ ∈ 𝒟ⁿ(U)` is admissible for `M_W(T)`, so `T(ω₀) ≤ M_W(T)`
  let ω : TestFormOn U n := ⟨ω₀, hω₀, hω₀W'.trans (subset_closure.trans hW'U.2)⟩
  have hTω : ENNReal.ofReal (T ω) ≤ T.massOn W := T.le_massOn ⟨hω₀W'.trans hW'W, hω₀1⟩
  -- Step 5: `f = ξ(ω₀)` vanishes off `W'`, so `T(ω₀) = ∫ f dν`
  set f : Euclid P → ℝ := fun x => ξ x (ω₀ x) with hf
  have hTf : T ω = ∫ x, f x ∂(μ.restrict W') := by
    rw [hT ω, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    simp [hf, image_eq_zero_of_notMem_tsupport fun h => hx (hω₀W' h)]
  -- Step 6: `|f| ≤ N(ω₀) ≤ 1`, so `f` is `ν`-integrable
  have hf1 : ∀ x, |f x| ≤ 1 := fun x => (hξ1 x (ω₀ x)).trans (hω₀1 x)
  have hfm : AEStronglyMeasurable f μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hξm.prodMk hω₀.1.continuous.aestronglyMeasurable)
  have hfi : Integrable f (μ.restrict W') :=
    Integrable.of_bound hfm.restrict 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf1 x)
  -- Step 7: `ν`-a.e., `1 - f = ξ(β - ω₀) ≤ N(ω₀ - β)`, since `ξ(β) = 1` and `|ξ(α)| ≤ N(α)`
  have hle : ∀ᵐ x ∂(μ.restrict W'), 1 - f x ≤ covectorEuclideanNorm (ω₀ x - β x) := by
    filter_upwards [ae_restrict_of_ae hξβ] with x hx
    have h := abs_le.1 (hξ1 x (ω₀ x - β x))
    rw [map_sub, hx] at h
    linarith [h.1]
  -- Step 8: `μ(W') - T(ω₀) = ∫ (1 - f) dν ≤ ∫ N(ω₀ - β) dν < ε`
  have hint : ENNReal.ofReal (μ.real W' - T ω) < ENNReal.ofReal ε := by
    have h1 : ∫ x, (1 - f x) ∂(μ.restrict W') = μ.real W' - T ω := by
      rw [integral_sub (integrable_const 1) hfi, integral_const, hTf, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ]
    have hgi : Integrable (fun x => 1 - f x) (μ.restrict W') := (integrable_const 1).sub hfi
    rw [← h1, ofReal_integral_eq_lintegral_ofReal hgi
      (Eventually.of_forall fun x => sub_nonneg.2 (le_of_abs_le (hf1 x)))]
    exact (lintegral_mono_ae (hle.mono fun x hx => ENNReal.ofReal_le_ofReal hx)).trans_lt hω₀β
  -- Step 9: `μ(W') ≤ T(ω₀) + ε ≤ M_W(T) + ε`
  calc μ W' = ENNReal.ofReal (T ω + (μ.real W' - T ω)) := by
        rw [add_sub_cancel, ofReal_measureReal hμW'.ne]
    _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal (μ.real W' - T ω) := ENNReal.ofReal_add_le
    _ ≤ T.massOn W + ε := add_le_add hTω (hint.le.trans_eq ENNReal.ofReal_coe_nnreal)
/-- Exhaustion by compactly contained open sets: if `U, W ⊆ ℝᴾ` are open, `μ(ℝᴾ \ U) = 0` and
`μ(W') ≤ m` for every open `W' ⊂⊂ U` with `W' ⊆ W`, then `μ(W) ≤ m`.  The open sets
`W'ⱼ = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` have closures inside the compact sets
`{y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} ⊆ W ∩ U`, increase with `j` and exhaust `W ∩ U`,
so `μ(W) = μ(W ∩ U) = supⱼ μ(W'ⱼ) ≤ m` by continuity from below. -/
theorem Submission.cmrc_measure_le_of_compactlyContained : ∀ (P : ℕ) (μ : Measure (Euclid P)) (U W : Set (Euclid P)) (m : ℝ≥0∞), IsOpen U → IsOpen W → μ Uᶜ = 0 → (∀ W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ m) → μ W ≤ m := by
  intro P μ U W m hU hW hUc hm
  -- `V j = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` exhausts the open set `W ∩ U`
  set V : ℕ → Set (Euclid P) :=
    fun j => {y | ‖y‖ < j ∧ ((j : ℝ≥0∞) + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}
  have hd : Continuous fun y : Euclid P => infEDist y (W ∩ U)ᶜ := continuous_infEDist
  have hpos : ∀ j : ℕ, 0 < ((j : ℝ≥0∞) + 1)⁻¹ := fun j => ENNReal.inv_pos.2 (by simp)
  -- `closure (V j)` lies in `F j = {y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ}`, a compact
  -- subset of `W ∩ U`
  have hF : ∀ j : ℕ, IsCompact (closure (V j)) ∧ closure (V j) ⊆ W ∩ U := by
    intro j
    have hVF : closure (V j) ⊆
        {y : Euclid P | ‖y‖ ≤ j ∧ ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} :=
      closure_minimal (fun y hy => ⟨hy.1.le, hy.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const hd))
    refine ⟨(isCompact_closedBall (0 : Euclid P) (j : ℝ)).of_isClosed_subset isClosed_closure
      fun y hy => ?_, fun y hy => ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact (hVF hy).1
    · by_contra hy'
      have h := (hVF hy).2
      rw [infEDist_zero_of_mem hy'] at h
      exact (hpos j).not_ge h
  have hVsub : ∀ j, V j ⊆ W ∩ U := fun j => subset_closure.trans (hF j).2
  have hVm : ∀ j, μ (V j) ≤ m := fun j =>
    hm (V j) ((isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd))
      ⟨(hF j).1, (hF j).2.trans inter_subset_right⟩ ((hVsub j).trans inter_subset_left)
  have hmono : Monotone V := by
    intro j k hjk y hy
    refine ⟨hy.1.trans_le (by exact_mod_cast hjk), lt_of_le_of_lt ?_ hy.2⟩
    gcongr
  have hUnion : ⋃ j, V j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset hVsub) fun y hy => ?_
    have hne : infEDist y (W ∩ U)ᶜ ≠ 0 := fun h0 =>
      ((mem_iff_infEDist_zero_of_closed (hW.inter hU).isClosed_compl).2 h0) hy
    obtain ⟨j₁, hj₁⟩ := ENNReal.exists_inv_nat_lt hne
    obtain ⟨j₂, hj₂⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨max j₁ j₂, hj₂.trans_le (by exact_mod_cast le_max_right j₁ j₂),
      lt_of_le_of_lt ?_ hj₁⟩
    gcongr
    norm_cast
    omega
  -- `μ W = μ (W ∩ U)` since `μ Uᶜ = 0`; continuity from below along the increasing `V j`
  calc μ W = μ (⋃ j, V j) := by rw [hUnion, measure_inter_conull hUc]
    _ = ⨆ j, μ (V j) := hmono.measure_iUnion
    _ ≤ m := iSup_le hVm
/-- **Uniform approximation by test forms supported in an open set** (selected proof, step 3,
approximating sequences).  Let `|α| = covectorEuclideanNorm α = ‖c α‖` for a continuous linear
equivalence `c`.  A continuous, compactly supported `n`-covector field `G` with `tsupport G ⊆ V`
(`V` open) is uniformly `ε`-approximated in `|·|` by a test form `ω` with `tsupport ω ⊆ V`.

Since `c` is linear, `|tα| = |t| |α|`.  `c ∘ G` is continuous with compact support, hence bounded
by some `C`; put `s = max C 0 + 1 > 0`, so `|G| ≤ s`.  Then `g = s⁻¹ G` is continuous, compactly
supported, `tsupport g ⊆ V` and `|g| ≤ 1`, so `dor_ims_sua_mollify_unit_field` gives a test form
`ω₀` with `tsupport ω₀ ⊆ V` and `|ω₀ − g| ≤ ε/s`.  Finally `ω = s ω₀` is a test form with
`tsupport ω ⊆ tsupport ω₀ ⊆ V` and `|ω − G| = s |ω₀ − g| ≤ ε`. -/
theorem Submission.dimred_mbl_fnd_tfe_uniform_testForm_approx : ∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (V : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n) (ε : ℝ), (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → IsOpen V → Continuous G → HasCompactSupport G → tsupport G ⊆ V → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ ∀ x, covectorEuclideanNorm (ω x - G x) ≤ ε := by
  intro P n d c V G ε hc hV hGc hGs hGV hε
  -- (1) homogeneity `|t • α| = |t| |α|`, since `c` is linear
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hc, hc, map_smul, norm_smul, Real.norm_eq_abs]
  -- (2) `c ∘ G` is continuous with compact support, so `‖c (G x)‖ ≤ C`; `s = max C 0 + 1`
  obtain ⟨C, hC⟩ := (hGs.comp_left (map_zero c)).exists_bound_of_continuous
    (c.continuous.comp hGc)
  set s : ℝ := max C 0 + 1
  have hs : 0 < s := by positivity
  have hGb : ∀ x, covectorEuclideanNorm (G x) ≤ s := fun x => by
    rw [hc]
    exact (hC x).trans ((le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one))
  -- (3) the normalized field `g = s⁻¹ • G`: continuous, compactly supported in `V`, `|g| ≤ 1`
  set g : Euclid P → Covector (Euclid P) n := fun x => s⁻¹ • G x with hg_def
  have hgc : Continuous g := hGc.const_smul s⁻¹
  have hgG : support g ⊆ support G := fun x hx h => hx (by simp [g, h])
  have hgs : HasCompactSupport g := hGs.mono hgG
  have hgV : tsupport g ⊆ V := (closure_mono hgG).trans hGV
  have hg1 : ∀ x, covectorEuclideanNorm (g x) ≤ 1 := fun x => by
    rw [hg_def, hsmul, abs_of_pos (inv_pos.2 hs), inv_mul_le_iff₀ hs, mul_one]
    exact hGb x
  -- (4) mollify `g` with error `ε / s`
  obtain ⟨ω₀, ⟨hω₀s, hω₀c⟩, hω₀V, -, hω₀g⟩ :=
    Submission.dor_ims_sua_mollify_unit_field P n V g (ε / s) hV hgc hgs hgV hg1 (div_pos hε hs)
  -- (5) rescale: `ω = s • ω₀` is a test form with `tsupport ω ⊆ tsupport ω₀ ⊆ V`
  refine ⟨fun x => s • ω₀ x, ⟨ContDiff.const_smul (𝕜 := ℝ) s hω₀s,
    hω₀c.smul_left (f := fun _ => s)⟩, (tsupport_smul_subset_right (fun _ => s) ω₀).trans hω₀V,
    fun x => ?_⟩
  -- (6) `ω x - G x = s • (ω₀ x - g x)`, so `|ω x - G x| = s |ω₀ x - g x| ≤ s (ε / s) = ε`
  have hdiff : s • ω₀ x - G x = s • (ω₀ x - g x) := by
    rw [hg_def, smul_sub, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  rw [hdiff, hsmul, abs_of_pos hs]
  calc s * covectorEuclideanNorm (ω₀ x - g x) ≤ s * (ε / s) :=
        mul_le_mul_of_nonneg_left (hω₀g x) hs.le
    _ = ε := mul_div_cancel₀ ε hs.ne'

/-- **Extending `T` to uniform limits of test forms** (the density step behind the Riesz
representation, Simon 6.2.7).  Let `|α| = ‖c α‖` for a continuous linear equivalence `c`, and let
`|T(ω)| ≤ r · m(W)` whenever `W ⊂⊂ U` is open, `spt ω ⊆ W` and `|ω| ≤ r`.  Call `(W, ωₖ, εₖ)`
approximating data for `G` if `W ⊂⊂ U` is open, `spt ωₖ ⊆ W`, `|ωₖ − G| ≤ εₖ` and `εₖ → 0`.
For two such data of one `G`, `ωₖ − ω'ₗ` is supported in the open set `W ∪ W' ⊂⊂ U` and
`|ωₖ − ω'ₗ| ≤ εₖ + ε'ₗ` (triangle inequality for `‖c ·‖`), so
`|T(ωₖ) − T(ω'ₗ)| ≤ (εₖ + ε'ₗ) m(W ∪ W')`.  With equal data `T(ωₖ)` is Cauchy, hence
convergent; `Φ(G)` is its limit along chosen data (`0` if `G` has none), and the estimate with
`l = k` shows that every approximating sequence of `G` tends to `Φ(G)`. -/
theorem Submission.dimred_mbl_fnd_tfe_exists_limit_functional : ∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : Set (Euclid P) → ℝ), (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → (∀ (W : Set (Euclid P)) (ω : TestFormOn U n) (r : ℝ), IsOpen W → CompactlyContained W U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * m W) → ∃ Φ : (Euclid P → Covector (Euclid P) n) → ℝ, ∀ (G : Euclid P → Covector (Euclid P) n) (W : Set (Euclid P)) (ωs : ℕ → TestFormOn U n) (εs : ℕ → ℝ), IsOpen W → CompactlyContained W U → (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) → (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) → Tendsto εs atTop (𝓝 0) → Tendsto (fun k => T (ωs k)) atTop (𝓝 (Φ G)) := by
  intro P n d c U T m hc hm
  classical
  -- `(W, ωs, εs)` is approximating data for `G`
  let IsApprox : (Euclid P → Covector (Euclid P) n) → Set (Euclid P) → (ℕ → TestFormOn U n) →
      (ℕ → ℝ) → Prop := fun G W ωs εs =>
    IsOpen W ∧ CompactlyContained W U ∧
      (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) ∧
      (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) ∧
      Tendsto εs atTop (𝓝 0)
  -- (1) the triangle inequality for `|α| = ‖c α‖`
  have htri : ∀ α β : Covector (Euclid P) n,
      covectorEuclideanNorm (α - β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hc, hc, hc, map_sub]
    exact norm_sub_le _ _
  -- (2), (3) the key estimate `|T ωₖ - T ω'ₗ| ≤ (εₖ + ε'ₗ) m(W ∪ W')`
  have hkey : ∀ G W ωs εs W' ωs' εs', IsApprox G W ωs εs → IsApprox G W' ωs' εs' →
      ∀ k l, |T (ωs k) - T (ωs' l)| ≤ (εs k + εs' l) * m (W ∪ W') := by
    rintro G W ωs εs W' ωs' εs' ⟨hW, hWU, hs, hε, -⟩ ⟨hW', hWU', hs', hε', -⟩ k l
    rw [show T (ωs k) - T (ωs' l) = T (ωs k - ωs' l) from (map_sub T.toCurrent _ _).symm]
    refine hm _ _ _ (hW.union hW') ⟨?_, ?_⟩ ?_ fun x => ?_
    · rw [closure_union]
      exact hWU.1.union hWU'.1
    · rw [closure_union]
      exact union_subset hWU.2 hWU'.2
    · exact (tsupport_sub (ωs k : DifferentialForm (Euclid P) n) (ωs' l)).trans
        (union_subset_union (hs k) (hs' l))
    · have hx : ((ωs k - ωs' l : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
          ((ωs k : DifferentialForm (Euclid P) n) x - G x) -
            ((ωs' l : DifferentialForm (Euclid P) n) x - G x) := by
        simp
      rw [hx]
      exact (htri _ _).trans (add_le_add (hε k x) (hε' l x))
  -- (4) along approximating data, `T ωₖ` is Cauchy, hence convergent
  have hconv : ∀ G W ωs εs, IsApprox G W ωs εs →
      ∃ L, Tendsto (fun k => T (ωs k)) atTop (𝓝 L) := by
    intro G W ωs εs hD
    refine cauchySeq_tendsto_of_complete (cauchySeq_iff_tendsto_dist_atTop_0.2 ?_)
    have hb : Tendsto (fun p : ℕ × ℕ => (εs p.1 + εs p.2) * m (W ∪ W)) atTop (𝓝 0) := by
      rw [← prod_atTop_atTop_eq]
      simpa using ((hD.2.2.2.2.comp tendsto_fst).add (hD.2.2.2.2.comp tendsto_snd)).mul_const
        (m (W ∪ W))
    refine squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) hb
    rw [Real.dist_eq]
    exact hkey G W ωs εs W ωs εs hD hD p.1 p.2
  -- (5) `Φ G` is the limit along chosen approximating data (`0` if there is none)
  refine ⟨fun G => if h : ∃ L, ∃ W ωs εs, IsApprox G W ωs εs ∧
      Tendsto (fun k => T (ωs k)) atTop (𝓝 L) then Classical.choose h else 0, ?_⟩
  -- (6) every approximating sequence tends to `Φ G`
  intro G W ωs εs hW hWU hs hε hε0
  have hD : IsApprox G W ωs εs := ⟨hW, hWU, hs, hε, hε0⟩
  obtain ⟨L₀, hL₀⟩ := hconv G W ωs εs hD
  have hex : ∃ L, ∃ W ωs εs, IsApprox G W ωs εs ∧ Tendsto (fun k => T (ωs k)) atTop (𝓝 L) :=
    ⟨L₀, W, ωs, εs, hD, hL₀⟩
  simp only [dite_eq_left hex]
  obtain ⟨W', ωs', εs', hD', hL⟩ := Classical.choose_spec hex
  have hdiff : Tendsto (fun k => T (ωs k) - T (ωs' k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => ?_) (by
      simpa using (hε0.add hD'.2.2.2.2).mul_const (m (W ∪ W')))
    rw [Real.norm_eq_abs]
    exact hkey G W ωs εs W' ωs' εs' hD hD' k k
  simpa using hdiff.add hL

/-- **Extending a locally bounded current to continuous covector fields.**  Let `|α| = ‖c α‖` for
a continuous linear equivalence `c` onto `ℝᵈ`, and let `m` bound `T` locally: `|T(ω)| ≤ r m(W)`
whenever `W ⊂⊂ U` is open, `spt ω ⊆ W` and `|ω| ≤ r`.  Take `Φ` with `T(ωₖ) → Φ(G)` along test
forms `ωₖ` supported in one open `W ⊂⊂ U` with `|ωₖ − G| ≤ εₖ → 0`
(`dimred_mbl_fnd_tfe_exists_limit_functional`).  A compact subset of `U` lies in an open
`W ⊂⊂ U`, and a continuous `G` with compact support in `W` has such approximants with
`εₖ = 1/(k+1)` (`dimred_mbl_fnd_tfe_uniform_testForm_approx`).  Sums and multiples of
approximants approximate `G₁ + G₂` (in `W₁ ∪ W₂`) and `t G`, so additivity and homogeneity follow
from the linearity of `T` and uniqueness of limits; the constant sequence `ω` gives
`Φ(ω) = T(ω)`; and `|ωₖ| ≤ r + 1/(k+1)` gives `|T(ωₖ)| ≤ (r + 1/(k+1)) m(W)`, whence
`|Φ(G)| ≤ r m(W)`. -/
theorem Submission.dimred_mbl_fnd_tfe_ambient_extension : ∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : Set (Euclid P) → ℝ), IsOpen U → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → (∀ (W : Set (Euclid P)) (ω : TestFormOn U n) (r : ℝ), IsOpen W → CompactlyContained W U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * m W) → ∃ Φ : (Euclid P → Covector (Euclid P) n) → ℝ, (∀ G₁ G₂ : Euclid P → Covector (Euclid P) n, Continuous G₁ → HasCompactSupport G₁ → tsupport G₁ ⊆ U → Continuous G₂ → HasCompactSupport G₂ → tsupport G₂ ⊆ U → Φ (G₁ + G₂) = Φ G₁ + Φ G₂) ∧ (∀ (t : ℝ) (G : Euclid P → Covector (Euclid P) n), Continuous G → HasCompactSupport G → tsupport G ⊆ U → Φ (t • G) = t * Φ G) ∧ (∀ ω : TestFormOn U n, Φ (ω : DifferentialForm (Euclid P) n) = T ω) ∧ ∀ (W : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n) (r : ℝ), IsOpen W → CompactlyContained W U → Continuous G → HasCompactSupport G → tsupport G ⊆ W → (∀ x, covectorEuclideanNorm (G x) ≤ r) → |Φ G| ≤ r * m W := by
  intro P n d c U T m hU hc hm
  -- (1) the limit functional `Φ`
  obtain ⟨Φ, hΦ⟩ := Submission.dimred_mbl_fnd_tfe_exists_limit_functional P n d c U T m hc hm
  -- `|α + β| ≤ |α| + |β|` and `|t • α| = |t| |α|`, read through `c`
  have hadd : ∀ α β : Covector (Euclid P) n,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hc, hc, hc, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hc, hc, map_smul, norm_smul, Real.norm_eq_abs]
  -- (2) a compact subset of `U` lies in an open `W ⊂⊂ U`; and `W ⊂⊂ U` gives `W ⊆ U`
  have hnbhd : ∀ S : Set (Euclid P), IsCompact S → S ⊆ U →
      ∃ W, IsOpen W ∧ S ⊆ W ∧ CompactlyContained W U := by
    intro S hS hSU
    obtain ⟨W, hWo, hSW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hS hU hSU
    exact ⟨W, hWo, hSW, hWc, hWU⟩
  have hsub : ∀ W, CompactlyContained W U → W ⊆ U := fun W hW => subset_closure.trans hW.2
  -- (3) approximants `ωₖ ∈ 𝒟ⁿ(U)` with `spt ωₖ ⊆ W` and `|ωₖ − G| ≤ 1/(k+1)`
  have happrox : ∀ (W : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n), IsOpen W →
      CompactlyContained W U → Continuous G → HasCompactSupport G → tsupport G ⊆ W →
      ∃ ωs : ℕ → TestFormOn U n, (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) ∧
        ∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤
          1 / ((k : ℝ) + 1) := by
    intro W G hW hWU hG hGc hGW
    have hk : ∀ k : ℕ, ∃ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W ∧
        ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x - G x) ≤
          1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨ω, hωt, hωW, hωe⟩ := Submission.dimred_mbl_fnd_tfe_uniform_testForm_approx P n d c
        W G (1 / ((k : ℝ) + 1)) hc hW hG hGc hGW (by positivity)
      exact ⟨⟨ω, hωt, hωW.trans (hsub W hWU)⟩, hωW, hωe⟩
    choose ωs hωW hωe using hk
    exact ⟨ωs, hωW, hωe⟩
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · -- (4) additivity: `ω¹ₖ + ω²ₖ` approximates `G₁ + G₂` in `W₁ ∪ W₂ ⊂⊂ U`
    intro G₁ G₂ hG₁ hG₁c hG₁U hG₂ hG₂c hG₂U
    obtain ⟨W₁, hW₁o, hG₁W₁, hW₁U⟩ := hnbhd _ hG₁c hG₁U
    obtain ⟨W₂, hW₂o, hG₂W₂, hW₂U⟩ := hnbhd _ hG₂c hG₂U
    obtain ⟨ω₁, hω₁W, hω₁e⟩ := happrox W₁ G₁ hW₁o hW₁U hG₁ hG₁c hG₁W₁
    obtain ⟨ω₂, hω₂W, hω₂e⟩ := happrox W₂ G₂ hW₂o hW₂U hG₂ hG₂c hG₂W₂
    have hWU : CompactlyContained (W₁ ∪ W₂) U := by
      refine ⟨?_, ?_⟩ <;> rw [closure_union]
      exacts [hW₁U.1.union hW₂U.1, union_subset hW₁U.2 hW₂U.2]
    have h := hΦ (G₁ + G₂) (W₁ ∪ W₂) (fun k => ω₁ k + ω₂ k)
      (fun k => 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1)) (hW₁o.union hW₂o) hWU
      (fun k => by
        simp only [Submodule.coe_add]
        exact (tsupport_add _ _).trans (union_subset_union (hω₁W k) (hω₂W k)))
      (fun k x => by
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [add_sub_add_comm]
        exact (hadd _ _).trans (add_le_add (hω₁e k x) (hω₂e k x)))
      (by simpa only [add_zero] using hlim.add hlim)
    have h' : Tendsto (fun k => T (ω₁ k + ω₂ k)) atTop (𝓝 (Φ G₁ + Φ G₂)) :=
      ((hΦ G₁ W₁ ω₁ _ hW₁o hW₁U hω₁W hω₁e hlim).add
        (hΦ G₂ W₂ ω₂ _ hW₂o hW₂U hω₂W hω₂e hlim)).congr fun k =>
          (T.toCurrent.map_add (ω₁ k) (ω₂ k)).symm
    exact tendsto_nhds_unique h h'
  · -- (5) homogeneity: `t ωₖ` approximates `t G` with errors `|t|/(k+1)`
    intro t G hG hGc hGU
    obtain ⟨W, hWo, hGW, hWU⟩ := hnbhd _ hGc hGU
    obtain ⟨ωs, hωW, hωe⟩ := happrox W G hWo hWU hG hGc hGW
    have h := hΦ (t • G) W (fun k => t • ωs k) (fun k => |t| * (1 / ((k : ℝ) + 1))) hWo hWU
      (fun k => by
        simp only [Submodule.coe_smul]
        exact (tsupport_smul_subset_right (fun _ => t) _).trans (hωW k))
      (fun k x => by
        simp only [Submodule.coe_smul, Pi.smul_apply]
        have e : t • (ωs k : DifferentialForm (Euclid P) n) x - t • G x =
            t • ((ωs k : DifferentialForm (Euclid P) n) x - G x) := (smul_sub t _ _).symm
        rw [e, hsmul]
        exact mul_le_mul_of_nonneg_left (hωe k x) (abs_nonneg t))
      (by simpa only [mul_zero] using hlim.const_mul |t|)
    have h' : Tendsto (fun k => T (t • ωs k)) atTop (𝓝 (t * Φ G)) :=
      ((hΦ G W ωs _ hWo hWU hωW hωe hlim).const_mul t).congr fun k => by
        rw [T.toCurrent.map_smul, smul_eq_mul]
    exact tendsto_nhds_unique h h'
  · -- (6) agreement: the constant sequence `ω`, with errors `0`
    intro ω
    obtain ⟨W, hWo, hωW, hWU⟩ := hnbhd _ ω.property.1.2 ω.property.2
    exact tendsto_nhds_unique (hΦ (ω : DifferentialForm (Euclid P) n) W (fun _ => ω) (fun _ => 0)
      hWo hWU (fun _ => hωW) (fun _ x => by simp) tendsto_const_nhds) tendsto_const_nhds
  · -- (7) bound: `|ωₖ| ≤ r + 1/(k+1)`, so `|T(ωₖ)| ≤ (r + 1/(k+1)) m(W)`; let `k → ∞`
    intro W G r hWo hWU hG hGc hGW hr
    obtain ⟨ωs, hωW, hωe⟩ := happrox W G hWo hWU hG hGc hGW
    have hb : ∀ k : ℕ, |T (ωs k)| ≤ (r + 1 / ((k : ℝ) + 1)) * m W := by
      intro k
      refine hm W (ωs k) _ hWo hWU (hωW k) fun x => ?_
      calc covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x)
          = covectorEuclideanNorm (((ωs k : DifferentialForm (Euclid P) n) x - G x) + G x) := by
            rw [sub_add_cancel]
        _ ≤ 1 / ((k : ℝ) + 1) + r := (hadd _ _).trans (add_le_add (hωe k x) (hr x))
        _ = r + 1 / ((k : ℝ) + 1) := add_comm _ _
    have hmW : Tendsto (fun k : ℕ => (r + 1 / ((k : ℝ) + 1)) * m W) atTop (𝓝 (r * m W)) := by
      simpa only [add_zero] using ((tendsto_const_nhds (x := r)).add hlim).mul_const (m W)
    exact le_of_tendsto_of_tendsto' (hΦ G W ωs _ hWo hWU hωW hωe hlim).abs hmW hb

/-- **Extension of a current of locally finite mass to compactly supported continuous fields**
(selected proof, steps 1 and 6–8).  Let `U` be open, `T ∈ 𝒟ₙ(U)` with `M_W(T) < ∞` for every open
`W ⊂⊂ U`, and `c : Λⁿ(ℝᴾ) ≃ ℝᵈ` a continuous linear equivalence with `|α| = ‖c α‖` for the
Euclidean coefficient norm.  Then there is a linear functional `L` on `C_c(U, ℝᵈ)` with
`L(g) = T(ω)` whenever `g = c ∘ ω`, `ω ∈ 𝒟ⁿ(U)`, and for each compact `K ⊆ U` a bound for `|L(g)|`
over all `g` with `spt g ⊆ K` and `‖g‖ ≤ 1`.

By `cmr_abs_apply_le_massOn`, `|T(ω)| ≤ r M_W(T)` when `spt ω ⊆ W` and `|ω| ≤ r`; so
`dimred_mbl_fnd_tfe_ambient_extension` with `m(W) = M_W(T)` gives `Φ` on continuous compactly
supported fields `G` with `spt G ⊆ U`: additive, homogeneous, `Φ(ω) = T(ω)`, and
`|Φ(G)| ≤ r M_W(T)` when `spt G ⊆ W` and `|G| ≤ r`.  For `g ∈ C_c(U, ℝᵈ)` let `g̃ = c⁻¹ ∘ g` on `U`
and `g̃ = 0` off `U`; as `U` is open, `g̃` is continuous with compact support and
`spt g̃ ⊆ spt g ⊆ U`.  Put `L(g) = Φ(g̃)`.  As `g ↦ g̃` is linear, so is `L`.  If `g = c ∘ ω`, then
`g̃ = ω` and `L(g) = T(ω)`.  For compact `K ⊆ U` choose an open `W ⊂⊂ U` with `K ⊆ W`; if
`spt g ⊆ K` and `‖g‖ ≤ 1`, then `spt g̃ ⊆ W` and `|g̃| ≤ 1`, so `|L(g)| ≤ M_W(T)`. -/
theorem Submission.dimred_mbl_fnd_testForm_extension_functional : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → ∃ L : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ, (∀ (ω : TestFormOn U n) (g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d))), (∀ x : U, g x = c ((ω : DifferentialForm (Euclid P) n) x)) → L g = T ω) ∧ ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M := by
  intro P n U T d c hU hfin hc
  -- (a) the extension `Φ` with `m(W) = M_W(T)`, finite for open `W ⊂⊂ U`
  obtain ⟨Φ, hΦadd, hΦsmul, hΦT, hΦbd⟩ := Submission.dimred_mbl_fnd_tfe_ambient_extension P n d c
    U T (fun W => (T.massOn W).toReal) hU hc fun W ω r hW hWU hωW hωr =>
      Submission.cmr_abs_apply_le_massOn P n U W T ω r (hfin W hW hWU).ne hωW hωr
  -- (b) the zero extension `g̃ = c⁻¹ ∘ g` on `U`, `0` off `U`
  obtain ⟨ext, hin, hout, hcont, hcpt, hspt⟩ : ∃ ext : CompactlySupportedContinuousMap U
      (EuclideanSpace ℝ (Fin d)) → Euclid P → Covector (Euclid P) n,
      (∀ g y (hy : y ∈ U), ext g y = c.symm (g ⟨y, hy⟩)) ∧ (∀ g y, y ∉ U → ext g y = 0) ∧
      (∀ g, Continuous (ext g)) ∧ (∀ g, HasCompactSupport (ext g)) ∧
      ∀ g, tsupport (ext g) ⊆ Subtype.val '' tsupport g := by
    have hcs : ∀ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)),
        HasCompactSupport (c.symm ∘ g) := fun g => g.hasCompactSupport.comp_left (map_zero _)
    exact ⟨fun g => Function.extend Subtype.val (c.symm ∘ g) 0,
      fun g y hy => Subtype.val_injective.extend_apply _ _ (⟨y, hy⟩ : U),
      fun g y hy => Function.extend_apply' _ _ y fun ⟨x, hx⟩ => hy (hx ▸ x.2),
      fun g => HasCompactSupport.continuous_extend_zero hU (c.symm.continuous.comp g.continuous)
        (hcs g),
      fun g => (hcs g).extend_zero continuous_subtype_val,
      fun g => ((hcs g).tsupport_extend_zero_subset continuous_subtype_val).trans
        (image_mono (tsupport_comp_subset (map_zero _) g))⟩
  have hsptU : ∀ g, tsupport (ext g) ⊆ U := fun g => (hspt g).trans (Subtype.coe_image_subset _ _)
  -- `g ↦ g̃` is linear
  have hext_add : ∀ g₁ g₂, ext (g₁ + g₂) = ext g₁ + ext g₂ := by
    intro g₁ g₂
    funext y
    by_cases hy : y ∈ U
    · rw [Pi.add_apply, hin _ y hy, hin _ y hy, hin _ y hy,
        CompactlySupportedContinuousMap.add_apply, map_add]
    · rw [Pi.add_apply, hout _ y hy, hout _ y hy, hout _ y hy, add_zero]
  have hext_smul : ∀ (t : ℝ) g, ext (t • g) = t • ext g := by
    intro t g
    funext y
    by_cases hy : y ∈ U
    · rw [Pi.smul_apply, hin _ y hy, hin _ y hy, CompactlySupportedContinuousMap.smul_apply,
        map_smul]
    · rw [Pi.smul_apply, hout _ y hy, hout _ y hy, smul_zero]
  -- (c) `L g = Φ g̃`
  refine ⟨{ toFun := fun g => Φ (ext g)
            map_add' := fun g₁ g₂ => by
              simp only [hext_add]
              exact hΦadd _ _ (hcont g₁) (hcpt g₁) (hsptU g₁) (hcont g₂) (hcpt g₂) (hsptU g₂)
            map_smul' := fun t g => by
              simp only [hext_smul, RingHom.id_apply, smul_eq_mul]
              exact hΦsmul t _ (hcont g) (hcpt g) (hsptU g) }, ?_, ?_⟩
  · -- (i) `g = c ∘ ω` gives `g̃ = ω`
    intro ω g hg
    have hω : ext g = (ω : DifferentialForm (Euclid P) n) := by
      funext y
      by_cases hy : y ∈ U
      · rw [hin g y hy, hg ⟨y, hy⟩, c.symm_apply_apply]
      · rw [hout g y hy, image_eq_zero_of_notMem_tsupport fun h => hy (ω.2.2 h)]
    show Φ (ext g) = T ω
    rw [hω, hΦT]
  · -- (ii) `|L g| ≤ M_W(T)` for an open `W ⊂⊂ U` containing `K`
    intro K hK
    obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure
      (hK.image continuous_subtype_val) hU (Subtype.coe_image_subset U K)
    refine ⟨(T.massOn W).toReal, fun g hgK hg1 => ?_⟩
    have hg1' : ∀ y, covectorEuclideanNorm (ext g y) ≤ 1 := by
      intro y
      by_cases hy : y ∈ U
      · rw [hin g y hy, hc, c.apply_symm_apply]
        exact hg1 _
      · rw [hout g y hy, covectorEuclideanNorm_zero]
        exact zero_le_one
    show |Φ (ext g)| ≤ (T.massOn W).toReal
    simpa only [one_mul] using hΦbd W (ext g) 1 hW ⟨hWc, hWU⟩ (hcont g) (hcpt g)
      ((hspt g).trans ((image_mono hgK).trans hKW)) hg1'
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

/-- **Riesz representation of locally bounded functionals on `C_c(X, ℝ^d)`** (step 3 of the
foundations of the moving blow-ups for Simon's dimension reduction, Ch. 7; the representation of
Simon Ch. 1, 4.14 used for currents in Ch. 6, 2.7).  If `X` is locally compact Hausdorff and second
countable with its Borel σ-algebra and `L : C_c(X, ℝ^d) → ℝ` is linear with `|L g| ≤ M_K`
whenever `tsupport g ⊆ K` and `‖g‖ ≤ 1`, then `L g = ∫ ⟨g, ν⟩ dμ₀` for a measure `μ₀` finite on
compact sets and a measurable `ν : X → ℝ^d` integrable on compact sets.  The coordinate
functionals `Λᵢ f = L(f eᵢ)` are locally bounded (`cmr_vr_coordinate_functional`), each is a
difference `Pᵢ − Nᵢ` of positive functionals (`cmr_vr_jordan_decomposition`, total variation),
the Riesz–Markov–Kakutani measures of all `Pᵢ, Nᵢ` have densities `ρᵢ` against one common `μ₀`
(`cmr_vr_common_density`), and `ν = Σᵢ ρᵢ eᵢ` (`cmr_vr_coordinate_assembly`). -/
theorem Submission.dimred_mbl_fnd_vector_riesz_representation : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∃ (μ₀ : Measure X) (ν : X → EuclideanSpace ℝ (Fin d)), IsFiniteMeasureOnCompacts μ₀ ∧ Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀ := by
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

/-- **Representation of a current of locally finite mass by its mass measure** (Simon Ch. 6,
2.7–2.8: `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T` with `|ξ| ≤ 1` and `μ_T(W) = M_W(T)`; `|·|_E` is
`covectorEuclideanNorm`).  Choose coordinates `c` with `|α|_E = ‖c α‖`
(`Submission.cmr_covector_euclidean_equiv`) and a linear extension `L` of `T` to `C_c(U, ℝᵈ)`
that is bounded on each compact set (`Submission.dimred_mbl_fnd_testForm_extension_functional`).
`U` is open, hence locally compact, and the vector Riesz theorem
(`Submission.dimred_mbl_fnd_vector_riesz_representation`) gives `L g = ∫ ⟨g, ν⟩ dμ₀` on `U`.
The polar normalization `μ = val_*(|ν| μ₀)`, `ξ = ⟨ν / |ν|, c(·)⟩`
(`Submission.cmrc_polar_pushforward`) gives `μ(Uᶜ) = 0`, `μ(K) < ∞` for compact `K ⊆ U`,
measurability, `|ξ(α)| ≤ |α|_E` and a norming field `β` with `ξ(β) = 1` `μ`-a.e.  For a test
form `ω`, `g = c ∘ ω` lies in `C_c(U, ℝᵈ)`, so `T(ω) = L(g) = ∫ ⟨c ω, ν⟩ dμ₀ = ∫ ξ(ω) dμ`.  Then
`M_W(T) ≤ μ(W)` because `|ξ(ω)| ≤ |ω|_E ≤ 1`; conversely `μ(W') ≤ M_W(T)` for open `W' ⊂⊂ U`
with `W' ⊆ W`, by approximating `β` with test forms, and exhausting `W ∩ U` by such `W'` gives
`μ(W) ≤ M_W(T)`. -/
theorem Submission.dimred_mbl_fnd_exists_massRepresentation_core : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by
  intro P n U T hU hfin
  -- Step 1: coordinates `c` on covectors with `|α|_E = ‖c α‖`
  obtain ⟨d, c, hc⟩ := Submission.cmr_covector_euclidean_equiv P n
  -- Step 2: a linear extension `L` of `T` to `C_c(U, ℝᵈ)`, bounded on each compact set
  obtain ⟨L, hLT, hLb⟩ :=
    Submission.dimred_mbl_fnd_testForm_extension_functional P n U T d c hU hfin hc
  -- Step 3: `U` is open, hence locally compact, and `L g = ∫ ⟨g, ν⟩ dμ₀` by vector Riesz
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨μ₀, ν, -, hνm, hνi, hL⟩ :=
    Submission.dimred_mbl_fnd_vector_riesz_representation U d L hLb
  -- Steps 4–7, 9: `μ = val_*(|ν| μ₀)`, `ξ = ⟨ν / |ν|, c(·)⟩` and the norming field `β`
  obtain ⟨μ, ξ, β, hUc, hμK, hξm, hξ1, hβm, hβC, hβ1, hξβ, hνξ⟩ :=
    Submission.cmrc_polar_pushforward P n d U c μ₀ ν hU hc hνm hνi
  -- Step 8: `T(ω) = L(c ∘ ω) = ∫ ⟨c ω, ν⟩ dμ₀ = ∫ ξ(ω) dμ`
  have hT : ∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
    intro ω
    obtain ⟨g, hg⟩ :=
      Submission.cmrc_testForm_restrict_cc P n d U c c.continuous (map_zero c) ω
    rw [← hLT ω g hg, hL g, ← hνξ ω]
    simp only [hg]
  refine ⟨μ, ξ, hUc, hμK, fun W hW => le_antisymm ?_ ?_, hξm, hξ1, hT⟩
  · -- Step 10: `M_W(T) ≤ μ(W)`, as `|ξ(ω)| ≤ |ω|_E ≤ 1`
    exact Submission.cmrc_massOn_le_of_repr P n U T μ ξ hξ1 hT W
  · -- Steps 11–12: `μ(W') ≤ M_W(T)` for open `W' ⊂⊂ U` with `W' ⊆ W`; exhaust `W ∩ U`
    exact Submission.cmrc_measure_le_of_compactlyContained P μ U W (T.massOn W) hU hW hUc
      fun W' hW' hW'U hW'W => Submission.cmrc_measure_le_massOn_of_norming P n U T μ ξ β hμK
        hξm hξ1 hT hβm hβC hβ1 hξβ W W' hW' hW'U hW'W
/-- **Directional difference estimate from the divergence bound** (steps 1–2 of the parent proof).
For `‖w‖ ≤ 1` the field `g(y) = a(y + v) • w` is admissible and `div g(y) = Da(y + v)(w)` (trace
of a rank-one map), so `|∫ h·Da(q + v)(w) dν| ≤ Λ`.  The fundamental theorem of calculus along
`s ↦ q x + s • z` and Fubini on `(0, 1] × X` (majorant `M‖z‖|h|`, `‖Da‖ ≤ M`) give
`∫ h·(a(q + z) − a(q)) dν = ∫₀¹ ∫ h·Da(q + s • z)(z) dν ds`, and `Da(p)(z) = ‖z‖·Da(p)(w)` with
`w = ‖z‖⁻¹ • z` bounds the inner integral by `Λ‖z‖`. -/
theorem Submission.cmr_tdn_directional_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, |a y| ≤ 1) → ∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖ := by
  intro n X _ ν q h Λ hν hq hh hdiv a ha hsupp hbd z
  -- Step 1: `a` is differentiable, `Da` is continuous with compact support, so `‖Da‖ ≤ M`
  have h0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ a := ha.differentiable h0
  have hcont : Continuous (fderiv ℝ a) := ha.continuous_fderiv h0
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support (hsupp.fderiv ℝ)
  -- Step 3: for `‖w‖ ≤ 1` the field `g(y) = a(y + v) • w` is admissible, with
  -- `div g(y) = Da(y + v)(w)`; this gives `(∗)`
  have key : ∀ v w : Euclid n, ‖w‖ ≤ 1 → |∫ x, h x * fderiv ℝ a (q x + v) w ∂ν| ≤ Λ := by
    intro v w hw
    set g : Euclid n → Euclid n := fun y => a (y + v) • w with hg_def
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
      (ha.comp (contDiff_id.add contDiff_const)).smul contDiff_const
    have hg_supp : HasCompactSupport g :=
      (hsupp.comp_homeomorph (Homeomorph.addRight v)).smul_right (f' := fun _ => w)
    have hg_bd : ∀ y, ‖g y‖ ≤ 1 := by
      intro y
      simp only [hg_def, norm_smul, Real.norm_eq_abs]
      calc |a (y + v)| * ‖w‖ ≤ 1 * 1 := mul_le_mul (hbd _) hw (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have htrace : ∀ y, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g y).toLinearMap
        = fderiv ℝ a (y + v) w := by
      intro y
      have h1 : HasFDerivAt (fun y => a (y + v)) (fderiv ℝ a (y + v)) y :=
        (hasFDerivAt_comp_add_right v).2 (hdiff (y + v)).hasFDerivAt
      rw [(h1.smul_const w).fderiv, ContinuousLinearMap.coe_smulRight,
        LinearMap.trace_smulRight]
      rfl
    simpa only [htrace] using hdiv g hg_smooth hg_supp hg_bd
  -- Step 4: fundamental theorem of calculus along `s ↦ q x + s • z`
  have hftc : ∀ x, ∫ s in (0 : ℝ)..1, h x * fderiv ℝ a (q x + s • z) z
      = h x * (a (q x + z) - a (q x)) := by
    intro x
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => a (q x + s • z)) (fderiv ℝ a (q x + s • z) z) s := by
      intro s _
      have hline : HasDerivAt (fun s : ℝ => q x + s • z) z s := by
        simpa using ((hasDerivAt_id s).smul_const z).const_add (q x)
      exact (hdiff (q x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
    have hcontS : Continuous (fun s : ℝ => fderiv ℝ a (q x + s • z) z) :=
      (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcontS.intervalIntegrable 0 1)]
    simp
  -- Step 5: Fubini on `Leb|(0, 1] ⊗ ν`, with integrable majorant `M‖z‖|h|`
  have hGint : Integrable (uncurry fun (s : ℝ) (x : X) => h x * fderiv ℝ a (q x + s • z) z)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) := by
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
      rw [uIoc_of_le zero_le_one]; infer_instance
    have hmaj : Integrable (fun p : ℝ × X => (M * ‖z‖) * |h p.2|)
        ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) :=
      (hh.abs.comp_snd _).const_mul _
    refine hmaj.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : ℝ × X => h p.2)
          ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) := hh.aestronglyMeasurable.comp_snd
      have h2 : Continuous (fun p : ℝ × Euclid n => fderiv ℝ a (p.2 + p.1 • z) z) :=
        (hcont.comp (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
          continuous_const
      have h3 : Measurable (fun p : ℝ × X => (p.1, q p.2)) :=
        measurable_fst.prodMk (hq.comp measurable_snd)
      exact h1.mul (h2.measurable.comp h3).aestronglyMeasurable
    · filter_upwards with p
      simp only [uncurry, Real.norm_eq_abs, abs_mul]
      have hp : |fderiv ℝ a (q p.2 + p.1 • z) z| ≤ M * ‖z‖ :=
        calc |fderiv ℝ a (q p.2 + p.1 • z) z| = ‖fderiv ℝ a (q p.2 + p.1 • z) z‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ a (q p.2 + p.1 • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖z‖ := by gcongr; exact hM _
      calc |h p.2| * |fderiv ℝ a (q p.2 + p.1 • z) z| ≤ |h p.2| * (M * ‖z‖) := by gcongr
        _ = M * ‖z‖ * |h p.2| := by ring
  have heq : ∫ x, h x * (a (q x + z) - a (q x)) ∂ν
      = ∫ s in (0 : ℝ)..1, ∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν := by
    rw [intervalIntegral_integral_swap hGint]
    exact integral_congr_ae (Eventually.of_forall fun x => (hftc x).symm)
  -- Step 6: with `w = ‖z‖⁻¹ • z` (so `‖w‖ ≤ 1`, `z = ‖z‖ • w`, also for `z = 0`),
  -- `(∗)` bounds the inner integral by `Λ‖z‖` for every `s`
  set w : Euclid n := ‖z‖⁻¹ • z with hw_def
  have hw : ‖w‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hw_def, hz]
    · rw [hw_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
  have hzw : z = ‖z‖ • w := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [hw_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz), one_smul]
  have hlin : ∀ p : Euclid n, fderiv ℝ a p z = ‖z‖ * fderiv ℝ a p w := by
    intro p
    conv_lhs => rw [hzw]
    rw [map_smul, smul_eq_mul]
  have hbound : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν‖ ≤ Λ * ‖z‖ := by
    intro s _
    have hrw : ∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν
        = ‖z‖ * ∫ x, h x * fderiv ℝ a (q x + s • z) w ∂ν := by
      rw [← integral_const_mul]
      congr 1
      ext x
      rw [hlin]
      ring
    rw [hrw, Real.norm_eq_abs, abs_mul, abs_norm, mul_comm Λ]
    exact mul_le_mul_of_nonneg_left (key (s • z) w hw) (norm_nonneg _)
  rw [heq]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound
/-- **Ball-averaging estimate** (step 3 of the parent proof).  With `B = B_r(0)` and
`V = λ(B) ∈ (0, ∞)`, Fubini on `ν ⊗ λ⌞B` gives
`V ∫ h(x) a(q x) dν = ∫∫ h(x) a(q x + z) − ∫∫ h(x) (a(q x + z) − a(q x))`.  The second double
integral is at most `V Λ r` by the directional bound (`‖z‖ < r` on `B`), and the first at most
`(∫ |h| dν) ∫ a` since `0 ≤ ∫_B a(q x + z) dz ≤ ∫ a` by translation invariance.  Divide by `V`. -/
theorem Submission.cmr_tdn_ball_average_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ) (a : Euclid n → ℝ) (r : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → 0 ≤ Λ → Continuous a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → (∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖) → 0 < r → |∫ x, h x * a (q x) ∂ν| ≤ r * Λ + (volume (ball (0 : Euclid n) r)).toReal⁻¹ * (∫ x, |h x| ∂ν) * ∫ y, a y := by
  intro n X mX ν q h Λ a r hν hq hh hΛ ha ha_supp ha0 ha1 hdir hr
  -- the ball `B = B_r(0)`: measurable, inside `‖z‖ ≤ r`, of measure `λ(B) ∈ (0, ∞)`
  have hBm : MeasurableSet (ball (0 : Euclid n) r) := measurableSet_ball
  have hBr : ∀ z ∈ ball (0 : Euclid n) r, ‖z‖ ≤ r := fun z hz => (mem_ball_zero_iff.1 hz).le
  have hBpos : 0 < volume (ball (0 : Euclid n) r) := measure_ball_pos volume 0 hr
  have hBfin : volume (ball (0 : Euclid n) r) < ∞ := measure_ball_lt_top
  generalize ball (0 : Euclid n) r = B at hBm hBr hBpos hBfin ⊢
  have hV : 0 < (volume B).toReal := ENNReal.toReal_pos hBpos.ne' hBfin.ne
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin.ne
  have hμB : (volume.restrict B).real univ = (volume B).toReal := by
    rw [measureReal_def, Measure.restrict_apply_univ]
  generalize (volume B).toReal = V at hV hμB ⊢
  -- `a` is integrable, and so are its translates
  have ha_int : Integrable a volume := ha.integrable_of_hasCompactSupport ha_supp
  -- the integrands on `ν ⊗ λ⌞B`, dominated by `|h x|`
  have hm₁ : Measurable fun p : X × Euclid n => a (q p.1 + p.2) :=
    ha.measurable.comp ((hq.comp measurable_fst).add measurable_snd)
  have hm₀ : Measurable fun p : X × Euclid n => a (q p.1) :=
    ha.measurable.comp (hq.comp measurable_fst)
  have hh₁ : AEStronglyMeasurable (fun p : X × Euclid n => h p.1) (ν.prod (volume.restrict B)) :=
    hh.aestronglyMeasurable.comp_fst
  have hdom : Integrable (fun p : X × Euclid n => |h p.1|) (ν.prod (volume.restrict B)) :=
    hh.abs.comp_fst _
  have hG₂ : Integrable (fun p : X × Euclid n => h p.1 * a (q p.1 + p.2))
      (ν.prod (volume.restrict B)) := by
    refine hdom.mono' (hh₁.mul hm₁.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (ha1 _)
  have hG₁ : Integrable (fun p : X × Euclid n => h p.1 * (a (q p.1 + p.2) - a (q p.1)))
      (ν.prod (volume.restrict B)) := by
    refine hdom.mono' (hh₁.mul (hm₁.sub hm₀).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) (abs_sub_le_iff.2 ⟨?_, ?_⟩)
    · linarith [ha0 (q p.1), ha1 (q p.1 + p.2)]
    · linarith [ha0 (q p.1 + p.2), ha1 (q p.1)]
  -- `V F = ∫∫ h(x) a(q x + z) - ∫∫ h(x) (a(q x + z) - a(q x))` over `ν ⊗ λ⌞B`
  have hsplit : V * ∫ x, h x * a (q x) ∂ν =
      (∫ p, h p.1 * a (q p.1 + p.2) ∂(ν.prod (volume.restrict B))) -
        ∫ p, h p.1 * (a (q p.1 + p.2) - a (q p.1)) ∂(ν.prod (volume.restrict B)) := by
    rw [← integral_sub hG₂ hG₁]
    have hfun : (fun p : X × Euclid n =>
        h p.1 * a (q p.1 + p.2) - h p.1 * (a (q p.1 + p.2) - a (q p.1))) =
        fun p => h p.1 * a (q p.1) := by
      funext p
      ring
    rw [hfun, integral_fun_fst (fun x => h x * a (q x)), hμB, smul_eq_mul]
  -- Fubini and the directional bound: `|∫∫ h(x) (a(q x + z) - a(q x))| ≤ V Λ r`
  have hJ : |∫ p, h p.1 * (a (q p.1 + p.2) - a (q p.1)) ∂(ν.prod (volume.restrict B))| ≤
      V * (Λ * r) := by
    rw [integral_prod_symm _ hG₁]
    have hb : ∀ᵐ z ∂(volume.restrict B), ‖∫ x, h x * (a (q x + z) - a (q x)) ∂ν‖ ≤ Λ * r := by
      filter_upwards [ae_restrict_mem hBm] with z hz
      rw [Real.norm_eq_abs]
      exact (hdir z).trans (mul_le_mul_of_nonneg_left (hBr z hz) hΛ)
    have := norm_integral_le_of_norm_le (integrable_const (Λ * r)) hb
    rw [integral_const, hμB, smul_eq_mul, Real.norm_eq_abs] at this
    exact this
  -- translation invariance: `|∫∫ h(x) a(q x + z)| ≤ (∫ |h|) ∫ a`
  have hM : |∫ p, h p.1 * a (q p.1 + p.2) ∂(ν.prod (volume.restrict B))| ≤
      (∫ x, |h x| ∂ν) * ∫ y, a y := by
    rw [integral_prod _ hG₂]
    have hb : ∀ x, ‖∫ z, h x * a (q x + z) ∂(volume.restrict B)‖ ≤ |h x| * ∫ y, a y := by
      intro x
      rw [integral_const_mul, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h0 : 0 ≤ ∫ z, a (q x + z) ∂(volume.restrict B) := integral_nonneg fun z => ha0 _
      rw [abs_of_nonneg h0]
      exact (setIntegral_le_integral (ha_int.comp_add_left (q x))
        (Eventually.of_forall fun z => ha0 _)).trans_eq (integral_add_left_eq_self a (q x))
    have := norm_integral_le_of_norm_le (hh.abs.mul_const (∫ y, a y)) (Eventually.of_forall hb)
    rw [integral_mul_const, Real.norm_eq_abs] at this
    exact this
  -- conclusion: `V |F| ≤ (∫ |h|) ∫ a + V Λ r`, then divide by `V > 0`
  have key : V * |∫ x, h x * a (q x) ∂ν| ≤ (∫ x, |h x| ∂ν) * (∫ y, a y) + V * (Λ * r) := by
    rw [← abs_of_pos hV, ← abs_mul, abs_of_pos hV, hsplit]
    exact (abs_sub _ _).trans (add_le_add hM hJ)
  generalize ∫ x, h x * a (q x) ∂ν = F at key ⊢
  generalize ∫ x, |h x| ∂ν = H at key ⊢
  generalize ∫ y, a y = A at key ⊢
  have hV0 : V ≠ 0 := hV.ne'
  calc |F| ≤ (H * A + V * (Λ * r)) / V := by
        rw [le_div_iff₀ hV]
        linarith
    _ = r * Λ + V⁻¹ * H * A := by
        field_simp
        ring
/-- **Smooth cut-offs of a compact Lebesgue-null set** (steps 4 and 5(ii) of the parent proof).
With `δₖ = 1/(k+1)`, take `aₖ` smooth with values in `[0, 1]`, support `thickening δₖ K`, and
`aₖ = 1` exactly on `K` (`exists_contDiff_support_eq_eq_one_iff`).  Then `aₖ` vanishes off the
compact `cthickening δₖ K`; a point `y ∉ K = ⋂_{δ>0} cthickening δ K` misses some
`cthickening δ K`, so `aₖ(y) = 0` once `δₖ < δ`; and `0 ≤ ∫ aₖ ≤ λ(cthickening δₖ K) → λ(K) = 0`. -/
theorem Submission.cmr_tdn_null_set_cutoffs : ∀ (n : ℕ) (K : Set (Euclid n)), IsCompact K → volume K = 0 → ∃ a : ℕ → Euclid n → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k, HasCompactSupport (a k)) ∧ (∀ k y, 0 ≤ a k y) ∧ (∀ k y, a k y ≤ 1) ∧ (∀ k, ∀ y ∈ K, a k y = 1) ∧ (∀ y, y ∉ K → ∀ᶠ k in atTop, a k y = 0) ∧ Tendsto (fun k => ∫ y, a k y) atTop (𝓝 0) := by
  intro n K hK hK0
  -- `aₖ`: smooth, `[0, 1]`-valued, with support `thickening δₖ K` and `aₖ = 1` exactly on `K`
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hex : ∀ k : ℕ, ∃ f : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
      support f = thickening (1 / ((k : ℝ) + 1)) K ∧ ∀ x, x ∈ K ↔ f x = 1 := fun k =>
    exists_contDiff_support_eq_eq_one_iff isOpen_thickening hK.isClosed
      (self_subset_thickening (hδ k) K)
  choose a ha_smooth ha_range ha_supp ha_one using hex
  have hnonneg : ∀ k y, 0 ≤ a k y := fun k y => (ha_range k (mem_range_self y)).1
  have hle : ∀ k y, a k y ≤ 1 := fun k y => (ha_range k (mem_range_self y)).2
  -- `aₖ` vanishes off the compact `cthickening δₖ K`
  have hzero : ∀ (k : ℕ) y, y ∉ cthickening (1 / ((k : ℝ) + 1)) K → a k y = 0 := by
    intro k y hy
    by_contra h
    have hy' : y ∈ support (a k) := h
    rw [ha_supp k] at hy'
    exact hy (thickening_subset_cthickening _ _ hy')
  refine ⟨a, ha_smooth, fun k => HasCompactSupport.intro hK.cthickening (hzero k), hnonneg, hle,
    fun k y hy => (ha_one k y).1 hy, ?_, ?_⟩
  · -- `y ∉ K = ⋂_{δ>0} cthickening δ K`, so `y ∉ cthickening δ K ⊇ cthickening δₖ K` for some
    -- `δ > 0` and all `k` with `δₖ < δ`
    intro y hy
    rw [← hK.isClosed.closure_eq, closure_eq_iInter_cthickening] at hy
    simp only [mem_iInter, not_forall] at hy
    obtain ⟨δ, hδpos, hyδ⟩ := hy
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hδpos
    filter_upwards [eventually_ge_atTop k₀] with k hk
    refine hzero k y fun hmem => hyδ (cthickening_mono ?_ K hmem)
    have hkk₀ : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    linarith
  · -- `0 ≤ ∫ aₖ ≤ λ(cthickening δₖ K)`, and `λ(cthickening δₖ K) → λ(K) = 0`
    have hmeas : Tendsto (fun k : ℕ => (volume (cthickening (1 / ((k : ℝ) + 1)) K)).toReal)
        atTop (𝓝 0) := by
      have h := (tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure (Euclid n)))
        hK).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rw [hK0] at h
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas
      (fun k => integral_nonneg (hnonneg k)) fun k => ?_
    set C := cthickening (1 / ((k : ℝ) + 1)) K
    have hCm : MeasurableSet C := isClosed_cthickening.measurableSet
    have hint : Integrable (C.indicator fun _ => (1 : ℝ)) volume :=
      (integrable_indicator_iff hCm).2 (integrableOn_const hK.cthickening.measure_lt_top.ne)
    have hind : ∀ y, a k y ≤ C.indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ C
      · rw [indicator_of_mem hy]
        exact hle k y
      · rw [indicator_of_notMem hy, hzero k y hy]
    calc ∫ y, a k y ≤ ∫ y, C.indicator (fun _ => (1 : ℝ)) y :=
          integral_mono_of_nonneg (Eventually.of_forall (hnonneg k)) hint
            (Eventually.of_forall hind)
      _ = (volume C).toReal := by
          rw [integral_indicator_const _ hCm]
          simp [measureReal_def]

/-- **Vanishing on compact null sets from an `ε + C ∫ a` bound** (steps 5(i) and 6 of the
top-dimensional null-set argument): let `q : X → ℝⁿ` be measurable and `h ∈ L¹(ν)` (`ν` need not
be finite), and suppose that for every `ε > 0` there is `C` with `|∫ h · a(q) dν| ≤ ε + C ∫ a`
for all smooth compactly supported `0 ≤ a ≤ 1`.  Then `∫_{q⁻¹K} h dν = 0` for every compact
Lebesgue-null `K ⊆ ℝⁿ`.  Along the cut-offs `a_k` of `K` given by
`Submission.cmr_tdn_null_set_cutoffs`, dominated convergence (majorant `|h|`) gives
`∫ h · a_k(q) dν → ∫_{q⁻¹K} h dν`, while `ε + C ∫ a_k → ε`; so `|∫_{q⁻¹K} h dν| ≤ ε` for every
`ε > 0`. -/
theorem Submission.cmr_tdn_null_of_average_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ), Measurable q → Integrable h ν → (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → |∫ x, h x * a (q x) ∂ν| ≤ ε + C * ∫ y, a y) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0 := by
  intro n X _ ν q h hq hh hbd K hK hK0
  -- smooth cut-offs `a k` of `K`: `a k = 1` on `K`, `a k → 0` pointwise off `K`, `∫ a k → 0`
  obtain ⟨a, ha, hac, ha0, ha1, haK, haoff, haint⟩ :=
    Submission.cmr_tdn_null_set_cutoffs n K hK hK0
  -- dominated convergence with majorant `|h|`: `∫ h (a k ∘ q) dν → ∫ 1_{q⁻¹K} h dν`
  have hE : MeasurableSet (q ⁻¹' K) := hq hK.isClosed.measurableSet
  have hlim : Tendsto (fun k => ∫ x, h x * a k (q x) ∂ν) atTop
      (𝓝 (∫ x in q ⁻¹' K, h x ∂ν)) := by
    rw [← integral_indicator hE]
    refine tendsto_integral_of_dominated_convergence (fun x => |h x|)
      (fun k => hh.aestronglyMeasurable.mul
        ((ha k).continuous.measurable.comp hq).aestronglyMeasurable)
      hh.abs (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k (q x))]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha1 k (q x))
    · by_cases hx : q x ∈ K
      · have h1 : ∀ k, a k (q x) = 1 := fun k => haK k (q x) hx
        simp only [indicator_of_mem (show x ∈ q ⁻¹' K from hx), h1, mul_one]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem (show x ∉ q ⁻¹' K from hx)]
        refine tendsto_nhds_of_eventually_eq ?_
        filter_upwards [haoff (q x) hx] with k hk
        rw [hk, mul_zero]
  -- for `ε > 0`: `|∫ h (a k ∘ q) dν| ≤ ε + C ∫ a k → ε`, so `|∫_{q⁻¹K} h dν| ≤ ε`
  refine abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨C, hC⟩ := hbd ε hε
  have hR : Tendsto (fun k => ε + C * ∫ y, a k y) atTop (𝓝 (ε + C * 0)) :=
    tendsto_const_nhds.add (haint.const_mul C)
  rw [mul_zero, add_zero] at hR
  rw [zero_add]
  exact le_of_tendsto_of_tendsto' hlim.abs hR fun k => hC (a k) (ha k) (hac k) (ha0 k) (ha1 k)

/-- **Compact Lebesgue-null sets are `q_#(h ν)`-null under a divergence bound** (Lemma TD of the
parent proof, for the finite signed measure `m = q_#(h ν)`): if `|∫ h · div g(q) dν| ≤ Λ` for all
smooth compactly supported fields `g` with `‖g‖ ≤ 1`, then `∫_{q⁻¹K} h dν = 0` for every compact
Lebesgue-null `K ⊆ ℝⁿ`.  The field `g = 0` gives `Λ ≥ 0`, and
`Submission.cmr_tdn_directional_bound` gives `|∫ h (a(q + z) − a(q)) dν| ≤ Λ‖z‖` for smooth
compactly supported `|a| ≤ 1`.  Given `ε > 0`, take `r = ε / (Λ + 1)`, so that `rΛ ≤ ε`; averaging
over `B_r(0)` (`Submission.cmr_tdn_ball_average_bound`) gives
`|∫ h · a(q) dν| ≤ ε + λ(B_r)⁻¹ ‖h‖₁ ∫ a` for smooth compactly supported `0 ≤ a ≤ 1`, and
`Submission.cmr_tdn_null_of_average_bound` turns these bounds into the claim. -/
theorem Submission.dimred_mbl_fnd_null_of_div_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0 := by
  intro n X _ ν q h Λ hν hq hh hdiv
  -- step 1: `Λ ≥ 0`, testing with the field `g = 0`
  have hΛ : 0 ≤ Λ := by
    simpa using hdiv (fun _ => 0) contDiff_const HasCompactSupport.zero fun _ => by simp
  -- step 2: `|∫ h (a(q + z) − a(q)) dν| ≤ Λ‖z‖` for smooth compactly supported `|a| ≤ 1`
  have hdir := Submission.cmr_tdn_directional_bound n X ν q h Λ hν hq hh hdiv
  -- steps 3–6: an `ε + C ∫ a` bound for every `ε > 0` suffices
  refine Submission.cmr_tdn_null_of_average_bound n X ν q h hq hh fun ε hε => ?_
  -- average over `B_r(0)` with `r = ε / (Λ + 1)`, so that `rΛ ≤ ε`
  obtain ⟨r, hr, hrΛ⟩ : ∃ r : ℝ, 0 < r ∧ r * Λ ≤ ε := by
    refine ⟨ε / (Λ + 1), div_pos hε (by linarith), ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨(volume (ball (0 : Euclid n) r)).toReal⁻¹ * ∫ x, |h x| ∂ν, fun a ha hac ha0 ha1 => ?_⟩
  have hB := Submission.cmr_tdn_ball_average_bound n X ν q h Λ a r hν hq hh hΛ ha.continuous hac
    ha0 ha1 (hdir a ha hac fun y => abs_le.2 ⟨by linarith [ha0 y], ha1 y⟩) hr
  linarith

/-- **Divergence form of `d(b · θ(G, ·))` with bounds uniform in `g`** (the form identity of
step 9 of the representation of currents of locally finite mass, used for the absolute continuity
in Simon 6.2.36).  Let `θ = dx^I` be the `(m+1)`-covector `θ(v) = det (v j (I k))_{k,j}` on `ℝᴾ`,
`p x = (x (I k))_k`, and `ι` a continuous linear right inverse of `p`.  For smooth `g` with
`‖g‖ ≤ 1` put `G = ι ∘ g ∘ p`, `η(x) = b(x) θ(G x, ·)` and `ζ(x) = Db(x) ∧ θ(G x, ·)`, i.e.
`ζ(x)(w) = Σᵢ (-1)ⁱ Db(x)(wᵢ) θ(G x, ŵᵢ)`.  Both are smooth; `η` vanishes where `b` does and `ζ`
where `Db` does, so both are test forms supported in `tsupport b`.  By
`Submission.cmr_df_extDeriv_smul_curryLeft`, `dη(x)(w) = ζ(x)(w) + b(x) Σᵢ (-1)ⁱ θ(DG(x)wᵢ, ŵᵢ)`,
and since `(DG(x)v)(I k) = (Dg(p x)(p v))_k`, `Submission.cmr_df_cons_sum_trace` turns the sum into
`tr(Dg(p x)) θ(w)`.  Finally `‖G x‖ ≤ ‖ι‖` gives `‖η(x)‖ ≤ sup|b| ‖θ‖ ‖ι‖` and
`‖ζ(x)‖ ≤ (m+1) sup‖Db‖ ‖θ‖ ‖ι‖`, and the Euclidean coefficient norm is at most a constant times
the operator norm (`Submission.rsd_mw_tfa_norm_props`), so `K` does not depend on `g`. -/
theorem Submission.dimred_mbl_fnd_coordinate_divergence_form : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ), StrictMono I → (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → ∃ K : ℝ, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → (∀ y, ‖g y‖ ≤ 1) → ∃ (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)), IsTestForm η ∧ IsTestForm ζ ∧ tsupport η ⊆ tsupport b ∧ tsupport ζ ⊆ tsupport b ∧ (∀ x, covectorEuclideanNorm (η x) ≤ K) ∧ (∀ x, covectorEuclideanNorm (ζ x) ≤ K) ∧ ∀ x, exteriorDerivative η x = (b x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ + ζ x := by
  intro P m I θ b hI hθ hb hbc
  -- Step 0: the coordinate projection `p` and a continuous linear right inverse `ι` of it
  obtain ⟨p, hp⟩ : ∃ p : Euclid P →L[ℝ] Euclid (m + 1),
      ∀ x, p x = WithLp.toLp 2 (fun k => x (I k)) :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun x => WithLp.toLp 2 (fun k => x (I k))
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }, fun x => rfl⟩
  obtain ⟨ι, hι⟩ : ∃ ι : Euclid (m + 1) →L[ℝ] Euclid P, ∀ y k, ι y (I k) = y k := by
    refine ⟨∑ k : Fin (m + 1),
      (EuclideanSpace.proj k : Euclid (m + 1) →L[ℝ] ℝ).smulRight
        (EuclideanSpace.single (I k) (1 : ℝ)), fun y k => ?_⟩
    simp [Pi.single_apply, hI.injective.eq_iff]
  -- Step 1: `β₀ = sup |b|`, `β₁ = sup ‖Db‖`, and the norm comparison constants `C₀`, `C₁`
  obtain ⟨β₀, hβ₀⟩ := hb.continuous.bounded_above_of_compact_support hbc
  obtain ⟨β₁, hβ₁⟩ :=
    (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support (hbc.fderiv ℝ)
  obtain ⟨C₀, hC₀, hC₀le⟩ := (Submission.rsd_mw_tfa_norm_props P m).2.2.1
  obtain ⟨C₁, hC₁, hC₁le⟩ := (Submission.rsd_mw_tfa_norm_props P (m + 1)).2.2.1
  have hβ₀0 : 0 ≤ β₀ := (norm_nonneg _).trans (hβ₀ 0)
  have hβ₁0 : 0 ≤ β₁ := (norm_nonneg _).trans (hβ₁ 0)
  have hR0 : 0 ≤ ‖θ‖ * ‖ι‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨C₀ * (β₀ * (‖θ‖ * ‖ι‖)) + C₁ * ((m + 1) * (β₁ * (‖θ‖ * ‖ι‖))), fun g hg hg1 => ?_⟩
  -- Step 2: the vector field `G = ι ∘ g ∘ p`, with `‖θ(G x, ·)‖ ≤ ‖θ‖ ‖ι‖`
  set G : Euclid P → Euclid P := fun x => ι (g (p x))
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := ι.contDiff.comp (hg.comp p.contDiff)
  have hcb : ∀ x, ‖ContinuousAlternatingMap.curryLeft θ (G x)‖ ≤ ‖θ‖ * ‖ι‖ := fun x => by
    calc _ ≤ ‖ContinuousAlternatingMap.curryLeft θ‖ * ‖G x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖θ‖ * ‖ι‖ := by
        rw [ContinuousAlternatingMap.norm_curryLeft]
        gcongr
        exact (ι.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (hg1 _))
  -- Step 3: `ζ(x) = Db(x) ∧ θ(G x, ·)`, which vanishes where `Db` does
  let ζ : DifferentialForm (Euclid P) (m + 1) := fun x =>
    ContinuousAlternatingMap.alternatizeUncurryFin
      ((fderiv ℝ b x).smulRight (ContinuousAlternatingMap.curryLeft θ (G x)))
  have hζsupp : support ζ ⊆ support (fderiv ℝ b) := fun x hx => by
    rw [Function.mem_support] at hx ⊢
    intro h0
    apply hx
    simp only [ζ, h0, ContinuousLinearMap.zero_smulRight]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ)
  refine ⟨fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y), ζ, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    tsupport_smul_subset_left _ _, (closure_mono hζsupp).trans (tsupport_fderiv_subset ℝ),
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  -- Step 4: `η` and `ζ` are smooth with compact support
  · exact hb.smul ((ContinuousAlternatingMap.curryLeft θ).contDiff.comp hGs)
  · exact hbc.smul_right
  · exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ).contDiff.comp
      ((contDiff_infty_iff_fderiv.1 hb).2.smulRight
        ((ContinuousAlternatingMap.curryLeft θ).contDiff.comp hGs))
  · exact (hbc.fderiv ℝ).mono hζsupp
  -- Step 5: `|η(x)| ≤ C₀ ‖η(x)‖ ≤ C₀ β₀ ‖θ‖ ‖ι‖` and `|ζ(x)| ≤ C₁ (m+1) β₁ ‖θ‖ ‖ι‖`
  · refine (hC₀le _).trans (le_add_of_le_of_nonneg ?_
      (mul_nonneg hC₁ (mul_nonneg (by positivity) (mul_nonneg hβ₁0 hR0))))
    gcongr
    rw [norm_smul]
    exact mul_le_mul (hβ₀ x) (hcb x) (norm_nonneg _) hβ₀0
  · refine (hC₁le _).trans (le_add_of_nonneg_of_le
      (mul_nonneg hC₀ (mul_nonneg hβ₀0 hR0)) ?_)
    gcongr
    refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans ?_
    gcongr
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (hβ₁ x) (hcb x) (norm_nonneg _) hβ₁0
  -- Step 6: `dη(x) = ζ(x) + b(x) Σᵢ (-1)ⁱ θ(DG(x)wᵢ, ŵᵢ) = ζ(x) + b(x) tr(Dg(p x)) θ`
  · have hbx : DifferentiableAt ℝ b x := (hb.differentiable (by simp)).differentiableAt
    have hgx : HasFDerivAt g (fderiv ℝ g (p x)) (p x) :=
      ((hg.differentiable (by simp)).differentiableAt).hasFDerivAt
    have hGx : HasFDerivAt G (ι.comp ((fderiv ℝ g (p x)).comp p)) x :=
      ι.hasFDerivAt.comp x (hgx.comp x p.hasFDerivAt)
    have hL : ∀ (v : Euclid P) (k : Fin (m + 1)), fderiv ℝ G x v (I k) =
        (fderiv ℝ g (p x)).toLinearMap (WithLp.toLp 2 (fun k' => v (I k'))) k := by
      intro v k
      rw [hGx.fderiv, ← hp v]
      exact hι _ k
    ext w
    have h3 := Submission.cmr_df_extDeriv_smul_curryLeft P m θ b G x hbx
      hGx.differentiableAt w
    have h2 := Submission.cmr_df_cons_sum_trace P m I θ (fderiv ℝ g (p x)).toLinearMap
      (fderiv ℝ G x) hθ hL w
    have hζ : ζ x w = ∑ i : Fin (m + 1),
        (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w))) := by
      simp only [ζ, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
        ContinuousAlternatingMap.curryLeft_apply_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rfl
    rw [h3, ← hp x, ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hζ, mul_assoc, ← h2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- **Simon 6.2.36** (`μ_T` charges no `Hⁿ`-null set when `M_W(∂T) < ∞` for `W ⊂⊂ U`): if
`T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|⟨α, ξ⟩| ≤ |α|`, `M_W(T) = μ(W)` and `μ` lives on `U`, then
`Hⁿ(E) = 0` implies `μ(E) = 0`.  For `n = 0`, `H⁰` is counting measure, so `E = ∅`.  For
`n = m + 1` it suffices to treat a compact `Hⁿ`-null `C ⊆ U`; take an open `W ⊂⊂ U` around `C`.
For each strictly increasing `I`, the coordinate projection `q_I` maps `C` onto a compact
Lebesgue-null `N ⊆ ℝⁿ`, and the coordinate divergence forms give
`|∫ b ⟨θ_I, ξ⟩ div g(q_I) dμ⌞W| ≤ K_b (M_W(∂T) + M_W(T))` uniformly in `‖g‖ ≤ 1`.  Hence
`⟨θ_I, ξ⟩ = 0` `μ`-a.e. on `W ∩ q_I⁻¹(N) ⊇ C`; the coordinate covectors `θ_I` determine `ξ`, so
`ξ = 0` `μ`-a.e. on `C`, and `M_W(T) = μ(W)` forces `μ(C) = 0`. -/
theorem Submission.dimred_mbl_fnd_null_of_representation : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0 := by
  intro P n U T μ ξ hU hB hUc hK hmass hξm hξ hT
  -- Step 9: it suffices to treat compact `Hⁿ`-null subsets of `U`
  refine Submission.cmr_null_of_compact_null P U μ μHE[n] hU hUc hK ?_
  intro C hC hCU hC0
  cases n with
  | zero =>
    -- Step 1: `H⁰` is counting measure, so `C = ∅`
    rw [Measure.euclideanHausdorffMeasure_zero] at hC0
    have hCe : C = ∅ := eq_empty_of_forall_notMem fun x hx => by
      simpa [hC0] using measure_mono (μ := (μH[0] : Measure (Euclid P))) (singleton_subset_iff.2 hx)
    rw [hCe, measure_empty]
  | succ m =>
    -- Step 2: an open `W ⊂⊂ U` around `C`, of finite mass and boundary mass
    obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
    have hWo : IsOpen (thickening δ C) := isOpen_thickening
    have hCW : C ⊆ thickening δ C := self_subset_thickening hδ C
    have hWcl : closure (thickening δ C) ⊆ cthickening δ C :=
      closure_thickening_subset_cthickening δ C
    have hWc : CompactlyContained (thickening δ C) U :=
      ⟨hC.cthickening.of_isClosed_subset isClosed_closure hWcl, hWcl.trans hδU⟩
    have hWU : thickening δ C ⊆ U := subset_closure.trans hWc.2
    have hμW : μ (thickening δ C) < ∞ :=
      (measure_mono subset_closure).trans_lt (hK _ hWc.1 hWc.2)
    have hTW : T.massOn (thickening δ C) = μ (thickening δ C) := hmass _ hWo
    have hTW' : T.massOn (thickening δ C) ≠ ∞ := by rw [hTW]; exact hμW.ne
    have hbd : T.boundary.massOn (thickening δ C) ≠ ∞ := (hB _ hWo hWc).ne
    -- Steps 3–6: `⟨θ_I, ξ⟩ = 0` `μ`-a.e. on `C` for each coordinate covector `θ_I`
    obtain ⟨hθex, hspan⟩ := Submission.dimred_mbl_fnd_coordinate_covectors_span P (m + 1)
    choose θI hθI using hθex
    have hcoord : ∀ I : Fin (m + 1) → Fin P, StrictMono I →
        ∀ᵐ x ∂μ, x ∈ C → ξ x (θI I) = 0 := by
      intro I hI
      set q : Euclid P → Euclid (m + 1) := fun x => WithLp.toLp 2 (fun k => x (I k))
      have hqc : Continuous q := by fun_prop
      have hN : IsCompact (q '' C) := hC.image hqc
      have hNv : volume (q '' C) = 0 :=
        Submission.cmr_volume_coordProj_image_null P (m + 1) I C hI.injective hC0
      have h := Submission.cmr_ae_zero_of_div_bounds P (m + 1) (thickening δ C) μ
        (fun x => ξ x (θI I)) q (q '' C) (covectorEuclideanNorm (θI I)) hWo hμW
        (hξm.apply_continuousLinearMap _) (fun x => hξ x _) hqc.measurable hN.measurableSet
        (fun ν h Λ hν hh hΛ => Submission.dimred_mbl_fnd_null_of_div_bound (m + 1) (Euclid P) ν q
          h Λ hν hqc.measurable hh hΛ (q '' C) hN hNv) ?_
      · filter_upwards [h] with x hx hxC
        exact hx (hCW hxC) (mem_image_of_mem q hxC)
      · -- Step 4: the divergence bound, uniformly in `g`
        intro b hb hbc hbW
        obtain ⟨K, hKg⟩ :=
          Submission.dimred_mbl_fnd_coordinate_divergence_form P m I (θI I) b hI (hθI I) hb hbc
        refine ⟨K * ((T.boundary.massOn (thickening δ C)).toReal +
          (T.massOn (thickening δ C)).toReal), fun g hg _ hg1 => ?_⟩
        obtain ⟨η, ζ, hη, hζ, hηb, hζb, hηK, hζK, hd⟩ := hKg g hg hg1
        exact Submission.cmr_abs_integral_div_le_mass P m U (thickening δ C) T μ ξ (θI I) b
          (fun x => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (q x)).toLinearMap) η ζ K
          hWU hTW' hbd hT (fun k S ω r => Submission.cmr_abs_apply_le_massOn P k U _ S ω r)
          hbW hη hζ hηb hζb hηK hζK hd
    -- Step 7: the coordinate covectors determine `ξ`, so `ξ = 0` `μ`-a.e. on `C`
    have hξC : ∀ᵐ x ∂μ, x ∈ C → ξ x = 0 := by
      have hall : ∀ᵐ x ∂μ, ∀ I : Fin (m + 1) → Fin P, StrictMono I → x ∈ C →
          ξ x (θI I) = 0 := by
        rw [ae_all_iff]
        intro I
        by_cases hI : StrictMono I
        · filter_upwards [hcoord I hI] with x hx _ using hx
        · exact ae_of_all _ fun x h => absurd h hI
      filter_upwards [hall] with x hx hxC
      refine hspan (ξ x) fun I θ hI hθ => ?_
      rw [show θ = θI I from ContinuousAlternatingMap.ext fun v => by rw [hθ, hθI]]
      exact hx I hI hxC
    -- Step 8: `M_W(T) = μ(W)` and `ξ = 0` a.e. on `C` force `μ(C) = 0`
    exact Submission.cmr_measure_null_of_orient_ae_zero P (m + 1) U (thickening δ C) C T μ ξ
      hWo.measurableSet hC.measurableSet hCW hμW hTW hξ hT hξC

/-- **Foundations** (Simon Ch. 6, 2.7–2.8 and 2.35–2.37; Ch. 3, 1.5(2) and 1.6; Ch. 6, 2.6, 2.9
and 3.2(1)).
(REP) A current `T ∈ 𝒟ₙ(U)` with `M_W(T) < ∞` for every open `W ⊂⊂ U` is `T(ω) = ∫ ⟨ω, ξ⟩ dμ`,
where `μ(W) = M_W(T)` for open `W`, `μ(ℝᴾ ∖ U) = 0`, `μ` is finite on compact subsets of `U` and
`|⟨α, ξ(x)⟩| ≤ |α|` (Riesz, 2.7–2.8).  If moreover `M_W(∂T) < ∞` for every open `W ⊂⊂ U`, then
`μ` does not charge `Hⁿ`-null sets (2.36).
(IMC) Tangent locality, restriction, differences and the orientation bound for integer
multiplicity currents.

Proof: the representation `(μ, ξ)` with its six properties is
`dimred_mbl_fnd_exists_massRepresentation_core`; `dimred_mbl_fnd_null_of_representation`,
applied to the same `(μ, ξ)`, gives the absolute continuity; (IMC) is
`cmc_imRep_locality_restrict_sub`. -/
theorem Submission.dimred_mbl_current_foundations : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) ∧ ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) := by
  refine ⟨fun P n U T hU hmass => ?_, Submission.cmc_imRep_locality_restrict_sub⟩
  -- `T = ξ μ` with `μ(W) = M_W(T)` for open `W` (2.7–2.8)
  obtain ⟨μ, ξ, hμU, hμK, hμW, hξ, hξα, hTξ⟩ :=
    Submission.dimred_mbl_fnd_exists_massRepresentation_core P n U T hU hmass
  -- locally finite `M(∂T)`: `μ` vanishes on `Hⁿ`-null sets (2.36)
  exact ⟨μ, ξ, hμU, hμK, hμW, hξ, hξα, hTξ, fun hbd =>
    Submission.dimred_mbl_fnd_null_of_representation P n U T μ ξ hU hbd hμU hμK hμW hξ hξα hTξ⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
