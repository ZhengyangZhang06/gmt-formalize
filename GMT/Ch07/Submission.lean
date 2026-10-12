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

/-- **Simon A.4** (proof of (1), the radii `λₖ ↓ 0`): if every `δ > 0` admits some `ρ ∈ (0, δ)`
with `Q ρ`, then there are `ρₖ ∈ (0, δ₀)` with `Q ρₖ`, strictly decreasing to `0`.  Choose
`g(δ) ∈ (0, δ)` with `Q (g δ)` for each `δ > 0` and set `ρ₀ = g(δ₀)`,
`ρₖ₊₁ = g(min ρₖ (1/(k+1)))`; then `0 < ρₖ₊₁ < min ρₖ (1/(k+1))`. -/
theorem Submission.adr_exists_strictAnti_radii : ∀ (Q : ℝ → Prop) (δ₀ : ℝ), 0 < δ₀ → (∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q ρ) → ∃ ρs : ℕ → ℝ, (∀ k, 0 < ρs k) ∧ (∀ k, ρs k < δ₀) ∧ StrictAnti ρs ∧ Tendsto ρs atTop (𝓝 0) ∧ ∀ k, Q (ρs k) := by
  intro Q δ₀ hδ₀ hQ
  -- `g δ ∈ (0, δ)` with `Q (g δ)` for every `δ > 0`
  choose! g hg0 hgδ hgQ using hQ
  -- `ρ₀ = g δ₀`, `ρₖ₊₁ = g (min ρₖ (1/(k+1)))`
  let ρs : ℕ → ℝ := fun k =>
    Nat.rec (motive := fun _ => ℝ) (g δ₀) (fun k ρ => g (min ρ (1 / ((k : ℝ) + 1)))) k
  have hsucc : ∀ k, ρs (k + 1) = g (min (ρs k) (1 / ((k : ℝ) + 1))) := fun _ => rfl
  have hpos : ∀ k, 0 < ρs k := by
    intro k
    induction k with
    | zero => exact hg0 δ₀ hδ₀
    | succ k ih =>
      rw [hsucc]
      exact hg0 _ (lt_min ih Nat.one_div_pos_of_nat)
  have hmin : ∀ k, 0 < min (ρs k) (1 / ((k : ℝ) + 1)) := fun k =>
    lt_min (hpos k) Nat.one_div_pos_of_nat
  have hlt : ∀ k, ρs (k + 1) < min (ρs k) (1 / ((k : ℝ) + 1)) := fun k => by
    rw [hsucc]
    exact hgδ _ (hmin k)
  have hanti : StrictAnti ρs :=
    strictAnti_nat_of_succ_lt fun k => (hlt k).trans_le (min_le_left _ _)
  refine ⟨ρs, hpos, fun k => (hanti.antitone k.zero_le).trans_lt (hgδ δ₀ hδ₀), hanti, ?_, ?_⟩
  · -- squeeze `0 < ρₖ₊₁ < 1/(k+1)`
    refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (hpos (k + 1)).le)
      fun k => ((hlt k).trans_le (min_le_right _ _)).le)
  · intro k
    cases k with
    | zero => exact hgQ δ₀ hδ₀
    | succ k =>
      rw [hsucc]
      exact hgQ _ (hmin k)
/-- **An `H^ℓ`-null set has open covers of arbitrarily small `ℓ`-dimensional cost**: the open
balls covering `sing ψ` with `∑ⱼ ω_ℓ ρⱼ^ℓ < ε` in the proof of Simon A.4 (chapter-A.txt
lines 88–97), with thickenings in place of balls.  The scale-`1` term of `hausdorffMeasure_apply`
gives a cover `E ⊆ ⋃ₙ tₙ` with `diam tₙ ≤ 1` and `∑ₙ c(tₙ) < ε / 2`, where `c(t) = (diam t)^ℓ`
for `t ≠ ∅` and `c(∅) = 0`.  With slack `δₙ > 0`, `∑ₙ δₙ < ε / 2`, each `tₙ` is replaced by its
open `rₙ`-thickening, `rₙ > 0` so small that `(diam tₙ + 2rₙ)^ℓ < (diam tₙ)^ℓ + δₙ`. -/
theorem Submission.adr_null_open_cover : ∀ (P : ℕ) (ℓ : ℝ) (E : Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → μH[ℓ] E = 0 → 0 < ε → ∃ U : ℕ → Set (Euclid P), (∀ j, IsOpen (U j)) ∧ E ⊆ ⋃ j, U j ∧ ∑' j, Metric.ediam (U j) ^ ℓ < ε := by
  intro P ℓ E ε hℓ hE hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- the scale-`1` term of the formula for `μH[ℓ] E = 0` gives a cheap cover `t`
  obtain ⟨t, hEt, ht1, ht⟩ : ∃ t : ℕ → Set (Euclid P), E ⊆ ⋃ n, t n ∧
      (∀ n, ediam (t n) ≤ 1) ∧ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ < ε / 2 := by
    have h1 : (⨅ (t : ℕ → Set (Euclid P)) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ 1),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) < ε / 2 := by
      refine lt_of_le_of_lt ?_ hε2
      rw [← hE, Measure.hausdorffMeasure_apply]
      exact le_iSup₂_of_le (1 : ℝ≥0∞) one_pos le_rfl
    simpa only [iInf_lt_iff, exists_prop] using h1
  -- slack `δₙ > 0` with `∑ₙ δₙ < ε / 2`
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε2.ne' ℕ
  -- radii `rₙ > 0` with `(diam tₙ + 2rₙ)^ℓ < (diam tₙ)^ℓ + δₙ`, by continuity at `0`
  have hr : ∀ n, ∃ r : NNReal, 0 < r ∧
      (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ < ediam (t n) ^ ℓ + δ n := by
    intro n
    have hcont : Continuous fun r : NNReal => (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ := by
      fun_prop (disch := norm_num)
    have hfin : ediam (t n) ^ ℓ ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hℓ.le ((ht1 n).trans_lt ENNReal.one_lt_top).ne
    have hev : ∀ᶠ r : NNReal in 𝓝 0,
        (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ < ediam (t n) ^ ℓ + δ n :=
      (isOpen_lt hcont continuous_const).mem_nhds
        (by simpa using ENNReal.lt_add_right hfin (hδ n).ne')
    exact (Filter.Eventually.and self_mem_nhdsWithin
      (hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ r : NNReal in 𝓝[>] 0, 0 < r ∧ _).exists
  choose r hr0 hr using hr
  -- `Uₙ` is the open `rₙ`-thickening of `tₙ`; `diam Uₙ ≤ diam tₙ + 2rₙ`
  refine ⟨fun n => thickening (r n) (t n), fun n => isOpen_thickening, ?_, ?_⟩
  · exact hEt.trans (iUnion_mono fun n => self_subset_thickening (NNReal.coe_pos.mpr (hr0 n)) _)
  calc ∑' n, ediam (thickening (r n) (t n)) ^ ℓ
      ≤ ∑' n, ((⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) + δ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rcases (t n).eq_empty_or_nonempty with h | h
        · simp [h, ENNReal.zero_rpow_of_pos hℓ]
        · rw [iSup_pos h]
          exact (ENNReal.rpow_le_rpow (ediam_thickening_le (r n)) hℓ.le).trans (hr n).le
    _ = ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) + ∑' n, δ n := ENNReal.tsum_add
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add ht hδsum
    _ = ε := ENNReal.add_halves ε

/-- **A small-cost cover of a null closed set eventually covers nearby sets in `B_{1/2}(0)`**:
Simon's "`K ≡ B̄₁(0) \ ∪ⱼ B_{ρⱼ}(xⱼ)` is a compact set with positive distance from `sing ψ`.
Hence by assumption A.3(3) we have `sing φ_{x,λₖ'} ∩ B₁(0) ⊆ ∪ⱼ B_{ρⱼ}(xⱼ)` for all sufficiently
large `k`" in the proof of A.4 (chapter-A.txt lines 97–101), for `S ∩ B̄_{1/2}(0)` only.
`adr_null_open_cover` covers the null set `E = S ∩ B̄_{1/2}(0)` by open `Uⱼ`.  The compact
`K = B̄_{1/2}(0) \ ⋃ⱼ Uⱼ` misses the closed `S`, so some thickening `thickening η K` misses `S`;
the hypothesis at this `η` puts `B_{1/2}(0) ∩ Tₖ` (`k ≥ k₀`) within `η` of `S`, hence off `K`. -/
theorem Submission.adr_eventually_subset_small_cover : ∀ (P : ℕ) (ℓ : ℝ) (S : Set (Euclid P)) (Ts : ℕ → Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → IsClosed S → μH[ℓ] (S ∩ ball (0 : Euclid P) 1) = 0 → 0 < ε → (∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ Ts k ⊆ {x | ∃ z ∈ S, dist x z < η}) → ∃ (U : ℕ → Set (Euclid P)) (k₀ : ℕ), ∑' j, Metric.ediam (U j) ^ ℓ < ε ∧ ∀ k ≥ k₀, ball (0 : Euclid P) (1 / 2) ∩ Ts k ⊆ ⋃ j, U j := by
  intro P ℓ S Ts ε hℓ hS hS1 hε hT
  -- `E = S ∩ B̄_{1/2}(0) ⊆ S ∩ B₁(0)` is `μH[ℓ]`-null, so it has an open cover of cost `< ε`
  have hE : μH[ℓ] (S ∩ closedBall (0 : Euclid P) (1 / 2)) = 0 :=
    measure_mono_null (inter_subset_inter_right S (closedBall_subset_ball (by norm_num))) hS1
  obtain ⟨U, hUo, hEU, hU⟩ := Submission.adr_null_open_cover P ℓ _ ε hℓ hE hε
  -- `K = B̄_{1/2}(0) \ ⋃ⱼ Uⱼ` is compact and misses the closed set `S`
  have hK : IsCompact (closedBall (0 : Euclid P) (1 / 2) \ ⋃ j, U j) :=
    (isCompact_closedBall _ _).diff (isOpen_iUnion hUo)
  have hKS : closedBall (0 : Euclid P) (1 / 2) \ ⋃ j, U j ⊆ Sᶜ := fun w hw hwS =>
    hw.2 (hEU ⟨hwS, hw.1⟩)
  -- a uniform gap: `thickening η K` misses `S`
  obtain ⟨η, hη, hηK⟩ := hK.exists_thickening_subset_open hS.isOpen_compl hKS
  obtain ⟨k₀, hk₀⟩ := hT η hη
  refine ⟨U, k₀, hU, fun k hk w hw => ?_⟩
  by_contra hwU
  obtain ⟨z, hzS, hwz⟩ := hk₀ k hk ⟨ball_subset_ball (by norm_num) hw.1, hw.2⟩
  exact hηK (mem_thickening_iff.mpr ⟨w, ⟨ball_subset_closedBall hw.1, hwU⟩, by rwa [dist_comm]⟩)
    hzS
/-- **Simon A.4** (proof of (1), the rescaling step, with blow-up scale `λ = 2ρ`): if every cover
`{Cⱼ}` of `A ∩ B_ρ(x)` has `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` and the `Uⱼ` cover every `z` with `|z| < 1/2`
and `x + 2ρz ∈ A`, then `Σⱼ (diam Uⱼ)^ℓ ≥ 2^{−ℓ}/8`.  The sets `Cⱼ = x + 2ρ·Uⱼ` cover
`A ∩ B_ρ(x)` and have `diam Cⱼ = 2ρ diam Uⱼ`, so a smaller sum would give
`ρ^ℓ ≤ 2·2^ℓρ^ℓ Σⱼ (diam Uⱼ)^ℓ < ρ^ℓ/4`. -/
theorem Submission.adr_rescaled_content_lower_bound : ∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)) (x : Euclid P) (ρ : ℝ) (U : ℕ → Set (Euclid P)), 0 < ℓ → 0 < ρ → (∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ) → (∀ z : Euclid P, x + (2 * ρ) • z ∈ A → ‖z‖ < 1 / 2 → z ∈ ⋃ j, U j) → (2 : ℝ≥0∞) ^ (-ℓ) / 8 ≤ ∑' j, Metric.ediam (U j) ^ ℓ := by
  intro P ℓ A x ρ U hℓ hρ hD hU
  have hlam : 0 < 2 * ρ := by positivity
  -- `Cⱼ = g(Uⱼ)` with `g(z) = x + 2ρz` cover `A ∩ B_ρ(x)`: `w = g(z)` for `z = (2ρ)⁻¹(w − x)`,
  -- and `|z| = |w − x|/(2ρ) < 1/2`
  have hcover : A ∩ ball x ρ ⊆ ⋃ j, (fun z => x + (2 * ρ) • z) '' U j := by
    rintro w ⟨hwA, hwB⟩
    have hgz : x + (2 * ρ) • ((2 * ρ)⁻¹ • (w - x)) = w := by
      rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
    have hzn : ‖(2 * ρ)⁻¹ • (w - x)‖ < 1 / 2 := by
      rw [mem_ball, dist_eq_norm] at hwB
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hlam.le, inv_mul_lt_iff₀ hlam]
      linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hU _ (by rw [hgz]; exact hwA) hzn)
    exact mem_iUnion.mpr ⟨j, _, hj, hgz⟩
  -- `diam Cⱼ = 2ρ diam Uⱼ`: `g` is the dilation by `2ρ` followed by a translation
  have hdiam : ∀ j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) =
      ENNReal.ofReal (2 * ρ) * Metric.ediam (U j) := by
    intro j
    rw [show (fun z => x + (2 * ρ) • z) '' U j = (fun y => x + y) '' ((fun z => (2 * ρ) • z) '' U j)
        from (Set.image_image (fun y => x + y) (fun z => (2 * ρ) • z) (U j)).symm,
      (isometry_add_left x).ediam_image, Set.image_smul, ediam_smul₀, ENNReal.smul_def, smul_eq_mul,
      ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hlam.le]
  -- hence `Σⱼ (diam Cⱼ)^ℓ = 2^ℓ ρ^ℓ Σⱼ (diam Uⱼ)^ℓ`
  have hsum : ∑' j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) ^ ℓ =
      2 ^ ℓ * ENNReal.ofReal ρ ^ ℓ * ∑' j, Metric.ediam (U j) ^ ℓ := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hdiam j, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ENNReal.mul_rpow_of_nonneg _ _ hℓ.le, ENNReal.mul_rpow_of_nonneg _ _ hℓ.le]
  have key :
      ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) ^ ℓ :=
    hD _ hcover
  rw [hsum] at key
  -- if `σ < 2^{−ℓ}/8` then `r ≤ 2·2^ℓ r σ < 2·2^ℓ r 2^{−ℓ}/8 = r/4 ≤ r`, where `r = ρ^ℓ ∈ (0, ∞)`
  rw [ENNReal.rpow_neg]
  refine not_lt.mp fun hlt => ?_
  set σ := ∑' j, Metric.ediam (U j) ^ ℓ
  set r := ENNReal.ofReal ρ ^ ℓ
  set t := (2 : ℝ≥0∞) ^ ℓ
  have hr0 : r ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hρ) ENNReal.ofReal_ne_top).ne'
  have hrT : r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hℓ.le ENNReal.ofReal_ne_top
  have ht0 : t ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have htT : t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hℓ.le (by norm_num)
  have hcalc : 2 * t * r * (t⁻¹ / 8) = r / 4 := by
    have h8 : (8 : ℝ≥0∞)⁻¹ = 2⁻¹ * 4⁻¹ := by
      rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
      norm_num
    rw [div_eq_mul_inv, div_eq_mul_inv, h8]
    calc 2 * t * r * (t⁻¹ * (2⁻¹ * 4⁻¹))
        = (2 * 2⁻¹) * (t * t⁻¹) * (r * 4⁻¹) := by ring
      _ = r * 4⁻¹ := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), ENNReal.mul_inv_cancel ht0 htT,
          one_mul, one_mul]
  have hfac0 : 2 * t * r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ht0) hr0
  have hfacT : 2 * t * r ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) htT) hrT
  have hrr : r < r :=
    calc r ≤ 2 * (t * r * σ) := key
      _ = 2 * t * r * σ := by ring
      _ < 2 * t * r * (t⁻¹ / 8) := ENNReal.mul_lt_mul_right hfac0 hfacT hlt
      _ = r / 4 := hcalc
      _ ≤ r := ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by norm_num))
  exact lt_irrefl r hrr

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
