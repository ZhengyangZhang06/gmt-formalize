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

/-- Integer median of an integer-valued function of bounded variation on the open unit cube
(the BV facts used in Simon 6.5.1, (26)–(33)): the Poincaré inequality, the bound on the median
and the boundary estimate.  The proof works with translations: for a smooth `ψ` supported in an
open `S` whose segments `S + [0, 1] h` stay in the cube, the field `(∫₀¹ ψ(· - τh) dτ) h` is
admissible, which bounds `∫ (u(x + h) - u(x)) ψ(x) dx`; a duality argument (smooth cut-offs and
inner regularity) turns this into an `L¹` bound for translation differences.  Integrating over
`h` gives the Poincaré inequality, the least integer `β` with `|{u ≤ β}| ≥ 1/2` is a median, and
difference quotients of `G` together with slab estimates near the faces give the boundary bound. -/
theorem Submission.dtc_bc_tc_cl_dfm_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
