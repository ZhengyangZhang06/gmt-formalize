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

/-- **Simon Ch. 6, 3.6–3.9 and 2.29 for `n = 0`**: the Lipschitz push-forward of a finite-mass
`0`-dimensional integer multiplicity current.  `H⁰ = μHE[0]` is counting measure, so
`H⁰(M) ≤ μ_R(ℝᴺ) < ∞` makes the carrier `M` finite and `H⁰⌞M`-a.e. statements hold on all of `M`;
there each `ξ(x)` is `ε(x) ev` with `ε(x) = ±1`.  `Y(F)(ω) = ∑_{x ∈ M} θ(x) ε(x) ω(F(x))(∅)` is a
current, `R.action(F_j^# ω)` is the same finite sum with `F_j` in place of `F` (so it converges to
`Y(F)(ω)`), and `Y(F)` depends only on `F` on `M`.  Regrouping by the fibres of `F`,
`Y(F) = τ(M', |c|, sign(c) ev)` with `c(y) = ∑_{F(x) = y} θ(x) ε(x)` and `M' = {c ≠ 0}` finite
(a finite set has approximate tangent space `{0}` at each of its points). -/
theorem Submission.dor_lmb_fcd_imp_degree_zero : ∀ (N N' : ℕ) (R : IMRep (univ : Set (Euclid N)) 0), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) 0, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) 0, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') 0) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[0].restrict R.carrier), F x = F' x) → Y F = Y F' := by
  intro N N' R hR
  classical
  -- `μHE[0]` is the counting measure
  have hsing : ∀ {P : ℕ} (x : Euclid P), (μHE[0] : Measure (Euclid P)) {x} = 1 := by
    intro P x
    rw [Measure.euclideanHausdorffMeasure_zero]
    exact Measure.hausdorffMeasure_zero_singleton x
  -- the carrier is finite, since `H⁰(M) ≤ R.measure univ < ∞`
  have hfin : R.carrier.Finite := by
    by_contra hinf
    have hle : (μHE[0] : Measure (Euclid N)) R.carrier ≤ R.measure univ := by
      rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← setLIntegral_one]
      exact setLIntegral_mono' R.measurableSet_carrier fun x hx => by
        exact_mod_cast R.mult_pos x hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_le_ne_top hR hle)
    obtain ⟨t, hts, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf n
    have : ((t.card : ℕ) : ℝ≥0∞) ≤ (μHE[0] : Measure (Euclid N)) R.carrier := by
      calc ((t.card : ℕ) : ℝ≥0∞) = ∑ x ∈ t, (μHE[0] : Measure (Euclid N)) {x} := by
            simp
        _ = (μHE[0] : Measure (Euclid N)) t := sum_measure_singleton
        _ ≤ _ := measure_mono hts
    exact absurd hn (not_lt.mpr this)
  set S := hfin.toFinset
  have hS : (S : Set (Euclid N)) = R.carrier := hfin.coe_toFinset
  -- `H⁰⌞M`-a.e. statements hold at every point of `M`
  have hpt : ∀ {p : Euclid N → Prop},
      (∀ᵐ x ∂((μHE[0] : Measure (Euclid N)).restrict R.carrier), p x) → ∀ x ∈ R.carrier, p x := by
    intro p hp x hx
    by_contra hpx
    have h0 := ae_iff.mp hp
    have hsub : ({x} : Set (Euclid N)) ⊆ {y | ¬ p y} ∩ R.carrier := by
      rintro y rfl
      exact ⟨hpx, hx⟩
    have h1 : (μHE[0] : Measure (Euclid N)) {x} ≤
        ((μHE[0] : Measure (Euclid N)).restrict R.carrier) {y | ¬ p y} :=
      (measure_mono hsub).trans (Measure.le_restrict_apply _ _)
    rw [hsing, h0] at h1
    exact absurd h1 (by norm_num)
  -- the unit `0`-covector and the empty tuple; a `0`-covector is `α(∅)` times the unit
  let K₁ : ∀ {P : ℕ}, Covector (Euclid P) 0 := fun {P} =>
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ)
  let v₀ : ∀ {P : ℕ}, Fin 0 → Euclid P := fun {P} => fun i => i.elim0
  have hcov : ∀ {P : ℕ} (α : Covector (Euclid P) 0), α = α v₀ • K₁ := by
    intro P α
    ext v
    simp [K₁, Subsingleton.elim v v₀]
  have horient : ∀ x (α : Covector (Euclid N) 0), R.orient x α = α v₀ * R.orient x K₁ := by
    intro x α
    conv_lhs => rw [hcov α]
    rw [map_smul, smul_eq_mul]
  -- signs: on `M`, `ξ(x) = ε(x) · ev` with `ε(x) = ±1`
  have hsign : ∀ x ∈ R.carrier, R.orient x K₁ = 1 ∨ R.orient x K₁ = -1 := by
    intro x hx
    obtain ⟨Q, -, τ, -, -, hτ⟩ := hpt R.orients x hx
    rcases hτ with hτ | hτ
    · left; rw [hτ]; simp [K₁]
    · right; rw [hτ]; simp [K₁]
  let σ : Euclid N → ℤ := fun x => if R.orient x K₁ = 1 then 1 else -1
  have hσ : ∀ x ∈ R.carrier, R.orient x K₁ = (σ x : ℝ) := by
    intro x hx
    rcases hsign x hx with h | h
    · simp [σ, h]
    · simp [σ, h]
  let wZ : Euclid N → ℤ := fun x => (R.mult x : ℤ) * σ x
  -- `R.action β = ∑_{x ∈ M} θ(x) ε(x) β(x)(∅)`
  have haction : ∀ β : DifferentialForm (Euclid N) 0,
      R.action β = ∑ x ∈ S, (wZ x : ℝ) * β x v₀ := by
    intro β
    have hint : IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (β x)) (S : Set (Euclid N))
        (μHE[0] : Measure (Euclid N)) := by
      rw [← (S : Set (Euclid N)).biUnion_of_singleton, integrableOn_finite_biUnion S.finite_toSet]
      intro x _
      exact integrableOn_singleton (hx := by rw [hsing]; exact ENNReal.one_lt_top)
    rw [IMRep.action, ← hS, setIntegral_finset S hint]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxM : x ∈ R.carrier := hS ▸ hx
    rw [measureReal_def, hsing, ENNReal.toReal_one, one_smul, horient, hσ x hxM]
    simp only [wZ]
    push_cast
    ring
  -- the currents `Y(F)(ω) = ∑_{x ∈ M} θ(x) ε(x) ω(F(x))(∅)`
  let L : (Euclid N → Euclid N') → CurrentOn (univ : Set (Euclid N')) 0 := fun F =>
    { toFun := fun ω => ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀
      map_add' := fun ω η => by
        simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring }
  have hL : ∀ F ω, L F ω = ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀ :=
    fun F ω => rfl
  have hcont : ∀ F (ωs : ℕ → TestFormOn (univ : Set (Euclid N')) 0), TestFormOnConverges ωs 0 →
      Tendsto (fun j => L F (ωs j)) atTop (𝓝 0) := by
    intro F ωs hωs
    obtain ⟨K, -, -, hsupp, -, hconv⟩ := hωs
    have hpt0 : ∀ y,
        Tendsto (fun j => (ωs j : DifferentialForm (Euclid N') 0) y v₀) atTop (𝓝 0) := by
      intro y
      by_cases hy : y ∈ K
      · have hΦ : Continuous (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Euclid N')
            (Covector (Euclid N') 0) => g v₀ v₀) :=
          (continuous_eval_const v₀).comp (continuous_eval_const v₀)
        have h0 := (hΦ.tendsto _).comp ((hconv 0).tendsto_at hy)
        simpa [Function.comp_def, iteratedFDeriv_zero_apply] using h0
      · have hz : ∀ j, (ωs j : DifferentialForm (Euclid N') 0) y = 0 := fun j =>
          image_eq_zero_of_notMem_tsupport fun h => hy (hsupp j h)
        simp [hz]
    have := tendsto_finsetSum S fun x _ => (hpt0 (F x)).const_mul (wZ x : ℝ)
    simpa [hL] using this
  let Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) 0 := fun F =>
    ⟨L F, hcont F⟩
  have hY : ∀ F ω, Y F ω = ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀ :=
    fun F ω => rfl
  refine ⟨Y, fun F Λ hF => ⟨?_, ?_⟩, ?_⟩
  · -- integrality: regroup the finite sum by the fibres of `F`
    let c : Euclid N' → ℤ := fun y => ∑ x ∈ S.filter (fun x => F x = y), wZ x
    have hc_supp : ∀ y, c y ≠ 0 → y ∈ S.image F := by
      intro y hy
      by_contra hy'
      apply hy
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_filter] at hx
      exact absurd (Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩) hy'
    let T' : Finset (Euclid N') := (S.image F).filter (fun y => c y ≠ 0)
    have hT' : ∀ y, y ∈ T' ↔ c y ≠ 0 := by
      intro y
      simp only [T', Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hc_supp y h, h⟩⟩
    have hT'meas : MeasurableSet (T' : Set (Euclid N')) := T'.finite_toSet.measurableSet
    let ev : MultiVector N' 0 := ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ v₀
    let orient' : Euclid N' → MultiVector N' 0 := fun y => if c y < 0 then -ev else ev
    refine ⟨{ carrier := T'
              mult := fun y => (c y).natAbs
              orient := orient'
              measurableSet_carrier := hT'meas
              carrier_subset := subset_univ _
              rectifiable := ?_
              measurable_mult := ?_
              mult_pos := ?_
              locallyIntegrable_mult := ?_
              aestronglyMeasurable_orient := ?_
              orients := ?_ }, ?_⟩
    · -- a finite set is countably `0`-rectifiable
      obtain ⟨g, hg⟩ := Set.countable_iff_exists_subset_range.mp T'.countable_toSet
      refine ⟨∅, measure_empty, fun j _ => g j, fun j => ⟨0, LipschitzWith.const _⟩, ?_⟩
      intro y hy
      obtain ⟨j, rfl⟩ := hg hy
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, 0, rfl⟩)
    · -- measurability of the multiplicity
      refine measurable_to_countable' fun k => ?_
      by_cases hk : k = 0
      · have : (fun y => (c y).natAbs) ⁻¹' {k} = (T' : Set (Euclid N'))ᶜ := by
          ext y
          simp [hk, hT']
        rw [this]
        exact hT'meas.compl
      · refine (T'.finite_toSet.subset fun y hy => ?_).measurableSet
        have hy' : (c y).natAbs = k := hy
        rw [Finset.mem_coe, hT']
        intro h0
        rw [h0] at hy'
        exact hk hy'.symm
    · intro y hy
      exact Int.natAbs_pos.mpr ((hT' y).mp hy)
    · intro K _ _
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_set Set.inter_subset_left)
      rw [lintegral_finset]
      exact ENNReal.sum_ne_top.mpr fun y _ => by simp
    · refine (StronglyMeasurable.ite ?_ stronglyMeasurable_const
        stronglyMeasurable_const).aestronglyMeasurable
      exact (T'.finite_toSet.subset fun y hy => (hT' y).mpr (ne_of_lt hy)).measurableSet
    · refine ae_restrict_of_forall_mem hT'meas fun y hy => ⟨⊥, ⟨by simp, fun f => ?_⟩, ?_⟩
      · -- the approximate tangent space of a finite set is `{0}`
        obtain ⟨ρ, hρ⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Euclid N')
        have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ ∀ z ∈ T', z ≠ y → ρ < r⁻¹ * ‖z - y‖ := by
          refine eventually_mem_nhdsWithin.and ((Filter.eventually_all_finset T').2 fun z _ => ?_)
          by_cases hzy : z = y
          · exact Eventually.of_forall fun _ h => absurd hzy h
          · have hd : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
            exact ((tendsto_inv_nhdsGT_zero.atTop_mul_const hd).eventually_gt_atTop ρ).mono
              fun r hr _ => hr
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with r hr
        obtain ⟨hr0, hfar⟩ := hr
        symm
        rw [Submodule.bot_coe]
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (T'.finite_toSet.image _).measurableSet ?_ ?_
        · rintro _ rfl
          exact ⟨y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap]⟩
        · rintro _ ⟨⟨z, hz, rfl⟩, hz0⟩
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have hzy : z ≠ y := by
            rintro rfl
            exact hz0 (by simp [Poincare.SimonGMT.Chapter03.blowUpMap])
          have h1 := hρ hmem
          have h2 := hfar z hz hzy
          rw [mem_closedBall_zero_iff, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
            Real.norm_of_nonneg hr0.le] at h1
          linarith
      · -- `±ev` orients `⊥`
        refine ⟨v₀, ⟨fun i => i.elim0, by intro i; exact i.elim0⟩, by simp, ?_⟩
        by_cases hneg : c y < 0
        · right; intro α; simp [orient', hneg, ev]
        · left; intro α; simp [orient', hneg, ev]
    · -- `R'` represents `Y(F)`
      intro ω
      have hint : IntegrableOn
          (fun y => ((c y).natAbs : ℝ) * orient' y ((ω : DifferentialForm (Euclid N') 0) y))
          (T' : Set (Euclid N')) (μHE[0] : Measure (Euclid N')) := by
        rw [← (T' : Set (Euclid N')).biUnion_of_singleton,
          integrableOn_finite_biUnion T'.finite_toSet]
        intro y _
        exact integrableOn_singleton (hx := by rw [hsing]; exact ENNReal.one_lt_top)
      show ∑ x ∈ S, (wZ x : ℝ) * (ω : DifferentialForm (Euclid N') 0) (F x) v₀ =
        ∫ y in (T' : Set (Euclid N')),
          ((c y).natAbs : ℝ) * orient' y ((ω : DifferentialForm (Euclid N') 0) y)
            ∂(μHE[0] : Measure (Euclid N'))
      rw [setIntegral_finset T' hint]
      have hterm : ∀ y ∈ T', (μHE[0] : Measure (Euclid N')).real {y} •
          (((c y).natAbs : ℝ) * orient' y ((ω : DifferentialForm (Euclid N') 0) y)) =
          (c y : ℝ) * (ω : DifferentialForm (Euclid N') 0) y v₀ := by
        intro y _
        rw [measureReal_def, hsing, ENNReal.toReal_one, one_smul, Nat.cast_natAbs, Int.cast_abs]
        by_cases hneg : c y < 0
        · have habs : |(c y : ℝ)| = -(c y : ℝ) := abs_of_neg (by exact_mod_cast hneg)
          simp only [orient', ite_eq_left hneg, ev, habs, neg_apply,
            ContinuousAlternatingMap.apply_apply]
          ring
        · have habs : |(c y : ℝ)| = (c y : ℝ) := abs_of_nonneg (by exact_mod_cast not_lt.mp hneg)
          simp only [orient', ite_eq_right hneg, ev, habs, ContinuousAlternatingMap.apply_apply]
      rw [Finset.sum_congr rfl hterm]
      show _ = ∑ y ∈ (S.image F).filter (fun y => c y ≠ 0),
        (c y : ℝ) * (ω : DifferentialForm (Euclid N') 0) y v₀
      rw [Finset.sum_filter_of_ne]
      · simp only [c, Int.cast_sum, Finset.sum_mul]
        rw [← Finset.sum_fiberwise_of_maps_to (g := F) (t := S.image F)
          fun x hx => Finset.mem_image_of_mem F hx]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
        rw [(Finset.mem_filter.mp hx).2]
      · intro y _ h h0
        apply h
        rw [h0, Int.cast_zero, zero_mul]
  · -- `R.action(F_j^# ω) → Y(F)(ω)`
    intro Fs _ _ hFs ω
    simp only [haction, hY]
    refine tendsto_finsetSum S fun x _ => Tendsto.const_mul _ ?_
    have hω : Continuous (ω : DifferentialForm (Euclid N') 0) := ContDiff.continuous ω.property.1.1
    have h1 := (((continuous_eval_const v₀).comp hω).tendsto (F x)).comp (hFs.tendsto_at x)
    refine h1.congr fun j => ?_
    simp only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  · -- locality
    intro F F' Λ _ _ hFF'
    have hEq : ∀ x ∈ R.carrier, F x = F' x := hpt hFF'
    ext ω
    simp only [hY]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hEq x (hS ▸ hx)]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
