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

/-- **Leibniz estimate for `f • g`** (used in the closure step to show that multiplication by a
smooth cutoff `ζ` preserves test-form convergence).  For `C^∞` maps `f : ℝᴾ → ℝ` and
`g : ℝᴾ → Λᵏ(ℝᴾ)`, `‖Dⁿ(f • g)(x)‖ ≤ ∑ᵢ C(n, i) ‖Dⁱf(x)‖ ‖Dⁿ⁻ⁱg(x)‖`.  This is Mathlib's
`norm_iteratedFDeriv_smul_le`, whose file `Mathlib.Analysis.Calculus.ContDiff.Bounds` is outside
the frozen imports, so it is proved by the same induction: for every continuous bilinear `B`,
`‖Dⁿₛ B(f, g)(x)‖ ≤ ‖B‖ ∑ᵢ C(n, i) ‖Dⁱₛf(x)‖ ‖Dⁿ⁻ⁱₛg(x)‖` over all normed spaces, by induction on
`n`, using `Dₛ B(f, g) = B.precompR (f, Dₛg) + B.precompL (Dₛf, g)` and Pascal's rule; then
take `B = lsmul` and `s = univ`. -/
theorem Submission.dmcbrcs_norm_iteratedFDeriv_smul_le : ∀ (P k : ℕ) (f : Euclid P → ℝ) (g : Euclid P → Covector (Euclid P) k), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g → ∀ (n : ℕ) (x : Euclid P), ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  -- Step 1: the bilinear estimate `(C_n)`, by induction on `n` over all normed spaces
  have aux : ∀ (n : ℕ) {Du Eu Fu Gu : Type} [NormedAddCommGroup Du] [NormedSpace ℝ Du]
      [NormedAddCommGroup Eu] [NormedSpace ℝ Eu] [NormedAddCommGroup Fu] [NormedSpace ℝ Fu]
      [NormedAddCommGroup Gu] [NormedSpace ℝ Gu]
      (B : Eu →L[ℝ] Fu →L[ℝ] Gu) {f : Du → Eu} {g : Du → Fu} {s : Set Du} {x : Du},
      ContDiffOn ℝ n f s → ContDiffOn ℝ n g s → UniqueDiffOn ℝ s → x ∈ s →
      ‖iteratedFDerivWithin ℝ n (fun y => B (f y) (g y)) s x‖ ≤
        ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f s x‖ *
          ‖iteratedFDerivWithin ℝ (n - i) g s x‖ := by
    intro n
    induction n with
    | zero =>
      -- Step 2: for `n = 0` this is the operator-norm bound `‖B u v‖ ≤ ‖B‖ ‖u‖ ‖v‖`
      intro Du Eu Fu Gu _ _ _ _ _ _ _ _ B f g s x _ _ _ _
      simp only [norm_iteratedFDerivWithin_zero, zero_add, Finset.range_one,
        Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
      apply B.le_opNorm₂
    | succ n IH =>
      intro Du Eu Fu Gu _ _ _ _ _ _ _ _ B f g s x hf hg hs hx
      have In : ((n : ℕ) : WithTop ℕ∞) + 1 ≤ ((n.succ : ℕ) : WithTop ℕ∞) := by
        simp only [Nat.cast_succ, le_refl]
      have hsum0 : ∀ (a : ℕ → ℝ), (∀ i, 0 ≤ a i) → 0 ≤ ∑ i ∈ Finset.range (n + 1), a i :=
        fun a ha => Finset.sum_nonneg fun i _ => ha i
      -- Step 5: `(C_n)` for `B.precompR` with `(f, Dₛg)`, `‖B.precompR‖ ≤ ‖B‖` and
      -- `‖Dⁿ⁻ⁱₛ(Dₛg)(x)‖ = ‖Dⁿ⁺¹⁻ⁱₛg(x)‖`
      have I1 :
          ‖iteratedFDerivWithin ℝ n (fun y : Du => B.precompR Du (f y) (fderivWithin ℝ g s y)) s x‖ ≤
            ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin ℝ i f s x‖ *
              ‖iteratedFDerivWithin ℝ (n + 1 - i) g s x‖ := by
        refine (IH (B.precompR Du) (hf.of_le (Nat.cast_le.2 (Nat.le_succ n)))
          (hg.fderivWithin hs In) hs hx).trans ?_
        refine (mul_le_mul_of_nonneg_right (B.norm_precompR_le Du)
          (hsum0 _ fun i => by positivity)).trans (le_of_eq ?_)
        congr 1
        apply Finset.sum_congr rfl fun i hi => ?_
        rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
          ← norm_iteratedFDerivWithin_fderivWithin hs hx]
      -- ... and for `B.precompL` with `(Dₛf, g)`
      have I2 :
          ‖iteratedFDerivWithin ℝ n (fun y : Du => B.precompL Du (fderivWithin ℝ f s y) (g y)) s x‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin ℝ (i + 1) f s x‖ *
            ‖iteratedFDerivWithin ℝ (n - i) g s x‖ := by
        refine (IH (B.precompL Du) (hf.fderivWithin hs In)
          (hg.of_le (Nat.cast_le.2 (Nat.le_succ n))) hs hx).trans ?_
        refine (mul_le_mul_of_nonneg_right (B.norm_precompL_le Du)
          (hsum0 _ fun i => by positivity)).trans (le_of_eq ?_)
        congr 1
        apply Finset.sum_congr rfl fun i _ => ?_
        rw [← norm_iteratedFDerivWithin_fderivWithin hs hx]
      -- Step 3: `Dₛ B(f, g) = B.precompR (f, Dₛg) + B.precompL (Dₛf, g)` on `s`
      have J : iteratedFDerivWithin ℝ n
          (fun y : Du => fderivWithin ℝ (fun y : Du => B (f y) (g y)) s y) s x =
            iteratedFDerivWithin ℝ n (fun y => B.precompR Du (f y)
              (fderivWithin ℝ g s y) + B.precompL Du (fderivWithin ℝ f s y) (g y)) s x := by
        apply iteratedFDerivWithin_congr (fun y hy => ?_) hx
        exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) y hy)
          (hg.differentiableOn (by positivity) y hy) (hs y hy)
      -- Step 4: `‖Dⁿ⁺¹ₛ B(f, g)(x)‖ = ‖Dⁿₛ(Dₛ B(f, g))(x)‖`, and `Dⁿₛ` of the sum of the two
      -- `Cⁿ` summands is the sum of their `Dⁿₛ`
      rw [← norm_iteratedFDerivWithin_fderivWithin hs hx, J]
      have A : ContDiffOn ℝ n (fun y => B.precompR Du (f y) (fderivWithin ℝ g s y)) s :=
        (B.precompR Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
          (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
      have A' : ContDiffOn ℝ n (fun y => B.precompL Du (fderivWithin ℝ f s y) (g y)) s :=
        (B.precompL Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
          (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
      rw [fun_iteratedFDerivWithin_add_apply (A.contDiffWithinAt hx) (A'.contDiffWithinAt hx) hs hx]
      -- Step 6: the triangle inequality, Step 5, and Pascal's rule
      apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq ?_))
      simp_rw [← mul_add, mul_assoc]
      congr 1
      exact (Finset.sum_choose_succ_mul
        (fun i j => ‖iteratedFDerivWithin ℝ i f s x‖ * ‖iteratedFDerivWithin ℝ j g s x‖) n).symm
  -- Step 7: specialize to `B = lsmul` (`‖lsmul‖ ≤ 1`) on `s = univ`
  intro P k f g hf hg n x
  have h := aux n (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Covector (Euclid P) k →L[ℝ] Covector (Euclid P) k)
    (f := f) (g := g) (s := univ) (x := x) (hf.contDiffOn.of_le (by exact_mod_cast le_top))
    (hg.contDiffOn.of_le (by exact_mod_cast le_top)) uniqueDiffOn_univ (mem_univ x)
  simp only [iteratedFDerivWithin_univ] at h
  refine h.trans (mul_le_of_le_one_left (by positivity) ContinuousLinearMap.opNorm_lsmul_le)

/-- **Multiplication by a cutoff is continuous on test forms** (the cutoff extension in the
localization of Simon Ch. 6, Remark 8.3(1), p. 176, chapter-06.txt lines 2311–2318): if `ζ` is
smooth with compact support in `U` and `ωⱼ → 0` in `𝒟ᵏ(ℝᴾ)`, then `ηⱼ = ζωⱼ → 0` in `𝒟ᵏ(U)`.
Every `spt ηⱼ` lies in the compact set `spt ζ ⊆ U`.  The derivatives of `ζ` are bounded; those of
`ωⱼ` vanish off the compact set of `ωⱼ → 0`, so they tend to `0` uniformly on `ℝᴾ`, and the
Leibniz bound `‖Dⁱ(ζωⱼ)‖ ≤ Σₗ C(i,l) ‖Dˡζ‖ ‖Dⁱ⁻ˡωⱼ‖` (`dmcbrcs_norm_iteratedFDeriv_smul_le`)
gives `Dⁱηⱼ → 0` uniformly on `spt ζ`. -/
theorem Submission.dmcbrcs_testFormOnConverges_smul : ∀ (P k : ℕ) (U : Set (Euclid P)) (ζ : Euclid P → ℝ) (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn U k), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → TestFormOnConverges ωs 0 → (∀ j x, (ηs j : DifferentialForm (Euclid P) k) x = ζ x • (ωs j : DifferentialForm (Euclid P) k) x) → TestFormOnConverges ηs 0 := by
  intro P k U ζ ωs ηs hζ hζc hζU hconv hη
  -- Step 1: `ωⱼ → 0` on the compact set `K'`, `ηⱼ = ζ • ωⱼ`, and `Dˡ 0 = 0`
  obtain ⟨K', -, -, hsupp, -, hunif⟩ := hconv
  have hηfun : ∀ j, (ηs j : DifferentialForm (Euclid P) k) =
      fun y => ζ y • (ωs j : DifferentialForm (Euclid P) k) y := fun j => funext (hη j)
  have hzero : ∀ (V : Set (Euclid P)) (l : ℕ) (x : Euclid P),
      iteratedFDeriv ℝ l (((0 : TestFormOn V k)) : DifferentialForm (Euclid P) k) x = 0 := by
    intro V l x
    change iteratedFDeriv ℝ l (fun _ => (0 : Covector (Euclid P) k)) x = 0
    rw [iteratedFDeriv_fun_zero]; rfl
  -- Step 2: every `spt ηⱼ` and `spt 0` lies in the compact set `spt ζ ⊆ U`
  refine ⟨tsupport ζ, hζc, hζU, fun j => ?_, ?_, fun i => ?_⟩
  · rw [hηfun j]
    exact tsupport_smul_subset_left _ _
  · change tsupport (fun _ => (0 : Covector (Euclid P) k)) ⊆ tsupport ζ
    rw [tsupport_fun_zero]; exact empty_subset _
  -- Step 3: `‖Dˡζ‖ ≤ B l`, as `Dˡζ` is continuous with compact support
  have hB : ∀ l : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ l ζ x‖ ≤ B := fun l =>
    (hζ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hζc.iteratedFDeriv l)
  choose B hB using hB
  -- Step 4: `Dˡωⱼ → 0` uniformly on `ℝᴾ`, as `Dˡωⱼ = 0` off `K'`
  have hsmall : ∀ l : ℕ, ∀ ε > 0, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ l (ωs j : DifferentialForm (Euclid P) k) x‖ < ε := by
    intro l ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hunif l) ε hε] with j hj x
    by_cases hx : x ∈ K'
    · have h := hj x hx
      rw [hzero, dist_zero_left] at h
      exact h
    · have hx' : x ∉ tsupport (iteratedFDeriv ℝ l (ωs j : DifferentialForm (Euclid P) k)) :=
        fun h => hx (hsupp j (tsupport_iteratedFDeriv_subset l h))
      rw [image_eq_zero_of_notMem_tsupport hx', norm_zero]
      exact hε
  -- Step 5: by Leibniz, `‖Dⁱηⱼ‖ ≤ Σₗ C(i,l) |B l| ‖Dⁱ⁻ˡωⱼ‖ < ε` for large `j`
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set S : ℝ := ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * |B l| + 1 with hS_def
  have hS : 0 < S := by positivity
  have hev : ∀ᶠ j in atTop, ∀ l ∈ Finset.range (i + 1), ∀ x,
      ‖iteratedFDeriv ℝ (i - l) (ωs j : DifferentialForm (Euclid P) k) x‖ < ε / S := by
    rw [Filter.eventually_all_finset]
    intro l _
    exact hsmall (i - l) (ε / S) (div_pos hε hS)
  filter_upwards [hev] with j hj x _
  rw [hzero, dist_zero_left, hηfun j]
  refine lt_of_le_of_lt
    (Submission.dmcbrcs_norm_iteratedFDeriv_smul_le P k ζ _ hζ (ωs j).property.1.1 i x) ?_
  calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l ζ x‖ *
        ‖iteratedFDeriv ℝ (i - l) (ωs j : DifferentialForm (Euclid P) k) x‖
      ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * |B l| * (ε / S) := by
        refine Finset.sum_le_sum fun l hl => ?_
        have h1 : ‖iteratedFDeriv ℝ l ζ x‖ ≤ |B l| := (hB l x).trans (le_abs_self _)
        have h2 := (hj l hl x).le
        have hc : (0 : ℝ) ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 (norm_nonneg _)
          (mul_nonneg hc (abs_nonneg _))
    _ = (∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * |B l|) * (ε / S) := by
        rw [Finset.sum_mul]
    _ < S * (ε / S) := by
        apply mul_lt_mul_of_pos_right _ (div_pos hε hS)
        rw [hS_def]; linarith
    _ = ε := by field_simp

/-- **Simon Ch. 6, Remark 8.3(1)** (extension of a current from `U` to `ℝᴾ` by a cutoff): for
`U ⊆ ℝᴾ` open and `K ⊆ U` compact, fix `ζ ∈ C^∞_c(U)`, `0 ≤ ζ ≤ 1`, with `ζ = 1` on an open
`N ⊇ K`, and put `(E X)(ω) = X(ζω)`.  Multiplication by `ζ` maps `𝒟ᵏ(ℝᴾ)` linearly and
sequentially continuously into `𝒟ᵏ(U)` (`Submission.dmcbrcs_testFormOnConverges_smul`) and keeps
`|ω| ≤ 1` (the Euclidean coefficient norm is absolutely homogeneous), so `E X ∈ 𝒟_{m+1}(ℝᴾ)`,
`E` preserves weak convergence, `M(E X) ≤ M(X)`, and `E X = X` on forms supported in `K`.  If
`X` kills every form supported off `K`, then `E X` vanishes on balls missing `K`, and
`∂(E X)(η) = X(ζ dη) = X(d(ζη)) = ∂X(ζη)` because `d(ζη) − ζ dη` vanishes on `N`.  An integer
multiplicity representation of `X` carried by `K` represents `E X` in `ℝᴾ`, as `ζ = 1` on its
carrier. -/
theorem Submission.dmcbrcs_cutoff_extension : ∀ (P m : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ K → E X (testFormOnInclusion (subset_univ U) (m + 1) ω) = X ω) ∧ (∀ (Xs : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)), WeaklyConvergesOn Xs X → WeaklyConvergesOn (fun j => E (Xs j)) (E X)) ∧ (∀ X : GeometricCurrentOn U (m + 1), (E X).mass ≤ X.mass) ∧ (∀ X : GeometricCurrentOn U (m + 1), (∀ ω : TestFormOn U (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → X ω = 0) → (E X).support ⊆ K ∧ (E X).boundary.mass ≤ X.boundary.mass) ∧ (∀ (X : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)), R.Represents X → R.carrier ⊆ K → IsIntegerMultiplicity (E X)) := by
  have hC := Submission.dmcbrcs_testFormOnConverges_smul
  intro P m U K hU hK hKU
  -- Step 1: a cutoff `ζ ∈ C^∞_c(U)`, `0 ≤ ζ ≤ 1`, with `ζ = 1` on the open `V₁ ⊇ K`
  obtain ⟨V₁, hV₁o, hKV₁, hV₁U, hV₁c⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₂, hV₂o, hV₁V₂, hV₂U, hV₂c⟩ := exists_open_between_and_isCompact_closure hV₁c hU hV₁U
  obtain ⟨ζ, hζs, hζr, hζsupp, hζone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₂o isClosed_closure hV₁V₂
  have htsζ : tsupport ζ = closure V₂ := by rw [tsupport, hζsupp]
  have hζc : HasCompactSupport ζ := by
    rw [HasCompactSupport, htsζ]; exact hV₂c
  have hζU : tsupport ζ ⊆ U := htsζ ▸ hV₂U
  have hζ1 : ∀ x ∈ V₁, ζ x = 1 := fun x hx => (hζone x).1 (subset_closure hx)
  have hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1 := fun x => hζr (mem_range_self x)
  -- Step 3: the Euclidean coefficient norm is absolutely homogeneous, so `|ζω| ≤ 1` if `|ω| ≤ 1`
  have hnorm : ∀ (k : ℕ) (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro k c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
          ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        = c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hadm : ∀ (k : ℕ) (ω : DifferentialForm (Euclid P) k), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) →
      ∀ x, covectorEuclideanNorm (ζ x • ω x) ≤ 1 := by
    intro k ω hω x
    rw [hnorm, abs_of_nonneg (hζ01 x).1]
    exact (mul_le_mul (hζ01 x).2 (hω x) (covectorEuclideanNorm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  -- Step 2: multiplication by `ζ` is a linear map `𝒟ᵏ(ℝᴾ) → 𝒟ᵏ(U)`
  have hmem : ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ∈ TestFormOn U k := by
    intro k ω
    have hω : IsTestForm (ω : DifferentialForm (Euclid P) k) ∧
        tsupport (ω : DifferentialForm (Euclid P) k) ⊆ univ := ω.property
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) k) := hω.1.1
    have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) k)) := hω.1.2
    have hsub : tsupport (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ⊆
        tsupport (ω : DifferentialForm (Euclid P) k) :=
      tsupport_smul_subset_right (fun x => ζ x) _
    have hsubζ : tsupport (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ⊆ tsupport ζ :=
      tsupport_smul_subset_left (fun x => ζ x) _
    have hcpt : IsCompact (tsupport fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) :=
      hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
    exact ⟨⟨hζs.smul hsmooth, hcpt⟩, hsubζ.trans hζU⟩
  let Mk : (k : ℕ) → TestFormOn (univ : Set (Euclid P)) k →ₗ[ℝ] TestFormOn U k := fun k =>
    { toFun := fun ω => ⟨fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x, hmem k ω⟩
      map_add' := fun ω η => by
        apply Subtype.ext; funext x
        change ζ x • ((ω : DifferentialForm (Euclid P) k) x + (η : DifferentialForm (Euclid P) k) x) =
          ζ x • (ω : DifferentialForm (Euclid P) k) x + ζ x • (η : DifferentialForm (Euclid P) k) x
        rw [smul_add]
      map_smul' := fun c ω => by
        apply Subtype.ext; funext x
        change ζ x • (c • (ω : DifferentialForm (Euclid P) k) x) =
          c • (ζ x • (ω : DifferentialForm (Euclid P) k) x)
        rw [smul_comm] }
  -- Step 5: `(E X)(ω) = X(ζω)`; step 4 (sibling `smul_continuity`) gives continuity
  let E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) :=
    fun X =>
      { toCurrent := X.toCurrent.comp (Mk (m + 1))
        continuous' := fun ωs hω => by
          have h1 := hC P (m + 1) U ζ ωs (fun j => Mk (m + 1) (ωs j)) hζs hζc hζU hω
            (fun j x => rfl)
          have h2 := X.continuous' _ h1
          have h3 : (fun j => X.toCurrent ((fun j => Mk (m + 1) (ωs j)) j)) =
              (fun j => (X.toCurrent.comp (Mk (m + 1))) (ωs j)) := rfl
          rw [h3] at h2
          exact h2 }
  have hE : ∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      E X ω = X (Mk (m + 1) ω) := fun _ _ => rfl
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) `ζω = ω` when `tsupport ω ⊆ K`
    intro X ω hω
    rw [hE]
    congr 1
    apply Subtype.ext; funext x
    change ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x = (ω : DifferentialForm (Euclid P) (m + 1)) x
    by_cases hx : x ∈ K
    · rw [hζ1 x (hKV₁ hx), one_smul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), smul_zero]
  · -- (ii) weak convergence: `ζω` is one fixed test form in `U`
    intro Xs X hX ω
    exact hX (Mk (m + 1) ω)
  · -- (iii) mass: admissible forms in `ℝᴾ` go to admissible forms in `U`
    intro X
    apply sSup_le
    rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
    exact X.le_massOn ⟨(Mk (m + 1) ω).property.2, hadm (m + 1) _ hω⟩
  · -- (iv) support and boundary mass
    intro X hvan
    constructor
    · -- `E X` vanishes on a ball around each `x ∉ K` that misses `K`
      intro x hx
      by_contra hxK
      obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hxK
      apply hx.2
      refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self (half_pos hε)⟩
      · exact (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
      · intro ω hω
        rw [hE]
        apply hvan
        rw [Set.disjoint_left]
        intro y hy hyK
        have hy' : y ∈ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) :=
          tsupport_smul_subset_right _ _ hy
        exact hεK (ball_subset_ball (half_le_self hε.le) (hω hy')) hyK
    · -- `d(ζη) − ζ dη` vanishes on `V₁ ⊇ K`, so `∂(E X)(η) = ∂X(ζη)`
      apply sSup_le
      rintro _ ⟨η, ⟨-, hη⟩, rfl⟩
      have hδ : X (exteriorDerivativeTestOn U m (Mk m η) -
          Mk (m + 1) (exteriorDerivativeTestOn univ m η)) = 0 := by
        apply hvan
        have hzero : ∀ y ∈ V₁, ((exteriorDerivativeTestOn U m (Mk m η) -
            Mk (m + 1) (exteriorDerivativeTestOn univ m η) : TestFormOn U (m + 1)) :
              DifferentialForm (Euclid P) (m + 1)) y = 0 := by
          intro y hy
          change extDeriv (fun x => ζ x • (η : DifferentialForm (Euclid P) m) x) y -
            ζ y • extDeriv (η : DifferentialForm (Euclid P) m) y = 0
          have hev : (fun x => ζ x • (η : DifferentialForm (Euclid P) m) x) =ᶠ[𝓝 y]
              (η : DifferentialForm (Euclid P) m) := by
            filter_upwards [hV₁o.mem_nhds hy] with z hz
            rw [hζ1 z hz, one_smul]
          rw [hev.extDeriv_eq, hζ1 y hy, one_smul, sub_self]
        have hts : tsupport ((exteriorDerivativeTestOn U m (Mk m η) -
            Mk (m + 1) (exteriorDerivativeTestOn univ m η) : TestFormOn U (m + 1)) :
              DifferentialForm (Euclid P) (m + 1)) ⊆ V₁ᶜ := by
          apply closure_minimal _ hV₁o.isClosed_compl
          intro y hy hyV
          exact hy (hzero y hyV)
        exact Set.disjoint_of_subset_left hts (Set.disjoint_compl_left_iff_subset.2 hKV₁)
      have heq : (E X).boundary η = X.boundary (Mk m η) := by
        rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hE]
        have hsub := X.toCurrent.map_sub (exteriorDerivativeTestOn U m (Mk m η))
          (Mk (m + 1) (exteriorDerivativeTestOn univ m η))
        change X.toCurrent (exteriorDerivativeTestOn U m (Mk m η) -
          Mk (m + 1) (exteriorDerivativeTestOn univ m η)) = 0 at hδ
        rw [hsub, sub_eq_zero] at hδ
        exact hδ.symm
      change ENNReal.ofReal ((E X).boundary η) ≤ X.boundary.mass
      rw [heq]
      exact X.boundary.le_massOn ⟨(Mk m η).property.2, hadm m _ hη⟩
  · -- (v) the representation of `X`, regarded in `ℝᴾ`, represents `E X` as `ζ = 1` on `K`
    intro X R hR hRK
    refine ⟨{ carrier := R.carrier
              mult := R.mult
              orient := R.orient
              measurableSet_carrier := R.measurableSet_carrier
              carrier_subset := subset_univ _
              rectifiable := R.rectifiable
              measurable_mult := R.measurable_mult
              mult_pos := R.mult_pos
              locallyIntegrable_mult := fun K' _ _ => ?_
              aestronglyMeasurable_orient := R.aestronglyMeasurable_orient
              orients := R.orients }, ?_⟩
    · refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) (lintegral_mono_set ?_)
      exact fun x hx => ⟨hx.1, hRK hx.1⟩
    · intro ω
      rw [hE, hR (Mk (m + 1) ω)]
      unfold IMRep.action
      apply setIntegral_congr_fun R.measurableSet_carrier
      intro x hx
      change (R.mult x : ℝ) * R.orient x (ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x) =
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x)
      rw [hζ1 x (hKV₁ (hRK hx)), one_smul]
/-- **Mass localization for a current vanishing away from a compact set** (Simon 7.2.4, proof,
step 4(a)).  Let `C ⊆ V` with `C` compact and `V` open, and let `X ∈ 𝒟ₖ(U)` kill every
`ω ∈ 𝒟ᵏ(U)` with `spt ω ∩ C = ∅`.  Then `M_G(X) ≤ M_V(X)` for every `G`.  Choose a smooth
`χ : ℝᴾ → [0, 1]` with `χ = 1` on an open `N ⊇ C` and `spt χ ⊆ V`.  For `ω` admissible
for `M_G`, `(1 − χ)ω` vanishes on `N`, so `X(ω) = X(χω)`, and `χω` is admissible for `M_V`
because `|χω| = χ|ω| ≤ 1`. -/
theorem Submission.lcmp_massOn_le_of_vanish_off_compact : ∀ (P k : ℕ) (U V C : Set (Euclid P)) (X : GeometricCurrentOn U k), IsCompact C → IsOpen V → C ⊆ V → (∀ ω : TestFormOn U k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) C → X ω = 0) → ∀ G : Set (Euclid P), X.massOn G ≤ X.massOn V := by
  intro P k U V C X hC hV hCV hvan G
  -- Step 4: `|cα| = |c| |α|` for the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
        ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
        c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        ring
      · simp
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  -- Step 1: if `C = ∅` then `X = 0`, so `M_G(X) = 0`
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · refine sSup_le ?_
    rintro r ⟨ω, -, rfl⟩
    show ENNReal.ofReal (X ω) ≤ X.massOn V
    rw [hvan ω (disjoint_empty _), ENNReal.ofReal_zero]
    exact zero_le
  -- Step 2: `C ⊆ V' = {dist(·, C) < δ/2}` with `closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hV'o : IsOpen (thickening (δ / 2) C) := isOpen_thickening
  -- Step 3: `χ = τ(2g/a)`, where `{g ≠ 0} = V'`, `a = min_C g > 0`, `τ` the smooth transition
  obtain ⟨g, hgsupp, hgsmooth, hgrange⟩ := hV'o.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hgnn : ∀ x, 0 ≤ g x := fun x => (hgrange ⟨x, rfl⟩).1
  have hgpos : ∀ x ∈ C, 0 < g x := by
    intro x hx
    have hxs : x ∈ support g := by
      rw [hgsupp]
      exact self_subset_thickening (half_pos hδ) C hx
    exact lt_of_le_of_ne (hgnn x) (Ne.symm hxs)
  obtain ⟨x₀, hx₀C, hx₀min⟩ := hC.exists_isMinOn hCne hgsmooth.continuous.continuousOn
  set a := g x₀
  have ha : 0 < a := hgpos x₀ hx₀C
  set χ : Euclid P → ℝ := fun x => Real.smoothTransition (2 * g x / a)
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hgsmooth).div_const a)
  -- `χ = 1` on the open set `N = {g > a/2} ⊇ C`
  set N : Set (Euclid P) := {x | a / 2 < g x}
  have hNo : IsOpen N := isOpen_lt continuous_const hgsmooth.continuous
  have hCN : C ⊆ N := fun x hx => by
    have h1 : a ≤ g x := hx₀min hx
    show a / 2 < g x
    linarith
  have hχN : ∀ x ∈ N, χ x = 1 := fun x hx => by
    apply Real.smoothTransition.one_of_one_le
    have hx' : a / 2 < g x := hx
    rw [le_div_iff₀ ha]
    linarith
  -- `χ = 0` where `g = 0`, so `spt χ ⊆ closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  have hχsupp : support χ ⊆ thickening (δ / 2) C := by
    intro x hx
    by_contra h
    rw [← hgsupp, mem_support, not_not] at h
    apply hx
    show Real.smoothTransition (2 * g x / a) = 0
    rw [h, mul_zero, zero_div]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  have hclχ : tsupport χ ⊆ cthickening (δ / 2) C :=
    (closure_mono hχsupp).trans (closure_thickening_subset_cthickening _ _)
  have htχ : tsupport χ ⊆ V :=
    hclχ.trans ((cthickening_mono (half_le_self hδ.le) C).trans hδV)
  -- Step 5: for `ω` admissible for `M_G`, `ω₁ = χω ∈ 𝒟ᵏ(U)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ X.massOn V
  have hωt : IsTestForm (ω : DifferentialForm (Euclid P) k) := ω.property.1
  obtain ⟨ω₁f, hω₁f⟩ : ∃ g : DifferentialForm (Euclid P) k,
      g = fun x => χ x • (ω : DifferentialForm (Euclid P) k) x := ⟨_, rfl⟩
  have hω₁smooth : IsSmoothForm ω₁f := by
    rw [hω₁f]
    exact hχsmooth.smul hωt.1
  have hω₁supp : tsupport ω₁f ⊆ tsupport (ω : DifferentialForm (Euclid P) k) := by
    rw [hω₁f]
    exact tsupport_smul_subset_right _ _
  have hω₁suppχ : tsupport ω₁f ⊆ tsupport χ := by
    rw [hω₁f]
    exact tsupport_smul_subset_left _ _
  have hω₁cpt : HasCompactSupport ω₁f :=
    IsCompact.of_isClosed_subset hωt.2 (isClosed_tsupport _) hω₁supp
  let ω₁ : TestFormOn U k := ⟨ω₁f, ⟨hω₁smooth, hω₁cpt⟩, hω₁supp.trans ω.property.2⟩
  -- Step 6: `ω₂ = ω − ω₁` vanishes on `N ⊇ C`, so `spt ω₂ ∩ C = ∅` and `X(ω₂) = 0`
  have hω₂van : X (ω - ω₁) = 0 := by
    apply hvan
    rw [Set.disjoint_left]
    intro x hx hxC
    have hzero : ∀ y ∈ N, ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y = 0 := by
      intro y hy
      have hco : ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y =
          (ω : DifferentialForm (Euclid P) k) y - ω₁f y := rfl
      rw [hco, hω₁f]
      beta_reduce
      rw [hχN y hy, one_smul, sub_self]
    have hxN : x ∈ N := hCN hxC
    have hnot : x ∉ tsupport ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hNo.mem_nhds hxN] with y hy
      exact hzero y hy
    exact hnot hx
  have hsplit : X ω = X ω₁ := by
    have : X (ω - ω₁) = X ω - X ω₁ := map_sub X.toCurrent ω ω₁
    linarith
  -- Step 5 (cont.): `spt ω₁ ⊆ spt χ ⊆ V` and `|ω₁(x)| = χ(x) |ω(x)| ≤ 1`
  have hadm : ω₁ ∈ massAdmissibleOn U k V := by
    refine ⟨hω₁suppχ.trans htχ, fun x => ?_⟩
    have hco : (ω₁ : DifferentialForm (Euclid P) k) x =
        χ x • (ω : DifferentialForm (Euclid P) k) x := by
      show ω₁f x = _
      rw [hω₁f]
    rw [hco, hsmul]
    have h0 : 0 ≤ χ x := Real.smoothTransition.nonneg _
    have h1 : χ x ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_of_nonneg h0]
    have h2 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
    have h3 := hω.2 x
    nlinarith
  -- Step 7: `ofReal X(ω) = ofReal X(ω₁) ≤ M_V(X)`; take the supremum over `ω`
  rw [hsplit]
  exact X.le_massOn hadm
/-- **Triangle inequality for local mass** (Simon 6.2.5).  If `|c| ≤ 1` and
`Z(ω) = X(ω) + c Y(ω)` for every `ω ∈ 𝒟ᵏ(U)` with `spt ω ⊆ G`, then
`M_G(Z) ≤ M_G(X) + M_G(Y)`.  For `ω` admissible for `M_G`, `−ω` is admissible too, so
`|Y(ω)| ≤ M_G(Y)`; since `c Y(ω) ≤ |Y(ω)|`, `Z(ω) ≤ X(ω) + |Y(ω)| ≤ M_G(X) + M_G(Y)`.  Taking the
supremum over admissible `ω` gives the claim (`c = ±1`: sum and difference). -/
theorem Submission.lcmp_massOn_le_add_of_eval_eq : ∀ (P k : ℕ) (U G : Set (Euclid P)) (X Y Z : GeometricCurrentOn U k) (c : ℝ), |c| ≤ 1 → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ G → Z ω = X ω + c * Y ω) → Z.massOn G ≤ X.massOn G + Y.massOn G := by
  intro P k U G X Y Z c hc hZ
  -- Step 4: `M_G(Z)` is a supremum, so bound each admissible value `ofReal (Z ω)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- Step 1: `−ω` is admissible (same support, same Euclidean coefficient norm)
  have hneg : -ω ∈ massAdmissibleOn U k G := by
    refine ⟨?_, fun x => ?_⟩
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) =
          -(ω : DifferentialForm (Euclid P) k) := rfl
      rw [hco, tsupport_neg]
      exact hω.1
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
          -((ω : DifferentialForm (Euclid P) k) x) := rfl
      rw [hco, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 2: `ofReal (X ω) ≤ M_G(X)` and, as `Y(−ω) = −Y(ω)`, `ofReal |Y(ω)| ≤ M_G(Y)`
  have hXle : ENNReal.ofReal (X ω) ≤ X.massOn G := X.le_massOn hω
  have hYle : ENNReal.ofReal (Y ω) ≤ Y.massOn G := Y.le_massOn hω
  have hYle' : ENNReal.ofReal (Y (-ω)) ≤ Y.massOn G := Y.le_massOn hneg
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hYle'
  have habs : ENNReal.ofReal |Y ω| ≤ Y.massOn G := by
    rcases abs_cases (Y ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hYle
    · rw [h]; exact hYle'
  -- Step 3: `c Y(ω) ≤ |c| |Y(ω)| ≤ |Y(ω)|`; `ofReal` is monotone and subadditive
  have hcy : c * Y ω ≤ |Y ω| :=
    calc c * Y ω ≤ |c * Y ω| := le_abs_self _
      _ = |c| * |Y ω| := abs_mul _ _
      _ ≤ 1 * |Y ω| := by gcongr
      _ = |Y ω| := one_mul _
  show ENNReal.ofReal (Z ω) ≤ X.massOn G + Y.massOn G
  calc ENNReal.ofReal (Z ω) = ENNReal.ofReal (X ω + c * Y ω) := by rw [hZ ω hω.1]
    _ ≤ ENNReal.ofReal (X ω + |Y ω|) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (X ω) + ENNReal.ofReal |Y ω| := ENNReal.ofReal_add_le
    _ ≤ X.massOn G + Y.massOn G := add_le_add hXle habs
/-- **Restriction of an integer multiplicity representation** (Simon Ch. 6, 3.1).  For
`R = (M, θ, ξ)` with weight `μ_R = θ Hⁿ⌞M`: (a) `μ_R ≪ Hⁿ⌞M`; (b) `ξ` is `μ_R`-a.e. strongly
measurable; (c) for Borel `E` and `R' = (M ∩ E, θ, ξ)`, `μ_{R'} = μ_R⌞E` and
`R'(ω) = ∫_E ⟨ω, ξ⟩ dμ_R` for every `n`-form `ω`. -/
theorem Submission.lcmp_imRep_measure_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), R.measure ≪ μHE[n].restrict R.carrier ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ (E : Set (Euclid P)) (R' : IMRep U n), MeasurableSet E → R'.carrier = R.carrier ∩ E → R'.mult = R.mult → R'.orient = R.orient → R'.measure = R.measure.restrict E ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x in E, R.orient x (ω x) ∂R.measure := by
  intro P n U R
  -- (a) a measure with a density is absolutely continuous; (b) so `ξ` is `μ_R`-measurable
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  refine ⟨hac, R.aestronglyMeasurable_orient.mono_ac hac, ?_⟩
  intro E R' hE hc hm ho
  -- (c), weights: `((Hⁿ⌞M).withDensity θ)⌞E = (Hⁿ⌞(E ∩ M)).withDensity θ = μ_{R'}`
  have hmeasEq : R'.measure = R.measure.restrict E := by
    unfold IMRep.measure
    rw [restrict_withDensity hE, Measure.restrict_restrict hE, hc, hm, inter_comm]
  refine ⟨hmeasEq, fun ω => ?_⟩
  -- (c), actions: `∫ h d(λ.withDensity θ) = ∫ θ h dλ` for the Borel density `θ : ℝᴾ → [0, ∞)`
  have hmult : (fun x => (R'.mult x : ℝ≥0∞)) = fun x => (((R'.mult x : NNReal)) : ℝ≥0∞) := by
    funext x
    simp
  have hmeas : Measurable fun x => ((R'.mult x : ℕ) : NNReal) :=
    (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R'.measurable_mult
  rw [← hmeasEq]
  unfold IMRep.action IMRep.measure
  rw [hmult, integral_withDensity_eq_integral_smul hmeas]
  congr 1
  funext x
  rw [ho, NNReal.smul_def, smul_eq_mul]
  norm_cast
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
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
/-- **Good radius** (Simon 7.2.4, choice of the slicing level; the factor-2 averaging of Ch. 2,
6.7(1)).  If `ρ < ρ'`, `μ(B̄_{ρ'}(y)) < ∞`, `∫ g dL¹ ≤ I` and `p` holds `L¹`-a.e., then some
`t ∈ (ρ, ρ')` has `p t`, `μ(∂B_t(y)) = 0` and `g t ≤ (2 / (ρ' - ρ)) I`: the levels failing `p` and
the (countably many) levels whose sphere charges the finite measure `μ⌞B̄_{ρ'}(y)` are `L¹`-null,
and by Markov's inequality the levels with `g t > (2 / (ρ' - ρ)) I` have `L¹`-measure at most
`(ρ' - ρ) / 2 < L¹((ρ, ρ'))`. -/
theorem Submission.dor_lmb_glc_good_radius : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (ρ ρ' : ℝ) (g : ℝ → ℝ≥0∞) (I : ℝ≥0∞) (p : ℝ → Prop), ρ < ρ' → μ (closedBall y ρ') ≠ ∞ → AEMeasurable g → ∫⁻ t, g t ≤ I → (∀ᵐ t, p t) → ∃ t : ℝ, ρ < t ∧ t < ρ' ∧ p t ∧ μ (sphere y t) = 0 ∧ g t ≤ ENNReal.ofReal (2 / (ρ' - ρ)) * I := by
  intro P μ y ρ ρ' g I p hρ hμ hg hI hp
  have hδ : 0 < ρ' - ρ := sub_pos.mpr hρ
  set c := ENNReal.ofReal (2 / (ρ' - ρ)) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcinv : c⁻¹ = ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rw [hc_def, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  -- `N₁`: the exceptional set of `p` is Lebesgue-null
  have hN₁ : volume {t : ℝ | ¬ p t} = 0 := ae_iff.mp hp
  -- `N₂`: only countably many spheres charge the finite measure `μ⌞B̄_{ρ'}(y)`
  have hfin : IsFiniteMeasure (μ.restrict (closedBall y ρ')) := isFiniteMeasure_restrict.mpr hμ
  have hcount : {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun s => isClosed_sphere.measurableSet)
      (fun s s' hss' => Set.disjoint_left.mpr fun x hx hx' =>
        hss' ((mem_sphere.mp hx).symm.trans (mem_sphere.mp hx')))
  have hN₂ : volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} = 0 :=
    hcount.measure_zero volume
  -- `N₃`: Markov's inequality gives `L¹(N₃) ≤ (ρ' - ρ) / 2`
  have hN₃ : volume {t : ℝ | c * I < g t} ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rcases eq_or_ne I 0 with h0 | h0
    · have hzero : ∫⁻ t, g t = 0 := le_antisymm (hI.trans h0.le) zero_le
      have hae : g =ᵐ[volume] 0 := (lintegral_eq_zero_iff' hg).mp hzero
      have hnull : volume {t : ℝ | c * I < g t} = 0 := by
        refine measure_mono_null (fun t ht => ?_) (ae_iff.mp hae)
        simp only [Set.mem_ofPred_eq, h0, mul_zero] at ht ⊢
        exact ht.ne'
      rw [hnull]
      exact zero_le
    rcases eq_or_ne I ∞ with htop | htop
    · have hempty : {t : ℝ | c * I < g t} = ∅ := by
        ext t
        simp [htop, ENNReal.mul_top hc0]
      rw [hempty, measure_empty]
      exact zero_le
    have hε0 : c * I ≠ 0 := mul_ne_zero hc0 h0
    have hεtop : c * I ≠ ∞ := ENNReal.mul_ne_top hctop htop
    calc volume {t : ℝ | c * I < g t} ≤ volume {t : ℝ | c * I ≤ g t} :=
          measure_mono fun t (ht : c * I < g t) => show c * I ≤ g t from ht.le
      _ ≤ (∫⁻ t, g t) / (c * I) := meas_ge_le_lintegral_div hg hε0 hεtop
      _ ≤ I / (c * I) := ENNReal.div_le_div_right hI _
      _ = c⁻¹ := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_assoc,
          ENNReal.inv_mul_cancel h0 htop, mul_one]
      _ = ENNReal.ofReal ((ρ' - ρ) / 2) := hcinv
  -- covering: if no good `t` existed, then `(ρ, ρ') ⊆ N₁ ∪ N₂ ∪ N₃`
  by_contra hcon
  have hcover : Ioo ρ ρ' ⊆ {t : ℝ | ¬ p t} ∪
      {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪ {t : ℝ | c * I < g t} := by
    intro t ht
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, nonpos_iff_eq_zero]
      at hnot
    obtain ⟨⟨hpt, hνt⟩, hgt⟩ := hnot
    have hμt : μ (sphere y t) = 0 := by
      rwa [Measure.restrict_apply isClosed_sphere.measurableSet, Set.inter_eq_left.mpr
        (sphere_subset_closedBall.trans (closedBall_subset_closedBall ht.2.le))] at hνt
    exact hcon ⟨t, ht.1, ht.2, hpt, hμt, hgt⟩
  have hle : ENNReal.ofReal (ρ' - ρ) ≤ ENNReal.ofReal ((ρ' - ρ) / 2) :=
    calc ENNReal.ofReal (ρ' - ρ) = volume (Ioo ρ ρ') := Real.volume_Ioo.symm
      _ ≤ volume ({t : ℝ | ¬ p t} ∪ {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪
          {t : ℝ | c * I < g t}) := measure_mono hcover
      _ ≤ volume {t : ℝ | ¬ p t} + volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} +
          volume {t : ℝ | c * I < g t} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
        rw [hN₁, hN₂, zero_add, zero_add]
        exact hN₃
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
