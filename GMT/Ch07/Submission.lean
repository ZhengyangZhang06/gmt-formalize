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

/-- Transfer of null sets to almost every slice (Simon 7.4.3, slicing step; co-area formula of
Ch. 2, 6.6 and slices of Ch. 6, 4.3): if the slice measures `ν_t` satisfy the co-area identity
`∫_ℝ ∫ φ dν_t dt = ∫ w φ dμ` for every Borel `φ ≥ 0`, then a property holding `μ`-a.e. holds
`ν_t`-a.e. for a.e. `t`.  With `Z ⊇ {¬p}` a Borel `μ`-null hull and `φ = 1_Z`, the right side
vanishes, so `ν_t(Z) = ∫ 1_Z dν_t = 0` for a.e. `t`. -/
theorem Submission.dor_lmbsf_si_coarea_ae_transfer : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (p : Euclid P → Prop), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → (∀ᵐ x ∂μ, p x) → ∀ᵐ t, ∀ᵐ x ∂(ν t), p x := by
  intro P μ ν w p hco hp
  -- a Borel `μ`-null hull `Z` of `{x | ¬p x}`
  set Z := toMeasurable μ {x | ¬p x} with hZ
  have hZm : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hμZ : μ Z = 0 := by rw [hZ, measure_toMeasurable]; exact ae_iff.mp hp
  -- co-area identity for `φ = 1_Z`: `∫_ℝ ν_t(Z) dt = ∫ w 1_Z dμ = 0`
  obtain ⟨hae, heq⟩ := hco (Z.indicator 1) (measurable_one.indicator hZm)
  have hzero : ∫⁻ x, w x * Z.indicator 1 x ∂μ = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμZ] with x hx
    simp [indicator_of_notMem hx]
  rw [hzero, lintegral_eq_zero_iff' hae] at heq
  -- for a.e. `t`, `ν_t(Z) = 0`, so `ν_t`-a.e. `x` lies outside `Z ⊇ {¬p}`
  filter_upwards [heq] with t ht
  have hνZ : ν t Z = 0 := by
    rw [← lintegral_indicator_one hZm]; exact ht
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνZ] with x hx
  by_contra hpx
  exact hx (subset_toMeasurable μ {x | ¬p x} hpx)

/-- Orthonormal frame of `Q` adapted to a unit vector `ν ∈ Q` (Simon Ch. 6, 4.3, used for the
orientation of the slices in 7.4): if `dim Q = n + 1`, then `Q' = Q ∩ ν^⊥` has an orthonormal
basis `σ = (σ₁, …, σₙ)`, so that `(ν, σ₁, …, σₙ)` is an orthonormal basis of `Q`.  The dimension
count is `dim (ℝν) + dim (ν^⊥ ∩ Q) = dim Q`. -/
theorem Submission.dor_lmbsf_io_adapted_frame : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ν : Euclid P), Module.finrank ℝ Q = n + 1 → ν ∈ Q → ‖ν‖ = 1 → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Q ⊓ (ℝ ∙ ν)ᗮ ∧ Orthonormal ℝ (Fin.cons ν σ : Fin (n + 1) → Euclid P) ∧ (∀ i, σ i ∈ Q) ∧ ∀ i, inner ℝ ν (σ i) = 0 := by
  intro P n Q ν hQ hνQ hν
  set Q' : Submodule ℝ (Euclid P) := Q ⊓ (ℝ ∙ ν)ᗮ
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, norm_zero] at hν; exact zero_ne_one hν
  have hle : (ℝ ∙ ν) ≤ Q := (Submodule.span_singleton_le_iff_mem ν Q).2 hνQ
  -- `dim Q' = n`
  have hdim : Module.finrank ℝ Q' = n := by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal hle
    rw [finrank_span_singleton hν0, hQ] at h1
    have : Q' = (ℝ ∙ ν)ᗮ ⊓ Q := inf_comm _ _
    rw [this]; omega
  -- `σ` is an orthonormal basis `b` of `Q'`, viewed in `ℝᴾ`
  let b : OrthonormalBasis (Fin n) ℝ Q' := (stdOrthonormalBasis ℝ Q').reindex (finCongr hdim)
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  have hσ : Orthonormal ℝ σ := b.orthonormal.comp_linearIsometry Q'.subtypeₗᵢ
  have hσmem : ∀ i, σ i ∈ Q' := fun i => (b i).2
  have hσspan : Submodule.span ℝ (Set.range σ) = Q' := by
    have hrange : Set.range σ = Q'.subtype '' Set.range b := by
      ext x; simp [σ]
    have htop : Submodule.span ℝ (Set.range b) = ⊤ := by simpa using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]
  have hσQ : ∀ i, σ i ∈ Q := fun i => (hσmem i).1
  have hνσ : ∀ i, inner ℝ ν (σ i) = 0 := fun i =>
    (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hσmem i).2
  refine ⟨σ, hσ, hσspan, ?_, hσQ, hνσ⟩
  -- `Fin.cons ν σ` is orthonormal: split both indices into `0` and successors
  rw [orthonormal_iff_ite] at hσ ⊢
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [hν]
  · simp [hνσ j', (Fin.succ_ne_zero j').symm]
  · simp [real_inner_comm, hνσ i', Fin.succ_ne_zero i']
  · simp [hσ i' j']
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

/-- Sign lemma for unit orientations (Simon 6.1.1; used for the slice orientation
`ξ ⌞ ∇^M f/|∇^M f|` of 6.4.3 in the slicing step of the proof of 7.4.3): if
`ζ = ±τ₁ ∧ ⋯ ∧ τₘ` is a unit orientation of `Q` and `ρ` is an orthonormal `m`-frame in `Q`, then
`ζ = ρ₁ ∧ ⋯ ∧ ρₘ` or `ζ = -ρ₁ ∧ ⋯ ∧ ρₘ`.  The change of frame `M = (⟨τᵢ, ρⱼ⟩)` satisfies
`Mᵀ M = I`, so `det M = ±1`, and `β(ρ) = det M · β(τ)` for every `m`-covector `β`. -/
theorem Submission.dor_lmbsf_io_orientation_frame_sign : ∀ (P m : ℕ) (ζ : MultiVector P m) (Q : Submodule ℝ (Euclid P)) (ρ : Fin m → Euclid P), IsUnitOrientationOf ζ Q → Orthonormal ℝ ρ → (∀ j, ρ j ∈ Q) → (∀ β : Covector (Euclid P) m, ζ β = β ρ) ∨ ∀ β : Covector (Euclid P) m, ζ β = -β ρ := by
  intro P m ζ Q ρ hζ hρ hρQ
  obtain ⟨τ, hτ, hspan, hsign⟩ := hζ
  set M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => inner ℝ (τ i) (ρ j) with hM
  have hρspan : ∀ j, ρ j ∈ Submodule.span ℝ (Set.range τ) := fun j => hspan ▸ hρQ j
  -- `β(ρ) = det M · β(τ)`
  have hdet : ∀ β : Covector (Euclid P) m, β ρ = M.det * β τ :=
    Submission.dgoj_covector_eq_det_mul_of_mem_span P m τ ρ hτ hρspan
  -- Parseval in `span τ`: `⟨x, y⟩ = ∑ᵢ ⟨τᵢ, x⟩ ⟨τᵢ, y⟩`
  have hparseval : ∀ x y : Euclid P, y ∈ Submodule.span ℝ (Set.range τ) →
      inner ℝ x y = ∑ i, inner ℝ (τ i) x * inner ℝ (τ i) y := by
    intro x y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hy
    simp only [hτ.inner_right_fintype, inner_sum, inner_smul_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_comm, mul_comm]
  -- `M` is orthogonal, so `det M = ±1`
  have hMM : M.transpose * M = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, hM, Matrix.of_apply]
    rw [← hparseval (ρ j) (ρ k) (hρspan k)]
    exact orthonormal_iff_ite.1 hρ j k
  have hdet2 : M.det * M.det = 1 := by
    have := congrArg Matrix.det hMM
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hpm : M.det = 1 ∨ M.det = -1 := by
    have h0 : (M.det - 1) * (M.det + 1) = 0 := by linear_combination hdet2
    rcases mul_eq_zero.1 h0 with h | h
    · left; linarith
    · right; linarith
  rcases hsign with h | h <;> rcases hpm with hd | hd
  · left; intro β; rw [h, hdet, hd, one_mul]
  · right; intro β; rw [h, hdet, hd]; ring
  · right; intro β; rw [h, hdet, hd, one_mul]
  · left; intro β; rw [h, hdet, hd]; ring
/-- Step 3 of the orientation of a slice (Simon 6.4.3, `⟨v⌞w, a⟩ = ⟨v, w ∧ a⟩`): if `ν` is a
unit vector orthogonal to `σ₀, …, σₙ₋₁`, then `(ν♭ ∧ α)(ν, σ₀, …, σₙ₋₁) = α(σ₀, …, σₙ₋₁)` for
every `n`-covector `α`, where `ν♭ ∧ α` is the alternatization of `w ↦ ⟨ν, w⟩ α`,
`(ν♭ ∧ α)(v) = ∑ᵢ (-1)ⁱ ⟨ν, vᵢ⟩ α(v₀, …, v̂ᵢ, …, vₙ)`.  The term `i = 0` is
`⟨ν, ν⟩ α(σ) = α(σ)`; every other term has a factor `⟨ν, σⱼ⟩ = 0`. -/
theorem Submission.dor_lmbsf_io_wedge_eval_cons : ∀ (P n : ℕ) (ν : Euclid P) (σ : Fin n → Euclid P) (α : Covector (Euclid P) n), ‖ν‖ = 1 → (∀ i, inner ℝ ν (σ i) = 0) → ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α) (Fin.cons ν σ : Fin (n + 1) → Euclid P) = α σ := by
  intro P n ν σ α hν hνσ
  -- expand at `v = (ν, σ₀, …, σₙ₋₁)` and split off the term `i = 0`
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  -- `⟨ν, ν⟩ = ‖ν‖² = 1`, `v` without `v₀` is `σ`, and `⟨ν, vⱼ₊₁⟩ = ⟨ν, σⱼ⟩ = 0`
  simp [Fin.removeNth_zero, Fin.tail_cons, innerSL_apply_apply, hνσ, hν]

/-- Orientation of a slice (Simon Ch. 6, 4.3: `⟨v⌞w, a⟩ = ⟨v, w ∧ a⟩`, and `ξ⌞ν` orients
`TₓM ∩ ν^⊥`): if the `(n+1)`-vector `ζ` orients `Q`, `ν ∈ Q` is a unit vector and
`⟨α, ζ'⟩ = ⟨ν♭ ∧ α, ζ⟩` for every `n`-covector `α`, then `ζ'` orients `Q ∩ ν^⊥`.  In an
orthonormal frame `(ν, σ)` of `Q` adapted to `ν`, `ζ` is `±` evaluation at `(ν, σ)` and
`(ν♭ ∧ α)(ν, σ) = α(σ)`, so `ζ'(α) = ±α(σ)`. -/
theorem Submission.dor_lmbsf_interior_product_orientation : ∀ (P n : ℕ) (ζ : MultiVector P (n + 1)) (ζ' : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (ν : Euclid P), IsUnitOrientationOf ζ Q → ν ∈ Q → ‖ν‖ = 1 → (∀ α : Covector (Euclid P) n, ζ' α = ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α))) → IsUnitOrientationOf ζ' (Q ⊓ (ℝ ∙ ν)ᗮ) := by
  intro P n ζ ζ' Q ν hζ hνQ hν hζ'
  -- `dim Q = n + 1`, read off the orthonormal frame `τ` oriented by `ζ`
  have hdim : Module.finrank ℝ Q = n + 1 := by
    obtain ⟨τ, hτ, hτQ, -⟩ := hζ
    rw [← hτQ, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- an orthonormal frame `(ν, σ)` of `Q`, with `σ` an orthonormal basis of `Q ∩ ν^⊥`
  obtain ⟨σ, hσ, hσspan, hνσo, hσQ, hνσ⟩ :=
    Submission.dor_lmbsf_io_adapted_frame P n Q ν hdim hνQ hν
  have hνσQ : ∀ j, (Fin.cons ν σ : Fin (n + 1) → Euclid P) j ∈ Q := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hνQ
    · simpa using hσQ i
  -- `(ν♭ ∧ α)(ν, σ) = α(σ)`
  have hwedge : ∀ α : Covector (Euclid P) n,
      ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α)
        (Fin.cons ν σ : Fin (n + 1) → Euclid P) = α σ := fun α =>
    Submission.dor_lmbsf_io_wedge_eval_cons P n ν σ α hν hνσ
  -- `ζ` is `±` evaluation at `(ν, σ)`, so `ζ'` is `±` evaluation at `σ`
  refine ⟨σ, hσ, hσspan, ?_⟩
  rcases Submission.dor_lmbsf_io_orientation_frame_sign P (n + 1) ζ Q _ hζ hνσo hνσQ with h | h
  · exact Or.inl fun α => by rw [hζ' α, h, hwedge]
  · exact Or.inr fun α => by rw [hζ' α, h, hwedge]

/-- Signed co-area integral (Simon Ch. 2, 6.6, used for the slices in 7.4): if the slice
measures `ν t` satisfy the co-area identity `∫ (∫ φ dν_t) dt = ∫ w φ dμ` for every Borel
`φ ≥ 0`, and `∫ w |q| dμ < ∞`, then `t ↦ ∫ q dν_t` is integrable and
`∫ (∫ q dν_t) dt = ∫ w q dμ`.  Apply the identity to `q⁺` and `q⁻` and subtract; where
`w = ∞`, finiteness of `∫ w |q| dμ` forces `q = 0` `μ`-a.e. -/
theorem Submission.dor_lmbsf_si_coarea_signed_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (q : Euclid P → ℝ), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → Measurable w → Measurable q → ∫⁻ x, w x * ‖q x‖ₑ ∂μ ≠ ∞ → Integrable (fun t => ∫ x, q x ∂(ν t)) ∧ ∫ t, ∫ x, q x ∂(ν t) = ∫ x, (w x).toReal * q x ∂μ := by
  intro P μ ν w q hco hw hq hfin
  -- `q⁺ = ofReal q` and `q⁻ = ofReal (-q)` are Borel and bounded by `|q|`
  have hqp : Measurable fun x => ENNReal.ofReal (q x) := hq.ennreal_ofReal
  have hqn : Measurable fun x => ENNReal.ofReal (-q x) := hq.neg.ennreal_ofReal
  have hle_p : ∀ x, ENNReal.ofReal (q x) ≤ ‖q x‖ₑ := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hle_n : ∀ x, ENNReal.ofReal (-q x) ≤ ‖q x‖ₑ := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  -- the co-area identity for `q⁺`, `q⁻` and `|q|`, all with finite total integral
  obtain ⟨haeP, heqP⟩ := hco _ hqp
  obtain ⟨haeN, heqN⟩ := hco _ hqn
  obtain ⟨haeA, heqA⟩ := hco _ hq.enorm
  have hfinP : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (q x) ∂(ν t) ≠ ∞ := by
    rw [heqP]; exact ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right (hle_p x) _)
  have hfinN : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t) ≠ ∞ := by
    rw [heqN]; exact ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right (hle_n x) _)
  have hfinA : ∫⁻ t, ∫⁻ x, ‖q x‖ₑ ∂(ν t) ≠ ∞ := by rw [heqA]; exact hfin
  -- `q` is `ν t`-integrable for a.e. `t`, where `∫ q dν_t = ∫ q⁺ dν_t - ∫ q⁻ dν_t`
  have hint : ∀ᵐ t, Integrable q (ν t) := by
    filter_upwards [ae_lt_top' haeA hfinA] with t ht
    exact ⟨hq.aestronglyMeasurable, ht⟩
  have hrepr : (fun t => ∫ x, q x ∂(ν t)) =ᵐ[volume] fun t =>
      (∫⁻ x, ENNReal.ofReal (q x) ∂(ν t)).toReal - (∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t)).toReal := by
    filter_upwards [hint] with t ht
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part ht
  have hIP : Integrable (fun t => (∫⁻ x, ENNReal.ofReal (q x) ∂(ν t)).toReal) :=
    integrable_toReal_of_lintegral_ne_top haeP hfinP
  have hIN : Integrable (fun t => (∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t)).toReal) :=
    integrable_toReal_of_lintegral_ne_top haeN hfinN
  refine ⟨(hIP.sub hIN).congr hrepr.symm, ?_⟩
  -- the left side is `(∫ w q⁺ dμ).toReal - (∫ w q⁻ dμ).toReal`
  rw [integral_congr_ae hrepr, integral_sub hIP hIN, integral_toReal haeP (ae_lt_top' haeP hfinP),
    integral_toReal haeN (ae_lt_top' haeN hfinN), heqP, heqN]
  -- `h = w q` is `μ`-integrable since `|h| ≤ w |q|`; split `∫ h dμ` into its two parts
  have hh : Integrable (fun x => (w x).toReal * q x) μ := by
    refine ⟨(hw.ennreal_toReal.mul hq).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin.lt_top
    rw [enorm_mul]
    gcongr
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh]
  -- `w |q| < ∞` `μ`-a.e., and there `ofReal (w r) = w ofReal r` whenever `|r| ≤ |q|`
  -- (if `w = ∞` then `q = 0`, so `r = 0`)
  have hnull : ∀ᵐ x ∂μ, w x * ‖q x‖ₑ < ∞ := ae_lt_top (hw.mul hq.enorm) hfin
  have key : ∀ x, w x * ‖q x‖ₑ < ∞ → ∀ r : ℝ, |r| ≤ |q x| →
      ENNReal.ofReal ((w x).toReal * r) = w x * ENNReal.ofReal r := by
    intro x hx r hr
    by_cases hwx : w x = ∞
    · have hq0 : q x = 0 := by
        by_contra hq0
        rw [hwx, ENNReal.top_mul (by simpa using hq0)] at hx
        exact lt_irrefl _ hx
      have : r = 0 := by rw [hq0, abs_zero] at hr; exact abs_nonpos_iff.mp hr
      simp [this]
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hwx]
  have e1 : ∫⁻ x, ENNReal.ofReal ((w x).toReal * q x) ∂μ = ∫⁻ x, w x * ENNReal.ofReal (q x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with x hx
    exact key x hx (q x) le_rfl
  have e2 : ∫⁻ x, ENNReal.ofReal (-((w x).toReal * q x)) ∂μ =
      ∫⁻ x, w x * ENNReal.ofReal (-q x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with x hx
    rw [← mul_neg]
    exact key x hx (-q x) (by rw [abs_neg])
  rw [e1, e2]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
