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

/-- **A covector vanishing on all increasing tuples of standard basis vectors is zero**
(definiteness of the Euclidean coefficient norm).  With `e` the standard basis of `ℝᴾ`, an
alternating map is determined by its values `α(e_{J(0)}, …, e_{J(n-1)})` on injective
`J : Fin n → Fin P`.  For such `J`, `σ = Tuple.sort J` makes `J ∘ σ` monotone and injective, hence
strictly increasing, so `0 = α(e_{J ∘ σ}) = sign σ • α(e_J)` with `sign σ = ±1`. -/
theorem Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords : ∀ (P n : ℕ) (α : Covector (Euclid P) n), (∀ I : Fin n → Fin P, StrictMono I → α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) = 0) → α = 0 := by
  intro P n α h
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 1: it suffices to check `α(e_J) = 0` for injective `J`
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine e.ext_alternating fun J hJ => ?_
  show α (fun i => e (J i)) = (0 : ℝ)
  -- Step 2: sorting `J` gives a strictly increasing `J ∘ σ`
  have hmono : StrictMono (J ∘ Tuple.sort J) :=
    (Tuple.monotone_sort J).strictMono_of_injective (hJ.comp (Tuple.sort J).injective)
  -- Step 3: `0 = α(e_J ∘ σ) = sign σ • α(e_J)`, and `sign σ = ±1`
  have h1 : α.toAlternatingMap ((fun i => e (J i)) ∘ Tuple.sort J) = 0 := h _ hmono
  rw [AlternatingMap.map_perm] at h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Tuple.sort J)) with hs | hs <;> simpa [hs] using h1
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
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

/-- The operator norm of an `n`-covector on `ℝᴾ` is at most a constant times its Euclidean
coefficient norm: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_I`, set to `0` on tuples `I` that are not
strictly increasing, is linear and injective on the finite-dimensional space `Λⁿ(ℝᴾ)`, hence
antilipschitz, and each of its coordinates is at most `covectorEuclideanNorm α` in absolute
value. -/
theorem Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm : ∀ (P n : ℕ), ∃ K : ℝ, 0 < K ∧ ∀ α : Covector (Euclid P) n, ‖α‖ ≤ K * covectorEuclideanNorm α := by
  intro P n
  classical
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  -- `L α = (α(e ∘ I))_I` on strictly increasing `I`, and `0` elsewhere
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I =>
        if StrictMono I then α fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i) else 0
      map_add' := fun α β => by
        funext I
        by_cases hI : StrictMono I <;> simp [hI]
      map_smul' := fun c α => by
        funext I
        by_cases hI : StrictMono I <;> simp [hI] }
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro α hα
    refine Submission.cbr_ci_dr_dn_covector_eq_zero_of_coords P n α fun I hI => ?_
    simpa [L, hI] using congrFun hα I
  obtain ⟨K, hKpos, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨K, NNReal.coe_pos.2 hKpos, fun α => ?_⟩
  have h1 : ‖α‖ ≤ K * ‖L α‖ := by
    simpa using hK.le_mul_dist α 0
  -- `|α(e ∘ I)| ≤ covectorEuclideanNorm α`: one summand of the sum under the square root
  have h2 : ‖L α‖ ≤ covectorEuclideanNorm α := by
    refine (pi_norm_le_iff_of_nonneg (covectorEuclideanNorm_nonneg α)).2 fun I => ?_
    by_cases hI : StrictMono I
    · have hs := Finset.single_le_sum (f := fun J : Fin n → Fin P =>
        if StrictMono J then (α fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) ^ 2 else 0)
        (fun J _ => by split_ifs <;> positivity) (Finset.mem_univ I)
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hI, ↓reduceIte, Real.norm_eq_abs]
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by simpa [hI] using hs)
    · simp [L, hI, covectorEuclideanNorm_nonneg]
  calc ‖α‖ ≤ K * ‖L α‖ := h1
    _ ≤ K * covectorEuclideanNorm α := by gcongr

/-- **The norm on `n`-vectors dual to the Euclidean coefficient norm** (step 1 of the density
representation of a cycle).  Let `|α|` be the Euclidean coefficient norm on `Λⁿ(ℝᴾ)`,
`B = {β : |β| ≤ 1}` and `N ζ = sup ζ(B)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper, and `B`
is closed (`|·|` is continuous) and bounded (`‖β‖ ≤ K |β| ≤ K`), hence compact; so the supremum
is attained, and `0 ∈ B` gives `N ζ ≥ 0`.  If `|α| = 0` then `‖α‖ ≤ K |α| = 0`; otherwise
`±|α|⁻¹ α ∈ B` gives `|ζ α| ≤ N ζ |α|`.  Finally, if `ζ β = N ζ` with `β ∈ B`, then
`N ζ ≤ ζ' β + ‖ζ - ζ'‖ ‖β‖ ≤ N ζ' + K ‖ζ - ζ'‖`, so `N` is `K`-Lipschitz, hence continuous. -/
theorem Submission.cbr_ci_dr_multivector_dual_norm : ∀ (P n : ℕ), ∃ N : MultiVector P n → ℝ, Continuous N ∧ (∀ ζ : MultiVector P n, 0 ≤ N ζ) ∧ (∀ (ζ : MultiVector P n) (α : Covector (Euclid P) n), |ζ α| ≤ N ζ * covectorEuclideanNorm α) ∧ (∀ ζ : MultiVector P n, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ β = N ζ) := by
  intro P n
  -- Steps 3–4: `Λⁿ(ℝᴾ)` is finite-dimensional (hence proper), `|·|` is continuous and
  -- absolutely homogeneous, and `‖α‖ ≤ K |α|`
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  obtain ⟨-, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨K, hK, hnorm⟩ := Submission.cbr_ci_dr_dn_norm_le_mul_covectorEuclideanNorm P n
  -- Step 5: the unit ball `B` of `|·|` contains `0`, lies in `closedBall 0 K` and is compact
  let B := {β : Covector (Euclid P) n | covectorEuclideanNorm β ≤ 1}
  have h0B : (0 : Covector (Euclid P) n) ∈ B := by
    show covectorEuclideanNorm (0 : Covector (Euclid P) n) ≤ 1
    rw [covectorEuclideanNorm_zero]
    exact zero_le_one
  have hBK : ∀ β ∈ B, ‖β‖ ≤ K := fun β hβ =>
    (hnorm β).trans (mul_le_of_le_one_right hK.le hβ)
  have hBc : IsCompact B :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : Covector (Euclid P) n)) (r := K)).subset
        fun β hβ => mem_closedBall_zero_iff.mpr (hBK β hβ))
  -- Step 6: `N ζ = sup ζ(B)` is attained on `B` and bounds `ζ` on `B`
  have hmem : ∀ ζ : MultiVector P n, ∃ β ∈ B, ζ β = sSup (ζ '' B) := fun ζ =>
    (hBc.image ζ.continuous).sSup_mem ⟨ζ 0, 0, h0B, rfl⟩
  have hle : ∀ ζ : MultiVector P n, ∀ β ∈ B, ζ β ≤ sSup (ζ '' B) := fun ζ β hβ =>
    le_csSup (hBc.image ζ.continuous).bddAbove ⟨β, hβ, rfl⟩
  refine ⟨fun ζ => sSup (ζ '' B), ?_, fun ζ => ?_, fun ζ α => ?_, hmem⟩
  · -- Step 9: `N ζ ≤ N ζ' + K ‖ζ - ζ'‖`, so `N` is `K`-Lipschitz
    refine (LipschitzWith.of_le_add_mul' (f := fun ζ : MultiVector P n => sSup (ζ '' B)) K
      fun ζ ζ' => ?_).continuous
    obtain ⟨β, hβ, hζβ⟩ := hmem ζ
    have h1 : ζ β - ζ' β ≤ ‖ζ - ζ'‖ * K := by
      have h := (ζ - ζ').le_opNorm β
      rw [sub_apply, Real.norm_eq_abs] at h
      exact (le_abs_self _).trans
        (h.trans (mul_le_mul_of_nonneg_left (hBK β hβ) (norm_nonneg _)))
    have h2 := hle ζ' β hβ
    rw [dist_eq_norm ζ ζ']
    show sSup (ζ '' B) ≤ sSup (ζ' '' B) + K * ‖ζ - ζ'‖
    linarith
  · -- Step 7: `0 ∈ B` and `ζ 0 = 0`
    exact (map_zero ζ).symm.le.trans (hle ζ 0 h0B)
  · -- Step 8: if `|α| = 0` then `α = 0`; otherwise rescale `α` into `B`
    show |ζ α| ≤ sSup (ζ '' B) * covectorEuclideanNorm α
    rcases (covectorEuclideanNorm_nonneg α).eq_or_lt with h | h
    · have hα : ‖α‖ ≤ 0 := by
        have h' := hnorm α
        rwa [← h, mul_zero] at h'
      rw [norm_le_zero_iff.mp hα, map_zero, abs_zero, covectorEuclideanNorm_zero, mul_zero]
    · have hβ : (covectorEuclideanNorm α)⁻¹ • α ∈ B := by
        show covectorEuclideanNorm ((covectorEuclideanNorm α)⁻¹ • α) ≤ 1
        rw [hsmul, abs_inv, abs_of_pos h, inv_mul_cancel₀ h.ne']
      have hβ' : -((covectorEuclideanNorm α)⁻¹ • α) ∈ B := by
        show covectorEuclideanNorm (-((covectorEuclideanNorm α)⁻¹ • α)) ≤ 1
        rw [covectorEuclideanNorm_neg]
        exact hβ
      have h1 := hle ζ _ hβ
      have h2 := hle ζ _ hβ'
      rw [map_neg] at h2
      calc |ζ α| = covectorEuclideanNorm α * |ζ ((covectorEuclideanNorm α)⁻¹ • α)| := by
            rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos h,
              mul_inv_cancel_left₀ h.ne']
        _ ≤ covectorEuclideanNorm α * sSup (ζ '' B) :=
            mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, h1⟩) h.le
        _ = sSup (ζ '' B) * covectorEuclideanNorm α := mul_comm _ _
/-- Positive lower `n`-density of a finite measure forces finite `Hⁿ`-measure (Vitali `5r`-covering,
used for Simon 7.2.4 via the density representation): if `μ(ℝᴾ) < ∞` and
`liminf_{r↓0} μ(B_r(x))/(ωₙrⁿ) ≥ η > 0` for every `x ∈ A`, then `Hⁿ(A) < ∞`.  At scale `k`, choose
radii `rₖ(x) < 1/(k+1)` with `c rₖ(x)ⁿ ≤ μ(B̄_{rₖ(x)}(x))`, `c = (η/2)ωₙ`; the Vitali subfamily
`uₖ ⊆ A` is countable and disjoint, so `Σ_{uₖ} rₖⁿ ≤ μ(ℝᴾ)/c`, and the enlarged balls
`B̄_{5rₖ(b)}(b)` cover `A` with `Σ diamⁿ ≤ 10ⁿ μ(ℝᴾ)/c`. -/
theorem Submission.cbr_ci_dr_euclideanHausdorff_lt_top_of_lower_density : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (η : ℝ), 0 < η → μ univ < ∞ → (∀ x ∈ A, ENNReal.ofReal η ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → μHE[n] A < ∞ := by
  intro P n μ A η hη hμ hA
  -- `c = (η/2) ωₙ ∈ (0, ∞)`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  set c : ℝ≥0∞ := ENNReal.ofReal (η / 2) * unitBallVolume n with hc
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (half_pos hη)).ne' hω0
  have hctop : c ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωtop
  -- arbitrarily small radii `ρ` with `c ρⁿ ≤ μ(B̄_ρ(x))`
  have hgood : ∀ x ∈ A, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
      c * ENNReal.ofReal (ρ ^ n) ≤ μ (closedBall x ρ) := by
    intro x hx δ hδ
    have hlt : ENNReal.ofReal (η / 2) < liminf (fun r : ℝ =>
        μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) :=
      ((ENNReal.ofReal_lt_ofReal_iff hη).2 (half_lt_self hη)).trans_le (hA x hx)
    obtain ⟨ρ, hρ, hρδ⟩ :=
      ((eventually_lt_of_lt_liminf hlt).and (Ioo_mem_nhdsGT hδ)).exists
    refine ⟨ρ, hρδ.1, hρδ.2, ?_⟩
    calc c * ENNReal.ofReal (ρ ^ n)
        = ENNReal.ofReal (η / 2) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by
          rw [hc, mul_assoc]
      _ ≤ μ (ball x ρ) := ENNReal.mul_le_of_le_div hρ.le
      _ ≤ μ (closedBall x ρ) := measure_mono ball_subset_closedBall
  -- radii `rₖ(x) < 1/(k+1)` at every scale `k`
  choose! r hr0 hrδ hrμ using fun (k : ℕ) (x : Euclid P) (hx : x ∈ A) =>
    hgood x hx (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  -- Vitali subfamilies `uₖ ⊆ A`; they are countable since the balls have nonempty interior
  have hvit : ∀ k : ℕ, ∃ u ⊆ A, (u.PairwiseDisjoint fun a => closedBall a (r k a)) ∧
      ∀ a ∈ A, ∃ b ∈ u, closedBall a (r k a) ⊆ closedBall b (5 * r k b) := fun k =>
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A (fun a => a) (r k)
      (1 / ((k : ℝ) + 1)) (fun a ha => (hrδ k a ha).le) 5 (by norm_num)
  choose u huA hudisj hucov using hvit
  have hucount : ∀ k, (u k).Countable := fun k =>
    (hudisj k).countable_of_nonempty_interior fun a ha =>
      (nonempty_ball.2 (hr0 k a (huA k ha))).mono
        (interior_maximal ball_subset_closedBall isOpen_ball)
  have : ∀ k, Countable (u k) := fun k => (hucount k).to_subtype
  -- `Σ_{b ∈ uₖ} rₖ(b)ⁿ ≤ μ(ℝᴾ)/c` by disjointness
  have hsum : ∀ k, ∑' b : u k, ENNReal.ofReal (r k b ^ n) ≤ μ univ / c := by
    intro k
    rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop), mul_comm, ← ENNReal.tsum_mul_left]
    calc ∑' b : u k, c * ENNReal.ofReal (r k b ^ n)
        ≤ ∑' b : u k, μ (closedBall (b : Euclid P) (r k b)) :=
          ENNReal.tsum_le_tsum fun b => hrμ k b (huA k b.2)
      _ = μ (⋃ b ∈ u k, closedBall b (r k b)) :=
          (measure_biUnion (hucount k) (hudisj k) fun b _ => measurableSet_closedBall).symm
      _ ≤ μ univ := measure_mono (subset_univ _)
  -- `diam B̄_{5rₖ(b)}(b) ≤ 10 rₖ(b)`
  have hdiam : ∀ k, ∀ b ∈ u k,
      ediam (closedBall b (5 * r k b)) ≤ ENNReal.ofReal (10 * r k b) := by
    intro k b _
    refine ediam_le_of_forall_dist_le fun y hy z hz => ?_
    calc dist y z ≤ dist y b + dist z b := dist_triangle_right y z b
      _ ≤ 5 * r k b + 5 * r k b := add_le_add (mem_closedBall.1 hy) (mem_closedBall.1 hz)
      _ = 10 * r k b := by ring
  set Λ : ℝ≥0∞ := ENNReal.ofReal (10 ^ n) * (μ univ / c) with hΛ
  have hΛtop : Λ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.div_lt_top hμ.ne hc0)
  -- `μH[n](A) ≤ Λ` from the covers `{B̄_{5rₖ(b)}(b)}_{b ∈ uₖ}` of mesh `≤ 10/(k+1)`
  have hH : μH[n] A ≤ Λ := by
    have htend :
        Tendsto (fun k : ℕ => ENNReal.ofReal (10 * (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (10 : ℝ))
      rw [mul_zero] at h
      simpa using ENNReal.tendsto_ofReal h
    refine (Measure.hausdorffMeasure_le_liminf_tsum (n : ℝ) A (l := atTop)
      (ι := fun k => u k) _ htend (fun k b => closedBall (b : Euclid P) (5 * r k b))
      (Eventually.of_forall fun k b => (hdiam k b b.2).trans (ENNReal.ofReal_le_ofReal ?_))
      (Eventually.of_forall fun k a ha => ?_)).trans ?_
    · have := hrδ k b (huA k b.2)
      linarith
    · obtain ⟨b, hb, hab⟩ := hucov k a ha
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hab (mem_closedBall_self (hr0 k a ha).le)⟩
    · refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
      calc ∑' b : u k, ediam (closedBall (b : Euclid P) (5 * r k b)) ^ (n : ℝ)
          ≤ ∑' b : u k, ENNReal.ofReal (10 ^ n) * ENNReal.ofReal (r k b ^ n) := by
            refine ENNReal.tsum_le_tsum fun b => ?_
            have h0 : 0 ≤ r k b := (hr0 k b (huA k b.2)).le
            rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
              ENNReal.ofReal_pow (by positivity)]
            exact pow_le_pow_left₀ bot_le (hdiam k b b.2) n
        _ = ENNReal.ofReal (10 ^ n) * ∑' b : u k, ENNReal.ofReal (r k b ^ n) :=
            ENNReal.tsum_mul_left
        _ ≤ Λ := by rw [hΛ]; gcongr; exact hsum k
  -- `μHE[n] = s • μH[n]` with a finite scalar `s`
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hH.trans_lt hΛtop)

/-- **The mass identity forces the representing `n`-vector field to attain `1` a.e.** (Simon Ch. 6,
2.7–2.8: in `T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T` with `μ_T(U) = M(T)`, `|T⃗| = 1` `μ_T`-a.e.).  Let `Γ ∈ 𝒟ₙ(ℝᴾ)`,
`μ` finite with `M(Γ) = μ(ℝᴾ)`, and `ξ` `μ`-a.e. strongly measurable with `|ξ(x)(α)| ≤ |α|` a.e.
and `Γ(ω) = ∫ ξ(x)(ω(x)) dμ`.  For the dual norm `N` of `|·|` on `n`-vectors, `f = N ∘ ξ` has
`0 ≤ f ≤ 1` a.e.; every mass-admissible `ω` gives `Γ(ω) ≤ ∫ f dμ`, so `μ(ℝᴾ) = M(Γ) ≤ ∫ f dμ`.
Hence `∫ (1 − f) dμ = 0`, `f = 1` a.e., and a covector `β` attaining `N(ξ(x))` has `|β| ≤ 1`
and `ξ(x)(β) = 1`. -/
theorem Submission.cbr_ci_dr_ae_unit_attained_of_mass_eq : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ univ < ∞ → Γ.massOn univ = μ univ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ x β = 1 := by
  intro P n Γ μ ξ hμ hmass hξ hbound hrep
  -- (1) the dual norm `N` of `|·|` on `n`-vectors (sibling `dual_norm`); `μ` is finite
  obtain ⟨N, hNc, hN0, hNle, hNatt⟩ := Submission.cbr_ci_dr_multivector_dual_norm P n
  have : IsFiniteMeasure μ := ⟨hμ⟩
  -- (2) `f = N ∘ ξ` satisfies `0 ≤ f ≤ 1` a.e. and is integrable
  have hf_le : ∀ᵐ x ∂μ, N (ξ x) ≤ 1 := by
    filter_upwards [hbound] with x hx
    obtain ⟨β, hβ, hξβ⟩ := hNatt (ξ x)
    calc N (ξ x) = ξ x β := hξβ.symm
      _ ≤ |ξ x β| := le_abs_self _
      _ ≤ covectorEuclideanNorm β := hx β
      _ ≤ 1 := hβ
  have hf_int : Integrable (fun x => N (ξ x)) μ := by
    refine Integrable.of_bound (hNc.comp_aestronglyMeasurable hξ) 1 ?_
    filter_upwards [hf_le] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (hN0 _)]
  -- (3) every mass-admissible `ω` has `Γ(ω) = ∫ ξ(ω) dμ ≤ ∫ f dμ`, as `|ξ(x)(ω(x))| ≤ f(x)`
  have hadm : ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid P)) n univ,
      Γ ω ≤ ∫ x, N (ξ x) ∂μ := by
    intro ω hω
    have hgN : ∀ x, |ξ x ((ω : DifferentialForm (Euclid P) n) x)| ≤ N (ξ x) := fun x =>
      (hNle (ξ x) _).trans (mul_le_of_le_one_right (hN0 _) (hω.2 x))
    have hg_meas : AEStronglyMeasurable
        (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ :=
      (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hξ.prodMk ω.property.1.1.continuous.aestronglyMeasurable)
    have hg_int : Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ :=
      hf_int.mono' hg_meas (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hgN x))
    rw [hrep ω]
    exact integral_mono hg_int hf_int fun x => (le_abs_self _).trans (hgN x)
  -- (4) `μ(ℝᴾ) = M(Γ) ≤ ∫ f dμ`
  have hmass_le : μ univ ≤ ENNReal.ofReal (∫ x, N (ξ x) ∂μ) := by
    rw [← hmass]
    apply sSup_le
    rintro r ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hadm ω hω)
  have hreal : μ.real univ ≤ ∫ x, N (ξ x) ∂μ :=
    ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => hN0 _) hmass_le
  -- (5) `∫ (1 − f) dμ = μ(ℝᴾ) − ∫ f dμ ≤ 0` with `1 − f ≥ 0` a.e., so `f = 1` a.e.
  have hsub_nonneg : 0 ≤ᵐ[μ] fun x => 1 - N (ξ x) := by
    filter_upwards [hf_le] with x hx
    exact sub_nonneg.2 hx
  have hsub_zero : ∫ x, (1 - N (ξ x)) ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hsub_nonneg)
    rw [integral_sub (integrable_const 1) hf_int, integral_const, smul_eq_mul, mul_one]
    exact sub_nonpos.2 hreal
  have hae : (fun x => 1 - N (ξ x)) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hsub_nonneg ((integrable_const 1).sub hf_int)).1 hsub_zero
  -- (6) where `N(ξ(x)) = 1`, the covector attaining `N(ξ(x))` is the required `β`
  filter_upwards [hae] with x hx
  obtain ⟨β, hβ, hξβ⟩ := hNatt (ξ x)
  refine ⟨β, hβ, ?_⟩
  have h1 : 1 - N (ξ x) = 0 := hx
  rw [hξβ]
  linarith

/-- **Bounded strongly measurable modification of an `n`-vector field** (the Borel normalized
field `ξ₀ / max(1, |ξ₀|*)` of the density representation).  If `ξ` is `μ`-a.e. strongly
measurable and `|⟨α, ξ(x)⟩| ≤ |α|` for `μ`-a.e. `x` and every `n`-covector `α`
(`|·| = covectorEuclideanNorm`), then some strongly measurable `ζ` satisfies the bound at every
`x` and agrees with `ξ` `μ`-a.e.  With `N = |·|*` the dual norm of
`cbr_ci_dr_multivector_dual_norm` and `ξ₀` a strongly measurable version of `ξ`, take
`ζ = max(1, N ∘ ξ₀)⁻¹ • ξ₀`: it is a continuous function of `ξ₀`, `|ζ(x)(α)| ≤ |α|` because
`N(ξ₀(x)) ≤ max(1, N(ξ₀(x)))`, and `ζ = ξ₀ = ξ` wherever `ξ₀ = ξ` and `ξ` is bounded, since
there `N(ξ) ≤ 1` by attainment of `N` on the unit ball. -/
theorem Submission.cbr_ci_dr_bounded_stronglyMeasurable_modification : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ ζ : Euclid P → MultiVector P n, StronglyMeasurable ζ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) ∧ ζ =ᵐ[μ] ξ := by
  intro P n μ ξ hξm hξb
  -- Step 1: the dual norm `N` on `n`-vectors (`dual_norm`)
  obtain ⟨N, hNc, -, hNle, hNatt⟩ := Submission.cbr_ci_dr_multivector_dual_norm P n
  -- Step 2: an `n`-vector `η` with `|η(α)| ≤ |α|` for all `α` has `N(η) ≤ 1` (attainment)
  have hN1 : ∀ η : MultiVector P n,
      (∀ α : Covector (Euclid P) n, |η α| ≤ covectorEuclideanNorm α) → N η ≤ 1 := by
    intro η hη
    obtain ⟨β, hβ, hηβ⟩ := hNatt η
    calc N η = η β := hηβ.symm
      _ ≤ |η β| := le_abs_self _
      _ ≤ covectorEuclideanNorm β := hη β
      _ ≤ 1 := hβ
  -- Step 3: the normalization `η ↦ max(1, N(η))⁻¹ • η` is continuous (denominator `≥ 1`)
  have hm : ∀ η : MultiVector P n, 0 < max 1 (N η) := fun η =>
    zero_lt_one.trans_le (le_max_left _ _)
  have hFc : Continuous fun η : MultiVector P n => (max 1 (N η))⁻¹ • η :=
    ((continuous_const.max hNc).inv₀ fun η => (hm η).ne').smul continuous_id
  -- Step 4: `ζ := max(1, N ∘ ξ₀)⁻¹ • ξ₀` for a strongly measurable version `ξ₀` of `ξ`
  obtain ⟨ξ₀, hξ₀, hξξ₀⟩ : ∃ ξ₀ : Euclid P → MultiVector P n, StronglyMeasurable ξ₀ ∧
      ξ =ᵐ[μ] ξ₀ :=
    ⟨hξm.mk ξ, hξm.stronglyMeasurable_mk, hξm.ae_eq_mk⟩
  refine ⟨fun x => (max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x, hFc.comp_stronglyMeasurable hξ₀, ?_, ?_⟩
  · -- Step 5: with `m = max(1, N(ξ₀ x))`, `|ζ(x)(α)| = m⁻¹ |ξ₀(x)(α)| ≤ m⁻¹ N(ξ₀ x) |α| ≤ |α|`
    intro x α
    show |((max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x) α| ≤ covectorEuclideanNorm α
    rw [smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 (hm (ξ₀ x))),
      inv_mul_le_iff₀ (hm (ξ₀ x))]
    exact (hNle (ξ₀ x) α).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (covectorEuclideanNorm_nonneg α))
  · -- Step 6: where `ξ₀ = ξ` and `ξ` is bounded, `N(ξ₀ x) ≤ 1`, so `m = 1` and `ζ(x) = ξ(x)`
    filter_upwards [hξξ₀, hξb] with x hx hxb
    show (max 1 (N (ξ₀ x)))⁻¹ • ξ₀ x = ξ x
    rw [← hx, max_eq_left (hN1 (ξ x) hxb), inv_one, one_smul]
/-- Radon–Nikodym with a carrier: if `μ` is finite, `μ(M₀ᶜ) = 0`, `ν(M₀) < ∞` and `μ ≪ ν`, then
`μ = (ν⌞M)·θ` for a Borel `M ⊆ M₀` and a Borel `θ > 0` on `M`.  With `ν₀ = ν⌞M₀` (finite) and
`h = dμ/dν₀`, `μ ≪ ν₀` gives `μ = ν₀·h` with `h < ∞` `ν₀`-a.e.; take
`M = M₀ ∩ {0 < h < ∞}` and `θ = 1_M · h.toReal`, so that `h = 1_M · ofReal θ` `ν₀`-a.e. -/
theorem Submission.cbr_ci_dr_withDensity_carrier_of_absolutelyContinuous : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (M₀ : Set (Euclid P)), μ univ < ∞ → MeasurableSet M₀ → ν M₀ < ∞ → μ M₀ᶜ = 0 → (∀ E : Set (Euclid P), ν E = 0 → μ E = 0) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ), MeasurableSet M ∧ M ⊆ M₀ ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ μ = (ν.restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) := by
  intro P μ ν M₀ hμ hM₀ hνM₀ hμM₀c hac
  -- `μ` and `ν₀ = ν⌞M₀` are finite
  have : IsFiniteMeasure μ := ⟨hμ⟩
  have : IsFiniteMeasure (ν.restrict M₀) := isFiniteMeasure_restrict.mpr hνM₀.ne
  -- `μ ≪ ν₀`: `ν₀(E) = ν(E ∩ M₀)` and `μ(M₀ᶜ) = 0`
  have hμν₀ : μ ≪ ν.restrict M₀ := by
    intro E hE
    rw [Measure.restrict_apply' hM₀] at hE
    rw [← inter_union_compl E M₀]
    exact measure_union_null (hac _ hE) (measure_mono_null inter_subset_right hμM₀c)
  -- Radon–Nikodym: `μ = ν₀·h` with `h = dμ/dν₀` Borel and `h < ∞` `ν₀`-a.e.
  obtain ⟨h, hh, hμh, hh_lt⟩ : ∃ h : Euclid P → ℝ≥0∞, Measurable h ∧
      μ = (ν.restrict M₀).withDensity h ∧ ∀ᵐ x ∂(ν.restrict M₀), h x < ∞ := by
    refine ⟨μ.rnDeriv (ν.restrict M₀), Measure.measurable_rnDeriv _ _, ?_,
      Measure.rnDeriv_lt_top _ _⟩
    have hdec := Measure.haveLebesgueDecomposition_add μ (ν.restrict M₀)
    rwa [Measure.singularPart_eq_zero_of_ac hμν₀, zero_add] at hdec
  -- the carrier `M = M₀ ∩ {0 < h} ∩ {h < ∞}` and the density `θ = 1_M · h.toReal`
  set M : Set (Euclid P) := M₀ ∩ {x | 0 < h x} ∩ {x | h x < ∞}
  have hM : MeasurableSet M :=
    (hM₀.inter (measurableSet_lt measurable_const hh)).inter (measurableSet_lt hh measurable_const)
  have hMM₀ : M ⊆ M₀ := fun x hx => hx.1.1
  refine ⟨M, M.indicator fun x => (h x).toReal, hM, hMM₀, hh.ennreal_toReal.indicator hM,
    fun x hx => ?_, ?_⟩
  · rw [indicator_of_mem hx]
    exact ENNReal.toReal_pos hx.1.2.ne' hx.2.ne
  -- `h = 1_M · ofReal θ` `ν₀`-a.e., since `ν₀`-a.e. `x ∈ M₀` and `h x < ∞`
  have hae : h =ᵐ[ν.restrict M₀]
      M.indicator fun x => ENNReal.ofReal (M.indicator (fun x => (h x).toReal) x) := by
    filter_upwards [ae_restrict_mem hM₀, hh_lt] with x hxM₀ hxlt
    by_cases hxM : x ∈ M
    · rw [indicator_of_mem hxM, indicator_of_mem hxM, ENNReal.ofReal_toReal hxlt.ne]
    · rw [indicator_of_notMem hxM]
      exact nonpos_iff_eq_zero.mp (not_lt.mp fun hpos => hxM ⟨⟨hxM₀, hpos⟩, hxlt⟩)
  -- `μ = ν₀·(1_M · ofReal θ) = (ν₀⌞M)·ofReal θ = (ν⌞M)·ofReal θ`
  rw [hμh, withDensity_congr_ae hae, withDensity_indicator hM,
    Measure.restrict_restrict_of_subset hMM₀]

/-- Density representation of the limit cycle (Simon 7.2.4 via the closure theorem, step 3 of the
integer multiplicity argument): if `μ = μ_Γ` is finite, `Γ(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|ξ|* ≤ 1`,
`μ ≪ Hⁿ` and `liminf_{r↓0} μ(B_r(x))/(ωₙrⁿ) ≥ η₀ > 0` for `μ`-a.e. `x`, then `μ = θ Hⁿ⌞M` and
`Γ(ω) = ∫_M θ ⟨ω, ζ⟩ dHⁿ` on a Borel carrier `M` with `Hⁿ(M) < ∞`.  `ζ` is the Borel bounded
modification of `ξ`; the mass identity `μ(ℝᴾ) = M(Γ)` makes it attain `1` on the unit covector
ball `μ`-a.e.  `M₀` is the complement of a Borel `μ`-null set off which this and the density
bound hold, so `Hⁿ(M₀) < ∞` (Vitali), and Radon–Nikodym for `μ ≪ Hⁿ⌞M₀` gives `M ⊆ M₀` and
`θ > 0` on `M`. -/
theorem Submission.cbr_ci_density_representation : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (η₀ : ℝ), 0 < η₀ → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → (∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0) → (∀ᵐ x ∂μ, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) → ∃ (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M ∧ μHE[n] M < ∞ ∧ Measurable θ ∧ StronglyMeasurable ζ ∧ μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) ∧ (∀ x ∈ M, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) ∧ (∀ x ∈ M, ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)) := by
  intro P n Γ μ ξ η₀ hη₀ hμ hmass hξm hξ hrep hnull hdens
  have hξae : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α :=
    Eventually.of_forall hξ
  -- a strongly measurable `ζ` with `|ζ(x)(α)| ≤ |α|` everywhere and `ζ = ξ` `μ`-a.e.
  obtain ⟨ζ, hζm, hζ, hζξ⟩ :=
    Submission.cbr_ci_dr_bounded_stronglyMeasurable_modification P n μ ξ hξm hξae
  -- `μ(ℝᴾ) = M(Γ)` forces `ξ`, hence `ζ`, to attain `1` on the unit covector ball `μ`-a.e.
  have hunit : ∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1 := by
    filter_upwards [Submission.cbr_ci_dr_ae_unit_attained_of_mass_eq P n Γ μ ξ hμ
      (hmass univ isOpen_univ) hξm hξae hrep, hζξ] with x hx hxζ
    rwa [hxζ]
  -- a Borel `μ`-null set `N` off which both `μ`-a.e. properties hold; `M₀ = Nᶜ`
  obtain ⟨N, hsN, hN, hμN⟩ := exists_measurable_superset_of_null (ae_iff.1 (hunit.and hdens))
  have hgood : ∀ x ∈ Nᶜ, (∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) ∧
      ENNReal.ofReal η₀ ≤ liminf (fun r : ℝ => μ (ball x r) /
        (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) :=
    fun x hx => not_not.1 fun h => hx (hsN h)
  -- `Hⁿ(M₀) < ∞` by the Vitali covering argument
  have hHN : μHE[n] Nᶜ < ∞ :=
    Submission.cbr_ci_dr_euclideanHausdorff_lt_top_of_lower_density P n μ Nᶜ η₀ hη₀ hμ
      fun x hx => (hgood x hx).2
  -- Radon–Nikodym for `μ ≪ Hⁿ⌞M₀`: `μ = θ Hⁿ⌞M` with `M ⊆ M₀` Borel and `θ > 0` on `M`
  obtain ⟨M, θ, hM, hMN, hθm, hθpos, hμeq⟩ :=
    Submission.cbr_ci_dr_withDensity_carrier_of_absolutelyContinuous P μ μHE[n] Nᶜ hμ hN.compl
      hHN (by rwa [compl_compl]) hnull
  refine ⟨M, θ, ζ, hM, (measure_mono hMN).trans_lt hHN, hθm, hζm, hμeq, hθpos, hζ,
    fun x hx => (hgood x (hMN hx)).1, fun ω => ?_, fun x hx => (hgood x (hMN hx)).2⟩
  -- `Γ(ω) = ∫ ⟨ω, ζ⟩ dμ = ∫_M θ ⟨ω, ζ⟩ dHⁿ`
  have hωζ : (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) =ᵐ[μ]
      fun x => ζ x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hζξ] with x hx
    rw [hx]
  rw [hrep ω, integral_congr_ae hωζ, hμeq, integral_withDensity_eq_integral_toReal_smul
    hθm.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hM fun x hx => ?_
  simp only [ENNReal.toReal_ofReal (hθpos x hx).le, smul_eq_mul]
/-- **Cut-off quadratic moments over `n`-planes** (the constant `cₙ` of the measurability proof
for the approximate tangent planes of Simon Ch. 3, 1.4).  For `n ≥ 1` one constant `c > 0`,
depending only on `n`, gives `∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|²` for every `P`,
every `n`-dimensional subspace `Q ⊆ ℝᴾ` and every `u ∈ ℝᴾ`.  On `ℝⁿ` put
`q(w) = ∫ max(1 − |z|², 0)⟨w, z⟩² dHⁿ(z)` and `c = q(e)`, `|e| = 1`: linear isometries preserve
`Hⁿ`, so `q` is invariant under them, `q(tw) = t²q(w)`, and a reflection maps `|w|e` to `w`,
whence `q(w) = c|w|²`; `c > 0` since the integrand is continuous, `≥ 0`, compactly supported and
`3/16` at `e/2`.  An isometry `ι = L⁻¹ : ℝⁿ → Q ⊆ ℝᴾ` carries `Hⁿ` to `Hⁿ⌞Q`, and
`⟨u, ι z⟩ = ⟨L(p_Q u), z⟩`, so the integral is `q(L(p_Q u)) = c|p_Q u|²`. -/
theorem Submission.exists_plane_cutoff_quadratic_moment_eq : ∀ n : ℕ, 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ u : Euclid P, ∫ y in (Q : Set (Euclid P)), max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 ∂μHE[n] = c * ‖Q.starProjection u‖ ^ 2 := by
  intro n hn
  -- The moment `q(w)` on the model plane `ℝⁿ`; the constant is `c = q(e)` for a unit vector `e`.
  obtain ⟨q, hq_def⟩ : ∃ q : Euclid n → ℝ,
      ∀ w, q w = ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ w z ^ 2 ∂μHE[n] :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Euclid n, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  -- `q(Rw) = q(w)` for a linear isometry `R`: substitute `z = Rz'`, `R` preserves `Hⁿ`.
  have hq_iso : ∀ (R : Euclid n ≃ₗᵢ[ℝ] Euclid n) (w : Euclid n), q (R w) = q w := by
    intro R w
    have key : ∫ z, max (1 - ‖R z‖ ^ 2) 0 * inner ℝ (R w) (R z) ^ 2 ∂μHE[n] =
        ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ (R w) z ^ 2 ∂μHE[n] :=
      (R.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n).integral_comp
        R.toHomeomorph.measurableEmbedding (fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ (R w) y ^ 2)
    simp only [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map] at key
    rw [hq_def, hq_def, ← key]
  have hq_smul : ∀ (t : ℝ) (w : Euclid n), q (t • w) = t ^ 2 * q w := by
    intro t w
    rw [hq_def, hq_def, ← integral_const_mul]
    congr 1
    funext z
    rw [real_inner_smul_left]
    ring
  -- `q(w) = c|w|²`: the reflection in `(|w|e − w)ᗮ` maps `|w|e` to `w`.
  have hq : ∀ w : Euclid n, q w = q e * ‖w‖ ^ 2 := by
    intro w
    have h1 : ‖‖w‖ • e‖ = ‖w‖ := by rw [norm_smul, he, mul_one, norm_norm]
    obtain ⟨R, hR⟩ : ∃ R : Euclid n ≃ₗᵢ[ℝ] Euclid n, R (‖w‖ • e) = w :=
      ⟨_, Submodule.reflection_sub h1⟩
    calc q w = q (R (‖w‖ • e)) := by rw [hR]
      _ = q (‖w‖ • e) := hq_iso R _
      _ = q e * ‖w‖ ^ 2 := by rw [hq_smul, mul_comm]
  -- `c > 0`: on `ℝⁿ`, `Hⁿ` is Lebesgue measure, and the integrand is `3/16` at `e/2`.
  have hc : 0 < q e := by
    have hcont : Continuous fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      fun_prop
    have hsupp : HasCompactSupport fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz => ?_
      have h1 : 1 < ‖z‖ := by simpa using hz
      have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
      simp [max_eq_right h2]
    have hnonneg : 0 ≤ fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 :=
      fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)
    have hx : (fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2) ((1 / 2 : ℝ) • e) ≠ 0 := by
      simp only [norm_smul, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      norm_num
    rw [hq_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg hx
  refine ⟨q e, hc, fun P Q hQ u => ?_⟩
  -- An orthonormal basis of `Q` indexed by `Fin n` gives `L : Q ≃ ℝⁿ`; `ι = L⁻¹` is an isometry
  -- of `ℝⁿ` onto `Q ⊆ ℝᴾ`, so `ι_# Hⁿ = Hⁿ⌞Q`.
  obtain ⟨L, -⟩ : ∃ L : Q ≃ₗᵢ[ℝ] Euclid n, True :=
    ⟨((stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)).repr, trivial⟩
  have hι : Isometry fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    isometry_subtype_coe.comp L.symm.isometry
  have hrange : Set.range (fun z : Euclid n => ((L.symm z : Q) : Euclid P)) =
      (Q : Set (Euclid P)) := by
    ext y
    refine ⟨?_, fun hy => ⟨L ⟨y, hy⟩, by simp⟩⟩
    rintro ⟨z, rfl⟩
    exact (L.symm z).2
  have hemb : MeasurableEmbedding fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    hι.isClosedEmbedding.measurableEmbedding
  have hnorm : ∀ z : Euclid n, ‖((L.symm z : Q) : Euclid P)‖ = ‖z‖ := fun z => L.symm.norm_map z
  -- `⟨u, ι z⟩ = ⟨p_Q u, ι z⟩ = ⟨L(p_Q u), z⟩`.
  have hinner : ∀ z : Euclid n, inner ℝ u ((L.symm z : Q) : Euclid P) =
      inner ℝ (L (Q.orthogonalProjectionOnto u)) z := by
    intro z
    rw [LinearIsometryEquiv.inner_map_eq_flip,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← hrange, ← hι.map_euclideanHausdorffMeasure, hemb.integral_map]
  simp only [hnorm, hinner]
  rw [← hq_def, hq, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
  rfl
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
  intro P n M x r hr f
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
      ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
    ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
  -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
  have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
    intro S
    have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
      rw [image_image, he]
      rfl
    rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
  have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
      Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
      e.image_preimage]
  -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
  rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]
/-- Continuity in the centre of the blow-up integrals of Simon Ch. 3, 1.4: for `f` continuous with
compact support, `r > 0` and `μ` finite on compact sets, `x ↦ ∫ f(η_{x,r}(y)) dμ(y)` is continuous,
`η_{x,r}(y) = r⁻¹(y − x)`.  With `‖f‖ ≤ C` and `tsupport f ⊆ B̄_R(0)`, the integrand vanishes for
`x ∈ B_1(x₀)` and `y ∉ B = B̄_{1+rR}(x₀)`; so near `x₀` it is dominated by `C·1_B`, integrable as
`μ(B) < ∞`, and dominated convergence gives continuity at `x₀`. -/
theorem Submission.continuous_integral_comp_blowUpMap : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun x : Euclid P => ∫ y, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μ) := by
  intro P μ hμ f hf hfs r hr
  -- `‖f‖ ≤ C` and `tsupport f ⊆ closedBall 0 R`
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  -- `(x, y) ↦ f (r⁻¹ • (y - x))` is jointly continuous
  have hF : Continuous fun p : Euclid P × Euclid P =>
      f (Poincare.SimonGMT.Chapter03.blowUpMap p.1 r p.2) :=
    hf.comp ((continuous_snd.sub continuous_fst).const_smul r⁻¹)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  -- dominated convergence with the bound `C · 1_B`, `B = closedBall x₀ (1 + r R)`
  refine continuousAt_of_dominated (bound := (closedBall x₀ (1 + r * R)).indicator fun _ => C)
    (Eventually.of_forall fun x => (hF.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    ?_ ?_ (Eventually.of_forall fun y => (hF.comp (Continuous.prodMk_left y)).continuousAt)
  · -- for `x ∈ ball x₀ 1`, `f (r⁻¹ • (y - x)) ≠ 0` forces `‖y - x‖ ≤ r R`, so `y ∈ B`
    filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ closedBall x₀ (1 + r * R)
    · rw [indicator_of_mem hy]
      exact hC _
    · rw [indicator_of_notMem hy]
      refine le_of_eq (norm_eq_zero.2 (by_contra fun h => hy ?_))
      have h1 := hR (subset_tsupport f h)
      rw [mem_closedBall, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_le_iff₀ hr, ← dist_eq_norm] at h1
      rw [mem_ball] at hx
      rw [mem_closedBall]
      linarith [dist_triangle y x x₀]
  · -- `C · 1_B` is integrable: `B` is compact, so `μ B < ∞`
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (hμ _ (isCompact_closedBall _ _))

/-- **Simon Ch. 3, 1.4**: if `Hⁿ(M ∩ K) < ∞` for every compact `K`, `f` is continuous with
compact support and `r > 0`, then the blow-up integral `x ↦ ∫_{η_{x,r}(M)} f dHⁿ` is continuous.
It equals `r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`, continuous in `x` because `Hⁿ⌞M` is finite on compact
sets. -/
theorem Submission.continuous_blowUp_image_setIntegral : ∀ (P n : ℕ) (M : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun x : Euclid P => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) := by
  intro P n M hM f hf hfs r hr
  -- `Hⁿ⌞M` is finite on compact sets: `(Hⁿ⌞M)(K) = Hⁿ(M ∩ K)`, `K` being closed
  have hμ : ∀ K : Set (Euclid P), IsCompact K → (μHE[n].restrict M) K ≠ ∞ := fun K hK => by
    rw [Measure.restrict_apply hK.isClosed.measurableSet, inter_comm]
    exact hM K hK
  -- change of variables, then continuity of `x ↦ r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`
  exact (continuous_const.mul
    (Submission.continuous_integral_comp_blowUpMap P _ hμ f hf hfs r hr)).congr fun x =>
      (Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul P n M x r hr f).symm
/-- A field of orthogonal projections `p_x = (K x).starProjection` is a.e.-measurable (Borel
σ-algebra of the operator-norm topology) when each quadratic form `x ↦ |p_x u|²` is.  As `p_x` is
self-adjoint and idempotent, `⟪p_x u, w⟫ = (|p_x(u + w)|² − |p_x(u − w)|²)/4`, so the matrix
coefficients `⟪p_x e_a, e_b⟫` are a.e.-measurable, and `p_x = Σ_{a,b} ⟪p_x e_a, e_b⟫ ⟪e_a, ·⟫ e_b`
is a continuous linear function of them. -/
theorem Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq : ∀ (P : ℕ) (μ : Measure (Euclid P)) (K : Euclid P → Submodule ℝ (Euclid P)), (∀ u : Euclid P, AEMeasurable (fun x => ‖(K x).starProjection u‖ ^ 2) μ) → AEMeasurable (fun x => (K x).starProjection) μ := by
  intro P μ K h
  -- by polarization every coefficient `x ↦ ⟪p_x u, w⟫` is a.e.-measurable
  have hcoef : ∀ u w : Euclid P,
      AEMeasurable (fun x => inner ℝ ((K x).starProjection u) w) μ := by
    intro u w
    have key : ∀ x, inner ℝ ((K x).starProjection u) w =
        (‖(K x).starProjection (u + w)‖ ^ 2 - ‖(K x).starProjection (u - w)‖ ^ 2) / 4 := by
      intro x
      have hsym : inner ℝ ((K x).starProjection u) w =
          inner ℝ ((K x).starProjection u) ((K x).starProjection w) := by
        rw [Submodule.inner_starProjection_left_eq_right,
          Submodule.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.2 ((K x).starProjection_apply_mem w)]
      rw [hsym, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
      ring
    simp_rw [key]
    exact ((h (u + w)).sub (h (u - w))).div_const 4
  -- `p_x = Λ (g x)`, `Λ m = ∑ m_{ab} ⟪e_a, ·⟫ e_b`, `g x = (⟪p_x e_a, e_b⟫)_{ab}`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let Λ : (Fin P × Fin P → ℝ) → (Euclid P →L[ℝ] Euclid P) := fun m =>
    ∑ ab, m ab • (innerSL ℝ (e ab.1)).smulRight (e ab.2)
  have heq : (fun x => (K x).starProjection) =
      fun x => Λ fun ab => inner ℝ ((K x).starProjection (e ab.1)) (e ab.2) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [Λ, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Fintype.sum_prod_type]
    calc (K x).starProjection v = (K x).starProjection (∑ a, inner ℝ (e a) v • e a) := by
          rw [e.sum_repr']
      _ = ∑ a, inner ℝ (e a) v • (K x).starProjection (e a) := by
          simp only [map_sum, map_smul]
      _ = ∑ a, inner ℝ (e a) v • ∑ b, inner ℝ (e b) ((K x).starProjection (e a)) • e b := by
          simp only [e.sum_repr']
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [real_inner_comm (e b), smul_smul, smul_smul, mul_comm]
  -- `Λ` is continuous and `g` is a.e.-measurable coordinatewise
  have hΛ : Continuous Λ :=
    continuous_finsetSum _ fun ab _ => (continuous_apply ab).smul continuous_const
  rw [heq]
  exact hΛ.measurable.comp_aemeasurable (AEMeasurable.of_eval fun ab => hcoef _ _)
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- **Simon Ch. 3, 1.4** (measurability of the approximate tangent planes): if `Hⁿ(M ∩ K) < ∞`
for every compact `K` and `Q(x)` is an approximate tangent space of `M` at `Hⁿ⌞M`-a.e. `x`, then
`x ↦ p_{Q(x)} = (Q x).starProjection` is `Hⁿ⌞M`-a.e. strongly measurable.  For `n = 0`,
`Q(x) = 0` a.e.  For `n ≥ 1` and `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²`, the blow-up integrals
`x ↦ ∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ` are continuous and tend a.e. to
`∫_{Q(x)} f_u dHⁿ = c|p_{Q(x)} u|²`, so every `x ↦ |p_{Q(x)} u|²` is a.e.-measurable, and hence
so is `x ↦ p_{Q(x)}`. -/
theorem Submission.cbr_ci_imc_tangent_field_aestronglyMeasurable : ∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) := by
  intro P n M Q hloc htan
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: `dim Q(x) = 0`, so `Q(x) = 0` and `p_{Q(x)} = 0` a.e.
    refine (aestronglyMeasurable_const (b := (0 : Euclid P →L[ℝ] Euclid P))).congr ?_
    filter_upwards [htan] with x hx
    have h0 : Q x = ⊥ := Submodule.finrank_eq_zero.1 hx.1
    rw [h0]
    ext v
    simp
  · -- `n ≥ 1`: `∫_{Q'} f_u dHⁿ = c|p_{Q'} u|²` for every `n`-plane `Q'`
    obtain ⟨c, hc, hmom⟩ := Submission.exists_plane_cutoff_quadratic_moment_eq n hn
    apply AEMeasurable.aestronglyMeasurable
    apply Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq
    intro u
    -- the test function `f_u ∈ C_c(ℝᴾ)`, vanishing outside the closed unit ball
    set f : Euclid P → ℝ := fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 with hf_def
    have hfc : Continuous f := by
      simp only [hf_def]
      fun_prop
    have hfs : HasCompactSupport f := by
      apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 1)
      intro y hy
      simp only [mem_closedBall, dist_zero_right, not_le] at hy
      have h1 : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg y]
      simp [hf_def, max_eq_right h1]
    let F : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨f, hfc⟩, hfs⟩
    -- the radii `r_k = 1/(k + 1) → 0⁺`
    let r : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hrpos : ∀ k, 0 < r k := fun k => by positivity
    have hr : Tendsto r atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hrpos⟩
    -- the blow-up integrals are continuous in `x`, hence measurable
    have hmeas : ∀ k, AEMeasurable (fun x => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (r k) '' M, f y ∂μHE[n]) (μHE[n].restrict M) := fun k =>
      (Submission.continuous_blowUp_image_setIntegral P n M hloc f hfc hfs (r k) (hrpos k)).measurable.aemeasurable
    -- and tend a.e. to `∫_{Q(x)} f_u dHⁿ = c|p_{Q(x)} u|²`
    have hlim : ∀ᵐ x ∂(μHE[n].restrict M), Tendsto (fun k => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (r k) '' M, f y ∂μHE[n]) atTop (𝓝 (c * ‖(Q x).starProjection u‖ ^ 2)) := by
      filter_upwards [htan] with x hx
      rw [← hmom P (Q x) hx.1 u]
      exact (hx.2 F).comp hr
    have h1 : AEMeasurable (fun x => c * ‖(Q x).starProjection u‖ ^ 2) (μHE[n].restrict M) :=
      aemeasurable_of_tendsto_metrizable_ae' hmeas hlim
    refine (h1.const_mul c⁻¹).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
/-- **Simon Ch. 6, 3.1** (integer multiplicity currents): if `Γ(ω) = ∫_M θ ⟨ω, ζ⟩ dHⁿ` with `M`
Borel and countably `n`-rectifiable, `θ > 0` on `M`, `∫_M θ dHⁿ < ∞`, and `Hⁿ`-a.e. on `M` the
density `θ` is an integer and `ζ` orients an approximate tangent space of `M`, then `Γ` is integer
multiplicity.  The bad set is `Hⁿ`-null; removing a measurable null hull `N₀` of it leaves a Borel
carrier `M'' = M \ N₀` on which everything holds pointwise, which has the approximate tangent
spaces of `M` (Ch. 3, 1.4) and `Hⁿ⌞M'' = Hⁿ⌞M`; the multiplicity is `⌊θ⌋₊` on `M''`. -/
theorem Submission.cbr_ci_imc_isIntegerMultiplicity_of_rectifiable : ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → CountablyRectifiable n M → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m) → IsIntegerMultiplicity Γ := by
  intro P n Γ M θ ζ hM hrect hθ hζ hpos hint hrep hae
  classical
  set p : Euclid P → Prop := fun x => ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m
  -- the bad set `{x ∈ M | ¬ p x}` is `Hⁿ`-null, and so is its measurable hull `N₀`
  have hbad : μHE[n] {x | x ∈ M ∧ ¬ p x} = 0 := by
    rw [ae_restrict_iff' hM, ae_iff] at hae
    simpa only [not_imp] using hae
  set N₀ := toMeasurable (μHE[n]) {x | x ∈ M ∧ ¬ p x} with hN₀_def
  have hN₀m : MeasurableSet N₀ := measurableSet_toMeasurable _ _
  have hN₀ : μHE[n] N₀ = 0 := by rw [hN₀_def, measure_toMeasurable]; exact hbad
  -- the carrier `M'' = M \ N₀` is Borel, `p` holds on all of it, and `M'' =ᵐ M`
  set M'' := M \ N₀
  have hM''m : MeasurableSet M'' := hM.diff hN₀m
  have hM''sub : M'' ⊆ M := Set.sdiff_subset
  have hgood : ∀ x ∈ M'', p x := by
    intro x hx
    by_contra h
    exact hx.2 (subset_toMeasurable _ _ ⟨hx.1, h⟩)
  have hdiff : μHE[n] (M \ M'') = 0 := by
    refine measure_mono_null (fun x hx => ?_) hN₀
    by_contra h
    exact hx.2 ⟨hx.1, h⟩
  have hdiff' : μHE[n] (M'' \ M) = 0 := by
    rw [Set.sdiff_eq_empty.2 hM''sub, measure_empty]
  -- the multiplicity `⌊θ⌋₊` on `M''`, which is `θ` there
  let mult : Euclid P → ℕ := fun x => if x ∈ M'' then ⌊θ x⌋₊ else 0
  have hmult_eq : ∀ x ∈ M'', (mult x : ℝ) = θ x := by
    intro x hx
    obtain ⟨Q, -, -, m, hm⟩ := hgood x hx
    simp [mult, hx, hm]
  have hmult_meas : Measurable mult :=
    Measurable.ite hM''m (Nat.floor_mono.measurable.comp hθ) measurable_const
  have hmult_pos : ∀ x ∈ M'', 0 < mult x := by
    intro x hx
    have h2 := hpos x (hM''sub hx)
    rw [← hmult_eq x hx] at h2
    exact_mod_cast h2
  have hmult_int : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in M'' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K _ _
    apply ne_of_lt
    calc ∫⁻ x in M'' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in M'', (mult x : ℝ≥0∞) ∂μHE[n] := lintegral_mono_set inter_subset_left
      _ = ∫⁻ x in M'', ENNReal.ofReal (θ x) ∂μHE[n] := by
        apply setLIntegral_congr_fun hM''m
        intro x hx
        simp only
        rw [← hmult_eq x hx, ENNReal.ofReal_natCast]
      _ ≤ ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] := lintegral_mono_set hM''sub
      _ < ∞ := hint
  -- `M` and `M''` have the same approximate tangent spaces (Ch. 3, 1.4)
  have horients : ∀ᵐ x ∂(μHE[n].restrict M''), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M'' x Q ∧ IsUnitOrientationOf (ζ x) Q := by
    rw [ae_restrict_iff' hM''m]
    refine Eventually.of_forall fun x hx => ?_
    obtain ⟨Q, hQ, hor, -⟩ := hgood x hx
    exact ⟨Q, (Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n M M'' x Q
      hdiff hdiff').1 hQ, hor⟩
  let R : IMRep (univ : Set (Euclid P)) n :=
    { carrier := M''
      mult := mult
      orient := ζ
      measurableSet_carrier := hM''m
      carrier_subset := subset_univ _
      rectifiable := hrect.mono hM''sub
      measurable_mult := hmult_meas
      mult_pos := hmult_pos
      locallyIntegrable_mult := hmult_int
      aestronglyMeasurable_orient := hζ.aestronglyMeasurable
      orients := horients }
  -- `R` represents `Γ`: `Hⁿ⌞M = Hⁿ⌞M''` and `mult = θ` on `M''`
  refine ⟨R, fun ω => ?_⟩
  rw [hrep ω]
  have hres : μHE[n].restrict M = μHE[n].restrict M'' :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨hdiff, hdiff'⟩)
  show _ = ∫ x in M'', (mult x : ℝ) * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
  rw [hres]
  refine setIntegral_congr_fun hM''m (fun x hx => ?_)
  simp only [hmult_eq x hx]

/-- **Integer multiplicity criterion** (Simon Ch. 6, 3.1, with Ch. 3, 1.4 and the rectifiability
criterion `(RECT)`, assumed as the first hypothesis).  Let `Γ(ω) = ∫_M θ⟨ω, ζ⟩ dHⁿ` with `M` Borel,
`Hⁿ(M) < ∞`, `θ > 0` on `M` and `∫_M θ dHⁿ < ∞`.  If at `Hⁿ`-a.e. `x ∈ M` the multiplicity `θ(x)` is
a natural number and `ζ(x)` orients an approximate tangent space of `M`, then `Γ` is integer
multiplicity.  At such `x` the plane `Tₓ = approxTangentPlane n M x` is an approximate tangent
space; `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞`, so `x ↦ p_{Tₓ}` is `Hⁿ⌞M`-a.e. strongly measurable and `(RECT)`
makes `M` countably `n`-rectifiable.  The representation is then assembled on a Borel part of `M`
of full measure. -/
theorem Submission.cbr_ci_isIntegerMultiplicity_of_ae_tangent : (∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), MeasurableSet M → μHE[n] M ≠ ∞ → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → CountablyRectifiable n M) → ∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → μHE[n] M < ∞ → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m) → IsIntegerMultiplicity Γ := by
  intro hRECT P n Γ M θ ζ hM hfin hθ hζ hpos hint hrep hae
  -- `Tₓ = approxTangentPlane n M x` is an approximate tangent space of `M` at a.e. `x ∈ M`
  have htan : ∀ᵐ x ∂(μHE[n].restrict M),
      HasApproximateTangentSpaceAt n M x (approxTangentPlane n M x) := by
    filter_upwards [hae] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have h : ∃ Q, HasApproximateTangentSpaceAt n M x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec
  -- `Hⁿ(M ∩ K) ≤ Hⁿ(M) < ∞`, so `x ↦ p_{Tₓ}` is a.e. strongly measurable and `(RECT)` applies
  have hloc : ∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞ := fun K _ =>
    ne_top_of_le_ne_top hfin.ne (measure_mono inter_subset_left)
  have hrect : CountablyRectifiable n M :=
    hRECT P n M (approxTangentPlane n M) hM hfin.ne
      (Submission.cbr_ci_imc_tangent_field_aestronglyMeasurable P n M _ hloc htan) htan
  -- assemble the integer multiplicity representation of `Γ` on the rectifiable `M`
  exact Submission.cbr_ci_imc_isIntegerMultiplicity_of_rectifiable P n Γ M θ ζ hM hrect hθ hζ
    hpos hint hrep hae
/-- **Simon, Ch. 1, proof of 2.10, final step** (p. 12): a centrally symmetric set `K ⊆ ℝᵈ`
(`x ∈ K → −x ∈ K`; no measurability or boundedness assumed) has `Lᵈ(K) ≤ ω_d (½ diam K)ᵈ`.
If `diam K = ∞` then `d ≥ 1` (`ℝ⁰` is a point) and the right-hand side is `∞`.  Otherwise
`2‖x‖ = |x − (−x)| ≤ diam K` for `x ∈ K`, so `K` lies in the closed ball of radius `½ diam K`
about `0`, whose measure is `(½ diam K)ᵈ ω_d` by the scaling of the Haar measure `Lᵈ`. -/
theorem Submission.cbr_ci_iso_volume_le_of_neg_mem : ∀ (d : ℕ) (K : Set (Euclid d)), (∀ x ∈ K, -x ∈ K) → volume K ≤ unitBallVolume d * (ediam K / 2) ^ d := by
  intro d K hK
  by_cases htop : ediam K = ∞
  · -- `diam K = ∞` forces `d ≥ 1` (`ℝ⁰` is a point), and then the right-hand side is `∞`
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact absurd (ediam_subsingleton Set.subsingleton_of_subsingleton) (htop ▸ ENNReal.top_ne_zero)
    · have hω : unitBallVolume d ≠ 0 := (measure_ball_pos volume (0 : Euclid d) one_pos).ne'
      rw [htop, ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top, ENNReal.top_pow hd.ne',
        ENNReal.mul_top hω]
      exact le_top
  · -- central symmetry: `2‖x‖ = dist(x, -x) ≤ diam K`, so `K ⊆ B̄(0, diam K / 2)`
    have hr : 0 ≤ diam K / 2 := div_nonneg diam_nonneg zero_le_two
    have hsub : K ⊆ closedBall (0 : Euclid d) (diam K / 2) := by
      intro x hx
      have h := dist_le_diam_of_mem' htop hx (hK x hx)
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ x, norm_smul, Real.norm_two] at h
      rw [mem_closedBall_zero_iff]
      linarith
    -- `Lᵈ(B̄(0, r)) = rᵈ ω_d` (`finrank ℝ ℝᵈ = d`) and `ofReal (diam K / 2) = ediam K / 2`
    have hball : volume (closedBall (0 : Euclid d) (diam K / 2)) =
        ENNReal.ofReal ((diam K / 2) ^ d) * unitBallVolume d := by
      rw [Measure.addHaar_closedBall volume _ hr, finrank_euclideanSpace_fin]
      rfl
    have hrad : ENNReal.ofReal ((diam K / 2) ^ d) = (ediam K / 2) ^ d := by
      rw [ENNReal.ofReal_pow hr, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat, diam,
        ENNReal.ofReal_toReal htop]
    calc volume K ≤ volume (closedBall (0 : Euclid d) (diam K / 2)) := measure_mono hsub
      _ = unitBallVolume d * (ediam K / 2) ^ d := by rw [hball, hrad, mul_comm]
/-- Reflection symmetries of the coordinate Steiner symmetrization (Simon, Ch. 1, proof of 2.10).
Write `y[i↦t]` for `y` with `i`-th coordinate replaced by `t`, `R_i(y) = y[i↦-y_i]`,
`A^j_y = {t : y[j↦t] ∈ A}` and `S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ L¹(A^j_y)/2}`.  Then (a) `S_j(A)`
is invariant under `R_j`, and (b) if `i ≠ j` and `A` is invariant under `R_i`, so is `S_j(A)`.
For (a), `R_j(y)[j↦t] = y[j↦t]`; for (b), `R_i(y)[j↦t] = R_i(y[j↦t])` and `R_i` is an involution,
so the `j`-slices of `y` and of its reflection agree, while `|(R_i y)_j| = |y_j|`. -/
theorem Submission.cbr_ci_iso_steiner_reflection : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), (∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp j (-x j)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}) ∧ ∀ i : Fin d, i ≠ j → (∀ x ∈ A, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ A) → ∀ x ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2}, WithLp.toLp 2 (Function.update x.ofLp i (-x i)) ∈ {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
  intro d j A
  refine ⟨fun x hx => ?_, fun i hij hA x hx => ?_⟩
  · -- (a) `R_j(x)[j↦t] = x[j↦t]`, so the `j`-slice is unchanged, and `|(R_j x)_j| = |x_j|`
    simpa using hx
  · -- (b) `R_i` is an involution and commutes with `y ↦ y[j↦t]`, so the `j`-slices of `x` and
    -- `R_i(x)` agree; moreover `(R_i x)_j = x_j` since `i ≠ j`
    have hR : ∀ z : Euclid d, WithLp.toLp 2 (update (WithLp.toLp 2 (update z.ofLp i (-z i))).ofLp i
        (-(WithLp.toLp 2 (update z.ofLp i (-z i))) i)) = z := by
      intro z
      ext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    have hcomm : ∀ t : ℝ, WithLp.toLp 2 (update (update x.ofLp i (-x i)) j t) =
        WithLp.toLp 2 (update (WithLp.toLp 2 (update x.ofLp j t)).ofLp i
          (-(WithLp.toLp 2 (update x.ofLp j t)) i)) := by
      intro t
      simp only [update_of_ne hij]
      rw [update_comm hij]
    have hslice : {t : ℝ | WithLp.toLp 2 (update (WithLp.toLp 2 (update x.ofLp i (-x i))).ofLp j t) ∈ A} =
        {t : ℝ | WithLp.toLp 2 (update x.ofLp j t) ∈ A} := by
      ext t
      simp only [Set.mem_ofPred_eq]
      rw [hcomm t]
      constructor
      · intro h
        have h' := hA _ h
        rwa [hR] at h'
      · exact hA _
    have hxj : (WithLp.toLp 2 (update x.ofLp i (-x i))) j = x j := by
      simp [hij.symm]
    show _ ∧ _
    rw [hslice, hxj]
    exact hx
/-- **Steiner symmetrization does not increase the diameter** (Simon 2.10, proof of the
isodiametric inequality).  For compact `A ⊆ ℝᵈ` and `j < d`, write `y[j↦t]` for `y` with its `j`-th
coordinate replaced by `t`, `A^j_y = {t : y[j↦t] ∈ A}`, `λ(y) = L¹(A^j_y)` and
`S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ λ(y)/2}`; then `ediam S_j(A) ≤ ediam A`.  Each slice `A^j_y` is
compact, so it contains `a_y = inf A^j_y` and `b_y = sup A^j_y`, and `λ(y) ≤ b_y - a_y`.  For
`x, y ∈ S_j(A)`, `|x_j - y_j| ≤ (λ(x) + λ(y))/2 ≤ max(b_y - a_x, b_x - a_y)`, and replacing the
`j`-th coordinates of `x, y` by the matching endpoints gives two points of `A` at distance at least
`|x - y|`. -/
theorem Submission.cbr_ci_iso_steiner_ediam_le : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → ediam {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} ≤ ediam A := by
  intro d j A hA
  -- (1) every slice `A^j_y` is compact: closed, and contained in the compact image of `A`
  -- under the `j`-th coordinate
  have hslice : ∀ y : Euclid d,
      IsCompact {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} := by
    intro y
    have hf : Continuous fun t : ℝ => WithLp.toLp 2 (Function.update y.ofLp j t) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_const.update j continuous_id)
    refine (hA.image (PiLp.continuous_apply 2 _ j)).of_isClosed_subset
      (hA.isClosed.preimage hf) fun t ht => ⟨_, ht, by simp⟩
  -- (2) a nonempty compact `P ⊆ ℝ` contains `inf P` and `sup P`, and `L¹(P) ≤ sup P - inf P`
  have hlen : ∀ P : Set ℝ, IsCompact P → P.Nonempty →
      sInf P ∈ P ∧ sSup P ∈ P ∧ (volume P).toReal ≤ sSup P - sInf P := by
    intro P hP hne
    refine ⟨hP.sInf_mem hne, hP.sSup_mem hne, ?_⟩
    refine ENNReal.toReal_le_of_le_ofReal
      (sub_nonneg.mpr (csInf_le_csSup hne hP.bddBelow hP.bddAbove)) ?_
    calc volume P ≤ volume (Icc (sInf P) (sSup P)) :=
          measure_mono fun t ht => ⟨csInf_le hP.bddBelow ht, le_csSup hP.bddAbove ht⟩
      _ = ENNReal.ofReal (sSup P - sInf P) := Real.volume_Icc
  -- (3) two-point estimate: replacing the `j`-th coordinates by `a, b` with
  -- `|x_j - y_j| ≤ |a - b|` does not decrease the distance
  have hpt : ∀ (x y : Euclid d) (a b : ℝ), WithLp.toLp 2 (Function.update x.ofLp j a) ∈ A →
      WithLp.toLp 2 (Function.update y.ofLp j b) ∈ A → |x j - y j| ≤ |a - b| →
      edist x y ≤ ediam A := by
    intro x y a b ha hb hab
    refine le_trans ?_ (edist_le_ediam_of_mem ha hb)
    rw [edist_dist, edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self, Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    · simp only [Function.update_of_ne hi, le_refl]
  -- (4) for `x, y ∈ S_j(A)`, `|x_j - y_j| ≤ (λ(x) + λ(y))/2` is realised by a pair of points of `A`
  refine ediam_le ?_
  rintro x ⟨hxne, hxj⟩ y ⟨hyne, hyj⟩
  obtain ⟨hax, hbx, hlx⟩ := hlen _ (hslice x) hxne
  obtain ⟨hay, hby, hly⟩ := hlen _ (hslice y) hyne
  have hx := abs_le.mp hxj
  have hy := abs_le.mp hyj
  rcases le_total
      (sSup {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A} -
        sInf {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A})
      (sSup {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} -
        sInf {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A}) with h | h
  · refine hpt x y _ _ hax hby ?_
    rw [abs_sub_comm _ (sSup _)]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self _)
  · refine hpt x y _ _ hbx hay ?_
    exact (abs_le.mpr ⟨by linarith, by linarith⟩).trans (le_abs_self _)
/-- **Simon, Ch. 1, Note after the proof of 2.10** (p. 12): for compact `A ⊆ ℝᵈ` and a coordinate
`j`, the length `y ↦ L¹{t : y[j ↦ t] ∈ A}` of the slice of `A` along the `j`-th coordinate line
through `y` is upper semicontinuous.  Every slice lies in `[-R, R]` (`A ⊆ B_R(0)`), so has finite
length.  Given `L¹(A^j_x) < r`, outer regularity gives an open `U ⊇ A^j_x` with `L¹(U) < r`; the
compact set `C = A ∖ {z : z_j ∈ U}` has closed image under `π z = z[j ↦ 0]`, `π x ∉ π(C)`, and for
`y` in the neighbourhood `π⁻¹(π(C)ᶜ)` of `x` the slice `A^j_y` lies in `U`, so `L¹(A^j_y) < r`. -/
theorem Submission.cbr_ci_iso_slice_length_usc : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → UpperSemicontinuous (fun y : Euclid d => (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal) := by
  intro d j A hA
  -- every slice lies in `[-R, R]`, so it has finite length
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall (0 : Euclid d)
  have hfin : ∀ y : Euclid d,
      volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} ≠ ∞ := by
    intro y
    refine ne_top_of_le_ne_top (measure_Icc_lt_top (a := -R) (b := R)).ne (measure_mono ?_)
    intro t ht
    have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Function.update y.ofLp j t) : Euclid d) j
    rw [WithLp.ofLp_toLp, Function.update_self, Real.norm_eq_abs] at h1
    exact abs_le.mp (h1.trans (mem_closedBall_zero_iff.mp (hR ht)))
  refine upperSemicontinuous_iff.mpr fun x => upperSemicontinuousAt_iff.mpr fun r hr => ?_
  -- outer regularity: an open `U` around the slice through `x` with `L¹(U) < r`
  obtain ⟨U, hxU, hUo, hUr⟩ := Set.exists_isOpen_lt_of_lt
    {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp j t) ∈ A} (ENNReal.ofReal r)
    ((ENNReal.lt_ofReal_iff_toReal_lt (hfin x)).mpr hr)
  -- the projection `z ↦ z[j ↦ 0]` and the compact part of `A` off `{z : z_j ∈ U}`
  let proj : Euclid d → Euclid d := fun z => WithLp.toLp 2 (Function.update z.ofLp j 0)
  have hproj : Continuous proj :=
    (PiLp.continuous_toLp 2 _).comp
      ((continuous_update j).comp ((PiLp.continuous_ofLp 2 _).prodMk continuous_const))
  have hC : IsCompact (A \ {z : Euclid d | z.ofLp j ∈ U}) :=
    hA.diff (hUo.preimage (PiLp.continuous_apply 2 _ j))
  -- `π x ∉ π(C)`: a point of `C` over `π x` would put its `j`-th coordinate in the slice at `x`
  have hx : proj x ∉ proj '' (A \ {z : Euclid d | z.ofLp j ∈ U}) := by
    rintro ⟨z, ⟨hzA, hzU⟩, hzx⟩
    have h : Function.update z.ofLp j 0 = Function.update x.ofLp j 0 := by
      simpa only [proj, WithLp.ofLp_toLp] using congrArg WithLp.ofLp hzx
    have hz : WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j)) = z := by
      calc WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j))
          = WithLp.toLp 2 (Function.update (Function.update x.ofLp j 0) j (z.ofLp j)) := by
            rw [Function.update_idem]
        _ = z := by rw [← h, Function.update_idem, Function.update_eq_self, WithLp.toLp_ofLp]
    exact hzU (hxU (show WithLp.toLp 2 (Function.update x.ofLp j (z.ofLp j)) ∈ A by
      rw [hz]; exact hzA))
  -- on the neighbourhood `π⁻¹(π(C)ᶜ)` of `x` every slice lies in `U`
  filter_upwards [((hC.image hproj).isClosed.isOpen_compl.preimage hproj).mem_nhds hx] with y hy
  have hy' : proj y ∉ proj '' (A \ {z : Euclid d | z.ofLp j ∈ U}) := hy
  have hyU : {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} ⊆ U := by
    intro t ht
    by_contra htU
    refine hy' ⟨WithLp.toLp 2 (Function.update y.ofLp j t), ⟨ht, ?_⟩, ?_⟩
    · show (WithLp.toLp 2 (Function.update y.ofLp j t)).ofLp j ∉ U
      rwa [WithLp.ofLp_toLp, Function.update_self]
    · simp only [proj, Function.update_idem]
  exact ENNReal.toReal_lt_of_lt_ofReal ((measure_mono hyU).trans_lt hUr)
/-- **Steiner symmetrization of a compact set is compact** (Simon Ch. 1, the Note after the proof
of 2.10: `S_j(A)` is compact because the slice length is upper semicontinuous).  Let `A ⊆ ℝ^d` be
compact, `A^j_y = {t : y[j ↦ t] ∈ A}` and `λ(y) = L¹(A^j_y)`.  If `λ` is upper semicontinuous,
then `S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ λ(y)/2}` is compact: `{y : A^j_y ≠ ∅} = π⁻¹(π(A))` for
`π z = z[j ↦ 0]`, `{y : |y_j| ≤ λ(y)/2}` is a superlevel set of the upper semicontinuous
`λ − 2|y_j|`, and `S_j(A) ⊆ closedBall(0, 3R)` whenever `A ⊆ closedBall(0, R)`. -/
theorem Submission.cbr_ci_iso_steiner_isCompact : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → UpperSemicontinuous (fun y : Euclid d => (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal) → IsCompact {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
  intro d j A hA hlen
  -- Step 1: `π z = z[j ↦ 0]` is continuous, and `π z = π y` forces `y[j ↦ z_j] = z`
  let π : Euclid d → Euclid d := fun z => WithLp.toLp 2 (Function.update z.ofLp j 0)
  have hπ : Continuous π :=
    (PiLp.continuous_toLp 2 _).comp ((PiLp.continuous_ofLp 2 _).update j continuous_const)
  have hπ_eq : ∀ y z : Euclid d, π z = π y →
      WithLp.toLp 2 (Function.update y.ofLp j (z j)) = z := by
    intro y z h
    ext i
    by_cases hi : i = j
    · subst hi
      simp
    · have := congrArg (fun w : Euclid d => w i) h
      simp only [π, Function.update_of_ne hi] at this ⊢
      exact this.symm
  -- Step 2: `{y : A^j_y ≠ ∅} = π⁻¹(π(A))` is closed, `π(A)` being compact
  have hN : IsClosed
      {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty} := by
    convert (hA.image hπ).isClosed.preimage hπ using 1
    ext y
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨_, ht, by simp [π]⟩
    · rintro ⟨z, hz, h⟩
      exact ⟨z j, by rw [mem_ofPred_eq, hπ_eq y z h]; exact hz⟩
  -- Step 3: `{y : 0 ≤ λ(y) − 2|y_j|}` is closed, `λ − 2|y_j|` being upper semicontinuous
  have hM : IsClosed {y : Euclid d | 0 ≤
      (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal + -(2 * |y j|)} :=
    (hlen.add ((PiLp.continuous_apply 2 _ j).abs.const_mul 2).neg.upperSemicontinuous)
      |>.isClosed_preimage 0
  -- Step 4: `S_j(A)` is the intersection of these two closed sets
  have hS : IsClosed {y : Euclid d |
      {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧
        |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} := by
    convert hN.inter hM using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr Iff.rfl ⟨fun h => by linarith, fun h => by linarith⟩
  -- Step 5: `S_j(A) ⊆ closedBall(0, 3R)` when `A ⊆ closedBall(0, R)`
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded hS
    ((isBounded_closedBall (x := (0 : Euclid d)) (r := 3 * R)).subset ?_)
  rintro y ⟨⟨t, ht⟩, hy⟩
  rw [mem_closedBall_zero_iff]
  -- every `s ∈ A^j_y` has `|s| ≤ ‖y[j ↦ s]‖ ≤ R`
  have hnorm : ∀ s : ℝ, WithLp.toLp 2 (Function.update y.ofLp j s) ∈ A → |s| ≤ R := by
    intro s hs
    have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Function.update y.ofLp j s)) j
    have h2 := mem_closedBall_zero_iff.1 (hR hs)
    simp only [Function.update_self, Real.norm_eq_abs] at h1
    linarith
  -- hence `A^j_y ⊆ [−R, R]` and `λ(y) ≤ 2R`
  have hR0 : 0 ≤ R := (abs_nonneg t).trans (hnorm t ht)
  have hvol : (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal ≤ 2 * R := by
    refine ENNReal.toReal_le_of_le_ofReal (by linarith) ?_
    calc volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}
        ≤ volume (Icc (-R) R) := measure_mono fun s hs => abs_le.1 (hnorm s hs)
      _ = ENNReal.ofReal (2 * R) := by rw [Real.volume_Icc]; ring_nf
  -- `y − y[j ↦ t] = (y_j − t) e_j`
  have hdiff : ‖y - WithLp.toLp 2 (Function.update y.ofLp j t)‖ = |y j - t| := by
    have : y - WithLp.toLp 2 (Function.update y.ofLp j t) = EuclideanSpace.single j (y j - t) := by
      ext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [hi]
    rw [this, PiLp.norm_single, Real.norm_eq_abs]
  have hz : ‖WithLp.toLp 2 (Function.update y.ofLp j t)‖ ≤ R := mem_closedBall_zero_iff.1 (hR ht)
  -- Step 6: `‖y‖ ≤ ‖y[j ↦ t]‖ + |y_j − t| ≤ R + |y_j| + |t| ≤ 3R`, using `|y_j| ≤ λ(y)/2 ≤ R`
  calc ‖y‖ = ‖WithLp.toLp 2 (Function.update y.ofLp j t) +
        (y - WithLp.toLp 2 (Function.update y.ofLp j t))‖ := by rw [add_sub_cancel]
    _ ≤ ‖WithLp.toLp 2 (Function.update y.ofLp j t)‖ +
        ‖y - WithLp.toLp 2 (Function.update y.ofLp j t)‖ := norm_add_le _ _
    _ ≤ R + (|y j| + |t|) := by
        rw [hdiff]
        gcongr
        exact abs_sub _ _
    _ ≤ 3 * R := by linarith [hnorm t ht]
/-- **Cavalieri's principle along a coordinate direction** (Simon Ch. 1, proof of 2.10: Steiner
symmetrization keeps Lebesgue measure "by Fubini").  If measurable `S, A ⊆ ℝᵈ` have line slices
`{t : y[j↦t] ∈ S}`, `{t : y[j↦t] ∈ A}` of equal `L¹`-measure through every `y`, then
`Lᵈ(S) = Lᵈ(A)`.  With `d = n + 1`, `φ(t, z) = Fin.insertNth j t z` is measure preserving from
`L¹ ⊗ Lⁿ` to `Lᵈ`; its fibre over `z` is the slice through `φ(0, z)`, and Tonelli
(`Measure.prod_apply_symm`) integrates the equal slice measures over `z`. -/
theorem Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq : ∀ (d : ℕ) (j : Fin d) (S A : Set (Euclid d)), MeasurableSet S → MeasurableSet A → (∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ S} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}) → volume S = volume A := by
  intro d j S A hS hA hslice
  cases d with
  | zero => exact Fin.elim0 j
  | succ n =>
    -- `φ(t, z) = Fin.insertNth j t z`, measure preserving from `L¹ ⊗ Lⁿ` to `Lᵈ`
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    let φ : ℝ × (Fin n → ℝ) → Euclid (n + 1) := fun p => WithLp.toLp 2 (e.symm p)
    have hφ : MeasurePreserving φ volume volume :=
      (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
        (MeasurePreserving.symm e (volume_preserving_piFinSuccAbove _ j))
    -- the fibre of `φ` over `z` is the coordinate slice through `φ(0, z)`
    have hfibre (B : Set (Euclid (n + 1))) (z : Fin n → ℝ) :
        (fun t => φ (t, z)) ⁻¹' B =
          {t : ℝ | WithLp.toLp 2 (Function.update (φ (0, z)).ofLp j t) ∈ B} := by
      ext t
      change WithLp.toLp 2 (j.insertNth t z) ∈ B ↔
        WithLp.toLp 2 (Function.update (j.insertNth 0 z) j t) ∈ B
      rw [Fin.update_insertNth]
    -- Tonelli: `Lᵈ(B) = (L¹ ⊗ Lⁿ)(φ⁻¹ B) = ∫⁻ z, L¹(fibre of φ⁻¹ B over z)`
    have hvol (B : Set (Euclid (n + 1))) (hB : MeasurableSet B) :
        volume B = ∫⁻ z : Fin n → ℝ, volume ((fun t => φ (t, z)) ⁻¹' B) :=
      (hφ.measure_preimage hB.nullMeasurableSet).symm.trans
        (Measure.prod_apply_symm (hB.preimage hφ.measurable))
    rw [hvol S hS, hvol A hA]
    refine lintegral_congr fun z => ?_
    rw [hfibre S z, hfibre A z]
    exact hslice (φ (0, z))
/-- Steiner symmetrization in direction `j` keeps the length of every line slice: for compact
`A ⊆ ℝᵈ` and `y ∈ ℝᵈ`, `L¹{t | y[j↦t] ∈ S_j(A)} = L¹(B)` with `B = {t | y[j↦t] ∈ A}`.  Each
point `y[j↦t]` of the line has `j`-th coordinate `t` and slice `B`, so the left set is
`{t | B ≠ ∅ ∧ |t| ≤ ℓ/2}`, `ℓ = L¹(B)`.  It is empty if `B = ∅` and `[-ℓ/2, ℓ/2]` otherwise, of
length `ℓ`, which is finite because `B` lies in the compact projection `π_j(A)`. -/
theorem Submission.cbr_ci_iso_svol_steiner_slice_volume_eq : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → ∀ y : Euclid d, volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ {x : Euclid d | {s : ℝ | WithLp.toLp 2 (Function.update x.ofLp j s) ∈ A}.Nonempty ∧ |x j| ≤ (volume {s : ℝ | WithLp.toLp 2 (Function.update x.ofLp j s) ∈ A}).toReal / 2}} = volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A} := by
  intro d j A hA y
  -- `B = A^j_y = {s | y[j↦s] ∈ A}`
  obtain ⟨B, hB⟩ : ∃ B : Set ℝ, {s : ℝ | WithLp.toLp 2 (update y.ofLp j s) ∈ A} = B :=
    ⟨_, rfl⟩
  -- steps 1–2: `(y[j↦t])_j = t` and `(y[j↦t])[j↦s] = y[j↦s]` (`WithLp.ofLp_toLp` is `rfl`), so
  -- `A^j_{y[j↦t]} = B` and the left set is `{t | B ≠ ∅ ∧ |t| ≤ ℓ/2}`, `ℓ = (L¹ B).toReal`
  simp only [mem_ofPred_eq, update_idem, update_self, hB]
  -- step 3: `B ⊆ π_j(A)`, which is compact, so `L¹(B) < ∞`
  have hBfin : volume B ≠ ∞ := by
    have hπ : IsCompact ((fun x : Euclid d => x j) '' A) := hA.image (PiLp.continuous_apply 2 _ j)
    refine (measure_lt_top_of_subset ?_ hπ.measure_lt_top.ne).ne
    rintro s hs
    rw [← hB] at hs
    exact ⟨_, hs, update_self j s y.ofLp⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  -- step 4: if `B = ∅`, the left set is empty
  · simp only [Set.not_nonempty_empty, false_and, ofPred_false]
  -- step 5: otherwise it is `[-ℓ/2, ℓ/2]`, of measure `ofReal ℓ = L¹(B)`
  · have hIcc : {t : ℝ | B.Nonempty ∧ |t| ≤ (volume B).toReal / 2} =
        Icc (-((volume B).toReal / 2)) ((volume B).toReal / 2) := by
      ext t
      rw [mem_ofPred_eq, mem_Icc, ← abs_le, and_iff_right hBne]
    rw [hIcc, Real.volume_Icc, sub_neg_eq_add, add_halves, ENNReal.ofReal_toReal hBfin]

/-- **Simon Ch. 1, proof of 2.10 (p. 12): Steiner symmetrization preserves Lebesgue measure.**
Let `A ⊆ ℝ^d` be compact, `j ∈ Fin d`, `A^j_y = {t : y[j↦t] ∈ A}`.  If the Steiner symmetral
`S_j(A) = {y : A^j_y ≠ ∅, |y_j| ≤ ½ L¹(A^j_y)}` is measurable, then `L^d(S_j(A)) = L^d(A)`, "by
Fubini": each line in direction `e_j` meets `S_j(A)` in `∅` or a centred segment of length
`L¹(A^j_y)`, hence in a set of the same `L¹`-measure as its trace on the measurable set `A`, and
Cavalieri's principle along `e_j` compares the volumes. -/
theorem Submission.cbr_ci_iso_steiner_volume_eq : ∀ (d : ℕ) (j : Fin d) (A : Set (Euclid d)), IsCompact A → MeasurableSet {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} → volume {y : Euclid d | {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}.Nonempty ∧ |y j| ≤ (volume {t : ℝ | WithLp.toLp 2 (Function.update y.ofLp j t) ∈ A}).toReal / 2} = volume A := by
  intro d j A hA hS
  exact Submission.cbr_ci_iso_svol_volume_eq_of_slice_volume_eq d j _ A hS hA.measurableSet
    (Submission.cbr_ci_iso_svol_steiner_slice_volume_eq d j A hA)
/-- Iterated coordinate Steiner symmetrization (Simon, Ch. 1, proof of 2.10): every compact
`A ⊆ ℝ^d` has a compact replacement `K` with `L^d(K) = L^d(A)`, `ediam K ≤ ediam A` and `-x ∈ K`
for all `x ∈ K`.  Write `y[i↦t]` for `y` with `i`-th coordinate replaced by `t`,
`R_k(y) = y[k↦-y_k]`, `B^i_y = {t : y[i↦t] ∈ B}`, `S_i(B) = {y : B^i_y ≠ ∅, |y_i| ≤ L¹(B^i_y)/2}`.
By induction over finite `F ⊆ Fin d` there is a compact `K_F` with the measure of `A`, diameter at
most `ediam A` and `R_k(K_F) ⊆ K_F` for `k ∈ F`: for `i ∉ F`, `S_i(K_F)` is compact, has the same
measure and no larger diameter (sibling lemmas), is `R_i`-invariant since `R_i(y)[i↦t] = y[i↦t]`,
and stays `R_k`-invariant for `k ∈ F` since `R_k(y)[i↦t] = R_k(y[i↦t])` and `R_k` is an involution.
For `K = K_{Fin d}`, flipping the coordinates of `x ∈ K` one at a time shows `-x ∈ K`. -/
theorem Submission.cbr_ci_iso_exists_symmetric_replacement : ∀ (d : ℕ) (A : Set (Euclid d)), IsCompact A → ∃ K : Set (Euclid d), IsCompact K ∧ volume K = volume A ∧ ediam K ≤ ediam A ∧ ∀ x ∈ K, -x ∈ K := by
  intro d A hA
  -- Step 1: for every finite set `F` of coordinates there is a compact `K_F` with the measure of
  -- `A`, diameter at most `ediam A`, and invariant under `R_k` for every `k ∈ F`
  have hF : ∀ F : Finset (Fin d), ∃ K : Set (Euclid d), IsCompact K ∧ volume K = volume A ∧
      ediam K ≤ ediam A ∧
      ∀ k ∈ F, ∀ x ∈ K, WithLp.toLp 2 (Function.update x.ofLp k (-x k)) ∈ K := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨A, hA, rfl, le_rfl, by simp⟩
    | insert i F hi ih =>
      -- replace `K' = K_F` by its Steiner symmetrization `S_i(K')` in the new direction `i`
      obtain ⟨K', hK', hvol', hdiam', hsym'⟩ := ih
      have hS := Submission.cbr_ci_iso_steiner_isCompact d i K' hK'
        (Submission.cbr_ci_iso_slice_length_usc d i K' hK')
      refine ⟨_, hS,
        (Submission.cbr_ci_iso_steiner_volume_eq d i K' hK' hS.measurableSet).trans hvol',
        (Submission.cbr_ci_iso_steiner_ediam_le d i K' hK').trans hdiam', fun k hk x hx => ?_⟩
      rcases Finset.mem_insert.1 hk with rfl | hkF
      · -- `R_k(x)[k↦t] = x[k↦t]`, so the `k`-slice is unchanged, and `|(R_k x)_k| = |x_k|`
        simpa using hx
      · -- `k ≠ i`: `R_k` is an involution preserving `K'` with `R_k(x)[i↦t] = R_k(x[i↦t])`, so
        -- `x` and `R_k(x)` have the same `i`-slice of `K'`, and `(R_k x)_i = x_i`
        have hki : k ≠ i := by
          rintro rfl
          exact hi hkF
        have hR := hsym' k hkF
        have hinv : ∀ z : Euclid d, WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update z.ofLp k (-z k))).ofLp k
            (-(WithLp.toLp 2 (Function.update z.ofLp k (-z k))) k)) = z := by
          intro z
          ext m
          by_cases hm : m = k
          · subst hm
            simp
          · simp [hm]
        have hcomm : ∀ t : ℝ,
            WithLp.toLp 2 (Function.update (Function.update x.ofLp k (-x k)) i t) =
              WithLp.toLp 2 (Function.update (WithLp.toLp 2 (Function.update x.ofLp i t)).ofLp k
                (-(WithLp.toLp 2 (Function.update x.ofLp i t)) k)) := by
          intro t
          simp only [Function.update_of_ne hki]
          rw [Function.update_comm hki]
        have hslice : {t : ℝ | WithLp.toLp 2 (Function.update
            (WithLp.toLp 2 (Function.update x.ofLp k (-x k))).ofLp i t) ∈ K'} =
            {t : ℝ | WithLp.toLp 2 (Function.update x.ofLp i t) ∈ K'} := by
          ext t
          simp only [Set.mem_ofPred_eq]
          rw [hcomm t]
          constructor
          · intro h
            have h' := hR _ h
            rwa [hinv] at h'
          · exact hR _
        have hxi : (WithLp.toLp 2 (Function.update x.ofLp k (-x k))) i = x i := by
          simp [hki.symm]
        show _ ∧ _
        rw [hslice, hxi]
        exact hx
  -- Step 4: `K = K_{Fin d}` is invariant under every coordinate reflection
  obtain ⟨K, hK, hvol, hdiam, hsym⟩ := hF Finset.univ
  refine ⟨K, hK, hvol, hdiam, fun x hx => ?_⟩
  -- Step 5: `x^G ∈ K` for every finite `G`, where `x^G` flips the coordinates of `x` in `G`
  have hG : ∀ G : Finset (Fin d), WithLp.toLp 2 (fun k => if k ∈ G then -x k else x k) ∈ K := by
    intro G
    induction G using Finset.induction_on with
    | empty => simpa using hx
    | insert i G hi ih =>
      -- `x^{insert i G} = R_i(x^G)` because `i ∉ G`
      convert hsym i (Finset.mem_univ i) _ ih using 1
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hi]
      · simp [hk]
  -- `x^{Fin d} = -x`
  convert hG Finset.univ using 1
  ext k
  simp

/-- **Simon 2.10** (isodiametric inequality, Ch. 1, p. 11): `Lᵈ(A) ≤ ω_d (diam A / 2)ᵈ` for every
`A ⊆ ℝᵈ`.  If `ediam A = ∞` then `d ≠ 0` (subsets of `ℝ⁰` are subsingletons) and the right side is
`ω_d · ∞ = ∞`, as `ω_d > 0`.  Otherwise the closure `Ā` is compact, `ediam Ā = ediam A` and
`Lᵈ(A) ≤ Lᵈ(Ā)`; a centrally symmetric compact `K` with `Lᵈ(K) = Lᵈ(Ā)` and `ediam K ≤ ediam Ā`
satisfies the bound, and the bound is monotone in the diameter. -/
theorem Submission.cbr_ci_iso_volume_le_ediam_pow : ∀ (d : ℕ) (A : Set (Euclid d)), volume A ≤ unitBallVolume d * (ediam A / 2) ^ d := by
  intro d A
  by_cases hA : ediam A = ⊤
  · -- unbounded `A`: then `d ≠ 0`, and the right side is `ω_d · ∞ = ∞`
    have hd : d ≠ 0 := by
      rintro rfl
      exact ENNReal.zero_ne_top ((ediam_subsingleton Set.subsingleton_of_subsingleton).symm.trans hA)
    have hω : unitBallVolume d ≠ 0 := (measure_ball_pos volume (0 : Euclid d) one_pos).ne'
    have h2 : ediam A / 2 = ⊤ := by
      rw [hA]
      exact ENNReal.top_div_of_ne_top ENNReal.ofNat_ne_top
    rw [h2, ENNReal.top_pow hd, ENNReal.mul_top hω]
    exact le_top
  · -- bounded `A`: pass to the compact closure, then to a centrally symmetric replacement
    have hc : IsCompact (closure A) := (isBounded_iff_ediam_ne_top.2 hA).isCompact_closure
    obtain ⟨K, -, hKA, hKd, hKs⟩ :=
      Submission.cbr_ci_iso_exists_symmetric_replacement d (closure A) hc
    rw [ediam_closure] at hKd
    calc volume A ≤ volume (closure A) := measure_mono subset_closure
      _ = volume K := hKA.symm
      _ ≤ unitBallVolume d * (ediam K / 2) ^ d := Submission.cbr_ci_iso_volume_le_of_neg_mem d K hKs
      _ ≤ unitBallVolume d * (ediam A / 2) ^ d := by gcongr

/-- Lebesgue measure on `ℝ^d` is at most `(ω_d / 2^d) • μH[d]` (Simon Ch. 1, "Completion of the
proof of 2.9", pp. 12–13, in Mathlib's unnormalised `μH[d]`, whose weight is `diam^d`).  Put
`c = ω_d / 2^d`; `c ≠ 0, ∞` since `0 < ω_d < ∞`.  The isodiametric inequality
`L^d(s) ≤ ω_d (diam s / 2)^d = c · diam(s)^d` gives `c⁻¹ L^d(s) ≤ diam(s)^d` for every `s`, so
`c⁻¹ • L^d ≤ μH[d]` (`Measure.le_hausdorffMeasure`: cover by sets `C_k` of small diameter,
`c⁻¹ L^d(B) ≤ Σ c⁻¹ L^d(C_k) ≤ Σ diam(C_k)^d`).  Multiplying back by `c` gives
`L^d ≤ c • μH[d]` setwise. -/
theorem Submission.cbr_ci_iso_volume_le_smul_hausdorff : ∀ (d : ℕ), (volume : Measure (Euclid d)) ≤ (unitBallVolume d / 2 ^ d) • (μH[(d : ℝ)] : Measure (Euclid d)) := by
  intro d
  -- Step 1: `c = ω_d / 2^d` is neither `0` nor `∞`
  set c : ℝ≥0∞ := unitBallVolume d / 2 ^ d with hc
  have hω0 : unitBallVolume d ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : Euclid d) one_pos).ne'
  have hωtop : unitBallVolume d ≠ ∞ := measure_ball_lt_top.ne
  have hc0 : c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hω0, ENNReal.pow_ne_top ENNReal.ofNat_ne_top⟩
  have hctop : c ≠ ∞ := ENNReal.div_ne_top hωtop (pow_ne_zero d two_ne_zero)
  -- Step 2: the isodiametric inequality gives `c⁻¹ L^d(s) ≤ diam(s)^d` for every `s`
  have hdiam : ∀ s : Set (Euclid d), c⁻¹ * volume s ≤ ediam s ^ d := by
    intro s
    have hiso : volume s ≤ c * ediam s ^ d :=
      calc volume s ≤ unitBallVolume d * (ediam s / 2) ^ d :=
            Submission.cbr_ci_iso_volume_le_ediam_pow d s
        _ = c * ediam s ^ d := by
            rw [hc, div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
            ring
    calc c⁻¹ * volume s ≤ c⁻¹ * (c * ediam s ^ d) := by gcongr
      _ = ediam s ^ d := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  -- Step 3: `ν = c⁻¹ • L^d ≤ μH[d]`; the bound is needed only for sets of diameter `≤ 1`
  have hν : c⁻¹ • (volume : Measure (Euclid d)) ≤ μH[(d : ℝ)] := by
    refine Measure.le_hausdorffMeasure (d : ℝ) _ 1 one_pos fun s _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast]
    exact hdiam s
  -- Step 4: `L^d(s) = c · ν(s) ≤ c · μH[d](s)` for every set `s`
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  calc volume s = c * (c⁻¹ * volume s) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
    _ ≤ c * μH[(d : ℝ)] s := by
        gcongr
        simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff'.1 hν s

/-- `Hⁿ = μHE[n]` is dominated by Simon's normalisation `ωₙ (diam/2)ⁿ` (Simon, Ch. 1, 2.1–2.2 and
the completion of the proof of 2.9): `μHE[n] ≤ (ωₙ/2ⁿ) • μH[n]` on every `ℝᴾ`.  By definition
`μHE[n] = c • μH[n]` with `c = addHaarScalarFactor volume μH[n]` on `ℝⁿ`, so `volume = c • μH[n]`
on `ℝⁿ`.  On the unit cube `K` of `ℝⁿ`, `volume K = 1` gives `c · μH[n](K) = 1`, which forces
`0 < μH[n](K) < ∞`; with `volume K ≤ (ωₙ/2ⁿ) μH[n](K)` (isodiametric inequality) this gives
`c ≤ ωₙ/2ⁿ`, whence `μHE[n](s) = c · μH[n](s) ≤ (ωₙ/2ⁿ) μH[n](s)` for every `s ⊆ ℝᴾ`. -/
theorem Submission.cbr_ci_euclideanHausdorff_le_isodiametric : ∀ (P n : ℕ), (μHE[n] : Measure (Euclid P)) ≤ (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid P)) := by
  intro P n
  -- `c` is the constant with `μHE[n] = c • μH[n]` on every space, so `volume = c • μH[n]` on `ℝⁿ`
  obtain ⟨c, hc⟩ : ∃ c : NNReal,
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)] = c :=
    ⟨_, rfl⟩
  have hvol : (volume : Measure (Euclid n)) = c • (μH[(n : ℝ)] : Measure (Euclid n)) := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_def,
      hc]
  -- `volume ≤ (ωₙ/2ⁿ) • μH[n]` on `ℝⁿ` (isodiametric inequality, completion of the proof of 2.9)
  have hiso : (volume : Measure (Euclid n)) ≤
      (unitBallVolume n / 2 ^ n) • (μH[(n : ℝ)] : Measure (Euclid n)) :=
    Submission.cbr_ci_iso_volume_le_smul_hausdorff n
  -- the unit cube `K` of `ℝⁿ` has `volume K = 1`, so `c · μH[n](K) = 1` and `0 < μH[n](K) < ∞`
  set K : Set (Euclid n) := parallelepiped (stdOrthonormalBasis ℝ (Euclid n))
  have hK : (c : ℝ≥0∞) * μH[(n : ℝ)] K = 1 := by
    rw [← Measure.coe_nnreal_smul_apply, ← hvol]
    exact (stdOrthonormalBasis ℝ (Euclid n)).volume_parallelepiped
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hK
    exact zero_ne_one hK
  have hK0 : μH[(n : ℝ)] K ≠ 0 := by
    intro h
    rw [h, mul_zero] at hK
    exact zero_ne_one hK
  have hKtop : μH[(n : ℝ)] K ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top hc0] at hK
    exact ENNReal.top_ne_one hK
  -- hence `c ≤ ωₙ/2ⁿ`
  have hcle : (c : ℝ≥0∞) ≤ unitBallVolume n / 2 ^ n := by
    have h := Measure.le_iff'.1 hiso K
    rw [hvol, Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul] at h
    exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).1 h
  -- conclusion on `ℝᴾ`: `μHE[n](s) = c · μH[n](s) ≤ (ωₙ/2ⁿ) · μH[n](s)`
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.euclideanHausdorffMeasure_def, hc, Measure.coe_nnreal_smul_apply,
    Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcle zero_le

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
