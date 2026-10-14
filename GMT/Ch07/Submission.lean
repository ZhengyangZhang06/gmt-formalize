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

/-- **Countably many `C¹` charts inside `U`** (Simon Ch. 2, §4 (4.1); Ch. 3, Lemma 1.2 and
Remark 1.3).  Let `U ⊆ ℝᴾ` be open and `M ⊆ U` with `M ⊆ N₀ ∪ ⋃ₗ Nₗ`, each `Nₗ` an embedded
`m`-dimensional `C¹` submanifold.  Then there are countably many charts `(Vₛ, ψₛ)`: `Vₛ ⊆ ℝᵐ`
open, `ψₛ` `C¹` and injective on `Vₛ` with injective differential at every point of `Vₛ`, and
`ψₛ(Vₛ) ⊆ U`, such that `M ⊆ N₀ ∪ ⋃ₛ ψₛ(Vₛ)`. -/
theorem Submission.dor_lmbsf_cp_submanifold_chart_cover : ∀ (P m : ℕ) (U M N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), IsOpen U → M ⊆ U → (∀ l, IsEmbeddedSubmanifold 1 m (N l)) → M ⊆ N₀ ∪ ⋃ l, N l → ∃ (V : ℕ → Set (Euclid m)) (ψ : ℕ → Euclid m → Euclid P), (∀ s, IsOpen (V s) ∧ ContDiffOn ℝ 1 (ψ s) (V s) ∧ InjOn (ψ s) (V s) ∧ (∀ y ∈ V s, Injective (fderiv ℝ (ψ s) y)) ∧ ψ s '' V s ⊆ U) ∧ M ⊆ N₀ ∪ ⋃ s, ψ s '' V s := by
  classical
  intro P m U M N₀ N hU hMU hN hMN
  -- a chart `(V, W, ψ)` of `Nₗ` at every `z ∈ Nₗ`, with `ψ(V) = W ∩ Nₗ`
  have hch : ∀ (l : ℕ) (z : N l), ∃ (V : Set (Euclid m)) (W : Set (Euclid P))
      (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ (z : Euclid P) ∈ W ∧
      ContDiffOn ℝ 1 ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ N l ∧ ∀ y ∈ V, Injective (fderiv ℝ ψ y) := by
    intro l z
    obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, -, hD⟩ := hN l z z.2
    exact ⟨V, W, ψ, hV, hW, hzW, by simpa using hψ, hinj, himg, hD⟩
  choose V W ψ hV hW hzW hψ hinj himg hD using hch
  -- Lindelöf: countably many `W l z`, `z ∈ T l`, cover `Nₗ`
  have hT : ∀ l, ∃ T : Set (N l), T.Countable ∧ ⋃ z ∈ T, W l z = ⋃ z, W l z :=
    fun l => TopologicalSpace.isOpen_iUnion_countable (W l) (hW l)
  choose T hTc hTU using hT
  let I := Σ l : ℕ, T l
  have : ∀ l, Countable (T l) := fun l => (hTc l).to_subtype
  have : Countable I := inferInstance
  -- shrink each domain to `V ∩ ψ⁻¹(U)`; the extra index `none` carries the empty chart
  let V' : Option I → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some i => V i.1 i.2 ∩ ψ i.1 i.2 ⁻¹' U
  let ψ' : Option I → Euclid m → Euclid P := fun o =>
    match o with
    | none => 0
    | some i => ψ i.1 i.2
  have hchart : ∀ o : Option I, IsOpen (V' o) ∧ ContDiffOn ℝ 1 (ψ' o) (V' o) ∧
      InjOn (ψ' o) (V' o) ∧ (∀ y ∈ V' o, Injective (fderiv ℝ (ψ' o) y)) ∧ ψ' o '' V' o ⊆ U := by
    intro o
    cases o with
    | none => simp [V', ψ']
    | some i =>
      refine ⟨(hψ i.1 i.2).continuousOn.isOpen_inter_preimage (hV i.1 i.2) hU,
        (hψ i.1 i.2).mono inter_subset_left, (hinj i.1 i.2).mono inter_subset_left,
        fun y hy => hD i.1 i.2 y hy.1, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2
  -- enumerate the countable index set `Option I` by `ℕ`
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (Option I)
  refine ⟨fun s => V' (σ s), fun s => ψ' (σ s), fun s => hchart (σ s), ?_⟩
  -- covering: `x ∈ M ∩ Nₗ` lies in some `W l z ∩ Nₗ = ψ(V)`, and its preimage in `ψ⁻¹(U)`
  intro x hxM
  rcases hMN hxM with h0 | hx
  · exact Or.inl h0
  · right
    obtain ⟨l, hxl⟩ := mem_iUnion.1 hx
    have hxW : x ∈ ⋃ z ∈ T l, W l z := by
      rw [hTU l]
      exact mem_iUnion.2 ⟨⟨x, hxl⟩, hzW l ⟨x, hxl⟩⟩
    obtain ⟨z, hzT, hxz⟩ := mem_iUnion₂.1 hxW
    have hx' : x ∈ ψ l z '' V l z := by
      rw [himg l z]
      exact ⟨hxz, hxl⟩
    obtain ⟨v, hv, hvx⟩ := hx'
    obtain ⟨s, hs⟩ := hσ (some ⟨l, ⟨z, hzT⟩⟩)
    refine mem_iUnion.2 ⟨s, v, ?_, ?_⟩
    · show v ∈ V' (σ s)
      rw [hs]
      exact ⟨hv, by simpa [hvx] using hMU hxM⟩
    · show ψ' (σ s) v = x
      rw [hs]
      exact hvx
/-- **Simon Ch. 3, Lemma 1.2** ("only if", C¹ pieces of a chart), assuming the C¹ approximation
of Lipschitz functions (Ch. 2, Theorem 1.5).  Countably many balls `B_r(c)` with
`B̄_{2r}(c) ⊆ V` cover `V` (Lindelöf); `ψ` is Lipschitz on `B̄_{2r}(c)`, so `f ∘ ψ` has a Lipschitz
extension `ũ` from `B̄_r(c)` (McShane), and `C¹` functions `G_k` agree with `ũ` off a set of
measure `< (k+1)⁻¹`.  The pieces are `B̄_r(c) ∩ {ũ = G_k}` inside `C' = B̄_{2r}(c)`, enumerated
by `ℕ` with an empty piece as padding; the remainder lies in `⋃_b ⋂_k {ũ_b ≠ G_{b,k}}`, a null
set. -/
theorem Submission.dor_lmbsf_cp_chart_c1_pieces : (∀ (m : ℕ) (u : Euclid m → ℝ) (K : NNReal), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧ volume {y | u y ≠ G y} < ε) → ∀ (m P : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (f : Euclid P → ℝ) (L : NNReal), IsOpen V → ContDiffOn ℝ 1 ψ V → LipschitzWith L f → ∃ (C C' : ℕ → Set (Euclid m)) (F : ℕ → Euclid m → ℝ), (∀ k, IsCompact (C k) ∧ IsCompact (C' k) ∧ Convex ℝ (C' k) ∧ C k ⊆ interior (C' k) ∧ C' k ⊆ V ∧ ContDiff ℝ 1 (F k) ∧ ∀ y ∈ C k, f (ψ y) = F k y) ∧ volume (V \ ⋃ k, C k) = 0 := by
  classical
  intro CA m P V ψ f L hV hψ hf
  -- balls `B_r(c)` with `r > 0` and `B̄_{2r}(c) ⊆ V`; countably many of them cover `V`
  let B := {p : Euclid m × ℝ // 0 < p.2 ∧ closedBall p.1 (2 * p.2) ⊆ V}
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun b : B => ball b.1.1 b.1.2) (fun _ => isOpen_ball)
  have hcovV : V ⊆ ⋃ b ∈ T, ball b.1.1 b.1.2 := by
    intro v hv
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV v hv
    have hsub : closedBall v (2 * (ε / 3)) ⊆ V :=
      (closedBall_subset_ball (by linarith)).trans hball
    let b : B := ⟨(v, ε / 3), by positivity, hsub⟩
    rw [hTU]
    exact mem_iUnion.2 ⟨b, mem_ball_self (by positivity)⟩
  -- on each ball: a Lipschitz extension `u` of `f ∘ ψ` and `C¹` functions `G k` with
  -- `volume {u ≠ G k} < (k+1)⁻¹`
  have hdata : ∀ b : B, ∃ (G : ℕ → Euclid m → ℝ) (u : Euclid m → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧
      Continuous u ∧ (∀ y ∈ closedBall b.1.1 b.1.2, f (ψ y) = u y) ∧
      ∀ k : ℕ, volume {y | u y ≠ G k y} < ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro b
    obtain ⟨Λ, hΛ⟩ := (hψ.mono b.2.2).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
      (isCompact_closedBall _ _)
    have hu : LipschitzOnWith (L * Λ) (f ∘ ψ) (closedBall b.1.1 b.1.2) :=
      (hf.comp_lipschitzOnWith hΛ).mono (closedBall_subset_closedBall (by linarith [b.2.1]))
    obtain ⟨u, hu', hequ⟩ := hu.extend_real
    have hk : ∀ k : ℕ, ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧
        volume {y | u y ≠ G y} < ((k : ℝ≥0∞) + 1)⁻¹ := fun k =>
      CA m u (L * Λ) hu' _ (ENNReal.inv_pos.2 (by simp))
    choose G hG hGvol using hk
    exact ⟨G, u, hG, hu'.continuous, fun y hy => hequ hy, hGvol⟩
  choose G u hG hucont hequ hGvol using hdata
  have : Countable T := hTc.to_subtype
  -- the pieces indexed by `Option (T × ℕ)`, with the empty piece at `none`
  let Cp : Option (T × ℕ) → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some (b, k) => closedBall b.1.1.1 b.1.1.2 ∩ {y | u b.1 y = G b.1 k y}
  let C'p : Option (T × ℕ) → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some (b, _) => closedBall b.1.1.1 (2 * b.1.1.2)
  let Fp : Option (T × ℕ) → Euclid m → ℝ := fun o =>
    match o with
    | none => 0
    | some (b, k) => G b.1 k
  have hprop : ∀ o, IsCompact (Cp o) ∧ IsCompact (C'p o) ∧ Convex ℝ (C'p o) ∧
      Cp o ⊆ interior (C'p o) ∧ C'p o ⊆ V ∧ ContDiff ℝ 1 (Fp o) ∧
      ∀ y ∈ Cp o, f (ψ y) = Fp o y := by
    intro o
    cases o with
    | none => exact ⟨isCompact_empty, isCompact_empty, convex_empty, empty_subset _, empty_subset _,
        contDiff_zero_fun, fun y hy => hy.elim⟩
    | some bk =>
      obtain ⟨b, k⟩ := bk
      refine ⟨(isCompact_closedBall _ _).inter_right
          (isClosed_eq (hucont b.1) (hG b.1 k).continuous),
        isCompact_closedBall _ _, convex_closedBall _ _, ?_, b.1.2.2, hG b.1 k, ?_⟩
      · intro y hy
        apply ball_subset_interior_closedBall
        have := hy.1
        rw [mem_closedBall] at this
        rw [mem_ball]
        linarith [b.1.2.1]
      · intro y hy
        exact (hequ b.1 y hy.1).trans hy.2
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (Option (T × ℕ))
  refine ⟨fun s => Cp (σ s), fun s => C'p (σ s), fun s => Fp (σ s), fun s => hprop (σ s), ?_⟩
  -- the remainder lies in `⋃_b ⋂_k {u_b ≠ G_{b,k}}`
  have hsub : V \ ⋃ s, Cp (σ s) ⊆ ⋃ b : T, ⋂ k : ℕ, {y | u b.1 y ≠ G b.1 k y} := by
    rintro v ⟨hv, hvnot⟩
    obtain ⟨b, hbT, hvb⟩ := mem_iUnion₂.1 (hcovV hv)
    refine mem_iUnion.2 ⟨⟨b, hbT⟩, mem_iInter.2 fun k => ?_⟩
    intro heq
    obtain ⟨s, hs⟩ := hσ (some (⟨b, hbT⟩, k))
    apply hvnot
    refine mem_iUnion.2 ⟨s, ?_⟩
    rw [hs]
    exact ⟨ball_subset_closedBall hvb, heq⟩
  refine measure_mono_null hsub (measure_iUnion_null fun b => ?_)
  -- each `⋂_k {u_b ≠ G_{b,k}}` has measure `< (n+1)⁻¹ ≤ n⁻¹` for every `n`
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  have h1 : volume (⋂ k : ℕ, {y | u b.1 y ≠ G b.1 k y}) ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
    (measure_mono (iInter_subset _ n)).trans (hGvol b.1 n).le
  have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.2 le_self_add
  exact absurd (h1.trans h2) (not_le.2 hn)
/-- **Lipschitz (`C¹`) images of Lebesgue-null sets are `Hᵐ`-null** (Simon Ch. 3, §2, discussion
after 2.4; Ch. 2, Theorem 1.8(i)).  If `ψ` is `C¹` on an open `V ⊆ ℝᵐ` and `Z ⊆ V` is `Lᵐ`-null,
then `Hᵐ(ψ(Z)) = 0`: `ψ` is Lipschitz near each point of `V`, countably many such neighbourhoods
cover `V` (Lindelöf), and on each the Lipschitz image bound gives `Hᵐ(ψ(Z ∩ t)) ≤ Kᵐ Lᵐ(Z ∩ t) = 0`.
-/
theorem Submission.dor_lmbsf_cp_c1_image_null : ∀ (m P : ℕ) (V Z : Set (Euclid m)) (ψ : Euclid m → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → Z ⊆ V → volume Z = 0 → μHE[m] (ψ '' Z) = 0 := by
  intro m P V Z ψ hV hψ hZV hZ
  -- Step 1: every `y ∈ V` has an open neighbourhood on which `ψ` is Lipschitz
  have hloc : ∀ y : V, ∃ K : NNReal, ∃ t : Set (Euclid m), IsOpen t ∧ (y : Euclid m) ∈ t ∧
      LipschitzOnWith K ψ t := by
    intro y
    obtain ⟨K, t, ht, hK⟩ := (hψ.contDiffAt (hV.mem_nhds y.2)).exists_lipschitzOnWith
    obtain ⟨u, hut, hu, hyu⟩ := _root_.mem_nhds_iff.1 ht
    exact ⟨K, u, hu, hyu, hK.mono hut⟩
  choose K t ht hyt hK using hloc
  -- Step 2: Lindelöf gives a countable subfamily covering `V ⊇ Z`
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable t ht
  have hcov : Z ⊆ ⋃ y ∈ T, t y := by
    intro z hz
    have : z ∈ ⋃ y, t y := mem_iUnion.2 ⟨⟨z, hZV hz⟩, hyt _⟩
    rw [← hT] at this
    exact this
  -- Step 3: `ψ(Z) ⊆ ⋃_{y ∈ T} ψ(Z ∩ t y)`
  have hsub : ψ '' Z ⊆ ⋃ y ∈ T, ψ '' (Z ∩ t y) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hyT, hzy⟩ := mem_iUnion₂.1 (hcov hz)
    exact mem_iUnion₂.2 ⟨y, hyT, z, ⟨hz, hzy⟩, rfl⟩
  -- Steps 4 and 5: each piece is null by the Lipschitz image bound and `μHE[m] = volume`
  refine measure_mono_null hsub ((measure_biUnion_null_iff hTc).2 fun y _ => ?_)
  refine le_antisymm ?_ zero_le
  calc μHE[m] (ψ '' (Z ∩ t y)) ≤ (K y : ℝ≥0∞) ^ m * μHE[m] (Z ∩ t y) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
          ((hK y).mono inter_subset_right)
    _ = 0 := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
          measure_mono_null inter_subset_left hZ, mul_zero]
/-- **Approximate tangent planes of `M` on a chart piece** (Simon Ch. 3, Remark 1.5(2) and the
proof of Theorem 1.6 "⇒"; Step 7 of `dor_lmbsf_lipschitz_chart_pieces`).  Assume the locality
principle (TL): for Borel `A ⊆ B ⊆ U` with `Hⁿ(B ∩ K) < ∞` for compact `K ⊆ U`, at `Hⁿ`-a.e.
`x ∈ A` the sets `B` and `A` have the same approximate tangent spaces.  Let `ψ` be `C¹` on the
convex compact `C'` with `ψ(C') ⊆ U`, let `C ⊆ int C'` be compact, and let `ψ(C')` have
approximate tangent space `Dψ(y)(ℝᵐ)` at `ψ(y)` for `y ∈ int C'`.  Then at `Hᵐ`-a.e.
`x ∈ M ∩ ψ(C)`, `M` has approximate tangent space `Dψ(y)(ℝᵐ)` for every `y ∈ C` with `ψ(y) = x`.
`S = ψ(C')` is compact, and `Hᵐ(S) ≤ Λᵐ Lᵐ(C') < ∞` since `ψ` is Lipschitz on `C'`; apply (TL)
to `M ∩ ψ(C) ⊆ S` and to `M ∩ ψ(C) ⊆ M`. -/
theorem Submission.dor_lmbsf_cp_chart_tangent_ae : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P m : ℕ) (U M : Set (Euclid P)) (C C' : Set (Euclid m)) (ψ : Euclid m → Euclid P), IsOpen U → MeasurableSet M → M ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → ContDiffOn ℝ 1 ψ C' → ψ '' C' ⊆ U → IsCompact C → IsCompact C' → Convex ℝ C' → C ⊆ interior C' → (∀ y ∈ interior C', HasApproximateTangentSpaceAt m (ψ '' C') (ψ y) (LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P))) → ∀ᵐ x ∂(μHE[m].restrict (M ∩ ψ '' C)), ∀ y ∈ C, ψ y = x → HasApproximateTangentSpaceAt m M x (LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P)) := by
  intro TL P m U M C C' ψ hU hM hMU hfin hψ hψU hC hC' hconv hCC' hIT
  have hψC' : ContinuousOn ψ C' := hψ.continuousOn
  have hCsub : C ⊆ C' := hCC'.trans interior_subset
  -- `S = ψ(C')` and `ψ(C)` are compact
  have hS : IsCompact (ψ '' C') := hC'.image_of_continuousOn hψC'
  have hSC : IsCompact (ψ '' C) := hC.image_of_continuousOn (hψC'.mono hCsub)
  -- `Hᵐ(S) ≤ Λᵐ Hᵐ(C') = Λᵐ Lᵐ(C') < ∞`, `ψ` being `Λ`-Lipschitz on the convex compact `C'`
  obtain ⟨Λ, hΛ⟩ := hψ.exists_lipschitzOnWith one_ne_zero hconv hC'
  have hSfin : μHE[m] (ψ '' C') ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hΛ) ?_)
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hC'.measure_lt_top
  -- (TL) for `A = M ∩ ψ(C) ⊆ S` and for `A ⊆ M`
  have hA : MeasurableSet (M ∩ ψ '' C) := hM.inter hSC.isClosed.measurableSet
  have h1 := TL P m U (M ∩ ψ '' C) (ψ '' C') hU hA hS.isClosed.measurableSet
    (fun x hx => image_mono hCsub hx.2) hψU
    (fun K _ _ => ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
  have h2 := TL P m U (M ∩ ψ '' C) M hU hA hM inter_subset_left hMU hfin
  -- at `x = ψ y`, transfer the tangent plane of `S` to `A`, then to `M`
  filter_upwards [h1, h2] with x hx1 hx2 y hy hyx
  have hS' := hIT y (hCC' hy)
  rw [hyx] at hS'
  exact (hx2 _).2 ((hx1 _).1 hS')
/-- **Slicing (Simon Ch. 6, §4), chart pieces, step 8: the gradient bound at density points**
(the estimate behind `|∇ᴹf| ≤ Lip f`, cf. Simon Ch. 3, 2.1 and Ch. 2, 4.10).  Let `F = f ∘ ψ` on
a Borel set `Z ⊆ ℝᵐ`, with `F` and `ψ` differentiable at every point of `Z` and `f`
`L`-Lipschitz.  Assuming the direction property (DD) of density points, `|DF(y)e| ≤ L |Dψ(y)e|`
for `Lᵐ`-a.e. `y ∈ Z` and every `e`.  By the Lebesgue density theorem
(`Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`) a.e. `y ∈ Z` is a density point of
`Z`.  For a unit vector `v`, (DD) gives `yᵢ ∈ Z ∖ {y}` with `yᵢ → y` and
`(yᵢ − y)/|yᵢ − y| → v`.  The difference quotients satisfy `|F(yᵢ) − F(y)| ≤ L |ψ(yᵢ) − ψ(y)|`
and converge to `DF(y)v` and `Dψ(y)v` (`HasFDerivWithinAt.lim`), so `|DF(y)v| ≤ L |Dψ(y)v|`.
A general `e ≠ 0` follows by linearity from `v = e/|e|`. -/
theorem Submission.dor_lmbsf_cp_gradient_bound_ae : (∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (m P : ℕ) (Z : Set (Euclid m)) (F : Euclid m → ℝ) (ψ : Euclid m → Euclid P) (f : Euclid P → ℝ) (L : NNReal), MeasurableSet Z → (∀ y ∈ Z, DifferentiableAt ℝ F y ∧ DifferentiableAt ℝ ψ y) → (∀ y ∈ Z, f (ψ y) = F y) → LipschitzWith L f → ∀ᵐ y ∂volume, y ∈ Z → ∀ e : Euclid m, |fderiv ℝ F y e| ≤ (L : ℝ) * ‖fderiv ℝ ψ y e‖ := by
  intro DD m P Z F ψ f L hZ hdiff heq hf
  -- step 1: almost every point of `Z` is a Lebesgue density point of `Z`
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hZ] with y hy hyZ
  have hdens : Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1) := by
    simpa [Set.indicator_of_mem hyZ] using hy
  -- steps 2–5: the bound in a unit direction `v`
  have hunit : ∀ v : Euclid m, ‖v‖ = 1 → |fderiv ℝ F y v| ≤ (L : ℝ) * ‖fderiv ℝ ψ y v‖ := by
    intro v hv
    -- step 2: points `yᵢ ∈ Z ∖ {y}`, `yᵢ → y`, approaching `y` from the direction `v`
    obtain ⟨ys, hys, hlim, hdir⟩ := DD m Z y hdens v hv
    -- step 3: `|F(yᵢ) − F(y)| = |f(ψ(yᵢ)) − f(ψ(y))| ≤ L |ψ(yᵢ) − ψ(y)|`, divided by `|yᵢ − y|`
    have hineq : ∀ i, |‖ys i - y‖⁻¹ • (F (ys i) - F y)| ≤
        (L : ℝ) * ‖‖ys i - y‖⁻¹ • (ψ (ys i) - ψ y)‖ := by
      intro i
      have hci : 0 ≤ ‖ys i - y‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      rw [smul_eq_mul, abs_mul, abs_of_nonneg hci, norm_smul, Real.norm_of_nonneg hci,
        ← heq _ (hys i).1, ← heq y hyZ]
      have h1 := hf.dist_le_mul (ψ (ys i)) (ψ y)
      rw [Real.dist_eq, dist_eq_norm] at h1
      calc ‖ys i - y‖⁻¹ * |f (ψ (ys i)) - f (ψ y)|
          ≤ ‖ys i - y‖⁻¹ * ((L : ℝ) * ‖ψ (ys i) - ψ y‖) := mul_le_mul_of_nonneg_left h1 hci
        _ = (L : ℝ) * (‖ys i - y‖⁻¹ * ‖ψ (ys i) - ψ y‖) := by ring
    -- step 4: the difference quotients along `yᵢ − y` converge to `DF(y)v` and `Dψ(y)v`
    have hd0 : Tendsto (fun i => ys i - y) atTop (𝓝 0) := by
      simpa using hlim.sub_const y
    have hF' := ((hdiff y hyZ).1.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    have hψ' := ((hdiff y hyZ).2.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    simp only [add_sub_cancel] at hF' hψ'
    -- step 5: the non-strict inequality passes to the limit
    exact le_of_tendsto_of_tendsto' hF'.abs (hψ'.norm.const_mul _) hineq
  -- step 6: a general `e ≠ 0` by linearity, from the unit vector `‖e‖⁻¹ • e`
  intro e
  by_cases he : e = 0
  · simp [he]
  · have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    have hv : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have h := hunit _ hv
    rw [map_smul, map_smul, smul_eq_mul, abs_mul, norm_smul, abs_inv, abs_norm, norm_inv,
      norm_norm] at h
    have hpos : 0 < ‖e‖⁻¹ := inv_pos.2 (norm_pos_iff.2 he)
    have h2 : ‖e‖⁻¹ * |fderiv ℝ F y e| ≤ ‖e‖⁻¹ * ((L : ℝ) * ‖fderiv ℝ ψ y e‖) := by
      calc ‖e‖⁻¹ * |fderiv ℝ F y e| ≤ (L : ℝ) * (‖e‖⁻¹ * ‖fderiv ℝ ψ y e‖) := h
        _ = ‖e‖⁻¹ * ((L : ℝ) * ‖fderiv ℝ ψ y e‖) := by ring
    exact le_of_mul_le_mul_left h2 hpos
/-- **Disjoint Borel refinement of chart pieces** (Simon Ch. 3, Remark 1.3).  Let `M ⊆ ℝᴾ` be
Borel, `Cⱼ ⊆ ℝᵐ` compact and `ψⱼ` continuous on `Cⱼ`, with `μ(M ∖ ⋃ⱼ ψⱼ(Cⱼ)) = 0`, and suppose
that for `μ⌞(M ∩ ψⱼ(Cⱼ))`-a.e. `x` every `y ∈ Cⱼ` with `ψⱼ(y) = x` satisfies `Goodⱼ(y)`.  Then
there are Borel sets `Yⱼ ⊆ Cⱼ` of good points whose images `ψⱼ(Yⱼ) ⊆ M` are pairwise disjoint
and cover `M` up to a `μ`-null set. -/
theorem Submission.dor_lmbsf_cp_disjoint_refinement : ∀ (m P : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (C : ℕ → Set (Euclid m)) (ψ : ℕ → Euclid m → Euclid P) (Good : ℕ → Euclid m → Prop), MeasurableSet M → (∀ j, IsCompact (C j) ∧ ContinuousOn (ψ j) (C j)) → μ (M \ ⋃ j, ψ j '' C j) = 0 → (∀ j, ∀ᵐ x ∂(μ.restrict (M ∩ ψ j '' C j)), ∀ y ∈ C j, ψ j y = x → Good j y) → ∃ Y : ℕ → Set (Euclid m), (∀ j, MeasurableSet (Y j) ∧ Y j ⊆ C j ∧ ψ j '' Y j ⊆ M ∧ ∀ y ∈ Y j, Good j y) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) ∧ μ (M \ ⋃ j, ψ j '' Y j) = 0 := by
  classical
  intro m P μ M C ψ Good hM hC hnull hgood
  -- `Eⱼ = ψⱼ(Cⱼ)` is compact, hence Borel, and `Aⱼ = M ∩ Eⱼ` is Borel
  let E : ℕ → Set (Euclid P) := fun j => ψ j '' C j
  have hEc : ∀ j, IsCompact (E j) := fun j => (hC j).1.image_of_continuousOn (hC j).2
  have hEm : ∀ j, MeasurableSet (E j) := fun j => (hEc j).isClosed.measurableSet
  let A : ℕ → Set (Euclid P) := fun j => M ∩ E j
  have hAm : ∀ j, MeasurableSet (A j) := fun j => hM.inter (hEm j)
  -- a Borel set `Tⱼ` containing the exceptional points, with `μ(Tⱼ ∩ Aⱼ) = 0`
  have hT : ∀ j, ∃ T : Set (Euclid P), {x | ¬ ∀ y ∈ C j, ψ j y = x → Good j y} ⊆ T ∧
      MeasurableSet T ∧ μ (T ∩ A j) = 0 := by
    intro j
    obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hgood j))
    exact ⟨T, hsub, hTm, by rwa [Measure.restrict_apply hTm] at hT0⟩
  choose T hTsub hTm hT0 using hT
  -- Remark 1.3: `Dⱼ = Aⱼ ∖ ⋃_{i<j} Aᵢ`; then `M'ⱼ = Dⱼ ∖ Tⱼ` and `Yⱼ = Cⱼ ∩ ψⱼ⁻¹(M'ⱼ)`
  let D : ℕ → Set (Euclid P) := disjointed A
  let M' : ℕ → Set (Euclid P) := fun j => D j \ T j
  have hDm : ∀ j, MeasurableSet (D j) := MeasurableSet.disjointed hAm
  have hM'm : ∀ j, MeasurableSet (M' j) := fun j => (hDm j).diff (hTm j)
  have hDA : ∀ j, D j ⊆ A j := disjointed_subset A
  -- `ψⱼ(Yⱼ) = M'ⱼ`, since `M'ⱼ ⊆ Aⱼ ⊆ ψⱼ(Cⱼ)`
  have himg : ∀ j, ψ j '' (C j ∩ ψ j ⁻¹' M' j) = M' j := by
    intro j
    ext x
    constructor
    · rintro ⟨y, ⟨_, hy⟩, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (hDA j hx.1).2
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  refine ⟨fun j => C j ∩ ψ j ⁻¹' M' j, fun j => ⟨?_, inter_subset_left, ?_, ?_⟩, ?_, ?_⟩
  · -- `Yⱼ` is Borel: on `Cⱼ`, `ψⱼ` agrees with the Borel map equal to `ψⱼ` on `Cⱼ`, `0` off it
    have hpw : Measurable ((C j).piecewise (ψ j) (fun _ => 0)) :=
      (hC j).2.measurable_piecewise continuousOn_const (hC j).1.isClosed.measurableSet
    have : C j ∩ ψ j ⁻¹' M' j = C j ∩ (C j).piecewise (ψ j) (fun _ => 0) ⁻¹' M' j := by
      ext y
      constructor
      · rintro ⟨hy, hy'⟩
        exact ⟨hy, by simpa [Set.piecewise_eq_of_mem _ _ _ hy] using hy'⟩
      · rintro ⟨hy, hy'⟩
        exact ⟨hy, by simpa [Set.piecewise_eq_of_mem _ _ _ hy] using hy'⟩
    show MeasurableSet (C j ∩ ψ j ⁻¹' M' j)
    rw [this]
    exact (hC j).1.isClosed.measurableSet.inter (hpw (hM'm j))
  · -- `ψⱼ(Yⱼ) = M'ⱼ ⊆ Aⱼ ⊆ M`
    rw [himg j]
    exact fun x hx => (hDA j hx.1).1
  · -- points of `Yⱼ` are good, since `ψⱼ(y) ∉ Tⱼ`
    intro y hy
    have hx : ψ j y ∉ T j := hy.2.2
    have : ψ j y ∉ {x | ¬ ∀ y ∈ C j, ψ j y = x → Good j y} := fun h => hx (hTsub j h)
    simp only [mem_ofPred_eq, not_not] at this
    exact this y hy.1 rfl
  · -- the images lie in the pairwise disjoint `Dⱼ`
    intro i j hij
    simp only
    rw [himg i, himg j]
    exact (disjoint_disjointed A hij).mono sdiff_subset sdiff_subset
  · -- `M ∖ ⋃ⱼ ψⱼ(Yⱼ) ⊆ (M ∖ ⋃ⱼ Eⱼ) ∪ ⋃ⱼ (Tⱼ ∩ Aⱼ)`, a `μ`-null set
    have hsub : M \ ⋃ j, ψ j '' (C j ∩ ψ j ⁻¹' M' j) ⊆ (M \ ⋃ j, E j) ∪ ⋃ j, (T j ∩ A j) := by
      rintro x ⟨hxM, hxnot⟩
      by_cases hxE : x ∈ ⋃ j, E j
      · right
        have hxA : x ∈ ⋃ j, A j := by
          obtain ⟨j, hj⟩ := mem_iUnion.1 hxE
          exact mem_iUnion.2 ⟨j, hxM, hj⟩
        rw [← iUnion_disjointed] at hxA
        obtain ⟨j, hj⟩ := mem_iUnion.1 hxA
        have hxT : x ∈ T j := by
          by_contra hxT
          exact hxnot (mem_iUnion.2 ⟨j, by rw [himg j]; exact ⟨hj, hxT⟩⟩)
        exact mem_iUnion.2 ⟨j, hxT, hDA j hj⟩
      · exact Or.inl ⟨hxM, hxE⟩
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨hnull, measure_iUnion_null hT0⟩
/-- **Tangential lift of a gradient on a `C¹` chart** (Simon Ch. 2, §4; Ch. 3, 2.1).  Let `ψ` be
`C¹` on the open set `V ⊆ ℝᵐ` with injective differential and `F : ℝᵐ → ℝ` be `C¹`.  With
`A(y) = Dψ(y)`, `Γ(y) = A(y)* A(y)` and `a(y)` the Riesz vector of `DF(y)`, the field
`Φ(y) = A(y) Γ(y)⁻¹ a(y)` is continuous on `V`, lies in `Dψ(y)(ℝᵐ)`, satisfies
`⟨Φ(y), Dψ(y)e⟩ = DF(y)e`, and `|Φ(y)| ≤ L` whenever `|DF(y)e| ≤ L |Dψ(y)e|` for all `e`. -/
theorem Submission.dor_lmbsf_cp_chart_tangent_lift : ∀ (m P : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (F : Euclid m → ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ Φ : Euclid m → Euclid P, ContinuousOn Φ V ∧ ∀ y ∈ V, Φ y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P) ∧ (∀ e : Euclid m, inner ℝ (Φ y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) ∧ ∀ L : NNReal, (∀ e : Euclid m, |fderiv ℝ F y e| ≤ (L : ℝ) * ‖fderiv ℝ ψ y e‖) → ‖Φ y‖ ≤ (L : ℝ) := by
  classical
  intro m P V ψ F hV hψ hinj hF
  let A : Euclid m → (Euclid m →L[ℝ] Euclid P) := fun y => fderiv ℝ ψ y
  let Γ : Euclid m → (Euclid m →L[ℝ] Euclid m) :=
    fun y => (ContinuousLinearMap.adjoint (A y)).comp (A y)
  let a : Euclid m → Euclid m :=
    fun y => (InnerProductSpace.toDual ℝ (Euclid m)).symm (fderiv ℝ F y)
  -- `Γ(y)` is injective, hence a unit, on `V`
  have hunit : ∀ y ∈ V, IsUnit (Γ y) := by
    intro y hy
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro e he
    have h1 : inner ℝ (Γ y e) e = ‖A y e‖ ^ 2 := by
      simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      exact real_inner_self_eq_norm_sq (A y e)
    have h2 : Γ y e = 0 := he
    rw [h2, inner_zero_left] at h1
    have h3 : A y e = 0 := by
      have : ‖A y e‖ = 0 := by nlinarith [norm_nonneg (A y e)]
      exact norm_eq_zero.1 this
    exact hinj y hy (by simpa [A] using h3)
  refine ⟨fun y => A y (Ring.inverse (Γ y) (a y)), ?_, ?_⟩
  · -- continuity: `fderiv`, adjoint, composition, `Ring.inverse` at units, evaluation
    have hA : ContinuousOn A V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
    have hAadj : ContinuousOn (fun y => ContinuousLinearMap.adjoint (A y)) V :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous
        |>.comp_continuousOn hA
    have hΓ : ContinuousOn Γ V := hAadj.clm_comp hA
    have hinv : ContinuousOn (fun y => Ring.inverse (Γ y)) V := by
      intro y hy
      obtain ⟨u, hu⟩ := hunit y hy
      have hc := NormedRing.inverse_continuousAt u
      rw [hu] at hc
      exact hc.comp_continuousWithinAt (hΓ y hy)
    have ha : Continuous a :=
      (InnerProductSpace.toDual ℝ (Euclid m)).symm.continuous.comp
        (hF.continuous_fderiv one_ne_zero)
    exact hA.clm_apply (hinv.clm_apply ha.continuousOn)
  · intro y hy
    set w := Ring.inverse (Γ y) (a y) with hw
    have hΓw : Γ y w = a y := by
      obtain ⟨u, hu⟩ := hunit y hy
      rw [hw, ← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
    -- the defining identity `⟨A w, A e⟩ = ⟨Γ w, e⟩ = ⟨a, e⟩ = DF(y) e`
    have hdef : ∀ e : Euclid m, inner ℝ (A y w) (fderiv ℝ ψ y e) = fderiv ℝ F y e := by
      intro e
      have : inner ℝ (A y w) (A y e) = inner ℝ (Γ y w) e := by
        simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      change inner ℝ (A y w) (A y e) = _
      rw [this, hΓw]
      simp [a, InnerProductSpace.toDual_symm_apply]
    refine ⟨⟨w, rfl⟩, hdef, fun L hL => ?_⟩
    -- `|Φ|² = DF(y) w ≤ L |A w| = L |Φ|`
    have hsq : ‖A y w‖ ^ 2 ≤ (L : ℝ) * ‖A y w‖ := by
      rw [← real_inner_self_eq_norm_sq]
      calc inner ℝ (A y w) (A y w) = fderiv ℝ F y w := hdef w
        _ ≤ |fderiv ℝ F y w| := le_abs_self _
        _ ≤ (L : ℝ) * ‖fderiv ℝ ψ y w‖ := hL w
    change ‖A y w‖ ≤ (L : ℝ)
    by_cases h0 : ‖A y w‖ = 0
    · rw [h0]; exact L.coe_nonneg
    · have hpos : 0 < ‖A y w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
/-- Borel gluing over pairwise disjoint injective images (Lusin–Souslin; the Borel field `g` on
the chart pieces in the slicing step of the proof of Simon 7.4.3): if `ψⱼ` is continuous and
injective and `Φⱼ` continuous on the Borel set `Yⱼ ⊆ ℝᵐ`, and the images `Mⱼ = ψⱼ(Yⱼ)` are
pairwise disjoint, then some Borel `g : ℝᴾ → ℝᴾ` has `g(ψⱼ(y)) = Φⱼ(y)` for `y ∈ Yⱼ` and `g = 0`
off `⋃ⱼ Mⱼ`.  `ψⱼ|_{Yⱼ}` is a measurable embedding, so the extension `gⱼ` of `Φⱼ|_{Yⱼ}` along it
by `0` is Borel; `g(x) = gₙ(x)` for the least `n` with `x ∈ Mₙ ∪ (⋃ⱼ Mⱼ)ᶜ`. -/
theorem Submission.dor_lmbsf_cp_measurable_glue : ∀ (m P : ℕ) (Y : ℕ → Set (Euclid m)) (ψ Φ : ℕ → Euclid m → Euclid P), (∀ j, MeasurableSet (Y j) ∧ ContinuousOn (ψ j) (Y j) ∧ InjOn (ψ j) (Y j) ∧ ContinuousOn (Φ j) (Y j)) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → ∃ g : Euclid P → Euclid P, Measurable g ∧ (∀ j, ∀ y ∈ Y j, g (ψ j y) = Φ j y) ∧ ∀ x, (∀ j, x ∉ ψ j '' Y j) → g x = 0 := by
  classical
  intro m P Y ψ Φ hY hdisj
  -- Lusin–Souslin: `Mⱼ = ψⱼ(Yⱼ)` is Borel
  have hM : ∀ j, MeasurableSet (ψ j '' Y j) := fun j =>
    (hY j).1.image_of_continuousOn_injOn (hY j).2.1 (hY j).2.2.1
  -- `gⱼ`: the extension of `Φⱼ|_{Yⱼ}` by `0` along the measurable embedding `ψⱼ|_{Yⱼ}`
  obtain ⟨gj, hgj, hgj_val, hgj_zero⟩ : ∃ gj : ℕ → Euclid P → Euclid P,
      (∀ j, Measurable (gj j)) ∧ (∀ j, ∀ y ∈ Y j, gj j (ψ j y) = Φ j y) ∧
        ∀ j x, x ∉ ψ j '' Y j → gj j x = 0 := by
    have hemb : ∀ j, MeasurableEmbedding ((Y j).domRestrict (ψ j)) := fun j =>
      (hY j).2.1.measurableEmbedding (hY j).1 (hY j).2.2.1
    refine ⟨fun j => Function.extend ((Y j).domRestrict (ψ j)) ((Y j).domRestrict (Φ j)) 0,
      fun j => (hemb j).measurable_extend (hY j).2.2.2.domRestrict.measurable measurable_const,
      fun j y hy => (hemb j).injective.extend_apply _ _ ⟨y, hy⟩, fun j x hx => ?_⟩
    refine Function.extend_apply' _ _ x ?_
    rintro ⟨y, hy⟩
    exact hx ⟨y, y.2, hy⟩
  -- glue by least index: `g(x) = gₙ(x)` for the least `n` with `x ∈ Mₙ ∪ (⋃ⱼ Mⱼ)ᶜ`
  have hp : ∀ x, ∃ n, x ∈ ψ n '' Y n ∪ (⋃ j, ψ j '' Y j)ᶜ := fun x => by
    by_cases hx : x ∈ ⋃ j, ψ j '' Y j
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact ⟨j, Set.mem_union_left _ hj⟩
    · exact ⟨0, Set.mem_union_right _ (Set.mem_compl hx)⟩
  refine ⟨fun x => gj (Nat.find (hp x)) x,
    Measurable.find (p := fun n x => x ∈ ψ n '' Y n ∪ (⋃ j, ψ j '' Y j)ᶜ) hgj
      (fun n => (hM n).union (MeasurableSet.iUnion hM).compl) hp, ?_, ?_⟩
  · -- at `ψⱼ(y)` the least index is `j`, by disjointness
    intro j y hy
    have hx : ψ j y ∈ ψ j '' Y j := Set.mem_image_of_mem _ hy
    have hfind : Nat.find (hp (ψ j y)) = j := by
      rcases Nat.find_spec (hp (ψ j y)) with h | h
      · by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) h hx
      · exact absurd (Set.mem_iUnion.2 ⟨j, hx⟩) h
    show gj (Nat.find (hp (ψ j y))) (ψ j y) = Φ j y
    rw [hfind]
    exact hgj_val j y hy
  · -- off `⋃ⱼ Mⱼ` every `gₙ` vanishes
    intro x hx
    exact hgj_zero _ x (hx _)
/-- **A `C¹` immersion is locally injective.**  If `G : ℝᵐ → ℝᴾ` is `C¹` and `DG(x)` is injective,
then for some `r > 0` the map `G` and every `DG(z)`, `z ∈ B̄_r(x)`, are injective.  `L = DG(x)` is
anti-Lipschitz on the finite-dimensional `ℝᵐ`, `c ‖v‖ ≤ ‖L v‖` with `c > 0`, and continuity of
`DG` gives `‖DG(z) - L‖ ≤ c/2` on `B̄_r(x)`.  If `DG(z) u = 0` then
`c ‖u‖ ≤ ‖L u‖ = ‖(DG(z) - L) u‖ ≤ (c/2) ‖u‖`; if `G a = G b`, the mean value inequality
`‖G a - G b - L (a - b)‖ ≤ (c/2) ‖a - b‖` gives `c ‖a - b‖ ≤ (c/2) ‖a - b‖`.  So `u = 0`, `a = b`. -/
theorem Submission.dor_lmbsf_c1c_immersion_local_injOn : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G x) → ∃ r : ℝ, 0 < r ∧ Set.InjOn G (Metric.closedBall x r) ∧ ∀ z ∈ Metric.closedBall x r, Function.Injective (fderiv ℝ G z) := by
  intro P m G x hG hx
  set L : Euclid m →L[ℝ] Euclid P := fderiv ℝ G x
  -- `L` is injective on the finite-dimensional `ℝᵐ`, hence anti-Lipschitz: `c ‖v‖ ≤ ‖L v‖`
  obtain ⟨K, hKpos, hK⟩ :=
    (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hx)
  have hK' : (0 : ℝ) < K := hKpos
  set c : ℝ := (K : ℝ)⁻¹
  have hcpos : 0 < c := inv_pos.2 hK'
  have hLc : ∀ v, c * ‖v‖ ≤ ‖L v‖ := fun v =>
    (inv_mul_le_iff₀ hK').2 (L.bound_of_antilipschitz hK v)
  -- continuity of `DG` gives `δ > 0` with `‖DG(z) - L‖ ≤ c/2` on `B̄_{δ/2}(x)`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuous_iff.1 (hG.continuous_fderiv one_ne_zero) x (c / 2) (half_pos hcpos)
  have hbound : ∀ z ∈ closedBall x (δ / 2), ‖fderiv ℝ G z - L‖ ≤ c / 2 := by
    intro z hz
    have h := hδ z (lt_of_le_of_lt (mem_closedBall.1 hz) (half_lt_self hδpos))
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨δ / 2, half_pos hδpos, ?_, ?_⟩
  · -- mean value inequality: `‖G a - G b - L (a - b)‖ ≤ (c/2) ‖a - b‖`
    intro a ha b hb hab
    have hmvt := (convex_closedBall x (δ / 2)).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => (hG.differentiable one_ne_zero) z) hbound hb ha
    rw [hab, sub_self, zero_sub, norm_neg] at hmvt
    have h1 := hLc (a - b)
    have h2 : ‖a - b‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  · -- if `DG(z) u = 0` then `c ‖u‖ ≤ ‖L u‖ = ‖(DG(z) - L) u‖ ≤ (c/2) ‖u‖`
    intro z hz v w hvw
    have hu : fderiv ℝ G z (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 := hLc (v - w)
    have h2 : ‖L (v - w)‖ ≤ c / 2 * ‖v - w‖ := by
      have h3 : L (v - w) = -((fderiv ℝ G z - L) (v - w)) := by
        rw [sub_apply, hu, zero_sub, neg_neg]
      rw [h3, norm_neg]
      calc ‖(fderiv ℝ G z - L) (v - w)‖ ≤ ‖fderiv ℝ G z - L‖ * ‖v - w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ c / 2 * ‖v - w‖ := by gcongr; exact hbound z hz
    have h4 : ‖v - w‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h4)
/-- **A `C¹` chart on a ball** (Simon Ch. 3, proof of Lemma 1.2, step 5): if `G : ℝᵐ → ℝᴾ` is
`C¹`, injective on `B̄_r(x)` and has injective derivative on `B_r(x)`, then `G(B_r(x))` is an
embedded `m`-dimensional `C¹` submanifold.  Every point is charted by `ψ = G` on `V = B_r(x)`
with `W = ℝᴾ \ G(∂B_r(x))`: `W` is open because the sphere is compact; injectivity on `B̄_r(x)`
gives `G(B_r(x)) ⊆ W`, so `ψ(V) = W ∩ G(B_r(x))`; and for compact `K ⊆ W`, sphere points map
outside `K`, so `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is compact. -/
theorem Submission.dor_lmbsf_c1c_injOn_closedBall_chart : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m) (r : ℝ), ContDiff ℝ 1 G → Set.InjOn G (Metric.closedBall x r) → (∀ z ∈ Metric.ball x r, Function.Injective (fderiv ℝ G z)) → IsEmbeddedSubmanifold 1 m (G '' Metric.ball x r) := by
  intro P m G x r hG hinj hD
  -- `W = ℝᴾ \ G(∂B_r(x))` is open: the sphere is compact and `G` is continuous
  have hW : IsOpen (G '' Metric.sphere x r)ᶜ :=
    ((isCompact_sphere x r).image hG.continuous).isClosed.isOpen_compl
  -- `G(B_r(x)) ⊆ W`: `G` is injective on `B̄_r(x)` and the sphere misses the open ball
  have hNW : G '' Metric.ball x r ⊆ (G '' Metric.sphere x r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩ ⟨s, hs, hsv⟩
    have hsv' : s = v :=
      hinj (Metric.sphere_subset_closedBall hs) (Metric.ball_subset_closedBall hv) hsv
    subst hsv'
    exact (Metric.mem_ball.1 hv).ne (Metric.mem_sphere.1 hs)
  -- the same chart `(V, W, ψ) = (B_r(x), W, G)` serves every point of `G(B_r(x))`
  intro y hy
  refine ⟨Metric.ball x r, (G '' Metric.sphere x r)ᶜ, G, Metric.isOpen_ball, hW, hNW hy, ?_,
    hinj.mono Metric.ball_subset_closedBall, (Set.inter_eq_right.2 hNW).symm, ?_, hD⟩
  · exact_mod_cast hG.contDiffOn
  -- properness: for compact `K ⊆ W`, `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is compact
  · intro K hKW hK
    have hball : Metric.ball x r ∩ G ⁻¹' K = Metric.closedBall x r ∩ G ⁻¹' K := by
      refine Set.Subset.antisymm
        (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall) ?_
      rintro z ⟨hz, hzK⟩
      refine ⟨?_, hzK⟩
      rcases (Metric.mem_closedBall.1 hz).lt_or_eq with h | h
      · exact Metric.mem_ball.2 h
      · exact (hKW (Set.mem_preimage.1 hzK) ⟨z, Metric.mem_sphere.2 h, rfl⟩).elim
    rw [hball]
    exact (isCompact_closedBall x r).inter_right (hK.isClosed.preimage hG.continuous)
/-- **A Lipschitz map `ℝᵐ → ℝᴾ` agrees with countably many `C¹` maps off a set with `Hᵐ`-null
image** (Simon Ch. 3, proof of Lemma 1.2), given the scalar `C¹` approximation (H) of Ch. 2,
Theorem 1.5.  Apply (H) to each `K`-Lipschitz coordinate `Fᵖ` with `ε = 1/i` and put
`Gᵢ = (g_{ip})_p`, so `Lᵐ({F ≠ Gᵢ}) ≤ Σ_p Lᵐ({Fᵖ ≠ g_{ip}}) ≤ P/i`.  Hence `Z = ⋂ᵢ {F ≠ Gᵢ}` is
`Lᵐ`-null, `E = F(Z)` has `Hᵐ(E) ≤ Kᵐ Hᵐ(Z) = Kᵐ Lᵐ(Z) = 0`, and off `Z`, `F = Gᵢ` for some `i`. -/
theorem Submission.dor_lmbsf_c1c_lipschitz_range_c1_pieces : ∀ (P m : ℕ) (F : Euclid m → Euclid P) (K : NNReal), LipschitzWith K F → (∀ (u : Euclid m → ℝ) (L : NNReal), LipschitzWith L u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid m → ℝ, ContDiff ℝ 1 g ∧ volume {y | u y ≠ g y} < ε) → ∃ (E : Set (Euclid P)) (G : ℕ → Euclid m → Euclid P), μHE[m] E = 0 ∧ (∀ i, ContDiff ℝ 1 (G i)) ∧ Set.range F ⊆ E ∪ ⋃ i, Set.range (G i) := by
  intro P m F K hF H
  -- the coordinates `Fᵖ` are `K`-Lipschitz, since `|a_p| ≤ |a|`
  have hcoord : ∀ p : Fin P, LipschitzWith K fun y => F y p := by
    intro p
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    calc dist (F a p) (F b p) = ‖(F a - F b) p‖ := by
          rw [PiLp.sub_apply, Real.dist_eq, Real.norm_eq_abs]
      _ ≤ ‖F a - F b‖ := PiLp.norm_apply_le _ _
      _ = dist (F a) (F b) := (dist_eq_norm _ _).symm
      _ ≤ K * dist a b := hF.dist_le_mul a b
  -- (H) for each coordinate with `ε = 1/i`: `Lᵐ({Fᵖ ≠ g_{ip}}) < 1/i`
  choose g hg hgvol using fun (i : ℕ) (p : Fin P) =>
    H (fun y => F y p) K (hcoord p) (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
  -- `Gᵢ = (g_{ip})_p` is `C¹`
  obtain ⟨G, hGp⟩ : ∃ G : ℕ → Euclid m → Euclid P, ∀ i y p, G i y p = g i p y :=
    ⟨fun i y => WithLp.toLp 2 fun p => g i p y, fun _ _ _ => rfl⟩
  have hGc : ∀ i, ContDiff ℝ 1 (G i) := fun i =>
    (contDiff_piLp 2).2 fun p => by simpa only [hGp] using hg i p
  -- `Z = ⋂ᵢ {F ≠ Gᵢ}`: `Lᵐ(Z) ≤ Lᵐ({F ≠ Gᵢ}) ≤ Σ_p Lᵐ({Fᵖ ≠ g_{ip}}) ≤ P/i`
  set Z : Set (Euclid m) := ⋂ i, {y | F y ≠ G i y} with hZ_def
  have hZi : ∀ i : ℕ, volume Z ≤ (P : ℝ≥0∞) * (i : ℝ≥0∞)⁻¹ := by
    intro i
    calc volume Z ≤ volume (⋃ p : Fin P, {y | F y p ≠ g i p y}) := by
          refine measure_mono fun y hy => ?_
          have hne : F y ≠ G i y := mem_iInter.1 hy i
          by_contra hcon
          simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
          exact hne (PiLp.ext fun p => by rw [hGp, hcon p])
      _ ≤ ∑ p : Fin P, volume {y | F y p ≠ g i p y} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : Fin P, (i : ℝ≥0∞)⁻¹ := Finset.sum_le_sum fun p _ => (hgvol i p).le
      _ = (P : ℝ≥0∞) * (i : ℝ≥0∞)⁻¹ := by simp
  -- `P/i → 0`, so `Lᵐ(Z) = 0`
  have hZ0 : volume Z = 0 := by
    have ht := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top P))
    rw [mul_zero] at ht
    exact le_antisymm (ge_of_tendsto' ht hZi) zero_le
  refine ⟨F '' Z, G, ?_, hGc, ?_⟩
  · -- `Hᵐ(F(Z)) ≤ Kᵐ Hᵐ(Z) = Kᵐ Lᵐ(Z) = 0`
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
      (hF.lipschitzOnWith (s := Z))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m, hZ0, mul_zero] at h
    exact le_antisymm h zero_le
  · -- `F z ∈ F(Z)` if `z ∈ Z`, otherwise `F z = Gᵢ z` for some `i`
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Z
    · exact Or.inl ⟨z, hz, rfl⟩
    · rw [hZ_def] at hz
      simp only [mem_iInter, mem_ofPred_eq, not_forall, not_not] at hz
      obtain ⟨i, hi⟩ := hz
      exact Or.inr (mem_iUnion.2 ⟨i, z, hi.symm⟩)
/-- **Simon Ch. 3, proof of Lemma 1.2 ("only if"), last paragraph**, for one `C¹` map
`G : ℝᵐ → ℝᴾ`: `G(ℝᵐ) ⊆ N₀ ∪ ⋃ₗ Nₗ` with `Hᵐ(N₀) = 0` and each `Nₗ` an embedded `C¹`
`m`-submanifold.  `N₀ = G({x : DG(x) not injective})` is `Hᵐ`-null (Simon: by the area formula of
Ch. 2 §3).  Here this is checked directly: if `DG(x) e = 0`, `|e| = 1`, and `‖DG - DG(x)‖ ≤ λM`,
`‖DG‖ ≤ M` on `B̄_ρ(x)`, then with `Ψ = id + (λ⁻¹ - 1) e ⊗ e` (`det Ψ = λ⁻¹`) the map `G ∘ Ψ` is
`2M`-Lipschitz on `Ψ⁻¹(B̄_ρ(x))`, so `Hᵐ(G(B̄_ρ(x))) ≤ (2M)ᵐ λ |B̄_ρ(x)|`; a Besicovitch disjoint
cover of the critical points in `B_R(0)` gives `Hᵐ(G(·)) ≤ (2M)ᵐ λ |B̄_{R+1}(0)|` for every `λ`.
At a regular point `x`, `G` is injective with injective derivative on some `B̄_{r_x}(x)`, so
`G(B_{r_x}(x))` is a submanifold; countably many of these balls cover the regular set (Lindelöf,
left implicit by Simon), and no ball is needed if it is empty. -/
theorem Submission.dor_lmbsf_c1c_c1_range_cover : ∀ (P m : ℕ) (G : Euclid m → Euclid P), ContDiff ℝ 1 G → ∃ (N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), μHE[m] N₀ = 0 ∧ (∀ l, IsEmbeddedSubmanifold 1 m (N l)) ∧ Set.range G ⊆ N₀ ∪ ⋃ l, N l := by
  intro P m G hG
  -- Step 1: `G` is differentiable everywhere, with continuous derivative.
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- Step 2: the critical image `N₀ = G({x : DG(x) not injective})` is `Hᵐ`-null.
  have hN₀ : μHE[m] (G '' {x | ¬ Injective (fderiv ℝ G x)}) = 0 := by
    have hvol : (μHE[m] : Measure (Euclid m)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
    have hcov : {x | ¬ Injective (fderiv ℝ G x)} =
        ⋃ k : ℕ, {x | ¬ Injective (fderiv ℝ G x)} ∩ ball (0 : Euclid m) k := by
      rw [← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hcov, image_iUnion]
    refine measure_iUnion_null fun k => ?_
    set R : ℝ := (k : ℝ)
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Euclid m) (R + 1)).exists_bound_of_continuousOn
      hDG.continuousOn
    set M : ℝ := max M₀ 1
    have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hMK : ∀ y ∈ closedBall (0 : Euclid m) (R + 1), ‖fderiv ℝ G y‖ ≤ M :=
      fun y hy => (hM₀ y hy).trans (le_max_left _ _)
    -- one ball `B̄_ρ(x)` around a critical point `x`
    have hloc : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ x, ¬ Injective (fderiv ℝ G x) → ∀ ρ : ℝ,
        (∀ y ∈ closedBall x ρ, ‖fderiv ℝ G y - fderiv ℝ G x‖ ≤ lam * M) →
        closedBall x ρ ⊆ closedBall 0 (R + 1) →
        μHE[m] (G '' closedBall x ρ) ≤
          ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam * volume (closedBall x ρ) := by
      intro lam hlam0 hlam1 x hx ρ hρ hρK
      obtain ⟨v, hv0, hv⟩ : ∃ v, fderiv ℝ G x v = 0 ∧ v ≠ 0 := by
        simpa only [injective_iff_map_eq_zero, not_forall, exists_prop] using hx
      set e : Euclid m := (‖v‖⁻¹ : ℝ) • v
      have he : ‖e‖ = 1 := norm_smul_inv_norm hv
      have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
      have hDe : fderiv ℝ G x e = 0 := by simp [e, hv0]
      set Ψ : Euclid m →L[ℝ] Euclid m :=
        ContinuousLinearMap.id ℝ _ + (lam⁻¹ - 1) • (innerSL ℝ e).smulRight e
      have hΨ : ∀ u, Ψ u = u + ((lam⁻¹ - 1) * inner ℝ e u) • e := by
        intro u
        simp [Ψ, smul_smul]
      -- `det Ψ = 1 + (λ⁻¹ - 1) |e|² = λ⁻¹` (matrix determinant lemma)
      have hdet : LinearMap.det (Ψ : Euclid m →ₗ[ℝ] Euclid m) = lam⁻¹ := by
        have hee' : e.ofLp ⬝ᵥ e.ofLp = 1 := by
          rw [← hee, EuclideanSpace.inner_eq_star_dotProduct]
          simp
        set b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        have hmat : LinearMap.toMatrix b b (Ψ : Euclid m →ₗ[ℝ] Euclid m) =
            1 + Matrix.replicateCol Unit ((lam⁻¹ - 1) • e.ofLp) * Matrix.replicateRow Unit e.ofLp := by
          ext i j
          simp [LinearMap.toMatrix_apply, b, hΨ, Matrix.one_apply, Matrix.mul_apply,
            EuclideanSpace.inner_single_right, PiLp.single_apply]
          ring
        rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_one_add_replicateCol_mul_replicateRow,
          dotProduct_smul, hee', smul_eq_mul, mul_one]
        ring
      have hsurj : Surjective Ψ := by
        intro y
        refine ⟨y + ((lam - 1) * inner ℝ e y) • e, ?_⟩
        have hcoef : (lam - 1) * inner ℝ e y +
            (lam⁻¹ - 1) * (inner ℝ e y + (lam - 1) * inner ℝ e y * 1) = 0 := by
          field_simp
          ring
        rw [hΨ, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul, hcoef, zero_smul,
          add_zero]
      -- `D(G ∘ Ψ) u = DG u + (λ⁻¹ - 1) ⟨e, u⟩ DG e` with `‖DG e‖ = ‖(DG - DG(x)) e‖ ≤ λM`
      have hLip : LipschitzOnWith (2 * M).toNNReal (G ∘ Ψ) (Ψ ⁻¹' closedBall x ρ) := by
        refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
          (fun z _ => (hGd (Ψ z)).comp z Ψ.differentiableAt) (fun z hz => ?_)
          ((convex_closedBall x ρ).linear_preimage (Ψ : Euclid m →ₗ[ℝ] Euclid m))
        have hy : Ψ z ∈ closedBall x ρ := hz
        rw [fderiv_comp z (hGd (Ψ z)) Ψ.differentiableAt, ContinuousLinearMap.fderiv,
          ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
        have h1 : ‖fderiv ℝ G (Ψ z) u‖ ≤ M * ‖u‖ :=
          ((fderiv ℝ G (Ψ z)).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right (hMK _ (hρK hy)) (norm_nonneg _))
        have h2 : ‖fderiv ℝ G (Ψ z) e‖ ≤ lam * M := by
          have h3 : fderiv ℝ G (Ψ z) e = (fderiv ℝ G (Ψ z) - fderiv ℝ G x) e := by
            rw [sub_apply, hDe, sub_zero]
          rw [h3]
          calc ‖(fderiv ℝ G (Ψ z) - fderiv ℝ G x) e‖
              ≤ ‖fderiv ℝ G (Ψ z) - fderiv ℝ G x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ lam * M := by rw [he, mul_one]; exact hρ _ hy
        have h4 : |lam⁻¹ - 1| ≤ lam⁻¹ := by
          have : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam0).2 hlam1
          rw [abs_of_nonneg (by linarith)]
          linarith
        have h5 : |inner ℝ e u| ≤ ‖u‖ := by
          simpa [he] using abs_real_inner_le_norm e u
        rw [ContinuousLinearMap.comp_apply, hΨ u, map_add, map_smul]
        calc ‖fderiv ℝ G (Ψ z) u + ((lam⁻¹ - 1) * inner ℝ e u) • fderiv ℝ G (Ψ z) e‖
            ≤ ‖fderiv ℝ G (Ψ z) u‖ + ‖((lam⁻¹ - 1) * inner ℝ e u) • fderiv ℝ G (Ψ z) e‖ :=
              norm_add_le _ _
          _ = ‖fderiv ℝ G (Ψ z) u‖ + |lam⁻¹ - 1| * |inner ℝ e u| * ‖fderiv ℝ G (Ψ z) e‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_mul]
          _ ≤ M * ‖u‖ + lam⁻¹ * ‖u‖ * (lam * M) := by gcongr
          _ = 2 * M * ‖u‖ := by
              rw [show lam⁻¹ * ‖u‖ * (lam * M) = (lam⁻¹ * lam) * (M * ‖u‖) by ring,
                inv_mul_cancel₀ hlam0.ne', one_mul]
              ring
      have hvolΨ : volume (Ψ ⁻¹' closedBall x ρ) = ENNReal.ofReal lam * volume (closedBall x ρ) := by
        rw [Measure.addHaar_preimage_continuousLinearMap volume
          (by rw [hdet]; exact inv_ne_zero hlam0.ne'), hdet, inv_inv, abs_of_pos hlam0]
      calc μHE[m] (G '' closedBall x ρ) = μHE[m] ((G ∘ Ψ) '' (Ψ ⁻¹' closedBall x ρ)) := by
            rw [image_comp, image_preimage_eq _ hsurj]
        _ ≤ ((2 * M).toNNReal : ℝ≥0∞) ^ m * μHE[m] (Ψ ⁻¹' closedBall x ρ) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hLip
        _ = ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam * volume (closedBall x ρ) := by
            rw [hvol, hvolΨ, mul_assoc]
    -- `G` is `M`-Lipschitz on `B̄_{R+1}(0)`, so it maps volume-null sets there to `Hᵐ`-null sets
    have hLipK : LipschitzOnWith M.toNNReal G (closedBall 0 (R + 1)) := by
      refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun y _ => hGd y)
        (fun y hy => ?_) (convex_closedBall _ _)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM.le]
      exact hMK y hy
    -- Besicovitch: disjoint balls `B̄_{ρ x}(x)` with `ρ x < r x` cover almost all critical points
    have hmain : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        μHE[m] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R)) ≤
          ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
            volume (closedBall (0 : Euclid m) (R + 1)) := by
      intro lam hlam0 hlam1
      have hr : ∀ x : Euclid m, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
          ∀ y ∈ ball x r, ‖fderiv ℝ G y - fderiv ℝ G x‖ < lam * M := by
        intro x
        obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hDG x (lam * M) (by positivity)
        refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun y hy => ?_⟩
        have h := hδ' y (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
        rwa [dist_eq_norm] at h
      choose r hr0 hr1 hr using hr
      obtain ⟨t, ρ, ht, hts, hρ, hnull, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae
        volume (fun _ => univ) ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R)
        (fun _ _ δ hδ => ⟨δ / 2, mem_univ _, half_pos hδ, half_lt_self hδ⟩) r (fun x _ => hr0 x)
      have hballK : ∀ x ∈ t, closedBall x (ρ x) ⊆ closedBall 0 (R + 1) := by
        intro x hx y hy
        have hx' : ‖x‖ < R := mem_ball_zero_iff.1 (hts hx).2
        rw [mem_closedBall, dist_eq_norm] at hy
        rw [mem_closedBall_zero_iff]
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith [(hρ x hx).2.2, hr1 x]
      have hsub : G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) ⊆
          G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \ ⋃ x ∈ t, closedBall x (ρ x)) ∪
            ⋃ x ∈ t, G '' closedBall x (ρ x) := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases hyU : y ∈ ⋃ x ∈ t, closedBall x (ρ x)
        · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
          exact Or.inr (mem_iUnion₂.2 ⟨x, hx, mem_image_of_mem G hyx⟩)
        · exact Or.inl (mem_image_of_mem G ⟨hy, hyU⟩)
      have h0 : μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
          ⋃ x ∈ t, closedBall x (ρ x))) = 0 := by
        refine le_antisymm ?_ bot_le
        calc μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
                ⋃ x ∈ t, closedBall x (ρ x)))
            ≤ (M.toNNReal : ℝ≥0∞) ^ m * μHE[m] (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
                ⋃ x ∈ t, closedBall x (ρ x)) :=
              Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
                (hLipK.mono fun y hy =>
                  closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy.1.2))
          _ = 0 := by rw [hvol, hnull, mul_zero]
      calc μHE[m] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R))
          ≤ μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
              ⋃ x ∈ t, closedBall x (ρ x))) + μHE[m] (⋃ x ∈ t, G '' closedBall x (ρ x)) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ∑' x : t, μHE[m] (G '' closedBall (x : Euclid m) (ρ x)) := by
            rw [h0, zero_add]
            exact measure_biUnion_le _ ht _
        _ ≤ ∑' x : t, ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (closedBall (x : Euclid m) (ρ x)) :=
            ENNReal.tsum_le_tsum fun x => hloc lam hlam0 hlam1 x (hts x.2).1 (ρ x)
              (fun y hy => (hr x y (closedBall_subset_ball (hρ x x.2).2.2 hy)).le) (hballK x x.2)
        _ = ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (⋃ x ∈ t, closedBall x (ρ x)) := by
            rw [ENNReal.tsum_mul_left, measure_biUnion ht hdisj fun _ _ => measurableSet_closedBall]
        _ ≤ ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (closedBall (0 : Euclid m) (R + 1)) := by
            gcongr
            exact iUnion₂_subset hballK
    -- let `λ → 0`
    have hlim : Tendsto (fun lam : ℝ => ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
        volume (closedBall (0 : Euclid m) (R + 1))) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun lam : ℝ => ENNReal.ofReal lam) (𝓝[>] 0) (𝓝 0) := by
        simpa using (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
          nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul h1
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))) (Or.inr measure_closedBall_lt_top.ne)
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Ioo_mem_nhdsGT one_pos] with lam hlam
    exact hmain lam hlam.1 hlam.2.le
  have hcrit : ∀ x, ¬ Injective (fderiv ℝ G x) → G x ∈ G '' {x | ¬ Injective (fderiv ℝ G x)} :=
    fun x hx => mem_image_of_mem G hx
  -- Step 3: at a regular point `x`, `G(B_{r_x}(x))` is an embedded `C¹` `m`-submanifold.
  have hchart : ∀ x : {x : Euclid m // Injective (fderiv ℝ G x)}, ∃ r : ℝ, 0 < r ∧
      IsEmbeddedSubmanifold 1 m (G '' ball (x : Euclid m) r) := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, hinj, hder⟩ := Submission.dor_lmbsf_c1c_immersion_local_injOn P m G x hG hx
    exact ⟨r, hr, Submission.dor_lmbsf_c1c_injOn_closedBall_chart P m G x r hG hinj
      fun z hz => hder z (ball_subset_closedBall hz)⟩
  choose r hr hN using hchart
  -- Step 4: with no regular point, `Nₗ = ∅` (vacuously a submanifold) and `G(ℝᵐ) ⊆ N₀`.
  rcases isEmpty_or_nonempty {x : Euclid m // Injective (fderiv ℝ G x)} with hR | hR
  · refine ⟨_, fun _ => ∅, hN₀, fun _ y hy => absurd hy (notMem_empty y), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Or.inl (hcrit x fun hx => hR.false ⟨x, hx⟩)
  -- Otherwise countably many balls `B_{r_{xₗ}}(xₗ)` cover the regular set (Lindelöf).
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof
    {x : Euclid m | Injective (fderiv ℝ G x)}).indexed_countable_subcover
    (fun x : {x : Euclid m // Injective (fderiv ℝ G x)} => ball (x : Euclid m) (r x))
    (fun _ => isOpen_ball) fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩
  refine ⟨_, fun l => G '' ball (f l : Euclid m) (r (f l)), hN₀, fun l => hN (f l), ?_⟩
  -- Step 5: `G(x) ∈ N₀` if `x` is critical, and `G(x) ∈ Nₗ` if `x ∈ B_{r_{xₗ}}(xₗ)`.
  rintro _ ⟨x, rfl⟩
  by_cases hx : Injective (fderiv ℝ G x)
  · obtain ⟨l, hl⟩ := mem_iUnion.mp
      (hf (show x ∈ {x : Euclid m | Injective (fderiv ℝ G x)} from hx))
    exact Or.inr (mem_iUnion.mpr ⟨l, mem_image_of_mem G hl⟩)
  · exact Or.inl (hcrit x hx)
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** for `Lⁿ` with a closed set, `Lⁿ(B) = ∞` allowed (Simon Ch. 2, proof of
1.5, step 2, glued as in the infinite-measure case of Simon 1.15(2)).  On the bounded Borel shells
`S_j = {j ≤ ‖x‖ < j + 1}`, the compact form `dor_ims_lusin_measurable_continuousOn` gives compact
`K_j ⊆ B ∩ S_j` with `Lⁿ((B ∩ S_j) \ K_j) < δ_j` on which `g` is continuous, where `∑ δ_j < ε`.
As `K_j ⊆ S_j`, the family `(K_j)` is locally finite, so `C = ⋃ⱼ K_j` is closed and `g` is
continuous on `C`; and `B \ C ⊆ ⋃ⱼ (B ∩ S_j) \ K_j` has measure `< ε`. -/
theorem Submission.codim1_rdo_c1a_lusin_isClosed : ∀ (n : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (g : Euclid n → Y) (B : Set (Euclid n)), Measurable g → MeasurableSet B → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Euclid n), C ⊆ B ∧ IsClosed C ∧ ContinuousOn g C ∧ volume (B \ C) < ε := by
  intro n Y _ _ _ _ g B hg hB ε hε
  -- bounded Borel shells `S_j = {j ≤ ‖x‖ < j + 1}`, each of finite measure; `x ∈ S_⌊‖x‖⌋`
  set S : ℕ → Set (Euclid n) := fun j => {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hSμ : ∀ j, volume (S j) ≠ ∞ := fun j =>
    ((measure_mono fun x hx => mem_closedBall_zero_iff.mpr hx.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hxS : ∀ x : Euclid n, x ∈ S ⌊‖x‖⌋₊ := fun x =>
    ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- weights `δ_j > 0` with `∑ δ_j < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  -- Lusin on each shell: compact `K_j ⊆ B ∩ S_j`, defect `< δ_j`, `g` continuous on `K_j`
  choose K hK hKB hKμ hKg using fun j =>
    Submission.dor_ims_lusin_measurable_continuousOn n volume (B ∩ S j) g (δ j) hg
      (hB.inter (hSm j)) (ne_top_of_le_ne_top (hSμ j) (measure_mono inter_subset_right))
      (hδ j).ne'
  -- `K_j ⊆ S_j`, so `ball x 1` meets `K_j` only for the finitely many `j < ‖x‖ + 1`
  have hlf : LocallyFinite K := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyK, hyx⟩
    refine Nat.lt_ceil.mpr ((hKB j hyK).2.1.trans_lt ?_)
    calc ‖y‖ ≤ ‖x‖ + dist y x := norm_le_norm_add_const_of_dist_le le_rfl
      _ < ‖x‖ + 1 := by linarith [mem_ball.mp hyx]
  -- hence `C = ⋃ⱼ K_j` is closed and `g` is continuous on `C`
  refine ⟨⋃ j, K j, iUnion_subset fun j => (hKB j).trans inter_subset_left,
    hlf.isClosed_iUnion fun j => (hK j).isClosed,
    hlf.continuousOn_iUnion (fun j => (hK j).isClosed) hKg, ?_⟩
  -- `x ∈ B \ C` lies in `(B ∩ S_j) \ K_j` for `j = ⌊‖x‖⌋`
  calc volume (B \ ⋃ j, K j) ≤ volume (⋃ j, (B ∩ S j) \ K j) :=
        measure_mono fun x hx => mem_iUnion.mpr
          ⟨⌊‖x‖⌋₊, ⟨hx.1, hxS x⟩, fun hxK => hx.2 (mem_iUnion_of_mem _ hxK)⟩
    _ ≤ ∑' j, volume ((B ∩ S j) \ K j) := measure_iUnion_le _
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (hKμ j).le
    _ < ε := hδε
/-- **Egoroff's theorem** on `ℝⁿ` with a closed good set (steps 5–6 of Simon's proof of Ch. 2,
1.5).  If `C` is measurable (possibly `|C| = ∞`), `η_k` and `g` are measurable and `η_k → g`
pointwise on `C`, then for every `ε > 0` there is a closed `A ⊆ C` with `|C \ A| < ε` such that
`η_k → g` uniformly on every compact `Q ⊆ A`.  For weights `δ_j > 0` with `∑ δ_j < ε`, Egoroff on
the finite-measure sets `C ∩ B_{j+1}(0)` gives `t_j` with `|t_j| ≤ δ_j / 2`; put
`A₀ = C \ ⋃ t_j`.  Outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with excess `< δ_j / 2`,
so `A = (⋃ U_j)ᶜ ⊆ A₀` is closed and `C \ A ⊆ ⋃ (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`.  A compact
`Q ⊆ A` is bounded, so `Q ⊆ (C ∩ B_{j+1}(0)) \ t_j` for large `j`. -/
theorem Submission.codim1_rdo_c1a_egorov_isClosed : ∀ (n : ℕ) (C : Set (Euclid n)) (η : ℕ → Euclid n → ℝ) (g : Euclid n → ℝ), MeasurableSet C → (∀ k, Measurable (η k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q := by
  intro n C η g hC hη hg hconv ε hε
  -- weights `δ_j > 0` with `∑ δ_j < ε`; every `s ∩ B_{j+1}(0)` has finite measure
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have hB : ∀ (j : ℕ) (s : Set (Euclid n)), volume (s ∩ ball 0 (j + 1)) ≠ ∞ := fun j s =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Egoroff on `C_j = C ∩ B_{j+1}(0)`: `η_k → g` uniformly on `C_j \ t_j`, `|t_j| ≤ δ_j / 2`
  choose t htC htm htμ htu using fun j : ℕ =>
    tendstoUniformlyOn_of_ae_tendsto (μ := volume) (fun k => (hη k).stronglyMeasurable)
      hg.stronglyMeasurable (hC.inter measurableSet_ball) (hB j C)
      (ae_of_all _ fun x hx => hconv x hx.1) (ENNReal.half_pos (hδ j).ne')
  -- `A₀ = C \ ⋃ t_j`; outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with small excess
  have hA₀ : MeasurableSet (C \ ⋃ j, t j) := hC.diff (MeasurableSet.iUnion htm)
  choose U hUD hUo hUf hUμ using fun j : ℕ =>
    (hA₀.compl.inter measurableSet_ball).exists_isOpen_sdiff_lt (hB j _)
      (ENNReal.half_pos (hδ j).ne').ne'
  -- the balls cover `A₀ᶜ`, so the closed set `A = (⋃ U_j)ᶜ` lies in `A₀`
  have hAA₀ : (⋃ j, U j)ᶜ ⊆ C \ ⋃ j, t j := by
    refine compl_subset_comm.1 fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨j, hUD j ⟨hx, mem_ball.2 (by linarith)⟩⟩
  refine ⟨(⋃ j, U j)ᶜ, hAA₀.trans sdiff_subset, (isOpen_iUnion hUo).isClosed_compl, ?_, ?_⟩
  -- `C \ A ⊆ ⋃_j (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`, and each piece has measure `≤ δ_j`
  · calc volume (C \ (⋃ j, U j)ᶜ)
        ≤ volume (⋃ j, (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1))))) := by
          refine measure_mono fun x ⟨hxC, hxU⟩ => ?_
          obtain ⟨j, hj⟩ := mem_iUnion.1 (not_not.1 hxU)
          by_cases hxt : x ∈ ⋃ i, t i
          · obtain ⟨i, hi⟩ := mem_iUnion.1 hxt
            exact mem_iUnion.2 ⟨i, Or.inl hi⟩
          · exact mem_iUnion.2 ⟨j, Or.inr ⟨hj, fun h => h.1 ⟨hxC, hxt⟩⟩⟩
      _ ≤ ∑' j, volume (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1)))) :=
          measure_iUnion_le _
      _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (measure_union_le _ _).trans <|
          (add_le_add (htμ j) (hUμ j).le).trans (ENNReal.add_halves _).le
      _ < ε := hδε
  -- a compact `Q ⊆ A` is bounded, so `Q ⊆ C_j \ t_j` for large `j`
  · intro Q hQ hQA
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball 0
    obtain ⟨j, hj⟩ := exists_nat_ge R
    refine (htu j).mono fun x hx => ⟨⟨(hAA₀ (hQA hx)).1, ?_⟩, fun hxt => ?_⟩
    · exact ball_subset_ball (by linarith) (hR hx)
    · exact (hAA₀ (hQA hx)).2 (mem_iUnion.2 ⟨j, hxt⟩)
/-- **Whitney's hypothesis 1.6(∗) on a large closed set** (Simon Ch. 2, proof of Theorem 1.5).
Let `f : ℝⁿ → ℝ` be `L`-Lipschitz and differentiable at every point of the closed set `C`, with
`Df` continuous on `C`.  The remainder quotient `R(x, y) = |f(y) − f(x) − Df(x)(y − x)| / |y − x|`
is at most `2L`, and `η_k(x) = sup {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}` (`0` off `C`)
tends to `0` on `C`.  Each `{η_k > t}`, `t ≥ 0`, is relatively open in `C`, so `η_k` is Borel,
and Egorov's theorem in closed form gives a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that
`η_k → 0` uniformly on every compact `Q ⊆ A`.  Then `R(x, y) ≤ η_k(x) < ε'` for `x ∈ Q`,
`y ∈ A`, `0 < |x − y| < 1/(k + 1)`. -/
theorem Submission.codim1_rdo_c1a_whitney_remainder : ∀ (n : ℕ) (f : Euclid n → ℝ) (L : NNReal) (C : Set (Euclid n)), LipschitzWith L f → IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ f x) → ContinuousOn (fderiv ℝ f) C → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε' * ‖y - x‖ := by
  intro n f L C hf hC hdiff hDf ε hε
  classical
  -- the remainder quotient `R(x, y)`, bounded by `2L` since `‖Df(x)‖ ≤ L`
  let R : Euclid n → Euclid n → ℝ := fun x y => ‖f y - f x - fderiv ℝ f x (y - x)‖ / ‖y - x‖
  have hR_le : ∀ x y, R x y ≤ 2 * L := by
    intro x y
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ‖f y - f x‖ + ‖fderiv ℝ f x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖y - x‖ + L * ‖y - x‖ := by
          refine add_le_add ?_ ?_
          · rw [← dist_eq_norm, ← dist_eq_norm]
            exact hf.dist_le_mul y x
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      _ = 2 * L * ‖y - x‖ := by ring
  -- `η_k(x) = sup E_k(x)`, `E_k(x) = {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}`, on `C`
  let E : ℕ → Euclid n → Set ℝ := fun k x =>
    R x '' {y | y ∈ C ∧ 0 < dist y x ∧ dist y x < 1 / ((k : ℝ) + 1)}
  let η : ℕ → Euclid n → ℝ := fun k x => if x ∈ C then sSup (E k x) else 0
  have hη_nonneg : ∀ k x, 0 ≤ η k x := by
    intro k x
    by_cases hx : x ∈ C
    · simp only [η, ite_eq_left hx]
      exact Real.sSup_nonneg (by
        rintro _ ⟨y, -, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [η, ite_eq_right hx, le_refl]
  have hR_le_η : ∀ (k : ℕ) x y, x ∈ C → y ∈ C → 0 < dist y x → dist y x < 1 / ((k : ℝ) + 1) →
      R x y ≤ η k x := by
    intro k x y hx hy h0 h1
    simp only [η, ite_eq_left hx]
    exact le_csSup ⟨2 * L, by rintro _ ⟨z, -, rfl⟩; exact hR_le x z⟩ ⟨y, ⟨hy, h0, h1⟩, rfl⟩
  -- `η_k(x) → 0` for `x ∈ C`, by differentiability of `f` at `x`
  have hη_tendsto : ∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨ρ, hρ, hρx⟩ :=
      Metric.eventually_nhds_iff.mp ((hdiff x hx).hasFDerivAt.isLittleO.bound (half_pos he))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hle : η k x ≤ e / 2 := by
      simp only [η, ite_eq_left hx]
      refine Real.sSup_le ?_ (half_pos he).le
      rintro _ ⟨y, ⟨-, -, h1⟩, rfl⟩
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos he).le
        (hρx (h1.trans_le ((Nat.one_div_le_one_div hk).trans hN.le)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hη_nonneg k x)]
    exact hle.trans_lt (half_lt_self he)
  -- `{η_k > t}` is relatively open in the closed set `C` for `t ≥ 0`, so `η_k` is Borel
  have hη_meas : ∀ k, Measurable (η k) := by
    intro k
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · convert MeasurableSet.univ
      exact eq_univ_of_forall fun x => ht.trans_le (hη_nonneg k x)
    have hUC : η k ⁻¹' Ioi t ⊆ C := by
      intro x hx
      by_contra hxC
      have hx' : t < η k x := hx
      simp only [η, ite_eq_right hxC] at hx'
      exact absurd hx' (not_lt.mpr ht)
    have hnhds : ∀ x ∈ η k ⁻¹' Ioi t, η k ⁻¹' Ioi t ∪ Cᶜ ∈ 𝓝 x := by
      intro x hx
      have hxC := hUC hx
      have hxt : t < sSup (E k x) := by
        have hx' : t < η k x := hx
        simpa only [η, ite_eq_left hxC] using hx'
      have hne : (E k x).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Real.sSup_empty] at hxt
        exact absurd hxt (not_lt.mpr ht)
      obtain ⟨_, ⟨y, ⟨hy, h0, h1⟩, rfl⟩, hty⟩ := exists_lt_of_lt_csSup hne hxt
      -- `z ↦ R(z, y)` is continuous within `C` at `x`, as `f` and `Df|_C` are continuous
      have hsub : ContinuousWithinAt (fun z => y - z) C x :=
        continuousWithinAt_const.sub continuousWithinAt_id
      have hnum : ContinuousWithinAt (fun z => ‖f y - f z - fderiv ℝ f z (y - z)‖) C x :=
        ((continuousWithinAt_const.sub hf.continuous.continuousWithinAt).sub
          ((hDf x hxC).clm_apply hsub)).norm
      have hRy : ContinuousWithinAt (fun z => R z y) C x :=
        hnum.div hsub.norm (norm_sub_pos_iff.mpr (dist_pos.mp h0)).ne'
      have hdist : Tendsto (fun z => dist y z) (𝓝 x) (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist tendsto_id
      -- near `x`, every `z ∈ C` has `η_k(z) ≥ R(z, y) > t`
      filter_upwards [eventually_nhdsWithin_iff.mp (Filter.Tendsto.eventually_const_lt hty hRy),
        hdist.eventually_const_lt h0, hdist.eventually_lt_const h1] with z hz hz0 hz1
      by_cases hzC : z ∈ C
      · exact Or.inl ((hz hzC).trans_le (hR_le_η k z y hzC hy hz0 hz1))
      · exact Or.inr hzC
    have heq : η k ⁻¹' Ioi t = C ∩ interior (η k ⁻¹' Ioi t ∪ Cᶜ) := by
      refine Subset.antisymm
        (fun x hx => ⟨hUC hx, mem_interior_iff_mem_nhds.mpr (hnhds x hx)⟩) ?_
      rintro x ⟨hxC, hxI⟩
      rcases interior_subset hxI with hx | hx
      · exact hx
      · exact absurd hxC hx
    rw [heq]
    exact hC.measurableSet.inter isOpen_interior.measurableSet
  -- Egorov on `C`: a closed `A ⊆ C`, `Lⁿ(C \ A) < ε`, with `η_k → 0` uniformly on compact `Q ⊆ A`
  obtain ⟨A, hAC, hA, hCA, hunif⟩ := Submission.codim1_rdo_c1a_egorov_isClosed n C η
    (fun _ => 0) hC.measurableSet hη_meas measurable_const hη_tendsto ε hε
  refine ⟨A, hAC, hA, hCA, fun Q hQ hQA ε' hε' => ?_⟩
  -- `η_k < ε'` on `Q` for some `k`; take `δ = 1/(k + 1)`
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp (hunif Q hQ hQA) ε' hε').exists
  refine ⟨1 / ((k : ℝ) + 1), Nat.one_div_pos_of_nat, fun x hx y hy hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have h0 : 0 < dist y x := dist_pos.mpr hyx
  have hηx : η k x < ε' := by
    have hkx := hk x hx
    rw [dist_comm, Real.dist_eq, sub_zero] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hR : R x y ≤ ε' :=
    (hR_le_η k x y (hAC (hQA hx)) (hAC hy) h0 (by rwa [dist_comm])).trans hηx.le
  exact (div_le_iff₀ (norm_sub_pos_iff.mpr hyx)).mp hR
/-- **Whitney's `C¹` extension theorem** (Simon Ch. 2, 1.6; proof of Evans–Gariepy §6.5).  If
`A ⊆ ℝⁿ` is closed, `h` and `D` are continuous on `A`, and the remainder
`h y - h x - D x (y - x)` is `o(|y - x|)` uniformly for `x` in compact subsets of `A`, then some
`g ∈ C¹(ℝⁿ)` has `g = h` and `Dg = D` on `A`.  With `r x = min(1, dist(x, A)) / 100`, Vitali's
lemma selects disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `ℝⁿ \ A`;
nearby radii are comparable, so the overlap is uniformly bounded.  Rescaled bumps divided by
their locally finite sum give a partition of unity `w c` on `ℝⁿ \ A` with
`∑ ‖D(w c)(x)‖ ≤ M / r x`.  Put `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`, where
`P b x = h b + D b (x - b)` and `pr c ∈ A` is a nearest point. -/
theorem Submission.codim1_rdo_c1a_whitney_extension : ∀ (n : ℕ) (A : Set (Euclid n)) (h : Euclid n → ℝ) (D : Euclid n → (Euclid n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖) → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧ ∀ a ∈ A, HasFDerivAt g (D a) a := by
  intro n A h D hA hh hD hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  -- the Whitney radius `r x = min 1 (dist x A) / 100`
  obtain ⟨r, hr⟩ : ∃ r : Euclid n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨_, fun _ => rfl⟩
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
    rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := fun x y => by
    have h₁ := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h₁
    have h₂ := (abs_sub_le_iff.mp h₁).1
    rw [hr, hr]; linarith
  -- radii of nearby centres are comparable
  have hnear : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := hrlip x c
    have h₂ := hrlip c x
    rw [dist_comm c x] at h₂
    have := hr0 x
    have := hr0 c
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Vitali: disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `Aᶜ`
  obtain ⟨Z, hZA, hZdisj, hZcov⟩ : ∃ Z ⊆ Aᶜ, Z.PairwiseDisjoint (fun c => ball c (r c)) ∧
      ∀ x ∉ A, ∃ c ∈ Z, dist x c < 4 * r c := by
    obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      Aᶜ (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
    refine ⟨s, hs, hd, fun x hx => ?_⟩
    obtain ⟨c, hcs, hxc⟩ := hc x hx
    exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
  have hsep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      simpa only [mem_ball, dist_comm] using lt_of_not_ge hlt
    exact Set.disjoint_left.mp (hZdisj hc hd hcd) hdc (mem_ball_self (hrpos d (hZA hd)))
  -- a `1/2`-separated subset of `B̄(0, 21)` has at most `N` points
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Euclid n), s ⊆ closedBall (0 : Euclid n) 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Euclid n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hssep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Euclid n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Euclid n) ≠ (y : Euclid n) := fun e => hxy' (Subtype.ext e)
      have hd := hssep x.property y.property hne'
      have htri := dist_triangle (x : Euclid n) (c x : Euclid n) (y : Euclid n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Euclid n) (c x : Euclid n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  -- bounded overlap: at most `N` centres are near any `x ∉ A`
  have hover : ∀ x ∉ A, {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := hrpos x hx
    let f : Euclid n → Euclid n := fun c => (r x)⁻¹ • (c - x)
    have hf : Injective f := by
      intro c d hcd
      have e := congrArg (fun z : Euclid n => r x • z) hcd
      simpa [f, smul_smul, hrx.ne'] using e
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖f c‖ ≤ 21 := by
      intro c hc
      have hd := (hnear x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      simp only [f]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep' : (f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun e => hcd (congrArg f e)
      have hdist := hsep c hc.1 d hd.1 hcd'
      have hrad := (hnear x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        simpa only [dist_eq_norm] using hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      simp only [f]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Euclid n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep'
    exact ⟨hfin.of_finite_image hf.injOn, by rwa [Set.ncard_image_of_injective _ hf] at hcard⟩
  -- the finite set `F x` of centres near `x ∉ A`
  have hfin : ∀ x ∉ A, {c : Z | dist x c ≤ r x + 10 * r c}.Finite := by
    intro x hx
    apply ((hover x hx).1.preimage (Subtype.val_injective (p := (· ∈ Z))).injOn).subset
    intro c hc
    exact ⟨c.property, hc⟩
  have hFex : ∀ x, ∃ s : Finset Z, x ∉ A → ∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun hx' => absurd hx hx'⟩
    · exact ⟨(hfin x hx).toFinset, fun _ c => by simp⟩
  choose F hF using hFex
  have hFcard : ∀ x ∉ A, (F x).card ≤ N := by
    intro x hx
    have hsub : (F x).map (Embedding.subtype _) ⊆ (hover x hx).1.toFinset := by
      intro c hc
      simp only [Finset.mem_map, Embedding.coe_subtype] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [Set.Finite.mem_toFinset]
      exact ⟨c'.property, (hF x hx c').mp hc'⟩
    calc (F x).card = ((F x).map (Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (hover x hx).1.toFinset.card := Finset.card_le_card hsub
      _ = {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard :=
          (Set.ncard_eq_toFinset_card _ _).symm
      _ ≤ N := (hover x hx).2
  -- a smooth bump `ψ = 1` on `B̄(0, 4)`, `ψ = 0` off `B(0, 8)`
  obtain ⟨ψ, hψc, hψ0, hψ1, hψin, hψout, L, hL⟩ : ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ 4 → ψ x = 1) ∧
      (∀ x, 8 ≤ ‖x‖ → ψ x = 0) ∧ ∃ L : NNReal, LipschitzWith L ψ := by
    let b : ContDiffBump (0 : Euclid n) := ⟨4, 8, by norm_num, by norm_num⟩
    have hb : ContDiff ℝ 1 b := b.contDiff
    obtain ⟨L, hL⟩ := hb.lipschitzWith_of_hasCompactSupport b.hasCompactSupport one_ne_zero
    refine ⟨b, hb, fun x => b.nonneg, fun x => b.le_one, fun x hx => ?_, fun x hx => ?_, L, hL⟩
    · exact b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    · apply notMem_support.mp
      rw [b.support_eq]
      exact fun hxb => absurd (mem_ball_zero_iff.mp hxb) (not_lt.mpr hx)
  -- the rescaled bumps `φ c x = ψ ((x - c) / r c)`
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid n → Euclid n → ℝ, ∀ c x, φ c x = ψ ((r c)⁻¹ • (x - c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hφfun : ∀ c, φ c = fun x => ψ ((r c)⁻¹ • (x - c)) := fun c => funext (hφ c)
  have hφc : ∀ c, ContDiff ℝ 1 (φ c) := by
    intro c
    rw [hφfun c]
    exact hψc.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hφ0 : ∀ c x, 0 ≤ φ c x := fun c x => by rw [hφ]; exact hψ0 _
  have hφin : ∀ c x, 0 < r c → dist x c ≤ 4 * r c → φ c x = 1 := by
    intro c x hc hx
    rw [hφ]
    apply hψin
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (r c)⁻¹ * dist x c ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have hφout : ∀ c x, 0 < r c → 8 * r c ≤ dist x c → φ c x = 0 := by
    intro c x hc hx
    rw [hφ]
    apply hψout
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * dist x c := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, hBb⟩ : ∃ B : ℝ, 0 < B ∧ ∀ c, 0 < r c → ∀ x, ‖fderiv ℝ (φ c) x‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c hc x => ?_⟩
    let ρ : NNReal := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Euclid n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (φ c) := by
      rw [hφfun c]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (φ c) x‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- near `x ∉ A`, only the bumps indexed by `F x` are active
  have hφzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → φ c y = 0 := by
    intro x hx y hy c hc
    apply hφout c y (hrpos c (hZA c.property))
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun e => hc ((hF x hx c).mpr e)
    have ht := dist_triangle x y (c : Euclid n)
    rw [dist_comm x y] at ht
    have := hr0 (c : Euclid n)
    linarith
  have hyA : ∀ x ∉ A, ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA'
    have hi := infDist_le_dist_of_mem (x := x) hyA'
    have hr' := hrd x
    rw [dist_comm x y] at hi
    linarith [hr0 x]
  -- the locally finite sum `S = ∑ φ c`
  obtain ⟨S, hS⟩ : ∃ S : Euclid n → ℝ, ∀ x, S x = ∑ᶠ c : Z, φ c x := ⟨_, fun _ => rfl⟩
  have hSnear : ∀ x ∉ A, ∀ y, dist y x < r x → S y = ∑ c ∈ F x, φ c y := by
    intro x hx y hy
    rw [hS]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hcF
    exact hc (hφzero x hx y hy c hcF)
  have hSev : ∀ x ∉ A, S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hSnear x hx y hy
  have hSc : ∀ x ∉ A, ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (c : Z) y => φ c y) (s := F x) fun c _ => hφc c).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hSfd : ∀ x ∉ A, fderiv ℝ S x = ∑ c ∈ F x, fderiv ℝ (φ c) x := by
    intro x hx
    rw [(hSev x hx).fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (hφc c).differentiable one_ne_zero x)
  have hS1 : ∀ x ∉ A, 1 ≤ S x := by
    intro x hx
    have hrx := hrpos x hx
    rw [hSnear x hx x (by simpa using hrx)]
    obtain ⟨c, hc, hxc⟩ := hZcov x hx
    have hi : (⟨c, hc⟩ : Z) ∈ F x := by
      rw [hF x hx]
      have := hr0 c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = φ c x := (hφin c x (hrpos c (hZA hc)) hxc.le).symm
      _ ≤ ∑ c ∈ F x, φ c x :=
          Finset.single_le_sum (f := fun c : Z => φ c x) (fun c _ => hφ0 c x) hi
  -- the partition of unity `w c = φ c / S` on `Aᶜ`
  obtain ⟨w, hw⟩ : ∃ w : Z → Euclid n → ℝ, ∀ c x, w c x = φ c x / S x := ⟨_, fun _ _ => rfl⟩
  have hwfun : ∀ c, w c = fun x => φ c x / S x := fun c => funext (hw c)
  have hwc : ∀ c : Z, ∀ x ∉ A, ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    rw [hwfun c]
    exact (hφc c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
  have hw0 : ∀ c : Z, ∀ x ∉ A, 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (hφ0 c x) (le_trans zero_le_one (hS1 x hx))
  have hwzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, hφzero x hx y hy c hc, zero_div]
  have hwsum : ∀ x ∉ A, ∀ y, dist y x < r x → ∑ c ∈ F x, w c y = 1 := by
    intro x hx y hy
    simp only [hw, ← Finset.sum_div, ← hSnear x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hyA x hx y hy))))
  have hwdsum : ∀ x ∉ A, ∑ c ∈ F x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ F x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hwsum x hx y hy
    have hh' := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh'
    rw [fderiv_fun_sum (fun c _ => (hwc c x hx).differentiableAt one_ne_zero)] at hh'
    exact hh'
  have hwd_le : ∀ x ∉ A, ∀ c : Z,
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
    intro x hx c
    have hS1x := hS1 x hx
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
    have hSi : (S x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1x
    have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ S x ^ 2 by nlinarith)
    have hb := ((hφc c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x := by
      simpa only [hwfun, div_eq_mul_inv, Function.comp_def] using hprod.fderiv
    rw [hder]
    have hb0 := hφ0 c x
    have hb1 : φ c x ≤ 1 := by rw [hφ]; exact hψ1 _
    calc ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x‖
        ≤ ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (φ c) x‖ :=
          norm_add_le _ _
      _ = φ c x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (φ c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (φ c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
  -- `∑_{c ∈ F x} ‖D w_c(x)‖ ≤ M / r x`
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∉ A, ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := hrpos x hx
    obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * B / r x := ⟨_, rfl⟩
    have hT : 0 ≤ T := by rw [hT_def]; positivity
    have hb' : ∀ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ T := by
      intro c hc
      have hcr := hrpos c (hZA c.property)
      have hlow := (hnear x c ((hF x hx c).mp hc)).1
      refine (hBb c hcr x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = T := by rw [hT_def]; ring
    have hcard : ((F x).card : ℝ) ≤ N := by exact_mod_cast hFcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSfd x hx]
      calc ‖∑ c ∈ F x, fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ F x, T := Finset.sum_le_sum hb'
        _ = ((F x).card : ℝ) * T := by simp
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ T + (N : ℝ) * T := fun c hc =>
      (hwd_le x hx c).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ ∑ _c ∈ F x, (T + (N : ℝ) * T) := Finset.sum_le_sum hw'
      _ = ((F x).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by rw [hT_def]; ring
  -- the affine jets `P b x = h b + D b (x - b)`
  obtain ⟨P, hP⟩ : ∃ P : Euclid n → Euclid n → ℝ, ∀ b x, P b x = h b + D b (x - b) :=
    ⟨_, fun _ _ => rfl⟩
  have hPfun : ∀ b, P b = fun x => h b + D b (x - b) := fun b => funext (hP b)
  have hPc : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    rw [hPfun b]
    exact contDiff_const.add ((D b).contDiff.comp (contDiff_id.sub contDiff_const))
  have hPd : ∀ b x, HasFDerivAt (P b) (D b) x := by
    intro b x
    have e := (((D b).hasFDerivAt (x := x)).sub_const (D b b)).const_add (h b)
    have hfun : (fun y => h b + D b (y - b)) = fun y => h b + (D b y - D b b) := by
      funext y
      rw [map_sub]
    rw [hPfun b, hfun]
    exact e
  have hPsub : ∀ a b x,
      ‖P b x - P a x‖ ≤ ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ := by
    intro a b x
    have heq : P b x - P a x = (h b - h a - D a (b - a)) + (D b - D a) (x - b) := by
      have hx : x - a = (x - b) + (b - a) := by abel
      simp only [hP, hx, map_add, sub_apply]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((D b - D a).le_opNorm (x - b)))
  -- nearest points `pr x ∈ A`
  choose pr hprA hprd using fun x => hA.exists_infDist_eq_dist hne x
  have hprle : ∀ x, ∀ a ∈ A, dist x (pr x) ≤ dist x a := by
    intro x a ha
    rw [← hprd x]
    exact infDist_le_dist_of_mem ha
  have hpr2 : ∀ x, ∀ a ∈ A, dist (pr x) a ≤ 2 * dist x a := by
    intro x a ha
    have ht := dist_triangle (pr x) x a
    rw [dist_comm (pr x) x] at ht
    linarith [hprle x a ha]
  have hanc1 : ∀ x ∉ A, ∀ c : Z, c ∈ F x → dist x (pr c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hd := (hnear x c ((hF x hx c).mp hc)).2.2
    have hr' := hrd x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Euclid n)) (y := x)
    have ht := dist_triangle x (c : Euclid n) (pr c)
    rw [dist_comm (c : Euclid n) x] at hi
    rw [← hprd (c : Euclid n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have hanc2 : ∀ x ∉ A, ∀ a ∈ A, ∀ c : Z, c ∈ F x → dist (pr c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := hanc1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (pr c) x a
    rw [dist_comm (pr c) x] at ht
    linarith
  -- uniform estimates near a point of `A`
  have hloc : ∀ a ∈ A, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ η) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖h c - h b - D b (c - b)‖ ≤ η * ‖c - b‖ := by
    intro a ha η hη
    obtain ⟨r₀, hr₀, hrem₀⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left η hη
    obtain ⟨η₀, hη₀, hD₀⟩ := Metric.continuousWithinAt_iff.mp (hD a ha) η hη
    have hδ1 : min 1 (min η₀ (r₀ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η₀ (r₀ / 3)) ≤ η₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hδr : min 1 (min η₀ (r₀ / 3)) ≤ r₀ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η₀ (r₀ / 3)), lt_min one_pos (lt_min hη₀ (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      simpa only [dist_eq_norm] using (hD₀ hb (hba.trans_le hδη)).le
    · intro b hb hba c hc hca
      apply hrem₀ b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- convex combinations
  have hconv : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (s : Finset Z)
      (a : Z → ℝ) (v : Z → G) (b : ℝ), (∀ i ∈ s, 0 ≤ a i) → ∑ i ∈ s, a i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, a i • v i‖ ≤ b := by
    intro G _ _ s a v b ha hs hv
    calc ‖∑ i ∈ s, a i • v i‖ ≤ ∑ i ∈ s, ‖a i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, a i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (ha i hi)]
      _ ≤ ∑ i ∈ s, a i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (ha i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- the extension: `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid n → ℝ, ∀ x,
      g x = if x ∈ A then h x else ∑ᶠ c : Z, w c x * P (pr c) x := ⟨_, fun _ => rfl⟩
  have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
  have hgnear : ∀ x ∉ A, ∀ y, dist y x < r x → g y = ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (hyA x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (pr c) y = 0
    rw [hwzero x hx y hy c hc', zero_mul]
  have hgev : ∀ x ∉ A, g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hgnear x hx y hy
  have hgc : ∀ x ∉ A, ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ F x, w c y * P (pr c) y) x :=
      ContDiffAt.sum (fun c _ => (hwc c x hx).mul (hPc _).contDiffAt)
    exact hs.congr_of_eventuallyEq (hgev x hx)
  have hgfd : ∀ x ∉ A, fderiv ℝ g x =
      ∑ c ∈ F x, (w c x • D (pr c) + P (pr c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(hgev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((hwc c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hPd _ x)
  -- `Dg = D` on `A`
  have hgd : ∀ a ∈ A, HasFDerivAt g (D a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, -, hDδ, hremδ⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by simpa using hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [hgA a ha]
    by_cases hxA : x ∈ A
    · rw [hgA x hxA]
      have hr' := hremδ a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hxx : dist x x < r x := by simpa using hrpos x hxA
      have hid : g x - h a - D a (x - a) = ∑ c ∈ F x, w c x • (P (pr c) x - P a x) := by
        rw [hgnear x hxA x hxx]
        simp only [smul_eq_mul, mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum x hxA x hxx, one_mul, hP a x]
        ring
      rw [hid]
      apply hconv (F x) (fun c => w c x) (fun c => P (pr c) x - P a x) _
        (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx)
      intro c hc
      have hbA := hprA (c : Euclid n)
      have hba := hanc2 x hxA a ha c hc
      have hxb : dist x (pr c) ≤ 2 * dist x a :=
        (hanc1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr c) hbA hbaδ
      have hr' := hremδ a ha haa (pr c) hbA hbaδ
      have hba' : ‖pr c - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
      have hxb' : ‖x - pr c‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
      calc ‖P (pr c) x - P a x‖
          ≤ ‖h (pr c) - h a - D a (pr c - a)‖ + ‖D (pr c) - D a‖ * ‖x - pr c‖ :=
            hPsub a (pr c) x
        _ ≤ (ε / 5) * ‖pr c - a‖ + (ε / 5) * ‖x - pr c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  -- `Dg` is continuous at the points of `A`
  have hgcont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by rw [hη_def]; positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by rw [hη_def]; field_simp
    have hηε : η ≤ ε / 2 := by nlinarith [mul_pos hη hM]
    obtain ⟨δ, hδ, hδ1, hDδ, hremδ⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [(hgd a ha).fderiv, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [(hgd x hxA).fderiv]
      exact (hDδ x hxA (by linarith)).trans hηε
    · have hrx := hrpos x hxA
      have hxx : dist x x < r x := by simpa using hrx
      have hbA := hprA x
      have hbaδ : dist (pr x) a < δ := by
        linarith [hpr2 x a ha, dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := by
        rw [hr x, min_eq_right hdx]
        ring
      have hD' : ∀ c ∈ F x, ‖D (pr c) - D a‖ ≤ η := by
        intro c hc
        apply hDδ _ (hprA c)
        have hi := hanc2 x hxA a ha c hc
        linarith [dist_nonneg (x := x) (y := a)]
      have hP' : ∀ c ∈ F x, ‖P (pr c) x - P (pr x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA := hprA (c : Euclid n)
        have hda := hanc2 x hxA a ha c hc
        have hdaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
        have hxd := hanc1 x hxA c hc
        have hxb : dist x (pr x) = infDist x A := (hprd x).symm
        have hdb : dist (pr c) (pr x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (pr c) x (pr x)
          rw [dist_comm (pr c) x, hxb] at ht
          linarith
        have hDd : ‖D (pr c) - D (pr x)‖ ≤ 2 * η := by
          calc ‖D (pr c) - D (pr x)‖ = ‖(D (pr c) - D a) - (D (pr x) - D a)‖ := by
                congr 1; abel
            _ ≤ ‖D (pr c) - D a‖ + ‖D (pr x) - D a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hremδ (pr x) hbA hbaδ (pr c) hdA hdaδ
        have hdb' : ‖pr c - pr x‖ ≤ 3 * infDist x A := by
          simpa only [dist_eq_norm] using hdb
        have hxd' : ‖x - pr c‖ ≤ 2 * infDist x A := by simpa only [dist_eq_norm] using hxd
        calc ‖P (pr c) x - P (pr x) x‖
            ≤ ‖h (pr c) - h (pr x) - D (pr x) (pr c - pr x)‖ +
                ‖D (pr c) - D (pr x)‖ * ‖x - pr c‖ := hPsub (pr x) (pr c) x
          _ ≤ η * ‖pr c - pr x‖ + (2 * η) * ‖x - pr c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by rw [hscale]; ring
      have hsplit : fderiv ℝ g x - D a = (∑ c ∈ F x, w c x • (D (pr c) - D a)) +
          ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x := by
        rw [hgfd x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hwsum x hxA x hxx, hwdsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hsplit]
      calc ‖(∑ c ∈ F x, w c x • (D (pr c) - D a)) +
            ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ F x, w c x • (D (pr c) - D a)‖ +
              ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact hconv (F x) (fun c => w c x) (fun c => D (pr c) - D a) η
                (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx) hD'
            · calc ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ F x, ‖(P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ c ∈ F x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ :=
                    (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by field_simp
        _ = ε / 2 := heq
  refine ⟨g, ?_, fun a ha => hgA a ha, hgd⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (hgd x hx).differentiableAt
    · exact (hgc x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact hgcont x hx
    · exact (hgc x hx).continuousAt_fderiv one_ne_zero

/-- **`C¹` approximation of Lipschitz functions** (Simon Ch. 2, Theorem 1.5, the part about
values).  If `u : ℝᵐ → ℝ` is `K`-Lipschitz and `ε > 0`, some `G ∈ C¹(ℝᵐ)` agrees with `u` off a
set of measure `< ε`.  By Rademacher's theorem, the Borel set `B` of points where `u` is
differentiable has null complement, and `Du` is Borel.  Lusin's theorem gives a closed `C ⊆ B`,
`Lᵐ(B \ C) < ε / 2`, on which `Du` is continuous.  Egorov's theorem applied to the Whitney
remainders gives a closed `A ⊆ C`, `Lᵐ(C \ A) < ε / 2`, on which `(u, Du)` satisfies Whitney's
condition 1.6(∗).  Whitney's extension theorem gives `G ∈ C¹` with `G = u` on `A`, and
`{u ≠ G} ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem Submission.dor_lmbsf_lipschitz_c1_approx : ∀ (m : ℕ) (u : Euclid m → ℝ) (K : NNReal), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧ volume {y | u y ≠ G y} < ε := by
  intro m u K hu ε hε
  -- Rademacher: the Borel set `B` of differentiability points of `u` has null complement
  set B : Set (Euclid m) := {x | DifferentiableAt ℝ u x}
  have hB : MeasurableSet B := measurableSet_of_differentiableAt ℝ u
  have hBc : volume Bᶜ = 0 := ae_iff.mp hu.ae_differentiableAt
  -- Lusin: a closed `C ⊆ B`, `Lᵐ(B \ C) < ε / 2`, on which `Du` is continuous
  obtain ⟨C, hCB, hC, hDC, hBC⟩ := Submission.codim1_rdo_c1a_lusin_isClosed m (fderiv ℝ u) B
    (measurable_fderiv ℝ u) hB (ε / 2) (ENNReal.half_pos hε.ne')
  -- Egorov on the Whitney remainders: a closed `A ⊆ C`, `Lᵐ(C \ A) < ε / 2`, satisfying 1.6(∗)
  obtain ⟨A, hAC, hA, hCA, hrem⟩ := Submission.codim1_rdo_c1a_whitney_remainder m u K C hu hC
    (fun x hx => hCB hx) hDC (ε / 2) (ENNReal.half_pos hε.ne')
  -- Whitney's extension theorem: `G ∈ C¹` with `G = u` on `A`
  obtain ⟨G, hG, hGA, -⟩ := Submission.codim1_rdo_c1a_whitney_extension m A u (fderiv ℝ u) hA
    hu.continuous.continuousOn (hDC.mono hAC) hrem
  refine ⟨G, hG, ?_⟩
  -- `{u ≠ G} ⊆ Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`
  calc volume {y | u y ≠ G y} ≤ volume (Bᶜ ∪ ((B \ C) ∪ (C \ A))) := by
        refine measure_mono fun y hy => ?_
        have hyA : y ∉ A := fun hyA => hy (hGA hyA).symm
        by_cases hyB : y ∈ B
        · by_cases hyC : y ∈ C
          · exact Or.inr (Or.inr ⟨hyC, hyA⟩)
          · exact Or.inr (Or.inl ⟨hyB, hyC⟩)
        · exact Or.inl hyB
    _ ≤ volume Bᶜ + (volume (B \ C) + volume (C \ A)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ < ε / 2 + ε / 2 := by
        rw [hBc, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε

/-- **Simon Ch. 3, Lemma 1.2, "only if" part** (chapter-03.txt lines 22–65): a countably
`m`-rectifiable `M ⊆ ℝᴾ` lies in `N₀ ∪ ⋃ₗ Nₗ` with `Hᵐ(N₀) = 0` and each `Nₗ` an embedded
`m`-dimensional `C¹` submanifold.  Write `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝᵐ)` with `Hᵐ(M₀) = 0` and `Fⱼ`
Lipschitz.  The `C¹` approximation theorem (Simon Ch. 2, Theorem 1.5) gives `C¹` maps `G_{ji}`
with `Fⱼ(ℝᵐ) ⊆ Eⱼ ∪ ⋃ᵢ G_{ji}(ℝᵐ)` and `Hᵐ(Eⱼ) = 0`.  Each `G_{ji}(ℝᵐ)` lies in an `Hᵐ`-null set
`N₀_{ji}` (the critical image, by the area formula) together with countably many submanifolds
`N_{jis}` (images of small balls about regular points).  Take
`N₀ = M₀ ∪ ⋃ⱼ Eⱼ ∪ ⋃_{j,i} N₀_{ji}` and `Nₗ = N_{jis}` for `l = Nat.pair j (Nat.pair i s)`. -/
theorem Submission.dor_lmbsf_rectifiable_c1_cover : ∀ (P m : ℕ) (M : Set (Euclid P)), CountablyRectifiable m M → ∃ (N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), μHE[m] N₀ = 0 ∧ (∀ l, IsEmbeddedSubmanifold 1 m (N l)) ∧ M ⊆ N₀ ∪ ⋃ l, N l := by
  intro P m M hM
  -- Step 1: `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝᵐ)` with `Hᵐ(M₀) = 0` and `Fⱼ` `Kⱼ`-Lipschitz
  obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hM
  choose K hK using hF
  -- Steps 2–3: `Fⱼ(ℝᵐ) ⊆ Eⱼ ∪ ⋃ᵢ G_{ji}(ℝᵐ)` with `Hᵐ(Eⱼ) = 0` and `G_{ji}` `C¹`
  choose E G hE hG hFG using fun j =>
    Submission.dor_lmbsf_c1c_lipschitz_range_c1_pieces P m (F j) (K j) (hK j)
      (Submission.dor_lmbsf_lipschitz_c1_approx m)
  -- Steps 4–6: `G_{ji}(ℝᵐ) ⊆ N₀_{ji} ∪ ⋃ₛ N_{jis}` with `Hᵐ(N₀_{ji}) = 0` and `N_{jis}`
  -- embedded `C¹` submanifolds
  choose N₀' N' hN₀' hN' hGN using fun j i =>
    Submission.dor_lmbsf_c1c_c1_range_cover P m (G j i) (hG j i)
  -- Step 7: collect the null sets and enumerate the submanifolds by `l = ⟨j, ⟨i, s⟩⟩`
  refine ⟨M₀ ∪ (⋃ j, E j) ∪ ⋃ j, ⋃ i, N₀' j i,
    fun l => N' l.unpair.1 l.unpair.2.unpair.1 l.unpair.2.unpair.2,
    measure_union_null (measure_union_null hM₀ (measure_iUnion_null hE))
      (measure_iUnion_null fun j => measure_iUnion_null (hN₀' j)),
    fun l => hN' _ _ _, ?_⟩
  intro y hy
  rcases hMF hy with hy | hy
  · exact Or.inl (Or.inl (Or.inl hy))
  obtain ⟨j, hj⟩ := mem_iUnion.1 hy
  rcases hFG j hj with hy | hy
  · exact Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨j, hy⟩)))
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy
  rcases hGN j i hi with hy | hy
  · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨j, i, hy⟩))
  obtain ⟨s, hs⟩ := mem_iUnion.1 hy
  refine Or.inr (mem_iUnion.2 ⟨Nat.pair j (Nat.pair i s), ?_⟩)
  simpa only [Nat.unpair_pair] using hs
/-- **Local `C¹` globalization by a bump cutoff** (the cut-off step letting the globally `C¹`
results apply to a map that is only `C¹` on an open set).  Let `W` be open, `χ` be `C¹` on `W`
and `y ∈ W`; choose `B_ρ(y) ⊆ W` and the smooth bump `φ` centred at `y` with `φ = 1` on
`B̄_{ρ/4}(y)` and `tsupport φ = B̄_{ρ/2}(y) ⊆ W`.  Then `g = φ χ` is `C¹` near points of `W`
(product of a `C^∞` and a `C¹` map) and vanishes near points outside `W`, so `g` is `C¹` on
`ℝᵏ`; and `g = χ` on `B_ε(y)`, `ε = ρ/4`. -/
theorem Submission.dor_lmbsf_cit_c1_local_extension : ∀ (P k : ℕ) (W : Set (Euclid k)) (χ : Euclid k → Euclid P) (y : Euclid k), IsOpen W → ContDiffOn ℝ 1 χ W → y ∈ W → ∃ (g : Euclid k → Euclid P) (ε : ℝ), 0 < ε ∧ ball y ε ⊆ W ∧ ContDiff ℝ 1 g ∧ EqOn g χ (ball y ε) := by
  intro P k W χ y hW hχ hy
  -- Step 1, a ball `B_ρ(y) ⊆ W`.
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hW y hy
  -- Step 2, the bump `φ`: `φ = 1` on `B̄_{ρ/4}(y)` and `tsupport φ = B̄_{ρ/2}(y) ⊆ W`.
  let φ : ContDiffBump y := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  have hsupp : tsupport φ ⊆ W := by
    rw [φ.tsupport_eq]
    exact (closedBall_subset_ball (by change ρ / 2 < ρ; linarith)).trans hball
  -- Step 3, `g = φ χ` and `ε = ρ/4`, so `B_ε(y) ⊆ W`.
  refine ⟨fun x => φ x • χ x, ρ / 4, by positivity,
    (ball_subset_ball (by linarith)).trans hball, ?_, fun x hx => ?_⟩
  · -- Steps 4–6, `g` is `C¹` at every point.
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ W
    · -- Step 4, on `W`, `g` is the product of the `C^∞` map `φ` and the `C¹` map `χ`.
      exact φ.contDiffAt.fun_smul (hχ.contDiffAt (hW.mem_nhds hx))
    · -- Step 5, off `W`, `x ∉ tsupport φ` and `g = 0` near `x`.
      refine (contDiffAt_const (c := (0 : Euclid P))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport φ).compl_mem_nhds fun h => hx (hsupp h)] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · -- `φ = 1` on `B_ε(y) ⊆ B̄_{ρ/4}(y)`, so `g = χ` there.
    change φ x • χ x = χ x
    rw [φ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]
/-- **Simon Ch. 3, Lemma 1.2** (the inverse-function step of the "only if" part): if `G` is `C¹`
and `DG(x)` is injective, then `μ |a − b| ≤ |G(a) − G(b)|` on some ball `B_δ(x)`.  With
`|v| ≤ K |DG(x) v|` and `μ = 1/(2K)`, strict differentiability gives
`|G(a) − G(b) − DG(x)(a − b)| ≤ μ |a − b|` near `x`, so `|G(a) − G(b)| ≥ 2μ|a − b| − μ|a − b|`. -/
theorem Submission.codim1_rdo_c1cov_local_lower_lipschitz : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖ := by
  intro P n G x hG hinj
  -- `L = DG(x)` is injective on the finite-dimensional `ℝⁿ`: `‖v‖ ≤ K ‖L v‖`
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hbound : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ G x v‖ :=
    (fderiv ℝ G x).bound_of_antilipschitz hKL
  -- `μ = 1/(2K)`, so `‖L v‖ ≥ 2μ ‖v‖`
  set μ : ℝ := (2 * K)⁻¹ with hμ
  have hK' : (0 : ℝ) < K := hK
  have hμ0 : 0 < μ := by positivity
  -- `G` is `C¹`, so `L` is a strict derivative: `G` approximates `L` with constant `μ` near `x`
  obtain ⟨s, hs, hGs⟩ := (hG.contDiffAt.hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
    (c := ⟨μ, hμ0.le⟩) (Or.inr hμ0)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, μ, hδ, hμ0, fun a ha b hb => ?_⟩
  have h1 : ‖G a - G b - fderiv ℝ G x (a - b)‖ ≤ μ * ‖a - b‖ := hGs a (hδs ha) b (hδs hb)
  have h2 : 2 * μ * ‖a - b‖ ≤ ‖fderiv ℝ G x (a - b)‖ := by
    calc 2 * μ * ‖a - b‖ ≤ 2 * μ * (K * ‖fderiv ℝ G x (a - b)‖) := by
          gcongr
          exact hbound (a - b)
      _ = ‖fderiv ℝ G x (a - b)‖ := by
          rw [hμ]
          field_simp
  -- triangle inequality: `‖L (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - L (a - b)‖`
  have h3 : ‖fderiv ℝ G x (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - fderiv ℝ G x (a - b)‖ := by
    simpa using norm_sub_le (G a - G b) (G a - G b - fderiv ℝ G x (a - b))
  linarith
/-- A lower Lipschitz bound at a point passes to the derivative (step 1 of the `C¹`-piece tangent
argument, Simon Ch. 3, 1.6): if `U` is open, `a ∈ U`, `g` is differentiable at `a` and
`m|x − a| ≤ |g(x) − g(a)|` on `U`, then `m|v| ≤ |Dg(a)v|`.  For small `t > 0`, `a + tv ∈ U`
gives `m|v| ≤ |t⁻¹(g(a + tv) − g(a))|`, and the quotients tend to `Dg(a)v` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_c1pt_fderiv_lower_bound : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (U : Set (Euclid n)) (a : Euclid n) (m : ℝ), IsOpen U → a ∈ U → DifferentiableAt ℝ g a → (∀ x ∈ U, m * ‖x - a‖ ≤ ‖g x - g a‖) → ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := by
  intro P n g U a m hU ha hg hm v
  -- difference quotients `q(t) = t⁻¹ • (g (a + t • v) - g a)` tend to `Dg(a) v` as `t ↓ 0`
  have hq : Tendsto (fun t : ℝ => t⁻¹ • (g (a + t • v) - g a)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ g a v)) := by
    simpa only [inv_inv] using hg.hasFDerivAt.lim v (c := fun t : ℝ => t⁻¹)
      (tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero)
  -- `a + t • v → a` as `t → 0`, so `a + t • v ∈ U` for small `t` (`U` is a neighbourhood of `a`)
  have hline : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a (by simp)
  -- for small `t > 0`: `t * (m‖v‖) ≤ ‖g (a + t • v) - g a‖`, i.e. `m‖v‖ ≤ ‖q(t)‖`
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), m * ‖v‖ ≤ ‖t⁻¹ • (g (a + t • v) - g a)‖ := by
    filter_upwards [nhdsWithin_le_nhds (hline (hU.mem_nhds ha)), self_mem_nhdsWithin]
      with t htU ht
    have ht : (0 : ℝ) < t := ht
    have h := hm _ htU
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm] at h
    rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  -- the non-strict inequality passes to the limit along the nontrivial filter `𝓝[>] 0`
  exact ge_of_tendsto hq.norm hle
/-- **Simon Ch. 2, (3.2) and (3.5)** (area formula for the blow-ups of an injective regular
image): if `g` is differentiable on the Borel set `B`, injective on `B` and `Dg(a)` is injective
for `a ∈ B`, then for `s > 0`, every `z` and every `f`,
`∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + s b) f(s⁻¹(g(z + s b) − g(z))) dLⁿ(b)`, where
`B_s = {b | z + s b ∈ B}` and `J_g = √det(Dg* ∘ Dg)`.  The rescaled map
`φ(b) = s⁻¹(g(z + s b) − g(z))` is injective on `B_s` with `Dφ(b) = Dg(z + s b)` and
`φ(B_s) = η_{g(z),s}(g(B))`, so this is the area formula for `φ`.  That formula is proved in
place: the linear case (3.1), sharp `Hⁿ` estimates for maps close to an injective linear map,
a measurable partition into such pieces, and the transport of the Jacobian-weighted measure,
following the pinned SimonGMT `Chapter02.AreaApproximation`, `AreaDerivative`, `AreaFormula`
and `WeightedArea` proofs, which lie outside this file's imports. -/
theorem Submission.codim1_rdo_c1pt_rescaled_area_formula : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (B : Set (Euclid n)) (z : Euclid n) (s : ℝ) (f : Euclid P → ℝ), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ g a) → InjOn g B → (∀ a ∈ B, Injective (fderiv ℝ g a)) → 0 < s → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B), f y ∂μHE[n] = ∫ b in {b : Euclid n | z + s • b ∈ B}, Real.sqrt (((fderiv ℝ g (z + s • b)).adjoint ∘L fderiv ℝ g (z + s • b)).det) * f (s⁻¹ • (g (z + s • b) - g z)) := by
  intro P n g B z s f hB hdiff hinj hreg hs
  classical
  -- `J(L) = √det(L* ∘ L)` is the metric Jacobian of a linear map `L : ℝⁿ → ℝᴾ`
  obtain ⟨J, hJdef⟩ : ∃ J : (Euclid n →L[ℝ] Euclid P) → ℝ,
      J = fun L => Real.sqrt ((L.adjoint ∘L L).det) := ⟨_, rfl⟩
  have hJnonneg : ∀ L, 0 ≤ J L := fun L => by rw [hJdef]; exact Real.sqrt_nonneg _
  have hJcont : Continuous J := by
    rw [hJdef]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  /- Simon (3.1), the linear area formula: an injective `L` factors as `ι ∘ M` with `ι` a
  linear isometry onto its range and `M` an endomorphism of `ℝⁿ`, so
  `Hⁿ(L(A)) = Lⁿ(M(A)) = |det M| Lⁿ(A)`, and `J(L)² = det(M* M) = (det M)² ≠ 0`. -/
  have hlin : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L →
      0 < J L ∧ ∀ A : Set (Euclid n), μHE[n] (L '' A) = ENNReal.ofReal (J L) * volume A := by
    intro L hL
    have hV : Module.finrank ℝ (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) = n := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let e : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) ≃ₗᵢ[ℝ] Euclid n :=
      ((stdOrthonormalBasis ℝ _).reindex (finCongr hV)).repr
    let ιI : Euclid n →ₗᵢ[ℝ] Euclid P :=
      (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)).subtypeₗᵢ.comp e.symm.toLinearIsometry
    let M : Euclid n →L[ℝ] Euclid n := (e : _ →L[ℝ] Euclid n) ∘L L.rangeRestrict
    have hLιM : L = ιI.toContinuousLinearMap ∘L M := by
      ext1 x
      show L x = ((e.symm (e (L.rangeRestrict x)) :
        LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) : Euclid P)
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hιadj : ιI.toContinuousLinearMap.adjoint ∘L ιI.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp ιI.norm_map
    have hdetadj : (ContinuousLinearMap.adjoint M).det = M.det := by
      have h := congrArg Matrix.det (LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ) (M : Euclid n →ₗ[ℝ] Euclid n))
      rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h
      simp only [star_trivial] at h
      exact h
    have hdet : (L.adjoint ∘L L).det = M.det ^ 2 := by
      have h1 : L.adjoint ∘L L = M.adjoint ∘L M := by
        rw [hLιM, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ _ M, hιadj, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
      have h2 : (M.adjoint ∘L M).det = M.adjoint.det * M.det :=
        LinearMap.det_comp _ _
      rw [h1, h2, hdetadj, sq]
    have hJ : J L = |M.det| := by
      rw [hJdef]
      dsimp only
      rw [hdet, Real.sqrt_sq_eq_abs]
    have hMinj : LinearMap.ker (M : Euclid n →ₗ[ℝ] Euclid n) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      have h := congrArg (fun v => ((e.symm v : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) :
        Euclid P)) hxy
      simpa [M] using h
    refine ⟨?_, fun A => ?_⟩
    · rw [hJ]
      exact abs_pos.mpr (fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hMinj)
    · rw [hJ, hLιM, ContinuousLinearMap.coe_comp, Set.image_comp,
        LinearIsometry.coe_toContinuousLinearMap, ιI.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact MeasureTheory.Measure.addHaar_image_linearMap volume (M : Euclid n →ₗ[ℝ] Euclid n) A
  -- comparison of pairwise distances gives comparison of the `Hⁿ` measures of the images
  have hdistcmp : ∀ (u v : Euclid n → Euclid P) (T : Set (Euclid n)) (K : NNReal), InjOn v T →
      (∀ x ∈ T, ∀ y ∈ T, dist (u x) (u y) ≤ K * dist (v x) (v y)) →
      μHE[n] (u '' T) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (v '' T) := by
    intro u v T K hv hK
    have hh : LipschitzOnWith K (u ∘ invFunOn v T) (v '' T) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy] using hK x hx y hy
    have himage : (u ∘ invFunOn v T) '' (v '' T) = u '' T := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  /- Near an injective `L`, one radius `δ` controls both the Jacobian of nearby linear maps and
  the `Hⁿ` measure of images under maps `δ`-approximating `L`, up to a factor `q > 1`. -/
  have hradius : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
          ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
            ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
        (∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P), ApproximatesLinearOn u L T δ →
          μHE[n] (u '' T) ≤ q * μHE[n] (L '' T) ∧ μHE[n] (L '' T) ≤ q * μHE[n] (u '' T)) := by
    intro L hL q hq
    obtain ⟨K, -, hK⟩ := (L : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hqR : (1 : ℝ) < q := hq
    have hJpos := (hlin L hL).1
    have hmul : J L < (q : ℝ) * J L := lt_mul_of_one_lt_left hJpos hqR
    have hnear : ∀ᶠ L' in 𝓝 L, J L' < (q : ℝ) * J L ∧ J L < (q : ℝ) * J L' :=
      (hJcont.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hJcont.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεev : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
      (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds,
        hεev.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    -- `‖(u x - u y) - L(x - y)‖ ≤ δ K ‖L x - L y‖` on `T`
    have herror : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P),
        ApproximatesLinearOn u L T δ → ∀ x ∈ T, ∀ y ∈ T,
          ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      intro T u hu x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      calc ‖u x - u y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hu x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    refine ⟨δ, hδ, fun L' hL' => ?_, fun T u hu => ⟨?_, ?_⟩⟩
    · have hdist : dist L' L < ε := by
        rw [dist_eq_norm]
        exact hL'.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hdist
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h1.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h2.le
    · refine (hdistcmp u L T (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖u x - u y‖ ≤ ‖u x - u y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
            add_le_add (herror T u hu x hx y hy) le_rfl
          _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
      · gcongr
        rw [← ENNReal.coe_pow]
        exact ENNReal.coe_le_coe.mpr hδupper.le
    · have hδR : (δ : ℝ) * K < 1 := hδK
      have hdist : ∀ x ∈ T, ∀ y ∈ T,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (u x) (u y) := by
        intro x hx y hy
        have h1 := herror T u hu x hx y hy
        have htriangle := norm_le_norm_add_norm_sub (u x - u y) (L x - L y)
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
        linarith only [h1, htriangle]
      have huinj : InjOn u T := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      refine (hdistcmp L u T _ huinj hdist).trans ?_
      gcongr
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlower.le
  /- On almost every point of a measurable piece where `u` is `δ`-approximated by `A`, the
  derivative is `δ`-close to `A` (the density-point argument of Mathlib's
  `ApproximatesLinearOn.norm_fderiv_sub_le`, for rectangular derivatives). -/
  have hderivbound : ∀ (u : Euclid n → Euclid P) (T : Set (Euclid n)) (A : Euclid n →L[ℝ] Euclid P)
      (δ : NNReal) (u' : Euclid n → Euclid n →L[ℝ] Euclid P), ApproximatesLinearOn u A T δ →
      MeasurableSet T → (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) →
      ∀ᵐ x ∂(volume.restrict T), ‖u' x - A‖₊ ≤ δ := by
    intro u T A δ u' hf hT hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume T, ae_restrict_mem hT]
    intro x hx xT
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun w => ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - A) w‖ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖w‖ + 0) + ‖u' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ := MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one volume T x hx
      (closedBall w ε) measurableSet_closedBall (measure_closedBall_pos volume w εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ T ⊆ {y : Euclid n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xT).isLittleO εpos)
    have B₂ := (eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := x)
      (isBounded_closedBall (x := w) (r := ε)) (ball_mem_nhds x ρpos)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    obtain ⟨r, ⟨y, ⟨yT, hy⟩⟩, rρ, rpos⟩ := (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, aw, ya⟩ : ∃ a, a ∈ closedBall w ε ∧ y = x + r • a := by
      have hy' := hy
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy'
      rcases hy' with ⟨a, aw, ha⟩
      exact ⟨a, aw, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖w‖ + ε :=
      calc ‖a‖ = ‖w + (a - w)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖w‖ + ‖a - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε := by grw [mem_closedBall_iff_norm.1 aw]
    have I : r * ‖(u' x - A) a‖ ≤ r * (δ + ε) * (‖w‖ + ε) :=
      calc r * ‖(u' x - A) a‖ = ‖(u' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - A (y - x) - (u y - u x - (u' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - A (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yT _ xT) (hρ ⟨rρ hy, yT⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖w‖ + ε) := by gcongr
    calc ‖(u' x - A) w‖ = ‖(u' x - A) a + (u' x - A) (w - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(u' x - A) a‖ + ‖(u' x - A) (w - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ‖w - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at aw
          gcongr
  /- Simon (3.2), measure form: for `u` injective on a measurable `T`, differentiable along `T`
  with injective derivative `u'`, `Hⁿ(u(T)) = ∫_T J(u'(x)) dLⁿ(x)`.  Partition `T` into
  measurable pieces on which `u` is close to linear maps `A i = u'(yᵢ)`, compare on each piece
  up to a factor `q²`, sum, and let `q ↓ 1`. -/
  have hmeasure : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet T →
      (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) → (∀ x ∈ T, Injective (u' x)) → InjOn u T →
      μHE[n] (u '' T) = ∫⁻ x in T, ENNReal.ofReal (J (u' x)) := by
    intro T u u' hT hu' hreg' hinj'
    have hcmp : ∀ q : NNReal, 1 < q →
        μHE[n] (u '' T) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' T) := by
      intro q hq
      rcases eq_empty_or_nonempty T with rfl | hTne
      · simp
      have hchoice : ∀ L : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
              ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
          (∀ (T' : Set (Euclid n)) (v : Euclid n → Euclid P), ApproximatesLinearOn v L T' δ →
            μHE[n] (v '' T') ≤ q * μHE[n] (L '' T') ∧
              μHE[n] (L '' T') ≤ q * μHE[n] (v '' T'))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, h1, h2⟩ := hradius L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨1, one_pos, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u T u' hu' δ
          (fun L => (hδpos L).ne')
      have hAreg : ∀ i, Injective (A i) := by
        intro i
        obtain ⟨x, hx, hA⟩ := hactual hTne i
        rw [hA]
        exact hreg' x hx
      have hTeq : T = ⋃ i, T ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[n] (u '' T) = ∑' i, μHE[n] (u '' (T ∩ t i)) := by
        conv_lhs => rw [hTeq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj' inter_subset_left inter_subset_left
        · intro i
          apply (hT.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hu' x hx.1).continuousWithinAt.mono inter_subset_left
          · exact hinj'.mono inter_subset_left
      have hsumintegral : ∫⁻ x in T, ENNReal.ofReal (J (u' x)) =
          ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
        conv_lhs => rw [hTeq]
        exact lintegral_iUnion (fun i => hT.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[n] (u '' (T ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by
        intro i
        have hJ := (hδ (A i) (hAreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (A i) (hAreg i)).2 (T ∩ t i) u (happrox i)
        have hlinA := (hlin (A i) (hAreg i)).2 (T ∩ t i)
        rw [hlinA] at harea_upper harea_lower
        have hderiv := hderivbound u (T ∩ t i) (A i) (δ (A i)) u' (happrox i) (hT.inter (ht i))
          (fun x hx => (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
          calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ ∫⁻ _ in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (A i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).1
            _ = q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (J (A i)) * volume (T ∩ t i) ≤
            q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
          calc ENNReal.ofReal (J (A i)) * volume (T ∩ t i)
              = ∫⁻ _ in T ∩ t i, ENNReal.ofReal (J (A i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (u' x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).2
            _ = q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[n] (u '' (T ∩ t i)) ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
                rw [pow_two, mul_assoc]
        · calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (T ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc ∑' i, μHE[n] (u '' (T ∩ t i))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_mul_left
      · calc ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, μHE[n] (u '' (T ∩ t i)) := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).2
  /- Simon (3.5), Bochner form: the Jacobian-weighted measure on `S` is transported by `u`
  to `Hⁿ ⌞ u(S)`, so `∫_{u(S)} f dHⁿ = ∫_S J(u'(x)) f(u(x)) dLⁿ(x)` for every `f`. -/
  have hbochner : ∀ (S : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet S →
      (∀ x ∈ S, HasFDerivAt u (u' x) x) → (∀ x ∈ S, Injective (u' x)) → InjOn u S →
      Measurable u' → ∫ y in u '' S, f y ∂μHE[n] = ∫ x in S, J (u' x) * f (u x) := by
    intro S u u' hS hu' hreg' hinj' hmeas'
    have hcont : ContinuousOn u S := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hS hinj'
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hJm : Measurable (fun x => J (u' x)) := hJcont.measurable.comp hmeas'
    have hmap : Measure.map (S.domRestrict u)
        ((volume.withDensity (fun x => ENNReal.ofReal (J (u' x)))).comap
          (Subtype.val : S → Euclid n)) = μHE[n].restrict (u '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((S.domRestrict u) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict u) ⁻¹' t) ⊆ S := by
        rintro x ⟨w, _, rfl⟩
        exact w.property
      rw [withDensity_apply _ hBm, ← hmeasure _ u u' hBm
        (fun x hx => (hu' x (hBS hx)).hasFDerivWithinAt) (fun x hx => hreg' x (hBS hx))
        (hinj'.mono hBS), Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨hw, ⟨w, w.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    simp only [Set.domRestrict_apply, ← Function.comp_apply (f := f), ENNReal.ofReal]
    rw [← hsub.integral_map, map_comap_subtype_coe hS,
      setIntegral_withDensity_eq_setIntegral_smul₀ (hJm.real_toNNReal.aemeasurable) _ hS]
    congr with x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hJnonneg _), smul_eq_mul, comp_apply]
  -- the rescaled map `φ(b) = s⁻¹ • (g (z + s • b) - g z)` on `B_s = {b | z + s • b ∈ B}`
  have hs0 : s ≠ 0 := hs.ne'
  have hBs : MeasurableSet {b : Euclid n | z + s • b ∈ B} :=
    hB.preimage ((measurable_const_add z).comp (measurable_const_smul s))
  have hderiv : ∀ b ∈ {b : Euclid n | z + s • b ∈ B},
      HasFDerivAt (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) (fderiv ℝ g (z + s • b)) b := by
    intro b hb
    have h1 : HasFDerivAt (fun b' : Euclid n => z + s • b')
        (s • ContinuousLinearMap.id ℝ (Euclid n)) b :=
      ((hasFDerivAt_id b).const_smul s).const_add z
    refine ((((hdiff _ hb).hasFDerivAt.comp b h1).sub_const (g z)).const_smul s⁻¹).congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ hs0]
  have hinjφ : InjOn (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z))
      {b : Euclid n | z + s • b ∈ B} := by
    intro b hb b' hb' h
    have h' : g (z + s • b) = g (z + s • b') := by
      simpa [hs0] using h
    exact smul_right_injective _ hs0 (add_left_cancel (hinj hb hb' h'))
  have himage :
      (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) '' {b : Euclid n | z + s • b ∈ B} =
        Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨g (z + s • b), ⟨z + s • b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s⁻¹ • (a - z), ?_, ?_⟩
      · show z + s • s⁻¹ • (a - z) ∈ B
        rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
      · show s⁻¹ • (g (z + s • s⁻¹ • (a - z)) - g z) = s⁻¹ • (g a - g z)
        rw [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
  have hmeasf' : Measurable (fun b : Euclid n => fderiv ℝ g (z + s • b)) :=
    (measurable_fderiv ℝ g).comp ((measurable_const_add z).comp (measurable_const_smul s))
  rw [← himage, hbochner _ _ (fun b : Euclid n => fderiv ℝ g (z + s • b)) hBs hderiv
    (fun b hb => hreg _ hb) hinjφ hmeasf', hJdef]
/-- **Simon Ch. 2, (3.1)** in integral form (area formula for an injective linear map): for an
injective linear `L : ℝⁿ → ℝᴾ` and every `f`, `∫_{L(ℝⁿ)} f dHⁿ = √det(L* ∘ L) ∫_{ℝⁿ} f(Lb) dLⁿ(b)`.
Write `L = W ∘ A` with `W` a linear isometry of `ℝⁿ` onto `L(ℝⁿ)` and `A` an automorphism of `ℝⁿ`;
then `Hⁿ⌞L(ℝⁿ) = W#Lⁿ`, `Lⁿ = |det A| A#Lⁿ` and `det(L* ∘ L) = det(A* ∘ A) = (det A)²`. -/
theorem Submission.codim1_rdo_c1pt_linear_range_integral : ∀ (P n : ℕ) (L : Euclid n →L[ℝ] Euclid P) (f : Euclid P → ℝ), Injective L → ∫ y in (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = Real.sqrt ((L.adjoint ∘L L).det) * ∫ b, f (L b) := by
  intro P n L f hL
  -- `L = W ∘ A`: `W` is a linear isometry of `ℝⁿ` onto `R = L(ℝⁿ)` (via an orthonormal basis of
  -- `R`, which has dimension `n`) and `A` is a surjective endomorphism of `ℝⁿ`
  obtain ⟨W, A, hWA, hA⟩ : ∃ (W : Euclid n →ₗᵢ[ℝ] Euclid P) (A : Euclid n →L[ℝ] Euclid n),
      (∀ x, W (A x) = L x) ∧ Surjective A := by
    let R := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)
    have hrank : Module.finrank ℝ R = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Euclid n →ₗ[ℝ] Euclid P)) hL).trans
        finrank_euclideanSpace_fin
    let bv : OrthonormalBasis (Fin n) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hrank)
    refine ⟨R.subtypeₗᵢ.comp bv.repr.symm.toLinearIsometry,
      bv.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        L.codRestrict R (fun x => LinearMap.mem_range_self _ x), fun x => by simp, fun z => ?_⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bv.repr.symm z).2
    refine ⟨x, ?_⟩
    have hx' : L.codRestrict R (fun x => LinearMap.mem_range_self _ x) x = bv.repr.symm z :=
      Subtype.ext hx
    simp [hx']
  have hAinj : Injective A := fun x y h => hL (by rw [← hWA x, ← hWA y, h])
  -- `L(ℝⁿ) = W(ℝⁿ)`
  have hrange : (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) =
      Set.range W := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hA.range_comp W]
    congr 1
    funext x
    exact (hWA x).symm
  -- `Hⁿ⌞W(ℝⁿ) = W#Hⁿ` (`W` is an isometry) and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hW : ∫ y in Set.range W, f y ∂μHE[n] = ∫ x, f (W x) := by
    rw [← W.isometry.map_euclideanHausdorffMeasure,
      W.isometry.isClosedEmbedding.measurableEmbedding.integral_map,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- change of variables `x = A b` on `ℝⁿ`
  have hAcv : ∫ x, f (W x) = |A.det| * ∫ b, f (W (A b)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) hAinj.injOn (fun x => f (W x))
    rw [Set.image_univ, hA.range_eq, Measure.restrict_univ] at h
    rw [h, ← integral_const_mul]
    simp only [smul_eq_mul]
  -- `L* ∘ L = A* ∘ W* ∘ W ∘ A = A* ∘ A`, so `det (L* ∘ L) = (det A)²`
  have hdet : (L.adjoint ∘L L).det = A.det ^ 2 := by
    have hL' : L = W.toContinuousLinearMap ∘L A := ContinuousLinearMap.ext fun x => (hWA x).symm
    have h1 : L.adjoint ∘L L = A.adjoint ∘L A := by
      rw [hL', ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _), W.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have hadj : LinearMap.det (LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n)) =
        LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
        Matrix.det_conjTranspose, LinearMap.det_toMatrix, star_trivial]
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap, hadj, sq]
  rw [hrange, hW, hAcv, hdet, Real.sqrt_sq_eq_abs]
  simp only [hWA]
/-- Rescaled integrals over a `C¹` piece converge to the integral over its tangent map (proof of
Simon Ch. 3, Theorem 1.6, with a continuous weight `h`).  With `L = Dg(z)`,
`B_s = {b : z + s b ∈ B}` and `φ_s(b) = s⁻¹ (g(z + s b) − g(z))`:
`∫_{B_s} h(z + s b) f(φ_s(b)) db → h(z) ∫ f(L b) db` as `s ↓ 0`.  Take `f = 0` off `B_R(0)` and
`B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R`, `K = B̄_{R/m}(0) ⊆ B_s`, and the integrand vanishes on
`B_s \ K` because `|φ_s(b)| ≥ m|b| > R`.  On `K` it is bounded by `sup_{B̄_ρ(z)} |h| · sup |f|` and
tends pointwise to `h(z) f(L b)`, so dominated convergence applies.  Finally `f(L b) = 0` off `K`
because `|L b| ≥ m|b| > R`. -/
theorem Submission.codim1_rdo_c1pt_rescaled_integral_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), Continuous g → DifferentiableAt ℝ g z → Continuous h → IsOpen B → z ∈ B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hg hgz hh hB hzB hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Step 3: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ closedBall z ρ := by
    intro s hs hss b hb
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 4: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hB.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hρB (hKB s hs.1 hs.2.le b hb)
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 5: uniform bounds
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 6–8: dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => Continuous.aestronglyMeasurable ?_
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      exact (hh.comp hz).mul (hf.comp (((hg.comp hz).sub continuous_const).const_smul s⁻¹))
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.tendsto z).comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 9: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc

/-- **Approximate tangent space of a `C¹` piece** (Simon Ch. 3, 1.4; the step "since `x ∈ Nⱼ` and
`Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of the proof of
1.6 "⇒", chapter-03.txt lines 113–125).  Let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on
`B = B_r(c)`, `m > 0`, and `z ∈ B`.  Then `|Dg(a)v| ≥ m|v|`, so `Dg(a)` is injective for `a ∈ B`,
`g` is injective on `B` and `T = Dg(z)(ℝⁿ)` has dimension `n`.  By the area formula (Ch. 2, 3.2,
3.3, 3.5), `∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + sb) f(s⁻¹(g(z + sb) − g(z))) db` for
`s > 0`.  The Jacobian `J_g = √det(Dg* ∘ Dg)` is continuous, so these integrals tend to
`J_g(z) ∫ f(Dg(z)b) db`, which is `∫_T f dHⁿ` by the linear area formula (Ch. 2, 3.1). -/
theorem Submission.codim1_rdo_c1_piece_approxTangent : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r m : ℝ), ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt n (g '' ball c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n g c r m hg hm hlip z hz
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- a vector `x` with `m|x| ≤ 0` vanishes, since `m > 0`
  have hzero : ∀ x : Euclid n, m * ‖x‖ ≤ 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hm)
  -- Step 1, `m|v| ≤ |Dg(a)v|` for `a ∈ B`, so `Dg(a)` is injective; `g` is injective on `B`.
  have hlow : ∀ a ∈ ball c r, ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := fun a ha =>
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P n g (ball c r) a m isOpen_ball ha (hdiff a)
      fun x hx => hlip x hx a ha
  have hinj : ∀ a ∈ ball c r, Injective (fderiv ℝ g a) := by
    intro a ha v w hvw
    have h := hlow a ha (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinjOn : InjOn g (ball c r) := by
    intro a ha b hb hab
    have h := hlip a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  -- Step 2, the Jacobian `J_g(a) = √det(Dg(a)* ∘ Dg(a))` is continuous.
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hJ : Continuous fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous.comp hcont).clm_comp hcont))
  refine ⟨?_, fun f => ?_⟩
  · -- `dim T = n`
    rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P))
      (hinj z hz), finrank_euclideanSpace_fin]
  · -- Steps 3–8, `∫_T f dHⁿ = J_g(z) ∫ f(Dg(z)b) db` is the limit of the rescaled area formulas.
    rw [Submission.codim1_rdo_c1pt_linear_range_integral P n (fderiv ℝ g z) f (hinj z hz)]
    refine (Submission.codim1_rdo_c1pt_rescaled_integral_tendsto P n g
      (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det)) (ball c r) z m f
      hdiff.continuous (hdiff z) hJ isOpen_ball hz hm (fun a ha => hlip a ha z hz) (hlow z hz)
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P n g (ball c r) z s f
      measurableSet_ball (fun a _ => hdiff a) hinjOn hinj hs).symm
/-- **Locality of approximate tangent spaces** (Simon Ch. 3, Definition 1.4): if `M' ⊆ M`, `M` is
Borel and `x ∉ closure (M \ M')`, then an approximate tangent space `Q` of `M'` at `x` is also one
of `M`.  Some `ρ > 0` has `|z − x| ≥ ρ` on `M \ M'`, and a test function `f` vanishes on
`|p| ≥ R`.  For `0 < r < ρ / R`, `η_{x,r}(M)` and `η_{x,r}(M')` differ only where
`|p| ≥ ρ / r > R`, so `∫_{η_{x,r}(M)} f dHⁿ = ∫_{η_{x,r}(M')} f dHⁿ` and the limit transfers. -/
theorem Submission.dor_lmbsf_cit_approxTangent_of_subset : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), MeasurableSet M → M' ⊆ M → x ∉ closure (M \ M') → HasApproximateTangentSpaceAt n M' x Q → HasApproximateTangentSpaceAt n M x Q := by
  intro P n M M' x Q hM hM'M hx hM'
  refine ⟨hM'.1, fun f => ?_⟩
  -- `x ∉ closure (M \ M')`: some `ρ > 0` has `ρ ≤ |x − z|` for all `z ∈ M \ M'`
  obtain ⟨ρ, hρ, hρM⟩ : ∃ ρ > 0, ∀ z ∈ M \ M', ρ ≤ dist x z := by
    simpa only [Metric.mem_closure_iff, not_forall, not_exists, not_and, not_lt,
      exists_prop] using hx
  -- `f` has compact support: `f p = 0` once `R ≤ |p|`
  obtain ⟨R, hR, hfR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ p : Euclid P, R ≤ ‖p‖ → f p = 0 :=
    f.hasCompactSupport.exists_pos_le_norm
  -- for `0 < r < ρ / R` the blown-up integrals over `M` and `M'` agree
  refine (hM'.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  rw [lt_div_iff₀ hR] at hrR
  -- `η_{x,r}(M)` is the preimage of `M` under `p ↦ x + r p`, hence Borel
  have hmeas : MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M) := by
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
        (fun p : Euclid P => x + r • p) ⁻¹' M := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr0.ne'] using hz
      · intro hp
        exact ⟨x + r • p, hp, by
          simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr0.ne']⟩
    rw [himage]
    exact hM.preimage (by fun_prop)
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas (image_mono hM'M) ?_
  -- a point of `η_{x,r}(M) \ η_{x,r}(M')` comes from `z ∈ M \ M'`, so its norm is `≥ ρ / r > R`
  rintro _ ⟨⟨z, hzM, rfl⟩, hzM'⟩
  have hz : z ∈ M \ M' := ⟨hzM, fun h => hzM' ⟨z, h, rfl⟩⟩
  apply hfR
  rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le),
    ← dist_eq_norm, dist_comm, inv_mul_eq_div, le_div_iff₀ hr0]
  linarith [hρM z hz]

/-- **Approximate tangent space of an injective `C¹` image** (Simon Ch. 3, 1.4; the step "since
`x ∈ Nⱼ` and `Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of
the proof of 1.6 "⇒", chapter-03.txt lines 113–125).  Let `χ` be `C¹` on the open `V ⊇ C`, `C`
compact, `χ` injective on `C`, `y ∈ int C` and `Dχ(y)` injective.  On a ball
`B_ε(y) ⊆ V ∩ int C`, `χ` agrees with a globally `C¹` map `g`, so `Dg(y) = Dχ(y)` and `g` has a
lower Lipschitz bound on some `B_δ(y) ⊆ B_ε(y)`.  Hence `χ(B_δ(y)) = g(B_δ(y))` has approximate
tangent space `Q = Dχ(y)(ℝᵏ)` at `χ(y)`.  The rest of `χ(C)` lies in the compact set
`χ(C \ B_δ(y))`, which misses `χ(y)` by injectivity, so it does not change the blow-up limits. -/
theorem Submission.dor_lmbsf_c1_image_approxTangent : ∀ (k P : ℕ) (V C : Set (Euclid k)) (χ : Euclid k → Euclid P) (y : Euclid k), IsOpen V → ContDiffOn ℝ 1 χ V → IsCompact C → C ⊆ V → InjOn χ C → y ∈ interior C → Injective (fderiv ℝ χ y) → HasApproximateTangentSpaceAt k (χ '' C) (χ y) (LinearMap.range (fderiv ℝ χ y : Euclid k →ₗ[ℝ] Euclid P)) := by
  intro k P V C χ y hV hχ hC hCV hinj hy hDχ
  -- Step 1, `χ` agrees on `B_ε(y) ⊆ W = V ∩ int C` with a globally `C¹` map `g`
  obtain ⟨g, ε, hε, hεW, hg, hgχ⟩ := Submission.dor_lmbsf_cit_c1_local_extension P k
    (V ∩ interior C) χ y (hV.inter isOpen_interior) (hχ.mono inter_subset_left)
    ⟨hCV (interior_subset hy), hy⟩
  -- Step 2, `g(y) = χ(y)` and `Dg(y) = Dχ(y)`, since `g = χ` near `y`
  have hgy : g y = χ y := hgχ (mem_ball_self hε)
  have hDg : fderiv ℝ g y = fderiv ℝ χ y :=
    (hgχ.eventuallyEq_of_mem (ball_mem_nhds y hε)).fderiv_eq
  -- Step 3, `μ|a − b| ≤ |g(a) − g(b)|` on `B_δ₀(y)`; take `δ = min(ε, δ₀)`
  obtain ⟨δ₀, μ, hδ₀, hμ, hlip⟩ :=
    Submission.codim1_rdo_c1cov_local_lower_lipschitz P k g y hg (by rwa [hDg])
  obtain ⟨δ, hδ, hδε, hδδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧ ball y δ ⊆ ball y ε ∧ ball y δ ⊆ ball y δ₀ :=
    ⟨min ε δ₀, lt_min hε hδ₀, ball_subset_ball (min_le_left _ _),
      ball_subset_ball (min_le_right _ _)⟩
  -- Step 4, `M' = g(B_δ(y)) = χ(B_δ(y))` has approximate tangent space `Q` at `χ(y)`
  have hpiece := Submission.codim1_rdo_c1_piece_approxTangent P k g y δ μ hg hμ
    (fun a ha b hb => hlip a (hδδ₀ ha) b (hδδ₀ hb)) y (mem_ball_self hδ)
  rw [(hgχ.mono hδε).image_eq, hgy, hDg] at hpiece
  -- Step 5, `M = χ(C)` is compact, `M' ⊆ M`, and `M \ M' ⊆ χ(C \ B_δ(y))`, a compact set that
  -- misses `χ(y)` because `χ` is injective on `C`
  have hδC : ball y δ ⊆ C := hδε.trans (hεW.trans (inter_subset_right.trans interior_subset))
  have hχC : ContinuousOn χ C := hχ.continuousOn.mono hCV
  have hfar : χ y ∉ closure (χ '' C \ χ '' ball y δ) := by
    intro hcl
    obtain ⟨z, ⟨hzC, hzδ⟩, hzy⟩ := closure_minimal (subset_image_sdiff χ C (ball y δ))
      ((hC.diff isOpen_ball).image_of_continuousOn (hχC.mono sdiff_subset)).isClosed hcl
    rw [hinj hzC (interior_subset hy) hzy] at hzδ
    exact hzδ (mem_ball_self hδ)
  -- Step 6, the part of `χ(C)` away from `χ(y)` does not change the blow-up limits
  exact Submission.dor_lmbsf_cit_approxTangent_of_subset P k (χ '' C) (χ '' ball y δ) (χ y) _
    (hC.image_of_continuousOn hχC).isClosed.measurableSet (image_mono hδC) hfar hpiece
/-- **Density points see every direction.**  If `y` is a Lebesgue density point of an arbitrary set
`Z ⊆ ℝᵈ`, i.e. `Lᵈ(Z ∩ B̄_r(y)) / Lᵈ(B̄_r(y)) → 1` as `r ↓ 0`, then every unit vector `v` is a limit
of secant directions `(yᵢ - y)/|yᵢ - y|` with `yᵢ ∈ Z ∖ {y}` and `yᵢ → y`.  For `0 < η ≤ 1` and
`r > 0` the ball `B_{ηr/4}(y + (r/2)v)` lies in `B̄_r(y) ∖ {y}` and in the `η`-cone around `v`, and
it has measure `(η/4)ᵈ Lᵈ(B̄_r(y))`, so density one forces `Z` to meet it for all small `r`; take
`η = 1/(i+1)` and `r < 1/(i+1)`. -/
theorem Submission.dor_lmbsf_density_directions : ∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v) := by
  intro d Z y hdens v hv
  -- the ball `B_{ηr/4}(y + (r/2)v)` lies in `B_r(y) ∖ {y}`, inside the `η`-cone around `v`
  have cone : ∀ η r : ℝ, 0 < η → η ≤ 1 → 0 < r → ∀ z ∈ ball (y + (r / 2) • v) (η * r / 4),
      ‖z - y‖ < r ∧ z ≠ y ∧ ‖‖z - y‖⁻¹ • (z - y) - v‖ < η := by
    intro η r hη hη1 hr z hz
    have hs : (0 : ℝ) < r / 2 := by positivity
    -- the offset `w = z - y - (r/2)v` of `z` from the centre has `‖w‖ < ηr/4 ≤ r/4`
    have hw : ‖z - y - (r / 2) • v‖ < η * r / 4 := by
      rwa [mem_ball, dist_eq_norm, sub_add_eq_sub_sub] at hz
    have hw' : ‖z - y - (r / 2) • v‖ < r / 4 := hw.trans_le (by nlinarith)
    have hsv : ‖(r / 2) • v‖ = r / 2 := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hs.le]
    have hdiff : |‖z - y‖ - r / 2| ≤ ‖z - y - (r / 2) • v‖ := by
      simpa only [hsv] using abs_norm_sub_norm_le (z - y) ((r / 2) • v)
    obtain ⟨hlo, hhi⟩ := abs_le.1 hdiff
    have hpos : 0 < ‖z - y‖ := by linarith
    refine ⟨by linarith, fun h => by rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos,
      ?_⟩
    -- `‖z - y‖⁻¹ (z - y) - v = (‖z - y‖⁻¹ - (r/2)⁻¹) (z - y) + (r/2)⁻¹ w`
    have hdecomp : ‖z - y‖⁻¹ • (z - y) - v
        = (‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y) + (r / 2)⁻¹ • (z - y - (r / 2) • v) := by
      rw [sub_smul ‖z - y‖⁻¹ (r / 2)⁻¹ (z - y), smul_sub (r / 2)⁻¹ (z - y) ((r / 2) • v), smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      abel
    have h1 : ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) := by
      have hne : ‖z - y‖ ≠ 0 := hpos.ne'
      have e : (‖z - y‖⁻¹ - (r / 2)⁻¹) * ‖z - y‖ = (r / 2 - ‖z - y‖) / (r / 2) := by
        field_simp
      calc ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ = |(‖z - y‖⁻¹ - (r / 2)⁻¹) * ‖z - y‖| := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_norm]
        _ = |‖z - y‖ - r / 2| / (r / 2) := by rw [e, abs_div, abs_of_pos hs, abs_sub_comm]
        _ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) := by gcongr
    have h2 : ‖(r / 2)⁻¹ • (z - y - (r / 2) • v)‖ = ‖z - y - (r / 2) • v‖ / (r / 2) := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div]
    calc ‖‖z - y‖⁻¹ • (z - y) - v‖
        ≤ ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ + ‖(r / 2)⁻¹ • (z - y - (r / 2) • v)‖ := by
          rw [hdecomp]; exact norm_add_le _ _
      _ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) + ‖z - y - (r / 2) • v‖ / (r / 2) := by
          rw [h2]; linarith
      _ < η := by rw [← add_div, div_lt_iff₀ hs]; linarith
  -- for `0 < η ≤ 1`, `Z` meets `B_{ηr/4}(y + (r/2)v)` for all small `r > 0`: otherwise
  -- `Lᵈ(Z ∩ B̄_r(y)) ≤ Lᵈ(B̄_r(y)) - Lᵈ(B_{ηr/4}(y + (r/2)v)) = (1 - (η/4)ᵈ) Lᵈ(B̄_r(y))`
  have hit : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∃ z ∈ Z, z ∈ ball (y + (r / 2) • v) (η * r / 4) := by
    intro η hη hη1
    have hκ : ENNReal.ofReal ((η / 4) ^ d) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (hdens.eventually_const_lt (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hκ))
    refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
    by_contra! hZ
    have hB : ball (y + (r / 2) • v) (η * r / 4) ⊆ closedBall y r := fun z hz => by
      rw [mem_closedBall, dist_eq_norm]; exact (cone η r hη hη1 hr z hz).1.le
    have hvol : volume (ball (y + (r / 2) • v) (η * r / 4))
        = ENNReal.ofReal ((η / 4) ^ d) * volume (closedBall y r) := by
      rw [Measure.addHaar_ball_of_pos volume _ (by positivity : (0 : ℝ) < η * r / 4),
        Measure.addHaar_closedBall volume _ hr.le, finrank_euclideanSpace_fin, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow, show η / 4 * r = η * r / 4 by ring]
    have hle : volume (Z ∩ closedBall y r)
        ≤ (1 - ENNReal.ofReal ((η / 4) ^ d)) * volume (closedBall y r) :=
      calc volume (Z ∩ closedBall y r)
          ≤ volume (closedBall y r \ ball (y + (r / 2) • v) (η * r / 4)) :=
            measure_mono fun z hz => ⟨hz.2, hZ z hz.1⟩
        _ = volume (closedBall y r) - volume (ball (y + (r / 2) • v) (η * r / 4)) :=
            measure_sdiff hB measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
        _ = (1 - ENNReal.ofReal ((η / 4) ^ d)) * volume (closedBall y r) := by
            rw [hvol, ENNReal.sub_mul fun _ _ => measure_closedBall_lt_top.ne, one_mul]
    have hgt : 1 - ENNReal.ofReal ((η / 4) ^ d)
        < volume (Z ∩ closedBall y r) / volume (closedBall y r) := hsub ⟨hr, hrr₀⟩
    exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
  -- take `η = 1/(i+1)` and `0 < rᵢ < min(r₀, 1/(i+1))`
  have hη : ∀ i : ℕ, (0 : ℝ) < 1 / ((i : ℝ) + 1) := fun i => by positivity
  have hη1 : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 := fun i =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hseq : ∀ i : ℕ, ∃ z ∈ Z, ∃ r : ℝ, 0 < r ∧ r < 1 / ((i : ℝ) + 1) ∧
      z ∈ ball (y + (r / 2) • v) (1 / ((i : ℝ) + 1) * r / 4) := by
    intro i
    obtain ⟨r₀, hr₀, h⟩ := hit _ (hη i) (hη1 i)
    have hm : 0 < min r₀ (1 / ((i : ℝ) + 1)) := lt_min hr₀ (hη i)
    obtain ⟨z, hzZ, hz⟩ := h (min r₀ (1 / ((i : ℝ) + 1)) / 2) (by positivity)
      (by linarith [min_le_left r₀ (1 / ((i : ℝ) + 1))])
    exact ⟨z, hzZ, _, by positivity, by linarith [min_le_right r₀ (1 / ((i : ℝ) + 1))], hz⟩
  choose ys hysZ rs hrs hrsi hysB using hseq
  have hcone := fun i => cone _ (rs i) (hη i) (hη1 i) (hrs i) (ys i) (hysB i)
  refine ⟨ys, fun i => ⟨hysZ i, (hcone i).2.1⟩, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => ((hcone i).1.trans (hrsi i)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => (hcone i).2.2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
