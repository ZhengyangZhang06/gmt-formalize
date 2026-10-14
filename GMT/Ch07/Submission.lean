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
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]
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

/-- **Simon Ch. 6, 3.1 (‡)**: for an integer multiplicity triple `(M, θ, ξ)` in `U`, a compact
`K ⊆ U` and an `n`-covector `α`, the component `θ ⟨α, ξ⟩` is `Hⁿ`-integrable on `M ∩ K`.  `θ` is
locally `Hⁿ`-integrable, and `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, so `‖ξ‖ ≤ 1` and
`|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ`, an integrable majorant on `M ∩ K`. -/
theorem Submission.lcn_mult_mul_orient_apply_integrableOn : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → ∀ α : Covector (Euclid P) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x α) (R.carrier ∩ K) μHE[n] := by
  intro P n U K R hK hKU α
  -- `μ := Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`
  have hμ : μHE[n].restrict (R.carrier ∩ K) ≤ μHE[n].restrict R.carrier :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- `θ` is `μ`-integrable, as `∫⁻_{M ∩ K} θ dHⁿ < ∞`; hence so is `‖α‖ θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hmaj : Integrable (fun x => ‖α‖ * (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
    simpa using (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
      (R.locallyIntegrable_mult K hK hKU)).const_mul ‖α‖
  -- `‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e., hence `μ`-a.e.
  have hξ : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ K)), ‖R.orient x‖ ≤ 1 := by
    refine ae_mono hμ ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `θ ⟨α, ξ⟩` is `μ`-a.e. strongly measurable: `ξ` is, and evaluation at `α` is continuous
  have hm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ K)) := by
    have hξα : AEStronglyMeasurable (fun x => R.orient x α) (μHE[n].restrict (R.carrier ∩ K)) :=
      (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_measure hμ)
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul hξα
  -- domination: `|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ` `μ`-a.e.
  refine hmaj.mono' hm ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (R.mult x : ℝ) * |R.orient x α| ≤ (R.mult x : ℝ) * (‖R.orient x‖ * ‖α‖) := by
        gcongr
        exact (Real.norm_eq_abs _).symm.trans_le ((R.orient x).le_opNorm α)
    _ ≤ (R.mult x : ℝ) * (1 * ‖α‖) := by gcongr
    _ = ‖α‖ * R.mult x := by ring

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then for every
`n`-covector `α`, `⟨α, ξ⟩ = 0` `Hⁿ`-a.e. on `M ∩ W`.  Let `ν = Hⁿ⌞(M ∩ closure W)`; then
`f = θ ⟨α, ξ⟩` is `ν`-integrable (`lcn_mult_mul_orient_apply_integrableOn`, `closure W` being a
compact subset of `U`).  For smooth `g` with compact support in `W`, `ω = g α` is a test form in
`U` supported in `W`, so `0 = T(ω) = ∫_M θ ⟨g α, ξ⟩ dHⁿ = ∫ g f dν` (`g = 0` off `W`).  The
fundamental lemma of the calculus of variations on `W` gives `f = 0` `ν`-a.e. on `W`; as
`Hⁿ⌞(M ∩ W) ≤ ν` and `θ > 0` on `M`, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. -/
theorem Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW α
  -- `f = θ ⟨α, ξ⟩` is integrable for `ν = Hⁿ⌞(M ∩ closure W)`
  have hf : Integrable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ closure W)) :=
    Submission.lcn_mult_mul_orient_apply_integrableOn P n U (closure W) R hWc hWU α
  -- fundamental lemma on the open set `W`: `f = 0` `ν`-a.e. on `W`
  have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ closure W)), x ∈ W →
      (R.mult x : ℝ) * R.orient x α = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrable.locallyIntegrableOn W) fun g hg hgc hgW => ?_
    -- `ω = g α` is a test form in `U` supported in `W`, so `T(ω) = 0`
    have hωW : tsupport (fun x => g x • α) ⊆ W := (tsupport_smul_subset_left g _).trans hgW
    have hω : (fun x => g x • α) ∈ TestFormOn U n :=
      ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, hωW.trans (subset_closure.trans hWU)⟩
    calc ∫ x, g x • ((R.mult x : ℝ) * R.orient x α) ∂(μHE[n].restrict (R.carrier ∩ closure W))
        = ∫ x in R.carrier ∩ closure W, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          congr 1
          funext x
          rw [map_smul, smul_eq_mul, smul_eq_mul]
          ring
      -- `g = 0` off `closure W`, so the integral over `M` is the integral over `M ∩ closure W`
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
            inter_subset_left fun x hx => ?_).symm
          have hgx : g x = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, subset_closure (hgW h)⟩
          rw [hgx, zero_smul, map_zero, mul_zero]
      _ = T ⟨_, hω⟩ := (hRT ⟨_, hω⟩).symm
      _ = 0 := hTW ⟨_, hω⟩ hωW
  -- pass to `Hⁿ⌞(M ∩ W) ≤ ν` and cancel `θ > 0` on `M`
  have hle : μHE[n].restrict (R.carrier ∩ W) ≤ μHE[n].restrict (R.carrier ∩ closure W) :=
    Measure.restrict_mono (inter_subset_inter_right _ subset_closure) le_rfl
  filter_upwards [ae_mono hle hae,
    ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)] with x hx hxMW
  have hθ : (R.mult x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (R.mult_pos x hxMW.1).ne'
  exact (mul_eq_zero.mp (hx hxMW.2)).resolve_left hθ

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then
`Hⁿ(M ∩ W) = 0`.  `Λⁿ` is finite-dimensional (`lcn_covector_finiteDimensional`); for each `α` of
a basis, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. (`lcn_orient_apply_ae_eq_zero_of_vanishesOn`), so
`ξ = 0` `Hⁿ⌞(M ∩ W)`-a.e.  But `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, hence nonzero
(`imsupp_unit_orientation_ne_zero_norm_le_one`), so `Hⁿ⌞(M ∩ W) = 0`. -/
theorem Submission.imrep_carrier_inter_null_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μHE[n] (R.carrier ∩ W) = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW
  -- a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ`
  have := Submission.lcn_covector_finiteDimensional P n
  let b := Module.finBasis ℝ (Covector (Euclid P) n)
  -- `⟨αₖ, ξ⟩ = 0` for every `k`, `Hⁿ⌞(M ∩ W)`-a.e.
  have h0 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ k, R.orient x (b k) = 0 :=
    ae_all_iff.mpr fun k =>
      Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn P n U W T R hRT hW hWc hWU hTW (b k)
  -- `ξ ≠ 0` `Hⁿ⌞M`-a.e., hence `Hⁿ⌞(M ∩ W)`-a.e.
  have h1 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x ≠ 0 := by
    refine ae_mono (Measure.restrict_mono inter_subset_left le_rfl) ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).1
  -- a functional on `Λⁿ` vanishing on a basis is zero, so `Hⁿ⌞(M ∩ W)`-a.e. `x` is impossible
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), False := by
    filter_upwards [h0, h1] with x hx hne
    exact hne (ContinuousLinearMap.coe_injective (b.ext fun k => hx k))
  exact Measure.restrict_eq_zero.mp (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp h2))

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` in `U`, then `Hⁿ(M ∖ spt T) = 0`, i.e.
`μ_T(U ∖ spt T) = 0`.  As `M ⊆ U` and `spt T = U ∖ Z`, `M ∖ spt T ⊆ M ∩ Z`, where the zero region
`Z = ⋃ 𝒲` is the union of the open `W ⊂⊂ U` on which `T` vanishes.  `ℝᴾ` is second countable, so
`Z = ⋃_{W ∈ 𝒮} W` for a countable `𝒮 ⊆ 𝒲`; each `Hⁿ(M ∩ W) = 0`
(`imrep_carrier_inter_null_of_vanishesOn`), and countable subadditivity concludes. -/
theorem Submission.imrep_carrier_sdiff_support_null : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → μHE[n] (R.carrier \ T.support) = 0 := by
  intro P n U T R _ hRT
  -- the zero region `Z = ⋃₀ 𝒲` is the union of a countable subfamily `𝒮 ⊆ 𝒲`
  obtain ⟨𝒮, h𝒮c, h𝒮W, h𝒮⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Euclid P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- `M ∖ spt T ⊆ ⋃_{W ∈ 𝒮} M ∩ W`: a point of `M ⊆ U` outside `spt T = U ∖ Z` lies in `Z`
  have hsub : R.carrier \ T.support ⊆ ⋃ W ∈ 𝒮, R.carrier ∩ W := by
    rintro x ⟨hxM, hxS⟩
    have hxZ : x ∈ ⋃₀ 𝒮 := by
      rw [h𝒮]
      by_contra hxZ
      exact hxS (mem_sdiff_of_mem (R.carrier_subset hxM) hxZ)
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxZ
    exact mem_biUnion hW ⟨hxM, hxW⟩
  -- `Hⁿ(M ∩ W) = 0` for each of the countably many `W ∈ 𝒮`
  refine measure_mono_null hsub ((measure_biUnion_null_iff h𝒮c).mpr fun W hW => ?_)
  obtain ⟨hWo, hWc, hWU, hTW⟩ := h𝒮W hW
  exact Submission.imrep_carrier_inter_null_of_vanishesOn P n U W T R hRT hWo hWc hWU hTW
/-- **Simon Ch. 3, 1.4**: approximate tangent planes are local and do not see `Hⁿ`-null
modifications.  If `M' ⊆ M`, `V` is open, `x ∈ V` and `Hⁿ((M \ M') ∩ V) = 0`, then an
approximate tangent plane of `M` at `x` is one of `M'`.  Given `f ∈ C_c(ℝᴾ)`, take
`B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`.  For `0 < r < s / L` the parts of `η_{x,r}(M)` and
`η_{x,r}(M')` in `B_L(0)` differ inside `η_{x,r}((M \ M') ∩ V)`, which is `Hⁿ`-null because
`η_{x,r}` is Lipschitz.  So the blow-up integrals agree for small `r` and have the same limit. -/
theorem Submission.dtc_approxTangent_of_null_diff : ∀ (P n : ℕ) (M M' V : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), M' ⊆ M → IsOpen V → x ∈ V → μHE[n] ((M \ M') ∩ V) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' V x Q hMM' hV hxV hnull hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV x hxV
  obtain ⟨L, hL, hfL⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  -- the blow-up integrals of `M` and `M'` agree for `0 < r < s / L`, so they have the same limit
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
  have hr0 : 0 < r := hr.1
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη]
  -- `f` vanishes off `B_L(0)`, so every set integral may be cut to `B_L(0)`
  have hfB : ∀ y, y ∉ ball (0 : Euclid P) L → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hfL h)
  have hcut : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) L ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hfB).symm
  -- `η_{x,r}` is `r⁻¹`-Lipschitz, so it maps the `Hⁿ`-null set `(M \ M') ∩ V` to a null set
  have hnullimg : μHE[n] ((fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V)) = 0 := by
    have hlip : LipschitzWith ‖r⁻¹‖₊ (fun y : Euclid P => r⁻¹ • (y - x)) :=
      LipschitzWith.of_dist_le_mul fun a b =>
        le_of_eq (by rw [dist_smul₀, dist_sub_right, coe_nnnorm])
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul] at hnull ⊢
    have hH : μH[(n : ℝ)] ((M \ M') ∩ V) = 0 := by
      simpa [Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n] using hnull
    have hle := hlip.hausdorffMeasure_image_le (Nat.cast_nonneg n) ((M \ M') ∩ V)
    rw [hH, mul_zero, nonpos_iff_eq_zero] at hle
    rw [hle, mul_zero]
  -- in `B_L(0)`, `η_{x,r}(M)` and `η_{x,r}(M')` differ inside `η_{x,r}((M \ M') ∩ V)`
  have hsub : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) \
      (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M') ⊆
      (fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V) := by
    rintro y ⟨⟨hyB, ⟨z, hz, rfl⟩⟩, hy'⟩
    refine ⟨z, ⟨⟨hz, fun hz' => hy' ⟨hyB, z, hz', rfl⟩⟩, hsV ?_⟩, rfl⟩
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
      inv_mul_lt_iff₀ hr0] at hyB
    have hrL := (lt_div_iff₀ hL).mp hr.2
    rw [mem_ball, dist_eq_norm]
    linarith
  -- hence the two parts are `Hⁿ`-a.e. equal (`M' ⊆ M` gives the other inclusion)
  have hae : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M' : Set (Euclid P))
      =ᵐ[μHE[n]] (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) := by
    rw [ae_eq_set]
    constructor
    · rw [sdiff_eq_empty.mpr (inter_subset_inter_right _ (image_mono hMM'))]
      exact measure_empty
    · exact measure_mono_null hsub hnullimg
  rw [hcut, hcut ((fun y : Euclid P => r⁻¹ • (y - x)) '' M'), Measure.restrict_congr_set hae]

/-- **An integer multiplicity triple essentially carried by a compact set moves to any domain
containing it** (step 6.6 of the localization in the proof of Simon 7.3.1; Simon 6.3.1,
chapter-06.txt lines 733–753).  If `R = (M, θ, ξ)` is an `IMRep` in `V`, `K ⊆ V ∩ U` is compact
and `Hⁿ(M \ K) = 0`, then `(M ∩ K, θ, ξ)` is an `IMRep` in `U` with the same action: `M ∩ K` and
`M` differ by the `Hⁿ`-null set `M \ K`, so `Hⁿ⌞(M ∩ K) = Hⁿ⌞M`; `∫_{M ∩ K} θ dHⁿ < ∞` since
`K ⊆ V` is compact; and `M ∩ K` has the approximate tangent planes of `M`
(`dtc_approxTangent_of_null_diff` with the open set `ℝᴾ`). -/
theorem Submission.dtc_imrep_of_null_off_compact : ∀ (P n : ℕ) (U V K : Set (Euclid P)) (R : IMRep V n), IsCompact K → K ⊆ V → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → ∃ R' : IMRep U n, R'.carrier ⊆ K ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action ω := by
  intro P n U V K R hK hKV hKU hnull
  have hsub : R.carrier ∩ K ⊆ R.carrier := inter_subset_left
  have hdiff : R.carrier \ (R.carrier ∩ K) = R.carrier \ K := Set.sdiff_self_inter
  -- `M ∩ K =ᵐ M`: `(M ∩ K) \ M = ∅` and `M \ (M ∩ K) = M \ K` is `Hⁿ`-null.
  have hrestr : μHE[n].restrict (R.carrier ∩ K) = μHE[n].restrict R.carrier := by
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, hdiff ▸ hnull⟩)
    rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  refine ⟨
    { carrier := R.carrier ∩ K
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hK.isClosed.measurableSet
      carrier_subset := inter_subset_right.trans hKU
      rectifiable := R.rectifiable.mono hsub
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      -- `∫_{(M ∩ K) ∩ C} θ ≤ ∫_{M ∩ K} θ < ∞`, using only that `K ⊆ V` is compact.
      locallyIntegrable_mult := fun _ _ _ => ne_top_of_le_ne_top
        (R.locallyIntegrable_mult K hK hKV) (lintegral_mono_set inter_subset_left)
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hsub le_rfl)
      -- a.e. on `M ∩ K`, the plane `Q` oriented by `ξ(x)` is also `Tₓ(M ∩ K)`.
      orients := (ae_restrict_of_ae_restrict_of_subset hsub R.orients).mono
        fun x ⟨Q, hQ, hξ⟩ => ⟨Q, Submission.dtc_approxTangent_of_null_diff P n R.carrier
          (R.carrier ∩ K) univ x Q hsub isOpen_univ (mem_univ x)
          (by rw [inter_univ, hdiff]; exact hnull) hQ, hξ⟩ },
    inter_subset_right, fun ω => ?_⟩
  -- the actions are integrals of the same function against the same measure
  change ∫ x in R.carrier ∩ K, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n] =
    ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]
  rw [hrestr]
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

/-- **Extension by zero** (steps 6.2–6.6 of the localization in the proof of Simon 7.3.1).  Let
`V ⊆ U` be open, `K ⊆ V` compact and `X = τ(M, θ, ξ) ∈ 𝒟ₙ(V)` with `Hⁿ(M \ K) = 0`.  Move the
representation to `U` with carrier in `K` and let `Y ∈ 𝒟ₙ(U)` be the current it defines.  Then
`Y⌞V = X`; `Y` kills every form whose support misses `K`, so `spt Y = K \ Z_Y` is a compact subset
of `K`; and if `∂X = 0`, then for a cutoff `χ ∈ C^∞_c(V)` equal to `1` near `K` we get
`∂Y(ω) = Y(dω) = X(d(χω)) = ∂X(χω) = 0`, since `d(χω) = dω` near the carrier. -/
theorem Submission.dtc_extend_by_zero : ∀ (P n : ℕ) (U V K : Set (Euclid P)) (hVU : V ⊆ U) (X : GeometricCurrentOn V n) (R : IMRep V n), IsOpen U → IsOpen V → IsCompact K → K ⊆ V → R.Represents X → μHE[n] (R.carrier \ K) = 0 → ∃ Y : GeometricCurrentOn U n, Y.restrictDomain hVU = X ∧ Y.support ⊆ K ∧ IsCompact Y.support ∧ (BoundaryVanishes X → BoundaryVanishes Y) ∧ IsIntegerMultiplicity Y := by
  intro P n U V K hVU X R hU hV hK hKV hRX hnull
  -- Step 1: move `R` to `U`, with carrier in `K` and the same action
  obtain ⟨R', hR'K, hR'R⟩ :=
    Submission.dtc_imrep_of_null_off_compact P n U V K R hK hKV (hKV.trans hVU) hnull
  -- Step 2: `Y = τ(R')`, which is integer multiplicity
  obtain ⟨Y, hY⟩ := Submission.dtc_imrep_current P n U R'
  -- Step 4: `Y` vanishes on forms whose support misses `K`
  have hvan : ∀ ω : TestFormOn U n,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → Y ω = 0 := by
    intro ω hω
    rw [hY ω, IMRep.action]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport (Set.disjoint_right.mp hω (hR'K hx)), map_zero,
      mul_zero]
  -- Step 5: `spt Y ⊆ K`; a point of `U \ K` has a ball `W ⊂⊂ U \ K` on which `Y` vanishes
  have hspt : Y.support ⊆ K := by
    rintro q ⟨hqU, hqZ⟩
    by_contra hqK
    obtain ⟨r, hr, hrUK⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) q ⟨hqU, hqK⟩
    have hcl : closure (ball q (r / 2)) ⊆ ball q r :=
      closure_ball_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hr))
    refine hqZ (mem_sUnion.mpr ⟨ball q (r / 2), ⟨isOpen_ball,
      (isCompact_closedBall q (r / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall,
      hcl.trans (hrUK.trans sdiff_subset), fun ω hω => hvan ω ?_⟩, mem_ball_self (half_pos hr)⟩)
    exact disjoint_sdiff_left.mono_left (hω.trans (subset_closure.trans (hcl.trans hrUK)))
  -- Step 6: `spt Y = K \ Z_Y` is compact
  have hcpt : IsCompact Y.support := by
    have heq : Y.support = K \ Y.zeroRegion :=
      Subset.antisymm (fun x hx => ⟨hspt hx, hx.2⟩) fun x hx => ⟨hVU (hKV hx.1), hx.2⟩
    rw [heq]
    exact hK.diff Y.isOpen_zeroRegion
  -- Step 3: `Y⌞V = X`, since `R'` and `R` have the same action
  have hres : Y.restrictDomain hVU = X := by
    ext ω
    rw [GeometricCurrentOn.restrictDomain_apply, hY (testFormOnInclusion hVU n ω),
      testFormOnInclusion_coe, hR'R, hRX ω]
  refine ⟨Y, hres, hspt, hcpt, ?_, ⟨R', hY⟩⟩
  -- Step 7: `∂X = 0 → ∂Y = 0` (trivial in degree `0`)
  rcases n with _ | m
  · exact fun _ => trivial
  intro hX
  change X.boundary = 0 at hX
  change Y.boundary = 0
  -- Step 7.1: a cutoff `χ ∈ C^∞_c(V)` equal to `1` on an open set `O ⊇ K`
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨χ, hχ1, hχ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Euclid P)) (n := ⊤) hK.isClosed
    ((self_subset_thickening hδ K).trans (thickening_subset_interior_cthickening δ K))
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχsupp : tsupport χ ⊆ cthickening δ K :=
    closure_minimal (fun x hx => by_contra fun h => hx (hχ0 x h)) isClosed_cthickening
  have hχc : HasCompactSupport χ :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hχsupp
  obtain ⟨O, hO, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  -- Step 7.2: `χω ∈ 𝒟^m(V)` for `ω ∈ 𝒟^m(U)`
  have hcut : ∀ ω : TestFormOn U m,
      (fun x => χ x • (ω : DifferentialForm (Euclid P) m) x) ∈ testFormOnSubmodule V m :=
    fun ω => ⟨⟨hχs.smul ω.property.1.1, hχc.smul_right⟩,
      (tsupport_smul_subset_left _ _).trans (hχsupp.trans hδV)⟩
  -- Step 7.4: `∂Y(ω) = R'(dω) = R'(d(χω)) = R(d(χω)) = X(d(χω)) = ∂X(χω) = 0`
  ext ω
  rw [GeometricCurrentOn.zero_apply, GeometricCurrentOn.boundary_apply,
    hY (exteriorDerivativeTestOn U m ω)]
  have hd : R'.action (exteriorDerivativeTestOn U m ω : DifferentialForm (Euclid P) (m + 1)) =
      R'.action (exteriorDerivativeTestOn V m ⟨_, hcut ω⟩ :
        DifferentialForm (Euclid P) (m + 1)) := by
    unfold IMRep.action
    refine setIntegral_congr_fun R'.measurableSet_carrier fun x hx => ?_
    -- Step 7.3: `χω = ω` near `x ∈ M' ⊆ K ⊆ O`, so `d(χω)(x) = dω(x)`
    have hloc : (fun y => χ y • (ω : DifferentialForm (Euclid P) m) y) =ᶠ[𝓝 x]
        (ω : DifferentialForm (Euclid P) m) :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds (hKO (hR'K hx))) fun y hy => by
        rw [show χ y = 1 from hOχ hy, one_smul]
    show (R'.mult x : ℝ) * R'.orient x (extDeriv (ω : DifferentialForm (Euclid P) m) x) =
      (R'.mult x : ℝ) * R'.orient x
        (extDeriv (fun y => χ y • (ω : DifferentialForm (Euclid P) m) y) x)
    rw [hloc.extDeriv_eq]
  rw [hd, hR'R, ← hRX, ← GeometricCurrentOn.boundary_apply, hX, GeometricCurrentOn.zero_apply]
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
/-- **Simon 6.2.5, 6.2.16** (mass across a change of domain).  If `W ⊆ V ⊆ U`, and
`S ∈ 𝒟ₙ(U)`, `S' ∈ 𝒟ₙ(V)` agree on every `ω ∈ 𝒟ⁿ(V)` with `spt ω ⊆ W`, then
`M_W(S) = M_W(S')`.  A form admissible for `M_W` has `spt ω ⊆ W ⊆ V`, so the admissible forms in
`U` and in `V` are the same underlying forms, related by `testFormOnInclusion`; the two suprema
therefore range over the same values. -/
theorem Submission.dtc_massOn_eq_of_agreeOn : ∀ (P n : ℕ) (U V W : Set (Euclid P)) (hVU : V ⊆ U) (S : GeometricCurrentOn U n) (S' : GeometricCurrentOn V n), W ⊆ V → (∀ ω : TestFormOn V n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → S (testFormOnInclusion hVU n ω) = S' ω) → S.massOn W = S'.massOn W := by
  intro P n U V W hVU S S' hWV hagree
  -- both masses are suprema of `ofReal (T ω)` over admissible forms: compare the value sets
  unfold GeometricCurrentOn.massOn
  congr 1
  ext r
  constructor
  · -- an admissible `ω ∈ 𝒟ⁿ(U)` has `spt ω ⊆ W ⊆ V`, so it is an admissible `ω' ∈ 𝒟ⁿ(V)`
    rintro ⟨ω, hω, rfl⟩
    let ω' : TestFormOn V n := ⟨ω, ω.property.1, hω.1.trans hWV⟩
    have hincl : testFormOnInclusion hVU n ω' = ω := Subtype.ext rfl
    refine ⟨ω', hω, ?_⟩
    dsimp only
    rw [← hagree ω' hω.1, hincl]
  · -- an admissible `ω' ∈ 𝒟ⁿ(V)` is admissible in `U` after inclusion
    rintro ⟨ω', hω', rfl⟩
    refine ⟨testFormOnInclusion hVU n ω', hω', ?_⟩
    dsimp only
    rw [hagree ω' hω'.1]
/-- **Simon 7.2 (proof), cutoff** (an extension to `ℝᴾ` supported in a compact `K ⊂ U` has no
more mass or boundary mass than its restriction to `U`).  Let `X ∈ 𝒟ₘ₊₁(U)` and
`Y ∈ 𝒟ₘ₊₁(ℝᴾ)` with `Y(ιη) = X(η)` for `η ∈ 𝒟ᵐ⁺¹(U)` and `spt Y ⊆ K`.  By Simon 6.2.11, `Y`
kills every `ω` with `spt ω ∩ K = ∅`, and so does `∂Y`, since `spt dω ⊆ spt ω`.  The cutoff
`X̂(ω) = X(ζω)`, `ζ = 1` near `K`, `spt ζ ⊆ U`, gives `M(Y) ≤ M_U(Y)` and `M(∂Y) ≤ M_U(∂Y)`.
Finally `Y`, `X` agree on test forms in `U`, and so do `∂Y`, `∂X`, because `d(ιη) = ι(dη)`;
hence `M_U(Y) = M_U(X) = M(X)` and `M_U(∂Y) = M_U(∂X) = M(∂X)`. -/
theorem Submission.cmc_fc_eu_cutoff_mass_le : ∀ (P m : ℕ) (U K : Set (Euclid P)) (X : GeometricCurrentOn U (m + 1)) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen U → IsCompact K → K ⊆ U → Y.restrictDomain (subset_univ U) = X → Y.support ⊆ K → Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass := by
  intro P m U K X Y hU hK hKU hYX hYK
  -- `Y(ω) = 0` when `spt ω ∩ K = ∅`, as `spt Y ⊆ K` (Simon 6.2.11)
  have hvan : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → Y ω = 0 :=
    fun ω hω => Submission.dtc_vanish_off_support P (m + 1) univ Y ω (hω.mono_right hYK)
  -- `∂Y(ω) = Y(dω) = 0` when `spt ω ∩ K = ∅`, as `spt dω ⊆ spt ω`
  have hvan' : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) K → Y.boundary ω = 0 := by
    intro ω hω
    rw [GeometricCurrentOn.boundary_apply]
    exact hvan _ (hω.mono_left (tsupport_exteriorDerivative_subset _))
  -- `Y(ιη) = X(η)`, and `∂Y(ιη) = Y(d(ιη)) = Y(ι(dη)) = X(dη) = ∂X(η)`
  have hagree : ∀ η : TestFormOn U (m + 1),
      Y (testFormOnInclusion (subset_univ U) (m + 1) η) = X η := by
    intro η
    rw [← hYX, GeometricCurrentOn.restrictDomain_apply]
  have hagree' : ∀ η : TestFormOn U m,
      Y.boundary (testFormOnInclusion (subset_univ U) m η) = X.boundary η := by
    intro η
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply,
      ← hagree (exteriorDerivativeTestOn U m η)]
    rfl
  constructor
  · -- `M(Y) ≤ M_U(Y) = M_U(X) = M(X)`
    calc Y.mass ≤ Y.massOn U :=
          Submission.lcmp_massOn_le_of_vanish_off_compact P (m + 1) univ U K Y hK hU hKU hvan univ
      _ = X.mass :=
          Submission.dtc_massOn_eq_of_agreeOn P (m + 1) univ U U (subset_univ U) Y X
            Subset.rfl fun η _ => hagree η
  · -- `M(∂Y) ≤ M_U(∂Y) = M_U(∂X) = M(∂X)`
    calc Y.boundary.mass ≤ Y.boundary.massOn U :=
          Submission.lcmp_massOn_le_of_vanish_off_compact P m univ U K Y.boundary hK hU hKU
            hvan' univ
      _ = X.boundary.mass :=
          Submission.dtc_massOn_eq_of_agreeOn P m univ U U (subset_univ U) Y.boundary X.boundary
            Subset.rfl fun η _ => hagree' η

/-- **Extension to `ℝᴾ`** (step 3(c) of the flat-convergence argument in the proof of Simon
7.2.4: a current supported in a compact `K ⊂ U` extends to `ℝᴾ` without increasing masses).  Let
`U` be open, `K ⊆ U` compact and `X = τ(M, θ, ξ) ∈ 𝒟_{m+1}(U)` with `spt X ⊆ K`.  Then
`Hⁿ(M \ K) ≤ Hⁿ(M \ spt X) = 0`, so extension by zero gives an integer multiplicity
`Y ∈ 𝒟_{m+1}(ℝᴾ)` with `Y⌞U = X` and `spt Y ⊆ K`.  For a cutoff `ζ ∈ C^∞_c(U; [0, 1])` equal to
`1` near `K` we get `Y(ω) = X(ζω)` and `∂Y(ω) = ∂X(ζω)`, with `|ζω| ≤ 1` whenever `|ω| ≤ 1`, so
`M(Y) ≤ M(X)` and `M(∂Y) ≤ M(∂X)`.  The two hypotheses (restricted representations, and mass
equal to the measure of a representation) are not needed. -/
theorem Submission.cmc_fc_extend_to_univ : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P m : ℕ) (U K : Set (Euclid P)) (X : GeometricCurrentOn U (m + 1)), IsOpen U → IsCompact K → K ⊆ U → IsIntegerMultiplicity X → X.support ⊆ K → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y ∧ Y.restrictDomain (subset_univ U) = X ∧ Y.support ⊆ K ∧ Y.mass ≤ X.mass ∧ Y.boundary.mass ≤ X.boundary.mass := by
  intro _hIR _hME P m U K X hU hK hKU hX hspt
  -- Steps 1–2: a representation `R = (M, θ, ξ)` of `X` has `Hⁿ(M \ K) ≤ Hⁿ(M \ spt X) = 0`
  obtain ⟨R, hR⟩ := hX
  have hnull : μHE[m + 1] (R.carrier \ K) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hspt)
      (Submission.imrep_carrier_sdiff_support_null P (m + 1) U X R hU hR)
  -- Steps 3–6: extension by zero to `ℝᴾ`: `Y⌞U = X`, `spt Y ⊆ K`, `Y` integer multiplicity
  obtain ⟨Y, hres, hsupp, -, -, hYIM⟩ := Submission.dtc_extend_by_zero P (m + 1) univ U K
    (subset_univ U) X R isOpen_univ hU hK hKU hR hnull
  -- Steps 7–8: the cutoff argument gives `M(Y) ≤ M(X)` and `M(∂Y) ≤ M(∂X)`
  obtain ⟨hm, hbm⟩ := Submission.cmc_fc_eu_cutoff_mass_le P m U K X Y hU hK hKU hres hsupp
  exact ⟨Y, hYIM, hres, hsupp, hm, hbm⟩

/-- **Slicing localization** (Simon Ch. 6, 4.6–4.10, and the general case of the proof of 6.2,
which cuts an integer multiplicity current at a good level by 4.5).  Assume the mass
representation (REP), the restriction (IMC)(b) and the orientation bound (IMC)(d) of integer
multiplicity representations, and slicing (SL).  Let `R ∈ 𝒟_{d+1}(U)` be integer multiplicity
with `M_W(∂R) < ∞` for every open `W ⊂⊂ U`, and `x₀ ∈ U`.  Then for some `r > 0` with
`B̄_r(x₀) ⊆ U`, `R' = R⌞B_r(x₀)` is integer multiplicity, `spt R' ⊆ B̄_r(x₀)`, `M(R') < ∞`,
`M(∂R') < ∞` and `∂R' = ∂R` on forms supported in `B_r(x₀)`.  Slice by `f = |x − x₀|`: the
integrated slice bound on `(0, r₀)` gives `r` with `M_{B_{r₀}(x₀)}(∂(R⌞B_r) − (∂R)⌞B_r) < ∞`,
and this current vanishes off the compact sphere `{f = r} ⊆ B_{r₀}(x₀)`, so its total mass is
finite. -/
theorem Submission.dtc_bc_tc_cl_bim_slice_localization : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P d : ℕ) (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)) (x₀ : Euclid P), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → x₀ ∈ U → ∃ r : ℝ, 0 < r ∧ closedBall x₀ r ⊆ U ∧ ∃ R' : GeometricCurrentOn U (d + 1), IsIntegerMultiplicity R' ∧ R'.support ⊆ closedBall x₀ r ∧ R'.mass < ∞ ∧ R'.boundary.mass < ∞ ∧ ∀ η : TestFormOn U d, tsupport (η : DifferentialForm (Euclid P) d) ⊆ ball x₀ r → R'.boundary η = R.boundary η := by
  intro hREP hIMCb hIMCd hSL P d U R x₀ hU hRim hbd hx₀
  -- Step 0: `M_W(X) ≤ ν(W)` if `X(ω) = ∫ ⟨ω, ζ⟩ dν` and `|⟨α, ζ⟩| ≤ |α|` `ν`-a.e.
  have hmassle : ∀ {k : ℕ} (X : GeometricCurrentOn U k) (ν : Measure (Euclid P))
      (ζ : Euclid P → MultiVector P k),
      (∀ᵐ x ∂ν, ∀ α : Covector (Euclid P) k, |ζ x α| ≤ covectorEuclideanNorm α) →
      (∀ ω : TestFormOn U k, X ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν) →
      ∀ W : Set (Euclid P), X.massOn W ≤ ν W := by
    intro k X ν ζ hζ hrep W
    apply sSup_le
    rintro _ ⟨ω, ⟨hsupp, hnorm⟩, rfl⟩
    change ENNReal.ofReal (X ω) ≤ ν W
    rw [hrep ω]
    calc ENNReal.ofReal (∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν)
        ≤ ‖∫ x, ζ x ((ω : DifferentialForm (Euclid P) k) x) ∂ν‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖ζ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, W.indicator 1 x ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hζ] with x hx
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW, Pi.one_apply, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.mpr ((hx _).trans (hnorm x))
          · have : (ω : DifferentialForm (Euclid P) k) x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun h => hxW (hsupp h))
            simp [this]
      _ ≤ ν W := lintegral_indicator_one_le W
  -- Step 1: `R(ω) = ∫ ⟨ω, ξ⟩ dμ` for the weight `μ = θ H^{d+1}⌞M` of an IMRep `(M, θ, ξ)` of `R`
  obtain ⟨R₀, hR₀⟩ := hRim
  obtain ⟨hac, haesm, hrestr⟩ := Submission.lcmp_imRep_measure_restrict P (d + 1) U R₀
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R₀.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact lt_top_iff_ne_top.mpr (R₀.locallyIntegrable_mult K hK hKU)
  have hξb : ∀ᵐ x ∂R₀.measure, ∀ α : Covector (Euclid P) (d + 1),
      |R₀.orient x α| ≤ covectorEuclideanNorm α :=
    hac.ae_le (hIMCd P (d + 1) U R₀)
  have hRrep : ∀ ω : TestFormOn U (d + 1),
      R ω = ∫ x, R₀.orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂R₀.measure := by
    intro ω
    have h := (hrestr univ R₀ MeasurableSet.univ (inter_univ _).symm rfl rfl).2
      (ω : DifferentialForm (Euclid P) (d + 1))
    rw [Measure.restrict_univ] at h
    rw [hR₀ ω, h]
  -- Step 2: `∂R(η) = ∫ ⟨η, ξ'⟩ dμ'` by (REP)
  obtain ⟨μ', ξ', -, hfin', -, haesm', hξ'b, hbrep, -⟩ := hREP P d U R.boundary hU hbd
  -- Step 3: `r₀ = ε/2` with `B̄_{r₀}(x₀) ⊆ B_ε(x₀) ⊆ U`
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  have hr₀pos : 0 < ε / 2 := by positivity
  have hcb₀ : closedBall x₀ (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  have hfL : LipschitzWith 1 (fun x : Euclid P => dist x x₀) := LipschitzWith.dist_left x₀
  -- Step 4: slice by the 1-Lipschitz `f = |x − x₀|`, so `{f < t} = B_t(x₀)`
  obtain ⟨A, B, hA, hB, hAB, -, hint5⟩ := hSL P d U R R₀.measure μ' R₀.orient ξ'
    (fun x => dist x x₀) 1 hU hfin hfin' haesm haesm' hξb (Eventually.of_forall hξ'b) hRrep hbrep
    hfL
  have hfinball : R₀.measure (closedBall x₀ (ε / 2)) < ∞ := hfin _ (isCompact_closedBall _ _) hcb₀
  have hfinball' : μ' (closedBall x₀ (ε / 2)) < ∞ := hfin' _ (isCompact_closedBall _ _) hcb₀
  -- Step 5: a good radius, from `∫_{(0, r₀)} M_G(∂A_t − B_t) dt ≤ μ(G) < ∞`, `G = B_{r₀}(x₀)`
  obtain ⟨r, hr, hZr⟩ : ∃ r ∈ Ioo 0 (ε / 2),
      ((A r).boundary - B r).massOn (ball x₀ (ε / 2)) < ∞ := by
    by_contra hcon
    push Not at hcon
    have hlint := hint5 (ball x₀ (ε / 2)) 0 (ε / 2) isOpen_ball
    have htop : ∫⁻ t in Ioo 0 (ε / 2), ((A t).boundary - B t).massOn (ball x₀ (ε / 2)) = ∞ := by
      rw [setLIntegral_congr_fun measurableSet_Ioo (fun t ht => top_le_iff.mp (hcon t ht))]
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
      exact ENNReal.top_mul (by simpa using hr₀pos)
    rw [htop, ENNReal.coe_one, one_mul] at hlint
    have hle : R₀.measure (ball x₀ (ε / 2) ∩ {x | 0 < dist x x₀ ∧ dist x x₀ < ε / 2}) < ∞ :=
      lt_of_le_of_lt (measure_mono (inter_subset_left.trans ball_subset_closedBall)) hfinball
    exact absurd (lt_of_le_of_lt hlint hle) (lt_irrefl _)
  -- Step 6: `Z = ∂A_r − B_r` vanishes off the compact sphere `{f = r} ⊆ G`, so `M(Z) ≤ M_G(Z)`
  set Z := (A r).boundary - B r with hZ
  have hZvan : ∀ η : TestFormOn U d,
      Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) → Z η = 0 := by
    intro η hη
    have := hAB r η hη
    change (A r).boundary η - B r η = 0
    rw [this, sub_self]
  have hsph : sphere x₀ r ⊆ ball x₀ (ε / 2) := fun y hy => by
    rw [mem_sphere] at hy; rw [mem_ball, hy]; exact hr.2
  have hZU : Z.massOn U < ∞ :=
    lt_of_le_of_lt (Submission.lcmp_massOn_le_of_vanish_off_compact P d U (ball x₀ (ε / 2))
      (sphere x₀ r) Z (isCompact_sphere _ _) isOpen_ball hsph hZvan U) hZr
  -- Step 7: `M(B_r) ≤ μ'(B_r(x₀)) < ∞`
  have hBU : (B r).massOn U < ∞ := by
    refine lt_of_le_of_lt (hmassle (B r) (μ'.restrict (ball x₀ r)) ξ'
      (ae_restrict_of_ae (Eventually.of_forall hξ'b)) (fun η => hB r η) U) ?_
    refine lt_of_le_of_lt ?_ hfinball'
    calc μ'.restrict (ball x₀ r) U ≤ μ'.restrict (ball x₀ r) univ := measure_mono (subset_univ _)
      _ = μ' (ball x₀ r) := Measure.restrict_apply_univ _
      _ ≤ μ' (closedBall x₀ (ε / 2)) :=
          measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le))
  -- Step 8: `M(∂A_r) ≤ M(B_r) + M(Z) < ∞`
  have hAbU : (A r).boundary.massOn U < ∞ := by
    refine lt_of_le_of_lt (b := (B r).massOn U + Z.massOn U) ?_ (ENNReal.add_lt_top.mpr ⟨hBU, hZU⟩)
    apply sSup_le
    rintro _ ⟨η, hη, rfl⟩
    have hsplit : (A r).boundary η = B r η + Z η := by
      change (A r).boundary η = B r η + ((A r).boundary η - B r η); ring
    change ENNReal.ofReal ((A r).boundary η) ≤ _
    rw [hsplit]
    exact ENNReal.ofReal_add_le.trans (add_le_add ((B r).le_massOn hη) (Z.le_massOn hη))
  -- Step 9: `R' = A_r` is represented by the IMRep `(M ∩ B_r(x₀), θ, ξ)` given by (IMC)(b)
  obtain ⟨A', Rr, -, hcar, hmult, hor⟩ := hIMCb P (d + 1) U R₀ (ball x₀ r) hU measurableSet_ball
  have hRrA : Rr.Represents (A r) := by
    intro ω
    rw [hA r ω]
    exact ((hrestr (ball x₀ r) Rr measurableSet_ball hcar hmult hor).2 _).symm
  -- Step 10: `M(A_r) ≤ μ(B_r(x₀)) < ∞`
  have hAU : (A r).massOn U < ∞ := by
    refine lt_of_le_of_lt (hmassle (A r) (R₀.measure.restrict (ball x₀ r)) R₀.orient
      (ae_restrict_of_ae hξb) (fun ω => hA r ω) U) ?_
    refine lt_of_le_of_lt ?_ hfinball
    calc R₀.measure.restrict (ball x₀ r) U ≤ R₀.measure.restrict (ball x₀ r) univ :=
          measure_mono (subset_univ _)
      _ = R₀.measure (ball x₀ r) := Measure.restrict_apply_univ _
      _ ≤ R₀.measure (closedBall x₀ (ε / 2)) :=
          measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hr.2.le))
  -- Step 11: `A_r` vanishes on a ball around each `y ∈ U ∖ B̄_r(x₀)`, so `spt A_r ⊆ B̄_r(x₀)`
  have hspt : (A r).support ⊆ closedBall x₀ r := by
    intro y hy
    by_contra hyc
    apply hy.2
    have hopen : IsOpen (U \ closedBall x₀ r) := hU.sdiff isClosed_closedBall
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hopen y ⟨hy.1, hyc⟩
    refine mem_sUnion.mpr ⟨ball y (δ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · exact (isCompact_closedBall y (δ / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hδsub.trans sdiff_subset))
    · intro ω hω
      rw [hA r ω]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hxt : x ∉ tsupport (ω : DifferentialForm (Euclid P) (d + 1)) := by
        intro hxt
        have h1 : x ∈ U \ closedBall x₀ r :=
          hδsub (ball_subset_ball (by linarith) (hω hxt))
        exact h1.2 (ball_subset_closedBall (mem_ball.mpr hx))
      rw [image_eq_zero_of_notMem_tsupport hxt, map_zero]
  -- Steps 12–13: for `spt η ⊆ B_r(x₀)`, `∂A_r(η) = B_r(η) = ∫ ⟨η, ξ'⟩ dμ' = ∂R(η)`
  refine ⟨r, hr.1, (closedBall_subset_closedBall hr.2.le).trans hcb₀, A r, ⟨Rr, hRrA⟩, hspt,
    hAU, hAbU, ?_⟩
  intro η hη
  have hdisj : Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) := by
    refine Set.disjoint_left.mpr fun y hy hys => ?_
    have h1 := hη hy
    rw [mem_ball] at h1; rw [mem_sphere] at hys
    linarith
  rw [hAB r η hdisj, hB r η, hbrep η]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have : (η : DifferentialForm (Euclid P) d) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hη h))
  rw [this, map_zero]
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
/-- **Integrability and zeroth-order bound of the pairing `∫_E ⟨ω, ξ⟩ dμ`** (Simon 6.2.4–6.2.5,
`μ⌞E ∧ ξ` as a current; used for restrictions of currents in the slicing argument of 7.2.4).
If `|⟨α, ξ(x)⟩| ≤ |α|` for every `n`-covector `α` and `μ`-a.e. `x`, and the continuous form
`ω` vanishes off a measurable `K` with `μ(K) < ∞` and `|ω| ≤ ε`, then `|ξ(ω)| ≤ ε 1_K`
`μ`-a.e., so `ξ(ω)` is `μ⌞E`-integrable and `|∫_E ξ(ω) dμ| ≤ ε μ(K ∩ E) ≤ ε μ(K)`. -/
theorem Submission.cmcs_rc_pairing_integrable_abs_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E K : Set (Euclid P)) (ω : DifferentialForm (Euclid P) n) (ε : ℝ), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Continuous ω → MeasurableSet K → μ K < ∞ → (∀ x, x ∉ K → ω x = 0) → (∀ x, covectorEuclideanNorm (ω x) ≤ ε) → Integrable (fun x => ξ x (ω x)) (μ.restrict E) ∧ |∫ x in E, ξ x (ω x) ∂μ| ≤ ε * (μ K).toReal := by
  intro P n μ ξ E K ω ε hξm hξb hω hK hμK hzero hε
  -- Step 1: `ε ≥ 0`
  have hε0 : 0 ≤ ε := (covectorEuclideanNorm_nonneg _).trans (hε 0)
  -- Step 2: `F x = ξ x (ω x)` is a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => ξ x (ω x)) μ :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n)
      (F := ℝ)).continuous.comp_aestronglyMeasurable₂ (g := fun Λ α => Λ α) hξm
      hω.aestronglyMeasurable
  -- Step 3: `‖F x‖ ≤ K.indicator ε x` a.e.
  have hbd : ∀ᵐ x ∂μ, ‖ξ x (ω x)‖ ≤ K.indicator (fun _ => ε) x := by
    filter_upwards [hξb] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs]
      exact (hx (ω x)).trans (hε x)
    · rw [indicator_of_notMem hxK, hzero x hxK, map_zero, norm_zero]
  -- Step 4: the dominating function is integrable
  have hg : Integrable (K.indicator (fun _ => ε)) μ :=
    (integrableOn_const hμK.ne).integrable_indicator hK
  -- Step 5: integrability of `F`, then on `μ.restrict E`
  have hint : Integrable (fun x => ξ x (ω x)) μ := hg.mono' hmeas hbd
  refine ⟨hint.restrict, ?_⟩
  -- Step 6: `‖∫_E F‖ ≤ ∫_E g = ν.real K * ε`
  have h1 : ‖∫ x in E, ξ x (ω x) ∂μ‖ ≤ ∫ x in E, K.indicator (fun _ => ε) x ∂μ :=
    norm_integral_le_of_norm_le hg.restrict (ae_restrict_of_ae hbd)
  rw [integral_indicator_const ε hK, smul_eq_mul] at h1
  -- Step 7: `ν K = μ (K ∩ E) ≤ μ K`, multiply by `ε ≥ 0`
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hε0
  rw [measureReal_def, Measure.restrict_apply hK]
  exact ENNReal.toReal_mono hμK.ne (measure_mono inter_subset_left)
/-- **A linear functional on `𝒟ⁿ(U)` with zeroth-order bounds is a current** (Simon 6.2.1; used
for the restricted currents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` in the slicing argument behind 7.2.4).  Suppose
every compact `K ⊆ U` has a `c` with `|L(ω)| ≤ c M` whenever `spt ω ⊆ K` and `‖ω(x)‖ ≤ M` for all
`x`.  Take `S = L`.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K ⊆ U`, the order-`0`
part of the uniform convergence on `K` gives `‖ωⱼ(x)‖ ≤ η` for large `j`.  Off `K` this holds
because `ωⱼ(x) = 0`.  With `η = δ / (|c| + 1)`, `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`. -/
theorem Submission.cmcs_rc_order_zero_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ (ω : TestFormOn U n) (M : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) → |L ω| ≤ c * M) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = L ω := by
  intro P n U L hL
  -- Step 1: `S = ⟨L, h⟩`, so `S ω = L ω` and only `L(ωⱼ) → 0` for `ωⱼ → 0` remains
  refine ⟨⟨L, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 2: the common compact support `K ⊆ U` and the constant `c` for `K`
  obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
  obtain ⟨c, hc⟩ := hL K hK hKU
  -- Step 3: order-`0` uniform convergence on `K`, to the zero form
  have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
  have hz : ∀ x, iteratedFDeriv ℝ 0
      ((0 : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 := by
    intro x
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hη : 0 < δ / (|c| + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 _ hη)
  refine ⟨N, fun j hj => ?_⟩
  -- Steps 3–4: `‖ωⱼ(x)‖ ≤ η` on `K` by uniform convergence, and off `K` since `ωⱼ(x) = 0`
  have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ / (|c| + 1) := by
    intro x
    by_cases hx : x ∈ K
    · have h := hN j hj x hx
      rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
      exact h.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
      exact hη.le
  -- Step 5: `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ c * (δ / (|c| + 1)) := hc (ωs j) _ (hsupp j) hsmall
    _ ≤ |c| * (δ / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hη.le
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- **Restriction of a measure-represented current** (Simon Ch. 6, 2.9:
`T ⌞ A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`), for an arbitrary pair `(μ, ξ)` and an arbitrary set `E`: if `μ` is
finite on compact subsets of `U` and `ξ` is `μ`-a.e. strongly measurable with
`|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for `μ`-a.e. `x`, then
`ω ↦ ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` is a current in `U`.  By `rsd_mw_tfa_norm_props`, `|α| ≤ C ‖α‖`.
For `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, `cmcs_rc_pairing_integrable_abs_le` then
gives integrability on `μ ⌞ E` and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`.  The functional is linear
(`integral_add`, `integral_const_mul`), and `cmcs_rc_order_zero_current` turns the order-zero
bound into Simon's sequential continuity. -/
theorem Submission.cmcs_restrict_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
  intro P n U μ ξ E hμK hξm hξb
  -- Step 1: `|α| ≤ C ‖α‖` for every `n`-covector `α`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Steps 2 and 4: for `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, the pairing is
  -- `μ ⌞ E`-integrable and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`
  have hpair : ∀ (ω : TestFormOn U n) (K : Set (Euclid P)) (M : ℝ), IsCompact K → K ⊆ U →
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K →
      (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) →
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) ∧
        |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| ≤ C * M * (μ K).toReal := by
    intro ω K M hK hKU hsupp hM
    exact Submission.cmcs_rc_pairing_integrable_abs_le P n μ ξ E K
      (ω : DifferentialForm (Euclid P) n) (C * M) hξm hξb ω.property.1.1.continuous
      hK.measurableSet (hμK K hK hKU)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h))
      (fun x => (hC _).trans (mul_le_mul_of_nonneg_left (hM x) hC0))
  -- Step 2: every test form is admissible, with `K = tsupport ω` and `M = sup ‖ω‖ < ∞`
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) := by
    intro ω
    obtain ⟨M, hM⟩ := ω.property.1.1.continuous.bounded_above_of_compact_support ω.property.1.2
    exact (hpair ω _ M ω.property.1.2 ω.property.2 subset_rfl hM).1
  -- Step 3: `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` is linear
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω₁) (hint ω₂)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  -- Steps 4 and 5: the order-zero bound with `c_K = C μ(K)` makes `L` a current
  obtain ⟨S, hS⟩ := Submission.cmcs_rc_order_zero_current P n U L fun K hK hKU =>
    ⟨C * (μ K).toReal, fun ω M hsupp hM => by
      calc |L ω| = |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| := rfl
        _ ≤ C * M * (μ K).toReal := (hpair ω K M hK hKU hsupp hM).2
        _ = C * (μ K).toReal * M := by ring⟩
  exact ⟨S, hS⟩
/-- **Level splitting of a test form** (a step in the proof of Simon Ch. 6, 4.8,
`spt ⟨T, f, t₊⟩ ⊆ spt T ∩ {f = t}`).  If `tsupport η` misses the level set `{f = t}` of a
continuous `f`, then `η = η₁ + η₂` with test forms `η₁ = χ η` supported in `{f < t}` and
`η₂ = (1 - χ) η` supported in `{t < f}`.  Here `χ` is a smooth Urysohn function equal to `1` on
`K₋ = tsupport η ∩ {f ≤ t}` and to `0` on `K₊ = tsupport η ∩ {t ≤ f}`; these closed sets are
disjoint, with `K₋ ⊆ {f < t}` and `K₊ ⊆ {t < f}`, because `tsupport η` misses `{f = t}`. -/
theorem Submission.cmcs_ss_testForm_level_split : ∀ (P n : ℕ) (U : Set (Euclid P)) (f : Euclid P → ℝ) (t : ℝ) (η : TestFormOn U n), Continuous f → Disjoint (tsupport (η : DifferentialForm (Euclid P) n)) {x | f x = t} → ∃ η₁ η₂ : TestFormOn U n, η = η₁ + η₂ ∧ tsupport (η₁ : DifferentialForm (Euclid P) n) ⊆ {x | f x < t} ∧ tsupport (η₂ : DifferentialForm (Euclid P) n) ⊆ {x | t < f x} := by
  intro P n U f t η hf hη
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := η.property
  set e : DifferentialForm (Euclid P) n := (η : DifferentialForm (Euclid P) n)
  -- the closed halves `K₋ = K ∩ {f ≤ t}` and `K₊ = K ∩ {t ≤ f}` of `K = tsupport η` are
  -- disjoint, since `K` misses `{f = t}`
  have hKl : IsClosed (tsupport e ∩ {x | f x ≤ t}) :=
    (isClosed_tsupport e).inter (isClosed_le hf continuous_const)
  have hKu : IsClosed (tsupport e ∩ {x | t ≤ f x}) :=
    (isClosed_tsupport e).inter (isClosed_le continuous_const hf)
  have hd : Disjoint (tsupport e ∩ {x | t ≤ f x}) (tsupport e ∩ {x | f x ≤ t}) :=
    Set.disjoint_left.2 fun x hxu hxl => Set.disjoint_left.1 hη hxu.1 (le_antisymm hxl.2 hxu.2)
  -- a smooth `χ` with `χ = 0` on `K₊` and `χ = 1` on `K₋`
  obtain ⟨χ, hχ, -, hχ₀, hχ₁⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hKu hKl hd
  -- `χ η` and `(1 - χ) η` are test forms in `U`, with sum `η`
  have h₁ : (fun x => χ x • e x) ∈ TestFormOn U n :=
    ⟨⟨hχ.smul hsmooth, hcpt.smul_left (f := χ)⟩, (tsupport_smul_subset_right χ e).trans hU⟩
  have h₂ : (fun x => (1 - χ x) • e x) ∈ TestFormOn U n :=
    ⟨⟨(contDiff_const.sub hχ).smul hsmooth, hcpt.smul_left (f := fun x => 1 - χ x)⟩,
      (tsupport_smul_subset_right (fun x => 1 - χ x) e).trans hU⟩
  refine ⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext (funext fun x => ?_), ?_, ?_⟩
  · change e x = χ x • e x + (1 - χ x) • e x
    rw [← add_smul, add_sub_cancel, one_smul]
  · -- `support (χ η) ⊆ K₋`, a closed subset of `{f < t}`
    have hs : support (fun x => χ x • e x) ⊆ tsupport e ∩ {x | f x ≤ t} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show f x ≤ t from le_of_not_ge fun h => ?_⟩
      exact left_ne_zero_of_smul hx ((hχ₀ x).1 ⟨he, h⟩)
    exact (closure_minimal hs hKl).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h
  · -- `support ((1 - χ) η) ⊆ K₊`, a closed subset of `{t < f}`
    have hs : support (fun x => (1 - χ x) • e x) ⊆ tsupport e ∩ {x | t ≤ f x} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show t ≤ f x from le_of_not_ge fun h => left_ne_zero_of_smul hx ?_⟩
      rw [(hχ₁ x).1 ⟨he, h⟩, sub_self]
    exact (closure_minimal hs hKu).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h.symm
/-- Restriction commutes with the boundary on forms supported in the restricting set (Simon 6.4.6,
used for 4.8): let `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`, and let `A = T⌞S`,
`B = (∂T)⌞S` be given by the same integrals over `S`.  Then `∂A(θ) = B(θ)` whenever
`spt θ ⊆ S`.  Off `S` both `θ` and `dθ` vanish (`spt dθ ⊆ spt θ`), so both integrals over `S`
are integrals over `ℝᴾ`, and `∂A(θ) = A(dθ) = T(dθ) = ∂T(θ) = B(θ)`. -/
theorem Submission.cmcs_ss_boundary_eq_of_tsupport_subset : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, tsupport (θ : DifferentialForm (Euclid P) k) ⊆ S → A.boundary θ = B θ := by
  intro P k U T μ μ' ξ ξ' S A B hT hbT hA hB θ hθ
  -- `θ` and `dθ` vanish off `S`, as `spt dθ ⊆ spt θ ⊆ S`
  have hθ0 : ∀ x, x ∉ S → (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hθ h)
  have hdθ0 : ∀ x, x ∉ S → exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      hx (hθ (tsupport_exteriorDerivative_subset _ h))
  -- so, `ξ x` and `ξ' x` being linear, both integrals over `S` are integrals over `ℝᴾ`
  have hAT : ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ =
      ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hdθ0 x hx, map_zero]
  have hBT : ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' =
      ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hθ0 x hx, map_zero]
  -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ = ∫ ⟨dθ, ξ⟩ dμ = T(dθ) = ∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`
  -- `= ∫_S ⟨θ, ξ'⟩ dμ' = B(θ)`
  calc A.boundary θ = A (exteriorDerivativeTestOn U k θ) := GeometricCurrentOn.boundary_apply A θ
    _ = ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hA _
    _ = ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hAT
    _ = T (exteriorDerivativeTestOn U k θ) := (hT (exteriorDerivativeTestOn U k θ)).symm
    _ = T.boundary θ := (GeometricCurrentOn.boundary_apply T θ).symm
    _ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hbT θ
    _ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hBT.symm
    _ = B θ := (hB θ).symm
/-- Simon Ch. 6, 4.6–4.8 (support of the slice `∂(T⌞S) − (∂T)⌞S`, `S = {f < t}`): if
`A(ω) = ∫_S ⟨ω, ξ⟩ dμ` and `B(θ) = ∫_S ⟨θ, ξ'⟩ dμ'`, then `∂A(θ) = A(dθ) = 0` and `B(θ) = 0`
whenever `spt θ` misses `S`, because `θ` and `dθ` (`spt dθ ⊆ spt θ`) vanish on `S`. -/
theorem Submission.cmcs_ss_boundary_vanish_of_disjoint : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, Disjoint (tsupport (θ : DifferentialForm (Euclid P) k)) S → A.boundary θ = 0 ∧ B θ = 0 := by
  intro P k U μ μ' ξ ξ' S A B hA hB θ hθ
  -- `θ` vanishes on `S`, and so does `dθ`, as `tsupport dθ ⊆ tsupport θ`
  have hθS : ∀ x ∈ S, (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hθ.notMem_of_mem_right hx)
  have hdθS : ∀ x ∈ S, exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun hx' =>
      hθ.notMem_of_mem_right hx (tsupport_exteriorDerivative_subset _ hx')
  refine ⟨?_, ?_⟩
  · -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ`
    rw [GeometricCurrentOn.boundary_apply, hA]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    change ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) = 0
    rw [hdθS x hx, map_zero]
  · rw [hB]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [hθS x hx, map_zero]

/-- **Simon Ch. 6, 4.8** (support of a slice): if `T = ξ μ` and `∂T = ξ' μ'` in `U`,
`A = T ⌞ {f < t}` and `B = (∂T) ⌞ {f < t}` (`f` continuous), then `∂A(η) = B(η)` for every
`η ∈ 𝒟ᵏ(U)` whose support misses the level set `{f = t}`; i.e. the slice `∂A − B` lives on
`{f = t}`.  Split `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {f > t}`
(`cmcs_ss_testForm_level_split`).  Below the level `∂A(η₁) = ∂T(η₁) = B(η₁)`
(`cmcs_ss_boundary_eq_of_tsupport_subset`); above it `∂A(η₂) = 0 = B(η₂)`
(`cmcs_ss_boundary_vanish_of_disjoint`), as `{f > t}` misses `{f < t}`.  Conclude by linearity
of `∂A` and `B`. -/
theorem Submission.cmcs_slice_support : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), Continuous f → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ η : TestFormOn U k, Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → A.boundary η = B η := by
  intro P k U T μ μ' ξ ξ' f t A B hf hT hbT hA hB η hη
  -- `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {t < f}`
  obtain ⟨η₁, η₂, rfl, h₁, h₂⟩ := Submission.cmcs_ss_testForm_level_split P k U f t η hf hη
  -- below the level: `∂A(η₁) = ∂T(η₁) = B(η₁)`
  have e₁ : A.boundary η₁ = B η₁ :=
    Submission.cmcs_ss_boundary_eq_of_tsupport_subset P k U T μ μ' ξ ξ' {x | f x < t} A B
      hT hbT hA hB η₁ h₁
  -- above the level: `∂A(η₂) = 0 = B(η₂)`, since `spt η₂ ⊆ {t < f}` misses `{f < t}`
  obtain ⟨e₂, e₂'⟩ := Submission.cmcs_ss_boundary_vanish_of_disjoint P k U μ μ' ξ ξ'
    {x | f x < t} A B hA hB η₂ (Set.disjoint_left.2 fun x hx hx' =>
      lt_asymm (show t < f x from h₂ hx) (show f x < t from hx'))
  -- `∂A` and `B` are linear
  rw [A.boundary.toCurrent.map_add, B.toCurrent.map_add, e₁, e₂, e₂']
/-- Integrability of the pairing `x ↦ ⟨ω(x), ξ(x)⟩`: if `μ` is finite on compact subsets of `U`,
`ξ` is `μ`-a.e. strongly measurable with `|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for
`μ`-a.e. `x`, and `ω ∈ 𝒟ⁿ(U)`, then `x ↦ ⟨ω(x), ξ(x)⟩` is `μ`-integrable.  The coefficient norm
`|ω(x)|` is continuous with compact support, hence bounded by some `M`, so the pairing is
dominated by `M` times the indicator of `spt ω`, which is integrable as `μ(spt ω) < ∞`. -/
theorem Submission.cmcs_smp_pairing_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (ω : TestFormOn U n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ := by
  intro P n U μ ξ ω hμ hξm hξ
  obtain ⟨w, ⟨hws, hwcs⟩, hwU⟩ := ω
  change Integrable (fun x => ξ x (w x)) μ
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous with compact support, hence bounded by some `M`
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  -- `(Λ, α) ↦ Λ α` is continuous, so the pairing is a.e. strongly measurable
  have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hmeas : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    hev.comp_aestronglyMeasurable₂ hξm hwc.aestronglyMeasurable
  -- domination by `M` times the indicator of `spt w`, integrable as `μ(spt w) < ∞`
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport w).measurableSet).2
    (integrableOn_const (hμ _ hwcs hwU).ne)) hmeas ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs]
  by_cases hxK : x ∈ tsupport w
  · rw [indicator_of_mem hxK]
    exact (hx (w x)).trans ((Real.le_norm_self _).trans (hM x))
  · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    simp
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
/-- **Dominated convergence for level cut-offs** (step 5 of the slice mass bound in the proof of
Simon 7.2.4, cut-offs `g_h` of the level set `{f < t}`).  If `F` is `μ`-integrable, `f` is
measurable and, for `0 < h < 1`, `g_h` is a.e. strongly measurable with `|g_h| ≤ C`, `g_h = 1` on
`{f ≤ t − h}` and `g_h = 0` on `{t ≤ f}`, then `∫ g_h F dμ → ∫_{f < t} F dμ` as `h → 0+`.
Along `𝓝[>] 0` eventually `0 < h < 1`, so `|g_h F| ≤ C|F|` (integrable); for each `x`,
`g_h(x)F(x)` is eventually `1_{f<t}(x)F(x)` (for `h < min (t − f x) 1` if `f x < t`, for all
`h ∈ (0, 1)` if `t ≤ f x`); dominated convergence along the countably generated `𝓝[>] 0`. -/
theorem Submission.cmcs_smp_cutoff_integral_tendsto : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F f : Euclid P → ℝ) (t C : ℝ) (g : ℝ → Euclid P → ℝ), Integrable F μ → Measurable f → (∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) μ) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, |g h x| ≤ C) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, f x ≤ t - h → g h x = 1) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, t ≤ f x → g h x = 0) → Tendsto (fun h : ℝ => ∫ x, g h x * F x ∂μ) (𝓝[>] 0) (𝓝 (∫ x in {x | f x < t}, F x ∂μ)) := by
  intro P μ F f t C g hF hf hgm hgC hg1 hg0
  -- Step 2: eventually along `𝓝[>] 0`, `h ∈ (0, 1)`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- Step 1: `{f < t}` is measurable, so the limit is `∫ 1_{f<t} F dμ`
  have hs : MeasurableSet {x | f x < t} := measurableSet_lt hf measurable_const
  rw [← integral_indicator hs]
  -- Step 6: dominated convergence with the integrable bound `C‖F‖`
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖F x‖) ?_ ?_ ?_ ?_
  · -- Step 3: `g_h F` is a.e. strongly measurable for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    exact (hgm h hh.1 hh.2).mul hF.aestronglyMeasurable
  · -- Step 4: `|g_h F| ≤ C|F|` for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hgC h hh.1 hh.2 x) (norm_nonneg _)
  · exact hF.norm.const_mul C
  · -- Step 5: `g_h(x)F(x)` is eventually equal to `1_{f<t}(x)F(x)`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : f x < t
    · rw [indicator_of_mem (show x ∈ {x | f x < t} from hx)]
      have hpos : 0 < min (t - f x) 1 := lt_min (by linarith) one_pos
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with h hh
      obtain ⟨h0, h1⟩ := hh
      have h1' : h < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      have h2 : h < t - f x := lt_of_lt_of_le h1 (min_le_left _ _)
      rw [hg1 h h0 h1' x (by linarith), one_mul]
    · rw [indicator_of_notMem (show x ∉ {x | f x < t} from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with h hh
      rw [hg0 h hh.1 hh.2 x (not_lt.1 hx), zero_mul]
/-- **Simon Ch. 6, 4.9** (end of its proof, p. 158, where `b ↓ a` and then `ε ↓ 0`): if
`Φ(h) → z` as `h ↓ 0` and `|Φ(h)| ≤ L / (h (1 − h/2)) · v(h)` for `0 < h < 1`, then
`z ≤ L · liminf_{h ↓ 0} h⁻¹ v(h)` in `[0, ∞]`.  For `r > 1` eventually `(1 − h/2)⁻¹ < r`, so
`|z| = liminf |Φ(h)| ≤ r · L · liminf h⁻¹ v(h)`; then let `r ↓ 1`. -/
theorem Submission.cmcs_smp_liminf_bound : ∀ (L : NNReal) (z : ℝ) (Φ : ℝ → ℝ) (v : ℝ → ℝ≥0∞), Tendsto Φ (𝓝[>] 0) (𝓝 z) → (∀ h : ℝ, 0 < h → h < 1 → ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h) → ENNReal.ofReal z ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0) := by
  intro L z Φ v hΦ hb
  set X := (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0)
  -- step 1: `(0, 1) ∈ 𝓝[>] 0`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- step 2: `ofReal |Φ h| → ofReal |z|`
  have hlimΦ : Tendsto (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |z|)) :=
    ENNReal.tendsto_ofReal hΦ.abs
  -- step 3: `ofReal z ≤ ofReal r * X` for every `r > 1`
  have key : ∀ r : ℝ, 1 < r → ENNReal.ofReal z ≤ ENNReal.ofReal r * X := by
    intro r hr
    -- 3a: `(1 - h / 2)⁻¹ → 1`, so eventually `(1 - h / 2)⁻¹ < r`
    have hcont : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝 0) (𝓝 (1 - 0 / 2)⁻¹) :=
        (tendsto_const_nhds.sub (tendsto_id.div_const 2)).inv₀ (by norm_num)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hevr : ∀ᶠ h in 𝓝[>] (0 : ℝ), (1 - h / 2)⁻¹ < r := hcont.eventually (gt_mem_nhds hr)
    calc ENNReal.ofReal z ≤ ENNReal.ofReal |z| := ENNReal.ofReal_le_ofReal (le_abs_self z)
      _ = liminf (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) := hlimΦ.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)))
            (𝓝[>] 0) := by
          -- 3b, 3c: the eventual pointwise bound and monotonicity of `liminf`
          refine liminf_le_liminf ?_
          filter_upwards [hev, hevr] with h ⟨h0, h1⟩ hhr
          have h2 : 0 < 1 - h / 2 := by linarith
          have heq : (L : ℝ) / (h * (1 - h / 2)) = (1 - h / 2)⁻¹ * ((L : ℝ) * h⁻¹) := by
            field_simp
          calc ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h :=
                hb h h0 h1
            _ = ENNReal.ofReal (1 - h / 2)⁻¹ * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                rw [heq, ENNReal.ofReal_mul (inv_nonneg.2 h2.le),
                  ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]
                ring
            _ ≤ ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                gcongr
      _ = ENNReal.ofReal r * X := by
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  -- step 4: let `r ↓ 1`
  by_cases hXtop : X = ⊤
  · rw [hXtop]
    exact le_top
  · have htend : Tendsto (fun r : ℝ => ENNReal.ofReal r * X) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal 1 * X)) :=
      ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_ofReal tendsto_id).mono_left nhdsWithin_le_nhds) (Or.inr hXtop)
    simpa using ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun r hr => key r hr)
/-- Strip estimate (Simon Ch. 6, 4.11: the bound for the right side `R` of 4.11): if `‖Dg‖ ≤ c`,
`Dg` vanishes off `S`, `spt η ⊆ W` and `|η| ≤ 1`, then `∫⁻ ‖Dg‖ |η| dμ ≤ c μ(W ∩ S)`.  The
integrand is dominated by `c 𝟙_{W ∩ S}`: on `W \ S` it vanishes because `Dg = 0`, off `W` because
`η = 0`.  No measurability is needed, as `∫⁻ c 𝟙_A dμ ≤ c μ(A)` for every set `A`. -/
theorem Submission.cmcs_smp_strip_lintegral_le : ∀ (P k : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (W S : Set (Euclid P)) (c : ℝ), (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → tsupport η ⊆ W → (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ∂μ ≤ ENNReal.ofReal c * μ (W ∩ S) := by
  intro P k μ g η W S c hc hS hW hη
  -- the integrand is dominated by the indicator of `W ∩ S` with value `ofReal c`
  refine le_trans (lintegral_mono fun x => ?_)
    (lintegral_indicator_const_le (W ∩ S) (ENNReal.ofReal c))
  show ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ≤
    (W ∩ S).indicator (fun _ => ENNReal.ofReal c) x
  by_cases hx : x ∈ W ∩ S
  · rw [indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal
      ((mul_le_of_le_one_right (norm_nonneg _) (hη x)).trans (hc x))
  · rw [indicator_of_notMem hx]
    -- off `W ∩ S` a factor vanishes: `Dg(x) = 0` on `W \ S` and `η(x) = 0` off `W`
    have h0 : ‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x) = 0 := by
      by_cases hxW : x ∈ W
      · obtain hD | hD := eq_or_ne (fderiv ℝ g x) 0
        · rw [hD, norm_zero, zero_mul]
        · exact absurd ⟨hxW, hS x hD⟩ hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxW (hW h)
        rw [hηx, covectorEuclideanNorm_zero, mul_zero]
    rw [h0, ENNReal.ofReal_zero]
/-- **Simon 6.4.11** (Leibniz rule behind the cutoff identity
`T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω)`): if `g` and the `k`-form `η` are differentiable
at `x`, then `d(gη)(x) = g(x) dη(x) + dg(x) ∧ η(x)`, where `dg(x) ∧ η(x)` is the alternation of
`v ↦ Dg(x)(v) η(x)`.  Unfold `d = extDeriv = alternatizeUncurryFin ∘ fderiv`, apply the product
rule `fderiv_fun_smul`, and use additivity and `ℝ`-homogeneity of `alternatizeUncurryFin`. -/
theorem Submission.cmcs_cd_extDeriv_smul_leibniz : ∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)) := by
  intro P k g η x hg hη
  -- `d θ x = alternatizeUncurryFin (fderiv ℝ θ x)` by definition
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => g y • η y) x) =
    g x • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) +
      ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))
  -- product rule, then linearity of the alternation
  rw [fderiv_fun_smul hg hη, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- **Simon Ch. 6, 4.11** (the multiplier step behind `T(γ∘f dω)` and `T(d(γ∘f ω))`): test forms
in `U` are closed under multiplication by `C^∞` functions.  For `ω ∈ 𝒟ⁿ(U)` and `g ∈ C^∞`, the
form `gω` is `C^∞`; it vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω ⊆ U`, and `spt(gω)` is
compact as a closed subset of the compact set `spt ω`.  Neither openness of `U` nor compact
support of `g` is needed. -/
theorem Submission.cmcs_cd_smul_mem_testFormOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (ω : TestFormOn U n), ContDiff ℝ (⊤ : ℕ∞) g → (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n := by
  intro P n U g ω hg
  -- `ω ∈ 𝒟ⁿ(U)`: `ω` is `C^∞`, `spt ω` is compact and `spt ω ⊆ U`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := hω.1.1
  have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
  -- `gω` vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω`
  have hsub : tsupport (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ⊆
      tsupport (ω : DifferentialForm (Euclid P) n) :=
    tsupport_smul_subset_right (fun x => g x) _
  -- `spt(gω)` is a closed subset of the compact set `spt ω`
  have hcpt : IsCompact (tsupport fun x => g x • (ω : DifferentialForm (Euclid P) n) x) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
  exact ⟨⟨hg.smul hsmooth, hcpt⟩, hsub.trans hω.2⟩

/-- **Simon 6.4.11, the cut-off defect identity**, with a smooth `g` in place of `γ ∘ f` and with
`T`, `∂T` written through integral representations `T = ξ μ`, `∂T = ξ' μ'`: for `g ∈ C^∞` and
`η ∈ 𝒟^k(U)`, `T(g dη) − ∂T(gη) = −T(dg ∧ η)`, where
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`.  The forms `gη` and `g dη` are test forms by
`cmcs_cd_smul_mem_testFormOn`, and `d(gη) − g dη = dg ∧ η` pointwise by the Leibniz rule
`cmcs_cd_extDeriv_smul_leibniz`.  Every equality of integrals is a representation hypothesis or
`integral_congr_ae` for a pointwise identity, so no integrability is needed. -/
theorem Submission.cmcs_cd_defect_identity : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hT hbT hg
  -- Step 1: the test forms `dη`, `gη`, `g dη` and `d(gη)`
  let dη : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k η
  let ηg : TestFormOn U k :=
    ⟨fun x => g x • (η : DifferentialForm (Euclid P) k) x,
      Submission.cmcs_cd_smul_mem_testFormOn P k U g η hg⟩
  let ωg : TestFormOn U (k + 1) :=
    ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k + 1)) x,
      Submission.cmcs_cd_smul_mem_testFormOn P (k + 1) U g dη hg⟩
  let dηg : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k ηg
  -- Step 2: the first integral is `T(g dη)`
  have h1 : ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ =
      T ωg := by
    rw [hT ωg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) =
      ξ x (g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 3: the second integral is `∂T(gη) = T(d(gη))`
  have h2 : ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = T dηg := by
    rw [show T dηg = T.boundary ηg from (GeometricCurrentOn.boundary_apply T ηg).symm, hbT ηg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) =
      ξ' x (g x • (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 4: pointwise, `d(gη) − g dη = dg ∧ η` by the Leibniz rule
  have h3 : ∀ x, ((dηg - ωg : TestFormOn U (k + 1)) : DifferentialForm (Euclid P) (k + 1)) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x)) := by
    intro x
    have hgx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    have hηx : DifferentiableAt ℝ (η : DifferentialForm (Euclid P) k) x :=
      η.property.1.1.differentiable (by simp) x
    change exteriorDerivative (fun y => g y • (η : DifferentialForm (Euclid P) k) y) x -
      g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x = _
    rw [Submission.cmcs_cd_extDeriv_smul_leibniz P k g _ x hgx hηx]
    abel
  -- Step 5: linearity of `T`
  have h4 : T ωg - T dηg = -T (dηg - ωg) := by
    have hsub := LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) dηg ωg
    change T.toCurrent ωg - T.toCurrent dηg = -T.toCurrent (dηg - ωg)
    rw [hsub]
    ring
  -- Steps 6 and 7: `T(d(gη) − g dη)` as an integral
  rw [h1, h2, h4, hT]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (ξ x) (h3 x))
/-- **Orthonormal basis adapted to a linear functional** (used for the wedge-norm bound
`|β ∧ γ| ≤ ‖β‖ |γ|`, Simon 6.1): for a continuous linear functional `β` on `ℝᴾ` and `i₀ : Fin P`
there is an orthonormal basis `f` of `ℝᴾ` with `β(f_{i₀}) = ‖β‖` and `β(f_i) = 0` for `i ≠ i₀`.
Write `β = ⟨b, ·⟩` (Riesz, `‖b‖ = ‖β‖`).  If `b = 0`, the standard basis `e` works.  Otherwise the
reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ`, `u = ‖b‖⁻¹ b`, maps `e_{i₀}` to `u`, and `f = R ∘ e` has
`β(f_i) = ‖b‖ ⟨R e_{i₀}, R e_i⟩ = ‖b‖ ⟨e_{i₀}, e_i⟩`. -/
theorem Submission.cmcs_wn_adapted_orthonormalBasis : ∀ (P : ℕ) (β : Euclid P →L[ℝ] ℝ) (i₀ : Fin P), ∃ f : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, β (f i) = if i = i₀ then ‖β‖ else 0 := by
  intro P β i₀
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Riesz representative: `β x = ⟪b, x⟫` and `‖b‖ = ‖β‖`
  set b : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm β with hb
  have hβb : ∀ x, β x = inner ℝ b x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hnorm : ‖b‖ = ‖β‖ := by
    rw [hb, LinearIsometryEquiv.norm_map]
  by_cases hb0 : b = 0
  · -- `β = 0`: the standard basis works
    refine ⟨e, fun i => ?_⟩
    have h0 : ‖β‖ = 0 := by rw [← hnorm, hb0, norm_zero]
    rw [hβb, hb0, inner_zero_left, h0, ite_self]
  · -- `u = ‖b‖⁻¹ b` is a unit vector and `b = ‖b‖ u`
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    set u : Euclid P := ‖b‖⁻¹ • b with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbpos.ne']
    have hbu : b = ‖b‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
    -- the reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ` maps `e_{i₀}` to `u`
    have he : ‖e i₀‖ = 1 := e.orthonormal.1 i₀
    set R := (ℝ ∙ (e i₀ - u))ᗮ.reflection
    have hR : R (e i₀) = u := Submodule.reflection_sub (he.trans hu.symm)
    -- `f = R ∘ e`: `β(f_i) = ‖b‖ ⟪R e_{i₀}, R e_i⟫ = ‖β‖ ⟪e_{i₀}, e_i⟫`
    refine ⟨e.map R, fun i => ?_⟩
    rw [OrthonormalBasis.map_apply, hβb, hbu, real_inner_smul_left, ← hR,
      LinearIsometryEquiv.inner_map_map, hnorm, orthonormal_iff_ite.mp e.orthonormal i₀ i]
    by_cases hi : i = i₀
    · rw [ite_eq_left hi.symm, ite_eq_left hi, mul_one]
    · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi, mul_zero]
/-- **`β ∧ γ` on tuples of a family adapted to `β`** (Simon 6.1.1–1.3; step 4 of the proof of
`|β ∧ γ| ≤ ‖β‖ |γ|`): if `β(v_a) = c` for `a = i₀` and `β(v_a) = 0` otherwise, then for every
`j : Fin (k + 1) → Fin P`, `(β ∧ γ)(v_{j(0)}, …, v_{j(k)})² ≤ c² Σ_{i, j(i) = i₀} γ(v ∘ ĵᵢ)²`,
where `ĵᵢ = i.removeNth j` deletes the `i`-th entry of `j`.  By definition
`(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`.  A repeated index in `j` makes `v ∘ j`
non-injective, so the left side vanishes (alternation); otherwise at most one `i₁` has
`j(i₁) = i₀`, only `i₁` contributes to either side, and `((−1)^{i₁})² = 1`. -/
theorem Submission.cmcs_wn_tuple_sq_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k) (v : Fin P → Euclid P) (i₀ : Fin P) (c : ℝ), Function.Injective v → (∀ i : Fin P, β (v i) = if i = i₀ then c else 0) → ∀ j : Fin (k + 1) → Fin P, (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ) (fun m => v (j m))) ^ 2 ≤ c ^ 2 * ∑ i : Fin (k + 1), if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0 := by
  intro P k β γ v i₀ c _hv hβ j
  classical
  -- the right side is `c²` times a sum of squares and zeros
  have hRHS : 0 ≤ c ^ 2 * ∑ i : Fin (k + 1),
      (if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0) :=
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  by_cases hj : Injective j
  · -- `(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`, with `β(v_{j(i)}) = c [j(i) = i₀]`
    have hexp : ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
        (fun m => v (j m)) = ∑ i : Fin (k + 1),
          (-1 : ℝ) ^ (i : ℕ) *
            ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smulRight_apply, hβ (j i)]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rfl
    rw [hexp]
    by_cases hex : ∃ i₁, j i₁ = i₀
    · -- `j` is injective, so `i₁` is the only index with `j(i₁) = i₀`
      obtain ⟨i₁, hi₁⟩ := hex
      have huniq : ∀ i, i ≠ i₁ → j i ≠ i₀ := fun i hi h => hi (hj (h.trans hi₁.symm))
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by rw [ite_eq_right (huniq i hi)]; ring)
          (fun h => absurd (Finset.mem_univ i₁) h),
        Finset.sum_eq_single i₁ (fun i _ hi => ite_eq_right (huniq i hi))
          (fun h => absurd (Finset.mem_univ i₁) h),
        ite_eq_left hi₁, ite_eq_left hi₁]
      have hsign : ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      refine le_of_eq ?_
      calc ((-1 : ℝ) ^ (i₁ : ℕ) * (c * γ (fun m => v (i₁.removeNth j m)))) ^ 2
          = ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 * (c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2) := by
            ring
        _ = c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2 := by rw [hsign, one_mul]
    · -- no index hits `i₀`: every term vanishes
      have h0 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
          ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [ite_eq_right fun h => hex ⟨i, h⟩]; ring
      rw [h0]
      simpa using hRHS
  · -- a repeated index makes `v ∘ j` non-injective, and `β ∧ γ` is alternating
    have hvj : ¬ Injective (fun m => v (j m)) := fun h => hj (Injective.of_comp (f := v) h)
    rw [ContinuousAlternatingMap.map_eq_zero_of_not_injective _ _ hvj]
    simpa using hRHS
/-- **Fibres of `j ↦ removeNth i j`** (the counting step of the bound `|β ∧ γ| ≤ ‖β‖ |γ|` for the
Euclidean norm of covectors, Simon Ch. 6, 1.1–1.3, 1.15): for `i₀ : Fin P` and
`F : (Fin k → Fin P) → ℝ`,
`Σ_{j : Fin (k+1) → Fin P} Σ_i [j i = i₀] F(removeNth i j) = (k + 1) Σ_{j' : Fin k → Fin P} F j'`.
For fixed `i`, `j ↦ (j i, removeNth i j)` is a bijection onto `Fin P × (Fin k → Fin P)`
(`Fin.insertNthEquiv`), so only `j i = i₀` survives and each of the `k + 1` indices `i`
contributes `Σ_{j'} F j'`. -/
theorem Submission.cmcs_wn_removeNth_fiber_sum : ∀ (k P : ℕ) (i₀ : Fin P) (F : (Fin k → Fin P) → ℝ), ∑ j : Fin (k + 1) → Fin P, ∑ i : Fin (k + 1), (if j i = i₀ then F (i.removeNth j) else 0) = ((k : ℝ) + 1) * ∑ j' : Fin k → Fin P, F j' := by
  intro k P i₀ F
  rw [Finset.sum_comm]
  -- for fixed `i`, reindex along `j ↦ (j i, removeNth i j)`; only `j i = i₀` survives
  have hfib : ∀ i : Fin (k + 1),
      ∑ j : Fin (k + 1) → Fin P, (if j i = i₀ then F (i.removeNth j) else 0) =
        ∑ j' : Fin k → Fin P, F j' := by
    intro i
    rw [Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Fin P) i).symm
      (fun j => if j i = i₀ then F (i.removeNth j) else 0)
      (fun p => if p.1 = i₀ then F p.2 else 0) fun _ => rfl,
      Fintype.sum_prod_type, Fintype.sum_eq_single i₀]
    · simp
    · intro x hx
      simp [hx]
  -- each of the `k + 1` indices `i` contributes `Σ_{j'} F j'`
  rw [Finset.sum_congr rfl fun i _ => hfib i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add_one]
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

/-- **`|β ∧ γ| ≤ ‖β‖ |γ|`** (Simon 6.1.1–1.3 and 1.15): for a linear functional `β` and a
`k`-covector `γ` on `ℝᴾ`, the Euclidean coefficient norm of the `(k+1)`-covector
`β ∧ γ = alternatizeUncurryFin (β.smulRight γ)` is at most `‖β‖ |γ|`.  Take an orthonormal basis
`f` with `β(fᵢ) = ‖β‖ [i = i₀]`; then `(β ∧ γ)(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²`.
Summing over `j`, each `j' : Fin k → Fin P` arises as `i.removeNth j` with `j i = i₀` for exactly
`k + 1` pairs `(i, j)`, so `(k+1)! |β ∧ γ|² ≤ ‖β‖² (k+1) k! |γ|²` by
`regcomp_covector_sq_sum_orthonormalBasis` in degrees `k + 1` and `k`.  For `P = 0` there are no
coordinate tuples and `|β ∧ γ| = 0`. -/
theorem Submission.cmcs_wedge_norm_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k), covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)) ≤ ‖β‖ * covectorEuclideanNorm γ := by
  intro P k β γ
  classical
  set ω := ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
  have hrhs : 0 ≤ ‖β‖ * covectorEuclideanNorm γ :=
    mul_nonneg (norm_nonneg β) (covectorEuclideanNorm_nonneg γ)
  rcases Nat.eq_zero_or_pos P with hP | hP
  · -- `P = 0`: there is no tuple `Fin (k + 1) → Fin 0`, so `|ω| = 0`
    subst hP
    have h0 : covectorEuclideanNorm ω = 0 := by
      simp [covectorEuclideanNorm]
    rw [h0]
    exact hrhs
  · -- an orthonormal basis `f` with `β(fᵢ) = ‖β‖ [i = i₀]`
    set i₀ : Fin P := ⟨0, hP⟩
    obtain ⟨f, hf⟩ := Submission.cmcs_wn_adapted_orthonormalBasis P β i₀
    -- `ω(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²` for every `j`
    have hle : ∑ j : Fin (k + 1) → Fin P, (ω (fun m => f (j m))) ^ 2 ≤
        ∑ j : Fin (k + 1) → Fin P, ‖β‖ ^ 2 * ∑ i : Fin (k + 1),
          (if j i = i₀ then (γ (fun m => f (i.removeNth j m))) ^ 2 else 0) :=
      Finset.sum_le_sum fun j _ => Submission.cmcs_wn_tuple_sq_le P k β γ f i₀ ‖β‖
        f.orthonormal.linearIndependent.injective hf j
    -- count the fibres of `j ↦ i.removeNth j`, then `Σ_j α(f ∘ j)² = m! |α|²` for `m = k + 1, k`
    rw [← Finset.mul_sum,
      Submission.cmcs_wn_removeNth_fiber_sum k P i₀ (fun j' => (γ (fun m => f (j' m))) ^ 2),
      Submission.regcomp_covector_sq_sum_orthonormalBasis P (k + 1) ω f,
      Submission.regcomp_covector_sq_sum_orthonormalBasis P k γ f] at hle
    -- cancel `(k+1)! = (k+1) k! > 0`
    have hpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hsq : covectorEuclideanNorm ω ^ 2 ≤ (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hpos
      calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm ω ^ 2
          ≤ ‖β‖ ^ 2 * (((k : ℝ) + 1) * ((k.factorial : ℝ) * covectorEuclideanNorm γ ^ 2)) := hle
        _ = ((k + 1).factorial : ℝ) * (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
          push_cast [Nat.factorial_succ]
          ring
    exact (sq_le_sq₀ (covectorEuclideanNorm_nonneg ω) hrhs).mp hsq

/-- **Simon Ch. 6, 4.11 (p. 158), the estimate of the cutoff defect**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')` with `|⟨α, ξ⟩| ≤ |α|` `μ`-a.e.: for a `C^∞` function `g`
and `η ∈ 𝒟ᵏ(U)`, `|∫ g ⟨dη, ξ⟩ dμ − ∫ g ⟨η, ξ'⟩ dμ'| ≤ ∫ |Dg| |η| dμ` in `[0, ∞]`.  The left side
is `|T(g dη) − ∂T(gη)| = |T(dg ∧ η)| = |∫ ⟨dg ∧ η, ξ⟩ dμ|` (`cmcs_cd_defect_identity`, with
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`), which is at most `∫ |⟨dg ∧ η, ξ⟩| dμ` whether
or not the integrand is integrable; and `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|` `μ`-a.e. by the bound
on `ξ` and `cmcs_wedge_norm_le`. -/
theorem Submission.cmcs_cutoff_defect_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ENNReal.ofReal |∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ'| ≤ ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm ((η : DifferentialForm (Euclid P) k) x)) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hξ hT hbT hg
  -- Simon 4.11: `T(g dη) − ∂T(gη) = −T(dg ∧ η) = −∫ ⟨dg ∧ η, ξ⟩ dμ`
  rw [Submission.cmcs_cd_defect_identity P k U T μ μ' ξ ξ' g η hT hbT hg, abs_neg,
    ← Real.enorm_eq_ofReal_abs]
  -- `‖∫ G dμ‖ₑ ≤ ∫⁻ ‖G‖ₑ dμ` for every `G`, integrable or not; then bound `G` `μ`-a.e.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hξ] with x hx
  -- `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|`
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((hx _).trans (Submission.cmcs_wedge_norm_le P k _ _))
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]

/-- **Smoothing of Lipschitz functions** (Simon Ch. 6, 4.8–4.9: use `f^{(σ)}` in place of a
Lipschitz `f`): a `K`-Lipschitz `g` on `ℝᴾ` and `σ > 0` give a `C^∞` function `g'` with
`‖Dg'‖ ≤ K`, `|g' − g| ≤ Kσ`, and `g'(x) = c` whenever `g ≡ c` on `B_σ(x)`.  Take the normalized
mollifier `ψ` (`support ψ ⊆ B_σ(0)`) and `g' = ψ ⋆ g`, `g'(x) = ∫ ψ(y) g(x − y) dy`: it is `C^∞`
(`ψ` is smooth with compact support, `g` is continuous) and `K`-Lipschitz, so `‖Dg'‖ ≤ K`.  The
last two claims are `dist_convolution_le` on `B_σ(x)`, with `ε = Kσ`, `z₀ = g(x)` and with
`ε = 0`, `z₀ = c`.  (`ContDiffBump.normed` and its convolution lemmas are outside the import
closure.) -/
theorem Submission.cmcs_lipschitz_smoothing : ∀ (P : ℕ) (g : Euclid P → ℝ) (K : NNReal) (σ : ℝ), LipschitzWith K g → 0 < σ → ∃ g' : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g' ∧ (∀ x, ‖fderiv ℝ g' x‖ ≤ K) ∧ (∀ x, |g' x - g x| ≤ K * σ) ∧ ∀ (x : Euclid P) (c : ℝ), (∀ y ∈ ball x σ, g y = c) → g' x = c := by
  intro P g K σ hg hσ
  obtain ⟨ψ, hψd, hψs, hψ0, hψ1, hψb⟩ := Submission.dgcr_stc_exists_normalized_mollifier P σ hσ
  -- `g' = ψ ⋆ g`
  have hconv : (fun x => ∫ y, ψ y * g (x - y)) =
      convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine ⟨fun x => ∫ y, ψ y * g (x - y), ?_, fun x => ?_, fun x => ?_, fun x c hc => ?_⟩
  · rw [hconv]
    exact hψs.contDiff_convolution_left _ hψd hg.continuous.locallyIntegrable
  · exact norm_fderiv_le_of_lipschitz ℝ
      (Submission.cmcs_ls_mollify_lipschitz P ψ g K hψd.continuous hψs hψ0 hψ1 hg)
  · -- `dist (g y) (g x) ≤ K ‖y − x‖ ≤ Kσ` on `B_σ(x)`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (mul_nonneg K.coe_nonneg hσ.le) hψb hψ0 hψ1 hg.continuous.aestronglyMeasurable
      (fun y hy => (hg.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg))
    rwa [← hconv, Real.dist_eq] at h
  · -- `g ≡ c` on `B_σ(x)`, so `dist (g' x) c ≤ 0`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := c) le_rfl hψb hψ0 hψ1
      hg.continuous.aestronglyMeasurable (fun y hy => by rw [hc y hy, dist_self])
    rw [← hconv] at h
    exact dist_le_zero.1 h

/-- **Smooth cut-off between two levels of a Lipschitz function** (Simon Ch. 6, proof of 4.9, with
`f^{(σ)}` in place of `f`).  If `f : ℝᴾ → ℝ` is `L`-Lipschitz, `t ∈ ℝ` and `0 < h < 1`, there is a
`C^∞` function `g` with `|g| ≤ 2`, `‖Dg‖ ≤ L/(h(1 − h/2))`, `g = 1` on `{f ≤ t − h}`, `g = 0` on
`{f ≥ t}` and `Dg = 0` off the strip `{t − h < f < t}`.  With `δ = h²/4` and
`w = h − 2δ = h(1 − h/2)`, the clamp `G = max 0 (min 1 ((t − δ − f)/w))` is `(L/w)`-Lipschitz,
`G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`; `g` is its smoothing at scale
`σ = δ/(2(L + 1))` (`cmcs_lipschitz_smoothing`), so `|g − G| ≤ Lσ/w ≤ 1`.  As `2Lσ < δ`, `G` is
constant on `B_{2σ}(x)` when `f x ≤ t − h` or `t ≤ f x`; by locality `g` is then constant on
`B_σ(x)`, so `Dg(x) = 0`. -/
theorem Submission.cmcs_level_cutoff : ∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (t h : ℝ), LipschitzWith L f → 0 < h → h < 1 → ∃ g : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧ (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧ (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
  intro P f L t h hf h0 h1
  -- parameters `δ = h²/4`, `w = h − 2δ = h(1 − h/2)` and `σ = δ/(2(L + 1))`, so `2Lσ < δ`
  set δ : ℝ := h ^ 2 / 4 with hδ
  set w : ℝ := h * (1 - h / 2) with hw
  have hw0 : 0 < w := mul_pos h0 (by linarith)
  have hδ0 : 0 < δ := by positivity
  have hL0 : (0 : ℝ) ≤ L := L.2
  set σ : ℝ := δ / (2 * ((L : ℝ) + 1)) with hσ
  have hσ0 : 0 < σ := by positivity
  have h2Lσ : 2 * (L : ℝ) * σ < δ := by
    rw [hσ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the clamped profile `G = max 0 (min 1 ((t − δ − f)/w))`: `(L/w)`-Lipschitz, `|G| ≤ 1`,
  -- `G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`
  set G : Euclid P → ℝ := fun x => max 0 (min 1 ((t - δ - f x) / w)) with hGdef
  set K : NNReal := L * Real.toNNReal w⁻¹ with hK
  have hKr : (K : ℝ) = L / w := by
    rw [hK, NNReal.coe_mul, Real.coe_toNNReal _ (inv_pos.2 hw0).le, div_eq_mul_inv]
  have hG : LipschitzWith K G := by
    have hlin : LipschitzWith K fun x => (t - δ - f x) / w := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hxy := hf.dist_le_mul x y
      rw [Real.dist_eq] at hxy
      rw [Real.dist_eq, hKr, show (t - δ - f x) / w - (t - δ - f y) / w = (f y - f x) / w by ring,
        abs_div, abs_of_pos hw0, abs_sub_comm, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hxy hw0.le
    exact (hlin.const_min 1).const_max 0
  have hG01 : ∀ y, |G y| ≤ 1 := by
    intro y
    simp only [hGdef]
    rw [abs_le]
    exact ⟨by linarith [le_max_left 0 (min 1 ((t - δ - f y) / w))],
      max_le zero_le_one (min_le_left _ _)⟩
  have hG1 : ∀ y, f y < t - h + δ → G y = 1 := by
    intro y hy
    have : 1 ≤ (t - δ - f y) / w := by rw [le_div_iff₀ hw0]; linarith
    simp [hGdef, min_eq_left this]
  have hG0 : ∀ y, t - δ < f y → G y = 0 := by
    intro y hy
    have : (t - δ - f y) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
    simp only [hGdef]
    exact max_eq_left ((min_le_right _ _).trans this)
  -- smoothing of `G` at scale `σ`
  obtain ⟨g, hgs, hgd, hga, hgl⟩ := Submission.cmcs_lipschitz_smoothing P G K σ hG hσ0
  -- plateaus: if `G = c` on `B_{2σ}(x)`, then `g = c` on `B_σ(x)`, so `g x = c` and `Dg(x) = 0`
  have hnear : ∀ x, ∀ c : ℝ, (∀ y ∈ ball x (2 * σ), G y = c) → g x = c ∧ fderiv ℝ g x = 0 := by
    intro x c hc
    have hball : ∀ x' ∈ ball x σ, g x' = c := fun x' hx' => hgl x' c fun y hy => hc y (by
      rw [mem_ball] at hx' hy ⊢
      linarith [dist_triangle y x' x])
    have hev : g =ᶠ[𝓝 x] fun _ => c := Filter.eventually_of_mem (ball_mem_nhds x hσ0) hball
    exact ⟨hball x (mem_ball_self hσ0), hev.fderiv_eq.trans (fderiv_const_apply c)⟩
  -- on `B_{2σ}(x)`, `|f y − f x| ≤ L |y − x| < 2Lσ < δ`
  have hclose : ∀ x, ∀ y ∈ ball x (2 * σ), |f y - f x| < δ := by
    intro x y hy
    have hd := hf.dist_le_mul y x
    rw [Real.dist_eq] at hd
    rw [mem_ball] at hy
    have : (L : ℝ) * dist y x ≤ L * (2 * σ) := mul_le_mul_of_nonneg_left hy.le hL0
    linarith
  have hlow : ∀ x, f x ≤ t - h → g x = 1 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 1 fun y hy => hG1 y (by linarith [(abs_lt.1 (hclose x y hy)).2])
  have hup : ∀ x, t ≤ f x → g x = 0 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 0 fun y hy => hG0 y (by linarith [(abs_lt.1 (hclose x y hy)).1])
  refine ⟨g, hgs, fun x => ?_, fun x => (hgd x).trans_eq hKr, fun x hx => ?_,
    fun x hx => (hlow x hx).1, fun x hx => (hup x hx).1⟩
  · -- `|g| ≤ |G| + Kσ ≤ 2`, as `Kσ = Lδ/(2(L + 1)w) ≤ 1` (`δ ≤ 2w`)
    have hKσ : (K : ℝ) * σ ≤ 1 := by
      rw [hKr, hσ, div_mul_div_comm, div_le_one (by positivity)]
      have hδw : δ ≤ 2 * w := by rw [hδ, hw]; nlinarith
      nlinarith
    linarith [abs_sub_abs_le_abs_sub (g x) (G x), hga x, hG01 x]
  · -- `Dg = 0` on both plateaus, so `Dg(x) ≠ 0` forces `t − h < f x < t`
    by_contra hcon
    rcases not_and_or.1 hcon with hc | hc
    · exact hx (hlow x (not_lt.1 hc)).2
    · exact hx (hup x (not_lt.1 hc)).2

/-- **Mass of a slice, pointwise in `t`** (Simon 6.4.9, proved as in 6.4.11): let `T = ξ μ`,
`∂T = ξ' μ'` with `|ξ|, |ξ'| ≤ 1`, let `f` be `L`-Lipschitz, and let `A = T ⌞ {f < t}`,
`B = (∂T) ⌞ {f < t}`.  Then `M_W(∂A − B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})`.
For an admissible `η` and `h ∈ (0, 1)`, the smooth cut-off `g_h` of `cmcs_level_cutoff` gives
`Φ_h = ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ'` with `|Φ_h| ≤ ∫ |Dg_h| |η| dμ ≤ c_h μ(W ∩ S_h)`,
`c_h = L / (h(1 − h/2))`, `S_h = {t − h < f < t}` (`cmcs_cutoff_defect_bound`,
`cmcs_smp_strip_lintegral_le`); `Φ_h → (∂A − B)(η)` by dominated convergence
(`cmcs_smp_cutoff_integral_tendsto`), and `cmcs_smp_liminf_bound` passes to the liminf. -/
theorem Submission.cmcs_slice_mass_pointwise : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k) (W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (A.boundary - B).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro P k U T μ μ' ξ ξ' f L t A B W hμ hμ' hξm hξm' hξ hξ' hT hbT hf hA hB
  -- Step 3: a cut-off `g h` for every `h ∈ (0, 1)` (junk value `0` for other `h`).
  have hcut : ∀ h : ℝ, ∃ g : Euclid P → ℝ, 0 < h → h < 1 →
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧
        (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧
        (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧
        (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
    intro h
    by_cases hh : 0 < h ∧ h < 1
    · obtain ⟨g, hg⟩ := Submission.cmcs_level_cutoff P f L t h hf hh.1 hh.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨0, fun h0 h1 => (hh ⟨h0, h1⟩).elim⟩
  choose g hg using hcut
  -- Step 1: it suffices to bound `ofReal ((∂A − B) η)` for one admissible `η`.
  apply sSup_le
  rintro r ⟨η, ⟨hηW, hη1⟩, rfl⟩
  have hZ : (A.boundary - B) η =
      (∫ x in {x | f x < t}, ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' := by
    change A (exteriorDerivativeTestOn U k η) - B η = _
    rw [hA, hB]
    rfl
  -- Step 2: `F = ξ(dη)` is `μ`-integrable and `F' = ξ'(η)` is `μ'`-integrable.
  have hF : Integrable
      (fun x => ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x)) μ :=
    Submission.cmcs_smp_pairing_integrable P (k + 1) U μ ξ (exteriorDerivativeTestOn U k η)
      hμ hξm hξ
  have hF' : Integrable (fun x => ξ' x ((η : DifferentialForm (Euclid P) k) x)) μ' :=
    Submission.cmcs_smp_pairing_integrable P k U μ' ξ' η hμ' hξm' hξ'
  -- Step 5: `Φ h → (∂A − B)(η)` as `h ↓ 0`, by dominated convergence for each integral.
  have hfm : Measurable f := hf.continuous.measurable
  have hgm : ∀ ν : Measure (Euclid P), ∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) ν :=
    fun _ h h0 h1 => (hg h h0 h1).1.continuous.aestronglyMeasurable
  have hlim : Tendsto (fun h : ℝ =>
      (∫ x, g h x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x, g h x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ')
      (𝓝[>] 0) (𝓝 ((A.boundary - B) η)) := by
    rw [hZ]
    exact (Submission.cmcs_smp_cutoff_integral_tendsto P μ _ f t 2 g hF hfm (hgm μ)
      (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
      (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2)).sub
      (Submission.cmcs_smp_cutoff_integral_tendsto P μ' _ f t 2 g hF' hfm (hgm μ')
        (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
        (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2))
  -- Steps 4 and 6: `ofReal |Φ h| ≤ ofReal (L / (h (1 − h/2))) μ(W ∩ S_h)` for `h ∈ (0, 1)`,
  -- then pass to the liminf.
  refine Submission.cmcs_smp_liminf_bound L ((A.boundary - B) η) _
    (fun h => μ (W ∩ {x | t - h < f x ∧ f x < t})) hlim fun h h0 h1 => ?_
  obtain ⟨hgs, -, hgd, hgS, -, -⟩ := hg h h0 h1
  exact (Submission.cmcs_cutoff_defect_bound P k U T μ μ' ξ ξ' (g h) η hξ hT hbT hgs).trans
    (Submission.cmcs_smp_strip_lintegral_le P k μ (g h) (η : DifferentialForm (Euclid P) k) W
      {x | t - h < f x ∧ f x < t} _ hgd hgS hηW hη1)
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
/-- An open `U ⊆ ℝᴾ` is exhausted by the compact sets `Kᵢ = B̄(0, i) \ thickening((i + 1)⁻¹, Uᶜ)`
(the exhaustion in the proof of Simon 1.4.16): `Kᵢ ⊆ U`, since a point of `Uᶜ` lies in every
positive thickening of `Uᶜ`; a compact `C ⊆ U` has a margin `δ > 0` with `thickening δ C ⊆ U` and
a radius `R` with `C ⊆ B̄(0, R)`, so `C ⊆ Kₘ` once `R ≤ m` and `(m + 1)⁻¹ < δ`. -/
theorem Submission.cbr_ct_vs_compact_exhaustion : ∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i := by
  intro P U hU
  refine ⟨fun i => closedBall (0 : Euclid P) i \ thickening ((i : ℝ) + 1)⁻¹ Uᶜ,
    fun i => (isCompact_closedBall _ _).diff isOpen_thickening, fun i x hx => ?_,
    fun C hC hCU => ?_⟩
  · by_contra hxU
    exact hx.2 (self_subset_thickening (by positivity) _ hxU)
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Euclid P)
    obtain ⟨m, hm⟩ := exists_nat_ge (max R δ⁻¹)
    have hmδ : ((m : ℝ) + 1)⁻¹ < δ := inv_lt_of_inv_lt₀ hδ (by linarith [le_max_right R δ⁻¹])
    refine ⟨m, fun x hx => ⟨closedBall_subset_closedBall ((le_max_left R δ⁻¹).trans hm) (hR hx),
      fun hxt => ?_⟩⟩
    -- a point `y ∉ U` within `(m + 1)⁻¹ < δ` of `x ∈ C` would lie in `thickening δ C ⊆ U`
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hxt
    exact hy (hδU (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
/-- **Simon 1.4.16, one compact piece** (the Alaoglu step of the proof, corrected to a genuine
subsequence).  If `K ⊆ ℝᴾ` is compact and `supⱼ μⱼ(K) < ∞`, there is a strictly increasing `θ`
such that `∫ f dμ_{θ(j)}` converges for every continuous `f` with `tsupport f ⊆ K`.  As `f`
vanishes off `K`, `∫ f dμⱼ = ∫_K f dμⱼ`.  The step functions `g (n, L) x = L[m]` (`m` the first
index with `|x - dₘ| < 1/(n+1)`, `(dₘ)` dense in `ℝᴾ`, `L` a list of rationals) form a countable
family that is uniformly dense on `K` for such `f`.  Sequential compactness of a countable product
of compact intervals gives one subsequence along which every `∫_K g dμⱼ` converges, and a `3ε`
argument makes `∫_K f dμ_{θ(j)}` Cauchy. -/
theorem Submission.cbr_ct_vs_compact_piece_subseq : ∀ (P : ℕ) (K : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsCompact K → ⨆ j, μs j K < ∞ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (θ j))) atTop (𝓝 c) := by
  classical
  intro P K μs hK hM
  -- `M = supⱼ μⱼ(K)` as a real number
  set M : ℝ := (⨆ j, μs j K).toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hμK : ∀ j, μs j K ≤ ⨆ j, μs j K := fun j => le_iSup (fun j => μs j K) j
  have hμKfin : ∀ j, μs j K < ∞ := fun j => lt_of_le_of_lt (hμK j) hM
  have hμKM : ∀ j, (μs j).real K ≤ M := fun j => ENNReal.toReal_mono hM.ne (hμK j)
  -- a dense sequence `d` in `ℝᴾ`: every `x` is within `1/(n+1)` of some `d m`
  set d : ℕ → Euclid P := TopologicalSpace.denseSeq (Euclid P)
  have hr : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  have hcov : ∀ (n : ℕ) (x : Euclid P), ∃ m, dist x (d m) < 1 / ((n : ℝ) + 1) :=
    fun n x => (TopologicalSpace.denseRange_denseSeq (Euclid P)).exists_dist_lt x (hr n)
  -- the countable test family `g (n, L) x = L[m]`, `m` the first index with
  -- `dist x (d m) < 1/(n+1)`; it is measurable and bounded by `B (n, L) = ∑ |L[i]|`
  let g : ℕ × List ℚ → Euclid P → ℝ := fun k x =>
    ((k.2.getD (Nat.find (hcov k.1 x)) 0 : ℚ) : ℝ)
  have hgm : ∀ k, Measurable (g k) := fun k =>
    Measurable.find (f := fun m _ => ((k.2.getD m 0 : ℚ) : ℝ)) (fun _ => measurable_const)
      (fun _ => measurableSet_ball) (hcov k.1)
  let B : ℕ × List ℚ → ℝ := fun k => (k.2.map (fun q : ℚ => |(q : ℝ)|)).sum
  have hgB : ∀ k x, |g k x| ≤ B k := by
    have key : ∀ (L : List ℚ) (m : ℕ),
        |((L.getD m 0 : ℚ) : ℝ)| ≤ (L.map (fun q : ℚ => |(q : ℝ)|)).sum := by
      intro L
      induction L with
      | nil => intro m; simp
      | cons a L ih =>
        intro m
        have hs : 0 ≤ (L.map (fun q : ℚ => |(q : ℝ)|)).sum := List.sum_nonneg (by simp)
        cases m with
        | zero =>
          simp only [List.getD_cons_zero, List.map_cons, List.sum_cons]
          linarith
        | succ m =>
          simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
          linarith [ih m, abs_nonneg (a : ℝ)]
    exact fun k x => key k.2 _
  -- every admissible `f` is uniformly approximated on `K` by the test family
  have happrox : ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K →
      ∀ ε > 0, ∃ k, ∀ x ∈ K, |f x - g k x| ≤ ε := by
    intro f hf hfK ε hε
    have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
      (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun m => ball (d m) (1 / ((n : ℝ) + 1)))
      (fun _ => isOpen_ball) (fun x _ => mem_iUnion.mpr (hcov n x))
    choose q hq using fun m => Rat.denseRange_cast.exists_dist_lt (f (d m)) (half_pos hε)
    refine ⟨(n, (List.range (t.sup id + 1)).map q), fun x hx => ?_⟩
    obtain ⟨m, hmt, hxm⟩ := mem_iUnion₂.mp (ht hx)
    have hlt : Nat.find (hcov n x) < t.sup id + 1 :=
      Nat.lt_succ_of_le ((Nat.find_min' (hcov n x) hxm).trans (Finset.le_sup (f := id) hmt))
    have h1 := hfδ ((Nat.find_spec (hcov n x)).trans hn)
    have h2 := hq (Nat.find (hcov n x))
    rw [Real.dist_eq] at h1 h2
    have hg : g (n, (List.range (t.sup id + 1)).map q) x = q (Nat.find (hcov n x)) := by
      simp only [g, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
        Option.map_some, Option.getD_some]
    rw [hg]
    linarith [abs_sub_le (f x) (f (d (Nat.find (hcov n x)))) (q (Nat.find (hcov n x)) : ℝ)]
  -- the test integrals `v j k = ∫_K g k dμⱼ` satisfy `|v j k| ≤ B k * M`
  have hgi : ∀ j k, IntegrableOn (g k) K (μs j) := fun j k =>
    Measure.integrableOn_of_bounded (hμKfin j).ne (hgm k).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hgB k x))
  let v : ℕ → ℕ × List ℚ → ℝ := fun j k => ∫ x in K, g k x ∂(μs j)
  have hvB : ∀ j k, |v j k| ≤ B k * M := by
    intro j k
    rw [← Real.norm_eq_abs]
    calc ‖∫ x in K, g k x ∂(μs j)‖ ≤ B k * (μs j).real K :=
          norm_setIntegral_le_of_norm_le_const (hμKfin j)
            (fun x _ => (Real.norm_eq_abs _).trans_le (hgB k x))
      _ ≤ B k * M := mul_le_mul_of_nonneg_left (hμKM j) ((abs_nonneg _).trans (hgB k 0))
  -- diagonal selection: `(v j)ⱼ` lies in the compact `∏ₖ [-B k M, B k M]`, which is
  -- first countable since `ℕ × List ℚ` is countable
  obtain ⟨a, -, θ, hθ, hlim⟩ :=
    (isCompact_univ_pi fun k : ℕ × List ℚ =>
      isCompact_Icc (a := -(B k * M)) (b := B k * M)).tendsto_subseq
      (x := v) fun j => Set.mem_univ_pi.mpr fun k => abs_le.mp (hvB j k)
  have hconv : ∀ k, Tendsto (fun j => v (θ j) k) atTop (𝓝 (a k)) := tendsto_pi_nhds.mp hlim
  refine ⟨θ, hθ, fun f hf hfK => ?_⟩
  -- `f` vanishes off `K`, so `∫ f dμⱼ = ∫_K f dμⱼ`; and `f` is bounded
  have hf0 : ∀ x ∉ K, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfK h)
  have hfK' : ∀ j, ∫ x, f x ∂(μs j) = ∫ x in K, f x ∂(μs j) := fun j =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero hf0).symm
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support
    (hK.of_isClosed_subset (isClosed_tsupport f) hfK)
  have hfi : ∀ j, IntegrableOn f K (μs j) := fun j =>
    Measure.integrableOn_of_bounded (hμKfin j).ne hf.aestronglyMeasurable (ae_of_all _ hC)
  -- `∫ f dμⱼ` is `η M`-close to a test integral, uniformly in `j`
  have hclose : ∀ η > 0, ∃ k, ∀ j, dist (∫ x, f x ∂(μs j)) (v j k) ≤ η * M := by
    intro η hη
    obtain ⟨k, hk⟩ := happrox f hf hfK η hη
    refine ⟨k, fun j => ?_⟩
    rw [hfK' j, dist_eq_norm, ← integral_sub (hfi j) (hgi j k)]
    calc ‖∫ x in K, (f x - g k x) ∂(μs j)‖ ≤ η * (μs j).real K :=
          norm_setIntegral_le_of_norm_le_const (hμKfin j)
            (fun x hx => (Real.norm_eq_abs _).trans_le (hk x hx))
      _ ≤ η * M := mul_le_mul_of_nonneg_left (hμKM j) hη.le
  -- hence `(∫ f dμ_{θ j})ⱼ` is Cauchy, so it converges
  have hcauchy : CauchySeq (fun j => ∫ x, f x ∂(μs (θ j))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := hclose (ε / (3 * (M + 1))) (by positivity)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hconv k).cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hk (θ m)
    have h2 := hk (θ n)
    have h3 := hN m hm n hn
    have hη : ε / (3 * (M + 1)) * M ≤ ε / 3 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc dist (∫ x, f x ∂(μs (θ m))) (∫ x, f x ∂(μs (θ n)))
        ≤ dist (∫ x, f x ∂(μs (θ m))) (v (θ m) k) + dist (v (θ m) k) (v (θ n) k) +
            dist (v (θ n) k) (∫ x, f x ∂(μs (θ n))) := dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm (v (θ n) k)]; linarith
  exact cauchySeq_tendsto_of_complete hcauchy
/-- **Diagonal subsequence** (Simon Ch. 1, proof of 4.16, chapter-01.txt lines 1767–1768: "By
choosing the subsequences successively and taking a diagonal sequence, we then get a subsequence
`μ_{k'}` …").  If every strictly increasing `ψ` has a strictly increasing refinement `ψ ∘ θ` along
which `s i` converges for all `i ∈ F m`, then one strictly increasing `φ` makes `s i ∘ φ` converge
for every `m` and every `i ∈ F m`.  Successive refinements `ψ₀ = Θ 0 id`,
`ψ_{m+1} = ψ_m ∘ Θ (m + 1) ψ_m` give the diagonal `φ j = ψ_j j`, whose tail
`φ (m + k) = ψ_m (τ_k (m + k))` is a subsequence of `ψ_m`. -/
theorem Submission.cbr_ct_vs_diagonal_subseq : ∀ (ι : Type) (F : ℕ → Set ι) (s : ι → ℕ → ℝ), (∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (ψ (θ j))) atTop (𝓝 c)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (φ j)) atTop (𝓝 c) := by
  intro ι F s h
  -- Step 2: choice `Θ m ψ` of a strictly increasing refinement of `ψ` convergent on `F m`
  choose Θ hΘ hΘconv using h
  -- Step 3: `ψ₀ = Θ 0 id`, `ψ_{m+1} = ψ_m ∘ Θ (m + 1) ψ_m`, carried with `StrictMono`
  let ψ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun m =>
    Nat.rec ⟨Θ 0 id strictMono_id, hΘ 0 id strictMono_id⟩
      (fun m p => ⟨p.1 ∘ Θ (m + 1) p.1 p.2, p.2.comp (hΘ (m + 1) p.1 p.2)⟩) m
  have hgood : ∀ m, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i ((ψ m).1 j)) atTop (𝓝 c) := by
    intro m
    cases m with
    | zero => exact hΘconv 0 id strictMono_id
    | succ m => exact hΘconv (m + 1) (ψ m).1 (ψ m).2
  -- Step 4: `ψ_{m+k} = ψ_m ∘ τ` with `τ` strictly increasing
  have hfac : ∀ m k, ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ n, (ψ (m + k)).1 n = (ψ m).1 (τ n) := by
    intro m k
    induction k with
    | zero => exact ⟨id, strictMono_id, fun n => rfl⟩
    | succ k ih =>
      obtain ⟨τ, hτ, hτeq⟩ := ih
      exact ⟨τ ∘ Θ (m + k + 1) (ψ (m + k)).1 (ψ (m + k)).2, hτ.comp (hΘ _ _ _),
        fun n => hτeq (Θ (m + k + 1) (ψ (m + k)).1 (ψ (m + k)).2 n)⟩
  -- Step 5: the diagonal `φ j = ψ_j j`; `ψ_{j+1} (j + 1) = ψ_j (Θ _ _ _ (j + 1)) ≥ ψ_j (j + 1)`
  let φ : ℕ → ℕ := fun j => (ψ j).1 j
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun j =>
    ((ψ j).2 (Nat.lt_add_one j)).trans_le
      ((ψ j).2.monotone (hΘ (j + 1) (ψ j).1 (ψ j).2).le_apply)
  refine ⟨φ, hφ, fun m i hi => ?_⟩
  -- Step 6: `φ (m + k) = ψ_m (σ k)` with `σ k = τ_k (m + k)` strictly increasing
  choose τ hτ hτeq using hfac m
  have hφτ : ∀ k, φ (m + k) = (ψ m).1 (τ k (m + k)) := fun k => hτeq k (m + k)
  have hσ : StrictMono fun k => τ k (m + k) := strictMono_nat_of_lt_succ fun k => by
    have h1 : φ (m + k) < φ (m + (k + 1)) := hφ (Nat.lt_add_one (m + k))
    rw [hφτ, hφτ] at h1
    exact (ψ m).2.lt_iff_lt.mp h1
  -- Step 7: compose with `σ → ∞` and undo the index shift by `m`
  obtain ⟨c, hc⟩ := hgood m i hi
  refine ⟨c, (tendsto_add_atTop_iff_nat m).mp ((hc.comp hσ.tendsto_atTop).congr fun k => ?_)⟩
  show s i ((ψ m).1 (τ k (m + k))) = s i (φ (k + m))
  rw [add_comm k m, hφτ]

/-- **Vague selection on an open set** (Simon Ch. 1, Theorem 4.16 and its proof, chapter-01.txt
lines 1750–1778, for `X = U` open in `ℝᴾ`).  If `supⱼ μⱼ(K) < ∞` for every compact `K ⊆ U`, one
strictly increasing `φ` makes `∫ f dμ_{φ(j)}` converge for every continuous `f` with compact
support in `U`.  Exhaust `U` by compact `Kₘ ⊆ U`; the one-piece selection (the Alaoglu step,
corrected to a genuine subsequence) refines any strictly increasing `ψ` on `Kₘ`, because
`supⱼ μ_{ψ(j)}(Kₘ) ≤ supⱼ μⱼ(Kₘ) < ∞`, and the diagonal argument yields `φ`.  The compact
`tsupport f ⊆ U` lies in some `Kₘ`. -/
theorem Submission.cbr_vague_convergent_subseq : ∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 c) := by
  intro P U μs hU hμ
  -- Step 1: compact `Kₘ ⊆ U` such that every compact subset of `U` lies in some `Kₘ`
  obtain ⟨K, hK, hKU, hKC⟩ := Submission.cbr_ct_vs_compact_exhaustion P U hU
  -- Steps 2–6: diagonal subsequence for `F m = {f | f continuous, tsupport f ⊆ Kₘ}` and
  -- `s f j = ∫ f dμⱼ`; Claim A refines `ψ` on `Kₘ`, as `supⱼ μ_{ψ(j)}(Kₘ) ≤ supⱼ μⱼ(Kₘ) < ∞`
  obtain ⟨φ, hφ, hconv⟩ := Submission.cbr_ct_vs_diagonal_subseq (Euclid P → ℝ)
    (fun m => {f | Continuous f ∧ tsupport f ⊆ K m}) (fun f j => ∫ x, f x ∂(μs j))
    fun m ψ _ => by
      obtain ⟨θ, hθ, hθc⟩ := Submission.cbr_ct_vs_compact_piece_subseq P (K m)
        (fun j => μs (ψ j)) (hK m)
        ((iSup_comp_le (fun j => μs j (K m)) ψ).trans_lt (hμ (K m) (hK m) (hKU m)))
      exact ⟨θ, hθ, fun f hf => hθc f hf.1 hf.2⟩
  -- Step 7: the compact `tsupport f ⊆ U` lies in some `Kₘ`
  refine ⟨φ, hφ, fun f hf hfc hfU => ?_⟩
  obtain ⟨m, hm⟩ := hKC (tsupport f) hfc.isCompact hfU
  exact hconv m f ⟨hf, hm⟩
/-- A continuous function `f` with compact support in `U` is `ν`-integrable for every measure `ν`
finite on compact subsets of `U` (Simon Ch. 1, 4.16: `∫ f dμ` is finite for `f ∈ K(X)`).
`S = spt f` is a compact subset of `U`, so `ν(S) < ∞` and `ν⌞S` is a finite measure; `f` is
`ν⌞S`-integrable, and since `f` vanishes off `S` it is `ν`-integrable. -/
theorem Submission.cbr_vl_integrable_of_tsupport_subset : ∀ (P : ℕ) (U : Set (Euclid P)) (ν : Measure (Euclid P)) (f : Euclid P → ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K < ∞) → Continuous f → HasCompactSupport f → tsupport f ⊆ U → Integrable f ν := by
  intro P U ν f hν hf hcf hU
  -- Step 1: `S = tsupport f` is a compact subset of `U`, so `ν(S) < ∞`.
  have hS : ν (tsupport f) < ∞ := hν _ hcf hU
  -- Step 2: `ν⌞S` has total mass `ν(S) < ∞`.
  have : IsFiniteMeasure (ν.restrict (tsupport f)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  -- Steps 3–4: `f` is `ν⌞S`-integrable and vanishes off `S`, hence is `ν`-integrable.
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    (hf.integrable_of_hasCompactSupport hcf)
/-- **Simon 1.4.12 on `U`** (Riesz representation, as invoked in the proof of 1.4.16): a positive
linear functional `Λ` on the continuous functions with compact support in the open set `U ⊆ ℝᴾ`
is `f ↦ ∫ f dμ` for a measure `μ` on `ℝᴾ` with `μ(ℝᴾ \ U) = 0` that is finite on compact subsets
of `U`.  Mathlib's `RealRMK.rieszMeasure` on the locally compact subtype `U`, applied to
`g ↦ Λ(ĝ)` (`ĝ` the extension of `g` by zero), is pushed forward to `ℝᴾ`. -/
theorem Submission.cbr_vl_riesz_measure_on_open : ∀ (P : ℕ) (U : Set (Euclid P)) (Λ : (Euclid P → ℝ) → ℝ), IsOpen U → (∀ f g : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (f + g) = Λ f + Λ g) → (∀ (c : ℝ) (f : Euclid P → ℝ), Continuous f → HasCompactSupport f → tsupport f ⊆ U → Λ (c • f) = c * Λ f) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → (∀ x, 0 ≤ f x) → 0 ≤ Λ f) → ∃ μ : Measure (Euclid P), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∫ x, f x ∂μ = Λ f := by
  intro P U Λ hU hadd hsmul hpos
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  -- the extension `ĝ = Subtype.val.extend g 0` of `g : U → ℝ` by zero
  have hext_val : ∀ (g : U → ℝ) (y : U), Subtype.val.extend g (0 : Euclid P → ℝ) y = g y :=
    fun g y => Subtype.val_injective.extend_apply g 0 y
  have hext_out : ∀ (g : U → ℝ) (x : Euclid P), x ∉ U →
      Subtype.val.extend g (0 : Euclid P → ℝ) x = 0 := by
    intro g x hx
    have hx' : ¬∃ y : U, (y : Euclid P) = x := by
      rintro ⟨y, rfl⟩
      exact hx y.2
    rw [extend_apply' g (0 : Euclid P → ℝ) x hx']
    rfl
  -- `ĝ` is continuous with compact support in `U` for `g ∈ C_c(U, ℝ)`
  have hext : ∀ g : CompactlySupportedContinuousMap U ℝ,
      Continuous (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ)) ∧
        HasCompactSupport (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ)) ∧
        tsupport (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ)) ⊆ U := fun g =>
    ⟨HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport,
      g.hasCompactSupport.extend_zero continuous_subtype_val,
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)⟩
  -- `Λ_U(g) = Λ(ĝ)` is a positive linear functional on `C_c(U, ℝ)`
  let L : CompactlySupportedContinuousMap U ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun g => Λ (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ))
      map_add' := fun g₁ g₂ => by
        have h := extend_add (Subtype.val : U → Euclid P) (g₁ : U → ℝ) g₂ (0 : Euclid P → ℝ) 0
        rw [add_zero] at h
        simp only [CompactlySupportedContinuousMap.coe_add]
        rw [h]
        exact hadd _ _ (hext g₁).1 (hext g₁).2.1 (hext g₁).2.2 (hext g₂).1 (hext g₂).2.1
          (hext g₂).2.2
      map_smul' := fun c g => by
        have h := extend_smul c (Subtype.val : U → Euclid P) (g : U → ℝ) (0 : Euclid P → ℝ)
        rw [smul_zero] at h
        simp only [CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [h]
        exact hsmul c _ (hext g).1 (hext g).2.1 (hext g).2.2 }
  let ΛU := PositiveLinearMap.mk₀ L fun g hg => by
    refine hpos _ (hext g).1 (hext g).2.1 (hext g).2.2 fun x => ?_
    by_cases hx : x ∈ U
    · rw [show x = ((⟨x, hx⟩ : U) : Euclid P) from rfl, hext_val]
      exact hg ⟨x, hx⟩
    · rw [hext_out _ x hx]
  -- the Riesz measure of `Λ_U` on `U`, pushed forward to `ℝᴾ`
  have hme : MeasurableEmbedding (Subtype.val : U → Euclid P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have hcpt : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IsCompact ((Subtype.val : U → Euclid P) ⁻¹' K) := by
    intro K hK hKU
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hKU]
    exact hK
  refine ⟨(RealRMK.rieszMeasure ΛU).map Subtype.val, ?_, fun K hK hKU => ?_,
    fun f hf hfc hfU => ?_⟩
  · rw [hme.map_apply, Subtype.preimage_coe_compl, measure_empty]
  · rw [hme.map_apply]
    exact (hcpt K hK hKU).measure_lt_top
  · -- `f = ĝ` for `g = f ∘ Subtype.val ∈ C_c(U, ℝ)`
    let g : CompactlySupportedContinuousMap U ℝ :=
      ⟨⟨f ∘ Subtype.val, hf.comp continuous_subtype_val⟩,
        IsCompact.of_isClosed_subset (hcpt _ hfc hfU) (isClosed_tsupport _)
          (tsupport_comp_subset_preimage f continuous_subtype_val)⟩
    have hfg : Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ) = f := by
      funext x
      by_cases hx : x ∈ U
      · rw [show x = ((⟨x, hx⟩ : U) : Euclid P) from rfl, hext_val]
        rfl
      · rw [hext_out _ x hx, image_eq_zero_of_notMem_tsupport fun h => hx (hfU h)]
    rw [hme.integral_map]
    calc ∫ y, f y ∂RealRMK.rieszMeasure ΛU = ∫ y, g y ∂RealRMK.rieszMeasure ΛU := rfl
      _ = ΛU g := RealRMK.integral_rieszMeasure ΛU g
      _ = Λ f := congrArg Λ hfg

/-- **Simon 1.4.16, last step** (the vague limit is a Radon measure on `U`): if every `ν_j` is
finite on compact subsets of the open set `U ⊆ ℝᴾ` and `∫ f dν_j` converges for every continuous
`f` with compact support in `U`, then `Λ(f) = lim_j ∫ f dν_j` is additive, homogeneous and
non-negative on these `f` (such `f` are `ν_j`-integrable; uniqueness of limits), so Simon 1.4.12
on `U` gives `μ` with `μ(ℝᴾ \ U) = 0`, finite on compact subsets of `U`, and
`∫ f dμ = Λ(f) = lim_j ∫ f dν_j`. -/
theorem Submission.cbr_vague_limit_measure : ∀ (P : ℕ) (U : Set (Euclid P)) (νs : ℕ → Measure (Euclid P)), IsOpen U → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → νs j K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 c)) → ∃ μ : Measure (Euclid P), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  intro P U νs hU hν hlim
  -- the limit functional `Λ(f) = lim_j ∫ f dν_j`
  let Λ : (Euclid P → ℝ) → ℝ := fun f => limUnder atTop fun j => ∫ x, f x ∂(νs j)
  have hΛ : ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (Λ f)) :=
    fun f hf hfc hfU => tendsto_nhds_limUnder (hlim f hf hfc hfU)
  -- such `f` are `ν_j`-integrable, so `∫ · dν_j` is linear on them
  have hint : ∀ (j : ℕ) (f : Euclid P → ℝ), Continuous f → HasCompactSupport f →
      tsupport f ⊆ U → Integrable f (νs j) :=
    fun j f => Submission.cbr_vl_integrable_of_tsupport_subset P U (νs j) f (hν j)
  -- `Λ` is additive, homogeneous and non-negative, so it is integration against some `μ`
  obtain ⟨μ, hμU, hμK, hμΛ⟩ := Submission.cbr_vl_riesz_measure_on_open P U Λ hU
    (fun f g hf hfc hfU hg hgc hgU => by
      refine tendsto_nhds_unique (hΛ _ (hf.add hg) (hfc.add hgc)
        ((tsupport_add f g).trans (union_subset hfU hgU))) ?_
      refine ((hΛ f hf hfc hfU).add (hΛ g hg hgc hgU)).congr fun j => ?_
      exact (integral_add (hint j f hf hfc hfU) (hint j g hg hgc hgU)).symm)
    (fun c f hf hfc hfU => by
      have hcf : support (c • f) ⊆ support f := support_const_smul_subset c f
      refine tendsto_nhds_unique (hΛ _ (hf.const_smul c) (hfc.mono hcf)
        ((closure_mono hcf).trans hfU)) ?_
      refine ((hΛ f hf hfc hfU).const_mul c).congr fun j => ?_
      exact (integral_smul c f).symm)
    (fun f hf hfc hfU hf0 => ge_of_tendsto' (hΛ f hf hfc hfU) fun j => integral_nonneg hf0)
  refine ⟨μ, hμU, hμK, fun f hf hfc hfU => ?_⟩
  rw [hμΛ f hf hfc hfU]
  exact hΛ f hf hfc hfU
/-- **Portmanteau inequalities for vague convergence on an open set** (Evans–Gariepy §1.9).
Simon does not state this separately: it is the converse of the "standard approximation
argument" ending the proof of 7.2.4, and its compact-set half is the `ε`-neighbourhood argument
giving (13) there (chapter-07.txt lines 264–288).  Let `U` be open and `νⱼ`, `μ` finite on compact
subsets of `U`.  If `∫ f dνⱼ → ∫ f dμ` for every continuous `f` with compact support in `U`, then
`limsup νⱼ(K) ≤ μ(K)` for compact `K ⊆ U` and `μ(G) ≤ liminf νⱼ(G)` for open `G ⊆ U`.  Urysohn
cut-offs `1_K ≤ h ≤ 1_{thickening r K}` give `limsup νⱼ(K) ≤ μ(cthickening r K) → μ(K)` as
`r ↓ 0`; cut-offs `1_C ≤ h` with `tsupport h ⊆ G` give `μ(C) ≤ liminf νⱼ(G)` for compact
`C ⊆ G`, and `G` is exhausted by increasing compact sets. -/
theorem Submission.cbr_vague_portmanteau : ∀ (P : ℕ) (U : Set (Euclid P)) (νs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), IsOpen U → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → νs j K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (∫ x, f x ∂μ))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => νs j K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => νs j G) atTop) := by
  intro P U νs μ hU hνs hμ hconv
  -- Step 1: cut-off functions.  For compact `C` and `r > 0`, Urysohn's lemma gives a continuous
  -- `h` with compact support, `0 ≤ h ≤ 1`, `h = 1` on `C` and `h = 0` off `thickening r C`;
  -- hence `tsupport h ⊆ cthickening r C`
  have hcut : ∀ (C : Set (Euclid P)) (r : ℝ), IsCompact C → 0 < r →
      ∃ h : Euclid P → ℝ, Continuous h ∧ HasCompactSupport h ∧ (∀ x, 0 ≤ h x) ∧
        (∀ x ∈ C, h x = 1) ∧ (∀ x, h x ≤ 1) ∧ (∀ x, x ∉ thickening r C → h x = 0) ∧
        tsupport h ⊆ cthickening r C := by
    intro C r hC hr
    obtain ⟨h, h1, h0, hcs, h01⟩ := exists_continuous_one_zero_of_isCompact hC
      isOpen_thickening.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (self_subset_thickening hr C))
    refine ⟨h, h.continuous, hcs, fun x => (h01 x).1, fun x hx => h1 hx, fun x => (h01 x).2,
      fun x hx => h0 hx, (closure_mono fun x hx => ?_).trans
        (closure_thickening_subset_cthickening r C)⟩
    by_contra hxr
    exact hx (h0 hxr)
  -- Step 0: such an `h` is `ρ`-integrable whenever `ρ(tsupport h) < ∞`; then
  -- `ρ(B) ≤ ofReal (∫ h dρ)` if `h = 1` on `B` (`Integrable.measure_le_integral`), and in any
  -- case `ofReal (∫ h dρ) ≤ ρ(V)` if `h ≤ 1` and `h = 0` off `V` (`integral_le_measure`)
  have hint : ∀ (ρ : Measure (Euclid P)) (h : Euclid P → ℝ), Continuous h → HasCompactSupport h →
      ρ (tsupport h) < ∞ → Integrable h ρ := fun ρ h hc hcs hρ =>
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport h)).mp
      (hc.continuousOn.integrableOn_of_subset_isCompact hcs (isClosed_tsupport h).measurableSet
        subset_rfl hρ.ne)
  -- Step 2: compact sets.  Choose `δ > 0` with `cthickening δ K ⊆ U`; for `0 < r ≤ δ`,
  -- `limsup νⱼ(K) ≤ lim ofReal (∫ h dνⱼ) = ofReal (∫ h dμ) ≤ μ(cthickening r K)`, and
  -- `μ(cthickening r K) → μ(K)` as `r → 0` because `μ(cthickening δ K) < ∞`
  have hK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      limsup (fun j => νs j K) atTop ≤ μ K := by
    intro K hKc hKU
    obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
    have hr : ∀ r, 0 < r → r ≤ δ → limsup (fun j => νs j K) atTop ≤ μ (cthickening r K) := by
      intro r hr hrδ
      obtain ⟨h, hc, hcs, h0, h1, hle1, hout, hts⟩ := hcut K r hKc hr
      have htsU : tsupport h ⊆ U := hts.trans ((cthickening_mono hrδ K).trans hδU)
      calc limsup (fun j => νs j K) atTop
          ≤ limsup (fun j => ENNReal.ofReal (∫ x, h x ∂(νs j))) atTop :=
            limsup_le_limsup (Eventually.of_forall fun j =>
              (hint (νs j) h hc hcs (hνs j _ hcs htsU)).measure_le_integral
                (Eventually.of_forall h0) fun x hx => (h1 x hx).ge)
        _ = ENNReal.ofReal (∫ x, h x ∂μ) :=
            ((ENNReal.continuous_ofReal.tendsto _).comp (hconv h hc hcs htsU)).limsup_eq
        _ ≤ μ (cthickening r K) := integral_le_measure (fun x _ => hle1 x)
            fun x hx => (hout x fun hx' => hx (thickening_subset_cthickening r K hx')).le
    have hlim := tendsto_measure_cthickening_of_isClosed
      ⟨δ, hδ, (hμ _ hKc.cthickening hδU).ne⟩ hKc.isClosed
    refine ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)) ?_
    filter_upwards [Ioc_mem_nhdsGT hδ] with r hr' using hr r hr'.1 hr'.2
  -- Step 3: compact subsets `C` of open `G ⊆ U`.  With `h = 1` on `C` and `tsupport h ⊆ G`,
  -- `μ(C) ≤ ofReal (∫ h dμ) = lim ofReal (∫ h dνⱼ) ≤ liminf νⱼ(G)`
  have hCG : ∀ G : Set (Euclid P), IsOpen G → G ⊆ U → ∀ C : Set (Euclid P), IsCompact C →
      C ⊆ G → μ C ≤ liminf (fun j => νs j G) atTop := by
    intro G hG hGU C hCc hCG
    obtain ⟨δ, hδ, hδG⟩ := hCc.exists_cthickening_subset_open hG hCG
    obtain ⟨h, hc, hcs, h0, h1, hle1, -, hts⟩ := hcut C δ hCc hδ
    have htsG : tsupport h ⊆ G := hts.trans hδG
    calc μ C ≤ ENNReal.ofReal (∫ x, h x ∂μ) :=
          (hint μ h hc hcs (hμ _ hcs (htsG.trans hGU))).measure_le_integral
            (Eventually.of_forall h0) fun x hx => (h1 x hx).ge
      _ = liminf (fun j => ENNReal.ofReal (∫ x, h x ∂(νs j))) atTop :=
          (((ENNReal.continuous_ofReal.tendsto _).comp
            (hconv h hc hcs (htsG.trans hGU))).liminf_eq).symm
      _ ≤ liminf (fun j => νs j G) atTop :=
          liminf_le_liminf (Eventually.of_forall fun j => integral_le_measure (fun x _ => hle1 x)
            fun x hx => (image_eq_zero_of_notMem_tsupport fun hx' => hx (htsG hx')).le)
  -- Step 4: open sets.  `G = ⋃ₙ Fₙ` with `Fₙ` closed and increasing, so `G` is exhausted by the
  -- increasing compact sets `Fₙ ∩ closedBall 0 n ⊆ G`; continuity from below and Step 3
  refine ⟨hK, fun G hG hGU => ?_⟩
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hCm : Monotone fun n : ℕ => F n ∩ closedBall (0 : Euclid P) n := fun m n hmn =>
    inter_subset_inter (hFm hmn) (closedBall_subset_closedBall (Nat.cast_le.mpr hmn))
  calc μ G ≤ μ (⋃ n : ℕ, F n ∩ closedBall (0 : Euclid P) n) := measure_mono fun x hx => by
        rw [← hFU] at hx
        obtain ⟨m, hm⟩ := mem_iUnion.mp hx
        obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
        exact mem_iUnion.mpr ⟨max m k, hFm (le_max_left m k) hm,
          mem_closedBall_zero_iff.mpr (hk.trans (Nat.cast_le.mpr (le_max_right m k)))⟩
    _ = ⨆ n : ℕ, μ (F n ∩ closedBall (0 : Euclid P) n) := hCm.measure_iUnion
    _ ≤ liminf (fun j => νs j G) atTop := iSup_le fun n =>
        hCG G hG hGU _ ((isCompact_closedBall 0 n).inter_left (hFc n))
          (inter_subset_left.trans (hFG n))
/-- A test form has bounded Euclidean coefficient norm: for `ω ∈ 𝒟ᵏ(U)` there is `M ≥ 0` with
`|ω(x)| ≤ M` for every `x` (Simon (6.1.15), `|ω|_U < ∞`).  The coefficient norm `|ω(x)|` is
continuous, as a square root of a finite sum of squares of evaluations of `ω(x)`, and vanishes
off `spt ω`, so it is continuous with compact support, hence bounded. -/
theorem Submission.cbr_rlim_coeffNorm_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ M : ℝ, 0 ≤ M ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M := by
  intro P k U ω
  obtain ⟨w, ⟨hws, hwcs⟩, -⟩ := ω
  change ∃ M : ℝ, 0 ≤ M ∧ ∀ x, covectorEuclideanNorm (w x) ≤ M
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  -- and vanishes off `spt w`, so it has compact support
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  -- hence it is bounded by some `M`, and by `max M 0`
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  exact ⟨max M 0, le_max_right _ _,
    fun x => ((Real.le_norm_self _).trans (hM x)).trans (le_max_left _ _)⟩
/-- **Smooth one-sided cut-off of a test form** (the `C^∞` version of the Lipschitz cut-off
`γ_ε ∘ f` in the proof of Simon 6.4.5(2)): for continuous `f`, `t` and `ε > 0` there is `χ` with
`0 ≤ χ ≤ 1`, `χ = 1` on `{f ≤ t - ε}` and `χ = 0` on `{f ≥ t}` such that `χ ω` is again a test
form in `U`.  The smooth Urysohn lemma for the closed set `{f ≤ t - ε}` inside the open set
`{f < t}` gives `χ`, and `χ ω` is smooth with `tsupport (χ ω) ⊆ tsupport ω ⊆ U` compact. -/
theorem Submission.cbr_rlim_smooth_cutoff : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k) (f : Euclid P → ℝ) (t ε : ℝ), Continuous f → 0 < ε → ∃ (χ : Euclid P → ℝ) (η : TestFormOn U k), (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, f x ≤ t - ε → χ x = 1) ∧ (∀ x, t ≤ f x → χ x = 0) := by
  intro P k U ω f t ε hf hε
  -- steps 1-2: a `C^∞` Urysohn function for the closed `{f ≤ t - ε}` inside the open `{f < t}`
  have hsub : {x | f x ≤ t - ε} ⊆ {x | f x < t} := fun x (hx : f x ≤ t - ε) =>
    show f x < t by linarith
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_lt hf continuous_const) (isClosed_le hf continuous_const) hsub
  -- step 3: `χ • ω` is smooth, compactly supported, with `tsupport (χ • ω) ⊆ tsupport ω ⊆ U`
  obtain ⟨⟨hω, hωc⟩, hωU⟩ := ω.2
  have hv : χ • (ω : DifferentialForm (Euclid P) k) ∈ testFormOnSubmodule U k :=
    ⟨⟨hχ.smul hω, hωc.smul_left⟩, (tsupport_smul_subset_right χ _).trans hωU⟩
  -- steps 4-5: `0 ≤ χ ≤ 1` from `range χ ⊆ [0, 1]`, and `χ = 1` exactly on `{f ≤ t - ε}`
  refine ⟨χ, ⟨_, hv⟩, fun x => rfl, fun x => hχr (mem_range_self x), fun x hx => (hχ1 x).1 hx,
    fun x hx => notMem_support.1 fun hx' => ?_⟩
  -- step 6: `t ≤ f x` puts `x` outside `support χ = {f < t}`
  rw [hχs] at hx'
  exact (not_lt.2 hx) hx'
/-- Cut-off error estimate for an admissible pair `(μ, ξ)` (`|ξ(x)(α)| ≤ |α|_E` for `μ`-a.e. `x`):
if `|ω|_E ≤ M`, `η = χ ω` with `0 ≤ χ ≤ 1`, `χ = 1` on `{f ≤ t − ε}` and `χ = 0` on `{f ≥ t}` (as
for the cut-off `γ_ε ∘ f` in the proof of Simon Ch. 6, 4.5(2)), then `∫_{f<t} ξ(ω) dμ` and
`∫ ξ(η) dμ` differ by at most `M μ(spt ω ∩ {t − ε < f < t})`.  Both integrands are bounded by
`M 1_{spt ω}`, and `1_{f<t} ξ(ω) − ξ(η) = (1_{f<t} − χ) ξ(ω)` vanishes off
`spt ω ∩ {t − ε < f < t}`. -/
theorem Submission.cbr_rlim_cutoff_error_le : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (ω η : TestFormOn U k) (χ f : Euclid P → ℝ) (t ε M : ℝ), Continuous f → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M) → (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x, f x ≤ t - ε → χ x = 1) → (∀ x, t ≤ f x → χ x = 0) → |(∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) - ∫ x, ξ x ((η : DifferentialForm (Euclid P) k) x) ∂μ| ≤ M * (μ (tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t})).toReal := by
  intro P k U μ ξ ω η χ f t ε M hf hμ hξm hξ hωM hη hχ hχ1 hχ0
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  have hηs := η.2.1.1
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  set v : DifferentialForm (Euclid P) k := (η : DifferentialForm (Euclid P) k)
  set C := tsupport w
  set S := {x | f x < t}
  set B := {x | t - ε < f x ∧ f x < t}
  -- Step 1: `M ≥ 0`.
  have hM : 0 ≤ M := (covectorEuclideanNorm_nonneg _).trans (hωM 0)
  -- Step 2: measurability and finiteness.
  have hCm : MeasurableSet C := (isClosed_tsupport w).measurableSet
  have hSm : MeasurableSet S := measurableSet_lt hf.measurable measurable_const
  have hBm : MeasurableSet B :=
    (measurableSet_lt measurable_const hf.measurable).inter
      (measurableSet_lt hf.measurable measurable_const)
  have hCf : μ C < ∞ := hμ C hωc hωU
  have hCBf : μ (C ∩ B) < ∞ := (measure_mono inter_subset_left).trans_lt hCf
  -- Step 3: `g = ξ(w)` and `h = ξ(v)` are a.e. strongly measurable.
  have hgm : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξm
      (ContDiff.continuous hωs).aestronglyMeasurable
  have hhm : AEStronglyMeasurable (fun x => ξ x (v x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξm
      (ContDiff.continuous hηs).aestronglyMeasurable
  -- Step 4: `|g| ≤ M` a.e., `g = 0` off `C`, so `g` is integrable.
  have hg0 : ∀ x, x ∉ C → ξ x (w x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, map_zero]
  have hgM : ∀ᵐ x ∂μ, |ξ x (w x)| ≤ M := by
    filter_upwards [hξ] with x hx
    exact (hx _).trans (hωM x)
  have hCi : Integrable (C.indicator fun _ => M) μ :=
    (integrable_indicator_iff hCm).2 (integrableOn_const hCf.ne)
  have hgi : Integrable (fun x => ξ x (w x)) μ := by
    refine hCi.mono' hgm ?_
    filter_upwards [hgM] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs]
      exact hx
    · rw [indicator_of_notMem hxC, hg0 x hxC, norm_zero]
  -- Step 5: `h = χ g`, so `h` is integrable.
  have hhg : ∀ x, ξ x (v x) = χ x * ξ x (w x) := fun x => by
    rw [hη x, map_smul, smul_eq_mul]
  have hhi : Integrable (fun x => ξ x (v x)) μ := by
    refine hgi.mono hhm (Eventually.of_forall fun x => ?_)
    rw [hhg x, norm_mul, Real.norm_eq_abs (χ x), abs_of_nonneg (hχ x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x).2
  -- Step 6: rewrite the difference as one integral.
  rw [← integral_indicator hSm, ← integral_sub (hgi.indicator hSm) hhi]
  -- Step 7: pointwise bound by `M 1_{C ∩ B}`.
  have hbd : ∀ᵐ x ∂μ, ‖S.indicator (fun x => ξ x (w x)) x - ξ x (v x)‖ ≤
      (C ∩ B).indicator (fun _ => M) x := by
    filter_upwards [hgM] with x hx
    have hnn : 0 ≤ (C ∩ B).indicator (fun _ => M) x := indicator_nonneg (fun _ _ => hM) x
    rw [hhg x]
    by_cases hxS : f x < t
    · rw [indicator_of_mem (show x ∈ S from hxS)]
      by_cases hxε : f x ≤ t - ε
      · rw [hχ1 x hxε, one_mul, sub_self, norm_zero]
        exact hnn
      · by_cases hxC : x ∈ C
        · rw [indicator_of_mem (show x ∈ C ∩ B from ⟨hxC, not_le.1 hxε, hxS⟩)]
          rw [← one_sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.2 (hχ x).2)]
          exact (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self 1 (hχ x).1)).trans hx
        · rw [hg0 x hxC, mul_zero, sub_zero, norm_zero]
          exact hnn
    · rw [indicator_of_notMem (show x ∉ S from hxS), hχ0 x (not_lt.1 hxS), zero_mul, sub_zero,
        norm_zero]
      exact hnn
  -- Step 8: integrate the majorant.
  have hmi : Integrable ((C ∩ B).indicator fun _ => M) μ :=
    (integrable_indicator_iff (hCm.inter hBm)).2 (integrableOn_const hCBf.ne)
  calc |∫ x, S.indicator (fun x => ξ x (w x)) x - ξ x (v x) ∂μ|
      = ‖∫ x, S.indicator (fun x => ξ x (w x)) x - ξ x (v x) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, (C ∩ B).indicator (fun _ => M) x ∂μ := norm_integral_le_of_norm_le hmi hbd
    _ = M * (μ (C ∩ B)).toReal := by
      rw [integral_indicator_const M (hCm.inter hBm), smul_eq_mul, measureReal_def, mul_comm]
/-- A thin level band of small measure: if `C` is measurable with `μ(C), ν(C) < ∞`, `f` is
continuous, `μ{f = t} = 0` and `δ > 0`, then some `ε > 0` has `μ(C ∩ {t − ε ≤ f ≤ t}) < δ` and
`ν(C ∩ {t − ε < f < t}) < δ`.  The closed bands of width `1/(n+1)` decrease into the `μ`-null set
`{f = t}` and the open ones decrease to `∅`, so by continuity from above both measures tend
to `0`. -/
theorem Submission.cbr_rlim_thin_band : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (C : Set (Euclid P)) (f : Euclid P → ℝ) (t δ : ℝ), MeasurableSet C → μ C < ∞ → ν C < ∞ → Continuous f → μ {x | f x = t} = 0 → 0 < δ → ∃ ε : ℝ, 0 < ε ∧ μ (C ∩ {x | t - ε ≤ f x ∧ f x ≤ t}) < ENNReal.ofReal δ ∧ ν (C ∩ {x | t - ε < f x ∧ f x < t}) < ENNReal.ofReal δ := by
  intro P μ ν C f t δ hC hμC hνC hf hμt hδ
  have hfm : Measurable f := hf.measurable
  -- the widths `1 / (n + 1)` decrease, so the closed and the open bands decrease in `n`
  have hr : Antitone fun n : ℕ => 1 / ((n : ℝ) + 1) := fun _ _ h => Nat.one_div_le_one_div h
  have hAm : Antitone fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t} :=
    fun _ _ h x hx => ⟨hx.1, (sub_le_sub_left (hr h) t).trans hx.2.1, hx.2.2⟩
  have hBm : Antitone fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t} :=
    fun _ _ h x hx => ⟨hx.1, (sub_le_sub_left (hr h) t).trans_lt hx.2.1, hx.2.2⟩
  -- the closed bands shrink into the `μ`-null level set `{f = t}`
  have hA0 : μ (⋂ n : ℕ, C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t}) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hμt
    rw [mem_iInter] at hx
    refine le_antisymm (hx 0).2.2 (le_of_not_gt fun hlt => ?_)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    linarith [(hx n).2.1]
  -- the open bands shrink to the empty set
  have hB0 : ν (⋂ n : ℕ, C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t}) = 0 := by
    refine measure_mono_null (fun x hx => ?_) measure_empty
    rw [mem_iInter] at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hx 0).2.2)
    exact absurd (hx n).2.1 (by linarith)
  -- continuity from above (the first bands have finite measure): eventually both band
  -- measures are below `δ`
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have hA := (tendsto_measure_iInter_atTop
    (s := fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t})
    (fun _ => (hC.inter ((measurableSet_le measurable_const hfm).inter
      (measurableSet_le hfm measurable_const))).nullMeasurableSet) hAm
    ⟨0, ((measure_mono inter_subset_left).trans_lt hμC).ne⟩).eventually_lt_const
    (hA0.trans_lt hδ')
  have hB := (tendsto_measure_iInter_atTop
    (s := fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t})
    (fun _ => (hC.inter ((measurableSet_lt measurable_const hfm).inter
      (measurableSet_lt hfm measurable_const))).nullMeasurableSet) hBm
    ⟨0, ((measure_mono inter_subset_left).trans_lt hνC).ne⟩).eventually_lt_const
    (hB0.trans_lt hδ')
  obtain ⟨N, hN⟩ := (hA.and hB).exists
  exact ⟨1 / ((N : ℝ) + 1), Nat.one_div_pos_of_nat, hN.1, hN.2⟩
/-- **Restriction to a sublevel set passes to weak limits** (the step of Simon Ch. 6, Remark
8.3(1), `T_j ⌞ {f < t} ⇀ T ⌞ {f < t}`, justified there "by an argument like that in 6.7(2) of
Ch. 2"): if `X_j ⇀ X` are represented by admissible pairs `(μ_j, ξ_j)`, `(μ_X, ξ_X)`, the
`μ_j` are dominated in the limit by `μ` on compact subsets of `U`, and `μ{f = t} = 0`, then
`∫_{f<t} ξ_j(ω) dμ_j → ∫_{f<t} ξ_X(ω) dμ_X` for every test form `ω`.  This is an `ε/3`
argument: with `|ω|_E ≤ M`, a thin band `{t − ε ≤ f ≤ t}` of `μ`- and `μ_X`-measure `< δ` on
`spt ω`, and the smooth cut-off `η = χ ω`, both restricted integrals are within `M δ` of
`X_j(η)` resp. `X(η)` (eventually in `j`, by the `limsup` bound on the compact band), and
`X_j(η) → X(η)`. -/
theorem Submission.cbr_sublevel_restriction_tendsto : ∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX)) := by
  intro P k U Xs X μs ξs μX μ ξX f t _ hf hconv hμs hξsm hξs hXs hμX hξXm hξX hX hμ hlim hμt ω
  obtain ⟨-, hωc⟩ := ω.2.1
  have hωU := ω.2.2
  -- step 1: `|ω|_E ≤ M` everywhere
  obtain ⟨M, hM, hωM⟩ := Submission.cbr_rlim_coeffNorm_bound P k U ω
  rw [Metric.tendsto_nhds]
  intro e he
  -- step 6: a band of width `ε` with `μ`- and `μ_X`-measure `< δ` on `spt ω`
  have hδ : 0 < e / (3 * (M + 1)) := div_pos he (by positivity)
  have hMδ : M * (e / (3 * (M + 1))) ≤ e / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨ε, hε, hband, hbandX⟩ := Submission.cbr_rlim_thin_band P μ μX
    (tsupport (ω : DifferentialForm (Euclid P) k)) f t (e / (3 * (M + 1)))
    (isClosed_tsupport _).measurableSet (hμ _ hωc hωU) (hμX _ hωc hωU) hf hμt hδ
  -- steps 3-4: the cut-off test form `η = χ ω`
  obtain ⟨χ, η, hη, hχ, hχ1, hχ0⟩ := Submission.cbr_rlim_smooth_cutoff P k U ω f t ε hf hε
  -- step 7: the closed band is a compact subset of `U`, so eventually `μ_j(band) < δ`
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε ≤ f x ∧ f x ≤ t}) :=
    IsCompact.inter_right hωc ((isClosed_le continuous_const hf).inter
      (isClosed_le hf continuous_const))
  have hev := eventually_lt_of_limsup_lt
    ((hlim _ hKc (inter_subset_left.trans hωU)).trans_lt hband)
  filter_upwards [hev, (hconv η).eventually (Metric.ball_mem_nhds (X η) (by positivity : 0 < e / 3))]
    with j hj hjη
  -- step 5: the cut-off errors for `(μ_j, ξ_j)` and `(μ_X, ξ_X)`, each at most `M δ ≤ e / 3`
  have hej := Submission.cbr_rlim_cutoff_error_le P k U (μs j) (ξs j) ω η χ f t ε M hf (hμs j)
    (hξsm j) (hξs j) hωM hη hχ hχ1 hχ0
  have heX := Submission.cbr_rlim_cutoff_error_le P k U μX ξX ω η χ f t ε M hf hμX hξXm hξX hωM
    hη hχ hχ1 hχ0
  have hsub : tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t} ⊆
      tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε ≤ f x ∧ f x ≤ t} :=
    fun x hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hbj : M * (μs j (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε < f x ∧ f x < t})).toReal ≤ e / 3 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal
      ((measure_mono hsub).trans_lt hj)).le hM).trans hMδ
  have hbX : M * (μX (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε < f x ∧ f x < t})).toReal ≤ e / 3 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hbandX).le hM).trans hMδ
  have h1 := abs_le.1 (hej.trans hbj)
  have h3 := abs_le.1 (heX.trans hbX)
  have h2 := abs_lt.1 (show |Xs j η - X η| < e / 3 from Metric.mem_ball.1 hjη)
  rw [hXs j η, hX η] at h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
/-- **Strip masses of an arbitrary set** (Simon Ch. 6, remark before 4.10: `M_W(T⌞{f < t})` is
increasing in `t`).  Put `F(s) = μ(G ∩ {a < f < min(s, b)})`, finite by hypothesis.  Then `F` is
nondecreasing, `F(b) − F(a) = μ(G ∩ {a < f < b})`, and `μ(G ∩ {t − h < f < t}) ≤ F(t) − F(t − h)`
because the strip `{t − h < f < t}` is open, hence measurable, and splits the possibly
non-measurable `G ∩ {a < f < t}` into `G ∩ {t − h < f < t}` and a superset of
`G ∩ {a < f < t − h}`. -/
theorem Submission.cbr_smm_strip_distribution_function : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ), Continuous f → μ (G ∩ {x | a < f x ∧ f x < b}) < ∞ → ∃ F : ℝ → ℝ, Monotone F ∧ ENNReal.ofReal (F b - F a) = μ (G ∩ {x | a < f x ∧ f x < b}) ∧ ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a), μ (G ∩ {x | t - h < f x ∧ f x < t}) ≤ ENNReal.ofReal (F t - F (t - h)) := by
  intro P μ f G a b hf hfin
  -- `G ∩ {a < f < s}` increases with `s` and has finite measure for `s ≤ b`
  have hmono : ∀ {s s' : ℝ}, s ≤ s' →
      G ∩ {x | a < f x ∧ f x < s} ⊆ G ∩ {x | a < f x ∧ f x < s'} :=
    fun hss' x hx => ⟨hx.1, hx.2.1, hx.2.2.trans_le hss'⟩
  have hfin' : ∀ {s : ℝ}, s ≤ b → μ (G ∩ {x | a < f x ∧ f x < s}) ≠ ∞ :=
    fun hs => ((measure_mono (hmono hs)).trans_lt hfin).ne
  refine ⟨fun s => (μ (G ∩ {x | a < f x ∧ f x < min s b})).toReal, ?_, ?_, ?_⟩
  · intro s s' hss'
    exact ENNReal.toReal_mono (hfin' (min_le_right _ _))
      (measure_mono (hmono (min_le_min_right b hss')))
  · simp only [min_self]
    rcases le_or_gt b a with hba | hab
    · -- `b ≤ a`: both sides vanish
      have hempty : G ∩ {x | a < f x ∧ f x < b} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => (hx.2.1.trans hx.2.2).not_ge hba
      rw [min_eq_right hba, sub_self, ENNReal.ofReal_zero, hempty, measure_empty]
    · -- `a < b`: `F a = μ ∅ = 0`
      have hempty : G ∩ {x | a < f x ∧ f x < a} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => (hx.2.1.trans hx.2.2).false
      rw [min_eq_left hab.le, hempty, measure_empty, ENNReal.toReal_zero, sub_zero,
        ENNReal.ofReal_toReal hfin.ne]
  · rintro t ⟨-, htb⟩ h ⟨hh0, hht⟩
    have hst : t - h ≤ b := by linarith
    simp only [min_eq_left htb.le, min_eq_left hst]
    -- the strip `{t - h < f < t}` is open, hence measurable; split `G ∩ {a < f < t}` along it
    have hS : MeasurableSet {x | t - h < f x ∧ f x < t} :=
      ((isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)).measurableSet
    have hinter : G ∩ {x | a < f x ∧ f x < t} ∩ {x | t - h < f x ∧ f x < t} =
        G ∩ {x | t - h < f x ∧ f x < t} :=
      Subset.antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx =>
        ⟨⟨hx.1, by linarith [hx.2.1], hx.2.2⟩, hx.2⟩
    have hdiff : G ∩ {x | a < f x ∧ f x < t - h} ⊆
        (G ∩ {x | a < f x ∧ f x < t}) \ {x | t - h < f x ∧ f x < t} :=
      fun x hx => ⟨hmono (by linarith) hx, fun hx' => hx.2.2.not_gt hx'.1⟩
    have key : μ (G ∩ {x | t - h < f x ∧ f x < t}) + μ (G ∩ {x | a < f x ∧ f x < t - h}) ≤
        μ (G ∩ {x | a < f x ∧ f x < t}) := by
      rw [← measure_inter_add_sdiff (G ∩ {x | a < f x ∧ f x < t}) hS, hinter]
      exact add_le_add le_rfl (measure_mono hdiff)
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin' htb.le),
      ENNReal.ofReal_toReal (hfin' hst)]
    exact ENNReal.le_sub_of_add_le_right (hfin' hst) key
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cbr_smm_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Simon Ch. 6, remark before 4.10** (integrated lower left Dini derivative).  For monotone
`F : ℝ → ℝ`, the lower integral over `(a, b)` of `D(t) = liminf_{h → 0+} (F(t) - F(t - h)) / h`
is at most `F(b) - F(a)`.  `F` is differentiable a.e. (Lebesgue), and at a point of
differentiability the left difference quotients tend to `F'(t)`, so `D = F'` a.e.  Changing the
integrand on a null set needs no measurability of `D`, and `∫_(a,b) F' ≤ F(b) - F(a)` is
`cmcs_smi_lintegral_ofReal_deriv_le`. -/
theorem Submission.cmcs_smi_lintegral_left_dini_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  -- `D = ofReal ∘ deriv F` at every point of differentiability, hence a.e.
  have hae : ∀ᵐ t, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) =
      ENNReal.ofReal (deriv F t) := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    have hlim : Tendsto (fun h : ℝ => (F t - F (t - h)) / h) (𝓝[>] 0) (𝓝 (deriv F t)) := by
      refine (ht.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]
      ring
    exact (ENNReal.tendsto_ofReal hlim).liminf_eq
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) := lintegral_congr_ae (ae_restrict_of_ae hae)
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_ofReal_deriv_le F a b hF

/-- **Simon Ch. 6, the remark deriving 4.10 from 4.9, for a measure on `ℝ`.**  For any measure
`ν` on `ℝ`, `∫⁻_{(a,b)} liminf_{h → 0+} h⁻¹ ν((t − h, t)) dt ≤ ν((a, b))` (Simon applies this to
`ν((s, t)) = M_W(T ⌞ {s < f < t})`).  When `ν((a, b)) < ∞`, `F(s) = ν((a, min s b))` is finite
and monotone, with `F a = 0` and `F b = ν((a, b))`.  For `0 < h < t − a`, additivity on
`(a, t − h) ∪ (t − h, t) ⊆ (a, t)` gives `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`, so the left
density is at most the lower left Dini derivative of `F`, whose integral
`cmcs_smi_lintegral_left_dini_le` bounds by `F b − F a`. -/
theorem Submission.cmcs_smi_lintegral_left_density_le : ∀ (ν : Measure ℝ) (a b : ℝ), ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤ ν (Ioo a b) := by
  intro ν a b
  by_cases hN : ν (Ioo a b) = ∞
  · rw [hN]
    exact le_top
  -- the distribution function `F(s) = ν((a, min s b))` of `ν` on `(a, b)`
  set F : ℝ → ℝ := fun s => (ν (Ioo a (min s b))).toReal with hFdef
  have hfin : ∀ s, ν (Ioo a (min s b)) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hN (measure_mono (Ioo_subset_Ioo_right (min_le_right s b)))
  have hFmono : Monotone F := fun s s' hss' =>
    ENNReal.toReal_mono (hfin s') (measure_mono (Ioo_subset_Ioo_right (min_le_min_right b hss')))
  have hofF : ∀ s, ENNReal.ofReal (F s) = ν (Ioo a (min s b)) := fun s =>
    ENNReal.ofReal_toReal (hfin s)
  have hFa : F a = 0 := by
    simp only [hFdef]
    rw [Ioo_eq_empty (not_lt.2 (min_le_left a b)), measure_empty, ENNReal.toReal_zero]
  have hFb : F b = (ν (Ioo a b)).toReal := by
    simp only [hFdef, min_self]
  -- the strip estimate: for `0 < h < t − a`, `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`
  have hstrip : ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a),
      ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t) ≤ ENNReal.ofReal ((F t - F (t - h)) / h) := by
    intro t ht h hh
    have hmt : min t b = t := min_eq_left ht.2.le
    have hmth : min (t - h) b = t - h := min_eq_left (by linarith [hh.1, ht.2])
    have hunion : ν (Ioo a (t - h)) + ν (Ioo (t - h) t) ≤ ν (Ioo a t) := by
      rw [← measure_union _ measurableSet_Ioo]
      · refine measure_mono (union_subset ?_ ?_)
        · exact Ioo_subset_Ioo_right (by linarith [hh.1])
        · exact Ioo_subset_Ioo_left (by linarith [hh.2])
      · rw [Set.disjoint_left]
        intro x hx1 hx2
        linarith [hx1.2, hx2.1]
    have hle : ν (Ioo (t - h) t) ≤ ENNReal.ofReal (F t - F (t - h)) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hofF, hofF, hmt, hmth]
      refine ENNReal.le_sub_of_add_le_left ?_ hunion
      rw [← hmth]
      exact hfin (t - h)
    calc ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)
        ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)) := mul_le_mul_right hle _
      _ = ENNReal.ofReal ((F t - F (t - h)) / h) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hh.1.le), div_eq_inv_mul]
  -- `(0, t − a) ∈ 𝓝[>] 0`, so the strip estimate compares the two liminfs on `(a, b)`
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤
        liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) := by
    intro t ht
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact hstrip t ht h hh
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_left_dini_le F a b hFmono
    _ = ν (Ioo a b) := by rw [hFb, hFa, sub_zero, ENNReal.ofReal_toReal hN]

/-- **Simon Ch. 6, 4.10** (integrated slice-mass bound, with `μ(W ∩ {a < f < s})` in place of
`M_W(T⌞{a < f < s})`): if `m(t) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})` for every
`t ∈ (a, b)`, then `∫⁻_{(a,b)} m ≤ L · μ(W ∩ {a < f < b})`.  The push-forward `ν = f_#(μ⌞W)` has
`ν((s, t)) = μ(W ∩ {s < f < t})`, so the hypothesis reads
`m(t) ≤ L · liminf_{h↓0} h⁻¹ ν((t − h, t))`; pull `L` out of the lower integral (`L ≠ ∞`) and bound
the integrated lower left density of `ν` by `ν((a, b))` (`cmcs_smi_lintegral_left_density_le`).
No measurability of `m` is needed. -/
theorem Submission.cmcs_slice_mass_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (W : Set (Euclid P)) (L : NNReal) (m : ℝ → ℝ≥0∞) (a b : ℝ), Measurable f → MeasurableSet W → (∀ t ∈ Ioo a b, m t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∫⁻ t in Ioo a b, m t ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by
  intro P μ f W L m a b hf _hW hm
  -- `ν = f_#(μ⌞W)`, so `ν((s, t)) = μ(f⁻¹(s, t) ∩ W) = μ(W ∩ {s < f < t})`
  set ν : Measure ℝ := (μ.restrict W).map f with hν
  have hνI : ∀ s t : ℝ, ν (Ioo s t) = μ (W ∩ {x | s < f x ∧ f x < t}) := by
    intro s t
    rw [hν, Measure.map_apply hf measurableSet_Ioo,
      Measure.restrict_apply (hf measurableSet_Ioo), Set.inter_comm]
    rfl
  calc ∫⁻ t in Ioo a b, m t
      ≤ ∫⁻ t in Ioo a b, (L : ℝ≥0∞) *
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => by simpa only [hνI] using hm t ht
    _ = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b,
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (L : ℝ≥0∞) * ν (Ioo a b) :=
        mul_le_mul_right (Submission.cmcs_smi_lintegral_left_density_le ν a b) _
    _ = (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by rw [hνI]

/-- **Simon Ch. 6, 4.6–4.10 (slicing by a Lipschitz function, pp. 157–158)**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')`: `A_t = T ⌞ {f < t}` and `B_t = (∂T) ⌞ {f < t}` (2.9, taken
through the given representations) are currents in `U`, and the slice `⟨T, f, t₋⟩ = ∂A_t − B_t`
(4.6) vanishes on forms supported off `{f = t}` (4.8), has
`M_W(⟨T, f, t₋⟩) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` (4.9), and
`∫⁻_{(a,b)} M_W(⟨T, f, t₋⟩) dt ≤ L · μ(W ∩ {a < f < b})` (4.10).  `A_t`, `B_t` are chosen by
`cmcs_restrict_current`; 4.8 is `cmcs_slice_support` (`f` is continuous); 4.9 is
`cmcs_slice_mass_pointwise`; 4.10 is `cmcs_slice_mass_integral` applied to `t ↦ M_W(∂A_t − B_t)`
and the bound 4.9 (`f` is measurable, `W` open hence measurable). -/
theorem Submission.cmc_slice_mass_bounds : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b})) := by
  intro P k U T μ μ' ξ ξ' f L _hU hμ hμ' hξm hξm' hξ hξ' hT hbT hf
  -- `A t = T ⌞ {f < t}` and `B t = (∂T) ⌞ {f < t}` (Simon 2.9)
  choose A hA using fun t : ℝ =>
    Submission.cmcs_restrict_current P (k + 1) U μ ξ {x | f x < t} hμ hξm hξ
  choose B hB using fun t : ℝ =>
    Submission.cmcs_restrict_current P k U μ' ξ' {x | f x < t} hμ' hξm' hξ'
  -- Simon 4.9, for every `W` and `t`
  have hpt : ∀ (W : Set (Euclid P)) (t : ℝ), ((A t).boundary - B t).massOn W ≤
      (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ *
        μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := fun W t =>
    Submission.cmcs_slice_mass_pointwise P k U T μ μ' ξ ξ' f L t (A t) (B t) W hμ hμ' hξm hξm'
      hξ hξ' hT hbT hf (hA t) (hB t)
  refine ⟨A, B, hA, hB, fun t η hη => ?_, fun W t _ => hpt W t, fun W a b hW => ?_⟩
  · -- Simon 4.8
    exact Submission.cmcs_slice_support P k U T μ μ' ξ ξ' f t (A t) (B t) hf.continuous hT hbT
      (hA t) (hB t) η hη
  · -- Simon 4.10, from 4.9 on `(a, b)`
    exact Submission.cmcs_slice_mass_integral P μ f W L
      (fun t => ((A t).boundary - B t).massOn W) a b hf.continuous.measurable hW.measurableSet
      fun t _ => hpt W t

/-- **Boundary rectifiability in `ℝᴾ` for compactly supported integer multiplicity currents**
(Simon Ch. 6, 6.2 first case and 6.3), from the deformation theorem (DTr) and the closure theorem
`CL_P(d)`: if `T ∈ 𝒟_{d+1}(ℝᴾ)` is integer multiplicity with compact support, `M(T) < ∞` and
`M(∂T) < ∞`, then `∂T` is integer multiplicity.  (DTr) with `ρ_k = 2⁻ᵏ` gives
`T - Q_k - S_k = ∂R_k` with `∂Q_k` integer multiplicity, `M(∂Q_k) ≤ c M(∂T)`,
`M(R_k) ≤ c ρ_k M(T)` and `M(S_k) ≤ c ρ_k M(∂T)`.  The evaluation bound by mass gives
`|Q_k(ω) - T(ω)| ≤ |S_k(ω)| + |R_k(dω)| ≤ ρ_k c (C_ω M(∂T) + C_{dω} M(T)) → 0`, so `Q_k ⇀ T` and
`∂Q_k ⇀ ∂T`.  Since `∂∂Q_k = 0` (and `∂ = 0` in degree `0`), `M_W(∂Q_k) + M_W(∂∂Q_k) ≤ c M(∂T)`
for every open `W`, and `CL_P(d)` in `U = ℝᴾ` shows that `∂T` is integer multiplicity. -/
theorem Submission.dtc_bc_tc_cl_bim_boundary_im_of_compact_support : (∀ (P m : ℕ), m + 1 < P → ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 0 < ρ → IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → ∀ (P d : ℕ), d + 1 < P → (∀ (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → IsIntegerMultiplicity T.boundary := by
  -- the zero current has zero local mass
  have massOn_zero_aux : ∀ {P m : ℕ} {U : Set (Euclid P)} (W : Set (Euclid P)),
      (0 : GeometricCurrentOn U m).massOn W = 0 := by
    intro P m U W
    apply le_antisymm _ bot_le
    apply sSup_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  -- `boundaryMassOn (∂Z) W = 0`: by definition in degree `0`, by `∂∂ = 0` otherwise
  have boundaryMassOn_boundary_aux : ∀ {P : ℕ} {U : Set (Euclid P)} (k : ℕ)
      (Z : GeometricCurrentOn U (k + 1)) (W : Set (Euclid P)), boundaryMassOn Z.boundary W = 0 := by
    intro P U k Z W
    cases k with
    | zero => rfl
    | succ m =>
      change Z.boundary.boundary.massOn W = 0
      rw [GeometricCurrentOn.boundary_boundary]
      exact massOn_zero_aux W
  intro hDTr P d hdP hCL T hT hTc hm hbm
  -- Steps 1–2: (DTr) with `ρ_k = (1/2)^k`
  obtain ⟨c, -, hc⟩ := hDTr P d hdP
  have hρ : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ k := fun k => by positivity
  choose Q R S _ hQb _ hEq _ _ hQbm hRm hSm _ _ using
    fun k => hc ((1 / 2 : ℝ) ^ k) T (hρ k) hT hTc hm hbm
  -- Step 3: a uniform bound for the Euclidean coefficient norm of a test form
  have hbound : ∀ {m : ℕ} (ω : TestFormOn (univ : Set (Euclid P)) m), ∃ C : ℝ, 0 < C ∧
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) ≤ C := by
    intro m ω
    have hω1 : IsSmoothForm (ω : DifferentialForm (Euclid P) m) := ω.property.1.1
    have hω2 : HasCompactSupport (ω : DifferentialForm (Euclid P) m) := ω.property.1.2
    have hωc : Continuous (ω : DifferentialForm (Euclid P) m) := hω1.continuous
    have hcont :
        Continuous fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) :=
      (Submission.rsd_mw_tfa_norm_props P m).2.2.2.comp hωc
    have hcs :
        HasCompactSupport fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) :=
      hω2.comp_left (g := fun α : Covector (Euclid P) m => covectorEuclideanNorm α)
        (covectorEuclideanNorm_zero P m)
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
    refine ⟨max C 1, lt_max_of_lt_right one_pos, fun x => ?_⟩
    exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC x).trans (le_max_left _ _))
  -- Step 4: `|Q_k(ω) - T(ω)| ≤ ρ_k A`, hence `Q_k ⇀ T`
  have hconv : WeaklyConvergesOn Q T := by
    intro ω
    obtain ⟨C₁, hC₁, hb₁⟩ := hbound ω
    obtain ⟨C₂, hC₂, hb₂⟩ := hbound (exteriorDerivativeTestOn univ (d + 1) ω)
    set A : ℝ≥0∞ := ENNReal.ofReal C₁ * ((c : ℝ≥0∞) * T.boundary.mass) +
      ENNReal.ofReal C₂ * ((c : ℝ≥0∞) * T.mass) with hA
    have hAfin : A ≠ ∞ := by
      rw [hA]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hbm.ne), ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top hm.ne)⟩
    have hkey : ∀ k, |Q k ω - T ω| ≤ (1 / 2 : ℝ) ^ k * A.toReal := by
      intro k
      have e : T ω - Q k ω - S k ω = R k (exteriorDerivativeTestOn univ (d + 1) ω) := by
        have := congrArg (fun Z : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1) => Z ω) (hEq k)
        exact this
      have hS :
          (S k).massOn univ ≤ (c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.boundary.mass :=
        hSm k
      have hR : (R k).massOn univ ≤ (c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.mass := hRm k
      have hSfin : (S k).massOn univ ≠ ∞ := ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hbm.ne) hS
      have hRfin : (R k).massOn univ ≠ ∞ := ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hm.ne) hR
      have h1 : ENNReal.ofReal |S k ω| ≤ ENNReal.ofReal C₁ * (S k).massOn univ := by
        have h := Submission.cmr_abs_apply_le_massOn P (d + 1) univ univ (S k) ω C₁ hSfin
          (subset_univ _) hb₁
        calc ENNReal.ofReal |S k ω| ≤ ENNReal.ofReal (C₁ * ((S k).massOn univ).toReal) :=
              ENNReal.ofReal_le_ofReal h
          _ = ENNReal.ofReal C₁ * (S k).massOn univ := by
              rw [ENNReal.ofReal_mul hC₁.le, ENNReal.ofReal_toReal hSfin]
      have h2 : ENNReal.ofReal |R k (exteriorDerivativeTestOn univ (d + 1) ω)| ≤
          ENNReal.ofReal C₂ * (R k).massOn univ := by
        have h := Submission.cmr_abs_apply_le_massOn P (d + 2) univ univ (R k)
          (exteriorDerivativeTestOn univ (d + 1) ω) C₂ hRfin (subset_univ _) hb₂
        calc ENNReal.ofReal |R k (exteriorDerivativeTestOn univ (d + 1) ω)| ≤
              ENNReal.ofReal (C₂ * ((R k).massOn univ).toReal) := ENNReal.ofReal_le_ofReal h
          _ = ENNReal.ofReal C₂ * (R k).massOn univ := by
              rw [ENNReal.ofReal_mul hC₂.le, ENNReal.ofReal_toReal hRfin]
      have hle : ENNReal.ofReal |Q k ω - T ω| ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * A := by
        have habs : |Q k ω - T ω| ≤ |S k ω| + |R k (exteriorDerivativeTestOn univ (d + 1) ω)| := by
          rw [← e]
          calc |Q k ω - T ω| = |-(S k ω) - (T ω - Q k ω - S k ω)| := by ring_nf
            _ ≤ |-(S k ω)| + |T ω - Q k ω - S k ω| := abs_sub _ _
            _ = |S k ω| + |T ω - Q k ω - S k ω| := by rw [abs_neg]
        calc ENNReal.ofReal |Q k ω - T ω|
            ≤ ENNReal.ofReal |S k ω| +
                ENNReal.ofReal |R k (exteriorDerivativeTestOn univ (d + 1) ω)| :=
              (ENNReal.ofReal_le_ofReal habs).trans ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal C₁ *
                ((c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.boundary.mass) +
              ENNReal.ofReal C₂ * ((c : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * T.mass) := by
              gcongr
              · exact h1.trans (by gcongr)
              · exact h2.trans (by gcongr)
          _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) * A := by rw [hA]; ring
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin) hle
      rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (hρ k).le] at this
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k * A.toReal) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const A.toReal
    exact squeeze_zero (fun k => dist_nonneg) (fun k => by rw [Real.dist_eq]; exact hkey k) hlim
  -- Steps 5–7: `∂Q_k ⇀ ∂T` with `M_W(∂Q_k) + M_W(∂∂Q_k) ≤ c M(∂T)`, then `CL_P(d)` in `ℝᴾ`
  refine hCL univ (fun k => (Q k).boundary) T.boundary isOpen_univ hQb ?_ hconv.boundary
  intro W _ _
  refine lt_of_le_of_lt (b := (c : ℝ≥0∞) * T.boundary.mass) (iSup_le fun k => ?_)
    (ENNReal.mul_lt_top ENNReal.coe_lt_top hbm)
  rw [boundaryMassOn_boundary_aux d (Q k) W, add_zero]
  exact ((Q k).boundary.massOn_mono (subset_univ W)).trans (hQbm k)
/-- **Left slopes at a point of differentiability** (Simon Ch. 6, 4.9 and (2) in the proof of
8.2).  If `F : ℝ → ℝ` is differentiable at `t`, then
`liminf_{h → 0+} ofReal (h⁻¹) * ofReal (F(t) - F(t - h)) ≤ ofReal (F′(t))`.  The left difference
quotients `h⁻¹ (F(t) - F(t - h))` tend to `F′(t)` as `h ↓ 0`; for `h > 0` the product above is
`ofReal` of the quotient, so it tends to `ofReal (F′(t))`, and along `𝓝[>] 0` the liminf of a
convergent function is its limit.  Monotonicity of `F` is not needed. -/
theorem Submission.cbr_smm_liminf_left_slope_le_deriv : ∀ (F : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ F t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h))) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv F t) := by
  intro F t hF
  -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
  have hlim : Tendsto (fun h : ℝ => h⁻¹ * (F t - F (t - h))) (𝓝[>] 0) (𝓝 (deriv F t)) := by
    refine (hF.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
    simp only [Function.comp_apply, smul_eq_mul]
    rw [← sub_eq_add_neg, inv_neg]
    ring
  -- for `h > 0`, `ofReal h⁻¹ * ofReal (F t - F (t - h)) = ofReal (h⁻¹ * (F t - F (t - h)))`
  have hlim' : Tendsto (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (deriv F t))) := by
    refine (ENNReal.tendsto_ofReal hlim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact ENNReal.ofReal_mul (inv_nonneg.2 hh.le)
  exact hlim'.liminf_eq.le

/-- **Fatou majorant from left difference quotients** (Simon Ch. 6, 4.9–4.10, integrated over a
sequence as in Remark 8.3(1)): if the `F_j` are nondecreasing and
`Z_j(t) ≤ L · liminf_{h↓0} h⁻¹ (F_j(t) − F_j(t − h))` on `(a, b)`, then `g = L · liminf_j F_j′`
is measurable, `liminf_j Z_j ≤ g` a.e. on `(a, b)`, and
`∫⁻_{(a,b)} g ≤ L · liminf_j (F_j(b) − F_j(a))`.  Wherever every `F_j` is differentiable (a.e.,
by Lebesgue's theorem) the left difference quotient tends to `F_j′`; the integral bound is
Fatou's lemma plus `∫⁻_{(a,b)} F_j′ ≤ F_j(b) − F_j(a)`. -/
theorem Submission.cbr_smm_monotone_majorant : ∀ (F : ℕ → ℝ → ℝ) (Z : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (L : NNReal), (∀ j, Monotone (F j)) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F j t - F j (t - h))) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (F j b - F j a)) atTop := by
  intro F Z a b L hF hZ
  -- the densities `d_j = F_j′` and `g = L · liminf_j d_j` are measurable
  have hd : ∀ j, Measurable fun t => ENNReal.ofReal (deriv (F j) t) :=
    fun j => (measurable_deriv (F j)).ennreal_ofReal
  have hlim : Measurable fun t => liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop :=
    Measurable.liminf hd
  refine ⟨fun t => (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop,
    hlim.const_mul _, ?_, ?_⟩
  · -- a.e. every `F_j` is differentiable, and there `Z_j ≤ L · d_j`
    have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j, DifferentiableAt ℝ (F j) t :=
      ae_all_iff.2 fun j => (hF j).ae_differentiableAt
    filter_upwards [hdiff] with t ht htab
    have hle : ∀ j, Z j t ≤ (L : ℝ≥0∞) * ENNReal.ofReal (deriv (F j) t) := fun j =>
      (hZ j t htab).trans
        (by gcongr; exact Submission.cbr_smm_liminf_left_slope_le_deriv (F j) t (ht j))
    calc liminf (fun j => Z j t) atTop
        ≤ liminf (fun j => (L : ℝ≥0∞) * ENNReal.ofReal (deriv (F j) t)) atTop :=
          liminf_le_liminf (Eventually.of_forall hle)
      _ = (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop :=
          ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top
  · -- Fatou's lemma, then `∫⁻_{(a,b)} F_j′ ≤ F_j(b) − F_j(a)` for each `j`
    calc ∫⁻ t in Ioo a b, (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop
        = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b, liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop :=
          lintegral_const_mul _ hlim
      _ ≤ (L : ℝ≥0∞) * liminf (fun j => ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv (F j) t)) atTop := by
          gcongr
          exact lintegral_liminf_le hd
      _ ≤ (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (F j b - F j a)) atTop := by
          gcongr
          exact liminf_le_liminf (Eventually.of_forall fun j =>
            Submission.cbr_smm_lintegral_ofReal_deriv_le (F j) a b (hF j))

/-- **Measurable majorant for slice masses** (Simon Ch. 6, 4.9–4.10 and the sentence between
them, in the sequence form used for Remark 8.3(1)).  For each `j` let `F_j` be the distribution
function of the strip masses of `G` (`cbr_smm_strip_distribution_function`): `F_j` is monotone,
`F_j(b) − F_j(a) = μ_j(G ∩ {a < f < b})` and `μ_j(G ∩ {t − h < f < t}) ≤ F_j(t) − F_j(t − h)` for
`0 < h < t − a`, i.e. eventually as `h ↓ 0`.  So the bound on `Z_j` passes to the left difference
quotients of `F_j`, and `cbr_smm_monotone_majorant` gives `g`. -/
theorem Submission.cbr_slice_mass_majorant : ∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop := by
  intro P μs f G a b L Z hf hfin hZ
  -- the distribution functions `F_j` of the strip masses
  choose F hFmono hFab hFstrip using fun j =>
    Submission.cbr_smm_strip_distribution_function P (μs j) f G a b hf (hfin j)
  -- for `0 < h < t − a` (a neighbourhood of `0⁺`) the strip mass is at most `F_j(t) − F_j(t − h)`
  have hZF : ∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) *
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F j t - F j (t - h))) (𝓝[>] 0) := by
    intro j t ht
    refine (hZ j t ht).trans (mul_le_mul_right (liminf_le_liminf ?_) _)
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact mul_le_mul_right (hFstrip j t ht h hh) _
  obtain ⟨g, hg, hgae, hgint⟩ := Submission.cbr_smm_monotone_majorant F Z a b L hFmono hZF
  -- `F_j(b) − F_j(a) = μ_j(G ∩ {a < f < b})`
  refine ⟨g, hg, hgae, hgint.trans_eq ?_⟩
  simp only [hFab]
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
/-- **Simon Ch. 6, 3.1–3.2** (the weight `θHᵏ⌞M`): for an integer multiplicity triple
`R = (M, θ, ξ)` in `W`, `R.measure = (Hᵏ⌞M).withDensity θ` has the same null sets as `Hᵏ⌞M`
(`θ` is measurable and `θ ≥ 1` on `M`).  For Borel `A`, `R.measure(A) = ∫_{M ∩ A} θ dHᵏ`; hence
`R.measure(ℝᴾ \ M) = 0`, and `R.measure(K) < ∞` for compact `K ⊆ W` by local integrability of
`θ`.  Absolute continuity makes `ξ` a.e. strongly measurable for `R.measure`, and
`R.action ω = ∫_M θ⟨ω, ξ⟩ dHᵏ = ∫ ⟨ω, ξ⟩ dR.measure` for every form `ω`. -/
theorem Submission.cbr_imRep_measure_basic : ∀ (P k : ℕ) (W : Set (Euclid P)) (R : IMRep W k), R.measure ≪ μHE[k].restrict R.carrier ∧ μHE[k].restrict R.carrier ≪ R.measure ∧ (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ x in R.carrier ∩ A, (R.mult x : ℝ≥0∞) ∂μHE[k]) ∧ R.measure R.carrierᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → R.measure K < ∞) ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ ω : DifferentialForm (Euclid P) k, R.action ω = ∫ x, R.orient x (ω x) ∂R.measure := by
  intro P k W R
  -- the density `θ`, as an `ℝ≥0`-valued measurable function
  have hθ : Measurable fun x => (R.mult x : NNReal) := measurable_from_nat.comp R.measurable_mult
  -- (a) a measure with density is absolutely continuous w.r.t. its base measure
  have hac : R.measure ≪ μHE[k].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- (c) `μ(A) = ∫_A θ d(Hᵏ⌞M) = ∫_{M ∩ A} θ dHᵏ` for Borel `A`
  have happly : ∀ A : Set (Euclid P), MeasurableSet A →
      R.measure A = ∫⁻ x in R.carrier ∩ A, (R.mult x : ℝ≥0∞) ∂μHE[k] := fun A hA => by
    rw [IMRep.measure, withDensity_apply _ hA, Measure.restrict_restrict hA, inter_comm A]
  refine ⟨hac, ?_, happly, ?_, fun K hK hKW => ?_, R.aestronglyMeasurable_orient.mono_ac hac,
    fun ω => ?_⟩
  -- (b) `θ ≠ 0` on `M`, hence `Hᵏ⌞M`-a.e.
  · refine withDensity_absolutelyContinuous'
      (measurable_from_nat.comp R.measurable_mult).aemeasurable ?_
    filter_upwards [ae_restrict_mem R.measurableSet_carrier] with x hx
    exact Nat.cast_ne_zero.2 (R.mult_pos x hx).ne'
  -- (d) `M ∩ Mᶜ = ∅`
  · rw [happly _ R.measurableSet_carrier.compl, inter_compl_self, Measure.restrict_empty,
      lintegral_zero_measure]
  -- (e) local integrability of `θ`
  · rw [happly K hK.measurableSet]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult K hK hKW)
  -- (g) `∫ ⟨ω, ξ⟩ d(θ Hᵏ⌞M) = ∫_M θ ⟨ω, ξ⟩ dHᵏ`
  · have h := integral_withDensity_eq_integral_smul (μ := μHE[k].restrict R.carrier) hθ
      fun x => R.orient x (ω x)
    simp only [ENNReal.coe_natCast] at h
    rw [IMRep.measure, h, IMRep.action]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [NNReal.smul_def]

/-- **Countable disjoint Borel refinement of a local open cover** (Lindelöf): if every point of
`U ⊆ ℝᴾ` has an open neighbourhood `W ⊆ U` with property `p`, then countably many such sets `Wᵢ`
cover `U` (`ℝᴾ` is second countable), and the pieces `Aᵢ = Wᵢ \ ⋃_{j<i} Wⱼ` are pairwise disjoint
Borel sets with `Aᵢ ⊆ Wᵢ` and `⋃ᵢ Aᵢ = U`.  The index type is empty when `U = ∅`. -/
theorem Submission.cbrg_exists_countable_disjoint_refinement : ∀ (P : ℕ) (U : Set (Euclid P)) (p : Set (Euclid P) → Prop), (∀ x ∈ U, ∃ W : Set (Euclid P), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ p W) → ∃ (ι : Type) (_ : Countable ι) (W A : ι → Set (Euclid P)), (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ U) ∧ (∀ i, p (W i)) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i, A i ⊆ W i) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧ ⋃ i, A i = U := by
  intro P U p h
  choose! V hVo hxV hVU hpV using h
  let s : U → Set (Euclid P) := fun x => V x
  -- Lindelöf: countably many of the open sets `s x` already cover `⋃ x, s x = U`
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable s (fun x => hVo x x.2)
  have hsU : ⋃ x, s x = U := by
    apply subset_antisymm
    · exact iUnion_subset fun x => hVU x x.2
    · intro y hy
      exact mem_iUnion.2 ⟨⟨y, hy⟩, hxV y hy⟩
  rcases T.eq_empty_or_nonempty with hT | hT
  · -- `T = ∅` forces `U = ∅`: take the empty index type
    have hU : U = ∅ := by
      rw [← hsU, ← hTU, hT]
      simp
    refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim, fun i => i.elim,
      fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    rw [hU]
    exact iUnion_of_empty _
  · -- enumerate `T = range f` and disjointify `Wₙ = s (f n)`
    obtain ⟨f, hf⟩ := hTc.exists_eq_range hT
    let W : ℕ → Set (Euclid P) := fun n => s (f n)
    refine ⟨ℕ, inferInstance, W, disjointed W, fun n => hVo _ (f n).2, fun n => hVU _ (f n).2,
      fun n => hpV _ (f n).2, MeasurableSet.disjointed (fun n => (hVo _ (f n).2).measurableSet),
      disjointed_subset W, disjoint_disjointed W, ?_⟩
    rw [iUnion_disjointed, ← hsU, ← hTU, hf, biUnion_range]
/-- **Orientation is local** (Simon Ch. 6, 3.1; Ch. 3, 1.4).  Assume (IMC)(a): for Borel
`M ⊆ M' ⊆ U`, `U` open, with `Hⁿ(M' ∩ K) < ∞` for compact `K ⊆ U`, the approximate tangent
spaces of `M` and `M'` agree `Hⁿ`-a.e. on `M`.  Let `Nᵢ ⊆ Mᵢ` (`i` in a countable type) be Borel
pieces of the carriers of integer multiplicity triples `Rᵢ = (Mᵢ, θᵢ, ξᵢ)` in open `Wᵢ`, with
`M = ⋃ᵢ Nᵢ ⊆ U`, `Hᵏ(M ∩ K) < ∞` for compact `K ⊆ U`, and `ξ = ξᵢ` `Hᵏ`-a.e. on `Nᵢ`.  Then `ξ`
orients an approximate tangent space of `M` `Hᵏ`-a.e. on `M`: `Hᵏ`-a.e. on `Nᵢ`, `ξ = ξᵢ` orients
`TₓMᵢ = TₓNᵢ = TₓM`, by (IMC)(a) in `Wᵢ` (`Hᵏ⌞Mᵢ` is locally finite in `Wᵢ`) and in `U`. -/
theorem Submission.cbrg_ae_orient_iUnion : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W N : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, MeasurableSet (N i)) → (∀ i, N i ⊆ (R i).carrier) → (⋃ i, N i) ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[k] ((⋃ i, N i) ∩ K) ≠ ∞) → (∀ i, ∀ᵐ y ∂(μHE[k].restrict (N i)), ξ y = (R i).orient y) → ∀ᵐ x ∂(μHE[k].restrict (⋃ i, N i)), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ i, N i) x Q ∧ IsUnitOrientationOf (ξ x) Q := by
  intro hIMC ι _ P k U W N R ξ hU hWo hNm hNR hNU hfinN hξ
  -- `M = ⋃ᵢ Nᵢ` is a countable union: it suffices to work `Hᵏ`-a.e. on each piece `Nᵢ`
  rw [ae_restrict_iUnion_iff]
  intro i
  have hMm : MeasurableSet (⋃ j, N j) := MeasurableSet.iUnion hNm
  -- (α) `ξᵢ` orients an approximate tangent space of `Mᵢ`, a.e. on `Nᵢ ⊆ Mᵢ`
  have hα : ∀ᵐ x ∂(μHE[k].restrict (N i)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (R i).carrier x Q ∧ IsUnitOrientationOf ((R i).orient x) Q :=
    ae_restrict_of_ae_restrict_of_subset (hNR i) (R i).orients
  -- (γ) (IMC)(a) in `Wᵢ` for `Nᵢ ⊆ Mᵢ ⊆ Wᵢ`, `Hᵏ⌞Mᵢ` being locally finite in `Wᵢ`
  have hγ := hIMC P k (W i) (N i) (R i).carrier (hWo i) (hNm i) (R i).measurableSet_carrier
    (hNR i) (R i).carrier_subset
    (fun K hK hKW => (Submission.rsd_imrep_compact_measure_ne_top P k (W i) (R i) K hK hKW).1)
  -- (δ) (IMC)(a) in `U` for `Nᵢ ⊆ M ⊆ U`
  have hδ := hIMC P k U (N i) (⋃ j, N j) hU (hNm i) hMm (subset_iUnion N i) hNU hfinN
  -- (β) `ξ = ξᵢ` a.e. on `Nᵢ`; then `TₓMᵢ = TₓNᵢ = TₓM` is oriented by `ξ(x) = ξᵢ(x)`
  filter_upwards [hα, hγ, hδ, hξ i] with x hxα hxγ hxδ hxξ
  obtain ⟨Q, hQ, hQo⟩ := hxα
  refine ⟨Q, (hxδ Q).1 ((hxγ Q).2 hQ), ?_⟩
  rw [hxξ]
  exact hQo

/-- **Gluing integer multiplicity triples over disjoint pieces** (Simon Ch. 6, 3.1).  Assume
(IMC)(a), as in `cbrg_ae_orient_iUnion`.  Let `Rᵢ = (Mᵢ, θᵢ, ξᵢ)` (`i` in a countable type) be
integer multiplicity triples in open `Wᵢ ⊆ U`, and `Aᵢ` pairwise disjoint Borel sets.  Let `μ` be
carried by `⋃ᵢ Aᵢ`, with `μ⌞Aᵢ = (θᵢHᵏ⌞Mᵢ)⌞Aᵢ` and `μ(K) < ∞` for compact `K ⊆ U`, and let `ξ` be
`μ`-measurable with `ξ = ξᵢ` `Hᵏ`-a.e. on `Mᵢ ∩ Aᵢ`.  Then `M = ⋃ᵢ Mᵢ ∩ Aᵢ`, with `θ = θᵢ` on `Aᵢ`
(`0` off `⋃ᵢ Aᵢ`) and orientation `ξ`, is an integer multiplicity triple in `U` of weight `μ`:
`θHᵏ⌞M = Σᵢ (θᵢHᵏ⌞Mᵢ)⌞Aᵢ = μ`, so `θ` is locally integrable, `Hᵏ⌞M` is locally finite and
`Hᵏ⌞M ≪ μ`, and `ξ` orients `M` a.e. by `cbrg_ae_orient_iUnion`. -/
theorem Submission.cbrg_imRep_glue_disjoint : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (ι : Type) [Countable ι] (P k : ℕ) (U : Set (Euclid P)) (W A : ι → Set (Euclid P)) (R : (i : ι) → IMRep (W i) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → (∀ i, IsOpen (W i)) → (∀ i, W i ⊆ U) → (∀ i, MeasurableSet (A i)) → Pairwise (fun i j => Disjoint (A i) (A j)) → μ (⋃ i, A i)ᶜ = 0 → (∀ i, μ.restrict (A i) = (R i).measure.restrict (A i)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ i, ∀ᵐ y ∂(μHE[k].restrict ((R i).carrier ∩ A i)), ξ y = (R i).orient y) → ∃ R' : IMRep U k, R'.carrier = ⋃ i, (R i).carrier ∩ A i ∧ R'.orient = ξ ∧ R'.measure = μ := by
  classical
  intro hIMC ι _ P k U W A R μ ξ hU hWo hWU hAm hAd hAc hμA hfin hξm hξ
  -- pieces `Nᵢ = Mᵢ ∩ Aᵢ` and multiplicities `mᵢ = θᵢ`
  let N : ι → Set (Euclid P) := fun i => (R i).carrier ∩ A i
  let m : ι → Euclid P → ℕ := fun i => (R i).mult
  -- glued multiplicity: `θ = θᵢ` on `Aᵢ`, `0` off `⋃ᵢ Aᵢ`
  let θ : Euclid P → ℕ := fun x => if h : ∃ i, x ∈ A i then m h.choose x else 0
  have hθA : ∀ i, ∀ x ∈ A i, θ x = (R i).mult x := by
    intro i x hx
    have h : ∃ j, x ∈ A j := ⟨i, hx⟩
    have hj : h.choose = i := by
      by_contra hne
      exact (Set.disjoint_left.1 (hAd hne)) h.choose_spec hx
    show (if h' : ∃ j, x ∈ A j then m h'.choose x else 0) = m i x
    rw [dite_eq_left h, hj]
  have hθ0 : ∀ x, (¬ ∃ i, x ∈ A i) → θ x = 0 := by
    intro x hx
    show (if h' : ∃ j, x ∈ A j then m h'.choose x else 0) = 0
    rw [dite_eq_right hx]
  -- the carrier `M = ⋃ᵢ Nᵢ` is Borel and lies in `U`
  have hNm : ∀ i, MeasurableSet (N i) := fun i => (R i).measurableSet_carrier.inter (hAm i)
  have hMm : MeasurableSet (⋃ i, N i) := MeasurableSet.iUnion hNm
  have hMU : (⋃ i, N i) ⊆ U :=
    iUnion_subset fun i => inter_subset_left.trans ((R i).carrier_subset.trans (hWU i))
  -- `θ` is measurable: its fibres are Borel
  have hθm : Measurable θ := by
    refine measurable_to_countable' fun n => ?_
    have hpre : θ ⁻¹' {n} = (⋃ i, A i ∩ (R i).mult ⁻¹' {n}) ∪ ((⋃ i, A i)ᶜ ∩ {_x | 0 = n}) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_iUnion, mem_inter_iff,
        mem_compl_iff, mem_ofPred_eq]
      constructor
      · intro hx
        by_cases h : ∃ i, x ∈ A i
        · obtain ⟨i, hi⟩ := h
          exact Or.inl ⟨i, hi, by rw [← hθA i x hi]; exact hx⟩
        · exact Or.inr ⟨h, by rw [← hθ0 x h]; exact hx⟩
      · rintro (⟨i, hi, hx⟩ | ⟨h, hn⟩)
        · rw [hθA i x hi]; exact hx
        · rw [hθ0 x h]; exact hn
    rw [hpre]
    refine (MeasurableSet.iUnion fun i =>
      (hAm i).inter ((R i).measurable_mult (measurableSet_singleton n))).union
      ((MeasurableSet.iUnion hAm).compl.inter ?_)
    by_cases hn : 0 = n
    · simp [hn]
    · simp [hn]
  -- `θ ≥ 1` on `M`
  have hθpos : ∀ x ∈ ⋃ i, N i, 0 < θ x := by
    intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
    rw [hθA i x hxi.2]
    exact (R i).mult_pos x hxi.1
  -- `M` is countably `k`-rectifiable (reindex the pieces by `ℕ`)
  have hMrect : CountablyRectifiable k (⋃ i, N i) := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · rw [iUnion_of_empty]
      exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
    · obtain ⟨s, hs⟩ := exists_surjective_nat ι
      rw [← hs.iUnion_comp N]
      exact Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _
        fun n => (R (s n)).rectifiable.mono inter_subset_left
  -- `μ = Σᵢ μ⌞Aᵢ = Σᵢ (θᵢHᵏ⌞Mᵢ)⌞Aᵢ`
  have hμsum : μ = Measure.sum (fun i => ((R i).measure).restrict (A i)) := by
    have h1 : μ.restrict (⋃ i, A i) = μ := by
      refine Measure.restrict_eq_self_of_ae_mem ?_
      rw [ae_iff]
      simpa [compl_def] using hAc
    calc μ = μ.restrict (⋃ i, A i) := h1.symm
      _ = Measure.sum (fun i => μ.restrict (A i)) := Measure.restrict_iUnion hAd hAm
      _ = Measure.sum (fun i => ((R i).measure).restrict (A i)) := by
          congr 1
          funext i
          exact hμA i
  -- the measure identity `θHᵏ⌞M = μ`
  have hmeas : (μHE[k].restrict (⋃ i, N i)).withDensity (fun x => (θ x : ℝ≥0∞)) = μ := by
    have hNd : Pairwise (fun i j => Disjoint (N i) (N j)) :=
      fun i j hij => (hAd hij).mono inter_subset_right inter_subset_right
    rw [hμsum, Measure.restrict_iUnion hNd hNm, withDensity_sum]
    congr 1
    funext i
    rw [IMRep.measure, restrict_withDensity (hAm i), Measure.restrict_restrict (hAm i),
      inter_comm (A i)]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem (hNm i)] with x hx
    rw [hθA i x hx.2]
  -- local integrability of `θ`: `∫_{M ∩ K} θ dHᵏ = μ(K) < ∞`
  have hlint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] ≠ ∞ := by
    intro K hK hKU
    have h1 : ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] =
        ((μHE[k].restrict (⋃ i, N i)).withDensity (fun x => (θ x : ℝ≥0∞))) K := by
      rw [withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet,
        inter_comm]
    rw [h1, hmeas]
    exact (hfin K hK hKU).ne
  -- local finiteness of `Hᵏ⌞M`: `Hᵏ(M ∩ K) ≤ ∫_{M ∩ K} θ dHᵏ`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[k] ((⋃ i, N i) ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hlint K hK hKU) ?_
    calc μHE[k] ((⋃ i, N i) ∩ K) = ∫⁻ _ in (⋃ i, N i) ∩ K, (1 : ℝ≥0∞) ∂μHE[k] := by
          rw [setLIntegral_one]
      _ ≤ ∫⁻ x in (⋃ i, N i) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] := by
          refine setLIntegral_mono (measurable_from_nat.comp hθm) ?_
          intro x hx
          exact_mod_cast hθpos x hx.1
  -- `Hᵏ⌞M ≪ θHᵏ⌞M = μ`, so `ξ` is `Hᵏ⌞M`-measurable
  have hac : μHE[k].restrict (⋃ i, N i) ≪ μ := by
    rw [← hmeas]
    refine withDensity_absolutelyContinuous' (measurable_from_nat.comp hθm).aemeasurable ?_
    filter_upwards [ae_restrict_mem hMm] with x hx
    exact_mod_cast (hθpos x hx).ne'
  have hξM : AEStronglyMeasurable ξ (μHE[k].restrict (⋃ i, N i)) := hξm.mono_ac hac
  -- orientation: `ξ` orients `M` a.e., by `cbrg_ae_orient_iUnion` for the pieces `Nᵢ ⊆ Mᵢ`
  have horient := Submission.cbrg_ae_orient_iUnion hIMC ι P k U W N R ξ hU hWo hNm
    (fun i => inter_subset_left) hMU hMfin hξ
  exact ⟨{ carrier := ⋃ i, N i
           mult := θ
           orient := ξ
           measurableSet_carrier := hMm
           carrier_subset := hMU
           rectifiable := hMrect
           measurable_mult := hθm
           mult_pos := hθpos
           locallyIntegrable_mult := hlint
           aestronglyMeasurable_orient := hξM
           orients := horient }, rfl, rfl, hmeas⟩
/-- Restricted representing integrals are determined by the represented current (closure theorem,
Simon Ch. 6, 8.2–8.3, as used for 7.2.4): if `∫ ⟨ω, ξ₁⟩ dμ₁ = ∫ ⟨ω, ξ₂⟩ dμ₂ + ∫ ⟨ω, ξ₃⟩ dμ₃` for
every `ω ∈ 𝒟ᵏ(U)`, the same identity holds for the integrals over every Borel set `B`.  For fixed
`ω` the integrands are integrable (bounded by `|ω|`, which vanishes off the compact `spt ω ⊆ U`).
Testing the hypothesis with `gω`, `g` smooth, and letting `g = (1 - f)ʲ ↓ 𝟙_F` (`f` smooth,
`0 ≤ f ≤ 1`, with support `ℝᴾ \ F`) gives the identity on closed sets `F` by dominated
convergence; Dynkin's π-λ theorem extends it to all Borel sets. -/
theorem Submission.cbr_setIntegral_eq_of_integral_eq : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ₁ μ₂ μ₃ : Measure (Euclid P)) (ξ₁ ξ₂ ξ₃ : Euclid P → MultiVector P k), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₁ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₂ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ₃ K < ∞) → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → AEStronglyMeasurable ξ₃ μ₃ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₃, ∀ α : Covector (Euclid P) k, |ξ₃ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, ∫ x, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃) → ∀ (B : Set (Euclid P)) (ω : TestFormOn U k), MeasurableSet B → ∫ x in B, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in B, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂ + ∫ x in B, ξ₃ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₃ := by
  intro P k U μ₁ μ₂ μ₃ ξ₁ ξ₂ ξ₃ _hU hμ₁ hμ₂ hμ₃ hξ₁ hξ₂ hξ₃ hb₁ hb₂ hb₃ heq B ω hB
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  have hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := ω.property.1.1
  have hwc : HasCompactSupport w := ω.property.1.2
  have hwU : tsupport w ⊆ U := ω.property.2
  -- Step 1: `x ↦ ξ x (w x)` is integrable: it vanishes off the compact set `tsupport w ⊆ U` and
  -- is bounded by `sup |w|`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖covectorEuclideanNorm (w x)‖ ≤ C := by
    refine Continuous.bounded_above_of_compact_support ?_
      (hwc.comp_left (g := fun α : Covector (Euclid P) k => covectorEuclideanNorm α)
        (covectorEuclideanNorm_zero P k))
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    exact Continuous.if_const _ ((hws.continuous.eval_const _).pow 2) continuous_const
  have hint : ∀ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k),
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ →
      (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) →
      Integrable (fun x => ξ x (w x)) μ := by
    intro μ ξ hμ hξ hb
    have hsupp : support (fun x => ξ x (w x)) ⊆ tsupport w := by
      intro x hx
      by_contra hxw
      exact hx (by simp [image_eq_zero_of_notMem_tsupport hxw])
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    refine Measure.integrableOn_of_bounded (M := C) (hμ _ hwc hwU).ne
      (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξ
        hws.continuous.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_of_ae hb] with x hx
    rw [Real.norm_eq_abs]
    exact (hx (w x)).trans ((le_abs_self _).trans ((Real.norm_eq_abs _) ▸ hC x))
  have hi₁ := hint μ₁ ξ₁ hμ₁ hξ₁ hb₁
  have hi₂ := hint μ₂ ξ₂ hμ₂ hξ₂ hb₂
  have hi₃ := hint μ₃ ξ₃ hμ₃ hξ₃ hb₃
  -- Step 2: testing the hypothesis with the test form `g • w`, `g` smooth.
  have hmul : ∀ g : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      ∫ x, g x * ξ₁ x (w x) ∂μ₁ = ∫ x, g x * ξ₂ x (w x) ∂μ₂ + ∫ x, g x * ξ₃ x (w x) ∂μ₃ := by
    intro g hg
    have hmem : (fun x => g x • w x) ∈ testFormOnSubmodule U k :=
      ⟨⟨hg.smul hws, hwc.mono' ((subset_tsupport _).trans (tsupport_smul_subset_right g w))⟩,
        (tsupport_smul_subset_right g w).trans hwU⟩
    simpa only [Submodule.coe_mk, map_smul, smul_eq_mul] using heq ⟨fun x => g x • w x, hmem⟩
  -- Step 3: closed sets, by smooth approximation of the indicator and dominated convergence.
  have hclosed : ∀ F : Set (Euclid P), IsClosed F →
      ∫ x in F, ξ₁ x (w x) ∂μ₁ = ∫ x in F, ξ₂ x (w x) ∂μ₂ + ∫ x in F, ξ₃ x (w x) ∂μ₃ := by
    intro F hF
    obtain ⟨f, hfs, hfd, hfr⟩ := hF.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
    have hgd : ∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (1 - f x) ^ n) :=
      fun n => (contDiff_const.sub hfd).pow n
    have hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := fun x => hfr ⟨x, rfl⟩
    have hgb : ∀ (n : ℕ) x, ‖(1 - f x) ^ n‖ ≤ 1 := by
      intro n x
      rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hf01 x).2])]
      exact pow_le_one₀ (by linarith [(hf01 x).2]) (by linarith [(hf01 x).1])
    have hlim : ∀ (μ : Measure (Euclid P)) (h : Euclid P → ℝ), Integrable h μ →
        Tendsto (fun n : ℕ => ∫ x, (1 - f x) ^ n * h x ∂μ) atTop (𝓝 (∫ x in F, h x ∂μ)) := by
      intro μ h hh
      rw [← integral_indicator hF.measurableSet]
      refine tendsto_integral_of_dominated_convergence (fun x => ‖h x‖) (fun n => ?_) hh.norm
        (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
      · exact (hgd n).continuous.aestronglyMeasurable.mul hh.aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hgb n x)
      · by_cases hx : x ∈ F
        · have hfx : f x = 0 := Function.notMem_support.mp (by rw [hfs]; exact fun h => h hx)
          simp [hfx, hx]
        · have hfx : f x ≠ 0 := Function.mem_support.mp (by rw [hfs]; exact hx)
          have hpos : 0 < f x := lt_of_le_of_ne (hf01 x).1 (Ne.symm hfx)
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - f x)
            (by linarith [(hf01 x).2]) (by linarith)).mul_const (h x)
          simpa [hx] using this
    exact tendsto_nhds_unique (hlim μ₁ _ hi₁)
      (((hlim μ₂ _ hi₂).add (hlim μ₃ _ hi₃)).congr fun n => (hmul _ (hgd n)).symm)
  -- Step 4: Dynkin's π-λ theorem extends the identity from closed sets to all Borel sets.
  have hall : ∀ (t : Set (Euclid P)) (_ : MeasurableSet t),
      ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃ := by
    refine MeasurableSpace.induction_on_inter (s := {s | IsClosed s})
      (C := fun t _ =>
        ∫ x in t, ξ₁ x (w x) ∂μ₁ = ∫ x in t, ξ₂ x (w x) ∂μ₂ + ∫ x in t, ξ₃ x (w x) ∂μ₃)
      ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
      (by simp) (fun t ht => hclosed t ht) (fun t htm ht => ?_) (fun f hfd hfm hf => ?_)
    · have e₁ := integral_add_compl htm hi₁
      have e₂ := integral_add_compl htm hi₂
      have e₃ := integral_add_compl htm hi₃
      have e := heq ω
      linarith
    · exact (hasSum_integral_iUnion hfm hfd hi₁.integrableOn).unique
        (((hasSum_integral_iUnion hfm hfd hi₂.integrableOn).add
          (hasSum_integral_iUnion hfm hfd hi₃.integrableOn)).congr_fun fun n => hf n)
  exact hall B hB

/-- **Integer multiplicity is local** (Simon Ch. 6, 3.1 and 6.3.1; localization remark 8.3(1)).
Assume (IMC)(a).  Let `X(ω) = ∫ ⟨ω, ξ⟩ dμ` for `ω ∈ 𝒟ᵏ(U)`, where `μ(ℝᴾ \ U) = 0`, `μ` is finite
on compact subsets of `U` and `ξ` is `μ`-measurable.  If each `x ∈ U` has an open neighbourhood
`W ⊆ U` with an integer multiplicity triple `R = (M, θ, ξ_R)` in `W` such that `μ⌞W = θHᵏ⌞M` and
`ξ = ξ_R` `μ`-a.e. on `W`, then `X` is integer multiplicity.  By Lindelöf, countably many such
`Wᵢ` cover `U`, and there are disjoint Borel pieces `Aᵢ ⊆ Wᵢ` covering `U`; then
`μ⌞Aᵢ = (θᵢHᵏ⌞Mᵢ)⌞Aᵢ`, and `ξ = ξᵢ` `Hᵏ`-a.e. on `Mᵢ ∩ Aᵢ` because `Hᵏ⌞Mᵢ ≪ θᵢHᵏ⌞Mᵢ`.  Gluing
the `Rᵢ` along the `Aᵢ` gives a triple in `U` with orientation `ξ` and weight `μ`, and it
represents `X`. -/
theorem Submission.cbr_isIntegerMultiplicity_of_local_reps : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (P k : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ ω : TestFormOn U k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ x ∈ U, ∃ (W : Set (Euclid P)) (R : IMRep W k), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ μ.restrict W = R.measure ∧ ∀ᵐ y ∂μ, y ∈ W → ξ y = R.orient y) → IsIntegerMultiplicity X := by
  intro hIMC P k U X μ ξ hU hμU hμK hξ hX hloc
  -- Step 1: countably many neighbourhoods `Wᵢ` carrying local triples `Rᵢ`, and disjoint Borel
  -- pieces `Aᵢ ⊆ Wᵢ` covering `U` (Lindelöf)
  obtain ⟨ι, _, W, A, hWo, hWU, hpW, hAm, hAW, hAd, hAU⟩ :=
    Submission.cbrg_exists_countable_disjoint_refinement P U
      (fun W => ∃ R : IMRep W k, μ.restrict W = R.measure ∧ ∀ᵐ y ∂μ, y ∈ W → ξ y = R.orient y)
      fun x hx => by
        obtain ⟨W, R, hWo, hxW, hWU, hRμ, hRξ⟩ := hloc x hx
        exact ⟨W, hWo, hxW, hWU, R, hRμ, hRξ⟩
  choose R hRμ hRξ using hpW
  -- Step 2: `ξ = ξᵢ` holds `μ⌞Wᵢ`-a.e., i.e. `θᵢHᵏ⌞Mᵢ`-a.e., hence `Hᵏ⌞Mᵢ`-a.e. and so
  -- `Hᵏ`-a.e. on `Mᵢ ∩ Aᵢ`
  have hξR : ∀ i, ∀ᵐ y ∂(μHE[k].restrict ((R i).carrier ∩ A i)), ξ y = (R i).orient y := by
    intro i
    have h : ∀ᵐ y ∂(R i).measure, ξ y = (R i).orient y := by
      rw [← hRμ i, ae_restrict_iff' (hWo i).measurableSet]
      exact hRξ i
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left
      ((Submission.cbr_imRep_measure_basic P k (W i) (R i)).2.1.ae_le h)
  -- Step 3: glue the `Rᵢ` along the `Aᵢ`; `μ⌞Aᵢ = (μ⌞Wᵢ)⌞Aᵢ = (θᵢHᵏ⌞Mᵢ)⌞Aᵢ` as `Aᵢ ⊆ Wᵢ`
  obtain ⟨R', -, hR'o, hR'μ⟩ := Submission.cbrg_imRep_glue_disjoint hIMC ι P k U W A R μ ξ hU
    hWo hWU hAm hAd (by rw [hAU]; exact hμU)
    (fun i => by rw [← Measure.restrict_restrict_of_subset (μ := μ) (hAW i), hRμ i]) hμK hξ hξR
  -- Step 4: the glued triple represents `X`: `R'.action ω = ∫ ⟨ω, ξ⟩ dμ = X(ω)`
  refine ⟨R', fun ω => ?_⟩
  rw [hX ω, (Submission.cbr_imRep_measure_basic P k U R').2.2.2.2.2.2, hR'o, hR'μ]
/-- **Equal set integrals against all test forms of an open `B` determine the orientation a.e.
on `B`** (orientation step of the locality of integer multiplicity).  On `E ⊆ B`,
`μ₂⌞E = (μ₂⌞B)⌞E = (μ₁⌞B)⌞E = μ₁⌞E`.  Fix a covector `α` and a compact `K ⊆ B`.  A smooth
Urysohn function `φ` with `φ = 1` on `K` and `tsupport φ` compact in `B` gives the test form
`ω = φ α ∈ 𝒟ᵏ(B)`, equal to `α` on `K`; so for Borel `s`, `∫_s ξ₁(α) d(μ₁⌞K) = ∫_{s∩K} ξ₁(ω) dμ₁
= ∫_{s∩K} ξ₂(ω) dμ₂ = ∫_s ξ₂(α) d(μ₁⌞K)`.  Both evaluations are bounded by `|α|` and `μ₁(K) < ∞`,
so they are `μ₁⌞K`-integrable and uniqueness of densities gives `ξ₁(α) = ξ₂(α)` `μ₁`-a.e. on `K`.
Testing on a finite basis of covectors (`Λᵏ` is finite-dimensional,
`Submission.lcn_covector_finiteDimensional`) gives `ξ₁ = ξ₂` `μ₁`-a.e. on `K`; each point of
`B` has a closed-ball neighbourhood `K ⊆ B`, and `μ₁`-null sets are local
(`measure_null_of_locally_null`, `ℝᴾ` second countable). -/
theorem Submission.cbr_orient_ae_eq_of_setIntegral_eq : ∀ (P k : ℕ) (B : Set (Euclid P)) (μ₁ μ₂ : Measure (Euclid P)) (ξ₁ ξ₂ : Euclid P → MultiVector P k), IsOpen B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ B → μ₁ K < ∞) → μ₁.restrict B = μ₂.restrict B → AEStronglyMeasurable ξ₁ μ₁ → AEStronglyMeasurable ξ₂ μ₂ → (∀ᵐ x ∂μ₁, ∀ α : Covector (Euclid P) k, |ξ₁ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ₂, ∀ α : Covector (Euclid P) k, |ξ₂ x α| ≤ covectorEuclideanNorm α) → (∀ (E : Set (Euclid P)) (ω : TestFormOn B k), MeasurableSet E → ∫ x in E, ξ₁ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₁ = ∫ x in E, ξ₂ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ₂) → ∀ᵐ x ∂μ₁, x ∈ B → ξ₁ x = ξ₂ x := by
  intro P k B μ₁ μ₂ ξ₁ ξ₂ hB hfin hres hm₁ hm₂ hb₁ hb₂ hint
  -- Step 1: on `E ⊆ B`, `μ₂⌞E = (μ₂⌞B)⌞E = (μ₁⌞B)⌞E = μ₁⌞E`
  have hrestr : ∀ E : Set (Euclid P), E ⊆ B → μ₂.restrict E = μ₁.restrict E := fun E hEB => by
    rw [← Measure.restrict_restrict_of_subset hEB, ← hres, Measure.restrict_restrict_of_subset hEB]
  -- Step 2: for a covector `α` and a compact `K ⊆ B`, `ξ₁(α) = ξ₂(α)` holds `μ₁⌞K`-a.e.
  have hcov : ∀ K : Set (Euclid P), IsCompact K → K ⊆ B → ∀ α : Covector (Euclid P) k,
      ∀ᵐ y ∂μ₁.restrict K, ξ₁ y α = ξ₂ y α := by
    intro K hKc hKB α
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    -- a smooth cut-off `φ`, `φ = 1` on `K`, with `tsupport φ = closure V` compact in `B`
    obtain ⟨V, hVo, hKV, hVB, hVc⟩ := exists_open_between_and_isCompact_closure hKc hB hKB
    obtain ⟨φ, hφ, -, hφs, hφ1⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := ⊤) hVo hKc.isClosed hKV
    have hts : tsupport φ = closure V := by rw [tsupport, hφs]
    -- the test form `ω = φ α ∈ 𝒟ᵏ(B)`: smooth, `tsupport ω ⊆ tsupport φ = closure V`
    have hωφ : tsupport (fun y => φ y • α : DifferentialForm (Euclid P) k) ⊆ closure V :=
      (tsupport_smul_subset_left φ fun _ => α).trans hts.subset
    have hω : (fun y => φ y • α : DifferentialForm (Euclid P) k) ∈ testFormOnSubmodule B k :=
      ⟨⟨hφ.smul (contDiff_const (c := α)), hVc.of_isClosed_subset (isClosed_tsupport _) hωφ⟩,
        hωφ.trans hVB⟩
    -- `ξ₁(α)`, `ξ₂(α)` are a.e. strongly measurable and bounded by `|α|`, `μ₁ K = μ₂ K < ∞`
    have hK₁ : μ₁ K ≠ ∞ := (hfin K hKc hKB).ne
    have hK₂ : μ₂ K ≠ ∞ :=
      calc μ₂ K = μ₂.restrict K univ := (Measure.restrict_apply_univ K).symm
        _ = μ₁.restrict K univ := by rw [hrestr K hKB]
        _ = μ₁ K := Measure.restrict_apply_univ K
        _ ≠ ∞ := hK₁
    have hf : Integrable (fun y => ξ₁ y α) (μ₁.restrict K) :=
      Measure.integrableOn_of_bounded hK₁ (hm₁.apply_continuousLinearMap α)
        ((ae_restrict_of_ae hb₁).mono fun y hy => (Real.norm_eq_abs _).trans_le (hy α))
    have hg : Integrable (fun y => ξ₂ y α) (μ₁.restrict K) := by
      rw [← hrestr K hKB]
      exact Measure.integrableOn_of_bounded hK₂ (hm₂.apply_continuousLinearMap α)
        ((ae_restrict_of_ae hb₂).mono fun y hy => (Real.norm_eq_abs _).trans_le (hy α))
    -- equal set integrals for `μ₁⌞K`: on `s ∩ K`, `ω = α`
    refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hf hg fun s hs _ => ?_
    have hsK : MeasurableSet (s ∩ K) := hs.inter hKm
    have heq : ∀ ξ : Euclid P → MultiVector P k,
        EqOn (fun y => ξ y α) (fun y => ξ y (φ y • α)) (s ∩ K) := fun ξ y hy => by
      show ξ y α = ξ y (φ y • α)
      rw [(hφ1 y).1 hy.2, one_smul]
    rw [Measure.restrict_restrict hs]
    calc ∫ y in s ∩ K, ξ₁ y α ∂μ₁ = ∫ y in s ∩ K, ξ₁ y (φ y • α) ∂μ₁ :=
          setIntegral_congr_fun hsK (heq ξ₁)
      _ = ∫ y in s ∩ K, ξ₂ y (φ y • α) ∂μ₂ := hint (s ∩ K) ⟨_, hω⟩ hsK
      _ = ∫ y in s ∩ K, ξ₂ y (φ y • α) ∂μ₁ := by
          rw [hrestr (s ∩ K) (inter_subset_right.trans hKB)]
      _ = ∫ y in s ∩ K, ξ₂ y α ∂μ₁ := (setIntegral_congr_fun hsK (heq ξ₂)).symm
  -- Step 3: on a compact `K ⊆ B`, test on a basis of the finite-dimensional `Λᵏ`
  have := Submission.lcn_covector_finiteDimensional P k
  let b := Module.finBasis ℝ (Covector (Euclid P) k)
  have hK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ B → ∀ᵐ y ∂μ₁, y ∈ K → ξ₁ y = ξ₂ y := by
    intro K hKc hKB
    refine (ae_restrict_iff' hKc.isClosed.measurableSet).1 ?_
    filter_upwards [ae_all_iff.2 fun i => hcov K hKc hKB (b i)] with y hy
    exact ContinuousLinearMap.coe_injective (b.ext hy)
  -- Step 4: each `x ∈ B` has a closed-ball neighbourhood `K ⊆ B`; null sets are local
  refine ae_iff.2 (measure_null_of_locally_null _ fun x hx => ?_)
  have hx' : ¬(x ∈ B → ξ₁ x = ξ₂ x) := hx
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB x (not_imp.1 hx').1
  refine ⟨_, inter_mem_nhdsWithin _ (closedBall_mem_nhds x (half_pos hε)),
    measure_mono_null ?_ (ae_iff.1 (hK _ (isCompact_closedBall x (ε / 2))
      ((closedBall_subset_ball (half_lt_self hε)).trans hεB)))⟩
  exact fun y hy h => hy.1 fun _ => h hy.2
/-- **Simon Ch. 6, 3.1 and 2.16** (with Ch. 3, 1.4): if `T = τ(M, θ, ξ)` is integer multiplicity
in `U` and `V ⊆ U` is open, then `T⌞V = τ(M ∩ V, θ, ξ)` is integer multiplicity in `V`.  The
restricted triple inherits measurability, rectifiability, positivity and local integrability from
`(M, θ, ξ)`.  At `Hⁿ`-a.e. `x ∈ M ∩ V` the approximate tangent space of `M` is also that of
`M ∩ V`, as the removed set `M ∖ (M ∩ V)` misses the open set `V ∋ x`
(`dtc_approxTangent_of_null_diff`).  A test form supported in `V` vanishes on `M ∖ V`, so its
integrals over `M` and over `M ∩ V` agree.  Openness of `U` is not used. -/
theorem Submission.dtc_restrictDomain_isIntegerMultiplicity : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n), IsOpen V → IsIntegerMultiplicity T → IsIntegerMultiplicity (T.restrictDomain hVU) := by
  rintro P n U V hVU T hV ⟨R, hR⟩
  -- Step 1: `M ∩ V` is Borel
  have hMV : MeasurableSet (R.carrier ∩ V) := R.measurableSet_carrier.inter hV.measurableSet
  -- the restricted triple `R' = (M ∩ V, θ, ξ)` in `V`
  let R' : IMRep V n :=
    { carrier := R.carrier ∩ V
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := hMV
      -- Step 2: `M ∩ V ⊆ V`
      carrier_subset := inter_subset_right
      -- Step 3: a subset of a countably `n`-rectifiable set is countably `n`-rectifiable
      rectifiable := R.rectifiable.mono inter_subset_left
      -- Step 4: `θ` is measurable, and positive on `M ∩ V ⊆ M`
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      -- Step 5: for compact `K ⊆ V`, `(M ∩ V) ∩ K = M ∩ K` and `K ⊆ V ⊆ U`
      locallyIntegrable_mult := fun K hK hKV => by
        rw [inter_assoc, inter_eq_right.2 hKV]
        exact R.locallyIntegrable_mult K hK (hKV.trans hVU)
      -- Step 6: `Hⁿ⌞(M ∩ V) ≤ Hⁿ⌞M`
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
      -- Step 7: at `Hⁿ⌞(M ∩ V)`-a.e. `x`, the plane `Q` oriented by `ξ(x)` stays the approximate
      -- tangent space, since `(M ∖ (M ∩ V)) ∩ V = ∅`
      orients := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
          (inter_subset_left : R.carrier ∩ V ⊆ R.carrier) R.orients, ae_restrict_mem hMV]
          with x hx hxMV
        obtain ⟨Q, hQ, hξQ⟩ := hx
        have hnull : μHE[n] ((R.carrier \ (R.carrier ∩ V)) ∩ V) = 0 := by
          rw [sdiff_self_inter, sdiff_inter_self, measure_empty]
        exact ⟨Q, Submission.dtc_approxTangent_of_null_diff P n R.carrier (R.carrier ∩ V) V x Q
          inter_subset_left hV hxMV.2 hnull hQ, hξQ⟩ }
  -- Step 8: `T⌞V(ω) = T(ιω) = ∫_M θ⟨ω, ξ⟩ dHⁿ = ∫_{M ∩ V} θ⟨ω, ξ⟩ dHⁿ`, as `ω = 0` off `V`
  refine ⟨R', fun ω => ?_⟩
  rw [GeometricCurrentOn.restrictDomain_apply, hR, testFormOnInclusion_coe]
  change ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n] =
    ∫ x in R.carrier ∩ V, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
    inter_subset_left fun x hx => ?_
  have hxω : x ∉ tsupport (ω : DifferentialForm (Euclid P) n) :=
    fun h => hx.2 ⟨hx.1, ω.property.2 h⟩
  rw [image_eq_zero_of_notMem_tsupport hxω, map_zero, mul_zero]
/-- Measures `μ, ν` on `ℝᴾ` that agree on the open subsets of an open set `O`, with `μ` finite on
compact subsets of `O`, agree on the Borel subsets of `O`.  `O` is exhausted by the open sets
`Oᵢ = {x : |x| < i, dist(x, ℝᴾ ∖ O) > 1/(i+1)}`, whose closures are compact subsets of `O`; the
finite measures `μ⌞Oᵢ, ν⌞Oᵢ` agree on the π-system of open sets, hence everywhere, and continuity
from below along `A ∩ Oᵢ ↑ A` gives `μ(A) = ν(A)`. -/
theorem Submission.cmc_ml_measure_eq_of_eq_on_open_subsets : ∀ (P : ℕ) (O : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen O → (∀ C : Set (Euclid P), IsCompact C → C ⊆ O → μ C ≠ ∞) → (∀ G : Set (Euclid P), IsOpen G → G ⊆ O → μ G = ν G) → ∀ A : Set (Euclid P), MeasurableSet A → A ⊆ O → μ A = ν A := by
  intro P O μ ν hO hfin hopen A hA hAO
  -- `d(x) = dist(x, ℝᴾ ∖ O) ∈ [0, ∞]` (`d ≡ ∞` if `O = ℝᴾ`), and the thresholds `1/(i+1)`
  set d : Euclid P → ℝ≥0∞ := fun x => infEDist x Oᶜ
  have hdc : Continuous d := continuous_infEDist
  set c : ℕ → ℝ≥0∞ := fun i => ((i + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hc0 : ∀ i, c i ≠ 0 := fun i => ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  -- 1. the exhaustion `Oᵢ = {x : |x| < i, d(x) > 1/(i+1)}`
  set Oi : ℕ → Set (Euclid P) := fun i => ball 0 i ∩ d ⁻¹' Ioi (c i)
  -- (a) `Oᵢ` is open
  have hOi_open : ∀ i, IsOpen (Oi i) := fun i => isOpen_ball.inter (isOpen_Ioi.preimage hdc)
  -- (b) `closure Oᵢ ⊆ Fᵢ = {x : |x| ≤ i, d(x) ≥ 1/(i+1)} ⊆ O`
  have hOi_cl : ∀ i, closure (Oi i) ⊆ closedBall 0 i ∩ d ⁻¹' Ici (c i) := fun i =>
    closure_minimal (inter_subset_inter ball_subset_closedBall (preimage_mono Ioi_subset_Ici_self))
      (isClosed_closedBall.inter (isClosed_Ici.preimage hdc))
  have hOi_O : ∀ i, closure (Oi i) ⊆ O := by
    intro i x hx
    by_contra hxO
    have h0 : d x = 0 := infEDist_zero_of_mem hxO
    have h1 : c i ≤ d x := (hOi_cl i hx).2
    rw [h0, nonpos_iff_eq_zero] at h1
    exact hc0 i h1
  -- (c) `closure Oᵢ` is compact
  have hOi_cpt : ∀ i, IsCompact (closure (Oi i)) := fun i =>
    (isCompact_closedBall 0 i).of_isClosed_subset isClosed_closure fun x hx => (hOi_cl i hx).1
  -- (d) `Oᵢ ⊆ Oⱼ` for `i ≤ j`
  have hOi_mono : Monotone Oi := by
    intro i j hij x hx
    have h1 : x ∈ ball (0 : Euclid P) j := ball_subset_ball (by exact_mod_cast hij) hx.1
    have h2 : c i < d x := hx.2
    have h3 : c j ≤ c i := ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.succ_le_succ hij)
    have h4 : c j < d x := h3.trans_lt h2
    exact ⟨h1, h4⟩
  -- (e) `⋃ᵢ Oᵢ = O`
  have hOi_union : ⋃ i, Oi i = O := by
    refine Subset.antisymm (iUnion_subset fun i => subset_closure.trans (hOi_O i)) fun x hx => ?_
    have hdx : 0 < d x := infEDist_pos_iff_notMem_closure.mpr (by
      rw [hO.isClosed_compl.closure_eq]; exact fun h => h hx)
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hdx.ne'
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    have h1 : x ∈ ball (0 : Euclid P) (max m k : ℕ) := by
      rw [mem_ball, dist_zero_right]
      exact hk.trans_le (by exact_mod_cast le_max_right m k)
    have h2 : c (max m k) ≤ (m : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast (le_max_left m k).trans (Nat.le_succ _))
    have h3 : c (max m k) < d x := h2.trans_lt hm
    exact mem_iUnion.mpr ⟨max m k, h1, h3⟩
  -- 2. `μ(Oᵢ) ≤ μ(closure Oᵢ) < ∞`
  have hμOi : ∀ i, μ (Oi i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top (hfin _ (hOi_cpt i) (hOi_O i)) (measure_mono subset_closure)
  -- 3. `μ⌞Oᵢ = ν⌞Oᵢ`: finite measures agreeing on the π-system of open sets (and on `ℝᴾ`)
  have hrestr : ∀ i, μ.restrict (Oi i) = ν.restrict (Oi i) := by
    intro i
    have : IsFiniteMeasure (μ.restrict (Oi i)) := isFiniteMeasure_restrict.mpr (hμOi i)
    have hG : ∀ G : Set (Euclid P), IsOpen G → μ.restrict (Oi i) G = ν.restrict (Oi i) G := by
      intro G hG
      rw [Measure.restrict_apply hG.measurableSet, Measure.restrict_apply hG.measurableSet]
      exact hopen _ (hG.inter (hOi_open i))
        (inter_subset_right.trans (subset_closure.trans (hOi_O i)))
    exact ext_of_generate_finite _ BorelSpace.measurable_eq isPiSystem_isOpen
      (fun G hG' => hG G hG') (hG univ isOpen_univ)
  -- 4. continuity from below along `A ∩ Oᵢ ↑ A`
  have hAunion : A = ⋃ i, A ∩ Oi i := by
    rw [← inter_iUnion, hOi_union, inter_eq_left.mpr hAO]
  have hmono : Monotone fun i => A ∩ Oi i := fun i j hij =>
    inter_subset_inter_right _ (hOi_mono hij)
  rw [hAunion, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun i => ?_
  rw [← Measure.restrict_apply hA, ← Measure.restrict_apply hA, hrestr i]

/-- **Foundations of the closure step** (Simon Ch. 6, 2.7–2.8, 2.35–2.37, 3.1, 8.3; Ch. 1, 4.4).
(REP): a current `T` with locally finite mass is `T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `μ(W) = M_W(T)` and
`|ξ| ≤ 1` (`dimred_mbl_fnd_exists_massRepresentation_core`); if `∂T` also has locally finite
mass, then `μ ≪ Hⁿ` for this same `(μ, ξ)` (`dimred_mbl_fnd_null_of_representation`).
(T1): measures with locally bounded masses have a vaguely convergent subsequence
(`cbr_vague_convergent_subseq`); its limit is a Radon measure on `U`
(`cbr_vague_limit_measure`) satisfying the portmanteau inequalities (`cbr_vague_portmanteau`).
(T2) and (MM) are `cbr_sublevel_restriction_tendsto` and `cbr_slice_mass_majorant`.
(IML): restriction to an open `V ⊆ U` preserves integer multiplicity
(`dtc_restrictDomain_isIntegerMultiplicity`).  Conversely, assume (REP), (MR) and (IMC), and
write `X = ξ·μ` by (REP).  Let `R` represent `X⌞B` on a ball `B ⊆ U`.  For `G ⊆ B`, `X` and
`X⌞B` have the same admissible forms for `M_G`.  So `μ(G) = M_G(X) = M_G(X⌞B) = μ_R(G)` for
open `G ⊆ B` by (MR), and `μ⌞B = μ_R` (`cmc_ml_measure_eq_of_eq_on_open_subsets`; `μ_R` lives
on `M_R ⊆ B`).  Both `ξ·μ` and `ξ_R·μ_R` represent `X⌞B`.  Hence their set integrals agree
(`cbr_setIntegral_eq_of_integral_eq`), so `ξ = ξ_R` `μ`-a.e. on `B`
(`cbr_orient_ae_eq_of_setIntegral_eq`).  The local triples then glue
(`cbr_isIntegerMultiplicity_of_local_reps`). -/
theorem Submission.dtc_bc_tc_cl_foundations : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) ∧ ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) ∧ ((∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P k : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U k), IsOpen U → ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → X.massOn W < ∞) → (∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∃ h : ball x r ⊆ U, IsIntegerMultiplicity (X.restrictDomain h)) → IsIntegerMultiplicity X) ∧ (∀ (V : Set (Euclid P)) (h : V ⊆ U), IsOpen V → IsIntegerMultiplicity X → IsIntegerMultiplicity (X.restrictDomain h))) := by
  refine ⟨?_, ⟨?_, Submission.cbr_sublevel_restriction_tendsto,
    Submission.cbr_slice_mass_majorant⟩, ?_⟩
  · -- (REP): the representation core, then absolute continuity for the same `(μ, ξ)`
    intro P n U T hU hmass
    obtain ⟨μ, ξ, hμU, hμK, hμW, hξ, hξα, hTξ⟩ :=
      Submission.dimred_mbl_fnd_exists_massRepresentation_core P n U T hU hmass
    exact ⟨μ, ξ, hμU, hμK, hμW, hξ, hξα, hTξ, fun hbd =>
      Submission.dimred_mbl_fnd_null_of_representation P n U T μ ξ hU hbd hμU hμK hμW hξ hξα
        hTξ⟩
  · -- (T1): a vaguely convergent subsequence, its limit measure and the portmanteau inequalities
    intro P U μs hU hbound
    obtain ⟨φ, hφ, hconv⟩ := Submission.cbr_vague_convergent_subseq P U μs hU hbound
    -- `μ_{φ(j)}(K) ≤ ⨆ᵢ μᵢ(K) < ∞` for compact `K ⊆ U`
    have hfin : ∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μs (φ j) K < ∞ :=
      fun j K hK hKU => (le_iSup (fun i => μs i K) (φ j)).trans_lt (hbound K hK hKU)
    obtain ⟨μ, hμU, hμK, hμconv⟩ :=
      Submission.cbr_vague_limit_measure P U (fun j => μs (φ j)) hU hfin hconv
    obtain ⟨hlimsup, hliminf⟩ :=
      Submission.cbr_vague_portmanteau P U (fun j => μs (φ j)) μ hU hfin hμK hμconv
    exact ⟨φ, μ, hφ, hμU, hμK, hμconv, hlimsup, hliminf⟩
  · -- (IML)
    intro hREP hMR hIMC P k U X hU
    -- (2): restriction to an open `V ⊆ U` preserves integer multiplicity
    refine ⟨fun hmass hloc => ?_, fun V hVU hV hX =>
      Submission.dtc_restrictDomain_isIntegerMultiplicity P k U V hVU X hV hX⟩
    -- (1), Step 1: `X = ξ·μ` with `μ(W) = M_W(X)` by (REP); it suffices to give local triples
    obtain ⟨μ, ξ, hμU, hμK, hμmass, hξmeas, hξbound, hXrep, -⟩ := hREP P k U X hU hmass
    refine Submission.cbr_isIntegerMultiplicity_of_local_reps hIMC.1 P k U X μ ξ hU hμU hμK
      hξmeas hXrep fun x hx => ?_
    -- Step 2: a ball `B = B_r(x) ⊆ U` and a triple `R` representing `X⌞B`
    obtain ⟨r, hr, hB, R, hR⟩ := hloc x hx
    obtain ⟨hRac, -, -, hRcompl, hRK, hRmeas, hRaction⟩ :=
      Submission.cbr_imRep_measure_basic P k (ball x r) R
    have hμKB : ∀ K : Set (Euclid P), IsCompact K → K ⊆ ball x r → μ K < ∞ :=
      fun K hK hKB => hμK K hK (hKB.trans hB)
    -- `|ξ_R| ≤ 1` holds `Hᵏ⌞M_R`-a.e. by (IMC)(d), hence `μ_R`-a.e.
    have hRbound : ∀ᵐ y ∂R.measure, ∀ α : Covector (Euclid P) k,
        |R.orient y α| ≤ covectorEuclideanNorm α :=
      hRac.ae_le (hIMC.2.2.2 P k (ball x r) R)
    -- Step 3: `M_G(X) = M_G(X⌞B)` for `G ⊆ B`: the admissible forms are the same forms
    have hmassB : ∀ G : Set (Euclid P), G ⊆ ball x r →
        X.massOn G = (X.restrictDomain hB).massOn G := by
      intro G hGB
      unfold GeometricCurrentOn.massOn
      congr 1
      ext s
      constructor
      · rintro ⟨ω, hω, rfl⟩
        exact ⟨⟨ω, ω.property.1, hω.1.trans hGB⟩, hω, rfl⟩
      · rintro ⟨ω', hω', rfl⟩
        exact ⟨testFormOnInclusion hB k ω', hω', rfl⟩
    -- Step 4: `μ(G) = M_G(X) = M_G(X⌞B) = μ_R(G)` for open `G ⊆ B` by (MR), so `μ⌞B = μ_R⌞B`
    have hopen : ∀ G : Set (Euclid P), IsOpen G → G ⊆ ball x r → μ G = R.measure G := by
      intro G hG hGB
      rw [← hμmass G hG, hmassB G hGB]
      exact hMR P k (ball x r) (X.restrictDomain hB) R isOpen_ball hR G hG
    have hborel := Submission.cmc_ml_measure_eq_of_eq_on_open_subsets P (ball x r) μ R.measure
      isOpen_ball (fun C hC hCB => (hμKB C hC hCB).ne) hopen
    have hrestr : μ.restrict (ball x r) = R.measure.restrict (ball x r) :=
      (Measure.restrict_congr_meas measurableSet_ball).2 fun A hAB hA => hborel A hA hAB
    -- `μ_R` lives on `M_R ⊆ B`, so `μ_R⌞B = μ_R`
    have hRB : R.measure.restrict (ball x r) = R.measure :=
      Measure.restrict_eq_self_of_ae_mem
        (Filter.mem_of_superset (mem_ae_iff.2 hRcompl) R.carrier_subset)
    -- Step 5: `∫ ⟨ω, ξ⟩ dμ = X(ιω) = X⌞B(ω) = ∫ ⟨ω, ξ_R⟩ dμ_R` for `ω ∈ 𝒟ᵏ(B)`, so the
    -- integrals over every Borel set agree
    have hset := Submission.cbr_setIntegral_eq_of_integral_eq P k (ball x r) μ R.measure 0 ξ
      R.orient 0 isOpen_ball hμKB hRK (fun K _ _ => by simp) hξmeas hRmeas
      (aestronglyMeasurable_zero_measure _) (ae_of_all μ hξbound) hRbound
      (ae_of_all _ fun y α => by simpa using covectorEuclideanNorm_nonneg α) fun ω => by
        rw [integral_zero_measure, add_zero, ← hRaction (ω : DifferentialForm (Euclid P) k),
          ← hR ω, GeometricCurrentOn.restrictDomain_apply, hXrep, testFormOnInclusion_coe]
    -- Step 6: hence `ξ = ξ_R` `μ`-a.e. on `B`, and `(B, R)` is the required local triple
    have hae := Submission.cbr_orient_ae_eq_of_setIntegral_eq P k (ball x r) μ R.measure ξ
      R.orient isOpen_ball hμKB hrestr hξmeas hRmeas (ae_of_all μ hξbound) hRbound
      fun E ω hE => by rw [hset E ω hE, Measure.restrict_zero, integral_zero_measure, add_zero]
    exact ⟨ball x r, R, isOpen_ball, mem_ball_self hr, hB, hrestr.trans hRB, hae⟩

/-- **Simon 6.2–6.3: boundary rectifiability `BR_P(d)` from the closure theorem `CL_P(d)`**
(`d + 1 < P`).  If `R ∈ 𝒟_{d+1}(U)` is integer multiplicity and `M_W(∂R) < ∞` for every open
`W ⊂⊂ U`, then `∂R` is integer multiplicity.  By the local criterion (IML)(1) of the sibling
foundations it suffices to treat a neighbourhood of each `x₀ ∈ U`.  Slicing by `|· − x₀|` gives
`r > 0` with `B̄_r(x₀) ⊆ U` and an integer multiplicity `R' = R ⌞ B_r(x₀)` supported in
`B̄_r(x₀)`, with `M(R'), M(∂R') < ∞` and `∂R' = ∂R` on forms supported in `B_r(x₀)`.  Its
extension `Y` by zero to `ℝ^P` is integer multiplicity, has compact support, `M(Y) ≤ M(R')` and
`M(∂Y) ≤ M(∂R')`, so the deformation theorem and `CL_P(d)` make `∂Y` integer multiplicity.  As
`(∂R)|_{B_r(x₀)} = (∂Y)|_{B_r(x₀)}`, (IML)(2) concludes. -/
theorem Submission.dtc_bc_tc_cl_boundary_isIntegerMultiplicity : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P m : ℕ), m + 1 < P → ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 0 < ρ → IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → ∀ (P d : ℕ), d + 1 < P → (∀ (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U d) (T : GeometricCurrentOn U d), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → IsIntegerMultiplicity T) → (∀ (U : Set (Euclid P)) (R : GeometricCurrentOn U (d + 1)), IsOpen U → IsIntegerMultiplicity R → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → R.boundary.massOn W < ∞) → IsIntegerMultiplicity R.boundary) := by
  intro hMR hIMC _hVO hDTr P d hdP hCL U R hU hR hbd
  -- (REP) and the locality of integer multiplicity (IML) from the sibling foundations
  obtain ⟨hREP, -, hIML⟩ := Submission.dtc_bc_tc_cl_foundations
  -- (IML)(1): `∂R` has locally finite mass, so it suffices to work near each `x₀ ∈ U`
  refine (hIML hREP hMR hIMC P d U R.boundary hU).1 hbd ?_
  intro x₀ hx₀
  -- slicing: `R' = R ⌞ B_r(x₀)` with `∂R' = ∂R` on forms supported in `B_r(x₀)`
  obtain ⟨r, hr, hrU, R', hR'im, hR'spt, hR'm, hR'bm, hagree⟩ :=
    Submission.dtc_bc_tc_cl_bim_slice_localization hREP hIMC.2.1 hIMC.2.2.2
      Submission.cmc_slice_mass_bounds P d U R x₀ hU hR hbd hx₀
  -- the extension `Y` of `R'` by zero to `ℝ^P`
  obtain ⟨Y, hYim, hYres, hYspt, hYm, hYbm⟩ :=
    Submission.cmc_fc_extend_to_univ hIMC.2.1 hMR P d U (closedBall x₀ r) R' hU
      (isCompact_closedBall x₀ r) hrU hR'im hR'spt
  -- `spt Y = ℝ^P ∖ Z(Y)` is closed and lies in the compact `B̄_r(x₀)`
  have hYcpt : IsCompact Y.support := by
    have hYclosed : IsClosed Y.support := by
      rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
      exact Y.isOpen_zeroRegion.isClosed_compl
    exact (isCompact_closedBall x₀ r).of_isClosed_subset hYclosed hYspt
  -- the deformation theorem and `CL_P(d)` in `ℝ^P`: `∂Y` is integer multiplicity
  have hYb : IsIntegerMultiplicity Y.boundary :=
    Submission.dtc_bc_tc_cl_bim_boundary_im_of_compact_support hDTr P d hdP hCL Y hYim hYcpt
      (hYm.trans_lt hR'm) (hYbm.trans_lt hR'bm)
  have hball : ball x₀ r ⊆ U := ball_subset_closedBall.trans hrU
  refine ⟨r, hr, hball, ?_⟩
  -- `∂R = ∂R' = ∂Y` on forms supported in `B_r(x₀)`
  have key : R.boundary.restrictDomain hball =
      Y.boundary.restrictDomain (subset_univ (ball x₀ r)) := by
    ext ω
    have hω : tsupport ((testFormOnInclusion hball d ω : TestFormOn U d) :
        DifferentialForm (Euclid P) d) ⊆ ball x₀ r := ω.property.2
    rw [GeometricCurrentOn.restrictDomain_apply, GeometricCurrentOn.restrictDomain_apply,
      ← hagree (testFormOnInclusion hball d ω) hω, ← hYres]
    rfl
  -- (IML)(2) in `ℝ^P`
  rw [key]
  exact (hIML hREP hMR hIMC P d univ Y.boundary isOpen_univ).2 (ball x₀ r) (subset_univ _)
    isOpen_ball hYb

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
