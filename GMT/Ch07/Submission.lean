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

/-- **Simon Ch. 5, proof of 2.6, (9)–(10), corrected** (estimate (10') of the Lipschitz
approximation: `B_σ(η)` becomes `B_{3s}(η)`, and as only `κσ₀ ≤ 1` is used there is no additive
error `Cδσⁿ`).
For `η ∈ (F ∖ spt μ) ∩ B_{σ₀/4}(ξ)` let `y ∈ spt μ` be a nearest point and `s = |y − η|/2`.  Then
`μ(B_s(η)) = 0`, the density bounds give `ωsⁿ/2 ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ`, and monotonicity with
radii `s < 3s` and `e^{3κs} ≤ 2` gives `μ(B_{3s}(η)) ≤ 2·3ⁿs⁻²∫_{B_{3s}(η)}|p_x^⊥(x − η)|² dμ`.
Splitting `p_x^⊥(x − η) = Q(x − η) + (P − p_x)(x − η)` (cone condition on `F`, Hilbert–Schmidt
bound) and absorbing the `λ²`-term yields `sⁿ ≤ C₉[μ(B_{3s}(η) ∖ F) + ∫_{B_{3s}(η)}|p_x − P|² dμ]`,
with `λ₀ = (288·15ⁿ)^{-1/2}` and `C₉ = 144·3ⁿ/ω`. -/
theorem Submission.dorag_lip_off_support_estimate : ∀ (n k : ℕ), ∃ lam₀ C₉ : ℝ, 0 < lam₀ ∧ 0 < C₉ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (F : Set (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ κ lam : ℝ), 0 < σ₀ → 0 ≤ κ → κ * σ₀ ≤ 1 → 0 ≤ lam → lam ≤ lam₀ → ξ ∈ μ.support → (∀ x ∈ F, ∀ x' ∈ F, ‖(x - x') - T₀.starProjection (x - x')‖ ≤ lam * ‖x - x'‖) → (∀ y ∈ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 8 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 8 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ (y : Euclid (n + k)) (s t : ℝ), y ∈ closedBall ξ (σ₀ / 4) → 0 < s → s < t → t ≤ 3 * σ₀ / 8 → ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * μ (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (τ x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ) → ∀ η ∈ (F \ μ.support) ∩ closedBall ξ (σ₀ / 4), ∃ s : ℝ, ∃ y ∈ μ.support, 0 < s ∧ 2 * s ≤ dist η ξ ∧ dist y η = 2 * s ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ) := by
  intro n k
  -- Hilbert–Schmidt bound `‖A u‖² ≤ (∑ᵢ ‖A eᵢ‖²) ‖u‖²`
  have hHS : ∀ (A : Euclid (n + k) →L[ℝ] Euclid (n + k)) (u : Euclid (n + k)),
      ‖A u‖ ^ 2 ≤ (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
    intro A u
    have hu : ∑ i : Fin (n + k), u i • EuclideanSpace.single i (1 : ℝ) = u := by
      have h := (EuclideanSpace.basisFun (Fin (n + k)) ℝ).sum_repr u
      simpa using h
    have hAu : A u = ∑ i : Fin (n + k), u i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← hu]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul A _ _
    have h1 : ‖A u‖ ≤ ∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAu]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
        (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : ∑ i : Fin (n + k), |u i| ^ 2 = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => sq_abs _
    calc ‖A u‖ ^ 2 ≤ (∑ i : Fin (n + k), |u i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ i : Fin (n + k), |u i| ^ 2) *
          ∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := h2
      _ = (∑ i : Fin (n + k), ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖u‖ ^ 2 := by
          rw [h3, mul_comm]
  -- pointwise splitting `u - S u = (u - T u) + (T u - S u)` with the Hilbert–Schmidt bound
  have hsplit : ∀ (T S : Submodule ℝ (Euclid (n + k))) (u : Euclid (n + k)) (r q : ℝ),
      ‖u‖ ≤ r → ‖u - T.starProjection u‖ ≤ q →
      ‖u - S.starProjection u‖ ^ 2 ≤ 2 * q ^ 2 + 2 * r ^ 2 *
        ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    intro T S u r q hr hq
    have hHS0 : 0 ≤ ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hA := hHS (T.starProjection - S.starProjection) u
    have e : ∑ i : Fin (n + k), ‖(T.starProjection - S.starProjection)
        (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sub_apply, norm_sub_rev]
    rw [e, sub_apply] at hA
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
    have hur : ‖u‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hu0 hr 2
    have hq2 : ‖u - T.starProjection u‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have htri : ‖u - S.starProjection u‖ ≤
        ‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖ := by
      have e2 : u - S.starProjection u =
          (u - T.starProjection u) + (T.starProjection u - S.starProjection u) := by abel
      rw [e2]
      exact norm_add_le _ _
    have hB : ‖T.starProjection u - S.starProjection u‖ ^ 2 ≤
        (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * r ^ 2 :=
      hA.trans (mul_le_mul_of_nonneg_left hur hHS0)
    have ha0 : 0 ≤ ‖u - T.starProjection u‖ := norm_nonneg _
    have hb0 : 0 ≤ ‖T.starProjection u - S.starProjection u‖ := norm_nonneg _
    have hc0 : 0 ≤ ‖u - S.starProjection u‖ := norm_nonneg _
    have hsq : ‖u - S.starProjection u‖ ^ 2 ≤
        (‖u - T.starProjection u‖ + ‖T.starProjection u - S.starProjection u‖) ^ 2 :=
      pow_le_pow_left₀ hc0 htri 2
    nlinarith [sq_nonneg (‖u - T.starProjection u‖ - ‖T.starProjection u - S.starProjection u‖)]
  -- the pointwise bound in `ℝ≥0∞`, in the two cases `x ∈ F` / `x ∉ F`
  have hptE : ∀ (T S : Submodule ℝ (Euclid (n + k))) (u : Euclid (n + k)) (s lam : ℝ)
      (c : ℝ≥0∞), ‖u‖ ≤ 3 * s →
      (‖u - T.starProjection u‖ ≤ lam * (3 * s) ∨ c = ENNReal.ofReal (18 * s ^ 2)) →
      ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + c + ENNReal.ofReal (18 * s ^ 2) *
          ENNReal.ofReal (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
            T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro T S u s lam c hu h
    have hHS0 : 0 ≤ ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases h with hq | hc
    · have h1 := hsplit T S u (3 * s) (lam * (3 * s)) hu hq
      calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
          ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2 + 18 * s ^ 2 *
            ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            refine h1.trans (le_of_eq ?_)
            ring
        _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
        _ ≤ _ := add_le_add le_self_add le_rfl
    · have hq : ‖u - T.starProjection u‖ ≤ 3 * s := by
        calc ‖u - T.starProjection u‖ = ‖Tᗮ.starProjection u‖ := by
              rw [Submodule.starProjection_orthogonal_val]
          _ ≤ ‖u‖ := Submodule.norm_starProjection_apply_le _ _
          _ ≤ 3 * s := hu
      have h1 := hsplit T S u (3 * s) (3 * s) hu hq
      rw [hc]
      calc ENNReal.ofReal (‖u - S.starProjection u‖ ^ 2)
          ≤ ENNReal.ofReal (18 * s ^ 2 + 18 * s ^ 2 *
            ∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            apply ENNReal.ofReal_le_ofReal
            refine h1.trans (le_of_eq ?_)
            ring
        _ = ENNReal.ofReal (18 * s ^ 2) + ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 18 * s ^ 2) (by positivity)]
        _ ≤ _ := add_le_add le_add_self le_rfl
  -- monotonicity with radii `s < 3 s`, combined with `e^{3κs} ≤ 2`
  have hexpb : ∀ (κ s : ℝ) (a J I₂ : ℝ≥0∞), 0 ≤ κ → 0 < s → κ * (3 * s) ≤ 3 / 8 →
      ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a ≤ J →
      J ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * I₂ →
      a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := by
    intro κ s a J I₂ hκ hs hκs hM hJ
    have hexp : Real.exp (κ * (3 * s)) ≤ 2 := by
      have h0 : 0 ≤ κ * (3 * s) := by positivity
      calc Real.exp (κ * (3 * s)) ≤ (2 + κ * (3 * s)) / (2 - κ * (3 * s)) :=
            Real.exp_le_two_add_div_two_sub h0 (by linarith)
        _ ≤ 2 := by
            rw [div_le_iff₀ (by linarith)]
            linarith
    have hc : 0 ≤ Real.exp (κ * (3 * s)) * (3 * s) ^ n := by positivity
    have hcinv : ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
        ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) = 1 := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one]
      congr 1
      have h1 : Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s))) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h2 : (3 * s) ^ n / (3 * s) ^ n = 1 := div_self (by positivity)
      calc Real.exp (κ * (3 * s)) * (3 * s) ^ n * (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n)
          = (Real.exp (κ * (3 * s)) * Real.exp (-(κ * (3 * s)))) *
            ((3 * s) ^ n / (3 * s) ^ n) := by ring
        _ = 1 := by rw [h1, h2, one_mul]
    have hcs : Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2)) ≤
        2 * 3 ^ n / s ^ 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), mul_pow, pow_add]
      have hpos : 0 ≤ 3 ^ n * s ^ n * s ^ 2 := by positivity
      nlinarith
    calc a = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
          (ENNReal.ofReal (Real.exp (-(κ * (3 * s))) / (3 * s) ^ n) * a) := by
          rw [← mul_assoc, hcinv, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n) *
          (ENNReal.ofReal (1 / s ^ (n + 2)) * I₂) := mul_le_mul_right (hM.trans hJ) _
      _ = ENNReal.ofReal (Real.exp (κ * (3 * s)) * (3 * s) ^ n * (1 / s ^ (n + 2))) * I₂ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc]
      _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hcs) _
  -- the final absorption argument (pure `ℝ≥0∞` arithmetic)
  have hfinal : ∀ (ω s lam : ℝ) (a I₂ X₁ X₂ : ℝ≥0∞), 0 < ω → 0 < s →
      72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 → ENNReal.ofReal (ω * s ^ n / 2) ≤ a →
      a ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) →
      a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ →
      I₂ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a + ENNReal.ofReal (18 * s ^ 2) * X₁ +
        ENNReal.ofReal (18 * s ^ 2) * X₂ →
      ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
    intro ω s lam a I₂ X₁ X₂ hω hs hlam2 ha_lower ha_upper haI hI
    have e1 : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) =
        ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      ring
    have e2 : ENNReal.ofReal (36 * 3 ^ n) =
        ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * ENNReal.ofReal (18 * s ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      ring
    have hmain : a ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
        ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      calc a ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * I₂ := haI
        _ ≤ ENNReal.ofReal (2 * 3 ^ n / s ^ 2) * (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * a +
            ENNReal.ofReal (18 * s ^ 2) * X₁ + ENNReal.ofReal (18 * s ^ 2) * X₂) :=
            mul_le_mul_right hI _
        _ = ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
            ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
            rw [e1, e2]
            ring
    have hlamterm : ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a ≤
        ENNReal.ofReal (ω * s ^ n / 4) := by
      calc ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a
          ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) :=
            mul_le_mul_right ha_upper _
        _ = ENNReal.ofReal (72 * 15 ^ n * lam ^ 2 * (ω * s ^ n)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (15 : ℝ) ^ n = 3 ^ n * 5 ^ n by rw [← mul_pow]; norm_num]
            ring
        _ ≤ ENNReal.ofReal (1 / 4 * (ω * s ^ n)) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right hlam2 (by positivity)
        _ = ENNReal.ofReal (ω * s ^ n / 4) := by
            congr 1
            ring
    have hfin : ENNReal.ofReal (ω * s ^ n / 4) ≤ ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
      have h1 : ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4) ≤
          ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := by
        calc ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (ω * s ^ n / 4)
            = ENNReal.ofReal (ω * s ^ n / 2) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1
              ring
          _ ≤ a := ha_lower
          _ ≤ ENNReal.ofReal (36 * 3 ^ n * lam ^ 2) * a +
              ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) := hmain
          _ ≤ ENNReal.ofReal (ω * s ^ n / 4) + ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂) :=
              add_le_add hlamterm le_rfl
      exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp h1
    calc ENNReal.ofReal (s ^ n) = ENNReal.ofReal (4 / ω) * ENNReal.ofReal (ω * s ^ n / 4) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [div_mul_div_comm, eq_div_iff (by positivity)]
          ring
      _ ≤ ENNReal.ofReal (4 / ω) * (ENNReal.ofReal (36 * 3 ^ n) * (X₁ + X₂)) :=
          mul_le_mul_right hfin _
      _ = ENNReal.ofReal (144 * 3 ^ n / ω) * (X₁ + X₂) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  -- Step 0: the constants `λ₀ = (288·15ⁿ)^{-1/2}` and `C₉ = 144·3ⁿ/ω`
  have hV_pos : 0 < unitBallVolume n := by
    unfold unitBallVolume
    exact measure_ball_pos _ _ one_pos
  have hV_lt : unitBallVolume n < ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, ω = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hω_pos : 0 < ω := by
    rw [hω_def]
    exact ENNReal.toReal_pos hV_pos.ne' hV_lt.ne
  have hV_eq : unitBallVolume n = ENNReal.ofReal ω := by
    rw [hω_def, ENNReal.ofReal_toReal hV_lt.ne]
  refine ⟨1 / Real.sqrt (288 * 15 ^ n), 144 * 3 ^ n / ω, by positivity, by positivity, ?_⟩
  intro μ τ T₀ F ξ σ₀ κ lam hσ₀ hκ hκσ hlam hlam₀ hξ hF hDa hDb hM2 η hη
  obtain ⟨⟨hηF, hηS⟩, hηξ'⟩ := hη
  have hηξ : dist η ξ ≤ σ₀ / 4 := mem_closedBall.mp hηξ'
  -- `72·15ⁿ·λ² ≤ 1/4` for `0 ≤ λ ≤ λ₀`
  have hlam2 : 72 * 15 ^ n * lam ^ 2 ≤ 1 / 4 := by
    have hpos : (0 : ℝ) < 288 * 15 ^ n := by positivity
    have hsq : lam ^ 2 ≤ 1 / (288 * 15 ^ n) := by
      have h1 : lam ^ 2 ≤ (1 / Real.sqrt (288 * 15 ^ n)) ^ 2 := pow_le_pow_left₀ hlam hlam₀ 2
      rwa [div_pow, Real.sq_sqrt hpos.le, one_pow] at h1
    calc 72 * 15 ^ n * lam ^ 2 ≤ 72 * 15 ^ n * (1 / (288 * 15 ^ n)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 1 / 4 := by
          rw [mul_one_div, div_eq_iff hpos.ne']
          ring
  -- Step 1: nearest point of the support
  have hSc : IsClosed μ.support := Measure.isClosed_support
  have hSne : μ.support.Nonempty := ⟨ξ, hξ⟩
  have hd_pos : 0 < Metric.infDist η μ.support := (hSc.notMem_iff_infDist_pos hSne).mp hηS
  have hd_le : Metric.infDist η μ.support ≤ dist η ξ := Metric.infDist_le_dist_of_mem hξ
  obtain ⟨y, hyS, hyd⟩ := hSc.exists_infDist_eq_dist hSne η
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Metric.infDist η μ.support / 2 := ⟨_, rfl⟩
  have hs : 0 < s := by
    rw [hs_def]
    positivity
  have h2s : 2 * s ≤ dist η ξ := by
    rw [hs_def]
    linarith
  have hyη : dist y η = 2 * s := by
    rw [dist_comm, ← hyd, hs_def]
    ring
  have hs8 : s ≤ σ₀ / 8 := by linarith
  have hyξ : dist y ξ ≤ σ₀ / 2 := by linarith [dist_triangle y η ξ]
  refine ⟨s, y, hyS, hs, h2s, hyη, ?_⟩
  -- Step 2: the small ball around `η` misses the support
  have hμs0 : μ (closedBall η s) = 0 := by
    have hsub : closedBall η s ⊆ μ.supportᶜ := by
      intro x hx
      rw [mem_compl_iff]
      intro hxS
      have h1 := Metric.infDist_le_dist_of_mem (x := η) hxS
      have h2 : dist x η ≤ s := mem_closedBall.mp hx
      rw [dist_comm] at h1
      linarith
    exact measure_mono_null hsub (Measure.measure_compl_support (μ := μ))
  -- Step 3: mass bounds `½ωsⁿ ≤ μ(B_{3s}(η)) ≤ 2·5ⁿωsⁿ`
  have hsub1 : closedBall y s ⊆ closedBall η (3 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    linarith [dist_triangle x y η]
  have hsub2 : closedBall η (3 * s) ⊆ closedBall y (5 * s) := by
    intro x hx
    rw [mem_closedBall] at hx ⊢
    have h := dist_triangle x η y
    rw [dist_comm η y] at h
    linarith
  have hDb' := hDb y ⟨hyS, mem_closedBall.mpr hyξ⟩ s hs hs8
  have hDa' := hDa y (mem_closedBall.mpr hyξ) (5 * s) (by positivity) (by linarith)
  have ha_lower : ENNReal.ofReal (ω * s ^ n / 2) ≤ μ (closedBall η (3 * s)) := by
    have h1 : ENNReal.ofReal (ω * s ^ n) ≤ 2 * μ (closedBall η (3 * s)) := by
      calc ENNReal.ofReal (ω * s ^ n) = unitBallVolume n * ENNReal.ofReal (s ^ n) := by
            rw [hV_eq, ENNReal.ofReal_mul hω_pos.le]
        _ ≤ 2 * μ (closedBall y s) := hDb'
        _ ≤ 2 * μ (closedBall η (3 * s)) := mul_le_mul_right (measure_mono hsub1) _
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul' h1
  have ha_upper : μ (closedBall η (3 * s)) ≤ ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
    calc μ (closedBall η (3 * s)) ≤ μ (closedBall y (5 * s)) := measure_mono hsub2
      _ ≤ 2 * unitBallVolume n * ENNReal.ofReal ((5 * s) ^ n) := hDa'
      _ = ENNReal.ofReal (2 * 5 ^ n * ω * s ^ n) := by
        rw [hV_eq, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  -- Step 4: monotonicity at `η` with radii `s < 3 s`
  have hM2' := hM2 η s (3 * s) hηξ' hs (by linarith) (by linarith)
  rw [hμs0, mul_zero, zero_add] at hM2'
  have hJ : ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ ≤
      ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s) \ closedBall η s, ENNReal.ofReal (1 / s ^ (n + 2)) *
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ := by
          refine setLIntegral_mono' (measurableSet_closedBall.diff measurableSet_closedBall) ?_
          intro x hx
          have hx2 : s < ‖x - η‖ := by
            rw [← dist_eq_norm]
            have h := hx.2
            rw [mem_closedBall, not_le] at h
            exact h
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / ‖x - η‖ ^ (n + 2)
              ≤ ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 / s ^ (n + 2) := by
                gcongr
            _ = 1 / s ^ (n + 2) * ‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2 := by ring
      _ = ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s) \ closedBall η s,
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (1 / s ^ (n + 2)) * ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ :=
          mul_le_mul_right (lintegral_mono_set sdiff_subset) _
  -- Step 5: the exponential factor
  have hκs : κ * (3 * s) ≤ 3 / 8 := by nlinarith [mul_le_mul_of_nonneg_left hs8 hκ]
  have ha_I2 := hexpb κ s _ _ _ hκ hs hκs hM2' hJ
  -- Step 6: pointwise bound on the ball `B_{3s}(η)`
  obtain ⟨M, hM_def⟩ : ∃ M : Set (Euclid (n + k)),
      M = toMeasurable μ (closedBall η (3 * s) \ F) := ⟨_, rfl⟩
  have hMmeas : MeasurableSet M := by
    rw [hM_def]
    exact measurableSet_toMeasurable _ _
  have hMsub : closedBall η (3 * s) \ F ⊆ M := by
    rw [hM_def]
    exact subset_toMeasurable _ _
  have hMmu : μ M = μ (closedBall η (3 * s) \ F) := by
    rw [hM_def]
    exact measure_toMeasurable _
  have hpt : ∀ x ∈ closedBall η (3 * s),
      ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ≤
        ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
          M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
          ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
            ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro x hx
    have hxr : ‖x - η‖ ≤ 3 * s := by
      rw [← dist_eq_norm]
      exact mem_closedBall.mp hx
    apply hptE T₀ (τ x) (x - η) s lam _ hxr
    by_cases hxF : x ∈ F
    · left
      exact (hF x hxF η hηF).trans (mul_le_mul_of_nonneg_left hxr hlam)
    · right
      exact Set.indicator_of_mem (hMsub ⟨hx, hxF⟩) _
  -- Step 7: integration over `B_{3s}(η)`
  have hI2 : ∫⁻ x in closedBall η (3 * s),
        ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
        ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
        ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
          (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
    calc ∫⁻ x in closedBall η (3 * s),
          ENNReal.ofReal (‖(x - η) - (τ x).starProjection (x - η)‖ ^ 2) ∂μ
        ≤ ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x +
            ENNReal.ofReal (18 * s ^ 2) * ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ∂μ :=
          setLIntegral_mono' measurableSet_closedBall hpt
      _ = ∫⁻ x in closedBall η (3 * s), (ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) +
            M.indicator (fun _ => ENNReal.ofReal (18 * s ^ 2)) x) ∂μ +
          ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (18 * s ^ 2) *
            ENNReal.ofReal (∑ i : Fin (n + k),
              ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ :=
          lintegral_add_left ((measurable_const.indicator hMmeas).const_add _) _
      _ = ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (M ∩ closedBall η (3 * s)) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_indicator_const hMmeas, Measure.restrict_apply hMmeas,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (18 * lam ^ 2 * s ^ 2) * μ (closedBall η (3 * s)) +
            ENNReal.ofReal (18 * s ^ 2) * μ (closedBall η (3 * s) \ F) +
          ENNReal.ofReal (18 * s ^ 2) * ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal
            (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
                T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ := by
          have hμM : μ (M ∩ closedBall η (3 * s)) ≤ μ (closedBall η (3 * s) \ F) :=
            (measure_mono inter_subset_left).trans hMmu.le
          exact add_le_add (add_le_add le_rfl (mul_le_mul_right hμM _)) le_rfl
  -- Step 8: absorption of the `λ²`-term
  exact hfinal ω s lam _ _ _ _ hω_pos hs hlam2 ha_lower ha_upper ha_I2 hI2

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
