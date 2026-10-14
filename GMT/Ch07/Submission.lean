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

/-- **Faces of the unit cubical lattice** (Simon Ch. 6, §5: the `n`-faces `F ∈ 𝓛ₙ` used in the proof
of the deformation theorem 5.1).  Let `n = m + 1` and `p = (z, ι)` with `ι : Fin n → Fin P` strictly
increasing.  The map `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` has coordinates `z_{ι(k)} + y_k` at `ι(k)` and
`zᵢ` off `range ι`, so it is an isometric embedding `ℝⁿ → ℝᴾ` with `Φ_p⁻¹(F_p) = [0, 1]ⁿ` and
`F_p ⊆ range Φ_p`.  As `μHE[n] = volume` on `ℝⁿ`, `Φ_p#μHE[n] = μHE[n]⌞range Φ_p` and `∂[0, 1]ⁿ` is
Lebesgue-null, `Hⁿ⌞F_p = Φ_p#(Lⁿ⌞(0, 1)ⁿ)`; hence `Hⁿ(F_p) = 1` and
`∫_{F_p} f dHⁿ = ∫_{(0, 1)ⁿ} f ∘ Φ_p`.  `F_p` is closed with diameter `≤ √P`, and the non-integer
coordinates of a point of `Φ_p((0, 1)ⁿ)` determine `ι` and `z`, so it lies in no other face
`F_q`. -/
theorem Submission.dor_lmb_fcd_fr_face_geometry : ∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)), StrictMono p.2 → volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ μHE[m + 1] {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = 1 ∧ (μHE[m + 1] : Measure (Euclid P)).restrict {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = Measure.map (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∀ f : Euclid P → ℝ, ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, f x ∂μHE[m + 1] = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, f (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))) ∧ (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}) ∧ (∀ y y' : Euclid (m + 1), dist (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.2 j) (1 : ℝ)) = dist y y') ∧ (∀ x ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, ∀ x' ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, dist x x' ≤ Real.sqrt P) ∧ IsClosed {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∉ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧ (i ∉ Set.range q.2 → x i = q.1 i)} := by
  intro P m p hp
  -- the face map `Φ = Φ_p`, the closed face `F = F_p`, the open cube `Q = Q₁`, the closed cube `C`
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let F : Set (Euclid P) := {x : Euclid P | ∀ i : Fin P,
    (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}
  let Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  let C : Set (Euclid (m + 1)) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1}
  show volume Q = 1 ∧ μHE[m + 1] F = 1 ∧
    (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) ∧
    (∀ f : Euclid P → ℝ, ∫ x in F, f x ∂μHE[m + 1] = ∫ y in Q, f (Φ y)) ∧
    (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F) ∧
    (∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y') ∧
    (∀ x ∈ F, ∀ x' ∈ F, dist x x' ≤ Real.sqrt P) ∧ IsClosed F ∧
    ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p →
      ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → Φ y ∉ {x : Euclid P | ∀ i : Fin P,
        (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧
          (i ∉ Set.range q.2 → x i = q.1 i)}
  have hinj : Injective p.2 := hp.injective
  -- Step 1: coordinates of `Φ`
  have hcoord : ∀ y i, Φ y i = p.1 i + ∑ j, if i = p.2 j then y j else 0 := by
    intro y i
    simp [Φ, Pi.single_apply]
  have hcoord_mem : ∀ y k, Φ y (p.2 k) = p.1 (p.2 k) + y k := by
    intro y k
    rw [hcoord]
    simp [hinj.eq_iff]
  have hcoord_nmem : ∀ y i, i ∉ range p.2 → Φ y i = p.1 i := by
    intro y i hi
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hi ⟨j, h.symm⟩
  -- Step 2: `Φ` is an isometry, hence a measurable embedding
  have hdist : ∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y' := by
    intro y y'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    symm
    refine Fintype.sum_of_injective p.2 hinj _ _ (fun i hi => ?_) (fun k => ?_)
    · rw [hcoord_nmem y i hi, hcoord_nmem y' i hi, dist_self]
      simp
    · rw [hcoord_mem, hcoord_mem, dist_add_left]
  have hiso : Isometry Φ := Isometry.of_dist_eq hdist
  have hemb : MeasurableEmbedding Φ := hiso.isClosedEmbedding.measurableEmbedding
  -- Step 3: `Φ` maps the closed cube `C` into `F`, `F ⊆ range Φ` and `Φ⁻¹(F) = C`
  have hCF : ∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F := by
    intro y hy i
    constructor
    · rintro ⟨k, rfl⟩
      rw [hcoord_mem]
      constructor <;> linarith [(hy k).1, (hy k).2]
    · exact hcoord_nmem y i
  have hFrange : F ⊆ range Φ := by
    intro x hx
    refine ⟨WithLp.toLp 2 fun k => x (p.2 k) - p.1 (p.2 k), PiLp.ext fun i => ?_⟩
    by_cases hi : i ∈ range p.2
    · obtain ⟨k, rfl⟩ := hi
      rw [hcoord_mem]
      simp
    · rw [hcoord_nmem _ i hi]
      exact ((hx i).2 hi).symm
  have hpreF : Φ ⁻¹' F = C := by
    ext y
    refine ⟨fun hy k => ?_, hCF y⟩
    have h := (hy (p.2 k)).1 ⟨k, rfl⟩
    rw [hcoord_mem] at h
    constructor <;> linarith [h.1, h.2]
  -- Step 4: `volume Q = volume C = 1`
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  have hQ_eq : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hC_eq : C = WithLp.ofLp ⁻¹' (Set.Icc (0 : Fin (m + 1) → ℝ) 1) := by
    ext y
    simp [C, Pi.le_def, forall_and]
  have hQmeas : MeasurableSet Q := by
    rw [hQ_eq]
    exact hvol.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hvolQ : volume Q = 1 := by
    rw [hQ_eq, hvol.measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hvolC : volume C = 1 := by
    rw [hC_eq, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp
  have hQC : volume.restrict C = volume.restrict Q := by
    refine (Measure.restrict_congr_set ?_).symm
    refine ae_eq_of_subset_of_measure_ge (fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩)
      (hvolC.trans hvolQ.symm).le hQmeas.nullMeasurableSet ?_
    rw [hvolC]
    exact ENNReal.one_ne_top
  -- Step 5: `F` is closed
  have hcont : ∀ i : Fin P, Continuous fun x : Euclid P => x i := fun i =>
    PiLp.continuous_apply 2 _ i
  have hFclosed : IsClosed F := by
    have hF : F = ⋂ i : Fin P, {x : Euclid P | (i ∈ Set.range p.2 →
        (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} :=
      Set.ofPred_forall _
    rw [hF]
    refine isClosed_iInter fun i =>
      (isClosed_imp isOpen_const ?_).inter (isClosed_imp isOpen_const ?_)
    · exact (isClosed_le continuous_const (hcont i)).inter (isClosed_le (hcont i) continuous_const)
    · exact isClosed_eq (hcont i) continuous_const
  have hFmeas : MeasurableSet F := hFclosed.measurableSet
  -- Step 6: `Hⁿ⌞F = Φ#(volume⌞Q)`
  have hmeas :
      (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) := by
    have h1 : Measure.map Φ (volume : Measure (Euclid (m + 1))) =
        (μHE[m + 1] : Measure (Euclid P)).restrict (range Φ) := by
      rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rw [← hQC, ← hpreF, ← hemb.restrict_map, h1, Measure.restrict_restrict hFmeas,
      inter_eq_left.2 hFrange]
  -- Step 7: `Hⁿ(F) = 1`
  have hFmass : μHE[m + 1] F = 1 := by
    have h := congrArg (fun μ : Measure (Euclid P) => μ univ) hmeas
    simp only [Measure.restrict_apply_univ] at h
    rw [h, hemb.map_apply, preimage_univ, Measure.restrict_apply_univ, hvolQ]
  refine ⟨hvolQ, hFmass, hmeas, fun f => ?_, hCF, hdist, ?_, hFclosed, ?_⟩
  -- Step 8: the integral formula
  · rw [hmeas, hemb.integral_map]
  -- Step 9: `diam F ≤ √P`
  · intro x hx x' hx'
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (x i) (x' i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => pow_le_one₀ dist_nonneg ?_
          by_cases hi : i ∈ range p.2
          · have h := (hx i).1 hi
            have h' := (hx' i).1 hi
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [h.1, h.2, h'.1, h'.2]
          · rw [(hx i).2 hi, (hx' i).2 hi, dist_self]
            exact zero_le_one
      _ = P := by simp
  -- Step 10: the open face `Φ(Q)` meets no other closed face
  · intro q hq hqp y hy hx
    apply hqp
    have hsub : range p.2 ⊆ range q.2 := by
      rintro _ ⟨k, rfl⟩
      by_contra hk
      have h := (hx (p.2 k)).2 hk
      rw [hcoord_mem] at h
      have a1 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) := by linarith [(hy k).1]
      have a2 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [(hy k).2]
      have b1 : p.1 (p.2 k) < q.1 (p.2 k) := by exact_mod_cast a1
      have b2 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a2
      omega
    have hrange : range p.2 = range q.2 := by
      apply Set.eq_of_subset_of_card_le hsub
      rw [Set.card_range_of_injective hq.injective, Set.card_range_of_injective hinj]
    have h2 : p.2 = q.2 := (hp.range_inj_of_wellFoundedLT hq).1 hrange
    have h1 : p.1 = q.1 := by
      funext i
      by_cases hi : i ∈ range p.2
      · obtain ⟨k, rfl⟩ := hi
        have h := (hx (p.2 k)).1 (hrange ▸ ⟨k, rfl⟩)
        rw [hcoord_mem] at h
        have a1 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [h.1, (hy k).2]
        have a2 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) + 1 := by linarith [h.2, (hy k).1]
        have b1 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a1
        have b2 : p.1 (p.2 k) < q.1 (p.2 k) + 1 := by exact_mod_cast a2
        omega
      · have h : (p.1 i : ℝ) = q.1 i := by
          rw [← hcoord_nmem y i hi]
          exact (hx i).2 (hrange ▸ hi)
        exact_mod_cast h
    exact Prod.ext h1.symm h2.symm
/-- **Coordinate covectors** (Simon Ch. 6, §1, 1.1, 1.2 and 1.5).  For `J : Fin k → Fin P`,
`dx^J = dx^{J(0)} ∧ ⋯ ∧ dx^{J(k−1)}` is the alternatization of the continuous multilinear map
`v ↦ ∏ᵣ (v_r)_{J(r)}`, so `dx^J(v) = Σ_σ sign σ ∏ᵣ (v_{σ(r)})_{J(r)}`.  At `e_I` the `σ`-term is
`[I ∘ σ = J]`; for strictly increasing `I, J`, `I ∘ σ = J` makes `σ` strictly increasing, hence
`σ = id` and `I = J`, so `dx^J(e_I) = [I = J]`.  For an injective family of strictly increasing
`J_l`, `(Σ_l c_l dx^{J_l})(e_I)` is `c_l` if `I = J_l` and `0` if `I ∉ range J`; summing the
squares over strictly increasing `I` gives `covectorEuclideanNorm (Σ_l c_l dx^{J_l}) = √(Σ_l c_l²)`.
-/
theorem Submission.dor_lmb_fcd_fr_coordinate_covectors : ∀ (P k : ℕ), ∃ dx : (Fin k → Fin P) → Covector (Euclid P) k, (∀ I J : Fin k → Fin P, StrictMono I → StrictMono J → dx J (fun r => EuclideanSpace.single (I r) (1 : ℝ)) = if I = J then 1 else 0) ∧ ∀ (N : ℕ) (J : Fin N → Fin k → Fin P) (c : Fin N → ℝ), Function.Injective J → (∀ l, StrictMono (J l)) → covectorEuclideanNorm (∑ l, c l • dx (J l)) = Real.sqrt (∑ l, c l ^ 2) := by
  intro P k
  classical
  -- Step 1: `dx^J` is the alternatization of `v ↦ ∏ᵣ (v_r)_{J(r)}`
  let dx : (Fin k → Fin P) → Covector (Euclid P) k := fun J =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
        (fun r => EuclideanSpace.proj (J r)))
  have hdx : ∀ (J : Fin k → Fin P) (v : Fin k → Euclid P),
      dx J v = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • ∏ r, (v (σ r)) (J r) := by
    intro J v
    simp only [dx, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, Function.comp_apply]
    rfl
  -- Step 2: if `I ∘ σ = J` with `I, J` strictly increasing, then `σ = id` and `I = J`
  have hperm : ∀ (I J : Fin k → Fin P), StrictMono I → StrictMono J →
      ∀ σ : Equiv.Perm (Fin k), (∀ r, I (σ r) = J r) → σ = 1 ∧ I = J := by
    intro I J hI hJ σ hσ
    have hσmono : StrictMono σ := by
      intro a b hab
      have : I (σ a) < I (σ b) := by rw [hσ a, hσ b]; exact hJ hab
      exact hI.lt_iff_lt.mp this
    have hrange : Set.range σ = Set.range (id : Fin k → Fin k) := by
      rw [Set.range_id]; exact σ.surjective.range_eq
    have hid : (σ : Fin k → Fin k) = id :=
      (StrictMono.range_inj_of_wellFoundedLT hσmono strictMono_id).mp hrange
    have hσ1 : σ = 1 := by
      ext r; simp [congrFun hid r]
    refine ⟨hσ1, ?_⟩
    funext r
    have := hσ r
    rw [hσ1] at this
    simpa using this
  -- duality `dx^J(e_I) = [I = J]` for strictly increasing `I, J`
  have hdual : ∀ I J : Fin k → Fin P, StrictMono I → StrictMono J →
      dx J (fun r => EuclideanSpace.single (I r) (1 : ℝ)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    rw [hdx]
    have hterm : ∀ σ : Equiv.Perm (Fin k),
        ∏ r, (EuclideanSpace.single (I (σ r)) (1 : ℝ)) (J r) =
          if (∀ r, I (σ r) = J r) then 1 else 0 := by
      intro σ
      split_ifs with h
      · refine Finset.prod_eq_one fun r _ => ?_
        rw [h r]; simp
      · push Not at h
        obtain ⟨r, hr⟩ := h
        refine Finset.prod_eq_zero (Finset.mem_univ r) ?_
        simp [Ne.symm hr]
    simp_rw [hterm]
    split_ifs with hIJ
    · subst hIJ
      rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin k))]
      · simp
      · intro σ _ hσ
        rw [ite_eq_right]
        · simp
        · intro h
          exact hσ (hperm I I hI hI σ h).1
      · simp
    · refine Finset.sum_eq_zero fun σ _ => ?_
      rw [ite_eq_right]
      · simp
      · intro h
        exact hIJ (hperm I J hI hJ σ h).2
  refine ⟨dx, hdual, ?_⟩
  intro N J c hJinj hJmono
  -- Step 3: values of `Σ_l c_l dx^{J_l}` on the coordinate frames `e_I`
  have hval : ∀ I : Fin k → Fin P, StrictMono I →
      (∑ l, c l • dx (J l)) (fun r => EuclideanSpace.basisFun (Fin P) ℝ (I r)) =
        ∑ l, if I = J l then c l else 0 := by
    intro I hI
    simp only [EuclideanSpace.basisFun_apply]
    rw [ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [ContinuousAlternatingMap.smul_apply, hdual I (J l) hI (hJmono l)]
    split_ifs <;> simp
  -- by injectivity of `J`, at most one `l` has `J_l = I`
  have hsq : ∀ I : Fin k → Fin P,
      (∑ l, if I = J l then c l else 0) ^ 2 = ∑ l, if I = J l then c l ^ 2 else 0 := by
    intro I
    by_cases hex : ∃ l, I = J l
    · obtain ⟨l₀, hl₀⟩ := hex
      have h1 : (∑ l, if I = J l then c l else 0) = c l₀ := by
        rw [Finset.sum_eq_single l₀]
        · simp [hl₀]
        · intro l _ hl
          rw [ite_eq_right]
          intro h
          exact hl (hJinj (h.symm.trans hl₀))
        · simp
      have h2 : (∑ l, if I = J l then c l ^ 2 else 0) = c l₀ ^ 2 := by
        rw [Finset.sum_eq_single l₀]
        · simp [hl₀]
        · intro l _ hl
          rw [ite_eq_right]
          intro h
          exact hl (hJinj (h.symm.trans hl₀))
        · simp
      rw [h1, h2]
    · push Not at hex
      simp [hex]
  -- Step 4: sum the squares over strictly increasing `I` and exchange the finite sums
  unfold covectorEuclideanNorm
  congr 1
  calc (∑ I : Fin k → Fin P, if StrictMono I then
          ((∑ l, c l • dx (J l)) (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
      = ∑ I : Fin k → Fin P, ∑ l, (if I = J l then c l ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        split_ifs with hI
        · rw [hval I hI, hsq I]
        · symm
          refine Finset.sum_eq_zero fun l _ => ?_
          rw [ite_eq_right]
          rintro rfl
          exact hI (hJmono l)
    _ = ∑ l, ∑ I : Fin k → Fin P, (if I = J l then c l ^ 2 else 0) := Finset.sum_comm
    _ = ∑ l, c l ^ 2 := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp

/-- **Divergence-form test forms near a face** (Simon Ch. 6, (28), by the arguments of 2.34–2.35).
For the face `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` and `g : ℝⁿ → ℝⁿ` smooth with compact support and
`|g| ≤ 1`, put `ω = χ Σ_l (-1)^l (g_l ∘ π) dx^{J_l}` with `J_l = ι ∘ succAbove l`, the face
coordinates `π(x)_k = x_{ι(k)} - z_{ι(k)}` and the normal cut-off `χ = η(|x - Φ_p(π x)|²)`, `η = 1`
on `[0, δ²/2]` and `η = 0` on `[δ², ∞)`.  The `dx^{J_l}` are orthonormal, so `|ω| = χ |g ∘ π| ≤ 1`;
`spt ω` lies in `{|x - Φ_p(π x)| ≤ δ} ∩ π⁻¹(spt g)`; and near the face
`ω(x)(e_{J_i}) = (-1)^i gᵢ(π x)`, so the alternating-sum formula for `d` gives
`dω(Φ_p y)(e_p) = Σᵢ ∂ᵢgᵢ(y) = trace Dg(y)`. -/
theorem Submission.dor_lmb_fcd_fr_divergence_form : ∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) (g : Euclid (m + 1) → Euclid (m + 1)) (δ : ℝ), StrictMono p.2 → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → 0 < δ → ∃ ω : TestFormOn (univ : Set (Euclid P)) m, (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ (∀ x ∈ tsupport (ω : DifferentialForm (Euclid P) m), ∃ y ∈ tsupport g, dist x (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) ≤ δ) ∧ ∀ y : Euclid (m + 1), exteriorDerivative (ω : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
  intro P m p g δ hι hg hgc hg1 hδ
  -- 1. coordinate covectors `dx^J`
  obtain ⟨dx, hdx, hdxn⟩ := Submission.dor_lmb_fcd_fr_coordinate_covectors P m
  -- 2. the frames `J l = ι ∘ succAbove l`: strictly increasing and pairwise distinct
  let J : Fin (m + 1) → Fin m → Fin P := fun l r => p.2 (l.succAbove r)
  have hJ : ∀ l, StrictMono (J l) := fun l => hι.comp (Fin.strictMono_succAbove l)
  have hJinj : Injective J := by
    intro l l' h
    apply Fin.succAbove_left_injective
    funext r
    exact hι.injective (congrFun h r)
  -- the face map `Φ` and the face coordinates `π x = πL x - πL z`, with `π ∘ Φ = id`
  let z : Euclid P := WithLp.toLp 2 (fun i => (p.1 i : ℝ))
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    z + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let πL : Euclid P →L[ℝ] Euclid (m + 1) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => EuclideanSpace.proj (p.2 k))
  have hπL : ∀ x k, πL x k = x (p.2 k) := fun x k => rfl
  have hπLe : ∀ j, πL (EuclideanSpace.single (p.2 j) (1 : ℝ)) = EuclideanSpace.single j 1 := by
    intro j
    ext k
    simp [hπL, PiLp.single_apply, hι.injective.eq_iff]
  let π : Euclid P → Euclid (m + 1) := fun x => πL x - πL z
  have hπΦ : ∀ y, π (Φ y) = y := by
    intro y
    simp only [π, Φ, map_add, add_sub_cancel_left, map_sum, map_smul, hπLe]
    ext k
    simp [Pi.single_apply]
  -- the squared normal distance `ν x = |x - Φ(π x)|²` and the cut-off `χ = η ∘ ν`
  let ν : Euclid P → ℝ := fun x => ‖x - Φ (π x)‖ ^ 2
  let χ : Euclid P → ℝ := fun x => Real.smoothTransition (2 - 2 * ν x / δ ^ 2)
  -- 3. the form `ω = Σ_l (-1)^l χ (g_l ∘ π) dx^{J l}`
  let c : Fin (m + 1) → Euclid P → ℝ := fun l x => (-1) ^ (l : ℕ) * χ x * g (π x) l
  let ω : DifferentialForm (Euclid P) m := fun x => ∑ l, c l x • dx (J l)
  have hcoord : ∀ j : Fin (m + 1), ContDiff ℝ (⊤ : ℕ∞) fun y : Euclid (m + 1) => y j :=
    fun j => (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).contDiff
  have hπ : ContDiff ℝ (⊤ : ℕ∞) π := πL.contDiff.sub contDiff_const
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ :=
    contDiff_const.add (ContDiff.sum fun j _ => (hcoord j).smul contDiff_const)
  have hν : ContDiff ℝ (⊤ : ℕ∞) ν := (contDiff_norm_sq ℝ).comp (contDiff_id.sub (hΦ.comp hπ))
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_const.mul hν).div_const _))
  have hgπ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) fun x => g (π x) l := fun l =>
    (hcoord l).comp (hg.comp hπ)
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω :=
    ContDiff.sum fun l _ => ((contDiff_const.mul hχ).mul (hgπ l)).smul contDiff_const
  -- `χ = 0` where `ν ≥ δ²` and `χ = 1` where `2ν ≤ δ²`
  have hχ0 : ∀ x, δ ^ 2 ≤ ν x → χ x = 0 := by
    intro x hx
    apply Real.smoothTransition.zero_of_nonpos
    have : 2 ≤ 2 * ν x / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have hχ1 : ∀ x, 2 * ν x ≤ δ ^ 2 → χ x = 1 := by
    intro x hx
    apply Real.smoothTransition.one_of_one_le
    have : 2 * ν x / δ ^ 2 ≤ 1 := by
      rw [div_le_one₀ (by positivity)]
      exact hx
    linarith
  -- `spt ω ⊆ Z = {ν ≤ δ²} ∩ π⁻¹(spt g)`, and `|x - Φ(π x)| ≤ δ` on `Z`
  have hω0 : ∀ x, (χ x = 0 ∨ g (π x) = 0) → ω x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases hx with h | h <;> simp [c, h]
  have hsuppZ : tsupport ω ⊆ {x | ν x ≤ δ ^ 2} ∩ π ⁻¹' tsupport g := by
    refine closure_minimal (fun x hx => ⟨?_, ?_⟩)
      ((isClosed_le hν.continuous continuous_const).inter
        ((isClosed_tsupport g).preimage hπ.continuous))
    · by_contra h
      exact hx (hω0 x (Or.inl (hχ0 x (le_of_not_ge h))))
    · by_contra h
      exact hx (hω0 x (Or.inr (image_eq_zero_of_notMem_tsupport h)))
  have hZδ : ∀ x, ν x ≤ δ ^ 2 → dist x (Φ (π x)) ≤ δ := fun x hx => by
    rw [dist_eq_norm]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).mp hx
  -- compact support: `Z ⊆ cthickening δ (Φ(spt g))`
  have hcpt : HasCompactSupport ω :=
    ((hgc.isCompact.image hΦ.continuous).cthickening (r := δ)).of_isClosed_subset
      (isClosed_tsupport ω) (hsuppZ.trans fun x hx =>
        Metric.mem_cthickening_of_dist_le x (Φ (π x)) δ _ (mem_image_of_mem Φ hx.2)
          (hZδ x hx.1))
  refine ⟨⟨ω, ⟨hω, hcpt⟩, subset_univ _⟩, fun x => ?_, fun x hx => ?_, fun y => ?_⟩
  · -- 4. (i) `|ω(x)| = χ(x) |g(π x)| ≤ 1`
    show covectorEuclideanNorm (∑ l, c l x • dx (J l)) ≤ 1
    rw [hdxn (m + 1) J (fun l => c l x) hJinj hJ]
    refine (Real.sqrt_le_sqrt ?_).trans_eq Real.sqrt_one
    calc ∑ l, c l x ^ 2 = χ x ^ 2 * ‖g (π x)‖ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [c]
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm (l : ℕ) 2, pow_mul, neg_one_sq, one_pow,
            one_mul]
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (Real.smoothTransition.nonneg _)
          (Real.smoothTransition.le_one _)) (pow_le_one₀ (norm_nonneg _) (hg1 _)) (sq_nonneg _)
          zero_le_one
      _ = 1 := one_mul 1
  · -- 5. (ii) `x` is within `δ` of `Φ(π x)`, `π x ∈ spt g`
    obtain ⟨hxν, hxg⟩ := hsuppZ hx
    exact ⟨π x, hxg, hZδ x hxν⟩
  · -- 6. (iii) near `Φ y`, `χ = 1`, so `ω` agrees with `ω₀ = Σ_l (-1)^l (g_l ∘ π) dx^{J l}`
    let ω₀ : DifferentialForm (Euclid P) m := fun x =>
      ∑ l : Fin (m + 1), ((-1) ^ (l : ℕ) * g (π x) l) • dx (J l)
    have hω₀ : ContDiff ℝ (⊤ : ℕ∞) ω₀ :=
      ContDiff.sum fun l _ => (contDiff_const.mul (hgπ l)).smul contDiff_const
    have hνΦ : 2 * ν (Φ y) < δ ^ 2 := by
      simp only [ν, hπΦ, sub_self, norm_zero]
      simpa using pow_pos hδ 2
    have hloc : ω =ᶠ[𝓝 (Φ y)] ω₀ := by
      filter_upwards [(isOpen_lt (continuous_const.mul hν.continuous) continuous_const).mem_nhds
        hνΦ] with x hx
      simp only [ω, ω₀, c, hχ1 x (le_of_lt hx), mul_one]
    have hd : exteriorDerivative ω (Φ y) = exteriorDerivative ω₀ (Φ y) := hloc.extDeriv_eq
    -- `ω₀(x)(e_{J i}) = (-1)^i g_i(π x)`
    have hω₀e : ∀ i : Fin (m + 1),
        (fun x => ω₀ x (i.removeNth fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) =
          fun x => (-1) ^ (i : ℕ) * g (π x) i := by
      intro i
      funext x
      show (∑ l : Fin (m + 1), ((-1) ^ (l : ℕ) * g (π x) l) • dx (J l))
          (fun r => EuclideanSpace.single (J i r) (1 : ℝ)) = _
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single i]
      · rw [ContinuousAlternatingMap.smul_apply, hdx _ _ (hJ i) (hJ i), ite_eq_left rfl,
          smul_eq_mul, mul_one]
      · intro l _ hl
        rw [ContinuousAlternatingMap.smul_apply, hdx _ _ (hJ i) (hJ l),
          ite_eq_right fun h => hl (hJinj h).symm, smul_zero]
      · exact fun h => absurd (Finset.mem_univ i) h
    -- `D[(-1)^i g_i ∘ π](Φ y)(e_{ι i}) = (-1)^i (Dg(y) ê_i)_i`
    have hderiv : ∀ i : Fin (m + 1),
        fderiv ℝ (fun x => (-1) ^ (i : ℕ) * g (π x) i) (Φ y)
          (EuclideanSpace.single (p.2 i) (1 : ℝ)) =
          (-1) ^ (i : ℕ) * fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ)) i := by
      intro i
      have hπd : HasFDerivAt π πL (Φ y) := πL.hasFDerivAt.sub_const (πL z)
      have hgd : HasFDerivAt g (fderiv ℝ g y) (π (Φ y)) := by
        rw [hπΦ]
        exact (hg.differentiable (by simp) y).hasFDerivAt
      have h2 : fderiv ℝ (fun x => (-1) ^ (i : ℕ) * g (π x) i) (Φ y) =
          ((-1 : ℝ) ^ (i : ℕ)) • ((EuclideanSpace.proj i).comp ((fderiv ℝ g y).comp πL)) :=
        (((EuclideanSpace.proj i).hasFDerivAt.comp (Φ y) (hgd.comp (Φ y) hπd)).const_mul
          ((-1 : ℝ) ^ (i : ℕ))).fderiv
      rw [h2, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, hπLe, smul_eq_mul]
      rfl
    show exteriorDerivative ω (Φ y) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ)) = _
    rw [hd, exteriorDerivative_apply (hω₀.differentiable (by simp)).differentiableAt,
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hω₀e i, hderiv i, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul, ContinuousLinearMap.coe_coe, zsmul_eq_mul]
    push_cast
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- **Boundary variation on the faces** (Simon Ch. 6, proof of 5.1, (28), second part, by the
arguments of the Constancy Theorem 2.34 and of 2.35).  Let `Q(ω) = Σ_{p∈s} ∫_{Q₁} u_p ω(Φ_p)(e_p)`
with `M(∂Q) < ∞`.  The sets `W_p = {x : dist(x, F_p) < dist(x, F_q) for q ∈ s ∖ {p}}` are
pairwise disjoint, so disjointly supported admissible forms add up to an admissible form and
`Σ_{p∈s} M_{W_p}(∂Q) ≤ M(∂Q)`; put `V_p = M_{W_p}(∂Q)`.  For an admissible `g`, the compact
`Φ_p(spt g)` has positive distance from the other faces, so the divergence form `ω` of `g` is
supported in `W_p`, and `∂Q(ω) = Q(dω) = ∫_{Q₁} u_p div g` since `dω` vanishes on the other faces;
hence `∫_{Q₁} u_p div g ≤ M_{W_p}(∂Q) = V_p`. -/
theorem Submission.dor_lmb_fcd_fr_boundary_variation : ∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (u : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → ℝ) (Q : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) → Q.boundary.mass ≠ ∞ → ∃ V : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℝ, (∀ p ∈ s, 0 ≤ V p) ∧ ENNReal.ofReal (∑ p ∈ s, V p) ≤ Q.boundary.mass ∧ ∀ p ∈ s, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V p := by
  intro P m s u Q hs hQ hmass
  classical
  -- the parametrizations `Φ_p`, the closed faces `F_p` and the sets `W_p`
  let Φ : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let F : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P) := fun p =>
    {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧
      (i ∉ Set.range p.2 → x i = p.1 i)}
  let W : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P) := fun p =>
    {x | ∀ q ∈ s, q ≠ p → infDist x (F p) < infDist x (F q)}
  -- face geometry: `Φ_p` maps the closed cube into `F_p`, is continuous, `F_p` is closed, and
  -- `Φ_p` maps the open cube off every other face
  have hFG : ∀ p ∈ s, (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ p y ∈ F p) ∧
      Continuous (Φ p) ∧ IsClosed (F p) ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P),
        StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → Φ p y ∉ F q := by
    intro p hp
    obtain ⟨-, -, -, -, h5, h6, -, h8, h9⟩ :=
      Submission.dor_lmb_fcd_fr_face_geometry P m p (hs p hp)
    exact ⟨h5, (Isometry.of_dist_eq h6).continuous, h8, h9⟩
  have hFne : ∀ p ∈ s, (F p).Nonempty := fun p hp =>
    ⟨Φ p 0, (hFG p hp).1 0 fun i => by simp⟩
  -- Step 1: the `W_p`, `p ∈ s`, are pairwise disjoint
  have hWdisj : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → ∀ x, x ∈ W p → x ∉ W q := by
    intro p hp q hq hpq x hxp hxq
    exact lt_asymm (hxp q hq (Ne.symm hpq)) (hxq p hp hpq)
  -- Step 2: `Σ_{p∈s} M_{W_p}(∂Q) ≤ M(∂Q)`
  set T := Q.boundary with hT
  have hadm0 : ∀ V : Set (Euclid P),
      (0 : TestFormOn (univ : Set (Euclid P)) m) ∈ massAdmissibleOn univ m V := by
    intro V
    refine ⟨?_, fun x => ?_⟩ <;> simp
  -- (a) a family of admissible forms, one in each `W_p`
  have hfam : ∀ ω : (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W p),
      ∑ p ∈ s, ENNReal.ofReal (T (ω p)) ≤ T.mass := by
    intro ω
    -- drop the forms with negative value
    let ω' : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → TestFormOn (univ : Set (Euclid P)) m :=
      fun p => if 0 ≤ T (ω p) then (ω p : TestFormOn (univ : Set (Euclid P)) m) else 0
    have hω' : ∀ p, ENNReal.ofReal (T (ω p)) = ENNReal.ofReal (T (ω' p)) ∧ 0 ≤ T (ω' p) ∧
        ω' p ∈ massAdmissibleOn univ m (W p) := by
      intro p
      by_cases h : 0 ≤ T (ω p)
      · have h0 : ω' p = ω p := ite_eq_left h
        rw [h0]
        exact ⟨rfl, h, (ω p).2⟩
      · have h0 : ω' p = 0 := ite_eq_right h
        rw [h0, map_zero, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero]
        exact ⟨(not_le.1 h).le, le_rfl, hadm0 (W p)⟩
    -- the sum is admissible in `ℝ^P`: at each point at most one summand is nonzero
    have hsum_adm : (∑ p ∈ s, ω' p) ∈ massAdmissibleOn univ m univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      have hx : ((∑ p ∈ s, ω' p : TestFormOn (univ : Set (Euclid P)) m) :
          DifferentialForm (Euclid P) m) x =
          ∑ p ∈ s, ((ω' p : TestFormOn (univ : Set (Euclid P)) m) :
            DifferentialForm (Euclid P) m) x := by
        rw [Submodule.coe_sum, Finset.sum_apply]
      rw [hx]
      by_cases hex : ∃ p ∈ s, ((ω' p : TestFormOn (univ : Set (Euclid P)) m) :
          DifferentialForm (Euclid P) m) x ≠ 0
      · obtain ⟨p, hp, hpx⟩ := hex
        have hzero : ∀ q ∈ s, q ≠ p → ((ω' q : TestFormOn (univ : Set (Euclid P)) m) :
            DifferentialForm (Euclid P) m) x = 0 := by
          intro q hq hqp
          by_contra hqx
          exact hWdisj p hp q hq (Ne.symm hqp) x ((hω' p).2.2.1 (subset_tsupport _ hpx))
            ((hω' q).2.2.1 (subset_tsupport _ hqx))
        rw [Finset.sum_eq_single p hzero fun h => absurd hp h]
        exact (hω' p).2.2.2 x
      · have hzero : ∀ p ∈ s, ((ω' p : TestFormOn (univ : Set (Euclid P)) m) :
            DifferentialForm (Euclid P) m) x = 0 := fun p hp =>
          not_not.1 fun hpx => hex ⟨p, hp, hpx⟩
        rw [Finset.sum_eq_zero hzero, covectorEuclideanNorm_zero]
        exact zero_le_one
    calc ∑ p ∈ s, ENNReal.ofReal (T (ω p)) = ∑ p ∈ s, ENNReal.ofReal (T (ω' p)) :=
          Finset.sum_congr rfl fun p _ => (hω' p).1
      _ = ENNReal.ofReal (∑ p ∈ s, T (ω' p)) :=
          (ENNReal.ofReal_sum_of_nonneg fun p _ => (hω' p).2.1).symm
      _ = ENNReal.ofReal (T (∑ p ∈ s, ω' p)) := by rw [map_sum]
      _ ≤ T.mass := T.le_massOn hsum_adm
  -- (b) `M_{W_p}(∂Q)` as a supremum over families, which are directed
  have hsupW : ∀ p, T.massOn (W p) =
      ⨆ ω : (q : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W q),
        ENNReal.ofReal (T (ω p)) := by
    intro p
    rw [GeometricCurrentOn.massOn, sSup_image']
    refine le_antisymm (iSup_le fun ω => ?_) (iSup_le fun ω => le_iSup_of_le (ω p) le_rfl)
    let z : (q : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W q) :=
      fun q => ⟨0, hadm0 (W q)⟩
    exact le_iSup_of_le (Function.update z p ω) (by simp only [Function.update_self, le_refl])
  have hdir : ∀ i j : (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W p),
      ∃ k : (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)) → massAdmissibleOn univ m (W p), ∀ p,
        ENNReal.ofReal (T (i p)) ≤ ENNReal.ofReal (T (k p)) ∧
          ENNReal.ofReal (T (j p)) ≤ ENNReal.ofReal (T (k p)) := by
    intro i j
    refine ⟨fun p => if ENNReal.ofReal (T (i p)) ≤ ENNReal.ofReal (T (j p)) then j p else i p,
      fun p => ?_⟩
    by_cases h : ENNReal.ofReal (T (i p)) ≤ ENNReal.ofReal (T (j p))
    · simp only [ite_eq_left h]
      exact ⟨h, le_rfl⟩
    · simp only [ite_eq_right h]
      exact ⟨le_rfl, (not_le.1 h).le⟩
  have hsum : ∑ p ∈ s, T.massOn (W p) ≤ T.mass := by
    rw [Finset.sum_congr rfl fun p _ => hsupW p, ENNReal.finsetSum_iSup hdir]
    exact iSup_le hfam
  -- Step 3: `V_p = M_{W_p}(∂Q)`
  have hne : ∀ p, T.massOn (W p) ≠ ∞ := fun p =>
    ne_top_of_le_ne_top hmass (T.massOn_mono (subset_univ (W p)))
  refine ⟨fun p => (T.massOn (W p)).toReal, fun p _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [ENNReal.ofReal_sum_of_nonneg fun p _ => ENNReal.toReal_nonneg]
    calc ∑ p ∈ s, ENNReal.ofReal (T.massOn (W p)).toReal = ∑ p ∈ s, T.massOn (W p) :=
          Finset.sum_congr rfl fun p _ => ENNReal.ofReal_toReal (hne p)
      _ ≤ T.mass := hsum
  intro p hp g hg hgc hgC hg1
  -- Step 4: `Φ_p(spt g)` is compact and has positive distance from the other faces
  have hGc : IsCompact (Φ p '' tsupport g) := IsCompact.image hgc (hFG p hp).2.1
  have hBc : IsClosed (⋃ q ∈ s.erase p, F q) :=
    isClosed_biUnion_finset fun q hq => (hFG q (Finset.mem_of_mem_erase hq)).2.2.1
  have hGB : Disjoint (Φ p '' tsupport g) (⋃ q ∈ s.erase p, F q) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyB
    obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.1 hyB
    exact (hFG p hp).2.2.2 q (hs q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq) y
      (hgC hy) hyq
  obtain ⟨r, hr0, hr⟩ := exists_pos_forall_lt_edist hGc hBc hGB
  set δ : ℝ := (r : ℝ) / 3 with hδ
  have hδ0 : 0 < δ := div_pos (NNReal.coe_pos.2 hr0) three_pos
  -- Step 5: the divergence form of `g`
  obtain ⟨ω, hω1, hωspt, hωd⟩ :=
    Submission.dor_lmb_fcd_fr_divergence_form P m p g δ (hs p hp) hg hgc hg1 hδ0
  -- Step 6: `spt ω ⊆ W_p`, so `ω` is admissible for `M_{W_p}(∂Q)`
  have hωW : tsupport (ω : DifferentialForm (Euclid P) m) ⊆ W p := by
    intro x hx q hq hqp
    obtain ⟨y, hy, hxy⟩ := hωspt x hx
    have hyC : ∀ i, 0 < y i ∧ y i < 1 := hgC hy
    have hxy' : dist (Φ p y) x ≤ δ := by
      rw [dist_comm]
      exact hxy
    have h1 : infDist x (F p) ≤ δ :=
      (infDist_le_dist_of_mem ((hFG p hp).1 y fun i => ⟨(hyC i).1.le, (hyC i).2.le⟩)).trans
        (by rw [dist_comm]; exact hxy')
    have h2 : 2 * δ ≤ infDist x (F q) := by
      refine (le_infDist (hFne q hq)).2 fun b hb => ?_
      have hb' : (r : ℝ≥0∞) < edist (Φ p y) b :=
        hr _ ⟨y, hy, rfl⟩ b (Set.mem_iUnion₂.2 ⟨q, Finset.mem_erase.2 ⟨hqp, hq⟩, hb⟩)
      have hrb : (r : ℝ) < dist (Φ p y) b := by
        rw [dist_edist]
        exact ENNReal.toReal_strict_mono (edist_ne_top _ _) hb'
      have htri := dist_triangle (Φ p y) x b
      linarith
    linarith
  have hωadm : ω ∈ massAdmissibleOn univ m (W p) := ⟨hωW, hω1⟩
  -- Step 7: `∂Q(ω) = Q(dω) = ∫_{Q₁} u_p div g`, `dω` vanishing on the other faces
  have hval : T ω = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
      u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
    rw [hT, GeometricCurrentOn.boundary_apply, hQ, Finset.sum_eq_single p]
    · congr 1
      funext y
      exact congrArg (fun t => u p y * t) (hωd y)
    · intro q hq hqp
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      have hyF : Φ q y ∈ F q := (hFG q hq).1 y fun i => ⟨(hy i).1.le, (hy i).2.le⟩
      have hnot : Φ q y ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) := by
        intro hmem
        have hlt := hωW (tsupport_exteriorDerivative_subset _ hmem) q hq hqp
        rw [infDist_zero_of_mem hyF] at hlt
        exact absurd hlt (not_lt.2 infDist_nonneg)
      have h0 : exteriorDerivative (ω : DifferentialForm (Euclid P) m) (Φ q y)
          (fun k => EuclideanSpace.single (q.2 k) (1 : ℝ)) = 0 := by
        rw [image_eq_zero_of_notMem_tsupport hnot]
        rfl
      exact (congrArg (fun t => u q y * t) h0).trans (mul_zero _)
    · intro h
      exact absurd hp h
  -- Step 8: `∫_{Q₁} u_p div g = ∂Q(ω) ≤ M_{W_p}(∂Q)`
  have hle : ENNReal.ofReal (T ω) ≤ T.massOn (W p) := T.le_massOn hωadm
  rw [hval] at hle
  exact (ENNReal.ofReal_le_iff_le_toReal (hne p)).1 hle

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
