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

/-- **Simon Ch. 6, 1.2 (p. 132)**: `Λⁿ(ℝᴾ)` is finite-dimensional.  An `n`-covector `α` is
determined by its values `α(e_{I(1)}, …, e_{I(n)})` on tuples of standard basis vectors (alternating
maps agreeing on distinct basis vectors are equal), so `α ↦ (α(e ∘ I))_{I : Fin n → Fin P}` is an
injective linear map into the finite-dimensional space `ℝ^(Fin n → Fin P)`. -/
theorem Submission.imsupp_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`, linear since addition and scaling of covectors are pointwise
  let L : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α I => α fun i => e (I i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `L α = L β` identifies `α` and `β` on distinct basis vectors, hence everywhere
  refine FiniteDimensional.of_injective L fun α β h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Simon Ch. 6, 3.2(3)**, one covector at a time: if `T = τ(M, θ, ξ)` vanishes on the open set
`W ⊆ U`, then `ξ(x)(α) = 0` for `μ_T`-a.e. `x ∈ W`.  Here `f = ξ(·)(α)` is a.e. bounded by `‖α‖`
(`ξ = ±τ₁ ∧ ⋯ ∧ τₙ`, `τ` orthonormal) and `μ_T = θ Hⁿ⌞M` is finite on compact subsets of `U`, so
`f` is locally `μ_T`-integrable on `W`.  For smooth compactly supported `g` with `spt g ⊆ W`,
`∫ g f dμ_T = τ(M, θ, ξ)(g α) = T(g α) = 0`, and the fundamental lemma of the calculus of
variations gives `f = 0` a.e. on `W`. -/
theorem Submission.imsupp_orient_apply_ae_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂R.measure, x ∈ W → R.orient x α = 0 := by
  intro P n U W T R hRT hW hWU hT α
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `|ξ(x)(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖` wherever `ξ(x)` is a unit orientation
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x α‖ ≤ ‖α‖ := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have h1 : ‖R.orient x α‖ = ‖α τ‖ := by
      rcases hξ with h | h
      · rw [h α]
      · rw [h α, norm_neg]
    rw [h1]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]
  -- `f = ξ(·)(α)` is the continuous evaluation at `α` composed with `ξ`
  have hmeas : AEStronglyMeasurable (fun x => R.orient x α) R.measure :=
    ((ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
      R.aestronglyMeasurable_orient).mono_ac hac
  -- `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞` for compact `K ⊆ U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  -- `f` is bounded and `μ_T` is finite on compact subsets of `W`
  have hli : LocallyIntegrableOn (fun x => R.orient x α) W R.measure := by
    refine (locallyIntegrableOn_iff hW.isLocallyClosed).2 fun K hKW hK => ?_
    exact IntegrableOn.of_bound (hfin K hK (hKW.trans hWU)) hmeas.restrict ‖α‖
      (ae_restrict_of_ae hbound)
  -- `∫ g f dμ_T = τ(M, θ, ξ)(g α) = T(g α) = 0`, as `g α` is a test form supported in `W`
  refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hli fun g hg hgc hgW => ?_
  let ω : TestFormOn U n := ⟨fun y => g y • α, ⟨hg.smul contDiff_const, hgc.smul_right⟩,
    (tsupport_smul_subset_left _ _).trans (hgW.trans hWU)⟩
  have h0 : T ω = 0 := hT ω ((tsupport_smul_subset_left _ _).trans hgW)
  rw [hRT ω] at h0
  have hθ : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
    funext x; simp
  have hmθ : Measurable fun x => (R.mult x : NNReal) :=
    (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R.measurable_mult
  rw [IMRep.measure, hθ, integral_withDensity_eq_integral_smul hmθ, ← h0, IMRep.action]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ω, NNReal.smul_def, NNReal.coe_natCast, smul_eq_mul, map_smul]
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

/-- **Simon 6.3.2(3)** (`M_W(T) = ∫_{M ∩ W} θ dHⁿ`, so `μ_T(W) = 0` where `T` vanishes): if
`T = τ(M, θ, ξ)` vanishes on the open set `W ⊆ U`, then the weight `μ_T = θHⁿ⌞M` has
`μ_T(W) = 0`.  Fix a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ` of `n`-covectors.
By the fundamental lemma, `μ_T`-a.e. `x ∈ W` has `⟨αₖ, ξ(x)⟩ = 0` for all `k`, so `ξ(x) = 0`;
but `ξ ≠ 0` holds `μ_T`-a.e., since `μ_T ≪ Hⁿ⌞M` and `ξ` is `Hⁿ⌞M`-a.e. a unit orientation. -/
theorem Submission.imsupp_measure_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → W ⊆ U → T.VanishesOn W → R.measure W = 0 := by
  intro P n U W T R hRT hW hWU hT
  -- `μ_T = θHⁿ⌞M ≪ Hⁿ⌞M`, and `Hⁿ⌞M`-a.e. `ξ(x)` is a unit orientation, hence nonzero
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hξ : ∀ᵐ x ∂R.measure, R.orient x ≠ 0 :=
    hac.ae_le <| R.orients.mono fun x ⟨Q, _, hQ⟩ =>
      (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).1
  -- a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ` of `n`-covectors
  have := Submission.imsupp_covector_finiteDimensional P n
  let α := Module.finBasis ℝ (Covector (Euclid P) n)
  -- `μ_T`-a.e. `x ∈ W` has `⟨αₖ, ξ(x)⟩ = 0` for every `k` (fundamental lemma, finitely many `k`)
  have hα : ∀ᵐ x ∂R.measure, ∀ k, x ∈ W → R.orient x (α k) = 0 :=
    ae_all_iff.2 fun k =>
      Submission.imsupp_orient_apply_ae_eq_zero_of_vanishesOn P n U W T R hRT hW hWU hT (α k)
  -- such an `x` has `ξ(x) = 0`, as `ξ(x)` vanishes on a basis; so `μ_T`-a.e. `x` lies outside `W`
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hξ, hα] with x hx0 hxα hxW
  exact hx0 (ContinuousLinearMap.coe_injective (α.ext fun k => by simpa using hxα k hxW))
/-- **Simon 6.2.11–6.2.12** (`spt T ⊆ spt μ_T`): if `T = τ(M, θ, ξ)` and `μ_T(W) = 0` for the
weight `μ_T = θHⁿ⌞M`, then `T` vanishes on `W`.  For `ω ∈ 𝒟ⁿ(U)` with `K = spt ω ⊆ W`, the closed
set `K` has `∫_K θ dHⁿ⌞M = μ_T(K) = 0`, so `θ ≥ 1` on `M` forces `Hⁿ⌞M(K) = 0`.  The integrand
`θ⟨ω, ξ⟩` of `T(ω)` vanishes off `K`, hence `Hⁿ⌞M`-a.e., and `T(ω) = 0`. -/
theorem Submission.imsupp_vanishesOn_of_measure_eq_zero : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → R.measure W = 0 → T.VanishesOn W := by
  intro P n U W T R hRT hW ω hω
  -- `ν = Hⁿ⌞M` and the closed, hence Borel, set `K = spt ω ⊆ W`
  set ν : Measure (Euclid P) := μHE[n].restrict R.carrier
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hK : MeasurableSet K := (isClosed_tsupport _).measurableSet
  -- `∫_K θ dν = μ_T(K) ≤ μ_T(W) = 0`, so `θ = 0` at `ν⌞K`-a.e. point
  have hθK : ∫⁻ x in K, (R.mult x : ℝ≥0∞) ∂ν = 0 := by
    rw [← withDensity_apply (fun x => (R.mult x : ℝ≥0∞)) hK]
    exact measure_mono_null hω hW
  have hθ : ∀ᵐ x ∂ν.restrict K, (R.mult x : ℝ≥0∞) = 0 :=
    (lintegral_eq_zero_iff ((measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp
      R.measurable_mult)).1 hθK
  -- `θ ≥ 1` on `M`, and `ν⌞K`-a.e. point lies in `M`, so `ν(K) = 0`
  have hνK : ν K = 0 := by
    rw [← Measure.restrict_apply_univ K, measure_eq_zero_iff_ae_notMem]
    filter_upwards [hθ, ae_restrict_of_ae (ae_restrict_mem R.measurableSet_carrier)]
      with x hx hxM
    exact absurd (Nat.cast_eq_zero.1 hx) (R.mult_pos x hxM).ne'
  -- `ω = 0` off `K`, so the integrand of `T(ω) = ∫ θ⟨ω, ξ⟩ dν` vanishes `ν`-a.e.
  rw [hRT ω, IMRep.action]
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hνK] with x hx
  rw [image_eq_zero_of_notMem_tsupport hx, map_zero, mul_zero, Pi.zero_apply]

/-- **Simon 6.2.11–6.2.12 and 6.3.2(3)** (`spt T = U ∩ spt μ_T`): if `T = τ(M, θ, ξ)` in the open
set `U`, then `spt T` is the part in `U` of the support of the weight `μ_T = θHⁿ⌞M`.  If
`x ∈ spt T` had a `μ_T`-null neighbourhood `N`, a ball `B_ε(x)` with `B̄_ε(x) ⊆ N ∩ U` would be
`μ_T`-null, so `T` would vanish on it and `x` would lie in the zero region.  Conversely, a piece
`W` of the zero region (open, `W̄ ⊆ U` compact, `T` vanishing on `W`) has `μ_T(W) = 0`, so it
misses `spt μ_T`. -/
theorem Submission.imrep_represents_support_eq_inter_measure_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → T.support = U ∩ R.measure.support := by
  intro P n U T R hU hRT
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_inter_iff]
  refine and_congr_right fun hxU => ⟨fun hxZ => ?_, fun hxμ hxZ => ?_⟩
  · -- `spt T ⊆ spt μ_T`: for a `μ_T`-null neighbourhood `N` of `x`, a ball `B_ε(x)` with
    -- `B̄_ε(x) ⊆ N ∩ U` is `μ_T`-null, so `T` vanishes on it and `x` lies in the zero region
    refine (Measure.mem_support_iff_forall x).2 fun N hN => pos_iff_ne_zero.2 fun hμN => hxZ ?_
    obtain ⟨ε, hε, hεN⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hN (hU.mem_nhds hxU))
    refine mem_sUnion.2 ⟨ball x ε, ⟨isOpen_ball,
      (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans (hεN.trans inter_subset_right), ?_⟩, mem_ball_self hε⟩
    exact Submission.imsupp_vanishesOn_of_measure_eq_zero P n U (ball x ε) T R hRT
      (measure_mono_null (ball_subset_closedBall.trans (hεN.trans inter_subset_left)) hμN)
  · -- `U ∩ spt μ_T ⊆ spt T`: a piece `W ∋ x` of the zero region has `μ_T(W) = 0`, while `W` is
    -- an open neighbourhood of `x ∈ spt μ_T`
    obtain ⟨W, ⟨hWo, -, hWU, hTW⟩, hxW⟩ := mem_sUnion.1 hxZ
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne'
      (Submission.imsupp_measure_eq_zero_of_vanishesOn P n U W T R hRT hWo
        (subset_closure.trans hWU) hTW)
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
/-- **Approximate tangent spaces under dilation** (Simon Ch. 3, 1.4).  For `c > 0` the blow-ups
of `c⁻¹M = {x : cx ∈ M}` at `z` are blow-ups of `M` at `cz`: `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)`, as
`(cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z)`.  Since `cr ↓ 0` as `r ↓ 0`, the limits defining `Q` as the
approximate tangent space of `M` at `cz` give the limits for `c⁻¹M` at `z`. -/
theorem Submission.approx_tangent_space_smul_preimage : ∀ (P n : ℕ) (M : Set (Euclid P)) (c : ℝ) (z : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < c → HasApproximateTangentSpaceAt n M (c • z) Q → HasApproximateTangentSpaceAt n ((fun x => c • x) ⁻¹' M) z Q := by
  intro P n M c z Q hc hT
  have hc0 : c ≠ 0 := hc.ne'
  -- `η_{cz,cr}(m) = (cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z) = η_{z,r}(c⁻¹m)`
  have hη : ∀ (r : ℝ) (m : Euclid P), Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) m =
      Poincare.SimonGMT.Chapter03.blowUpMap z r (c⁻¹ • m) := by
    intro r m
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, Poincare.SimonGMT.Chapter03.blowUpMap, mul_inv_rev,
      ← smul_smul, smul_sub c⁻¹, inv_smul_smul₀ hc0]
  -- `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)` for every `r`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap z r '' ((fun x => c • x) ⁻¹' M) =
      Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) '' M := by
    intro r
    ext y
    constructor
    · rintro ⟨m', hm', rfl⟩
      exact ⟨c • m', hm', by rw [hη, inv_smul_smul₀ hc0]⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨c⁻¹ • m, ?_, (hη r m).symm⟩
      show c • c⁻¹ • m ∈ M
      rwa [smul_inv_smul₀ hc0]
  -- `r ↦ cr` tends to `0` within `(0, ∞)`: it is continuous, vanishes at `0` and is positive
  -- for `r > 0`
  have hφ : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := (continuous_const_mul c).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  -- the limit at `cz` along `cr ↓ 0` is the limit at `z` along `r ↓ 0`
  refine ⟨hT.1, fun f => ((hT.2 f).comp hφ).congr fun r => ?_⟩
  rw [Function.comp_apply, hset r]

/-- **Dilating an integer multiplicity triple** (Simon Ch. 6, 3.1 and 2.23).  For `c > 0` and
`T x = c • x`, the triple `(T⁻¹M, θ ∘ T, ξ ∘ T)` is again integer multiplicity in `ℝᴾ`.  By the
change of variables `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M`, null sets, local integrability and
`Hⁿ⌞M`-a.e. statements transfer through the measurable embedding `T`; the maps `c⁻¹ • Fⱼ`
parametrize `T⁻¹M`, and approximate tangent spaces are dilation invariant. -/
theorem Submission.imrep_univ_smul_rescale_exists : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = (fun x => c • x) ⁻¹' R.carrier ∧ (∀ x, R'.mult x = R.mult (c • x)) ∧ ∀ x, R'.orient x = R.orient (c • x) := by
  intro P n R c hc
  have hc0 : c ≠ 0 := hc.ne'
  -- `T x = c • x` is a homeomorphism of `ℝᴾ`, hence measurable and a measurable embedding
  have hT : Measurable (fun x : Euclid P => c • x) := measurable_const_smul c
  have hTemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc0).measurableEmbedding
  -- (CV): `T_#(Hⁿ⌞T⁻¹S) = c⁻ⁿ Hⁿ⌞S` and the lower-integral change of variables, for every `S`
  have hCV := Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
  -- (∗) `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M` for `M = R.carrier`
  have hstar := (hCV R.carrier).1
  refine ⟨{ carrier := (fun x : Euclid P => c • x) ⁻¹' R.carrier
            mult := fun x => R.mult (c • x)
            orient := fun x => R.orient (c • x)
            measurableSet_carrier := hT R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp hT
            mult_pos := fun x hx => R.mult_pos (c • x) hx
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, rfl, fun _ => rfl, fun _ => rfl⟩
  · -- rectifiability: `T⁻¹M ⊆ T⁻¹M₀ ∪ ⋃ⱼ range (c⁻¹ • Fⱼ)` with `Hⁿ(T⁻¹M₀) = 0`
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun x : Euclid P => c • x) ⁻¹' M₀, ?_, fun j w => c⁻¹ • F j w, fun j => ?_, ?_⟩
    · -- evaluate `T_#(Hⁿ⌞T⁻¹M₀) = c⁻ⁿ Hⁿ⌞M₀` on `univ`
      have h := congrArg (fun μ : Measure (Euclid P) => μ univ) (hCV M₀).1
      simp only at h
      rwa [Measure.map_apply hT MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
        Measure.smul_apply, Measure.restrict_apply_univ, hM₀, smul_zero] at h
    · -- `c⁻¹ • Fⱼ` is `‖c⁻¹‖₊ Kⱼ`-Lipschitz
      obtain ⟨K, hK⟩ := hF j
      exact ⟨‖c⁻¹‖₊ * K, (lipschitzWith_smul c⁻¹).comp hK⟩
    · -- if `c • z = Fⱼ w` then `z = c⁻¹ • Fⱼ w`
      intro z hz
      rcases hcover hz with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, w, by simp only [hw, inv_smul_smul₀ hc0]⟩)
  · -- local integrability: `T⁻¹M ∩ K = T⁻¹(M ∩ T(K))` with `T(K)` compact
    intro K hK _
    have hTK : IsCompact ((fun x : Euclid P => c • x) '' K) := hK.image (continuous_const_smul c)
    have hset : (fun x : Euclid P => c • x) ⁻¹' R.carrier ∩ K =
        (fun x : Euclid P => c • x) ⁻¹' (R.carrier ∩ (fun x : Euclid P => c • x) '' K) := by
      rw [preimage_inter, hTemb.injective.preimage_image]
    rw [hset, (hCV (R.carrier ∩ (fun x : Euclid P => c • x) '' K)).2.1 fun y => (R.mult y : ℝ≥0∞)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (R.locallyIntegrable_mult _ hTK (subset_univ _))
  · -- `ξ` is a.e.-strongly measurable for `c⁻ⁿ Hⁿ⌞M = T_#(Hⁿ⌞T⁻¹M)`; compose with `T`
    have h := R.aestronglyMeasurable_orient.smul_measure (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar] at h
    exact h.comp_aemeasurable hT.aemeasurable
  · -- the orientation statement holds `T_#(Hⁿ⌞T⁻¹M)`-a.e., i.e. at `c • z` for a.e. `z ∈ T⁻¹M`;
    -- there `Q` is also the approximate tangent space of `T⁻¹M` at `z`
    have h := Measure.ae_smul_measure R.orients (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar, hTemb.ae_map_iff] at h
    filter_upwards [h] with z ⟨Q, hQ, hξ⟩
    exact ⟨Q, Submission.approx_tangent_space_smul_preimage P n R.carrier c z Q hc hQ, hξ⟩
/-- **A cone takes equal values on dilated test forms** (Simon 7.3.1(2), via 6.2.23).
If `C ∈ 𝒟ₙ(ℝᴾ)` is a cone, `λ > 0` and `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `ω'(y) = λ⁻ⁿ ω(λ⁻¹y)` defines a test
form with `C(ω') = C(ω)`.  As `η_{0,λ}(ℝᴾ) = ℝᴾ`, the cone property `η_{0,λ#}C = C` reads
`C(η_{0,λ}^# ω) = C(ω)`, and by multilinearity
`η_{0,λ}^# ω (y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)`. -/
theorem Submission.cone_current_apply_dilation_pullback : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsConeCurrent C → ∀ lam : ℝ, 0 < lam → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) ∧ C ω' = C ω := by
  intro P n C hC lam hlam ω
  -- Step 1: the cone property `η_{0,λ#}C(ω) = C(ω)`.
  have hcone := hC lam hlam ω
  -- Step 2: `η_{0,λ}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (0 : Euclid P) lam '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨lam • x, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hlam.ne']
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) lam '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h] at hcone
  -- Steps 3–4: unfolding `blowUp`, `η_{0,λ#}C(ω) = C(ω')` for the affine pullback `ω'` of `ω`,
  -- so `C(ω') = C(ω)`.
  refine ⟨_, fun y => ?_, hcone⟩
  -- Step 5: `ω'(y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)` by multilinearity.
  ext v
  change (ω : DifferentialForm (Euclid P) n) (-(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam y)
      (fun i => dilationCLM P lam (v i)) = _
  simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Action and weight of a dilated triple** (Simon 6.3.1 (‡) and Ch. 4, 1.1, under
`x ↦ cx`; used for the cone `C` of 7.3.1(2)).  If `c > 0` and `R' = (M', θ', ξ')` is
`R = (M, θ, ξ)` pulled back by `x ↦ cx`, i.e. `M' = {x : cx ∈ M}`, `θ'(x) = θ(cx)` and
`ξ'(x) = ξ(cx)`, then `τ(R')(ω) = τ(R)(ω_c)` with `ω_c(y) = c⁻ⁿ ω(c⁻¹y)` for every `n`-form `ω`,
and `μ_{R'}(A) = c⁻ⁿ μ_R(cA)` for every Borel `A`.  Both follow from the change of variables
`∫_{M'} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ`. -/
theorem Submission.imrep_smul_rescale_action_measure : ∀ (P n : ℕ) (R R' : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → R'.carrier = (fun x => c • x) ⁻¹' R.carrier → (∀ x, R'.mult x = R.mult (c • x)) → (∀ x, R'.orient x = R.orient (c • x)) → (∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action (fun y => (c⁻¹ ^ n) • ω (c⁻¹ • y))) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R'.measure A = ENNReal.ofReal (c⁻¹ ^ n) * R.measure ((fun x => c • x) '' A) := by
  intro P n R R' c hc hcar hmult horient
  -- `T x = cx` is a measurable embedding with `c⁻¹ (cz) = z`.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    measurableEmbedding_const_smul₀ hc.ne'
  have hinv : ∀ z : Euclid P, c⁻¹ • c • z = z := fun z => by
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- Step 1: `R'.action ω = ∫_{T⁻¹M} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ` for
    -- `g(y) = θ(y) ξ(y)(ω(c⁻¹y))`.
    have hcv := (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      R.carrier).2.2 fun y => (R.mult y : ℝ) * R.orient y (ω (c⁻¹ • y))
    simp only [hinv] at hcv
    unfold IMRep.action
    rw [hcar]
    simp only [hmult, horient]
    -- Step 2: move `c⁻ⁿ` inside the integral and use the linearity of `ξ(y)`.
    rw [hcv, ← integral_const_mul]
    congr 1
    funext y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  · -- Step 3: `R'.measure A = ∫⁻_{A ∩ M'} θ(c·) dHⁿ`, and `A ∩ M' = T⁻¹(cA ∩ M)`.
    have hTA : MeasurableSet ((fun x : Euclid P => c • x) '' A) := hT.measurableSet_image.2 hA
    have hset : A ∩ R'.carrier =
        (fun x : Euclid P => c • x) ⁻¹' ((fun x : Euclid P => c • x) '' A ∩ R.carrier) := by
      rw [preimage_inter, preimage_image_eq _ hT.injective, hcar]
    unfold IMRep.measure
    rw [withDensity_apply _ hA, withDensity_apply _ hTA, Measure.restrict_restrict hA,
      Measure.restrict_restrict hTA, hset]
    simp only [hmult]
    -- Step 4: the lower-integral change of variables on `cA ∩ M`.
    exact (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      ((fun x : Euclid P => c • x) '' A ∩ R.carrier)).2.1 fun y => (R.mult y : ℝ≥0∞)
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
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

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **The weight of a cone is homogeneous of degree `n`** (proof of Simon 7.4.5,
chapter-07.txt lines 697–699, "by virtue of the fact that `C` is a cone").  If the cone `C` is
represented by `R = (M, θ, ξ)` with weight `μ = θHⁿ⌞M` and `λ > 0`, then `μ(λA) = λⁿ μ(A)` for
every Borel `A`.  The dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, and
`R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·)) = C(λ⁻ⁿ ω(λ⁻¹·)) = C(ω)` as `η_{0,λ#}C = C`, so `R_λ` represents `C`.
By the uniqueness of the weight (Simon Ch. 6, 3.2(3)), `μ(A) = μ_{R_λ}(A) = λ⁻ⁿ μ(λA)`. -/
theorem Submission.cone_current_imrep_measure_smul_image : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsConeCurrent C → R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A := by
  intro P n C R hC hR lam hlam A hA
  -- Step 1: the dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, with
  -- `R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·))` for every form `ω` and `μ_{R_λ}(A) = λ⁻ⁿ μ(λA)` for Borel `A`
  obtain ⟨Rl, hcar, hmult, horient⟩ := Submission.imrep_univ_smul_rescale_exists P n R lam hlam
  obtain ⟨haction, hmeasure⟩ :=
    Submission.imrep_smul_rescale_action_measure P n R Rl lam hlam hcar hmult horient
  -- Step 2: `R_λ` represents `C`: `C(ω) = C(ω') = R(ω') = R_λ(ω)` for `ω' = λ⁻ⁿ ω(λ⁻¹·)`
  have hRl : Rl.Represents C := by
    intro ω
    obtain ⟨ω', hω', hCω'⟩ := Submission.cone_current_apply_dilation_pullback P n C hC lam hlam ω
    rw [← hCω', hR ω', haction]
    congr 1
    funext y
    exact hω' y
  -- Step 3: the weight does not depend on the representation, so `μ_{R_λ} = μ` and
  -- `μ(A) = λ⁻ⁿ μ(λA)`
  have hA' := hmeasure A hA
  rw [Submission.imrep_measure_eq_of_represents_same_current P n univ C Rl R isOpen_univ hRl hR]
    at hA'
  -- Step 4: multiply by `λⁿ`, using `λⁿ λ⁻ⁿ = 1`
  have hpow : ENNReal.ofReal (lam ^ n) * ENNReal.ofReal (lam⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
      ENNReal.ofReal_one]
  rw [hA', ← mul_assoc, hpow, one_mul]
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

/-- **Simon Ch. 3, 1.4; Ch. 4**: the approximate tangent planes `TₓM` of an integer multiplicity
representation `R = (M, θ, ξ)` in `ℝᴾ` form an `R.measure`-a.e.-measurable field of orthogonal
projections `x ↦ p_{TₓM}` (Borel σ-algebra of the operator-norm topology).  For `n = 0` every
`TₓM` is `⊥`.  For `n ≥ 1` let `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²`: as `θ ≥ 1` on `M`,
`Hⁿ⌞M` is finite on compact sets, so `x ↦ ∫_{η_{x,r}(M)} f_u dHⁿ` is continuous; at `μ`-a.e. `x`
(`R.orients`, `μ = θHⁿ⌞M ≪ Hⁿ⌞M`) `TₓM` exists and these integrals tend, along `r = 1/(k+1)`, to
`∫_{TₓM} f_u dHⁿ = cₙ|p_{TₓM} u|²`, `cₙ > 0`.  So each `x ↦ |p_{TₓM} u|²` is a.e.-measurable,
hence so is `x ↦ p_{TₓM}`. -/
theorem Submission.imrep_univ_tangent_starProjection_aemeasurable : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n R
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: a `0`-dimensional approximate tangent plane is `⊥`, so `p_{TₓM} = 0` for every `x`
    have h0 : ∀ x, (approxTangentPlane 0 R.carrier x).starProjection = 0 := by
      intro x
      have hx : approxTangentPlane 0 R.carrier x = ⊥ := by
        unfold approxTangentPlane
        split_ifs with h
        · exact Submodule.finrank_eq_zero.1 h.choose_spec.1
        · rfl
      rw [hx, Submodule.starProjection_bot]
    simp_rw [h0]
    exact aemeasurable_const
  obtain ⟨c, hc, hcQ⟩ := Submission.exists_plane_cutoff_quadratic_moment_eq n hn
  -- `Hⁿ(M ∩ K) ≤ ∫_{M ∩ K} θ dHⁿ < ∞` for compact `K`, as `θ ≥ 1` on `M`
  have hM : ∀ K : Set (Euclid P), IsCompact K → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK (subset_univ K)) ?_
    calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
        setLIntegral_mono' (R.measurableSet_carrier.inter hK.isClosed.measurableSet)
          fun x hx => by exact_mod_cast R.mult_pos x hx.1
  -- `TₓM` is an approximate tangent plane at `μ`-a.e. `x`, since `μ ≪ Hⁿ⌞M`
  have hT : ∀ᵐ x ∂R.measure,
      HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
    have h : ∀ᵐ x ∂μHE[n].restrict R.carrier,
        HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, hQ, -⟩ := hx
      have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
      unfold approxTangentPlane
      rw [dite_eq_left h]
      exact h.choose_spec
    exact (withDensity_absolutelyContinuous _ _).ae_le h
  refine Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq P R.measure
    (approxTangentPlane n R.carrier) fun u => ?_
  -- the test function `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²`, continuous with support in `B̄₁(0)`
  obtain ⟨φ, hφ_def⟩ : ∃ φ : Euclid P → ℝ, φ = fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 :=
    ⟨_, rfl⟩
  have hφ : Continuous φ := by
    rw [hφ_def]
    fun_prop
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 1) fun z hz => ?_
    have h1 : 1 < ‖z‖ := by simpa using hz
    have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
    simp [hφ_def, max_eq_right h2]
  -- `|p_x u|² = lim_k c⁻¹ ∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ` at `μ`-a.e. `x`
  refine aemeasurable_of_tendsto_metrizable_ae' (f := fun (k : ℕ) x => c⁻¹ *
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (1 / ((k : ℝ) + 1)) '' R.carrier, φ y ∂μHE[n])
    (fun k => (continuous_const.mul (Submission.continuous_blowUp_image_setIntegral P n R.carrier
      hM φ hφ hφs (1 / ((k : ℝ) + 1)) (by positivity))).aemeasurable) ?_
  filter_upwards [hT] with x hx
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
  have hval : ‖(approxTangentPlane n R.carrier x).starProjection u‖ ^ 2 =
      c⁻¹ * ∫ y in (approxTangentPlane n R.carrier x : Set (Euclid P)), φ y ∂μHE[n] := by
    rw [hφ_def, hcQ P _ hx.1 u, inv_mul_cancel_left₀ hc.ne']
  rw [hval]
  exact ((hx.2 ⟨⟨φ, hφ⟩, hφs⟩).comp hr).const_mul c⁻¹
/-- **Radial tangency from a constant density ratio** (Simon Ch. 4, 3.6 with `H = 0` and centre
`0`, as used in the proof of 7.4.5).  Let `R = (M, θ, ξ)` be an integer multiplicity triple in `ℝᴾ`
and `μ = θ Hⁿ⌞M`.  If `v(M, θ)` is stationary in `ℝᴾ`, `x ↦ p_{TₓM}` is `μ`-measurable and
`μ(B̄_ρ(0)) = ρⁿ μ(B̄_1(0))` for every `ρ > 0`, then `p_{TₓM}(x) = x` for `μ`-a.e. `x`.

For `n = 0` all balls have the same mass, so `μ` is carried by `{0}`.  For `n ≥ 1` the ball masses
fix the image of `μ` under `x ↦ ‖x‖` as `μ(B̄_1) n tⁿ⁻¹ dt` on `(0, ∞)`.  Testing stationarity
with `X(x) = η(‖x‖²) x`, `η' = −max(r² − ·, 0)`, whose tangential divergence is
`n η(‖x‖²) + 2 η'(‖x‖²) ‖pₓ x‖²` (4.3.2), and subtracting `∫ (n η(‖x‖²) + 2 η'(‖x‖²) ‖x‖²) dμ = 0`
gives `∫ max(r² − ‖x‖², 0) ‖x − pₓ x‖² dμ = 0` for every `r > 0`: the defect term of the
monotonicity identity 4.3.6 vanishes. -/
theorem Submission.stationary_imrep_radial_tangency_of_ball_ratio : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ ρ : ℝ, 0 < ρ → R.measure (closedBall (0 : Euclid P) ρ) = ENNReal.ofReal (ρ ^ n) * R.measure (closedBall (0 : Euclid P) 1)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x := by
  intro P n R hstat hproj hratio
  -- Step 1: `μ = θ Hⁿ⌞M` is finite on compact sets.
  have hfin : IsFiniteMeasureOnCompacts R.measure := by
    refine ⟨fun K hK => ?_⟩
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult K hK (subset_univ K))
  have hball_fin : ∀ r : ℝ, R.measure (closedBall (0 : Euclid P) r) ≠ ∞ :=
    fun r => (isCompact_closedBall 0 r).measure_lt_top.ne
  have hc : R.measure (closedBall (0 : Euclid P) 1) ≠ ∞ := hball_fin 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: all balls have the same mass, so `μ` is carried by the origin.
    have hann : ∀ j : ℕ, R.measure (closedBall (0 : Euclid P) ((j : ℝ) + 1) \
        closedBall 0 (1 / ((j : ℝ) + 1))) = 0 := by
      intro j
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hsub : closedBall (0 : Euclid P) (1 / ((j : ℝ) + 1)) ⊆
          closedBall 0 ((j : ℝ) + 1) := by
        refine closedBall_subset_closedBall ?_
        rw [div_le_iff₀ hj]
        nlinarith
      rw [measure_sdiff hsub measurableSet_closedBall.nullMeasurableSet (hball_fin _),
        hratio _ hj, hratio (1 / ((j : ℝ) + 1)) (by positivity)]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hann)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (map_zero _)
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    obtain ⟨j, hj⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj1 : ‖x‖ < (j : ℝ) + 1 := by
      have := le_max_left ‖x‖ (1 / ‖x‖)
      linarith
    have hj2 : 1 / ((j : ℝ) + 1) < ‖x‖ := by
      have h3 := le_max_right ‖x‖ (1 / ‖x‖)
      rw [div_lt_iff₀ hjpos]
      have h4 : 1 / ‖x‖ < (j : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hxpos] at h4
      linarith
    refine mem_iUnion.2 ⟨j, ?_⟩
    simp only [Set.mem_sdiff, mem_closedBall, dist_zero_right, not_le]
    exact ⟨hj1.le, hj2⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
    -- Step 2: `Tₓ = approxTangentPlane` is an `n`-plane for `μ`-a.e. `x` (`R.orients`).
    have hrank : ∀ᵐ x ∂R.measure,
        Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier x) = m + 1 := by
      have hac : R.measure ≪ μHE[m + 1].restrict R.carrier :=
        withDensity_absolutelyContinuous _ _
      refine hac.ae_le ?_
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, hQ, -⟩ := hx
      have h : ∃ Q, HasApproximateTangentSpaceAt (m + 1) R.carrier x Q := ⟨Q, hQ⟩
      rw [approxTangentPlane, dite_eq_left h]
      exact h.choose_spec.finrank_eq
    -- The origin is not an atom: `μ{0} ≤ μ(B̄_ε) = εⁿ μ(B̄₁) → 0`.
    have hzero : R.measure {0} = 0 := by
      have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ (m + 1)) *
          R.measure (closedBall (0 : Euclid P) 1)) (𝓝[>] 0) (𝓝 0) := by
        have h1 : Tendsto (fun ε : ℝ => ε ^ (m + 1)) (𝓝[>] 0) (𝓝 0) := by
          have h : Tendsto (fun ε : ℝ => ε ^ (m + 1)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (m + 1))) :=
            (continuous_pow (m + 1)).tendsto 0
          rw [zero_pow (Nat.succ_ne_zero m)] at h
          exact h.mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
      refine nonpos_iff_eq_zero.1 (ge_of_tendsto hlim ?_)
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [← hratio ε hε]
      exact measure_mono (singleton_subset_iff.2 (mem_closedBall_self (le_of_lt hε)))
    -- Ball masses for every real radius.
    have hcdf : ∀ t : ℝ, R.measure (closedBall (0 : Euclid P) t) =
        R.measure (closedBall (0 : Euclid P) 1) * ENNReal.ofReal (max t 0 ^ (m + 1)) := by
      intro t
      rcases lt_trichotomy t 0 with ht | rfl | ht
      · rw [closedBall_eq_empty.2 ht, measure_empty, max_eq_right ht.le]
        simp
      · rw [closedBall_zero, hzero]
        simp
      · rw [hratio t ht, max_eq_left ht.le, mul_comm]
    -- Step 5 (radial form): the image of `μ` under `x ↦ ‖x‖` is `μ(B̄₁) · n tⁿ⁻¹ dt` on `(0, ∞)`.
    set ν : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun t => ENNReal.ofReal (((m : ℝ) + 1) * t ^ m)) with hν
    have hνIoc : ∀ a b : ℝ, a < b → ν (Ioc a b) =
        ENNReal.ofReal (max b 0 ^ (m + 1)) - ENNReal.ofReal (max a 0 ^ (m + 1)) := by
      intro a b hab
      rw [hν, withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        Ioc_inter_Ioi]
      rcases le_or_gt b (max a 0) with hba | hab'
      · have hb0 : b ≤ 0 := by
          rcases le_total a 0 with ha | ha
          · rwa [max_eq_right ha] at hba
          · rw [max_eq_left ha] at hba
            exact absurd hab (not_lt.2 hba)
        rw [Ioc_eq_empty (not_lt.2 hba), Measure.restrict_empty, lintegral_zero_measure,
          max_eq_right hb0, max_eq_right (hab.le.trans hb0)]
        simp
      · have ha0 : 0 ≤ max a 0 := le_max_right _ _
        rw [max_eq_left (ha0.trans hab'.le)]
        have hcont : Continuous fun t : ℝ => ((m : ℝ) + 1) * t ^ m := by fun_prop
        rw [← ofReal_integral_eq_lintegral_ofReal
            (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
            ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht =>
              mul_nonneg (by positivity) (pow_nonneg (ha0.trans ht.1.le) m))),
          ← intervalIntegral.integral_of_le hab'.le,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => t ^ (m + 1))
            (fun t _ => by simpa using hasDerivAt_pow (m + 1) t) (hcont.intervalIntegrable _ _),
          ENNReal.ofReal_sub _ (pow_nonneg ha0 _)]
    have hmap : R.measure.map (fun x : Euclid P => ‖x‖) =
        R.measure (closedBall (0 : Euclid P) 1) • ν := by
      refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b hab => ?_)
      · rw [Measure.map_apply continuous_norm.measurable measurableSet_Ioc]
        refine ne_top_of_le_ne_top (hball_fin b) (measure_mono fun x hx => ?_)
        simpa using hx.2
      · have hpre : (fun x : Euclid P => ‖x‖) ⁻¹' Ioc a b = closedBall 0 b \ closedBall 0 a := by
          ext x
          simp [and_comm]
        rw [Measure.map_apply continuous_norm.measurable measurableSet_Ioc, Measure.smul_apply,
          smul_eq_mul, hνIoc a b hab, hpre,
          measure_sdiff (closedBall_subset_closedBall hab.le)
            measurableSet_closedBall.nullMeasurableSet (hball_fin a),
          hcdf b, hcdf a, ENNReal.mul_sub (fun _ _ => hc)]
    -- Steps 3–6 at the radius `r`: `∫ max(r² − ‖x‖², 0) (‖x‖² − ‖pₓ x‖²) dμ = 0`.
    have key : ∀ r : ℝ, 0 < r → ∀ᵐ x ∂R.measure, max (r ^ 2 - ‖x‖ ^ 2) 0 *
        (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) = 0 := by
      intro r hr
      -- The profile `g(s) = max(r² − s, 0) ≥ 0` and its primitive `η(s) = ∫ₛ^{r²} g`, `η' = −g`.
      obtain ⟨η, hη_deriv, hη_zero⟩ : ∃ η : ℝ → ℝ,
          (∀ s, HasDerivAt η (-max (r ^ 2 - s) 0) s) ∧ ∀ s, r ^ 2 ≤ s → η s = 0 := by
        have hgc : Continuous fun u : ℝ => max (r ^ 2 - u) 0 := by fun_prop
        refine ⟨fun s => ∫ u in s..r ^ 2, max (r ^ 2 - u) 0, fun s => ?_, fun s hs => ?_⟩
        · exact intervalIntegral.integral_hasDerivAt_left (hgc.intervalIntegrable _ _)
            (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
        · show ∫ u in s..r ^ 2, max (r ^ 2 - u) 0 = 0
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_]
          · simp
          · rw [uIcc_of_ge hs] at hu
            exact max_eq_right (by linarith [hu.1])
      have hηc : Continuous η := continuous_iff_continuousAt.2 fun s => (hη_deriv s).continuousAt
      have hη_C1 : ContDiff ℝ 1 η := by
        have hderiv : deriv η = fun s => -max (r ^ 2 - s) 0 :=
          funext fun s => (hη_deriv s).deriv
        exact contDiff_one_iff_deriv.2
          ⟨fun s => (hη_deriv s).differentiableAt, by rw [hderiv]; fun_prop⟩
      -- Functions vanishing off `B̄_r(0)` have compact support.
      have hcs : ∀ f : Euclid P → ℝ, (∀ x : Euclid P, r < ‖x‖ → f x = 0) →
          HasCompactSupport f := by
        intro f hf
        refine (isCompact_closedBall (0 : Euclid P) r).of_isClosed_subset (isClosed_tsupport _) ?_
        refine closure_minimal (fun x hx => ?_) isClosed_closedBall
        by_contra hxr
        exact hx (hf x (by simpa using hxr))
      have hη_out : ∀ x : Euclid P, r < ‖x‖ →
          η (‖x‖ ^ 2) = 0 ∧ max (r ^ 2 - ‖x‖ ^ 2) 0 = 0 :=
        fun x hx => ⟨hη_zero _ (by nlinarith [norm_nonneg x]),
          max_eq_right (by nlinarith [norm_nonneg x])⟩
      -- The radial test field `X(x) = η(‖x‖²) x` (`C¹`, supported in `B̄_r(0)`).
      have hX_C1 : ContDiff ℝ 1 (fun x : Euclid P => η (‖x‖ ^ 2) • x) :=
        (hη_C1.comp (contDiff_norm_sq ℝ)).smul contDiff_id
      have hX_cs : HasCompactSupport (fun x : Euclid P => η (‖x‖ ^ 2) • x) := by
        refine (isCompact_closedBall (0 : Euclid P) r).of_isClosed_subset (isClosed_tsupport _) ?_
        refine closure_minimal (fun x hx => ?_) isClosed_closedBall
        by_contra hxr
        exact hx (by simp [(hη_out x (by simpa using hxr)).1])
      have hX_fderiv : ∀ x : Euclid P, HasFDerivAt (fun x : Euclid P => η (‖x‖ ^ 2) • x)
          (η (‖x‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
            (2 * -max (r ^ 2 - ‖x‖ ^ 2) 0) • (innerSL ℝ x).smulRight x) x := by
        intro x
        have hsq := (hasFDerivAt_id x).norm_sq
        have hηComp := (hη_deriv (‖x‖ ^ 2)).comp_hasFDerivAt x hsq
        refine (hηComp.smul (hasFDerivAt_id x)).congr_fderiv
          (ContinuousLinearMap.ext fun w => ?_)
        simp [mul_smul]
        module
      -- Simon 4.3.2: `div_M X = n η(‖x‖²) − 2 g(‖x‖²) ‖pₓ x‖²` wherever `dim Tₓ = n`.
      have hdiv : ∀ x : Euclid P,
          Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier x) = m + 1 →
          tangentialDivergence (m + 1) R.carrier (fun x : Euclid P => η (‖x‖ ^ 2) • x) x =
            ((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 *
              ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 := by
        intro x hx
        set T := approxTangentPlane (m + 1) R.carrier x
        rw [tangentialDivergence, (hX_fderiv x).fderiv, LinearMap.trace_comp_comm']
        have hcomp : ((η (‖x‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
            (2 * -max (r ^ 2 - ‖x‖ ^ 2) 0) • (innerSL ℝ x).smulRight x).toLinearMap ∘ₗ
              T.starProjection.toLinearMap) =
            η (‖x‖ ^ 2) • T.starProjection.toLinearMap +
              (2 * -max (r ^ 2 - ‖x‖ ^ 2) 0) •
                ((innerSL ℝ x).toLinearMap ∘ₗ T.starProjection.toLinearMap).smulRight x := by
          ext w
          simp
        have htr : LinearMap.trace ℝ (Euclid P) T.starProjection.toLinearMap =
            (m : ℝ) + 1 := by
          rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
            LinearMap.trace_comp_comm']
          have hid : T.orthogonalProjectionOnto.toLinearMap ∘ₗ T.subtypeL.toLinearMap =
              LinearMap.id := by
            ext y
            simp
          rw [hid, LinearMap.trace_id, hx]
          push_cast
          ring
        have hinner : inner ℝ x (T.starProjection x) = ‖T.starProjection x‖ ^ 2 := by
          rw [← T.inner_starProjection_left_eq_right x x]
          simpa using T.re_inner_starProjection_eq_normSq x
        rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htr]
        simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
          innerSL_apply_apply, smul_eq_mul, hinner]
        ring
      -- Steps 3–4: stationarity, rewritten as an integral against `μ`.
      have hstatX : ∫ x, tangentialDivergence (m + 1) R.carrier
          (fun x : Euclid P => η (‖x‖ ^ 2) • x) x ∂R.measure = 0 := by
        have hden : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
          funext x
          simp
        have hmeas : Measurable fun x => (R.mult x : NNReal) :=
          measurable_from_nat.comp R.measurable_mult
        rw [IMRep.measure, hden, integral_withDensity_eq_integral_smul hmeas,
          ← hstat _ hX_C1 hX_cs, IMRep.firstVariation]
        congr 1
      have hstat' : ∫ x, (((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 *
          ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) ∂R.measure = 0 := by
        refine (integral_congr_ae ?_).trans hstatX
        filter_upwards [hrank] with x hx
        exact (hdiv x hx).symm
      -- Step 6: by Step 5 the same integral with `‖x‖²` in place of `‖pₓ x‖²` is
      -- `μ(B̄₁) ∫₀^r (d/dt)(n tⁿ η(t²)) dt = 0`.
      have hhom : ∫ x, (((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2)
          ∂R.measure = 0 := by
        set G : ℝ → ℝ := fun t =>
          ((m : ℝ) + 1) * η (t ^ 2) + 2 * -max (r ^ 2 - t ^ 2) 0 * t ^ 2 with hG
        have hGc : Continuous G := by fun_prop
        change ∫ x, G ‖x‖ ∂R.measure = 0
        rw [← integral_map continuous_norm.aemeasurable hGc.aestronglyMeasurable, hmap,
          integral_smul_measure]
        suffices h : ∫ t, G t ∂ν = 0 by rw [h, smul_zero]
        have hd : (fun t : ℝ => ENNReal.ofReal (((m : ℝ) + 1) * t ^ m)) =
            fun t => ((Real.toNNReal (((m : ℝ) + 1) * t ^ m) : NNReal) : ℝ≥0∞) := rfl
        rw [hν, hd, integral_withDensity_eq_integral_smul (by fun_prop)]
        have hF : ∀ t, HasDerivAt (fun t : ℝ => ((m : ℝ) + 1) * (t ^ (m + 1) * η (t ^ 2)))
            (((m : ℝ) + 1) * t ^ m * G t) t := by
          intro t
          have h3 := ((hasDerivAt_pow (m + 1) t).mul
            ((hη_deriv (t ^ 2)).comp t (hasDerivAt_pow 2 t))).const_mul ((m : ℝ) + 1)
          refine h3.congr_deriv ?_
          simp only [hG, Function.comp_apply]
          push_cast
          ring
        rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (Ioc_subset_Ioi_self : Ioc (0 : ℝ) r ⊆ Ioi 0) fun t ht => ?_]
        · rw [setIntegral_congr_fun measurableSet_Ioc
            (g := fun t => ((m : ℝ) + 1) * t ^ m * G t) fun t ht => ?_,
            ← intervalIntegral.integral_of_le hr.le,
            intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
              ((by fun_prop : Continuous fun t : ℝ =>
                ((m : ℝ) + 1) * t ^ m * G t).intervalIntegrable _ _)]
          · simp [hη_zero (r ^ 2) le_rfl]
          · simp only [NNReal.smul_def, smul_eq_mul]
            rw [Real.coe_toNNReal _ (mul_nonneg (by positivity) (pow_nonneg ht.1.le m))]
        · have hrt : r < t := by
            simp only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at ht
            exact ht.2 ht.1
          have hG0 : G t = 0 := by
            simp only [hG, hη_zero (t ^ 2) (by nlinarith),
              max_eq_right (by nlinarith : r ^ 2 - t ^ 2 ≤ 0)]
            ring
          simp [hG0]
      -- Subtracting, `∫ g(‖x‖²) (‖x‖² − ‖pₓ x‖²) dμ = 0` with a nonnegative integrand.
      have hpx_meas : AEMeasurable
          (fun x => ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) R.measure :=
        ((ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
          (hproj.prodMk aemeasurable_id)).norm).pow_const 2
      have hint1 : Integrable (fun x : Euclid P => ((m : ℝ) + 1) * η (‖x‖ ^ 2) +
          2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2) R.measure := by
        refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx => ?_)
        simp [(hη_out x hx).1, (hη_out x hx).2]
      have hint2 : Integrable (fun x : Euclid P => max (r ^ 2 - ‖x‖ ^ 2) 0 *
          (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2))
          R.measure := by
        refine Integrable.mono' (g := fun x : Euclid P => max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2)
          ?_ ?_ (ae_of_all _ fun x => ?_)
        · refine Continuous.integrable_of_hasCompactSupport (by fun_prop) (hcs _ fun x hx => ?_)
          simp [(hη_out x hx).2]
        · exact (by fun_prop : Continuous fun x : Euclid P =>
            max (r ^ 2 - ‖x‖ ^ 2) 0).aestronglyMeasurable.mul
              ((by fun_prop : Continuous fun x : Euclid P => ‖x‖ ^ 2).aestronglyMeasurable.sub
                hpx_meas.aestronglyMeasurable)
        · have h2 : ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ x) 2
          have h3 : 0 ≤ ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 := by
            positivity
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sub_nonneg.2 h2))]
          exact mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      have hsplit : (fun x : Euclid P => ((m : ℝ) + 1) * η (‖x‖ ^ 2) +
          2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 *
            ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) =
          fun x => (((m : ℝ) + 1) * η (‖x‖ ^ 2) + 2 * -max (r ^ 2 - ‖x‖ ^ 2) 0 * ‖x‖ ^ 2) +
            2 * (max (r ^ 2 - ‖x‖ ^ 2) 0 *
              (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2)) := by
        funext x
        ring
      rw [hsplit, integral_add hint1 (hint2.const_mul 2), hhom, zero_add, integral_const_mul]
        at hstat'
      have h0 : ∫ x, max (r ^ 2 - ‖x‖ ^ 2) 0 *
          (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2)
            ∂R.measure = 0 := by
        linarith
      have hnn : 0 ≤ᵐ[R.measure] fun x : Euclid P => max (r ^ 2 - ‖x‖ ^ 2) 0 *
          (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) :=
        ae_of_all _ fun x => mul_nonneg (le_max_right _ _) (sub_nonneg.2
          (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ x) 2))
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint2).1 h0] with x hx
      exact hx
    -- Step 7: exhaust `ℝᴾ` by the balls `B_{k+1}(0)`; then `‖x − pₓ x‖² = ‖x‖² − ‖pₓ x‖² = 0`.
    have hall : ∀ᵐ x ∂R.measure, ∀ k : ℕ, max (((k : ℝ) + 1) ^ 2 - ‖x‖ ^ 2) 0 *
        (‖x‖ ^ 2 - ‖(approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2) = 0 :=
      ae_all_iff.2 fun k => key _ (by positivity)
    filter_upwards [hall] with x hx
    obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
    have hpos : 0 < max (((k : ℝ) + 1) ^ 2 - ‖x‖ ^ 2) 0 :=
      lt_max_of_lt_left (by nlinarith [norm_nonneg x])
    have hq := (mul_eq_zero.1 (hx k)).resolve_left hpos.ne'
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x
      (approxTangentPlane (m + 1) R.carrier x)
    rw [Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply] at hpy
    have h0 : ‖x - (approxTangentPlane (m + 1) R.carrier x).starProjection x‖ ^ 2 = 0 := by
      linarith
    exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))).symm
/-- Stationarity plus radial tangency make the weighted first moments vanish (Simon 7.4.5,
proof, chapter-07.txt lines 708–719): if `δV(X) = 0` for every compactly supported `C¹` field
`X` and `p_{TₓM} x = x` for `μ_V`-a.e. `x`, then `∫ max(ρ² − |x|², 0) ⟨e, x⟩ dμ_V = 0`.  Test
with `Y(x) = max(ρ² − |x|², 0)² e`, which is `C¹`, vanishes outside `closedBall 0 |ρ|` and has
`DY(x) w = −4 max(ρ² − |x|², 0) ⟨x, w⟩ e`; the rank-one trace and self-adjointness of `p_x`
give `div_M Y(x) = −4 max(ρ² − |x|², 0) ⟨p_x x, e⟩ = −4 max(ρ² − |x|², 0) ⟨e, x⟩` a.e. -/
theorem Submission.stationary_radial_imrep_weighted_moment_eq_zero : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x) → ∀ (e : Euclid P) (ρ : ℝ), ∫ x, max (ρ ^ 2 - ‖x‖ ^ 2) 0 * inner ℝ e x ∂R.measure = 0 := by
  intro P n R hstat hrad e ρ
  -- the profile `g(t) = (max t 0)²` is `C¹` with `g'(t) = 2 max t 0`
  set g : ℝ → ℝ := fun t => max t 0 ^ 2 with hg_def
  have hg_ne : ∀ t : ℝ, t ≠ 0 → HasDerivAt g (2 * max t 0) t := by
    intro t ht
    rcases ht.lt_or_gt with ht | ht
    · have hev : g =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht] with s (hs : s < 0)
        simp [hg_def, max_eq_right hs.le]
      rw [max_eq_right ht.le, mul_zero]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
    · have hev : g =ᶠ[𝓝 t] fun s => s ^ 2 := by
        filter_upwards [Ioi_mem_nhds ht] with s (hs : 0 < s)
        simp [hg_def, max_eq_left hs.le]
      rw [max_eq_left ht.le]
      simpa using (hasDerivAt_pow 2 t).congr_of_eventuallyEq hev
  have hg : ∀ t : ℝ, HasDerivAt g (2 * max t 0) t :=
    hasDerivAt_of_hasDerivAt_of_ne' (x := 0) hg_ne (by fun_prop) (by fun_prop)
  have hg_cd : ContDiff ℝ 1 g := by
    refine contDiff_one_iff_deriv.mpr ⟨fun t => (hg t).differentiableAt, ?_⟩
    rw [show deriv g = fun t => 2 * max t 0 from funext fun t => (hg t).deriv]
    fun_prop
  -- the field `Y(x) = g(ρ² − ‖x‖²) e`: `C¹`, supported in `closedBall 0 |ρ|`
  set Y : Euclid P → Euclid P := fun x => g (ρ ^ 2 - ‖x‖ ^ 2) • e with hY_def
  have hY_cd : ContDiff ℝ 1 Y :=
    (hg_cd.comp (contDiff_const.sub (contDiff_norm_sq ℝ))).smul contDiff_const
  have hY_cs : HasCompactSupport Y := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) |ρ|) fun x hx => ?_
    have hx' : |ρ| < ‖x‖ := by simpa using hx
    have hneg : ρ ^ 2 - ‖x‖ ^ 2 ≤ 0 := by nlinarith [abs_nonneg ρ, sq_abs ρ]
    simp [hY_def, hg_def, max_eq_right hneg]
  -- `DY(x) w = 2 m(x) (−2⟨x, w⟩) e`, where `m(x) = max(ρ² − ‖x‖², 0)`
  have hY_deriv : ∀ x, HasFDerivAt Y
      (((2 * max (ρ ^ 2 - ‖x‖ ^ 2) 0) • -(2 • innerSL ℝ x)).smulRight e) x := by
    intro x
    have h1 : HasFDerivAt (fun y : Euclid P => ρ ^ 2 - ‖y‖ ^ 2) (-(2 • innerSL ℝ x)) x :=
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub (ρ ^ 2)
    exact ((hg _).comp_hasFDerivAt x h1).smul_const e
  -- `div_M Y(x) = trace(p_x ∘ DY(x)) = −4 m(x) ⟨x, p_x e⟩` (rank-one trace)
  have hdiv : ∀ x, tangentialDivergence n R.carrier Y x =
      -4 * max (ρ ^ 2 - ‖x‖ ^ 2) 0 *
        inner ℝ x ((approxTangentPlane n R.carrier x).starProjection e) := by
    intro x
    rw [tangentialDivergence, (hY_deriv x).fderiv]
    set p := (approxTangentPlane n R.carrier x).starProjection
    set L : Euclid P →L[ℝ] ℝ := (2 * max (ρ ^ 2 - ‖x‖ ^ 2) 0) • -(2 • innerSL ℝ x) with hL
    have hcomp : p.toLinearMap ∘ₗ (L.smulRight e).toLinearMap =
        (L : Euclid P →ₗ[ℝ] ℝ).smulRight (p e) := by
      ext w
      simp
    rw [hcomp, LinearMap.trace_smulRight]
    simp [hL]
    ring
  -- `δV(Y) = ∫ div_M Y dμ`
  have hfv : R.firstVariation Y = ∫ x, tangentialDivergence n R.carrier Y x ∂R.measure := by
    rw [IMRep.firstVariation, IMRep.measure, integral_withDensity_eq_integral_toReal_smul]
    · simp
    · exact measurable_from_nat.comp R.measurable_mult
    · exact Eventually.of_forall fun x => ENNReal.natCast_lt_top _
  -- radial tangency: `⟨x, p_x e⟩ = ⟨p_x x, e⟩ = ⟨e, x⟩` a.e.
  have hae : (fun x => tangentialDivergence n R.carrier Y x) =ᵐ[R.measure]
      fun x => -4 * (max (ρ ^ 2 - ‖x‖ ^ 2) 0 * inner ℝ e x) := by
    filter_upwards [hrad] with x hx
    rw [hdiv x, ← Submodule.inner_starProjection_left_eq_right, hx, real_inner_comm]
    ring
  have h0 := hstat Y hY_cd hY_cs
  rw [hfv, integral_congr_ae hae, integral_const_mul] at h0
  linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
