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

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- **Pull-back by the coordinates of an orthonormal frame preserves `|·|_E`** (orthogonal
invariance of the Euclidean coefficient norm of Simon 6.1.2, 6.1.5): if `v₁, …, vₙ` are orthonormal
in `ℝᴾ` and `pL x = (⟨v₁, x⟩, …, ⟨vₙ, x⟩)`, then `|γ ∘ pL|_E = |γ|_E` for every `l`-covector `γ`
on `ℝⁿ`.  Extend `v` to an orthonormal basis `f` of `ℝᴾ` with `f ∘ ι = v`, `ι = Fin.castLE`; then
`pL (f (ι i)) = eᵢ` and `pL f_m = 0` for `m ∉ range ι`.  So `(γ ∘ pL)(f ∘ j)` vanishes unless
`j = ι ∘ j'`, where it is `γ(e ∘ j')`, and `Σ_j (γ ∘ pL)(f ∘ j)² = Σ_{j'} γ(e ∘ j')²`; by
`regcomp_covector_sq_sum_orthonormalBasis` these are `l! |γ ∘ pL|_E²` and `l! |γ|_E²`. -/
theorem Submission.cbr_ci_pw_cb_pullback_covectorEuclideanNorm_eq : ∀ (P n : ℕ) (v : Fin n → Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → ∀ (l : ℕ) (γ : Covector (Euclid n) l), covectorEuclideanNorm (γ.compContinuousLinearMap pL) = covectorEuclideanNorm γ := by
  intro P n v pL hv hpL l γ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = v k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hv.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let w : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then v ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hws : Orthonormal ℝ (s.domRestrict w) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hwe : s.domRestrict w = v ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [w, e, hi]
    rw [hwe]
    exact hv.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hws
  have hfι : ∀ k, f (ι k) = v k := by
    intro k
    rw [hf (ι k) k.2]
    simp [w, ι]
  -- Step 2: `pL (f (ι i)) = eᵢ`, and `pL (f m) = 0` for `m ∉ range ι`
  have hpLι : ∀ i, pL (f (ι i)) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    intro i
    ext k
    rw [hpL, hfι, (orthonormal_iff_ite.mp hv) k i, EuclideanSpace.basisFun_apply,
      PiLp.single_apply]
  have hpL0 : ∀ m ∉ Set.range ι, pL (f m) = 0 := by
    intro m hm
    ext k
    rw [hpL, ← hfι, (orthonormal_iff_ite.mp f.orthonormal) (ι k) m,
      ite_eq_right fun h => hm ⟨k, h⟩, PiLp.zero_apply]
  -- Step 3: `Σ_{j'} γ(e ∘ j')² = Σ_j (γ ∘ pL)(f ∘ j)²` through the injection `j' ↦ ι ∘ j'`
  let Φ : (Fin l → Fin n) → (Fin l → Fin P) := fun j' => ι ∘ j'
  have hΦ : Injective Φ := fun a b h => funext fun k => hι (congrFun h k)
  have hsum : ∑ j' : Fin l → Fin n, (γ (fun k => EuclideanSpace.basisFun (Fin n) ℝ (j' k))) ^ 2 =
      ∑ j : Fin l → Fin P, (γ.compContinuousLinearMap pL (fun k => f (j k))) ^ 2 := by
    refine Fintype.sum_of_injective Φ hΦ _ _ ?_ ?_
    · -- a tuple `j ∉ range Φ` has a slot `k` with `j k ∉ range ι`, where `pL (f (j k)) = 0`
      intro j hj
      obtain ⟨k, hk⟩ : ∃ k, j k ∉ Set.range ι := by
        by_contra! hcon
        choose j' hj' using hcon
        exact hj ⟨j', funext hj'⟩
      have h0 : γ.compContinuousLinearMap pL (fun k => f (j k)) = 0 :=
        γ.map_coord_zero (m := pL ∘ fun k => f (j k)) k (hpL0 (j k) hk)
      rw [h0, sq, mul_zero]
    · intro j'
      have he : (pL ∘ fun k => f (Φ j' k)) = fun k => EuclideanSpace.basisFun (Fin n) ℝ (j' k) :=
        funext fun k => hpLι (j' k)
      show _ = (γ (pL ∘ fun k => f (Φ j' k))) ^ 2
      rw [he]
  -- Step 4: both sums are `l!`-multiples of the squared norms; cancel `l! ≠ 0`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis n l γ (EuclideanSpace.basisFun (Fin n) ℝ),
    Submission.regcomp_covector_sq_sum_orthonormalBasis P l _ f] at hsum
  have hsq : covectorEuclideanNorm (γ.compContinuousLinearMap pL) ^ 2 =
      covectorEuclideanNorm γ ^ 2 :=
    (mul_left_cancel₀ (Nat.cast_ne_zero.mpr l.factorial_ne_zero) hsum).symm
  exact (sq_eq_sq₀ (covectorEuclideanNorm_nonneg _) (covectorEuclideanNorm_nonneg _)).mp hsq

/-- **Covector bounds for an orthonormal frame and its coordinate map** (consequences (O1), (O3) of
the orthogonal invariance (O) of the coefficient norm in White's projection argument; Simon Ch. 6,
1.15 and Remark 2.6(a)): let `v₁, …, vₙ` be orthonormal in `ℝᴾ` and
`pL x = (⟨v₁, x⟩, …, ⟨vₙ, x⟩)`.  (a) `|β(v)| ≤ |β|_E` for every `n`-covector `β` on `ℝᴾ`
(`regcomp_covector_eval_orthonormal_le` with `τ = v`).  (b) For every `l`-covector `γ` on `ℝⁿ`,
`|γ ∘ pL|_E = |γ|_E` (`cbr_ci_pw_cb_pullback_covectorEuclideanNorm_eq`), in particular
`|γ ∘ pL|_E ≤ |γ|_E`. -/
theorem Submission.cbr_ci_pw_orthonormal_covector_bounds : ∀ (P n : ℕ) (v : Fin n → Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → (∀ β : Covector (Euclid P) n, |β v| ≤ covectorEuclideanNorm β) ∧ ∀ (l : ℕ) (γ : Covector (Euclid n) l), covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ := by
  intro P n v pL hv hpL
  -- (a) is evaluation on the orthonormal frame `v`; (b) weakens the equality `|γ ∘ pL|_E = |γ|_E`
  exact ⟨fun β => Submission.regcomp_covector_eval_orthonormal_le P n β v hv,
    fun l γ => (Submission.cbr_ci_pw_cb_pullback_covectorEuclideanNorm_eq P n v pL hv hpL l γ).le⟩

/-- **Projection of a sliced current to `ℝⁿ`** (White's projection argument, steps 5–7 of the
closure and boundary rectifiability proof; Simon Ch. 6, 2.5, 2.20 and Remark 2.6(a)): let
`v₀, …, v_d` be orthonormal in `ℝᴾ`, `pL x = (⟨v₀, x⟩, …, ⟨v_d, x⟩)`, `n = d + 1`, `U ⊆ ℝⁿ` open,
`F ⊆ S ⊆ ℝᴾ` with `F` measurable and `S ∩ pL⁻¹(K)` compact for every compact `K ⊆ U`, `μ` finite on
compact sets, `ξ` an a.e. strongly measurable `n`-vector field with `|⟨β, ξ⟩| ≤ |β|_E`, and
`Z(ω) = ∫_F ⟨ω, ξ⟩ dμ`.  Then `Y(ω) := ∫_F ⟨ω(pL x) ∘ pL, ξ(x)⟩ dμ` is a current in `U` (the
integrand is bounded and vanishes off the compact set `S ∩ pL⁻¹(spt ω)`), with
`M_U(Y) ≤ μ(F ∩ pL⁻¹(U))` since `|γ ∘ pL|_E ≤ |γ|_E` (`cbr_ci_pw_orthonormal_covector_bounds`).
A smooth cut-off `χ = 1` near `S ∩ pL⁻¹(spt ω)` turns `p^#ω` into a test form on `ℝᴾ` agreeing
with `p^#ω` on `S`; for `γ` admissible for `M_W(∂Y)` the cut-off `γ' = χ p^#γ` is admissible for
`M_{pL⁻¹(W)}(∂Z)` and `dγ' = p^#(dγ)` on `S` (locality and naturality of `d`), so
`∂Y(γ) = ∂Z(γ')` and `M_W(∂Y) ≤ M_{pL⁻¹(W)}(∂Z)`. -/
theorem Submission.dmcbr_ci_pw_projected_current : ∀ (P d : ℕ) (v : Fin (d + 1) → Euclid P) (pL : Euclid P →L[ℝ] Euclid (d + 1)) (U : Set (Euclid (d + 1))) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin (d + 1)), pL x i = inner ℝ (v i) x) → IsOpen U → MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid (d + 1)), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) (d + 1), |ξ x β| ≤ covectorEuclideanNorm β) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Z ω = ∫ x in F, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → ∃ Y : GeometricCurrentOn U (d + 1), (∀ ω : TestFormOn U (d + 1), Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) (pL x)).compContinuousLinearMap pL) ∂μ) ∧ Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) ∧ (∀ W : Set (Euclid (d + 1)), IsOpen W → W ⊆ U → Y.boundary.massOn W ≤ Z.boundary.massOn (pL ⁻¹' W)) ∧ ∀ ω : TestFormOn U (d + 1), ∃ ω' : TestFormOn (univ : Set (Euclid P)) (d + 1), ∀ x ∈ S, (ω' : DifferentialForm (Euclid P) (d + 1)) x = ((ω : DifferentialForm (Euclid (d + 1)) (d + 1)) (pL x)).compContinuousLinearMap pL := by
  have aux_smooth_cutoff : ∀ (P : ℕ) (K O : Set (Euclid P)), IsCompact K → IsOpen O → K ⊆ O → ∃ (χ : Euclid P → ℝ) (O' : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen O' ∧ K ⊆ O' ∧ ∀ x ∈ O', χ x = 1 := by
    intro P K O hK hO hKO
    -- Step 1: `cthickening δ K ⊆ O` for some `δ > 0`; put `r = δ/2`
    obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
    have hr : 0 < δ / 2 := half_pos hδ
    -- Steps 2-3: smooth Urysohn for the closed `cthickening r K` inside the open `thickening δ K`
    obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K))
        (isClosed_cthickening (δ := δ / 2) (E := K))
        (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
    -- Step 4: `tsupport χ = closure (thickening δ K) ⊆ cthickening δ K`
    have hts : tsupport χ ⊆ cthickening δ K := by
      rw [tsupport, hsupp]
      exact closure_thickening_subset_cthickening δ K
    -- Steps 5-7: compact support inside the compact `cthickening δ K`, the bounds `0 ≤ χ ≤ 1`, and
    -- `χ = 1` on `O' = thickening r K ⊆ cthickening r K`
    refine ⟨χ, thickening (δ / 2) K, hχ, ?_, hts.trans hδO, fun x => ?_, isOpen_thickening,
      self_subset_thickening hr K, fun x hx => (hone x).1 (thickening_subset_cthickening _ _ hx)⟩
    · exact (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport χ) hts
    · exact hrange (mem_range_self x)
  have aux_pullback_extension : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S O : Set (Euclid P)) (γ : DifferentialForm (Euclid m) l), ContDiff ℝ (⊤ : ℕ∞) γ → IsOpen O → IsCompact (S ∩ pL ⁻¹' tsupport γ) → S ∩ pL ⁻¹' tsupport γ ⊆ O → ∃ γ' : TestFormOn (univ : Set (Euclid P)) l, tsupport (γ' : DifferentialForm (Euclid P) l) ⊆ O ∧ (∀ x, covectorEuclideanNorm ((γ' : DifferentialForm (Euclid P) l) x) ≤ covectorEuclideanNorm ((γ (pL x)).compContinuousLinearMap pL)) ∧ (∀ x ∈ S, (γ' : DifferentialForm (Euclid P) l) x = (γ (pL x)).compContinuousLinearMap pL) ∧ ∀ x ∈ S, exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x = (exteriorDerivative γ (pL x)).compContinuousLinearMap pL := by
    intro P m l pL S O γ hγ hO hK hKO
    -- Step 1: a smooth cut-off `χ`, `spt χ ⊆ O`, `0 ≤ χ ≤ 1`, `χ = 1` on an open `O' ⊇ K`
    obtain ⟨χ, O', hχ, hχc, hχO, hχ01, hO', hKO', hχ1⟩ :=
      aux_smooth_cutoff P _ O hK hO hKO
    -- Step 2: `β = p^#γ = Λ ∘ γ ∘ pL` is smooth, `Λ α = α ∘ pL` being continuous linear
    set β : DifferentialForm (Euclid P) l := fun x => (γ (pL x)).compContinuousLinearMap pL
      with hβdef
    have hβ : ContDiff ℝ (⊤ : ℕ∞) β := by
      have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ) pL).contDiff
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) |>.comp (hγ.comp pL.contDiff)
      simpa [Function.comp_def] using this
    -- Step 3: `β x = 0` whenever `pL x ∉ spt γ`
    have hβ0 : ∀ x, pL x ∉ tsupport γ → β x = 0 := by
      intro x hx
      ext v
      simp [hβdef, image_eq_zero_of_notMem_tsupport hx]
    -- Step 4: `γ' = χ • β` is a test form on `ℝᴾ` with `spt γ' ⊆ spt χ ⊆ O`
    set g : DifferentialForm (Euclid P) l := fun x => χ x • β x with hgdef
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hχ.smul hβ
    have hgc : HasCompactSupport g := hχc.smul_right
    have hgs : tsupport g ⊆ tsupport χ := tsupport_smul_subset_left _ _
    let γ' : TestFormOn (univ : Set (Euclid P)) l := ⟨g, ⟨⟨hg, hgc⟩, subset_univ _⟩⟩
    -- Step 5: the coefficient norm is absolutely homogeneous, `|c • α| = |c| |α|`
    have hscale : ∀ (c : ℝ) (α : Covector (Euclid P) l),
        covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
      intro c α
      unfold covectorEuclideanNorm
      have : (∑ I : Fin l → Fin P, if StrictMono I then
            ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
          c ^ 2 * ∑ I : Fin l → Fin P, if StrictMono I then
            (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        split_ifs <;> simp [mul_pow]
      rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
    refine ⟨γ', hgs.trans hχO, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    -- Step 6 (b): `|χ x • β x| = χ x |β x| ≤ |β x|`
    · change covectorEuclideanNorm (χ x • β x) ≤ covectorEuclideanNorm (β x)
      rw [hscale, abs_of_nonneg (hχ01 x).1]
      exact mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2
    -- Step 7 (c): `χ = 1` on `O'`, and `β x = 0` at `x ∈ S \ O'`, since `K ⊆ O'`
    · change χ x • β x = β x
      by_cases hxO' : x ∈ O'
      · rw [hχ1 x hxO', one_smul]
      · have : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
        rw [hβ0 x this, smul_zero]
    -- Step 8 (d) on `O'`: `g = β` near `x`, so `dg(x) = dβ(x) = p^#(dγ)(x)` by naturality of `d`
    · change extDeriv g x = (extDeriv γ (pL x)).compContinuousLinearMap pL
      by_cases hxO' : x ∈ O'
      · have hev : g =ᶠ[𝓝 x] β := by
          filter_upwards [hO'.mem_nhds hxO'] with y hy
          simp [hgdef, hχ1 y hy]
        rw [hev.extDeriv_eq]
        have hpb := extDeriv_pullback (x := x) (ω := γ) (f := ⇑pL) (r := ((⊤ : ℕ∞) : WithTop ℕ∞))
          ((hγ.differentiable (by simp)).differentiableAt) pL.contDiff.contDiffAt (by simp)
        simpa [ContinuousLinearMap.fderiv] using hpb
      -- Step 9 (d) off `O'`: `g` vanishes near `x` and `γ` near `pL x`, so both sides are `0`
      · have hxK : pL x ∉ tsupport γ := fun h => hxO' (hKO' ⟨hx, h⟩)
        have hopen : IsOpen ((tsupport γ)ᶜ) := (isClosed_tsupport γ).isOpen_compl
        have hev : g =ᶠ[𝓝 x] 0 := by
          filter_upwards [(hopen.preimage pL.continuous).mem_nhds hxK] with y hy
          simp [hgdef, hβ0 y hy]
        have hev' : γ =ᶠ[𝓝 (pL x)] 0 := by
          filter_upwards [hopen.mem_nhds hxK] with y hy
          exact image_eq_zero_of_notMem_tsupport hy
        rw [hev.extDeriv_eq, hev'.extDeriv_eq]
        ext v
        simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have aux_integral_estimate : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (S F : Set (Euclid P)) (K : Set (Euclid m)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → IsCompact (S ∩ pL ⁻¹' K) → (∀ K' : Set (Euclid P), IsCompact K' → μ K' < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ c : ℝ, 0 ≤ c ∧ ∀ (ω : DifferentialForm (Euclid m) l) (M : ℝ), Continuous ω → (∀ y, y ∉ K → ω y = 0) → (∀ y, ‖ω y‖ ≤ M) → Integrable (fun x => ξ x ((ω (pL x)).compContinuousLinearMap pL)) (μ.restrict F) ∧ |∫ x in F, ξ x ((ω (pL x)).compContinuousLinearMap pL) ∂μ| ≤ c * M := by
    intro P m l pL S F K μ ξ hF hFS hSK hμ hξm hξb hN3
    -- Step 1 (N2): `|α|_E ≤ C ‖α‖` with `C = √#(Fin l → Fin m)`, since `|α(e_I)| ≤ ‖α‖`
    set C : ℝ := Real.sqrt (Fintype.card (Fin l → Fin m)) with hCdef
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    have hN2 : ∀ α : Covector (Euclid m) l, covectorEuclideanNorm α ≤ C * ‖α‖ := by
      intro α
      unfold covectorEuclideanNorm
      rw [hCdef, ← Real.sqrt_sq (norm_nonneg α), ← Real.sqrt_mul (Nat.cast_nonneg _)]
      apply Real.sqrt_le_sqrt
      calc (∑ I : Fin l → Fin m, if StrictMono I then
              (α (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))) ^ 2 else 0)
          ≤ ∑ _I : Fin l → Fin m, ‖α‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · have h1 := α.le_opNorm (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))
              have hprod : ∏ i, ‖EuclideanSpace.basisFun (Fin m) ℝ (I i)‖ = 1 := by
                simp
              rw [hprod, mul_one] at h1
              have h2 : |α (fun i ↦ EuclideanSpace.basisFun (Fin m) ℝ (I i))| ≤ ‖α‖ := by
                simpa [Real.norm_eq_abs] using h1
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) h2 2
            · positivity
        _ = (Fintype.card (Fin l → Fin m) : ℝ) * ‖α‖ ^ 2 := by simp
    -- Step 2: `A = S ∩ pL⁻¹(K)` is compact, so measurable with `μ(A) < ∞`; `c = C μ(A)`
    set μK : ℝ := (μ (S ∩ pL ⁻¹' K)).toReal with hμKdef
    have hSKm : MeasurableSet (S ∩ pL ⁻¹' K) := hSK.isClosed.measurableSet
    have hμKfin : μ (S ∩ pL ⁻¹' K) < ∞ := hμ _ hSK
    refine ⟨C * μK, mul_nonneg hC0 ENNReal.toReal_nonneg, fun ω M hω hωK hωM => ?_⟩
    -- Step 3: `M ≥ ‖ω(0)‖ ≥ 0`, and `β(x) = ω(pL x) ∘ pL` is continuous
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hωM 0)
    set β : Euclid P → Covector (Euclid P) l := fun x => (ω (pL x)).compContinuousLinearMap pL
      with hβdef
    have hβc : Continuous β := by
      have := (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin l) (F := ℝ)
        pL).continuous.comp (hω.comp pL.continuous)
      simpa [Function.comp_def] using this
    -- Step 4: `x ↦ ξ(x)(β(x))` is the continuous evaluation of `(ξ, β)`, so a.e. strongly measurable
    have hΦm : AEStronglyMeasurable (fun x => ξ x (β x)) μ :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) l)
        (F := ℝ)).continuous.comp_aestronglyMeasurable (hξm.prodMk hβc.aestronglyMeasurable)
    -- Step 5: `|ξ(x)(β(x))| ≤ g(x) = C M 1_A(x)` for `μ⌞F`-a.e. `x`
    set g : Euclid P → ℝ := (S ∩ pL ⁻¹' K).indicator (fun _ => C * M) with hgdef
    have hb : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (β x)‖ ≤ g x := by
      filter_upwards [ae_restrict_mem hF, ae_restrict_of_ae hξb] with x hxF hx
      by_cases hxK : pL x ∈ K
      · rw [hgdef, indicator_of_mem (show x ∈ S ∩ pL ⁻¹' K from ⟨hFS hxF, hxK⟩), Real.norm_eq_abs]
        calc |ξ x (β x)| ≤ covectorEuclideanNorm (β x) := hx _
          _ ≤ covectorEuclideanNorm (ω (pL x)) := hN3 _
          _ ≤ C * ‖ω (pL x)‖ := hN2 _
          _ ≤ C * M := mul_le_mul_of_nonneg_left (hωM _) hC0
      · have h0 : ω (pL x) = 0 := hωK _ hxK
        have hβ0 : β x = 0 := by
          ext v
          simp [hβdef, h0]
        rw [hgdef, indicator_of_notMem (fun h => hxK h.2), hβ0, map_zero, norm_zero]
    -- Step 6: `g` is `μ⌞F`-integrable since `μ(A ∩ F) ≤ μ(A) < ∞`; domination gives integrability
    have hgint : Integrable g (μ.restrict F) := by
      rw [hgdef, integrable_indicator_iff hSKm]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply hSKm]
      exact (lt_of_le_of_lt (measure_mono inter_subset_left) hμKfin).ne
    refine ⟨Integrable.mono' hgint hΦm.restrict hb, ?_⟩
    -- Step 7: `|∫_F ξ(β)| ≤ ∫ g d(μ⌞F) = C M μ(A ∩ F) ≤ C M μ(A) = c M`
    have hle := norm_integral_le_of_norm_le hgint hb
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    rw [hgdef, integral_indicator hSKm, setIntegral_const, smul_eq_mul]
    have hle2 : (μ.restrict F).real (S ∩ pL ⁻¹' K) ≤ μK := by
      rw [Measure.real, Measure.restrict_apply hSKm, hμKdef]
      exact ENNReal.toReal_mono hμKfin.ne (measure_mono inter_subset_left)
    have hCM : 0 ≤ C * M := mul_nonneg hC0 hM0
    calc (μ.restrict F).real (S ∩ pL ⁻¹' K) * (C * M) ≤ μK * (C * M) :=
          mul_le_mul_of_nonneg_right hle2 hCM
      _ = C * μK * M := by ring
  have aux_integral_current : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → ∃ Y : GeometricCurrentOn U l, ∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ := by
    intro P m l pL U S F μ ξ hF hFS hcpt hμ hξm hξb hN3
    -- every integrand is `μ⌞F`-integrable: `integral_estimate` with `K = spt ω`, `M = sup ‖ω‖`
    have hint : ∀ ω : TestFormOn U l, Integrable (fun x => ξ x
        (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)) (μ.restrict F) := by
      intro ω
      have hωc : Continuous (ω : DifferentialForm (Euclid m) l) := ω.property.1.1.continuous
      have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid m) l)) := ω.property.1.2
      obtain ⟨c, -, hc⟩ := aux_integral_estimate P m l pL S F
        (tsupport (ω : DifferentialForm (Euclid m) l)) μ ξ hF hFS (hcpt _ hK ω.property.2) hμ hξm
        hξb hN3
      obtain ⟨M, hM⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
      exact (hc _ M hωc (fun y hy => image_eq_zero_of_notMem_tsupport hy) hM).1
    -- `Y` is linear: `ω ↦ ⟨ω(pL x) ∘ pL, ξ(x)⟩` is linear for each `x`
    let T : CurrentOn U l :=
      { toFun := fun ω => ∫ x in F, ξ x
          (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ
        map_add' := fun ω η => by
          rw [← integral_add (hint ω) (hint η)]
          congr 1
          funext x
          rw [← map_add]
          congr 1
        map_smul' := fun c ω => by
          rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
          congr 1
          funext x
          rw [← smul_eq_mul, ← map_smul]
          congr 1 }
    refine ⟨⟨T, fun ωs hωs => ?_⟩, fun ω => rfl⟩
    -- continuity: the supports lie in one compact `K ⊆ U` and `ωⱼ → 0` uniformly on `K`
    obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hωs
    obtain ⟨c, hc0, hc⟩ := aux_integral_estimate P m l pL S F K μ ξ hF hFS
      (hcpt K hK hKU) hμ hξm hξb hN3
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (c + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 (hconv 0) _ hδ).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    -- `‖ωₙ(y)‖ ≤ ε / (c + 1)` everywhere: on `K` by uniform convergence, off `K` `ωₙ(y) = 0`
    have hbd : ∀ y, ‖(ωs n : DifferentialForm (Euclid m) l) y‖ ≤ ε / (c + 1) := by
      intro y
      by_cases hy : y ∈ K
      · have := hN n hn y hy
        simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
          norm_iteratedFDeriv_zero] at this
        exact this.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)), norm_zero]
        exact hδ.le
    have hωc : Continuous (ωs n : DifferentialForm (Euclid m) l) := (ωs n).property.1.1.continuous
    have := (hc _ _ hωc (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hsupp n h)))
      hbd).2
    rw [Real.dist_eq, sub_zero]
    calc |T (ωs n)| ≤ c * (ε / (c + 1)) := this
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  have aux_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P l) (Y : GeometricCurrentOn U l), IsOpen U → (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) l, |ξ x β| ≤ covectorEuclideanNorm β) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U l, Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ) → Y.massOn U ≤ μ (F ∩ pL ⁻¹' U) := by
    intro P m l pL U F μ ξ Y hU hξb hN3 hY
    -- `pL⁻¹(U)` is open, hence measurable
    have hUm : MeasurableSet (pL ⁻¹' U) := (hU.preimage pL.continuous).measurableSet
    -- Step 1: it suffices to bound `ofReal (Y ω)` for each admissible `ω`
    apply sSup_le
    rintro r ⟨ω, ⟨-, hω1⟩, rfl⟩
    show ENNReal.ofReal (Y ω) ≤ _
    rw [hY ω]
    -- Step 2: `‖Φ_ω‖ₑ ≤ 1_{pL⁻¹(U)}` a.e. on `F`; off `pL⁻¹(U)`, `ω (pL x) = 0` as `tsupport ω ⊆ U`
    have hpt : ∀ᵐ x ∂(μ.restrict F), ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ≤ (pL ⁻¹' U).indicator 1 x := by
      filter_upwards [ae_restrict_of_ae hξb] with x hx
      by_cases hxU : pL x ∈ U
      · rw [indicator_of_mem (show x ∈ pL ⁻¹' U from hxU), Pi.one_apply, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((hx _).trans ((hN3 _).trans (hω1 _)))
      · have h0 : (ω : DifferentialForm (Euclid m) l) (pL x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hxU (ω.property.2 h))
        have hβ0 : ((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL = 0 := by
          ext v
          simp [h0]
        rw [hβ0, map_zero, enorm_zero]
        exact zero_le
    -- Step 3: `ofReal (Y ω) ≤ ‖∫_F Φ_ω‖ₑ ≤ ∫⁻_F ‖Φ_ω‖ₑ ≤ ∫⁻_F 1_{pL⁻¹(U)} = μ(F ∩ pL⁻¹(U))`
    calc ENNReal.ofReal (∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ)
        ≤ ‖∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in F, ‖ξ x (((ω : DifferentialForm (Euclid m) l) (pL x)).compContinuousLinearMap pL)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in F, (pL ⁻¹' U).indicator 1 x ∂μ := lintegral_mono_ae hpt
      _ = μ (F ∩ pL ⁻¹' U) := by
          rw [lintegral_indicator_one hUm, Measure.restrict_apply hUm, inter_comm]
  have aux_boundary_mass_le : ∀ (P m l : ℕ) (pL : Euclid P →L[ℝ] Euclid m) (U : Set (Euclid m)) (S F : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (l + 1)) (Y : GeometricCurrentOn U (l + 1)) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (l + 1)), MeasurableSet F → F ⊆ S → (∀ K : Set (Euclid m), IsCompact K → K ⊆ U → IsCompact (S ∩ pL ⁻¹' K)) → (∀ γ : Covector (Euclid m) l, covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ) → (∀ ω : TestFormOn U (l + 1), Y ω = ∫ x in F, ξ x (((ω : DifferentialForm (Euclid m) (l + 1)) (pL x)).compContinuousLinearMap pL) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (l + 1), Z ω = ∫ x in F, ξ x ((ω : DifferentialForm (Euclid P) (l + 1)) x) ∂μ) → ∀ W : Set (Euclid m), IsOpen W → Y.boundary.massOn W ≤ Z.boundary.massOn (pL ⁻¹' W) := by
    intro P m l pL U S F μ ξ Y Z hF hFS hcpt hN3 hY hZ W hW
    -- Step 1: it suffices to bound `∂Y(γ)` for every `γ` admissible for `M_W(∂Y)`
    apply sSup_le
    rintro r ⟨γ, ⟨hγW, hγ1⟩, rfl⟩
    show ENNReal.ofReal (Y.boundary γ) ≤ _
    -- Steps 2–3: `S ∩ p⁻¹(spt γ)` is a compact subset of the open set `p⁻¹(W)`, so `p^#γ` has a
    -- cut-off `γ' ∈ 𝒟ˡ(ℝᴾ)` supported in `p⁻¹(W)`
    have hK : IsCompact (S ∩ pL ⁻¹' tsupport (γ : DifferentialForm (Euclid m) l)) :=
      hcpt _ γ.property.1.2 γ.property.2
    obtain ⟨γ', hγ'O, hγ'n, -, hγ'd⟩ := aux_pullback_extension P m l pL S
      (pL ⁻¹' W) (γ : DifferentialForm (Euclid m) l) γ.property.1.1 (hW.preimage pL.continuous) hK
      (fun x hx => hγW hx.2)
    -- Step 4: `|γ'(x)| ≤ |γ(p x) ∘ p| ≤ |γ(p x)| ≤ 1`, so `γ'` is admissible for `M_{p⁻¹(W)}(∂Z)`
    have hadm : γ' ∈ massAdmissibleOn (univ : Set (Euclid P)) l (pL ⁻¹' W) :=
      ⟨hγ'O, fun x => (hγ'n x).trans ((hN3 _).trans (hγ1 _))⟩
    -- Step 5: `∂Y(γ) = ∫_F ξ(p^#(dγ)) dμ = ∫_F ξ(dγ') dμ = ∂Z(γ')`, since `F ⊆ S`
    have heq : Y.boundary γ = Z.boundary γ' := by
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hY, hZ]
      apply setIntegral_congr_fun hF
      intro x hx
      change ξ x ((exteriorDerivative (γ : DifferentialForm (Euclid m) l)
          (pL x)).compContinuousLinearMap pL) =
        ξ x (exteriorDerivative (γ' : DifferentialForm (Euclid P) l) x)
      rw [hγ'd x (hFS hx)]
    -- Step 6: `ofReal (∂Y(γ)) = ofReal (∂Z(γ')) ≤ M_{p⁻¹(W)}(∂Z)`
    rw [heq]
    exact Z.boundary.le_massOn hadm
  intro P d v pL U S F μ ξ Z hv hpL hU hF hFS hcpt hμ hξm hξb hZ
  -- (N3): `|γ ∘ pL| ≤ |γ|` for covectors of every degree on `ℝⁿ`, `n = d + 1`.
  have hN3 := (Submission.cbr_ci_pw_orthonormal_covector_bounds P (d + 1) v pL hv hpL).2
  -- Steps 1–3: `Y` is a current in `U`, given by the integral formula (i).
  obtain ⟨Y, hY⟩ := aux_integral_current P (d + 1) (d + 1) pL U S F μ ξ
    hF hFS hcpt hμ hξm hξb (hN3 (d + 1))
  -- Step 4 gives (ii) and step 6 gives (iii).
  refine ⟨Y, hY,
    aux_mass_le P (d + 1) (d + 1) pL U F μ ξ Y hU hξb (hN3 (d + 1)) hY,
    fun W hW _ => aux_boundary_mass_le P (d + 1) d pL U S F μ ξ Y Z hF hFS
      hcpt (hN3 d) hY hZ W hW, fun ω => ?_⟩
  -- Step 5, (iv): cut off `p^#ω` near the compact set `S ∩ pL⁻¹(spt ω)`.
  obtain ⟨ω', -, -, hω', -⟩ := aux_pullback_extension P (d + 1) (d + 1) pL
    S univ (ω : DifferentialForm (Euclid (d + 1)) (d + 1)) ω.property.1.1 isOpen_univ
    (hcpt _ ω.property.1.2 ω.property.2) (subset_univ _)
  exact ⟨ω', hω'⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
