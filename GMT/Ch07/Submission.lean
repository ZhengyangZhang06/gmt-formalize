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

/-- **Weak convergence of derivatives against `C¹` test fields.**  If the `uₖ : ℝᵈ → ℝ` are
`K`-Lipschitz and converge uniformly to `u`, and `Ψ : ℝᵈ → ℝᵈ` is `C¹` with compact support, then
`∫ Duₖ[Ψ] → ∫ Du[Ψ]`.  The limit `u` is again `K`-Lipschitz.  Writing `Ψ = Σₗ Ψₗ eₗ`,
Rademacher's theorem and integration by parts give `∫ Dv[Ψ] = Σₗ ∫ qₗ v` for every Lipschitz `v`,
where `qₗ = DΨₗ[-eₗ]` is continuous with compact support; dominated convergence with the bound
`|qₗ| (|u| + 1)` gives `∫ qₗ uₖ → ∫ qₗ u`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_weak_smooth : ∀ (d : ℕ) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ) (Ψ : Euclid d → Euclid d), (∀ k, LipschitzWith K (us k)) → TendstoUniformly us u atTop → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → Tendsto (fun k => ∫ y, fderiv ℝ (us k) y (Ψ y)) atTop (𝓝 (∫ y, fderiv ℝ u y (Ψ y))) := by
  intro d K us u Ψ hus hU hΨ hΨc
  -- the uniform limit `u` is again `K`-Lipschitz
  have hu : LipschitzWith K u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hU.tendsto_at x).dist (hU.tendsto_at y))
      (Eventually.of_forall fun k => (hus k).dist_le_mul x y)
  -- coordinates `Ψₗ = ⟨Ψ, eₗ⟩`: `C¹` with compact support
  set e : Fin d → Euclid d := fun l => EuclideanSpace.single l 1
  set g : Fin d → Euclid d → ℝ := fun l y => Ψ y l
  have hg_smooth : ∀ l, ContDiff ℝ 1 (g l) := fun l =>
    (EuclideanSpace.proj l : Euclid d →L[ℝ] ℝ).contDiff.comp hΨ
  have hg_supp : ∀ l, HasCompactSupport (g l) := fun l =>
    hΨc.comp_left (g := fun v : Euclid d => v l) (by simp)
  have hdecomp : ∀ (L : Euclid d →L[ℝ] ℝ) (x : Euclid d), L x = ∑ l, L (e l) * x l := by
    intro L x
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp [map_sum, map_smul, e, EuclideanSpace.basisFun_apply, mul_comm]
  -- `qₗ = DΨₗ[-eₗ]` is continuous with compact support
  set q : Fin d → Euclid d → ℝ := fun l y => lineDeriv ℝ (g l) y (-(e l))
  have hq_eq : ∀ l, q l = fun y => fderiv ℝ (g l) y (-(e l)) := fun l => funext fun y =>
    ((hg_smooth l).differentiable one_ne_zero y).lineDeriv_eq_fderiv
  have hq_cont : ∀ l, Continuous (q l) := by
    intro l
    rw [hq_eq l]
    exact ((hg_smooth l).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hq_supp : ∀ l, HasCompactSupport (q l) := by
    intro l
    rw [hq_eq l]
    exact ((hg_supp l).fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euclid d →L[ℝ] ℝ => L (-(e l)))
      (by simp)
  -- for Lipschitz `v`, `∫ Dv[Ψ] = Σₗ ∫ Dv[eₗ] Ψₗ = Σₗ ∫ qₗ v` (Rademacher, integration by parts)
  have hsum : ∀ (v : Euclid d → ℝ) (C : NNReal), LipschitzWith C v →
      ∫ y, fderiv ℝ v y (Ψ y) = ∑ l, ∫ y, q l y * v y := by
    intro v C hv
    have h1 : (fun y => fderiv ℝ v y (Ψ y)) = fun y => ∑ l, fderiv ℝ v y (e l) * g l y := by
      funext y
      exact hdecomp _ _
    rw [h1, integral_finsetSum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      obtain ⟨D, hD⟩ := (hg_smooth l).lipschitzWith_of_hasCompactSupport (hg_supp l) one_ne_zero
      rw [← hv.integral_lineDeriv_mul_eq hD (hg_supp l) (e l)]
      apply integral_congr_ae
      filter_upwards [hv.ae_differentiableAt] with y hy
      rw [hy.lineDeriv_eq_fderiv]
    · intro l _
      have hgi : Integrable (g l) :=
        (hg_smooth l).continuous.integrable_of_hasCompactSupport (hg_supp l)
      refine Integrable.bdd_mul (c := C * ‖e l‖) hgi
        (measurable_fderiv_apply_const ℝ v (e l)).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
  rw [hsum u K hu]
  have hk : (fun k => ∫ y, fderiv ℝ (us k) y (Ψ y)) = fun k => ∑ l, ∫ y, q l y * us k y := by
    funext k
    exact hsum (us k) K (hus k)
  rw [hk]
  -- dominated convergence for each `∫ qₗ uₖ`, with bound `|qₗ| (|u| + 1)`
  refine tendsto_finsetSum _ fun l _ => ?_
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖q l y‖ * (‖u y‖ + 1))
  · exact Eventually.of_forall fun k => ((hq_cont l).mul (hus k).continuous).aestronglyMeasurable
  · rw [Metric.tendstoUniformly_iff] at hU
    filter_upwards [hU 1 one_pos] with k hk
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    gcongr
    have h1 := hk y
    rw [dist_eq_norm] at h1
    have h2 : ‖us k y‖ ≤ ‖u y‖ + ‖u y - us k y‖ := by
      have := norm_sub_norm_le (us k y) (u y)
      rw [norm_sub_rev] at this
      linarith
    linarith
  · exact ((hq_cont l).norm.mul (hu.continuous.norm.add continuous_const))
      |>.integrable_of_hasCompactSupport (hq_supp l).norm.mul_right
  · exact Eventually.of_forall fun y => ((hU.tendsto_at y).const_mul (q l y))

/-- **Weak convergence of derivatives against `L¹` fields.**  If the `uₖ : ℝᵈ → ℝ` are
`K`-Lipschitz and converge uniformly to `u`, then `∫ Duₖ[Φ] → ∫ Du[Φ]` for every integrable
`Φ : ℝᵈ → ℝᵈ`.  The limit `u` is `K`-Lipschitz, and for `K`-Lipschitz `v` and integrable `Θ` the
field `Dv[Θ]` is integrable with `|∫ Dv[Θ]| ≤ K ∫ |Θ|`.  Given `ε > 0`, take a `C¹` compactly
supported `Ψ` with `∫ |Φ - Ψ| ≤ ε/(4K + 1)`: such fields are dense in `L¹`, as each `c 1_s` with
`|s| < ∞` is approximated by `f c`, `f` a smooth Urysohn function for a compact `L ⊆ s` inside an
open `W ⊇ s` with `|W \ L|` small.  Then `|∫ Dv[Φ] - ∫ Dv[Ψ]| ≤ ε/4` for `v = uₖ, u`, and
`∫ Duₖ[Ψ] → ∫ Du[Ψ]` by `dor_lmbsf_pwl_fderiv_weak_smooth`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_weak_integrable : ∀ (d : ℕ) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ) (Φ : Euclid d → Euclid d), (∀ k, LipschitzWith K (us k)) → TendstoUniformly us u atTop → Integrable Φ → Tendsto (fun k => ∫ y, fderiv ℝ (us k) y (Φ y)) atTop (𝓝 (∫ y, fderiv ℝ u y (Φ y))) := by
  intro d K us u Φ hus hU hΦ
  -- the uniform limit `u` is `K`-Lipschitz
  have hu : LipschitzWith K u := LipschitzWith.of_dist_le_mul fun x z =>
    le_of_tendsto ((hU.tendsto_at x).dist (hU.tendsto_at z))
      (Eventually.of_forall fun k => (hus k).dist_le_mul x z)
  -- `‖Dv‖ ≤ K` for `K`-Lipschitz `v`, so `Dv[Θ]` is integrable and `|∫ Dv[Θ]| ≤ K ∫ |Θ|`
  have hbound : ∀ v : Euclid d → ℝ, LipschitzWith K v → ∀ Θ : Euclid d → Euclid d,
      Integrable Θ → Integrable (fun y => fderiv ℝ v y (Θ y)) ∧
        ‖∫ y, fderiv ℝ v y (Θ y)‖ ≤ K * ∫ y, ‖Θ y‖ := by
    intro v hv Θ hΘ
    have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ v y (Θ y)) volume :=
      Continuous.comp_aestronglyMeasurable
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Euclid d) (F := ℝ)).continuous
        ((measurable_fderiv ℝ v).aestronglyMeasurable.prodMk hΘ.aestronglyMeasurable)
    have hle : ∀ y, ‖fderiv ℝ v y (Θ y)‖ ≤ K * ‖Θ y‖ := fun y =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
    refine ⟨(hΘ.norm.const_mul K).mono' hmeas (Eventually.of_forall hle), ?_⟩
    calc ‖∫ y, fderiv ℝ v y (Θ y)‖ ≤ ∫ y, (K : ℝ) * ‖Θ y‖ :=
          norm_integral_le_of_norm_le (hΘ.norm.const_mul K) (Eventually.of_forall hle)
      _ = K * ∫ y, ‖Θ y‖ := integral_const_mul _ _
  -- `C¹` compactly supported fields are dense in `L¹`.  By `MemLp.induction_dense` it suffices to
  -- approximate `c 1_s` for `s` of finite measure: take a compact `L ⊆ s` and an open `W ⊇ s` with
  -- `|W \ L| < δ/|c|`, and a smooth `f : ℝᵈ → [0, 1]` with `f = 1` on `L` and support
  -- `W ∩ B_R(0) ⊇ L`; then `|f c - c 1_s| ≤ |c| 1_{W \ L}`.
  have hdense : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ Ψ : Euclid d → Euclid d,
      eLpNorm (Φ - Ψ) 1 volume ≤ ε ∧ ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ := by
    intro ε hε
    refine (memLp_one_iff_integrable.2 hΦ).induction_dense ENNReal.one_ne_top
      (fun Ψ => ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ) ?_ ?_ hε
    · intro c s hs hμs δ hδ
      rcases eq_or_ne c 0 with rfl | hc
      · exact ⟨0, by simp, contDiff_const, HasCompactSupport.zero⟩
      have hc0 : ‖c‖ₑ ≠ 0 := enorm_ne_zero.2 hc
      have hη : δ / ‖c‖ₑ / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hδ]
      obtain ⟨W, hsW, hWo, -, hW⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hη
      obtain ⟨L, hLs, hLc, hL⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hη
      obtain ⟨R, hR⟩ := hLc.isBounded.subset_ball 0
      obtain ⟨f, hfs, hf01, hfsupp, hf1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
        (hWo.inter isOpen_ball) hLc.isClosed (subset_inter (hLs.trans hsW) hR)
      have hf0 : ∀ x, x ∉ W ∩ ball 0 R → f x = 0 := fun x hx =>
        notMem_support.1 (hfsupp.symm ▸ hx)
      refine ⟨fun x => f x • c, ?_, hfs.smul contDiff_const, ?_⟩
      · have hpt : ∀ x, ‖((fun x => f x • c) - s.indicator fun _ => c) x‖
            ≤ ‖(W \ L).indicator (fun _ => c) x‖ := by
          intro x
          obtain ⟨hfx0, hfx1⟩ := hf01 (mem_range_self x)
          by_cases hxs : x ∈ s
          · by_cases hxL : x ∈ L
            · simp [indicator_of_mem hxs, (hf1 x).1 hxL]
            · rw [Pi.sub_apply, indicator_of_mem hxs,
                indicator_of_mem (mem_sdiff_of_mem (hsW hxs) hxL),
                show f x • c - c = (f x - 1) • c by rw [sub_smul, one_smul], norm_smul,
                Real.norm_eq_abs, abs_of_nonpos (by linarith)]
              exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
          · by_cases hxW : x ∈ W
            · rw [Pi.sub_apply, indicator_of_notMem hxs,
                indicator_of_mem (mem_sdiff_of_mem hxW fun h => hxs (hLs h)), sub_zero, norm_smul,
                Real.norm_eq_abs, abs_of_nonneg hfx0]
              exact mul_le_of_le_one_left (norm_nonneg _) hfx1
            · simp [indicator_of_notMem hxs, hf0 x fun h => hxW h.1]
        have hWL : volume (W \ L) ≤ δ / ‖c‖ₑ := by
          calc volume (W \ L) ≤ volume ((W \ s) ∪ (s \ L)) := measure_mono fun x hx => by
                by_cases h : x ∈ s
                · exact Or.inr ⟨h, hx.2⟩
                · exact Or.inl ⟨hx.1, h⟩
            _ ≤ volume (W \ s) + volume (s \ L) := measure_union_le _ _
            _ ≤ δ / ‖c‖ₑ / 2 + δ / ‖c‖ₑ / 2 := add_le_add hW.le hL.le
            _ = δ / ‖c‖ₑ := ENNReal.add_halves _
        calc eLpNorm ((fun x => f x • c) - s.indicator fun _ => c) 1 volume
            ≤ eLpNorm ((W \ L).indicator fun _ => c) 1 volume :=
              eLpNorm_mono ((hfs.continuous.smul continuous_const).aestronglyMeasurable.sub
                (aestronglyMeasurable_const.indicator hs)) hpt
          _ ≤ ‖c‖ₑ * volume (W \ L) := by
              simpa using eLpNorm_indicator_const_le c 1
                (μ := volume) (hWo.measurableSet.diff hLc.measurableSet).nullMeasurableSet
          _ ≤ ‖c‖ₑ * (δ / ‖c‖ₑ) := by gcongr
          _ = δ := ENNReal.mul_div_cancel hc0 enorm_ne_top
      · refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => ?_
        rw [hf0 x fun h => hx (ball_subset_closedBall h.2), zero_smul]
    · rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
      exact ⟨hf.add hg, hf'.add hg'⟩
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  -- a `C¹` compactly supported `Ψ` with `∫ |Φ - Ψ| ≤ η`, where `Kη ≤ ε/4`
  set η : ℝ := ε / (4 * K + 1) with hη
  have hηpos : 0 < η := div_pos hε (by positivity)
  have hKη : (K : ℝ) * η ≤ ε / 4 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [K.2]
  obtain ⟨Ψ, hΨε, hΨs, hΨc⟩ := hdense (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hηpos).ne'
  have hΨi : Integrable Ψ := hΨs.continuous.integrable_of_hasCompactSupport hΨc
  have hdiff : ∫ y, ‖(Φ - Ψ) y‖ ≤ η := by
    rw [integral_norm_eq_lintegral_enorm (hΦ.sub hΨi).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm (hΦ.sub hΨi).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hηpos.le hΨε
  -- replacing `Φ` by `Ψ` moves `∫ Dv[Φ]` by at most `Kη ≤ ε/4`
  have hclose : ∀ v : Euclid d → ℝ, LipschitzWith K v →
      dist (∫ y, fderiv ℝ v y (Φ y)) (∫ y, fderiv ℝ v y (Ψ y)) ≤ ε / 4 := by
    intro v hv
    rw [dist_eq_norm, ← integral_sub (hbound v hv Φ hΦ).1 (hbound v hv Ψ hΨi).1]
    calc ‖∫ y, (fderiv ℝ v y (Φ y) - fderiv ℝ v y (Ψ y))‖
        = ‖∫ y, fderiv ℝ v y ((Φ - Ψ) y)‖ := by simp only [Pi.sub_apply, map_sub]
      _ ≤ K * ∫ y, ‖(Φ - Ψ) y‖ := (hbound v hv (Φ - Ψ) (hΦ.sub hΨi)).2
      _ ≤ K * η := mul_le_mul_of_nonneg_left hdiff K.2
      _ ≤ ε / 4 := hKη
  -- `∫ Duₖ[Ψ] → ∫ Du[Ψ]` for the `C¹` compactly supported field `Ψ`
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (Submission.dor_lmbsf_pwl_fderiv_weak_smooth d K us u Ψ hus hU hΨs hΨc) (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hclose (us k) (hus k)
  have h2 : dist (∫ y, fderiv ℝ (us k) y (Ψ y)) (∫ y, fderiv ℝ u y (Ψ y)) < ε / 2 := hN k hk
  have h3 := hclose u hu
  rw [dist_comm] at h3
  linarith [dist_triangle4 (∫ y, fderiv ℝ (us k) y (Φ y)) (∫ y, fderiv ℝ (us k) y (Ψ y))
    (∫ y, fderiv ℝ u y (Ψ y)) (∫ y, fderiv ℝ u y (Φ y))]
/-- **Functions agreeing on a measurable set have equal derivatives a.e. on it.**  Assume that
density points see every direction (the statement of `Submission.dor_lmbsf_density_directions`).
If `Z ⊆ ℝᵈ` is measurable and `v₁ = v₂` on `Z`, then `Dv₁(y) = Dv₂(y)` at `Lᵈ`-a.e. `y ∈ Z` where
both are differentiable.  By the Besicovitch density theorem a.e. `y ∈ Z` is a density point of `Z`;
there each unit vector `e` is a limit of `(yᵢ - y)/|yᵢ - y|` with `yᵢ ∈ Z ∖ {y}`, `yᵢ → y`, and the
difference quotients of `v₁ - v₂` along `yᵢ` vanish, so `(Dv₁(y) - Dv₂(y)) e = 0`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn : (∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (d : ℕ) (Z : Set (Euclid d)) (v₁ v₂ : Euclid d → ℝ), MeasurableSet Z → EqOn v₁ v₂ Z → ∀ᵐ y ∂(volume : Measure (Euclid d)), y ∈ Z → DifferentiableAt ℝ v₁ y → DifferentiableAt ℝ v₂ y → fderiv ℝ v₁ y = fderiv ℝ v₂ y := by
  intro hDD d Z v₁ v₂ hZ hEq
  -- a.e. point of `Z` is a Lebesgue density point of `Z`
  have h := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid d)) Z
  rw [ae_restrict_iff' hZ] at h
  filter_upwards [h] with y hy hyZ h1 h2
  have hden := hy hyZ
  set L := fderiv ℝ v₁ y - fderiv ℝ v₂ y with hLdef
  have hv : HasFDerivAt (fun x => v₁ x - v₂ x) L y := h1.hasFDerivAt.sub h2.hasFDerivAt
  -- along `yᵢ ∈ Z` with `(yᵢ - y)/|yᵢ - y| → e` the difference quotients of `v₁ - v₂` are `0`
  have hunit : ∀ e : Euclid d, ‖e‖ = 1 → L e = 0 := by
    intro e he
    obtain ⟨ys, hysZ, hys, hdir⟩ := hDD d Z y hden e he
    have hd0 : Tendsto (fun i => ys i - y) atTop (𝓝 0) := by
      simpa using hys.sub_const y
    have hlim := (hv.hasFDerivWithinAt (s := univ)).lim (l := atTop)
      (c := fun i => ‖ys i - y‖⁻¹) (d := fun i => ys i - y) hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    have hzero : (fun i => ‖ys i - y‖⁻¹ • ((v₁ (y + (ys i - y)) - v₂ (y + (ys i - y))) -
        (v₁ y - v₂ y))) = fun _ => (0 : ℝ) := by
      funext i
      have hi : y + (ys i - y) = ys i := by abel
      rw [hi, hEq (hysZ i).1, hEq hyZ]
      simp
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- a linear map vanishing on unit vectors is `0`
  have hL : L = 0 := by
    ext e
    by_cases he : e = 0
    · simp [he]
    · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
      have h1' : ‖‖e‖⁻¹ • e‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have := hunit _ h1'
      rw [map_smul, smul_eq_mul, mul_eq_zero] at this
      rcases this with h | h
      · exact absurd (inv_eq_zero.1 h) hn
      · simpa using h
  exact sub_eq_zero.1 hL

/-- **Chain rule for the cutoff `γ ∘ F`, a.e. on a Borel set.**  Let `a < b`,
`γ(s) = min{1, max{0, (b - s)/(b - a)}}`, `F : ℝᵈ → ℝ` differentiable and `u` Lipschitz with
`u = γ ∘ F` on a Borel set `Z`.  Assuming the density-directions lemma (DD), for a.e. `y ∈ Z`,
`Du(y) = γ'(F(y)) DF(y)`, where `γ' = -(b - a)⁻¹` on `(a, b)` and `γ' = 0` elsewhere.  By
Rademacher `u` is differentiable a.e.  On the kink levels `Z ∩ {F = a}` and `Z ∩ {F = b}`, `u` agrees
with the constants `γ(a) = 1` and `γ(b) = 0`; off them `γ ∘ F` is, near `y`, identically `1`,
`(b - F)/(b - a)` or `0`, hence differentiable with derivative `γ'(F(y)) DF(y)`.  In each case the
agreement lemma `dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn` transfers the derivative to `u`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_cutoff_comp_ae : (∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (d : ℕ) (Z : Set (Euclid d)) (F u : Euclid d → ℝ) (K : NNReal) (a b : ℝ), MeasurableSet Z → Differentiable ℝ F → LipschitzWith K u → a < b → (∀ y ∈ Z, u y = min 1 (max 0 ((b - F y) / (b - a)))) → ∀ᵐ y ∂(volume : Measure (Euclid d)), y ∈ Z → fderiv ℝ u y = (if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y := by
  intro hDD d Z F u K a b hZ hF hu hab hEq
  have hFc : Continuous F := hF.continuous
  have hba : 0 < b - a := sub_pos.2 hab
  set g : Euclid d → ℝ := fun y => min 1 (max 0 ((b - F y) / (b - a))) with hgdef
  -- the Borel pieces `Z ∩ {F ∉ {a, b}}`, `Z ∩ {F = a}`, `Z ∩ {F = b}`
  have hZ0 : MeasurableSet (Z ∩ {y | F y ≠ a ∧ F y ≠ b}) := by
    refine hZ.inter ?_
    have h1 : MeasurableSet {y | F y ≠ a} :=
      (measurableSet_singleton a).compl.preimage hFc.measurable
    have h2 : MeasurableSet {y | F y ≠ b} :=
      (measurableSet_singleton b).compl.preimage hFc.measurable
    exact h1.inter h2
  have hZa : MeasurableSet (Z ∩ F ⁻¹' {a}) :=
    hZ.inter ((measurableSet_singleton a).preimage hFc.measurable)
  have hZb : MeasurableSet (Z ∩ F ⁻¹' {b}) :=
    hZ.inter ((measurableSet_singleton b).preimage hFc.measurable)
  -- Rademacher: `u` is differentiable a.e.
  have hdiff : ∀ᵐ y ∂(volume : Measure (Euclid d)), DifferentiableAt ℝ u y :=
    hu.ae_differentiableAt
  -- `u = γ ∘ F` off the kinks, `u = γ(a) = 1` on `{F = a}` and `u = γ(b) = 0` on `{F = b}`
  have h0 := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ {y | F y ≠ a ∧ F y ≠ b}) u g
    hZ0 (fun y hy => hEq y hy.1)
  have ha := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ F ⁻¹' {a}) u (fun _ => 1)
    hZa (by
      intro y hy
      have hFy : F y = a := hy.2
      simp only [hEq y hy.1, hFy, div_self hba.ne']
      simp)
  have hb := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ F ⁻¹' {b}) u (fun _ => 0)
    hZb (by
      intro y hy
      have hFy : F y = b := hy.2
      simp only [hEq y hy.1, hFy, sub_self, zero_div]
      simp)
  filter_upwards [hdiff, h0, ha, hb] with y hyd hy0 hya hyb hyZ
  -- kink levels: `Du(y) = 0 = γ'(F(y)) DF(y)`
  by_cases hFa : F y = a
  · have h := hya ⟨hyZ, hFa⟩ hyd (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp [hFa]
  by_cases hFb : F y = b
  · have h := hyb ⟨hyZ, hFb⟩ hyd (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp [hFb]
  -- off the kinks `g = γ ∘ F` is locally `1`, `(b - F)/(b - a)` or `0`
  have hgd : HasFDerivAt g ((if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y) y := by
    have hFd : HasFDerivAt F (fderiv ℝ F y) y := (hF y).hasFDerivAt
    rcases lt_or_gt_of_ne hFa with h | h
    · -- `F y < a`: `g = 1` near `y`
      have hev : g =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
        filter_upwards [hFc.continuousAt.eventually (gt_mem_nhds h)] with z hz
        have : 1 < (b - F z) / (b - a) := by
          rw [one_lt_div hba]; linarith
        simp only [hgdef]
        rw [max_eq_right (by linarith), min_eq_left this.le]
      have hn : ¬ (a < F y ∧ F y < b) := fun h' => absurd h'.1 (not_lt.2 h.le)
      simp only [hn, ite_false, zero_smul]
      exact (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hev
    · rcases lt_or_gt_of_ne hFb with h' | h'
      · -- `a < F y < b`: `g = (b - F)/(b - a)` near `y`
        have hev : g =ᶠ[𝓝 y] fun z => (b - F z) / (b - a) := by
          filter_upwards [hFc.continuousAt.eventually (lt_mem_nhds h),
            hFc.continuousAt.eventually (gt_mem_nhds h')] with z hz1 hz2
          have hpos : 0 < (b - F z) / (b - a) := div_pos (by linarith) hba
          have hlt : (b - F z) / (b - a) < 1 := by
            rw [div_lt_one hba]; linarith
          simp only [hgdef]
          rw [max_eq_right hpos.le, min_eq_right hlt.le]
        have hy' : a < F y ∧ F y < b := ⟨h, h'⟩
        simp only [hy', and_self, ite_true]
        have hlin : HasFDerivAt (fun z => (b - F z) / (b - a))
            (-(b - a)⁻¹ • fderiv ℝ F y) y := by
          have := ((hasFDerivAt_const b y).sub hFd).const_mul (b - a)⁻¹
          convert this using 1
          · funext z
            simp only [Pi.sub_apply]
            rw [div_eq_inv_mul]
          · rw [zero_sub, smul_neg, neg_smul]
        exact hlin.congr_of_eventuallyEq hev
      · -- `F y > b`: `g = 0` near `y`
        have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hFc.continuousAt.eventually (lt_mem_nhds h')] with z hz
          have : (b - F z) / (b - a) < 0 := div_neg_of_neg_of_pos (by linarith) hba
          simp only [hgdef]
          rw [max_eq_left this.le]
          simp
        have hn : ¬ (a < F y ∧ F y < b) := fun h'' => absurd h''.2 (not_lt.2 h'.le)
        simp only [hn, ite_false, zero_smul]
        exact (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
  have h := hy0 ⟨hyZ, hFa, hFb⟩ hyd hgd.differentiableAt
  rw [h, hgd.fderiv]
/-- **Cut-off localization of `hₖ ∘ ψ` near a compact subset of a `C¹` chart domain.**  Choose
`δ > 0` with `S = cthickening δ C ⊆ V` and a `C¹` Urysohn function `χ : ℝᵈ → [0, 1]` equal to `1`
on `cthickening (δ/2) C` and to `0` off `thickening δ C`, so `tsupport χ ⊆ S`.  Then
`uₖ = χ · (hₖ ∘ ψ)` and `u = χ · (h ∘ ψ)` agree with `hₖ ∘ ψ`, `h ∘ ψ` on `O = thickening (δ/2) C`.
On `S` the `hₖ ∘ ψ` are bounded by some `B` uniformly in `k` (`ψ(S)` is bounded, the `hₖ` are
`c`-Lipschitz and `hₖ(ψ(y₀))` converges), so the product and chain rules give
`‖Duₖ‖ ≤ B sup ‖Dχ‖ + c sup_S ‖Dψ‖`; `uₖ → u` uniformly because `0 ≤ χ ≤ 1`, and `u` is Lipschitz
as the pointwise limit of the `uₖ`.  For `C = ∅` all the functions are `0`. -/
theorem Submission.dor_lmbsf_pwl_chart_cutoff_localize : ∀ (P d : ℕ) (V C : Set (Euclid d)) (ψ : Euclid d → Euclid P) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (c : ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → IsCompact C → C ⊆ V → (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs h atTop → ∃ (O : Set (Euclid d)) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ), IsOpen O ∧ C ⊆ O ∧ (∀ k, LipschitzWith K (us k)) ∧ LipschitzWith K u ∧ TendstoUniformly us u atTop ∧ (∀ k, ∀ y ∈ O, us k y = hs k (ψ y)) ∧ ∀ y ∈ O, u y = h (ψ y) := by
  intro P d V C ψ hs h c hV hψ hC hCV hhs hhsb hU
  rcases C.eq_empty_or_nonempty with hCe | ⟨y₀, hy₀⟩
  · refine ⟨∅, 0, fun _ _ => 0, fun _ => 0, isOpen_empty, by simp [hCe],
      fun _ => LipschitzWith.const 0, LipschitzWith.const 0, ?_, by simp, by simp⟩
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ => by simpa using hε
  have hc : 0 ≤ c := (norm_nonneg _).trans (hhsb 0 0)
  -- the compact `S = cthickening δ C ⊆ V` and the cut-off `χ`, `1` near `C` and `0` off `S`
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hδ2 : 0 < δ / 2 := by positivity
  set S := cthickening δ C
  have hS : IsCompact S := hC.cthickening
  have hst : Disjoint (thickening δ C)ᶜ (cthickening (δ / 2) C) := by
    rw [disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' hδ (by linarith) C
  obtain ⟨χ, hχs, hχr, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := 1)
    isOpen_thickening.isClosed_compl isClosed_cthickening hst
  have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
  have hsupp : tsupport χ ⊆ S := by
    apply closure_minimal _ isClosed_cthickening
    intro y hy
    by_contra hcon
    exact hy ((hχ0 y).1 (fun h' => hcon (thickening_subset_cthickening δ C h')))
  have hχc : HasCompactSupport χ := hS.of_isClosed_subset (isClosed_tsupport χ) hsupp
  -- bounds `Mχ` for `‖Dχ‖`, `Mψ` for `‖Dψ‖` on `S` and `B` for `|hₖ ∘ ψ|` on `S`, uniform in `k`
  obtain ⟨Mχ, hMχ⟩ := (hχc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hχs.continuous_fderiv one_ne_zero)
  obtain ⟨Mψ, hMψ⟩ := hS.exists_bound_of_continuousOn
    ((hψ.continuousOn_fderiv_of_isOpen hV le_rfl).mono hδV)
  have hy₀S : y₀ ∈ S := self_subset_cthickening C hy₀
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ y₀)
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ y₀ hy₀S)
  have hhsL : ∀ k, LipschitzWith ⟨c, hc⟩ (hs k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le ((hhs k).differentiable one_ne_zero) (fun x =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact hhsb k x))
  have hψS : IsCompact (ψ '' S) := hS.image_of_continuousOn (hψ.continuousOn.mono hδV)
  obtain ⟨D, hD⟩ := hψS.isBounded.subset_closedBall (ψ y₀)
  obtain ⟨B₀, hB₀⟩ := ((hU.tendsto_at (ψ y₀)).abs).bddAbove_range
  set B := B₀ + c * D
  have hB : ∀ k, ∀ y ∈ S, |hs k (ψ y)| ≤ B := by
    intro k y hy
    have h1 : |hs k (ψ y) - hs k (ψ y₀)| ≤ c * dist (ψ y) (ψ y₀) := by
      have := (hhsL k).dist_le_mul (ψ y) (ψ y₀)
      rw [Real.dist_eq] at this
      exact this
    have h2 : dist (ψ y) (ψ y₀) ≤ D := hD (mem_image_of_mem ψ hy)
    have h3 : |hs k (ψ y₀)| ≤ B₀ := hB₀ ⟨k, rfl⟩
    have h4 := abs_sub_abs_le_abs_sub (hs k (ψ y)) (hs k (ψ y₀))
    have h5 : c * dist (ψ y) (ψ y₀) ≤ c * D := mul_le_mul_of_nonneg_left h2 hc
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 y₀ hy₀S)
  set K : ℝ := B * Mχ + c * Mψ with hKdef
  have hK0 : 0 ≤ K := by positivity
  -- `uₖ = χ · (hₖ ∘ ψ)` has `‖Duₖ‖ ≤ K`: product and chain rules on `tsupport χ ⊆ S ⊆ V`, and
  -- `uₖ` vanishes near every point off `tsupport χ`
  set us : ℕ → Euclid d → ℝ := fun k y => χ y * hs k (ψ y) with husdef
  have hderiv : ∀ k y, DifferentiableAt ℝ (us k) y ∧ ‖fderiv ℝ (us k) y‖ ≤ K := by
    intro k y
    by_cases hy : y ∈ tsupport χ
    · have hyS : y ∈ S := hsupp hy
      have hyV : y ∈ V := hδV hyS
      have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
        ((hψ.differentiableOn one_ne_zero y hyV).differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
      have hhd : HasFDerivAt (hs k) (fderiv ℝ (hs k) (ψ y)) (ψ y) :=
        ((hhs k).differentiable one_ne_zero (ψ y)).hasFDerivAt
      have hχd : HasFDerivAt χ (fderiv ℝ χ y) y := (hχs.differentiable one_ne_zero y).hasFDerivAt
      have hprod : HasFDerivAt (us k) (χ y • (fderiv ℝ (hs k) (ψ y)).comp (fderiv ℝ ψ y) +
          (hs k ∘ ψ) y • fderiv ℝ χ y) y := hχd.mul (hhd.comp y hψd)
      refine ⟨hprod.differentiableAt, ?_⟩
      rw [hprod.fderiv]
      calc ‖χ y • (fderiv ℝ (hs k) (ψ y)).comp (fderiv ℝ ψ y) + (hs k ∘ ψ) y • fderiv ℝ χ y‖
          ≤ ‖χ y‖ * (‖fderiv ℝ (hs k) (ψ y)‖ * ‖fderiv ℝ ψ y‖) +
              ‖(hs k ∘ ψ) y‖ * ‖fderiv ℝ χ y‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul]
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (c * Mψ) + B * Mχ := by
            gcongr
            · rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 y).1]
              exact (hχ01 y).2
            · exact hhsb k (ψ y)
            · exact hMψ y hyS
            · rw [Real.norm_eq_abs]
              exact hB k y hyS
            · exact hMχ y
        _ = K := by rw [hKdef]; ring
    · have hev : us k =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have : (tsupport χ)ᶜ ∈ 𝓝 y := (isClosed_tsupport χ).isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz
        simp [us, image_eq_zero_of_notMem_tsupport hz]
      have h0 : HasFDerivAt (us k) (0 : Euclid d →L[ℝ] ℝ) y :=
        (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
      refine ⟨h0.differentiableAt, ?_⟩
      rw [h0.fderiv, norm_zero]
      exact hK0
  have husL : ∀ k, LipschitzWith ⟨K, hK0⟩ (us k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hderiv k y).1) (fun y =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact (hderiv k y).2))
  -- `uₖ → u = χ · (h ∘ ψ)` uniformly since `0 ≤ χ ≤ 1`; the pointwise limit `u` is `K`-Lipschitz
  set u : Euclid d → ℝ := fun y => χ y * h (ψ y) with hudef
  have hUu : TendstoUniformly us u atTop := by
    rw [Metric.tendstoUniformly_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with k hk
    intro y
    have h1 := hk (ψ y)
    rw [Real.dist_eq] at h1 ⊢
    calc |u y - us k y| = |χ y| * |h (ψ y) - hs k (ψ y)| := by
          rw [← abs_mul]
          congr 1
          simp only [hudef, husdef]
          ring
      _ ≤ 1 * |h (ψ y) - hs k (ψ y)| := by
          gcongr
          rw [abs_of_nonneg (hχ01 y).1]
          exact (hχ01 y).2
      _ < ε := by linarith
  have huL : LipschitzWith ⟨K, hK0⟩ u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hUu.tendsto_at x).dist (hUu.tendsto_at y))
      (Eventually.of_forall fun k => (husL k).dist_le_mul x y)
  -- `χ = 1` on `O = thickening (δ / 2) C`
  have hχO : ∀ y ∈ thickening (δ / 2) C, χ y = 1 := fun y hy =>
    (hχ1 y).1 (thickening_subset_cthickening _ _ hy)
  refine ⟨thickening (δ / 2) C, ⟨K, hK0⟩, us, u, isOpen_thickening,
    self_subset_thickening hδ2 C, husL, huL, hUu, ?_, ?_⟩
  · intro k y hy
    simp [husdef, hχO y hy]
  · intro y hy
    simp [hudef, hχO y hy]
/-- **Continuous left inverse of an immersion's derivative.**  If `ψ` is `C¹` on the open set
`V ⊆ ℝᵈ` and `A(y) = Dψ(y)` is injective for every `y ∈ V`, then `R(y) = Γ(y)⁻¹ A(y)*`, with
`Γ(y) = A(y)* A(y)` the Gram operator, is a left inverse of `A(y)` depending continuously on
`y ∈ V`.  `Γ` is continuous on `V`, and `Γ(y)` is injective since `⟨Γ(y)z, z⟩ = |A(y)z|²`, hence
a unit of `L(ℝᵈ, ℝᵈ)`; `Ring.inverse` is continuous at units. -/
theorem Submission.dor_lmbsf_pwl_immersion_left_inverse : ∀ (P d : ℕ) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ∃ R : Euclid d → (Euclid P →L[ℝ] Euclid d), ContinuousOn R V ∧ ∀ y ∈ V, (R y).comp (fderiv ℝ ψ y) = ContinuousLinearMap.id ℝ (Euclid d) := by
  intro P d V ψ hV hψ hinj
  let A : Euclid d → (Euclid d →L[ℝ] Euclid P) := fun y => fderiv ℝ ψ y
  -- the Gram operator `Γ(y) = A(y)* A(y)`
  let Γ : Euclid d → (Euclid d →L[ℝ] Euclid d) :=
    fun y => (ContinuousLinearMap.adjoint (A y)).comp (A y)
  -- `Γ(y)` is injective (`⟨Γ(y)z, z⟩ = |A(y)z|²`), hence bijective and a unit
  have hunit : ∀ y ∈ V, IsUnit (Γ y) := by
    intro y hy
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hinjΓ : Injective (Γ y) := by
      intro z₁ z₂ hz
      have h0 : Γ y (z₁ - z₂) = 0 := by rw [map_sub, hz, sub_self]
      have h1 : inner ℝ (A y (z₁ - z₂)) (A y (z₁ - z₂)) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        change inner ℝ (Γ y (z₁ - z₂)) (z₁ - z₂) = 0
        rw [h0, inner_zero_left]
      have h2 : A y (z₁ - z₂) = 0 := by
        simpa using h1
      have h3 : z₁ - z₂ = 0 := by
        apply hinj y hy
        rw [h2, map_zero]
      exact sub_eq_zero.1 h3
    have hsurj : Surjective (Γ y : Euclid d →ₗ[ℝ] Euclid d) :=
      LinearMap.injective_iff_surjective.1 hinjΓ
    exact ⟨hinjΓ, hsurj⟩
  refine ⟨fun y => (Ring.inverse (Γ y)).comp (ContinuousLinearMap.adjoint (A y)), ?_, ?_⟩
  · have hA : ContinuousOn A V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
    have hAd : ContinuousOn (fun y => ContinuousLinearMap.adjoint (A y)) V :=
      ContinuousLinearMap.adjoint.continuous.comp_continuousOn hA
    have hΓ : ContinuousOn Γ V := hAd.clm_comp hA
    -- `Ring.inverse` is continuous at every unit
    have hinv : ContinuousOn (fun y => Ring.inverse (Γ y)) V := by
      intro y hy
      have := NormedRing.inverse_continuousAt (hunit y hy).unit
      rw [IsUnit.unit_spec] at this
      exact this.comp_continuousWithinAt (hΓ y hy)
    exact hinv.clm_comp hAd
  · intro y hy
    rw [ContinuousLinearMap.comp_assoc]
    exact Ring.inverse_mul_cancel _ (hunit y hy)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
