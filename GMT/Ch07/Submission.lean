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
/-- **The approximate tangent projection of an integer multiplicity triple is measurable**
(Simon Ch. 3, 1.4 and 1.5(1); Ch. 6, 3.1).  For `R = (M, θ, ξ)`, `x ↦ p_{TₓM}` is
`Hⁿ⌞M`-a.e. strongly measurable.  By uniqueness of approximate tangent planes, `TₓM` is a.e. the
plane oriented by `ξ(x)`.  A unit simple `n`-vector `ζ = ±τ₁ ∧ ⋯ ∧ τₙ` determines its plane: if
also `ζ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` and `y ⊥ span τ'`, the `n`-covector `α(u) = det(⟨cₖ, uⱼ⟩)`, where `c` is
`τ` with `τᵢ` replaced by `y`, gives `±⟨y, τᵢ⟩ = ±α(τ) = ζ(α) = ±α(τ') = 0`, so `τᵢ ∈ span τ'`.
Hence `p_{TₓM} = G(ξ(x))` a.e., where `G(ζ)` is the projection onto the plane of `ζ` (`0` if there
is none).  `G` is Borel: `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` is continuous on the compact set `Ω` of
orthonormal frames and signs, and `G(Φ(τ, s)) = Σₖ ⟨τₖ, ·⟩ τₖ` is continuous, so for closed `t`,
`G⁻¹(t) = Φ(Ω ∩ (G ∘ Φ)⁻¹(t)) ∪ (Φ(Ω)ᶜ ∩ {0 ∈ t})` is Borel. -/
theorem Submission.imrep_approxTangent_starProjection_aesm : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) := by
  intro P n U R
  classical
  -- `ev τ = (α ↦ α(τ₁, …, τₙ))`, a continuous alternating map of `τ`
  let ev : Euclid P [⋀^Fin n]→L[ℝ] MultiVector P n :=
    (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
  have hev : ∀ (τ : Fin n → Euclid P) (α : Covector (Euclid P) n), ev τ α = α τ :=
    fun τ α => rfl
  -- `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` on the compact set `Ω` of orthonormal frames and signs `s = ±1`
  let Φ : (Fin n → Euclid P) × ℝ → MultiVector P n := fun ω => ω.2 • ev ω.1
  have hΦc : Continuous Φ := continuous_snd.smul (ev.coe_continuous.comp continuous_fst)
  let Ω : Set ((Fin n → Euclid P) × ℝ) := {τ | Orthonormal ℝ τ} ×ˢ {1, -1}
  have hΩ : IsCompact Ω := by
    refine IsCompact.prod (isCompact_of_isClosed_isBounded ?_ ?_) (Set.toFinite _).isCompact
    · have hset : {τ : Fin n → Euclid P | Orthonormal ℝ τ} =
          ⋂ i, ⋂ j, {τ | inner ℝ (τ i) (τ j) = if i = j then (1 : ℝ) else 0} := by
        ext τ
        simp [orthonormal_iff_ite]
      rw [hset]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
    · refine (isBounded_iff_subset_closedBall 0).mpr ⟨1, fun τ hτ => ?_⟩
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hτ.1 i).le
  -- `ζ` orients `Q` iff `ζ = Φ(τ, s)` for a point `(τ, s)` of `Ω` with `span τ = Q`
  have horient : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q ↔ ∃ ω ∈ Ω, Φ ω = ζ ∧ Submodule.span ℝ (range ω.1) = Q := by
    intro ζ Q
    constructor
    · rintro ⟨τ, hτ, hQ, h | h⟩
      · refine ⟨(τ, 1), ⟨hτ, Or.inl rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
      · refine ⟨(τ, -1), ⟨hτ, Or.inr rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
    · rintro ⟨⟨τ, s⟩, ⟨hτ, hs⟩, rfl, hQ⟩
      refine ⟨τ, hτ, hQ, ?_⟩
      rcases hs with rfl | rfl
      · left
        intro α
        simp [Φ, hev]
      · right
        intro α
        simp [Φ, hev]
  -- the `n`-covector `u ↦ det(⟨cₖ, uⱼ⟩)ₖⱼ`
  have hdet : ∀ c : Fin n → Euclid P, ∃ α : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, α u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
    intro c
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => (innerSL ℝ (c k)).toLinearMap
    let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hA : ∀ u : Fin n → Euclid P, A u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
      intro u
      rw [← Matrix.det_transpose]
      rfl
    have hAc : Continuous fun u : Fin n → Euclid P => A u := by
      simp only [hA]
      exact Continuous.matrix_det (continuous_matrix fun k j => by
        simp only [Matrix.of_apply]
        exact continuous_const.inner (continuous_apply j))
    exact ⟨{ A with cont := hAc }, hA⟩
  -- a unit simple `n`-vector determines its plane: if `ζ` orients `span τ` and `span τ'`, then
  -- each `τᵢ` is orthogonal to `(span τ')ᗮ`
  have hle : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q ≤ Q' := by
    rintro ζ Q Q' ⟨τ, hτ, rfl, hζ⟩ ⟨τ', hτ', rfl, hζ'⟩
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ')),
      Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨α, hα⟩ := hdet (Function.update τ i y)
    -- `α(τ)` is the determinant of the identity matrix with row `i` replaced by `(⟨y, τⱼ⟩)ⱼ`
    have h1 : α τ = inner ℝ y (τ i) := by
      rw [hα]
      have hM : (Matrix.of fun k j => inner ℝ (Function.update τ i y k) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => inner ℝ y (τ j)) := by
        ext k j
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk, Matrix.one_apply, orthonormal_iff_ite.mp hτ k j]
      rw [hM, ← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
        ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    -- row `i` of the matrix of `α(τ')` is `(⟨y, τ'ⱼ⟩)ⱼ = 0`
    have h2 : α τ' = 0 := by
      rw [hα]
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      simp only [Matrix.of_apply, Function.update_self]
      rw [real_inner_comm]
      exact hy _ (Submodule.subset_span ⟨j, rfl⟩)
    have h3 : ζ α = 0 := by
      rcases hζ' with h | h <;> simp [h, h2]
    rcases hζ with h | h
    · rw [← h1, ← h, h3]
    · have h4 := h α
      rw [h3] at h4
      rw [← h1]
      linarith
  have huniq : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q = Q' :=
    fun ζ Q Q' h h' => le_antisymm (hle ζ Q Q' h h') (hle ζ Q' Q h' h)
  -- the projection onto the span of an orthonormal frame `τ` is `Σₖ ⟨τₖ, ·⟩ τₖ`, continuous in `τ`
  let F : (Fin n → Euclid P) × ℝ → (Euclid P →L[ℝ] Euclid P) :=
    fun ω => ∑ k, (innerSL ℝ (ω.1 k)).smulRight (ω.1 k)
  have hFapply : ∀ ω v, F ω v = ∑ k, inner ℝ (ω.1 k) v • ω.1 k := by
    intro ω v
    simp [F]
  have hFc : Continuous F := by
    refine continuous_clm_apply.mpr fun v => ?_
    simp only [hFapply]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hFproj : ∀ ω ∈ Ω, (Submodule.span ℝ (range ω.1)).starProjection = F ω := by
    rintro ⟨τ, s⟩ ⟨hτ, -⟩
    refine ContinuousLinearMap.ext fun v => ?_
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hFapply]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨j, rfl⟩
        rw [hFapply, inner_sub_left, sum_inner]
        simp [inner_smul_left, orthonormal_iff_ite.mp hτ, real_inner_comm]
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx
        rw [inner_smul_right, hx, mul_zero]
  -- `G ζ` is the projection onto the plane oriented by `ζ` (`0` if there is none)
  let G : MultiVector P n → (Euclid P →L[ℝ] Euclid P) := fun ζ =>
    if h : ∃ Q, IsUnitOrientationOf ζ Q then h.choose.starProjection else 0
  have hGQ : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → G ζ = Q.starProjection := by
    intro ζ Q hQ
    have hex : ∃ Q, IsUnitOrientationOf ζ Q := ⟨Q, hQ⟩
    simp only [G, dite_eq_left hex]
    rw [huniq _ _ _ hex.choose_spec hQ]
  have hGΦ : ∀ ω ∈ Ω, G (Φ ω) = F ω := fun ω hω => by
    rw [hGQ _ _ ((horient _ _).mpr ⟨ω, hω, rfl, rfl⟩), hFproj ω hω]
  -- `G` is Borel: for closed `t`, `G⁻¹(t)` is a compact set `Φ(Ω ∩ F⁻¹(t))` together with the
  -- complement of the compact set `Φ(Ω)` (if `0 ∈ t`)
  have hG : Measurable G := by
    refine measurable_of_isClosed fun t ht => ?_
    have hset : G ⁻¹' t = Φ '' (Ω ∩ F ⁻¹' t) ∪
        ((Φ '' Ω)ᶜ ∩ {_ζ | (0 : Euclid P →L[ℝ] Euclid P) ∈ t}) := by
      ext ζ
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
        Set.mem_compl_iff]
      by_cases h : ∃ Q, IsUnitOrientationOf ζ Q
      · obtain ⟨Q, hQ⟩ := h
        obtain ⟨ω, hω, hΦω, -⟩ := (horient ζ Q).mp hQ
        have hGζ : G ζ = F ω := by
          rw [← hΦω]
          exact hGΦ ω hω
        constructor
        · intro hζt
          exact Or.inl ⟨ω, ⟨hω, by rwa [← hGζ]⟩, hΦω⟩
        · rintro (⟨ω', ⟨hω', hω't⟩, hΦω'⟩ | ⟨hn, -⟩)
          · rw [← hΦω', hGΦ ω' hω']
            exact hω't
          · exact absurd ⟨ω, hω, hΦω⟩ hn
      · have hGζ : G ζ = 0 := dite_eq_right h
        have hn : ¬∃ ω, ω ∈ Ω ∧ Φ ω = ζ := fun ⟨ω, hω, hΦω⟩ =>
          h ⟨_, (horient ζ _).mpr ⟨ω, hω, hΦω, rfl⟩⟩
        rw [hGζ]
        constructor
        · intro h0
          exact Or.inr ⟨hn, h0⟩
        · rintro (⟨ω', ⟨hω', -⟩, hΦω'⟩ | ⟨-, h0⟩)
          · exact absurd ⟨ω', hω', hΦω'⟩ hn
          · exact h0
    rw [hset]
    exact ((hΩ.inter_right (ht.preimage hFc)).image hΦc).isClosed.measurableSet.union
      ((hΩ.image hΦc).isClosed.measurableSet.compl.inter (MeasurableSet.const _))
  -- a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes), so
  -- `p_{TₓM} = G(ξ(x))`
  have hae : (fun x => (approxTangentPlane n R.carrier x).starProjection)
      =ᵐ[μHE[n].restrict R.carrier] G ∘ R.orient := by
    filter_upwards [R.orients] with x ⟨Q, hQ, hor⟩
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    have h1 : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    rw [Function.comp_apply, hGQ _ _ hor, h1]
  -- `G ∘ ξ` is a.e. measurable, with values in the finite-dimensional space `End(ℝᴾ)`
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  exact ((hG.comp_aemeasurable R.aestronglyMeasurable_orient.aemeasurable).aestronglyMeasurable
    ).congr hae.symm
/-- **A.e. strongly measurable maps into `L(ℝᴾ, ℝᴾ)` are a.e. measurable.**  With the operator
norm, `Euclid P →L[ℝ] Euclid P` is a metric space whose measurable structure is its Borel
σ-algebra (`ContinuousLinearMap.instBorelSpace`).  A strongly measurable representative `g` of `f`
is a pointwise limit of simple functions `gₖ`; for open `O ≠ L`, `dist(gₖ, Oᶜ) → dist(g, Oᶜ)`, so
`g⁻¹(O) = {dist(g, Oᶜ) > 0}` is measurable.  Hence `g` is Borel measurable and `f = g` a.e. -/
theorem Submission.dtc_cone_opEuclid_aemeasurable_of_aesm : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable f μ → AEMeasurable f μ := by
  intro P μ f hf
  exact hf.aemeasurable

/-- **The approximate tangent projection of an integer multiplicity triple is a.e. measurable**
(Simon Ch. 3, 1.4 and 1.5(1); Ch. 6, 3.1).  For `R = (M, θ, ξ)`, `x ↦ p_{TₓM}` is
`Hⁿ⌞M`-a.e. strongly measurable, since a.e. `TₓM` is the plane oriented by `ξ(x)`.  A.e. strongly
measurable maps into the finite-dimensional normed space `L(ℝᴾ, ℝᴾ)` are a.e. measurable for its
Borel σ-algebra. -/
theorem Submission.dtc_cone_tangentProjection_aemeasurable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) := by
  intro P n U R
  exact Submission.dtc_cone_opEuclid_aemeasurable_of_aesm P _ _
    (Submission.imrep_approxTangent_starProjection_aesm P n U R)
/-- **Simon 4.3.6, the stationary monotonicity identity** (Ch. 4, 3.1–3.6, chapter-04.txt
lines 215–307, applied with `U = ℝᴾ`; used in the proof of 7.3.1, chapter-07.txt line 356).
Let `R = (M, θ, ξ)` be an integer multiplicity triple in `ℝᴾ` with `V = v(M, θ)` stationary:
`δV(X) = 0` for every `X ∈ C¹_c(ℝᴾ; ℝᴾ)`.  Then for `z ∈ ℝᴾ` and `0 < σ ≤ ρ`, with closed balls,
`μ_V = θHⁿ⌞M` and `p_x` the orthogonal projection onto `TₓM`,
`σ⁻ⁿμ_V(B_σ(z)) + ∫_{B_ρ(z) \ B_σ(z)} |(x − z) − p_x(x − z)|² / |x − z|ⁿ⁺² dμ_V = ρ⁻ⁿμ_V(B_ρ(z))`.
`δV(X) = ∫ div_M X dμ_V`, and for `X(x) = η(|x − z|²)(x − z)` (3.2), `μ_V`-a.e.
`div_M X = nη + 2η'|p_x(x − z)|²`, since `dim TₓM = n` and `x ↦ p_x` is `μ_V`-measurable
(`dtc_cone_tangentProjection_aemeasurable`, `μ_V ≪ Hⁿ⌞M`).  Simon integrates (3.3) for the
cutoffs `φ(r/t)` against `t⁻ⁿ⁻¹ dt` over `[σ, ρ]` (3.4–3.5); here this is done in the field:
`η = F ∘ m_σ − F ∘ m_ρ` with `F(u) = u^{-n/2}` and `m_c` a `C¹` smoothing of `max(·, c²)` on
`[c², c² + ε]`, so `η → max(·, σ²)^{-n/2} − max(·, ρ²)^{-n/2}` as `ε ↓ 0`.  The divergences
converge pointwise and are uniformly bounded on `B_{ρ+1}(z)`, so dominated convergence (3.6)
gives `n(σ⁻ⁿμ_V(B_σ) − ρ⁻ⁿμ_V(B_ρ) + ∫_{B_ρ \ B_σ} |D^⊥r|²r⁻ⁿ dμ_V) = 0`, with `D^⊥r` the normal
part of `(x − z)/|x − z|`.  For `n = 0`, `TₓM = 0` a.e. and the identity is additivity of
`μ_V`. -/
theorem Submission.dtc_cone_monotonicity_identity : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → ∀ (z : Euclid P) (σ ρ : ℝ), 0 < σ → σ ≤ ρ → R.measure (closedBall z σ) / ENNReal.ofReal (σ ^ n) + ∫⁻ x in closedBall z ρ \ closedBall z σ, ENNReal.ofReal (‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2)) ∂R.measure = R.measure (closedBall z ρ) / ENNReal.ofReal (ρ ^ n) := by
  intro P n R hstat z σ ρ hσ hσρ
  classical
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- `μ_V = θHⁿ⌞M` is finite on compact sets
  have : IsFiniteMeasureOnCompacts R.measure := ⟨fun K hK => by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK (subset_univ K)).lt_top⟩
  -- `x ↦ p_x` is `μ_V`-measurable, since `μ_V ≪ Hⁿ⌞M`
  have hp : AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure :=
    (Submission.dtc_cone_tangentProjection_aemeasurable P n univ R).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hpv : AEMeasurable
      (fun x => ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2) R.measure :=
    (ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
      (hp.prodMk (measurable_id.sub_const z).aemeasurable)).norm.pow_const 2
  -- `μ_V`-a.e., `TₓM` is an `n`-dimensional approximate tangent plane
  have hrank : ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec.finrank_eq
  -- Pythagoras: `|(x - z) - p_x(x - z)|² = |x - z|² - |p_x(x - z)|²`
  have hpyth : ∀ x : Euclid P,
      ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 =
        ‖x - z‖ ^ 2 - ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 := by
    intro x
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection (x - z)
      (approxTangentPlane n R.carrier x)
    rw [Submodule.starProjection_orthogonal] at h
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    linarith
  -- the first variation is the `μ_V`-integral of `div_M X`
  have hfv : ∀ Y : Euclid P → Euclid P,
      R.firstVariation Y = ∫ x, tangentialDivergence n R.carrier Y x ∂R.measure := by
    intro Y
    have hd : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    have hm : Measurable fun x => (R.mult x : NNReal) :=
      (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R.measurable_mult
    rw [IMRep.measure, IMRep.firstVariation, hd, integral_withDensity_eq_integral_smul hm]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [NNReal.smul_def])
  -- Simon 4.3.2–4.3.3 for radial fields `X(x) = η(|x - z|²)(x - z)`:
  -- `div_M X = n η(|x - z|²) + 2η'(|x - z|²)|p_x(x - z)|²` `μ_V`-a.e.
  have hrad : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → ∀ R0 : ℝ, (∀ s, R0 ^ 2 ≤ s → η s = 0) →
      ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2) + 2 * deriv η (‖x - z‖ ^ 2) *
        ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2) ∂R.measure = 0 := by
    intro η hη R0 hcut
    have hsub : ContDiff ℝ 1 (fun x : Euclid P => x - z) := contDiff_id.sub contDiff_const
    have hX : ContDiff ℝ 1 (fun x : Euclid P => η (‖x - z‖ ^ 2) • (x - z)) :=
      (hη.comp (hsub.norm_sq ℝ)).smul hsub
    have hXc : HasCompactSupport (fun x : Euclid P => η (‖x - z‖ ^ 2) • (x - z)) := by
      refine (isCompact_closedBall z |R0|).of_isClosed_subset (isClosed_tsupport _) ?_
      refine closure_minimal (fun x hx => ?_) isClosed_closedBall
      by_contra hball
      have hnorm : |R0| < ‖x - z‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hball
      have hR0 : R0 ^ 2 ≤ ‖x - z‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hnorm.le 2
      exact hx (by simp [hcut _ hR0])
    have hD : ∀ x : Euclid P, HasFDerivAt (fun y : Euclid P => η (‖y - z‖ ^ 2) • (y - z))
        (η (‖x - z‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
          (2 * deriv η (‖x - z‖ ^ 2)) • (innerSL ℝ (x - z)).smulRight (x - z)) x := by
      intro x
      have hs : HasFDerivAt (fun y : Euclid P => y - z) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
        hasFDerivAt_sub_const z
      have hηx := ((hη.differentiable (by simp)) (‖x - z‖ ^ 2)).hasDerivAt
      refine ((hηx.comp_hasFDerivAt x hs.norm_sq).smul hs).congr_fderiv
        (ContinuousLinearMap.ext fun w => ?_)
      simp only [Function.comp_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      module
    have htr : ∀ x : Euclid P,
        tangentialDivergence n R.carrier (fun y : Euclid P => η (‖y - z‖ ^ 2) • (y - z)) x =
          η (‖x - z‖ ^ 2) * (Module.finrank ℝ (approxTangentPlane n R.carrier x) : ℝ) +
            2 * deriv η (‖x - z‖ ^ 2) *
              ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 := by
      intro x
      rw [tangentialDivergence, (hD x).fderiv]
      set K := approxTangentPlane n R.carrier x
      have hlin : K.starProjection.toLinearMap ∘ₗ
          (η (‖x - z‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
            (2 * deriv η (‖x - z‖ ^ 2)) • (innerSL ℝ (x - z)).smulRight (x - z)).toLinearMap =
          η (‖x - z‖ ^ 2) • K.starProjection.toLinearMap +
            (2 * deriv η (‖x - z‖ ^ 2)) •
              (innerSL ℝ (x - z)).toLinearMap.smulRight (K.starProjection (x - z)) := by
        ext w
        simp [map_smul, smul_smul]
      have htrK : LinearMap.trace ℝ (Euclid P) K.starProjection.toLinearMap =
          (Module.finrank ℝ K : ℝ) := by
        rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
          LinearMap.trace_comp_comm']
        have hcomp : K.orthogonalProjectionOnto.toLinearMap.comp K.subtypeL.toLinearMap =
            LinearMap.id := by
          ext y
          simp
        rw [hcomp, LinearMap.trace_id]
      have hinner :
          inner ℝ (x - z) (K.starProjection (x - z)) = ‖K.starProjection (x - z)‖ ^ 2 := by
        rw [← K.inner_starProjection_left_eq_right (x - z) (x - z)]
        simpa using K.re_inner_starProjection_eq_normSq (x - z)
      rw [hlin, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htrK]
      simp only [smul_eq_mul, ContinuousLinearMap.coe_coe, innerSL_apply_apply, hinner]
      ring
    have h0 := hstat _ hX hXc
    rw [hfv] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hrank] with x hx
    rw [htr x, hx]
    ring
  -- the smooth transition `τ` (`0` on `(-∞, 0]`, `1` on `[1, ∞)`) and a bound for `τ'`
  have hτc : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hτd : ∀ u, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
    fun u => ((hτc.differentiable (by simp)) u).hasDerivAt
  have hτ0 : ∀ u : ℝ, u < 0 → deriv Real.smoothTransition u = 0 := by
    intro u hu
    have h : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hu] with w hw
      exact Real.smoothTransition.zero_of_nonpos hw.le
    rw [h.deriv_eq, deriv_const]
  have hτ1 : ∀ u : ℝ, 1 < u → deriv Real.smoothTransition u = 0 := by
    intro u hu
    have h : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 1 := by
      filter_upwards [lt_mem_nhds hu] with w hw
      exact Real.smoothTransition.one_of_one_le hw.le
    rw [h.deriv_eq, deriv_const]
  obtain ⟨Cτ, hCτ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hτc.continuous_deriv le_rfl).continuousOn (s := Icc (0 : ℝ) 1))
  have hCτ0 : 0 ≤ Cτ := (norm_nonneg _).trans (hCτ 0 ⟨le_rfl, zero_le_one⟩)
  -- `m c ε` is `C¹`, equals `c` on `(-∞, c]` and the identity on `(c + ε, ∞)`; `dm c ε = (m c ε)'`
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ → ℝ → ℝ,
      ∀ c ε s, m c ε s = c + (s - c) * Real.smoothTransition ((s - c) / ε) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨dm, hdm⟩ : ∃ dm : ℝ → ℝ → ℝ → ℝ, ∀ c ε s, dm c ε s = Real.smoothTransition ((s - c) / ε) +
      (s - c) / ε * deriv Real.smoothTransition ((s - c) / ε) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hm_deriv : ∀ c ε s, ε ≠ 0 → HasDerivAt (m c ε) (dm c ε s) s := by
    intro c ε s hε
    rw [show m c ε = fun t => c + (t - c) * Real.smoothTransition ((t - c) / ε) from
      funext (hm c ε), hdm]
    have h1 : HasDerivAt (fun t : ℝ => t - c) 1 s := (hasDerivAt_id s).sub_const c
    have h3 := (hτd ((s - c) / ε)).comp s (h1.div_const ε)
    refine ((h1.mul h3).const_add c).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
  have hm_cd : ∀ c ε, ContDiff ℝ 1 (m c ε) := by
    intro c ε
    rw [show m c ε = fun t => c + (t - c) * Real.smoothTransition ((t - c) / ε) from
      funext (hm c ε)]
    exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
      (hτc.comp ((contDiff_id.sub contDiff_const).div_const ε)))
  have hm_lo : ∀ c ε s, 0 < ε → s ≤ c → m c ε s = c ∧ dm c ε s = 0 := by
    intro c ε s hε hs
    have hu : (s - c) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    refine ⟨by rw [hm, Real.smoothTransition.zero_of_nonpos hu, mul_zero, add_zero], ?_⟩
    rw [hdm, Real.smoothTransition.zero_of_nonpos hu, zero_add]
    rcases hu.lt_or_eq with hu' | hu'
    · rw [hτ0 _ hu', mul_zero]
    · rw [hu', zero_mul]
  have hm_hi : ∀ c ε s, 0 < ε → c + ε < s → m c ε s = s ∧ dm c ε s = 1 := by
    intro c ε s hε hs
    have hu : 1 < (s - c) / ε := (one_lt_div hε).mpr (by linarith)
    refine ⟨by rw [hm, Real.smoothTransition.one_of_one_le hu.le, mul_one]; ring, ?_⟩
    rw [hdm, Real.smoothTransition.one_of_one_le hu.le, hτ1 _ hu, mul_zero, add_zero]
  have hm_ge : ∀ c ε s, 0 < ε → c ≤ m c ε s := by
    intro c ε s hε
    rw [hm]
    rcases le_or_gt s c with hs | hs
    · rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le), mul_zero, add_zero]
    · have := Real.smoothTransition.nonneg ((s - c) / ε)
      nlinarith
  have hdm_le : ∀ c ε s, |dm c ε s| ≤ 1 + Cτ := by
    intro c ε s
    rw [hdm]
    rcases lt_or_ge ((s - c) / ε) 0 with hu | hu
    · rw [Real.smoothTransition.zero_of_nonpos hu.le, hτ0 _ hu, mul_zero, add_zero, abs_zero]
      linarith
    rcases le_or_gt ((s - c) / ε) 1 with hu1 | hu1
    · have h1 := hCτ _ ⟨hu, hu1⟩
      rw [Real.norm_eq_abs] at h1
      calc |Real.smoothTransition ((s - c) / ε) +
            (s - c) / ε * deriv Real.smoothTransition ((s - c) / ε)|
          ≤ |Real.smoothTransition ((s - c) / ε)| +
            |(s - c) / ε * deriv Real.smoothTransition ((s - c) / ε)| := abs_add_le _ _
        _ ≤ 1 + 1 * Cτ := by
          gcongr
          · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
            exact Real.smoothTransition.le_one _
          · rw [abs_mul, abs_of_nonneg hu]
            exact mul_le_mul hu1 h1 (abs_nonneg _) zero_le_one
        _ = 1 + Cτ := by ring
    · rw [Real.smoothTransition.one_of_one_le hu1.le, hτ1 _ hu1, mul_zero, add_zero, abs_one]
      linarith
  -- the profile `F(u) = u^{-n/2}`, so that `F(|x - z|²) = |x - z|⁻ⁿ`, and its derivative
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ u, F u = u ^ (-(n : ℝ) / 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → ℝ, ∀ u, F' u = -(n : ℝ) / 2 * u ^ (-(n : ℝ) / 2 - 1) :=
    ⟨_, fun _ => rfl⟩
  have hF_deriv : ∀ u, 0 < u → HasDerivAt F (F' u) u := by
    intro u hu
    rw [show F = fun u => u ^ (-(n : ℝ) / 2) from funext hF, hF']
    exact Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hF_cd : ∀ u, 0 < u → ContDiffAt ℝ 1 F u := by
    intro u hu
    rw [show F = fun u => u ^ (-(n : ℝ) / 2) from funext hF]
    exact Real.contDiffAt_rpow_const_of_ne hu.ne'
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hρ2 : σ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hσ.le hσρ 2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hF_le : ∀ u, σ ^ 2 ≤ u → |F u| ≤ F (σ ^ 2) := by
    intro u hu
    rw [hF, hF, abs_of_pos (Real.rpow_pos_of_pos (hσ2.trans_le hu) _)]
    exact Real.rpow_le_rpow_of_nonpos hσ2 hu (by linarith)
  have hF'_le : ∀ u, σ ^ 2 ≤ u → |F' u| ≤ (n : ℝ) / 2 * (σ ^ 2) ^ (-(n : ℝ) / 2 - 1) := by
    intro u hu
    rw [hF', abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hσ2.trans_le hu) _),
      abs_of_nonpos (by linarith : -(n : ℝ) / 2 ≤ 0), show -(-(n : ℝ) / 2) = (n : ℝ) / 2 by ring]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hσ2 hu (by linarith))
      (by positivity)
  have hFsq : ∀ t : ℝ, 0 < t → F (t ^ 2) = (t ^ n)⁻¹ := by
    intro t ht
    rw [hF, show t ^ 2 = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul ht.le,
      show (2 : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) by ring, Real.rpow_neg ht.le, Real.rpow_natCast]
  have hF'sq : ∀ t : ℝ, 0 < t → F' (t ^ 2) = -(n : ℝ) / 2 * (t ^ (n + 2))⁻¹ := by
    intro t ht
    rw [hF', show t ^ 2 = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul ht.le,
      show (2 : ℝ) * (-(n : ℝ) / 2 - 1) = -((n + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_natCast]
  -- the test profiles `η ε ≈ max(·, σ²)^{-n/2} - max(·, ρ²)^{-n/2}` and their derivatives
  obtain ⟨η, hη⟩ : ∃ η : ℝ → ℝ → ℝ, ∀ ε s, η ε s = F (m (σ ^ 2) ε s) - F (m (ρ ^ 2) ε s) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨dη, hdη⟩ : ∃ dη : ℝ → ℝ → ℝ, ∀ ε s, dη ε s =
      F' (m (σ ^ 2) ε s) * dm (σ ^ 2) ε s - F' (m (ρ ^ 2) ε s) * dm (ρ ^ 2) ε s :=
    ⟨_, fun _ _ => rfl⟩
  have hmpos : ∀ c ε s, 0 < ε → σ ^ 2 ≤ c → 0 < m c ε s :=
    fun c ε s hε hc => hσ2.trans_le (hc.trans (hm_ge c ε s hε))
  have hη_deriv : ∀ ε s, 0 < ε → HasDerivAt (η ε) (dη ε s) s := by
    intro ε s hε
    rw [show η ε = fun s => F (m (σ ^ 2) ε s) - F (m (ρ ^ 2) ε s) from funext (hη ε), hdη]
    exact ((hF_deriv _ (hmpos _ ε s hε le_rfl)).comp s (hm_deriv _ ε s hε.ne')).sub
      ((hF_deriv _ (hmpos _ ε s hε hρ2)).comp s (hm_deriv _ ε s hε.ne'))
  have hη_cd : ∀ ε, 0 < ε → ContDiff ℝ 1 (η ε) := by
    intro ε hε
    rw [show η ε = fun s => F (m (σ ^ 2) ε s) - F (m (ρ ^ 2) ε s) from funext (hη ε)]
    refine contDiff_iff_contDiffAt.2 fun s => ?_
    exact ((hF_cd _ (hmpos _ ε s hε le_rfl)).comp s (hm_cd _ ε).contDiffAt).sub
      ((hF_cd _ (hmpos _ ε s hε hρ2)).comp s (hm_cd _ ε).contDiffAt)
  have hη_cut : ∀ ε s, 0 < ε → ε ≤ 1 → (ρ + 1) ^ 2 ≤ s → η ε s = 0 ∧ dη ε s = 0 := by
    intro ε s hε hε1 hs
    have hs' : ρ ^ 2 + ε < s := by nlinarith
    obtain ⟨h1, h2⟩ := hm_hi (σ ^ 2) ε s hε (by linarith)
    obtain ⟨h3, h4⟩ := hm_hi (ρ ^ 2) ε s hε hs'
    rw [hη, hdη, h1, h2, h3, h4]
    constructor <;> ring
  -- the widths `εₖ = 1/(k + 1)` and the divergences `Gₖ` of the corresponding radial fields
  have hεpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hεle : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Euclid P → ℝ, ∀ k x, G k x =
      (n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) + 2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) *
        ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  have hG0 : ∀ k, ∫ x, G k x ∂R.measure = 0 := by
    intro k
    have h := hrad (η (1 / ((k : ℝ) + 1))) (hη_cd _ (hεpos k)) (ρ + 1)
      (fun s hs => (hη_cut _ s (hεpos k) (hεle k) hs).1)
    have hder : ∀ s, deriv (η (1 / ((k : ℝ) + 1))) s = dη (1 / ((k : ℝ) + 1)) s :=
      fun s => (hη_deriv _ s (hεpos k)).deriv
    simp only [hder] at h
    simpa only [hG] using h
  -- the defect `Ψ = |D^⊥r|²/rⁿ` and the pointwise limit `L` of the `Gₖ`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Euclid P → ℝ, ∀ x, Ψ x =
      ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
        ‖x - z‖ ^ (n + 2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Euclid P → ℝ, ∀ x, L x =
      (n : ℝ) * ((closedBall z σ).indicator (fun _ => (σ ^ n)⁻¹) x -
        (closedBall z ρ).indicator (fun _ => (ρ ^ n)⁻¹) x +
          (closedBall z ρ \ closedBall z σ).indicator Ψ x) :=
    ⟨_, fun _ => rfl⟩
  have hεmono : ∀ k k0 : ℕ, k0 ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) := fun k k0 hk =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
  have hlim : ∀ x, Tendsto (fun k : ℕ => G k x) atTop (𝓝 (L x)) := by
    intro x
    by_cases hxσ : x ∈ closedBall z σ
    · -- inside `B_σ(z)` every `Gₖ(x)` is `n(σ⁻ⁿ - ρ⁻ⁿ)`
      have hs : ‖x - z‖ ^ 2 ≤ σ ^ 2 := by
        rw [mem_closedBall, dist_eq_norm] at hxσ
        exact pow_le_pow_left₀ (norm_nonneg _) hxσ 2
      refine tendsto_atTop_of_eventually_const (i₀ := 0) fun k _ => ?_
      obtain ⟨h1, h2⟩ := hm_lo (σ ^ 2) _ _ (hεpos k) hs
      obtain ⟨h3, h4⟩ := hm_lo (ρ ^ 2) _ _ (hεpos k) (hs.trans hρ2)
      rw [hG, hL, hη, hdη, h1, h2, h3, h4, indicator_of_mem hxσ,
        indicator_of_mem (closedBall_subset_closedBall hσρ hxσ),
        indicator_of_notMem (fun h => h.2 hxσ), hFsq σ hσ, hFsq ρ hρ]
      ring
    have hxσ' : σ < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hxσ
    have hr : 0 < ‖x - z‖ := hσ.trans hxσ'
    have hs1 : σ ^ 2 < ‖x - z‖ ^ 2 := pow_lt_pow_left₀ hxσ' hσ.le two_ne_zero
    by_cases hxρ : x ∈ closedBall z ρ
    · -- on the annulus, eventually `Gₖ(x) = n(|x - z|⁻ⁿ - ρ⁻ⁿ) - n|p_x(x - z)|²/|x - z|ⁿ⁺²`
      have hs2 : ‖x - z‖ ^ 2 ≤ ρ ^ 2 := by
        rw [mem_closedBall, dist_eq_norm] at hxρ
        exact pow_le_pow_left₀ (norm_nonneg _) hxρ 2
      obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (sub_pos.mpr hs1)
      refine tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_
      have hεk := hεmono k k0 hk
      obtain ⟨h1, h2⟩ := hm_hi (σ ^ 2) _ (‖x - z‖ ^ 2) (hεpos k) (by linarith)
      obtain ⟨h3, h4⟩ := hm_lo (ρ ^ 2) _ _ (hεpos k) hs2
      rw [hG, hL, hη, hdη, h1, h2, h3, h4, indicator_of_notMem hxσ, indicator_of_mem hxρ,
        indicator_of_mem (show x ∈ closedBall z ρ \ closedBall z σ from ⟨hxρ, hxσ⟩), hΨ, hpyth,
        hFsq _ hr, hFsq ρ hρ, hF'sq _ hr]
      field_simp
      ring
    · -- outside `B_ρ(z)`, eventually `Gₖ(x) = 0`
      have hxρ' : ρ < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hxρ
      have hs2 : ρ ^ 2 < ‖x - z‖ ^ 2 := pow_lt_pow_left₀ hxρ' hρ.le two_ne_zero
      obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (sub_pos.mpr hs2)
      refine tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_
      have hεk := hεmono k k0 hk
      obtain ⟨h1, h2⟩ := hm_hi (σ ^ 2) _ (‖x - z‖ ^ 2) (hεpos k) (by linarith)
      obtain ⟨h3, h4⟩ := hm_hi (ρ ^ 2) _ (‖x - z‖ ^ 2) (hεpos k) (by linarith)
      rw [hG, hL, hη, hdη, h1, h2, h3, h4, indicator_of_notMem hxσ, indicator_of_notMem hxρ,
        indicator_of_notMem (fun h => hxρ h.1)]
      ring
  -- uniform domination of the `Gₖ` on `B_{ρ+1}(z)`
  have hGbound : ∀ k x, ‖G k x‖ ≤ (closedBall z (ρ + 1)).indicator (fun _ =>
      (n : ℝ) * (2 * F (σ ^ 2)) +
        2 * (2 * ((n : ℝ) / 2 * (σ ^ 2) ^ (-(n : ℝ) / 2 - 1) * (1 + Cτ))) * (ρ + 1) ^ 2) x := by
    intro k x
    have hε := hεpos k
    by_cases hx : x ∈ closedBall z (ρ + 1)
    · rw [indicator_of_mem hx, hG, Real.norm_eq_abs]
      have hxr : ‖x - z‖ ≤ ρ + 1 := by rwa [mem_closedBall, dist_eq_norm] at hx
      have hηb : |η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| ≤ 2 * F (σ ^ 2) := by
        rw [hη]
        refine (abs_sub _ _).trans ?_
        linarith [hF_le _ (hm_ge (σ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε),
          hF_le _ (hρ2.trans (hm_ge (ρ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε))]
      have hdηb : |dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| ≤
          2 * ((n : ℝ) / 2 * (σ ^ 2) ^ (-(n : ℝ) / 2 - 1) * (1 + Cτ)) := by
        rw [hdη]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 := hF'_le _ (hm_ge (σ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε)
        have h2 := hF'_le _ (hρ2.trans (hm_ge (ρ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε))
        have h3 := hdm_le (σ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)
        have h4 := hdm_le (ρ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)
        have h5 := mul_le_mul h1 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
        have h6 := mul_le_mul h2 h4 (abs_nonneg _) (le_trans (abs_nonneg _) h2)
        linarith
      have hpvb : ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 ≤ (ρ + 1) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _)
          (((approxTangentPlane n R.carrier x).norm_starProjection_apply_le (x - z)).trans hxr) 2
      calc |(n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) +
            2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) *
              ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2|
          ≤ (n : ℝ) * |η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| +
            2 * |dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| *
              ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hn0, abs_two,
              abs_of_nonneg (by positivity :
                (0 : ℝ) ≤ ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2)]
        _ ≤ _ := by gcongr
    · rw [indicator_of_notMem hx, hG, norm_le_zero_iff]
      have hxr : ρ + 1 < ‖x - z‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
      obtain ⟨h1, h2⟩ := hη_cut _ _ hε (hεle k)
        (pow_le_pow_left₀ (by linarith) hxr.le 2)
      rw [h1, h2]
      ring
  -- measurability of the `Gₖ` and of `Ψ`
  have hGmeas : ∀ k, AEStronglyMeasurable (G k) R.measure := by
    intro k
    have hε := hεpos k
    have hdη_cont : Continuous (dη (1 / ((k : ℝ) + 1))) := by
      rw [show dη (1 / ((k : ℝ) + 1)) = deriv (η (1 / ((k : ℝ) + 1))) from
        funext fun s => ((hη_deriv _ s hε).deriv).symm]
      exact (hη_cd _ hε).continuous_deriv le_rfl
    have hc1 : Continuous fun x : Euclid P => (n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) :=
      continuous_const.mul ((hη_cd _ hε).continuous.comp (by fun_prop))
    have hc2 : Continuous fun x : Euclid P => 2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) :=
      continuous_const.mul (hdη_cont.comp (by fun_prop))
    rw [show G k = fun x => (n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) +
        2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) *
          ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 from funext (hG k)]
    exact (hc1.aemeasurable.add (hc2.aemeasurable.mul hpv)).aestronglyMeasurable
  have hΨmeas : AEMeasurable Ψ R.measure := by
    rw [show Ψ = fun x =>
        ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
          ‖x - z‖ ^ (n + 2) from funext hΨ]
    have h1 : AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection (x - z))
        R.measure :=
      ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
        (hp.prodMk (measurable_id.sub_const z).aemeasurable)
    exact (((measurable_id.sub_const z).aemeasurable.sub h1).norm.pow_const 2).div
      ((measurable_id.sub_const z).norm.pow_const _).aemeasurable
  have hΨnn : ∀ x, 0 ≤ Ψ x := fun x => by
    rw [hΨ]
    positivity
  -- `Ψ ≤ σ⁻ⁿ` on the annulus, so `Ψ` is integrable there
  have hann : MeasurableSet (closedBall z ρ \ closedBall z σ) :=
    measurableSet_closedBall.diff measurableSet_closedBall
  have hΨint : IntegrableOn Ψ (closedBall z ρ \ closedBall z σ) R.measure := by
    refine Measure.integrableOn_of_bounded (M := (σ ^ n)⁻¹)
      ((measure_mono sdiff_subset).trans_lt (isCompact_closedBall z ρ).measure_lt_top).ne
      hΨmeas.aestronglyMeasurable (ae_restrict_of_forall_mem hann fun x hx => ?_)
    have hxσ' : σ < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx.2
    have hr : 0 < ‖x - z‖ := hσ.trans hxσ'
    rw [Real.norm_eq_abs, abs_of_nonneg (hΨnn x), hΨ, hpyth, div_le_iff₀ (by positivity),
      pow_add, ← mul_assoc, inv_mul_eq_div]
    have h1 : 1 ≤ ‖x - z‖ ^ n / σ ^ n := by
      rw [one_le_div (by positivity)]
      exact pow_le_pow_left₀ hσ.le hxσ'.le n
    nlinarith [sq_nonneg ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖,
      sq_nonneg ‖x - z‖]
  -- dominated convergence: `∫ L dμ = lim ∫ Gₖ dμ = 0`
  have hL0 : ∫ x, L x ∂R.measure = 0 := by
    have hconv := tendsto_integral_of_dominated_convergence _ hGmeas
      ((integrableOn_const (isCompact_closedBall z (ρ + 1)).measure_lt_top.ne).integrable_indicator
        measurableSet_closedBall)
      (fun k => Eventually.of_forall (hGbound k)) (Eventually.of_forall hlim)
    simp only [hG0] at hconv
    exact tendsto_nhds_unique hconv tendsto_const_nhds
  -- `∫ L dμ = n (σ⁻ⁿ μ(B_σ) - ρ⁻ⁿ μ(B_ρ) + ∫_{B_ρ \ B_σ} Ψ dμ)`
  have hint_σ : Integrable ((closedBall z σ).indicator fun _ : Euclid P => (σ ^ n)⁻¹) R.measure :=
    (integrableOn_const (isCompact_closedBall z σ).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hint_ρ : Integrable ((closedBall z ρ).indicator fun _ : Euclid P => (ρ ^ n)⁻¹) R.measure :=
    (integrableOn_const (isCompact_closedBall z ρ).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hLexp : ∫ x, L x ∂R.measure = (n : ℝ) * (R.measure.real (closedBall z σ) * (σ ^ n)⁻¹ -
      R.measure.real (closedBall z ρ) * (ρ ^ n)⁻¹ +
        ∫ x in closedBall z ρ \ closedBall z σ, Ψ x ∂R.measure) := by
    have hdiff : Integrable (fun x => (closedBall z σ).indicator (fun _ => (σ ^ n)⁻¹) x -
        (closedBall z ρ).indicator (fun _ => (ρ ^ n)⁻¹) x) R.measure := hint_σ.sub hint_ρ
    rw [show L = fun x => (n : ℝ) * ((closedBall z σ).indicator (fun _ => (σ ^ n)⁻¹) x -
        (closedBall z ρ).indicator (fun _ => (ρ ^ n)⁻¹) x +
          (closedBall z ρ \ closedBall z σ).indicator Ψ x) from funext hL,
      integral_const_mul, integral_add hdiff (hΨint.integrable_indicator hann),
      integral_sub hint_σ hint_ρ, integral_indicator_const _ measurableSet_closedBall,
      integral_indicator_const _ measurableSet_closedBall, integral_indicator hann, smul_eq_mul,
      smul_eq_mul]
  -- the real form of Simon 4.3.6
  have hreal : R.measure.real (closedBall z σ) * (σ ^ n)⁻¹ -
      R.measure.real (closedBall z ρ) * (ρ ^ n)⁻¹ +
        ∫ x in closedBall z ρ \ closedBall z σ, Ψ x ∂R.measure = 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: a.e. `TₓM = 0`, so `Ψ = 1` on the annulus
      have hΨ1 : ∀ᵐ x ∂(R.measure.restrict (closedBall z ρ \ closedBall z σ)), Ψ x = 1 := by
        rw [ae_restrict_iff' hann]
        filter_upwards [hrank] with x hx hxA
        have hxσ' : σ < ‖x - z‖ := by
          simpa only [mem_closedBall, dist_eq_norm, not_le] using hxA.2
        have hbot : approxTangentPlane n R.carrier x = ⊥ :=
          Submodule.finrank_eq_zero.mp (hx.trans hn)
        rw [hΨ, hbot, Submodule.starProjection_bot, zero_apply, sub_zero, hn, zero_add,
          div_self (pow_pos (hσ.trans hxσ') 2).ne']
      have h1 : (σ ^ n)⁻¹ = 1 := by rw [hn, pow_zero, inv_one]
      have h2 : (ρ ^ n)⁻¹ = 1 := by rw [hn, pow_zero, inv_one]
      rw [integral_congr_ae hΨ1, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_sdiff (closedBall_subset_closedBall hσρ) measurableSet_closedBall
          (isCompact_closedBall z ρ).measure_lt_top.ne, h1, h2]
      ring
    · have h := hLexp ▸ hL0
      exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn.ne')
  -- back to `[0, ∞]`
  have hlint : ∫⁻ x in closedBall z ρ \ closedBall z σ, ENNReal.ofReal
      (‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
        ‖x - z‖ ^ (n + 2)) ∂R.measure =
      ENNReal.ofReal (∫ x in closedBall z ρ \ closedBall z σ, Ψ x ∂R.measure) := by
    rw [ofReal_integral_eq_lintegral_ofReal hΨint (Eventually.of_forall hΨnn)]
    simp only [hΨ]
  have hball : ∀ t : ℝ, 0 < t → R.measure (closedBall z t) / ENNReal.ofReal (t ^ n) =
      ENNReal.ofReal (R.measure.real (closedBall z t) * (t ^ n)⁻¹) := by
    intro t ht
    rw [← div_eq_mul_inv, ENNReal.ofReal_div_of_pos (pow_pos ht n), measureReal_def,
      ENNReal.ofReal_toReal (isCompact_closedBall z t).measure_lt_top.ne]
  rw [hlint, hball σ hσ, hball ρ hρ, ← ENNReal.ofReal_add
    (mul_nonneg measureReal_nonneg (inv_nonneg.mpr (pow_nonneg hσ.le n)))
    (integral_nonneg hΨnn)]
  congr 1
  linarith
/-- **Closed-ball masses at points of the spine** (step 1 of the parent proof: the scaling
`(ωₙρⁿ)⁻¹μ_C(B_ρ(0)) = Θⁿ(T, x)` for each `ρ > 0` in Simon's proof of 7.3.1, moved to centres `z`
in the subspace `L` of Lemma 7.3.5).  Let `μ` be invariant under translations by vectors of `L`
and satisfy `μ(λA) = λⁿμ(A)` for `λ > 0`, both on Borel sets.  Then `μ(B̄_ρ(z)) = ρⁿμ(B̄_1(z))`
for `z ∈ L` and `ρ > 0`.  Translation by `-z ∈ L` maps `B̄_r(z)` onto `B̄_r(0)`, and
`B̄_ρ(0) = ρB̄_1(0)`. -/
theorem Submission.dimred_cs_st_closedBall_measure_scaling : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (L : Submodule ℝ (Euclid P)), (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => y + x) ⁻¹' A) = μ A) → (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * μ A) → ∀ z ∈ L, ∀ ρ : ℝ, 0 < ρ → μ (closedBall z ρ) = ENNReal.ofReal (ρ ^ n) * μ (closedBall z 1) := by
  intro P n μ L htrans hhom z hz ρ hρ
  -- translation by `-z ∈ L`: `B̄_r(z) = (x ↦ -z + x)⁻¹' B̄_r(0)`
  have htr : ∀ r : ℝ, μ (closedBall z r) = μ (closedBall 0 r) := by
    intro r
    rw [← htrans (-z) (L.neg_mem hz) (closedBall 0 r) measurableSet_closedBall]
    congr 1
    ext x
    simp only [mem_closedBall, mem_preimage, dist_eq_norm, sub_zero, neg_add_eq_sub]
  -- dilation by `ρ`: `B̄_ρ(0) = (x ↦ ρ • x) '' B̄_1(0)`
  have hsc : (fun x => ρ • x) '' closedBall (0 : Euclid P) 1 = closedBall 0 ρ := by
    rw [Set.image_smul, smul_unitClosedBall_of_nonneg hρ.le]
  rw [htr ρ, htr 1, ← hsc, hhom ρ hρ _ measurableSet_closedBall]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
