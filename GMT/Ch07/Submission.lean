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

/-- **Simon 6.5.1** (proof, (31): `Lⁿ` of the interior of a unit face is `1`): the open unit cube
`{y : 0 < yᵢ < 1}` of `ℝᵏ` has volume `1`.  It is the preimage of the box `∏ᵢ (0, 1)` under the
volume-preserving `ofLp : ℝᵏ → (Fin k → ℝ)`, and the box has volume `∏ᵢ (1 - 0) = 1` (the empty
product if `k = 0`). -/
theorem Submission.cmcdtfrfg_cube_volume : ∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro k
  -- the box `∏ᵢ (0, 1)` in `Fin k → ℝ`
  have hB : MeasurableSet (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- the cube is `ofLp⁻¹` of the box
  have hpre : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hB.nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp
/-- **Coordinates of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face of the
cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P`, `b ∈ ℤᴾ`, `y ∈ ℝᵏ` and
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)}`: coordinates are additive and linear and `(eᵢ)ₗ = [l = i]`, so
`Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`.  At `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`,
giving `b_{ι(m)} + yₘ`; for `l` outside the range of `ι` every summand vanishes, giving `bₗ`. -/
theorem Submission.cmcdtfrfg_face_coord : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ) (y : Euclid k), Function.Injective ι → (∀ m, (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (ι m) = (b (ι m) : ℝ) + y m) ∧ (∀ l, (∀ m, ι m ≠ l) → (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l = (b l : ℝ)) := by
  intro P k ι b y hι
  -- steps 1-2: `Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`
  have hcoord : ∀ l : Fin P, (WithLp.toLp 2 (fun i => (b i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l =
      (b l : ℝ) + ∑ j, if ι j = l then y j else 0 := by
    intro l
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact if_congr eq_comm rfl rfl
  refine ⟨fun m => ?_, fun l hl => ?_⟩
  -- step 3: at `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`
  · rw [hcoord, Fintype.sum_eq_single m fun j hj => ite_eq_right (hι.ne hj), ite_eq_left rfl]
  -- step 4: for `l` outside the range of `ι` every summand vanishes
  · rw [hcoord, Finset.sum_eq_zero fun j _ => ite_eq_right (hl j), add_zero]

/-- **Isometry and diameter of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face
of the cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P` and `b ∈ ℤᴾ`, the
map `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` is an isometry `ℝᵏ → ℝᴾ`: by `face_coord` the coordinate gap of
`Φ(y)` and `Φ(y')` is `yₘ - y'ₘ` at `ι(m)` and `0` off the range of `ι`, so reindexing the sum of
squared gaps along `ι` gives `|Φ(y) - Φ(y')| = |y - y'|`.  On the closed unit cube every squared gap
is at most `1`, so `|y - y'| ≤ √k ≤ √P`, as `k ≤ P` by injectivity of `ι`. -/
theorem Submission.cmcdtfrfg_face_isometry_diam : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ), Function.Injective ι → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) ≤ Real.sqrt P) := by
  intro P k ι b hι
  -- (a), steps 1-5: `|Φ(y) - Φ(y')|² = Σₗ |Φ(y)ₗ - Φ(y')ₗ|² = Σₘ |yₘ - y'ₘ|² = |y - y'|²`
  have hiso : ∀ y y' : Euclid k,
      dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))
        (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) =
      dist y y' := by
    intro y y'
    -- step 2: the coordinates of `Φ(y)` and `Φ(y')`
    obtain ⟨hy, hyc⟩ := Submission.cmcdtfrfg_face_coord P k ι b y hι
    obtain ⟨hy', hy'c⟩ := Submission.cmcdtfrfg_face_coord P k ι b y' hι
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    -- steps 3-4: reindex the sum of squared gaps along the injective `ι`
    symm
    refine Fintype.sum_of_injective ι hι _ _ (fun l hl => ?_) fun m => ?_
    -- off the range of `ι` the gap is `bₗ - bₗ = 0`
    · have hl' : ∀ m, ι m ≠ l := fun m hm => hl ⟨m, hm⟩
      rw [hyc l hl', hy'c l hl', dist_self, sq, mul_zero]
    -- at `ι(m)` the gap is `(b_{ι(m)} + yₘ) - (b_{ι(m)} + y'ₘ) = yₘ - y'ₘ`
    · rw [hy m, hy' m, dist_add_left]
  refine ⟨hiso, fun y y' hy hy' => ?_⟩
  -- (b), step 6: on the unit cube `-1 ≤ yₘ - y'ₘ ≤ 1`, so every squared gap is at most `1`
  have hgap : ∀ m, dist (y m) (y' m) ^ 2 ≤ 1 := by
    intro m
    obtain ⟨hy₀, hy₁⟩ := hy m
    obtain ⟨hy'₀, hy'₁⟩ := hy' m
    rw [Real.dist_eq, sq_abs, sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  -- step 7: `k = #(Fin k) ≤ #(Fin P) = P`, as `ι` is injective
  have hkP : k ≤ P := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ι hι
  -- step 8: `|Φ(y) - Φ(y')| = |y - y'| = √(Σₘ |yₘ - y'ₘ|²) ≤ √k ≤ √P`
  rw [hiso, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ m, dist (y m) (y' m) ^ 2 ≤ ∑ _m : Fin k, (1 : ℝ) := Finset.sum_le_sum fun m _ => hgap m
    _ = k := by simp
    _ ≤ P := by exact_mod_cast hkP
/-- **Separation of distinct unit lattice faces** (Simon Ch. 6, §5, chapter-06.txt lines 1841–1918:
the faces `F ∈ 𝓛ₖ` and their interiors `F̆`).  For `p = (ι, b) ≠ q = (ι', b')` with `ι, ι'`
strictly increasing, `x = Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` with `y ∈ (0,1)ᵏ` and `z = Φ_q(y')` with
`y' ∈ [0,1]ᵏ`, either `1 ≤ |x − z|` or `min(yⱼ, 1 − yⱼ) ≤ |x − z|` for some `j`.  If some
`z_{ι(j)}` lies outside `(b_{ι(j)}, b_{ι(j)} + 1) ∋ x_{ι(j)} = b_{ι(j)} + yⱼ`, the coordinate `ι(j)`
gives the second alternative.  Otherwise no `z_{ι(j)}` is an integer, so `range ι ⊆ range ι'` and
`ι = ι'` (both enumerate the same `k`-element set increasingly), `b = b'` on `range ι`, and a
coordinate `l ∉ range ι` with `b_l ≠ b'_l` gives `|x_l − z_l| = |b_l − b'_l| ≥ 1`.  The coordinates
of `x` and `z` are `cmcdtfrfg_face_coord`. -/
theorem Submission.cmcdtfrfg_face_separation : ∀ (P k : ℕ) (p q : (Fin k → Fin P) × (Fin P → ℤ)), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) := by
  intro P k p q hp hq hpq y y' hy hy'
  -- step 1: the coordinates of `x = Φ_p(y)` and `z = Φ_q(y')`
  obtain ⟨hx₁, hx₂⟩ := Submission.cmcdtfrfg_face_coord P k p.1 p.2 y hp.injective
  obtain ⟨hz₁, hz₂⟩ := Submission.cmcdtfrfg_face_coord P k q.1 q.2 y' hq.injective
  set x := WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  set z := WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)
  -- step 2: `|x_l − z_l| ≤ |x − z|`
  have hcoord : ∀ l, |x l - z l| ≤ dist x z := fun l => by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x z l
  by_cases hA : ∃ j, ¬((p.2 (p.1 j) : ℝ) < z (p.1 j) ∧ z (p.1 j) < p.2 (p.1 j) + 1)
  · -- step 3 (Case A): `z_{ι(j)} ∉ (b_{ι(j)}, b_{ι(j)} + 1)` while `x_{ι(j)} = b_{ι(j)} + y_j`
    obtain ⟨j, hj⟩ := hA
    obtain ⟨hy₀, hy₁⟩ := hy j
    refine Or.inr ⟨j, le_trans ?_ (hcoord (p.1 j))⟩
    rw [hx₁ j]
    rcases not_and_or.mp hj with h | h
    · calc min (y j) (1 - y j) ≤ y j := min_le_left _ _
        _ ≤ (p.2 (p.1 j) : ℝ) + y j - z (p.1 j) := by linarith [not_lt.mp h]
        _ ≤ |(p.2 (p.1 j) : ℝ) + y j - z (p.1 j)| := le_abs_self _
    · calc min (y j) (1 - y j) ≤ 1 - y j := min_le_right _ _
        _ ≤ z (p.1 j) - ((p.2 (p.1 j) : ℝ) + y j) := by linarith [not_lt.mp h]
        _ ≤ |(p.2 (p.1 j) : ℝ) + y j - z (p.1 j)| := by rw [abs_sub_comm]; exact le_abs_self _
  -- step 4 (Case B): `b_{ι(j)} < z_{ι(j)} < b_{ι(j)} + 1` for every `j`
  have hB : ∀ j, (p.2 (p.1 j) : ℝ) < z (p.1 j) ∧ z (p.1 j) < p.2 (p.1 j) + 1 :=
    fun j => not_not.mp fun h => hA ⟨j, h⟩
  refine Or.inl ?_
  -- step 5: `range ι ⊆ range ι'`, since `z_l = b'_l ∈ ℤ` for `l ∉ range ι'`
  have hsub : ∀ j, ∃ m, q.1 m = p.1 j := by
    intro j
    by_contra hne
    obtain ⟨h₁, h₂⟩ := hB j
    rw [hz₂ (p.1 j) fun m hm => hne ⟨m, hm⟩] at h₁ h₂
    have h₁' : (p.2 (p.1 j) : ℝ) < q.2 (p.1 j) := h₁
    have h₂' : (q.2 (p.1 j) : ℝ) < p.2 (p.1 j) + 1 := h₂
    have : p.2 (p.1 j) < q.2 (p.1 j) := by exact_mod_cast h₁'
    have : q.2 (p.1 j) < p.2 (p.1 j) + 1 := by exact_mod_cast h₂'
    omega
  -- step 6: `ι = ι'`, both being the increasing enumeration of the `k`-element set `range ι'`
  have hι : p.1 = q.1 := by
    have hcard : (Finset.univ.image q.1).card = k := by
      rw [Finset.card_image_of_injective _ hq.injective, Finset.card_univ, Fintype.card_fin]
    refine (Finset.orderEmbOfFin_unique hcard (fun j => ?_) hp).trans
      (Finset.orderEmbOfFin_unique hcard
        (fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j)) hq).symm
    obtain ⟨m, hm⟩ := hsub j
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, hm⟩
  -- step 7: `b = b'` on `range ι`, since `b_{ι(j)} = ⌊z_{ι(j)}⌋ = b'_{ι(j)}`
  have hb : ∀ j, p.2 (p.1 j) = q.2 (p.1 j) := by
    intro j
    obtain ⟨h₁, h₂⟩ := hB j
    obtain ⟨h₃, h₄⟩ := hy' j
    have hzj := hz₁ j
    rw [← hι] at hzj
    rw [hzj] at h₁ h₂
    have h₅ : (p.2 (p.1 j) : ℝ) < q.2 (p.1 j) + 1 := by linarith
    have h₆ : (q.2 (p.1 j) : ℝ) < p.2 (p.1 j) + 1 := by linarith
    have : p.2 (p.1 j) < q.2 (p.1 j) + 1 := by exact_mod_cast h₅
    have : q.2 (p.1 j) < p.2 (p.1 j) + 1 := by exact_mod_cast h₆
    omega
  -- step 8: as `p ≠ q`, some `l ∉ range ι` has `b_l ≠ b'_l`, and there `x_l = b_l`, `z_l = b'_l`
  obtain ⟨l, hl⟩ := Function.ne_iff.mp fun h : p.2 = q.2 => hpq (Prod.ext hι h)
  have hlι : ∀ m, p.1 m ≠ l := by
    rintro m rfl
    exact hl (hb m)
  calc (1 : ℝ) ≤ |(p.2 l : ℝ) - q.2 l| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hl)
    _ = |x l - z l| := by rw [hx₂ l hlι, hz₂ l (hι ▸ hlι)]
    _ ≤ dist x z := hcoord l

/-- **Geometry of unit lattice faces** (Simon Ch. 6, §5, Lemma 2.1 and the faces `F ∈ 𝓛ₖ` of the
deformation theorem, for faces of any dimension `k`).  `(0)` `vol((0,1)ᵏ) = 1`.  For `p = (ι, b)`
with `ι` strictly increasing and `b ∈ ℤᴾ`, the face map `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` is `(a)` an
isometry `ℝᵏ → ℝᴾ` with `(b)` `dist(Φ_p y, Φ_p y') ≤ √P` on `[0,1]ᵏ`; `(c)` if `q ≠ p`,
`y ∈ (0,1)ᵏ` and `y' ∈ [0,1]ᵏ`, then `dist(Φ_p y, Φ_q y') ≥ 1` or `≥ min(yⱼ, 1 − yⱼ)` for some
`j`.  A strictly increasing `ι` is injective, so `(a)`, `(b)` are `cmcdtfrfg_face_isometry_diam`;
`(0)` is `cmcdtfrfg_cube_volume` and `(c)` is `cmcdtfrfg_face_separation`. -/
theorem Submission.cmcdtfr_face_geometry : ∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) := by
  intro P k
  refine ⟨Submission.cmcdtfrfg_cube_volume k, fun p q hp hq => ?_⟩
  -- `(a)`, `(b)` for the face map of `p`, whose strictly increasing `p.1` is injective
  obtain ⟨hiso, hdiam⟩ := Submission.cmcdtfrfg_face_isometry_diam P k p.1 p.2 hp.injective
  -- `(c)`: the open face of `p` against the closed face of `q ≠ p`
  exact ⟨hiso, hdiam, Submission.cmcdtfrfg_face_separation P k p q hp hq⟩
/-- **The `m`-skeleton of the unit cubical lattice is `H^{m+1}`-null** (Simon Ch. 6, proof of the
deformation theorem 5.1, (26)–(33): `Hⁿ(L_{n−1}) = 0`, `n = m + 1`).  The points of `ℝᴾ` with at
least `P − m` integer coordinates lie in the countably many coordinate planes
`A(s, z) = {x : xᵢ = zᵢ for i ∈ s}`, `P ≤ m + |s|`, `z ∈ ℤᴾ`.  Each `A(s, z)` is the image of the
Lipschitz map `ℝ^{Fin P \ s} → ℝᴾ`, `t ↦ (zᵢ on s, tᵢ off s)`, whose source is `μH[m + 1]`-null:
it is a union of balls of finite `μH[P − |s|]` (= Lebesgue) measure, and `P − |s| < m + 1`.
Finally `μHE[m + 1]` is a multiple of `μH[m + 1]`. -/
theorem Submission.cmcdtfr_skeleton_null : ∀ (P m : ℕ), μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
  intro P m
  -- Step 1: each coordinate plane `A(s, z)` with `P ≤ m + |s|` is `μH[m + 1]`-null
  have hplane : ∀ s : Finset (Fin P), P ≤ m + s.card → ∀ z : Fin P → ℤ,
      μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∀ i ∈ s, x i = z i} = 0 := by
    intro s hs z
    -- `A(s, z)` is the image of the Lipschitz map `g : t ↦ (zᵢ on s, tᵢ off s)`
    let g : ({i // i ∉ s} → ℝ) → Euclid P := fun t =>
      WithLp.toLp 2 fun i => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩
    have hg1 : LipschitzWith 1 fun t : {i // i ∉ s} → ℝ =>
        fun i : Fin P => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩ := by
      refine LipschitzWith.of_dist_le_mul fun t t' => ?_
      rw [NNReal.coe_one, one_mul]
      refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
      by_cases h : i ∈ s
      · simp [h]
      · simpa [h] using dist_le_pi_dist t t' ⟨i, h⟩
    have hg : LipschitzWith _ g := (PiLp.lipschitzWith_toLp 2 fun _ : Fin P => ℝ).comp hg1
    have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ g '' univ := by
      intro x hx
      refine ⟨fun j => x j.1, mem_univ _, ?_⟩
      ext i
      by_cases h : i ∈ s
      · simp [g, h, hx i h]
      · simp [g, h]
    -- the source of `g` has dimension `P − |s| ≤ m < m + 1`, so it is `μH[m + 1]`-null
    have hcard : Fintype.card {i // i ∉ s} ≤ m := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
      omega
    have huniv : (μH[((m + 1 : ℕ) : ℝ)] : Measure ({i // i ∉ s} → ℝ)) univ = 0 := by
      rw [← Metric.iUnion_ball_nat (0 : {i // i ∉ s} → ℝ)]
      refine measure_iUnion_null fun n => ?_
      refine (Measure.hausdorffMeasure_zero_or_top
        (d₁ := (Fintype.card {i // i ∉ s} : ℝ)) ?_ _).resolve_right ?_
      · exact_mod_cast Nat.lt_succ_of_le hcard
      · rw [hausdorffMeasure_pi_real]
        exact measure_ball_lt_top.ne
    refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
    calc μH[((m + 1 : ℕ) : ℝ)] (g '' univ)
        ≤ _ ^ ((m + 1 : ℕ) : ℝ) * μH[((m + 1 : ℕ) : ℝ)] (univ : Set ({i // i ∉ s} → ℝ)) :=
          hg.hausdorffMeasure_image_le (Nat.cast_nonneg _) univ
      _ = 0 := by rw [huniv, mul_zero]
  -- Step 2: the set is covered by the countably many planes `A(s, z)`, `P ≤ m + |s|`, `z ∈ ℤᴾ`
  have hcover : {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, x i = z} ⊆ ⋃ (s : {s : Finset (Fin P) // P ≤ m + s.card})
        (z : Fin P → ℤ), {x : Euclid P | ∀ i ∈ s.1, x i = z i} := by
    rintro x ⟨s, hs, hx⟩
    choose! z hz using hx
    exact mem_iUnion₂.2 ⟨⟨s, hs⟩, z, hz⟩
  -- Step 3: countable subadditivity gives `μH[m + 1]`-nullity, and `μHE[m + 1] = c • μH[m + 1]`
  have hnull : μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 :=
    measure_mono_null hcover
      (measure_iUnion_null fun s => measure_iUnion_null fun z => hplane s.1 s.2 z)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hnull, smul_zero]
/-- **Simon Ch. 3, 1.4** (the test-function argument of Remark 1.5(3)): if `A − x ⊆ V` for a
subspace `V`, then every approximate tangent space `Q` of `A` at `x` lies in `V`.  Every blow-up
`η_{x,r}(A) = r⁻¹(A − x)` lies in `V`.  At `q ∈ Q \ V`, `d = dist(q, V) > 0` (`V` is closed), and
the bump `g = max(0, d/2 − |· − q|) ∈ C_c` vanishes on `V`, so all blow-up integrals of `g` vanish
and the limit gives `∫_Q g dHⁿ = 0`.  But `Hⁿ⌞Q` is regular with support `Q ∋ q` (`dim Q = n`), and
`g ≥ 0` has support `B_{d/2}(q)`, so `∫_Q g dHⁿ > 0`. -/
theorem Submission.cmcdtfrpo_approxTangent_le_of_sub_mem : ∀ (P n : ℕ) (A : Set (Euclid P)) (x : Euclid P) (Q V : Submodule ℝ (Euclid P)), (∀ a ∈ A, a - x ∈ V) → HasApproximateTangentSpaceAt n A x Q → Q ≤ V := by
  intro P n A x Q V hAV hQ q hq
  by_contra hqV
  -- `d = dist(q, V) > 0`, as `V` is closed
  have hd : 0 < infDist q (V : Set (Euclid P)) :=
    (V.closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, V.zero_mem⟩).mp hqV
  set d := infDist q (V : Set (Euclid P))
  -- the bump `g = max(0, d/2 − dist(·, q))`: continuous, `≥ 0`, support `B_{d/2}(q)`, zero on `V`
  set g : Euclid P → ℝ := fun y => max 0 (d / 2 - dist y q)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hg_nonneg : 0 ≤ g := fun y => le_max_left _ _
  have hg_supp : support g = ball q (d / 2) := by
    ext y
    simp only [mem_support, mem_ball, g]
    constructor
    · intro h
      by_contra h'
      exact h (max_eq_left (by linarith [not_lt.mp h']))
    · intro h
      exact (lt_max_of_lt_right (by linarith : (0 : ℝ) < d / 2 - dist y q)).ne'
  have hg_cpt : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall q (d / 2)) fun y hy => ?_
    simp only [mem_closedBall, not_le] at hy
    exact max_eq_left (by linarith)
  have hgV : ∀ v ∈ V, g v = 0 := by
    intro v hv
    have h1 : d ≤ dist q v := infDist_le_dist_of_mem (SetLike.mem_coe.mpr hv)
    rw [dist_comm] at h1
    exact max_eq_left (by linarith)
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_cpt⟩
  -- every blow-up `η_{x,r}(A) = r⁻¹(A − x)` lies in `V`, so all blow-up integrals of `f` vanish
  have hzero : ∀ r : ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] = 0 := by
    intro r
    apply setIntegral_eq_zero_of_forall_eq_zero
    rintro _ ⟨a, ha, rfl⟩
    exact hgV _ (V.smul_mem r⁻¹ (hAV a ha))
  -- uniqueness of limits along `𝓝[>] 0` gives `∫_Q g dHⁿ = 0`
  have hQint : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := by
    refine tendsto_nhds_unique (hQ.2 f) ?_
    simp only [hzero]
    exact tendsto_const_nhds
  -- `Hⁿ⌞Q` is regular with support `Q ∋ q` (`dim Q = n`), so `∫_Q g dHⁿ > 0`
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
  have hint : Integrable g (μHE[n].restrict (Q : Set (Euclid P))) :=
    hg_cont.integrable_of_hasCompactSupport hg_cpt
  have hqsupp : q ∈ (μHE[n].restrict (Q : Set (Euclid P))).support := by
    rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
    exact hq
  have hball : 0 < μHE[n].restrict (Q : Set (Euclid P)) (ball q (d / 2)) :=
    (Measure.mem_support_iff_forall q).mp hqsupp _ (ball_mem_nhds q (half_pos hd))
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg_nonneg hint, hg_supp]
    exact hball
  exact hpos.ne' hQint
/-- **Orthonormal frames of one plane agree up to a global sign** (Simon Ch. 6, §1 and §3: an
`n`-plane is oriented by `±τ₁ ∧ ⋯ ∧ τₙ` for any orthonormal basis `τ` of it).  If `τ` and `e` are
orthonormal `n`-frames in `ℝᴾ` spanning the same subspace `W`, then for every `n`-covector `α`,
`α(τ) = c α(e)` with `c = det_e(τ)`, the determinant of `τ` in the basis `e` of `W`
(`AlternatingMap.eq_smul_basis_det` for `α` restricted to `W`); `c = ±1`, being the change-of-basis
determinant between two orthonormal bases of `W`. -/
theorem Submission.cmcdtfrpo_orthonormal_frame_sign : ∀ (P n : ℕ) (τ e : Fin n → Euclid P), Orthonormal ℝ τ → Orthonormal ℝ e → Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range e) → (∀ α : Covector (Euclid P) n, α τ = α e) ∨ (∀ α : Covector (Euclid P) n, α τ = -α e) := by
  intro P n τ e hτ he hspan
  -- Step 1: the basis `b` of `W = span (range e)` with `b j = e j`, so `finrank W = n`
  let W : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range e)
  have hli : LinearIndependent ℝ e := he.linearIndependent
  let b : Module.Basis (Fin n) ℝ W := Module.Basis.span hli
  have hb : ∀ j, (b j : Euclid P) = e j := Module.Basis.coe_span_apply hli
  have hfin : Module.finrank ℝ W = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  -- Step 2: `τ` as a family `τW` in `W`
  have hτW : ∀ j, τ j ∈ W := fun j => hspan.le (Submodule.subset_span (Set.mem_range_self j))
  let τW : Fin n → W := fun j => ⟨τ j, hτW j⟩
  -- Step 3: `α(τ) = det_b(τW) α(e)` for every `n`-covector `α`
  have key : ∀ α : Covector (Euclid P) n, α τ = b.det τW * α e := by
    intro α
    let αW : W [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap W.subtype
    have h := congrArg (fun f : W [⋀^Fin n]→ₗ[ℝ] ℝ => f τW) (αW.eq_smul_basis_det b)
    have hτ' : (fun j => W.subtype (τW j)) = τ := rfl
    have he' : (fun j => W.subtype (b j)) = e := funext hb
    simp only [αW, AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h
    rw [hτ', he'] at h
    rw [mul_comm]
    exact h
  -- Step 4: `det_b(τW) = ±1`, since `b` and `τW` are orthonormal bases of `W`
  have hbon : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite] at he ⊢
    intro i j
    rw [Submodule.coe_inner, hb, hb]
    exact he i j
  have hτWon : Orthonormal ℝ τW := by
    rw [orthonormal_iff_ite] at hτ ⊢
    intro i j
    rw [Submodule.coe_inner]
    exact hτ i j
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range τW) :=
    (hτWon.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, hfin])).ge
  have hc : b.det τW = 1 ∨ b.det τW = -1 := by
    have h := (b.toOrthonormalBasis hbon).det_to_matrix_orthonormalBasis_real
      (OrthonormalBasis.mk hτWon hsp)
    rwa [Module.Basis.toBasis_toOrthonormalBasis, OrthonormalBasis.coe_mk] at h
  -- Step 5: the sign `det_b(τW)` does not depend on `α`
  rcases hc with h | h
  · exact Or.inl fun α => by rw [key, h, one_mul]
  · exact Or.inr fun α => by rw [key, h, neg_one_mul]

/-- **Faces in a coordinate plane are oriented by `±e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`** (Simon Ch. 6, 5.1
(26); Ch. 3, 1.4).  If `A` lies in the coordinate plane `x + V`, `V = span{e_{ι(j)}}`, then
`A − x ⊆ V`, so every approximate tangent space `Q` of `A` at `x` satisfies `Q ≤ V`
(`cmcdtfrpo_approxTangent_le_of_sub_mem`), hence `Q = V` as both have dimension `n`.  A unit
orientation `ξ = ±τ` of `Q` then uses an orthonormal frame `τ` of `V`, and `α(τ) = ±α(e_ι)` with a
sign independent of `α` (`cmcdtfrpo_orthonormal_frame_sign`). -/
theorem Submission.cmcdtfr_plane_orientation : ∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) := by
  intro P n ι A x Q ξ hι hA hQ hξ
  -- the coordinate frame `e j = e_{ι(j)}` (orthonormal, `ι` being injective) and `V = span e`
  set e : Fin n → Euclid P := fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp ι hι.injective
  set V : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range e) with hV
  -- Step 1: `A − x ⊆ V`, since `(a − x)_i = 0` off `range ι`
  have hAV : ∀ a ∈ A, a - x ∈ V := by
    intro a ha
    rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (a - x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ∃ j, ι j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [EuclideanSpace.basisFun_apply]
      exact V.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [EuclideanSpace.basisFun_repr, PiLp.sub_apply, hA a ha i fun j hj => hi ⟨j, hj⟩,
        sub_self, zero_smul]
      exact V.zero_mem
  -- Step 2: `Q ≤ V`, hence `Q = V` as `dim Q = n = dim V`
  have hQV : Q = V := by
    refine Submodule.eq_of_le_of_finrank_eq
      (Submission.cmcdtfrpo_approxTangent_le_of_sub_mem P n A x Q V hAV hQ) ?_
    rw [hQ.1, hV, finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  -- Step 3: `ξ = ±τ` for an orthonormal frame `τ` of `Q = V`, and `α(τ) = ±α(e)`
  obtain ⟨τ, hτ, hτQ, hξτ⟩ := hξ
  rcases hξτ with h1 | h1 <;>
    rcases Submission.cmcdtfrpo_orthonormal_frame_sign P n τ e hτ he (hτQ.trans hQV) with h2 | h2
  · exact Or.inl fun α => by rw [h1, h2]
  · exact Or.inr fun α => by rw [h1, h2]
  · exact Or.inr fun α => by rw [h1, h2]
  · exact Or.inl fun α => by rw [h1, h2, neg_neg]

/-- **Points of the `(m + 1)`-skeleton off the `m`-skeleton lie in open `(m + 1)`-faces** (Simon
Ch. 6, proof of the deformation theorem 5.1: `L_n \ L_{n−1}` is the union of the interiors `F̆` of
the faces `F ∈ 𝓛_n`, `n = m + 1`).  If `x ∈ ℝᴾ` has at least `P − (m + 1)` integer coordinates but
not `P − m` of them, its set `J` of integer coordinates has exactly `P − (m + 1)` elements, so the
increasing enumeration `ι` of `Jᶜ` is defined on `Fin (m + 1)`.  With `b = ⌊x⌋` and
`yⱼ = fract(x_{ι(j)}) ∈ (0, 1)` (as `x_{ι(j)} ∉ ℤ`), the face point `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`
is `x`: its coordinate is `⌊xᵢ⌋ = xᵢ` for `i ∈ J` and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ` for `i = ι(j)`. -/
theorem Submission.cmcdtfrsd_skeleton_point_on_open_face : ∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) = x := by
  classical
  intro P m x ⟨s, hs, hsx⟩ hnot
  -- step 1: the set `J` of integer coordinates of `x`
  set J : Finset (Fin P) := Finset.univ.filter fun i => ∃ z : ℤ, x i = z
  have hJx : ∀ i ∈ J, ∃ z : ℤ, x i = z := fun i hi => (Finset.mem_filter.mp hi).2
  -- step 2: `s ⊆ J`, so `P ≤ m + 1 + |J|`
  have hsJ : s.card ≤ J.card :=
    Finset.card_le_card fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsx i hi⟩
  -- step 3: `m + |J| < P`, otherwise `J` itself would contradict the second hypothesis
  have hJP : m + J.card < P := by
    by_contra h
    exact hnot ⟨J, by omega, hJx⟩
  -- step 4: `|Jᶜ| = P − |J| = m + 1`
  have hcard : Jᶜ.card = m + 1 := by
    have h := Finset.card_add_card_compl J
    rw [Fintype.card_fin] at h
    omega
  -- step 5: `ι` enumerates `Jᶜ` increasingly
  set ι : Fin (m + 1) ↪o Fin P := Jᶜ.orderEmbOfFin hcard with hι
  have hιJ : ∀ j, ι j ∉ J := fun j => Finset.mem_compl.mp (Finset.orderEmbOfFin_mem Jᶜ hcard j)
  -- step 6: the base point `b = ⌊x⌋` and the parameters `yⱼ = fract(x_{ι(j)})`
  refine ⟨(ι, fun i => ⌊x i⌋), WithLp.toLp 2 fun j => Int.fract (x (ι j)), ι.strictMono,
    fun j => ?_, ?_⟩
  -- step 7: `0 < yⱼ < 1`, as `x_{ι(j)}` is not an integer
  · refine ⟨Int.fract_pos.mpr fun h => hιJ j ?_, Int.fract_lt_one _⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⌊x (ι j)⌋, h⟩
  -- step 8: `Φ_p(y)ᵢ = ⌊xᵢ⌋ + Σⱼ [i = ι(j)] yⱼ = xᵢ` for every `i`
  · ext i
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ J
    -- (a) `i ∈ J`: no summand survives and `⌊xᵢ⌋ = xᵢ`
    · obtain ⟨z, hz⟩ := hJx i hi
      rw [Finset.sum_eq_zero fun j _ => ite_eq_right fun h : i = ι j => hιJ j (h ▸ hi), add_zero,
        hz, Int.floor_intCast]
    -- (b) `i = ι(j₀)`: only the summand `j₀` survives and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ`
    · obtain ⟨j₀, rfl⟩ : i ∈ Set.range ι := by
        rw [hι, Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr (Finset.mem_compl.mpr hi)
      rw [Fintype.sum_eq_single j₀ fun j hj => ite_eq_right fun h => hj (ι.injective h).symm,
        ite_eq_left rfl, Int.floor_add_fract]
/-- **Only finitely many unit lattice faces meet a compact set** (Simon Ch. 6, proof of the
deformation theorem 5.1, after (33): the sum `P = Σ_{F ∈ 𝓛ₙ} β_F [[F]]` runs over the finitely many
faces meeting the compact `spt Q`).  Let `p = (ι, b)`, `ι : Fin k → Fin P` arbitrary, `b ∈ ℤᴾ`,
and `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)} ∈ K` for some `y ∈ [0,1]ᵏ`.  Then `Φ_p(y)ᵢ = bᵢ + Sᵢ` with
`Sᵢ = Σⱼ [ι(j) = i] yⱼ ∈ [0, k]`, and `|Φ_p(y)ᵢ| ≤ ‖Φ_p(y)‖ ≤ ρ` on the bounded `K`, so
`−⌈ρ⌉ − k ≤ bᵢ ≤ ⌈ρ⌉`.  Hence `p` lies in the finite set `(Fin k → Fin P) × [−N, N]ᴾ`,
`N = ⌈ρ⌉ + k`. -/
theorem Submission.cmcdtfrsd_faces_meeting_compact_finite : ∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ K}.Finite := by
  intro P k K hK
  -- step 1: `K` is bounded, `‖x‖ ≤ ρ` on `K`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  -- step 4: the set lies in `(Fin k → Fin P) × [−N, N]ᴾ`, `N = ⌈ρ⌉ + k`
  refine (Set.finite_univ.prod (Set.Finite.pi fun _ : Fin P =>
    Set.finite_Icc (-(⌈ρ⌉ + k)) (⌈ρ⌉ + k))).subset ?_
  rintro p ⟨y, hy, hx⟩
  refine ⟨Set.mem_univ p.1, Set.mem_univ_pi.mpr fun i => ?_⟩
  -- the coordinate formula `Φ(y)ᵢ = bᵢ + Sᵢ`, `Sᵢ = Σⱼ [ι(j) = i] yⱼ`
  have hcoord : (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) i =
      (p.2 i : ℝ) + ∑ j, if p.1 j = i then y j else 0 := by
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact if_congr eq_comm rfl rfl
  -- step 2: `0 ≤ Sᵢ ≤ k`
  have hS₀ : 0 ≤ ∑ j, if p.1 j = i then y j else 0 :=
    Finset.sum_nonneg fun j _ => by split_ifs; exacts [(hy j).1, le_rfl]
  have hS₁ : ∑ j, (if p.1 j = i then y j else 0) ≤ k :=
    calc ∑ j, (if p.1 j = i then y j else 0) ≤ ∑ _j : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by split_ifs; exacts [(hy j).2, zero_le_one]
      _ = k := by simp
  -- step 3: `|bᵢ + Sᵢ| = |Φ(y)ᵢ| ≤ ‖Φ(y)‖ ≤ ρ ≤ ⌈ρ⌉`, so `−⌈ρ⌉ − k ≤ bᵢ ≤ ⌈ρ⌉`
  have hxi : ‖(WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) i‖ ≤ ρ :=
    le_trans (PiLp.norm_apply_le _ i) (hρ _ hx)
  rw [hcoord, Real.norm_eq_abs, abs_le] at hxi
  have hρc := Int.le_ceil ρ
  constructor
  · have h : ((-(⌈ρ⌉ + k) : ℤ) : ℝ) ≤ p.2 i := by push_cast; linarith [hxi.1]
    exact_mod_cast h
  · have h : (p.2 i : ℝ) ≤ ((⌈ρ⌉ + k : ℤ) : ℝ) := by push_cast; linarith [hxi.2]
    exact_mod_cast h
/-- **On a Borel subset of a coordinate `n`-plane the orientation is a Borel sign times
`e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`** (Simon Ch. 6, proof of 5.1, (26)–(28): the orientation of `T` on a
face `F̆` of the cube lattice).  Assume (IMC-b), the restriction `τ(M ∩ E, θ, ξ)` of `τ(M, θ, ξ)`
to a Borel set `E` (`U` open), and (PO), `cmcdtfr_plane_orientation`.  Let `E` lie in the
coordinate plane through `c` spanned by `e_ι = (e_{ι(0)}, …, e_{ι(n-1)})`.  The restriction
orients the approximate tangent planes `Q` of `M ∩ E` by `ξ(x)` a.e., and points of `M ∩ E` agree
with `x` off `range ι`, so (PO) gives `ξ(x) = ±e` a.e. on `M ∩ E`, where `e = (α ↦ α(e_ι))`.  For
a strongly measurable version `ξ̃` of `ξ`, the sign `σ = 1` on `{ξ̃ = e}`, `-1` on
`{ξ̃ ≠ e, ξ̃ = -e}`, `0` elsewhere is Borel with `|σ| ≤ 1`, and `ξ(x)(α) = σ(x) α(e_ι)` a.e. on
`M ∩ E`. -/
theorem Submission.cmcdtfrsd_coordinate_plane_orientation_sign : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ι : Fin n → Fin P) (c : Euclid P) (E : Set (Euclid P)), IsOpen U → StrictMono ι → MeasurableSet E → (∀ a ∈ E, ∀ i, (∀ j, ι j ≠ i) → a i = c i) → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  intro hIMC hPO P n U R ι c E hU hι hE hEc
  classical
  -- Step 1: (IMC-b) restricts `R` to `M ∩ E` keeping `ξ`, and `R'.orients` orients its tangents
  obtain ⟨-, R', -, hcarr, -, horient⟩ := hIMC P n U R E hU hE
  have hor := R'.orients
  rw [hcarr, horient] at hor
  -- Step 2: points of `M ∩ E` agree with `x ∈ M ∩ E` off `range ι`, so (PO) gives `ξ(x) = ±e_ι`
  have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
  have hsign : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)),
      (∀ α : Covector (Euclid P) n,
          R.orient x α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨
        ∀ α : Covector (Euclid P) n,
          R.orient x α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    filter_upwards [hor, ae_restrict_mem hME] with x ⟨Q, hQ, hξ⟩ hx
    refine hPO P n ι (R.carrier ∩ E) x Q (R.orient x) hι (fun a ha i hi => ?_) hQ hξ
    rw [hEc a ha.2 i hi, hEc x hx.2 i hi]
  -- Step 3: a strongly measurable version `ξ̃` of `ξ`, equal to `ξ` a.e. on `M ∩ E ⊆ M`
  set ξ' := R.aestronglyMeasurable_orient.mk R.orient
  have hξ'm : StronglyMeasurable ξ' := R.aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξξ' : R.orient =ᵐ[μHE[n].restrict (R.carrier ∩ E)] ξ' :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left R.aestronglyMeasurable_orient.ae_eq_mk
  -- Step 4: the coordinate `n`-vector `e = (α ↦ α(e_ι))`
  set e : MultiVector P n :=
    ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  -- Step 5: the sign `σ`; `{ξ̃ = ±e}` are Borel, as `MultiVector P n` is metrizable (the
  -- pseudometrizability of its normed structure is not found by instance search)
  have hT0 : T0Space (MultiVector P n) := inferInstance
  have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
    let m : PseudoMetricSpace (MultiVector P n) := inferInstance
    { toPseudoMetrizableSpace := ⟨⟨m.toUniformSpace, rfl,
        @EMetric.instIsCountablyGeneratedUniformity _ m.toPseudoEMetricSpace⟩⟩
      toT0Space := hT0 }
  refine ⟨fun x => if ξ' x = e then 1 else if ξ' x = -e then -1 else 0,
    Measurable.ite (hξ'm.measurableSet_eq_fun stronglyMeasurable_const) measurable_const
      (Measurable.ite (hξ'm.measurableSet_eq_fun stronglyMeasurable_const) measurable_const
        measurable_const), fun x => ?_, ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  -- Step 6: case analysis on `ξ(x) = ±e`
  filter_upwards [hsign, hξξ'] with x hx hxx' α
  rcases hx with h | h
  · -- `ξ(x) = e`, so `ξ̃(x) = e` and `σ(x) = 1`
    have hxe : ξ' x = e := hxx' ▸ ContinuousLinearMap.ext fun β => h β
    rw [h α, ite_eq_left hxe, Int.cast_one, one_mul]
  · -- `ξ(x) = -e`, so `ξ̃(x) = -e`; `σ(x) = 1` if also `ξ̃(x) = e`, else `σ(x) = -1`
    have hxe : ξ' x = -e := hxx' ▸ ContinuousLinearMap.ext fun β => h β
    by_cases hxe' : ξ' x = e
    · rw [ite_eq_left hxe', Int.cast_one, one_mul, hxx', hxe']
      rfl
    · rw [h α, ite_eq_right hxe', ite_eq_left hxe, Int.cast_neg, Int.cast_one, neg_one_mul]

/-- **On one open lattice face an integer multiplicity current is an integer `L¹` density**
(Simon Ch. 6, proof of the deformation theorem 5.1, (33)).  Let `Φ_p(y) = b + ∑ⱼ yⱼ e_{ι(j)}` be
an isometry, `Q₁ = (0, 1)ⁿ` and `F̆ = Φ_p(Q₁)`.  `F̆` is Borel and lies in the coordinate plane
through `b`, so by `cmcdtfrsd_coordinate_plane_orientation_sign` the orientation of
`R = (M, θ, ξ)` is `ξ = σ E_p` `Hⁿ`-a.e. on `M ∩ F̆`, with `σ ∈ {-1, 0, 1}` Borel.  As `Φ_p` is an
isometry and `Hⁿ = vol` on `ℝⁿ`, `Hⁿ⌞F̆ = Φ_p # (vol⌞Q₁)`, so the integer function
`u = (1_M θ σ) ∘ Φ_p` satisfies `∫_{M ∩ F̆} θ ⟨ω, ξ⟩ dHⁿ = ∫_{Q₁} u ⟨ω ∘ Φ_p, E_p⟩` and
`∫_{Q₁} |u| ≤ ∫_{Q₁} (1_M θ) ∘ Φ_p = μ_R(F̆) < ∞` (`F̆` lies in a compact set). -/
theorem Submission.cmcdtfrsd_face_density : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} ∧ ENNReal.ofReal (∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∫ x in R.carrier ∩ (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = ∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, u y * (ω : DifferentialForm (Euclid P) n) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro hIMC hPO P n R p hι hΦ
  -- notation: `Φ = Φ_p`, `Q₁` the open unit cube of `ℝⁿ`, `F̆ = Φ(Q₁)` the open face
  set Φ : Euclid n → Euclid P := fun y => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
    ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  set Q₁ : Set (Euclid n) := {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}
  -- Step 1: `Q₁` and `F̆` are Borel (`Φ` is an isometry, hence a measurable embedding)
  have hQ₁ : MeasurableSet Q₁ := by
    have hQ : Q₁ = ⋂ i, ({y : Euclid n | 0 < y i} ∩ {y : Euclid n | y i < 1}) := by
      ext y
      simp [Q₁]
    rw [hQ]
    refine MeasurableSet.iInter fun i => ?_
    have hm : Measurable fun y : Euclid n => y i :=
      (EuclideanSpace.proj i).continuous.measurable
    exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
  have hF : MeasurableSet (Φ '' Q₁) := hemb.measurableSet_image' hQ₁
  -- Step 2: `F̆` lies in the coordinate plane through `b`
  have hplane : ∀ a ∈ Φ '' Q₁, ∀ i, (∀ j, p.1 j ≠ i) →
      a i = (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) : Euclid P) i := by
    rintro _ ⟨y, -, rfl⟩ i hi
    have hi' : ∀ j, i ≠ p.1 j := fun j h => hi j h.symm
    simp [Φ, hi']
  -- Step 3: the orientation is `σ E_p` a.e. on `M ∩ F̆`, with `σ ∈ {-1, 0, 1}` Borel
  obtain ⟨σ, hσm, hσ1, hσ⟩ := Submission.cmcdtfrsd_coordinate_plane_orientation_sign hIMC hPO
    P n univ R p.1 (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (Φ '' Q₁) isOpen_univ hι hF hplane
  -- Step 4: change of variables, `Hⁿ⌞F̆ = Φ_# (vol⌞Q₁)`
  have hrestr : μHE[n].restrict (Φ '' Q₁) = (volume.restrict Q₁).map Φ := by
    calc μHE[n].restrict (Φ '' Q₁) = (μHE[n].restrict (range Φ)).restrict (Φ '' Q₁) :=
          (Measure.restrict_restrict_of_subset (image_subset_range Φ Q₁)).symm
      _ = ((volume : Measure (Euclid n)).map Φ).restrict (Φ '' Q₁) := by
          rw [← hΦ.map_euclideanHausdorffMeasure,
            EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      _ = (volume.restrict Q₁).map Φ := by
          rw [hemb.restrict_map, hΦ.injective.preimage_image]
  have hint : ∀ f : Euclid P → ℝ, ∫ x in Φ '' Q₁, f x ∂μHE[n] = ∫ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hemb.integral_map]
  have hlint : ∀ f : Euclid P → ℝ≥0∞,
      ∫⁻ x in Φ '' Q₁, f x ∂μHE[n] = ∫⁻ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hemb.lintegral_map]
  -- Step 5: the density `u = g ∘ Φ`, `g = 1_M θ σ`, dominated by `h = 1_M θ`
  set g : Euclid P → ℝ := R.carrier.indicator fun x => (R.mult x : ℝ) * (σ x : ℝ)
  set h : Euclid P → ℝ := R.carrier.indicator fun x => (R.mult x : ℝ)
  have hgm : Measurable g :=
    (((measurable_of_countable fun k : ℕ => (k : ℝ)).comp R.measurable_mult).mul
      ((measurable_of_countable fun k : ℤ => (k : ℝ)).comp hσm)).indicator
      R.measurableSet_carrier
  have hgh : ∀ x, |g x| ≤ h x := by
    intro x
    by_cases hx : x ∈ R.carrier
    · simp only [g, h, indicator_of_mem hx, abs_mul, Nat.abs_cast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by exact_mod_cast hσ1 x)
    · simp [g, h, indicator_of_notMem hx]
  -- Step 6: `∫⁻_{Q₁} h ∘ Φ = R.measure F̆`
  have hmass : ∫⁻ y in Q₁, ENNReal.ofReal (h (Φ y)) = R.measure (Φ '' Q₁) := by
    rw [← hlint fun x => ENNReal.ofReal (h x)]
    have hh : (fun x => ENNReal.ofReal (h x)) =
        R.carrier.indicator fun x => (R.mult x : ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ R.carrier <;> simp [h, hx]
    rw [hh, lintegral_indicator R.measurableSet_carrier, IMRep.measure, withDensity_apply _ hF,
      Measure.restrict_restrict R.measurableSet_carrier, Measure.restrict_restrict hF,
      inter_comm]
  -- Step 7: `R.measure F̆ < ∞`, `F̆` lying in the compact set `Φ(toLp [0, 1]ⁿ)`
  have hfin : R.measure (Φ '' Q₁) ≠ ∞ := by
    have hK : IsCompact (Φ '' (WithLp.toLp 2 '' Icc (0 : Fin n → ℝ) 1)) :=
      (isCompact_Icc.image (PiLp.continuous_toLp 2 _)).image hΦ.continuous
    have hFK : Φ '' Q₁ ⊆ Φ '' (WithLp.toLp 2 '' Icc (0 : Fin n → ℝ) 1) := by
      refine image_mono fun y hy => ?_
      exact ⟨WithLp.ofLp y, ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩,
        WithLp.toLp_ofLp _ y⟩
    refine ne_top_of_le_ne_top ?_ (measure_mono hFK)
    rw [IMRep.measure, withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult _ hK (subset_univ _)
  -- Step 8: integrability of `u` and the mass bound
  have hle : ∀ y, ENNReal.ofReal |g (Φ y)| ≤ ENNReal.ofReal (h (Φ y)) :=
    fun y => ENNReal.ofReal_le_ofReal (hgh _)
  have hui : IntegrableOn (fun y => g (Φ y)) Q₁ := by
    refine ⟨(hgm.comp hΦ.continuous.measurable).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.2 ?_⟩
    calc ∫⁻ y in Q₁, ‖g (Φ y)‖ₑ = ∫⁻ y in Q₁, ENNReal.ofReal |g (Φ y)| := by
          simp_rw [Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ y in Q₁, ENNReal.ofReal (h (Φ y)) := lintegral_mono hle
      _ = R.measure (Φ '' Q₁) := hmass
      _ < ∞ := lt_top_iff_ne_top.2 hfin
  refine ⟨fun y => g (Φ y), fun y => ?_, hui, ?_, fun ω => ?_⟩
  · -- Step 5(b): `u` is integer valued
    by_cases hy : Φ y ∈ R.carrier
    · exact ⟨(R.mult (Φ y) : ℤ) * σ (Φ y), by simp [g, indicator_of_mem hy]⟩
    · exact ⟨0, by simp [g, indicator_of_notMem hy]⟩
  · rw [ofReal_integral_eq_lintegral_ofReal hui.abs (ae_of_all _ fun y => abs_nonneg _),
      ← hmass]
    exact lintegral_mono hle
  · -- Step 9: the integral identity
    have hMF : MeasurableSet (R.carrier ∩ Φ '' Q₁) := R.measurableSet_carrier.inter hF
    calc ∫ x in R.carrier ∩ Φ '' Q₁,
            (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
        = ∫ x in R.carrier ∩ Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) ∂μHE[n] := by
          refine setIntegral_congr_ae hMF ?_
          filter_upwards [(ae_restrict_iff' hMF).1 hσ] with x hx hxMF
          rw [hx hxMF, show g x = (R.mult x : ℝ) * (σ x : ℝ) from indicator_of_mem hxMF.1 _]
          ring
      _ = ∫ x in Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hF inter_subset_right
            ?_).symm
          intro x hx
          have hxM : x ∉ R.carrier := fun hxM => hx.2 ⟨hxM, hx.1⟩
          simp [g, indicator_of_notMem hxM]
      _ = ∫ y in Q₁, g (Φ y) * (ω : DifferentialForm (Euclid P) n) (Φ y)
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := hint _
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
/-- **Integrability of the action integrand** (Simon Ch. 6, 3.1 (‡)).  For an integer
multiplicity triple `R = (C, θ, ξ)` in `U` and `ω ∈ 𝒟ⁿ(U)`, `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is
`Hⁿ⌞C`-integrable: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal `Hⁿ`-a.e. on `C`, so
`|⟨α, ξ(x)⟩| ≤ ‖α‖`, and the integrand is dominated by `B θ 1_{spt ω}` (`B` a bound for `‖ω‖`),
which is integrable because `spt ω` is a compact subset of `U` and `∫_{C ∩ K} θ dHⁿ < ∞` for
such `K`. -/
theorem Submission.regcomp_rim_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  set K : Set (Euclid P) := tsupport f
  /- Step 1: `ω` is continuous, bounded by some `B`, and vanishes off the compact set
  `K = spt ω ⊆ U`. -/
  have hcont : Continuous f := hsmooth.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
  /- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal gives `|⟨α, ξ(x)⟩| = |α(τ)| ≤ ‖α‖`
  for `Hⁿ`-a.e. `x ∈ C`. -/
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      ‖R.orient x α‖ ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hor⟩ := hx
    have hατ : ‖α τ‖ ≤ ‖α‖ := by
      simpa [hτ.norm_eq_one] using α.le_opNorm τ
    rcases hor with h | h
    · rw [h]
      exact hατ
    · rw [h, norm_neg]
      exact hατ
  /- Step 3: the integrand is a.e. strongly measurable (evaluation is continuous). -/
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hev : AEStronglyMeasurable (fun x => R.orient x (f x)) (μHE[n].restrict R.carrier) :=
    happly.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable)
  have hF : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (f x))
      (μHE[n].restrict R.carrier) := hθm.aestronglyMeasurable.mul hev
  /- Step 4: `B θ 1_K` is integrable, since `∫_{C ∩ K} θ dHⁿ < ∞`. -/
  have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) K (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hKm, inter_comm]
    simpa only [Real.enorm_natCast] using (R.locallyIntegrable_mult K hcpt hU).lt_top
  have hg : Integrable (fun x => B * K.indicator (fun x => (R.mult x : ℝ)) x)
      (μHE[n].restrict R.carrier) := (hθK.integrable_indicator hKm).const_mul B
  /- Step 5: `|θ ⟨ω, ξ⟩| ≤ B θ 1_K` a.e. on `C`. -/
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (f x)‖ ≤ B * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (f x)).trans (hB x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
      simp
  /- Step 6: dominated by an integrable function. -/
  exact hg.mono' hF hbound

/-- **Unit-face decomposition of an integer multiplicity current on the `(m+1)`-skeleton**
(Simon Ch. 6, proof of the deformation theorem 5.1, (26)–(28) and (33)).  Let `Q₀ = τ(M, θ, ξ)` in
`ℝᴾ`, `n = m + 1`, with `spt Q₀ ⊆ K` compact and `spt Q₀ ⊆ L_n`.  The faces `p = (ι, b)` whose
closed face `Φ_p([0,1]ⁿ)` meets `spt Q₀` form a finite set `s`, and distinct open faces
`F̆_p = Φ_p((0,1)ⁿ)` are disjoint Borel sets (`Φ_p` is an isometry).  `M ∖ ⋃_{p ∈ s} F̆_p` lies in
`(M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null: off `L_m`, a point of `spt Q₀ ⊆ L_n` lies on an open
face.  On each face `face_density` gives an integer density `u_p` with
`∫_{M ∩ F̆_p} θ ⟨ω, ξ⟩ dHⁿ = ∫_{(0,1)ⁿ} u_p(y) ω(Φ_p y)(E_p) dy` and `∫ |u_p| ≤ μ(F̆_p)`,
`μ = θ Hⁿ⌞M`.  Summing over the disjoint faces gives the representation of `Q₀(ω)`, and
`Σ_p ∫ |u_p| ≤ μ(ℝᴾ) = M(Q₀)` by the mass hypothesis (MR). -/
theorem Submission.cmcdtfr_skeleton_decomposition : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ) (K : Set (Euclid P)) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → ∃ (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∀ y, ∃ z : ℤ, u p y = z) ∧ (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) ≤ Q₀.mass ∧ (∀ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.support) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro _hVO hMR hIMC P m K Q₀ hK hQ₀ hQK hQL
  -- Step 1: an integer multiplicity representation `R = (M, θ, ξ)` of `Q₀`
  obtain ⟨R, hR⟩ := hQ₀
  -- the face maps `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` and the open unit cube `Q₁`
  let Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  -- Step 8: `Φ_p` is an isometry (`face_geometry` (a)), so the open face `F̆_p = Φ_p(Q₁)` is Borel
  have hiso : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → Isometry (Φ p) :=
    fun p hp => Isometry.of_dist_eq ((Submission.cmcdtfr_face_geometry P (m + 1)).2 p p hp hp).1
  have hQ₁ : MeasurableSet Q₁ := by
    have hpre : Q₁ = WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Q₁, Set.mem_pi]
    rw [hpre]
    exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hF : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 →
      MeasurableSet (Φ p '' Q₁) :=
    fun p hp => (hiso p hp).isClosedEmbedding.measurableEmbedding.measurableSet_image' hQ₁
  -- Step 6: distinct open faces are disjoint (`face_geometry` (c))
  have hdisj : ∀ p q : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 →
      p ≠ q → Disjoint (Φ p '' Q₁) (Φ q '' Q₁) := by
    intro p q hp hq hpq
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have h : 1 ≤ dist (Φ p y) (Φ q y') ∨ ∃ j, min (y j) (1 - y j) ≤ dist (Φ p y) (Φ q y') :=
      ((Submission.cmcdtfr_face_geometry P (m + 1)).2 p q hp hq).2.2 hpq y y' hy
        fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩
    rw [hyy', dist_self] at h
    rcases h with h | ⟨j, hj⟩
    · exact absurd h (by norm_num)
    · obtain ⟨hy₀, hy₁⟩ := hy j
      exact absurd hj (not_le.mpr (lt_min hy₀ (by linarith)))
  -- Step 5: the finite set `s` of faces `p` whose closed face meets `spt Q₀ ⊆ K`
  obtain ⟨s, hs⟩ : ∃ s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ)), ∀ p, p ∈ s ↔
      StrictMono p.1 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ Φ p y ∈ Q₀.support := by
    have hfin : {p : (Fin (m + 1) → Fin P) × (Fin P → ℤ) | StrictMono p.1 ∧
        ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ Φ p y ∈ Q₀.support}.Finite :=
      (Submission.cmcdtfrsd_faces_meeting_compact_finite P (m + 1) K hK).subset
        fun p ⟨_, y, hy, hyQ⟩ => ⟨y, hy, hQK hyQ⟩
    exact ⟨hfin.toFinset, fun p => hfin.mem_toFinset⟩
  -- Steps 9–11: the integer densities `u_p` on the faces (`face_density`)
  have hfd : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 →
      ∃ u : Euclid (m + 1) → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u Q₁ ∧
        ENNReal.ofReal (∫ y in Q₁, |u y|) ≤ R.measure (Φ p '' Q₁) ∧
        ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
          ∫ x in R.carrier ∩ Φ p '' Q₁, (R.mult x : ℝ) *
              R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
            ∫ y in Q₁, u y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y)
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) :=
    fun p hp => Submission.cmcdtfrsd_face_density hIMC.2.1 Submission.cmcdtfr_plane_orientation
      P (m + 1) R p hp (hiso p hp)
  choose! u hu_int hu_integ hu_mass hu_rep using hfd
  refine ⟨s, u, fun p hp => ((hs p).1 hp).1, fun p hp => hu_int p ((hs p).1 hp).1,
    fun p hp => hu_integ p ((hs p).1 hp).1, ?_, fun p hp => ((hs p).1 hp).2, fun ω => ?_⟩
  · -- Step 11: `Σ_p ∫|u_p| ≤ Σ_p μ(F̆_p) = μ(⋃_p F̆_p) ≤ μ(ℝᴾ) = M(Q₀)`, the last step by (MR)
    calc ENNReal.ofReal (∑ p ∈ s, ∫ y in Q₁, |u p y|)
        = ∑ p ∈ s, ENNReal.ofReal (∫ y in Q₁, |u p y|) :=
          ENNReal.ofReal_sum_of_nonneg fun p _ => integral_nonneg fun y => abs_nonneg (u p y)
      _ ≤ ∑ p ∈ s, R.measure (Φ p '' Q₁) :=
          Finset.sum_le_sum fun p hp => hu_mass p ((hs p).1 hp).1
      _ = R.measure (⋃ p ∈ s, Φ p '' Q₁) :=
          (measure_biUnion_finset (fun p hp q hq hpq =>
            hdisj p q ((hs p).1 hp).1 ((hs q).1 hq).1 hpq) fun p hp => hF p ((hs p).1 hp).1).symm
      _ ≤ R.measure univ := measure_mono (subset_univ _)
      _ = Q₀.mass := (hMR P (m + 1) univ Q₀ R isOpen_univ hR univ isOpen_univ).symm
  · -- Step 7: `M ∖ ⋃_{p ∈ s} (M ∩ F̆_p) ⊆ (M ∖ spt Q₀) ∪ L_m`, an `Hⁿ`-null set
    have hnull : μHE[m + 1] (R.carrier \ ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁)) = 0 := by
      refine measure_mono_null ?_ (measure_union_null
        (Submission.imrep_carrier_sdiff_support_null P (m + 1) univ Q₀ R isOpen_univ hR)
        (Submission.cmcdtfr_skeleton_null P m))
      rintro x ⟨hxM, hx⟩
      by_cases hxS : x ∈ Q₀.support
      · -- `x ∈ spt Q₀ ⊆ L_{m+1}`; off `L_m` it lies on an open face `F̆_p` with `p ∈ s`
        refine Or.inr (by_contra fun hxL => ?_)
        obtain ⟨p, y, hp, hy, rfl⟩ :=
          Submission.cmcdtfrsd_skeleton_point_on_open_face P m _ (hQL hxS) hxL
        exact hx (mem_iUnion₂.2 ⟨p, (hs p).2 ⟨hp, y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hxS⟩,
          hxM, y, hy, rfl⟩)
      · exact Or.inl ⟨hxM, hxS⟩
    have hae : R.carrier =ᵐ[μHE[m + 1]] ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁) := by
      refine ae_eq_set.2 ⟨hnull, ?_⟩
      rw [Set.sdiff_eq_empty.2 (iUnion₂_subset fun p _ => inter_subset_left), measure_empty]
    -- Step 12: split `Q₀(ω) = ∫_M θ ⟨ω, ξ⟩ dHⁿ` over the disjoint faces and change variables
    have hint := Submission.regcomp_rim_action_integrable P (m + 1) univ R ω
    calc Q₀ ω = ∫ x in R.carrier,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          hR ω
      _ = ∫ x in ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁),
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          setIntegral_congr_set hae
      _ = ∑ p ∈ s, ∫ x in R.carrier ∩ Φ p '' Q₁,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          integral_biUnion_finset s
            (fun p hp => R.measurableSet_carrier.inter (hF p ((hs p).1 hp).1))
            (fun p hp q hq hpq => (hdisj p q ((hs p).1 hp).1 ((hs q).1 hq).1 hpq).mono
              inter_subset_right inter_subset_right)
            fun p _ => IntegrableOn.mono_set hint inter_subset_left
      _ = _ := Finset.sum_congr rfl fun p hp => hu_rep p ((hs p).1 hp).1 ω

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
