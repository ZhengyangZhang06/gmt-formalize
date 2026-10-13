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

/-- **Densities of a cone with translation-invariant weight** (Simon 6.2.8, 6.3.2(3) and 7.3.1(2);
the `ℝx`-translation step for tangent objects of cones in the proof of A.4, chapter-A.txt lines
125–131).  Let `S = τ(M, θ, ξ)` be a cone in `ℝᴾ` whose weight `μ_R = θHⁿ⌞M` is invariant under
translation by the subspace `L`.  If `Θⁿ(μ_S, w) = θ`, then `Θⁿ(μ_S, y + λw) = θ` for `y ∈ L` and
`λ > 0`.  First `M_W(S) = μ_R(W)` for open `W` (6.3.2(3)): `⟨ω, ξ⟩ ≤ |ω|` gives `≤`, and Lusin's
theorem with a smooth partition of unity approximating the dual covector field of `ξ` gives `≥`.
The cone property `η_{0,λ#}S = S` gives `M_{B_{λρ}(λx)}(S) = λⁿ M_{B_ρ(x)}(S)`, and `-y ∈ L` gives
`μ_R(B_ρ(y + λw)) = μ_R(B_ρ(λw))`.  Hence the density ratio of `S` at `y + λw` and radius `ρ`
equals that at `w` and radius `ρ/λ`, and `ρ/λ → 0+` as `ρ → 0+`. -/
theorem Submission.idtp_cttp_cone_density_translation_invariant : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), R.Represents S → IsConeCurrent S → (∀ v ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => x + v) ⁻¹' A) = R.measure A) → ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ := by
  intro P n
  -- Step 1 (coefficients): `|α| = ‖coef α‖` for the continuous linear map
  -- `coef α = (α(e_I))_I`, `I` strictly increasing (and `0` otherwise)
  obtain ⟨coef, hcoef⟩ : ∃ coef : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P),
      ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖coef α‖ := by
    let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
      if StrictMono I then
        ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i =>
          EuclideanSpace.basisFun (Fin P) ℝ (I i)
      else 0
    refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi c), fun α => ?_⟩
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 2 (Simon Ch. 6, 1.2 and 1.5–1.7): a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has
  -- `|ξ(α)| ≤ |α|`, and `Ld ζ = Σ_I ζ(dx^I) dx^I` has `|Ld ξ| ≤ 1` and `ξ(Ld ξ) = 1`
  obtain ⟨Ld, hLd⟩ : ∃ Ld : MultiVector P n →L[ℝ] Covector (Euclid P) n,
      ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
        (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧
          covectorEuclideanNorm (Ld ξ) ≤ 1 ∧ ξ (Ld ξ) = 1 := by
    -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
    let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
      ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun k => innerSL ℝ (u k))
    have hW : ∀ u v, W u v =
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
      intro u v
      simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
    -- `W u v = W v u` (the determinant of the transpose)
    have hWsymm : ∀ u v, W u v = W v u := by
      intro u v
      rw [hW, hW]
      refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
      rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
        ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
    -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
    have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
      intro u hu
      rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul]
        refine Finset.prod_eq_one fun k _ => ?_
        rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`
    let e := EuclideanSpace.basisFun (Fin P) ℝ
    have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.mp e.orthonormal
    have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
        W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
      intro I J hI hJ
      split_ifs with hIJ
      · subst hIJ
        have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
        exact hW1 _ hIo
      · rw [hW]
        refine Finset.sum_eq_zero fun σ _ => ?_
        rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
        by_contra! h
        apply hIJ
        have hJσ : J ∘ σ = I := funext fun k => by
          have := h k (Finset.mem_univ k)
          rw [he] at this
          split_ifs at this with hk
          · exact hk.symm
          · exact absurd rfl this
        rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
    -- expansion `α = Σ_{I ∈ Sinc} α(e_I) dx^I`
    let Sinc : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
    have hE : ∀ α : Covector (Euclid P) n,
        α = ∑ I ∈ Sinc, α (fun k => e (I k)) • W (fun k => e (I k)) := by
      intro α
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      refine e.toBasis.ext_alternating fun f hf => ?_
      simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
      set σ := Tuple.sort f
      have hJ : StrictMono (f ∘ σ) :=
        (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
      have hperm : ∀ β : Covector (Euclid P) n,
          β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
        intro β
        have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
          funext k
          simp
        rw [this]
        exact β.toAlternatingMap.map_perm _ _
      rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
          mul_one]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
          ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
    -- `|β| = (Σ_{I ∈ Sinc} β(e_I)²)^{1/2}`
    have hnorm : ∀ β : Covector (Euclid P) n,
        covectorEuclideanNorm β = Real.sqrt (∑ I ∈ Sinc, β (fun k => e (I k)) ^ 2) := by
      intro β
      rw [covectorEuclideanNorm, Finset.sum_filter]
    -- Cauchy–Binet `Σ_{I ∈ Sinc} dx^I(τ)² = 1` for orthonormal `τ`
    have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
        ∑ I ∈ Sinc, W (fun k => e (I k)) τ ^ 2 = 1 := by
      intro τ hτ
      have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
      simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul, hW1 τ hτ] at h
      rw [h]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [hWsymm τ, sq]
    refine ⟨∑ I ∈ Sinc, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
      (W fun k => e (I k)), ?_⟩
    rintro ξ Q ⟨τ, hτ, -, hξ⟩
    have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
      intro α β
      rcases hξ with h | h
      · rw [h, h]
      · rw [h, h, neg_mul_neg]
    have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
      intro α
      rcases hξ with h | h
      · rw [h]
      · rw [h, abs_neg]
    have hLζ : ∀ ζ : MultiVector P n, (∑ I ∈ Sinc, (ContinuousLinearMap.apply ℝ ℝ
        (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
        ∑ I ∈ Sinc, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
      intro ζ
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
    have hCBτ := hCB τ hτ
    refine ⟨fun α => ?_, ?_, ?_⟩
    · rw [hξabs, hnorm]
      apply Real.abs_le_sqrt
      have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
      simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at h
      rw [h]
      calc (∑ I ∈ Sinc, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
          ≤ (∑ I ∈ Sinc, α (fun k => e (I k)) ^ 2) * ∑ I ∈ Sinc, W (fun k => e (I k)) τ ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = ∑ I ∈ Sinc, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
    · rw [hnorm, hLζ]
      have : ∑ J ∈ Sinc, (∑ I ∈ Sinc, ξ (W fun k => e (I k)) • W fun k => e (I k))
          (fun k => e (J k)) ^ 2 = 1 := by
        rw [← hCBτ]
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
        · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
            (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
        · intro I hI hIJ
          rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
            (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
        · exact fun h => absurd hJ h
      rw [this, Real.sqrt_one]
    · rw [hLζ, map_sum, ← hCBτ]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_smul, smul_eq_mul, hξ2, sq]
  -- Step 3 (Simon Ch. 6, 1.15 and 2.5): if `coef ∘ β` is continuous on a compact `K ⊆ V`
  -- (`V` open) with `|β| ≤ 1` there, a test form `ω = Σₐ fₐ β(a)` supported in `V`, with
  -- `|ω| ≤ 1` and `|ω - β| ≤ δ` on `K`, comes from a smooth partition of unity `(fₐ)` on `K`
  -- subordinate to a finite cover of `K` by small balls `B_s(a)`, `a ∈ K`
  have hsmooth : ∀ (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ),
      IsCompact K → IsOpen V → K ⊆ V → ContinuousOn (fun x => coef (β x)) K →
      (∀ x ∈ K, ‖coef (β x)‖ ≤ 1) → 0 < δ →
      ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧
        (∀ x, ‖coef (ω x)‖ ≤ 1) ∧ ∀ x ∈ K, ‖coef (ω x) - coef (β x)‖ ≤ δ := by
    intro K V β δ hK hV hKV hβ hβ1 hδ
    -- a modulus `s` of uniform continuity of `coef ∘ β` on `K`, and a margin `r`
    obtain ⟨s, hs, hβs⟩ := Metric.uniformContinuousOn_iff.1
      (hK.uniformContinuousOn_of_continuous hβ) δ hδ
    obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
    have hsr : 0 < min s r := lt_min hs hr
    -- a finite cover of `K` by balls `B_{min s r}(a)`, `a ∈ t ⊆ K`, and a smooth partition of
    -- unity on `K` subordinate to it
    obtain ⟨t, htK, hKt⟩ :=
      hK.elim_nhds_subcover (fun a => ball a (min s r)) fun a _ => ball_mem_nhds a hsr
    obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
      (modelWithCornersSelf ℝ (Euclid P)) hK.isClosed
      (fun a : t => ball (a : Euclid P) (min s r)) (fun a => isOpen_ball) fun x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
    have hsum : ∀ x, ∑ a : t, f a x ≤ 1 := fun x => by
      rw [← finsum_eq_sum_of_fintype]
      exact f.sum_le_one x
    have hsum1 : ∀ x ∈ K, ∑ a : t, f a x = 1 := fun x hx => by
      rw [← finsum_eq_sum_of_fintype]
      exact f.sum_eq_one hx
    have hfa : ∀ (a : t) (x : Euclid P), f a x ≠ 0 → dist x a < min s r := fun a x h =>
      mem_ball.1 (hf a (subset_tsupport _ h))
    -- `spt ω ⊆ cthickening (min s r) K ⊆ cthickening r K ⊆ V`
    have hsupp : support (fun x => ∑ a : t, f a x • β a) ⊆ thickening (min s r) K := by
      intro x hx
      rw [Function.mem_support] at hx
      obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hfx : f a x ≠ 0 := fun h => ha (by rw [h, zero_smul])
      exact mem_thickening_iff.2 ⟨a, htK a a.2, hfa a x hfx⟩
    have htsupp : tsupport (fun x => ∑ a : t, f a x • β a) ⊆ cthickening (min s r) K :=
      (closure_mono hsupp).trans (closure_thickening_subset_cthickening _ _)
    refine ⟨fun x => ∑ a : t, f a x • β a, ⟨?_, ?_⟩, ?_, fun x => ?_, fun x hx => ?_⟩
    · exact ContDiff.sum fun a _ => (contMDiff_iff_contDiff.1 (f a).contMDiff).smul contDiff_const
    · exact hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp
    · exact htsupp.trans ((cthickening_mono (min_le_right s r) K).trans hrV)
    · -- `|ω x| ≤ Σₐ fₐ(x) |β(a)| ≤ Σₐ fₐ(x) ≤ 1`
      rw [map_sum]
      calc ‖∑ a : t, coef (f a x • β a)‖ ≤ ∑ a : t, ‖coef (f a x • β a)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, f a x := Finset.sum_le_sum fun a _ => by
            rw [map_smul, norm_smul, Real.norm_of_nonneg (f.nonneg a x)]
            exact mul_le_of_le_one_right (f.nonneg a x) (hβ1 a (htK a a.2))
        _ ≤ 1 := hsum x
    · -- on `K`: `ω x - β x = Σₐ fₐ(x) (β(a) - β(x))` and `|β(a) - β(x)| < δ` when `fₐ(x) ≠ 0`
      have hdiff : coef (∑ a : t, f a x • β a) - coef (β x) =
          ∑ a : t, f a x • (coef (β a) - coef (β x)) := by
        simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
          hsum1 x hx, one_smul]
      rw [hdiff]
      calc ‖∑ a : t, f a x • (coef (β a) - coef (β x))‖
          ≤ ∑ a : t, ‖f a x • (coef (β a) - coef (β x))‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, f a x * δ := Finset.sum_le_sum fun a _ => by
            rw [norm_smul, Real.norm_of_nonneg (f.nonneg a x)]
            rcases eq_or_ne (f a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (f.nonneg a x)
              rw [← dist_eq_norm]
              refine (hβs a (htK a a.2) x hx ?_).le
              rw [dist_comm]
              exact (hfa a x h).trans_le (min_le_left s r)
        _ = δ := by rw [← Finset.sum_mul, hsum1 x hx, one_mul]
  intro S R L hR hcone hinv y hy lam hlam w θ hθ
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- Step 4 (Simon Ch. 6, 3.1 (‡)): `S(ω) = ∫ ⟨ω, ξ⟩ dμ_R` with `μ_R = θ Hⁿ⌞M`, the integrand
  -- being bounded by `sup |ω|` `μ_R`-a.e. and vanishing off the compact `spt ω`
  have haction : ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
      Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧
        S ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
    intro ω
    rw [hR ω]
    obtain ⟨⟨hsm, hcpt⟩, -⟩ := ω.2
    set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
    have hmult : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
    have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
      isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
        (R.aestronglyMeasurable_orient.mono_ac hac) hsm.continuous.aestronglyMeasurable
    obtain ⟨C, hC⟩ := hsm.continuous.bounded_above_of_compact_support hcpt
    have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
    have hbound : ∀ᵐ x ∂R.measure,
        ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
      filter_upwards [hac.ae_le R.orients] with x hx
      obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
      by_cases hxK : x ∈ tsupport f
      · rw [Set.indicator_of_mem hxK]
        have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
          simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
        rcases hξ with h | h
        · rw [h]
          exact hτ1.trans (hC x)
        · rw [h, norm_neg]
          exact hτ1.trans (hC x)
      · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero,
          norm_zero]
    have hKfin : R.measure (tsupport f) ≠ ∞ := by
      rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
        Set.inter_comm (tsupport f) R.carrier]
      exact R.locallyIntegrable_mult _ hcpt (subset_univ _)
    have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
      ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
    refine ⟨hint, ?_⟩
    rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hmult
      (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
    simp only [ENNReal.toReal_natCast, smul_eq_mul]
  have hfin : ∀ K : Set (Euclid P), IsCompact K → R.measure K < ∞ := by
    intro K hK
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK (subset_univ K)).lt_top
  -- Step 5 (Simon Ch. 6, 3.2(3), upper bound): `M_W(S) ≤ μ_R(W)`, since for admissible `ω`,
  -- `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_R`-a.e. and `⟨ω, ξ⟩ = 0` off `spt ω ⊆ W`
  have hupper : ∀ W : Set (Euclid P), S.massOn W ≤ R.measure W := by
    intro W
    have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
        |R.orient x α| ≤ covectorEuclideanNorm α := by
      refine hac.ae_le ?_
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, -, hQ⟩ := hx
      exact (hLd _ Q hQ).1
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    set K := tsupport (ω : DifferentialForm (Euclid P) n)
    have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
    have hμK : R.measure K ≠ ∞ := (hfin K ω.2.1.2.isCompact).ne
    obtain ⟨hint, heq⟩ := haction ω
    have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
        K.indicator fun _ => (1 : ℝ) := by
      filter_upwards [hdual] with x hx
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK]
        exact (le_abs_self _).trans ((hx _).trans (hω1 x))
      · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
    calc ENNReal.ofReal (S ω)
        = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x)
            ∂R.measure) := by rw [heq]
      _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
          ENNReal.ofReal_le_ofReal (integral_mono_ae hint
            ((integrableOn_const hμK).integrable_indicator hKm) hle)
      _ = R.measure K := by
          rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
            ENNReal.ofReal_toReal hμK]
      _ ≤ R.measure W := measure_mono hωW
  -- Step 6 (Simon Ch. 6, 3.2(3), lower bound): `μ_R(W) ≤ M_W(S)` for open `W`.  Take a compact
  -- `K ⊆ W` of nearly full measure; by Lusin (Simon 1.17) `β = Ld ∘ ξ` is continuous on a compact
  -- `K' ⊆ K` with `μ_R(K \ K') < η`; for a thin open `V ⊇ K'` and the form `ω` of Step 3 with
  -- `|ω - β| ≤ δ` on `K'`, `S(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')` is close to `μ_R(W)`
  have hlower : ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ S.massOn W := by
    intro W hW
    have hgm : AEStronglyMeasurable (fun x => coef (Ld (R.orient x))) R.measure :=
      (coef.comp Ld).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_ac hac)
    -- `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|Ld ξ(x)| ≤ 1`, `ξ(x)(Ld ξ(x)) = 1`, and
    -- `coef (Ld ξ(x)) = g x` for the measurable version `g = hgm.mk _`
    have hgood : ∀ᵐ x ∂R.measure,
        ((∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
          covectorEuclideanNorm (Ld (R.orient x)) ≤ 1 ∧ R.orient x (Ld (R.orient x)) = 1) ∧
        coef (Ld (R.orient x)) = hgm.mk _ x := by
      have h1 : ∀ᵐ x ∂R.measure,
          (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
            covectorEuclideanNorm (Ld (R.orient x)) ≤ 1 ∧ R.orient x (Ld (R.orient x)) = 1 := by
        refine hac.ae_le ?_
        filter_upwards [R.orients] with x hx
        obtain ⟨Q, -, hQ⟩ := hx
        exact hLd _ Q hQ
      exact h1.and hgm.ae_eq_mk
    obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
    -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W)`
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
    set η : ℝ := (ε : ℝ) / 4 with hη
    have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
    -- a compact `K ⊆ W` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W`
    obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hW.exists_iUnion_isClosed
    have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
      inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
    have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W := by
      refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
        fun x hx => ?_
      rw [← hFU] at hx
      obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact hk.trans (Nat.cast_le.2 (le_max_right i k))
    have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
      rwa [hKU]
    obtain ⟨j, hj⟩ :=
      ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
    set K := F j ∩ closedBall (0 : Euclid P) j
    have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
    have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
    have hKG : K ⊆ W := inter_subset_left.trans (hFG j)
    have hKfin : R.measure K < ∞ := hfin K hKc
    -- Lusin (Simon 1.17) for `g = hgm.mk _` on `K \ Z`: `μ_R⌞(K \ Z)` is finite, hence
    -- inner regular; for a countable basis `(O_k)` and weights `ηs_k` with `Σ ηs_k < η`, take
    -- compact `C_k ⊆ (K \ Z) ∩ g⁻¹(O_k)`, `D_k ⊆ (K \ Z) \ g⁻¹(O_k)` with small defects, and
    -- `K' = ⋂ₖ (C_k ∪ D_k)`; on `K'`, `g⁻¹(O_k) = D_kᶜ`
    obtain ⟨K', hK'c, hK'K, hK'small, hgc⟩ : ∃ K' : Set (Euclid P), IsCompact K' ∧
        K' ⊆ K \ Z ∧ R.measure ((K \ Z) \ K') < ENNReal.ofReal η ∧ ContinuousOn (hgm.mk _) K' := by
      have hA : MeasurableSet (K \ Z) := hKc.measurableSet.diff hZm
      have hμA : R.measure (K \ Z) ≠ ∞ := ((measure_mono sdiff_subset).trans_lt hKfin).ne
      have hg : Measurable (hgm.mk _) := hgm.stronglyMeasurable_mk.measurable
      have : IsFiniteMeasure (R.measure.restrict (K \ Z)) := isFiniteMeasure_restrict.mpr hμA
      have approx : ∀ B, B ⊆ K \ Z → MeasurableSet B → ∀ η' : ℝ≥0∞, η' ≠ 0 →
          ∃ C ⊆ B, IsCompact C ∧ R.measure (B \ C) < η' := by
        intro B hBA hB η' hη'
        obtain ⟨C, hCB, hC, hlt⟩ :=
          hB.exists_isCompact_sdiff_lt (μ := R.measure.restrict (K \ Z)) (measure_ne_top _ _) hη'
        exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
      obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis (EuclideanSpace ℝ (Fin n → Fin P))
      obtain ⟨ηs, hηs, hηsε⟩ :=
        ENNReal.exists_pos_sum_of_countable' (ENNReal.ofReal_pos.2 hη0).ne' ℕ
      have hS : ∀ k, MeasurableSet (hgm.mk _ ⁻¹' O k) :=
        fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
      choose C hCA hC hCμ using fun k =>
        approx ((K \ Z) ∩ hgm.mk _ ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (ηs k / 2)
          (ENNReal.half_pos (hηs k).ne').ne'
      choose D hDA hD hDμ using fun k =>
        approx ((K \ Z) \ hgm.mk _ ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (ηs k / 2)
          (ENNReal.half_pos (hηs k).ne').ne'
      have hE : ∀ k, R.measure ((K \ Z) \ (C k ∪ D k)) < ηs k := by
        intro k
        calc R.measure ((K \ Z) \ (C k ∪ D k))
            ≤ R.measure (((K \ Z) ∩ hgm.mk _ ⁻¹' O k) \ C k ∪
                ((K \ Z) \ hgm.mk _ ⁻¹' O k) \ D k) := by
              refine measure_mono fun x hx => ?_
              by_cases hxO : hgm.mk _ x ∈ O k
              · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
              · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
          _ ≤ R.measure (((K \ Z) ∩ hgm.mk _ ⁻¹' O k) \ C k) +
                R.measure (((K \ Z) \ hgm.mk _ ⁻¹' O k) \ D k) := measure_union_le _ _
          _ < ηs k / 2 + ηs k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
          _ = ηs k := ENNReal.add_halves _
      refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
      · exact ((hC 0).union (hD 0)).of_isClosed_subset
          (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
      · exact (iInter_subset _ 0).trans
          (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
      · calc R.measure ((K \ Z) \ ⋂ k, (C k ∪ D k))
            = R.measure (⋃ k, (K \ Z) \ (C k ∪ D k)) := by rw [sdiff_iInter]
          _ ≤ ∑' k, R.measure ((K \ Z) \ (C k ∪ D k)) := measure_iUnion_le _
          _ ≤ ∑' k, ηs k := ENNReal.tsum_le_tsum fun k => (hE k).le
          _ < ENNReal.ofReal η := hηsε
      · rw [hO.continuousOn_iff]
        rintro _ ⟨k, rfl⟩
        refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
        ext x
        refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩,
          fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
        rcases mem_iInter.mp hxK k with hxC | hxD'
        · exact (hCA k hxC).2
        · exact absurd hxD' hxD
    have hgoodK' : ∀ x ∈ K',
        ((∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
          covectorEuclideanNorm (Ld (R.orient x)) ≤ 1 ∧ R.orient x (Ld (R.orient x)) = 1) ∧
        coef (Ld (R.orient x)) = hgm.mk _ x := fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
    have hβc : ContinuousOn (fun x => coef (Ld (R.orient x))) K' :=
      hgc.congr fun x hx => (hgoodK' x hx).2
    have hK'G : K' ⊆ W := hK'K.trans (sdiff_subset.trans hKG)
    have hK'm : MeasurableSet K' := hK'c.measurableSet
    have hK'fin : R.measure K' ≠ ∞ :=
      ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
    have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
      calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
            by_cases hxZ : x ∈ Z
            · exact Or.inr hxZ
            · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
        _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
        _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
    -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W` and `μ_R(V \ K') < η`
    obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hW hK'G
    have hthick : R.measure (thickening ρ K') ≠ ∞ :=
      ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
        (hfin _ hK'c.cthickening)).ne
    obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
      ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
        (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
    set V := thickening t K'
    have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
    have hVG : V ⊆ W := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
    have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
      measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
    have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
    have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
    -- a test form `ω` supported in `V` with `|ω| ≤ 1` and `|ω - Ld ∘ ξ| ≤ δ` on `K'`
    set m : ℝ := R.measure.real K
    have hm0 : 0 ≤ m := measureReal_nonneg
    set δ : ℝ := η / (m + 1) with hδ
    have hδ0 : 0 < δ := div_pos hη0 (by linarith)
    obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := hsmooth K' V (fun x => Ld (R.orient x)) δ hK'c
      isOpen_thickening hK'V hβc
      (fun x hx => by rw [← hcoef]; exact (hgoodK' x hx).1.2.1) hδ0
    let ω : TestFormOn (univ : Set (Euclid P)) n := ⟨ω₀, hω₀t, subset_univ _⟩
    have hadm : ω ∈ massAdmissibleOn univ n W :=
      ⟨hω₀V.trans hVG, fun x => by rw [hcoef]; exact hω₀1 x⟩
    obtain ⟨hfi, hfe⟩ := haction ω
    -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `S(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
    have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
      (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
    have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
      (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
    have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
        (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
          fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
      filter_upwards [hgood] with x hx
      obtain ⟨⟨hx1, -, hx3⟩, -⟩ := hx
      change _ ≤ R.orient x (ω₀ x)
      by_cases hxK' : x ∈ K'
      · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
        have h1 := hx1 (ω₀ x - Ld (R.orient x))
        have h2 : covectorEuclideanNorm (ω₀ x - Ld (R.orient x)) ≤ δ := by
          rw [hcoef, map_sub]
          exact hω₀β x hxK'
        rw [map_sub, hx3] at h1
        linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
      · rw [indicator_of_notMem hxK', zero_sub]
        by_cases hxV : x ∈ V
        · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
          have h3 : covectorEuclideanNorm (ω₀ x) ≤ 1 := by
            rw [hcoef]
            exact hω₀1 x
          linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x)]
        · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
            image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
    have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
        ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
      integral_mono_ae (hi1.sub hi2) hfi hle
    rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
      smul_eq_mul, smul_eq_mul, mul_one, ← hfe] at hint
    -- arithmetic: `S(ω) > r`
    have hm1 : (r : ℝ) + ε < m := by
      have := ENNReal.toReal_strict_mono hKfin.ne hrK
      rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
        ENNReal.coe_toReal] at this
    have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
    have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
    have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
      measureReal_inter_add_sdiff hK'm hKfin.ne
    rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
    have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
    have hδm : R.measure.real K' * δ < η := by
      have h1 : m * δ < η := by
        rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
        nlinarith
      have h2 : R.measure.real K' * δ ≤ m * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ0.le
      linarith
    have hrT : (r : ℝ) < S ω := by linarith
    calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
      _ ≤ ENNReal.ofReal (S ω) := ENNReal.ofReal_le_ofReal hrT.le
      _ ≤ S.massOn W := S.le_massOn hadm
  -- Step 7 (Simon Ch. 6, 3.2(3)): `M_W(S) = μ_R(W)` for every open `W`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → S.massOn W = R.measure W :=
    fun W hW => le_antisymm (hupper W) (hlower W hW)
  -- Step 8 (Simon 7.3.1(2) via 6.2.23): for `c > 0`, the cone property `η_{0,c#}S = S` reads
  -- `S(ω) = S(η_{0,c}^# ω)` with `η_{0,c}^# ω(z) = c⁻ⁿ ω(c⁻¹z)` (multilinearity), so
  -- `ω'(z) = ω(c⁻¹z)` defines a test form with `S(ω') = cⁿ S(ω)`
  have hdil : ∀ c : ℝ, 0 < c → ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
      ∃ ω' : TestFormOn (univ : Set (Euclid P)) n,
        (∀ z, (ω' : DifferentialForm (Euclid P) n) z =
          (ω : DifferentialForm (Euclid P) n) (c⁻¹ • z)) ∧ S ω' = c ^ n * S ω := by
    intro c hc ω
    have hc1 := hcone c hc ω
    have hV : dilation (0 : Euclid P) c '' univ = univ := by
      refine eq_univ_of_forall fun x => ⟨c • x, mem_univ _, ?_⟩
      simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hc.ne']
    have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
        tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) c '' univ :=
      ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
    rw [currentEval, dite_eq_left h] at hc1
    obtain ⟨ω₁, hω₁, hS₁⟩ : ∃ ω₁ : TestFormOn (univ : Set (Euclid P)) n,
        (∀ z, (ω₁ : DifferentialForm (Euclid P) n) z =
          (c⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (c⁻¹ • z)) ∧ S ω₁ = S ω := by
      refine ⟨_, fun z => ?_, hc1⟩
      ext v
      change (ω : DifferentialForm (Euclid P) n) (-(c⁻¹ • (0 : Euclid P)) + dilationCLM P c z)
          (fun i => dilationCLM P c (v i)) = _
      simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
        ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    refine ⟨(c ^ n) • ω₁, fun z => ?_, ?_⟩
    · change (c ^ n) • (ω₁ : DifferentialForm (Euclid P) n) z = _
      rw [hω₁, smul_smul, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow, one_smul]
    · rw [map_smul, smul_eq_mul, hS₁]
  -- Step 9: `cⁿ M_{B_ρ(x)}(S) ≤ M_{B_{cρ}(cx)}(S)`: `ω ↦ ω'` maps admissible forms for `B_ρ(x)`
  -- to admissible forms for `B_{cρ}(cx)`
  have hscale : ∀ c : ℝ, 0 < c → ∀ (x : Euclid P) (ρ : ℝ),
      ENNReal.ofReal (c ^ n) * S.massOn (ball x ρ) ≤ S.massOn (ball (c • x) (c * ρ)) := by
    intro c hc x ρ
    rw [GeometricCurrentOn.massOn, ENNReal.mul_sSup]
    refine iSup₂_le fun _ ⟨ω, ⟨hωB, hω1⟩, hω⟩ => ?_
    subst hω
    obtain ⟨ω', hω', hS'⟩ := hdil c hc ω
    have hadm : ω' ∈ massAdmissibleOn univ n (ball (c • x) (c * ρ)) := by
      refine ⟨fun z hz => ?_, fun z => ?_⟩
      · have hsub : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆
            (fun z => c⁻¹ • z) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) n) := by
          have hfun : (ω' : DifferentialForm (Euclid P) n) =
              (ω : DifferentialForm (Euclid P) n) ∘ fun z => c⁻¹ • z := funext hω'
          rw [hfun]
          exact tsupport_comp_subset_preimage _ (continuous_const_smul _)
        have h2 := hωB (hsub hz)
        rw [mem_ball, dist_eq_norm] at h2 ⊢
        calc ‖z - c • x‖ = ‖c • (c⁻¹ • z - x)‖ := by
              rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
          _ = c * ‖c⁻¹ • z - x‖ := by rw [norm_smul, Real.norm_of_nonneg hc.le]
          _ < c * ρ := mul_lt_mul_of_pos_left h2 hc
      · rw [hω']
        exact hω1 _
    calc ENNReal.ofReal (c ^ n) * ENNReal.ofReal (S ω) = ENNReal.ofReal (S ω') := by
          rw [← ENNReal.ofReal_mul (by positivity), hS']
      _ ≤ S.massOn (ball (c • x) (c * ρ)) := S.le_massOn hadm
  -- Step 10: `M_{B_{cρ}(cx)}(S) = cⁿ M_{B_ρ(x)}(S)`, using Step 9 for `c` and `c⁻¹`
  have hscale_eq : ∀ c : ℝ, 0 < c → ∀ (x : Euclid P) (ρ : ℝ),
      S.massOn (ball (c • x) (c * ρ)) = ENNReal.ofReal (c ^ n) * S.massOn (ball x ρ) := by
    intro c hc x ρ
    refine le_antisymm ?_ (hscale c hc x ρ)
    have h1 := hscale c⁻¹ (inv_pos.2 hc) (c • x) (c * ρ)
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, ← mul_assoc, inv_mul_cancel₀ hc.ne',
      one_mul] at h1
    calc S.massOn (ball (c • x) (c * ρ))
        = ENNReal.ofReal (c ^ n) * (ENNReal.ofReal (c⁻¹ ^ n) *
            S.massOn (ball (c • x) (c * ρ))) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
            mul_inv_cancel₀ hc.ne', one_pow, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (c ^ n) * S.massOn (ball x ρ) := by gcongr
  -- Step 11: `B_ρ(y + λw) = (· + (-y))⁻¹(B_ρ(λw))` with `-y ∈ L` and `ρ = λ(ρ/λ)`, so
  -- `M_{B_ρ(y + λw)}(S) = μ_R(B_ρ(y + λw)) = μ_R(B_ρ(λw)) = M_{B_ρ(λw)}(S) = λⁿ M_{B_{ρ/λ}(w)}(S)`
  have hball : ∀ ρ : ℝ, S.massOn (ball (y + lam • w) ρ) =
      ENNReal.ofReal (lam ^ n) * S.massOn (ball w (ρ / lam)) := by
    intro ρ
    have htr : ball (y + lam • w) ρ = (fun x => x + -y) ⁻¹' ball (lam • w) ρ := by
      ext x
      simp only [mem_preimage, mem_ball, dist_eq_norm]
      rw [show x + -y - lam • w = x - (y + lam • w) by abel]
    have hρ : lam * (ρ / lam) = ρ := by field_simp
    rw [hmass _ isOpen_ball, htr, hinv (-y) (L.neg_mem hy) _ measurableSet_ball,
      ← hmass _ isOpen_ball, ← hscale_eq lam hlam w (ρ / lam), hρ]
  -- Step 12: the density ratio of `S` at `y + λw` and radius `ρ > 0` equals that at `w` and
  -- radius `ρ/λ` (cancel `0 < λⁿ < ∞`), and `ρ/λ → 0+` as `ρ → 0+`
  refine ⟨hθ.1, ?_⟩
  have hratio : ∀ ρ : ℝ, 0 < ρ →
      S.massOn (ball (y + lam • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) =
        S.massOn (ball w (ρ / lam)) / (unitBallVolume n * ENNReal.ofReal ((ρ / lam) ^ n)) := by
    intro ρ hρ
    have hρn : ENNReal.ofReal (ρ ^ n) =
        ENNReal.ofReal (lam ^ n) * ENNReal.ofReal ((ρ / lam) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_div_cancel₀ ρ hlam.ne']
    rw [hball ρ, hρn, mul_left_comm, ENNReal.mul_div_mul_left _ _
      (ENNReal.ofReal_pos.2 (pow_pos hlam n)).ne' ENNReal.ofReal_ne_top]
  have hmap : Tendsto (fun ρ : ℝ => ρ / lam) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨?_, eventually_nhdsWithin_of_forall fun ρ hρ => div_pos hρ hlam⟩
    have h0 : Tendsto (fun ρ : ℝ => ρ / lam) (𝓝 0) (𝓝 (0 / lam)) :=
      (continuous_id.div_const lam).tendsto 0
    rw [zero_div] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact (hθ.2.comp hmap).congr' (eventually_nhdsWithin_of_forall fun ρ hρ => (hratio ρ hρ).symm)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
