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

/-- **Smooth pull-backs and the homotopy formula on forms** (Simon 6.2.23–6.2.26, dual form).
(a) The pull-back `Φ^#α(x) = α(Φ x) ∘ DΦ(x)` of a smooth form by a `C^∞` map is smooth.
(b) Let `F, G` be `C^∞`, `h(t, x) = F x + t(G x - F x)` the affine homotopy (6.2.26) and `ω` a
smooth `(k+1)`-form.  Then `Kω(x) = ∫₀¹ (ι_{G x - F x} ω(h(t, x))) ∘ D_x h(t, x) dt` is smooth and
`G^#ω - F^#ω = d(Kω) + K(dω)`, the homotopy formula 6.2.25 tested on `ω`.  The precomposition
`L ↦ (γ ↦ γ ∘ L)` is analytic, which gives (a).  For (b) we work on a proper normed space `E`:
with `H = h` on `ℝ × E`, `Θ = H^#ω` and `e = (1, 0)`, `dΘ = H^#(dω)` and Cartan's formula
`d(ι_e Θ) + ι_e dΘ = DΘ[e]` hold; pulling back by `y ↦ (t, y)` turns `ι_e Θ` and `ι_e dΘ` into the
integrands of `Kω` and `K(dω)` and `DΘ[e]` into `∂_t (h_t^#ω)`.  Integrating over `t ∈ [0, 1]`
and differentiating under the integral sign gives the formula. -/
theorem Submission.dor_lmb_fcdp_smooth_homotopy : (∀ (N N' m : ℕ) (Φ : Euclid N → Euclid N') (α : DifferentialForm (Euclid N') m), ContDiff ℝ (⊤ : ℕ∞) Φ → IsSmoothForm α → IsSmoothForm (fun x => (α (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x))) ∧ ∀ (P k : ℕ) (F G : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1, ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧ ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) - (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) = exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1, ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x + ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
  -- the pull-back `x ↦ α(x) ∘ L(x)` is `C^∞` when `α` and `L` are, as `L ↦ (γ ↦ γ ∘ L)` is analytic
  have hpb : ∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
      [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
      (m : ℕ) (α : E₁ → E₂ [⋀^Fin m]→L[ℝ] ℝ) (L : E₁ → E₃ →L[ℝ] E₂),
      ContDiff ℝ (⊤ : ℕ∞) α → ContDiff ℝ (⊤ : ℕ∞) L →
        ContDiff ℝ (⊤ : ℕ∞) (fun x => (α x).compContinuousLinearMap (L x)) := by
    intro E₁ E₂ E₃ _ _ _ _ _ _ m α L hα hL
    have hΨ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E₃ →L[ℝ] E₂) → (E₂ [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] (E₃ [⋀^Fin m]→L[ℝ] ℝ)) :=
      (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
    exact (hΨ.comp hL).clm_apply hα
  -- (a) `Φ^#α(x) = α(Φ x) ∘ DΦ(x)`
  refine ⟨fun N N' m Φ α hΦ hα => hpb (Euclid N) (Euclid N') (Euclid N) m (fun x => α (Φ x))
    (fderiv ℝ Φ) (hα.comp hΦ) (contDiff_infty_iff_fderiv.mp hΦ).2, ?_⟩
  -- (b) on an abstract proper normed space `E`, then for `E = ℝᴾ`
  suffices key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (k : ℕ)
      (F G : E → E) (ω : DifferentialForm E (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1,
        ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧
      ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) -
        (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) =
        exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1,
          ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap
            (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x +
        ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft
          (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) by
    intro P k F G ω hF hG hω
    exact key (Euclid P) k F G ω hF hG hω
  intro E _ _ _ k F G ω hF hG hω
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω := hω
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hr : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hF1 : Differentiable ℝ F := hF.differentiable hne
  have hG1 : Differentiable ℝ G := hG.differentiable hne
  have hω1 : Differentiable ℝ ω := hωs.differentiable hne
  -- `γ ↦ γ.curryLeft` is a linear isometry, hence `C^∞`
  have hcl : ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] (m : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) (fun γ : E₁ [⋀^Fin (m + 1)]→L[ℝ] ℝ => γ.curryLeft) := by
    intro E₁ _ _ m
    have h := LinearIsometry.contDiff (𝕜 := ℝ) (E := E₁ [⋀^Fin (m + 1)]→L[ℝ] ℝ)
      (F := E₁ →L[ℝ] E₁ [⋀^Fin m]→L[ℝ] ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      ContinuousAlternatingMap.curryLeftLI
    exact h
  -- differentiation under the integral sign: `D_x ∫₀¹ f(t, x) dt = ∫₀¹ Df(t, x) ∘ J dt`, `J = inr`,
  -- with the bound `sup ‖Df ∘ J‖` over the compact set `[0, 1] × B̄(x₀, 1)`
  have hpar : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (f : ℝ × E → Y), ContDiff ℝ (⊤ : ℕ∞) f → ∀ x₀ : E,
      HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, f (t, x))
        (∫ t in (0 : ℝ)..1, (fderiv ℝ f (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x₀ := by
    intro Y _ _ _ f hf x₀
    have : SecondCountableTopologyEither ℝ (E →L[ℝ] Y) := ⟨Or.inl inferInstance⟩
    have hf1 : Differentiable ℝ f := hf.differentiable hne
    have hDf : Continuous (fun p : ℝ × E => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
      (hf.continuous_fderiv hne).clm_comp continuous_const
    have hjt : ∀ x : E, Continuous (fun t : ℝ => ((t, x) : ℝ × E)) :=
      fun x => continuous_id.prodMk continuous_const
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
      (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn hDf.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => f (t, x))
      (F' := fun x t => (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (bound := fun _ => C) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x => (hf.continuous.comp (hjt x)).aestronglyMeasurable)
      ((hf.continuous.comp (hjt x₀)).intervalIntegrable 0 1)
      (hDf.comp (hjt x₀)).aestronglyMeasurable ?_ intervalIntegrable_const ?_
    · rw [ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun t ht x hx => hC (t, x) ⟨?_, ?_⟩
      · rw [uIoc_of_le zero_le_one] at ht
        exact Ioc_subset_Icc_self ht
      · exact ball_subset_closedBall hx
    · exact Eventually.of_forall fun t x _ =>
        (hf1 (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- `x ↦ ∫₀¹ f(t, x) dt` is `C^n` for every `n`, by induction (for all `Y` at once)
  have hsm : ∀ (n : ℕ) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (f : ℝ × E → Y), ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, f (t, x)) := by
    intro n
    induction n with
    | zero =>
      intro Y _ _ _ f hf
      rw [Nat.cast_zero, contDiff_zero]
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => f (t, x)) (hf.continuous.comp continuous_swap) 0 1
    | succ n ih =>
      intro Y _ _ _ f hf
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ t in (0 : ℝ)..1, (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E),
        ih (E →L[ℝ] Y) (fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E))
          ((contDiff_infty_iff_fderiv.mp hf).2.clm_comp contDiff_const), hpar Y f hf⟩
  have hcc : ∀ (m : ℕ) (g : Covector E m) (L : ℝ × E →L[ℝ] E) (L' : E →L[ℝ] ℝ × E),
      (g.compContinuousLinearMap L).compContinuousLinearMap L' =
        g.compContinuousLinearMap (L.comp L') := fun _ _ _ _ => rfl
  -- the homotopy `H(t, y) = F y + t • (G y - F y)` on `ℝ × E`: `DH(t, y) e = G y - F y` for
  -- `e = (1, 0)`, and `DH(t, y) ∘ J = DF y + t • (DG y - DF y)`
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × E → E, H = fun p => F p.2 + p.1 • (G p.2 - F p.2) := ⟨_, rfl⟩
  have hHapp : ∀ (t : ℝ) (y : E), H (t, y) = F y + t • (G y - F y) := fun t y => by rw [hHdef]
  have hHs : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [hHdef]
    exact (hF.comp contDiff_snd).add
      (contDiff_fst.smul ((hG.comp contDiff_snd).sub (hF.comp contDiff_snd)))
  have hH1 : Differentiable ℝ H := hHs.differentiable hne
  have hDHe : ∀ (t : ℝ) (y : E), fderiv ℝ H (t, y) (1, 0) = G y - F y := by
    intro t y
    have h1 : HasDerivAt (fun s : ℝ => H (s, y)) (fderiv ℝ H (t, y) (1, 0)) t :=
      (hH1 (t, y)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    have h2 := ((hasDerivAt_id' t).smul_const (G y - F y)).const_add (F y)
    rw [one_smul] at h2
    simp only [← hHapp] at h2
    exact h1.unique h2
  have hDHJ : ∀ (t : ℝ) (y : E), (fderiv ℝ H (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      fderiv ℝ F y + t • (fderiv ℝ G y - fderiv ℝ F y) := by
    intro t y
    have h1 : HasFDerivAt (fun y' : E => H (t, y'))
        ((fderiv ℝ H (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
      (hH1 (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
    have h2 : HasFDerivAt (fun y' : E => F y' + t • (G y' - F y'))
        (fderiv ℝ F y + t • (fderiv ℝ G y - fderiv ℝ F y)) y :=
      (hF1 y).hasFDerivAt.add (((hG1 y).hasFDerivAt.sub (hF1 y).hasFDerivAt).const_smul t)
    simp only [← hHapp] at h2
    exact h1.unique h2
  -- `Θ = H^#ω` is `C^∞` with `dΘ = H^#(dω)`, and `ι_e Θ` is `C^∞`
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : DifferentialForm (ℝ × E) (k + 1),
      Θ = fun p => (ω (H p)).compContinuousLinearMap (fderiv ℝ H p) := ⟨_, rfl⟩
  have hΘs : ContDiff ℝ (⊤ : ℕ∞) Θ := by
    rw [hΘdef]
    exact hpb (ℝ × E) E (ℝ × E) (k + 1) (fun p => ω (H p)) (fderiv ℝ H) (hωs.comp hHs)
      (contDiff_infty_iff_fderiv.mp hHs).2
  have hΘ1 : Differentiable ℝ Θ := hΘs.differentiable hne
  have hdΘ : ∀ p, extDeriv Θ p = (extDeriv ω (H p)).compContinuousLinearMap (fderiv ℝ H p) := by
    intro p
    rw [hΘdef]
    exact extDeriv_pullback (hω1 (H p)) hHs.contDiffAt hr
  obtain ⟨ιΘ, hιΘdef⟩ : ∃ ιΘ : DifferentialForm (ℝ × E) k,
      ιΘ = fun p => (Θ p).curryLeft (1, 0) := ⟨_, rfl⟩
  have hιΘs : ContDiff ℝ (⊤ : ℕ∞) ιΘ := by
    rw [hιΘdef]
    exact ((hcl (ℝ × E) k).comp hΘs).clm_apply contDiff_const
  have hιΘ1 : Differentiable ℝ ιΘ := hιΘs.differentiable hne
  -- the integrands `κ` of `Kω` and `κd` of `K(dω)` are `ι_e Θ ∘ J` and `ι_e dΘ ∘ J`
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ × E → Covector E k, κ = fun p =>
      ((ω (F p.2 + p.1 • (G p.2 - F p.2))).curryLeft (G p.2 - F p.2)).compContinuousLinearMap
        (fderiv ℝ F p.2 + p.1 • (fderiv ℝ G p.2 - fderiv ℝ F p.2)) := ⟨_, rfl⟩
  have hκapp : ∀ (t : ℝ) (x : E), κ (t, x) =
      ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := fun t x => by rw [hκdef]
  obtain ⟨κd, hκddef⟩ : ∃ κd : ℝ × E → Covector E (k + 1), κd = fun p =>
      ((extDeriv ω (F p.2 + p.1 • (G p.2 - F p.2))).curryLeft
        (G p.2 - F p.2)).compContinuousLinearMap
        (fderiv ℝ F p.2 + p.1 • (fderiv ℝ G p.2 - fderiv ℝ F p.2)) := ⟨_, rfl⟩
  have hκdapp : ∀ (t : ℝ) (x : E), κd (t, x) =
      ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft
        (G x - F x)).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := fun t x => by rw [hκddef]
  have hκeq : ∀ (t : ℝ) (y : E),
      (ιΘ (t, y)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) = κ (t, y) := by
    intro t y
    rw [hκapp, hιΘdef, hΘdef]
    simp only [ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDHe, hcc, hDHJ, hHapp]
  have hκdeq : ∀ (t : ℝ) (y : E), ((extDeriv Θ (t, y)).curryLeft (1, 0)).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E) = κd (t, y) := by
    intro t y
    rw [hκddef, hdΘ]
    simp only [ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDHe, hcc, hDHJ, hHapp]
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := by
    have hκfun : κ = fun p => (ιΘ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) :=
      funext fun p => (hκeq p.1 p.2).symm
    rw [hκfun]
    exact hpb (ℝ × E) (ℝ × E) E k ιΘ (fun _ => ContinuousLinearMap.inr ℝ ℝ E) hιΘs contDiff_const
  -- `Kω` is `C^∞`
  simp only [← hκapp, ← hκdapp]
  refine ⟨contDiff_infty.mpr fun n => hsm n _ κ hκs, fun x => ?_⟩
  -- Cartan's formula for the constant field `e`: `d(ι_e Θ) + ι_e dΘ = DΘ[e]`
  have hcartan : ∀ p, extDeriv ιΘ p + (extDeriv Θ p).curryLeft (1, 0) = fderiv ℝ Θ p (1, 0) := by
    intro p
    ext v
    have h0 : Fin.removeNth 0 (Matrix.vecCons ((1 : ℝ), (0 : E)) v) = v := by simp
    have hs : ∀ i : Fin (k + 1), Fin.removeNth i.succ (Matrix.vecCons ((1 : ℝ), (0 : E)) v) =
        Matrix.vecCons ((1 : ℝ), (0 : E)) (Fin.removeNth i v) :=
      fun i => Fin.cons_comp_succ_succAbove _ v i
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      extDeriv_apply (hιΘ1 p), extDeriv_apply (hΘ1 p), Fin.sum_univ_succ (n := k + 1)]
    simp only [hιΘdef, ContinuousAlternatingMap.curryLeft_apply_apply, h0, hs, Fin.val_zero,
      pow_zero, one_smul, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_succ]
    rw [fderiv_continuousAlternatingMap_apply_const_apply (hΘ1 p), add_left_comm,
      ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
    intro i _
    rw [pow_succ, mul_neg_one, neg_smul, add_neg_cancel]
  -- pulling back by `y ↦ (t, y)`: `d(κ(t, ·))(x) = d(ι_e Θ)(t, x) ∘ J`
  have hj : ∀ (t : ℝ) (y : E),
      fderiv ℝ (fun y' : E => ((t, y') : ℝ × E)) y = ContinuousLinearMap.inr ℝ ℝ E :=
    fun t y => (hasFDerivAt_prodMk_right t y).fderiv
  have hpull : ∀ t : ℝ, extDeriv (fun x' => κ (t, x')) x =
      (extDeriv ιΘ (t, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro t
    have h := extDeriv_pullback (ω := ιΘ) (f := fun y' : E => ((t, y') : ℝ × E)) (x := x)
      (hιΘ1 (t, x)) (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
        (fun y' : E => ((t, y') : ℝ × E))).contDiffAt hr
    simp only [hj, hκeq] at h
    exact h
  -- `Θ ∘ J` is `C^∞` with `D(Θ ∘ J)[e] = DΘ[e] ∘ J = d(κ(t, ·))(x) + κd(t, x)` at `(t, x)`
  have hΘ's : ContDiff ℝ (⊤ : ℕ∞)
      (fun p => (Θ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E)) :=
    hpb (ℝ × E) (ℝ × E) E (k + 1) Θ (fun _ => ContinuousLinearMap.inr ℝ ℝ E) hΘs contDiff_const
  have hΘ'1 : Differentiable ℝ
      (fun p => (Θ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E)) :=
    hΘ's.differentiable hne
  have hΘ'e : ∀ p, fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) p (1, 0) =
      (fderiv ℝ Θ p (1, 0)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro p
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ← fderiv_continuousAlternatingMap_apply_const_apply (hΘ'1 p),
      ← fderiv_continuousAlternatingMap_apply_const_apply (hΘ1 p)]
    rfl
  have hpt : ∀ t : ℝ, fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0) =
      extDeriv (fun x' => κ (t, x')) x + κd (t, x) := by
    intro t
    rw [hΘ'e, ← hcartan, hpull, ← hκdeq]
    ext v
    rfl
  -- the fundamental theorem of calculus for `t ↦ Θ(t, x) ∘ J`
  have hjt : Continuous (fun t : ℝ => ((t, x) : ℝ × E)) := continuous_id.prodMk continuous_const
  have hc1 : Continuous (fun t : ℝ => fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0)) :=
    ((hΘ's.continuous_fderiv hne).comp hjt).clm_apply continuous_const
  have hβd : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (Θ (s, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E))
      (fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
        (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0)) t := by
    intro t
    have h := (hΘ'1 (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hβd t)
    (hc1.intervalIntegrable 0 1)
  -- `d(Kω)(x) = ∫₀¹ d(κ(t, ·))(x) dt`, as `d = alternatizeUncurryFin ∘ D` with a CLM
  have hκ1 : Differentiable ℝ κ := hκs.differentiable hne
  have hκt : ∀ t : ℝ, fderiv ℝ (fun x' => κ (t, x')) x =
      (fderiv ℝ κ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    fun t => ((hκ1 (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hc3 : Continuous (fun t : ℝ => (fderiv ℝ κ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
    ((hκs.continuous_fderiv hne).comp hjt).clm_comp continuous_const
  have hi3 := Continuous.intervalIntegrable (E := E →L[ℝ] Covector E k) (μ := volume) hc3 0 1
  have hc4 : Continuous (fun t : ℝ => extDeriv (fun x' => κ (t, x')) x) := by
    simp only [extDeriv, hκt]
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).continuous.comp hc3
  have hc2 : Continuous (fun t : ℝ => κd (t, x)) := by
    refine (hc1.sub hc4).congr fun t => ?_
    simp only [Pi.sub_apply]
    rw [hpt t, add_sub_cancel_left]
  have hdK : extDeriv (fun x' => ∫ t in (0 : ℝ)..1, κ (t, x')) x =
      ∫ t in (0 : ℝ)..1, extDeriv (fun x' => κ (t, x')) x := by
    simp only [extDeriv, hκt]
    rw [(hpar _ κ hκs x).fderiv]
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
      (E := E →L[ℝ] Covector E k) (F := Covector E (k + 1))
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) hi3
    exact hcomm.symm
  -- `Θ(1, x) ∘ J = G^#ω(x)` and `Θ(0, x) ∘ J = F^#ω(x)`
  have hβ : ∀ t : ℝ, (Θ (t, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (F x + t • (G x - F x))).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
    intro t
    rw [hΘdef]
    simp only [hcc, hDHJ, hHapp]
  have hβ1 : (Θ (1, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) := by
    rw [hβ, one_smul, one_smul, add_sub_cancel, add_sub_cancel]
  have hβ0 : (Θ (0, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
    rw [hβ, zero_smul ℝ (G x - F x), zero_smul ℝ (fderiv ℝ G x - fderiv ℝ F x), add_zero,
      add_zero]
  -- `G^#ω - F^#ω = ∫₀¹ (d(κ(t, ·))(x) + κd(t, x)) dt = d(Kω)(x) + K(dω)(x)`
  show (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) -
      (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) =
    extDeriv (fun x' => ∫ t in (0 : ℝ)..1, κ (t, x')) x + ∫ t in (0 : ℝ)..1, κd (t, x)
  rw [← hβ1, ← hβ0, ← hftc, hdK, ← intervalIntegral.integral_add (hc4.intervalIntegrable 0 1)
    (hc2.intervalIntegrable 0 1)]
  exact intervalIntegral.integral_congr fun t _ => hpt t

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
