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

/-- `Hⁿ(Q ∩ B_ρ(y)) = ωₙρⁿ` for an `n`-dimensional linear subspace `Q` of `ℝᴾ`, `y ∈ Q` and
`ρ > 0` (used in the proof of Simon 7.3.3(1), p. 191, for the density of the planes of a
2-dimensional minimizing cone).  The inclusion `Q → ℝᴾ` is an isometry, so `Q ∩ B_ρ(y)` has the
measure of the ball `B_ρ(y)` of `Q`; on `Q`, `μHE[n]` is the volume, Haar scaling gives
`vol(B_ρ(y)) = ρⁿ vol(B_1(0))`, and orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume, so
`vol(B_1(0)) = ωₙ`. -/
theorem Submission.idtp_tdc_subspace_ball_measure : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (y : Euclid P) (ρ : ℝ), Module.finrank ℝ Q = n → y ∈ Q → 0 < ρ → μHE[n] ((Q : Set (Euclid P)) ∩ ball y ρ) = unitBallVolume n * ENNReal.ofReal (ρ ^ n) := by
  intro P n Q y ρ hn hy hρ
  subst hn
  -- the inclusion `Q → ℝᴾ` is an isometry with range `Q`; `B_ρ(y)` pulls back to the ball of `Q`
  have hball : μHE[Module.finrank ℝ Q] ((Q : Set (Euclid P)) ∩ ball y ρ) =
      μHE[Module.finrank ℝ Q] (ball (⟨y, hy⟩ : Q) ρ) := by
    rw [← isometry_subtype_coe.preimage_ball (⟨y, hy⟩ : Q) ρ,
      isometry_subtype_coe.euclideanHausdorffMeasure_preimage, Subtype.range_coe, Set.inter_comm]
  -- orthonormal coordinates `Q ≃ₗᵢ ℝⁿ` preserve volume and map `B_1(0)` onto `B_1(0)`
  have hunit := (stdOrthonormalBasis ℝ Q).measurePreserving_repr.measure_preimage
    (measurableSet_ball (x := (0 : Euclid (Module.finrank ℝ Q))) (ε := 1)).nullMeasurableSet
  rw [LinearIsometryEquiv.preimage_ball, map_zero] at hunit
  -- `μHE[n] = volume` on `Q`, then Haar scaling of balls
  rw [hball, InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos _ _ hρ, hunit, mul_comm]
  rfl

/-- `Hⁿ({y : y - w ∈ V} ∩ B_R(0)) = ωₙ(√(R² - ‖w‖²))ⁿ` for an `n`-dimensional linear subspace `V`
of `ℝᴾ`, an offset `w ∈ V^⊥` and `‖w‖ < R` (a plane in a ball, used in the proof of Simon 7.2.4,
p. 184, for measures carried by finitely many parallel `n`-planes).  Put `ρ = √(R² - ‖w‖²) > 0`.
By Pythagoras `‖t + w‖² = ‖t‖² + ‖w‖²` for `t ∈ V`, so the translation `t ↦ t + w`, an isometry,
maps `V ∩ B_ρ(0)` onto the set; isometry invariance of `μHE[n]` and the subspace-ball formula
`Hⁿ(V ∩ B_ρ(0)) = ωₙρⁿ` conclude. -/
theorem Submission.cbr_ci_cp_fp_offset_plane_ball_measure : ∀ (P n : ℕ) (V : Submodule ℝ (Euclid P)) (w : Euclid P) (R : ℝ), Module.finrank ℝ V = n → w ∈ Vᗮ → ‖w‖ < R → μHE[n] ({y : Euclid P | y - w ∈ V} ∩ ball 0 R) = unitBallVolume n * ENNReal.ofReal (Real.sqrt (R ^ 2 - ‖w‖ ^ 2) ^ n) := by
  intro P n V w R hn hw hR
  -- the radius `ρ = √(R² - ‖w‖²)` is positive and `ρ² = R² - ‖w‖²`
  have hpos : 0 < R ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hρ : 0 < Real.sqrt (R ^ 2 - ‖w‖ ^ 2) := Real.sqrt_pos.2 hpos
  have hρsq : Real.sqrt (R ^ 2 - ‖w‖ ^ 2) ^ 2 = R ^ 2 - ‖w‖ ^ 2 := Real.sq_sqrt hpos.le
  -- Pythagoras: `‖t + w‖² = ‖t‖² + ‖w‖²` for `t ∈ V`, as `w ⊥ V`
  have hpyth : ∀ t ∈ V, ‖t + w‖ ^ 2 = ‖t‖ ^ 2 + ‖w‖ ^ 2 := fun t ht => by
    rw [sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_real (Submodule.inner_right_of_mem_orthogonal ht hw)
  -- the translation `t ↦ t + w` maps `V ∩ B_ρ(0)` onto `{y | y - w ∈ V} ∩ B_R(0)`
  have himage : (fun t => t + w) '' ((V : Set (Euclid P)) ∩ ball 0 (Real.sqrt (R ^ 2 - ‖w‖ ^ 2))) =
      {y : Euclid P | y - w ∈ V} ∩ ball 0 R := by
    ext y
    simp only [Set.mem_image, Set.mem_inter_iff, SetLike.mem_coe, mem_ball_zero_iff,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ⟨ht, htρ⟩, rfl⟩
      refine ⟨by simpa using ht, ?_⟩
      have h := hpyth t ht
      nlinarith [norm_nonneg t, norm_nonneg w, norm_nonneg (t + w)]
    · rintro ⟨hy, hyR⟩
      refine ⟨y - w, ⟨hy, ?_⟩, sub_add_cancel y w⟩
      have h := hpyth (y - w) hy
      rw [sub_add_cancel] at h
      nlinarith [norm_nonneg (y - w), norm_nonneg y]
  -- isometry invariance of `μHE[n]`, then the subspace-ball formula with centre `0 ∈ V`
  rw [← himage, (isometry_add_right w).euclideanHausdorffMeasure_image]
  exact Submission.idtp_tdc_subspace_ball_measure P n V 0 _ hn V.zero_mem hρ

/-- Weighted parallel `n`-planes with at most Euclidean volume growth have total weight `≤ 1`.
Let `V ⊆ ℝᴾ` be an `n`-dimensional subspace, `Z ⊆ V^⊥` and `a : ℝᴾ → [0, ∞]`.  If
`ν = Σ_{w ∈ Z} a(w) Hⁿ⌞{y : y − w ∈ V}` satisfies `ν(B_R(0)) ≤ ωₙRⁿ` for every `R > 0`, then
`Σ_{w ∈ Z} a(w) ≤ 1`.  For a finite set `s` of offsets put `M = Σ_{z ∈ s} ‖z‖` and let `R > M`.
Each plane `z + V` meets `B_R(0)` in an `n`-ball of radius `√(R² − ‖z‖²) ≥ R − M`, so
`ωₙ(R − M)ⁿ Σ_{z ∈ s} a(z) ≤ ν(B_R(0)) ≤ ωₙRⁿ`, i.e. `Σ_{z ∈ s} a(z) ≤ (R / (R − M))ⁿ`; let
`R → ∞`. -/
theorem Submission.cbr_ci_cp_fp_tsum_weight_le_one : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)) (a : Euclid P → ℝ≥0∞), Module.finrank ℝ V = n → Z ⊆ (Vᗮ : Set (Euclid P)) → ν = Measure.sum (fun w : Z => a w • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume n * ENNReal.ofReal (R ^ n)) → ∑' w : Z, a w ≤ 1 := by
  intro P n ν V Z a hn hZ hν hνR
  -- `0 < ωₙ < ∞`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  -- `ν(B_R(0)) = Σ_{z ∈ Z} a(z) Hⁿ({y : y − z ∈ V} ∩ B_R(0))`
  have hball : ∀ R : ℝ, ν (ball 0 R) =
      ∑' z : Z, a z * μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) := by
    intro R
    rw [hν, Measure.sum_apply _ measurableSet_ball]
    refine tsum_congr fun z => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_ball, inter_comm]
  -- it suffices to bound every finite partial sum; `M` bounds the offsets in `s`
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  obtain ⟨M, hM, hzM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ s, ‖(z : Euclid P)‖ ≤ M :=
    ⟨∑ z ∈ s, ‖(z : Euclid P)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun z hz =>
      Finset.single_le_sum (f := fun z : Z => ‖(z : Euclid P)‖) (fun _ _ => norm_nonneg _) hz⟩
  -- for `R > M`: `Σ_{z ∈ s} a(z) ≤ (R / (R − M))ⁿ`
  have key : ∀ R : ℝ, M < R → ∑ z ∈ s, a z ≤ ENNReal.ofReal ((R / (R - M)) ^ n) := by
    intro R hR
    have hRM : 0 < R - M := sub_pos.mpr hR
    -- each plane meets `B_R(0)` in an `n`-ball of radius `√(R² − ‖z‖²) ≥ R − M`
    have hplane : ∀ z ∈ s, unitBallVolume n * ENNReal.ofReal ((R - M) ^ n) ≤
        μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) := by
      intro z hz
      have hzR := hzM z hz
      have hr : R - M ≤ Real.sqrt (R ^ 2 - ‖(z : Euclid P)‖ ^ 2) := by
        refine Real.le_sqrt_of_sq_le ?_
        nlinarith [mul_nonneg hRM.le hM, mul_nonneg (sub_nonneg.mpr hzR) hM,
          mul_nonneg (sub_nonneg.mpr hzR) (norm_nonneg (z : Euclid P))]
      rw [Submission.cbr_ci_cp_fp_offset_plane_ball_measure P n V z R hn (hZ z.2)
        (hzR.trans_lt hR)]
      gcongr
    have hsum : unitBallVolume n * ((∑ z ∈ s, a z) * ENNReal.ofReal ((R - M) ^ n)) ≤
        unitBallVolume n * ENNReal.ofReal (R ^ n) :=
      calc unitBallVolume n * ((∑ z ∈ s, a z) * ENNReal.ofReal ((R - M) ^ n))
          = ∑ z ∈ s, a z * (unitBallVolume n * ENNReal.ofReal ((R - M) ^ n)) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => mul_left_comm _ _ _
        _ ≤ ∑ z ∈ s, a z * μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) := by
            gcongr with z hz
            exact hplane z hz
        _ ≤ ∑' z : Z, a z * μHE[n] ({y : Euclid P | y - z ∈ V} ∩ ball 0 R) :=
            ENNReal.sum_le_tsum s
        _ = ν (ball 0 R) := (hball R).symm
        _ ≤ unitBallVolume n * ENNReal.ofReal (R ^ n) := hνR R (hM.trans_lt hR)
    have hpow : 0 < (R - M) ^ n := pow_pos hRM n
    rwa [ENNReal.mul_le_mul_iff_right hω0 hωtop,
      ← ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hpow).ne')
        (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_div_of_pos hpow, ← div_pow] at hsum
  -- `(R / (R − M))ⁿ → 1` as `R → ∞`
  have hlim : Tendsto (fun R : ℝ => ENNReal.ofReal ((R / (R - M)) ^ n)) atTop (𝓝 1) := by
    have hsub : Tendsto (fun R : ℝ => R - M) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b + M, fun R hR => by linarith⟩
    have h1 : Tendsto (fun R : ℝ => 1 + M / (R - M)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hsub)
    have h2 : Tendsto (fun R : ℝ => R / (R - M)) atTop (𝓝 1) :=
      h1.congr' ((eventually_gt_atTop M).mono fun R hR => by
        rw [← same_add_div (sub_pos.mpr hR).ne', sub_add_cancel])
    simpa using ENNReal.tendsto_ofReal (h2.pow n)
  exact ge_of_tendsto hlim ((eventually_gt_atTop M).mono key)
/-- A finite sum `ν = ∑ᵢ (αᵢ)₊ Hⁿ⌞(wᵢ + V)` of planes parallel to `V`, with offsets `wᵢ ∈ Vᗮ`,
that charges every ball `B_r(0)` has a plane through `0`: some `wᵢ = 0` (used in the proof that
the limit in Simon 7.2.4 is integer multiplicity, Remark 7.2.5(1)).  Otherwise pick
`0 < r < ‖wᵢ‖` for all `i`; for `y ∈ wᵢ + V`, Pythagoras gives `‖y‖² = ‖y - wᵢ‖² + ‖wᵢ‖² > r²`,
so every plane misses `B_r(0)` and `ν(B_r(0)) = 0`. -/
theorem Submission.cbr_ci_cp_fp_exists_offset_eq_zero : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), (∀ i, w i ∈ Vᗮ) → ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ V} → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → ∃ i, w i = 0 := by
  intro P n ν V N w α hw hν hpos
  by_contra hne
  -- a radius `0 < r < ‖w i‖` for each of the finitely many offsets `w i ≠ 0`
  obtain ⟨r, hr, hrw⟩ : ∃ r : ℝ, 0 < r ∧ ∀ i, r < ‖w i‖ :=
    ((eventually_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0).and
      (eventually_all.2 fun i => nhdsWithin_le_nhds
        (eventually_lt_nhds (norm_pos_iff.2 fun hi => hne ⟨i, hi⟩)))).exists
  -- by Pythagoras (`w i ∈ Vᗮ`), every plane `{y | y - w i ∈ V}` misses `B_r(0)`
  have hmiss : ∀ i, ball (0 : Euclid P) r ∩ {y : Euclid P | y - w i ∈ V} = ∅ := by
    intro i
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hy, ht⟩ => ?_
    rw [mem_ball_zero_iff] at hy
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real
      (Submodule.inner_right_of_mem_orthogonal (show y - w i ∈ V from ht) (hw i))
    rw [sub_add_cancel] at hpyth
    have hlt : ‖y‖ < ‖w i‖ := hy.trans (hrw i)
    nlinarith [norm_nonneg y, mul_self_nonneg ‖y - w i‖]
  -- hence `ν(B_r(0)) = 0`, contradicting the positivity hypothesis
  have hzero : ν (ball 0 r) = 0 := by
    rw [hν, Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_ball, hmiss i, measure_empty,
      smul_zero]
  exact (hpos r hr).ne' hzero

/-- Let `ν = Σ_{w ∈ Z} a(w) Hⁿ⌞{y : y − w ∈ V}` be a sum of parallel translates of the `n`-plane
`V`, with offsets `Z ⊆ V^⊥` and weights `a(w) ≥ c > 0`.  If `ν(B_R(0)) ≤ ωₙRⁿ` for all `R > 0`
and `ν(B_r(0)) > 0` for all `r > 0`, then `ν = Σᵢ αᵢ Hⁿ⌞{y : y − wᵢ ∈ V}` for finitely many
distinct `wᵢ ∈ V^⊥` and `αᵢ ≥ c` with `Σᵢ αᵢ ≤ 1` and some `wᵢ = 0` (the constant-plane step
of the closure argument for Simon 7.2.4).  The growth bound gives `Σ_{w ∈ Z} a(w) ≤ 1`, so `Z`
is finite; enumerating `Z` gives the finite sum, and positivity near `0` forces a plane through
`0`. -/
theorem Submission.cbr_ci_cp_finite_parallel_planes : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Submodule ℝ (Euclid P)) (Z : Set (Euclid P)) (a : Euclid P → ℝ≥0∞) (c : ℝ), 0 < c → Module.finrank ℝ V = n → Z ⊆ (Vᗮ : Set (Euclid P)) → (∀ w ∈ Z, ENNReal.ofReal c ≤ a w) → ν = Measure.sum (fun w : Z => a w • (μHE[n]).restrict {y : Euclid P | y - w ∈ V}) → (∀ R : ℝ, 0 < R → ν (ball 0 R) ≤ unitBallVolume n * ENNReal.ofReal (R ^ n)) → (∀ r : ℝ, 0 < r → 0 < ν (ball 0 r)) → ∃ (N : ℕ) (w : Fin N → Euclid P) (α : Fin N → ℝ), Injective w ∧ (∀ i, w i ∈ Vᗮ) ∧ (∀ i, c ≤ α i) ∧ ∑ i, α i ≤ 1 ∧ (∃ i, w i = 0) ∧ ν = ∑ i, ENNReal.ofReal (α i) • (μHE[n]).restrict {y : Euclid P | y - w i ∈ V} := by
  intro P n ν V Z a c hc hn hZ ha hν hgrowth hpos
  -- the total weight is at most `1`
  have htsum : ∑' w : Z, a w ≤ 1 :=
    Submission.cbr_ci_cp_fp_tsum_weight_le_one P n ν V Z a hn hZ hν hgrowth
  -- every weight is at least `ofReal c ≠ 0`, so `Z` is finite
  have hZfin : Finite Z := by
    by_contra hinf
    have : Infinite Z := not_finite_iff_infinite.1 hinf
    have hle : ∑' _ : Z, ENNReal.ofReal c ≤ ∑' w : Z, a w :=
      ENNReal.tsum_le_tsum fun w => ha w w.2
    rw [ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_pos.2 hc).ne'] at hle
    exact ENNReal.one_ne_top (top_le_iff.1 (hle.trans htsum))
  have : Fintype Z := Fintype.ofFinite Z
  -- every weight is finite
  have hfin : ∀ w : Z, a w ≠ ∞ := fun w =>
    ne_top_of_le_ne_top ENNReal.one_ne_top ((ENNReal.le_tsum w).trans htsum)
  -- enumerate `Z` as `w₁, …, w_N` and put `αᵢ := a(wᵢ)`
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card Z) ≃ Z) := ⟨(Fintype.equivFin Z).symm⟩
  have hw : ∀ i, (e i : Euclid P) ∈ Vᗮ := fun i => hZ (e i).2
  have hνsum : ν = ∑ i, ENNReal.ofReal (a (e i)).toReal •
      (μHE[n]).restrict {y : Euclid P | y - (e i : Euclid P) ∈ V} := by
    rw [hν, Measure.sum_fintype, ← e.sum_comp]
    exact Finset.sum_congr rfl fun i _ => by rw [ENNReal.ofReal_toReal (hfin (e i))]
  refine ⟨Fintype.card Z, fun i => e i, fun i => (a (e i)).toReal,
    Subtype.val_injective.comp e.injective, hw,
    fun i => (ENNReal.ofReal_le_iff_le_toReal (hfin (e i))).1 (ha _ (e i).2), ?_,
    Submission.cbr_ci_cp_fp_exists_offset_eq_zero P n ν V (Fintype.card Z) (fun i => e i)
      (fun i => (a (e i)).toReal) hw hνsum hpos, hνsum⟩
  -- `Σᵢ αᵢ = (Σ_{w ∈ Z} a(w)).toReal ≤ 1`
  rw [tsum_fintype] at htsum
  rw [← ENNReal.toReal_sum fun i _ => hfin (e i), e.sum_comp (fun w : Z => a w)]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top htsum).trans_eq ENNReal.toReal_one

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
