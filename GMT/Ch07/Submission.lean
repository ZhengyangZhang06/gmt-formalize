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

/-- **Normalized `C¹` bump** in a given open interval.  For `c < d` there is a `C¹` function
`χ : ℝ → ℝ` with `spt χ ⊆ (c, d)` and `∫ χ = 1`.  With `σ = Real.smoothTransition`,
`m = (c + d)/2`, `ρ = (d − c)/2`, `p = m − ρ/2` and `q = m + ρ/2` (so `c < p < q < d`), the
function `θ(α) = σ((4/ρ)(α − p)) σ((4/ρ)(q − α))` is smooth, nonnegative, vanishes off `[p, q]`
and has `θ(m) = 1`, so `∫ θ > 0`; take `χ = (∫ θ)⁻¹ θ`. -/
theorem Submission.idtp_cse_ah_normalized_bump : ∀ c d : ℝ, c < d → ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ tsupport χ ⊆ Ioo c d ∧ ∫ α, χ α = 1 := by
  intro c d hcd
  -- `c < p < m < q < d` with `m = (c + d)/2`, `ρ = (d - c)/2`, `p = m - ρ/2`, `q = m + ρ/2`
  set ρ : ℝ := (d - c) / 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; linarith
  set m : ℝ := (c + d) / 2 with hm_def
  set p : ℝ := m - ρ / 2 with hp_def
  set q : ℝ := m + ρ / 2 with hq_def
  have hcp : c < p := by rw [hp_def, hm_def, hρ_def]; linarith
  have hqd : q < d := by rw [hq_def, hm_def, hρ_def]; linarith
  -- `θ(α) = σ((4/ρ)(α - p)) σ((4/ρ)(q - α))`, `σ = Real.smoothTransition`
  set θ : ℝ → ℝ := fun α =>
    Real.smoothTransition (4 / ρ * (α - p)) * Real.smoothTransition (4 / ρ * (q - α)) with hθ_def
  have hθ_diff : ContDiff ℝ 1 θ := by
    have h₁ : ContDiff ℝ 1 fun α : ℝ => Real.smoothTransition (4 / ρ * (α - p)) :=
      Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
    have h₂ : ContDiff ℝ 1 fun α : ℝ => Real.smoothTransition (4 / ρ * (q - α)) :=
      Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
    exact h₁.mul h₂
  have hθ_nonneg : 0 ≤ θ := fun α =>
    mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  -- `θ` vanishes off `[p, q]`
  have hθ_supp : support θ ⊆ Icc p q := by
    intro α hα
    rw [mem_support] at hα
    by_contra h
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    apply hα
    rcases h with h | h
    · have h' : 4 / ρ * (α - p) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      simp only [hθ_def, Real.smoothTransition.zero_of_nonpos h', zero_mul]
    · have h' : 4 / ρ * (q - α) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
      simp only [hθ_def, Real.smoothTransition.zero_of_nonpos h', mul_zero]
  have hθ_tsupp : tsupport θ ⊆ Icc p q := closure_minimal hθ_supp isClosed_Icc
  have hθ_cpt : HasCompactSupport θ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport θ) hθ_tsupp
  -- `θ(m) = 1`
  have hθm : θ m = 1 := by
    have h₁ : 4 / ρ * (m - p) = 2 := by rw [hp_def]; field_simp; ring
    have h₂ : 4 / ρ * (q - m) = 2 := by rw [hq_def]; field_simp; ring
    simp only [hθ_def, h₁, h₂, Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2),
      mul_one]
  -- `∫ θ > 0`; normalize
  have hI : 0 < ∫ α, θ α :=
    hθ_diff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hθ_cpt hθ_nonneg
      (x := m) (by rw [hθm]; exact one_ne_zero)
  refine ⟨fun α => (∫ α, θ α)⁻¹ * θ α, contDiff_const.mul hθ_diff, ?_, ?_⟩
  · exact tsupport_mul_subset_right.trans (hθ_tsupp.trans (Icc_subset_Ioo hcp hqd))
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hI.ne'
/-- **Smooth plateaus converge weakly to `1_{(p, q)}`.**  For real `p, q` the `C¹` functions
`χ_k(α) = σ(k(α - p)) σ(k(q - α))`, `σ = Real.smoothTransition`, satisfy `0 ≤ χ_k ≤ 1` and vanish
off `(p, q)`, so `tsupport χ_k ⊆ [p, q]`; for `p < α < q`, `χ_k(α) = 1` once
`k ≥ max (1/(α - p)) (1/(q - α))`.  Dominated convergence with bound `|g|` then gives
`∫ χ_k g → ∫_{(p, q)} g` for every integrable `g`. -/
theorem Submission.idtp_cse_ah_cst_plateau_weak_limit : ∀ p q : ℝ, ∃ χ : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ 1 (χ k)) ∧ (∀ k, tsupport (χ k) ⊆ Icc p q) ∧ ∀ g : ℝ → ℝ, Integrable g → Tendsto (fun k => ∫ α, χ k α * g α) atTop (𝓝 (∫ α in Ioo p q, g α)) := by
  intro p q
  -- `χ_k(α) = σ(k(α - p)) σ(k(q - α))`, with `σ` the smooth transition from `0` (on `(-∞, 0]`)
  -- to `1` (on `[1, ∞)`)
  have hzero : ∀ (k : ℕ) (α : ℝ), α ∉ Ioo p q →
      Real.smoothTransition (k * (α - p)) * Real.smoothTransition (k * (q - α)) = 0 := by
    intro k α hα
    rcases not_and_or.1 hα with h | h
    · rw [Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg (sub_nonpos.2 (not_lt.1 h))), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos k.cast_nonneg (sub_nonpos.2 (not_lt.1 h))), mul_zero]
  refine ⟨fun k α => Real.smoothTransition (k * (α - p)) * Real.smoothTransition (k * (q - α)),
    fun k => ?_, fun k => ?_, fun g hg => ?_⟩
  · exact (Real.smoothTransition.contDiff.comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
      (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))
  · -- `χ_k` vanishes off `(p, q)`, so its closed support lies in `[p, q]`
    exact closure_minimal (fun α hα => Ioo_subset_Icc_self (by_contra fun h => hα (hzero k α h)))
      isClosed_Icc
  · -- dominated convergence with bound `|g|`, the limit being `1_{(p, q)} g`
    rw [← integral_indicator measurableSet_Ioo]
    refine tendsto_integral_of_dominated_convergence (fun α => ‖g α‖) (fun k => ?_) hg.norm
      (fun k => Eventually.of_forall fun α => ?_) (Eventually.of_forall fun α => ?_)
    · exact (((Real.smoothTransition.continuous.comp (continuous_const.mul
        (continuous_id.sub continuous_const))).mul (Real.smoothTransition.continuous.comp
        (continuous_const.mul (continuous_const.sub continuous_id)))).aestronglyMeasurable).mul
        hg.aestronglyMeasurable
    · -- `0 ≤ χ_k ≤ 1`
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.nonneg _))]
      exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
        (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)
    · by_cases hα : α ∈ Ioo p q
      · -- `χ_k(α) = 1` once `k ≥ max (1/(α - p)) (1/(q - α))`
        rw [indicator_of_mem hα]
        obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / (α - p)) (1 / (q - α)))
        have hp : 0 < α - p := sub_pos.2 hα.1
        have hq : 0 < q - α := sub_pos.2 hα.2
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with k hk
        have hk' : max (1 / (α - p)) (1 / (q - α)) ≤ k := hN.trans (Nat.cast_le.2 hk)
        have h1 : 1 ≤ (k : ℝ) * (α - p) := by
          have := (le_max_left _ _).trans hk'
          rwa [div_le_iff₀ hp] at this
        have h2 : 1 ≤ (k : ℝ) * (q - α) := by
          have := (le_max_right _ _).trans hk'
          rwa [div_le_iff₀ hq] at this
        rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, one_mul,
          one_mul]
      · -- `χ_k(α) = 0` for every `k`
        rw [indicator_of_notMem hα]
        simp only [hzero _ α hα, zero_mul]
        exact tendsto_const_nhds
/-- Vanishing integrals over rational subintervals force a.e. vanishing: if `w` is integrable on
`(c, d)` and `∫_{(p, q)} w = 0` for all rationals `c < p < q < d`, then `w = 0` a.e. on `(c, d)`.
Extend `w` by zero to `w̄ = 𝟙_{(c, d)} w`.  The primitive `W x = ∫_c^x w̄` is continuous and
constant on the dense set `(c, d) ∩ ℚ`, hence `W ≡ W c = 0` on `[c, d]`; so the averages of `w̄`
over `[x - ρ, x + ρ] ⊆ [c, d]` vanish, and Lebesgue differentiation gives `w x = w̄ x = 0` for
a.e. `x ∈ (c, d)`. -/
theorem Submission.idtp_cse_ah_cst_ae_zero_of_rat_intervals : ∀ (c d : ℝ) (w : ℝ → ℝ), IntegrableOn w (Ioo c d) → (∀ p q : ℚ, c < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < d → ∫ α in Ioo (p : ℝ) (q : ℝ), w α = 0) → ∀ᵐ α, α ∈ Ioo c d → w α = 0 := by
  intro c d w hw hrat
  -- Step 0: if `d ≤ c` the interval is empty and the claim is vacuous.
  rcases le_or_gt d c with hdc | hcd
  · exact Eventually.of_forall fun α hα => absurd (hα.1.trans hα.2) (not_lt.mpr hdc)
  -- Step 1: the extension `w̄ = 𝟙_{(c, d)} w` by zero is integrable on `ℝ`.
  set wb : ℝ → ℝ := (Ioo c d).indicator w with hwb
  have hwbi : Integrable wb := hw.integrable_indicator measurableSet_Ioo
  have hwb_rat : ∀ p q : ℚ, c < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < d →
      ∫ α in Ioo (p : ℝ) (q : ℝ), wb α = 0 := by
    intro p q hcp hpq hqd
    rw [← hrat p q hcp hpq hqd]
    exact setIntegral_congr_fun measurableSet_Ioo fun α hα =>
      indicator_of_mem (show α ∈ Ioo c d from ⟨hcp.trans hα.1, hα.2.trans hqd⟩) w
  -- Step 2: the primitive `W x = ∫_c^x w̄` is continuous and `W q = W p` for rationals.
  set W : ℝ → ℝ := fun x => ∫ t in c..x, wb t with hW
  have hWc : Continuous W :=
    intervalIntegral.continuous_primitive (fun _ _ => hwbi.intervalIntegrable) c
  have hWsub : ∀ a b : ℝ, W b - W a = ∫ t in a..b, wb t := fun a b =>
    intervalIntegral.integral_interval_sub_left hwbi.intervalIntegrable hwbi.intervalIntegrable
  have hWrat : ∀ p q : ℚ, c < (p : ℝ) → (p : ℝ) < (q : ℝ) → (q : ℝ) < d → W q = W p := by
    intro p q hcp hpq hqd
    have h := hWsub p q
    rw [intervalIntegral.integral_of_le hpq.le, integral_Ioc_eq_integral_Ioo,
      hwb_rat p q hcp hpq hqd] at h
    linarith
  -- Step 3: `W` is constant on the dense set `(c, d) ∩ ℚ`, hence `W ≡ W c = 0` on `[c, d]`.
  obtain ⟨q₀, hcq₀, hq₀d⟩ := exists_rat_btwn hcd
  have hWS : ∀ r : ℚ, c < (r : ℝ) → (r : ℝ) < d → W r = W q₀ := by
    intro r hcr hrd
    rcases lt_trichotomy (r : ℝ) (q₀ : ℝ) with h | h | h
    · exact (hWrat r q₀ hcr h hq₀d).symm
    · rw [h]
    · exact hWrat q₀ r hcq₀ h hrd
  have hSsub : Ioo c d ∩ range ((↑) : ℚ → ℝ) ⊆ Icc c d := fun x hx =>
    Ioo_subset_Icc_self hx.1
  have hclos : Icc c d ⊆ closure (Ioo c d ∩ range ((↑) : ℚ → ℝ)) := by
    have h : Ioo c d ⊆ closure (Ioo c d ∩ range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
    rw [← closure_Ioo hcd.ne]
    exact closure_minimal h isClosed_closure
  have hEq : EqOn W (fun _ => W q₀) (Icc c d) := by
    refine EqOn.of_subset_closure ?_ hWc.continuousOn continuousOn_const hSsub hclos
    rintro x ⟨hxJ, r, rfl⟩
    exact hWS r hxJ.1 hxJ.2
  have hWq₀ : W q₀ = 0 := by
    have h := hEq (left_mem_Icc.mpr hcd.le)
    simp only [hW, intervalIntegral.integral_same] at h
    exact h.symm
  have hW0 : ∀ x ∈ Icc c d, W x = 0 := fun x hx => (hEq hx).trans hWq₀
  -- Step 4: Lebesgue differentiation for `w̄` along closed balls centred at `x`.
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hwbi.locallyIntegrable 1]
    with x hx hxJ
  have hlim : Tendsto (fun ρ => ⨍ y in closedBall x ρ, wb y) (𝓝[>] 0) (𝓝 (wb x)) := by
    refine hx (fun _ => x) id tendsto_id ?_
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    exact mem_closedBall_self (by rw [one_mul]; exact le_of_lt hρ)
  -- Step 5: the averages vanish for `0 < ρ < min (x - c) (d - x)`.
  have hm : 0 < min (x - c) (d - x) := lt_min (sub_pos.mpr hxJ.1) (sub_pos.mpr hxJ.2)
  have hzero : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ⨍ y in closedBall x ρ, wb y = 0 := by
    filter_upwards [Ioo_mem_nhdsGT hm] with ρ hρ
    have h1 : c ≤ x - ρ := by linarith [min_le_left (x - c) (d - x), hρ.2]
    have h2 : x + ρ ≤ d := by linarith [min_le_right (x - c) (d - x), hρ.2]
    have hle : x - ρ ≤ x + ρ := by linarith [hρ.1]
    rw [setAverage_eq, Real.closedBall_eq_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, ← hWsub, hW0 _ ⟨by linarith, h2⟩,
      hW0 _ ⟨h1, by linarith⟩, sub_zero, smul_zero]
  have hwbx : wb x = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun ρ hρ => hρ.symm))
  rwa [hwb, indicator_of_mem hxJ] at hwbx
/-- **Reduction of a product-tested integral to one variable** (step 7 of the `α`-homogeneity
rigidity at the edge of a planar sector of a 2-dimensional minimizing cone, Simon 7.3.3).  If
`H(p) = h(p.1)` for a.e. `p ∈ O = (a, b) × (c, d)`, `f = 0` off `(a, b)`, `ψ₀ = 0` off `(c, d)`
and `∫ ψ₀ = 1`, then `∫ f(p.1) ψ₀(p.2) H(p) dp = ∫ f h`.  The integrand vanishes off `O` and
equals `(f h)(p.1) ψ₀(p.2)` a.e. on `O`; `setIntegral_prod_mul` (no integrability needed) factors
the box integral as `(∫_{(a,b)} f h) (∫_{(c,d)} ψ₀)`, and both factors are whole-line integrals. -/
theorem Submission.idtp_cse_ah_product_integral_reduce : ∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ) (h f ψ₀ : ℝ → ℝ), (∀ᵐ p : ℝ × ℝ, p ∈ Ioo a b ×ˢ Ioo c d → H p = h p.1) → (∀ t, t ∉ Ioo a b → f t = 0) → (∀ α, α ∉ Ioo c d → ψ₀ α = 0) → ∫ α, ψ₀ α = 1 → ∫ p : ℝ × ℝ, f p.1 * ψ₀ p.2 * H p = ∫ t, f t * h t := by
  intro a b c d H h f ψ₀ hH hf hψ hψ1
  -- step 1: the integrand vanishes off the box `O = (a, b) × (c, d)`
  have hvan : ∀ p : ℝ × ℝ, p ∉ Ioo a b ×ˢ Ioo c d → f p.1 * ψ₀ p.2 * H p = 0 := by
    intro p hp
    rcases not_and_or.mp hp with hp1 | hp2
    · rw [hf _ hp1, zero_mul, zero_mul]
    · rw [hψ _ hp2, mul_zero, zero_mul]
  -- step 2: on `O`, `H p = h p.1` almost everywhere
  have hO : ∫ p in Ioo a b ×ˢ Ioo c d, f p.1 * ψ₀ p.2 * H p =
      ∫ p in Ioo a b ×ˢ Ioo c d, f p.1 * h p.1 * ψ₀ p.2 := by
    refine setIntegral_congr_ae (measurableSet_Ioo.prod measurableSet_Ioo) ?_
    filter_upwards [hH] with p hp hpO
    rw [hp hpO, mul_right_comm]
  -- step 3: `volume = volume.prod volume` on `ℝ × ℝ`, and the box integral factors
  have hprod : ∫ p in Ioo a b ×ˢ Ioo c d, f p.1 * h p.1 * ψ₀ p.2 =
      (∫ t in Ioo a b, f t * h t) * ∫ α in Ioo c d, ψ₀ α := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod_mul (fun t => f t * h t) ψ₀ (Ioo a b) (Ioo c d)
  -- step 4: both factors are whole-line integrals, and `∫ ψ₀ = 1`
  have hfh : ∀ t, t ∉ Ioo a b → f t * h t = 0 := fun t ht => by rw [hf t ht, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan, hO, hprod,
    setIntegral_eq_integral_of_forall_compl_eq_zero hψ, hψ1, mul_one,
    setIntegral_eq_integral_of_forall_compl_eq_zero hfh]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

/-- Test functions for the `α`-independence step of the cone-sector endpoint density argument
(Simon 7.3.3): the primitive of a mean-zero continuous test function is a `C¹` test function.
Let `ψ(x) = ∫_c^x g`, so `ψ' = g` by the fundamental theorem of calculus and `ψ` is `C¹`.  If
`spt g ≠ ∅`, let `p = min spt g` and `q = max spt g`, so `c < p ≤ q < d`.  Then `ψ = 0` on
`(-∞, p)`, as `g` vanishes between `c` and `x`, and `ψ(x) = ∫ g = 0` for `x > q`.  Hence
`spt ψ ⊆ [p, q] ⊆ (c, d)`. -/
theorem Submission.idtp_cse_ah_antiderivative_test : ∀ (c d : ℝ) (g : ℝ → ℝ), Continuous g → tsupport g ⊆ Ioo c d → ∫ α, g α = 0 → ∃ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ ∧ tsupport ψ ⊆ Ioo c d ∧ deriv ψ = g := by
  intro c d g hg hgcd hg0
  -- step 3: `ψ(x) = ∫_c^x g` has derivative `g x` at every `x` (FTC for the continuous `g`)
  have hψ : ∀ x, HasDerivAt (fun y => ∫ α in c..y, g α) (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable c x)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have hdψ : deriv (fun y => ∫ α in c..y, g α) = g := funext fun x => (hψ x).deriv
  -- step 4: `ψ` is differentiable with continuous derivative `g`, hence `C¹`
  refine ⟨fun y => ∫ α in c..y, g α,
    contDiff_one_iff_deriv.2 ⟨fun x => (hψ x).differentiableAt, hdψ.symm ▸ hg⟩, ?_, hdψ⟩
  -- step 2: if `spt g = ∅`, then `g = 0` and `ψ = 0`
  rcases (tsupport g).eq_empty_or_nonempty with he | hne
  · obtain rfl := tsupport_eq_empty_iff.1 he
    simp
  -- step 1: `spt g` is a closed subset of `[c, d]`, hence compact; `p = min spt g` and
  -- `q = max spt g` lie in `spt g ⊆ (c, d)`, and `g = 0` off `[p, q]`
  have hK : IsCompact (tsupport g) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (hgcd.trans Ioo_subset_Icc_self)
  have hp := hgcd (hK.sInf_mem hne)
  have hq := hgcd (hK.sSup_mem hne)
  have hpq : sInf (tsupport g) ≤ sSup (tsupport g) := csInf_le hK.bddBelow (hK.sSup_mem hne)
  have hgpq : ∀ α ∉ Icc (sInf (tsupport g)) (sSup (tsupport g)), g α = 0 := fun α hα =>
    image_eq_zero_of_notMem_tsupport fun h =>
      hα ⟨csInf_le hK.bddBelow h, le_csSup hK.bddAbove h⟩
  -- step 6: `spt ψ ⊆ [p, q] ⊆ (c, d)`, once `ψ = 0` off `[p, q]`
  refine (closure_minimal (support_subset_iff'.2 fun x hx => ?_) isClosed_Icc).trans
    (Icc_subset_Ioo hp.1 hq.2)
  show ∫ α in c..x, g α = 0
  -- step 5: `ψ = 0` off `[p, q]`
  rcases not_and_or.1 hx with hx | hx <;> rw [not_le] at hx
  · -- `x < p`: `g` vanishes on `Ι c x`, which lies left of `p`
    refine intervalIntegral.integral_zero_ae
      (Eventually.of_forall fun α hα => hgpq α fun h => ?_)
    exact lt_irrefl _ ((h.1.trans hα.2).trans_lt (max_lt hp.1 hx))
  · -- `x > q`: `ψ(x) = ∫_{(c, x]} g = ∫ g = 0`, as `g` vanishes off `[p, q] ⊆ (c, x]`
    rw [intervalIntegral.integral_of_le (hp.1.trans_le (hpq.trans hx.le)).le,
      setIntegral_eq_integral_of_forall_compl_eq_zero, hg0]
    exact fun α hα => hgpq α fun h => hα ⟨hp.1.trans_le h.1, h.2.trans hx.le⟩
/-- **Product-tested vanishing forces a.e. vanishing of slice integrals** (step 2 of the
`α`-homogeneity step in the cone-sector endpoint density argument for Simon 7.3.3).  Let
`I = (a, b)`, `J = (c, d)`, `H` integrable on `I × J` and `g` continuous with `tsupport g ⊆ J`.
If `∫ g(α) l(t) H(t, α) = 0` for every `C¹` function `l` with `tsupport l ⊆ I`, then
`Φ(t) = ∫_J g(α) H(t, α) dα` vanishes for a.e. `t ∈ I`.  As `g` is bounded, `g(α) H(t, α)` is
integrable for `vol|I ⊗ vol|J = vol|(I × J)` and `Φ` is integrable on `I` (Fubini).  The test
integrand vanishes off `I × J`, so Fubini turns the hypothesis into `∫ l Φ = 0` for every smooth
`l` with compact support in `I`, and the fundamental lemma on the open set `I` applies. -/
theorem Submission.idtp_cse_ah_slice_integral_ae_zero : ∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ) (g : ℝ → ℝ), IntegrableOn H (Ioo a b ×ˢ Ioo c d) → Continuous g → tsupport g ⊆ Ioo c d → (∀ l : ℝ → ℝ, ContDiff ℝ 1 l → tsupport l ⊆ Ioo a b → ∫ p : ℝ × ℝ, g p.2 * l p.1 * H p = 0) → ∀ᵐ t, t ∈ Ioo a b → ∫ α in Ioo c d, g α * H (t, α) = 0 := by
  intro a b c d H g hH hg hgs htest
  -- step 1: `H` is integrable for `μ.prod ν`, `μ = vol|I`, `ν = vol|J`
  have hH' : Integrable H ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hH
  -- step 2: `g` is bounded, so `K(t, α) = g α * H (t, α)` is integrable for `μ.prod ν`
  have hgc : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) (hgs.trans Ioo_subset_Icc_self)
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg
  have hK : Integrable (fun p : ℝ × ℝ => g p.2 * H p)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) :=
    hH'.bdd_mul (hg.comp continuous_snd).aestronglyMeasurable (Eventually.of_forall fun p => hM p.2)
  -- step 3: `Φ(t) = ∫_J g α H(t, α) dα` is integrable on `I` (Fubini)
  have hΦ : IntegrableOn (fun t => ∫ α in Ioo c d, g α * H (t, α)) (Ioo a b) := hK.integral_prod_left
  -- step 5: the fundamental lemma on the open interval `I`
  refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hΦ.locallyIntegrableOn
    fun l hl hlc hls => ?_
  -- step 4: `∫ l Φ = ∫_{I × J} g(p.2) l(p.1) H(p) = ∫_{ℝ²} g(p.2) l(p.1) H(p) = 0`
  obtain ⟨L, hL⟩ := hlc.exists_bound_of_continuous hl.continuous
  have hl0 : ∀ t ∉ Ioo a b, l t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hls h)
  have hg0 : ∀ α ∉ Ioo c d, g α = 0 := fun α hα => image_eq_zero_of_notMem_tsupport fun h => hα (hgs h)
  have hlK : Integrable (fun p : ℝ × ℝ => g p.2 * l p.1 * H p)
      ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) :=
    (hK.bdd_mul (f := fun p => l p.1) (hl.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hL p.1)).congr (Eventually.of_forall fun p => by ring)
  rw [← htest l (hl.of_le (by exact_mod_cast le_top)) hls,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b) fun t ht => by
      rw [hl0 t ht, zero_smul],
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b ×ˢ Ioo c d) fun p hp => by
      rcases not_and_or.mp hp with hp | hp
      · rw [hl0 _ hp, mul_zero, zero_mul]
      · rw [hg0 _ hp, zero_mul, zero_mul],
    Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hlK]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun α => ?_)
  simp only
  ring
/-- **Countable separating `C¹` tests on an interval** (replaces the separability of `C([−s, s])`
in the `α`-homogeneity step of the cone-sector endpoint density argument for Simon 7.3.3).  For
reals `c, d` there are `C¹` functions `Fₙ` with `tsupport Fₙ ⊆ (c, d)` such that every `w`
integrable on `(c, d)` with `∫ Fₙ w = 0` for all `n` vanishes a.e. on `(c, d)`.  Enumerate the
triples `(p, q, k) ∈ ℚ × ℚ × ℕ` by a surjection `e : ℕ → ℚ × ℚ × ℕ`, and let `Fₙ` be the `k`-th
`C¹` plateau `χ_{p,q,k}` (`tsupport ⊆ [p, q]`) if `c < p < q < d`, and `0` otherwise.  For such
`p, q` the plateaus vanish off `(c, d)`, so with `w̄ = 1_{(c,d)} w` integrable,
`∫_{(p,q)} w = ∫_{(p,q)} w̄ = lim_k ∫ χ_{p,q,k} w̄ = lim_k ∫ χ_{p,q,k} w = 0`; vanishing on all
rational subintervals gives `w = 0` a.e. on `(c, d)`. -/
theorem Submission.idtp_cse_ah_countable_separating_tests : ∀ c d : ℝ, ∃ F : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 1 (F n)) ∧ (∀ n, tsupport (F n) ⊆ Ioo c d) ∧ ∀ w : ℝ → ℝ, IntegrableOn w (Ioo c d) → (∀ n, ∫ α, F n α * w α = 0) → ∀ᵐ α, α ∈ Ioo c d → w α = 0 := by
  intro c d
  classical
  -- plateaus `χ p q k`: `C¹`, `tsupport ⊆ [p, q]`, and `∫ χ p q k · g → ∫_{(p,q)} g`
  choose χ hχC hχS hχT using Submission.idtp_cse_ah_cst_plateau_weak_limit
  -- an enumeration `e` of the triples `(p, q, k)`; `A t` says `c < p < q < d`
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ × ℚ × ℕ)
  let A : ℚ × ℚ × ℕ → Prop := fun t => c < (t.1 : ℝ) ∧ (t.1 : ℝ) < t.2.1 ∧ (t.2.1 : ℝ) < d
  refine ⟨fun n => if A (e n) then χ (e n).1 (e n).2.1 (e n).2.2 else 0, fun n => ?_, fun n => ?_,
    ?_⟩
  · dsimp only
    split_ifs
    · exact hχC _ _ _
    · exact contDiff_zero_fun
  -- `tsupport Fₙ ⊆ [p, q] ⊆ (c, d)`, or `Fₙ = 0`
  · dsimp only
    split_ifs with h
    · exact (hχS _ _ _).trans (Icc_subset_Ioo h.1 h.2.2)
    · simp
  -- it suffices that `∫_{(p,q)} w = 0` for rationals `c < p < q < d`
  · intro w hw hF
    refine Submission.idtp_cse_ah_cst_ae_zero_of_rat_intervals c d w hw fun p q hcp hpq hqd => ?_
    have hg : Integrable ((Ioo c d).indicator w) := hw.integrable_indicator measurableSet_Ioo
    -- `∫ χ p q k · w̄ = ∫ Fₙ w = 0` for `e n = (p, q, k)`, since `χ p q k = 0` off `(c, d)`
    have hzero : ∀ k, ∫ α, χ p q k α * (Ioo c d).indicator w α = 0 := by
      intro k
      obtain ⟨n, hn⟩ := he (p, q, k)
      have hA : A (e n) := by rw [hn]; exact ⟨hcp, hpq, hqd⟩
      have h := hF n
      dsimp only at h
      rw [ite_eq_left hA, hn] at h
      rw [← h]
      congr 1
      funext α
      by_cases hα : α ∈ Ioo c d
      · rw [indicator_of_mem hα]
      · have hα' : α ∉ tsupport (χ p q k) :=
          fun h' => hα ((hχS _ _ _).trans (Icc_subset_Ioo hcp hqd) h')
        simp [image_eq_zero_of_notMem_tsupport hα']
    -- so `∫_{(p,q)} w̄ = lim_k ∫ χ p q k · w̄ = 0`, and `w̄ = w` on `(p, q)`
    have hlim := hχT p q _ hg
    simp only [hzero] at hlim
    rw [← tendsto_nhds_unique hlim tendsto_const_nhds]
    exact (setIntegral_congr_fun measurableSet_Ioo fun α hα =>
      indicator_of_mem (Ioo_subset_Ioo hcp.le hqd.le hα) w).symm

/-- **Slices are a.e. constant** (one-variable du Bois-Reymond lemma, with a parameter).  Let
`I = (a, b)`, `J = (c, d)` with `c < d`, and let `H` be integrable on `I × J` with
`∫ ψ′(α) l(t) H(t, α) = 0` for all `C¹` functions `ψ`, `l` supported in `J`, `I`.  Fix a normalized
`C¹` bump `χ` and a countable separating family `F n` of `C¹` tests in `J`.  Then
`g n = F n − (∫ F n) χ` has mean zero, so `g n = ψ n′` with `ψ n ∈ C¹` supported in `J`, and the
hypothesis gives `∫_J g n H(t, ·) = 0` for a.e. `t ∈ I`.  By Fubini the slice `H(t, ·)` is
integrable on `J` for a.e. `t ∈ I`.  For such `t`, `w = H(t, ·) − ∫_J χ H(t, ·)` is integrable on
`J` and satisfies `∫ F n w = 0` for all `n`, so `w = 0` a.e. on `J`. -/
theorem Submission.idtp_cse_ah_slice_ae_const : ∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ), c < d → IntegrableOn H (Ioo a b ×ˢ Ioo c d) → (∀ ψ l : ℝ → ℝ, ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo c d → tsupport l ⊆ Ioo a b → ∫ p : ℝ × ℝ, deriv ψ p.2 * l p.1 * H p = 0) → ∀ᵐ t, t ∈ Ioo a b → ∃ k : ℝ, ∀ᵐ α, α ∈ Ioo c d → H (t, α) = k := by
  intro a b c d H hcd hH hweak
  -- Step 1: the normalized bump `χ` and the separating family `F n`, all supported in `J`; they
  -- are continuous with compact support, hence integrable, bounded and zero off `J`
  obtain ⟨χ, hχ_diff, hχ_supp, hχ_int⟩ := Submission.idtp_cse_ah_normalized_bump c d hcd
  obtain ⟨F, hF_diff, hF_supp, hF_sep⟩ := Submission.idtp_cse_ah_countable_separating_tests c d
  have hJ_cpt : ∀ f : ℝ → ℝ, tsupport f ⊆ Ioo c d → HasCompactSupport f := fun f hf =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) (hf.trans Ioo_subset_Icc_self)
  have hJ_zero : ∀ f : ℝ → ℝ, tsupport f ⊆ Ioo c d → ∀ α, α ∉ Ioo c d → f α = 0 :=
    fun f hf α hα => image_eq_zero_of_notMem_tsupport fun h => hα (hf h)
  have hχ_integrable : Integrable χ :=
    hχ_diff.continuous.integrable_of_hasCompactSupport (hJ_cpt χ hχ_supp)
  have hF_integrable : ∀ n, Integrable (F n) := fun n =>
    (hF_diff n).continuous.integrable_of_hasCompactSupport (hJ_cpt (F n) (hF_supp n))
  obtain ⟨Cχ, hCχ⟩ := hχ_diff.continuous.bounded_above_of_compact_support (hJ_cpt χ hχ_supp)
  choose CF hCF using fun n =>
    (hF_diff n).continuous.bounded_above_of_compact_support (hJ_cpt (F n) (hF_supp n))
  -- Step 2: `g n = F n - (∫ F n) χ` is continuous, supported in `J` and of mean zero, so it is
  -- the derivative of some `ψ n ∈ C¹` supported in `J`
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ → ℝ, ∀ n, g n = fun α => F n α - (∫ β, F n β) * χ α :=
    ⟨_, fun _ => rfl⟩
  have hg_cont : ∀ n, Continuous (g n) := fun n => by
    rw [hg n]
    exact (hF_diff n).continuous.sub (continuous_const.mul hχ_diff.continuous)
  have hg_supp : ∀ n, tsupport (g n) ⊆ Ioo c d := fun n => by
    rw [hg n]
    exact (tsupport_sub _ _).trans (union_subset (hF_supp n)
      ((tsupport_mul_subset_right (f := fun _ => ∫ β, F n β) (g := χ)).trans hχ_supp))
  have hg_mean : ∀ n, ∫ α, g n α = 0 := fun n => by
    rw [hg n, integral_sub (hF_integrable n) (hχ_integrable.const_mul _), integral_const_mul, hχ_int,
      mul_one, sub_self]
  choose ψ hψ_diff hψ_supp hψ_deriv using fun n =>
    Submission.idtp_cse_ah_antiderivative_test c d (g n) (hg_cont n) (hg_supp n) (hg_mean n)
  -- Step 3: the hypothesis with `ψ n` gives `∫_J g n H(t, ·) = 0` for a.e. `t ∈ I`
  have hslice : ∀ n, ∀ᵐ t, t ∈ Ioo a b → ∫ α in Ioo c d, g n α * H (t, α) = 0 := fun n =>
    Submission.idtp_cse_ah_slice_integral_ae_zero a b c d H (g n) hH (hg_cont n) (hg_supp n)
      fun l hl_diff hl_supp => by
        have h := hweak (ψ n) l (hψ_diff n) hl_diff (hψ_supp n) hl_supp
        rwa [hψ_deriv n] at h
  -- Step 4: Fubini; for a.e. `t ∈ I` the slice `H(t, ·)` is integrable on `J`
  have hH' : Integrable H ((volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hH
  have hslice_int : ∀ᵐ t, t ∈ Ioo a b → IntegrableOn (fun α => H (t, α)) (Ioo c d) :=
    (ae_restrict_iff' measurableSet_Ioo).mp hH'.prod_right_ae
  -- Step 5: intersect the countably many full-measure sets and fix a good `t`
  filter_upwards [ae_all_iff.mpr hslice, hslice_int] with t ht hti htI
  have hHt : Integrable (fun α => H (t, α)) (volume.restrict (Ioo c d)) := hti htI
  -- Step 6: `w = H(t, ·) - k` with `k = ∫_J χ H(t, ·)` is integrable on `J` and `∫ F n w = 0`
  set k : ℝ := ∫ α in Ioo c d, χ α * H (t, α)
  refine ⟨k, ?_⟩
  have hw_int : IntegrableOn (fun α => H (t, α) - k) (Ioo c d) :=
    hHt.sub (integrableOn_const measure_Ioo_lt_top.ne)
  have hFH_int : ∀ n, Integrable (fun α => F n α * H (t, α)) (volume.restrict (Ioo c d)) :=
    fun n => hHt.bdd_mul (hF_diff n).continuous.aestronglyMeasurable
      (Eventually.of_forall (hCF n))
  have hχH_int : Integrable (fun α => χ α * H (t, α)) (volume.restrict (Ioo c d)) :=
    hHt.bdd_mul hχ_diff.continuous.aestronglyMeasurable (Eventually.of_forall hCχ)
  have hw_zero : ∀ n, ∫ α, F n α * (H (t, α) - k) = 0 := by
    intro n
    have h₁ : ∫ α, F n α * (H (t, α) - k) = ∫ α in Ioo c d, F n α * (H (t, α) - k) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun α hα => by
        rw [hJ_zero (F n) (hF_supp n) α hα, zero_mul]).symm
    have h₂ : ∫ α in Ioo c d, F n α * (H (t, α) - k) =
        (∫ α in Ioo c d, F n α * H (t, α)) - (∫ α in Ioo c d, F n α) * k := by
      simp_rw [mul_sub]
      rw [integral_sub (hFH_int n) ((hF_integrable n).integrableOn.mul_const k), integral_mul_const]
    have h₃ : ∫ α in Ioo c d, g n α * H (t, α) =
        (∫ α in Ioo c d, F n α * H (t, α)) - (∫ β, F n β) * k := by
      simp_rw [hg n, sub_mul, mul_assoc]
      rw [integral_sub (hFH_int n) (hχH_int.const_mul _), integral_const_mul]
    have h₄ : ∫ α in Ioo c d, F n α = ∫ α, F n α :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (hJ_zero (F n) (hF_supp n))
    rw [h₁, h₂, h₄, ← h₃]
    exact ht n htI
  -- Step 7: the separating property of `F n` gives `w = 0` a.e. on `J`
  filter_upwards [hF_sep (fun α => H (t, α) - k) hw_int hw_zero] with α hα hαJ
  exact sub_eq_zero.mp (hα hαJ)
/-- **Fibrewise a.e. constancy gives the product form** (steps 1 and 6 of the `α`-homogeneity
step in the cone-sector endpoint density argument for Simon 7.3.3).  Let `c < d`, `I = (a, b)`,
`J = (c, d)` and `H` integrable on `I × J`.  If for a.e. `t ∈ I` the slice `H(t, ·)` equals a
constant `k_t` a.e. on `J`, then `H(t, α) = (d − c)⁻¹ ∫_J H(t, ·)` for a.e. `(t, α) ∈ I × J`.
Lebesgue measure on `I × J` is `μ.prod ν` with `μ = vol|I`, `ν = vol|J`.  Take a strongly
measurable `H̃ = H` a.e.; then `h̃(t) = (d − c)⁻¹ ∫_J H̃(t, ·)` is measurable and equals the slice
average `h(t)` for a.e. `t`.  As `vol J = d − c`, `k_t = h(t)`.  So the measurable set
`{H̃ = h̃ ∘ fst}` has a.e.-full sections and is conull, and `fst` carries `h̃ = h` back to the
product. -/
theorem Submission.idtp_cse_ah_ae_eq_slice_average : ∀ (a b c d : ℝ) (H : ℝ × ℝ → ℝ), c < d → IntegrableOn H (Ioo a b ×ˢ Ioo c d) → (∀ᵐ t, t ∈ Ioo a b → ∃ k : ℝ, ∀ᵐ α, α ∈ Ioo c d → H (t, α) = k) → ∀ᵐ p : ℝ × ℝ, p ∈ Ioo a b ×ˢ Ioo c d → H p = (d - c)⁻¹ * ∫ α in Ioo c d, H (p.1, α) := by
  intro a b c d H hcd hH hk
  -- step 1: `vol|(I × J) = (vol|I).prod (vol|J)`, so `H` is integrable for the product measure
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) =
      (volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [IntegrableOn, hprod] at hH
  refine (ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)).1 ?_
  rw [hprod]
  -- a strongly measurable representative `H̃ = H` a.e.
  obtain ⟨H', hH'm, hHH'⟩ := hH.aestronglyMeasurable
  -- step 2: `h̃(t) = (d - c)⁻¹ ∫_J H̃(t, ·)` is strongly measurable
  have hh'm : StronglyMeasurable fun t => (d - c)⁻¹ * ∫ β in Ioo c d, H' (t, β) :=
    hH'm.integral_prod_right'.const_mul _
  -- step 3: `h̃ = h` for a.e. `t ∈ I`
  have hhh' : ∀ᵐ t ∂volume.restrict (Ioo a b), (d - c)⁻¹ * ∫ β in Ioo c d, H' (t, β) =
      (d - c)⁻¹ * ∫ β in Ioo c d, H (t, β) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hHH'] with t ht
    rw [integral_congr_ae ht]
  -- step 4: for a.e. `t ∈ I`, `H(t, ·)` is a.e. on `J` its constant `k_t`, which is the average
  have hslice : ∀ᵐ t ∂volume.restrict (Ioo a b), ∀ᵐ α ∂volume.restrict (Ioo c d),
      H (t, α) = (d - c)⁻¹ * ∫ β in Ioo c d, H (t, β) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).2 hk] with t ⟨k, hk⟩
    rw [← ae_restrict_iff' measurableSet_Ioo] at hk
    rw [integral_congr_ae hk, setIntegral_const, Real.volume_real_Ioo_of_le hcd.le, smul_eq_mul,
      inv_mul_cancel_left₀ (sub_pos.2 hcd).ne']
    exact hk
  -- steps 5, 6: `{H̃ = h̃ ∘ fst}` is measurable with a.e.-full sections, hence conull
  have hE : MeasurableSet {p : ℝ × ℝ | H' p = (d - c)⁻¹ * ∫ β in Ioo c d, H' (p.1, β)} :=
    hH'm.measurableSet_eq_fun (hh'm.comp_measurable measurable_fst)
  have h6 : ∀ᵐ p ∂(volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)),
      H' p = (d - c)⁻¹ * ∫ β in Ioo c d, H' (p.1, β) := by
    refine (Measure.ae_prod_iff_ae_ae hE).2 ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hHH', hslice, hhh'] with t h1 h2 h3
    filter_upwards [h1, h2] with α h1 h2
    exact h1.symm.trans (h2.trans h3.symm)
  -- step 7: `h̃ ∘ fst = h ∘ fst` a.e., as `fst` is quasi-measure-preserving
  have h7 : ∀ᵐ p ∂(volume.restrict (Ioo a b)).prod (volume.restrict (Ioo c d)),
      (d - c)⁻¹ * ∫ β in Ioo c d, H' (p.1, β) = (d - c)⁻¹ * ∫ β in Ioo c d, H (p.1, β) :=
    Measure.quasiMeasurePreserving_fst.ae hhh'
  -- step 8: `H = H̃ = h̃ ∘ fst = h ∘ fst` a.e.
  filter_upwards [hHH', h6, h7] with p h1 h2 h3
  exact h1.trans (h2.trans h3)

end GMT.Ch07
