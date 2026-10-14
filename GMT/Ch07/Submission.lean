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

/-- **Density vanishing off the image** (step 10 of the plane-weight bound).  Let `U ⊆ ℝⁿ` be
open, `u` integrable on `U`, `σ` a finite measure on `ℝᴾ`, `q` continuous, `h ∈ L¹(σ)` and
`σ(Aᶜ) = 0`.  If `∫_U b u = ∫ (b ∘ q) h dσ` for every smooth `b` with compact support in `U`, then
`Lⁿ(B ∩ {u ≠ 0}) ≤ Lⁿ(B ∩ q(A))` for every measurable `B ⊆ U`.  The finite measures
`u⁺Lⁿ⌞U + q_♯(h⁻σ)` and `u⁻Lⁿ⌞U + q_♯(h⁺σ)` agree on smooth tests, hence (smooth cutoffs, dominated
convergence, π-system uniqueness) on Borel subsets of `U`; so `∫_B u = ∫_{q⁻¹(B)} h dσ`, which
vanishes for `B` disjoint from the measurable hull `E` of `q(A)`.  Thus `u = 0` a.e. on `U \ E`
and `Lⁿ(B ∩ E) = Lⁿ(B ∩ q(A))`. -/
theorem Submission.dmcbr_ci_pw_density_null_off_image : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ) (A : Set (Euclid P)), IsOpen U → Continuous q → IntegrableOn u U → σ univ < ∞ → Integrable h σ → σ Aᶜ = 0 → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → volume (B ∩ {y | u y ≠ 0}) ≤ volume (B ∩ q '' A) := by
  have aux_smooth_cutoff_seq : ∀ (n : ℕ) (V : Set (Euclid n)), IsOpen V → ∃ b : ℕ → Euclid n → ℝ, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (b j)) ∧ (∀ j, HasCompactSupport (b j)) ∧ (∀ j, tsupport (b j) ⊆ V) ∧ (∀ j y, 0 ≤ b j y ∧ b j y ≤ 1) ∧ ∀ y, Tendsto (fun j => b j y) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ)) y)) := by
    intro n V hV
    -- Step 1: the compact exhaustion `Kⱼ = {y : infEDist y Vᶜ ≥ 1/(j+1)} ∩ B̄(0, j)` of `V`.
    set K : ℕ → Set (Euclid n) := fun j =>
      {y | ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ} ∩ closedBall 0 j
    have hKc : ∀ j, IsCompact (K j) := fun j =>
      (isCompact_closedBall 0 (j : ℝ)).inter_left (isClosed_le continuous_const continuous_infEDist)
    have hKV : ∀ j, K j ⊆ V := by
      intro j y hy
      by_contra hyV
      have h1 : ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := hy.1
      rw [infEDist_zero_of_mem hyV] at h1
      exact (ENNReal.inv_pos.mpr (by simp)).ne' (le_antisymm h1 bot_le)
    have hKev : ∀ y ∈ V, ∀ᶠ j in atTop, y ∈ K j := by
      intro y hy
      have hpos : 0 < infEDist y Vᶜ := by
        rw [infEDist_pos_iff_notMem_closure, hV.isClosed_compl.closure_eq]
        exact fun h => h hy
      have h1 : ∀ᶠ j : ℕ in atTop, ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y Vᶜ := by
        have ht : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) :=
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by simp
        filter_upwards [ht.eventually (gt_mem_nhds hpos)] with j hj using hj.le
      have h2 : ∀ᶠ j : ℕ in atTop, y ∈ closedBall (0 : Euclid n) j := by
        obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
        filter_upwards [eventually_ge_atTop N] with j hj
        rw [mem_closedBall, dist_zero_right]
        exact hN.trans (by exact_mod_cast hj)
      filter_upwards [h1, h2] with j hj1 hj2 using ⟨hj1, hj2⟩
    -- Step 2: radii `rⱼ > 0` with `cthickening (2 rⱼ) Kⱼ ⊆ V`.
    have hr : ∀ j, ∃ r : ℝ, 0 < r ∧ cthickening (2 * r) (K j) ⊆ V := by
      intro j
      obtain ⟨δ, hδ, hsub⟩ := (hKc j).exists_cthickening_subset_open hV (hKV j)
      exact ⟨δ / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
    choose r hr0 hrV using hr
    -- Step 3: smooth Urysohn functions, `1` exactly on `cthickening rⱼ Kⱼ`, with support
    -- `thickening (2 rⱼ) Kⱼ`.
    have hb : ∀ j, ∃ f : Euclid n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
        support f = thickening (2 * r j) (K j) ∧ ∀ x, x ∈ cthickening (r j) (K j) ↔ f x = 1 :=
      fun j => exists_contDiff_support_eq_eq_one_iff isOpen_thickening isClosed_cthickening
        (cthickening_subset_thickening' (by linarith [hr0 j]) (by linarith [hr0 j]) _)
    choose b hbsmooth hbrange hbsupp hbone using hb
    have htsupp : ∀ j, tsupport (b j) ⊆ cthickening (2 * r j) (K j) := by
      intro j
      rw [tsupport, hbsupp]
      exact closure_thickening_subset_cthickening _ _
    refine ⟨b, hbsmooth,
      fun j => (hKc j).cthickening.of_isClosed_subset (isClosed_tsupport _) (htsupp j),
      fun j => (htsupp j).trans (hrV j), fun j y => hbrange j ⟨y, rfl⟩, fun y => ?_⟩
    -- Step 4: `bⱼ y = 1` for large `j` if `y ∈ V`, and `bⱼ y = 0` for all `j` if `y ∉ V`.
    by_cases hy : y ∈ V
    · rw [indicator_of_mem hy]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hKev y hy] with j hj
      exact ((hbone j y).mp (self_subset_cthickening _ hj)).symm
    · rw [indicator_of_notMem hy]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
      by_contra hne
      exact hy ((htsupp j).trans (hrV j) (subset_tsupport _ (Ne.symm hne)))
  have aux_restrict_eq_of_smooth_test : ∀ (n : ℕ) (U : Set (Euclid n)) (μ ν : Measure (Euclid n)), IsOpen U → IsFiniteMeasure μ → IsFiniteMeasure ν → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y, b y ∂μ = ∫ y, b y ∂ν) → μ.restrict U = ν.restrict U := by
    intro n U μ ν hU hμ hν htest
    -- Step 1: `μ` and `ν` agree on `O ∩ U` for every open `O`, by testing with smooth cutoffs
    -- `bⱼ → 𝟙_{O ∩ U}` and dominated convergence (bound `1`, integrable as the measures are finite).
    have hopen : ∀ O : Set (Euclid n), IsOpen O → μ (O ∩ U) = ν (O ∩ U) := by
      intro O hO
      obtain ⟨b, hbs, hbc, hbt, hb01, hblim⟩ :=
        aux_smooth_cutoff_seq n (O ∩ U) (hO.inter hU)
      have hlim : ∀ ρ : Measure (Euclid n), IsFiniteMeasure ρ →
          Tendsto (fun j => ∫ y, b j y ∂ρ) atTop (𝓝 (ρ.real (O ∩ U))) := by
        intro ρ hρ
        rw [← integral_indicator_one (hO.inter hU).measurableSet]
        refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
          (fun j => (hbs j).continuous.aestronglyMeasurable) (integrable_const 1)
          (fun j => Eventually.of_forall fun y => ?_) (Eventually.of_forall hblim)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hb01 j y).1, (hb01 j y).2]
      have heq : ∀ j, ∫ y, b j y ∂μ = ∫ y, b j y ∂ν := fun j =>
        htest (b j) (hbs j) (hbc j) ((hbt j).trans inter_subset_right)
      have h₁ := hlim μ hμ
      have h₂ := hlim ν hν
      simp_rw [heq] at h₁
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
        (tendsto_nhds_unique h₁ h₂)
    -- Step 2: `μ⌞U` and `ν⌞U` agree on the π-system of open sets, which generates the Borel
    -- σ-algebra, and on `univ`; finite measures agreeing there are equal.
    refine ext_of_generate_finite {s | IsOpen s} BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
    · intro s (hs : IsOpen s)
      rw [Measure.restrict_apply hs.measurableSet, Measure.restrict_apply hs.measurableSet]
      exact hopen s hs
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      simpa using hopen univ isOpen_univ
  have aux_setIntegral_eq_preimage : ∀ (P n : ℕ) (U : Set (Euclid n)) (u : Euclid n → ℝ) (σ : Measure (Euclid P)) (q : Euclid P → Euclid n) (h : Euclid P → ℝ), IsOpen U → Measurable q → IntegrableOn u U → Integrable h σ → (∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U → ∫ y in U, b y * u y = ∫ x, b (q x) * h x ∂σ) → ∀ B : Set (Euclid n), MeasurableSet B → B ⊆ U → ∫ y in B, u y = ∫ x in q ⁻¹' B, h x ∂σ := by
    intro P n U u σ q h hU hq hu hh htest B hB hBU
    -- Step 1: the finite measures `λ± = u± Lⁿ⌞U` and `m± = q_♯(h± σ)`.
    set lp : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (u y)
      with hlp
    set lm : Measure (Euclid n) := (volume.restrict U).withDensity fun y => ENNReal.ofReal (-u y)
      with hlm
    set mp : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (h x)).map q with hmp
    set mm : Measure (Euclid n) := (σ.withDensity fun x => ENNReal.ofReal (-h x)).map q with hmm
    have hlpf : IsFiniteMeasure lp := isFiniteMeasure_withDensity_ofReal hu.2
    have hlmf : IsFiniteMeasure lm := isFiniteMeasure_withDensity_ofReal hu.neg.2
    have hmpf : IsFiniteMeasure mp := by
      have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (h x)) :=
        isFiniteMeasure_withDensity_ofReal hh.2
      exact Measure.isFiniteMeasure_map _ _
    have hmmf : IsFiniteMeasure mm := by
      have : IsFiniteMeasure (σ.withDensity fun x => ENNReal.ofReal (-h x)) :=
        isFiniteMeasure_withDensity_ofReal hh.neg.2
      exact Measure.isFiniteMeasure_map _ _
    -- Step 2: integrals of a function `b` against `λ±` and `m±`.
    have hlam : ∀ (f : Euclid n → ℝ) (b : Euclid n → ℝ), IntegrableOn f U →
        ∫ y, b y ∂((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) =
          ∫ y in U, max (f y) 0 * b y := by
      intro f b hf
      rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aemeasurable.ennreal_ofReal
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    have hpush : ∀ (g : Euclid P → ℝ) (b : Euclid n → ℝ), Integrable g σ → Continuous b →
        ∫ y, b y ∂((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) =
          ∫ x, max (g x) 0 * b (q x) ∂σ := by
      intro g b hg hb
      rw [integral_map hq.aemeasurable hb.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul₀ hg.aemeasurable.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    -- Step 3: `λ₊ + m₋` and `λ₋ + m₊` have the same integral against every test function, since
    -- `u = u⁺ - u⁻`, `h = h⁺ - h⁻` and `∫_U b u = ∫ (b ∘ q) h dσ`.
    have hkey : ∀ b : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ U →
        ∫ y, b y ∂(lp + mm) = ∫ y, b y ∂(lm + mp) := by
      intro b hb hbc hbU
      have hbcont : Continuous b := hb.continuous
      obtain ⟨C, hC⟩ := hbcont.bounded_above_of_compact_support hbc
      have hbm : AEStronglyMeasurable b (volume.restrict U) := hbcont.aestronglyMeasurable
      have hbqm : AEStronglyMeasurable (fun x => b (q x)) σ :=
        (hbcont.measurable.comp hq).aestronglyMeasurable
      rw [integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
          (hbcont.integrable_of_hasCompactSupport hbc),
        integral_add_measure (hbcont.integrable_of_hasCompactSupport hbc)
          (hbcont.integrable_of_hasCompactSupport hbc),
        hlam u b hu, hlam (fun y => -u y) b hu.neg, hpush h b hh hbcont,
        hpush (fun x => -h x) b hh.neg hbcont]
      have I1 : (∫ y in U, max (u y) 0 * b y) - ∫ y in U, max (-u y) 0 * b y =
          ∫ y in U, b y * u y := by
        have hsub := integral_sub (hu.pos_part.mul_bdd hbm (Eventually.of_forall hC))
          (hu.neg_part.mul_bdd hbm (Eventually.of_forall hC))
        refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
        simp only
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
      have I2 : ∫ x, max (h x) 0 * b (q x) ∂σ - ∫ x, max (-h x) 0 * b (q x) ∂σ =
          ∫ x, b (q x) * h x ∂σ := by
        have hsub := integral_sub (hh.pos_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
          (hh.neg_part.mul_bdd hbqm (Eventually.of_forall fun x => hC (q x)))
        refine hsub.symm.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
        simp only
        rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
      have := htest b hb hbc hbU
      linarith
    -- Step 4: uniqueness, so the two measures agree on the measurable subset `B` of `U`.
    have hres := aux_restrict_eq_of_smooth_test n U (lp + mm) (lm + mp) hU
      inferInstance inferInstance hkey
    have hBeq : (lp + mm) B = (lm + mp) B := by
      have := congrArg (fun μ : Measure (Euclid n) => μ B) hres
      simpa only [Measure.restrict_apply hB, inter_eq_left.mpr hBU] using this
    -- Step 5: `λ±(B) = ∫⁻_B (±u)⁺` and `m±(B) = ∫⁻_{q⁻¹ B} (±h)⁺ dσ`.
    have hlB : ∀ f : Euclid n → ℝ, ((volume.restrict U).withDensity fun y => ENNReal.ofReal (f y)) B =
        ∫⁻ y in B, ENNReal.ofReal (f y) := by
      intro f
      rw [withDensity_apply _ hB, Measure.restrict_restrict hB, inter_eq_left.mpr hBU]
    have hmB : ∀ g : Euclid P → ℝ, ((σ.withDensity fun x => ENNReal.ofReal (g x)).map q) B =
        ∫⁻ x in q ⁻¹' B, ENNReal.ofReal (g x) ∂σ := by
      intro g
      rw [Measure.map_apply hq hB, withDensity_apply _ (hq hB)]
    -- Step 6: all four values are finite, so the identity of Step 4 passes to real numbers, and
    -- both set integrals are differences of positive and negative parts.
    rw [Measure.add_apply, Measure.add_apply] at hBeq
    have hreal : (lp B).toReal + (mm B).toReal = (lm B).toReal + (mp B).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hBeq]
    have hL : ∫ y in B, u y = (lp B).toReal - (lm B).toReal := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hu.mono_set hBU), hlp, hlm, hlB, hlB]
    have hR : ∫ x in q ⁻¹' B, h x ∂σ = (mp B).toReal - (mm B).toReal := by
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh.integrableOn, hmp, hmm, hmB, hmB]
    rw [hL, hR]
    linarith
  intro P n U u σ q h A hU hq hu _hσ hh hA htest B hB hBU
  -- the measurable hull `E` of `q '' A`
  set E : Set (Euclid n) := toMeasurable volume (q '' A) with hE
  have hUE : MeasurableSet (U \ E) := hU.measurableSet.diff (measurableSet_toMeasurable _ _)
  -- `∫_s u = 0` for measurable `s ⊆ U \ E`, because `q ⁻¹' s ⊆ Aᶜ` is `σ`-null
  have hzero : ∀ s : Set (Euclid n), MeasurableSet s → s ⊆ U \ E → ∫ y in s, u y = 0 := by
    intro s hs hsUE
    rw [aux_setIntegral_eq_preimage P n U u σ q h hU hq.measurable hu hh
      htest s hs (hsUE.trans sdiff_subset)]
    refine setIntegral_measure_zero _ (measure_mono_null ?_ hA)
    intro x hx hxA
    exact (hsUE hx).2 (subset_toMeasurable _ _ ⟨x, hxA, rfl⟩)
  -- hence `u = 0` a.e. on `U \ E`
  have hae : u =ᵐ[volume.restrict (U \ E)] 0 :=
    (hu.mono_set sdiff_subset).ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => by
      rw [Measure.restrict_restrict hs]
      exact hzero _ (hs.inter hUE) inter_subset_right
  have hnull : volume ({y | u y ≠ 0} ∩ (U \ E)) = 0 := by
    rw [← Measure.restrict_apply' hUE]
    exact hae
  -- `B ∩ {u ≠ 0} ⊆ (B ∩ E) ∪ ({u ≠ 0} ∩ (U \ E))` and `Lⁿ(B ∩ E) = Lⁿ(B ∩ q '' A)`
  calc volume (B ∩ {y | u y ≠ 0})
      ≤ volume (B ∩ E ∪ {y | u y ≠ 0} ∩ (U \ E)) := by
        refine measure_mono fun y hy => ?_
        by_cases hyE : y ∈ E
        · exact Or.inl ⟨hy.1, hyE⟩
        · exact Or.inr ⟨hy.2, hBU hy.1, hyE⟩
    _ ≤ volume (B ∩ E) + volume ({y | u y ≠ 0} ∩ (U \ E)) := measure_union_le _ _
    _ = volume (B ∩ q '' A) := by
        rw [hnull, add_zero, inter_comm, hE,
          Measure.measure_toMeasurable_inter_of_sFinite hB, inter_comm]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
