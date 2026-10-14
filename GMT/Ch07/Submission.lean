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

/-- **Support calculus** for currents in `ℝᴾ` (Simon 6.2.11): (i) if `E` is closed and `X(ω) = 0`
whenever `spt ω ∩ E = ∅`, then `spt X ⊆ E`; (ii) `spt X` is closed; (iii)
`spt(A − B) ⊆ spt A ∪ spt B`; (iv) `spt 0 = ∅`; (v) `spt ∂A ⊆ spt A`.  A point lies off `spt X`
iff it has an open neighbourhood with compact closure on which `X` vanishes.  Small balls are such
neighbourhoods in the proper space `ℝᴾ`; zero neighbourhoods of `A` and `B` intersect to one of
`A − B`; and since `spt dη ⊆ spt η`, a zero neighbourhood of `A` is one of `∂A`. -/
theorem Submission.cmcsd_support_calculus : ∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support) := by
  intro P n
  -- `B_ε(x)` is open, and its closure lies in the compact `closedBall x ε` (`ℝᴾ` is proper)
  have hball : ∀ (x : Euclid P) (ε : ℝ), IsOpen (ball x ε) ∧ IsCompact (closure (ball x ε)) ∧
      closure (ball x ε) ⊆ univ := fun x ε =>
    ⟨isOpen_ball, (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i) for `x ∉ E`, a ball around `x` inside the open set `Eᶜ` is a zero neighbourhood of `x`
    intro E X hE hX x hx
    by_contra hxE
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
    refine hx.2 (mem_sUnion_of_mem (mem_ball_self hε)
      ⟨(hball x ε).1, (hball x ε).2.1, (hball x ε).2.2, fun ω hω => hX ω ?_⟩)
    exact subset_compl_iff_disjoint_right.mp (hω.trans hεE)
  · -- (ii) `spt X = univ \ X.zeroRegion`, and the zero region is open
    intro X
    exact isClosed_univ.sdiff X.isOpen_zeroRegion
  · -- (iii) the intersection of zero neighbourhoods of `A` and `B` is one of `A − B`
    intro A B x hx
    by_contra hAB
    have hxA : x ∈ A.zeroRegion := by
      by_contra h
      exact hAB (mem_union_left _ ⟨mem_univ x, h⟩)
    have hxB : x ∈ B.zeroRegion := by
      by_contra h
      exact hAB (mem_union_right _ ⟨mem_univ x, h⟩)
    obtain ⟨WA, ⟨hWAo, hWAc, -, hWAv⟩, hxWA⟩ := mem_sUnion.mp hxA
    obtain ⟨WB, ⟨hWBo, -, -, hWBv⟩, hxWB⟩ := mem_sUnion.mp hxB
    refine hx.2 (mem_sUnion_of_mem (⟨hxWA, hxWB⟩ : x ∈ WA ∩ WB) ⟨hWAo.inter hWBo,
      hWAc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩)
    change A ω - B ω = 0
    rw [hWAv ω (hω.trans inter_subset_left), hWBv ω (hω.trans inter_subset_right), sub_zero]
  · -- (iv) every ball is a zero neighbourhood of the zero current
    exact eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 (mem_sUnion_of_mem
      (mem_ball_self one_pos) ⟨(hball x 1).1, (hball x 1).2.1, (hball x 1).2.2,
        fun ω _ => GeometricCurrentOn.zero_apply ω⟩)
  · -- (v) `∂A(η) = A(dη)` with `spt dη ⊆ spt η`: a zero neighbourhood of `A` is one of `∂A`
    intro A x hx
    refine ⟨mem_univ x, fun hxA => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := mem_sUnion.mp hxA
    refine mem_sUnion_of_mem hxW ⟨hWo, hWc, hWU, fun η hη => ?_⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) n)).trans hη)

/-- **Current toolkit** in `ℝᴺ` (Simon 6.2.4–6.2.11), given that a current kills forms supported
off its support (VO) and the representation theorem (REP): (A0) `|X(ψ)| ≤ c M(X)` if `|ψ| ≤ c` on
`spt X`; (MB) `|T(ω)| ≤ C c` whenever `|ω| ≤ c` gives `M(T) ≤ C`; (LOC) `X(η) = X(η')` if `η = η'`
on an open `W ⊇ spt X`; (NCD) differences and (NCB) boundaries of currents with compact support,
finite mass and finite boundary mass are again such currents.  For (A0), (REP) gives `(μ, ξ)` with
`μ(ℝᴺ) = M(X)`, and (VO) gives `μ((spt X)ᶜ) = 0`; the rest uses mass suprema, the support calculus
and `∂∂ = 0`. -/
theorem Submission.dimred_mbl_dt_lpo_current_toolkit : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ψ : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), X.mass < ∞ → (∀ x ∈ X.support, covectorEuclideanNorm ((ψ : DifferentialForm (Euclid N) k) x) ≤ c) → |X ψ| ≤ c * X.mass.toReal) ∧ (∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : ℝ), (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ), (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) → |T ω| ≤ C * c) → T.mass ≤ ENNReal.ofReal C) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (η η' : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W → X.support ⊆ W → (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = (η' : DifferentialForm (Euclid N) k) x) → X η = X η') ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → (X - Y).support ⊆ X.support ∪ Y.support ∧ IsCompact (X - Y).support ∧ (X - Y).mass < ∞ ∧ boundaryMassOn (X - Y) univ < ∞) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.boundary.mass < ∞ → X.boundary.support ⊆ X.support ∧ IsCompact X.boundary.support ∧ boundaryMassOn X.boundary univ < ∞ := by
  intro hVO hREP
  -- (MB) each admissible test form has value at most `C`, so their supremum `M(T)` is at most `C`
  have hMB : ∀ (N k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid N)) k) (C : ℝ),
      (∀ (ω : TestFormOn (univ : Set (Euclid N)) k) (c : ℝ),
        (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid N) k) x) ≤ c) →
          |T ω| ≤ C * c) → T.mass ≤ ENNReal.ofReal C := by
    intro N k T C hT
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((hT ω 1 hω.2).trans_eq (mul_one C)))
  -- `M(A − B) ≤ M(A) + M(B)`: `(A − B)(ω) = A(ω) + B(−ω)`, and `−ω` is admissible with `ω`
  have hmass_sub : ∀ (N k : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid N)) k),
      (A - B).mass ≤ A.mass + B.mass := by
    intro N k A B
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have hω' : -ω ∈ massAdmissibleOn univ k univ :=
      ⟨subset_univ _, fun x => by simpa using hω.2 x⟩
    have hneg : B (-ω) = -B ω := map_neg B.toCurrent ω
    calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by
          rw [hneg, ← sub_eq_add_neg]
          rfl
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.mass + B.mass := add_le_add (A.le_massOn hω) (B.le_massOn hω')
  refine ⟨?_, hMB, ?_, ?_, ?_⟩
  · -- (A0) represent `X` by `(μ, ξ)`; `μ` is finite, with `μ(univ) = M(X)`, and carried by `spt X`
    intro N k X ψ c hX hψ
    obtain ⟨μ, ξ, -, -, hμW, -, hξ, hrep, -⟩ := hREP N k univ X isOpen_univ
      fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX
    have hμ : μ univ = X.mass := (hμW univ isOpen_univ).symm
    have : IsFiniteMeasure μ := ⟨by rw [hμ]; exact hX⟩
    -- `μ((spt X)ᶜ) = M_{(spt X)ᶜ}(X) = 0`: `X` kills the forms supported off `spt X` (VO)
    have hZ : μ X.zeroRegion = 0 := by
      rw [← hμW _ X.isOpen_zeroRegion]
      refine nonpos_iff_eq_zero.mp (sSup_le ?_)
      rintro _ ⟨ω, hω, rfl⟩
      simp [hVO N k univ X ω (Set.disjoint_left.mpr fun x hx hxX => hxX.2 (hω.1 hx))]
    have hspt : ∀ᵐ x ∂μ, x ∈ X.support :=
      ae_iff.mpr (measure_mono_null (fun x hx => not_not.mp fun h => hx ⟨mem_univ x, h⟩) hZ)
    have hb : ∀ᵐ x ∂μ, ‖ξ x ((ψ : DifferentialForm (Euclid N) k) x)‖ ≤ c := by
      filter_upwards [hspt] with x hx
      exact (Real.norm_eq_abs _).trans_le ((hξ x _).trans (hψ x hx))
    calc |X ψ| = ‖∫ x, ξ x ((ψ : DifferentialForm (Euclid N) k) x) ∂μ‖ := by
          rw [hrep ψ, Real.norm_eq_abs]
      _ ≤ c * μ.real univ := norm_integral_le_of_norm_le_const hb
      _ = c * X.mass.toReal := by rw [measureReal_def, hμ]
  · -- (LOC) `η − η'` vanishes on `W`, so `spt(η − η') ⊆ Wᶜ` misses `spt X ⊆ W`; apply (VO)
    intro N k X η η' W hW hXW hηη'
    have hsupp : tsupport ((η - η' : TestFormOn (univ : Set (Euclid N)) k) :
        DifferentialForm (Euclid N) k) ⊆ Wᶜ :=
      closure_minimal (fun x hx hxW => hx (by simp [hηη' x hxW])) hW.isClosed_compl
    have hlin : X (η - η') = X η - X η' := map_sub X.toCurrent η η'
    rw [← sub_eq_zero, ← hlin]
    exact hVO N k univ X (η - η') (disjoint_compl_left.mono hsupp hXW)
  · -- (NCD) `spt(X − Y) ⊆ spt X ∪ spt Y` is closed, hence compact; masses add up, also for `∂`
    intro N k X Y hXc hXm hXb hYc hYm hYb
    have hspt := (Submission.cmcsd_support_calculus N k).2.2.1 X Y
    refine ⟨hspt, (hXc.union hYc).of_isClosed_subset
      ((Submission.cmcsd_support_calculus N k).2.1 _) hspt,
      (hmass_sub N k X Y).trans_lt (ENNReal.add_lt_top.mpr ⟨hXm, hYm⟩), ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      -- `∂(X − Y) = ∂X − ∂Y`: both send `ω` to `X(dω) − Y(dω)`
      have hb : (X - Y).boundary = X.boundary - Y.boundary := GeometricCurrentOn.ext fun ω => rfl
      show (X - Y).boundary.mass < ∞
      rw [hb]
      exact (hmass_sub N k _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hXb, hYb⟩)
  · -- (NCB) `spt ∂X ⊆ spt X` is closed, hence compact; `∂∂X = 0` has mass `0` by (MB)
    intro N k X hXc hXb
    have hspt := (Submission.cmcsd_support_calculus N k).2.2.2.2 X
    refine ⟨hspt, hXc.of_isClosed_subset ((Submission.cmcsd_support_calculus N k).2.1 _) hspt, ?_⟩
    cases k with
    | zero => exact ENNReal.zero_lt_top
    | succ k =>
      show X.boundary.boundary.mass < ∞
      rw [GeometricCurrentOn.boundary_boundary]
      exact (hMB N k 0 0 fun ω c _ => by simp).trans_lt ENNReal.ofReal_lt_top
/-- **A cut-off of the pull-back that is compatible with `d`** (Simon 6.1.13–6.1.14).  Let
`F : ℝᴺ → ℝᴺ'` be `C^∞`, `ω ∈ 𝒟ᵏ(ℝᴺ')` and `K ⊆ ℝᴺ` compact.  Then some test form `η ∈ 𝒟ᵏ(ℝᴺ)`
and open `W ⊇ K` satisfy `η = F^#ω` and `dη = F^#(dω)` on `W`.  The pull-back
`F^#ω(x) = Φ(DF(x))(ω(F x))` is `C^∞` because the precomposition `Φ(L) = (γ ↦ γ ∘ L)` is
analytic.  It satisfies `d(F^#ω) = F^#(dω)` (`extDeriv_pullback`).  Take `η = ζ · F^#ω` for a
smooth `ζ` with `support ζ = thickening 1 K` and `ζ = 1` on `cthickening (1/2) K`.  Then
`η = F^#ω` on the open set `W = thickening (1/2) K ⊇ K`, so `dη = d(F^#ω)` there. -/
theorem Submission.dimred_mbl_dt_lpo_cutoff_pullback : ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
  intro N N' k F ω K hF hK
  -- `ω` is `C^∞`
  have hωs : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid N') k) := ω.property.1.1
  -- the precomposition `Φ(L) = (γ ↦ γ ∘ L)` on `k`-covectors is analytic, hence `C^∞`
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Euclid N →L[ℝ] Euclid N') →
        (Euclid N' [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (Euclid N [⋀^Fin k]→L[ℝ] ℝ)) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- `DF` and `ω ∘ F` are `C^∞`, so `F^#ω = Φ(DF)(ω ∘ F)` is `C^∞`
  have hDF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) :=
    (hΦ.comp hDF).clm_apply (hωs.comp hF)
  -- `d(F^#ω) = F^#(dω)` at every point
  have hpb : ∀ x, exteriorDerivative (fun y =>
      ((ω : DifferentialForm (Euclid N') k) (F y)).compContinuousLinearMap (fderiv ℝ F y)) x =
      (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap
        (fderiv ℝ F x) := fun x =>
    extDeriv_pullback (hωs.differentiable (by simp)).differentiableAt hF.contDiffAt (by simp)
  -- a cut-off `ζ` with `support ζ = thickening 1 K` and `ζ = 1` exactly on `cthickening (1/2) K`
  obtain ⟨ζ, hζ, -, hζsupp, hζone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := 1) (E := K)) (isClosed_cthickening (δ := 1 / 2) (E := K))
    (cthickening_subset_thickening' one_pos (by norm_num) K)
  -- `spt ζ ⊆ cthickening 1 K`, which is compact
  have hζc : HasCompactSupport ζ := by
    refine (hK.cthickening (r := 1)).of_isClosed_subset (isClosed_tsupport ζ) ?_
    show closure (support ζ) ⊆ _
    rw [hζsupp]
    exact closure_thickening_subset_cthickening 1 K
  -- `ζ = 1` on the open set `W = thickening (1/2) K ⊇ K`
  have hW : ∀ x ∈ thickening (1 / 2) K, ζ x = 1 := fun x hx =>
    (hζone x).mp (thickening_subset_cthickening _ _ hx)
  -- `η = ζ · F^#ω` is a test form, equal to `F^#ω` on `W`
  refine ⟨⟨fun x => ζ x • ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap
      (fderiv ℝ F x), ⟨hζ.smul hβ, hζc.smul_right⟩, subset_univ _⟩, thickening (1 / 2) K,
    isOpen_thickening, self_subset_thickening (by norm_num) K, fun x hx => ?_, fun x hx => ?_⟩
  · show ζ x • _ = _
    rw [hW x hx, one_smul]
  · -- `η = F^#ω` near `x ∈ W`, so `dη(x) = d(F^#ω)(x) = F^#(dω)(x)`
    rw [← hpb x]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
    show ζ y • _ = _
    rw [hW y hy, one_smul]
/-- **Smooth `Λ`-Lipschitz mollifications of a `Λ`-Lipschitz map.**  For `σ = 1/(j+1)` let `φ` be
a `C^∞` bump with support `B(0, σ)` and `ρⱼ = (∫ φ)⁻¹ φ` its normalization (`ρⱼ ≥ 0`,
`∫ ρⱼ = 1`).  Then `Fⱼ = ρⱼ ⋆ F`, `Fⱼ(x) = ∫ ρⱼ(t) F(x − t) dt`, is `C^∞` (convolution with a
compactly supported smooth kernel), `Λ`-Lipschitz (an average of the `Λ`-Lipschitz translates of
`F`), and `|Fⱼ(x) − F(x)| ≤ Λσ`, since `|F(y) − F(x)| ≤ Λσ` on `B(x, σ)`. -/
theorem Submission.dimred_mbl_dt_lpo_mollify_lipschitz : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ ∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := by
  intro N N' Λ F hF
  -- for each `j` a mollifier `ρ j`: `C^∞`, compactly supported, `≥ 0`, `∫ ρ j = 1`,
  -- `spt ρ j ⊆ B(0, 1/(j+1))`; it is the normalized bump `(∫ φ)⁻¹ φ`
  have hmoll : ∀ j : ℕ, ∃ ρ : Euclid N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∀ y, 0 ≤ ρ y) ∧ ∫ y, ρ y = 1 ∧ support ρ ⊆ ball 0 (1 / ((j : ℝ) + 1)) := by
    intro j
    have hσ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    let φ : ContDiffBump (0 : Euclid N) :=
      ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), half_pos hσ, half_lt_self hσ⟩
    have hφi : Integrable φ := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    -- `∫ φ > 0`, as `φ ≥ 0` and `support φ = B(0, σ)` has positive measure
    have hφp : 0 < ∫ y, φ y := by
      rw [integral_pos_iff_support_of_nonneg (fun y => φ.nonneg) hφi, φ.support_eq]
      exact measure_ball_pos volume 0 φ.rOut_pos
    have hsupp : support (fun y => (∫ z, φ z)⁻¹ * φ y) ⊆ support φ :=
      support_mul_subset_right _ _
    refine ⟨fun y => (∫ z, φ z)⁻¹ * φ y, contDiff_const.mul φ.contDiff,
      φ.hasCompactSupport.mono hsupp, fun y => mul_nonneg (inv_nonneg.2 hφp.le) φ.nonneg, ?_,
      hsupp.trans φ.support_eq.subset⟩
    rw [integral_const_mul, inv_mul_cancel₀ hφp.ne']
  choose ρ hρs hρc hρn hρi hρsupp using hmoll
  -- `Fs j = ρ j ⋆ F`
  refine ⟨fun j => convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun j => ?_,
    fun j => ?_, fun j x => ?_⟩
  · -- `C^∞`: `ρ j` is `C^∞` with compact support and `F` is continuous, so locally integrable
    exact (hρc j).contDiff_convolution_left _ (hρs j) hF.continuous.locallyIntegrable
  · -- `Λ`-Lipschitz: `Fs j x - Fs j x' = ∫ ρ j t • (F (x - t) - F (x' - t)) dt`
    refine LipschitzWith.of_dist_le_mul fun x x' => ?_
    have hint : ∀ z, Integrable (fun t => ρ j t • F (z - t)) := fun z =>
      ((hρs j).continuous.smul (hF.continuous.comp (continuous_const.sub continuous_id))
        ).integrable_of_hasCompactSupport ((hρc j).smul_right (f' := fun t => F (z - t)))
    show dist (∫ t, ρ j t • F (x - t)) (∫ t, ρ j t • F (x' - t)) ≤ Λ * dist x x'
    rw [dist_eq_norm, ← integral_sub (hint x) (hint x')]
    calc ‖∫ t, ρ j t • F (x - t) - ρ j t • F (x' - t)‖
        ≤ ∫ t, ρ j t * ((Λ : ℝ) * dist x x') := by
          refine norm_integral_le_of_norm_le
            (((hρs j).continuous.integrable_of_hasCompactSupport (hρc j)).mul_const _)
            (Eventually.of_forall fun t => ?_)
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hρn j t), ← dist_eq_norm]
          refine mul_le_mul_of_nonneg_left ?_ (hρn j t)
          calc dist (F (x - t)) (F (x' - t)) ≤ Λ * dist (x - t) (x' - t) := hF.dist_le_mul _ _
            _ = Λ * dist x x' := by rw [dist_sub_right]
      _ = (Λ : ℝ) * dist x x' := by rw [integral_mul_const, hρi j, one_mul]
  · -- distance: `dist (F y) (F x) ≤ Λ / (j + 1)` on `B(x, 1/(j+1))`, and `ρ j` is a mollifier
    have hg : ∀ y ∈ ball x (1 / ((j : ℝ) + 1)), dist (F y) (F x) ≤ Λ * (1 / ((j : ℝ) + 1)) :=
      fun y hy => (hF.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le Λ.coe_nonneg)
    calc dist (convolution (ρ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume x) (F x)
        ≤ Λ * (1 / ((j : ℝ) + 1)) :=
          dist_convolution_le (by positivity) (hρsupp j) (hρn j) (hρi j)
            hF.continuous.aestronglyMeasurable hg
      _ = Λ / ((j : ℝ) + 1) := by ring

/-- **Properties of the Lipschitz push-forward** `F_#` (Simon 6.2.23–2.29), derived from its
characterization `CHAR` (`X(ηⱼ) → F_# X(ω)` along smooth `Fⱼ → F` with `‖DFⱼ‖` bounded on `spt X`
and test forms `ηⱼ = Fⱼ^#ω` near `spt X`): (1) `id_# X = X`; (2) `F_#(X − Y) = F_# X − F_# Y`;
(3) `F_# X` only depends on `F` on `spt X`; (4) `M(F_# X) ≤ Λᵏ M(X)`, `spt F_# X ⊆ F(spt X)`;
(5) `∂F_# X = F_# ∂X`; (6) `F_# X(ω)` is such a limit for smooth `Λ`-Lipschitz `Fⱼ → F`.  Each
follows from `CHAR` along the standard approximants (mollified `Fⱼ`, cut-off pull-backs `ηⱼ`)
and uniqueness of limits. -/
theorem Submission.dimred_mbl_dt_lpo_lpush_properties : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → lpush N N k (fun x => x) X = X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → lpush N N' k F (X - Y) = lpush N N' k F X - lpush N N' k F Y) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → EqOn F G X.support → lpush N N' k F X = lpush N N' k G X) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (lpush N N' k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ (lpush N N' k F X).support ⊆ F '' X.support) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → (lpush N N' (k + 1) F X).boundary = lpush N N' k F X.boundary) ∧ (∀ (N N' k : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop ∧ ∀ ω : TestFormOn (univ : Set (Euclid N')) k, ∃ ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k, (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) ∧ Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) := by
  intro hVO hREP hL lpush hCHAR
  obtain ⟨hA0, hMB, hLOC, hNCD, hNCB⟩ := Submission.dimred_mbl_dt_lpo_current_toolkit hVO hREP
  obtain ⟨hL1, -⟩ := hL
  -- standard approximants: the mollified `Fⱼ` are smooth and `Λ`-Lipschitz (so `‖DFⱼ‖ ≤ Λ`), and
  -- `Λ/(j+1)`-close to `F`, hence eventually `ε`-close to `F` and uniformly convergent to it
  have hstd : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F →
      ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧
        (∀ j, LipschitzWith Λ (Fs j)) ∧ (∀ j x, ‖fderiv ℝ (Fs j) x‖ ≤ Λ) ∧
        (∀ ε > 0, ∀ᶠ j in atTop, ∀ x, dist (Fs j x) (F x) < ε) ∧ TendstoUniformly Fs F atTop := by
    intro N N' Λ F hF
    obtain ⟨Fs, hsm, hlip, hdist⟩ := Submission.dimred_mbl_dt_lpo_mollify_lipschitz N N' Λ F hF
    have h0 : Tendsto (fun j : ℕ => (Λ : ℝ) * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Λ : ℝ)
    have hclose : ∀ ε > 0, ∀ᶠ j in atTop, ∀ x, dist (Fs j x) (F x) < ε := fun ε hε =>
      ((tendsto_order.1 h0).2 ε hε).mono fun j hj x =>
        ((hdist j x).trans_eq (mul_one_div _ _).symm).trans_lt hj
    exact ⟨Fs, hsm, hlip, fun j _ => norm_fderiv_le_of_lipschitz ℝ (hlip j), hclose,
      Metric.tendstoUniformly_iff.2 fun ε hε => (hclose ε hε).mono fun j hj x => by
        rw [dist_comm]
        exact hj x⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `CHAR` for `F = Fⱼ = id` and `ηⱼ = ω`: the constant sequence `X(ω)` tends to `id_# X(ω)`
    intro N k X hXc hXm hXb
    ext ω
    refine tendsto_nhds_unique (hCHAR N N k 1 1 (fun x => x) (fun _ x => x) X ω (fun _ => ω)
      LipschitzWith.id hXc hXm hXb (fun _ => contDiff_id) (fun _ x _ => ?_)
      (fun u hu => Eventually.of_forall fun _ x _ => refl_mem_uniformity hu)
      fun _ => ⟨univ, isOpen_univ, subset_univ _, fun x _ => ?_⟩) tendsto_const_nhds
    · rw [fderiv_fun_id]
      exact ContinuousLinearMap.norm_id_le
    · rw [fderiv_fun_id]
      ext v
      simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  · -- (2) shared approximants for `K = spt X ∪ spt Y ⊇ spt(X − Y)`; `(X − Y)(ηⱼ) = X(ηⱼ) − Y(ηⱼ)`
    intro N N' k Λ F X Y hF hXc hXm hXb hYc hYm hYb
    obtain ⟨hXYs, hXYc, hXYm, hXYb⟩ := hNCD N k X Y hXc hXm hXb hYc hYm hYb
    obtain ⟨Fs, hsm, -, hD, -, hU⟩ := hstd N N' Λ F hF
    ext ω
    choose η W hWo hKW hη _ using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) (hXc.union hYc)
    have hX := hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, subset_union_left.trans (hKW j), hη j⟩
    have hY := hCHAR N N' k Λ Λ F Fs Y ω η hF hYc hYm hYb hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, subset_union_right.trans (hKW j), hη j⟩
    have hXY : Tendsto (fun j => X (η j) - Y (η j)) atTop (𝓝 (lpush N N' k F (X - Y) ω)) :=
      hCHAR N N' k Λ Λ F Fs (X - Y) ω η hF hXYc hXYm hXYb hsm (fun j x _ => hD j x)
        hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hXYs.trans (hKW j), hη j⟩
    exact tendsto_nhds_unique hXY (hX.sub hY)
  · -- (3) `Fⱼ → F = G` uniformly on `spt X`: `CHAR` for `F` and for `G` share the sequence `X(ηⱼ)`
    intro N N' k Λ F G X hF hG hXc hXm hXb hFG
    obtain ⟨Fs, hsm, -, hD, -, hU⟩ := hstd N N' Λ F hF
    ext ω
    choose η W hWo hKW hη _ using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
    exact tendsto_nhds_unique
      (hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm (fun j x _ => hD j x)
        hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩)
      (hCHAR N N' k Λ Λ G Fs X ω η hG hXc hXm hXb hsm (fun j x _ => hD j x)
        (hU.tendstoUniformlyOn.congr_right hFG) fun j => ⟨W j, hWo j, hKW j, hη j⟩)
  · intro N N' k Λ F X hF hXc hXm hXb
    obtain ⟨Fs, hsm, -, hD, hclose, hU⟩ := hstd N N' Λ F hF
    refine ⟨?_, ?_⟩
    · -- (4) mass: on `spt X`, `|ηⱼ| ≤ ‖DFⱼ‖ᵏ|ω ∘ Fⱼ| ≤ Λᵏc`, so `|X(ηⱼ)| ≤ ΛᵏcM(X)`; take limits
      refine (hMB N' k (lpush N N' k F X) ((Λ : ℝ) ^ k * X.mass.toReal)
        fun ω c hc => ?_).trans_eq ?_
      · choose η W hWo hKW hη _ using fun j =>
          Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
        refine le_of_tendsto' (hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm
          (fun j x _ => hD j x) hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩).abs
          fun j => (hA0 N k X (η j) ((Λ : ℝ) ^ k * c) hXm fun x hx => ?_).trans_eq (by ring)
        rw [hη j x (hKW j hx)]
        exact (hL1 N N' k _ _).trans (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hD j x) k)
          (hc _) (covectorEuclideanNorm_nonneg _) (pow_nonneg Λ.coe_nonneg k))
      · rw [ENNReal.ofReal_mul (pow_nonneg Λ.coe_nonneg k), ENNReal.ofReal_pow Λ.coe_nonneg,
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hXm.ne]
    · -- (4) support: if `spt ω` misses the compact `F(spt X)`, then eventually `Fⱼ(spt X)` misses
      -- `spt ω`, so `ηⱼ = 0` near `spt X` (locality) and `F_# X(ω) = lim X(ηⱼ) = 0`
      have hEc : IsCompact (F '' X.support) := hXc.image hF.continuous
      refine (Submission.cmcsd_support_calculus N' k).1 _ _ hEc.isClosed fun ω hω => ?_
      obtain ⟨δ, hδ, hδE⟩ := hEc.exists_thickening_subset_open
        (isClosed_tsupport (ω : DifferentialForm (Euclid N') k)).isOpen_compl
        (subset_compl_iff_disjoint_left.2 hω)
      choose η W hWo hKW hη _ using fun j =>
        Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
      have hzero : ∀ᶠ j in atTop, X (η j) = 0 := (hclose δ hδ).mono fun j hj => by
        refine (hLOC N k X (η j) 0 _ ((hWo j).inter ((isClosed_tsupport _).isOpen_compl.preimage
          (hsm j).continuous)) (fun x hx => ⟨hKW j hx, hδE (mem_thickening_iff.2
            ⟨F x, mem_image_of_mem F hx, hj x⟩)⟩) fun x hx => ?_).trans (map_zero _)
        rw [hη j x hx.1, image_eq_zero_of_notMem_tsupport hx.2]
        ext v
        simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact tendsto_nhds_unique (hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm
        (fun j x _ => hD j x) hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩)
        (tendsto_const_nhds.congr' (hzero.mono fun j hj => hj.symm))
  · -- (5) `CHAR` for `X`, `dω`, `dηⱼ` and for `∂X`, `ω`, `ηⱼ`; both sequences are `X(dηⱼ) = ∂X(ηⱼ)`
    intro N N' k Λ F X hF hXc hXm hbm
    obtain ⟨hbs, hbc, hbb⟩ := hNCB N k X hXc hbm
    obtain ⟨Fs, hsm, -, hD, -, hU⟩ := hstd N N' Λ F hF
    ext ω
    choose η W hWo hKW hη hdη using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
    have h1 := hCHAR N N' (k + 1) Λ Λ F Fs X (exteriorDerivativeTestOn univ k ω)
      (fun j => exteriorDerivativeTestOn univ k (η j)) hF hXc hXm hbm hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hdη j⟩
    have h2 := hCHAR N N' k Λ Λ F Fs X.boundary ω η hF hbc hbm hbb hsm (fun j x _ => hD j x)
      hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hbs.trans (hKW j), hη j⟩
    simp only [GeometricCurrentOn.boundary_apply] at h2
    rw [GeometricCurrentOn.boundary_apply]
    exact tendsto_nhds_unique h1 h2
  · -- (6) the mollified `Fⱼ` with the cut-off pull-backs `ηⱼ` of `ω`
    intro N N' k Λ F X hF hXc hXm hXb
    obtain ⟨Fs, hsm, hlip, hD, -, hU⟩ := hstd N N' Λ F hF
    refine ⟨Fs, hsm, hlip, hU, fun ω => ?_⟩
    choose η W hWo hKW hη _ using fun j =>
      Submission.dimred_mbl_dt_lpo_cutoff_pullback N N' k (Fs j) ω _ (hsm j) hXc
    exact ⟨η, fun j => ⟨W j, hWo j, hKW j, hη j⟩, hCHAR N N' k Λ Λ F Fs X ω η hF hXc hXm hXb hsm
      (fun j x _ => hD j x) hU.tendstoUniformlyOn fun j => ⟨W j, hWo j, hKW j, hη j⟩⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
