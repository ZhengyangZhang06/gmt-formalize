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

/-- Step 1 of the proof that an integer multiplicity cycle carried by a `C¹` graph is regular
(Simon 7.4.3, via Allard's theorem): orthogonal coordinates on `ℝ^{n+k}`.  If the linear
isometries `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` have orthogonal ranges `L`, `L'`, then every
`x ∈ ℝ^{n+k}` is `ι v + ι' w`, and `‖ι v + ι' w‖² = ‖v‖² + ‖w‖²`.  `L` and `L'` have dimensions `n`
and `k` and meet only in `0`, so by the dimension formula `L ⊔ L' = ℝ^{n+k}`; the norm identity
is Pythagoras. -/
theorem Submission.dgcr_orthogonal_coordinates : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ x : Euclid (n + k), ∃ v : Euclid n, ∃ w : Euclid k, x = ι v + ι' w) ∧ ∀ (v : Euclid n) (w : Euclid k), ‖ι v + ι' w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  intro n k ι ι' horth
  refine ⟨fun x => ?_, fun v w => ?_⟩
  · -- `L := range ι` and `L' := range ι'` have dimensions `n` and `k` (isometries are injective)
    have hL : Module.finrank ℝ (LinearMap.range ι.toLinearMap) = n := by
      rw [LinearMap.finrank_range_of_inj ι.injective, finrank_euclideanSpace_fin]
    have hL' : Module.finrank ℝ (LinearMap.range ι'.toLinearMap) = k := by
      rw [LinearMap.finrank_range_of_inj ι'.injective, finrank_euclideanSpace_fin]
    -- `L ⊓ L' = ⊥`: if `ι v = ι' w`, then `⟪ι v, ι v⟫ = ⟪ι v, ι' w⟫ = 0`, so `ι v = 0`
    have hinf : LinearMap.range ι.toLinearMap ⊓ LinearMap.range ι'.toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨⟨v, rfl⟩, w, hw⟩
      have h0 : inner ℝ (ι v) (ι v) = 0 := by
        have h := horth v w
        rwa [show ι' w = ι v from hw] at h
      exact inner_self_eq_zero.1 h0
    -- dimension formula: `dim (L ⊔ L') = n + k = dim ℝ^{n+k}`, so `L ⊔ L' = ⊤`
    have hsup : LinearMap.range ι.toLinearMap ⊔ LinearMap.range ι'.toLinearMap = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range ι.toLinearMap) (LinearMap.range ι'.toLinearMap)
      rw [hinf, finrank_bot, hL, hL'] at h
      rw [finrank_euclideanSpace_fin]
      omega
    -- `x ∈ L ⊔ L'`, so `x = ι v + ι' w`
    have hx : x ∈ LinearMap.range ι.toLinearMap ⊔ LinearMap.range ι'.toLinearMap := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, hvw⟩ := Submodule.mem_sup.1 hx
    exact ⟨v, w, hvw.symm⟩
  · -- Pythagoras: the cross term `2 ⟪ι v, ι' w⟫` vanishes and `ι`, `ι'` preserve norms
    rw [norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]
    ring
/-- Simon Ch. 2, §4 (graph charts): for linear isometries `ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}`
with `⟨ιv, ι'w⟩ = 0` and `u` of class `C¹` on `D = B_s(0)`, the graph map
`Φ(v) = z + ιv + ι'u(v)` is `C¹` on `D`, and the adjoint `ι*` satisfies `ι*(Φ(v) − z) = v` for
every `v`: `⟨ι*(ιv + ι'u(v)), e⟩ = ⟨ιv, ιe⟩ + ⟨ι'u(v), ιe⟩ = ⟨v, e⟩ + 0`. -/
theorem Submission.dgce_graph_contDiffOn_left_inverse : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ContDiffOn ℝ 1 u (ball 0 s) → ContDiffOn ℝ 1 (fun v => z + ι v + ι' (u v)) (ball (0 : Euclid n) s) ∧ ∃ L : Euclid (n + k) →L[ℝ] Euclid n, ∀ v, L (z + ι v + ι' (u v) - z) = v := by
  intro n k ι ι' u z s horth hu
  -- `Φ = (z + ι·) + ι' ∘ u`: constants and linear isometries are smooth, `ι' ∘ u` is `C¹` on `D`
  refine ⟨(contDiffOn_const.add ι.contDiff.contDiffOn).add (ι'.contDiff.comp_contDiffOn hu),
    ContinuousLinearMap.adjoint ι.toContinuousLinearMap, fun v => ext_inner_right ℝ fun e => ?_⟩
  -- `⟨ι*(Φ(v) − z), e⟩ = ⟨ιv + ι'u(v), ιe⟩ = ⟨v, e⟩ + ⟨ιe, ι'u(v)⟩ = ⟨v, e⟩`
  rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap, add_assoc,
    add_sub_cancel_left, inner_add_left, LinearIsometry.inner_map_map,
    real_inner_comm (ι e) (ι' (u v)), horth, add_zero]
/-- **A `C¹` map on a ball with a continuous affine left inverse parametrizes an embedded `C¹`
submanifold** (Simon Ch. 2, §4, (4.1), chapter-02.txt lines 849–860).  Let `D = B_s(0) ⊆ ℝᵈ`, let
`Φ : ℝᵈ → ℝᴾ` be `C¹` on `D`, and let `Pr(x) = L(x − z)` (`L` continuous linear) satisfy
`Pr(Φ(v)) = v` on `D`.  Then (a) `Φ` is injective on `D`; (b) `Φ` is differentiable on `D` and
`L ∘ DΦ(v) = id`, so `DΦ(v)` is injective; (c) `Σ = Φ(D)` is an embedded `d`-dimensional `C¹`
submanifold: at every `y ∈ Σ` take `V = D`, `W = Pr⁻¹(D) ⊇ Σ` and `ψ = Φ`; `ψ` is proper since,
for compact `K ⊆ W` with `t = max_K ‖Pr‖ < s`, `D ∩ Φ⁻¹(K) = B̄_t(0) ∩ Φ⁻¹(K)` is closed in the
compact ball `B̄_t(0)`. -/
theorem Submission.dgce_left_inverse_chart_embedded : ∀ (d P : ℕ) (Φ : Euclid d → Euclid P) (L : Euclid P →L[ℝ] Euclid d) (z : Euclid P) (s : ℝ), ContDiffOn ℝ 1 Φ (ball 0 s) → (∀ v ∈ ball (0 : Euclid d) s, L (Φ v - z) = v) → InjOn Φ (ball (0 : Euclid d) s) ∧ (∀ v ∈ ball (0 : Euclid d) s, DifferentiableAt ℝ Φ v ∧ Injective (fderiv ℝ Φ v)) ∧ IsEmbeddedSubmanifold 1 d (Φ '' ball (0 : Euclid d) s) := by
  intro d P Φ L z s hΦ hL
  -- `D = B_s(0)` is open and `Pr(x) = L(x − z)` is continuous.
  have hD : IsOpen (ball (0 : Euclid d) s) := isOpen_ball
  have hPr : Continuous fun x : Euclid P => L (x - z) := L.continuous.comp (continuous_sub_right z)
  -- Step 1, (a): `Φ v = Φ v'` gives `v = Pr(Φ v) = Pr(Φ v') = v'`.
  have hinj : InjOn Φ (ball (0 : Euclid d) s) := fun v hv v' hv' h => by
    rw [← hL v hv, ← hL v' hv', h]
  -- Step 2: `Φ` is `C¹` on the open set `D`, hence differentiable at every point of `D`.
  have hdiff : ∀ v ∈ ball (0 : Euclid d) s, DifferentiableAt ℝ Φ v := fun v hv =>
    hΦ.differentiableOn_one.differentiableAt (hD.mem_nhds hv)
  -- Step 3: `L ∘ DΦ(v) = id`.  By the chain rule `x ↦ L(Φ x − z)` has derivative `L ∘ DΦ(v)` at
  -- `v`; it equals `id` on the neighbourhood `D` of `v`, so its derivative is also `id`.
  have hLD : ∀ v ∈ ball (0 : Euclid d) s, ∀ a, L (fderiv ℝ Φ v a) = a := by
    intro v hv a
    have h₁ : HasFDerivAt (fun x => L (Φ x - z)) (L.comp (fderiv ℝ Φ v)) v :=
      L.hasFDerivAt.comp v ((hdiff v hv).hasFDerivAt.sub_const z)
    have h₂ : HasFDerivAt (fun x => L (Φ x - z)) (ContinuousLinearMap.id ℝ (Euclid d)) v := by
      refine (hasFDerivAt_id v).congr_of_eventuallyEq ?_
      filter_upwards [hD.mem_nhds hv] with x hx using hL x hx
    exact congrArg (fun f : Euclid d →L[ℝ] Euclid d => f a) (h₁.unique h₂)
  -- Step 4, (b): `DΦ(v) a = DΦ(v) b` gives `a = L(DΦ(v) a) = L(DΦ(v) b) = b`.
  have hfinj : ∀ v ∈ ball (0 : Euclid d) s, Injective (fderiv ℝ Φ v) := fun v hv =>
    Function.LeftInverse.injective (hLD v hv)
  refine ⟨hinj, fun v hv => ⟨hdiff v hv, hfinj v hv⟩, ?_⟩
  -- Step 5, (c): at `y ∈ Σ` take `V = D`, `W = Pr⁻¹(D)` and `ψ = Φ`.  `Σ ⊆ W`, since
  -- `Pr(Φ v) = v ∈ D`; hence `y ∈ W` and `ψ(V) = Σ = W ∩ Σ`.
  have hSW : Φ '' ball (0 : Euclid d) s ⊆ (fun x => L (x - z)) ⁻¹' ball (0 : Euclid d) s := by
    rintro _ ⟨v, hv, rfl⟩
    show L (Φ v - z) ∈ ball (0 : Euclid d) s
    rw [hL v hv]
    exact hv
  intro y hy
  refine ⟨ball (0 : Euclid d) s, (fun x => L (x - z)) ⁻¹' ball (0 : Euclid d) s, Φ, hD,
    hD.preimage hPr, hSW hy, by exact_mod_cast hΦ, hinj, (inter_eq_right.mpr hSW).symm, ?_,
    hfinj⟩
  -- (iv) Properness: `D ∩ Φ⁻¹(K)` is compact for every compact `K ⊆ W`; trivial if `K = ∅`.
  intro K hKW hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp
  -- `‖Pr‖` attains its maximum `t` on `K` at `x₀`; `t < s` as `x₀ ∈ W`, so `B̄_t(0) ⊆ D`.
  obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn hKne hPr.norm.continuousOn
  have hx₀W : L (x₀ - z) ∈ ball (0 : Euclid d) s := hKW hx₀
  have hsub : closedBall (0 : Euclid d) ‖L (x₀ - z)‖ ⊆ ball (0 : Euclid d) s :=
    closedBall_subset_ball (mem_ball_zero_iff.mp hx₀W)
  -- `D ∩ Φ⁻¹(K) = B̄_t(0) ∩ Φ⁻¹(K)`: if `v ∈ D` and `Φ v ∈ K`, then `‖v‖ = ‖Pr(Φ v)‖ ≤ t`.
  have heq : ball (0 : Euclid d) s ∩ Φ ⁻¹' K =
      closedBall (0 : Euclid d) ‖L (x₀ - z)‖ ∩ Φ ⁻¹' K := by
    ext v
    refine ⟨fun ⟨hv, hvK⟩ => ⟨?_, hvK⟩, fun ⟨hv, hvK⟩ => ⟨hsub hv, hvK⟩⟩
    rw [mem_closedBall_zero_iff, ← hL v hv]
    exact isMaxOn_iff.mp hmax (Φ v) hvK
  -- `Φ` is continuous on the closed ball `B̄_t(0) ⊆ D` and `K` is closed, so `B̄_t(0) ∩ Φ⁻¹(K)` is
  -- a closed subset of the compact ball `B̄_t(0)`.
  rw [heq]
  exact (isCompact_closedBall 0 _).of_isClosed_subset
    ((hΦ.continuousOn.mono hsub).preimage_isClosed_of_isClosed isClosed_closedBall hK.isClosed)
    inter_subset_left
/-- **Simon Ch. 2, §4, (4.3)**: if `Φ` is `C¹` on `D = B_s(0) ⊆ ℝᵈ` and `x ↦ L(x − z)` is a left
inverse of `Φ` on `D`, then `T_{Φ(v)}Φ(D) ⊆ DΦ(v)(ℝᵈ)` for every `v ∈ D`.  If `γ` witnesses
`w ∈ T_{Φ(v)}Φ(D)`, the curve `c(t) = L(γ(t) − z)` has `c(0) = v`, `c'(0) = L w` and
`γ = Φ ∘ c` on `(−1, 1)`, so the chain rule and uniqueness of derivatives give
`w = DΦ(v)(L w)`. -/
theorem Submission.dgce_left_inverse_tangentSpace_subset_range : ∀ (d P : ℕ) (Φ : Euclid d → Euclid P) (L : Euclid P →L[ℝ] Euclid d) (z : Euclid P) (s : ℝ), ContDiffOn ℝ 1 Φ (ball 0 s) → (∀ v ∈ ball (0 : Euclid d) s, L (Φ v - z) = v) → ∀ v ∈ ball (0 : Euclid d) s, tangentSpace (Φ '' ball (0 : Euclid d) s) (Φ v) ⊆ (LinearMap.range (fderiv ℝ Φ v : Euclid d →ₗ[ℝ] Euclid P) : Set (Euclid P)) := by
  rintro d P Φ L z s hΦ hL v₀ hv₀ w ⟨γ, -, hγ, hγ0, hγw⟩
  -- `Φ` is `C¹` on the open ball, hence differentiable at `v₀`
  have hΦv₀ : HasFDerivAt Φ (fderiv ℝ Φ v₀) v₀ :=
    (hΦ.differentiableOn_one.differentiableAt (isOpen_ball.mem_nhds hv₀)).hasFDerivAt
  -- `c(t) = L(γ(t) − z)` has `c'(0) = L w` and `c(0) = L(Φ(v₀) − z) = v₀`
  have hc : HasDerivAt (fun t => L (γ t - z)) (L w) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (hγw.sub_const z)
  have hc0 : v₀ = L (γ 0 - z) := by rw [hγ0, hL v₀ hv₀]
  -- `γ = Φ ∘ c` on the neighbourhood `(−1, 1)` of `0`: `γ(t) = Φ(u)` with `u ∈ D`, so `c(t) = u`
  have hγc : γ =ᶠ[𝓝 0] Φ ∘ fun t => L (γ t - z) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos] with t ht
    obtain ⟨u, hu, hut⟩ := hγ ht
    rw [Function.comp_apply, ← hut, hL u hu]
  -- chain rule, then uniqueness of derivatives: `w = DΦ(v₀)(L w)`
  have hw : w = fderiv ℝ Φ v₀ (L w) :=
    hγw.unique ((hΦv₀.comp_hasDerivAt_of_eq 0 hc hc0).congr_of_eventuallyEq hγc)
  exact ⟨L w, hw.symm⟩
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm

/-- **Simon Ch. 2, §4, (4.3)** for a map with a continuous affine left inverse: if `Φ` is `C¹` on
`D = B_s(0) ⊆ ℝᵈ` and `L(Φ(v) − z) = v` for `v ∈ D`, then `T_{Φ(v₀)}Φ(D) = DΦ(v₀)(ℝᵈ)` for every
`v₀ ∈ D`.  `⊆` is `dgce_left_inverse_tangentSpace_subset_range`.  For `⊇` and `a ∈ ℝᵈ`, take the
constant curve if `a = 0`.  Otherwise, with `c₀ = (s − |v₀|) / (2|a|)` and `θ(t) = c₀ sin(t / c₀)`
(smooth, `θ(0) = 0`, `θ'(0) = 1`, `|θ| ≤ c₀`), the curve `γ(t) = Φ(v₀ + θ(t) a)` stays in `Φ(D)`
and has velocity `DΦ(v₀) a`. -/
theorem Submission.dgce_left_inverse_tangentSpace_eq_range : ∀ (d P : ℕ) (Φ : Euclid d → Euclid P) (L : Euclid P →L[ℝ] Euclid d) (z : Euclid P) (s : ℝ), ContDiffOn ℝ 1 Φ (ball 0 s) → (∀ v ∈ ball (0 : Euclid d) s, L (Φ v - z) = v) → ∀ v ∈ ball (0 : Euclid d) s, tangentSpace (Φ '' ball (0 : Euclid d) s) (Φ v) = (LinearMap.range (fderiv ℝ Φ v : Euclid d →ₗ[ℝ] Euclid P) : Set (Euclid P)) := by
  intro d P Φ L z s hΦ hL v₀ hv₀
  refine Subset.antisymm
    (Submission.dgce_left_inverse_tangentSpace_subset_range d P Φ L z s hΦ hL v₀ hv₀) ?_
  rintro _ ⟨a, rfl⟩
  -- `Φ` is `C¹` on the open ball `D`, hence differentiable at `v₀`
  have hΦv₀ : HasFDerivAt Φ (fderiv ℝ Φ v₀) v₀ :=
    (hΦ.differentiableOn_one.differentiableAt (isOpen_ball.mem_nhds hv₀)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `Φ(v₀)` has velocity `0 = DΦ(v₀) 0`
    subst ha
    refine ⟨fun _ => Φ v₀, contDiffOn_const, fun _ _ => mem_image_of_mem Φ hv₀, rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (Φ v₀)
  · -- `a ≠ 0`: `κ(t) = v₀ + θ(t) a` with `θ(t) = c₀ sin(t / c₀)`, `c₀ = (s − |v₀|) / (2|a|)`
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hv₀s : ‖v₀‖ < s := mem_ball_zero_iff.mp hv₀
    set c₀ : ℝ := (s - ‖v₀‖) / (2 * ‖a‖) with hc₀_def
    have hc₀ : 0 < c₀ := div_pos (sub_pos.mpr hv₀s) (by positivity)
    set θ : ℝ → ℝ := fun t => c₀ * Real.sin (t / c₀) with hθ_def
    -- (a) `θ` is smooth
    have hθ_cd : ContDiff ℝ 1 θ :=
      contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const c₀))
    -- (b) `θ(0) = 0` and `θ'(0) = c₀ cos 0 / c₀ = 1`
    have hθ0 : θ 0 = 0 := by simp [hθ_def]
    have hθ_deriv : HasDerivAt θ 1 0 := by
      have h := ((Real.hasDerivAt_sin (0 / c₀)).comp 0
        ((hasDerivAt_id' (x := (0 : ℝ))).div_const c₀)).const_mul c₀
      rw [zero_div, Real.cos_zero, one_mul, mul_one_div_cancel hc₀.ne'] at h
      exact h
    -- (c) `|θ(t)| ≤ c₀`
    have hθ_bd : ∀ t, |θ t| ≤ c₀ := fun t => by
      rw [hθ_def, abs_mul, abs_of_pos hc₀]
      exact mul_le_of_le_one_right hc₀.le (Real.abs_sin_le_one _)
    -- `κ` stays in `D`, `κ(0) = v₀` and `κ'(0) = a`
    set κ : ℝ → Euclid d := fun t => v₀ + θ t • a with hκ_def
    have hκD : ∀ t, κ t ∈ ball (0 : Euclid d) s := fun t => by
      rw [mem_ball_zero_iff]
      calc ‖κ t‖ ≤ ‖v₀‖ + |θ t| * ‖a‖ := by
            simpa only [hκ_def, norm_smul, Real.norm_eq_abs] using norm_add_le v₀ (θ t • a)
        _ ≤ ‖v₀‖ + c₀ * ‖a‖ := by gcongr; exact hθ_bd t
        _ = ‖v₀‖ + (s - ‖v₀‖) / 2 := by rw [hc₀_def]; field_simp
        _ < s := by linarith
    have hκ0 : κ 0 = v₀ := by simp [hκ_def, hθ0]
    have hκ_cd : ContDiff ℝ 1 κ := contDiff_const.add (hθ_cd.smul contDiff_const)
    have hκ_deriv : HasDerivAt κ a 0 := by
      have := HasDerivAt.const_add v₀ (hθ_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = Φ ∘ κ` is `C¹` on `(-1, 1)`, lies in `Φ(D)`, and `γ'(0) = DΦ(v₀) a`
    refine ⟨Φ ∘ κ, hΦ.comp hκ_cd.contDiffOn fun t _ => hκD t,
      fun t _ => mem_image_of_mem Φ (hκD t), by simp [hκ0], ?_⟩
    exact hΦv₀.comp_hasDerivAt_of_eq 0 hκ_deriv hκ0.symm

/-- Simon Ch. 2, §4, 4.1 and 4.3 for graphs (cf. Remark 4.4): for linear isometries
`ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` with `⟨ιv, ι'w⟩ = 0` and `u` of class `C¹` on
`D = B_s(0)`, the graph map `Φ(v) = z + ιv + ι'u(v)` is injective on `D` with injective derivative,
`Σ = Φ(D)` is an embedded `n`-dimensional `C¹` submanifold, and `T_{Φ(v)}Σ = range DΦ(v)` for
`v ∈ D`. -/
theorem Submission.dgcr_graph_chart_embedded : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → InjOn (fun v => z + ι v + ι' (u v)) (ball (0 : Euclid n) s) ∧ (∀ v ∈ ball (0 : Euclid n) s, DifferentiableAt ℝ (fun v => z + ι v + ι' (u v)) v ∧ Injective (fderiv ℝ (fun v => z + ι v + ι' (u v)) v)) ∧ IsEmbeddedSubmanifold 1 n ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ ∀ v ∈ ball (0 : Euclid n) s, tangentSpace ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) (z + ι v + ι' (u v)) = (LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v : Euclid n →ₗ[ℝ] Euclid (n + k)) : Set (Euclid (n + k))) := by
  intro n k ι ι' u z s horth _hs hu
  -- `Φ` is `C¹` on `D`, and `Pr(x) = L(x − z)` inverts it on the left: `Pr ∘ Φ = id`
  obtain ⟨hΦ, L, hL⟩ := Submission.dgce_graph_contDiffOn_left_inverse n k ι ι' u z s horth hu
  -- (i)–(iii) and (iv) hold for any `C¹` map on `D` with a continuous affine left inverse
  obtain ⟨hinj, hdiff, hemb⟩ := Submission.dgce_left_inverse_chart_embedded n (n + k)
    (fun v => z + ι v + ι' (u v)) L z s hΦ fun v _ => hL v
  exact ⟨hinj, hdiff, hemb, Submission.dgce_left_inverse_tangentSpace_eq_range n (n + k)
    (fun v => z + ι v + ι' (u v)) L z s hΦ fun v _ => hL v⟩
/-- Step 8 of the proof that an integer multiplicity cycle carried by a `C¹` graph is regular
(Simon 7.4.3, via Allard's theorem; consequences of the area formula, Ch. 2, 3.2–3.5): for the
graph map `Φ(v) = z + ιv + ι'u(v)` of a `C¹` function `u` on `B_s(0)` (`ι`, `ι'` orthogonal linear
isometries), `∫_A g ∘ Φ dLⁿ ≤ ∫_{Φ(A)} g dHⁿ` for Borel `A ⊆ B_s(0)` and Borel `g ≥ 0`, and
`Hⁿ(Φ(B̄_t(0))) < ∞` for `t < s`.  `Pr = ι*(· − z)` is a 1-Lipschitz left inverse of `Φ`, so
`Lⁿ(S) = Hⁿ(Pr(Φ(S))) ≤ Hⁿ(Φ(S))` and `Φ_#(Lⁿ⌞A) ≤ Hⁿ⌞Φ(A)`; on the compact convex set `B̄_t(0)`,
`Φ` is Lipschitz by the mean value inequality. -/
theorem Submission.dgcr_graph_measure_bounds : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → (∀ (A : Set (Euclid n)) (g : Euclid (n + k) → ℝ≥0∞), MeasurableSet A → A ⊆ ball 0 s → Measurable g → ∫⁻ v in A, g (z + ι v + ι' (u v)) ≤ ∫⁻ x in (fun v => z + ι v + ι' (u v)) '' A, g x ∂μHE[n]) ∧ ∀ t : ℝ, t < s → μHE[n] ((fun v => z + ι v + ι' (u v)) '' closedBall (0 : Euclid n) t) ≠ ∞ := by
  intro n k ι ι' u z s horth hs hu
  set Φ : Euclid n → Euclid (n + k) := fun v => z + ι v + ι' (u v) with hΦ
  -- step 1: `Pr = ι*(· − z)` is a 1-Lipschitz left inverse of `Φ`
  set ιs : Euclid (n + k) →L[ℝ] Euclid n := ContinuousLinearMap.adjoint ι.toContinuousLinearMap
    with hιs
  have hιsι : ∀ v, ιs (ι v) = v := fun v => ext_inner_right ℝ fun w => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.inner_map_map]
  have hιsι' : ∀ w, ιs (ι' w) = 0 := fun w => ext_inner_right ℝ fun v => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      inner_zero_left, real_inner_comm, horth]
  have hιs_le : ∀ y, ‖ιs y‖ ≤ ‖y‖ := fun y =>
    calc ‖ιs y‖ ≤ ‖ιs‖ * ‖y‖ := ιs.le_opNorm y
      _ = ‖ι.toContinuousLinearMap‖ * ‖y‖ := by rw [hιs, LinearIsometryEquiv.norm_map]
      _ ≤ 1 * ‖y‖ := by gcongr; exact ι.norm_toContinuousLinearMap_le
      _ = ‖y‖ := one_mul _
  let Pr : Euclid (n + k) → Euclid n := fun x => ιs (x - z)
  have hPrΦ : ∀ v, Pr (Φ v) = v := fun v => by
    simp only [Pr, hΦ, add_assoc, add_sub_cancel_left, map_add, hιsι, hιsι', add_zero]
  have hPr : LipschitzWith 1 Pr := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [Pr, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right, NNReal.coe_one, one_mul]
    exact hιs_le _
  -- step 3: `Lⁿ(S) ≤ Hⁿ(Φ(S))` for every `S`
  have hvol : ∀ S : Set (Euclid n), volume S ≤ μHE[n] (Φ '' S) := fun S => by
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hPr.lipschitzOnWith (s := Φ '' S))
    rwa [image_image, show (fun v => Pr (Φ v)) = id from funext hPrΦ, image_id,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ENNReal.coe_one, one_pow, one_mul] at h
  have hΦC1 : ContDiffOn ℝ 1 Φ (ball 0 s) :=
    (contDiffOn_const.add ι.contDiff.contDiffOn).add (ι'.contDiff.comp_contDiffOn hu)
  refine ⟨fun A g hA hAs hg => ?_, fun t ht => ?_⟩
  · -- steps 4–5: `Φ_#(Lⁿ⌞A) ≤ Hⁿ⌞Φ(A)`
    have hΦm : AEMeasurable Φ (volume.restrict A) := (hΦC1.continuousOn.mono hAs).aemeasurable hA
    have hν : Measure.map Φ (volume.restrict A) ≤ μHE[n].restrict (Φ '' A) := by
      refine Measure.le_iff.2 fun S hS => ?_
      rw [Measure.map_apply_of_aemeasurable hΦm hS, Measure.restrict_apply' hA,
        Measure.restrict_apply hS, ← image_preimage_inter]
      exact hvol _
    calc ∫⁻ v in A, g (Φ v) = ∫⁻ x, g x ∂(Measure.map Φ (volume.restrict A)) :=
          (lintegral_map' hg.aemeasurable hΦm).symm
      _ ≤ ∫⁻ x in Φ '' A, g x ∂μHE[n] := lintegral_mono' hν le_rfl
  · -- step 6: `Φ` is Lipschitz on `B̄_t(0)`
    rcases lt_or_ge t 0 with ht0 | ht0
    · rw [closedBall_eq_empty.2 ht0, image_empty, measure_empty]
      exact ENNReal.zero_ne_top
    have hKs : closedBall (0 : Euclid n) t ⊆ ball 0 s := closedBall_subset_ball ht
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid n) t).exists_bound_of_continuousOn
      ((hΦC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hKs)
    have hLip : LipschitzOnWith C.toNNReal Φ (closedBall 0 t) :=
      (convex_closedBall (0 : Euclid n) t).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
        (fun v hv => ((hΦC1.differentiableOn one_ne_zero).differentiableAt
          (isOpen_ball.mem_nhds (hKs hv))).hasFDerivAt.hasFDerivWithinAt)
        (fun v hv => by rw [← norm_toNNReal]; exact Real.toNNReal_le_toNNReal (hC v hv))
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (isCompact_closedBall (0 : Euclid n) t).measure_lt_top.ne
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]
/-- Steps 3(ii)–(iii) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3,
via Allard's theorem): if `τ` is an orthonormal `n`-frame whose span contains every `F eⱼ`, then
`det(F* ∘ F) = (det 𝒜)²` with `𝒜ᵢⱼ = ⟨τᵢ, F eⱼ⟩`.  Expanding `F eⱼ = Σₗ 𝒜ₗⱼ τₗ` gives the Gram
identity `⟨F eᵢ, F eⱼ⟩ = (𝒜ᵀ𝒜)ᵢⱼ`, and the Gram matrix is the matrix of `F* ∘ F` in the standard
basis of `ℝⁿ`. -/
theorem Submission.dgoj_det_adjoint_comp_eq_det_sq : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P) (τ : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, F (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ)) → (F.adjoint ∘L F).det = (Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ)))).det ^ 2 := by
  intro P n F τ hτ hb
  set A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ))) with hA
  -- `F eⱼ = Σₗ 𝒜ₗⱼ τₗ`: the coordinates of a vector of `span τ` are its inner products with `τ`
  have hexp : ∀ j, F (EuclideanSpace.single j (1 : ℝ)) = ∑ l, A l j • τ l := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hb j)
    have hcA : ∀ l, A l j = c l := by
      intro l
      rw [hA, Matrix.of_apply, ← hc, hτ.inner_right_fintype]
    rw [← hc]
    simp only [hcA]
  -- the Gram identity `⟨F eᵢ, F eⱼ⟩ = (𝒜ᵀ𝒜)ᵢⱼ`
  have hgram : ∀ i j, inner ℝ (F (EuclideanSpace.single i (1 : ℝ)))
      (F (EuclideanSpace.single j (1 : ℝ))) = (A.transpose * A) i j := by
    intro i j
    rw [Matrix.mul_apply]
    conv_lhs => rw [hexp i]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, Matrix.transpose_apply]
    simp [hA]
  -- the matrix of `F* ∘ F` in the standard basis has entries `⟨eᵢ, F* F eⱼ⟩ = ⟨F eᵢ, F eⱼ⟩`
  let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmat : LinearMap.toMatrix B B ((F.adjoint ∘L F : Euclid n →L[ℝ] Euclid n) : Euclid n →ₗ[ℝ] Euclid n)
      = A.transpose * A := by
    ext i j
    rw [LinearMap.toMatrix_apply, ← hgram i j]
    simp only [B, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right, EuclideanSpace.inner_single_left]
    simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, hmat, Matrix.det_mul,
    Matrix.det_transpose, sq]
/-- Step 3 of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem): if `F : ℝⁿ → ℝᴾ` is injective, its range `L` has an orthonormal basis
`τ = (τ₁, …, τₙ)`, regarded as an orthonormal `n`-frame in `ℝᴾ` spanning `L`.  Since
`dim L = n`, reindex `stdOrthonormalBasis ℝ L` along `Fin (dim L) ≃ Fin n` and include it into
`ℝᴾ` by the linear isometry `L → ℝᴾ`. -/
theorem Submission.dgoj_exists_orthonormal_frame_range : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P), Injective F → ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (Set.range τ) = LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P) := by
  intro P n F hF
  set L := LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P) with hLdef
  -- `dim L = dim ℝⁿ = n`, since `F` is injective
  have hL : Module.finrank ℝ L = n := by
    rw [hLdef, LinearMap.finrank_range_of_inj hF, finrank_euclideanSpace_fin]
  let T : OrthonormalBasis (Fin n) ℝ L := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
  refine ⟨fun i => (T i : Euclid P), ?_, ?_⟩
  · -- the inclusion `L → ℝᴾ` is a linear isometry
    exact T.orthonormal.comp_linearIsometry L.subtypeₗᵢ
  · -- `span (ι '' range T) = ι '' span (range T) = ι '' L = L`
    have h1 : (fun i => (T i : Euclid P)) = L.subtype ∘ T := rfl
    rw [h1, Set.range_comp, Submodule.span_image, ← T.coe_toBasis, T.toBasis.span_eq,
      Submodule.map_top, Submodule.range_subtype]

/-- **The normalized evaluation at `F e` is a unit orientation of `range F`** (Simon 6.1.1,
6.1.7; `√det(F* ∘ F)` is the area Jacobian of Ch. 2, 3.1/3.3).  For injective `F : ℝⁿ → ℝᴾ`,
`det(F* ∘ F) > 0`, and if `α(F e₁, …, F eₙ) = √det(F* ∘ F) ξ(α)` for every `n`-covector `α` then
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal frame `τ` of `range F`: with `d = det(⟨τᵢ, F eⱼ⟩)` one has
`det(F* ∘ F) = d² ≠ 0` and `α(F e) = d α(τ)`, so `|d| ξ(α) = d α(τ)` and the sign is that of `d`. -/
theorem Submission.dgoj_unitOrientation_of_injective : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P), Injective F → 0 < (F.adjoint ∘L F).det ∧ ∀ ξ : MultiVector P n, (∀ α : Covector (Euclid P) n, α (fun i => F (EuclideanSpace.single i (1 : ℝ))) = Real.sqrt ((F.adjoint ∘L F).det) * ξ α) → IsUnitOrientationOf ξ (LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F hF
  -- an orthonormal frame `τ` of `range F`; every `F eⱼ` lies in its span
  obtain ⟨τ, hτo, hτs⟩ := Submission.dgoj_exists_orthonormal_frame_range P n F hF
  have hb : ∀ j, F (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ) := by
    intro j
    rw [hτs]
    exact LinearMap.mem_range_self _ _
  -- `det(F* ∘ F) = d²` for `d = det(⟨τᵢ, F eⱼ⟩)`
  set d := (Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ)))).det
  have hdet : (F.adjoint ∘L F).det = d ^ 2 :=
    Submission.dgoj_det_adjoint_comp_eq_det_sq P n F τ hτo hb
  -- `ker(F* ∘ F) = ker F = 0`, so `det(F* ∘ F) ≠ 0` and hence `d ≠ 0`
  have hd : d ≠ 0 := by
    intro h
    have h0 : (F.adjoint ∘L F).det = 0 := by rw [hdet, h, zero_pow two_ne_zero]
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0
    rw [F.ker_adjoint_comp_self, LinearMap.ker_eq_bot]
    exact hF
  -- (i): `det(F* ∘ F) = d² > 0`
  refine ⟨by rw [hdet]; positivity, fun ξ hξ => ⟨τ, hτo, hτs, ?_⟩⟩
  -- (ii): `|d| ξ(α) = √det(F* ∘ F) ξ(α) = α(F e) = d α(τ)` for every `α`
  have key : ∀ α : Covector (Euclid P) n, |d| * ξ α = d * α τ := by
    intro α
    rw [← Real.sqrt_sq_eq_abs, ← hdet, ← hξ α]
    exact Submission.dgoj_covector_eq_det_mul_of_mem_span P n τ _ hτo hb α
  -- the sign of `d` decides between `ξ(α) = -α(τ)` and `ξ(α) = α(τ)`
  rcases hd.lt_or_gt with hneg | hpos
  · right
    intro α
    have h := key α
    rw [abs_of_neg hneg] at h
    apply mul_left_cancel₀ hd
    linarith
  · left
    intro α
    have h := key α
    rw [abs_of_pos hpos] at h
    exact mul_left_cancel₀ hd h
/-- Evaluation of `n`-covectors at an `n`-family `c`, `ev c = (α ↦ α c)`, is a continuous map
into `n`-vectors: `‖ev c - ev c'‖ ≤ n · max(‖c‖, ‖c'‖)ⁿ⁻¹ · ‖c - c'‖`. -/
theorem Submission.dgoj_exists_continuous_covector_eval : ∀ (P n : ℕ), ∃ ev : (Fin n → Euclid P) → MultiVector P n, Continuous ev ∧ ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := by
  intro P n
  let ev : (Fin n → Euclid P) → MultiVector P n := fun c =>
    LinearMap.mkContinuous
      { toFun := fun α => α c
        map_add' := fun α β => rfl
        map_smul' := fun r α => rfl }
      (∏ i, ‖c i‖) fun α => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        calc ‖α c‖ ≤ ‖α‖ * ∏ i, ‖c i‖ := α.le_opNorm c
          _ = (∏ i, ‖c i‖) * ‖α‖ := mul_comm _ _
  have hev : ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := fun c α => rfl
  refine ⟨ev, ?_, hev⟩
  have key : ∀ c c' : Fin n → Euclid P,
      ‖ev c - ev c'‖ ≤ (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := by
    intro c c'
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
    rw [sub_apply, hev, hev]
    have h := α.norm_image_sub_le c c'
    rw [Fintype.card_fin] at h
    calc ‖α c - α c'‖ ≤ ‖α‖ * n * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := h
      _ = (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ * ‖α‖ := by ring
  rw [continuous_iff_continuousAt]
  intro c₀
  have hcont : Continuous fun c : Fin n → Euclid P => (n : ℝ) * max ‖c‖ ‖c₀‖ ^ (n - 1) * ‖c - c₀‖ := by
    fun_prop
  have h0 := hcont.tendsto c₀
  simp only [sub_self, norm_zero, mul_zero] at h0
  have h1 : Tendsto (fun c => ‖ev c - ev c₀‖) (𝓝 c₀) (𝓝 0) :=
    squeeze_zero (fun c => norm_nonneg (ev c - ev c₀)) (fun c => key c c₀) h0
  exact (tendsto_iff_norm_sub_tendsto_zero (E := MultiVector P n) (f := ev) (b := ev c₀)).2 h1
/-- **A continuous determinant `n`-covector on `ℝⁿ`**: some `δ ∈ Λⁿ(ℝⁿ)` (a continuous
alternating `n`-form) has `δ(e₁, …, eₙ) = 1` for the standard basis `eᵢ`.  Take the volume form
`ω` of the orientation of the standard orthonormal basis `B`; Hadamard's inequality
`|ω(v)| ≤ ∏ᵢ ‖vᵢ‖` makes it continuous, and `ω = det_B` gives `δ(e₁, …, eₙ) = det_B(B) = 1`. -/
theorem Submission.dgoj_exists_det_covector : ∀ n : ℕ, ∃ δ : Covector (Euclid n) n, δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
  intro n
  have : Fact (Module.finrank ℝ (Euclid n) = n) := ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let o : Orientation ℝ (Euclid n) (Fin n) := b.toBasis.orientation
  refine ⟨o.volumeForm.mkContinuous 1 fun m => ?_, ?_⟩
  · rw [one_mul, Real.norm_eq_abs]
    exact o.abs_volumeForm_apply_le m
  · rw [AlternatingMap.coe_mkContinuous, o.volumeForm_robust b rfl]
    have h : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b.toBasis := by
      funext i; simp [b]
    rw [h, Module.Basis.det_self]
/-- Steps 1–2 of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem): for linear isometries `ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` with
`⟨ιv, ι'w⟩ = 0` and `u` of class `C¹` on `D = B_s(0)`, the adjoint `ι*` is a left inverse of
`ι + ι'`, the derivative of the graph map `Φ(v) = z + ιv + ι'u(v)` is continuous on `D`, and
`ι* ∘ DΦ(v) = id` on `D`, because `DΦ(v) = ι + ι' ∘ Du(v)`. -/
theorem Submission.dgoj_graph_fderiv_left_inverse : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ContDiffOn ℝ 1 u (ball 0 s) → (∀ (v : Euclid n) (w : Euclid k), ι.toContinuousLinearMap.adjoint (ι v + ι' w) = v) ∧ ContinuousOn (fderiv ℝ (fun v => z + ι v + ι' (u v))) (ball (0 : Euclid n) s) ∧ ∀ v ∈ ball (0 : Euclid n) s, ∀ w : Euclid n, ι.toContinuousLinearMap.adjoint (fderiv ℝ (fun v => z + ι v + ι' (u v)) v w) = w := by
  intro n k ι ι' u z s horth hu
  -- (i) `⟨ι*(ιv + ι'w), v'⟩ = ⟨ιv, ιv'⟩ + ⟨ι'w, ιv'⟩ = ⟨v, v'⟩ + 0` for every `v'`
  have hadj : ∀ (v : Euclid n) (w : Euclid k), ι.toContinuousLinearMap.adjoint (ι v + ι' w) = v := by
    intro v w
    apply ext_inner_right ℝ
    intro v'
    rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
    have h1 : inner ℝ (ι' w) (ι.toContinuousLinearMap v') = 0 := by
      rw [real_inner_comm]; exact horth v' w
    rw [h1, add_zero]
    exact ι.inner_map_map v v'
  refine ⟨hadj, ?_, ?_⟩
  -- (ii) `Φ = (z + ι·) + ι' ∘ u` is `C¹` on the open ball, so `DΦ` is continuous there
  · have hΦ : ContDiffOn ℝ 1 (fun v => z + ι v + ι' (u v)) (ball 0 s) :=
      (contDiffOn_const.add ι.toContinuousLinearMap.contDiff.contDiffOn).add
        (ι'.toContinuousLinearMap.contDiff.comp_contDiffOn hu)
    exact hΦ.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  -- (iii) `DΦ(v) = ι + ι' ∘ Du(v)`, so `ι*(DΦ(v)w) = ι*(ιw + ι'(Du(v)w)) = w` by (i)
  · intro v hv w
    have hdu : DifferentiableAt ℝ u v :=
      (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hv)
    have hder : HasFDerivAt (fun v => z + ι v + ι' (u v))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v := by
      have h1 : HasFDerivAt (fun v => z + ι v) ι.toContinuousLinearMap v :=
        ι.toContinuousLinearMap.hasFDerivAt.const_add z
      have h2 : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v :=
        ι'.toContinuousLinearMap.hasFDerivAt.comp v hdu.hasFDerivAt
      exact h1.add h2
    rw [hder.fderiv]
    exact hadj w _

/-- **Continuous unit orientation of a `C¹` graph and the Jacobian identity** (Simon 7.4.3, via
Allard's theorem; steps 3 and 7 of the graph-cycle argument).  Let `Φ(v) = z + ιv + ι'u(v)` on
`D = B_s(0)`, `F(v) = DΦ(v)`, `b(v) = (F(v)e₁, …, F(v)eₙ)`, `J(v) = √det(F(v)* ∘ F(v))` and
`Pr(x) = ι*(x - z)`, so that `Pr ∘ Φ = id` and `ι* ∘ F(v) = id` (hence `F(v)` is injective and
`J > 0` on `D`).  With `ev` the evaluation of `n`-covectors at `n`-families and `δ` the normalized
determinant covector of `ℝⁿ`, take `ξ(x) = J(Pr x)⁻¹ ev(b(Pr x))` and `β(x) = J(Pr x) (δ ∘ ι*)`.
Both are continuous on `Σ = Φ(D)` because `Pr` maps `Σ` into `D`; `ξ(β) = δ(ι* b) = δ(e) = 1` on
`Σ`; `J(v) ξ(Φ v)(α) = α(b(v))` is the Jacobian identity, and with it the pointwise frame argument
for injective `F(v)` makes `ξ(Φ v)` a unit orientation of `range F(v)`. -/
theorem Submission.dgcr_graph_orientation_jacobian : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), 0 < n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → ∃ (ξ : Euclid (n + k) → MultiVector (n + k) n) (β : Euclid (n + k) → Covector (Euclid (n + k)) n), ContinuousOn ξ ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ ContinuousOn β ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ (∀ x ∈ (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, ξ x (β x) = 1) ∧ (∀ v ∈ ball (0 : Euclid n) s, IsUnitOrientationOf (ξ (z + ι v + ι' (u v))) (LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v : Euclid n →ₗ[ℝ] Euclid (n + k)))) ∧ ∀ v ∈ ball (0 : Euclid n) s, ∀ α : Covector (Euclid (n + k)) n, α (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => z + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => z + ι v + ι' (u v)) v).det) * ξ (z + ι v + ι' (u v)) α := by
  intro n k ι ι' u z s _hn horth _hs hu
  obtain ⟨hadj, hFc, hFinv⟩ := Submission.dgoj_graph_fderiv_left_inverse n k ι ι' u z s horth hu
  obtain ⟨ev, hevc, hev⟩ := Submission.dgoj_exists_continuous_covector_eval (n + k) n
  obtain ⟨δ, hδ⟩ := Submission.dgoj_exists_det_covector n
  -- `ι*`, the projection `Pr`, the derivative `F`, the frame `b`, the Jacobian `J` and `δ ∘ ι*`
  let ιs : Euclid (n + k) →L[ℝ] Euclid n := ι.toContinuousLinearMap.adjoint
  let Pr : Euclid (n + k) → Euclid n := fun x => ιs (x - z)
  let F : Euclid n → Euclid n →L[ℝ] Euclid (n + k) := fderiv ℝ (fun v => z + ι v + ι' (u v))
  let b : Euclid n → Fin n → Euclid (n + k) := fun v i => F v (EuclideanSpace.single i (1 : ℝ))
  let J : Euclid n → ℝ := fun v => Real.sqrt (((F v).adjoint ∘L F v).det)
  let β₀ : Covector (Euclid (n + k)) n := δ.compContinuousLinearMap ιs
  -- `Pr ∘ Φ = id`, so `Pr` maps `Σ = Φ(D)` into `D`
  have hPrΦ : ∀ v, Pr (z + ι v + ι' (u v)) = v := by
    intro v
    show ιs (z + ι v + ι' (u v) - z) = v
    rw [show z + ι v + ι' (u v) - z = ι v + ι' (u v) by abel]
    exact hadj v (u v)
  have hPrc : Continuous Pr := ιs.continuous.comp (continuous_id.sub continuous_const)
  have hmaps : MapsTo Pr ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) (ball 0 s) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hPrΦ]
    exact hv
  -- `ι* ∘ F(v) = id` on `D`: `F(v)` is injective, so `J(v) > 0`
  have hinj : ∀ v ∈ ball (0 : Euclid n) s, Injective (F v) := by
    intro v hv x y hxy
    have h := congrArg ιs hxy
    rwa [hFinv v hv x, hFinv v hv y] at h
  have hpos : ∀ v ∈ ball (0 : Euclid n) s, 0 < J v := fun v hv =>
    Real.sqrt_pos.2 (Submission.dgoj_unitOrientation_of_injective (n + k) n (F v) (hinj v hv)).1
  -- continuity of `J` and of `b` on `D`
  have hJc : ContinuousOn J (ball 0 s) := by
    have h1 : ContinuousOn (fun v => (F v).adjoint ∘L F v) (ball 0 s) :=
      ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid n)
        (F := Euclid (n + k))).continuous.comp_continuousOn hFc).clm_comp hFc
    exact Real.continuous_sqrt.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn h1)
  have hbc : ContinuousOn b (ball 0 s) :=
    continuousOn_pi.2 fun i => hFc.clm_apply continuousOn_const
  -- `(δ ∘ ι*)(b(v)) = δ(e₁, …, eₙ) = 1`
  have hβ₀ : ∀ v ∈ ball (0 : Euclid n) s, β₀ (b v) = 1 := by
    intro v hv
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    convert hδ using 2
    funext i
    exact hFinv v hv _
  refine ⟨fun x => (J (Pr x))⁻¹ • ev (b (Pr x)), fun x => J (Pr x) • β₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hJc.comp hPrc.continuousOn hmaps).inv₀ fun x hx => (hpos _ (hmaps hx)).ne').smul
      (hevc.comp_continuousOn (hbc.comp hPrc.continuousOn hmaps))
  · exact (hJc.comp hPrc.continuousOn hmaps).smul continuousOn_const
  · rintro _ ⟨v, hv, rfl⟩
    simp only [hPrΦ]
    rw [smul_apply, hev, ContinuousAlternatingMap.smul_apply, hβ₀ v hv,
      smul_eq_mul, smul_eq_mul, mul_one, inv_mul_cancel₀ (hpos v hv).ne']
  · intro v hv
    refine (Submission.dgoj_unitOrientation_of_injective (n + k) n (F v) (hinj v hv)).2 _
      fun α => ?_
    simp only [hPrΦ]
    rw [smul_apply, hev, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (hpos v hv).ne', one_mul]
  · intro v hv α
    simp only [hPrΦ]
    rw [smul_apply, hev, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (hpos v hv).ne', one_mul]
/-- **Simon Ch. 3, 1.4** (approximate tangent planes of flat sets): if `Hⁿ((A ∩ B_r(x)) \ S) = 0`
and `S` is flat at `x` along `T` (points `y ∈ S` near `x` lie within `ε‖y - x‖` of `x + T`), then an
approximate tangent plane `Q` of `A` at `x` lies in `T`.  For `y ∈ Q \ T` put `δ = dist(y, T)` and
test with `f = max(0, δ/2 - dist(·, y))`.  For small `λ > 0`, `η_{x,λ}(A) ∩ B̄_{δ/2}(y)` lies in the
`Hⁿ`-null set `η_{x,λ}((A ∩ B_r(x)) \ S)` (points of `S` blow up to within `δ/4` of `T`), so
`∫_{η_{x,λ}(A)} f dHⁿ = 0`.  In the limit `∫_Q f dHⁿ = 0`, contradicting `y ∈ spt Hⁿ⌞Q`. -/
theorem Submission.dgcr_atg_approxTangent_le_of_flat : ∀ (P n : ℕ) (S A : Set (Euclid P)) (x : Euclid P) (r : ℝ) (Q T : Submodule ℝ (Euclid P)), 0 < r → μHE[n] ((A ∩ ball x r) \ S) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ S, dist y x < ρ → ∃ t ∈ T, ‖y - x - t‖ ≤ ε * ‖y - x‖) → HasApproximateTangentSpaceAt n A x Q → Q ≤ T := by
  intro P n S A x r Q T hr hN hflat hQ y hyQ
  by_contra hyT
  -- `δ = infDist(y, T) > 0`, `T` being closed
  have hδ : 0 < infDist y (T : Set (Euclid P)) :=
    (T.closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hyT
  obtain ⟨δ, hδdef⟩ : ∃ δ, infDist y (T : Set (Euclid P)) = δ := ⟨_, rfl⟩
  rw [hδdef] at hδ
  -- `R = ‖y‖ + δ` and `ε = δ/(4R)`
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, ‖y‖ + δ = R := ⟨_, rfl⟩
  have hR : 0 < R := by rw [← hRdef]; exact add_pos_of_nonneg_of_pos (norm_nonneg y) hδ
  obtain ⟨ε, hε, hεR⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * R = δ / 4 :=
    ⟨δ / (4 * R), div_pos hδ (mul_pos four_pos hR), by field_simp⟩
  -- the test function `f = max(0, δ/2 - dist(·, y))`, supported in `B̄_{δ/2}(y)`
  have hf0 : ∀ w ∉ closedBall y (δ / 2), max 0 (δ / 2 - dist w y) = 0 := fun w hw =>
    max_eq_left (by rw [mem_closedBall, not_le] at hw; linarith)
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun w => max 0 (δ / 2 - dist w y), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall y (δ / 2)) hf0⟩
  have hf : ∀ w, f w = max 0 (δ / 2 - dist w y) := fun w => rfl
  -- flatness at `ε` gives `ρ`
  obtain ⟨ρ, hρ, hS⟩ := hflat ε hε
  have hlam₀ : 0 < min ρ r / R := div_pos (lt_min hρ hr) hR
  -- for `0 < λ < min(ρ, r)/R` the blow-up integral vanishes
  have hzero : ∀ lam ∈ Ioo 0 (min ρ r / R),
      ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x lam '' A, f w ∂μHE[n] = 0 := by
    rintro lam ⟨hlam, hlamR⟩
    -- `η_λ(A) ∩ B̄_{δ/2}(y) ⊆ η_λ((A ∩ B_r(x)) \ S)`
    have hsub : closedBall y (δ / 2) ∩ Poincare.SimonGMT.Chapter03.blowUpMap x lam '' A ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x lam '' ((A ∩ ball x r) \ S) := by
      rintro _ ⟨hw, a, ha, rfl⟩
      have hwa : a - x = lam • Poincare.SimonGMT.Chapter03.blowUpMap x lam a :=
        (smul_inv_smul₀ hlam.ne' (a - x)).symm
      obtain ⟨w, hw_def⟩ : ∃ w, Poincare.SimonGMT.Chapter03.blowUpMap x lam a = w := ⟨_, rfl⟩
      rw [hw_def] at hw hwa
      rw [mem_closedBall] at hw
      -- `‖w‖ < R`, so `‖a - x‖ = λ‖w‖ < min(ρ, r)`
      have hwR : ‖w‖ < R := by
        have := norm_sub_norm_le w y
        rw [← dist_eq_norm] at this
        linarith
      have hax : ‖a - x‖ = lam * ‖w‖ := by rw [hwa, norm_smul_of_nonneg hlam.le]
      have haxlt : ‖a - x‖ < min ρ r := by
        rw [hax]
        exact (mul_lt_mul_of_pos_left hwR hlam).trans ((lt_div_iff₀ hR).1 hlamR)
      refine ⟨a, ⟨⟨ha, ?_⟩, fun haS => ?_⟩, rfl⟩
      · rw [mem_ball, dist_eq_norm]
        exact haxlt.trans_le (min_le_right _ _)
      · -- a point of `S` would put `w` within `δ/4` of `T`
        obtain ⟨t, ht, hat⟩ :=
          hS a haS (by rw [dist_eq_norm]; exact haxlt.trans_le (min_le_left _ _))
        have hwt : dist w (lam⁻¹ • t) = lam⁻¹ * ‖a - x - t‖ := by
          rw [hwa, dist_eq_norm, ← norm_smul_of_nonneg (inv_nonneg.2 hlam.le), smul_sub,
            inv_smul_smul₀ hlam.ne']
        have h1 : infDist w (T : Set (Euclid P)) < δ / 4 :=
          calc infDist w (T : Set (Euclid P)) ≤ dist w (lam⁻¹ • t) :=
                infDist_le_dist_of_mem (T.smul_mem lam⁻¹ ht)
            _ = lam⁻¹ * ‖a - x - t‖ := hwt
            _ ≤ lam⁻¹ * (ε * ‖a - x‖) := mul_le_mul_of_nonneg_left hat (inv_nonneg.2 hlam.le)
            _ = ε * ‖w‖ := by rw [hax]; field_simp
            _ < ε * R := mul_lt_mul_of_pos_left hwR hε
            _ = δ / 4 := hεR
        have h2 : infDist y (T : Set (Euclid P)) ≤ infDist w (T : Set (Euclid P)) + dist y w :=
          infDist_le_infDist_add_dist
        rw [hδdef, dist_comm] at h2
        linarith
    -- `η_λ` is `λ⁻¹`-Lipschitz, so `η_λ((A ∩ B_r(x)) \ S)` is `Hⁿ`-null
    have hlip : LipschitzWith ‖lam⁻¹‖₊ (Poincare.SimonGMT.Chapter03.blowUpMap x lam) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        show dist (lam⁻¹ • (a - x)) (lam⁻¹ • (b - x)) ≤ _
        rw [dist_smul₀, dist_sub_right, coe_nnnorm]
    have hnull :
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' ((A ∩ ball x r) \ S)) = 0 := by
      have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
        (A := (A ∩ ball x r) \ S) n hlip.lipschitzOnWith
      rw [hN, mul_zero] at h
      exact le_antisymm h zero_le
    -- so `f = 0` a.e. for `Hⁿ ⌞ η_λ(A)`
    have hball : ((μHE[n] : Measure (Euclid P)).restrict
        (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' A)) (closedBall y (δ / 2)) = 0 := by
      rw [Measure.restrict_apply measurableSet_closedBall]
      exact measure_mono_null hsub hnull
    apply integral_eq_zero_of_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hball] with w hw
    rw [hf]
    exact hf0 w hw
  -- hence `∫_Q f dHⁿ = 0`
  have hlim : Tendsto (fun lam : ℝ =>
      ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x lam '' A, f w ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hlam₀] with lam hlam
    exact (hzero lam hlam).symm
  have hQ0 : ∫ w in (Q : Set (Euclid P)), f w ∂μHE[n] = 0 := tendsto_nhds_unique (hQ.2 f) hlim
  -- but `∫_Q f dHⁿ > 0`: `Hⁿ ⌞ Q` is locally finite with support `Q ∋ y`, and `f > 0` near `y`
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
  have hnn : 0 ≤ ⇑f := fun w => by
    show (0 : ℝ) ≤ f w
    rw [hf]
    exact le_max_left _ _
  have hfi : Integrable (⇑f) ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    (map_continuous f).integrable_of_hasCompactSupport f.hasCompactSupport
  have hy : y ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
    rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
    exact hyQ
  have hpos : 0 < ∫ w in (Q : Set (Euclid P)), f w ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hnn hfi]
    refine (Measure.mem_support_iff_forall y).1 hy _
      (mem_of_superset (ball_mem_nhds y (half_pos hδ)) fun w hw => ?_)
    rw [mem_ball] at hw
    rw [Function.mem_support, hf]
    exact (lt_max_of_lt_right (by linarith)).ne'
  exact hpos.ne' hQ0
/-- **Simon 7.4.3** (proof, via Allard's Theorem 5.2 of Ch. 5): the graph `Σ = Φ(D)`,
`Φ(v) = z + ιv + ι'u(v)` with orthogonal linear isometries `ι`, `ι'`, is flat at `Φ(v₀)` along
`range DΦ(v₀)` (the step identifying its approximate tangent plane, Ch. 3, 1.4).  Pythagoras gives
`‖v − v₀‖ ≤ ‖Φ(v) − Φ(v₀)‖`, so points of `Φ(D)` near `Φ(v₀)` come from `v` near `v₀`, where
`t = DΦ(v₀)(v − v₀)` has `‖Φ(v) − Φ(v₀) − t‖ ≤ ε‖v − v₀‖ ≤ ε‖Φ(v) − Φ(v₀)‖`. -/
theorem Submission.dgcr_atg_graph_image_flat : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (D : Set (Euclid n)) (v₀ : Euclid n), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → DifferentiableAt ℝ u v₀ → ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ (fun v => z + ι v + ι' (u v)) '' D, dist y (z + ι v₀ + ι' (u v₀)) < ρ → ∃ t ∈ LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v₀ : Euclid n →ₗ[ℝ] Euclid (n + k)), ‖y - (z + ι v₀ + ι' (u v₀)) - t‖ ≤ ε * ‖y - (z + ι v₀ + ι' (u v₀))‖ := by
  intro n k ι ι' u z D v₀ horth hu ε hε
  set Φ : Euclid n → Euclid (n + k) := fun v => z + ι v + ι' (u v) with hΦ
  -- coercivity: `‖Φ v − Φ v₀‖² = ‖v − v₀‖² + ‖u v − u v₀‖²` by Pythagoras
  have hcoer : ∀ v, ‖v - v₀‖ ≤ ‖Φ v - Φ v₀‖ := by
    intro v
    have hsplit : Φ v - Φ v₀ = ι (v - v₀) + ι' (u v - u v₀) := by
      simp only [hΦ, map_sub]
      abel
    have hpyth : ‖Φ v - Φ v₀‖ * ‖Φ v - Φ v₀‖ =
        ‖v - v₀‖ * ‖v - v₀‖ + ‖u v - u v₀‖ * ‖u v - u v₀‖ := by
      rw [hsplit, ← ι.norm_map (v - v₀), ← ι'.norm_map (u v - u v₀)]
      exact norm_add_sq_eq_norm_sq_add_norm_sq_real (horth _ _)
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2
      (hpyth ▸ le_add_of_nonneg_right (mul_self_nonneg _))
  -- `Φ = z + ι + ι' ∘ u` is differentiable at `v₀`
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ v₀) v₀ :=
    (((differentiableAt_const z).add ι.toContinuousLinearMap.differentiableAt).add
      (ι'.toContinuousLinearMap.differentiableAt.comp v₀ hu)).hasFDerivAt
  -- little-o: `‖Φ v − Φ v₀ − DΦ(v₀)(v − v₀)‖ ≤ ε‖v − v₀‖` whenever `dist v v₀ < ρ`
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (hΦd.isLittleO.bound hε)
  refine ⟨ρ, hρ, ?_⟩
  -- `y = Φ v` with `‖v − v₀‖ ≤ ‖y − Φ v₀‖ < ρ`; take `t = DΦ(v₀)(v − v₀)`
  rintro y ⟨v, -, rfl⟩ hy
  refine ⟨fderiv ℝ Φ v₀ (v - v₀), LinearMap.mem_range_self _ _, ?_⟩
  have hv : dist v v₀ < ρ := by
    rw [dist_eq_norm] at hy ⊢
    exact (hcoer v).trans_lt hy
  calc ‖Φ v - Φ v₀ - fderiv ℝ Φ v₀ (v - v₀)‖ ≤ ε * ‖v - v₀‖ := hball hv
    _ ≤ ε * ‖Φ v - Φ v₀‖ := mul_le_mul_of_nonneg_left (hcoer v) hε.le
/-- Step 1 of identifying the approximate tangent plane of a `C¹` graph (used for Simon 7.4.3):
for linear isometries `ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` with `⟨ιv, ι'w⟩ = 0` and `u`
differentiable at `v₀`, the graph map `Φ(v) = z + ιv + ι'u(v)` has `DΦ(v₀) = ι + ι' ∘ Du(v₀)`.
By Pythagoras `‖DΦ(v₀)h‖² = ‖h‖² + ‖Du(v₀)h‖²`, so `DΦ(v₀)` is injective and its range is
`n`-dimensional. -/
theorem Submission.dgcr_atg_graph_tangent_finrank : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (v₀ : Euclid n), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → DifferentiableAt ℝ u v₀ → Module.finrank ℝ (LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v₀ : Euclid n →ₗ[ℝ] Euclid (n + k))) = n := by
  intro n k ι ι' u z v₀ horth hu
  -- `DΦ(v₀) = ι + ι' ∘ Du(v₀)` by the sum and chain rules
  have hΦ : HasFDerivAt (fun v => z + ι v + ι' (u v))
      (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ u v₀) v₀ :=
    (ι.toContinuousLinearMap.hasFDerivAt.const_add z).add
      (ι'.toContinuousLinearMap.hasFDerivAt.comp v₀ hu.hasFDerivAt)
  rw [hΦ.fderiv]
  -- injectivity: `ιh + ι'(Du(v₀)h) = 0` gives `0 = ‖h‖² + ‖Du(v₀)h‖²`, so `h = 0`
  have hinj : Function.Injective ((ι.toContinuousLinearMap +
      ι'.toContinuousLinearMap ∘L fderiv ℝ u v₀ : Euclid n →L[ℝ] Euclid (n + k)) :
        Euclid n →ₗ[ℝ] Euclid (n + k)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hh
    have h0 : ι h + ι' (fderiv ℝ u v₀ h) = 0 := by simpa using hh
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ) (ι h)
      (ι' (fderiv ℝ u v₀ h)) (horth _ _)
    rw [h0, norm_zero, ι.norm_map, ι'.norm_map] at hpyth
    have hh0 : ‖h‖ * ‖h‖ = 0 := by
      linarith [mul_self_nonneg ‖h‖, mul_self_nonneg ‖fderiv ℝ u v₀ h‖]
    simpa using hh0
  -- `dim range DΦ(v₀) = dim ℝⁿ = n`
  rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]

/-- **Simon Ch. 3, 1.4–1.5** on a `C¹` graph (used for 7.4.3, via Allard's Theorem 5.2 of Ch. 5):
let `Φ(v) = z + ιv + ι'u(v)` with `u` of class `C¹` on `D = B_s(0) ∋ v₀`.  If `Hⁿ`-almost all of
`A ∩ B_r(Φ(v₀))` lies on the graph `Φ(D)`, then an approximate tangent plane `Q` of `A` at
`Φ(v₀)` is the graph's tangent plane `range DΦ(v₀)`.  The graph is flat at `Φ(v₀)` along
`range DΦ(v₀)`, which therefore contains `Q`, and both planes are `n`-dimensional. -/
theorem Submission.dgcr_approxTangent_eq_graph_tangent : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s r : ℝ) (A : Set (Euclid (n + k))) (v₀ : Euclid n) (Q : Submodule ℝ (Euclid (n + k))), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ContDiffOn ℝ 1 u (ball 0 s) → v₀ ∈ ball (0 : Euclid n) s → 0 < r → μHE[n] ((A ∩ ball (z + ι v₀ + ι' (u v₀)) r) \ ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s)) = 0 → HasApproximateTangentSpaceAt n A (z + ι v₀ + ι' (u v₀)) Q → Q = LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v₀ : Euclid n →ₗ[ℝ] Euclid (n + k)) := by
  intro n k ι ι' u z s r A v₀ Q horth hu hv₀ hr hnull hQ
  -- `u` is `C¹` on the open ball `D ∋ v₀`, hence differentiable at `v₀`
  have hdiff : DifferentiableAt ℝ u v₀ :=
    (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hv₀)
  -- `Φ(D)` is flat at `Φ(v₀)` along `L = range DΦ(v₀)`, so `Q ≤ L`
  have hle := Submission.dgcr_atg_approxTangent_le_of_flat (n + k) n _ A _ r Q _ hr hnull
    (Submission.dgcr_atg_graph_image_flat n k ι ι' u z (ball (0 : Euclid n) s) v₀ horth hdiff) hQ
  -- `dim Q = n = dim L`
  have hL := Submission.dgcr_atg_graph_tangent_finrank n k ι ι' u z v₀ horth hdiff
  exact Submodule.eq_of_le_of_finrank_eq hle (hQ.finrank_eq.trans hL.symm)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
