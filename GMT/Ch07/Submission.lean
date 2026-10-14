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
/-- **Isolation of a ray** (steps 2–3 of the proof of `idtp_fons_odc_ray_orientation`): for a
finite set `F` of unit vectors, a unit vector `e` and `t₀ > 0`, some ball about `t₀e` meets the
open rays `{te' : t > 0}`, `e' ∈ F`, only inside `{te : t > 0}`.  The closed rays
`{se' : s ≥ 0}`, `e' ∈ F ∖ {e}`, are closed (`s ↦ se'` is an isometry of `ℝ`) and miss `t₀e`
(comparing norms in `t₀e = se'` gives `s = t₀`, hence `e' = e`); take a ball about `t₀e` avoiding
their finite union. -/
theorem Submission.idtp_fons_odc_ro_ray_isolation : ∀ (P : ℕ) (F : Finset (Euclid P)) (e : Euclid P) (t₀ : ℝ), (∀ e' ∈ F, ‖e'‖ = 1) → ‖e‖ = 1 → 0 < t₀ → ∃ δ : ℝ, 0 < δ ∧ ball (t₀ • e) δ ∩ (⋃ e' ∈ F, (fun t : ℝ => t • e') '' Ioi 0) ⊆ (fun t : ℝ => t • e) '' Ioi 0 := by
  classical
  intro P F e t₀ hF he ht₀
  -- `K`: the closed rays `{s • e' : s ≥ 0}` of the directions `e' ∈ F` other than `e`
  have hK : IsClosed (⋃ e' ∈ F.erase e, (fun t : ℝ => t • e') '' Ici 0) := by
    refine isClosed_biUnion_finset fun e' he' => ?_
    -- `s ↦ s • e'` is an isometry of `ℝ` (as `‖e'‖ = 1`), hence a closed embedding
    have hiso : Isometry fun t : ℝ => t • e' := Isometry.of_dist_eq fun s s' => by
      rw [dist_eq_norm, ← sub_smul, norm_smul, hF e' (Finset.mem_of_mem_erase he'), mul_one,
        Real.dist_eq, Real.norm_eq_abs]
    exact hiso.isClosedEmbedding.isClosedMap _ isClosed_Ici
  -- `t₀ • e ∉ K`: comparing norms in `s • e' = t₀ • e` gives `s = t₀`, hence `e' = e`
  have hx : t₀ • e ∉ ⋃ e' ∈ F.erase e, (fun t : ℝ => t • e') '' Ici 0 := by
    simp only [mem_iUnion, mem_image, mem_Ici, not_exists, not_and]
    intro e' he' s hs hse
    have hs' : s = t₀ := by
      have h := congrArg norm hse
      rwa [norm_smul, norm_smul, hF e' (Finset.mem_of_mem_erase he'), he, mul_one, mul_one,
        Real.norm_of_nonneg hs, Real.norm_of_nonneg ht₀.le] at h
    rw [hs'] at hse
    exact (Finset.mem_erase.mp he').1 (smul_right_injective _ ht₀.ne' hse)
  -- a ball about `t₀ • e` inside the open complement of `K`
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl _ hx
  refine ⟨δ, hδ, ?_⟩
  rintro y ⟨hyB, hyU⟩
  simp only [mem_iUnion, mem_image, mem_Ioi] at hyU
  obtain ⟨e'', he'', t, ht, rfl⟩ := hyU
  by_cases h : e'' = e
  · subst h
    exact ⟨t, ht, rfl⟩
  · exfalso
    refine hball hyB ?_
    simp only [mem_iUnion, mem_image, mem_Ici]
    exact ⟨e'', Finset.mem_erase.mpr ⟨h, he''⟩, t, ht.le, rfl⟩
/-- **Simon 7.3.3, proof of (2), formula (10)**: `ω₁ = 2`, and for `‖v‖ = 1` the line
`γ(t) = p + t v` is a measurable embedding with `H¹⌞γ(I) = γ_#(ℒ¹⌞I)` and `H¹(γ(I)) = ℒ¹(I)`
for every `I ⊆ ℝ`.  `γ` is an isometry, `μHE[1] = volume` on `ℝ` and `μHE[1]` is preserved by
isometries; the unit ball of `ℝ¹` is the image of `(-1, 1)` under `t ↦ 0 + t e₀`. -/
theorem Submission.idtp_fons_odc_line_hausdorff : unitBallVolume 1 = 2 ∧ ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → MeasurableEmbedding (fun t : ℝ => p + t • v) ∧ ∀ I : Set ℝ, (μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => p + t • v) '' I) = Measure.map (fun t : ℝ => p + t • v) (volume.restrict I) ∧ (μHE[1] : Measure (Euclid P)) ((fun t : ℝ => p + t • v) '' I) = volume I := by
  -- `H¹ = ℒ¹` on `ℝ`, since `finrank ℝ ℝ = 1`
  have hR : (μHE[1] : Measure ℝ) = volume := by
    simpa only [Module.finrank_self] using
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  -- `γ(t) = p + t v` is an isometry when `‖v‖ = 1`
  have hiso : ∀ (P : ℕ) (p v : Euclid P), ‖v‖ = 1 → Isometry (fun t : ℝ => p + t • v) :=
    fun P p v hv => Isometry.of_dist_eq fun s t => by
      show dist (p + s • v) (p + t • v) = dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  refine ⟨?_, fun P p v hv => ?_⟩
  · -- `ω₁ = 2`: the unit ball of `ℝ¹` is the image of `(-1, 1)` under `t ↦ 0 + t e₀`
    set e : Euclid 1 := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have hball : ball (0 : Euclid 1) 1 = (fun t : ℝ => (0 : Euclid 1) + t • e) '' Ioo (-1) 1 := by
      ext x
      constructor
      · intro hx
        have hxe : x 0 • e = x := by
          ext i
          rw [Fin.fin_one_eq_zero i]
          simp [e]
        rw [mem_ball_zero_iff, ← hxe, norm_smul, he, mul_one, Real.norm_eq_abs] at hx
        exact ⟨x 0, abs_lt.mp hx, (zero_add _).trans hxe⟩
      · rintro ⟨t, ht, rfl⟩
        rw [mem_ball_zero_iff]
        show ‖(0 : Euclid 1) + t • e‖ < 1
        rw [zero_add, norm_smul, he, mul_one, Real.norm_eq_abs]
        exact abs_lt.mpr ht
    rw [unitBallVolume, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 1, hball,
      (hiso 1 0 e he).euclideanHausdorffMeasure_image, hR, Real.volume_Ioo]
    norm_num
  · have hemb : MeasurableEmbedding (fun t : ℝ => p + t • v) :=
      (hiso P p v hv).isClosedEmbedding.measurableEmbedding
    refine ⟨hemb, fun I => ⟨?_, ?_⟩⟩
    · -- `H¹⌞γ(I) = (H¹⌞range γ)⌞γ(I) = (γ_#ℒ¹)⌞γ(I) = γ_#(ℒ¹⌞γ⁻¹(γ(I))) = γ_#(ℒ¹⌞I)`
      rw [← Measure.restrict_restrict_of_subset (image_subset_range _ I),
        ← (hiso P p v hv).map_euclideanHausdorffMeasure, hR, hemb.restrict_map,
        hemb.injective.preimage_image]
    · rw [(hiso P p v hv).euclideanHausdorffMeasure_image, hR]

/-- **Simon 7.3.3, proof of (2), formula (10)**, along one ray: let `(M, θ, ξ)` be a
`1`-dimensional integer multiplicity triple in `ℝᴾ`, `‖e‖ = 1`, `γ(t) = t e`, and `ξ = ±e`
`H¹`-a.e. on `M ∩ γ(0, ∞)`.  With `β = ⟪e, ·⟫`, `g(t) = 1_M(t e) θ(t e) ⟨β, ξ(t e)⟩` is locally
integrable, a.e. integer valued on `(0, ∞)` (as `⟨β, ±e⟩ = ±1`), and
`∫_{M ∩ γ(0, ∞)} θ ⟨ω, ξ⟩ dH¹ = ∫₀^∞ g(t) ω(t e)(e) dt` for every test `1`-form `ω`: a.e. on
`M ∩ γ(0, ∞)`, `⟨ω, ξ⟩ = ⟨β, ξ⟩ ω(e)`, and `γ` carries `ℒ¹⌞I` to `H¹⌞γ(I)`. -/
theorem Submission.idtp_fons_odc_ra_single_ray : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (e : Euclid P), ‖e‖ = 1 → (∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict (R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0)), R.orient x = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ R.orient x = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e)) → ∃ g : ℝ → ℝ, LocallyIntegrableOn g (Ioi 0) ∧ (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ, g t = k) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] = ∫ t in Ioi (0 : ℝ), g t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  intro P R e he hξ
  have hM := R.measurableSet_carrier
  -- `γ(t) = t e` is a measurable embedding with `H¹⌞γ(I) = γ_#(ℒ¹⌞I)`
  obtain ⟨hemb, hmap⟩ := Submission.idtp_fons_odc_line_hausdorff.2 P 0 e he
  simp only [zero_add] at hemb hmap
  replace hmap := fun I => (hmap I).1
  -- the covector `β = ⟪e, ·⟫` has `β(e) = ‖e‖² = 1`
  obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) 1, β (fun _ => e) = 1 :=
    ⟨ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e), by
      rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, innerSL_apply_apply,
        real_inner_self_eq_norm_sq, he, one_pow]⟩
  -- for `ξ = ±e`: `⟨β, ξ⟩ = ±1` and `⟨α, ξ⟩ = ⟨β, ξ⟩ α(e)`
  have hsign : ∀ ξ : MultiVector P 1,
      (ξ = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨
        ξ = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e)) →
      (ξ β = 1 ∨ ξ β = -1) ∧ ∀ α : Covector (Euclid P) 1, ξ α = ξ β * α (fun _ => e) := by
    rintro ξ (rfl | rfl) <;> simp [hβ]
  refine ⟨fun t => R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e), ?_, ?_,
    fun ω => ?_⟩
  · -- on a compact `k`, `g` is integrable since `θ ⟨β, ξ⟩` is `H¹`-integrable on `M ∩ γ(k)`
    refine (locallyIntegrable_iff.2 fun k hk => ?_).locallyIntegrableOn _
    have h1 : Integrable (R.carrier.indicator fun x => (R.mult x : ℝ) * R.orient x β)
        ((μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => t • e) '' k)) := by
      rw [integrable_indicator_iff hM, IntegrableOn, Measure.restrict_restrict hM]
      exact Submission.lcn_mult_mul_orient_apply_integrableOn P 1 univ _ R
        (hk.image (by fun_prop)) (subset_univ _) β
    rw [hmap] at h1
    exact hemb.integrable_map_iff.1 h1
  · -- for a.e. `t > 0`, `g(t) = ±θ(t e)` if `t e ∈ M` (`ξ(t e) = ±e`) and `g(t) = 0` otherwise
    rw [← Measure.restrict_restrict hM, ae_restrict_iff' hM, hmap, hemb.ae_map_iff] at hξ
    filter_upwards [hξ] with t ht
    by_cases hx : t • e ∈ R.carrier
    · rw [indicator_of_mem hx]
      rcases (hsign _ (ht hx)).1 with h1 | h1
      · exact ⟨R.mult (t • e), by rw [h1, mul_one, Int.cast_natCast]⟩
      · exact ⟨-(R.mult (t • e) : ℤ), by rw [h1, mul_neg_one, Int.cast_neg, Int.cast_natCast]⟩
    · exact ⟨0, by rw [indicator_of_notMem hx, Int.cast_zero]⟩
  · -- `θ ⟨ω, ξ⟩ = θ ⟨β, ξ⟩ ω(e)` a.e. on `M ∩ γ(0, ∞)`; extend by `0` off `M`, pull back by `γ`
    calc ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1]
        = ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x β *
            (ω : DifferentialForm (Euclid P) 1) x (fun _ => e) ∂μHE[1] := by
          refine integral_congr_ae ?_
          filter_upwards [hξ] with x hx
          rw [(hsign _ hx).2 ((ω : DifferentialForm (Euclid P) 1) x), mul_assoc]
      _ = ∫ x in (fun t : ℝ => t • e) '' Ioi 0,
            R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) x *
              (ω : DifferentialForm (Euclid P) 1) x (fun _ => e) ∂μHE[1] := by
          rw [inter_comm, ← setIntegral_indicator hM]
          congr 1
          funext x
          exact Set.indicator_mul_left _ _ _
      _ = ∫ t in Ioi (0 : ℝ), R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e) *
            (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
          rw [hmap, hemb.integral_map]

/-- **Splitting the action along finitely many rays** (Simon Ch. 6, 3.1 (‡)).  Let
`R = (M, θ, ξ)` be a `1`-dimensional integer multiplicity triple in `ℝᴾ` and `F` a finite set of
unit vectors such that `H¹`-almost all of `M` lies on the open rays `ray(e) = {t e : t > 0}`,
`e ∈ F`.  Then `τ(M, θ, ξ)(ω) = Σ_{e ∈ F} ∫_{M ∩ ray(e)} θ ⟨ω, ξ⟩ dH¹` for every `ω ∈ 𝒟¹(ℝᴾ)`:
the pieces `M ∩ ray(e)` are Borel (`t ↦ t e` is an isometric, hence measurable, embedding of
`ℝ`), pairwise disjoint (rays of distinct unit vectors do not meet), their union is `M` up to an
`H¹`-null set, and the integrand is `H¹⌞M`-integrable. -/
theorem Submission.idtp_fons_odc_ra_action_split : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, R.action (ω : DifferentialForm (Euclid P) 1) = ∑ e ∈ F, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] := by
  intro P R F hF hnull ω
  /- Step 1: the integrand `θ ⟨ω, ξ⟩` is `H¹`-integrable on `M`, hence on each `M ∩ ray(e)`. -/
  have hint : IntegrableOn
      (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x))
      R.carrier μHE[1] :=
    Submission.regcomp_rim_action_integrable P 1 univ R ω
  /- Step 2: for a unit vector `e`, `t ↦ t • e` is an isometry `ℝ → ℝᴾ`, hence a closed and
  measurable embedding, so the ray `ray(e) = (0, ∞) • e` is Borel. -/
  have hray : ∀ e ∈ F, MeasurableSet ((fun t : ℝ => t • e) '' Ioi 0) := by
    intro e he
    have hiso : Isometry (fun t : ℝ => t • e) := Isometry.of_dist_eq fun s t => by
      show dist (s • e) (t • e) = dist s t
      rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, hF e he, mul_one]
    exact hiso.isClosedEmbedding.measurableEmbedding.measurableSet_image.2 measurableSet_Ioi
  /- Step 3: rays of distinct unit vectors are disjoint: `s • e' = t • e` with `s, t > 0` gives
  `s = ‖s • e'‖ = ‖t • e‖ = t`, and then `e' = e`. -/
  have hdisj : (F : Set (Euclid P)).Pairwise
      (Disjoint on fun e => R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0) := by
    intro e he e' he' hne
    refine Set.disjoint_left.2 ?_
    rintro x ⟨-, t, ht, rfl⟩ ⟨-, s, hs, hst⟩
    have hst' : s • e' = t • e := hst
    have hts : s = t := by
      have h := congrArg norm hst'
      rwa [norm_smul, norm_smul, hF e he, hF e' he', mul_one, mul_one,
        Real.norm_of_nonneg (mem_Ioi.1 hs).le, Real.norm_of_nonneg (mem_Ioi.1 ht).le] at h
    subst hts
    exact hne (smul_right_injective (Euclid P) (mem_Ioi.1 hs).ne' hst').symm
  /- Step 4: finite additivity over the disjoint measurable pieces `M ∩ ray(e)`, `e ∈ F`. -/
  have hsplit : ∫ x in ⋃ e ∈ F, R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0,
      (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] =
      ∑ e ∈ F, ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0,
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] :=
    integral_biUnion_finset F (fun e he => R.measurableSet_carrier.inter (hray e he)) hdisj
      fun e _ => hint.mono_set inter_subset_left
  /- Step 5: `M` and `⋃_{e ∈ F} M ∩ ray(e)` differ by a subset of the `H¹`-null set
  `M ∖ ⋃_{e ∈ F} ray(e)`. -/
  have hae : R.carrier =ᵐ[μHE[1]] ⋃ e ∈ F, R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0 := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ hnull, ?_⟩
    · rintro x ⟨hxM, hxA⟩
      refine ⟨hxM, ?_⟩
      simp only [mem_compl_iff, mem_iUnion, not_exists] at hxA ⊢
      exact fun e he hxe => hxA e he ⟨hxM, hxe⟩
    · rw [Set.sdiff_eq_empty.2 (iUnion₂_subset fun e _ => inter_subset_left), measure_empty]
  /- Step 6: `R.action ω = ∫_M f = ∫_{⋃ M ∩ ray(e)} f = Σ_e ∫_{M ∩ ray(e)} f`. -/
  rw [IMRep.action, setIntegral_congr_set hae, hsplit]
/-- **Simon 7.3.3, proof of (2), step 4a**: for `‖u‖ = 1` and `f ≥ 0` continuous with compact
support and `f(u) > 0`, `∫_{ℝu} f dH¹ > 0`.  By `idtp_fons_odc_line_hausdorff` (`p = 0`, `v = u`,
`I = ℝ`), `H¹⌞ℝu = γ_#ℒ¹` for `γ(t) = t u`, so the integral is `∫_ℝ f(t u) dt`; `γ` is an
isometry, so `t ↦ f(t u)` is continuous, nonnegative, compactly supported and positive at `1`. -/
theorem Submission.idtp_fons_odc_ro_line_integral_pos : ∀ (P : ℕ) (u : Euclid P) (f : Euclid P → ℝ), ‖u‖ = 1 → Continuous f → HasCompactSupport f → (∀ y, 0 ≤ f y) → 0 < f u → 0 < ∫ y in (Submodule.span ℝ {u} : Set (Euclid P)), f y ∂(μHE[1] : Measure (Euclid P)) := by
  intro P u f hu hf hfc hf0 hfu
  obtain ⟨hemb, hline⟩ := Submission.idtp_fons_odc_line_hausdorff.2 P 0 u hu
  -- `γ(t) = 0 + t u` is an isometry
  have hiso : Isometry (fun t : ℝ => (0 : Euclid P) + t • u) :=
    Isometry.of_dist_eq fun s t => by
      show dist ((0 : Euclid P) + s • u) (0 + t • u) = dist s t
      rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hu, mul_one, Real.dist_eq,
        Real.norm_eq_abs]
  -- the line `ℝu` is `γ(ℝ)`
  have hspan : (Submodule.span ℝ {u} : Set (Euclid P)) =
      (fun t : ℝ => (0 : Euclid P) + t • u) '' univ := by
    ext y
    simp only [SetLike.mem_coe, Submodule.mem_span_singleton, image_univ, mem_range, zero_add]
  -- `∫_{ℝu} f dH¹ = ∫_ℝ f(γ t) dt`
  rw [hspan, (hline univ).1, Measure.restrict_univ, hemb.integral_map]
  exact (hf.comp hiso.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hfc.comp_isClosedEmbedding hiso.isClosedEmbedding) (fun t => hf0 _) (x := 1)
    (by simpa using hfu.ne')

/-- **Simon Ch. 3, Definition 1.4** (step 4 of `idtp_fons_odc_ray_orientation`): if near `x` the
set `M` lies on the line `x + ℝv` up to an `H¹`-null set `N`, every `1`-dimensional approximate
tangent space `Q` of `M` at `x` is `ℝv`.  As `finrank Q = 1 = finrank ℝv` it suffices to exclude a
unit vector `u ∈ Q \ ℝv`, for which `Q = ℝu`.  With `d = dist(u, ℝv) > 0` and the bump
`f = max(0, d/2 - |· - u|) ∈ C_c`, `line_integral_pos` gives `∫_Q f dH¹ > 0`.  But for
`0 < ρ < δ/(1 + d)` every `y ∈ η_{x,ρ}(M)` with `f(y) ≠ 0` has `x + ρy ∈ B_δ(x)` off the line,
so `y` lies in the `H¹`-null set `η_{x,ρ}(N)` (`η_{x,ρ}` is Lipschitz) and
`∫_{η_{x,ρ}(M)} f dH¹ = 0`; uniqueness of limits as `ρ ↓ 0` then forces `∫_Q f dH¹ = 0`. -/
theorem Submission.idtp_fons_odc_ro_tangent_line : ∀ (P : ℕ) (M N : Set (Euclid P)) (x v : Euclid P) (δ : ℝ) (Q : Submodule ℝ (Euclid P)), v ≠ 0 → 0 < δ → (μHE[1] : Measure (Euclid P)) N = 0 → M ∩ ball x δ ⊆ range (fun s : ℝ => x + s • v) ∪ N → HasApproximateTangentSpaceAt 1 M x Q → Q = Submodule.span ℝ {v} := by
  intro P M N x v δ Q hv hδ hN hloc hQ
  -- `η_{x,ρ}(S) = {y | x + ρ y ∈ S}` for `ρ ≠ 0`
  have himage : ∀ (S : Set (Euclid P)) {ρ : ℝ}, ρ ≠ 0 →
      Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S = (fun y => x + ρ • y) ⁻¹' S := by
    intro S ρ hρ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ] using hz
    · intro hy
      exact ⟨_, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hρ]⟩
  -- `η_{x,ρ}` is `|ρ⁻¹|`-Lipschitz, so `η_{x,ρ}(N)` is `H¹`-null
  have hnull : ∀ ρ : ℝ,
      (μHE[1] : Measure (Euclid P)) (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' N) = 0 := by
    intro ρ
    have hlip : LipschitzWith ‖ρ⁻¹‖₊ (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dist_smul₀, dist_sub_right,
          coe_nnnorm, le_refl]
    refine nonpos_iff_eq_zero.1 ?_
    calc _ ≤ (‖ρ⁻¹‖₊ : ℝ≥0∞) ^ 1 * μHE[1] N :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn 1
            hlip.lipschitzOnWith
      _ = 0 := by rw [hN, mul_zero]
  -- `x + ρ y` lies on the line `x + ℝv` iff `y ∈ ℝv` (`ρ ≠ 0`)
  have hline : ∀ (y : Euclid P) {ρ : ℝ}, ρ ≠ 0 →
      (x + ρ • y ∈ range (fun s : ℝ => x + s • v) ↔ y ∈ Submodule.span ℝ {v}) := by
    intro y ρ hρ
    simp only [mem_range, add_right_inj, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨ρ⁻¹ * s, by rw [mul_smul, hs, smul_smul, inv_mul_cancel₀ hρ, one_smul]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ρ * a, mul_smul _ _ _⟩
  -- `finrank Q = 1 = finrank ℝv`, so it suffices to show `Q ≤ ℝv`
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hQ.1, finrank_span_singleton hv])
  by_contra hQL
  -- a unit vector `u ∈ Q \ ℝv`; then `Q = ℝu`
  obtain ⟨u, huQ, huL, hu⟩ : ∃ u ∈ Q, u ∉ Submodule.span ℝ {v} ∧ ‖u‖ = 1 := by
    obtain ⟨w, hwQ, hwL⟩ := IsConcreteLE.not_le_iff_exists.1 hQL
    have hw : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 fun h => hwL (h ▸ Submodule.zero_mem _)
    refine ⟨‖w‖⁻¹ • w, Q.smul_mem _ hwQ, fun h => hwL ?_, ?_⟩
    · simpa [smul_smul, mul_inv_cancel₀ hw] using (Submodule.span ℝ {v}).smul_mem ‖w‖ h
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw]
  have hspan : Submodule.span ℝ {u} = Q :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 huQ)
      (by rw [hQ.1, finrank_span_singleton (by rintro rfl; simp at hu)])
  -- `d = dist(u, ℝv) > 0` and the bump `f = max(0, d/2 - |· - u|)`
  obtain ⟨d, hdu, hd⟩ : ∃ d, d = infDist u (Submodule.span ℝ {v} : Set (Euclid P)) ∧ 0 < d :=
    ⟨_, rfl, ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos
      ⟨0, Submodule.zero_mem _⟩).1 huL⟩
  obtain ⟨f, hf⟩ : ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∀ y, f y = max 0 (d / 2 - ‖y - u‖) :=
    ⟨⟨⟨fun y => max 0 (d / 2 - ‖y - u‖), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall u (d / 2)) fun y hy => max_eq_left (by
        rw [mem_closedBall, dist_eq_norm, not_le] at hy; linarith)⟩, fun y => rfl⟩
  -- by `line_integral_pos`, the limit `∫_Q f dH¹ = ∫_{ℝu} f dH¹` is positive
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), f y ∂(μHE[1] : Measure (Euclid P)) := by
    rw [← hspan]
    refine Submission.idtp_fons_odc_ro_line_integral_pos P u f hu (map_continuous f)
      f.hasCompactSupport (fun y => by rw [hf]; exact le_max_left _ _) ?_
    rw [hf, sub_self, norm_zero, sub_zero]
    exact lt_max_of_lt_right (half_pos hd)
  -- for `0 < ρ < δ / (1 + d)`, `f = 0` on `η_{x,ρ}(M)` off the null set `η_{x,ρ}(N)`
  have hzero : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' M,
      f y ∂(μHE[1] : Measure (Euclid P)) = 0 := by
    have h1d : (0 : ℝ) < 1 + d := by linarith
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ h1d)] with ρ ⟨hρ0, hρ⟩
    rw [lt_div_iff₀ h1d] at hρ
    refine setIntegral_eq_zero_of_ae_eq_zero (ae_iff.2 (measure_mono_null (fun y hy => ?_)
      (hnull ρ)))
    simp only [mem_ofPred_eq, not_imp] at hy
    rw [himage _ hρ0.ne'] at hy ⊢
    obtain ⟨hyM, hfy⟩ := hy
    have hyu : ‖y - u‖ < d / 2 := by
      by_contra h
      exact hfy (by rw [hf]; exact max_eq_left (by linarith [not_lt.1 h]))
    have hball : x + ρ • y ∈ ball x δ := by
      have hy1 : ‖y‖ < 1 + d := by linarith [norm_sub_norm_le y u]
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
      exact (mul_lt_mul_of_pos_left hy1 hρ0).trans hρ
    rcases hloc (show x + ρ • y ∈ M ∩ ball x δ from ⟨hyM, hball⟩) with hyl | hyN
    · exfalso
      have h := infDist_le_dist_of_mem (x := u) (SetLike.mem_coe.2 ((hline y hρ0.ne').1 hyl))
      rw [← hdu, dist_comm, dist_eq_norm] at h
      linarith
    · exact hyN
  -- uniqueness of the limit as `ρ ↓ 0` contradicts `∫_Q f dH¹ > 0`
  exact hpos.ne' (tendsto_nhds_unique (hQ.2 f)
    (tendsto_const_nhds.congr' (hzero.mono fun ρ h => h.symm)))
/-- A unit orientation of the line `ℝe`, `‖e‖ = 1`, is `±e`, i.e. `ξ = ±(α ↦ α(e))` (Simon 6.1.1,
6.2.2 with `n = 1`).  An orthonormal `τ : Fin 1 → ℝᴾ` spanning `ℝe` has `τ₀ = c e` with
`|c| = ‖τ₀‖ = 1`, and `α(τ) = c α(e)` by multilinearity, so `⟨α, ξ⟩ = ±α(τ) = ±α(e)`. -/
theorem Submission.idtp_fons_odc_ro_line_orientation : ∀ (P : ℕ) (e : Euclid P) (ξ : MultiVector P 1), ‖e‖ = 1 → IsUnitOrientationOf ξ (Submodule.span ℝ {e}) → ξ = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ ξ = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) := by
  intro P e ξ he ⟨τ, hτ, hspan, hξ⟩
  -- `τ 0 ∈ span (range τ) = ℝe`, so `τ 0 = c • e`
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (hspan ▸ Submodule.subset_span (Set.mem_range_self 0) : τ 0 ∈ Submodule.span ℝ {e})
  -- `1 = ‖τ 0‖ = |c| ‖e‖ = |c|`, so `c = ±1`
  have hc1 : |c| = 1 := by
    have h := hτ.1 0
    rwa [← hc, norm_smul, he, mul_one, Real.norm_eq_abs] at h
  -- `Fin 1 = {0}`, so `α τ = α (fun _ => c • e) = c * α (fun _ => e)`
  have hev : ∀ α : Covector (Euclid P) 1, α τ = c * α (fun _ => e) := by
    intro α
    have hτc : τ = fun _ => c • e := funext fun i => by rw [Subsingleton.elim i 0, hc]
    rw [hτc, α.map_smul_univ (fun _ => c) (fun _ => e)]
    simp
  rcases (abs_eq zero_le_one).mp hc1 with rfl | rfl <;> rcases hξ with hξ | hξ
  · exact Or.inl (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, one_mul, ContinuousAlternatingMap.apply_apply])
  · exact Or.inr (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, one_mul, neg_apply, ContinuousAlternatingMap.apply_apply])
  · exact Or.inr (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, neg_one_mul, neg_apply, ContinuousAlternatingMap.apply_apply])
  · exact Or.inl (ContinuousLinearMap.ext fun α => by
      rw [hξ, hev, neg_one_mul, neg_neg, ContinuousAlternatingMap.apply_apply])

/-- **Orientation along the rays of a `1`-dimensional carrier** (for Simon 7.3.3, proof of (2),
(10): `1`-dimensional minimizing cones are `m[[ℓ]]`; Ch. 3, 1.4 and Ch. 6, 3.1).  Let
`R = (M, θ, ξ)` be a `1`-dimensional integer multiplicity triple in `ℝᴾ` and `F` a finite set of
unit vectors with `H¹(M \ ⋃_{e ∈ F} ray(e)) = 0`, `ray(e) = {t e : t > 0}`.  Then for each
`e ∈ F`, `ξ(x) = ±e` for `H¹`-a.e. `x ∈ M ∩ ray(e)`: near `x = t₀ e` the other rays stay away,
so `M` lies on the line `x + ℝe` up to an `H¹`-null set, the approximate tangent line `TₓM` is
`ℝe`, and the unit orientations of `ℝe` are `±e`. -/
theorem Submission.idtp_fons_odc_ray_orientation : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 1) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → (μHE[1] : Measure (Euclid P)) (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 → ∀ e ∈ F, ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict (R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0)), R.orient x = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) ∨ R.orient x = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => e) := by
  intro P R F hF hnull e he
  have he1 : ‖e‖ = 1 := hF e he
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he1
  -- Step 1: `ray(e)` is the image of `(0, ∞)` under the measurable embedding `t ↦ 0 + t e`
  -- (line_param), so `M ∩ ray(e)` is measurable.
  have hray : MeasurableSet ((fun t : ℝ => t • e) '' Ioi 0) := by
    have h := (Submission.idtp_fons_odc_line_hausdorff.2 P 0 e he1).1.measurableSet_image.2
      (measurableSet_Ioi (a := (0 : ℝ)))
    simpa only [zero_add] using h
  -- Step 6: `R.orients` holds a.e. on `M`, hence a.e. on `M ∩ ray(e)`, and a.e. point of
  -- `M ∩ ray(e)` is `t₀ e` with `t₀ > 0`.
  filter_upwards [ae_restrict_mem (R.measurableSet_carrier.inter hray),
    ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients] with x hx hxQ
  obtain ⟨-, t₀, ht₀ : 0 < t₀, hxe⟩ := hx
  simp only at hxe
  subst hxe
  obtain ⟨Q, hQ, hQo⟩ := hxQ
  -- Step 2: near `t₀ e`, every point on a ray of `F` lies on `ray(e)` (ray_isolation).
  obtain ⟨δ, hδ, hball⟩ := Submission.idtp_fons_odc_ro_ray_isolation P F e t₀ hF he1 ht₀
  -- Step 3: `M ∩ B_δ(t₀ e) ⊆ (t₀ e + ℝe) ∪ N` with `N = M \ ⋃_{e' ∈ F} ray(e')`.
  have hloc : R.carrier ∩ ball (t₀ • e) δ ⊆ range (fun s : ℝ => t₀ • e + s • e) ∪
      (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) := by
    rintro y ⟨hyM, hyB⟩
    by_cases hy : y ∈ ⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0
    · obtain ⟨t, -, rfl⟩ := hball ⟨hyB, hy⟩
      exact Or.inl ⟨t - t₀, by simp only [← add_smul, add_sub_cancel]⟩
    · exact Or.inr ⟨hyM, hy⟩
  -- Step 4: the approximate tangent line of `M` at `t₀ e` is `ℝe` (tangent_line).
  obtain rfl := Submission.idtp_fons_odc_ro_tangent_line P R.carrier _ (t₀ • e) e δ Q he0 hδ
    hnull hloc hQ
  -- Step 5: the unit orientations of `ℝe` are `±e` (line_orientation).
  exact Submission.idtp_fons_odc_ro_line_orientation P e (R.orient (t₀ • e)) he1 hQo

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
