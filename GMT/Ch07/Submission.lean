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

/-- **`C¹` approximation of an indicator in `L¹`**: if `P ⊆ B_R(0) ⊆ ℝⁿ` is measurable and
`η > 0`, there is a `C¹` function `ψ : ℝⁿ → [0, 1]` with compact support in `B_R(0)` and
`∫ |ψ - 1_P| < η`.  Take a compact `K ⊆ P` with `L(P \ K) < η/2` (inner regularity), an open
`U ⊇ K` with `L(U \ K) < η/2` (outer regularity at `K`) and `r' < R` with `K ⊆ B_{r'}(0)`; the
smooth Urysohn lemma for `K ⊆ s := U ∩ B_{r'}(0)` gives `ψ` with `support ψ = s` and `ψ = 1`
exactly on `K`, and `|ψ - 1_P| ≤ 1_{P \ K} + 1_{s \ K}`. -/
theorem Submission.codim1_rdo_dg_bvc_smooth_indicator_approx : ∀ (n : ℕ) (P : Set (Euclid n)) (R η : ℝ), MeasurableSet P → P ⊆ ball (0 : Euclid n) R → 0 < η → ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball (0 : Euclid n) R ∧ (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧ ∫ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z| < η := by
  intro n P R η hP hPR hη
  -- Step 1: `L(P) ≤ L(B_R) < ∞`
  have hPfin : volume P ≠ ∞ := (measure_mono hPR |>.trans_lt measure_ball_lt_top).ne
  have hη2 : ENNReal.ofReal (η / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos hη)).ne'
  -- Step 2: a compact closed `K ⊆ P` with `L(P \ K) < η/2`
  obtain ⟨K, hKP, hKc, hKcl, hPK⟩ := hP.exists_isCompact_isClosed_sdiff_lt hPfin hη2
  -- Step 3: an open `U ⊇ K` with `L(U) < L(K) + η/2`
  obtain ⟨U, hKU, hUo, hU⟩ := hKc.exists_isOpen_lt_add (μ := volume) hη2
  -- Step 4: `K ⊆ B_{r'}(0)` for some `r' < R`
  obtain ⟨r', hr'R, hKr'⟩ := exists_lt_subset_ball hKcl (hKP.trans hPR)
  -- Step 5: smooth Urysohn for `K ⊆ s := U ∩ B_{r'}(0)`
  set s := U ∩ ball (0 : Euclid n) r' with hsdef
  have hs : IsOpen s := hUo.inter isOpen_ball
  have hKs : K ⊆ s := fun x hx => ⟨hKU hx, hKr' hx⟩
  obtain ⟨ψ, hψ, hψr, hψs, hψ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1) hs hKcl hKs
  have hψ01 : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1 := fun z => hψr (mem_range_self z)
  -- Step 6: `tsupport ψ = closure s ⊆ B̄_{r'}(0) ⊆ B_R(0)`, which is compact
  have htsupp : tsupport ψ ⊆ closedBall (0 : Euclid n) r' := by
    rw [tsupport, hψs]
    exact closure_minimal (inter_subset_right.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨ψ, hψ, ?_, htsupp.trans (closedBall_subset_ball hr'R), hψ01, ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport ψ).trans htsupp)
  -- Step 7: `|ψ - 1_P| ≤ 1_{P \ K} + 1_{s \ K}` pointwise
  have hdom : ∀ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z|
      ≤ (P \ K).indicator (fun _ => (1 : ℝ)) z + (s \ K).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h01 := hψ01 z
    by_cases hzK : z ∈ K
    · have h1 : ψ z = 1 := (hψ1 z).1 hzK
      simp [h1, hKP hzK, hzK]
    · by_cases hzP : z ∈ P
      · have : (P \ K).indicator (fun _ => (1 : ℝ)) z = 1 := by simp [hzP, hzK]
        rw [indicator_of_mem hzP, this]
        have : 0 ≤ (s \ K).indicator (fun _ => (1 : ℝ)) z :=
          indicator_nonneg (fun _ _ => zero_le_one) _
        rw [abs_le]; constructor <;> linarith
      · rw [indicator_of_notMem hzP, sub_zero, abs_of_nonneg h01.1]
        by_cases hzs : z ∈ s
        · have : (s \ K).indicator (fun _ => (1 : ℝ)) z = 1 := by simp [hzs, hzK]
          rw [this]
          have : 0 ≤ (P \ K).indicator (fun _ => (1 : ℝ)) z :=
            indicator_nonneg (fun _ _ => zero_le_one) _
          linarith [h01.2]
        · have : ψ z = 0 := by
            by_contra h
            exact hzs (hψs ▸ (mem_support.2 h))
          rw [this]
          exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
            (indicator_nonneg (fun _ _ => zero_le_one) _)
  -- Step 8: integrate, using `L(P \ K) < η/2` and `L(s \ K) ≤ L(U \ K) < η/2`
  have hPKm : MeasurableSet (P \ K) := hP.diff hKcl.measurableSet
  have hsKm : MeasurableSet (s \ K) := hs.measurableSet.diff hKcl.measurableSet
  have hPKfin : volume (P \ K) ≠ ∞ := (measure_mono sdiff_subset |>.trans_lt hPfin.lt_top).ne
  have hsKlt : volume (s \ K) < ENNReal.ofReal (η / 2) := by
    calc volume (s \ K) ≤ volume (U \ K) :=
          measure_mono (sdiff_subset_sdiff_left inter_subset_left)
      _ = volume U - volume K :=
          measure_sdiff hKU hKcl.measurableSet.nullMeasurableSet hKc.measure_lt_top.ne
      _ < ENNReal.ofReal (η / 2) := by
        rw [ENNReal.sub_lt_iff_lt_right hKc.measure_lt_top.ne (measure_mono hKU)]
        rwa [add_comm]
  have hsKfin : volume (s \ K) ≠ ∞ := (hsKlt.trans ENNReal.ofReal_lt_top).ne
  have hint1 : Integrable ((P \ K).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hPKfin).integrable_indicator hPKm
  have hint2 : Integrable ((s \ K).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hsKfin).integrable_indicator hsKm
  calc ∫ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z|
      ≤ ∫ z, ((P \ K).indicator (fun _ => (1 : ℝ)) z + (s \ K).indicator (fun _ => (1 : ℝ)) z) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _)
          (hint1.add hint2) (Filter.Eventually.of_forall hdom)
    _ = (volume (P \ K)).toReal + (volume (s \ K)).toReal := by
        rw [integral_add hint1 hint2, integral_indicator_const _ hPKm,
          integral_indicator_const _ hsKm]
        simp [Measure.real]
    _ < η / 2 + η / 2 := by
        gcongr
        · exact (ENNReal.toReal_lt_toReal hPKfin ENNReal.ofReal_ne_top).2 hPK
            |>.trans_eq (ENNReal.toReal_ofReal (half_pos hη).le)
        · exact (ENNReal.toReal_lt_toReal hsKfin ENNReal.ofReal_ne_top).2 hsKlt
            |>.trans_eq (ENNReal.toReal_ofReal (half_pos hη).le)
    _ = η := add_halves η

/-- **The `L¹` norm on a ball by duality with `C¹` test functions** (used in the mollification
estimate of the precompactness step of the BV compactness theorem, Simon Ch. 2, 2.6, which the book
delegates to [GT01, Theorem 7.22]; this serves De Giorgi's argument), for
bounded Borel `f`: if `|f| ≤ M` and `∫ f φ ≤ A` for every `C¹` function `φ` with compact support in
`B_R(0)` and `|φ| ≤ 1`, then `∫_{B_R(0)} |f| ≤ A`.  With `P = {f > 0} ∩ B_R(0)`,
`N = {f < 0} ∩ B_R(0)` and `g = 1_P − 1_N` one has `f g = 1_{B_R(0)} |f|`.  Approximating `1_P` and
`1_N` in `L¹` within `η' = η / (2(M + 1))` by `C¹` functions `ψ_P`, `ψ_N` with values in `[0, 1]`
and compact support in `B_R(0)` (`smooth_indicator_approx`) gives the admissible test
`φ = ψ_P − ψ_N`, and `∫ f g − ∫ f φ ≤ M (∫ |ψ_P − 1_P| + ∫ |ψ_N − 1_N|) < (M + 1) 2η' = η`. -/
theorem Submission.codim1_rdo_dg_bvc_l1_le_of_tests : ∀ (n : ℕ) (f : Euclid n → ℝ) (R A M : ℝ), Measurable f → (∀ z, |f z| ≤ M) → (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid n) R → (∀ z, |φ z| ≤ 1) → ∫ z, f z * φ z ≤ A) → ∫ z in ball (0 : Euclid n) R, |f z| ≤ A := by
  intro n f R A M hf hM hA
  -- Step 1: `M ≥ |f 0| ≥ 0`; `P = {f > 0} ∩ B_R` and `N = {f < 0} ∩ B_R` are Borel subsets of
  -- `B_R` (so of finite measure); `g = 1_P − 1_N`
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set P : Set (Euclid n) := {z | 0 < f z} ∩ ball 0 R
  set N : Set (Euclid n) := {z | f z < 0} ∩ ball 0 R
  have hPm : MeasurableSet P := (measurableSet_lt measurable_const hf).inter measurableSet_ball
  have hNm : MeasurableSet N := (measurableSet_lt hf measurable_const).inter measurableSet_ball
  have hPfin : volume P ≠ ∞ := (measure_mono inter_subset_right |>.trans_lt measure_ball_lt_top).ne
  have hNfin : volume N ≠ ∞ := (measure_mono inter_subset_right |>.trans_lt measure_ball_lt_top).ne
  set g : Euclid n → ℝ := fun z =>
    P.indicator (fun _ => (1 : ℝ)) z - N.indicator (fun _ => (1 : ℝ)) z with hg
  -- Step 2: `f g = 1_{B_R} |f|` pointwise, so `∫_{B_R} |f| = ∫ f g`; `f g` is integrable, being
  -- Borel, bounded by `M` and zero outside `B_R`
  have hfg : (fun z => f z * g z) = (ball (0 : Euclid n) R).indicator fun z => |f z| := by
    funext z
    by_cases hz : z ∈ ball (0 : Euclid n) R
    · rw [indicator_of_mem hz]
      rcases lt_trichotomy (f z) 0 with h | h | h
      · have hzP : z ∉ P := fun hzP => lt_asymm h hzP.1
        have hzN : z ∈ N := ⟨h, hz⟩
        simp only [hg, indicator_of_notMem hzP, indicator_of_mem hzN, abs_of_neg h]
        ring
      · simp [h]
      · have hzP : z ∈ P := ⟨h, hz⟩
        have hzN : z ∉ N := fun hzN => lt_asymm h hzN.1
        simp only [hg, indicator_of_mem hzP, indicator_of_notMem hzN, abs_of_pos h]
        ring
    · have hzP : z ∉ P := fun hzP => hz hzP.2
      have hzN : z ∉ N := fun hzN => hz hzN.2
      simp only [hg, indicator_of_notMem hzP, indicator_of_notMem hzN, indicator_of_notMem hz]
      ring
  have hrepr : ∫ z in ball (0 : Euclid n) R, |f z| = ∫ z, f z * g z := by
    rw [hfg, integral_indicator measurableSet_ball]
  have hfg_int : Integrable fun z => f z * g z := by
    rw [hfg]
    refine (Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne
      (continuous_abs.measurable.comp hf).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)).integrable_indicator measurableSet_ball
    simpa [Real.norm_eq_abs] using hM z
  -- Step 3: given `η > 0`, approximate `1_P` and `1_N` in `L¹` within `η' = η / (2(M + 1))`
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hM1 : 0 < M + 1 := by linarith
  set η' : ℝ := η / (2 * (M + 1)) with hη'
  have hη'0 : 0 < η' := div_pos hη (mul_pos two_pos hM1)
  obtain ⟨ψP, hψP, hcP, htP, h01P, hapP⟩ :=
    Submission.codim1_rdo_dg_bvc_smooth_indicator_approx n P R η' hPm inter_subset_right hη'0
  obtain ⟨ψN, hψN, hcN, htN, h01N, hapN⟩ :=
    Submission.codim1_rdo_dg_bvc_smooth_indicator_approx n N R η' hNm inter_subset_right hη'0
  -- Step 4: `φ = ψ_P − ψ_N` is an admissible test, so `∫ f φ ≤ A`; `f φ` is integrable
  set φ : Euclid n → ℝ := fun z => ψP z - ψN z with hφ
  have hφ1 : ∀ z, |φ z| ≤ 1 := fun z => by
    obtain ⟨h0P, h1P⟩ := h01P z
    obtain ⟨h0N, h1N⟩ := h01N z
    rw [hφ, abs_le]
    constructor <;> linarith
  have hφA : ∫ z, f z * φ z ≤ A :=
    hA φ (hψP.sub hψN) (hcP.sub hcN) ((tsupport_sub ψP ψN).trans (union_subset htP htN)) hφ1
  have hfφ_int : Integrable fun z => f z * φ z :=
    ((hψP.sub hψN).continuous.integrable_of_hasCompactSupport (hcP.sub hcN)).bdd_mul
      hf.aestronglyMeasurable (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM z)
  -- Step 5: `f g − f φ ≤ M (|ψ_P − 1_P| + |ψ_N − 1_N|)` pointwise, and these errors are integrable;
  -- integrate
  have hIP : Integrable fun z => |ψP z - P.indicator (fun _ => (1 : ℝ)) z| :=
    ((hψP.continuous.integrable_of_hasCompactSupport hcP).sub
      ((integrableOn_const (C := (1 : ℝ)) hPfin).integrable_indicator hPm)).abs
  have hIN : Integrable fun z => |ψN z - N.indicator (fun _ => (1 : ℝ)) z| :=
    ((hψN.continuous.integrable_of_hasCompactSupport hcN).sub
      ((integrableOn_const (C := (1 : ℝ)) hNfin).integrable_indicator hNm)).abs
  have hpt : ∀ z, f z * g z - f z * φ z ≤ M * (|ψP z - P.indicator (fun _ => (1 : ℝ)) z| +
      |ψN z - N.indicator (fun _ => (1 : ℝ)) z|) := by
    intro z
    calc f z * g z - f z * φ z
        = f z * ((P.indicator (fun _ => (1 : ℝ)) z - ψP z) -
            (N.indicator (fun _ => (1 : ℝ)) z - ψN z)) := by
          simp only [hg, hφ]
          ring
      _ ≤ |f z| * |(P.indicator (fun _ => (1 : ℝ)) z - ψP z) -
            (N.indicator (fun _ => (1 : ℝ)) z - ψN z)| := by
          rw [← abs_mul]
          exact le_abs_self _
      _ ≤ M * (|ψP z - P.indicator (fun _ => (1 : ℝ)) z| +
            |ψN z - N.indicator (fun _ => (1 : ℝ)) z|) := by
          rw [abs_sub_comm (ψP z), abs_sub_comm (ψN z)]
          exact mul_le_mul (hM z) (abs_sub _ _) (abs_nonneg _) hM0
  have hmain : (∫ z, f z * g z) - ∫ z, f z * φ z ≤
      M * ((∫ z, |ψP z - P.indicator (fun _ => (1 : ℝ)) z|) +
        ∫ z, |ψN z - N.indicator (fun _ => (1 : ℝ)) z|) := by
    rw [← integral_sub hfg_int hfφ_int, ← integral_add hIP hIN, ← integral_const_mul]
    exact integral_mono (hfg_int.sub hfφ_int) ((hIP.add hIN).const_mul M) hpt
  -- Step 6: `S = ∫ |ψ_P − 1_P| + ∫ |ψ_N − 1_N|` satisfies `0 ≤ S < 2η'`, so
  -- `M S ≤ (M + 1) S < (M + 1) 2η' = η`
  set S : ℝ := (∫ z, |ψP z - P.indicator (fun _ => (1 : ℝ)) z|) +
    ∫ z, |ψN z - N.indicator (fun _ => (1 : ℝ)) z| with hS
  have hS0 : 0 ≤ S :=
    add_nonneg (integral_nonneg fun _ => abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hS2 : S < 2 * η' := by
    rw [hS]
    linarith
  have hMS : M * S < η :=
    calc M * S ≤ (M + 1) * S := by linarith
      _ < (M + 1) * (2 * η') := mul_lt_mul_of_pos_left hS2 hM1
      _ = η := by
        rw [hη']
        field_simp
  -- Step 7: `∫_{B_R} |f| = ∫ f g ≤ ∫ f φ + M S < A + η`; `η > 0` is arbitrary
  rw [hrepr]
  linarith
/-- **Translation against a `C¹` test function** (step 1 of the BV compactness argument, for a
single translation vector `w`): if `∫_F div g ≤ C` for every `C¹` field `g` with `|g| ≤ 1` and
compact support in `B_{R+|w|}(0)`, then `∫_F (φ(z) − φ(z + w)) dz ≤ |w| C` for every `C¹` test
function `φ` with `|φ| ≤ 1` and compact support in `B_R(0)`.  For `t ∈ [0, 1]` the field
`G_t = −|w|⁻¹ φ(· + tw) w` is admissible and `div G_t = −|w|⁻¹ Dφ(· + tw)[w]` (trace of a rank-one
map), so `Φ(t) = ∫_F φ(z + tw) dz`, differentiable under the integral sign, has
`Φ'(t) = ∫_F Dφ(z + tw)[w] dz ≥ −|w| C` on `[0, 1]`; hence `Φ(0) − Φ(1) ≤ |w| C`. -/
theorem Submission.codim1_rdo_dg_bvc_translate_test_le : ∀ (n : ℕ) (F : Set (Euclid n)) (R C : ℝ) (w : Euclid n) (φ : Euclid n → ℝ), MeasurableSet F → (∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid n) (R + ‖w‖) → (∀ z, ‖g z‖ ≤ 1) → ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C) → ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid n) R → (∀ z, |φ z| ≤ 1) → ∫ z in F, (φ z - φ (z + w)) ≤ ‖w‖ * C := by
  intro n F R C w φ _hF hdiv hφ hφc hφs hφb
  -- `w = 0`: both sides vanish
  by_cases hw : w = 0
  · subst hw; simp
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  -- the elementary fields `G_t = (−‖w‖⁻¹ φ(· + t • w)) • w`, `0 ≤ t ≤ 1`, give
  -- `−‖w‖ C ≤ ∫_F Dφ(z + t • w)[w]`
  have hfield : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      -(‖w‖ * C) ≤ ∫ z in F, fderiv ℝ φ (z + t • w) w := by
    intro t ht0 ht1
    set c : ℝ := -(‖w‖⁻¹) with hc
    set G : Euclid n → Euclid n := fun z => (c * φ (z + t • w)) • w with hG
    have hGd : ∀ z, HasFDerivAt G ((c • fderiv ℝ φ (z + t • w)).smulRight w) z := by
      intro z
      have h1 : HasFDerivAt (fun y : Euclid n => φ (y + t • w)) (fderiv ℝ φ (z + t • w)) z :=
        (hφd (z + t • w)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const (t • w))
      exact (h1.const_mul c).smul_const w
    have hGc1 : ContDiff ℝ 1 G :=
      (contDiff_const.mul (hφ.comp (contDiff_id.add contDiff_const))).smul contDiff_const
    -- `tsupport G ⊆ tsupport φ(· + t • w) = tsupport φ − t • w`
    have hpre : tsupport (fun y : Euclid n => φ (y + t • w)) =
        (fun y => y + t • w) ⁻¹' tsupport φ :=
      tsupport_comp_eq_preimage φ (Homeomorph.addRight (t • w))
    have hGsupp : tsupport G ⊆ tsupport (fun y : Euclid n => φ (y + t • w)) :=
      (tsupport_smul_subset_left _ _).trans tsupport_mul_subset_right
    have hGcs : HasCompactSupport G :=
      (hφc.comp_homeomorph (Homeomorph.addRight (t • w))).mul_left.smul_right
    have hGball : tsupport G ⊆ ball (0 : Euclid n) (R + ‖w‖) := by
      intro z hz
      have h1 : z + t • w ∈ ball (0 : Euclid n) R := hφs (hpre.subset (hGsupp hz))
      rw [mem_ball_zero_iff] at h1 ⊢
      have h2 : ‖t • w‖ ≤ ‖w‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      calc ‖z‖ = ‖(z + t • w) - t • w‖ := by simp
        _ ≤ ‖z + t • w‖ + ‖t • w‖ := norm_sub_le _ _
        _ < R + ‖w‖ := by linarith
    have hGnorm : ∀ z, ‖G z‖ ≤ 1 := by
      intro z
      simp only [hG, hc, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_norm]
      rw [mul_comm (‖w‖⁻¹), mul_assoc, inv_mul_cancel₀ hwpos.ne', mul_one]
      exact hφb _
    -- `div G_t(z) = c Dφ(z + t • w)[w]`: the trace of the rank-one map `h ↦ c Dφ(z + t • w)[h] w`
    have htrace : ∀ z, LinearMap.trace ℝ (Euclid n) (fderiv ℝ G z : Euclid n →ₗ[ℝ] Euclid n) =
        c * fderiv ℝ φ (z + t • w) w := by
      intro z
      rw [(hGd z).fderiv]
      have : ((c • fderiv ℝ φ (z + t • w)).smulRight w : Euclid n →L[ℝ] Euclid n) =
          (((c • fderiv ℝ φ (z + t • w) : Euclid n →L[ℝ] ℝ) : Euclid n →ₗ[ℝ] ℝ).smulRight w :
            Euclid n →ₗ[ℝ] Euclid n) := by
        ext v; simp
      rw [this, LinearMap.trace_smulRight]
      simp
    have hbound := hdiv G hGc1 hGcs hGball hGnorm
    simp_rw [htrace] at hbound
    rw [integral_const_mul] at hbound
    -- `−‖w‖⁻¹ ∫_F Dφ(z + t • w)[w] ≤ C`; multiply by `‖w‖ > 0`
    have h3 := mul_le_mul_of_nonneg_left hbound hwpos.le
    rw [← mul_assoc, hc, mul_neg, mul_inv_cancel₀ hwpos.ne', neg_one_mul] at h3
    linarith
  -- `Φ(t) = ∫_F φ(z + t • w)` has derivative `∫_F Dφ(z + t • w)[w]` (dominated differentiation)
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖fderiv ℝ φ x‖ ≤ B :=
    (hφc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hφ'c
  set Φ : ℝ → ℝ := fun t => ∫ z in F, φ (z + t • w) with hΦ
  have hΦd : ∀ t₀ : ℝ, HasDerivAt Φ (∫ z in F, fderiv ℝ φ (z + t₀ • w) w) t₀ := by
    intro t₀
    set K : Set (Euclid n) := closedBall (0 : Euclid n) (R + (|t₀| + 1) * ‖w‖)
    have hKm : MeasurableSet K := measurableSet_closedBall
    have hKfin : volume K ≠ ∞ := measure_closedBall_lt_top.ne
    -- `Dφ(z + t • w) ≠ 0` forces `z + t • w ∈ tsupport φ ⊆ B_R(0)`
    have hsupp : ∀ z t, fderiv ℝ φ (z + t • w) ≠ 0 → ‖z‖ < R + |t| * ‖w‖ := by
      intro z t h
      have h1 := hφs (tsupport_fderiv_subset ℝ (subset_tsupport _ h))
      rw [mem_ball_zero_iff] at h1
      calc ‖z‖ = ‖(z + t • w) - t • w‖ := by simp
        _ ≤ ‖z + t • w‖ + ‖t • w‖ := norm_sub_le _ _
        _ < R + |t| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]; linarith
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict F)
      (F := fun t z => φ (z + t • w)) (F' := fun t z => fderiv ℝ φ (z + t • w) w)
      (bound := K.indicator (fun _ => B * ‖w‖)) (s := ball t₀ 1) (ball_mem_nhds t₀ zero_lt_one)
      ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Filter.Eventually.of_forall fun t =>
        (hφ.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · exact (hφi.comp_add_right (t₀ • w)).integrableOn
    · exact ((hφ'c.comp (continuous_id.add continuous_const)).clm_apply
        continuous_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z t ht => ?_
      by_cases hz : fderiv ℝ φ (z + t • w) = 0
      · simp only [hz, zero_apply, norm_zero]
        exact indicator_nonneg
          (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hB 0)) (norm_nonneg _)) _
      · have hzK : z ∈ K := by
          have h1 := hsupp z t hz
          have h2 : |t| ≤ |t₀| + 1 := by
            have := abs_sub_abs_le_abs_sub t t₀
            rw [mem_ball, Real.dist_eq] at ht; linarith
          rw [mem_closedBall_zero_iff]
          nlinarith [norm_nonneg w]
        rw [indicator_of_mem hzK]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    · exact ((integrableOn_const hKfin).integrable_indicator hKm).integrableOn
    · refine Filter.Eventually.of_forall fun z t _ => ?_
      have h1 : HasDerivAt (fun s : ℝ => z + s • w) w t := by
        simpa using ((hasDerivAt_id t).smul_const w).const_add z
      exact (hφd (z + t • w)).hasFDerivAt.comp_hasDerivAt t h1
  -- `Ψ(t) = Φ(t) + ‖w‖ C t` has `Ψ' ≥ 0` on `(0, 1)`, so `Ψ(0) ≤ Ψ(1)`
  set Ψ : ℝ → ℝ := fun t => Φ t + ‖w‖ * C * t with hΨ
  have hΨd : ∀ t, HasDerivAt Ψ ((∫ z in F, fderiv ℝ φ (z + t • w) w) + ‖w‖ * C) t := by
    intro t
    have := (hΦd t).add ((hasDerivAt_id t).const_mul (‖w‖ * C))
    simp only [id, mul_one] at this
    exact this
  have hmono : MonotoneOn Ψ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t _ => (hΨd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hΨd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hΨd t).deriv]
      linarith [hfield t ht.1.le ht.2.le]
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hΨ, hΦ, zero_smul, add_zero, one_smul, mul_zero, mul_one] at h01
  -- `Φ(0) − Φ(1) = ∫_F (φ z − φ (z + w))`
  rw [integral_sub hφi.integrableOn (hφi.comp_add_right w).integrableOn]
  linarith
/-- **`L¹` translation estimate** (step 1 of the BV compactness argument behind Simon Ch. 2, 2.6,
via [GT01, 7.22], for a single translation `w`).  If `∫_F div g ≤ C` for every `C¹` vector field
`g` with `|g| ≤ 1` and compact support in `B_{R+|w|}(0)`, then
`∫_{B_R(0)} |1_F(z) − 1_F(z − w)| dz ≤ |w| C`.  The difference `f = 1_F − 1_F(· − w)` is Borel with
`|f| ≤ 1`; for an admissible test `φ`, translation invariance of Lebesgue measure gives
`∫ f φ = ∫_F (φ − φ(· + w))`, which `translate_test` bounds by `|w| C`, and `l1_duality` (with
`M = 1`) turns this weak bound into the `L¹` bound. -/
theorem Submission.codim1_rdo_dg_bvc_translation_l1_le : ∀ (n : ℕ) (F : Set (Euclid n)) (R C : ℝ) (w : Euclid n), MeasurableSet F → (∀ g : Euclid n → Euclid n, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid n) (R + ‖w‖) → (∀ z, ‖g z‖ ≤ 1) → ∫ z in F, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid n) ≤ C) → ∫ z in ball (0 : Euclid n) R, |F.indicator (fun _ => (1 : ℝ)) z - F.indicator (fun _ => (1 : ℝ)) (z - w)| ≤ ‖w‖ * C := by
  intro n F R C w hF hdiv
  -- Step 1: `u = 1_F` takes values in `[0, 1]`, so `f = u − u(· − w)` is Borel with `|f| ≤ 1`
  set u : Euclid n → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
  have hu01 : ∀ z, 0 ≤ u z ∧ u z ≤ 1 := fun z => by
    by_cases hz : z ∈ F <;> simp [hu, hz]
  have hu_meas : Measurable u := measurable_const.indicator hF
  have hu_shift : Measurable fun z => u (z - w) := hu_meas.comp (measurable_id.sub_const w)
  have hbd : ∀ z, |u z - u (z - w)| ≤ 1 := fun z => by
    rw [abs_le]
    constructor <;> linarith [(hu01 z).1, (hu01 z).2, (hu01 (z - w)).1, (hu01 (z - w)).2]
  -- Step 4: `l1_duality` with `M = 1` and `A = ‖w‖ C` reduces the claim to the tested bound
  refine Submission.codim1_rdo_dg_bvc_l1_le_of_tests n (fun z => u z - u (z - w)) R (‖w‖ * C) 1
    (hu_meas.sub hu_shift) hbd fun φ hφ hφc hφs hφb => ?_
  -- Step 2: `∫ f φ = ∫_F (φ − φ(· + w))`, moving the translation onto `φ` (`z = y + w`)
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hmul : ∀ ψ : Euclid n → ℝ, (fun z => u z * ψ z) = F.indicator ψ := fun ψ => by
    funext z
    by_cases hz : z ∈ F <;> simp [hu, hz]
  have h1 : Integrable fun z => u z * φ z := by
    rw [hmul]
    exact hφi.indicator hF
  have hu_shift_le : ∀ z, ‖u (z - w)‖ ≤ 1 := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hu01 (z - w)).1]
    exact (hu01 (z - w)).2
  have h2 : Integrable fun z => u (z - w) * φ z :=
    hφi.bdd_mul hu_shift.aestronglyMeasurable (Eventually.of_forall hu_shift_le)
  have h3 : Integrable fun z => u z * φ (z + w) := by
    rw [hmul]
    exact (hφi.comp_add_right w).indicator hF
  have hshift : ∫ z, u (z - w) * φ z = ∫ z, u z * φ (z + w) := by
    rw [← integral_add_right_eq_self (fun z => u (z - w) * φ z) w]
    simp
  have key : ∫ z, (u z - u (z - w)) * φ z = ∫ z in F, (φ z - φ (z + w)) := by
    simp_rw [sub_mul]
    rw [integral_sub h1 h2, hshift, ← integral_sub h1 h3, ← integral_indicator hF]
    congr 1
    funext z
    by_cases hz : z ∈ F <;> simp [hu, hz]
  -- Step 3: `translate_test` bounds `∫_F (φ − φ(· + w))` by `‖w‖ C`
  exact key.trans_le
    (Submission.codim1_rdo_dg_bvc_translate_test_le n F R C w φ hF hdiv hφ hφc hφs hφb)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
