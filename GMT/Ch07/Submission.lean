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

/-- **Affine change of variables for `μH[n]`-integrals** (Simon's rescalings
`φ_{x,λ}(z) = φ(x + λz)`, Appendix A).  For `c > 0` the map `x ↦ c • x` pushes `μH[n]` forward to
`c⁻ⁿ μH[n]` (Hausdorff scaling law) and `μH[n]` is translation invariant, so
`∫ h(y + c x) dμH[n](x) = c⁻ⁿ ∫ h dμH[n]` for every `h`; both sides vanish when `h` is not
integrable. -/
theorem Submission.adr_hausdorff_integral_comp_affine : ∀ (P n Q : ℕ) (h : Euclid P → Euclid Q) (y : Euclid P) (c : ℝ), 0 < c → ∫ x, h (y + c • x) ∂μH[(n : ℝ)] = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)] := by
  intro P n Q h y c hc
  -- `x ↦ c • x` is a homeomorphism, hence a measurable embedding
  have hemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- push-forward of `μH[n]` under `x ↦ c • x` (the homothety with centre `0` and ratio `c`)
  have hmap : Measure.map (fun x : Euclid P => c • x) μH[(n : ℝ)] =
      ‖c‖₊⁻¹ ^ (n : ℝ) • μH[(n : ℝ)] := by
    have := map_homothety_hausdorffMeasure (Nat.cast_nonneg n) (0 : Euclid P) hc.ne'
    convert this using 2
    funext x
    simp [AffineMap.homothety_apply]
  calc ∫ x, h (y + c • x) ∂μH[(n : ℝ)]
      = ∫ w, h (y + w) ∂(Measure.map (fun x : Euclid P => c • x) μH[(n : ℝ)]) :=
        (hemb.integral_map (fun w => h (y + w))).symm
    _ = (‖c‖₊⁻¹ ^ (n : ℝ)) • ∫ w, h (y + w) ∂μH[(n : ℝ)] := by
        rw [hmap, integral_smul_nnreal_measure]
    _ = (‖c‖₊⁻¹ ^ (n : ℝ)) • ∫ w, h w ∂μH[(n : ℝ)] := by
        rw [integral_add_left_eq_self]
    _ = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)] := by
        rw [NNReal.smul_def]
        congr 1
        simp [Real.norm_of_nonneg hc.le, inv_pow]
/-- **Uniform bound for weakly bounded sequences** (Simon, Appendix A: needed tacitly by the weak
limits `ψ_{y,1} = lim φ_{y+x,λⱼ}` in the proof of A.4, p. 228).  The bounded continuous functions
vanishing off the compact set `K` form a closed subspace `X` of `Euclid P →ᵇ ℝ`, hence a Banach
space.  On it, `Λₖ u = ∫ u • gₖ dμ` are continuous linear maps (`‖Λₖ u‖ ≤ (∫_K ‖gₖ‖ dμ) ‖u‖`),
pointwise bounded by hypothesis, so the uniform boundedness principle, proved here from the Baire
category theorem, gives `‖Λₖ‖ ≤ M` for all `k`. -/
theorem Submission.adr_uniform_bound_of_weak_bounded : ∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∃ C, ∀ k, ‖∫ x, f x • gs k x ∂μ‖ ≤ C) → IsCompact K → ∃ M, ∀ (k : ℕ) (h : Euclid P → ℝ) (C : ℝ), Continuous h → (∀ x ∉ K, h x = 0) → (∀ x, |h x| ≤ C) → ‖∫ x, h x • gs k x ∂μ‖ ≤ M * C := by
  intro P Q μ gs K hloc hbdd hK
  -- the subspace `X` of bounded continuous functions vanishing off `K`
  let X : Submodule ℝ (BoundedContinuousFunction (Euclid P) ℝ) :=
    { carrier := {u | ∀ x ∉ K, u x = 0}
      add_mem' := fun {u v} hu hv x hx => by simp [hu x hx, hv x hx]
      zero_mem' := fun x _ => rfl
      smul_mem' := fun c u hu x hx => by simp [hu x hx] }
  -- `X` is closed, hence complete
  have hXclosed : IsClosed (X : Set (BoundedContinuousFunction (Euclid P) ℝ)) := by
    change IsClosed {u : BoundedContinuousFunction (Euclid P) ℝ | ∀ x ∉ K, u x = 0}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe)
        continuous_const
  let _ : SeminormedAddCommGroup X := Submodule.seminormedAddCommGroup X
  let _ : NormedSpace ℝ X := Submodule.normedSpace X
  have : CompleteSpace X := hXclosed.completeSpace_coe
  -- every `u ∈ X` has compact support, so `u • gₖ` is integrable
  have hcs : ∀ u : X,
      HasCompactSupport ((u : BoundedContinuousFunction (Euclid P) ℝ) : Euclid P → ℝ) :=
    fun u => HasCompactSupport.intro hK u.2
  have hint : ∀ k (u : X),
      Integrable (fun x => (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x) μ :=
    fun k u => (hloc k).integrable_smul_left_of_hasCompactSupport
      (u : BoundedContinuousFunction (Euclid P) ℝ).continuous (hcs u)
  -- `‖Λₖ u‖ ≤ (∫_K ‖gₖ‖ dμ) ‖u‖`
  have hbound : ∀ k (u : X), ‖∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ‖ ≤
      (∫ x in K, ‖gs k x‖ ∂μ) * ‖u‖ := by
    intro k u
    have hgK : IntegrableOn (gs k) K μ := (hloc k).integrableOn_isCompact hK
    calc ‖∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ‖
        ≤ ∫ x, ‖(u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = ∫ x in K, ‖(u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x‖ ∂μ := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
          simp [u.2 x hx]
      _ ≤ ∫ x in K, ‖u‖ * ‖gs k x‖ ∂μ := by
          refine setIntegral_mono_on (hint k u).norm.integrableOn
            (hgK.norm.const_mul _) hK.measurableSet fun x _ => ?_
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right
            (BoundedContinuousFunction.norm_coe_le_norm
              (u : BoundedContinuousFunction (Euclid P) ℝ) x)
            (norm_nonneg _)
      _ = (∫ x in K, ‖gs k x‖ ∂μ) * ‖u‖ := by
          rw [integral_const_mul, mul_comm]
  -- the continuous linear maps `Λₖ : X → ℝ^Q`
  let L : ℕ → X →ₗ[ℝ] Euclid Q := fun k =>
    { toFun := fun u => ∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ
      map_add' := fun u v => by
        simp only [Submodule.coe_add, BoundedContinuousFunction.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint k u) (hint k v)
      map_smul' := fun c u => by
        simp only [SetLike.val_smul, BoundedContinuousFunction.coe_smul, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact integral_smul c _ }
  let Λ : ℕ → X →L[ℝ] Euclid Q := fun k =>
    LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := X) (F := Euclid Q) (L k)
      (∫ x in K, ‖gs k x‖ ∂μ) (hbound k)
  -- pointwise boundedness: the hypothesis applied to `u ∈ X`
  have hpt : ∀ u : X, ∃ C, ∀ k, ‖Λ k u‖ ≤ C := fun u => by
    obtain ⟨C, hC⟩ := hbdd _ (u : BoundedContinuousFunction (Euclid P) ℝ).continuous (hcs u)
    exact ⟨C, fun k => hC k⟩
  -- uniform boundedness principle (Banach–Steinhaus) from the Baire category theorem
  obtain ⟨M', hM'⟩ : ∃ M', ∀ k, ‖Λ k‖ ≤ M' := by
    let e : ℕ → Set X := fun n => ⋂ k : ℕ, {u : X | ‖Λ k u‖ ≤ n}
    have hc : ∀ n, IsClosed (e n) := fun n =>
      isClosed_iInter fun k => isClosed_le (Λ k).continuous.norm continuous_const
    have hU : ⋃ n, e n = univ := by
      refine eq_univ_of_forall fun u => ?_
      obtain ⟨C, hC⟩ := hpt u
      obtain ⟨m, hm⟩ := exists_nat_ge C
      exact mem_iUnion.2 ⟨m, mem_iInter.2 fun k => (hC k).trans hm⟩
    obtain ⟨m, u₀, hu₀⟩ := nonempty_interior_of_iUnion_of_closed hc hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u₀ hu₀
    have hm : ∀ v ∈ Metric.ball u₀ ε, ∀ k, ‖Λ k v‖ ≤ m := fun v hv k =>
      mem_iInter.1 (interior_subset (hball hv)) k
    refine ⟨(m + m : ℝ) / (ε / 2), fun k =>
      ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hε (by positivity) (by norm_num)
        fun v hv1 _ => ?_⟩
    have hv1' : ε / 2 ≤ ‖v‖ := by simpa using hv1
    calc ‖Λ k v‖ = ‖Λ k (v + u₀) - Λ k u₀‖ := by rw [map_add, add_sub_cancel_right]
      _ ≤ ‖Λ k (v + u₀)‖ + ‖Λ k u₀‖ := norm_sub_le _ _
      _ ≤ m + m := add_le_add
          (hm _ (by rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]) k)
          (hm _ (Metric.mem_ball_self hε) k)
      _ ≤ (m + m : ℝ) / (ε / 2) * ‖v‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hv1' (by positivity)
  -- conclusion with `M = max M' 0`: a continuous `h` vanishing off `K` with `|h| ≤ C` is an
  -- element of `X` of norm `≤ C`
  refine ⟨max M' 0, fun k h C hcont hK0 hC => ?_⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  let hb : BoundedContinuousFunction (Euclid P) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨h, hcont⟩ (2 * C) (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      calc |h x - h y| ≤ |h x| + |h y| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC x, hC y])
  have hbX : hb ∈ X := fun x hx => hK0 x hx
  have hnorm : ‖(⟨hb, hbX⟩ : X)‖ ≤ C := by
    change ‖hb‖ ≤ C
    exact (BoundedContinuousFunction.norm_le hC0).2 fun x => by simpa [hb] using hC x
  calc ‖∫ x, h x • gs k x ∂μ‖ = ‖Λ k ⟨hb, hbX⟩‖ := rfl
    _ ≤ M' * ‖(⟨hb, hbX⟩ : X)‖ := (Λ k).le_of_opNorm_le (hM' k) _
    _ ≤ max M' 0 * C := mul_le_mul (le_max_left _ _) hnorm (norm_nonneg _) (le_max_right _ _)

/-- **Weak convergence against moving test functions** (Simon, Appendix A: "all limits in the
weak sense", the limits `ψ_{y,1} = lim φ_{y+x,λⱼ}` in the proof of A.4, p. 228).  If
`∫ f • gₖ dμ → ∫ f • g dμ` for every continuous compactly supported `f`, and continuous `hₖ → h`
uniformly, with `h` and eventually every `hₖ` vanishing off a fixed compact `K`, then
`∫ hₖ • gₖ dμ → ∫ h • g dμ`: by `Submission.adr_uniform_bound_of_weak_bounded`,
`‖∫ (hₖ - h) • gₖ dμ‖ ≤ M ‖hₖ - h‖_∞ → 0`, and `∫ h • gₖ dμ → ∫ h • g dμ` by hypothesis. -/
theorem Submission.adr_weak_tendsto_of_tendstoUniformly : ∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μ) atTop (𝓝 (∫ x, f x • g x ∂μ))) → IsCompact K → (∀ k, Continuous (hs k)) → Continuous h → (∀ᶠ k in atTop, ∀ x ∉ K, hs k x = 0) → (∀ x ∉ K, h x = 0) → TendstoUniformly hs h atTop → Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ) atTop (𝓝 (∫ x, h x • g x ∂μ)) := by
  intro P Q μ gs g hs h K hloc hweak hK hcont hc hsK hK0 hunif
  -- convergent sequences are bounded, so the uniform bound applies on `K`
  obtain ⟨M, hM⟩ := Submission.adr_uniform_bound_of_weak_bounded P Q μ gs K hloc
    (fun f hf hfc => by
      obtain ⟨C, hC⟩ :=
        isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hweak f hf hfc))
      exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩) hK
  -- `h` vanishes off the compact `K`, so it is an admissible test function
  have hhc : HasCompactSupport h := HasCompactSupport.intro hK hK0
  -- `∫ hₖ • gₖ dμ - ∫ h • gₖ dμ = ∫ (hₖ - h) • gₖ dμ → 0`
  have hdiff : Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ - ∫ x, h x • gs k x ∂μ) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hδ : 0 < ε / (2 * (|M| + 1)) := by positivity
    filter_upwards [hsK, Metric.tendstoUniformly_iff.1 hunif _ hδ] with k hk0 hk1
    rw [dist_zero_right, ← integral_sub
      ((hloc k).integrable_smul_left_of_hasCompactSupport (hcont k) (HasCompactSupport.intro hK hk0))
      ((hloc k).integrable_smul_left_of_hasCompactSupport hc hhc)]
    simp_rw [← sub_smul]
    calc ‖∫ x, (hs k x - h x) • gs k x ∂μ‖ ≤ M * (ε / (2 * (|M| + 1))) :=
          hM k (fun x => hs k x - h x) _ ((hcont k).sub hc)
            (fun x hx => by simp [hk0 x hx, hK0 x hx])
            (fun x => by simpa [Real.dist_eq, abs_sub_comm] using (hk1 x).le)
      _ ≤ |M| * (ε / (2 * (|M| + 1))) := mul_le_mul_of_nonneg_right (le_abs_self M) hδ.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [mul_nonneg (abs_nonneg M) hε.le]
  simpa using hdiff.add (hweak h hc hhc)
/-- **Rescaled translates converge uniformly** (Simon, Appendix A, the weak limits
`ψ = lim φ_{x+λⱼβx,λⱼ}`; step 3 of the proof of `adr_weak_tendsto_comp_affine`).  If `f` is
continuous with compact support and `c_k → 1`, then `f(c_k⁻¹(w − y)) → f(w − y)` uniformly in `w`,
and `f(· − y)` and, for large `k`, `f(c_k⁻¹(· − y))` vanish off one compact ball `K = B̄_{2R}(y)`,
where `R ≥ 1` and `f = 0` off `B̄_R(0)`.  No sign of `c_k` is assumed: eventually `1/2 < c_k < 2`. -/
theorem Submission.adr_rescaled_translate_tendstoUniformly : ∀ (P : ℕ) (f : Euclid P → ℝ) (y : Euclid P) (mus : ℕ → ℝ), Continuous f → HasCompactSupport f → Tendsto mus atTop (𝓝 1) → ∃ K : Set (Euclid P), IsCompact K ∧ (∀ w ∉ K, f (w - y) = 0) ∧ (∀ᶠ k in atTop, ∀ w ∉ K, f ((mus k)⁻¹ • (w - y)) = 0) ∧ TendstoUniformly (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) atTop := by
  intro P f y mus hf hfc hmus
  -- step 1: `tsupport f ⊆ B̄_{R₀}(0)`; with `R := max R₀ 1 ≥ 1`, `f x = 0` whenever `‖x‖ > R`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hzero : ∀ x : Euclid P, R < ‖x‖ → f x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
    have h := hR₀ hxs
    rw [mem_closedBall_zero_iff] at h
    linarith [le_max_left R₀ 1]
  have h2R : 0 < 2 * R := by linarith
  -- step 2: `K := B̄_{2R}(y)`; `f (w - y) = 0` off `K`
  have hK : ∀ w ∉ closedBall y (2 * R), f (w - y) = 0 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    exact hzero _ (by linarith)
  -- step 3: eventually `1 / 2 < c_k < 2`, so `‖c_k⁻¹ (w - y)‖ > 2R / 2 = R` and
  -- `f (c_k⁻¹ (w - y)) = 0` off `K`
  have hKk : ∀ᶠ k in atTop, ∀ w ∉ closedBall y (2 * R), f ((mus k)⁻¹ • (w - y)) = 0 := by
    filter_upwards [hmus (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))] with k hk w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    have hpos : 0 < mus k := by linarith [hk.1]
    apply hzero
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith [hk.2]
  refine ⟨closedBall y (2 * R), isCompact_closedBall y (2 * R), hK, hKk, ?_⟩
  -- step 4: `f` is uniformly continuous; on `K` the argument moves by
  -- `|1 - c_k⁻¹| ‖w - y‖ ≤ |c_k⁻¹ - 1| 2R → 0`, and off `K` both values vanish
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf) ε hε
  have hinv : Tendsto (fun k => (mus k)⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hmus.inv₀ one_ne_zero
  filter_upwards [hKk, Metric.tendsto_nhds.mp hinv (δ / (2 * R)) (div_pos hδ h2R)]
    with k hk hk' w
  show dist (f (w - y)) (f ((mus k)⁻¹ • (w - y))) < ε
  by_cases hw : w ∈ closedBall y (2 * R)
  · apply hfδ
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [Real.dist_eq, abs_sub_comm] at hk'
    have hsub : (w - y) - (mus k)⁻¹ • (w - y) = (1 - (mus k)⁻¹) • (w - y) := by
      rw [sub_smul, one_smul]
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |1 - (mus k)⁻¹| * ‖w - y‖ ≤ |1 - (mus k)⁻¹| * (2 * R) :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ < δ / (2 * R) * (2 * R) := mul_lt_mul_of_pos_right hk' h2R
      _ = δ := div_mul_cancel₀ δ h2R.ne'
  · rw [hK w hw, hk w hw, dist_self]
    exact hε

/-- **Simon, proof of A.4 (chapter-A.txt lines 125–133): weak limits of rescalings.**  If
`gₖ ⇀ g` in the weak sense of Appendix A (lines 13–15: tested against `C⁰_c(ℝᴾ)`), each `gₖ`
locally `μH[n]`-integrable, and `cₖ > 0`, `cₖ → 1`, then `gₖ(y + cₖ ·) ⇀ g(y + ·)`.  The change of
variables `w = y + cₖ x` (`adr_hausdorff_integral_comp_affine`) gives
`∫ f(x) gₖ(y + cₖ x) dμ = (cₖⁿ)⁻¹ ∫ fₖ gₖ dμ` with `fₖ = f(cₖ⁻¹ • (· - y))`.  The `fₖ` converge
uniformly to `f(· - y)` with supports eventually in a fixed compact set
(`adr_rescaled_translate_tendstoUniformly`), so the Banach–Steinhaus bound behind
`adr_weak_tendsto_of_tendstoUniformly` gives `∫ fₖ gₖ dμ → ∫ f(· - y) g dμ`. -/
theorem Submission.adr_weak_tendsto_comp_affine : ∀ (P n Q : ℕ) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (y : Euclid P) (mus : ℕ → ℝ), (∀ k, LocallyIntegrable (gs k) μH[(n : ℝ)]) → (∀ k, 0 < mus k) → Tendsto mus atTop (𝓝 1) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g x ∂μH[(n : ℝ)]))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g (y + x) ∂μH[(n : ℝ)])) := by
  intro P n Q gs g y mus hloc hpos hmus hweak f hf hfc
  -- `fₖ = f (cₖ⁻¹ • (· - y)) → f (· - y)` uniformly, all eventually vanishing off a compact `K`
  obtain ⟨K, hK, h0, hk0, hunif⟩ :=
    Submission.adr_rescaled_translate_tendstoUniformly P f y mus hf hfc hmus
  -- change of variables `w = y + cₖ • x`, and `w = y + x` in the limit
  have hL : ∀ k, ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)] =
      ((mus k) ^ n)⁻¹ • ∫ w, f ((mus k)⁻¹ • (w - y)) • gs k w ∂μH[(n : ℝ)] := by
    intro k
    rw [← Submission.adr_hausdorff_integral_comp_affine P n Q
      (fun w => f ((mus k)⁻¹ • (w - y)) • gs k w) y (mus k) (hpos k)]
    simp only [add_sub_cancel_left, inv_smul_smul₀ (hpos k).ne']
  have hR : ∫ x, f x • g (y + x) ∂μH[(n : ℝ)] = ∫ w, f (w - y) • g w ∂μH[(n : ℝ)] := by
    simpa only [one_smul, add_sub_cancel_left, one_pow, inv_one] using
      Submission.adr_hausdorff_integral_comp_affine P n Q (fun w => f (w - y) • g w) y 1 one_pos
  -- weak convergence against the moving test functions `fₖ`
  have hmain := Submission.adr_weak_tendsto_of_tendstoUniformly P Q μH[(n : ℝ)] gs g
    (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) K hloc hweak hK
    (fun k => by fun_prop) (by fun_prop) hk0 h0 hunif
  -- the Jacobian factors `(cₖⁿ)⁻¹ → 1`
  have hc : Tendsto (fun k => ((mus k) ^ n)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, inv_one] using (hmus.pow n).inv₀ (pow_ne_zero n one_ne_zero)
  have hlim := hc.smul hmain
  rw [one_smul] at hlim
  rw [hR]
  exact hlim.congr fun k => (hL k).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
