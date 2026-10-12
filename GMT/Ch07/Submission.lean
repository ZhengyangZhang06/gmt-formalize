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

/-- Step 3 of the tilt-excess/height estimate (Simon Ch. 5, Lemma 2.1, display (2)): for
subspaces `T`, `S` of `ℝᴾ` with `dim T = dim S`,
`trace(p_T ∘ (I − p_S)) = ½ Σᵢ |p_T eᵢ − p_S eᵢ|²`, i.e. `½ |p_T − p_S|²` in the Hilbert–Schmidt
norm.  `p_T`, `p_S` are symmetric idempotents with `trace p_T = dim T`, `trace p_S = dim S`
(`p = ι ∘ π`, cyclicity), so `Σᵢ |(p_T − p_S) eᵢ|² = trace((p_T − p_S)²) =
dim T + dim S − 2 trace(p_T p_S)`, while `trace(p_T (I − p_S)) = dim T − trace(p_T p_S)`. -/
theorem Submission.dorag_th_trace_proj_comp_compl : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)), Module.finrank ℝ T = Module.finrank ℝ S → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) = 1 / 2 * ∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  intro P T S hTS
  -- step 2: `trace p_K = dim K`, as `p_K = ι ∘ π`, `π ∘ ι = id_K` and the trace is cyclic
  have htr : ∀ K : Submodule ℝ (Euclid P),
      LinearMap.trace ℝ (Euclid P) K.starProjection.toLinearMap =
        (Module.finrank ℝ K : ℝ) := by
    intro K
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp :
        K.orthogonalProjectionOnto.toLinearMap ∘ₗ K.subtypeL.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.trace_id]
  set p : Euclid P →L[ℝ] Euclid P := T.starProjection
  set s : Euclid P →L[ℝ] Euclid P := S.starProjection
  have hp : LinearMap.trace ℝ (Euclid P) p.toLinearMap = (Module.finrank ℝ T : ℝ) := htr T
  have hs : LinearMap.trace ℝ (Euclid P) s.toLinearMap = (Module.finrank ℝ S : ℝ) := htr S
  -- step 1: `p` and `s` are symmetric idempotents
  have hp_symm : ∀ u w : Euclid P, inner ℝ (p u) w = inner ℝ u (p w) :=
    T.inner_starProjection_left_eq_right
  have hs_symm : ∀ u w : Euclid P, inner ℝ (s u) w = inner ℝ u (s w) :=
    S.inner_starProjection_left_eq_right
  have hpp : p.toLinearMap ∘ₗ p.toLinearMap = p.toLinearMap := by
    rw [← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap T.isIdempotentElem_starProjection.eq
  have hss : s.toLinearMap ∘ₗ s.toLinearMap = s.toLinearMap := by
    rw [← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection.eq
  -- steps 3–4: `D = p - s` is symmetric, so `Σᵢ ‖D eᵢ‖² = Σᵢ ⟪eᵢ, D (D eᵢ)⟫ = trace (D ∘ D)`
  have hD : ∀ u w : Euclid P, inner ℝ ((p - s) u) w = inner ℝ u ((p - s) w) := by
    intro u w
    simp only [sub_apply, inner_sub_left, inner_sub_right, hp_symm, hs_symm]
  have hsum : ∑ i : Fin P,
      ‖p (EuclideanSpace.single i (1 : ℝ)) - s (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        LinearMap.trace ℝ (Euclid P) ((p - s).toLinearMap ∘ₗ (p - s).toLinearMap) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← hD,
      real_inner_self_eq_norm_sq, sub_apply]
  -- step 6: `p ∘ (I - s) = p - p ∘ s`
  have hlhs : p.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - s).toLinearMap =
      p.toLinearMap - p.toLinearMap ∘ₗ s.toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub, ContinuousLinearMap.coe_id,
      LinearMap.comp_id]
  -- step 5: `D ∘ D = p + s - p ∘ s - s ∘ p` and `trace (s ∘ p) = trace (p ∘ s)`; step 7
  rw [hlhs, hsum, ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, hpp, hss, map_sub, map_sub, map_sub, map_sub,
    LinearMap.trace_comp_comm' p.toLinearMap s.toLinearMap, hp, hs, hTS]
  ring
/-- **Operator norm ≤ Hilbert–Schmidt norm** (step 3 of the tilt-excess estimate, Simon 5.2.1: the
bound `‖p_x − p_S‖ ≤ |p_x − p_S|` used for the cross term).  For every linear map `A` of `ℝᴾ` and
every `v ∈ ℝᴾ`, `|Av|² ≤ (Σᵢ |A eᵢ|²) |v|²`, where `eᵢ` is the standard basis.  Expanding
`v = Σᵢ vᵢ eᵢ` gives `Av = Σᵢ vᵢ A eᵢ`, so `|Av| ≤ Σᵢ |vᵢ| |A eᵢ|` by the triangle inequality;
squaring and Cauchy–Schwarz give `|Av|² ≤ (Σᵢ vᵢ²)(Σᵢ |A eᵢ|²)`, and `Σᵢ vᵢ² = |v|²`. -/
theorem Submission.dorag_th_norm_apply_sq_le_hs : ∀ (P : ℕ) (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P), ‖A v‖ ^ 2 ≤ (∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v‖ ^ 2 := by
  intro P A v
  -- Step 1: `v = Σᵢ vᵢ eᵢ` in the orthonormal basis `EuclideanSpace.basisFun`
  have hv : v = ∑ i : Fin P, v i • EuclideanSpace.single i (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v).symm
  -- Step 2: `Av = Σᵢ vᵢ A eᵢ`, so `|Av| ≤ Σᵢ |vᵢ| |A eᵢ|`
  have hAv : A v = ∑ i : Fin P, v i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  have h1 : ‖A v‖ ≤ ∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAv]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_smul]
  -- Step 3: Cauchy–Schwarz for finite sums, and `Σᵢ |vᵢ|² = |v|²`
  have h2 : (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin P, |v i| ^ 2) * ∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin P, |v i| ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  -- Step 4: both sides of step 2 are nonnegative, so square it and combine with step 3
  calc ‖A v‖ ^ 2 ≤ (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = _ := by rw [h3, mul_comm]
/-- **Divergence of the tilt test field `X(y) = ζ(y)²((y − ξ) − p_S(y − ξ))`** (Simon Ch. 5, proof
of Lemma 2.1: the test field `X = ζ²(x)x′` and the computation of `div_M X`, chapter-05.txt
lines 222–247).  With `w(y) = (y − ξ) − p_S(y − ξ)`, `Dw(x) = I − p_S` and
`D(ζ²)(x) = 2ζ(x)Dζ(x)`, so by the product rule `DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x)`
(`(L ⊗ u)h = L(h)u`).  Composing with `p_T`, linearity of the trace and `trace(L ⊗ u) = L(u)` give
`trace(p_T ∘ DX(x)) = ζ(x)² trace(p_T ∘ (I − p_S)) + 2ζ(x) Dζ(x)[p_T w(x)]`; for
`T = approxTangentPlane n M x` the left side is `tangentialDivergence n M X x = div_M X(x)`. -/
theorem Submission.dorag_th_trace_comp_fderiv_test_field : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)) (ζ : Euclid P → ℝ) (ξ x : Euclid P), DifferentiableAt ℝ ζ x → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))) x).toLinearMap) = ζ x ^ 2 * LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) + 2 * ζ x * fderiv ℝ ζ x (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
  intro P T S ζ ξ x hζ
  -- Step 1: `w(y) = (y − ξ) − p_S(y − ξ)` is affine, with `Dw(x) = I − p_S`.
  have hw : HasFDerivAt (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ))
      (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection) x := by
    have h : HasFDerivAt (fun y : Euclid P => y - ξ) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const ξ
    have h' := h.sub (S.starProjection.hasFDerivAt.comp x h)
    rwa [ContinuousLinearMap.comp_id] at h'
  -- Step 2: `D(ζ²)(x) = 2ζ(x)·Dζ(x)`.
  have hg : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    simpa using hζ.hasFDerivAt.pow 2
  -- Step 3: product rule, `DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x)`.
  have hX : HasFDerivAt (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ)))
      (ζ x ^ 2 • (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection) +
        ((2 * ζ x) • fderiv ℝ ζ x).smulRight ((x - ξ) - S.starProjection (x - ξ))) x :=
    hg.smul hw
  rw [hX.fderiv]
  -- Step 4: `p_T ∘ DX(x) = ζ(x)²(p_T ∘ (I − p_S)) + (2ζ(x)Dζ(x)) ⊗ p_T w(x)`.
  have hcomp : T.starProjection.toLinearMap ∘ₗ (ζ x ^ 2 • (ContinuousLinearMap.id ℝ (Euclid P) -
        S.starProjection) + ((2 * ζ x) • fderiv ℝ ζ x).smulRight
          ((x - ξ) - S.starProjection (x - ξ))).toLinearMap =
      ζ x ^ 2 • (T.starProjection.toLinearMap ∘ₗ
          (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) +
        (2 * ζ x) • (fderiv ℝ ζ x).toLinearMap.smulRight
          (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
    ext v
    simp [smul_smul]
  -- Steps 5–6: the trace is linear and `trace(L ⊗ u) = L(u)`.
  rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, smul_eq_mul, smul_eq_mul,
    ContinuousLinearMap.coe_coe]

/-- **Simon, proof of Ch. 5, Lemma 2.1** (displays (1)–(3)), for an arbitrary cut-off `ζ`: with
`w(x) = (x − ξ) − p_S(x − ξ)`, `∫ζ²|p_{TₓM} − p_S|² dμ ≤ 16∫|Dζ|²|w|² dμ + 4∫κζ²|w| dμ`.
Test the first variation with `X = ζ²w`.  For `μ`-a.e. `x` we have `dim TₓM = n = dim S`, so
`div_M X = ½ζ²|p_{TₓM} − p_S|² + 2ζ Dζ[p_{TₓM}w]` (`dorag_th_trace_comp_fderiv_test_field`,
`dorag_th_trace_proj_comp_compl`).  As `p_S w = 0`, `|p_{TₓM}w| ≤ |p_{TₓM} − p_S| |w|`
(`dorag_th_norm_apply_sq_le_hs`), and `2αβ ≤ ¼α² + 4β²` bounds the cross term; `|⟨X, H⟩| ≤ κζ²|w|`.
Every integrand is bounded and vanishes off the compact `tsupport ζ ⊆ U`, which has finite
`μ`-measure, so the `¼`-term can be absorbed. -/
theorem Submission.dorag_th_tilt_energy_inequality : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (S : Submodule ℝ (Euclid P)) (ξ : Euclid P) (ζ : Euclid P → ℝ), W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → Module.finrank ℝ S = n → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ W → ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure := by
  intro P n U W R H κ S ξ ζ hWU hpM hH hHκ hMC hS hζC hζcpt hζW
  -- Step 1: `κ ≥ 0`.
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- Step 2: `K = tsupport ζ` is compact and `K ⊆ U`, so `μ(K) < ∞`.
  have hKm : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
  have hμK : R.measure (tsupport ζ) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hζcpt (hζW.trans hWU)
  -- Step 3: bounded a.e. strongly measurable functions vanishing off `K` are integrable.
  have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f R.measure → (∃ C, ∀ x, |f x| ≤ C) →
      (∀ x, x ∉ tsupport ζ → f x = 0) → Integrable f R.measure := by
    rintro f hf ⟨C, hC⟩ h0
    have hg : Integrable ((tsupport ζ).indicator (fun _ => C)) R.measure :=
      (integrableOn_const hμK).integrable_indicator hKm
    refine hg.mono' hf (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport ζ
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hC x
    · rw [Set.indicator_of_notMem hx, h0 x hx, norm_zero]
  -- Step 4: `|ζ| ≤ Z`, `‖Dζ‖ ≤ D'`, `|w| ≤ B` on `K`, `ζ = Dζ = 0` off `K`, `0 ≤ a ≤ 4P`.
  have hζ_cont : Continuous ζ := hζC.continuous
  have hDζ_cont : Continuous (fderiv ℝ ζ) := hζC.continuous_fderiv one_ne_zero
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx => fderiv_of_notMem_tsupport ℝ hx
  have hw_cont : Continuous (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ)) := by fun_prop
  obtain ⟨Z, hZ⟩ := hζ_cont.bounded_above_of_compact_support hζcpt
  obtain ⟨D', hD'⟩ := hDζ_cont.bounded_above_of_compact_support (hζcpt.fderiv (𝕜 := ℝ))
  obtain ⟨B₁, hB₁⟩ := IsCompact.exists_bound_of_continuousOn hζcpt hw_cont.continuousOn
  set B := max B₁ 0
  have hB : ∀ x ∈ tsupport ζ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ B :=
    fun x hx => (hB₁ x hx).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ ξ)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' ξ)
  have hζsq : ∀ x, ζ x ^ 2 ≤ Z ^ 2 := by
    intro x
    have := hZ x; rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (ζ x), sq_abs (ζ x)]
  set a : Euclid P → ℝ := fun x => ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
      (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have ha0 : ∀ x, 0 ≤ a x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha_le : ∀ x, a x ≤ 4 * P := by
    intro x
    have : ∀ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
          ≤ 4 := by
      intro i
      have h1 := (approxTangentPlane n R.carrier x).norm_starProjection_apply_le
        (EuclideanSpace.single i (1 : ℝ))
      have h2 := S.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℝ))
      have h3 := norm_sub_le ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ))) (S.starProjection (EuclideanSpace.single i (1 : ℝ)))
      simp only [PiLp.norm_single, norm_one] at h1 h2
      nlinarith [norm_nonneg ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ)))]
    calc a x ≤ ∑ _i : Fin P, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
      _ = 4 * P := by simp [mul_comm]
  -- Step 5: `a` and `x ↦ p_x w(x)` are `μ`-a.e. strongly measurable.
  have ha_meas : AEStronglyMeasurable a R.measure := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (((hpM.apply_continuousLinearMap _).sub aestronglyMeasurable_const).norm).pow 2
  have hpw_meas : AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ))) R.measure :=
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P) => A v)
      (by fun_prop) hpM hw_cont.aestronglyMeasurable
  -- Step 6: `F₁ = ζ²a`, `F₂ = 2ζ Dζ[p_x w]`, `F₃ = ⟨X, H⟩` (`X = ζ²w`), `G₁ = ‖Dζ‖²|w|²` and
  -- `G₂ = κζ²|w|` are bounded and vanish off `K`, hence are `μ`-integrable.
  set F1 : Euclid P → ℝ := fun x => ζ x ^ 2 * a x
  set F2 : Euclid P → ℝ := fun x => 2 * ζ x * fderiv ℝ ζ x
      ((approxTangentPlane n R.carrier x).starProjection ((x - ξ) - S.starProjection (x - ξ)))
  set X : Euclid P → Euclid P := fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))
  set F3 : Euclid P → ℝ := fun x => inner ℝ (X x) (H x)
  set G1 : Euclid P → ℝ := fun x => ‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2
  set G2 : Euclid P → ℝ := fun x => κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖
  have hX_cont : Continuous X := by fun_prop
  have hF1i : Integrable F1 R.measure := by
    refine hint F1 ((hζ_cont.aestronglyMeasurable.pow 2).mul ha_meas)
      ⟨Z ^ 2 * (4 * P), fun x => ?_⟩ (fun x hx => by simp [F1, hζ0 x hx])
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (ha0 x))]
    exact mul_le_mul (hζsq x) (ha_le x) (ha0 x) (sq_nonneg _)
  have hF2i : Integrable F2 R.measure := by
    refine hint F2 ?_ ⟨2 * Z * (D' * B), fun x => ?_⟩ (fun x hx => by simp [F2, hζ0 x hx])
    · exact (aestronglyMeasurable_const.mul hζ_cont.aestronglyMeasurable).mul
        (Continuous.comp_aestronglyMeasurable₂
          (g := fun (L : Euclid P →L[ℝ] ℝ) (v : Euclid P) => L v)
          (by fun_prop) hDζ_cont.aestronglyMeasurable hpw_meas)
    · by_cases hx : x ∈ tsupport ζ
      · have h1 : |ζ x| ≤ Z := by simpa [Real.norm_eq_abs] using hZ x
        have h2 : |fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
            ((x - ξ) - S.starProjection (x - ξ)))| ≤ D' * B := by
          rw [← Real.norm_eq_abs]
          calc _ ≤ ‖fderiv ℝ ζ x‖ * ‖(approxTangentPlane n R.carrier x).starProjection
                ((x - ξ) - S.starProjection (x - ξ))‖ := (fderiv ℝ ζ x).le_opNorm _
            _ ≤ D' * B := by
              apply mul_le_mul (hD' x) _ (norm_nonneg _) hD'0
              exact ((approxTangentPlane n R.carrier x).norm_starProjection_apply_le _).trans
                (hB x hx)
        simp only [F2, abs_mul, abs_two]
        have := mul_le_mul h1 h2 (abs_nonneg _) hZ0
        nlinarith [abs_nonneg (ζ x)]
      · simp only [F2, hζ0 x hx, mul_zero, zero_mul, abs_zero]
        positivity
  have hF3i : Integrable F3 R.measure := by
    refine hint F3 (Continuous.comp_aestronglyMeasurable₂
      (g := fun (u v : Euclid P) => (inner ℝ u v : ℝ)) continuous_inner
      hX_cont.aestronglyMeasurable hH) ⟨Z ^ 2 * B * κ, fun x => ?_⟩
      (fun x hx => by simp [F3, X, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · calc |F3 x| ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
        _ ≤ (Z ^ 2 * B) * κ := by
          apply mul_le_mul _ (hHκ x) (norm_nonneg _) (by positivity)
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
          exact mul_le_mul (hζsq x) (hB x hx) (norm_nonneg _) (sq_nonneg _)
    · simp only [F3, X, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul,
        inner_zero_left, abs_zero]
      positivity
  have hG1i : Integrable G1 R.measure := by
    refine hint G1 ((hDζ_cont.norm.pow 2).mul (hw_cont.norm.pow 2)).aestronglyMeasurable
      ⟨D' ^ 2 * B ^ 2, fun x => ?_⟩ (fun x hx => by simp [G1, hDζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hD' x) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hB x hx) 2) (sq_nonneg _) (sq_nonneg _)
    · simp only [G1, hDζ0 x hx, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, abs_zero]
      positivity
  have hG2i : Integrable G2 R.measure := by
    refine hint G2 ((continuous_const.mul (hζ_cont.pow 2)).mul hw_cont.norm).aestronglyMeasurable
      ⟨κ * Z ^ 2 * B, fun x => ?_⟩ (fun x hx => by simp [G2, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hζsq x) hκ) (hB x hx) (norm_nonneg _)
        (by positivity)
    · simp only [G2, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
        abs_zero]
      positivity
  -- Step 7: `X` is `C¹` with `tsupport X ⊆ K ⊆ W`, so `δV(X) = -∫F₃ dμ`.
  have hXC : ContDiff ℝ 1 X :=
    (hζC.pow 2).smul ((contDiff_id.sub contDiff_const).sub
      (S.starProjection.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hXsupp : tsupport X ⊆ tsupport ζ := by
    apply closure_mono
    intro y hy
    by_contra h
    apply hy
    simp only [Function.mem_support, not_not] at h
    simp [X, h]
  have hXcpt : HasCompactSupport X := hζcpt.mono' ((subset_tsupport X).trans hXsupp)
  have hMCX := hMC X hXC hXcpt (hXsupp.trans hζW)
  -- Step 8: `δV(X) = ∫ div_M X dμ`, since `μ = (Hⁿ⌞M).withDensity θ`.
  have hFV : R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
    have hm : Measurable (fun x => ((R.mult x : NNReal))) :=
      (measurable_from_nat (f := fun m : ℕ => (m : NNReal))).comp R.measurable_mult
    have h := integral_withDensity_eq_integral_smul hm
      (fun x => tangentialDivergence n R.carrier X x) (μ := μHE[n].restrict R.carrier)
    simp only [ENNReal.coe_natCast] at h
    rw [IMRep.measure, h, IMRep.firstVariation]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])
  rw [hFV] at hMCX
  -- Step 9: `dim TₓM = n` for `μ`-a.e. `x` (`R.orients`, `μ ≪ Hⁿ⌞M`).
  have hdim : ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec.1
  -- Step 10: `div_M X = ½F₁ + F₂` `μ`-a.e. (children (D) and (B)).
  have hdiv : (fun x => tangentialDivergence n R.carrier X x) =ᵐ[R.measure]
      (fun x => 1 / 2 * F1 x + F2 x) := by
    filter_upwards [hdim] with x hx
    have hd := Submission.dorag_th_trace_comp_fderiv_test_field P
      (approxTangentPlane n R.carrier x) S ζ ξ x ((hζC.differentiable one_ne_zero) x)
    rw [tangentialDivergence, hd,
      Submission.dorag_th_trace_proj_comp_compl P _ S (by rw [hx, hS])]
    simp only [F1, F2, a]
    ring
  -- Step 11: `½∫F₁ + ∫F₂ = ∫ div_M X dμ = δV(X) = -∫F₃`.
  have hid : 1 / 2 * ∫ x, F1 x ∂R.measure + ∫ x, F2 x ∂R.measure = -∫ x, F3 x ∂R.measure := by
    rw [← integral_const_mul, ← integral_add (hF1i.const_mul _) hF2i, ← integral_congr_ae hdiv]
    exact hMCX
  -- Step 12: cross term.  `p_S w = 0` gives `p_T w = (p_T - p_S)w`, so by child (C)
  -- `|L(p_T w)| ≤ ‖L‖ √|p_T - p_S|² |w|`; then `-F₂ ≤ ¼F₁ + 4G₁` by `2αβ ≤ ¼α² + 4β²`.
  have hcross : ∀ (T : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] ℝ) (v : Euclid P),
      |L (T.starProjection (v - S.starProjection v))| ≤
        ‖L‖ * (Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v - S.starProjection v‖) := by
    intro T L v
    set w := v - S.starProjection v
    have hw : S.starProjection w = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff S).mpr
        (Submodule.sub_starProjection_mem_orthogonal v)
    have heq : T.starProjection w = (T.starProjection - S.starProjection) w := by
      simp [hw]
    have hsq := Submission.dorag_th_norm_apply_sq_le_hs P (T.starProjection - S.starProjection) w
    simp only [sub_apply] at hsq
    have hn : ‖(T.starProjection - S.starProjection) w‖ ≤
        Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg w),
        ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by simpa [sub_apply] using hsq)
    rw [heq]
    calc |L ((T.starProjection - S.starProjection) w)|
        ≤ ‖L‖ * ‖(T.starProjection - S.starProjection) w‖ := by
          rw [← Real.norm_eq_abs]; exact L.le_opNorm _
      _ ≤ _ := by gcongr
  have hb1 : ∀ x, -F2 x ≤ 1 / 4 * F1 x + 4 * G1 x := by
    intro x
    have ht := hcross (approxTangentPlane n R.carrier x) (fderiv ℝ ζ x) (x - ξ)
    set t := fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ)))
    set c := ‖fderiv ℝ ζ x‖
    set s := Real.sqrt (a x)
    set β := ‖(x - ξ) - S.starProjection (x - ξ)‖
    have hs : s ^ 2 = a x := Real.sq_sqrt (ha0 x)
    have hc0 : 0 ≤ c := norm_nonneg _
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hβ0 : 0 ≤ β := norm_nonneg _
    have h1 : -(2 * ζ x * t) ≤ 2 * |ζ x| * |t| := by
      have := neg_le_abs (2 * ζ x * t)
      rwa [abs_mul, abs_mul, abs_two] at this
    have h2 : 2 * |ζ x| * |t| ≤ 2 * |ζ x| * (c * (s * β)) := by gcongr
    have h3 : 2 * |ζ x| * (c * (s * β)) ≤ 1 / 4 * (ζ x ^ 2 * s ^ 2) + 4 * (c ^ 2 * β ^ 2) := by
      nlinarith [sq_nonneg (|ζ x| * s - 4 * c * β), sq_abs (ζ x), abs_nonneg (ζ x)]
    simp only [F1, F2, G1]
    rw [← hs]
    linarith
  -- Step 13: curvature term `-F₃ ≤ |X| |H| ≤ G₂`.
  have hb2 : ∀ x, -F3 x ≤ G2 x := by
    intro x
    calc -F3 x ≤ |F3 x| := neg_le_abs _
      _ ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
      _ = ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * ‖H x‖ := by
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
      _ ≤ ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * κ := by
          gcongr
          exact hHκ x
      _ = G2 x := by simp only [G2]; ring
  -- Step 14: integrate and absorb `¼∫F₁`: `∫F₁ ≤ 16∫G₁ + 4∫G₂`.
  have i1 : ∫ x, -F2 x ∂R.measure ≤ ∫ x, (1 / 4 * F1 x + 4 * G1 x) ∂R.measure :=
    integral_mono hF2i.neg ((hF1i.const_mul _).add (hG1i.const_mul _)) hb1
  have i2 : ∫ x, -F3 x ∂R.measure ≤ ∫ x, G2 x ∂R.measure := integral_mono hF3i.neg hG2i hb2
  rw [integral_neg] at i1 i2
  rw [integral_add (hF1i.const_mul _) (hG1i.const_mul _), integral_const_mul,
    integral_const_mul] at i1
  have hreal : ∫ x, F1 x ∂R.measure ≤ 16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure := by
    linarith
  -- Step 15: `F₁, G₁, G₂ ≥ 0` are integrable, so pass to lower integrals of `ofReal`.
  have hF1n : ∀ x, 0 ≤ F1 x := fun x => mul_nonneg (sq_nonneg _) (ha0 x)
  have hG1n : ∀ x, 0 ≤ G1 x := fun x => by positivity
  have hG2n : ∀ x, 0 ≤ G2 x := fun x => by positivity
  have l1 := ofReal_integral_eq_lintegral_ofReal hF1i (Filter.Eventually.of_forall hF1n)
  have l2 := ofReal_integral_eq_lintegral_ofReal hG1i (Filter.Eventually.of_forall hG1n)
  have l3 := ofReal_integral_eq_lintegral_ofReal hG2i (Filter.Eventually.of_forall hG2n)
  have hI1 : 0 ≤ ∫ x, G1 x ∂R.measure := integral_nonneg hG1n
  have hI2 : 0 ≤ ∫ x, G2 x ∂R.measure := integral_nonneg hG2n
  calc ∫⁻ x, ENNReal.ofReal (F1 x) ∂R.measure = ENNReal.ofReal (∫ x, F1 x ∂R.measure) := l1.symm
    _ ≤ ENNReal.ofReal (16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 16 * ENNReal.ofReal (∫ x, G1 x ∂R.measure) +
          ENNReal.ofReal 4 * ENNReal.ofReal (∫ x, G2 x ∂R.measure) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by rw [l2, l3]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
