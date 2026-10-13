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

/-- **Cut-off quadratic moments over `n`-planes** (the constant `cₙ` of the measurability proof
for the approximate tangent planes of Simon Ch. 3, 1.4).  For `n ≥ 1` one constant `c > 0`,
depending only on `n`, gives `∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|²` for every `P`,
every `n`-dimensional subspace `Q ⊆ ℝᴾ` and every `u ∈ ℝᴾ`.  On `ℝⁿ` put
`q(w) = ∫ max(1 − |z|², 0)⟨w, z⟩² dHⁿ(z)` and `c = q(e)`, `|e| = 1`: linear isometries preserve
`Hⁿ`, so `q` is invariant under them, `q(tw) = t²q(w)`, and a reflection maps `|w|e` to `w`,
whence `q(w) = c|w|²`; `c > 0` since the integrand is continuous, `≥ 0`, compactly supported and
`3/16` at `e/2`.  An isometry `ι = L⁻¹ : ℝⁿ → Q ⊆ ℝᴾ` carries `Hⁿ` to `Hⁿ⌞Q`, and
`⟨u, ι z⟩ = ⟨L(p_Q u), z⟩`, so the integral is `q(L(p_Q u)) = c|p_Q u|²`. -/
theorem Submission.exists_plane_cutoff_quadratic_moment_eq : ∀ n : ℕ, 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ u : Euclid P, ∫ y in (Q : Set (Euclid P)), max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 ∂μHE[n] = c * ‖Q.starProjection u‖ ^ 2 := by
  intro n hn
  -- The moment `q(w)` on the model plane `ℝⁿ`; the constant is `c = q(e)` for a unit vector `e`.
  obtain ⟨q, hq_def⟩ : ∃ q : Euclid n → ℝ,
      ∀ w, q w = ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ w z ^ 2 ∂μHE[n] :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Euclid n, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  -- `q(Rw) = q(w)` for a linear isometry `R`: substitute `z = Rz'`, `R` preserves `Hⁿ`.
  have hq_iso : ∀ (R : Euclid n ≃ₗᵢ[ℝ] Euclid n) (w : Euclid n), q (R w) = q w := by
    intro R w
    have key : ∫ z, max (1 - ‖R z‖ ^ 2) 0 * inner ℝ (R w) (R z) ^ 2 ∂μHE[n] =
        ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ (R w) z ^ 2 ∂μHE[n] :=
      (R.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n).integral_comp
        R.toHomeomorph.measurableEmbedding (fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ (R w) y ^ 2)
    simp only [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map] at key
    rw [hq_def, hq_def, ← key]
  have hq_smul : ∀ (t : ℝ) (w : Euclid n), q (t • w) = t ^ 2 * q w := by
    intro t w
    rw [hq_def, hq_def, ← integral_const_mul]
    congr 1
    funext z
    rw [real_inner_smul_left]
    ring
  -- `q(w) = c|w|²`: the reflection in `(|w|e − w)ᗮ` maps `|w|e` to `w`.
  have hq : ∀ w : Euclid n, q w = q e * ‖w‖ ^ 2 := by
    intro w
    have h1 : ‖‖w‖ • e‖ = ‖w‖ := by rw [norm_smul, he, mul_one, norm_norm]
    obtain ⟨R, hR⟩ : ∃ R : Euclid n ≃ₗᵢ[ℝ] Euclid n, R (‖w‖ • e) = w :=
      ⟨_, Submodule.reflection_sub h1⟩
    calc q w = q (R (‖w‖ • e)) := by rw [hR]
      _ = q (‖w‖ • e) := hq_iso R _
      _ = q e * ‖w‖ ^ 2 := by rw [hq_smul, mul_comm]
  -- `c > 0`: on `ℝⁿ`, `Hⁿ` is Lebesgue measure, and the integrand is `3/16` at `e/2`.
  have hc : 0 < q e := by
    have hcont : Continuous fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      fun_prop
    have hsupp : HasCompactSupport fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz => ?_
      have h1 : 1 < ‖z‖ := by simpa using hz
      have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
      simp [max_eq_right h2]
    have hnonneg : 0 ≤ fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 :=
      fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)
    have hx : (fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2) ((1 / 2 : ℝ) • e) ≠ 0 := by
      simp only [norm_smul, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      norm_num
    rw [hq_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg hx
  refine ⟨q e, hc, fun P Q hQ u => ?_⟩
  -- An orthonormal basis of `Q` indexed by `Fin n` gives `L : Q ≃ ℝⁿ`; `ι = L⁻¹` is an isometry
  -- of `ℝⁿ` onto `Q ⊆ ℝᴾ`, so `ι_# Hⁿ = Hⁿ⌞Q`.
  obtain ⟨L, -⟩ : ∃ L : Q ≃ₗᵢ[ℝ] Euclid n, True :=
    ⟨((stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)).repr, trivial⟩
  have hι : Isometry fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    isometry_subtype_coe.comp L.symm.isometry
  have hrange : Set.range (fun z : Euclid n => ((L.symm z : Q) : Euclid P)) =
      (Q : Set (Euclid P)) := by
    ext y
    refine ⟨?_, fun hy => ⟨L ⟨y, hy⟩, by simp⟩⟩
    rintro ⟨z, rfl⟩
    exact (L.symm z).2
  have hemb : MeasurableEmbedding fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    hι.isClosedEmbedding.measurableEmbedding
  have hnorm : ∀ z : Euclid n, ‖((L.symm z : Q) : Euclid P)‖ = ‖z‖ := fun z => L.symm.norm_map z
  -- `⟨u, ι z⟩ = ⟨p_Q u, ι z⟩ = ⟨L(p_Q u), z⟩`.
  have hinner : ∀ z : Euclid n, inner ℝ u ((L.symm z : Q) : Euclid P) =
      inner ℝ (L (Q.orthogonalProjectionOnto u)) z := by
    intro z
    rw [LinearIsometryEquiv.inner_map_eq_flip,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← hrange, ← hι.map_euclideanHausdorffMeasure, hemb.integral_map]
  simp only [hnorm, hinner]
  rw [← hq_def, hq, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
  rfl
/-- A field of orthogonal projections `p_x = (K x).starProjection` is a.e.-measurable (Borel
σ-algebra of the operator-norm topology) when each quadratic form `x ↦ |p_x u|²` is.  As `p_x` is
self-adjoint and idempotent, `⟪p_x u, w⟫ = (|p_x(u + w)|² − |p_x(u − w)|²)/4`, so the matrix
coefficients `⟪p_x e_a, e_b⟫` are a.e.-measurable, and `p_x = Σ_{a,b} ⟪p_x e_a, e_b⟫ ⟪e_a, ·⟫ e_b`
is a continuous linear function of them. -/
theorem Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq : ∀ (P : ℕ) (μ : Measure (Euclid P)) (K : Euclid P → Submodule ℝ (Euclid P)), (∀ u : Euclid P, AEMeasurable (fun x => ‖(K x).starProjection u‖ ^ 2) μ) → AEMeasurable (fun x => (K x).starProjection) μ := by
  intro P μ K h
  -- by polarization every coefficient `x ↦ ⟪p_x u, w⟫` is a.e.-measurable
  have hcoef : ∀ u w : Euclid P,
      AEMeasurable (fun x => inner ℝ ((K x).starProjection u) w) μ := by
    intro u w
    have key : ∀ x, inner ℝ ((K x).starProjection u) w =
        (‖(K x).starProjection (u + w)‖ ^ 2 - ‖(K x).starProjection (u - w)‖ ^ 2) / 4 := by
      intro x
      have hsym : inner ℝ ((K x).starProjection u) w =
          inner ℝ ((K x).starProjection u) ((K x).starProjection w) := by
        rw [Submodule.inner_starProjection_left_eq_right,
          Submodule.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.2 ((K x).starProjection_apply_mem w)]
      rw [hsym, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
      ring
    simp_rw [key]
    exact ((h (u + w)).sub (h (u - w))).div_const 4
  -- `p_x = Λ (g x)`, `Λ m = ∑ m_{ab} ⟪e_a, ·⟫ e_b`, `g x = (⟪p_x e_a, e_b⟫)_{ab}`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let Λ : (Fin P × Fin P → ℝ) → (Euclid P →L[ℝ] Euclid P) := fun m =>
    ∑ ab, m ab • (innerSL ℝ (e ab.1)).smulRight (e ab.2)
  have heq : (fun x => (K x).starProjection) =
      fun x => Λ fun ab => inner ℝ ((K x).starProjection (e ab.1)) (e ab.2) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [Λ, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Fintype.sum_prod_type]
    calc (K x).starProjection v = (K x).starProjection (∑ a, inner ℝ (e a) v • e a) := by
          rw [e.sum_repr']
      _ = ∑ a, inner ℝ (e a) v • (K x).starProjection (e a) := by
          simp only [map_sum, map_smul]
      _ = ∑ a, inner ℝ (e a) v • ∑ b, inner ℝ (e b) ((K x).starProjection (e a)) • e b := by
          simp only [e.sum_repr']
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [real_inner_comm (e b), smul_smul, smul_smul, mul_comm]
  -- `Λ` is continuous and `g` is a.e.-measurable coordinatewise
  have hΛ : Continuous Λ :=
    continuous_finsetSum _ fun ab _ => (continuous_apply ab).smul continuous_const
  rw [heq]
  exact hΛ.measurable.comp_aemeasurable (AEMeasurable.of_eval fun ab => hcoef _ _)
/-- For an integer multiplicity triple `R = (M, θ, ξ)` in an open set `U`, `Hⁿ⌞M` is σ-finite.
The open set `U ⊆ ℝᴾ` is σ-compact, `U = ⋃ⱼ Kⱼ` with `Kⱼ` compact.  As `θ ≥ 1` on `M`,
`Hⁿ(M ∩ Kⱼ) ≤ ∫_{M ∩ Kⱼ} θ dHⁿ < ∞`, and `M ⊆ ⋃ⱼ (M ∩ Kⱼ)`. -/
theorem Submission.dsmc_imrep_carrier_sigmaFinite : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → SigmaFinite (μHE[n].restrict R.carrier) := by
  intro P n U R hU
  -- `U` is locally compact and second countable, hence σ-compact
  obtain ⟨K, hKc, hKU⟩ : IsSigmaCompact U := by
    have := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  -- `Hⁿ(M ∩ Kⱼ) ≤ ∫_{M ∩ Kⱼ} θ dHⁿ < ∞`, since `θ ≥ 1` on `M`
  have hfin : ∀ j, μHE[n] (R.carrier ∩ K j) < ∞ := by
    intro j
    calc μHE[n] (R.carrier ∩ K j) = ∫⁻ _ in R.carrier ∩ K j, 1 ∂μHE[n] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ K j, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' (R.measurableSet_carrier.inter (hKc j).isClosed.measurableSet)
            fun x hx => Nat.one_le_cast.mpr (R.mult_pos x hx.1)
      _ < ∞ := (R.locallyIntegrable_mult (K j) (hKc j)
          ((subset_iUnion K j).trans hKU.subset)).lt_top
  -- `M ⊆ U = ⋃ⱼ Kⱼ`, so the sets `M ∩ Kⱼ` cover `M`
  refine Poincare.SimonGMT.Chapter03.sigmaFinite_restrict_of_hausdorff_finite_cover
    (fun j => R.carrier ∩ K j) ?_ hfin
  rw [← inter_iUnion, hKU]
  exact fun x hx => ⟨hx, R.carrier_subset hx⟩
/-- The blow-up integrals `x ↦ ∫_{η_{x,r}(M)} f dHⁿ` of a continuous `f ≥ 0` are Borel
measurable when `Hⁿ⌞M` is s-finite; `M` need not be measurable.  As `η_{x,r}` is a translation
followed by the dilation by `r⁻¹`, `Hⁿ(η_{x,r}(s)) = r⁻ⁿ Hⁿ(s)` for every set `s`, so
`Hⁿ⌞η_{x,r}(M) = r⁻ⁿ (η_{x,r})_#(Hⁿ⌞M)` (on Borel `B`, `η(M) ∩ B = η(M ∩ η⁻¹B)`).  Hence the
integral is `(r⁻ⁿ ∫ f(r⁻¹(y − x)) d(Hⁿ⌞M)(y)).toReal`, measurable in `x` by Tonelli for the
s-finite `Hⁿ⌞M`. -/
theorem Submission.dsmc_measurable_blowUp_image_setIntegral : ∀ (P n : ℕ) (M : Set (Euclid P)), SFinite (μHE[n].restrict M) → ∀ f : Euclid P → ℝ, Continuous f → (∀ y, 0 ≤ f y) → ∀ r : ℝ, 0 < r → Measurable (fun x : Euclid P => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) := by
  intro P n M hM f hf hf0 r hr
  set η : Euclid P → Euclid P → Euclid P := fun x => Poincare.SimonGMT.Chapter03.blowUpMap x r
    with hη
  -- `(x, y) ↦ η_x(y) = r⁻¹(y − x)` is continuous
  have hηc : Continuous fun p : Euclid P × Euclid P => η p.1 p.2 := by
    simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap]
    fun_prop
  have hηm : ∀ x, Measurable (η x) := fun x =>
    (hηc.comp (Continuous.prodMk continuous_const continuous_id)).measurable
  -- `Hⁿ(η_x(s)) = r⁻ⁿ Hⁿ(s)` for every set `s`
  have hscale : ∀ x (s : Set (Euclid P)), μHE[n] (η x '' s) = ‖r⁻¹‖₊ ^ n • μHE[n] s := by
    intro x s
    have himg : η x '' s = (fun y => r⁻¹ • y) '' (IsometryEquiv.subRight x '' s) := by
      rw [Set.image_image]
      rfl
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_x(M) = r⁻ⁿ (η_x)_#(Hⁿ⌞M)`, checked on Borel sets
  have hrestr : ∀ x, μHE[n].restrict (η x '' M) =
      ‖r⁻¹‖₊ ^ n • (μHE[n].restrict M).map (η x) := by
    intro x
    ext B hB
    rw [Measure.restrict_apply hB, Measure.smul_apply, Measure.map_apply (hηm x) hB,
      Measure.restrict_apply (hηm x hB), Set.inter_comm, ← Set.image_inter_preimage, hscale,
      Set.inter_comm]
  -- `∫_{η_x(M)} f dHⁿ = (r⁻ⁿ ∫ f ∘ η_x d(Hⁿ⌞M)).toReal`, also when `f` is not integrable
  have hint : ∀ x, ∫ y in η x '' M, f y ∂μHE[n] =
      (‖r⁻¹‖₊ ^ n • ∫⁻ y, ENNReal.ofReal (f (η x y)) ∂(μHE[n].restrict M)).toReal := by
    intro x
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable,
      hrestr, lintegral_smul_measure, lintegral_map hf.measurable.ennreal_ofReal (hηm x)]
  -- Tonelli for the s-finite measure `Hⁿ⌞M`
  show Measurable fun x => ∫ y in η x '' M, f y ∂μHE[n]
  simp_rw [hint]
  exact ((Measurable.lintegral_prod_right'
    (f := fun p : Euclid P × Euclid P => ENNReal.ofReal (f (η p.1 p.2)))
    (ENNReal.continuous_ofReal.comp (hf.comp hηc)).measurable).const_smul _).ennreal_toReal

/-- **The approximate tangent projections of an integer multiplicity triple are measurable**
(Simon Ch. 3, 1.4; Ch. 4, 2.3).  For `R = (M, θ, ξ)` in an open `U ⊆ ℝᴾ`, `x ↦ p_{TₓM}` is
a.e.-measurable for `μ_R = θHⁿ⌞M`.  As `μ_R ≪ ν = Hⁿ⌞M`, it suffices to treat `ν`, which is
σ-finite.  If `n = 0`, every candidate plane is `{0}`.  If `n ≥ 1`, `TₓM` is an approximate tangent
plane at `ν`-a.e. `x`, so for `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²` the blow-up integrals
`∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ`, which are Borel in `x`, converge `ν`-a.e. to
`∫_{TₓM} f_u dHⁿ = c|p_x u|²`.  Hence each `x ↦ |p_x u|²`, and so `x ↦ p_x`, is
`ν`-a.e.-measurable. -/
theorem Submission.dsmc_approxTangentPlane_starProjection_aemeasurable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n U R hU
  -- `μ_R = θHⁿ⌞M ≪ Hⁿ⌞M`, so it suffices to work with `ν = Hⁿ⌞M`
  refine AEMeasurable.mono_ac ?_ (withDensity_absolutelyContinuous _ _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: every candidate plane is `0`-dimensional, so `p_x = 0` for every `x`
    have h0 : ∀ x, (approxTangentPlane 0 R.carrier x).starProjection = 0 := by
      intro x
      have hK : approxTangentPlane 0 R.carrier x = ⊥ := by
        rw [approxTangentPlane]
        split_ifs with h
        · exact Submodule.finrank_eq_zero.1 h.choose_spec.1
        · rfl
      refine ContinuousLinearMap.ext fun v => ?_
      exact (Submodule.mem_bot ℝ).1
        (hK.le ((approxTangentPlane 0 R.carrier x).starProjection_apply_mem v))
    simp only [h0]
    exact aemeasurable_const
  have : SigmaFinite ((μHE[n] : Measure (Euclid P)).restrict R.carrier) :=
    Submission.dsmc_imrep_carrier_sigmaFinite P n U R hU
  obtain ⟨c, hc, hcQ⟩ := Submission.exists_plane_cutoff_quadratic_moment_eq n hn
  -- `TₓM` is an approximate tangent plane of `M` at `ν`-a.e. `x`
  have hT : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec
  refine Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq P _ _ fun u => ?_
  -- the test function `f_u(y) = max(1 − |y|², 0)⟨u, y⟩² ∈ C_c(ℝᴾ)`
  let f : Euclid P → ℝ := fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2
  have hf : Continuous f := by fun_prop
  have hf0 : ∀ y, 0 ≤ f y := fun y => mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 1) fun y hy => ?_
    have h1 : 1 < ‖y‖ := by simpa using hy
    have h2 : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith
    simp [f, max_eq_right h2]
  let F : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨f, hf⟩, hfc⟩
  -- the scales `1/(k+1) ↓ 0`
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
  -- the blow-up integrals `Φₖ(x) = ∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ` are Borel functions of `x`
  let Φ : ℕ → Euclid P → ℝ := fun k x =>
    ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (1 / ((k : ℝ) + 1)) '' R.carrier, f y ∂μHE[n]
  have hΦ : ∀ k, Measurable (Φ k) := fun k =>
    Submission.dsmc_measurable_blowUp_image_setIntegral P n R.carrier inferInstance f hf hf0 _
      (by positivity)
  -- at `ν`-a.e. `x` they converge to `∫_{TₓM} f_u dHⁿ = c|p_x u|²`
  have hlim : ∀ᵐ x ∂(μHE[n].restrict R.carrier), Tendsto (fun k => Φ k x) atTop
      (𝓝 (c * ‖(approxTangentPlane n R.carrier x).starProjection u‖ ^ 2)) := by
    filter_upwards [hT] with x hx
    rw [← hcQ P _ hx.1 u]
    exact (hx.2 F).comp hr
  refine ((aemeasurable_of_tendsto_metrizable_ae' (fun k => (hΦ k).aemeasurable) hlim).const_mul
    c⁻¹).congr (Eventually.of_forall fun x => ?_)
  exact inv_mul_cancel_left₀ hc.ne' _
/-- **Integrating factor for the monotonicity identity** (Simon Ch. 4, 3.16–3.17).  If `I` is
continuous on `(0, r]`, has derivative `I'` on `(0, r)` and `n I(s) − s I'(s) ≤ κ s I(s)` there,
then `s ↦ e^{κs} s⁻ⁿ I(s)` is nondecreasing on `(0, r]`.  On `(0, r]` this function equals
`G(s) = exp(κs − n log s) I(s)`, and `G'(s) = exp(κs − n log s) s⁻¹ (κ s I(s) − (n I(s) − s I'(s)))
≥ 0` on `(0, r)`, so the mean value theorem applies. -/
theorem Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq : ∀ (n : ℕ) (κ r : ℝ) (I I' : ℝ → ℝ), ContinuousOn I (Ioc 0 r) → (∀ s ∈ Ioo 0 r, HasDerivAt I (I' s) s) → (∀ s ∈ Ioo 0 r, (n : ℝ) * I s - s * I' s ≤ κ * s * I s) → MonotoneOn (fun s => Real.exp (κ * s) / s ^ n * I s) (Ioc 0 r) := by
  intro n κ r I I' hIc hId hineq
  -- on `(0, r]`, `e^{κs}/sⁿ · I(s) = G(s) := exp(κs − n log s) · I(s)`
  refine MonotoneOn.congr (f₁ := fun s => Real.exp (κ * s - n * Real.log s) * I s) ?_ ?_
  swap
  · intro s hs
    simp only [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hs.1]
  -- `G` is continuous on `(0, r]`
  have hGc : ContinuousOn (fun s => Real.exp (κ * s - n * Real.log s) * I s) (Ioc 0 r) := by
    refine ContinuousOn.mul (Real.continuous_exp.comp_continuousOn ?_) hIc
    exact (continuousOn_const.mul continuousOn_id).sub
      (continuousOn_const.mul (Real.continuousOn_log.mono fun s hs => hs.1.ne'))
  -- `G' = exp(κs − n log s) · ((κ − n/s) I + I') ≥ 0` on `(0, r)`; mean value theorem
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 r) hGc
    (f' := fun s => Real.exp (κ * s - n * Real.log s) * ((κ - n * s⁻¹) * I s + I' s)) ?_ ?_
  · intro s hs
    rw [interior_Ioc] at hs
    have h1 : HasDerivAt (fun s => κ * s - n * Real.log s) (κ * 1 - n * s⁻¹) s :=
      ((hasDerivAt_id' s).const_mul κ).sub ((Real.hasDerivAt_log hs.1.ne').const_mul (n : ℝ))
    exact ((h1.exp.mul (hId s hs)).congr_deriv (by ring)).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    have key : (κ - n * s⁻¹) * I s + I' s = s⁻¹ * (κ * s * I s - (n * I s - s * I' s)) := by
      linear_combination (-(κ * I s + I' s)) * mul_inv_cancel₀ hs.1.ne'
    rw [key]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (inv_nonneg.mpr hs.1.le) (sub_nonneg.mpr (hineq s hs)))
/-- **Differentiation of radial cutoff integrals** (Simon Ch. 4, 3.3–3.4, where
`I(ρ) = ∫ φ(r/ρ) dμ` is differentiated in `ρ`; here the cutoff is written in the squared ratio
`|x - z|²/t²`).  If `μ(B_r(z)) < ∞` and `η` is `C¹` with `η = 0` on `[1, ∞)`, then
`I(t) = ∫ η(|x - z|²/t²) dμ` is continuous on `(0, r]` and, for `0 < s < r`,
`I'(s) = -(∫ 2 (|x - z|²/s²) η'(|x - z|²/s²) dμ)/s` (dominated convergence and differentiation
under the integral sign). -/
theorem Submission.dsmc_em_cutoff_integral_hasDerivAt : ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), μ (ball z r) < ∞ → ContDiff ℝ 1 η → (∀ u, 1 ≤ u → η u = 0) → ContinuousOn (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (Ioc 0 r) ∧ ∀ s ∈ Ioo 0 r, HasDerivAt (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (-(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s) s := by
  intro P μ z r η hμ hη hη1
  have hηc : Continuous η := hη.continuous
  have hη'c : Continuous (deriv η) := hη.continuous_deriv le_rfl
  -- `η' = deriv η` vanishes on `(1, ∞)` (where `η` is locally zero), hence on `[1, ∞)`.
  have hη'1 : ∀ u, 1 ≤ u → deriv η u = 0 := by
    have hIoi : Ioi (1 : ℝ) ⊆ {u | deriv η u = 0} := fun u hu => by
      have hloc : η =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact hη1 v (le_of_lt hv)
      show deriv η u = 0
      rw [hloc.deriv_eq, deriv_const]
    have hIci : Ici (1 : ℝ) ⊆ {u | deriv η u = 0} := by
      rw [← closure_Ioi]
      exact closure_minimal hIoi (isClosed_eq hη'c continuous_const)
    exact fun u hu => hIci hu
  -- Bounds on `[0, 1]` for `η` and for `u ↦ 2 u η'(u)`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hηc.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (f := fun u : ℝ => 2 * u * deriv η u) (by fun_prop)
  have hg1 : ∀ u, 1 ≤ u → 2 * u * deriv η u = 0 := fun u hu => by
    rw [hη'1 u hu, mul_zero]
  -- For `0 < t ≤ r`, `g(|x - z|²/t²)` vanishes off `B_t(z) ⊆ B_r(z)` and is dominated there.
  have hdom : ∀ (g : ℝ → ℝ) (B : ℝ), (∀ u, 1 ≤ u → g u = 0) → (∀ u ∈ Icc (0 : ℝ) 1, ‖g u‖ ≤ B) →
      ∀ t, 0 < t → t ≤ r → ∀ x : Euclid P,
        ‖g (‖x - z‖ ^ 2 / t ^ 2)‖ ≤ (ball z r).indicator (fun _ => B) x := by
    intro g B hg0 hgB t ht htr x
    have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0 ⟨le_rfl, zero_le_one⟩)
    by_cases hx : ‖x - z‖ < t
    · have hxr : x ∈ ball z r := by
        rw [mem_ball, dist_eq_norm]
        exact hx.trans_le htr
      rw [indicator_of_mem hxr]
      apply hgB
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx.le 2
    · rw [not_lt] at hx
      rw [hg0 _ ?_, norm_zero]
      · exact indicator_nonneg (fun _ _ => hB) x
      · rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ ht.le hx 2
  have hint : ∀ c : ℝ, Integrable ((ball z r).indicator (fun _ => c)) μ := fun c =>
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
  have hcont : ∀ t : ℝ, Continuous fun x : Euclid P => η (‖x - z‖ ^ 2 / t ^ 2) := fun t => by
    fun_prop
  -- Pointwise derivative in `t ≠ 0`.
  have hderiv : ∀ x : Euclid P, ∀ t : ℝ, t ≠ 0 →
      HasDerivAt (fun t => η (‖x - z‖ ^ 2 / t ^ 2))
        (-(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t) t := by
    intro x t ht
    have h1 := (hasDerivAt_const t (‖x - z‖ ^ 2)).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht)
    have h2 := (hη.differentiable one_ne_zero (‖x - z‖ ^ 2 / t ^ 2)).hasDerivAt.comp t h1
    refine h2.congr_deriv ?_
    field_simp
    ring
  refine ⟨?_, fun s hs => ?_⟩
  · -- (i) continuity on `(0, r]` by dominated convergence
    refine continuousOn_of_dominated (F := fun t x => η (‖x - z‖ ^ 2 / t ^ 2))
      (bound := (ball z r).indicator (fun _ => C)) (fun t _ => (hcont t).aestronglyMeasurable)
      (fun t ht => Eventually.of_forall (hdom η C hη1 hC t ht.1 ht.2)) (hint C)
      (Eventually.of_forall fun x t ht => (hderiv x t ht.1.ne').continuousAt.continuousWithinAt)
  · -- (ii) differentiation under the integral sign on `(s/2, r)`
    have hs0 : 0 < s := hs.1
    have hb : ∀ x : Euclid P, ∀ t ∈ Ioo (s / 2) r,
        ‖-(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t‖ ≤
          (ball z r).indicator (fun _ => K) x / (s / 2) := by
      intro x t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have h1 : ‖2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)‖ ≤
          (ball z r).indicator (fun _ => K) x :=
        hdom (fun u => 2 * u * deriv η u) K hg1 hK t ht0 ht.2.le x
      have h2 : 0 ≤ (ball z r).indicator (fun _ => K) x := (norm_nonneg _).trans h1
      rw [norm_div, norm_neg, Real.norm_of_nonneg ht0.le]
      calc ‖2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)‖ / t
          ≤ (ball z r).indicator (fun _ => K) x / t := by gcongr
        _ ≤ (ball z r).indicator (fun _ => K) x / (s / 2) := by
          gcongr
          exact ht.1.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
      (F := fun t x => η (‖x - z‖ ^ 2 / t ^ 2))
      (F' := fun t x => -(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t)
      (bound := fun x => (ball z r).indicator (fun _ => K) x / (s / 2))
      (Ioo_mem_nhds (by linarith) hs.2)
      (Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
      ((hint C).mono' (hcont s).aestronglyMeasurable
        (Eventually.of_forall (hdom η C hη1 hC s hs0 hs.2.le)))
      (by fun_prop : Continuous fun x : Euclid P =>
        -(2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) / s).aestronglyMeasurable
      (Eventually.of_forall hb) ((hint K).div_const (s / 2))
      (Eventually.of_forall fun x t ht => hderiv x t (by linarith [ht.1] : 0 < t).ne')
    have hval : ∫ x, -(2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) / s ∂μ =
        -(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s := by
      rw [integral_div, integral_neg]
    rw [← hval]
    exact key.2
/-- **Radial first-variation inequality** (Simon Ch. 4, 3.2–3.3 with the bounded generalized mean
curvature of 3.14–3.16).  Test the first variation of `v(M, θ)` with the radial field
`X(x) = η(u(x)) (x - z)`, `u(x) = ‖x - z‖² / s²`, where `η ≥ 0` is `C¹`, nonincreasing and vanishes
on `[1, ∞)`.  Then `μ`-a.e. `n η(u) + 2 u η'(u) ≤ div_M X ≤ n η(u)`, and
`|X · H| ≤ κ s η(u)`, so `n ∫ η(u) dμ + ∫ 2 u η'(u) dμ ≤ ∫ div_M X dμ = -∫ X · H dμ ≤ κ s ∫ η(u) dμ`. -/
theorem Submission.dsmc_em_cutoff_first_variation_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ContDiff ℝ 1 η → (∀ u, 0 ≤ η u) → (∀ u, deriv η u ≤ 0) → (∀ u, 1 ≤ u → η u = 0) → ∀ s : ℝ, 0 < s → s < r → (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure + ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure := by
  intro P n U R H κ z r η hzU hPm hHκ hfv hη hη0 hη'0 hη1 s hs hsr
  classical
  set μ : Measure (Euclid P) := R.measure with hμ
  /- Step 0.  `κ ≥ 0`; `μ(B̄_s(z)) < ∞`; `η' = deriv η` is continuous and vanishes on `(1, ∞)`;
  `η` and `η'` are bounded on `[0, 1]`. -/
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hBc : IsCompact (closedBall z s) := isCompact_closedBall z s
  have hBm : MeasurableSet (closedBall z s) := measurableSet_closedBall
  have hBU : closedBall z s ⊆ U := (closedBall_subset_closedBall hsr.le).trans hzU
  have hBr : closedBall z s ⊆ ball z r := closedBall_subset_ball hsr
  have hμB : μ (closedBall z s) < ∞ := by
    rw [hμ, IMRep.measure, withDensity_apply _ hBm, Measure.restrict_restrict hBm, inter_comm]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult _ hBc hBU)
  have hind : ∀ c : ℝ, Integrable ((closedBall z s).indicator fun _ => c) μ := fun c =>
    (integrable_indicator_iff hBm).mpr (integrableOn_const hμB.ne)
  have hηd : ∀ u, HasDerivAt η (deriv η u) u := fun u =>
    ((hη.differentiable (by norm_num)) u).hasDerivAt
  have hηc : Continuous η := hη.continuous
  have hη'c : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have hη'1 : ∀ u, 1 < u → deriv η u = 0 := by
    intro u hu
    have : η =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact hη1 v hv.le
    rw [this.deriv_eq]
    simp
  obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Icc (0 : ℝ) 1, ‖η u‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hηc.continuousOn
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ Icc (0 : ℝ) 1, ‖deriv η u‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hη'c.continuousOn
  -- the radius ratio `u(x) = ‖x - z‖² / s²`
  have hucont : Continuous fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2 := by fun_prop
  have hu0 : ∀ x : Euclid P, 0 ≤ ‖x - z‖ ^ 2 / s ^ 2 := fun x => by positivity
  have hu_le : ∀ x ∈ closedBall z s, ‖x - z‖ ^ 2 / s ^ 2 ≤ 1 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [div_le_one (pow_pos hs 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hu_gt : ∀ x, x ∉ closedBall z s → 1 < ‖x - z‖ ^ 2 / s ^ 2 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [one_lt_div (pow_pos hs 2)]
    exact pow_lt_pow_left₀ hx hs.le two_ne_zero
  -- the two integrands vanish off `B̄_s(z)` and are bounded on it
  have hFint : Integrable (fun x => η (‖x - z‖ ^ 2 / s ^ 2)) μ := by
    refine Integrable.mono' (hind C) (hηc.comp hucont).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall z s
    · rw [indicator_of_mem hx]
      exact hC _ ⟨hu0 x, hu_le x hx⟩
    · rw [indicator_of_notMem hx, hη1 _ (hu_gt x hx).le, norm_zero]
  have hGint : Integrable
      (fun x => 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) μ := by
    refine Integrable.mono' (hind (2 * M))
      ((continuous_const.mul hucont).mul (hη'c.comp hucont)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall z s
    · have h1 := hu_le x hx
      have h2 := hM _ ⟨hu0 x, h1⟩
      rw [Real.norm_eq_abs] at h2
      rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_mul, abs_two,
        abs_of_nonneg (hu0 x)]
      calc 2 * (‖x - z‖ ^ 2 / s ^ 2) * |deriv η (‖x - z‖ ^ 2 / s ^ 2)| ≤ 2 * 1 * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) h2 (abs_nonneg _)
              (by norm_num)
        _ = 2 * M := by ring
    · rw [indicator_of_notMem hx, hη'1 _ (hu_gt x hx), mul_zero, norm_zero]
  /- Step 1.  The radial field `X(x) = η(u(x)) (x - z)` is `C¹`, with
  `DX(x) v = η(u) v + η'(u) (2/s²) ⟪x - z, v⟫ (x - z)` and `tsupport X ⊆ B̄_s(z) ⊆ B_r(z)`. -/
  let X : Euclid P → Euclid P := fun x => η (‖x - z‖ ^ 2 / s ^ 2) • (x - z)
  have hXd : ∀ x, HasFDerivAt X
      (η (‖x - z‖ ^ 2 / s ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
        ((deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2)) • innerSL ℝ (x - z)).smulRight
          (x - z)) x := by
    intro x
    have h1 : HasFDerivAt (fun x : Euclid P => x - z) (ContinuousLinearMap.id ℝ _) x :=
      (hasFDerivAt_id x).sub_const z
    have h3 : HasFDerivAt (fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2)
        ((s ^ 2)⁻¹ • (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ (Euclid P)))) x := by
      simpa only [div_eq_mul_inv] using HasFDerivAt.mul_const h1.norm_sq (s ^ 2)⁻¹
    have h5 := ((hηd (‖x - z‖ ^ 2 / s ^ 2)).comp_hasFDerivAt x h3).smul h1
    refine HasFDerivAt.congr_fderiv (f := X) h5 (ContinuousLinearMap.ext fun v => ?_)
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      ContinuousLinearMap.comp_apply, Function.comp_apply, smul_eq_mul]
    congr 2
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hXcd : ContDiff ℝ 1 X := by
    have h1 : ContDiff ℝ 1 (fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2) :=
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _
    exact (hη.comp h1).smul (contDiff_id.sub contDiff_const)
  have hXzero : ∀ x, x ∉ closedBall z s → X x = 0 := by
    intro x hx
    show η (‖x - z‖ ^ 2 / s ^ 2) • (x - z) = 0
    rw [hη1 _ (hu_gt x hx).le, zero_smul]
  have hXts : tsupport X ⊆ closedBall z s := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra h
    exact hx (hXzero x h)
  have hXcs : HasCompactSupport X := HasCompactSupport.intro hBc hXzero
  /- Step 2.  `μ`-a.e. the tangent projection is `∑ᵢ τᵢ ⟪τᵢ, ·⟫` for an orthonormal family `τ`
  of size `n` (`R.orients` and uniqueness of approximate tangent spaces). -/
  have hproj : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      (Submodule.span ℝ (range τ)).starProjection =
        ∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) := by
    intro τ hτ
    let b0 := Module.Basis.span hτ.linearIndependent
    have hb0 : ∀ i, (b0 i : Euclid P) = τ i := fun i =>
      congrArg Subtype.val (Module.Basis.span_apply hτ.linearIndependent i)
    have hb0o : Orthonormal ℝ b0 := by
      have e : (Submodule.span ℝ (range τ)).subtypeₗᵢ ∘ b0 = τ := funext hb0
      rw [← (Submodule.span ℝ (range τ)).subtypeₗᵢ.orthonormal_comp_iff, e]
      exact hτ
    rw [OrthonormalBasis.starProjection_eq_sum_rankOne (b0.toOrthonormalBasis hb0o),
      Module.Basis.coe_toOrthonormalBasis]
    simp only [hb0]
  have hμac : μ ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hPae : ∀ᵐ x ∂μ, ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧
      (approxTangentPlane n R.carrier x).starProjection =
        ∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) := by
    refine hμac.ae_le ?_
    filter_upwards [R.orients] with x ⟨Q, hQ, τ, hτ, hspan, _⟩
    have hex : ∃ Q', HasApproximateTangentSpaceAt n R.carrier x Q' := ⟨Q, hQ⟩
    have happrox : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    exact ⟨τ, hτ, by rw [happrox, ← hspan, hproj τ hτ]⟩
  /- Step 3.  `div_M X = n η(u) + η'(u) (2/s²) ∑ᵢ ⟪τᵢ, x - z⟫²`, and by Bessel's inequality and
  `η' ≤ 0`, `n η(u) + 2 u η'(u) ≤ div_M X ≤ n η(u)` `μ`-a.e. -/
  let d : Euclid P → ℝ := fun x => tangentialDivergence n R.carrier X x
  -- `trace ((∑ τᵢ ⊗ τᵢ) ∘ L) = ∑ ⟪τᵢ, L τᵢ⟫`
  have htr : ∀ (τ : Fin n → Euclid P) (L : Euclid P →L[ℝ] Euclid P),
      LinearMap.trace ℝ (Euclid P) ((∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) :
        Euclid P →L[ℝ] Euclid P).toLinearMap ∘ₗ L.toLinearMap) =
        ∑ i, inner ℝ (τ i) (L (τ i)) := by
    intro τ L
    rw [← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.finsetSum_comp,
      ContinuousLinearMap.toLinearMap_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.comp_rankOne,
      InnerProductSpace.trace_rankOne]
  -- Bessel's inequality
  have hbessel : ∀ (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∀ v : Euclid P,
      ∑ i, inner ℝ (τ i) v ^ 2 ≤ ‖v‖ ^ 2 := by
    intro τ hτ v
    have := hτ.sum_inner_products_le (s := Finset.univ) (x := v)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hdae : ∀ᵐ x ∂μ,
      n * η (‖x - z‖ ^ 2 / s ^ 2) + 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ≤
        d x ∧ d x ≤ n * η (‖x - z‖ ^ 2 / s ^ 2) := by
    filter_upwards [hPae] with x ⟨τ, hτ, hPx⟩
    have h1 : ∀ i, inner ℝ (τ i) (τ i) = (1 : ℝ) := fun i => by
      rw [real_inner_self_eq_norm_sq, hτ.1 i, one_pow]
    have e : d x = n * η (‖x - z‖ ^ 2 / s ^ 2) + deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) *
        ∑ i, inner ℝ (τ i) (x - z) ^ 2 := by
      show tangentialDivergence n R.carrier X x = _
      unfold tangentialDivergence
      rw [hPx, (hXd x).fderiv, htr]
      simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, inner_add_right,
        inner_smul_right, h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (x - z) (τ i)]
      ring
    have hb := hbessel τ hτ (x - z)
    have hS0 : 0 ≤ ∑ i, inner ℝ (τ i) (x - z) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hk : deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hη'0 _) (div_nonneg zero_le_two (sq_nonneg s))
    have h2 := mul_le_mul_of_nonpos_left hb hk
    have h3 := mul_nonpos_of_nonpos_of_nonneg hk hS0
    have e2 : deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) * ‖x - z‖ ^ 2 =
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) := by ring
    rw [e]
    exact ⟨e2 ▸ add_le_add le_rfl h2, add_le_of_nonpos_right h3⟩
  /- Step 4.  `div_M X` is `μ`-integrable: it is `AEStronglyMeasurable` (the tangent projection
  is `μ`-measurable, `DX` is continuous, `(A, B) ↦ trace (A ∘ B)` is continuous) and
  `|div_M X| ≤ n η(u) + |2 u η'(u)|` `μ`-a.e. -/
  have hTc : Continuous fun p : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
      LinearMap.trace ℝ (Euclid P) (p.1.toLinearMap ∘ₗ p.2.toLinearMap) := by
    have h1 : Continuous fun A : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) A.toLinearMap :=
      ((LinearMap.trace ℝ (Euclid P)).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact h1.comp (continuous_fst.clm_comp continuous_snd)
  have hPmeas : AEStronglyMeasurable
      (fun x => (approxTangentPlane n R.carrier x).starProjection) μ := hPm.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable d μ := by
    have h3 := hTc.comp_aestronglyMeasurable
      (hPmeas.prodMk (hXcd.continuous_fderiv one_ne_zero).aestronglyMeasurable)
    show AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) μ
    unfold tangentialDivergence
    exact h3
  have hdint : Integrable d μ := by
    refine Integrable.mono' ((hFint.const_mul n).add hGint.abs) hdmeas ?_
    filter_upwards [hdae] with x hx
    have h0 : 0 ≤ (n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) := mul_nonneg (Nat.cast_nonneg n) (hη0 _)
    have hG1 := neg_abs_le (2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2))
    have hG2 := abs_nonneg (2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2))
    show ‖d x‖ ≤ n * η (‖x - z‖ ^ 2 / s ^ 2) +
      |2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)|
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  /- Step 5.  `∫ f dμ = ∫_M θ f dHⁿ`, so `∫ div_M X dμ = R.firstVariation X`. -/
  have hμint : ∀ f : Euclid P → ℝ,
      ∫ x, f x ∂μ = ∫ x in R.carrier, (R.mult x : ℝ) * f x ∂μHE[n] := by
    intro f
    have hθ : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    have hθm : Measurable fun x => (R.mult x : NNReal) :=
      measurable_from_top.comp R.measurable_mult
    rw [hμ, IMRep.measure, hθ, integral_withDensity_eq_integral_smul hθm]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [NNReal.smul_def]
  /- Step 6.  Integrate: `n ∫ η(u) + ∫ 2 u η'(u) ≤ ∫ div_M X = -∫ X · H ≤ κ s ∫ η(u)`, using
  `|X · H| ≤ ‖X‖ κ ≤ κ s η(u)` (`X = 0` off `B̄_s(z)`). -/
  have e1 : (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ +
      ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ =
      ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) +
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) ∂μ := by
    rw [integral_add (hFint.const_mul _) hGint, integral_const_mul]
  have e3 : ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) +
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) ∂μ ≤ ∫ x, d x ∂μ := by
    refine integral_mono_ae ((hFint.const_mul _).add hGint) hdint ?_
    filter_upwards [hdae] with x hx
    exact hx.1
  have e4 : ∫ x, d x ∂μ = -∫ x, inner ℝ (X x) (H x) ∂μ := by
    rw [hμint]
    exact hfv X hXcd hXcs (hXts.trans hBr)
  have e5 : -∫ x, inner ℝ (X x) (H x) ∂μ ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ := by
    have h1 : -∫ x, inner ℝ (X x) (H x) ∂μ ≤ ∫ x, ‖inner ℝ (X x) (H x)‖ ∂μ := by
      refine (neg_le_abs _).trans ?_
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ x, ‖inner ℝ (X x) (H x)‖ ∂μ ≤ ∫ x, κ * s * η (‖x - z‖ ^ 2 / s ^ 2) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hFint.const_mul _)
        (ae_of_all _ fun x => ?_)
      show ‖inner ℝ (X x) (H x)‖ ≤ κ * s * η (‖x - z‖ ^ 2 / s ^ 2)
      by_cases hx : x ∈ closedBall z s
      · have hXn : ‖X x‖ ≤ η (‖x - z‖ ^ 2 / s ^ 2) * s := by
          show ‖η (‖x - z‖ ^ 2 / s ^ 2) • (x - z)‖ ≤ η (‖x - z‖ ^ 2 / s ^ 2) * s
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 _)]
          exact mul_le_mul_of_nonneg_left (by rwa [mem_closedBall, dist_eq_norm] at hx) (hη0 _)
        calc ‖inner ℝ (X x) (H x)‖ ≤ ‖X x‖ * ‖H x‖ := norm_inner_le_norm _ _
          _ ≤ (η (‖x - z‖ ^ 2 / s ^ 2) * s) * κ :=
            mul_le_mul hXn (hHκ x) (norm_nonneg _) (mul_nonneg (hη0 _) hs.le)
          _ = κ * s * η (‖x - z‖ ^ 2 / s ^ 2) := by ring
      · rw [hXzero x hx, inner_zero_left, norm_zero]
        exact mul_nonneg (mul_nonneg hκ0 hs.le) (hη0 _)
    rw [integral_const_mul] at h2
    exact h1.trans h2
  calc (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ +
        ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ = _ := e1
    _ ≤ _ := e3
    _ = _ := e4
    _ ≤ _ := e5
/-- **Radial cutoffs for the monotonicity formula** (Simon Ch. 4, 3.1–3.4).  With
`g = Real.smoothTransition` and `ηⱼ(u) = g((j + 2)(1 − u))`, every `ηⱼ` is `C¹`, nonnegative and
nonincreasing, vanishes for `u ≥ 1`, and `ηⱼ(|x − z|²/s²)` increases to the indicator of the
open ball `B_s(z)`; by dominated convergence `∫ ηⱼ(|x − z|²/s²) dμ → μ(B_s(z))` whenever
`μ(B_s(z)) < ∞`. -/
theorem Submission.dsmc_em_cutoff_tendsto_ball : ∃ η : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (η j)) ∧ (∀ j u, 0 ≤ η j u) ∧ (∀ j u, deriv (η j) u ≤ 0) ∧ (∀ j u, 1 ≤ u → η j u = 0) ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (s : ℝ), 0 < s → μ (ball z s) < ∞ → Tendsto (fun j => ∫ x, η j (‖x - z‖ ^ 2 / s ^ 2) ∂μ) atTop (𝓝 (μ.real (ball z s))) := by
  -- Steps 1–5: `ηⱼ(u) = g((j + 2)(1 − u))` is `C¹`, `≥ 0`, antitone, and `0` for `u ≥ 1`.
  have hanti : ∀ j : ℕ, Antitone fun u : ℝ => Real.smoothTransition (((j : ℝ) + 2) * (1 - u)) := by
    intro j a b hab
    apply Real.smoothTransition.monotone
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    nlinarith
  have hzero : ∀ (j : ℕ) (u : ℝ), 1 ≤ u →
      Real.smoothTransition (((j : ℝ) + 2) * (1 - u)) = 0 := by
    intro j u hu
    apply Real.smoothTransition.zero_of_nonpos
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    nlinarith
  refine ⟨fun j u => Real.smoothTransition (((j : ℝ) + 2) * (1 - u)), fun j => ?_,
    fun j u => Real.smoothTransition.nonneg _, fun j u => (hanti j).deriv_nonpos, hzero, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
  -- Step 6: dominated convergence with the bound `1_{B_s(z)}`.
  intro P μ z s hs hμ
  have hs2 : 0 < s ^ 2 := by positivity
  -- `|x − z|²/s² < 1` exactly on the open ball
  have hlt : ∀ x : Euclid P, x ∈ ball z s → ‖x - z‖ ^ 2 / s ^ 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [div_lt_one hs2]
    exact pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero
  have hge : ∀ x : Euclid P, x ∉ ball z s → 1 ≤ ‖x - z‖ ^ 2 / s ^ 2 := by
    intro x hx
    rw [mem_ball, dist_eq_norm, not_lt] at hx
    rw [one_le_div hs2]
    exact pow_le_pow_left₀ hs.le hx 2
  have hint : Integrable ((ball z s).indicator (1 : Euclid P → ℝ)) μ :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
  rw [← integral_indicator_one measurableSet_ball]
  refine tendsto_integral_of_dominated_convergence ((ball z s).indicator 1)
    (F := fun (j : ℕ) (x : Euclid P) =>
      Real.smoothTransition (((j : ℝ) + 2) * (1 - ‖x - z‖ ^ 2 / s ^ 2)))
    (fun j => ?_) hint (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · -- (a) each integrand is continuous
    exact (Real.smoothTransition.continuous.comp (by fun_prop)).aestronglyMeasurable
  · -- (a) `|ηⱼ(u(x))| ≤ 1_{B_s(z)}(x)`
    by_cases hx : x ∈ ball z s
    · rw [indicator_of_mem hx, Pi.one_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rw [indicator_of_notMem hx, hzero j _ (hge x hx), norm_zero]
  · -- (b) pointwise convergence to `1_{B_s(z)}(x)`
    by_cases hx : x ∈ ball z s
    · rw [indicator_of_mem hx, Pi.one_apply]
      have hpos : 0 < 1 - ‖x - z‖ ^ 2 / s ^ 2 := sub_pos.2 (hlt x hx)
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / (1 - ‖x - z‖ ^ 2 / s ^ 2))
      rw [div_le_iff₀ hpos] at hN
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun j hj => ?_⟩)
      have hj : (N : ℝ) ≤ j := by exact_mod_cast hj
      refine (Real.smoothTransition.one_of_one_le ?_).symm
      nlinarith
    · rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun j => (hzero j _ (hge x hx)).symm

/-- **Monotonicity of `e^{κρ} ρ⁻ⁿ μ_R(B_ρ(z))` under bounded generalized mean curvature**
(Simon Ch. 4, 3.14–3.17).  If `δV(X) = -∫ X · H dμ_R` for `C¹` fields `X` supported in `B_r(z)`,
`B̄_r(z) ⊆ U` and `|H| ≤ κ`, then `e^{κs} s⁻ⁿ μ_R(B_s(z))` is nondecreasing on `(0, r]`.  For each
radial cutoff `ηⱼ`, `I(s) = ∫ ηⱼ(|x - z|²/s²) dμ_R` satisfies `n I - s I' ≤ κ s I` on `(0, r)`, so
`e^{κs} s⁻ⁿ I(s)` is nondecreasing; letting `j → ∞` gives `I(s) → μ_R(B_s(z))`. -/
theorem Submission.dsmc_exp_ball_mass_monotone : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ r → ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (ball z σ) ≤ ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n) * R.measure (ball z ρ) := by
  intro P n U R H κ z r hzU hPm _ hHκ hfv σ ρ hσ hσρ hρr
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- (a) `μ(B̄_r(z)) < ∞` (`R.locallyIntegrable_mult`), so `μ(B_t(z)) < ∞` for `t ≤ r`
  have hμB : R.measure (closedBall z r) < ∞ := by
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult _ (isCompact_closedBall z r) hzU)
  have hμt : ∀ t, t ≤ r → R.measure (ball z t) < ∞ := fun t ht =>
    (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall ht))).trans_lt hμB
  -- (b) for each cutoff `ηⱼ`, `e^{κs} s⁻ⁿ ∫ ηⱼ(|x - z|²/s²) dμ` is nondecreasing on `(0, r]`
  obtain ⟨η, hηC, hη0, hη'0, hη1, hlim⟩ := Submission.dsmc_em_cutoff_tendsto_ball
  have hj : ∀ j, Real.exp (κ * σ) / σ ^ n * ∫ x, η j (‖x - z‖ ^ 2 / σ ^ 2) ∂R.measure ≤
      Real.exp (κ * ρ) / ρ ^ n * ∫ x, η j (‖x - z‖ ^ 2 / ρ ^ 2) ∂R.measure := by
    intro j
    obtain ⟨hcont, hderiv⟩ := Submission.dsmc_em_cutoff_integral_hasDerivAt P R.measure z r (η j)
      (hμt r le_rfl) (hηC j) (hη1 j)
    refine Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq n κ r _ _ hcont hderiv (fun s hs => ?_)
      ⟨hσ, hσρ.trans hρr⟩ ⟨hρ, hρr⟩ hσρ
    -- `n I(s) - s I'(s) = n I(s) + ∫ 2 u η'(u) dμ ≤ κ s I(s)`
    have h := Submission.dsmc_em_cutoff_first_variation_le P n U R H κ z r (η j) hzU hPm hHκ hfv
      (hηC j) (hη0 j) (hη'0 j) (hη1 j) s hs.1 hs.2
    rw [mul_div_cancel₀ _ hs.1.ne', sub_neg_eq_add]
    exact h
  -- (c) let `j → ∞`: the integrals tend to `μ(B_σ(z))` and `μ(B_ρ(z))`
  have hreal : Real.exp (κ * σ) / σ ^ n * R.measure.real (ball z σ) ≤
      Real.exp (κ * ρ) / ρ ^ n * R.measure.real (ball z ρ) :=
    le_of_tendsto_of_tendsto'
      ((hlim P R.measure z σ hσ (hμt σ (hσρ.trans hρr))).const_mul _)
      ((hlim P R.measure z ρ hρ (hμt ρ hρr)).const_mul _) hj
  -- (d) transfer to `[0, ∞]`
  rw [← ofReal_measureReal (hμt σ (hσρ.trans hρr)).ne, ← ofReal_measureReal (hμt ρ hρr).ne,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Simon Ch. 4, 2.2 and 4.1.1**: for `R = (M, θ, ξ)` and `X ∈ C¹_c(U; ℝᴾ)` with `x ↦ p_{TₓM}`
`μ_R`-measurable, `div_M X` is `μ_R`-integrable and `δV(X) = ∫_M θ div_M X dHⁿ = ∫ div_M X dμ_R`,
`μ_R = θ Hⁿ⌞M`.  `div_M X(x) = tr(p_{TₓM} ∘ DX(x))` is bounded by `‖tr‖ ‖DX(x)‖`, and it vanishes
off the compact `spt X ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dsmc_firstVariation_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure ∧ R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
  intro P n U R X hX hcpt hU hp
  -- the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and `div_M X(x) = tr(p_x ∘ DX(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ x, tangentialDivergence n R.carrier X x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ X x) := fun x => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hD : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- `div_M X` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
      (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp.aestronglyMeasurable
      hD.aestronglyMeasurable
  -- `|div_M X(x)| ≤ ‖tr‖ C 1_K(x)`, `K = spt X`, `C = sup ‖DX‖`
  obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hcpt.fderiv ℝ)
  have hKm : MeasurableSet (tsupport X) := (isClosed_tsupport X).measurableSet
  have hbound : ∀ x, ‖tangentialDivergence n R.carrier X x‖ ≤
      (tsupport X).indicator (fun _ => ‖tr‖ * C) x := by
    intro x
    rw [hdiv]
    by_cases hxK : x ∈ tsupport X
    · rw [Set.indicator_of_mem hxK]
      refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _) zero_le_one
    · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
        ContinuousLinearMap.comp_zero, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport X) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport X) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.firstVariation]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
/-- **Simon Ch. 4, 3.14–3.15**: if `V = v(M, θ)` has generalized mean curvature `H₀` in `U`,
bounded `μ_V`-a.e. on compact subsets, then for a compact `K ⊆ U` there are `Λ ≥ 0` and a
`μ_V`-measurable `H` with `|H| ≤ Λ` everywhere and `δV(X) = −∫ X · H dμ_V` for every `C¹` field `X`
with compact support in `K`.  Take a strongly measurable version `H₁` of `H₀` and set
`H = 1_{|H₁| ≤ Λ} H₁` with `Λ = max(Λ_K, 0)`: then `H = H₀` `μ_V`-a.e. on `K`, and `X = 0` off
`K`, so `X · H = X · H₀` `μ_V`-a.e. -/
theorem Submission.dimred_mono_truncated_mean_curvature : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), R.HasLocallyBoundedMeanCurvature → ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧ (∀ x, ‖H x‖ ≤ Λ) ∧ ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ K → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure := by
  intro P n U R hR K hK hKU
  obtain ⟨H₀, hH₀m, hH₀b, hH₀fv⟩ := hR
  obtain ⟨Λ₀, hΛ₀⟩ := hH₀b K hK hKU
  -- `H₁` is a strongly measurable version of `H₀`; `S = {|H₁| ≤ Λ}` is measurable
  obtain ⟨H₁, hH₁, hH₀₁⟩ : ∃ H₁ : Euclid P → Euclid P, StronglyMeasurable H₁ ∧
      H₀ =ᵐ[R.measure] H₁ :=
    ⟨hH₀m.mk H₀, hH₀m.stronglyMeasurable_mk, hH₀m.ae_eq_mk⟩
  set S : Set (Euclid P) := {x | ‖H₁ x‖ ≤ max Λ₀ 0}
  have hS : MeasurableSet S := measurableSet_le hH₁.norm.measurable measurable_const
  refine ⟨max Λ₀ 0, le_max_right _ _, S.indicator H₁, (hH₁.indicator hS).aestronglyMeasurable,
    fun x => ?_, fun X hX hXc hXK => ?_⟩
  · by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
      exact hx
    · rw [Set.indicator_of_notMem hx, norm_zero]
      exact le_max_right _ _
  -- `X · H₀ = X · H` `μ_V`-a.e.: on `K`, `H = H₁ = H₀` a.e.; off `K`, `X = 0`
  rw [hH₀fv X hX hXc (hXK.trans hKU)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hH₀₁, hΛ₀] with x hx₁ hx₂
  by_cases hxK : x ∈ K
  · have hxS : x ∈ S := by
      change ‖H₁ x‖ ≤ max Λ₀ 0
      rw [← hx₁]
      exact (hx₂ hxK).trans (le_max_left _ _)
    rw [Set.indicator_of_mem hxS, hx₁]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hxK (hXK h), inner_zero_left, inner_zero_left]
/-- **Simon Ch. 4, 3.8–3.11 and the remark after 3.17**: let `U` be open, let every `y ∈ U` be
the centre of a ball of finite mass, and let every compact `K ⊆ U` have `Λ ≥ 0` such that
`ρ ↦ e^{Λρ}ρ⁻ⁿ M_{B_ρ(y)}(T)` is nondecreasing on `(0, R)` whenever `B̄_R(y) ⊆ K`.  Then `T` has a
density `Θ(y)` at every `y ∈ U`, and `Θ` is upper semicontinuous on `U`.
The monotone quantity has a finite limit as `ρ ↓ 0`; multiplying by `e^{-Λρ} → 1` gives the
density.  Monotonicity at a centre `z` bounds `ωₙΘ(z)` by `e^{Λρ}ρ⁻ⁿ M_{B_ρ(z)}(T)` for every
smaller radius `ρ`.  For `|z - y| < δρ`, `B_ρ(z) ⊆ B_{(1+δ)ρ}(y)`, and the density at `y` gives
`Θ(z) < e^δ(1 + δ)ⁿ(Θ(y) + δ)` for small `ρ`. -/
theorem Submission.dimred_mono_density_usc_of_monotone : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ T.massOn (ball y r) ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) → ∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U := by
  intro P n U T hU hfin hmono
  -- `0 < ωₙ < ∞`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ :=
    (measure_ball_lt_top (μ := volume) (x := (0 : Euclid n)) (r := 1)).ne
  -- (1) the density exists at every `y ∈ U` (Simon Ch. 4, 3.8–3.10)
  have hex : ∀ y : Euclid P, ∃ θ : ℝ, y ∈ U → HasMassDensity T y θ := by
    intro y
    by_cases hy : y ∈ U
    swap
    · exact ⟨0, fun h => absurd h hy⟩
    obtain ⟨r₀, hr₀, hr₀fin⟩ := hfin y hy
    obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU y hy
    have hRpos : 0 < min r₀ (r₁ / 2) := lt_min hr₀ (half_pos hr₁)
    have hKU : closedBall y (min r₀ (r₁ / 2)) ⊆ U :=
      (closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hr₁))).trans hr₁U
    obtain ⟨Λ, -, hΛ⟩ := hmono _ (isCompact_closedBall y _) hKU
    -- the monotone function `g` tends to its infimum `L < ∞` as `ρ ↓ 0`
    obtain ⟨L, hlim, hLtop⟩ : ∃ L : ℝ≥0∞, Tendsto (fun ρ : ℝ => ENNReal.ofReal
        (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (𝓝[>] 0) (𝓝 L) ∧ L ≠ ∞ := by
      refine ⟨_, (hΛ y _ subset_rfl).tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hRpos)
        (OrderBot.bddBelow _), ne_top_of_le_ne_top ?_
        (sInf_le (mem_image_of_mem _ ⟨half_pos hRpos, half_lt_self hRpos⟩))⟩
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top hr₀fin
        (T.massOn_mono (ball_subset_ball ((half_le_self hRpos.le).trans (min_le_left _ _)))))
    -- multiply by `e^{-Λρ} → 1` and divide by `ωₙ`
    have hexp : Tendsto (fun ρ : ℝ => ENNReal.ofReal (Real.exp (-(Λ * ρ)))) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun ρ : ℝ => Real.exp (-(Λ * ρ))) (𝓝 0) (𝓝 1) :=
        (by fun_prop : Continuous fun ρ : ℝ => Real.exp (-(Λ * ρ))).tendsto' 0 1 (by simp)
      simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
    have hdiv := ENNReal.Tendsto.div_const
      (ENNReal.Tendsto.mul hexp (Or.inl one_ne_zero) hlim (Or.inr ENNReal.one_ne_top))
      (Or.inr hω0)
    rw [one_mul] at hdiv
    refine ⟨(L / unitBallVolume n).toReal, fun _ => ⟨ENNReal.toReal_nonneg, ?_⟩⟩
    rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hLtop hω0)]
    refine hdiv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    have h1 : Real.exp (-(Λ * ρ)) * (Real.exp (Λ * ρ) / ρ ^ n) = (ρ ^ n)⁻¹ := by
      rw [mul_div_assoc', ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_div]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, h1,
      ENNReal.ofReal_inv_of_pos (pow_pos hρ n), div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop)]
    ring
  choose Θ hΘ using hex
  -- (2) comparison with a fixed radius: `ωₙ Θ(z) ≤ e^{Λρ} ρ⁻ⁿ M_{B_ρ(z)}(T)`
  have hcomp : ∀ (Λ : ℝ) (z : Euclid P) (R : ℝ), 0 ≤ Λ → z ∈ U →
      MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball z ρ))
        (Ioo 0 R) → ∀ ρ ∈ Ioo 0 R, unitBallVolume n * ENNReal.ofReal (Θ z) ≤
          ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball z ρ) := by
    intro Λ z R hΛ hz hg ρ hρ
    refine le_of_tendsto (ENNReal.Tendsto.const_mul (hΘ z hz).2 (Or.inr hωtop)) ?_
    filter_upwards [Ioo_mem_nhdsGT hρ.1] with t ht
    calc unitBallVolume n * (T.massOn (ball z t) / (unitBallVolume n * ENNReal.ofReal (t ^ n)))
        = ENNReal.ofReal (t ^ n)⁻¹ * T.massOn (ball z t) := by
          rw [← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hω0 hωtop, ENNReal.div_eq_inv_mul,
            ENNReal.ofReal_inv_of_pos (pow_pos ht.1 n)]
      _ ≤ ENNReal.ofReal (Real.exp (Λ * t) / t ^ n) * T.massOn (ball z t) := by
          gcongr
          rw [div_eq_mul_inv]
          exact le_mul_of_one_le_left (inv_nonneg.2 (pow_nonneg ht.1.le n))
            (Real.one_le_exp (mul_nonneg hΛ ht.1.le))
      _ ≤ ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball z ρ) :=
          hg ⟨ht.1, ht.2.trans hρ.2⟩ hρ ht.2.le
  -- (3) upper semicontinuity (Simon Ch. 4, 3.11)
  refine ⟨Θ, hΘ, upperSemicontinuousOn_iff.2 fun y hy =>
    upperSemicontinuousWithinAt_iff.2 fun c hc => ?_⟩
  have hΘy := hΘ y hy
  have hc0 : 0 < c := hΘy.1.trans_lt hc
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hy
  have hKU : closedBall y (2 * (r / 3)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  obtain ⟨Λ, hΛ0, hΛ⟩ := hmono _ (isCompact_closedBall y _) hKU
  -- choose `δ > 0` with `e^δ (1 + δ)ⁿ (Θ(y) + δ) < c`
  obtain ⟨δ, hδc, hδ⟩ : ∃ δ : ℝ, Real.exp δ * (1 + δ) ^ n * (Θ y + δ) < c ∧ 0 < δ := by
    have hcont : Continuous fun δ : ℝ => Real.exp δ * (1 + δ) ^ n * (Θ y + δ) := by fun_prop
    have h0 : (fun δ : ℝ => Real.exp δ * (1 + δ) ^ n * (Θ y + δ)) 0 < c := by simpa using hc
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Real.exp δ * (1 + δ) ^ n * (Θ y + δ) < c :=
      ((hcont.tendsto 0).eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
    exact (hev.and eventually_mem_nhdsWithin).exists
  -- choose `ρ > 0` with `(1 + δ)ρ` below the density scale at `y` and `r / 3`, and `Λρ < δ`
  have hscale : Tendsto (fun ρ : ℝ => (1 + δ) * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((by fun_prop : Continuous fun ρ : ℝ => (1 + δ) * ρ).tendsto' 0 0
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      exact mul_pos (by linarith) hρ
  have hΛlim : Tendsto (fun ρ : ℝ => Λ * ρ) (𝓝[>] 0) (𝓝 0) :=
    ((by fun_prop : Continuous fun ρ : ℝ => Λ * ρ).tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hlt : ENNReal.ofReal (Θ y) < ENNReal.ofReal (Θ y + δ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith [hΘy.1])).2 (by linarith)
  obtain ⟨ρ, ⟨hρF, hρR⟩, hρΛ, hρ⟩ := (((hscale.eventually (hΘy.2.eventually
    (gt_mem_nhds hlt))).and ((hscale.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < r / 3)))).and ((hΛlim.eventually
        (gt_mem_nhds hδ)).and eventually_mem_nhdsWithin)).exists
  have hρ : 0 < ρ := hρ
  have hρF : T.massOn (ball y ((1 + δ) * ρ)) /
      (unitBallVolume n * ENNReal.ofReal (((1 + δ) * ρ) ^ n)) < ENNReal.ofReal (Θ y + δ) := hρF
  have hρR' : ρ < r / 3 := by nlinarith
  -- every `z ∈ B_{δρ}(y)` has `Θ(z) < c`
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (mul_pos hδ hρ))] with z hz
  have hzy : dist z y < δ * ρ := hz
  have hzU : z ∈ U := hrU (mem_ball.2 (by nlinarith))
  have hρz := hcomp Λ z (r / 3) hΛ0 hzU
    (hΛ z (r / 3) (closedBall_subset_closedBall' (by nlinarith))) ρ ⟨hρ, hρR'⟩
  have hD0 : unitBallVolume n * ENNReal.ofReal (((1 + δ) * ρ) ^ n) ≠ 0 :=
    mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos (mul_pos (by linarith) hρ) n)).ne'
  have hDtop : unitBallVolume n * ENNReal.ofReal (((1 + δ) * ρ) ^ n) ≠ ∞ :=
    ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hmass := (ENNReal.div_lt_iff (Or.inl hD0) (Or.inl hDtop)).1 hρF
  have hA0 : ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (div_pos (Real.exp_pos _) (pow_pos hρ n))).ne'
  have hkey : unitBallVolume n * ENNReal.ofReal (Θ z) < unitBallVolume n * ENNReal.ofReal c := by
    calc unitBallVolume n * ENNReal.ofReal (Θ z)
        ≤ ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball z ρ) := hρz
      _ ≤ ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ((1 + δ) * ρ)) := by
          gcongr
          exact T.massOn_mono (ball_subset_ball' (by nlinarith))
      _ < ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * (ENNReal.ofReal (Θ y + δ) *
            (unitBallVolume n * ENNReal.ofReal (((1 + δ) * ρ) ^ n))) :=
          ENNReal.mul_lt_mul_right hA0 ENNReal.ofReal_ne_top hmass
      _ = unitBallVolume n * ENNReal.ofReal (Real.exp (Λ * ρ) * (1 + δ) ^ n * (Θ y + δ)) := by
          have hX : Real.exp (Λ * ρ) * (1 + δ) ^ n * (Θ y + δ) =
              Real.exp (Λ * ρ) / ρ ^ n * ((Θ y + δ) * ((1 + δ) * ρ) ^ n) := by
            rw [mul_pow, div_mul_eq_mul_div, eq_div_iff (pow_pos hρ n).ne']
            ring
          rw [hX, ENNReal.ofReal_mul (div_pos (Real.exp_pos _) (pow_pos hρ n)).le,
            ENNReal.ofReal_mul (by linarith [hΘy.1] : (0 : ℝ) ≤ Θ y + δ)]
          ring
      _ < unitBallVolume n * ENNReal.ofReal c := by
          refine ENNReal.mul_lt_mul_right hω0 hωtop
            ((ENNReal.ofReal_lt_ofReal_iff hc0).2 (lt_of_le_of_lt ?_ hδc))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 hρΛ.le) (pow_nonneg (by linarith) n)) (by linarith [hΘy.1])
  exact (ENNReal.ofReal_lt_ofReal_iff hc0).1 ((ENNReal.mul_lt_mul_iff_right hω0 hωtop).1 hkey)
/-- An approximate tangent plane forces unit `Hⁿ`-density on closed balls (Simon Ch. 3,
Remark 1.5(3), with Definition 1.4).  If `Hⁿ(M ∩ B̄_s(x)) < ∞` and `Q` is an approximate tangent
space of `M` at `x`, then `Hⁿ(M ∩ B̄_ρ(x)) / (ωₙρⁿ) → 1` as `ρ ↓ 0`.  Since
`Hⁿ(η_{x,r}(M) ∩ B̄_1(0)) = r⁻ⁿHⁿ(M ∩ B̄_r(x))` and `Hⁿ(Q ∩ B̄_t(0)) = ωₙtⁿ`, the radial cut-offs
`g_{1-ε,1} ≤ 1_{B̄_1(0)} ≤ g_{1,1+ε}` in `C_c` squeeze `r⁻ⁿHⁿ(M ∩ B̄_r(x))` between blow-up integrals
whose limits lie within `ωₙ(1 ∓ ε)ⁿ`. -/
theorem Submission.rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M x Q s hs hfin hT
  obtain ⟨hQ, hconv⟩ := hT
  -- Step 1: `ωₙ ∈ (0, ∞)`
  set ω := unitBallVolume n with hωdef
  have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set w := ω.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
  -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`, via a linear isometry `ℝⁿ ≅ Q`
  have hplane0 : ∀ t : ℝ, 0 ≤ t →
      μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(b.repr.symm v).2, ?_⟩
        rw [mem_closedBall, dist_zero_right] at hv ⊢
        have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
        simpa [ι, this] using hv
      · rintro ⟨hyQ, hy⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right] at hy ⊢
          simpa using hy
        · simp [ι]
    rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
  -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
    intro r hr A
    have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A =
        (fun y => r⁻¹ • y) '' ((fun y => y - x) '' A) := by
      rw [image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) :=
      Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
    rw [h1, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [abs_of_pos hr]
  have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
    intro r hr t
    have key : ∀ z : Euclid P,
        ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
      intro z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, dist_eq_norm]
      rw [inv_mul_le_iff₀ hr, mul_comm r t]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      rw [mem_closedBall, dist_zero_right, key] at hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_zero_right, key]
      exact hzb
  have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
        ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
    intro r hr t
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
  have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
  have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
    intro r hr t ht
    rw [hνball r hr t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
  -- Step 4: radial cut-off functions `g_{a,b}` in `C_c`
  have hbump : ∀ a b : ℝ, 0 < a → a < b →
      ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Continuous f ∧ (0 ≤ ⇑f) ∧
        (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
    intro a b ha hab
    have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
      continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
    have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
      intro y hy
      have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [max_eq_left ((min_le_right _ _).trans h1)]
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
        continuous_toFun := hcont
        hasCompactSupport' := by
          refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
          intro y hy
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hzero y hy.le }
    have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
    refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) a
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        rw [mem_closedBall, dist_zero_right] at hy
        have : 1 ≤ (b - ‖y‖) / (b - a) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) b
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        exact max_le zero_le_one (min_le_left _ _)
      · rw [indicator_of_notMem hy, hf, hzero]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le
  -- Step 5: integrability of functions dominated by the indicator of a finite-measure closed ball
  have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
      Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h)
  have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
      ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
      Integrable f ν := by
    intro ν f t hf hfin' h0 hle
    refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y
  -- Step 6: the normalised mass `a(r) = r⁻ⁿ Hⁿ(M ∩ B̄_r(x))` and the plane-ball values
  set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
  have hareal : ∀ r : ℝ, 0 < r →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
    intro r hr
    rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hplane : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
  have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
    intro t ht
    rw [hplane t ht]
    exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hplanereal : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
    intro t ht
    rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step 7: `a r → ωₙ`
  have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
      -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
      have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
        rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
          (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
      filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `∫_{η(M)} f ≤ a r`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
          (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
      exact hr1.trans_le hle
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
      -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
      have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
        rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
          (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
      filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `a r ≤ ∫_{η(M)} f`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have h2 : (1 + ε) * r ≤ s := by nlinarith [hr2.1, hr2.2, hε.2]
      have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
          (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
      exact hge.trans_lt hr1
  -- Step 8: back to the `ℝ≥0∞` quotient
  have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
    intro ρ hρ hρs
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
    congr 1
    simp only [hadef, inv_pow]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (ha.div_const w)
    rwa [div_self hw.ne', ENNReal.ofReal_one] at this
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
  exact (hconvert ρ hρ.1 hρ.2).symm
/-- **Simon Ch. 1, 3.1–3.2** (densities may be computed with closed or open balls; cf. 6.2.8 and
`HasMassDensity`): if `ν(B̄_ρ(x)) / (ωₙρⁿ) → θ ∈ [0, ∞]` as `ρ ↓ 0`, then also
`ν(B_ρ(x)) / (ωₙρⁿ) → θ`.  The upper bound follows from `B_ρ(x) ⊆ B̄_ρ(x)`.  For the lower
bound, given `a < θ` pick `t ∈ (0, 1)` with `a < tⁿθ`; then `B̄_{tρ}(x) ⊆ B_ρ(x)` and
`ωₙ(tρ)ⁿ = tⁿ ωₙρⁿ` give `ν(B_ρ(x)) / (ωₙρⁿ) ≥ tⁿ · ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) > a` for small
`ρ`. -/
theorem Submission.rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
  intro P n ν x θ hg
  set ω := unitBallVolume n
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Step 2: choose `t ∈ (0, 1)` with `a < tⁿθ`, using `tⁿθ → θ` as `t ↑ 1`
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
        (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [one_mul] at hlim
    obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
      have h1 := (tendsto_order.1 hlim).1 a ha
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
      exact ⟨t, ht, ht'.1, ht'.2⟩
    have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]
      exact hta
    -- Step 3: the rescaled closed-ball ratio `g(tρ)` still tends to `θ`
    have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact mul_pos ht0 hρ
    have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
    filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
    simp only [Function.comp] at hρ
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- Step 4: `ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) · tⁿ = ν(B̄_{tρ}(x)) / (ωₙρⁿ)`
    have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
        = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
        ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
        mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    -- Step 5: `a < tⁿ g(tρ) ≤ h(ρ)`, as `B̄_{tρ}(x) ⊆ B_ρ(x)`
    calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.div_mul_cancel hc0 hctop).symm
      _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
      _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
      _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
          exact closedBall_subset_ball (by nlinarith)
  · -- Step 1: `h(ρ) ≤ g(ρ)`, as `B_ρ(x) ⊆ B̄_ρ(x)`
    filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
    refine lt_of_le_of_lt ?_ hρ
    gcongr
    exact ball_subset_closedBall

/-- **Simon Ch. 4, 3.11–3.13** (with Ch. 3, Remark 1.5(3)): the weight `μ = θHⁿ⌞M` of an integer
multiplicity triple `(M, θ, ξ)` in an open `U` has density `≥ 1` at `μ`-a.e. `x`: every limit `θ₀`
of `μ(B_ρ(x)) / (ωₙρⁿ)` as `ρ ↓ 0` satisfies `θ₀ ≥ 1`.  Since `μ ≪ ν = Hⁿ⌞M`, it suffices to take
`ν`-a.e. `x`; such `x` lie in `M` and have an approximate tangent plane.  With `B̄_s(x) ⊆ U`,
`Hⁿ(M ∩ B̄_s(x)) ≤ ∫_{M ∩ B̄_s(x)} θ dHⁿ < ∞`, so `ν(B_ρ(x)) / (ωₙρⁿ) → 1`; and `θ ≥ 1` on `M`
gives `ν ≤ μ`, hence `1 ≤ θ₀`. -/
theorem Submission.dimred_mono_ae_ball_density_ge_one : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → ∀ᵐ x ∂R.measure, ∀ θ : ℝ, Tendsto (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → 1 ≤ θ := by
  intro P n U R hU
  -- Step 1: `μ ≪ ν`, where `ν = Hⁿ⌞M`
  set ν : Measure (Euclid P) := μHE[n].restrict R.carrier with hνdef
  have hac : R.measure ≪ ν := withDensity_absolutelyContinuous _ _
  -- Step 3: `θ ≥ 1` `ν`-a.e., hence `ν ≤ μ`
  have hmem : ∀ᵐ y ∂ν, y ∈ R.carrier := ae_restrict_mem R.measurableSet_carrier
  have hle : ν ≤ R.measure :=
    calc ν = ν.withDensity 1 := withDensity_one.symm
      _ ≤ R.measure := withDensity_mono (hmem.mono fun y hy => Nat.one_le_cast.2 (R.mult_pos y hy))
  -- Step 2: `ν`-a.e. `x` lies in `M` and has an approximate tangent plane `Q`
  refine hac.ae_le ?_
  filter_upwards [hmem, R.orients] with x hxM hxQ
  obtain ⟨Q, hQ, -⟩ := hxQ
  intro θ hθ
  -- Step 4: `Hⁿ(M ∩ B̄_s(x)) < ∞` for some `s > 0` with `B̄_s(x) ⊆ U`
  obtain ⟨s, hs, hsU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (R.carrier_subset hxM))
  have hfin : μHE[n] (R.carrier ∩ closedBall x s) ≠ ∞ := by
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult _ (isCompact_closedBall x s) hsU) ?_
    calc μHE[n] (R.carrier ∩ closedBall x s) = ∫⁻ _ in R.carrier ∩ closedBall x s, 1 ∂μHE[n] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ y in R.carrier ∩ closedBall x s, (R.mult y : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun y hy =>
            Nat.one_le_cast.2 (R.mult_pos y hy.1)
  -- Step 5: `ν(B_ρ(x)) / (ωₙρⁿ) → 1`
  have hνclosed : Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
      (𝓝[>] 0) (𝓝 1) := by
    refine (Submission.rsd_tendsto_closedBall_density_of_approxTangent P n R.carrier x Q s hs hfin
      hQ).congr fun ρ => ?_
    rw [hνdef, Measure.restrict_apply measurableSet_closedBall, inter_comm]
  have hνball := Submission.rsd_tendsto_ball_density_of_closedBall P n ν x 1 hνclosed
  -- Step 6: `ν ≤ μ` on balls gives `1 ≤ ofReal θ`
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal θ :=
    le_of_tendsto_of_tendsto' hνball hθ fun ρ => ENNReal.div_le_div_right (hle _) _
  exact ENNReal.one_le_ofReal.1 h1
/-- **Simon Ch. 4, 3.13 and the remark after it**: let `M_W(T) = μ(W)` for open `W ⊆ U`, let
`μ(B_ε(x)) ≠ 0` for `x ∈ spt T` and `ε > 0`, and let every existing density
`lim_{ρ ↓ 0} μ(B_ρ(x))/(ωₙρⁿ)` be `≥ 1` for `μ`-a.e. `x`.  If `Θ` is an upper semicontinuous
density of `T` on the open set `U`, then every density of `T` at a point `y ∈ spt T` is `≥ 1`.
Such a density equals `Θ(y)`.  If `Θ(y) < 1`, then `Θ < 1` on a ball `B_ε(y) ⊆ U`.  On this ball
the mass ratios equal the `μ`-ratios for small radii, so no point of `B_ε(y)` has the a.e.
property.  Hence `μ(B_ε(y)) = 0`, contradicting `y ∈ spt T`. -/
theorem Submission.dimred_mono_support_density_ge_one_of_usc : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (Θ : Euclid P → ℝ), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = μ W) → (∀ x ∈ T.support, ∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0) → (∀ᵐ x ∂μ, ∀ θ : ℝ, Tendsto (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → 1 ≤ θ) → (∀ y ∈ U, HasMassDensity T y (Θ y)) → UpperSemicontinuousOn Θ U → ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ := by
  intro P n U T μ Θ hU hmass hpos hae hΘ husc y hy θ hθ
  have hyU : y ∈ U := T.support_subset_domain hy
  -- `θ = Θ(y)`: both are nonnegative limits of the same ratio in `[0, ∞]`
  rw [(ENNReal.ofReal_eq_ofReal_iff hθ.1 (hΘ y hyU).1).1 (tendsto_nhds_unique hθ.2 (hΘ y hyU).2)]
  by_contra! hlt
  -- if `Θ(y) < 1`, then `Θ < 1` on a ball `B_ε(y) ⊆ U`
  have hlt' : ∀ᶠ z in 𝓝[U] y, Θ z < 1 := husc y hyU 1 hlt
  rw [hU.nhdsWithin_eq hyU] at hlt'
  obtain ⟨ε, hε, hball⟩ := eventually_nhds_iff_ball.1 (hlt'.and (hU.eventually_mem hyU))
  -- no point of `B_ε(y)` has the a.e. property, so `μ(B_ε(y)) = 0`, contradicting `y ∈ spt T`
  refine hpos y hy ε hε (measure_mono_null ?_ (ae_iff.1 hae))
  intro z hz hgood
  obtain ⟨hzΘ, hzU⟩ := hball z hz
  -- for `0 < ρ < ε - |z - y|`, `B_ρ(z) ⊆ B_ε(y) ⊆ U`, so `M_{B_ρ(z)}(T) = μ(B_ρ(z))`
  have hρ : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < ε - dist z y :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (sub_pos.2 (mem_ball.1 hz)))
  refine hzΘ.not_ge (hgood (Θ z) ((hΘ z hzU).2.congr' (hρ.mono fun ρ hρ => ?_)))
  dsimp only
  rw [hmass (ball z ρ) isOpen_ball fun w hw => (hball w (ball_subset_ball' (by linarith) hw)).2]
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
