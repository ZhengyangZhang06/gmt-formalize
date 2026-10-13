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

/-- An embedded `Cʳ` submanifold `M ⊆ ℝᴾ` (Simon Ch. 2, §4, (4.1)) is Borel, and it meets every
small closed ball about one of its points in a compact set.  For a chart `(V, W, ψ)` and a compact
`K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact because `ψ` is proper and continuous on `V`.  With `O`
the union of the chart domains `W`, `M = O ∩ closure M`: a point `p ∈ O ∩ closure M` lies in the
closure of the compact, hence closed, set `M ∩ closedBall p ε`.  So `M` is Borel. -/
theorem Submission.dimred_rpd_embedded_locally_closed : ∀ (P r d : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → MeasurableSet M ∧ ∀ y ∈ M, ∃ ε : ℝ, 0 < ε ∧ IsCompact (M ∩ closedBall y ε) := by
  intro P r d M hM
  -- step 1: for a chart `(V, W, ψ)` at `y` and compact `K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact
  have key : ∀ y ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧
      ∀ K ⊆ W, IsCompact K → IsCompact (M ∩ K) := by
    intro y hy
    obtain ⟨V, W, ψ, -, hW, hyW, hψ, -, himg, hprop, -⟩ := hM y hy
    refine ⟨W, hW, hyW, fun K hKW hK => ?_⟩
    have hEq : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
      ext x
      constructor
      · rintro ⟨hxM, hxK⟩
        have hx : x ∈ ψ '' V := by rw [himg]; exact ⟨hKW hxK, hxM⟩
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨v, ⟨hv, hxK⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
        have hv' : ψ v ∈ W ∩ M := by rw [← himg]; exact ⟨v, hv, rfl⟩
        exact ⟨hv'.2, hvK⟩
    rw [hEq]
    exact (hprop K hKW hK).image_of_continuousOn (hψ.continuousOn.mono inter_subset_left)
  refine ⟨?_, ?_⟩
  · -- steps 3-5: `O = ⋃_{y ∈ M} W_y` is open and `M = O ∩ closure M`, so `M` is Borel
    choose! Wf hWo hyW hcpt using key
    have hO : IsOpen (⋃ y ∈ M, Wf y) := isOpen_biUnion fun y hy => hWo y hy
    have hMeq : M = (⋃ y ∈ M, Wf y) ∩ closure M := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩
      · -- `p ∈ O ∩ closure M` lies in the closure of the compact set `M ∩ closedBall p (r'/2)`
        rintro p ⟨hpO, hpcl⟩
        obtain ⟨y, hy, hpW⟩ := mem_iUnion₂.1 hpO
        obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 (hWo y hy) p hpW
        have hcb : closedBall p (r' / 2) ⊆ Wf y :=
          (closedBall_subset_ball (by linarith)).trans hball
        have hC := hcpt y hy (closedBall p (r' / 2)) hcb (isCompact_closedBall p (r' / 2))
        have h1 : p ∈ ball p (r' / 2) ∩ closure M := ⟨mem_ball_self (by linarith), hpcl⟩
        have h2 := isOpen_ball.inter_closure h1
        have hsub : ball p (r' / 2) ∩ M ⊆ M ∩ closedBall p (r' / 2) :=
          fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
        have h3 : p ∈ closure (M ∩ closedBall p (r' / 2)) := closure_mono hsub h2
        rw [hC.isClosed.closure_eq] at h3
        exact h3.1
    rw [hMeq]
    exact hO.measurableSet.inter isClosed_closure.measurableSet
  · -- step 2: a closed ball about `y` inside the chart domain `W` meets `M` in a compact set
    intro y hy
    obtain ⟨W, hW, hyW, hcpt⟩ := key y hy
    obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 hW y hyW
    exact ⟨r' / 2, by linarith,
      hcpt _ ((closedBall_subset_ball (by linarith)).trans hball) (isCompact_closedBall y _)⟩
/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))

/-- Near-isometric local parametrizations of an embedded `C¹` submanifold `M` (charts as in
Simon Ch. 2, (4.1)): for `z ∈ M` and `ε > 0` there are `χ` with `χ(0) = z` and `δ, δ' > 0` such
that `χ` is `(1 ± ε)`-bi-Lipschitz on `B_δ(0)`, `χ(B_δ(0)) ⊆ M` and `M ∩ B_{δ'}(z) ⊆ χ(B_δ(0))`.
Take a chart `ψ` with `ψ(v₀) = z`, choose `L ∈ GL(ℝⁿ)` with `Dψ(v₀) ∘ L` a linear isometry (an
orthonormal basis of `Dψ(v₀)(ℝⁿ)`) and put `χ(w) = ψ(v₀ + Lw)`; strict differentiability of `χ`
at `0` gives the two-point bounds, and continuity of the chart inverse
(`Submission.dsmc_chart_inverse_continuity`) gives the covering of `M ∩ B_{δ'}(z)`. -/
theorem Submission.dimred_rpd_near_isometric_chart : ∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → ∀ ε : ℝ, 0 < ε → ∃ (χ : Euclid n → Euclid P) (δ δ' : ℝ), 0 < δ ∧ 0 < δ' ∧ χ 0 = z ∧ (∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ, (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖) ∧ χ '' ball 0 δ ⊆ M ∧ M ∩ ball z δ' ⊆ χ '' ball 0 δ := by
  intro P n M z hM hz ε hε
  obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, hprop, hder⟩ := hM z hz
  obtain ⟨v₀, hv₀V, hψv₀⟩ : z ∈ ψ '' V := by rw [himg]; exact ⟨hzW, hz⟩
  set A : Euclid n →L[ℝ] Euclid P := fderiv ℝ ψ v₀
  have hA : Injective A := hder v₀ hv₀V
  have hstrict : HasStrictFDerivAt ψ A v₀ :=
    (hψ.contDiffAt (hV.mem_nhds hv₀V)).hasStrictFDerivAt one_ne_zero
  -- isometric normalization
  obtain ⟨L, hLJ⟩ : ∃ L : Euclid n ≃L[ℝ] Euclid n, ∀ w, ‖A (L w)‖ = ‖w‖ := by
    let Q := LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P)
    have hfin : Module.finrank ℝ Q = n := by
      rw [LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace_fin]
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hfin)
    let A' : Euclid n ≃ₗ[ℝ] Q := LinearEquiv.ofInjective (A : Euclid n →ₗ[ℝ] Euclid P) hA
    let L₀ : Euclid n ≃ₗ[ℝ] Euclid n := b.repr.symm.toLinearEquiv.trans A'.symm
    refine ⟨L₀.toContinuousLinearEquiv, fun w => ?_⟩
    have h1 : A' (L₀ w) = b.repr.symm w := by simp [L₀]
    have h2 : A (L₀ w) = ((A' (L₀ w) : Q) : Euclid P) := rfl
    change ‖A (L₀ w)‖ = ‖w‖
    rw [h2, h1]
    exact b.repr.symm.norm_map w
  set χ : Euclid n → Euclid P := fun w => ψ (v₀ + L w)
  have hχ0 : χ 0 = z := by simp [χ, hψv₀]
  have hχstrict : HasStrictFDerivAt χ (A.comp (L : Euclid n →L[ℝ] Euclid n)) 0 := by
    have h1 : HasStrictFDerivAt (fun w : Euclid n => v₀ + L w) (L : Euclid n →L[ℝ] Euclid n) 0 :=
      (L.hasStrictFDerivAt).const_add v₀
    have h2 : HasStrictFDerivAt ψ A (v₀ + L 0) := by simpa using hstrict
    exact h2.comp (0 : Euclid n) h1
  -- two-point estimate
  have h1 := (hasStrictFDerivAt_iff_isLittleO.1 hχstrict).bound hε
  have h2 : ∀ᶠ w in 𝓝 (0 : Euclid n), v₀ + L w ∈ V := by
    have hc : Continuous (fun w : Euclid n => v₀ + L w) := continuous_const.add L.continuous
    have : (fun w : Euclid n => v₀ + L w) 0 ∈ V := by simpa using hv₀V
    exact hc.continuousAt.preimage_mem_nhds (hV.mem_nhds this)
  obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.eventually_nhds_iff_ball.1 h1
  obtain ⟨δ₂, hδ₂, hball2⟩ := Metric.eventually_nhds_iff_ball.1 h2
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδV : ∀ w ∈ ball (0 : Euclid n) δ, v₀ + L w ∈ V :=
    fun w hw => hball2 w (ball_subset_ball (min_le_right _ _) hw)
  have hbil : ∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ,
      (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖ := by
    intro a ha b hb
    have hab : (a, b) ∈ ball ((0 : Euclid n), (0 : Euclid n)) δ₁ := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_left _ _) ha, ball_subset_ball (min_le_left _ _) hb⟩
    have he := hball1 (a, b) hab
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at he
    have hn : ‖A (L (a - b))‖ = ‖a - b‖ := hLJ _
    have t1 := norm_sub_norm_le (χ a - χ b) (A (L (a - b)))
    have t2 := norm_sub_norm_le (A (L (a - b))) (χ a - χ b)
    rw [norm_sub_rev (A (L (a - b))) (χ a - χ b)] at t2
    constructor <;> linarith
  -- local surjectivity
  have hinvc := Submission.dsmc_chart_inverse_continuity P n V W ψ hψ.continuousOn hinj
    (by rw [himg]; exact inter_subset_left) hprop v₀ hv₀V
  set C : ℝ := ‖((L.symm : Euclid n ≃L[ℝ] Euclid n) : Euclid n →L[ℝ] Euclid n)‖ with hCdef
  have hC : 0 ≤ C := norm_nonneg _
  obtain ⟨η, hη, hηprop⟩ := hinvc (δ / (C + 1)) (div_pos hδ (by linarith))
  obtain ⟨r₀, hr₀, hr₀W⟩ := Metric.isOpen_iff.1 hW z hzW
  refine ⟨χ, δ, min η r₀, hδ, lt_min hη hr₀, hχ0, hbil, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have : ψ (v₀ + L w) ∈ W ∩ M := by rw [← himg]; exact ⟨_, hδV w hw, rfl⟩
    exact this.2
  · rintro x ⟨hxM, hxb⟩
    have hxW : x ∈ W := hr₀W (ball_subset_ball (min_le_right _ _) hxb)
    obtain ⟨v', hv'V, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hxM⟩
    have hd : dist (ψ v') (ψ v₀) < η := by
      rw [hψv₀]; exact lt_of_lt_of_le (mem_ball.1 hxb) (min_le_left _ _)
    have hv' := hηprop v' hv'V hd
    refine ⟨L.symm (v' - v₀), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      calc ‖L.symm (v' - v₀)‖ ≤ C * ‖v' - v₀‖ := by
            rw [hCdef]
            exact ContinuousLinearMap.le_opNorm
              ((L.symm : Euclid n ≃L[ℝ] Euclid n) : Euclid n →L[ℝ] Euclid n) (v' - v₀)
        _ ≤ C * (δ / (C + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← dist_eq_norm]; exact hv'.le
        _ < δ := by
            rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
            nlinarith
    · simp [χ]
/-- **Bi-Lipschitz images** (Simon Ch. 2, 1.8(i), applied to `χ` and to its inverse): if
`c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b|` on `E ⊆ ℝⁿ`, then `c₁ⁿ Lⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿ Lⁿ(E)`.
`Hⁿ = μHE[n]` is `c · μH[n]` with one constant `c` on every metric space and equals `volume` on
`ℝⁿ`; `χ` is `c₂`-Lipschitz on `E`, and it is injective there with `c₁⁻¹`-Lipschitz inverse on
`χ(E)`. -/
theorem Submission.dimred_rpd_bilipschitz_image_measure : ∀ (P n : ℕ) (χ : Euclid n → Euclid P) (E : Set (Euclid n)) (c₁ c₂ : ℝ), 0 < c₁ → 0 ≤ c₂ → (∀ a ∈ E, ∀ b ∈ E, c₁ * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ c₂ * ‖a - b‖) → ENNReal.ofReal (c₁ ^ n) * volume E ≤ μHE[n] (χ '' E) ∧ μHE[n] (χ '' E) ≤ ENNReal.ofReal (c₂ ^ n) * volume E := by
  intro P n χ E c₁ c₂ hc₁ hc₂ h
  -- `Lⁿ = Hⁿ` on `ℝⁿ`, and `Hⁿ = c · μH[n]` on every metric space
  have hvol : (volume : Measure (Euclid n)) = μHE[n] :=
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).symm
  have hscale : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
      (μHE[n] : Measure X) S = (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) * μH[(n : ℝ)] S := by
    intro X _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  constructor
  · -- lower bound: `χ` is injective on `E` and its inverse on `χ(E)` is `c₁⁻¹`-Lipschitz
    have hinj : InjOn χ E := by
      intro a ha b hb hab
      have := (h a ha b hb).1
      rw [hab, sub_self, norm_zero] at this
      have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    set g := Function.invFunOn χ E
    have hleft : LeftInvOn g χ E := hinj.leftInvOn_invFunOn
    have hgL : LipschitzOnWith (Real.toNNReal c₁⁻¹) g (χ '' E) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hleft ha, hleft hb, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le)]
      have := (h a ha b hb).1
      rw [inv_mul_eq_div, le_div_iff₀ hc₁]
      linarith
    have himg : g '' (χ '' E) = E := hleft.image_image
    have hle := hgL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [himg] at hle
    rw [hvol, hscale, hscale (χ '' E)]
    set c : ℝ≥0∞ := (Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞)
    have hK : ((Real.toNNReal c₁⁻¹ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₁ ^ n)⁻¹ := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le), ← ENNReal.ofReal_pow (inv_nonneg.2 hc₁.le),
        inv_pow]
    rw [hK] at hle
    have hpos : ENNReal.ofReal (c₁ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hc₁ n)).ne'
    have hinv : ENNReal.ofReal (c₁ ^ n)⁻¹ = (ENNReal.ofReal (c₁ ^ n))⁻¹ :=
      ENNReal.ofReal_inv_of_pos (pow_pos hc₁ n)
    rw [hinv] at hle
    calc ENNReal.ofReal (c₁ ^ n) * (c * μH[(n : ℝ)] E)
        ≤ ENNReal.ofReal (c₁ ^ n) * (c * ((ENNReal.ofReal (c₁ ^ n))⁻¹ * μH[(n : ℝ)] (χ '' E))) := by
          gcongr
      _ = c * μH[(n : ℝ)] (χ '' E) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal (c₁ ^ n)) c, mul_assoc,
            ← mul_assoc (ENNReal.ofReal (c₁ ^ n)), ENNReal.mul_inv_cancel hpos ENNReal.ofReal_ne_top,
            one_mul]
  · -- upper bound: `χ` is `c₂`-Lipschitz on `E`
    have hL : LipschitzOnWith (Real.toNNReal c₂) χ E := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc₂]
      exact (h a ha b hb).2
    have hle := hL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [hvol, hscale, hscale E]
    have hK : ((Real.toNNReal c₂ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₂ ^ n) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc₂,
        ← ENNReal.ofReal_pow hc₂]
    rw [hK] at hle
    calc _ ≤ (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
          (ENNReal.ofReal (c₂ ^ n) * μH[(n : ℝ)] E) := by gcongr
      _ = _ := by ring

/-- **Density one on an embedded `C¹` submanifold** (the fact `Θⁿ(Hⁿ⌞M, z) = 1` behind
`Θⁿ(μ_T, z) = |m|` for `T = m[[M]]` near `z ∈ reg T`, Simon 7.4.1):
`Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) → 1` as `s ↓ 0`.  For `ε ∈ (0, 1)`, a `(1 ± ε)`-bi-Lipschitz chart `χ`
with `χ(0) = z` gives `χ(B_{s/(1+ε)}(0)) ⊆ M ∩ B_s(z) ⊆ χ(B_{s/(1−ε)}(0))` for small `s > 0`.  With
the bi-Lipschitz measure bounds (Simon Ch. 2, 1.8(i)) and `Lⁿ(B_r(0)) = ωₙrⁿ` this gives
`((1 − ε)/(1 + ε))ⁿ ≤ Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) ≤ ((1 + ε)/(1 − ε))ⁿ`, and both bounds tend to `1`
as `ε → 0`. -/
theorem Submission.dimred_rpd_submanifold_density_one : ∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → Tendsto (fun s : ℝ => μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M z hM hz
  -- `ωₙ ∈ (0, ∞)`, and `Lⁿ(B_r(0)) = rⁿωₙ` for `r > 0`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωT : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hvol : ∀ r : ℝ, 0 < r →
      volume (ball (0 : Euclid n) r) = ENNReal.ofReal (r ^ n) * unitBallVolume n := by
    intro r hr; rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace_fin]; rfl
  -- Step 1: for `ε ∈ (0, 1)`, `((1 − ε)/(1 + ε))ⁿ ≤ Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) ≤ ((1 + ε)/(1 − ε))ⁿ`
  -- for all small `s > 0`
  have hbounds : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n) ≤
          μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) ∧
        μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) ≤
          ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n) := by
    intro ε hε hε1
    -- the `(1 ± ε)`-bi-Lipschitz chart `χ : B_δ(0) → M` with `χ(0) = z`, onto `M` near `z`
    obtain ⟨χ, δ, δ', hδ, hδ', hχ0, hbil, hχM, hMχ⟩ :=
      Submission.dimred_rpd_near_isometric_chart P n M z hM hz ε hε
    have h1ε : 0 < 1 - ε := by linarith
    have h1ε' : 0 < 1 + ε := by linarith
    have hs₀ : 0 < min δ' ((1 - ε) * δ) := lt_min hδ' (mul_pos h1ε hδ)
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hsδ' : s < δ' := lt_of_lt_of_le hs1 (min_le_left _ _)
    have hsδ : s < (1 - ε) * δ := lt_of_lt_of_le hs1 (min_le_right _ _)
    -- `0 < r₁ = s/(1 + ε) ≤ r₂ = s/(1 − ε) < δ`
    set r₁ := s / (1 + ε) with hr₁def
    set r₂ := s / (1 - ε) with hr₂def
    have hr₁ : 0 < r₁ := div_pos hs0 h1ε'
    have hr₂ : 0 < r₂ := div_pos hs0 h1ε
    have hr₂δ : r₂ < δ := by rw [hr₂def, div_lt_iff₀ h1ε]; linarith
    have hr₁r₂ : r₁ ≤ r₂ := div_le_div_of_nonneg_left hs0.le h1ε (by linarith)
    have hb₁ : ball (0 : Euclid n) r₁ ⊆ ball 0 δ := ball_subset_ball (by linarith)
    have hb₂ : ball (0 : Euclid n) r₂ ⊆ ball 0 δ := ball_subset_ball hr₂δ.le
    -- (a) `χ(B_{r₁}(0)) ⊆ M ∩ B_s(z)`: `|χ(w) − z| ≤ (1 + ε)|w| < (1 + ε)r₁ = s`
    have hinc₁ : χ '' ball 0 r₁ ⊆ M ∩ ball z s := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨hχM ⟨w, hb₁ hw, rfl⟩, ?_⟩
      rw [mem_ball, dist_eq_norm, ← hχ0]
      have h := (hbil w (hb₁ hw) 0 (mem_ball_self hδ)).2
      rw [sub_zero] at h
      rw [mem_ball, dist_zero_right] at hw
      calc ‖χ w - χ 0‖ ≤ (1 + ε) * ‖w‖ := h
        _ < (1 + ε) * r₁ := mul_lt_mul_of_pos_left hw h1ε'
        _ = s := by rw [hr₁def]; field_simp
    -- (b) `M ∩ B_s(z) ⊆ χ(B_{r₂}(0))`: `x = χ(w)` with `(1 − ε)|w| ≤ |x − z| < s`
    have hinc₂ : M ∩ ball z s ⊆ χ '' ball 0 r₂ := by
      rintro x ⟨hxM, hxs⟩
      obtain ⟨w, hw, rfl⟩ := hMχ ⟨hxM, ball_subset_ball hsδ'.le hxs⟩
      refine ⟨w, ?_, rfl⟩
      have h := (hbil w hw 0 (mem_ball_self hδ)).1
      rw [sub_zero] at h
      rw [mem_ball, dist_eq_norm, ← hχ0] at hxs
      rw [mem_ball, dist_zero_right, hr₂def, lt_div_iff₀ h1ε]
      nlinarith [norm_nonneg w]
    -- (c) the bi-Lipschitz measure bounds on `B_{r₁}(0), B_{r₂}(0) ⊆ B_δ(0)`
    have hlow := (Submission.dimred_rpd_bilipschitz_image_measure P n χ (ball 0 r₁) (1 - ε) (1 + ε)
      h1ε h1ε'.le (fun a ha b hb => hbil a (hb₁ ha) b (hb₁ hb))).1
    have hupp := (Submission.dimred_rpd_bilipschitz_image_measure P n χ (ball 0 r₂) (1 - ε) (1 + ε)
      h1ε h1ε'.le (fun a ha b hb => hbil a (hb₂ ha) b (hb₂ hb))).2
    rw [hvol r₁ hr₁] at hlow
    rw [hvol r₂ hr₂] at hupp
    have hm1 := hlow.trans (measure_mono hinc₁)
    have hm2 := (measure_mono hinc₂).trans hupp
    -- divide by `ωₙsⁿ ∈ (0, ∞)`
    have hden0 : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hs0 n)).ne'
    have hdenT : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top hωT ENNReal.ofReal_ne_top
    constructor
    · rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenT)]
      have e : ((1 - ε) / (1 + ε)) ^ n * s ^ n = (1 - ε) ^ n * r₁ ^ n := by
        rw [hr₁def, div_pow, div_pow]; field_simp
      calc ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n) * (unitBallVolume n * ENNReal.ofReal (s ^ n))
          = ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n * s ^ n) * unitBallVolume n := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ = ENNReal.ofReal ((1 - ε) ^ n * r₁ ^ n) * unitBallVolume n := by rw [e]
        _ = ENNReal.ofReal ((1 - ε) ^ n) * (ENNReal.ofReal (r₁ ^ n) * unitBallVolume n) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ ≤ _ := hm1
    · rw [ENNReal.div_le_iff hden0 hdenT]
      have e : ((1 + ε) / (1 - ε)) ^ n * s ^ n = (1 + ε) ^ n * r₂ ^ n := by
        rw [hr₂def, div_pow, div_pow]; field_simp
      calc μHE[n] (M ∩ ball z s)
          ≤ ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal (r₂ ^ n) * unitBallVolume n) := hm2
        _ = ENNReal.ofReal ((1 + ε) ^ n * r₂ ^ n) * unitBallVolume n := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n * s ^ n) * unitBallVolume n := by rw [e]
        _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n) *
              (unitBallVolume n * ENNReal.ofReal (s ^ n)) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
  -- Step 2: both bounds tend to `1` as `ε → 0`, so `Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) → 1` (`tendsto_order`)
  have hg₁ : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => ((1 - ε) / (1 + ε)) ^ n) (𝓝 0) (𝓝 (((1 - 0) / (1 + 0)) ^ n)) :=
      ((tendsto_const_nhds.sub tendsto_id).div (tendsto_const_nhds.add tendsto_id)
        (by norm_num)).pow n
    simpa using ENNReal.tendsto_ofReal h
  have hg₂ : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ n) (𝓝 0) (𝓝 (((1 + 0) / (1 - 0)) ^ n)) :=
      ((tendsto_const_nhds.add tendsto_id).div (tendsto_const_nhds.sub tendsto_id)
        (by norm_num)).pow n
    simpa using ENNReal.tendsto_ofReal h
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with ε h1 h2
    exact ⟨h1, h2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- `a < 1`: choose `ε ∈ (0, 1)` with `a < ((1 − ε)/(1 + ε))ⁿ`
    obtain ⟨ε, hεa, hε0, hε1⟩ :=
      (((hg₁.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds ha)).and hsmall).exists
    filter_upwards [hbounds ε hε0 hε1] with s hs
    exact lt_of_lt_of_le hεa hs.1
  · -- `1 < b`: choose `ε ∈ (0, 1)` with `((1 + ε)/(1 − ε))ⁿ < b`
    obtain ⟨ε, hεb, hε0, hε1⟩ :=
      (((hg₂.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb)).and hsmall).exists
    filter_upwards [hbounds ε hε0 hε1] with s hs
    exact lt_of_le_of_lt hs.2 hεb

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
