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

/-- **Gram identity for the linear graph map** (Simon Ch. 2, 3.3 and Example 3.6(3): the area
Jacobian of a graph).  If `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` are linear isometries with
`⟨ιv, ι'w⟩ = 0` and `T : ℝⁿ → ℝᵏ` is linear, then `A = ι + ι' ∘ T` has `A* ∘ A = id + T* ∘ T`.
Pair both sides with `y`: `⟨A*Ax, y⟩ = ⟨Ax, Ay⟩ = ⟨ιx, ιy⟩ + ⟨ι'Tx, ι'Ty⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩`,
the cross terms vanishing by orthogonality, and `⟨(id + T*T)x, y⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩`. -/
theorem Submission.doraggt_graph_map_gram_identity : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (T : Euclid n →ₗ[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LinearMap.adjoint (ι.toLinearMap + ι'.toLinearMap ∘ₗ T) ∘ₗ (ι.toLinearMap + ι'.toLinearMap ∘ₗ T) = LinearMap.id + LinearMap.adjoint T ∘ₗ T := by
  intro n k ι ι' T h
  -- the other cross term vanishes too, by symmetry of the real inner product
  have h' : ∀ v w, inner ℝ (ι' w) (ι v) = 0 := fun v w => by rw [real_inner_comm]; exact h v w
  -- endomorphisms of `ℝⁿ` agree once `⟨S x, y⟩` agrees for all `x, y`
  refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
  -- `⟨A*Ax, y⟩ = ⟨Ax, Ay⟩` and `⟨T*Tx, y⟩ = ⟨Tx, Ty⟩`; expand, isometries keep `⟨·, ·⟩`
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply,
    LinearMap.id_apply, LinearIsometry.coe_toLinearMap, inner_add_left, inner_add_right,
    LinearIsometry.inner_map_map, h, h', add_zero, zero_add]
/-- **Metric and Hausdorff-measure properties of a Lipschitz graph map** (Simon Ch. 2,
Theorem 1.8(i); Steps 0, 1 and 3 of the graph-tangent argument for Allard's graph).  Let
`ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` be linear isometries with orthogonal ranges, `g` an
`L`-Lipschitz map and `Ψ(u) = b + ιu + ι'(g u)`.  Then (i) `|u − u'| ≤ |Ψ(u) − Ψ(u')|`
(Pythagoras), (ii) `Ψ` is `(1 + L)`-Lipschitz, (iii) `Ψ(ℝⁿ)` is closed (antilipschitz and
uniformly continuous on the complete `ℝⁿ`), (iv) `Hⁿ(Ψ(ℝⁿ) ∩ K) < ∞` for compact `K` (by (i),
`Ψ(ℝⁿ) ∩ K ⊆ Ψ(B̄ₘ(0))`), (v) `Hⁿ(Ψ(N)) = 0` if `Lⁿ(N) = 0`; (iv) and (v) use
`Hⁿ(Ψ(A)) ≤ (1 + L)ⁿ Hⁿ(A)` and `Hⁿ = Lⁿ` on `ℝⁿ`. -/
theorem Submission.doraggt_lipschitz_graph_map_basics : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (b : Euclid (n + k)) (g : Euclid n → Euclid k) (L : NNReal), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L g → (∀ u u' : Euclid n, dist u u' ≤ dist (b + ι u + ι' (g u)) (b + ι u' + ι' (g u'))) ∧ LipschitzWith (1 + L) (fun u => b + ι u + ι' (g u)) ∧ IsClosed (Set.range fun u => b + ι u + ι' (g u)) ∧ (∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range (fun u => b + ι u + ι' (g u)) ∩ K) ≠ ∞) ∧ ∀ N : Set (Euclid n), volume N = 0 → μHE[n] ((fun u => b + ι u + ι' (g u)) '' N) = 0 := by
  intro n k ι ι' b g L horth hg
  set Ψ : Euclid n → Euclid (n + k) := fun u => b + ι u + ι' (g u) with hΨ
  -- Step 1: `Ψ(u) − Ψ(u') = ι(u − u') + ι'(g u − g u')`.
  have hdiff : ∀ u u', Ψ u - Ψ u' = ι (u - u') + ι' (g u - g u') := by
    intro u u'
    simp only [hΨ, map_sub]
    abel
  -- Step 2 (i): Pythagoras, `|Ψ(u) − Ψ(u')|² = |u − u'|² + |g u − g u'|²`.
  have hdist : ∀ u u', dist u u' ≤ dist (Ψ u) (Ψ u') := by
    intro u u'
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth (u - u') (g u - g u'))
/-- Difference quotients `r⁻¹(f(v + rw) − f(v))` of a map differentiable at `v` converge to
`Df(v)w` uniformly on every closed ball `B̄_R(0)` as `r ↓ 0` (the `o(|h|)` estimate in the
weighted blow-up limit of the Allard graph step).  With `R' = max R 1`, pick `ρ > 0` such that
`|f(v + h) − f(v) − Df(v)h| ≤ ε|h|/(2R')` for `|h| < ρ`.  For `0 < r < ρ/R'` and `|w| ≤ R`,
`|rw| < ρ`, and linearity of `Df(v)` gives `|Df(v)w − r⁻¹(f(v + rw) − f(v))| ≤ ε|w|/(2R') < ε`. -/
theorem Submission.dorwbl_diff_quotient_tendstoUniformlyOn : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (v : Euclid n), DifferentiableAt ℝ f v → ∀ R : ℝ, TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => r⁻¹ • (f (v + r • w) - f v)) (fun w => fderiv ℝ f v w) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
  intro n k f v hf R
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hR : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hc : 0 < ε / (2 * max R 1) := by positivity
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).bound hc)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / max R 1 by positivity)] with r hr w hw
  obtain ⟨hr0, hrρ⟩ := hr
  have hw' : ‖w‖ ≤ max R 1 := (mem_closedBall_zero_iff.1 hw).trans (le_max_left R 1)
  have hrw : ‖r • w‖ = r * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
  -- `|rw| ≤ rR' < ρ`, so the little-o bound applies to `h = rw`
  have hbound := hsmall (show dist (r • w) 0 < ρ by
    rw [dist_zero_right, hrw]
    calc r * ‖w‖ ≤ r * max R 1 := mul_le_mul_of_nonneg_left hw' hr0.le
      _ < ρ / max R 1 * max R 1 := mul_lt_mul_of_pos_right hrρ hR
      _ = ρ := div_mul_cancel₀ ρ hR.ne')
  -- `Df(v)w − r⁻¹(f(v + rw) − f(v)) = −r⁻¹(f(v + rw) − f(v) − Df(v)(rw))`
  have hid : fderiv ℝ f v w - r⁻¹ • (f (v + r • w) - f v) =
      -(r⁻¹ • (f (v + r • w) - f v - fderiv ℝ f v (r • w))) := by
    simp only [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
    abel
  rw [dist_eq_norm, hid, norm_neg, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le]
  calc r⁻¹ * ‖f (v + r • w) - f v - fderiv ℝ f v (r • w)‖
      ≤ r⁻¹ * (ε / (2 * max R 1) * ‖r • w‖) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr0.le)
    _ = ε / (2 * max R 1) * ‖w‖ := by
        rw [hrw]
        field_simp
    _ ≤ ε / (2 * max R 1) * max R 1 := mul_le_mul_of_nonneg_left hw' hc.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- Test-function step (Step 8) of the weighted graph blow-up limit used for the tangent planes of
Lipschitz graphs (cf. Simon Ch. 3, proof of 1.6 "⇒", where `∫_{η_{x,λ}(N)} f dHⁿ → ∫_{T_x N} f dHⁿ`).
If `f : ℝⁿ → ℝᵏ` is differentiable at `v` and `ψ ∈ C_c(ℝ^{n+k})`, then
`U(r) = ∫_{B̄_R(0)} |ψ(ιw + ι'(r⁻¹(f(v + rw) − f(v)))) − ψ(ιw + ι'(Df(v)w))| dw → 0` as `r ↓ 0`.
The difference quotients tend to `Df(v)` uniformly on `B̄_R(0)`; the isometry `ι'` carries this to
the graph maps, and `ψ` is uniformly continuous, so eventually the integrand is at most
`ε / (Lⁿ(B̄_R(0)) + 1)` on the ball, which has finite measure.  Continuity of `f` is not used. -/
theorem Submission.dorwbl_test_fn_diff_quotient_integral_tendsto_zero : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (ψ : Euclid (n + k) → ℝ), Continuous f → DifferentiableAt ℝ f v → Continuous ψ → HasCompactSupport ψ → ∀ R : ℝ, Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|) (𝓝[>] 0) (𝓝 0) := by
  intro n k ι ι' f v ψ _hf hfv hψ hψc R
  -- the graph maps `Φ_r w = ι w + ι' (f_{v,r} w)` tend to `Φ w = ι w + ι' (Df(v) w)` uniformly on
  -- `B̄_R(0)`: `dist (Φ w) (Φ_r w) = dist (Df(v) w) (f_{v,r} w)` since `ι'` is an isometry
  have hΦ : TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => ι w + ι' (r⁻¹ • (f (v + r • w) - f v)))
      (fun w => ι w + ι' (fderiv ℝ f v w)) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
    have h := Submission.dorwbl_diff_quotient_tendstoUniformlyOn n k f v hfv R
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with r hr w hw
    simp only [dist_add_left, LinearIsometry.dist_map]
    exact hr w hw
  -- `ψ` is uniformly continuous (continuous with compact support), so `ψ ∘ Φ_r → ψ ∘ Φ` uniformly
  have hψΦ := (hψc.uniformContinuous_of_continuous hψ).comp_tendstoUniformlyOn hΦ
  rw [Metric.tendstoUniformlyOn_iff] at hψΦ
  have hB : volume (closedBall (0 : Euclid n) R) < ∞ := measure_closedBall_lt_top
  have hV : 0 ≤ volume.real (closedBall (0 : Euclid n) R) := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- with `η = ε / (Lⁿ(B̄_R(0)) + 1)`, eventually `|U(r)| ≤ η Lⁿ(B̄_R(0)) < ε`
  have hη : 0 < ε / (volume.real (closedBall (0 : Euclid n) R) + 1) := div_pos hε (by linarith)
  filter_upwards [hψΦ _ hη] with r hr
  rw [dist_zero_right]
  refine (norm_setIntegral_le_of_norm_le_const
    (C := ε / (volume.real (closedBall (0 : Euclid n) R) + 1)) hB fun w hw => ?_).trans_lt ?_
  · have h1 := hr w hw
    simp only [Function.comp_apply, Real.dist_eq] at h1
    rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]
    exact h1.le
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith

/-- Weighted blow-up limit at one good point `v`.  Let `f` be continuous and differentiable at
`v`, `G` Borel with `|G| ≤ C`, and `∫_{B_R(0)} |G(v + r w) - G(v)| dw → 0` as `r ↓ 0` for every
`R > 0`.  With `Φ_r w = ι w + ι'(r⁻¹(f(v + r w) - f(v)))` and `Φ w = ι w + ι'(Df(v) w)`, every
continuous compactly supported `ψ` has `∫ ψ(Φ_r w) G(v + r w) dw → G(v) ∫ ψ(Φ w) dw`.
Orthogonality gives `‖w‖ ≤ ‖ι w + ι' u‖`, so both integrands vanish off `B_R(0)` once
`spt ψ ⊆ B_R(0)`; there they differ by at most `C |ψ ∘ Φ_r - ψ ∘ Φ| + M |G(v + r ·) - G(v)|`
(`|ψ| ≤ M`), whose integral tends to `0`. -/
theorem Submission.dorwbl_weighted_blowup_tendsto_at_point : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (G : Euclid n → ℝ) (C : ℝ) (v : Euclid n), (∀ x y, inner ℝ (ι x) (ι' y) = 0) → Continuous f → Measurable G → (∀ u, |G u| ≤ C) → DifferentiableAt ℝ f v → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v|) (𝓝[>] 0) (𝓝 0)) → ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)))) := by
  intro n k ι ι' f G C v horth hf hG hGC hdiff hleb ψ hψ hψc
  -- `|ψ| ≤ M`, and `tsupport ψ ⊆ closedBall 0 R₀` with `R₀ ≤ R`, `0 < R`.
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  have hψM : ∀ y, |ψ y| ≤ M := fun y => by rw [← Real.norm_eq_abs]; exact hM y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hψM 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hGC 0)
  obtain ⟨R₀, hR₀⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euclid (n + k))
  obtain ⟨R, hRpos, hR₀R⟩ : ∃ R : ℝ, 0 < R ∧ R₀ ≤ R :=
    ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  have hBfin : volume (closedBall (0 : Euclid n) R) ≠ ∞ := measure_closedBall_lt_top.ne
  -- Pythagoras: `‖w‖ ≤ ‖ι w + ι' u‖`.
  have hpyth : ∀ (w : Euclid n) (u : Euclid k), ‖w‖ ≤ ‖ι w + ι' u‖ := by
    intro w u
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth w u)
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map] at h
    refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
    rw [h]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  -- Step 3 (ii): triangle inequality and the Lipschitz bound for `g`.
  have hlip : LipschitzWith (1 + L) Ψ := by
    refine LipschitzWith.of_dist_le_mul fun u u' => ?_
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    calc ‖ι (u - u') + ι' (g u - g u')‖ ≤ ‖ι (u - u')‖ + ‖ι' (g u - g u')‖ := norm_add_le _ _
      _ = ‖u - u'‖ + dist (g u) (g u') := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map, dist_eq_norm]
      _ ≤ ‖u - u'‖ + L * ‖u - u'‖ := by
          rw [← dist_eq_norm u u']
          gcongr
          exact hg.dist_le_mul u u'
      _ = ((1 + L : NNReal) : ℝ) * ‖u - u'‖ := by
          push_cast
          ring
  -- Step 4 (iii): `Ψ` is antilipschitz and uniformly continuous on the complete `ℝⁿ`.
  have hclosed : IsClosed (Set.range Ψ) := by
    have hanti : AntilipschitzWith 1 Ψ :=
      AntilipschitzWith.of_le_mul_dist fun u u' => by simpa using hdist u u'
    exact hanti.isClosed_range hlip.uniformContinuous
  -- Step 5: `Hⁿ(Ψ(A)) ≤ (1 + L)ⁿ Lⁿ(A)`, using `Hⁿ = Lⁿ` on `ℝⁿ`.
  have himage : ∀ A : Set (Euclid n),
      μHE[n] (Ψ '' A) ≤ ((1 + L : NNReal) : ℝ≥0∞) ^ n * volume A := by
    intro A
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hlip.lipschitzOnWith (s := A))
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  -- Step 6 (iv): `Ψ(ℝⁿ) ∩ K ⊆ Ψ(B̄ₘ(0))` for `K ⊆ B̄ₘ(Ψ(0))`, by (i).
  have hfin : ∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range Ψ ∩ K) ≠ ∞ := by
    intro K hK
    obtain ⟨m, hm⟩ := hK.isBounded.subset_closedBall (Ψ 0)
    have hsub : Set.range Ψ ∩ K ⊆ Ψ '' closedBall 0 m := by
      rintro _ ⟨⟨u, rfl⟩, huK⟩
      exact ⟨u, mem_closedBall.2 ((hdist u 0).trans (mem_closedBall.1 (hm huK))), rfl⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (himage _))
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_closedBall_lt_top.ne
  -- Step 7 (v): null sets go to null sets.
  have hnull : ∀ N : Set (Euclid n), volume N = 0 → μHE[n] (Ψ '' N) = 0 := by
    intro N hN
    exact le_zero_iff.1 ((himage N).trans (by rw [hN, mul_zero]))
  exact ⟨hdist, hlip, hclosed, hfin, hnull⟩
/-- **Blow-ups of a graph are graphs of difference quotients** (Simon Ch. 3, 1.4: the dilation
`η_{x,λ}(y) = λ⁻¹(y − x)`).  Let `Φ(u) = a + ιu + ι'f(u)`, `r ≠ 0` and
`f_{v,r}(w) = r⁻¹(f(v + rw) − f(v))`.  By linearity
`η_{Φ(v),r}(Φ(u)) = ι(r⁻¹(u − v)) + ι'(r⁻¹(f(u) − f(v)))`, so the bijection `u = v + rw` of `ℝⁿ`
gives `η_{Φ(v),r}(Φ(ℝⁿ)) = {ιw + ι'f_{v,r}(w) : w ∈ ℝⁿ}`.  Where `f` is differentiable at
`v + rw`, the chain rule gives `Df_{v,r}(w) = r⁻¹ Df(v + rw) ∘ (r id) = Df(v + rw)`; elsewhere
`f_{v,r}` is not differentiable at `w` either (`f(u) = f(v) + r f_{v,r}(r⁻¹(u − v))`), and both
`fderiv`s are `0`. -/
theorem Submission.doraggt_graph_blowup_rescaling : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (a : Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (r : ℝ), r ≠ 0 → Poincare.SimonGMT.Chapter03.blowUpMap (a + ι v + ι' (f v)) r '' Set.range (fun u => a + ι u + ι' (f u)) = Set.range (fun w => ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) ∧ ∀ w : Euclid n, fderiv ℝ (fun w' => r⁻¹ • (f (v + r • w') - f v)) w = fderiv ℝ f (v + r • w) := by
  intro n k ι ι' a f v r hr
  refine ⟨?_, fun w => ?_⟩
  · -- Steps 2–3: reparametrize `ℝⁿ` by the bijection `w ↦ v + r • w`
    have he : Function.Surjective fun w : Euclid n => v + r • w := fun u =>
      ⟨r⁻¹ • (u - v), by simp only [smul_inv_smul₀ hr, add_sub_cancel]⟩
    rw [← Set.range_comp, ← he.range_comp]
    congr 1
    funext w
    -- Step 1: `η(Φ(v + r • w)) = r⁻¹ • (r • ι w + (ι' (f (v + r • w)) - ι' (f v)))`
    simp only [Function.comp_apply, Poincare.SimonGMT.Chapter03.blowUpMap, map_add, map_smul,
      map_sub]
    rw [show a + (ι v + r • ι w) + ι' (f (v + r • w)) - (a + ι v + ι' (f v)) =
        r • ι w + (ι' (f (v + r • w)) - ι' (f v)) by abel, smul_add, inv_smul_smul₀ hr]
  · by_cases hf : DifferentiableAt ℝ f (v + r • w)
    · -- Step 4: chain rule through `w' ↦ v + r • w'`, whose derivative is `r • id`
      have h : HasFDerivAt (fun w' => r⁻¹ • (f (v + r • w') - f v))
          (r⁻¹ • (fderiv ℝ f (v + r • w)).comp (r • ContinuousLinearMap.id ℝ (Euclid n))) w :=
        ((hf.hasFDerivAt.comp w (((hasFDerivAt_id w).const_smul r).const_add v)).sub_const
          (f v)).const_smul r⁻¹
      rw [h.fderiv, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
        ContinuousLinearMap.comp_id, inv_smul_smul₀ hr]
    · -- Step 5: `u ↦ r⁻¹ • (u - v)` maps `v + r • w` to `w` and
      -- `f u = f v + r • f_{v,r} (r⁻¹ • (u - v))`, so `f_{v,r}` is not differentiable at `w`
      -- either; both derivatives are `0`
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt]
      intro hg
      have hw : r⁻¹ • (v + r • w - v) = w := by rw [add_sub_cancel_left, inv_smul_smul₀ hr]
      rw [← hw] at hg
      have hL : DifferentiableAt ℝ (fun u : Euclid n => r⁻¹ • (u - v)) (v + r • w) :=
        (differentiableAt_id.sub_const v).const_smul r⁻¹
      refine hf ((((hg.comp (v + r • w) hL).const_smul r).const_add (f v)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u => ?_))
      simp only [Pi.smul_apply, Function.comp_apply, smul_inv_smul₀ hr, add_sub_cancel]
  -- Both integrands vanish off `closedBall 0 R`.
  have hvanish : ∀ w : Euclid n, w ∉ closedBall (0 : Euclid n) R → ∀ u : Euclid k,
      ψ (ι w + ι' u) = 0 := by
    intro w hw u
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hw
    have h1 := hR₀ hmem
    rw [mem_closedBall_zero_iff] at h1 ⊢
    exact (hpyth w u).trans (h1.trans hR₀R)
  -- `C ∫_{B_R} |ψ ∘ Φ_r - ψ ∘ Φ| + M ∫_{B_R} |G(v + r ·) - G(v)| → 0`.
  have hU := Submission.dorwbl_test_fn_diff_quotient_integral_tendsto_zero n k ι ι' f v ψ hf
    hdiff hψ hψc R
  have hV := hleb R hRpos
  have hlim := (hU.const_mul C).add (hV.const_mul M)
  rw [mul_zero, mul_zero, add_zero] at hlim
  -- Pointwise: `a x - G(v) b = (a - b) x + b (x - G(v))`.
  have hpt : ∀ a b x : ℝ, |b| ≤ M → |x| ≤ C →
      |a * x - G v * b| ≤ C * |a - b| + M * |x - G v| := by
    intro a b x hb hx
    calc |a * x - G v * b| = |(a - b) * x + b * (x - G v)| := by congr 1; ring
      _ ≤ |(a - b) * x| + |b * (x - G v)| := abs_add_le _ _
      _ = |a - b| * |x| + |b| * |x - G v| := by rw [abs_mul, abs_mul]
      _ ≤ |a - b| * C + M * |x - G v| :=
        add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
      _ = C * |a - b| + M * |x - G v| := by ring
  -- For every `r`, the error is bounded by the quantity in `hlim`.
  have key : ∀ r : ℝ,
      ‖(∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) -
          G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))‖ ≤
        C * (∫ w in closedBall (0 : Euclid n) R,
            |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|) +
          M * ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v| := by
    intro r
    have hcr : Continuous fun w : Euclid n => ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) := by
      fun_prop
    have hc : Continuous fun w : Euclid n => ψ (ι w + ι' (fderiv ℝ f v w)) := by fun_prop
    have hGr : Measurable fun w : Euclid n => G (v + r • w) :=
      hG.comp (by fun_prop : Continuous fun w : Euclid n => v + r • w).measurable
    have ha : IntegrableOn
        (fun w => ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w))
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := M * C) hBfin
        (hcr.measurable.mul hGr).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hψM _) (hGC _) (abs_nonneg _) hM0)
    have hb : IntegrableOn (fun w => G v * ψ (ι w + ι' (fderiv ℝ f v w)))
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := C * M) hBfin
        (hc.measurable.const_mul (G v)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hGC _) (hψM _) (abs_nonneg _) hC0)
    have hΔ : IntegrableOn
        (fun w => |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|)
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := M + M) hBfin
        (continuous_abs.measurable.comp (hcr.measurable.sub hc.measurable)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (add_le_add (hψM _) (hψM _)))
    have hg : IntegrableOn (fun w => |G (v + r • w) - G v|) (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := C + C) hBfin
        (continuous_abs.measurable.comp (hGr.sub measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (add_le_add (hGC _) (hGC _)))
    have hA : (∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) =
        ∫ w in closedBall (0 : Euclid n) R,
          ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hvanish w hw, zero_mul]
    have hB : G v * (∫ w, ψ (ι w + ι' (fderiv ℝ f v w))) =
        ∫ w in closedBall (0 : Euclid n) R, G v * ψ (ι w + ι' (fderiv ℝ f v w)) := by
      rw [← integral_const_mul]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hvanish w hw, mul_zero]
    rw [hA, hB, ← integral_sub ha hb, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hΔ.const_mul C) (hg.const_mul M)]
    refine norm_integral_le_of_norm_le ((hΔ.const_mul C).add (hg.const_mul M))
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs]
    exact hpt _ _ _ (hψM _) (hGC _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun r => norm_nonneg _) key hlim
/-- **Lebesgue points, rescaled** (Simon Ch. 1, Corollary 3.17, in the Lebesgue-point form of
Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`): if `g : ℝⁿ → ℝ` is locally
`Lⁿ`-integrable, then for `Lⁿ`-a.e. `v` and every `R > 0`, `∫_{B_R(0)} |g(v + rw) − g(v)| dw → 0`
as `r ↓ 0`.  The substitutions `u = rw`, `y = v + u` and `Lⁿ(B_{rR}(v)) = rⁿ Lⁿ(B_R(0))` give
`∫_{B_R(0)} |g(v + rw) − g(v)| dw = Lⁿ(B_R(0)) ⨍_{B_{rR}(v)} |g − g(v)|`, and these averages tend
to `0` at every Lebesgue point `v` of `g`. -/
theorem Submission.doraggt_ae_rescaled_lebesgue_point : ∀ (n : ℕ) (g : Euclid n → ℝ), LocallyIntegrable g volume → ∀ᵐ v ∂(volume : Measure (Euclid n)), ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v|) (𝓝[>] 0) (𝓝 0) := by
  intro n g hg
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (volume : Measure (Euclid n)) hg 1] with v hv R hR
  -- Lebesgue point: the averages over `closedBall v (r * R)` tend to `0` as `r ↓ 0`
  have hδ : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  have hA : Tendsto (fun r : ℝ => ⨍ y in closedBall v (r * R), |g y - g v|) (𝓝[>] 0) (𝓝 0) := by
    have h := hv (fun _ => v) (fun r : ℝ => r * R) hδ (by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      rw [one_mul]
      exact mem_closedBall_self (mul_pos hr hR).le)
    simpa only [Real.norm_eq_abs] using h
  -- change of variables `u = r • w` (dilation), `y = v + u` (translation)
  have key : ∀ r : ℝ, 0 < r → ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v| =
      volume.real (closedBall (0 : Euclid n) R) * ⨍ y in closedBall v (r * R), |g y - g v| := by
    intro r hr
    have h1 : ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v| =
        (r ^ n)⁻¹ • ∫ u in closedBall (0 : Euclid n) (r * R), |g (v + u) - g v| := by
      rw [Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euclid n))
        (fun u => |g (v + u) - g v|) _ hr, _root_.smul_closedBall _ _ hR.le, smul_zero,
        Real.norm_of_nonneg hr.le, finrank_euclideanSpace_fin]
    have h2 : ∫ u in closedBall (0 : Euclid n) (r * R), |g (v + u) - g v| =
        ∫ y in closedBall v (r * R), |g y - g v| := by
      have h := MeasurePreserving.setIntegral_preimage_emb
        (measurePreserving_add_left (volume : Measure (Euclid n)) v)
        (measurableEmbedding_addLeft v) (fun y => |g y - g v|) (closedBall v (r * R))
      simpa using h
    -- `∫_{B_{rR}(v)} = Lⁿ(B_{rR}(v)) ⨍_{B_{rR}(v)}` and `Lⁿ(B_{rR}(v)) = rⁿ Lⁿ(B_R(0))`
    have h3 := measure_smul_setAverage (μ := (volume : Measure (Euclid n)))
      (fun y => |g y - g v|) (s := closedBall v (r * R)) measure_closedBall_lt_top.ne
    rw [h1, h2, ← h3, smul_eq_mul, smul_eq_mul,
      Measure.addHaar_real_closedBall _ _ (mul_pos hr hR).le,
      Measure.addHaar_real_closedBall _ _ hR.le, finrank_euclideanSpace_fin, mul_pow]
    have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr.ne'
    field_simp
  have hlim : Tendsto (fun r : ℝ => volume.real (closedBall (0 : Euclid n) R) *
      ⨍ y in closedBall v (r * R), |g y - g v|) (𝓝[>] 0) (𝓝 0) := by
    simpa using hA.const_mul (volume.real (closedBall (0 : Euclid n) R))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact (key r hr).symm

/-- **Weighted blow-ups of a Lipschitz graph** (Simon Ch. 2, Theorem 1.4 (Rademacher) and Ch. 1,
Corollary 3.17).  Let `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` be linear isometries with
orthogonal ranges, `f : ℝⁿ → ℝᵏ` Lipschitz and `G : ℝⁿ → ℝ` measurable with `|G| ≤ C`.  Then for
`Lⁿ`-a.e. `v`, `f` is differentiable at `v` and, for every continuous compactly supported `ψ`,
`∫ ψ(ιw + ι'(r⁻¹(f(v + rw) − f(v)))) G(v + rw) dw → G(v) ∫ ψ(ιw + ι'(Df(v)w)) dw` as `r ↓ 0`.
The bounded measurable weight `G` is locally integrable, so Rademacher's theorem and the rescaled
Lebesgue-point property of `G` hold simultaneously at a.e. `v`; at every such `v` the convergence
is the blow-up limit at a differentiability point that is a rescaled Lebesgue point of `G`. -/
theorem Submission.doraggt_ae_weighted_graph_blowup_tendsto : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (L : NNReal) (G : Euclid n → ℝ) (C : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L f → Measurable G → (∀ u, |G u| ≤ C) → ∀ᵐ v ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f v ∧ ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)))) := by
  intro n k ι ι' f L G C horth hf hG hGC
  -- `G` is bounded and measurable, hence integrable on every compact set
  have hloc : LocallyIntegrable G volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hG.aestronglyMeasurable (M := C)
      (Eventually.of_forall fun u => (Real.norm_eq_abs (G u)).trans_le (hGC u))
  -- Rademacher and the rescaled Lebesgue-point property of `G` hold simultaneously a.e.
  filter_upwards [hf.ae_differentiableAt (μ := volume),
    Submission.doraggt_ae_rescaled_lebesgue_point n G hloc] with v hv hleb
  -- at such `v`, the blow-up limit holds for every test function `ψ`
  exact ⟨hv, Submission.dorwbl_weighted_blowup_tendsto_at_point n k ι ι' f G C v horth
    hf.continuous hG hGC hv hleb⟩
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in an open set**
(Simon Ch. 1, 3.6 and Remark 3.7(2); chapter-01.txt lines 700–711).  If `U ⊆ ℝᴾ` is open and
`S ⊆ ℝᴾ` is Borel with `Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e.
`x ∈ U \ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B(y, r_y)` with
`B̄(y, r_y) ⊆ U` cover `U` (Lindelöf); the upper density theorem applies to each piece
`S ∩ B(y, r_y)`, of finite measure, and the piece agrees with `S` on small balls about
`x ∈ B(y, r_y)`. -/
theorem Submission.doraggt_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U` (Lindelöf).
  have hrad : ∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hrad
  obtain ⟨D, hDU, hDc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    (fun y hy => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (hr0 y hy)))
  -- Steps 2 and 3, the upper density theorem for each finite-measure piece `S ∩ B(y, r y)`,
  -- simultaneously for the countably many `y ∈ D`.
  have hae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] ((S ∩ ball y (r y)) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    refine Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball) ?_
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
  -- Step 4, near `x ∈ B(y, r y)` the piece and `S` agree.
  filter_upwards [hae] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcover hxU)
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεball)]
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]
/-- Changing a set by parts of vanishing `n`-density at `x` does not change its approximate
tangent spaces at `x` (Simon Ch. 3, Definition 1.4 and Remark 1.5(2); proof of 3.1.6).  For
`f ∈ C_c(ℝᴾ)` with `|f| ≤ C`, `f = 0` off `B̄_R(0)` and `0 < r < r₀/R`, comparing both blow-up
integrals with the one over `η_{x,r}(A ∩ B)` gives `|∫_{η_{x,r}(A)} f dHⁿ − ∫_{η_{x,r}(B)} f dHⁿ| ≤
C Hⁿ(η_{x,r}(A \ B) ∩ B̄_R(0)) + C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`, and
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`. -/
theorem Submission.doraggt_approxTangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → 0 < r₀ → μHE[n] (A ∩ closedBall x r₀) ≠ ∞ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((A \ B) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n A B x r₀ hA hB hr₀ hAfin hBfin hAB hBA
  -- Step 1: it suffices that `∫_{η_r(A)} f − ∫_{η_r(B)} f → 0` for every `f ∈ C_c`
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n A B x fun f => ?_
  -- Step 2: `|f| ≤ C`, and `f = 0` off `B̄_R(0)` for some `R > 0`
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R, hR, hzero⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
      f.hasCompactSupport.isCompact.isBounded
    exact ⟨max R₁ 1, lt_max_of_lt_right one_pos, fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (closedBall_subset_closedBall (le_max_left _ _) (hR₁ h))⟩
  -- Step 3: for `0 < r < r₀ / R`, `Hⁿ(η_r(S) ∩ B̄_R(0)) ≤ r⁻ⁿ Hⁿ(S ∩ B̄_{r₀}(x)) < ∞`
  have hfin : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall x r₀) ≠ ∞ → ∀ r ∈ Ioo 0 (r₀ / R),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) ≠ ∞ := by
    intro S hS r hr
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr.1).ne'))
      (ne_top_of_le_ne_top hS (measure_mono (inter_subset_inter_right _
        (closedBall_subset_closedBall ((lt_div_iff₀ hR).mp hr.2).le))))
  -- Step 4: `C Hⁿ(η_r(S) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`
  have herr : ∀ S : Set (Euclid P),
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun r : ℝ => C *
        (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
        (𝓝[>] 0) (𝓝 0) := by
    intro S hS
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ => μHE[n] (S ∩ closedBall x ρ)) R hR hS)).const_mul C
    rw [ENNReal.toReal_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Function.comp_apply, Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr]
  -- Step 5: for `0 < r < r₀ / R`, compare both integrals with the one over `η_r(A ∩ B)`
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]‖ ≤
        C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A \ B) ∩
            closedBall 0 R)).toReal +
          C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩
            closedBall 0 R)).toReal := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
    have hA' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) A x r R C f
      f.continuous (hA.inter hB) hA inter_subset_left hr.1 (hfin A hAfin r hr) hC hzero
    have hB' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) B x r R C f
      f.continuous (hA.inter hB) hB inter_subset_right hr.1 (hfin B hBfin r hr) hC hzero
    rw [Set.sdiff_self_inter] at hA'
    rw [Set.sdiff_inter_self_eq_sdiff] at hB'
    rw [← sub_sub_sub_cancel_right _ _
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ B), f y ∂μHE[n])]
    exact (norm_sub_le _ _).trans (add_le_add hA' hB')
  -- Step 6: squeeze
  have hlim := (herr _ hAB).add (herr _ hBA)
  rw [add_zero] at hlim
  exact squeeze_zero_norm' hle hlim

/-- **Approximate tangent planes of two locally finite sets agree a.e. on their overlap** (Simon
Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 "⇒", chapter-03.txt lines 86–90 and 113–146,
stated symmetrically for two sets).  Let `W ⊆ ℝᴾ` be open and `A`, `B` Borel with `Hⁿ(A ∩ K)` and
`Hⁿ(B ∩ K)` finite for every compact `K ⊆ W`.  By the upper density theorem the densities of
`A ∖ B` and `B ∖ A` vanish at `Hⁿ`-a.e. `x ∈ W ∩ A ∩ B`; a closed ball about such `x` inside `W`
has finite measure in `A` and in `B`, so `A` and `B` have the same approximate tangent planes at
`x`. -/
theorem Submission.doraggt_ae_approxTangent_transfer : ∀ (P n : ℕ) (W A B : Set (Euclid P)), IsOpen W → MeasurableSet A → MeasurableSet B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (A ∩ K) ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ W → x ∈ A → x ∈ B → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n W A B hW hA hB hAfin hBfin
  -- Step 1, the densities of `A ∖ B` and `B ∖ A` vanish `Hⁿ`-a.e. on `W` off these sets.
  have hAB := Submission.doraggt_local_density_zero P n W (A \ B) hW (hA.diff hB)
    fun K hK hKW => ne_top_of_le_ne_top (hAfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  have hBA := Submission.doraggt_local_density_zero P n W (B \ A) hW (hB.diff hA)
    fun K hK hKW => ne_top_of_le_ne_top (hBfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 2, at such `x ∈ W ∩ A ∩ B`, `x ∉ A ∖ B` and `x ∉ B ∖ A`, so both densities vanish.
  filter_upwards [hAB, hBA] with x hxAB hxBA hxW hxA hxB
  -- Step 3, `B̄(x, ε/2) ⊆ B(x, ε) ⊆ W` is compact, so `A` and `B` have finite measure in it.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  have hsub : closedBall x (ε / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Step 4, the approximate tangent planes of `A` and `B` at `x` agree.
  exact Submission.doraggt_approxTangent_iff_of_density_zero P n A B x (ε / 2) hA hB
    (half_pos hε) (hAfin _ (isCompact_closedBall x (ε / 2)) hsub)
    (hBfin _ (isCompact_closedBall x (ε / 2)) hsub) (hxAB hxW fun h => h.2 hxB)
    (hxBA hxW fun h => h.2 hxA)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
