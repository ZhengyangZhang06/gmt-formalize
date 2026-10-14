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

/-- **A `C¹` immersion is locally injective.**  If `G : ℝᵐ → ℝᴾ` is `C¹` and `DG(x)` is injective,
then for some `r > 0` the map `G` and every `DG(z)`, `z ∈ B̄_r(x)`, are injective.  `L = DG(x)` is
anti-Lipschitz on the finite-dimensional `ℝᵐ`, `c ‖v‖ ≤ ‖L v‖` with `c > 0`, and continuity of
`DG` gives `‖DG(z) - L‖ ≤ c/2` on `B̄_r(x)`.  If `DG(z) u = 0` then
`c ‖u‖ ≤ ‖L u‖ = ‖(DG(z) - L) u‖ ≤ (c/2) ‖u‖`; if `G a = G b`, the mean value inequality
`‖G a - G b - L (a - b)‖ ≤ (c/2) ‖a - b‖` gives `c ‖a - b‖ ≤ (c/2) ‖a - b‖`.  So `u = 0`, `a = b`. -/
theorem Submission.dor_lmbsf_c1c_immersion_local_injOn : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G x) → ∃ r : ℝ, 0 < r ∧ Set.InjOn G (Metric.closedBall x r) ∧ ∀ z ∈ Metric.closedBall x r, Function.Injective (fderiv ℝ G z) := by
  intro P m G x hG hx
  set L : Euclid m →L[ℝ] Euclid P := fderiv ℝ G x
  -- `L` is injective on the finite-dimensional `ℝᵐ`, hence anti-Lipschitz: `c ‖v‖ ≤ ‖L v‖`
  obtain ⟨K, hKpos, hK⟩ :=
    (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hx)
  have hK' : (0 : ℝ) < K := hKpos
  set c : ℝ := (K : ℝ)⁻¹
  have hcpos : 0 < c := inv_pos.2 hK'
  have hLc : ∀ v, c * ‖v‖ ≤ ‖L v‖ := fun v =>
    (inv_mul_le_iff₀ hK').2 (L.bound_of_antilipschitz hK v)
  -- continuity of `DG` gives `δ > 0` with `‖DG(z) - L‖ ≤ c/2` on `B̄_{δ/2}(x)`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuous_iff.1 (hG.continuous_fderiv one_ne_zero) x (c / 2) (half_pos hcpos)
  have hbound : ∀ z ∈ closedBall x (δ / 2), ‖fderiv ℝ G z - L‖ ≤ c / 2 := by
    intro z hz
    have h := hδ z (lt_of_le_of_lt (mem_closedBall.1 hz) (half_lt_self hδpos))
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨δ / 2, half_pos hδpos, ?_, ?_⟩
  · -- mean value inequality: `‖G a - G b - L (a - b)‖ ≤ (c/2) ‖a - b‖`
    intro a ha b hb hab
    have hmvt := (convex_closedBall x (δ / 2)).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => (hG.differentiable one_ne_zero) z) hbound hb ha
    rw [hab, sub_self, zero_sub, norm_neg] at hmvt
    have h1 := hLc (a - b)
    have h2 : ‖a - b‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  · -- if `DG(z) u = 0` then `c ‖u‖ ≤ ‖L u‖ = ‖(DG(z) - L) u‖ ≤ (c/2) ‖u‖`
    intro z hz v w hvw
    have hu : fderiv ℝ G z (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 := hLc (v - w)
    have h2 : ‖L (v - w)‖ ≤ c / 2 * ‖v - w‖ := by
      have h3 : L (v - w) = -((fderiv ℝ G z - L) (v - w)) := by
        rw [sub_apply, hu, zero_sub, neg_neg]
      rw [h3, norm_neg]
      calc ‖(fderiv ℝ G z - L) (v - w)‖ ≤ ‖fderiv ℝ G z - L‖ * ‖v - w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ c / 2 * ‖v - w‖ := by gcongr; exact hbound z hz
    have h4 : ‖v - w‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h4)
/-- **A `C¹` chart on a ball** (Simon Ch. 3, proof of Lemma 1.2, step 5): if `G : ℝᵐ → ℝᴾ` is
`C¹`, injective on `B̄_r(x)` and has injective derivative on `B_r(x)`, then `G(B_r(x))` is an
embedded `m`-dimensional `C¹` submanifold.  Every point is charted by `ψ = G` on `V = B_r(x)`
with `W = ℝᴾ \ G(∂B_r(x))`: `W` is open because the sphere is compact; injectivity on `B̄_r(x)`
gives `G(B_r(x)) ⊆ W`, so `ψ(V) = W ∩ G(B_r(x))`; and for compact `K ⊆ W`, sphere points map
outside `K`, so `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is compact. -/
theorem Submission.dor_lmbsf_c1c_injOn_closedBall_chart : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m) (r : ℝ), ContDiff ℝ 1 G → Set.InjOn G (Metric.closedBall x r) → (∀ z ∈ Metric.ball x r, Function.Injective (fderiv ℝ G z)) → IsEmbeddedSubmanifold 1 m (G '' Metric.ball x r) := by
  intro P m G x r hG hinj hD
  -- `W = ℝᴾ \ G(∂B_r(x))` is open: the sphere is compact and `G` is continuous
  have hW : IsOpen (G '' Metric.sphere x r)ᶜ :=
    ((isCompact_sphere x r).image hG.continuous).isClosed.isOpen_compl
  -- `G(B_r(x)) ⊆ W`: `G` is injective on `B̄_r(x)` and the sphere misses the open ball
  have hNW : G '' Metric.ball x r ⊆ (G '' Metric.sphere x r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩ ⟨s, hs, hsv⟩
    have hsv' : s = v :=
      hinj (Metric.sphere_subset_closedBall hs) (Metric.ball_subset_closedBall hv) hsv
    subst hsv'
    exact (Metric.mem_ball.1 hv).ne (Metric.mem_sphere.1 hs)
  -- the same chart `(V, W, ψ) = (B_r(x), W, G)` serves every point of `G(B_r(x))`
  intro y hy
  refine ⟨Metric.ball x r, (G '' Metric.sphere x r)ᶜ, G, Metric.isOpen_ball, hW, hNW hy, ?_,
    hinj.mono Metric.ball_subset_closedBall, (Set.inter_eq_right.2 hNW).symm, ?_, hD⟩
  · exact_mod_cast hG.contDiffOn
  -- properness: for compact `K ⊆ W`, `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is compact
  · intro K hKW hK
    have hball : Metric.ball x r ∩ G ⁻¹' K = Metric.closedBall x r ∩ G ⁻¹' K := by
      refine Set.Subset.antisymm
        (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall) ?_
      rintro z ⟨hz, hzK⟩
      refine ⟨?_, hzK⟩
      rcases (Metric.mem_closedBall.1 hz).lt_or_eq with h | h
      · exact Metric.mem_ball.2 h
      · exact (hKW (Set.mem_preimage.1 hzK) ⟨z, Metric.mem_sphere.2 h, rfl⟩).elim
    rw [hball]
    exact (isCompact_closedBall x r).inter_right (hK.isClosed.preimage hG.continuous)
/-- **A Lipschitz map `ℝᵐ → ℝᴾ` agrees with countably many `C¹` maps off a set with `Hᵐ`-null
image** (Simon Ch. 3, proof of Lemma 1.2), given the scalar `C¹` approximation (H) of Ch. 2,
Theorem 1.5.  Apply (H) to each `K`-Lipschitz coordinate `Fᵖ` with `ε = 1/i` and put
`Gᵢ = (g_{ip})_p`, so `Lᵐ({F ≠ Gᵢ}) ≤ Σ_p Lᵐ({Fᵖ ≠ g_{ip}}) ≤ P/i`.  Hence `Z = ⋂ᵢ {F ≠ Gᵢ}` is
`Lᵐ`-null, `E = F(Z)` has `Hᵐ(E) ≤ Kᵐ Hᵐ(Z) = Kᵐ Lᵐ(Z) = 0`, and off `Z`, `F = Gᵢ` for some `i`. -/
theorem Submission.dor_lmbsf_c1c_lipschitz_range_c1_pieces : ∀ (P m : ℕ) (F : Euclid m → Euclid P) (K : NNReal), LipschitzWith K F → (∀ (u : Euclid m → ℝ) (L : NNReal), LipschitzWith L u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid m → ℝ, ContDiff ℝ 1 g ∧ volume {y | u y ≠ g y} < ε) → ∃ (E : Set (Euclid P)) (G : ℕ → Euclid m → Euclid P), μHE[m] E = 0 ∧ (∀ i, ContDiff ℝ 1 (G i)) ∧ Set.range F ⊆ E ∪ ⋃ i, Set.range (G i) := by
  intro P m F K hF H
  -- the coordinates `Fᵖ` are `K`-Lipschitz, since `|a_p| ≤ |a|`
  have hcoord : ∀ p : Fin P, LipschitzWith K fun y => F y p := by
    intro p
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    calc dist (F a p) (F b p) = ‖(F a - F b) p‖ := by
          rw [PiLp.sub_apply, Real.dist_eq, Real.norm_eq_abs]
      _ ≤ ‖F a - F b‖ := PiLp.norm_apply_le _ _
      _ = dist (F a) (F b) := (dist_eq_norm _ _).symm
      _ ≤ K * dist a b := hF.dist_le_mul a b
  -- (H) for each coordinate with `ε = 1/i`: `Lᵐ({Fᵖ ≠ g_{ip}}) < 1/i`
  choose g hg hgvol using fun (i : ℕ) (p : Fin P) =>
    H (fun y => F y p) K (hcoord p) (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
  -- `Gᵢ = (g_{ip})_p` is `C¹`
  obtain ⟨G, hGp⟩ : ∃ G : ℕ → Euclid m → Euclid P, ∀ i y p, G i y p = g i p y :=
    ⟨fun i y => WithLp.toLp 2 fun p => g i p y, fun _ _ _ => rfl⟩
  have hGc : ∀ i, ContDiff ℝ 1 (G i) := fun i =>
    (contDiff_piLp 2).2 fun p => by simpa only [hGp] using hg i p
  -- `Z = ⋂ᵢ {F ≠ Gᵢ}`: `Lᵐ(Z) ≤ Lᵐ({F ≠ Gᵢ}) ≤ Σ_p Lᵐ({Fᵖ ≠ g_{ip}}) ≤ P/i`
  set Z : Set (Euclid m) := ⋂ i, {y | F y ≠ G i y} with hZ_def
  have hZi : ∀ i : ℕ, volume Z ≤ (P : ℝ≥0∞) * (i : ℝ≥0∞)⁻¹ := by
    intro i
    calc volume Z ≤ volume (⋃ p : Fin P, {y | F y p ≠ g i p y}) := by
          refine measure_mono fun y hy => ?_
          have hne : F y ≠ G i y := mem_iInter.1 hy i
          by_contra hcon
          simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
          exact hne (PiLp.ext fun p => by rw [hGp, hcon p])
      _ ≤ ∑ p : Fin P, volume {y | F y p ≠ g i p y} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : Fin P, (i : ℝ≥0∞)⁻¹ := Finset.sum_le_sum fun p _ => (hgvol i p).le
      _ = (P : ℝ≥0∞) * (i : ℝ≥0∞)⁻¹ := by simp
  -- `P/i → 0`, so `Lᵐ(Z) = 0`
  have hZ0 : volume Z = 0 := by
    have ht := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top P))
    rw [mul_zero] at ht
    exact le_antisymm (ge_of_tendsto' ht hZi) zero_le
  refine ⟨F '' Z, G, ?_, hGc, ?_⟩
  · -- `Hᵐ(F(Z)) ≤ Kᵐ Hᵐ(Z) = Kᵐ Lᵐ(Z) = 0`
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
      (hF.lipschitzOnWith (s := Z))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m, hZ0, mul_zero] at h
    exact le_antisymm h zero_le
  · -- `F z ∈ F(Z)` if `z ∈ Z`, otherwise `F z = Gᵢ z` for some `i`
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Z
    · exact Or.inl ⟨z, hz, rfl⟩
    · rw [hZ_def] at hz
      simp only [mem_iInter, mem_ofPred_eq, not_forall, not_not] at hz
      obtain ⟨i, hi⟩ := hz
      exact Or.inr (mem_iUnion.2 ⟨i, z, hi.symm⟩)
/-- **Simon Ch. 3, proof of Lemma 1.2 ("only if"), last paragraph**, for one `C¹` map
`G : ℝᵐ → ℝᴾ`: `G(ℝᵐ) ⊆ N₀ ∪ ⋃ₗ Nₗ` with `Hᵐ(N₀) = 0` and each `Nₗ` an embedded `C¹`
`m`-submanifold.  `N₀ = G({x : DG(x) not injective})` is `Hᵐ`-null (Simon: by the area formula of
Ch. 2 §3).  Here this is checked directly: if `DG(x) e = 0`, `|e| = 1`, and `‖DG - DG(x)‖ ≤ λM`,
`‖DG‖ ≤ M` on `B̄_ρ(x)`, then with `Ψ = id + (λ⁻¹ - 1) e ⊗ e` (`det Ψ = λ⁻¹`) the map `G ∘ Ψ` is
`2M`-Lipschitz on `Ψ⁻¹(B̄_ρ(x))`, so `Hᵐ(G(B̄_ρ(x))) ≤ (2M)ᵐ λ |B̄_ρ(x)|`; a Besicovitch disjoint
cover of the critical points in `B_R(0)` gives `Hᵐ(G(·)) ≤ (2M)ᵐ λ |B̄_{R+1}(0)|` for every `λ`.
At a regular point `x`, `G` is injective with injective derivative on some `B̄_{r_x}(x)`, so
`G(B_{r_x}(x))` is a submanifold; countably many of these balls cover the regular set (Lindelöf,
left implicit by Simon), and no ball is needed if it is empty. -/
theorem Submission.dor_lmbsf_c1c_c1_range_cover : ∀ (P m : ℕ) (G : Euclid m → Euclid P), ContDiff ℝ 1 G → ∃ (N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), μHE[m] N₀ = 0 ∧ (∀ l, IsEmbeddedSubmanifold 1 m (N l)) ∧ Set.range G ⊆ N₀ ∪ ⋃ l, N l := by
  intro P m G hG
  -- Step 1: `G` is differentiable everywhere, with continuous derivative.
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- Step 2: the critical image `N₀ = G({x : DG(x) not injective})` is `Hᵐ`-null.
  have hN₀ : μHE[m] (G '' {x | ¬ Injective (fderiv ℝ G x)}) = 0 := by
    have hvol : (μHE[m] : Measure (Euclid m)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
    have hcov : {x | ¬ Injective (fderiv ℝ G x)} =
        ⋃ k : ℕ, {x | ¬ Injective (fderiv ℝ G x)} ∩ ball (0 : Euclid m) k := by
      rw [← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hcov, image_iUnion]
    refine measure_iUnion_null fun k => ?_
    set R : ℝ := (k : ℝ)
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Euclid m) (R + 1)).exists_bound_of_continuousOn
      hDG.continuousOn
    set M : ℝ := max M₀ 1
    have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hMK : ∀ y ∈ closedBall (0 : Euclid m) (R + 1), ‖fderiv ℝ G y‖ ≤ M :=
      fun y hy => (hM₀ y hy).trans (le_max_left _ _)
    -- one ball `B̄_ρ(x)` around a critical point `x`
    have hloc : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ x, ¬ Injective (fderiv ℝ G x) → ∀ ρ : ℝ,
        (∀ y ∈ closedBall x ρ, ‖fderiv ℝ G y - fderiv ℝ G x‖ ≤ lam * M) →
        closedBall x ρ ⊆ closedBall 0 (R + 1) →
        μHE[m] (G '' closedBall x ρ) ≤
          ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam * volume (closedBall x ρ) := by
      intro lam hlam0 hlam1 x hx ρ hρ hρK
      obtain ⟨v, hv0, hv⟩ : ∃ v, fderiv ℝ G x v = 0 ∧ v ≠ 0 := by
        simpa only [injective_iff_map_eq_zero, not_forall, exists_prop] using hx
      set e : Euclid m := (‖v‖⁻¹ : ℝ) • v
      have he : ‖e‖ = 1 := norm_smul_inv_norm hv
      have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
      have hDe : fderiv ℝ G x e = 0 := by simp [e, hv0]
      set Ψ : Euclid m →L[ℝ] Euclid m :=
        ContinuousLinearMap.id ℝ _ + (lam⁻¹ - 1) • (innerSL ℝ e).smulRight e
      have hΨ : ∀ u, Ψ u = u + ((lam⁻¹ - 1) * inner ℝ e u) • e := by
        intro u
        simp [Ψ, smul_smul]
      -- `det Ψ = 1 + (λ⁻¹ - 1) |e|² = λ⁻¹` (matrix determinant lemma)
      have hdet : LinearMap.det (Ψ : Euclid m →ₗ[ℝ] Euclid m) = lam⁻¹ := by
        have hee' : e.ofLp ⬝ᵥ e.ofLp = 1 := by
          rw [← hee, EuclideanSpace.inner_eq_star_dotProduct]
          simp
        set b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        have hmat : LinearMap.toMatrix b b (Ψ : Euclid m →ₗ[ℝ] Euclid m) =
            1 + Matrix.replicateCol Unit ((lam⁻¹ - 1) • e.ofLp) * Matrix.replicateRow Unit e.ofLp := by
          ext i j
          simp [LinearMap.toMatrix_apply, b, hΨ, Matrix.one_apply, Matrix.mul_apply,
            EuclideanSpace.inner_single_right, PiLp.single_apply]
          ring
        rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_one_add_replicateCol_mul_replicateRow,
          dotProduct_smul, hee', smul_eq_mul, mul_one]
        ring
      have hsurj : Surjective Ψ := by
        intro y
        refine ⟨y + ((lam - 1) * inner ℝ e y) • e, ?_⟩
        have hcoef : (lam - 1) * inner ℝ e y +
            (lam⁻¹ - 1) * (inner ℝ e y + (lam - 1) * inner ℝ e y * 1) = 0 := by
          field_simp
          ring
        rw [hΨ, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul, hcoef, zero_smul,
          add_zero]
      -- `D(G ∘ Ψ) u = DG u + (λ⁻¹ - 1) ⟨e, u⟩ DG e` with `‖DG e‖ = ‖(DG - DG(x)) e‖ ≤ λM`
      have hLip : LipschitzOnWith (2 * M).toNNReal (G ∘ Ψ) (Ψ ⁻¹' closedBall x ρ) := by
        refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
          (fun z _ => (hGd (Ψ z)).comp z Ψ.differentiableAt) (fun z hz => ?_)
          ((convex_closedBall x ρ).linear_preimage (Ψ : Euclid m →ₗ[ℝ] Euclid m))
        have hy : Ψ z ∈ closedBall x ρ := hz
        rw [fderiv_comp z (hGd (Ψ z)) Ψ.differentiableAt, ContinuousLinearMap.fderiv,
          ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
        have h1 : ‖fderiv ℝ G (Ψ z) u‖ ≤ M * ‖u‖ :=
          ((fderiv ℝ G (Ψ z)).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right (hMK _ (hρK hy)) (norm_nonneg _))
        have h2 : ‖fderiv ℝ G (Ψ z) e‖ ≤ lam * M := by
          have h3 : fderiv ℝ G (Ψ z) e = (fderiv ℝ G (Ψ z) - fderiv ℝ G x) e := by
            rw [sub_apply, hDe, sub_zero]
          rw [h3]
          calc ‖(fderiv ℝ G (Ψ z) - fderiv ℝ G x) e‖
              ≤ ‖fderiv ℝ G (Ψ z) - fderiv ℝ G x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ lam * M := by rw [he, mul_one]; exact hρ _ hy
        have h4 : |lam⁻¹ - 1| ≤ lam⁻¹ := by
          have : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam0).2 hlam1
          rw [abs_of_nonneg (by linarith)]
          linarith
        have h5 : |inner ℝ e u| ≤ ‖u‖ := by
          simpa [he] using abs_real_inner_le_norm e u
        rw [ContinuousLinearMap.comp_apply, hΨ u, map_add, map_smul]
        calc ‖fderiv ℝ G (Ψ z) u + ((lam⁻¹ - 1) * inner ℝ e u) • fderiv ℝ G (Ψ z) e‖
            ≤ ‖fderiv ℝ G (Ψ z) u‖ + ‖((lam⁻¹ - 1) * inner ℝ e u) • fderiv ℝ G (Ψ z) e‖ :=
              norm_add_le _ _
          _ = ‖fderiv ℝ G (Ψ z) u‖ + |lam⁻¹ - 1| * |inner ℝ e u| * ‖fderiv ℝ G (Ψ z) e‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_mul]
          _ ≤ M * ‖u‖ + lam⁻¹ * ‖u‖ * (lam * M) := by gcongr
          _ = 2 * M * ‖u‖ := by
              rw [show lam⁻¹ * ‖u‖ * (lam * M) = (lam⁻¹ * lam) * (M * ‖u‖) by ring,
                inv_mul_cancel₀ hlam0.ne', one_mul]
              ring
      have hvolΨ : volume (Ψ ⁻¹' closedBall x ρ) = ENNReal.ofReal lam * volume (closedBall x ρ) := by
        rw [Measure.addHaar_preimage_continuousLinearMap volume
          (by rw [hdet]; exact inv_ne_zero hlam0.ne'), hdet, inv_inv, abs_of_pos hlam0]
      calc μHE[m] (G '' closedBall x ρ) = μHE[m] ((G ∘ Ψ) '' (Ψ ⁻¹' closedBall x ρ)) := by
            rw [image_comp, image_preimage_eq _ hsurj]
        _ ≤ ((2 * M).toNNReal : ℝ≥0∞) ^ m * μHE[m] (Ψ ⁻¹' closedBall x ρ) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hLip
        _ = ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam * volume (closedBall x ρ) := by
            rw [hvol, hvolΨ, mul_assoc]
    -- `G` is `M`-Lipschitz on `B̄_{R+1}(0)`, so it maps volume-null sets there to `Hᵐ`-null sets
    have hLipK : LipschitzOnWith M.toNNReal G (closedBall 0 (R + 1)) := by
      refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun y _ => hGd y)
        (fun y hy => ?_) (convex_closedBall _ _)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM.le]
      exact hMK y hy
    -- Besicovitch: disjoint balls `B̄_{ρ x}(x)` with `ρ x < r x` cover almost all critical points
    have hmain : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        μHE[m] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R)) ≤
          ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
            volume (closedBall (0 : Euclid m) (R + 1)) := by
      intro lam hlam0 hlam1
      have hr : ∀ x : Euclid m, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
          ∀ y ∈ ball x r, ‖fderiv ℝ G y - fderiv ℝ G x‖ < lam * M := by
        intro x
        obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hDG x (lam * M) (by positivity)
        refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun y hy => ?_⟩
        have h := hδ' y (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
        rwa [dist_eq_norm] at h
      choose r hr0 hr1 hr using hr
      obtain ⟨t, ρ, ht, hts, hρ, hnull, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae
        volume (fun _ => univ) ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R)
        (fun _ _ δ hδ => ⟨δ / 2, mem_univ _, half_pos hδ, half_lt_self hδ⟩) r (fun x _ => hr0 x)
      have hballK : ∀ x ∈ t, closedBall x (ρ x) ⊆ closedBall 0 (R + 1) := by
        intro x hx y hy
        have hx' : ‖x‖ < R := mem_ball_zero_iff.1 (hts hx).2
        rw [mem_closedBall, dist_eq_norm] at hy
        rw [mem_closedBall_zero_iff]
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith [(hρ x hx).2.2, hr1 x]
      have hsub : G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) ⊆
          G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \ ⋃ x ∈ t, closedBall x (ρ x)) ∪
            ⋃ x ∈ t, G '' closedBall x (ρ x) := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases hyU : y ∈ ⋃ x ∈ t, closedBall x (ρ x)
        · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
          exact Or.inr (mem_iUnion₂.2 ⟨x, hx, mem_image_of_mem G hyx⟩)
        · exact Or.inl (mem_image_of_mem G ⟨hy, hyU⟩)
      have h0 : μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
          ⋃ x ∈ t, closedBall x (ρ x))) = 0 := by
        refine le_antisymm ?_ bot_le
        calc μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
                ⋃ x ∈ t, closedBall x (ρ x)))
            ≤ (M.toNNReal : ℝ≥0∞) ^ m * μHE[m] (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
                ⋃ x ∈ t, closedBall x (ρ x)) :=
              Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
                (hLipK.mono fun y hy =>
                  closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy.1.2))
          _ = 0 := by rw [hvol, hnull, mul_zero]
      calc μHE[m] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R))
          ≤ μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
              ⋃ x ∈ t, closedBall x (ρ x))) + μHE[m] (⋃ x ∈ t, G '' closedBall x (ρ x)) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ∑' x : t, μHE[m] (G '' closedBall (x : Euclid m) (ρ x)) := by
            rw [h0, zero_add]
            exact measure_biUnion_le _ ht _
        _ ≤ ∑' x : t, ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (closedBall (x : Euclid m) (ρ x)) :=
            ENNReal.tsum_le_tsum fun x => hloc lam hlam0 hlam1 x (hts x.2).1 (ρ x)
              (fun y hy => (hr x y (closedBall_subset_ball (hρ x x.2).2.2 hy)).le) (hballK x x.2)
        _ = ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (⋃ x ∈ t, closedBall x (ρ x)) := by
            rw [ENNReal.tsum_mul_left, measure_biUnion ht hdisj fun _ _ => measurableSet_closedBall]
        _ ≤ ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (closedBall (0 : Euclid m) (R + 1)) := by
            gcongr
            exact iUnion₂_subset hballK
    -- let `λ → 0`
    have hlim : Tendsto (fun lam : ℝ => ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
        volume (closedBall (0 : Euclid m) (R + 1))) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun lam : ℝ => ENNReal.ofReal lam) (𝓝[>] 0) (𝓝 0) := by
        simpa using (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
          nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul h1
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))) (Or.inr measure_closedBall_lt_top.ne)
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Ioo_mem_nhdsGT one_pos] with lam hlam
    exact hmain lam hlam.1 hlam.2.le
  have hcrit : ∀ x, ¬ Injective (fderiv ℝ G x) → G x ∈ G '' {x | ¬ Injective (fderiv ℝ G x)} :=
    fun x hx => mem_image_of_mem G hx
  -- Step 3: at a regular point `x`, `G(B_{r_x}(x))` is an embedded `C¹` `m`-submanifold.
  have hchart : ∀ x : {x : Euclid m // Injective (fderiv ℝ G x)}, ∃ r : ℝ, 0 < r ∧
      IsEmbeddedSubmanifold 1 m (G '' ball (x : Euclid m) r) := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, hinj, hder⟩ := Submission.dor_lmbsf_c1c_immersion_local_injOn P m G x hG hx
    exact ⟨r, hr, Submission.dor_lmbsf_c1c_injOn_closedBall_chart P m G x r hG hinj
      fun z hz => hder z (ball_subset_closedBall hz)⟩
  choose r hr hN using hchart
  -- Step 4: with no regular point, `Nₗ = ∅` (vacuously a submanifold) and `G(ℝᵐ) ⊆ N₀`.
  rcases isEmpty_or_nonempty {x : Euclid m // Injective (fderiv ℝ G x)} with hR | hR
  · refine ⟨_, fun _ => ∅, hN₀, fun _ y hy => absurd hy (notMem_empty y), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Or.inl (hcrit x fun hx => hR.false ⟨x, hx⟩)
  -- Otherwise countably many balls `B_{r_{xₗ}}(xₗ)` cover the regular set (Lindelöf).
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof
    {x : Euclid m | Injective (fderiv ℝ G x)}).indexed_countable_subcover
    (fun x : {x : Euclid m // Injective (fderiv ℝ G x)} => ball (x : Euclid m) (r x))
    (fun _ => isOpen_ball) fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩
  refine ⟨_, fun l => G '' ball (f l : Euclid m) (r (f l)), hN₀, fun l => hN (f l), ?_⟩
  -- Step 5: `G(x) ∈ N₀` if `x` is critical, and `G(x) ∈ Nₗ` if `x ∈ B_{r_{xₗ}}(xₗ)`.
  rintro _ ⟨x, rfl⟩
  by_cases hx : Injective (fderiv ℝ G x)
  · obtain ⟨l, hl⟩ := mem_iUnion.mp
      (hf (show x ∈ {x : Euclid m | Injective (fderiv ℝ G x)} from hx))
    exact Or.inr (mem_iUnion.mpr ⟨l, mem_image_of_mem G hl⟩)
  · exact Or.inl (hcrit x hx)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
