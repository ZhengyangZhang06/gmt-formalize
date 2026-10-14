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

/-- Uniqueness of planes in the proof of Simon 7.3.3(1) (p. 191: `spt S₀` lies in finitely many
2-planes `Pᵢ` with `Pᵢ ∩ Pⱼ = {0}`): linear subspaces `Q₁, Q₂` of `ℝᴾ` that agree on a ball
`B_t(x)`, `t > 0`, about a point `x ∈ Q₁` are equal.  First, `x ∈ Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x)`
gives `x ∈ Q₂`.  For `v ∈ Q₁` and `s = t / (2(|v| + 1)) > 0` we have `|s v| < t`, so `x + s v`
lies in `Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x)`; hence `s v ∈ Q₂` and `v ∈ Q₂`.  Exchanging `Q₁` and `Q₂`,
antisymmetry gives `Q₁ = Q₂`. -/
theorem Submission.idtp_tdc_csfp_subspace_eq_of_inter_ball : ∀ (P : ℕ) (Q₁ Q₂ : Submodule ℝ (Euclid P)) (x : Euclid P) (t : ℝ), x ∈ Q₁ → 0 < t → (Q₁ : Set (Euclid P)) ∩ ball x t = (Q₂ : Set (Euclid P)) ∩ ball x t → Q₁ = Q₂ := by
  intro P Q₁ Q₂ x t hx ht h
  -- Step 1: `x ∈ Q₁ ∩ B_t(x) = Q₂ ∩ B_t(x)`, so `x ∈ Q₂`
  have hx₂ : x ∈ Q₂ := by
    have hx' : x ∈ (Q₁ : Set (Euclid P)) ∩ ball x t := ⟨hx, mem_ball_self ht⟩
    rw [h] at hx'
    exact hx'.1
  -- Step 2: if `x ∈ A`, `x ∈ B` and `A ∩ B_t(x) = B ∩ B_t(x)`, then `A ≤ B`
  have key : ∀ A B : Submodule ℝ (Euclid P), x ∈ A → x ∈ B →
      (A : Set (Euclid P)) ∩ ball x t = (B : Set (Euclid P)) ∩ ball x t → A ≤ B := by
    intro A B hxA hxB hAB v hv
    -- `s := t / (2(|v| + 1)) > 0` has `s |v| ≤ s (|v| + 1) = t / 2 < t`
    obtain ⟨s, hs, hsv⟩ : ∃ s : ℝ, 0 < s ∧ s * ‖v‖ < t := by
      refine ⟨t / (2 * (‖v‖ + 1)), by positivity, ?_⟩
      calc t / (2 * (‖v‖ + 1)) * ‖v‖ ≤ t / (2 * (‖v‖ + 1)) * (‖v‖ + 1) := by gcongr; linarith
        _ = t / 2 := by field_simp
        _ < t := half_lt_self ht
    -- `y := x + s v ∈ A ∩ B_t(x) = B ∩ B_t(x)`, so `s v = y − x ∈ B` and `v = s⁻¹ (s v) ∈ B`
    have hy : x + s • v ∈ (A : Set (Euclid P)) ∩ ball x t := ⟨A.add_mem hxA (A.smul_mem s hv), by
      rwa [mem_ball, dist_self_add_left, norm_smul_of_nonneg hs.le]⟩
    rw [hAB] at hy
    exact (B.smul_mem_iff hs.ne').1 ((B.add_mem_iff_right hxB).1 hy.1)
  -- Step 3: `Q₁ ≤ Q₂` and `Q₂ ≤ Q₁`
  exact le_antisymm (key Q₁ Q₂ hx hx₂ h) (key Q₂ Q₁ hx₂ hx h.symm)

/-- Propagation along the great circle in the proof of Simon 7.3.3(1) (p. 191: `spt S₀` lies in
finitely many 2-planes `Pᵢ` with `Pᵢ ∩ Pⱼ = {0}`): if a closed set `S ⊆ ℝᴾ` is a 2-plane near each
of its nonzero points and agrees with the 2-plane `Q` near one unit vector `x₀ ∈ Q`, then `S`
agrees with `Q` near every unit vector of `Q`.  The great circle `K = Q ∩ 𝕊` is preconnected: two
non-antipodal points of `K` lie on the radial projection of the segment joining them, which
avoids `0`, and antipodal points are joined through a third unit vector of `Q` (`dim Q = 2`).  The
set `A` of points near which `S` agrees with `Q` is open, contains `x₀`, and `A ∩ Q ⊆ S`.  A point
of `K` outside `A` has a ball free of `A ∩ Q`: off `S` because `S` is closed, and on `S` because
its local plane `Q' ≠ Q` would agree with `Q` near a point of `A ∩ Q`
(`idtp_tdc_csfp_subspace_eq_of_inter_ball`).  So the open sets `A` and `(closure (A ∩ Q))ᶜ`
would separate `K` unless `K ⊆ A`. -/
theorem Submission.idtp_tdc_csfp_great_circle_local_plane : ∀ (P : ℕ) (S : Set (Euclid P)) (Q : Submodule ℝ (Euclid P)) (x₀ : Euclid P) (ε₀ : ℝ), IsClosed S → (∀ p ∈ S, p ≠ 0 → ∃ (δ : ℝ) (Q' : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q' = 2 ∧ S ∩ ball p δ = (Q' : Set (Euclid P)) ∩ ball p δ) → Module.finrank ℝ Q = 2 → x₀ ∈ Q → ‖x₀‖ = 1 → 0 < ε₀ → S ∩ ball x₀ ε₀ = (Q : Set (Euclid P)) ∩ ball x₀ ε₀ → ∀ x : Euclid P, x ∈ Q → ‖x‖ = 1 → ∃ ε : ℝ, 0 < ε ∧ S ∩ ball x ε = (Q : Set (Euclid P)) ∩ ball x ε := by
  intro P S Q x₀ ε₀ hS hloc hQ hx₀Q hx₀ hε₀ hx₀ε₀
  -- Agreement of two sets on a set `U` persists on every `V ⊆ U`
  have hres : ∀ {T₁ T₂ U V : Set (Euclid P)}, V ⊆ U → T₁ ∩ U = T₂ ∩ U → T₁ ∩ V = T₂ ∩ V := by
    intro T₁ T₂ U V hVU h
    rw [← inter_eq_right.2 hVU, ← inter_assoc, h, inter_assoc]
  -- Step 1: the great circle `K = Q ∩ 𝕊` is preconnected
  set K : Set (Euclid P) := (Q : Set (Euclid P)) ∩ sphere 0 1
  have hx₀K : x₀ ∈ K := ⟨hx₀Q, mem_sphere_zero_iff_norm.2 hx₀⟩
  have hKconn : IsPreconnected K := by
    -- (i) `a, b ∈ K` with `a + b ≠ 0` lie on the arc `z ↦ z / |z|` of the segment `[a, b] ∌ 0`
    have harc : ∀ a ∈ K, ∀ b ∈ K, a + b ≠ 0 → ∃ t ⊆ K, a ∈ t ∧ b ∈ t ∧ IsPreconnected t := by
      rintro a ⟨haQ, ha⟩ b ⟨hbQ, hb⟩ hab
      rw [mem_sphere_zero_iff_norm] at ha hb
      -- `s a + t b = 0` with `s, t ≥ 0`, `s + t = 1` forces `s = t = 1 / 2` and `a + b = 0`
      have h0 : ∀ z ∈ segment ℝ a b, z ≠ 0 := by
        rintro _ ⟨s, t, hs, ht, hst, rfl⟩ h0
        have hts : s = t := by
          have h := congrArg norm (eq_neg_of_add_eq_zero_left h0)
          rwa [norm_neg, norm_smul, norm_smul, ha, hb, Real.norm_of_nonneg hs,
            Real.norm_of_nonneg ht, mul_one, mul_one] at h
        subst hts
        rw [← smul_add] at h0
        exact hab ((smul_eq_zero.1 h0).resolve_left (by linarith))
      refine ⟨(fun z => ‖z‖⁻¹ • z) '' segment ℝ a b, ?_,
        ⟨a, left_mem_segment ℝ a b, by simp [ha]⟩, ⟨b, right_mem_segment ℝ a b, by simp [hb]⟩,
        (convex_segment a b).isPreconnected.image _ ?_⟩
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨Q.smul_mem _ (Q.convex.segment_subset haQ hbQ hz), ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 (h0 z hz))]
      · exact (continuous_norm.continuousOn.inv₀ fun z hz => norm_ne_zero_iff.2 (h0 z hz)).smul
          continuousOn_id
    -- (ii) as `dim Q = 2 > 1 = dim ℝx₀`, some unit vector `w ∈ Q` is neither `x₀` nor `-x₀`
    obtain ⟨w, hwK, hw₁, hw₂⟩ : ∃ w ∈ K, x₀ + w ≠ 0 ∧ w + -x₀ ≠ 0 := by
      have hx₀0 : x₀ ≠ 0 := norm_ne_zero_iff.1 (by rw [hx₀]; exact one_ne_zero)
      obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Q, q ∉ Submodule.span ℝ {x₀} := by
        by_contra! h
        have h' := Submodule.finrank_mono (show Q ≤ Submodule.span ℝ {x₀} from h)
        rw [hQ, finrank_span_singleton hx₀0] at h'
        norm_num at h'
      have hq0 : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 fun h => hq (h ▸ Submodule.zero_mem _)
      have hw : ∀ c : ℝ, ‖q‖⁻¹ • q ≠ c • x₀ := fun c h => hq <| by
        rw [← smul_inv_smul₀ hq0 q, h]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₀))
      refine ⟨‖q‖⁻¹ • q, ⟨Q.smul_mem _ hqQ, ?_⟩, fun h => hw (-1) ?_, fun h => hw 1 ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hq0]
      · rw [neg_one_smul]
        exact eq_neg_of_add_eq_zero_right h
      · rw [one_smul]
        exact add_neg_eq_zero.1 h
    -- (iii) each `y ∈ K` is joined to `x₀` by one arc, or by two arcs through `w` if `y = -x₀`
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    by_cases hxy : x₀ + y = 0
    · obtain ⟨t₁, ht₁K, hx₀t₁, hwt₁, ht₁⟩ := harc x₀ hx₀K w hwK hw₁
      obtain ⟨t₂, ht₂K, hwt₂, hyt₂, ht₂⟩ :=
        harc w hwK y hy (by rwa [eq_neg_of_add_eq_zero_right hxy])
      exact ⟨t₁ ∪ t₂, union_subset ht₁K ht₂K, Or.inl hx₀t₁, Or.inr hyt₂,
        IsPreconnected.union w hwt₁ hwt₂ ht₁ ht₂⟩
    · exact harc x₀ hx₀K y hy hxy
  -- Step 2: the set `A` of points near which `S` agrees with `Q` is open
  set A : Set (Euclid P) :=
    {y | ∃ ε : ℝ, 0 < ε ∧ S ∩ ball y ε = (Q : Set (Euclid P)) ∩ ball y ε}
  have hAopen : IsOpen A := by
    refine Metric.isOpen_iff.2 fun y hy => ?_
    obtain ⟨ε, hε, hyε⟩ := hy
    refine ⟨ε, hε, fun y' hy' => ⟨ε - dist y' y, sub_pos.2 (mem_ball.1 hy'), ?_⟩⟩
    exact hres (ball_subset_ball' (sub_add_cancel _ _).le) hyε
  -- Step 3: `A ∩ Q ⊆ S`
  have hAQS : ∀ y ∈ A, y ∈ Q → y ∈ S := by
    rintro y ⟨ε, hε, hyε⟩ hyQ
    exact (hyε.ge ⟨hyQ, mem_ball_self hε⟩).1
  -- Step 4: a point of `K` outside `A` is not in `closure (A ∩ Q)`
  have hfar : ∀ x ∈ K, x ∉ A → x ∉ closure (A ∩ (Q : Set (Euclid P))) := by
    intro x hxK hxA hxcl
    rw [Metric.mem_closure_iff] at hxcl
    by_cases hxS : x ∈ S
    · -- (b) `S` is a plane `Q' ≠ Q` on `B_δ(x)`; for `y ∈ A ∩ Q` with `|x - y| < δ / 2`, `Q`
      -- and `Q'` agree with `S` on `B_τ(y)`, `τ = min(ε_y, δ / 2)`, so `Q = Q'`
      have hx0 : x ≠ 0 :=
        norm_ne_zero_iff.1 (by rw [mem_sphere_zero_iff_norm.1 hxK.2]; exact one_ne_zero)
      obtain ⟨δ, Q', hδ, -, hxδ⟩ := hloc x hxS hx0
      have hQ' : Q' ≠ Q := by
        rintro rfl
        exact hxA ⟨δ, hδ, hxδ⟩
      obtain ⟨y, ⟨⟨εy, hεy, hyεy⟩, hyQ⟩, hxy⟩ := hxcl (δ / 2) (half_pos hδ)
      obtain ⟨τ, hτ, hτy, hτδ⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ εy ∧ τ ≤ δ / 2 :=
        ⟨min εy (δ / 2), lt_min hεy (half_pos hδ), min_le_left _ _, min_le_right _ _⟩
      have hτx : ball y τ ⊆ ball x δ := ball_subset_ball' (by rw [dist_comm]; linarith)
      exact hQ' (Submission.idtp_tdc_csfp_subspace_eq_of_inter_ball P Q Q' y τ hyQ hτ
        ((hres (ball_subset_ball hτy) hyεy).symm.trans (hres hτx hxδ))).symm
    · -- (a) a ball around `x` misses the closed set `S ⊇ A ∩ Q`
      obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
      obtain ⟨y, ⟨hyA, hyQ⟩, hxy⟩ := hxcl r hr
      exact hrS (mem_ball'.2 hxy) (hAQS y hyA hyQ)
  -- Step 5: `A` and `(closure (A ∩ Q))ᶜ` are open and cover `K` (Step 4); both meet `K` if
  -- `K ⊄ A`, but no point of `K ∩ A ⊆ A ∩ Q` lies outside `closure (A ∩ Q)`
  have hKA : K ⊆ A := by
    intro x hxK
    by_contra hxA
    obtain ⟨z, hzK, hzA, hzv⟩ := hKconn A (closure (A ∩ (Q : Set (Euclid P))))ᶜ hAopen
      isClosed_closure.isOpen_compl (fun y hy => (em (y ∈ A)).imp id (hfar y hy))
      ⟨x₀, hx₀K, ε₀, hε₀, hx₀ε₀⟩ ⟨x, hxK, hfar x hxK hxA⟩
    exact hzv (subset_closure ⟨hzA, hzK.1⟩)
  -- Step 6: every unit vector of `Q` lies in `K ⊆ A`
  intro x hxQ hx
  exact hKA ⟨hxQ, mem_sphere_zero_iff_norm.2 hx⟩

/-- Two seeded 2-planes of a closed, locally planar set are equal or meet only in `0` (proof of
Simon 7.3.3(1), pp. 191–192: `spt S₀` lies in 2-planes `P₁, …, P_q` with `Pᵢ ∩ Pⱼ = {0}` for
`i ≠ j`).  Here `S ⊆ ℝᴾ` is closed and locally a 2-plane near each `p ∈ S ∖ {0}`, and
`S ∩ B_{δᵢ}(pᵢ) = Qᵢ ∩ B_{δᵢ}(pᵢ)` for 2-planes `Qᵢ` and unit vectors `pᵢ ∈ Qᵢ`.  If
`Q₁ ⊓ Q₂ ≠ ⊥`, normalise a nonzero common vector to a unit vector `u ∈ Q₁ ∩ Q₂`.  Propagating
local planarity along the great circles of `Q₁` and `Q₂` gives `S ∩ B_{εᵢ}(u) = Qᵢ ∩ B_{εᵢ}(u)`,
so `Q₁` and `Q₂` agree on `B_t(u)`, `t = min(ε₁, ε₂)`, whence `Q₁ = Q₂`. -/
theorem Submission.idtp_tdc_csfp_planes_eq_or_inf_bot : ∀ (P : ℕ) (S : Set (Euclid P)) (Q₁ Q₂ : Submodule ℝ (Euclid P)) (p₁ p₂ : Euclid P) (δ₁ δ₂ : ℝ), IsClosed S → (∀ p ∈ S, p ≠ 0 → ∃ (δ : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q = 2 ∧ S ∩ ball p δ = (Q : Set (Euclid P)) ∩ ball p δ) → Module.finrank ℝ Q₁ = 2 → Module.finrank ℝ Q₂ = 2 → p₁ ∈ Q₁ → ‖p₁‖ = 1 → 0 < δ₁ → S ∩ ball p₁ δ₁ = (Q₁ : Set (Euclid P)) ∩ ball p₁ δ₁ → p₂ ∈ Q₂ → ‖p₂‖ = 1 → 0 < δ₂ → S ∩ ball p₂ δ₂ = (Q₂ : Set (Euclid P)) ∩ ball p₂ δ₂ → Q₁ = Q₂ ∨ Q₁ ⊓ Q₂ = ⊥ := by
  intro P S Q₁ Q₂ p₁ p₂ δ₁ δ₂ hS hloc hQ₁ hQ₂ hp₁ hp₁n hδ₁ hS₁ hp₂ hp₂n hδ₂ hS₂
  -- if `Q₁ ⊓ Q₂ ≠ ⊥`, there is a nonzero `v ∈ Q₁ ∩ Q₂`
  rcases eq_or_ne (Q₁ ⊓ Q₂) ⊥ with hbot | hbot
  · exact Or.inr hbot
  refine Or.inl ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hbot
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.1 hv
  -- `u = |v|⁻¹ v` is a common unit vector
  obtain ⟨u, hu₁, hu₂, hun⟩ : ∃ u : Euclid P, u ∈ Q₁ ∧ u ∈ Q₂ ∧ ‖u‖ = 1 :=
    ⟨‖v‖⁻¹ • v, Q₁.smul_mem _ hv₁, Q₂.smul_mem _ hv₂, by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]⟩
  -- along the great circles through `p₁` and `p₂`, `S` is locally `Q₁` and locally `Q₂` at `u`
  obtain ⟨ε₁, hε₁, h₁⟩ := Submission.idtp_tdc_csfp_great_circle_local_plane P S Q₁ p₁ δ₁ hS hloc
    hQ₁ hp₁ hp₁n hδ₁ hS₁ u hu₁ hun
  obtain ⟨ε₂, hε₂, h₂⟩ := Submission.idtp_tdc_csfp_great_circle_local_plane P S Q₂ p₂ δ₂ hS hloc
    hQ₂ hp₂ hp₂n hδ₂ hS₂ u hu₂ hun
  -- so `Q₁ ∩ B_t(u) = S ∩ B_t(u) = Q₂ ∩ B_t(u)` for `t = min(ε₁, ε₂)`, and `Q₁ = Q₂`
  obtain ⟨t, ht, ht₁, ht₂⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε₁ ∧ t ≤ ε₂ :=
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, min_le_left _ _, min_le_right _ _⟩
  have hshrink : ∀ (A : Set (Euclid P)) (ε : ℝ), t ≤ ε → A ∩ ball u ε ∩ ball u t = A ∩ ball u t :=
    fun A ε hε => by rw [inter_assoc, inter_eq_right.2 (ball_subset_ball hε)]
  refine Submission.idtp_tdc_csfp_subspace_eq_of_inter_ball P Q₁ Q₂ u t hu₁ ht ?_
  calc (Q₁ : Set (Euclid P)) ∩ ball u t = (Q₁ : Set (Euclid P)) ∩ ball u ε₁ ∩ ball u t :=
        (hshrink _ _ ht₁).symm
    _ = S ∩ ball u ε₁ ∩ ball u t := by rw [h₁]
    _ = S ∩ ball u t := hshrink _ _ ht₁
    _ = S ∩ ball u ε₂ ∩ ball u t := (hshrink _ _ ht₂).symm
    _ = (Q₂ : Set (Euclid P)) ∩ ball u ε₂ ∩ ball u t := by rw [h₂]
    _ = (Q₂ : Set (Euclid P)) ∩ ball u t := hshrink _ _ ht₂

/-- Finitely many planes in the proof of Simon 7.3.3(1) (p. 191: `spt S₀` lies in 2-planes
`P₁, …, P_q` with `Pᵢ ∩ Pⱼ = {0}` for `i ≠ j`): a closed dilation-invariant set `S ⊆ ℝᴾ` that is
a 2-plane near each `p ∈ S ∖ {0}` has `S ∖ {0}` inside finitely many 2-planes meeting pairwise
only in `0`.  Choose `δ_p`, `Q_p` with `S ∩ B_{δ_p}(p) = Q_p ∩ B_{δ_p}(p)` (so `p ∈ Q_p`).  The
link `Σ = S ∩ 𝕊` is compact, so finitely many balls `B_{δ_p}(p)`, `p ∈ F ⊆ Σ`, cover it; enumerate
the finite set `{Q_p : p ∈ F}` injectively.  Distinct planes of it meet only in `0`
(`idtp_tdc_csfp_planes_eq_or_inf_bot`).  For `x ∈ S ∖ {0}`, `x̂ = |x|⁻¹ x ∈ Σ` by dilation
invariance; it lies in some `S ∩ B_{δ_p}(p) = Q_p ∩ B_{δ_p}(p)`, `p ∈ F`, so `x = |x| x̂ ∈ Q_p`. -/
theorem Submission.idtp_tdc_cone_set_finite_planes : ∀ (P : ℕ) (S : Set (Euclid P)), IsClosed S → (∀ x ∈ S, ∀ s : ℝ, 0 < s → s • x ∈ S) → (∀ p ∈ S, p ≠ 0 → ∃ (δ : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q = 2 ∧ S ∩ ball p δ = (Q : Set (Euclid P)) ∩ ball p δ) → ∃ (q : ℕ) (Ps : Fin q → Submodule ℝ (Euclid P)), (∀ i, Module.finrank ℝ (Ps i) = 2) ∧ (∀ i j, i ≠ j → Ps i ⊓ Ps j = ⊥) ∧ ∀ x ∈ S, x ≠ 0 → ∃ i, x ∈ Ps i := by
  intro P S hS hdil hloc
  classical
  -- Step 1: a radius `δ p` and a plane `Q p` with `S ∩ B_{δ p}(p) = Q p ∩ B_{δ p}(p)` for every
  -- `p ∈ S ∖ {0}`; then `p ∈ Q p`
  have hloc' := hloc
  choose! δ Q hδ hQ hSQ using hloc'
  have hpQ : ∀ p ∈ S, p ≠ 0 → p ∈ Q p := by
    intro p hp hp0
    have h : p ∈ S ∩ ball p (δ p) := ⟨hp, mem_ball_self (hδ p hp hp0)⟩
    rw [hSQ p hp hp0] at h
    exact h.1
  -- Step 2: the link `L = S ∩ 𝕊` is compact and consists of nonzero unit vectors of `S`
  set L : Set (Euclid P) := S ∩ sphere 0 1
  have hLc : IsCompact L := (isCompact_sphere 0 1).inter_left hS
  have hL : ∀ p ∈ L, p ∈ S ∧ p ≠ 0 ∧ ‖p‖ = 1 := by
    rintro p ⟨hp, hp1⟩
    rw [mem_sphere_zero_iff_norm] at hp1
    exact ⟨hp, norm_ne_zero_iff.1 (by rw [hp1]; exact one_ne_zero), hp1⟩
  -- Step 3: finitely many balls `B_{δ p}(p)`, `p ∈ F ⊆ L`, cover `L`
  obtain ⟨F, hFL, hcov⟩ := hLc.elim_nhds_subcover (fun p => ball p (δ p))
    fun p hp => ball_mem_nhds p (hδ p (hL p hp).1 (hL p hp).2.1)
  -- Step 4: enumerate the finite set of planes `{Q p : p ∈ F}` injectively by `Fin q`
  set planes : Finset (Submodule ℝ (Euclid P)) := F.image Q
  have hplanes : ∀ R ∈ planes, ∃ p ∈ L, Q p = R := by
    intro R hR
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hR
    exact ⟨p, hFL p hp, rfl⟩
  refine ⟨planes.card, fun i => planes.equivFin.symm i, fun i => ?_, fun i j hij => ?_,
    fun x hx hx0 => ?_⟩
  · -- each plane is some `Q p`, `p ∈ L`, of dimension 2
    obtain ⟨p, hp, hpR⟩ := hplanes _ (planes.equivFin.symm i).2
    show Module.finrank ℝ (planes.equivFin.symm i : Submodule ℝ (Euclid P)) = 2
    rw [← hpR]
    exact hQ p (hL p hp).1 (hL p hp).2.1
  · -- distinct planes `Q p ≠ Q p'` meet only in `0`
    obtain ⟨p, hp, hpR⟩ := hplanes _ (planes.equivFin.symm i).2
    obtain ⟨p', hp', hp'R⟩ := hplanes _ (planes.equivFin.symm j).2
    obtain ⟨hpS, hp0, hp1⟩ := hL p hp
    obtain ⟨hp'S, hp'0, hp'1⟩ := hL p' hp'
    show (planes.equivFin.symm i : Submodule ℝ (Euclid P)) ⊓ planes.equivFin.symm j = ⊥
    rw [← hpR, ← hp'R]
    refine (Submission.idtp_tdc_csfp_planes_eq_or_inf_bot P S (Q p) (Q p') p p' (δ p) (δ p') hS
      hloc (hQ p hpS hp0) (hQ p' hp'S hp'0) (hpQ p hpS hp0) hp1 (hδ p hpS hp0) (hSQ p hpS hp0)
      (hpQ p' hp'S hp'0) hp'1 (hδ p' hp'S hp'0) (hSQ p' hp'S hp'0)).resolve_left fun h => hij ?_
    exact planes.equivFin.symm.injective (Subtype.ext (hpR.symm.trans (h.trans hp'R)))
  · -- `x̂ = |x|⁻¹ x ∈ L` lies in a ball `B_{δ p}(p)`, `p ∈ F`, so `x̂ ∈ Q p` and `x = |x| x̂ ∈ Q p`
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hxL : ‖x‖⁻¹ • x ∈ L := ⟨hdil x hx _ (inv_pos.2 hxn), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']⟩
    obtain ⟨p, hpF, hxp⟩ := mem_iUnion₂.1 (hcov hxL)
    obtain ⟨hpS, hp0, -⟩ := hL p (hFL p hpF)
    have hxQ : ‖x‖⁻¹ • x ∈ Q p := by
      have h : ‖x‖⁻¹ • x ∈ S ∩ ball p (δ p) := ⟨hxL.1, hxp⟩
      rw [hSQ p hpS hp0] at h
      exact h.1
    have hxQ' : x ∈ Q p := by
      have h := (Q p).smul_mem ‖x‖ hxQ
      rwa [smul_inv_smul₀ hxn.ne'] at h
    have hQp : Q p ∈ planes := Finset.mem_image_of_mem Q hpF
    refine ⟨planes.equivFin ⟨Q p, hQp⟩, ?_⟩
    show x ∈ (planes.equivFin.symm (planes.equivFin ⟨Q p, hQp⟩) : Submodule ℝ (Euclid P))
    rw [Equiv.symm_apply_apply]
    exact hxQ'

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
