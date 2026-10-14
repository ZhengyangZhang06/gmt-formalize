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

/-- **Faces of the unit cubical lattice** (Simon Ch. 6, §5: the `n`-faces `F ∈ 𝓛ₙ` used in the proof
of the deformation theorem 5.1).  Let `n = m + 1` and `p = (z, ι)` with `ι : Fin n → Fin P` strictly
increasing.  The map `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` has coordinates `z_{ι(k)} + y_k` at `ι(k)` and
`zᵢ` off `range ι`, so it is an isometric embedding `ℝⁿ → ℝᴾ` with `Φ_p⁻¹(F_p) = [0, 1]ⁿ` and
`F_p ⊆ range Φ_p`.  As `μHE[n] = volume` on `ℝⁿ`, `Φ_p#μHE[n] = μHE[n]⌞range Φ_p` and `∂[0, 1]ⁿ` is
Lebesgue-null, `Hⁿ⌞F_p = Φ_p#(Lⁿ⌞(0, 1)ⁿ)`; hence `Hⁿ(F_p) = 1` and
`∫_{F_p} f dHⁿ = ∫_{(0, 1)ⁿ} f ∘ Φ_p`.  `F_p` is closed with diameter `≤ √P`, and the non-integer
coordinates of a point of `Φ_p((0, 1)ⁿ)` determine `ι` and `z`, so it lies in no other face
`F_q`. -/
theorem Submission.dor_lmb_fcd_fr_face_geometry : ∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)), StrictMono p.2 → volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ μHE[m + 1] {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = 1 ∧ (μHE[m + 1] : Measure (Euclid P)).restrict {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = Measure.map (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∀ f : Euclid P → ℝ, ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, f x ∂μHE[m + 1] = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, f (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))) ∧ (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}) ∧ (∀ y y' : Euclid (m + 1), dist (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.2 j) (1 : ℝ)) = dist y y') ∧ (∀ x ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, ∀ x' ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, dist x x' ≤ Real.sqrt P) ∧ IsClosed {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∉ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧ (i ∉ Set.range q.2 → x i = q.1 i)} := by
  intro P m p hp
  -- the face map `Φ = Φ_p`, the closed face `F = F_p`, the open cube `Q = Q₁`, the closed cube `C`
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let F : Set (Euclid P) := {x : Euclid P | ∀ i : Fin P,
    (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}
  let Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  let C : Set (Euclid (m + 1)) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1}
  show volume Q = 1 ∧ μHE[m + 1] F = 1 ∧
    (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) ∧
    (∀ f : Euclid P → ℝ, ∫ x in F, f x ∂μHE[m + 1] = ∫ y in Q, f (Φ y)) ∧
    (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F) ∧
    (∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y') ∧
    (∀ x ∈ F, ∀ x' ∈ F, dist x x' ≤ Real.sqrt P) ∧ IsClosed F ∧
    ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p →
      ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → Φ y ∉ {x : Euclid P | ∀ i : Fin P,
        (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧
          (i ∉ Set.range q.2 → x i = q.1 i)}
  have hinj : Injective p.2 := hp.injective
  -- Step 1: coordinates of `Φ`
  have hcoord : ∀ y i, Φ y i = p.1 i + ∑ j, if i = p.2 j then y j else 0 := by
    intro y i
    simp [Φ, Pi.single_apply]
  have hcoord_mem : ∀ y k, Φ y (p.2 k) = p.1 (p.2 k) + y k := by
    intro y k
    rw [hcoord]
    simp [hinj.eq_iff]
  have hcoord_nmem : ∀ y i, i ∉ range p.2 → Φ y i = p.1 i := by
    intro y i hi
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hi ⟨j, h.symm⟩
  -- Step 2: `Φ` is an isometry, hence a measurable embedding
  have hdist : ∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y' := by
    intro y y'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    symm
    refine Fintype.sum_of_injective p.2 hinj _ _ (fun i hi => ?_) (fun k => ?_)
    · rw [hcoord_nmem y i hi, hcoord_nmem y' i hi, dist_self]
      simp
    · rw [hcoord_mem, hcoord_mem, dist_add_left]
  have hiso : Isometry Φ := Isometry.of_dist_eq hdist
  have hemb : MeasurableEmbedding Φ := hiso.isClosedEmbedding.measurableEmbedding
  -- Step 3: `Φ` maps the closed cube `C` into `F`, `F ⊆ range Φ` and `Φ⁻¹(F) = C`
  have hCF : ∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F := by
    intro y hy i
    constructor
    · rintro ⟨k, rfl⟩
      rw [hcoord_mem]
      constructor <;> linarith [(hy k).1, (hy k).2]
    · exact hcoord_nmem y i
  have hFrange : F ⊆ range Φ := by
    intro x hx
    refine ⟨WithLp.toLp 2 fun k => x (p.2 k) - p.1 (p.2 k), PiLp.ext fun i => ?_⟩
    by_cases hi : i ∈ range p.2
    · obtain ⟨k, rfl⟩ := hi
      rw [hcoord_mem]
      simp
    · rw [hcoord_nmem _ i hi]
      exact ((hx i).2 hi).symm
  have hpreF : Φ ⁻¹' F = C := by
    ext y
    refine ⟨fun hy k => ?_, hCF y⟩
    have h := (hy (p.2 k)).1 ⟨k, rfl⟩
    rw [hcoord_mem] at h
    constructor <;> linarith [h.1, h.2]
  -- Step 4: `volume Q = volume C = 1`
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  have hQ_eq : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hC_eq : C = WithLp.ofLp ⁻¹' (Set.Icc (0 : Fin (m + 1) → ℝ) 1) := by
    ext y
    simp [C, Pi.le_def, forall_and]
  have hQmeas : MeasurableSet Q := by
    rw [hQ_eq]
    exact hvol.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hvolQ : volume Q = 1 := by
    rw [hQ_eq, hvol.measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hvolC : volume C = 1 := by
    rw [hC_eq, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp
  have hQC : volume.restrict C = volume.restrict Q := by
    refine (Measure.restrict_congr_set ?_).symm
    refine ae_eq_of_subset_of_measure_ge (fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩)
      (hvolC.trans hvolQ.symm).le hQmeas.nullMeasurableSet ?_
    rw [hvolC]
    exact ENNReal.one_ne_top
  -- Step 5: `F` is closed
  have hcont : ∀ i : Fin P, Continuous fun x : Euclid P => x i := fun i =>
    PiLp.continuous_apply 2 _ i
  have hFclosed : IsClosed F := by
    have hF : F = ⋂ i : Fin P, {x : Euclid P | (i ∈ Set.range p.2 →
        (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} :=
      Set.ofPred_forall _
    rw [hF]
    refine isClosed_iInter fun i =>
      (isClosed_imp isOpen_const ?_).inter (isClosed_imp isOpen_const ?_)
    · exact (isClosed_le continuous_const (hcont i)).inter (isClosed_le (hcont i) continuous_const)
    · exact isClosed_eq (hcont i) continuous_const
  have hFmeas : MeasurableSet F := hFclosed.measurableSet
  -- Step 6: `Hⁿ⌞F = Φ#(volume⌞Q)`
  have hmeas :
      (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) := by
    have h1 : Measure.map Φ (volume : Measure (Euclid (m + 1))) =
        (μHE[m + 1] : Measure (Euclid P)).restrict (range Φ) := by
      rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rw [← hQC, ← hpreF, ← hemb.restrict_map, h1, Measure.restrict_restrict hFmeas,
      inter_eq_left.2 hFrange]
  -- Step 7: `Hⁿ(F) = 1`
  have hFmass : μHE[m + 1] F = 1 := by
    have h := congrArg (fun μ : Measure (Euclid P) => μ univ) hmeas
    simp only [Measure.restrict_apply_univ] at h
    rw [h, hemb.map_apply, preimage_univ, Measure.restrict_apply_univ, hvolQ]
  refine ⟨hvolQ, hFmass, hmeas, fun f => ?_, hCF, hdist, ?_, hFclosed, ?_⟩
  -- Step 8: the integral formula
  · rw [hmeas, hemb.integral_map]
  -- Step 9: `diam F ≤ √P`
  · intro x hx x' hx'
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (x i) (x' i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => pow_le_one₀ dist_nonneg ?_
          by_cases hi : i ∈ range p.2
          · have h := (hx i).1 hi
            have h' := (hx' i).1 hi
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [h.1, h.2, h'.1, h'.2]
          · rw [(hx i).2 hi, (hx' i).2 hi, dist_self]
            exact zero_le_one
      _ = P := by simp
  -- Step 10: the open face `Φ(Q)` meets no other closed face
  · intro q hq hqp y hy hx
    apply hqp
    have hsub : range p.2 ⊆ range q.2 := by
      rintro _ ⟨k, rfl⟩
      by_contra hk
      have h := (hx (p.2 k)).2 hk
      rw [hcoord_mem] at h
      have a1 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) := by linarith [(hy k).1]
      have a2 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [(hy k).2]
      have b1 : p.1 (p.2 k) < q.1 (p.2 k) := by exact_mod_cast a1
      have b2 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a2
      omega
    have hrange : range p.2 = range q.2 := by
      apply Set.eq_of_subset_of_card_le hsub
      rw [Set.card_range_of_injective hq.injective, Set.card_range_of_injective hinj]
    have h2 : p.2 = q.2 := (hp.range_inj_of_wellFoundedLT hq).1 hrange
    have h1 : p.1 = q.1 := by
      funext i
      by_cases hi : i ∈ range p.2
      · obtain ⟨k, rfl⟩ := hi
        have h := (hx (p.2 k)).1 (hrange ▸ ⟨k, rfl⟩)
        rw [hcoord_mem] at h
        have a1 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [h.1, (hy k).2]
        have a2 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) + 1 := by linarith [h.2, (hy k).1]
        have b1 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a1
        have b2 : p.1 (p.2 k) < q.1 (p.2 k) + 1 := by exact_mod_cast a2
        omega
      · have h : (p.1 i : ℝ) = q.1 i := by
          rw [← hcoord_nmem y i hi]
          exact (hx i).2 (hrange ▸ hi)
        exact_mod_cast h
    exact Prod.ext h1.symm h2.symm
/-- **A set that coincides near `x` with the plane `x + V` has approximate tangent space `V` at
`x`** (Simon Ch. 3, Definition 1.4).  A test function `f ∈ C_c(ℝᴾ)` vanishes off a ball `B_R(0)`,
so `∫_S f dHⁿ = ∫_{B_R(0) ∩ S} f dHⁿ` for every `S`.  For `0 < λ < r/R` the blow-up
`η_{x,λ}(N) = λ⁻¹(N − x)` coincides with `V` inside `B_R(0)`, hence the blow-up integrals equal
`∫_V f dHⁿ` for all small `λ > 0` and converge to it. -/
theorem Submission.dor_lmb_fcd_fr_local_plane_tangent : ∀ (P n : ℕ) (N : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (r : ℝ), Module.finrank ℝ V = n → 0 < r → (∀ y ∈ Metric.ball x r, y ∈ N ↔ y - x ∈ V) → HasApproximateTangentSpaceAt n N x V := by
  intro P n N x V r hV hr hN
  refine ⟨hV, fun f => ?_⟩
  -- Step 1: `f` vanishes off a ball `B_R(0)`
  obtain ⟨R, hR, hfR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ w, w ∉ ball (0 : Euclid P) R → f w = 0 := by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 f.hasCompactSupport.isCompact.isBounded
    refine ⟨max C 0 + 1, add_pos_of_nonneg_of_pos (le_max_right C 0) one_pos,
      fun w hw => image_eq_zero_of_notMem_tsupport fun hwt => hw ?_⟩
    rw [mem_ball_zero_iff]
    exact (hC w hwt).trans_lt ((le_max_left C 0).trans_lt (lt_add_one _))
  -- Step 2: the integral of `f` over any `S` only sees `B_R(0) ∩ S`
  have hB : MeasurableSet (ball (0 : Euclid P) R) := measurableSet_ball
  have hloc : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) R ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict hB, setIntegral_eq_integral_of_forall_compl_eq_zero hfR]
  -- Step 3: for `0 < λ < r/R` the blow-up of `N` coincides with `V` inside `B_R(0)`
  have hblow : ∀ lam ∈ Ioo 0 (r / R), ball (0 : Euclid P) R ∩
      Poincare.SimonGMT.Chapter03.blowUpMap x lam '' N =
        ball (0 : Euclid P) R ∩ (V : Set (Euclid P)) := by
    rintro lam ⟨hlam0, hlamR⟩
    have hsmall : ∀ w : Euclid P, ‖w‖ < R → ‖lam • w‖ < r := fun w hw => by
      rw [norm_smul, Real.norm_of_nonneg hlam0.le]
      exact (mul_lt_mul_of_pos_left hw hlam0).trans ((lt_div_iff₀ hR).1 hlamR)
    ext w
    constructor
    · rintro ⟨hw, y, hy, rfl⟩
      have hyx : y - x = lam • Poincare.SimonGMT.Chapter03.blowUpMap x lam y := by
        rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hlam0.ne',
          one_smul]
      have hy' : y ∈ ball x r := by
        rw [Metric.mem_ball, dist_eq_norm, hyx]
        exact hsmall _ (mem_ball_zero_iff.1 hw)
      exact ⟨hw, V.smul_mem lam⁻¹ ((hN y hy').1 hy)⟩
    · rintro ⟨hw, hwV⟩
      have hy : x + lam • w ∈ ball x r := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact hsmall w (mem_ball_zero_iff.1 hw)
      refine ⟨hw, x + lam • w, (hN _ hy).2 ?_, ?_⟩
      · rw [add_sub_cancel_left]
        exact V.smul_mem lam hwV
      · rw [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ hlam0.ne', one_smul]
  -- Step 4: the blow-up integrals are eventually equal to `∫_V f dHⁿ`
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr hR)] with lam hlam
  rw [hloc (V : Set (Euclid P)), hloc (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' N),
    hblow lam hlam]

/-- **Lattice chains are integer multiplicity** (Simon Ch. 6, proof of 5.1: "the fact that `P`,
`R` are integer multiplicity … should be evident").  Let `T(ω) = Σ_{p ∈ s} ∫_{Q₁} β_p
ω(Φ_p(y))(e_p) dy`, where `p = (z, ι)` has `ι` strictly increasing, `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}`,
`e_p = (e_{ι(0)}, …, e_{ι(m)})` and `Q₁ = (0, 1)ⁿ`.  Then `T = τ(N, θ, ξ)`, where `N` is the union
of the open faces `A_p = Φ_p(Q₁)` with `β_p ≠ 0`, `θ = |β_p|` and `ξ = sgn(β_p) e_p^*` on `A_p`
(`e_p^*(α) = α(e_p)`).  The face facts (`Φ_p` an isometry, `A_p ⊆ F_p` closed with `Hⁿ(F_p) = 1`,
`∫_{F_p} f dHⁿ = ∫_{Q₁} f ∘ Φ_p`, `A_p ∩ F_q = ∅` for `q ≠ p`) make the `A_p` disjoint Borel sets
of measure `≤ 1`, so `(N, θ, ξ)` is Borel, countably `n`-rectifiable and locally integrable; near
`x ∈ A_p`, `N` coincides with `x + V_p`, `V_p = span e_p` (the other faces are closed and miss
`x`), so `TₓN = V_p`, oriented by `±e_p`; and face by face its action is `T(ω)`. -/
theorem Submission.dor_lmb_fcd_fr_lattice_chain_im : ∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) → IsIntegerMultiplicity T := by
  intro P m s β T hmono hT
  classical
  -- Step 1: the face facts, in the notation `Q₁`, `Φ_p`, `F_p`, `e_p`
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q : Set (Euclid (m + 1)), Q = {y | ∀ i, 0 < y i ∧ y i < 1} := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Euclid (m + 1) → Euclid P,
      Φ = fun p y => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P),
      F = fun p => {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧
        x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Fin (m + 1) → Euclid P,
      e = fun p k => EuclideanSpace.single (p.2 k) (1 : ℝ) := ⟨_, rfl⟩
  have hFG := fun p (hp : p ∈ s) => Submission.dor_lmb_fcd_fr_face_geometry P m p (hmono p hp)
  have hFmeas : ∀ p ∈ s, μHE[m + 1] (F p) = 1 := fun p hp => by
    rw [hF]; exact (hFG p hp).2.1
  have hFint : ∀ p ∈ s, ∀ f : Euclid P → ℝ,
      ∫ x in F p, f x ∂μHE[m + 1] = ∫ y in Q₁, f (Φ p y) := fun p hp f => by
    rw [hF, hQ₁, hΦ]; exact (hFG p hp).2.2.2.1 f
  have hΦF : ∀ p ∈ s, ∀ y ∈ Q₁, Φ p y ∈ F p := fun p hp y hy => by
    rw [hQ₁] at hy
    rw [hF, hΦ]
    exact (hFG p hp).2.2.2.2.1 y fun i => ⟨(hy i).1.le, (hy i).2.le⟩
  have hiso : ∀ p ∈ s, Isometry (Φ p) := fun p hp => Isometry.of_dist_eq fun y y' => by
    rw [hΦ]; exact (hFG p hp).2.2.2.2.2.1 y y'
  have hFclosed : ∀ p ∈ s, IsClosed (F p) := fun p hp => by
    rw [hF]; exact (hFG p hp).2.2.2.2.2.2.2.1
  have hΦnotF : ∀ p ∈ s, ∀ q ∈ s, q ≠ p → ∀ y ∈ Q₁, Φ p y ∉ F q :=
    fun p hp q hq hqp y hy => by
      rw [hQ₁] at hy
      rw [hF, hΦ]
      exact (hFG p hp).2.2.2.2.2.2.2.2 q (hmono q hq) hqp y hy
  have hQ₁open : IsOpen Q₁ := by
    rw [hQ₁, ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  -- the open faces `A_p = Φ_p(Q₁) ⊆ F_p`: Borel, pairwise disjoint, `Hⁿ(A_p) ≤ 1`
  obtain ⟨A, hA⟩ : ∃ A : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → Set (Euclid P),
      A = fun p => Φ p '' Q₁ := ⟨_, rfl⟩
  have hAmem : ∀ p x, x ∈ A p ↔ ∃ y ∈ Q₁, Φ p y = x := fun p x => by
    rw [hA]; exact Iff.rfl
  have hAmeas : ∀ p ∈ s, MeasurableSet (A p) := fun p hp => by
    rw [hA]
    exact (hiso p hp).isClosedEmbedding.measurableEmbedding.measurableSet_image.mpr
      hQ₁open.measurableSet
  have hAF : ∀ p ∈ s, A p ⊆ F p := fun p hp x hx => by
    obtain ⟨y, hy, rfl⟩ := (hAmem p x).mp hx
    exact hΦF p hp y hy
  have hAdisj : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint (A p) (A q) := fun p hp q hq hpq => by
    refine Set.disjoint_left.mpr fun x hxp hxq => ?_
    obtain ⟨y, hy, rfl⟩ := (hAmem p x).mp hxp
    exact hΦnotF p hp q hq (Ne.symm hpq) y hy (hAF q hq hxq)
  have hAfin : ∀ p ∈ s, μHE[m + 1] (A p) ≤ 1 := fun p hp =>
    (measure_mono (hAF p hp)).trans (hFmeas p hp).le
  -- Step 2: the triple `N = ⋃_{β_p ≠ 0} A_p`, `θ = Σ_p |β_p| 1_{A_p}`,
  -- `ξ = Σ_p sgn(β_p) 1_{A_p} e_p^*`
  obtain ⟨s', hs'⟩ : ∃ s' : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P)),
      s' = s.filter fun p => β p ≠ 0 := ⟨_, rfl⟩
  have hs's : ∀ p ∈ s', p ∈ s := fun p hp => by
    rw [hs'] at hp; exact (Finset.mem_filter.mp hp).1
  have hs'β : ∀ p ∈ s', β p ≠ 0 := fun p hp => by
    rw [hs'] at hp; exact (Finset.mem_filter.mp hp).2
  obtain ⟨N, hN⟩ : ∃ N : Set (Euclid P), N = ⋃ p ∈ s', A p := ⟨_, rfl⟩
  have hNmem : ∀ x, x ∈ N ↔ ∃ p ∈ s', x ∈ A p := fun x => by
    rw [hN]; simp only [mem_iUnion, exists_prop]
  have hNmeas : MeasurableSet N := by
    rw [hN]; exact Finset.measurableSet_biUnion s' fun p hp => hAmeas p (hs's p hp)
  obtain ⟨θ, hθ⟩ : ∃ θ : Euclid P → ℕ,
      θ = fun x => ∑ p ∈ s', (A p).indicator (fun _ => (β p).natAbs) x := ⟨_, rfl⟩
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Euclid P → MultiVector P (m + 1),
      ξ = fun x => ∑ p ∈ s', (A p).indicator
        (fun _ => ((β p).sign : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p)) x :=
    ⟨_, rfl⟩
  -- on `A_p` (`β_p ≠ 0`), by disjointness, `θ = |β_p|` and `ξ = sgn(β_p) e_p^*`
  have hθA : ∀ p ∈ s', ∀ x ∈ A p, θ x = (β p).natAbs := fun p hp x hx => by
    rw [hθ]
    beta_reduce
    rw [Finset.sum_eq_single_of_mem p hp, indicator_of_mem hx]
    intro q hq hqp
    exact indicator_of_notMem (fun hxq => Set.disjoint_left.mp
      (hAdisj p (hs's p hp) q (hs's q hq) (Ne.symm hqp)) hx hxq) _
  have hξA : ∀ p ∈ s', ∀ x ∈ A p,
      ξ x = ((β p).sign : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p) :=
    fun p hp x hx => by
      rw [hξ]
      beta_reduce
      rw [Finset.sum_eq_single_of_mem p hp, indicator_of_mem hx]
      intro q hq hqp
      exact indicator_of_notMem (fun hxq => Set.disjoint_left.mp
        (hAdisj p (hs's p hp) q (hs's q hq) (Ne.symm hqp)) hx hxq) _
  -- Step 3: measurability, positivity, rectifiability, local integrability
  have hθmeas : Measurable θ := by
    rw [hθ]
    exact Finset.measurable_sum s' fun p hp => measurable_const.indicator (hAmeas p (hs's p hp))
  have hξmeas : StronglyMeasurable ξ := by
    -- `Λₙ(ℝᴾ)` is a topological additive group; its `ContinuousAdd` is not found by inference
    have : ContinuousAdd (MultiVector P (m + 1)) :=
      (inferInstance : IsTopologicalAddGroup (MultiVector P (m + 1))).toContinuousAdd
    rw [hξ]
    exact Finset.stronglyMeasurable_fun_sum s' fun p hp =>
      stronglyMeasurable_const.indicator (hAmeas p (hs's p hp))
  have hθpos : ∀ x ∈ N, 0 < θ x := fun x hx => by
    obtain ⟨p, hp, hxp⟩ := (hNmem x).mp hx
    rw [hθA p hp x hxp]
    exact Int.natAbs_pos.mpr (hs'β p hp)
  -- `N ⊆ ⋃_{j < |s'|} Φ_{p_j}(ℝⁿ)`, each `Φ_p` being `1`-Lipschitz
  have hrect : CountablyRectifiable (m + 1) N := by
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun j : ℕ => if h : j < s'.card then range (Φ (s'.equivFin.symm ⟨j, h⟩)) else ∅)
      fun j => ?_).mono fun x hx => ?_
    · beta_reduce
      split_ifs with h
      · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range
          (hiso _ (hs's _ (s'.equivFin.symm ⟨j, h⟩).2)).lipschitzWith
      · exact Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
    · obtain ⟨p, hp, hxp⟩ := (hNmem x).mp hx
      obtain ⟨y, -, rfl⟩ := (hAmem p x).mp hxp
      refine mem_iUnion.mpr ⟨s'.equivFin ⟨p, hp⟩, ?_⟩
      rw [dite_eq_left (s'.equivFin ⟨p, hp⟩).2]
      simp only [Fin.eta, Equiv.symm_apply_apply]
      exact mem_range_self y
  -- `∫_{N ∩ K} θ dHⁿ ≤ Σ_p |β_p| Hⁿ(A_p) < ∞`
  have hθint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
      ∫⁻ x in N ∩ K, (θ x : ℝ≥0∞) ∂μHE[m + 1] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_set inter_subset_left)
    rw [hN, lintegral_biUnion_finset
      (fun p hp q hq hpq => hAdisj p (hs's p hp) q (hs's q hq) hpq)
      fun p hp => hAmeas p (hs's p hp)]
    refine ENNReal.sum_ne_top.mpr fun p hp => ?_
    rw [setLIntegral_congr_fun (g := fun _ => ((β p).natAbs : ℝ≥0∞)) (hAmeas p (hs's p hp))
      fun x hx => by rw [hθA p hp x hx], setLIntegral_const]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hAfin p (hs's p hp)))
  -- Step 4: at `x ∈ A_p`, `TₓN = V_p = span e_p`, unit-oriented by `ξ(x) = ±e_p^*`
  have horth : ∀ p ∈ s, Orthonormal ℝ (e p) := fun p hp => by
    have h : e p = (EuclideanSpace.basisFun (Fin P) ℝ) ∘ p.2 := by
      funext k
      rw [he]
      simp only [Function.comp_apply, EuclideanSpace.basisFun_apply]
    rw [h]
    exact (EuclideanSpace.basisFun (Fin P) ℝ).orthonormal.comp p.2 (hmono p hp).injective
  have hunit : ∀ p ∈ s', IsUnitOrientationOf
      (((β p).sign : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p))
      (Submodule.span ℝ (range (e p))) := fun p hp => by
    refine ⟨e p, horth p (hs's p hp), rfl, ?_⟩
    rcases lt_or_gt_of_ne (hs'β p hp) with h | h
    · refine Or.inr fun α => ?_
      rw [Int.sign_eq_neg_one_of_neg h]
      simp
    · refine Or.inl fun α => ?_
      rw [Int.sign_eq_one_of_pos h]
      simp
  have htan : ∀ p ∈ s', ∀ x ∈ A p,
      HasApproximateTangentSpaceAt (m + 1) N x (Submodule.span ℝ (range (e p))) := by
    intro p hp x hx
    have hps := hs's p hp
    obtain ⟨y₀, hy₀, rfl⟩ := (hAmem p x).mp hx
    -- `B_{r₁}(y₀) ⊆ Q₁`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.isOpen_iff.mp hQ₁open y₀ hy₀
    -- `B_{r₂}(x)` misses the closed faces `F_q`, `q ∈ s' \ {p}`
    have hGclosed : IsClosed (⋃ q ∈ s'.erase p, F q) :=
      isClosed_biUnion_finset fun q hq => hFclosed q (hs's q (Finset.mem_of_mem_erase hq))
    have hxG : Φ p y₀ ∉ ⋃ q ∈ s'.erase p, F q := by
      simp only [mem_iUnion, exists_prop, not_exists, not_and]
      intro q hq
      exact hΦnotF p hps q (hs's q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq)
        y₀ hy₀
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hGclosed.isOpen_compl _ hxG
    refine Submission.dor_lmb_fcd_fr_local_plane_tangent P (m + 1) N (Φ p y₀) _ (min r₁ r₂)
      ?_ (lt_min hr₁ hr₂) fun y hy => ?_
    · rw [finrank_span_eq_card (horth p hps).linearIndependent, Fintype.card_fin]
    have hy₁ : dist y (Φ p y₀) < r₁ := (mem_ball.mp hy).trans_le (min_le_left _ _)
    have hy₂ : y ∉ ⋃ q ∈ s'.erase p, F q :=
      hball₂ (mem_ball.mpr ((mem_ball.mp hy).trans_le (min_le_right _ _)))
    constructor
    · -- `y ∈ N` forces `y ∈ A_p`, so `y − x = Σ_k (y₁ − y₀)_k e_{ι(k)} ∈ V_p`
      intro hyN
      obtain ⟨q, hq, hyq⟩ := (hNmem y).mp hyN
      have hqp : q = p := by
        by_contra hqp
        exact hy₂ (mem_iUnion₂.mpr ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, hAF q (hs's q hq) hyq⟩)
      rw [hqp] at hyq
      obtain ⟨y₁, -, rfl⟩ := (hAmem p y).mp hyq
      have hdiff : Φ p y₁ - Φ p y₀ = ∑ k, (y₁ k - y₀ k) • e p k := by
        rw [hΦ, he]
        simp only [sub_smul, Finset.sum_sub_distrib, add_sub_add_left_eq_sub]
      rw [hdiff]
      exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self k))
    · -- `y − x = Σ_k c_k e_{ι(k)}` with `|c| = |y − x| < r₁`, so `y = Φ_p(y₀ + c) ∈ A_p`
      intro hyV
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hyV
      have hΦc : Φ p (y₀ + WithLp.toLp 2 c) = y := by
        have h : Φ p (y₀ + WithLp.toLp 2 c) = Φ p y₀ + ∑ k, c k • e p k := by
          rw [hΦ, he]
          simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, add_assoc]
        rw [h, hc, add_sub_cancel]
      have hc₁ : y₀ + WithLp.toLp 2 c ∈ Q₁ := by
        apply hball₁
        rw [mem_ball, ← (hiso p hps).dist_eq, hΦc]
        exact hy₁
      exact (hNmem y).mpr ⟨p, hp, (hAmem p y).mpr ⟨_, hc₁, hΦc⟩⟩
  have horients : ∀ x ∈ N, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt (m + 1) N x Q ∧ IsUnitOrientationOf (ξ x) Q := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := (hNmem x).mp hx
    exact ⟨_, htan p hp x hxp, by rw [hξA p hp x hxp]; exact hunit p hp⟩
  -- `R = (N, θ, ξ)` is an `IMRep` in `ℝ^P`
  refine ⟨⟨N, θ, ξ, hNmeas, subset_univ N, hrect, hθmeas, hθpos, hθint,
    hξmeas.aestronglyMeasurable, ae_restrict_of_forall_mem hNmeas horients⟩, fun ω => ?_⟩
  -- Step 5: `R` represents `T`, face by face
  show T ω = ∫ x in N, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]
  obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) (m + 1)) := ContDiff.continuous hsmooth
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hωc
  -- on `A_p`: `θ ⟨ω, ξ⟩ = |β_p| sgn(β_p) ω(e_p) = β_p ω(e_p)`
  have hpt : ∀ p ∈ s', ∀ x ∈ A p, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) =
      (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p) := fun p hp x hx => by
    rw [hθA p hp x hx, hξA p hp x hx, smul_apply,
      ContinuousAlternatingMap.apply_apply, smul_eq_mul, ← mul_assoc]
    congr 1
    have h : (((β p).sign * ((β p).natAbs : ℤ) : ℤ) : ℝ) = (β p : ℝ) := by
      rw [Int.sign_mul_natAbs]
    rw [Int.cast_mul, Int.cast_natCast] at h
    rw [mul_comm]
    exact h
  -- integrability on each face: `|β_p ω(x)(e_p)| ≤ |β_p| sup ‖ω‖ ∏_k ‖e_{ι(k)}‖`, `Hⁿ(A_p) ≤ 1`
  have hintA : ∀ p ∈ s', IntegrableOn
      (fun x => (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x)) (A p)
      μHE[m + 1] := by
    intro p hp
    have hps := hs's p hp
    have hcont : Continuous fun x =>
        (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p) :=
      continuous_const.mul
        ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (e p)).continuous.comp hωc)
    refine IntegrableOn.congr_fun ?_ (fun x hx => (hpt p hp x hx).symm) (hAmeas p hps)
    refine Measure.integrableOn_of_bounded (M := |(β p : ℝ)| * (C * ∏ k, ‖e p k‖))
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hAfin p hps)) hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    gcongr
    exact ((((ω : DifferentialForm (Euclid P) (m + 1)) x).le_opNorm (e p)).trans
      (by gcongr; exact hC x))
  -- on each face, `∫_{A_p} β_p ω(e_p) dHⁿ = ∫_{F_p} 1_{A_p} β_p ω(e_p) dHⁿ`
  -- `= ∫_{Q₁} β_p ω(Φ_p y)(e_p) dy`
  have hface : ∀ p ∈ s', ∫ x in A p, (θ x : ℝ) *
      ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
      ∫ y in Q₁, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (e p) := by
    intro p hp
    have hps := hs's p hp
    calc ∫ x in A p, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]
        = ∫ x in A p, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p)
            ∂μHE[m + 1] := setIntegral_congr_fun (hAmeas p hps) fun x hx => hpt p hp x hx
      _ = ∫ x in F p, (A p).indicator
            (fun x => (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p)) x
            ∂μHE[m + 1] := by
          rw [integral_indicator (hAmeas p hps), Measure.restrict_restrict (hAmeas p hps),
            inter_eq_left.mpr (hAF p hps)]
      _ = ∫ y in Q₁, (A p).indicator
            (fun x => (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) x (e p)) (Φ p y) :=
          hFint p hps _
      _ = ∫ y in Q₁, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (e p) :=
          setIntegral_congr_fun hQ₁open.measurableSet fun y hy =>
            indicator_of_mem ((hAmem p _).mpr ⟨y, hy, rfl⟩) _
  -- sum over the disjoint faces; the faces with `β_p = 0` contribute nothing
  rw [hT ω, hN, integral_biUnion_finset s' (fun p hp => hAmeas p (hs's p hp))
    (fun p hp q hq hpq => hAdisj p (hs's p hp) q (hs's q hq) hpq) hintA,
    Finset.sum_congr rfl hface, hs', Finset.sum_filter_of_ne]
  · subst hQ₁ hΦ he
    rfl
  · intro p _ hp0 hβ
    exact hp0 (by simp [hβ])

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
