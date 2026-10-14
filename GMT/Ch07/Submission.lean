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

/-- **Simon Ch. 2, §4 (tangent plane of a locally conical surface).**  Let `M ⊆ ℝᴾ` be an
embedded `C¹` surface, `p ∈ M`, and let `M ∩ B_ρ(p)` be closed under positive dilations `x ↦ tx`
that stay in `B_ρ(p)`.  Then `span T_pM` is `2`-dimensional and contains `p`.  For a chart
`ψ : V → W` with `ψ(v₀) = p`, `span T_pM = Dψ(v₀)(ℝ²)`: `⊇` by the curves `t ↦ ψ(v₀ + ctw)`;
`⊆` since, for a left inverse `π` of `Dψ(v₀)`, `π ∘ ψ` has a local inverse `g` near `v₀`
(inverse function theorem), and properness of `ψ` gives `γ = ψ ∘ g ∘ π ∘ γ` near `0` for every
`C¹` curve `γ` in `M` through `p`.  The radial curve `t ↦ (1 + ε₀t)p` lies in `M` and has
velocity `ε₀p` at `0`. -/
theorem Submission.idtp_ccd_scsp_tangent_plane_mem : ∀ (P : ℕ) (M : Set (Euclid P)) (p : Euclid P) (ρ : ℝ), IsEmbeddedSubmanifold 1 2 M → p ∈ M → 0 < ρ → (∀ x ∈ M ∩ ball p ρ, ∀ t : ℝ, 0 < t → t • x ∈ ball p ρ → t • x ∈ M) → Module.finrank ℝ (Submodule.span ℝ (tangentSpace M p)) = 2 ∧ p ∈ Submodule.span ℝ (tangentSpace M p) := by
  intro P M p ρ hM hp hρ hrad
  -- Step 1: a chart `ψ : V → W` of `M` at `p`, and `v₀ ∈ V` with `ψ(v₀) = p`
  obtain ⟨V, W, ψ, hV, hW, hpW, hψ, hinj, himg, hprop, hD⟩ := hM p hp
  obtain ⟨v₀, hv₀V, hv₀⟩ : p ∈ ψ '' V := by rw [himg]; exact ⟨hpW, hp⟩
  have hψ1 : ContDiffOn ℝ 1 ψ V := by exact_mod_cast hψ
  set L := fderiv ℝ ψ v₀
  have hψv₀ : HasStrictFDerivAt ψ L v₀ :=
    (hψ1.contDiffAt (hV.mem_nhds hv₀V)).hasStrictFDerivAt one_ne_zero
  -- Step 2: `span T_pM = Dψ(v₀)(ℝ²)`
  have hspan : Submodule.span ℝ (tangentSpace M p) =
      LinearMap.range (L : Euclid 2 →ₗ[ℝ] Euclid P) := by
    apply le_antisymm
    · -- `T_pM ⊆ Dψ(v₀)(ℝ²)`: let `γ` be a `C¹` curve in `M` with `γ(0) = p`, `γ'(0) = v`
      rw [Submodule.span_le]
      rintro v ⟨γ, -, hγM, hγ0, hγv⟩
      -- a continuous left inverse `π` of the injective `L`
      obtain ⟨π₀, hπ₀⟩ := (L : Euclid 2 →ₗ[ℝ] Euclid P).exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.mpr (hD v₀ hv₀V))
      set π : Euclid P →L[ℝ] Euclid 2 := LinearMap.toContinuousLinearMap π₀
      have hπL : π.comp L = ContinuousLinearMap.id ℝ (Euclid 2) := by
        refine ContinuousLinearMap.ext fun w => ?_
        simpa [π] using LinearMap.congr_fun hπ₀ w
      -- `π ∘ ψ` has derivative `id` at `v₀`, so it has a local inverse `g` near `v₀`
      have hf : HasStrictFDerivAt (fun x => π (ψ x))
          ((ContinuousLinearEquiv.refl ℝ (Euclid 2) : Euclid 2 →L[ℝ] Euclid 2)) v₀ := by
        rw [ContinuousLinearEquiv.coe_refl, ← hπL]
        exact π.hasStrictFDerivAt.comp v₀ hψv₀
      obtain ⟨g, hleft, hgd⟩ : ∃ g : Euclid 2 → Euclid 2, (∀ᶠ x in 𝓝 v₀, g (π (ψ x)) = x) ∧
          HasFDerivAt g (ContinuousLinearMap.id ℝ (Euclid 2)) (π (ψ v₀)) :=
        ⟨_, hf.eventually_left_inverse, by simpa using hf.to_localInverse.hasFDerivAt⟩
      have hg0 : g (π (ψ v₀)) = v₀ := hleft.self_of_nhds
      obtain ⟨U₀, hU₀, hU₀o, hv₀U₀⟩ := _root_.eventually_nhds_iff.mp hleft
      -- properness: for `B̄_δ(p) ⊆ W`, `C = (V ∩ ψ⁻¹(B̄_δ(p))) \ U₀` is compact, so `ψ(C)` is
      -- closed, and `p ∉ ψ(C)` as `ψ` is injective on `V`
      obtain ⟨δ, hδ, hδW⟩ := nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hpW)
      set C := (V ∩ ψ ⁻¹' closedBall p δ) \ U₀
      have hCc : IsCompact C := (hprop _ hδW (isCompact_closedBall p δ)).diff hU₀o
      have hCcl : IsClosed (ψ '' C) :=
        (hCc.image_of_continuousOn (hψ1.continuousOn.mono fun x hx => hx.1.1)).isClosed
      have hpC : p ∉ ψ '' C := by
        rintro ⟨x, ⟨⟨hxV, -⟩, hxU⟩, hx⟩
        exact hxU (by rw [hinj hxV hv₀V (hx.trans hv₀.symm)]; exact hv₀U₀)
      -- near `t = 0`, `γ(t) = ψ(x)` with `x ∈ U₀`, so `γ = ψ ∘ g ∘ π ∘ γ`
      have hev : γ =ᶠ[𝓝 0] fun t => ψ (g (π (γ t))) := by
        have h1 : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ (ψ '' C)ᶜ ∩ ball p δ := by
          have h := hγv.continuousAt.tendsto
          rw [hγ0] at h
          exact h (inter_mem (hCcl.isOpen_compl.mem_nhds hpC) (ball_mem_nhds p hδ))
        filter_upwards [h1, Ioo_mem_nhds (show (-1:ℝ) < 0 by norm_num)
          (show (0:ℝ) < 1 by norm_num)] with t ht ht'
        obtain ⟨x, hxV, hxt⟩ : γ t ∈ ψ '' V := by
          rw [himg]; exact ⟨hδW (ball_subset_closedBall ht.2), hγM ht'⟩
        have hxU : x ∈ U₀ := by
          by_contra hxU
          exact ht.1 ⟨x, ⟨⟨hxV, by rw [mem_preimage, hxt]; exact ball_subset_closedBall ht.2⟩,
            hxU⟩, hxt⟩
        rw [← hxt, hU₀ x hxU]
      -- chain rule: `v = γ'(0) = L(π v)`
      have h1 : HasDerivAt (fun t => π (γ t)) (π v) 0 := π.hasFDerivAt.comp_hasDerivAt 0 hγv
      have h2 : HasDerivAt (fun t => g (π (γ t))) (π v) 0 :=
        hgd.comp_hasDerivAt_of_eq 0 h1 (by show π (ψ v₀) = π (γ 0); rw [hγ0, hv₀])
      have h3 : HasDerivAt (fun t => ψ (g (π (γ t)))) (L (π v)) 0 :=
        hψv₀.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2
          (by show v₀ = g (π (γ 0)); rw [hγ0, ← hv₀, hg0])
      exact ⟨π v, (hγv.unique (h3.congr_of_eventuallyEq hev)).symm⟩
    · -- `Dψ(v₀)(ℝ²) ⊆ span T_pM`: `t ↦ ψ(v₀ + ctw)` (with `B_{r₀}(v₀) ⊆ V`) has velocity `cLw`
      rintro _ ⟨w, rfl⟩
      obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hV v₀ hv₀V
      set c : ℝ := r₀ / (‖w‖ + 1) with hc
      have hc0 : 0 < c := div_pos hr₀ (by positivity)
      have hmaps : ∀ t ∈ Ioo (-1:ℝ) 1, v₀ + (c * t) • w ∈ V := by
        intro t ht
        apply hball
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_pos hc0]
        have ht1 : |t| < 1 := abs_lt.mpr ⟨ht.1, ht.2⟩
        calc c * |t| * ‖w‖ ≤ c * 1 * ‖w‖ := by gcongr
          _ < r₀ := by
            rw [mul_one, hc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg w]
      have hmem : c • L w ∈ tangentSpace M p := by
        refine ⟨fun t => ψ (v₀ + (c * t) • w), ?_, ?_, ?_, ?_⟩
        · exact hψ1.comp (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => v₀ + (c * t) • w)).contDiffOn
            hmaps
        · intro t ht
          exact (himg ▸ mem_image_of_mem ψ (hmaps t ht) : ψ _ ∈ W ∩ M).2
        · simp [hv₀]
        · have hβ : HasDerivAt (fun t : ℝ => v₀ + (c * t) • w) (c • w) 0 := by
            simpa using (((hasDerivAt_id (0:ℝ)).const_mul c).smul_const w).const_add v₀
          have h := hψv₀.hasFDerivAt.comp_hasDerivAt_of_eq 0 hβ (by simp)
          rw [map_smul] at h
          exact h
      have := Submodule.smul_mem _ c⁻¹ (Submodule.subset_span hmem)
      rwa [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul] at this
  refine ⟨?_, ?_⟩
  · -- Step 3: `dim span T_pM = dim Dψ(v₀)(ℝ²) = 2`, as `Dψ(v₀)` is injective
    rw [hspan, LinearMap.finrank_range_of_inj (f := (L : Euclid 2 →ₗ[ℝ] Euclid P)) (hD v₀ hv₀V),
      finrank_euclideanSpace_fin]
  · -- Step 4: the radial curve `t ↦ (1 + ε₀t)p`, `ε₀ = min(1/2, ρ/(|p| + 1))`, stays in
    -- `M ∩ B_ρ(p)` by radial invariance at `x = p`, so `ε₀p ∈ T_pM` and `p ∈ span T_pM`
    set ε₀ : ℝ := min (1/2) (ρ / (‖p‖ + 1))
    have hε₀0 : 0 < ε₀ := lt_min (by norm_num) (div_pos hρ (by positivity))
    have hmem : ε₀ • p ∈ tangentSpace M p := by
      refine ⟨fun t => (1 + ε₀ * t) • p, ?_, ?_, ?_, ?_⟩
      · exact (by fun_prop : ContDiff ℝ 1 (fun t : ℝ => (1 + ε₀ * t) • p)).contDiffOn
      · intro t ht
        have ht1 : |t| < 1 := abs_lt.mpr ⟨ht.1, ht.2⟩
        have hpos : 0 < 1 + ε₀ * t := by
          have : -ε₀ < ε₀ * t := by nlinarith [ht.1]
          linarith [min_le_left (1/2 : ℝ) (ρ / (‖p‖ + 1))]
        refine hrad p ⟨hp, mem_ball_self hρ⟩ _ hpos ?_
        rw [mem_ball, dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_mul, abs_of_pos hε₀0]
        calc ε₀ * |t| * ‖p‖ ≤ ε₀ * 1 * ‖p‖ := by gcongr
          _ ≤ ρ / (‖p‖ + 1) * ‖p‖ := by rw [mul_one]; gcongr; exact min_le_right _ _
          _ < ρ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg p]
      · simp
      · simpa using ((hasDerivAt_id (0:ℝ)).const_mul ε₀ |>.const_add 1).smul_const p
    have := Submodule.smul_mem _ ε₀⁻¹ (Submodule.subset_span hmem)
    rwa [smul_smul, inv_mul_cancel₀ hε₀0.ne', one_smul] at this
/-- **`C¹` local inverse with surjective inverse derivative** (inverse function theorem on `ℝᵈ`;
local inverse step of the stationary-cone sheet argument).  If `Φ : ℝᵈ → ℝᵈ` is `C¹` on an open
`V ∋ v₀` and `DΦ(v₀)` is injective, there are open sets `V₁` and `O` with `v₀ ∈ V₁ ⊆ V` and
`Φ(v₀) ∈ O`, and a map `H`, `C¹` on `O`, with `H(O) = V₁`, `Φ(H w) = w` and `DH(w)` surjective
for every `w ∈ O`.  `DΦ` is continuous on `V`, so `V₁′ = {v ∈ V : DΦ(v) invertible}` is open and
contains `v₀`; the strict-derivative inverse function theorem gives an open partial homeomorphism
`Φ̃ = Φ` with `v₀ ∈ Φ̃.source`; restrict it to `V₁′` and take `V₁ = source`, `O = target` and
`H = Φ̃.symm`, which is `C¹` with derivative `DΦ(H w)⁻¹` at every `w ∈ O`. -/
theorem Submission.idtp_ccd_scsp_li_c1_inverse : ∀ (d : ℕ) (Φ : Euclid d → Euclid d) (V : Set (Euclid d)) (v₀ : Euclid d), IsOpen V → v₀ ∈ V → ContDiffOn ℝ 1 Φ V → Injective (fderiv ℝ Φ v₀) → ∃ (V₁ O : Set (Euclid d)) (H : Euclid d → Euclid d), IsOpen V₁ ∧ IsOpen O ∧ v₀ ∈ V₁ ∧ V₁ ⊆ V ∧ Φ v₀ ∈ O ∧ ContDiffOn ℝ 1 H O ∧ H '' O = V₁ ∧ (∀ w ∈ O, Φ (H w) = w) ∧ ∀ w ∈ O, Surjective (fderiv ℝ H w) := by
  intro d Φ V v₀ hV hv₀ hΦ hinj
  -- step 1: `Φ` is `C¹` and differentiable at every point of `V`
  have hC1 : ∀ v ∈ V, ContDiffAt ℝ 1 Φ v := fun v hv => hΦ.contDiffAt (hV.mem_nhds hv)
  have hdiff : ∀ v ∈ V, HasFDerivAt Φ (fderiv ℝ Φ v) v := fun v hv =>
    ((hC1 v hv).differentiableAt one_ne_zero).hasFDerivAt
  -- step 2: `DΦ(v₀)` is the coercion of a continuous linear equivalence `E₀`
  set E₀ : Euclid d ≃L[ℝ] Euclid d := (LinearEquiv.ofInjectiveEndo
    (fderiv ℝ Φ v₀ : Euclid d →ₗ[ℝ] Euclid d) hinj).toContinuousLinearEquiv
  have hE₀ : (E₀ : Euclid d →L[ℝ] Euclid d) = fderiv ℝ Φ v₀ := by ext x; rfl
  -- step 3: `V₁′ = V ∩ DΦ⁻¹(invertible maps)` is open and contains `v₀`
  set V₁' := V ∩ fderiv ℝ Φ ⁻¹' range ((↑) : (Euclid d ≃L[ℝ] Euclid d) → Euclid d →L[ℝ] Euclid d)
  have hV₁' : IsOpen V₁' := (hΦ.continuousOn_fderiv_of_isOpen hV le_rfl).isOpen_inter_preimage hV
    ContinuousLinearEquiv.isOpen
  have hv₀' : v₀ ∈ V₁' := ⟨hv₀, E₀, hE₀⟩
  -- step 4: the inverse function theorem at `v₀`, restricted to `V₁′`
  have hstrict : HasStrictFDerivAt Φ (E₀ : Euclid d →L[ℝ] Euclid d) v₀ := by
    rw [hE₀]; exact (hC1 v₀ hv₀).hasStrictFDerivAt one_ne_zero
  set Φ₁ := (hstrict.toOpenPartialHomeomorph Φ).restrOpen V₁' hV₁'
  have hsrc : Φ₁.source = (hstrict.toOpenPartialHomeomorph Φ).source ∩ V₁' :=
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hv₀₁ : v₀ ∈ Φ₁.source := by
    rw [hsrc]; exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hv₀'⟩
  have hsub : Φ₁.source ⊆ V₁' := by rw [hsrc]; exact inter_subset_right
  refine ⟨Φ₁.source, Φ₁.target, Φ₁.symm, Φ₁.open_source, Φ₁.open_target, hv₀₁,
    fun v hv => (hsub hv).1, Φ₁.map_source hv₀₁, ?_, Φ₁.symm_image_target_eq_source,
    fun w hw => Φ₁.right_inv hw, ?_⟩
  -- step 5: at `w ∈ O`, `v = H w ∈ V₁′`, so `DΦ(v) = E_v` is invertible and `Φ` is `C¹` at `v`
  · intro w hw
    have hv : Φ₁.symm w ∈ V₁' := hsub (Φ₁.map_target hw)
    obtain ⟨E, hE⟩ := hv.2
    apply ContDiffAt.contDiffWithinAt
    apply Φ₁.contDiffAt_symm hw
    · rw [hE]; exact hdiff _ hv.1
    · exact hC1 _ hv.1
  · intro w hw
    have hv : Φ₁.symm w ∈ V₁' := hsub (Φ₁.map_target hw)
    obtain ⟨E, hE⟩ := hv.2
    have hH : HasFDerivAt Φ₁.symm (E.symm : Euclid d →L[ℝ] Euclid d) w :=
      Φ₁.hasFDerivAt_symm hw (by rw [hE]; exact hdiff _ hv.1)
    rw [hH.fderiv]
    exact E.symm.surjective
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm
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
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ : V → W` is a local representation of `N` as in (4.1)
(`Cʳ`, `r ≥ 1`, 1:1 and proper, `ψ(V) = W ∩ N`, `Dψ` injective), then
`T_{ψ(v)}N = Dψ(v)(ℝᵈ)` for every `v ∈ V`.  `Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N` because `ψ(V) ⊆ N`.
Conversely, properness and injectivity make `ψ⁻¹` continuous at `ψ(v)` on `ψ(V)`; with `Dψ(v)`
injective this gives, for each `ε > 0`, some `a` with `|y − ψ(v) − Dψ(v)a| ≤ ε|y − ψ(v)|` for all
`y ∈ N` near `ψ(v)`, so the difference quotients of a `C¹` curve in `N` through `ψ(v)` converge
into the closed subspace `Dψ(v)(ℝᵈ)`. -/
theorem Submission.chart_tangentSpace_eq_range_fderiv : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) := by
  intro P d r N W V ψ v hr hV hW hψ hinj hψV hproper hDψ hv
  -- `ψ` is `C¹` on the open set `V`, hence differentiable at `v` with derivative `Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  -- `ψ(V) = W ∩ N` lies in `W` and in `N`
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  -- `ψ⁻¹` is continuous at `ψ(v)` on `ψ(V)`
  have hinv := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj hVW
    hproper v hv
  refine Subset.antisymm ?_
    (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ hVN v hv)
  -- `T_{ψ(v)}N ⊆ Dψ(v)(ℝᵈ)`, from the secant estimate at `ψ(v)`
  exact Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v)
    (Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW hψV hv hψv
      (hDψ v hv) hinv)

/-- Images of open sets under a proper injective chart are relatively open: if `W` is open, `ψ` is
continuous and injective on `V` with `ψ(V) = W ∩ M`, and `V ∩ ψ⁻¹(K)` is compact for every compact
`K ⊆ W`, then every open `V₁ ⊆ V` has `ψ(V₁) = M ∩ N₀` for some open `N₀`.  For `v ∈ V₁`,
continuity of the inverse (`Submission.dsmc_chart_inverse_continuity`) gives `δᵥ > 0` such that
`v' ∈ V` and `|ψ(v') - ψ(v)| < δᵥ` force `v' ∈ V₁`; take `N₀ = ⋃_{v ∈ V₁} W ∩ B_{δᵥ}(ψ(v))`. -/
theorem Submission.idtp_ccd_scsp_li_chart_image_open : ∀ (P d : ℕ) (M W : Set (Euclid P)) (V V₁ : Set (Euclid d)) (ψ : Euclid d → Euclid P), IsOpen W → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → IsOpen V₁ → V₁ ⊆ V → ∃ N₀ : Set (Euclid P), IsOpen N₀ ∧ M ∩ N₀ = ψ '' V₁ := by
  intro P d M W V V₁ ψ hW hψ hinj hVM hproper hV₁ hV₁V
  -- `δᵥ`: `B_ε(v) ⊆ V₁`, and continuity of the inverse at `v` for this `ε`
  have hrad : ∀ v ∈ V₁, ∃ δ > 0, ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → v' ∈ V₁ := by
    intro v hv
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV₁ v hv
    obtain ⟨δ, hδ, hδε⟩ := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ hinj
      (hVM ▸ inter_subset_left) hproper v (hV₁V hv) ε hε
    exact ⟨δ, hδ, fun v' hv' hd => hball (mem_ball.2 (hδε v' hv' hd))⟩
  choose δ hδ hδV₁ using hrad
  refine ⟨⋃ v, ⋃ hv : v ∈ V₁, W ∩ ball (ψ v) (δ v hv),
    isOpen_iUnion fun v => isOpen_iUnion fun hv => hW.inter isOpen_ball, ?_⟩
  ext x
  simp only [mem_inter_iff, mem_iUnion, mem_image]
  constructor
  · -- a point of `M ∩ W ∩ B_{δᵥ}(ψ(v))` is `ψ(v')` with `v' ∈ V`, hence `v' ∈ V₁`
    rintro ⟨hxM, v, hv, hxW, hxb⟩
    obtain ⟨v', hv'V, rfl⟩ : x ∈ ψ '' V := hVM ▸ ⟨hxW, hxM⟩
    exact ⟨v', hδV₁ v hv v' hv'V (mem_ball.1 hxb), rfl⟩
  · -- `ψ(v) ∈ W ∩ M` and `ψ(v) ∈ B_{δᵥ}(ψ(v))`
    rintro ⟨v, hv, rfl⟩
    have h : ψ v ∈ W ∩ M := hVM ▸ mem_image_of_mem ψ (hV₁V hv)
    exact ⟨h.2, v, hv, h.1, mem_ball_self (hδ v hv)⟩

/-- **Local inversion of a transversal `C¹` map on an embedded `C¹` surface** (Simon Ch. 2, §4,
(4.1)–(4.3), with the inverse function theorem).  Let `ψ : V₀ → W₀ ∩ M` be a chart at
`p = ψ(v₀)`.  On the open set `V₀ ∩ ψ⁻¹(U) ∋ v₀`, `Φ = F ∘ ψ` is `C¹`, and
`DΦ(v₀) = DF(p) ∘ Dψ(v₀)` is injective because `Dψ(v₀)(ℝ²) = T_pM` and `DF(p)` is injective on
`span T_pM`.  The `C¹` inverse function theorem gives `H : O → V₁` with `Φ ∘ H = id` on `O`,
`H(O) = V₁` and `DH` onto.  `G = ψ ∘ H` then satisfies `F ∘ G = id` on `O` and
`DG(w)(ℝ²) = Dψ(H w)(ℝ²) = T_{G w}M`.  Finally `ψ(V₁) = M ∩ N₀` for an open `N₀`, so
`N = N₀ ∩ U` has `G(O) = ψ(V₁) = M ∩ N`, since `ψ(V₁) ⊆ U`. -/
theorem Submission.idtp_ccd_scsp_local_inverse : ∀ (P : ℕ) (M : Set (Euclid P)) (p : Euclid P) (U : Set (Euclid P)) (F : Euclid P → Euclid 2), IsEmbeddedSubmanifold 1 2 M → p ∈ M → IsOpen U → p ∈ U → ContDiffOn ℝ 1 F U → (∀ v ∈ Submodule.span ℝ (tangentSpace M p), fderiv ℝ F p v = 0 → v = 0) → ∃ (O : Set (Euclid 2)) (N : Set (Euclid P)) (G : Euclid 2 → Euclid P), IsOpen O ∧ IsOpen N ∧ F p ∈ O ∧ p ∈ N ∧ N ⊆ U ∧ ContDiffOn ℝ 1 G O ∧ G '' O = M ∩ N ∧ (∀ w ∈ O, F (G w) = w) ∧ ∀ w ∈ O, tangentSpace M (G w) = Set.range (fderiv ℝ G w) := by
  intro P M p U F hM hp hU hpU hF htr
  -- Step 1: a chart `ψ : V₀ → W₀ ∩ M` at `p = ψ(v₀)`, with `T_{ψ(v)}M = Dψ(v)(ℝ²)` on `V₀`
  obtain ⟨V₀, W₀, ψ, hV₀, hW₀, hpW₀, hψ, hinj, hψV₀, hproper, hDψ⟩ := hM p hp
  obtain ⟨v₀, hv₀, rfl⟩ : p ∈ ψ '' V₀ := hψV₀ ▸ ⟨hpW₀, hp⟩
  have hψ1 : ContDiffOn ℝ 1 ψ V₀ := by exact_mod_cast hψ
  have hT : ∀ v ∈ V₀, tangentSpace M (ψ v) = Set.range (fderiv ℝ ψ v) := fun v hv =>
    Submission.chart_tangentSpace_eq_range_fderiv P 2 1 M W₀ V₀ ψ v le_rfl hV₀ hW₀ hψ hinj
      hψV₀ hproper hDψ hv
  -- Step 2: `ψ` is differentiable on the open set `V₀`, and `F` on the open set `U`
  have hψd : ∀ v ∈ V₀, DifferentiableAt ℝ ψ v := fun v hv =>
    (hψ1.differentiableOn one_ne_zero).differentiableAt (hV₀.mem_nhds hv)
  have hFd : DifferentiableAt ℝ F (ψ v₀) :=
    (hF.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hpU)
  -- Step 3: `Φ = F ∘ ψ` is `C¹` on the open set `V₀ ∩ ψ⁻¹(U) ∋ v₀`, and `DΦ(v₀)` is injective:
  -- if `DF(p)(Dψ(v₀) z) = 0`, then `Dψ(v₀) z ∈ T_pM` gives `Dψ(v₀) z = 0`, so `z = 0`
  have hV₀U : IsOpen (V₀ ∩ ψ ⁻¹' U) := hψ1.continuousOn.isOpen_inter_preimage hV₀ hU
  have hΦinj : Injective (fderiv ℝ (F ∘ ψ) v₀) := by
    rw [fderiv_comp v₀ hFd (hψd v₀ hv₀)]
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    have hzT : fderiv ℝ ψ v₀ z ∈ tangentSpace M (ψ v₀) := by
      rw [hT v₀ hv₀]
      exact mem_range_self z
    exact (injective_iff_map_eq_zero _).1 (hDψ v₀ hv₀) z (htr _ (Submodule.subset_span hzT) hz)
  -- Steps 4–6: the `C¹` inverse function theorem for `Φ` at `v₀`
  obtain ⟨V₁, O, H, hV₁, hO, hv₀V₁, hV₁U, hΦO, hH, hHO, hΦH, hDH⟩ :=
    Submission.idtp_ccd_scsp_li_c1_inverse 2 (F ∘ ψ) (V₀ ∩ ψ ⁻¹' U) v₀ hV₀U ⟨hv₀, hpU⟩
      (hF.comp_inter hψ1) hΦinj
  have hV₁V₀ : V₁ ⊆ V₀ := hV₁U.trans inter_subset_left
  have hHV₀ : ∀ w ∈ O, H w ∈ V₀ := fun w hw => hV₁V₀ (hHO ▸ mem_image_of_mem H hw)
  -- Step 8: `ψ(V₁)` is relatively open in `M`, and `ψ(V₁) ⊆ U`
  obtain ⟨N₀, hN₀, hMN₀⟩ := Submission.idtp_ccd_scsp_li_chart_image_open P 2 M W₀ V₀ V₁ ψ hW₀
    hψ1.continuousOn hinj hψV₀ hproper hV₁ hV₁V₀
  have hψV₁U : ψ '' V₁ ⊆ U := image_subset_iff.2 fun v hv => (hV₁U hv).2
  have hpN₀ : ψ v₀ ∈ M ∩ N₀ := by
    rw [hMN₀]
    exact mem_image_of_mem ψ hv₀V₁
  -- Steps 7 and 9: `G = ψ ∘ H`, `N = N₀ ∩ U`
  refine ⟨O, N₀ ∩ U, ψ ∘ H, hO, hN₀.inter hU, hΦO, ⟨hpN₀.2, hpU⟩, inter_subset_right,
    hψ1.comp hH fun w hw => hHV₀ w hw, ?_, hΦH, fun w hw => ?_⟩
  · -- `G(O) = ψ(H(O)) = ψ(V₁) = (M ∩ N₀) ∩ U`
    rw [image_comp, hHO, ← inter_assoc, hMN₀, inter_eq_left.2 hψV₁U]
  · -- `DG(w)(ℝ²) = Dψ(H w)(DH(w)(ℝ²)) = Dψ(H w)(ℝ²) = T_{G w}M`, as `DH(w)` is onto
    have hHd : DifferentiableAt ℝ H w :=
      (hH.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds hw)
    rw [Function.comp_apply, hT (H w) (hHV₀ w hw), fderiv_comp w (hψd _ (hHV₀ w hw)) hHd,
      ContinuousLinearMap.coe_comp, (hDH w hw).range_comp]
/-- **Angle-parametrized unit curve** (step 6 of the parent proof).  Differentiating
`⟨γ, γ⟩ = ‖γ‖² ≡ 1` gives `⟨γ, γ′⟩ = 0`.  With `A = ⟨γ, u⟩ > 0` and `B = ⟨γ, e⟩`, the quotient
and chain rules differentiate `arctan (B / A) ≡ α` to `(1 + (B / A)²)⁻¹ (B′ A − B A′) / A² = 1`,
i.e. `A B′ − B A′ = A² + B²`; the right side is positive, so `γ′ ≠ 0`. -/
theorem Submission.idtp_ccd_scsp_angle_curve : ∀ (P : ℕ) (u e : Euclid P) (s : ℝ) (γ : ℝ → Euclid P), ContDiffOn ℝ 1 γ (Ioo (-s) s) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ 0 < inner ℝ (γ α) u ∧ Real.arctan (inner ℝ (γ α) e / inner ℝ (γ α) u) = α) → ∀ α ∈ Ioo (-s) s, inner ℝ (γ α) (deriv γ α) = 0 ∧ inner ℝ (γ α) u * inner ℝ (deriv γ α) e - inner ℝ (γ α) e * inner ℝ (deriv γ α) u = inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2 ∧ deriv γ α ≠ 0 := by
  intro P u e s γ hγ hprop α hα
  -- `(-s, s)` is a neighbourhood of `α` on which `γ` is differentiable
  have hI : Ioo (-s) s ∈ 𝓝 α := Ioo_mem_nhds hα.1 hα.2
  have hd : HasDerivAt γ (deriv γ α) α :=
    ((hγ.differentiableOn one_ne_zero).differentiableAt hI).hasDerivAt
  -- orthogonality: `⟨γ, γ⟩ = ‖γ‖² ≡ 1` near `α`, so its derivative `2 ⟨γ, γ′⟩` vanishes
  have hn1 : (fun t => inner ℝ (γ t) (γ t)) =ᶠ[𝓝 α] fun _ => (1 : ℝ) := by
    filter_upwards [hI] with t ht
    rw [real_inner_self_eq_norm_sq, (hprop t ht).1, one_pow]
  have h0 := (hd.inner ℝ hd).unique ((hasDerivAt_const α (1 : ℝ)).congr_of_eventuallyEq hn1)
  rw [real_inner_comm (γ α) (deriv γ α)] at h0
  have horth : inner ℝ (γ α) (deriv γ α) = 0 := by linarith
  -- the angle: `A = ⟨γ, u⟩`, `B = ⟨γ, e⟩` and `arctan (B / A) ≡ id` near `α`
  have hA : 0 < inner ℝ (γ α) u := (hprop α hα).2.1
  have hAd : HasDerivAt (fun t => inner ℝ (γ t) u) (inner ℝ (deriv γ α) u) α := by
    simpa using hd.inner ℝ (hasDerivAt_const α u)
  have hBd : HasDerivAt (fun t => inner ℝ (γ t) e) (inner ℝ (deriv γ α) e) α := by
    simpa using hd.inner ℝ (hasDerivAt_const α e)
  have hid : (fun t => Real.arctan (((fun t => inner ℝ (γ t) e) / fun t => inner ℝ (γ t) u) t))
      =ᶠ[𝓝 α] fun t => t := by
    filter_upwards [hI] with t ht
    exact (hprop t ht).2.2
  have h1 := ((hBd.div hAd hA.ne').arctan).unique ((hasDerivAt_id' α).congr_of_eventuallyEq hid)
  simp only [Pi.div_apply] at h1
  -- clearing `(1 + (B / A)²) A² = A² + B² > 0` from `h1` gives the angle identity
  have hpos : 0 < inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2 := by positivity
  have hkey : inner ℝ (γ α) u * inner ℝ (deriv γ α) e - inner ℝ (γ α) e * inner ℝ (deriv γ α) u =
      inner ℝ (γ α) u ^ 2 + inner ℝ (γ α) e ^ 2 := by
    field_simp at h1
    linarith
  -- non-degeneracy: `γ′ = 0` would make the left side `0`
  refine ⟨horth, hkey, fun h => ?_⟩
  rw [h, inner_zero_left, inner_zero_left, mul_zero, mul_zero, sub_zero] at hkey
  exact hpos.ne' hkey.symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
