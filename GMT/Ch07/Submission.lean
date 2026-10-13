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

/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Dilations of currents in `ℝᴾ` exist and agree with the blow-up `η_{a,λ#}`** (Simon Ch. 3,
1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413).  Call
`X' ∈ 𝒟ₘ(ℝᴾ)` a dilation of `X` if `X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`, `η = η_{a,λ}`.
Since `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`, so `η_{a,λ#}X ∈ 𝒟ₘ(η(ℝᴾ))` restricts to `ℝᴾ`.  (i) This
restriction is a dilation of `X`; (ii) every dilation `X'` of `X` agrees with `η_{a,λ#}X`:
`X'(ω) = η_{a,λ#}X(ω₁)` whenever `ω₁ ∈ 𝒟ᵐ(η(ℝᴾ))` has the underlying form of `ω`.  Both follow
from `Submission.dtc_blowUp_testForm_corr` with `U = ℝᴾ`. -/
theorem Submission.cbr_cidc_dilation_exists_eq_blowUp : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ (ω : TestFormOn (univ : Set (Euclid P)) m) (ω₁ : TestFormOn (dilation a lam '' (univ : Set (Euclid P))) m), (ω₁ : DifferentialForm (Euclid P) m) = (ω : DifferentialForm (Euclid P) m) → X' ω = blowUp X a lam hlam.ne' ω₁ := by
  intro P m a lam hlam
  obtain ⟨hA, -, hC⟩ := Submission.dtc_blowUp_testForm_corr P m univ a lam hlam
  -- Step 1: `η` maps `ℝᴾ` onto `ℝᴾ`, since `η(a + λy) = y`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by
      simp [dilation, dilationCLM, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']⟩
  refine ⟨fun X => ?_, fun X X' hX' ω ω₁ hω => ?_⟩
  · -- Step 2, (i): the restriction of `η_{a,λ#}X` to `ℝᴾ` is a dilation of `X`, by part (c).
    refine ⟨(blowUp X a lam hlam.ne').restrictDomain hsurj, fun ω ω' hωω' => ?_⟩
    rw [GeometricCurrentOn.restrictDomain_apply]
    exact hC X _ ω' (by simpa using hωω')
  · -- Steps 3–4, (ii): part (a) gives `ω' = ω₁ ∘ η = ω ∘ η`, and part (c) and the dilation
    -- property give `η_{a,λ#}X(ω₁) = λ⁻ᵐ X(ω') = X'(ω)`.
    obtain ⟨ω', hω'⟩ := hA ω₁
    rw [hC X ω₁ ω' hω', hX' ω ω' (fun y => by rw [hω', hω])]
/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl

/-- **Dilations commute with the boundary** (Simon 6.2.3, chapter-06.txt line 216, and
6.2.24(1), line 414, for `η = η_{a,λ}`, `λ > 0`; the dilations of the closure theorem 6.8.2):
if `X'(ω) = λ^{-(m+1)} X(ω ∘ η)` on `𝒟^{m+1}(ℝᴾ)`, then `∂X'(ω) = λ⁻ᵐ ∂X(ω ∘ η)` on `𝒟ᵐ(ℝᴾ)`.

`η` maps `ℝᴾ` onto itself, so `ω` is also a test form `ω₁` in `η(ℝᴾ)`, and `dω`, `dω₁` have the
same underlying form.  Hence
`∂X'(ω) = X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁) = η_#(∂X)(ω₁) = λ⁻ᵐ ∂X(ω')`
(`cbr_cidc_dilation_exists_eq_blowUp`, `dtc_blowUp_algebra` (iv), `dtc_blowUp_testForm_corr` (c)). -/
theorem Submission.cbr_cidc_dilation_boundary : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω' := by
  intro P m a lam hlam X X' hX ω ω' hω
  -- Step 1: `η(a + λy) = y`, so `η(ℝᴾ) = ℝᴾ` and `ω` is a test form `ω₁` in `η(ℝᴾ)`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  let ω₁ : TestFormOn (dilation a lam '' univ) m := testFormOnInclusion hsurj m ω
  -- Step 2: `X'(dω) = η_#X(dω₁)`, as `dω₁` and `dω` are the same form.
  have h1 := (Submission.cbr_cidc_dilation_exists_eq_blowUp P (m + 1) a lam hlam).2 X X' hX
    (exteriorDerivativeTestOn univ m ω) (exteriorDerivativeTestOn _ m ω₁) rfl
  -- Steps 2–3: `∂X'(ω) = X'(dω) = η_#X(dω₁) = ∂(η_#X)(ω₁) = η_#(∂X)(ω₁)`.
  rw [GeometricCurrentOn.boundary_apply, h1, ← GeometricCurrentOn.boundary_apply,
    (Submission.dtc_blowUp_algebra P univ a lam hlam).2.2.2 m X]
  -- Step 4: `η_#(∂X)(ω₁) = λ⁻ᵐ ∂X(ω')`, as `ω' = ω ∘ η = ω₁ ∘ η`.
  exact (Submission.dtc_blowUp_testForm_corr P m univ a lam hlam).2.2 X.boundary ω₁ ω' hω

/-- **A dilation of an integer multiplicity current is integer multiplicity** (item (3) of the
dilation calculus for `η = η_{a,λ}`, `λ > 0`: Simon Ch. 6, 3.3–3.9 for the push-forward 6.2.23,
as used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  If `R = (M, θ, ξ)`
represents `X` in `ℝᴾ`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}X` in `η(ℝᴾ)`
(`dtc_blowUp_imrep`).  As `η(a + λy) = y`, `η(ℝᴾ) = ℝᴾ`: `R'` is also a triple in `ℝᴾ` (a compact
`K ⊆ ℝᴾ` lies in `η(ℝᴾ)`), and `X'(ω) = η_{a,λ#}X(ω) = R'(ω)` for every test form `ω` on `ℝᴾ`
(`cbr_cidc_dilation_exists_eq_blowUp`). -/
theorem Submission.cbr_cidc_dilation_isIntegerMultiplicity : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X' := by
  intro P m a lam hlam X X' hX hXim
  obtain ⟨R, hR⟩ := hXim
  -- `η = η_{a,λ}` is onto, `η(a + λy) = y`, so `ℝᴾ ⊆ η(ℝᴾ)`
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  -- `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}X` in `η(ℝᴾ)`
  obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P m univ X a lam hlam R hR
  -- the same triple in `ℝᴾ`: of its conditions only local integrability involves the domain
  refine ⟨{ carrier := R'.carrier
            mult := R'.mult
            orient := R'.orient
            measurableSet_carrier := R'.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := R'.rectifiable
            measurable_mult := R'.measurable_mult
            mult_pos := R'.mult_pos
            locallyIntegrable_mult := fun K hK _ =>
              R'.locallyIntegrable_mult K hK ((subset_univ K).trans hsurj)
            aestronglyMeasurable_orient := R'.aestronglyMeasurable_orient
            orients := R'.orients }, ?_⟩
  -- `X'(ω) = η_{a,λ#}X(ω) = R'(ω)`, with `ω` regarded as a test form in `η(ℝᴾ)`
  intro ω
  rw [(Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).2 X X' hX ω
    (testFormOnInclusion hsurj m ω) rfl, hR' (testFormOnInclusion hsurj m ω)]
  rfl

/-- **Integral representations under the dilation `η = η_{a,λ}`, `λ > 0`** (Simon 6.2.7 and
Remark 6.2.24(2), chapter-06.txt lines 271 and 414–419, for `f = η`; `η` as in Ch. 3, 1.4,
chapter-03.txt line 85).  If `X'` is a dilation of `X` (`X'(ω) = λ⁻ᵐ X(ω')` whenever
`ω' = ω ∘ η`) and `X(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`, then
`X'(ω) = ∫ ⟨ω(y), ξ(a + λy)⟩ d(λ⁻ᵐ η_*μ)(y)`: take `ω' = ω ∘ η`, change variables `y = η(x)`
(`η` is a homeomorphism, hence a measurable embedding) and use `a + λη(x) = x`. -/
theorem Submission.cbr_cidc_dilation_integral_rep : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) := by
  intro P m a lam hlam X X' μ ξ hX hrep ω
  have hne : lam ≠ 0 := hlam.ne'
  -- `η = η_{a,λ}` (`y ↦ −λ⁻¹a + λ⁻¹y`) and `ι(z) = a + λz` are mutually inverse.
  have hηι : ∀ y, dilation a lam (a + lam • y) = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ x, a + lam • dilation a lam x = x := by
    intro x
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  -- Step 1: `η` maps `ℝᴾ` onto itself, so `ω ∈ 𝒟ᵐ(η(ℝᴾ))`, and the accepted
  -- `dtc_blowUp_testForm_corr` (a) gives `ω' ∈ 𝒟ᵐ(ℝᴾ)` with `ω' = ω ∘ η`.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ :=
    fun y _ => ⟨a + lam • y, mem_univ _, hηι y⟩
  obtain ⟨ω', hω'⟩ :=
    (Submission.dtc_blowUp_testForm_corr P m univ a lam hlam).1 (testFormOnInclusion hsurj m ω)
  -- Step 2: `X'(ω) = λ⁻ᵐ X(ω') = λ⁻ᵐ ∫ ⟨ω'(x), ξ(x)⟩ dμ(x)`.
  rw [hX ω ω' (fun y => by simpa using hω' y), hrep ω']
  -- Step 3: `η` is a homeomorphism, hence a measurable embedding, so
  -- `∫ g d(η_*μ) = ∫ g ∘ η dμ` for every `g` (no integrability needed).
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • a)))
  have hη : ⇑η = dilation a lam := by
    funext y
    simp [η, dilation, dilationCLM]
  have hemb : MeasurableEmbedding (dilation a lam) := hη ▸ η.measurableEmbedding
  -- Steps 4–5: `∫ g d(c • ν) = c.toReal * ∫ g dν` with `(ofReal λ⁻ᵐ).toReal = λ⁻ᵐ`; for
  -- `g(y) = ⟨ω(y), ξ(a + λy)⟩`, `g(η(x)) = ⟨ω'(x), ξ(x)⟩` because `a + λη(x) = x`.
  rw [integral_smul_measure, hemb.integral_map, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [hιη x, hω' x, testFormOnInclusion_coe]
/-- **Mass scaling for dilations: `M_{η(W)}(X') = λ⁻ᵐ M_W(X)`** for `η = η_{a,λ}`, `λ > 0`, a
dilation `X' ∈ 𝒟ₘ(ℝᴾ)` of `X ∈ 𝒟ₘ(ℝᴾ)` (`X'(ω) = λ⁻ᵐ X(ω')` whenever `ω' = ω ∘ η`) and every
`W ⊆ ℝᴾ` (item (5) of the dilation calculus for the integer-multiplicity criterion for cycles;
`η_{x,λ}` of Simon Ch. 3, 1.4, chapter-03.txt line 85; mass `M_W` of 6.2.5, chapter-06.txt
lines 221–233, with the Euclidean coefficient norm).  `η(a + λy) = y`, so `η(ℝᴾ) = ℝᴾ` and
`𝒟ᵐ(ℝᴾ)`, `𝒟ᵐ(η(ℝᴾ))` consist of the same forms, with the same admissible forms for `M_{η(W)}`.
By `Submission.cbr_cidc_dilation_exists_eq_blowUp`, `X'(ω) = η_{a,λ#}X(ω)` on equal forms, so
`M_{η(W)}(X') = M_{η(W)}(η_{a,λ#}X)`, which is `λ⁻ᵐ M_W(X)` by
`Submission.dtc_blowUp_massOn_image`. -/
theorem Submission.cbr_cidc_dilation_massOn_image : ∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W := by
  intro P m a lam hlam X X' hX W
  -- `η = η_{a,λ}` is onto (`η(a + λy) = y`), so `ℝᴾ` and `η(ℝᴾ)` have the same test forms.
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation a lam '' univ := fun y _ =>
    ⟨a + lam • y, mem_univ _, by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne']⟩
  have hsub : dilation a lam '' (univ : Set (Euclid P)) ⊆ univ := subset_univ _
  -- `X'(ω) = η_{a,λ#}X(ω₁)` whenever `ω` and `ω₁` have the same underlying form.
  have hblow := (Submission.cbr_cidc_dilation_exists_eq_blowUp P m a lam hlam).2 X X' hX
  refine Eq.trans ?_ (Submission.dtc_blowUp_massOn_image P m univ X a lam hlam W)
  -- The admissible forms for `M_{η(W)}(X')` and `M_{η(W)}(η_{a,λ#}X)` are the same forms, on
  -- which `X'` and `η_{a,λ#}X` agree.
  unfold GeometricCurrentOn.massOn
  congr 1
  ext r
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨testFormOnInclusion hsurj m φ, hφ,
      congrArg ENNReal.ofReal (hblow φ (testFormOnInclusion hsurj m φ) rfl).symm⟩
  · rintro ⟨φ₁, hφ₁, rfl⟩
    exact ⟨testFormOnInclusion hsub m φ₁, hφ₁,
      congrArg ENNReal.ofReal (hblow (testFormOnInclusion hsub m φ₁) φ₁ rfl)⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
