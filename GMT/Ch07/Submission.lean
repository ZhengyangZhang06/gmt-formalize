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

/-- **Cube averages under a translation estimate** (Kolmogorov–Riesz averaging step): if
`Lᵐ(((F − h) Δ F) ∩ B_R(0)) ≤ C|h|` for `|h| ≤ 1`, then `1_F` is `KCδ`-close in `L¹(B_R(0))` to its
averages over the grid cubes `Q_δ(v)` of side `δ`, `δ√m ≤ 1`.  `Q_δ(v)` is a box of volume `δᵐ`
inside `B̄_{√m δ}(v)`, so `|1_F(v) − a(v)| ≤ δ⁻ᵐ ∫_{|h| ≤ √m δ} |1_F(v) − 1_F(v + h)| dh`; Tonelli
over `v ∈ B_R(0)` and `Lᵐ(B̄_{√m δ}(0)) = (√m δ)ᵐ Lᵐ(B₁(0))` give `K = (√m)^{m+1} Lᵐ(B₁(0))`. -/
theorem Submission.codim1_zsl_pc_cube_average_bound : ∀ (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set (Euclid m)) (R C δ : ℝ), MeasurableSet F → 0 ≤ C → 0 < δ → δ * Real.sqrt m ≤ 1 → (∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ ≤ ENNReal.ofReal (K * C * δ) := by
  intro m
  refine ⟨Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal, by positivity, ?_⟩
  intro F R C δ hF hC hδ hδm hsd
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hs0 : 0 ≤ Real.sqrt m * δ := by positivity
  have hs1 : Real.sqrt m * δ ≤ 1 := by rw [mul_comm]; exact hδm
  have hδm0 : 0 < δ ^ m := pow_pos hδ m
  -- Step 1: the cube `Q v` is (the preimage of) a half-open box of side `δ`
  have hQbox : ∀ v : Euclid m, {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} =
      (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) := by
    intro v
    ext w
    simp only [Set.mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico]
    refine forall_congr' fun j => ?_
    rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]
  have hbox_meas : ∀ v : Euclid m,
      MeasurableSet (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) :=
    fun v => MeasurableSet.univ_pi fun j => measurableSet_Ico
  have hQvol : ∀ v : Euclid m,
      volume {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} = ENNReal.ofReal (δ ^ m) := by
    intro v
    rw [hQbox v, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (hbox_meas v).nullMeasurableSet, Real.volume_pi_Ico]
    have : ∀ j : Fin m, ((⌊v j / δ⌋ : ℝ) + 1) * δ - (⌊v j / δ⌋ : ℝ) * δ = δ := fun j => by ring
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hδ.le]
  -- Step 2: the cube lies in the closed ball of radius `√m δ` about `v`
  have hQball : ∀ v : Euclid m,
      {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} ⊆ closedBall v (Real.sqrt m * δ) := by
    intro v w hw
    rw [hQbox v] at hw
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico] at hw
    rw [mem_closedBall, EuclideanSpace.dist_eq]
    have hcoord : ∀ j, dist (w j) (v j) ^ 2 ≤ δ ^ 2 := by
      intro j
      have hwj := hw j
      have h1 := Int.floor_le (v j / δ)
      have h2 := Int.lt_floor_add_one (v j / δ)
      rw [le_div_iff₀ hδ] at h1
      rw [div_lt_iff₀ hδ] at h2
      have hab : |w j - v j| ≤ δ := by
        rw [abs_le]; constructor <;> nlinarith [hwj.1, hwj.2]
      rw [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc Real.sqrt (∑ j, dist (w j) (v j) ^ 2) ≤ Real.sqrt (∑ _j : Fin m, δ ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hcoord j)
      _ = Real.sqrt m * δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hδ.le]
  -- Step 3: pointwise bound by an average of differences over the closed ball
  have hpt : ∀ (v : Euclid m) (Q : Set (Euclid m)), volume Q = ENNReal.ofReal (δ ^ m) →
      Q ⊆ closedBall v (Real.sqrt m * δ) →
      ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
    intro v Q hQv hQb
    have hQfin : volume Q ≠ ∞ := by rw [hQv]; exact ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (volume.restrict Q) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hQfin.lt_top⟩
    have hint_c : Integrable (fun _ : Euclid m => F.indicator (fun _ => (1 : ℝ)) v)
        (volume.restrict Q) := integrable_const _
    have hint_u : Integrable (F.indicator (fun _ => (1 : ℝ))) (volume.restrict Q) :=
      (integrable_const (1 : ℝ)).indicator hF
    have h1 : ∫ w in Q, F.indicator (fun _ => (1 : ℝ)) w = (volume (F ∩ Q)).toReal := by
      rw [integral_indicator_const (1 : ℝ) hF, smul_eq_mul, mul_one,
        measureReal_restrict_apply hF, measureReal_def]
    have h2 : F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m =
        (δ ^ m)⁻¹ * ∫ w in Q, (F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w) := by
      rw [integral_sub hint_c hint_u, setIntegral_const, h1, measureReal_def, hQv,
        ENNReal.toReal_ofReal hδm0.le, smul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hδm0.ne', one_mul, div_eq_inv_mul]
    have h3 : ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ := by
      rw [h2, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.2 hδm0.le)]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    have h4 : ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ ≤
        ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
      calc ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ
          ≤ ∫⁻ w in closedBall v (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ :=
            lintegral_mono_set hQb
        _ = ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
          rw [← lintegral_indicator measurableSet_closedBall,
            ← lintegral_indicator measurableSet_closedBall,
            ← lintegral_add_left_eq_self ((closedBall v (Real.sqrt m * δ)).indicator fun w =>
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ) v]
          refine lintegral_congr fun h => ?_
          have hmem : v + h ∈ closedBall v (Real.sqrt m * δ) ↔
              h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ) := by
            rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
              sub_zero]
          by_cases hh : h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ)
          · rw [indicator_of_mem (hmem.2 hh), indicator_of_mem hh]
          · rw [indicator_of_notMem (mt hmem.1 hh), indicator_of_notMem hh]
    exact h3.trans (mul_le_mul' le_rfl h4)
  -- Step 4: integrate, swap the order of integration, and use the hypothesis
  have hind : ∀ v h : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ =
        (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v := by
    intro v h
    by_cases h1 : v ∈ F <;> by_cases h2 : v + h ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  have hinner : ∀ h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ),
      ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ ≤
        ENNReal.ofReal (C * (Real.sqrt m * δ)) := by
    intro h hh
    have hh' : ‖h‖ ≤ Real.sqrt m * δ := mem_closedBall_zero_iff.1 hh
    calc ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ
        = ∫⁻ v in ball (0 : Euclid m) R, (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v :=
          lintegral_congr fun v => hind v h
      _ ≤ (volume.restrict (ball (0 : Euclid m) R)) (symmDiff ((fun v => v + h) ⁻¹' F) F) :=
          lintegral_indicator_one_le _
      _ = volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) :=
          Measure.restrict_apply' measurableSet_ball
      _ ≤ ENNReal.ofReal (C * ‖h‖) := hsd h (hh'.trans hs1)
      _ ≤ ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh' hC)
  have hmeas2 : Measurable (uncurry fun (v h : Euclid m) =>
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m =>
        F.indicator (fun _ => (1 : ℝ)) p.1 - F.indicator (fun _ => (1 : ℝ)) (p.1 + p.2) :=
      (hu_meas.comp measurable_fst).sub (hu_meas.comp (measurable_fst.add measurable_snd))
    exact this.enorm
  have hV1fin : volume (ball (0 : Euclid m) 1) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v -
        (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_mono fun v => hpt v _ (hQvol v) (hQball v)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ∫⁻ v in ball (0 : Euclid m) R,
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
        rw [lintegral_lintegral_swap (μ := volume.restrict (ball (0 : Euclid m) R))
          (ν := volume.restrict (closedBall (0 : Euclid m) (Real.sqrt m * δ)))
          hmeas2.aemeasurable]
    _ ≤ ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
        mul_le_mul' le_rfl (setLIntegral_mono measurable_const hinner)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * (ENNReal.ofReal (C * (Real.sqrt m * δ)) *
          (ENNReal.ofReal ((Real.sqrt m * δ) ^ m) * volume (ball (0 : Euclid m) 1))) := by
        rw [setLIntegral_const, Measure.addHaar_closedBall _ _ hs0, finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal (Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ) := by
        have e1 : Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ =
            ((δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m) *
              (volume (ball (0 : Euclid m) 1)).toReal := by
          rw [mul_pow]
          field_simp
          ring
        rw [e1, ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m)
            (by positivity), ENNReal.ofReal_toReal hV1fin,
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ))) (by positivity),
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹) (by positivity)]
        ring
/-- Common convergent subsequence for countably many bounded real sequences.  The points
`xᵢ = (b_k(i))_k` lie in the product `Π_k [-M_k, M_k]`, which is compact (Tychonoff,
`isCompact_univ_pi`); `ℝ^ι` is first countable since `ι` is countable, so `IsCompact.tendsto_subseq`
gives a strictly increasing `σ` and a limit `a` with `x_{σ(i)} → a`.  Evaluation at `k` is
continuous, hence `b_k(σ(i)) → a(k)` for every `k`. -/
theorem Submission.codim1_zsl_pc_diagonal_subseq : ∀ (ι : Type) [Countable ι] (b : ι → ℕ → ℝ) (M : ι → ℝ), (∀ k i, |b k i| ≤ M k) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ k, ∃ L : ℝ, Tendsto (fun i => b k (σ i)) atTop (𝓝 L) := by
  intro ι _ b M hb
  have hS : IsCompact (Set.pi univ (fun k => Icc (-M k) (M k))) :=
    isCompact_univ_pi (fun k => isCompact_Icc)
  have hx : ∀ i, (fun k => b k i) ∈ Set.pi univ (fun k => Icc (-M k) (M k)) := by
    intro i
    rw [Set.mem_univ_pi]
    intro k
    exact Set.mem_Icc.mpr (abs_le.mp (hb k i))
  obtain ⟨a, -, σ, hσ, hlim⟩ := hS.tendsto_subseq hx
  exact ⟨σ, hσ, fun k => ⟨a k, ((continuous_apply k).tendsto a).comp hlim⟩⟩
/-- Sets that are Cauchy in measure on every ball have a subsequence converging in measure on
every ball to a measurable set.  With `N_l` chosen for `R = l + 1`, `η = 2⁻ˡ`, the subsequence
`σ(l) = l + Σ_{k ≤ l} N_k` makes `E_l = (F_{σ(l+1)} Δ F_{σ(l)}) ∩ B_{l+1}(0)` summable in measure,
so by Borel–Cantelli (`ae_eventually_notMem`) a.e. `v` lies in only finitely many `E_l`.  For such
`v`, membership in `F_{σ(l)}` is eventually constant and equals membership in the liminf
`F' = ⋃_{l₀} ⋂_{l ≥ l₀} F_{σ(l)}`.  Continuity from above (`tendsto_measure_iInter_atTop`) on the
finite-measure ball `B_R(0)`, applied to `⋃_{l ≥ l₀} (F_{σ(l)} Δ F') ∩ B_R(0)`, concludes. -/
theorem Submission.codim1_zsl_pc_cauchy_limit_set : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hF hC
  -- Fast subsequence: `N l` works for `R = l + 1`, `η = 2⁻ˡ`, and `N l ≤ σ l'` for `l ≤ l'`.
  have hN : ∀ l : ℕ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) ((l : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ l) :=
    fun l => hC ((l : ℝ) + 1) (by positivity) ((1 / 2 : ℝ) ^ l) (by positivity)
  choose N hN using hN
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, ∀ l, σ l = l + ∑ k ∈ Finset.range (l + 1), N k :=
    ⟨_, fun _ => rfl⟩
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro l
    simp only [hσ, Finset.sum_range_succ]
    omega
  have hσge : ∀ l l', l ≤ l' → N l ≤ σ l' := by
    intro l l' h
    have h1 : N l ≤ ∑ k ∈ Finset.range (l' + 1), N k :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    rw [hσ]
    omega
  -- The limit set: the points lying in `F (σ l)` for all large `l`.
  obtain ⟨F', hF'eq⟩ : ∃ F' : Set (Euclid m), F' = ⋃ l₀ : ℕ, ⋂ l : ℕ, ⋂ (_ : l₀ ≤ l), F (σ l) :=
    ⟨_, rfl⟩
  have hF'meas : MeasurableSet F' := by
    rw [hF'eq]
    exact MeasurableSet.iUnion fun l₀ => MeasurableSet.iInter fun l =>
      MeasurableSet.iInter fun _ => hF _
  have hF'mem : ∀ v, v ∈ F' ↔ ∃ l₀, ∀ l, l₀ ≤ l → v ∈ F (σ l) := by
    intro v
    rw [hF'eq]
    simp only [mem_iUnion, mem_iInter]
  -- The transition sets `E l` have summable measures.
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set (Euclid m), ∀ l,
      E l = symmDiff (F (σ (l + 1))) (F (σ l)) ∩ ball (0 : Euclid m) ((l : ℝ) + 1) :=
    ⟨_, fun _ => rfl⟩
  have hEle : ∀ l, volume (E l) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ l) := by
    intro l
    rw [hE]
    exact hN l _ _ (hσge l (l + 1) (Nat.le_succ l)) (hσge l l le_rfl)
  have hsum : ∑' l, volume (E l) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  -- Borel–Cantelli: a.e. `v` is eventually outside `F (σ l) Δ F'`.
  have hae : ∀ᵐ v ∂(volume : Measure (Euclid m)),
      ∀ᶠ l in atTop, v ∉ symmDiff (F (σ l)) F' := by
    filter_upwards [ae_eventually_notMem hsum] with v hv
    have hball : ∀ᶠ l : ℕ in atTop, v ∈ ball (0 : Euclid m) ((l : ℝ) + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_gt ‖v‖
      filter_upwards [eventually_ge_atTop n] with l hl
      rw [mem_ball_zero_iff]
      have : (n : ℝ) ≤ l := Nat.cast_le.mpr hl
      linarith
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp (hv.and hball)
    have hstep : ∀ l, l₁ ≤ l → (v ∈ F (σ (l + 1)) ↔ v ∈ F (σ l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hl₁ l hl
      rw [hE] at h1
      have h3 : v ∉ symmDiff (F (σ (l + 1))) (F (σ l)) := fun h => h1 (Set.mem_inter h h2)
      rw [Set.mem_symmDiff] at h3
      tauto
    have hconst : ∀ l, l₁ ≤ l → (v ∈ F (σ l) ↔ v ∈ F (σ l₁)) := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => exact Iff.rfl
      | succ l hl ih => exact (hstep l hl).trans ih
    have hF'iff : v ∈ F' ↔ v ∈ F (σ l₁) := by
      rw [hF'mem]
      constructor
      · rintro ⟨l₀, hl₀⟩
        exact (hconst (max l₀ l₁) (le_max_right _ _)).mp (hl₀ _ (le_max_left _ _))
      · intro h
        exact ⟨l₁, fun l hl => (hconst l hl).mpr h⟩
    filter_upwards [eventually_ge_atTop l₁] with l hl
    rw [Set.mem_symmDiff]
    have := hconst l hl
    tauto
  refine ⟨σ, F', hσmono, hF'meas, fun R => ?_⟩
  -- Continuity from above for the tails `G l₀` inside the finite-measure ball `B_R(0)`.
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Set (Euclid m), ∀ l₀,
      G l₀ = ⋃ l : ℕ, ⋃ (_ : l₀ ≤ l), symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R :=
    ⟨_, fun _ => rfl⟩
  have hGmem : ∀ l₀ v, v ∈ G l₀ ↔ ∃ l, l₀ ≤ l ∧ v ∈ symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R := by
    intro l₀ v
    rw [hG]
    simp only [mem_iUnion, exists_prop]
  have hGmeas : ∀ l₀, NullMeasurableSet (G l₀) volume := by
    intro l₀
    rw [hG]
    exact (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ =>
      ((hF _).symmDiff hF'meas).inter measurableSet_ball).nullMeasurableSet
  have hGanti : Antitone G := by
    intro a b hab v hv
    rw [hGmem] at hv ⊢
    obtain ⟨l, hl, hv⟩ := hv
    exact ⟨l, hab.trans hl, hv⟩
  have hGfin : ∃ i, volume (G i) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclid m)) (r := R)).ne (measure_mono ?_)⟩
    intro v hv
    rw [hGmem] at hv
    obtain ⟨l, _, hv⟩ := hv
    exact hv.2
  have hGnull : volume (⋂ l₀, G l₀) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    intro v hv
    rw [mem_iInter] at hv
    intro hev
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp hev
    obtain ⟨l, hl, hvl⟩ := (hGmem l₁ v).mp (hv l₁)
    exact hl₁ l hl hvl.1
  have hGlim := tendsto_measure_iInter_atTop hGmeas hGanti hGfin
  rw [hGnull] at hGlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim (fun _ => zero_le) ?_
  intro l
  exact measure_mono (fun v hv => (hGmem l v).mpr ⟨l, le_rfl, hv⟩)

/-- Compactness from a uniform translation estimate: the precompactness part of Simon Ch. 2, 2.6,
proved with cube averages (Hanche-Olsen–Holden, Expo. Math. 28 (2010), Theorem 5).  The averages
`b_{(l,z)}(i) = Lᵐ(Fᵢ ∩ Q_{l,z})/δₗᵐ ∈ [0, 1]` over the grid cubes `Q_{l,z}` of side
`δₗ = 1/((l+1)(m+1))` all converge along one diagonal subsequence `σ₀`.  On `B_R`, the cube
average bound (`2KCδₗ`) and dominated convergence for the step functions make `F_{σ₀ i}` Cauchy
in measure, and `codim1_zsl_pc_cauchy_limit_set` extracts a further subsequence and the limit. -/
theorem Submission.codim1_zsl_pc_compact_of_translation : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ i in atTop, ∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F i) (F i) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hFm hT
  obtain ⟨K, hK0, hK⟩ := Submission.codim1_zsl_pc_cube_average_bound m
  -- Step 1: the scales `δ l`
  obtain ⟨δ, hδpos, hδsqrt, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ l, 0 < δ l) ∧ (∀ l, δ l * Real.sqrt m ≤ 1) ∧
      Tendsto δ atTop (𝓝 0) := by
    have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hsq : Real.sqrt m ≤ (m:ℝ) + 1 := by
      have h1 : (m:ℝ) ≤ ((m:ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      calc Real.sqrt m ≤ Real.sqrt (((m:ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (m:ℝ) + 1 := Real.sqrt_sq hm1.le
    refine ⟨fun l => 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1), fun l => by positivity, fun l => ?_, ?_⟩
    · have hl1 : (0:ℝ) < (l:ℝ) + 1 := by positivity
      calc 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1) * Real.sqrt m
          ≤ 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1) * ((m:ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 1 / ((l:ℝ) + 1) := div_mul_cancel₀ _ hm1.ne'
        _ ≤ 1 := by
            rw [div_le_one hl1]
            linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.div_const ((m:ℝ) + 1)
      rwa [zero_div] at h
  -- Step 2: grid cubes and cube averages
  set Q : ℕ → (Fin m → ℤ) → Set (Euclid m) := fun l z => {w : Euclid m | ∀ j, ⌊w j / δ l⌋ = z j}
    with hQ
  have hQvol : ∀ l (z : Fin m → ℤ), volume (Q l z) ≤ ENNReal.ofReal (δ l ^ m) := by
    intro l z
    have hQeq : Q l z = (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((z j : ℝ) * δ l) (((z j : ℝ) + 1) * δ l)) := by
      ext w
      simp only [hQ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Ico]
      refine forall_congr' fun j => ?_
      rw [Int.floor_eq_iff, le_div_iff₀ (hδpos l), div_lt_iff₀ (hδpos l)]
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (MeasurableSet.univ_pi fun j => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
    have hsub : ∀ j : Fin m, ((z j : ℝ) + 1) * δ l - (z j : ℝ) * δ l = δ l := fun j => by ring
    simp only [hsub, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (hδpos l).le m).ge
  set b : ℕ × (Fin m → ℤ) → ℕ → ℝ := fun k i => (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m
    with hb
  have hb01 : ∀ k i, 0 ≤ b k i ∧ b k i ≤ 1 := by
    intro k i
    have hpos : 0 < δ k.1 ^ m := pow_pos (hδpos k.1) m
    show 0 ≤ (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m ∧
      (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m ≤ 1
    refine ⟨div_nonneg ENNReal.toReal_nonneg hpos.le, ?_⟩
    rw [div_le_one hpos]
    exact ENNReal.toReal_le_of_le_ofReal hpos.le
      ((measure_mono inter_subset_right).trans (hQvol k.1 k.2))
  -- Step 3: diagonal subsequence
  obtain ⟨σ₀, hσ₀, hL⟩ := Submission.codim1_zsl_pc_diagonal_subseq (ℕ × (Fin m → ℤ)) b
    (fun _ => 1) (fun k i => (abs_le.2 ⟨by linarith [(hb01 k i).1], (hb01 k i).2⟩ : |b k i| ≤ 1))
  choose L hL using hL
  have hL01 : ∀ k, 0 ≤ L k ∧ L k ≤ 1 := fun k =>
    ⟨ge_of_tendsto' (hL k) (fun i => (hb01 k (σ₀ i)).1),
      le_of_tendsto' (hL k) (fun i => (hb01 k (σ₀ i)).2)⟩
  -- measurability of the floor map and of coordinates
  have hfloor : Measurable (Int.floor : ℝ → ℤ) :=
    measurable_to_countable' fun n => by
      rw [Int.preimage_floor_singleton]
      exact measurableSet_Ico
  have hcoord : ∀ j : Fin m, Measurable (fun v : Euclid m => v j) := fun j =>
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin m → ℝ))
  -- Step 4: the subsequence is Cauchy in `L¹_loc`
  have hCauchy : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F (σ₀ i)) (F (σ₀ j)) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η := by
    intro R hR η hη
    obtain ⟨C, hC⟩ := hT R hR
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hC
    have hC'0 : (0:ℝ) ≤ max C 0 := le_max_right _ _
    have htrans : ∀ i, i₀ ≤ i → ∀ h : Euclid m, ‖h‖ ≤ 1 →
        volume (symmDiff ((fun v => v + h) ⁻¹' F (σ₀ i)) (F (σ₀ i)) ∩ ball (0 : Euclid m) R) ≤
          ENNReal.ofReal (max C 0 * ‖h‖) := by
      intro i hi h hh
      exact (hi₀ (σ₀ i) (le_trans hi (hσ₀.id_le i)) h hh).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    have hKC : 0 ≤ K * max C 0 := mul_nonneg hK0 hC'0
    have hlim0 : Tendsto (fun l => K * max C 0 * δ l) atTop (𝓝 0) := by
      have h := hδlim.const_mul (K * max C 0)
      rwa [mul_zero] at h
    obtain ⟨l, hl⟩ := (hlim0.eventually (gt_mem_nhds (show (0:ℝ) < η / 4 by positivity))).exists
    have hKCδ : 0 ≤ K * max C 0 * δ l := mul_nonneg hKC (hδpos l).le
    set kf : Euclid m → (Fin m → ℤ) := fun v j => ⌊v j / δ l⌋ with hkf
    have hkf_meas : Measurable kf := by
      rw [measurable_pi_iff]
      intro j
      exact hfloor.comp ((hcoord j).div_const (δ l))
    have hmeasA : ∀ i, Measurable (fun v => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) := fun i =>
      (measurable_of_countable (fun z : Fin m → ℤ => ‖b (l, z) (σ₀ i) - L (l, z)‖ₑ)).comp hkf_meas
    have hmeasU : ∀ i, Measurable
        (fun v => ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ) := fun i =>
      ((measurable_const.indicator (hFm (σ₀ i))).sub
        ((measurable_of_countable (fun z : Fin m → ℤ => b (l, z) (σ₀ i))).comp hkf_meas)).enorm
    have hDCT : Tendsto (fun i => ∫⁻ v in ball (0 : Euclid m) R,
        ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) atTop (𝓝 0) := by
      have hbound : ∀ i, (fun v => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ)
          ≤ᵐ[volume.restrict (ball (0 : Euclid m) R)] (fun _ => (1 : ℝ≥0∞)) := by
        intro i
        refine ae_of_all _ (fun v => ?_)
        have h1 := hb01 (l, kf v) (σ₀ i)
        have h2 := hL01 (l, kf v)
        show ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ ≤ 1
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2
          (abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩)
      have hfin : ∫⁻ _, (1 : ℝ≥0∞) ∂(volume.restrict (ball (0 : Euclid m) R)) ≠ ∞ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
        exact measure_ball_lt_top.ne
      have hlim : ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid m) R)),
          Tendsto (fun i => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) atTop (𝓝 0) := by
        refine ae_of_all _ (fun v => ?_)
        have h := ((hL (l, kf v)).sub_const (L (l, kf v))).enorm
        rwa [sub_self, enorm_zero] at h
      have h := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hmeasA hbound
        hfin hlim
      rwa [lintegral_zero] at h
    obtain ⟨i₁, hi₁⟩ := ENNReal.tendsto_atTop_zero.1 hDCT (ENNReal.ofReal (η / 8))
      (ENNReal.ofReal_pos.2 (by positivity))
    refine ⟨max i₀ i₁, fun i j hi hj => ?_⟩
    have hi0 : i₀ ≤ i := le_trans (le_max_left _ _) hi
    have hj0 : i₀ ≤ j := le_trans (le_max_left _ _) hj
    have hi1 : i₁ ≤ i := le_trans (le_max_right _ _) hi
    have hj1 : i₁ ≤ j := le_trans (le_max_right _ _) hj
    have cube_i : ∫⁻ v in ball (0 : Euclid m) R,
        ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ ≤
          ENNReal.ofReal (K * max C 0 * δ l) :=
      hK (F (σ₀ i)) R (max C 0) (δ l) (hFm _) hC'0 (hδpos l) (hδsqrt l) (htrans i hi0)
    have cube_j : ∫⁻ v in ball (0 : Euclid m) R,
        ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ ≤
          ENNReal.ofReal (K * max C 0 * δ l) :=
      hK (F (σ₀ j)) R (max C 0) (δ l) (hFm _) hC'0 (hδpos l) (hδsqrt l) (htrans j hj0)
    have dct_i : ∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ ≤
        ENNReal.ofReal (η / 8) := hi₁ i hi1
    have dct_j : ∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ ≤
        ENNReal.ofReal (η / 8) := hi₁ j hj1
    have tri : ∀ a b c d e : ℝ, ‖a - e‖ₑ ≤ ‖a - b‖ₑ + ‖b - c‖ₑ + ‖d - c‖ₑ + ‖e - d‖ₑ := by
      intro a b c d e
      have h1 : a - e = (a - b) + (b - c) - (d - c) - (e - d) := by ring
      rw [h1]
      exact enorm_sub_le.trans (add_le_add (enorm_sub_le.trans (add_le_add (enorm_add_le _ _)
        le_rfl)) le_rfl)
    have hS : MeasurableSet (symmDiff (F (σ₀ i)) (F (σ₀ j))) := (hFm _).symmDiff (hFm _)
    have hpt : ∀ v, (symmDiff (F (σ₀ i)) (F (σ₀ j))).indicator (1 : Euclid m → ℝ≥0∞) v ≤
        ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ
          + ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ + ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ
          + ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ := by
      intro v
      refine le_trans ?_ (tri _ _ _ _ _)
      by_cases h1 : v ∈ F (σ₀ i) <;> by_cases h2 : v ∈ F (σ₀ j) <;>
        simp [Set.mem_symmDiff, h1, h2]
    calc volume (symmDiff (F (σ₀ i)) (F (σ₀ j)) ∩ ball (0 : Euclid m) R)
        = ∫⁻ v in ball (0 : Euclid m) R,
            (symmDiff (F (σ₀ i)) (F (σ₀ j))).indicator (1 : Euclid m → ℝ≥0∞) v := by
          rw [lintegral_indicator_one hS, Measure.restrict_apply hS]
      _ ≤ ∫⁻ v in ball (0 : Euclid m) R,
            (‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ
              + ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ + ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ
              + ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ) :=
          lintegral_mono hpt
      _ = (∫⁻ v in ball (0 : Euclid m) R,
              ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R,
              ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ) := by
          rw [lintegral_add_right _ (hmeasU j), lintegral_add_right _ (hmeasA j),
            lintegral_add_right _ (hmeasA i)]
      _ ≤ ENNReal.ofReal (K * max C 0 * δ l) + ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8)
            + ENNReal.ofReal (K * max C 0 * δ l) :=
          add_le_add (add_le_add (add_le_add cube_i dct_i) dct_j) cube_j
      _ ≤ ENNReal.ofReal η := by
          have e2 : (0:ℝ) ≤ η / 8 := by positivity
          rw [← ENNReal.ofReal_add hKCδ e2,
            ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ K * max C 0 * δ l + η / 8) e2,
            ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ K * max C 0 * δ l + η / 8 + η / 8) hKCδ]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Step 5: extract a convergent subsequence
  obtain ⟨σ₁, F', hσ₁, hF', hlim⟩ :=
    Submission.codim1_zsl_pc_cauchy_limit_set m (fun i => F (σ₀ i)) (fun i => hFm _) hCauchy
  exact ⟨σ₀ ∘ σ₁, F', hσ₀.comp hσ₁, hF', hlim⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
