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

/-- **Smooth cutoff function** (the cutoff `ζ` with `X(ζ ·)` extending a current from `U` to
`ℝᴾ`).  If `U ⊆ ℝᴾ` is open and `K ⊆ U` is compact, there is a `C^∞` function `ζ` with
`0 ≤ ζ ≤ 1`, compact support `spt ζ ⊆ U`, and `ζ = 1` on an open set `N ⊇ K`.  Choose open sets
`V₁ ⊇ K` and `V₂ ⊇ closure V₁` with compact closures in `U`; the smooth Urysohn lemma gives `ζ`
with values in `[0, 1]`, `support ζ = V₂` and `ζ = 1` exactly on `closure V₁`.  Then
`spt ζ = closure V₂` and `N = V₁` work. -/
theorem Submission.cbrcs_ce_smooth_cutoff : ∀ (P : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ (ζ : Euclid P → ℝ) (N : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ U ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ IsOpen N ∧ K ⊆ N ∧ ∀ x ∈ N, ζ x = 1 := by
  intro P U K hU hK hKU
  -- Step 1: an open `V₁ ⊇ K` with compact closure inside `U`
  obtain ⟨V₁, hV₁open, hKV₁, hV₁U, hV₁compact⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  -- Step 2: an open `V₂ ⊇ closure V₁` with compact closure inside `U`
  obtain ⟨V₂, hV₂open, hV₁V₂, hV₂U, hV₂compact⟩ :=
    exists_open_between_and_isCompact_closure hV₁compact hU hV₁U
  -- Step 3: the smooth Urysohn function for `closure V₁ ⊆ V₂`
  obtain ⟨ζ, hζsmooth, hζrange, hζsupport, hζone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₂open isClosed_closure hV₁V₂
  -- Step 4: `spt ζ = closure V₂`, compact and contained in `U`
  have htsupport : tsupport ζ = closure V₂ := by
    rw [tsupport, hζsupport]
  refine ⟨ζ, V₁, hζsmooth, ?_, htsupport ▸ hV₂U, ?_, hV₁open, hKV₁, ?_⟩
  · rw [HasCompactSupport, htsupport]
    exact hV₂compact
  · -- Step 5: `ζ` takes values in `[0, 1]`
    intro x
    exact hζrange (mem_range_self x)
  · -- Step 6: `ζ = 1` on `N = V₁ ⊆ closure V₁`
    intro x hx
    exact (hζone x).1 (subset_closure hx)
/-- **Leibniz estimate for `f • g`** (used in the closure step of Simon 7.2.4 to show that
multiplication by a smooth cutoff `ζ` is continuous on test forms).  For `C^∞` maps
`f : ℝᴾ → ℝ` and `g : ℝᴾ → Λᵏ`, `‖Dⁿ(f • g)(x)‖ ≤ ∑ᵢ C(n, i) ‖Dⁱf(x)‖ ‖Dⁿ⁻ⁱg(x)‖`.  This is
Mathlib's `norm_iteratedFDeriv_smul_le`, whose file is outside the frozen imports, so it is
proved by the same induction: for a continuous bilinear `B` with `‖B u v‖ ≤ c ‖u‖ ‖v‖`,
`‖Dⁿ B(a, b)(x)‖ ≤ c ∑ᵢ C(n, i) ‖Dⁱa(x)‖ ‖Dⁿ⁻ⁱb(x)‖` for all target spaces, by induction on `n`:
`D B(a, b) = B.precompR (a, Db) + B.precompL (Da, b)`, both bilinear maps are again bounded by
`c`, and Pascal's rule combines the two bounds.  Then take `B = lsmul` and `c = 1`. -/
theorem Submission.cbrcs_ce_leibniz_smul_bound : ∀ (P k n : ℕ) (f : Euclid P → ℝ) (g : DifferentialForm (Euclid P) k) (x : Euclid P), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g → ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by
  intro P k n f g x hf hg
  -- Step 1: the bilinear estimate `(A_n)`, by induction on `n` over all target spaces
  have aux : ∀ (n : ℕ) (E F G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : E →L[ℝ] F →L[ℝ] G) (c : ℝ) (a : Euclid P → E) (b : Euclid P → F), 0 ≤ c →
      (∀ u v, ‖B u v‖ ≤ c * ‖u‖ * ‖v‖) → ContDiff ℝ (⊤ : ℕ∞) a → ContDiff ℝ (⊤ : ℕ∞) b →
      ‖iteratedFDeriv ℝ n (fun y => B (a y) (b y)) x‖ ≤
        c * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
          ‖iteratedFDeriv ℝ (n - i) b x‖ := by
    intro n
    induction n with
    | zero =>
      -- Step 2: for `n = 0` this is the hypothesis on `B` at `(a x, b x)`
      intro E F G _ _ _ _ _ _ B c a b _ hB _ _
      simp only [norm_iteratedFDeriv_zero, zero_add, Finset.range_one, Finset.sum_singleton,
        Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
      exact hB _ _
    | succ n IH =>
      intro E F G _ _ _ _ _ _ B c a b hc hB ha hb
      -- Step 3: `a`, `b` are differentiable and `Da`, `Db` are smooth
      obtain ⟨ha₁, hDa⟩ := contDiff_infty_iff_fderiv.1 ha
      obtain ⟨hb₁, hDb⟩ := contDiff_infty_iff_fderiv.1 hb
      -- Step 4: `B₁ = B.precompR` and `B₂ = B.precompL` are bounded with the same constant `c`
      have hB₁ : ∀ (u : E) (L : Euclid P →L[ℝ] F),
          ‖B.precompR (Euclid P) u L‖ ≤ c * ‖u‖ * ‖L‖ := by
        intro u L
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
          ContinuousLinearMap.comp_apply]
        calc ‖B u (L v)‖ ≤ c * ‖u‖ * ‖L v‖ := hB _ _
          _ ≤ c * ‖u‖ * (‖L‖ * ‖v‖) := by gcongr; exact L.le_opNorm v
          _ = c * ‖u‖ * ‖L‖ * ‖v‖ := by ring
      have hB₂ : ∀ (L : Euclid P →L[ℝ] E) (w : F),
          ‖B.precompL (Euclid P) L w‖ ≤ c * ‖L‖ * ‖w‖ := by
        intro L w
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
        rw [ContinuousLinearMap.precompL_apply]
        calc ‖B (L v) w‖ ≤ c * ‖L v‖ * ‖w‖ := hB _ _
          _ ≤ c * (‖L‖ * ‖v‖) * ‖w‖ := by gcongr; exact L.le_opNorm v
          _ = c * ‖L‖ * ‖w‖ * ‖v‖ := by ring
      -- Step 5: the product rule `Dh = B₁ (a, Db) + B₂ (Da, b)`
      have hD : fderiv ℝ (fun y => B (a y) (b y)) = fun y =>
          B.precompR (Euclid P) (a y) (fderiv ℝ b y) +
            B.precompL (Euclid P) (fderiv ℝ a y) (b y) := by
        funext y
        exact B.fderiv_of_bilinear (ha₁ y) (hb₁ y)
      -- Step 6: both terms are smooth, so `Dⁿ` of the sum is the sum of the `Dⁿ`
      have hA₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y => B.precompR (Euclid P) (a y) (fderiv ℝ b y)) :=
        (B.precompR (Euclid P)).isBoundedBilinearMap.contDiff.comp₂ ha hDb
      have hA₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y => B.precompL (Euclid P) (fderiv ℝ a y) (b y)) :=
        (B.precompL (Euclid P)).isBoundedBilinearMap.contDiff.comp₂ hDa hb
      -- Step 7: the first term, by `(A_n)` for `B₁`
      have I₁ : ‖iteratedFDeriv ℝ n (fun y => B.precompR (Euclid P) (a y) (fderiv ℝ b y)) x‖ ≤
          c * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i a x‖ *
            ‖iteratedFDeriv ℝ (n + 1 - i) b x‖ := by
        refine (IH E (Euclid P →L[ℝ] F) (Euclid P →L[ℝ] G) (B.precompR (Euclid P)) c a
          (fderiv ℝ b) hc hB₁ ha hDb).trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), norm_iteratedFDeriv_fderiv]
      -- Step 8: the second term, by `(A_n)` for `B₂`
      have I₂ : ‖iteratedFDeriv ℝ n (fun y => B.precompL (Euclid P) (fderiv ℝ a y) (b y)) x‖ ≤
          c * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ (i + 1) a x‖ *
            ‖iteratedFDeriv ℝ (n - i) b x‖ := by
        refine (IH (Euclid P →L[ℝ] E) F (Euclid P →L[ℝ] G) (B.precompL (Euclid P)) c
          (fderiv ℝ a) b hc hB₂ hDa hb).trans (le_of_eq ?_)
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_iteratedFDeriv_fderiv]
      -- Step 9: combine with Pascal's rule
      rw [← norm_iteratedFDeriv_fderiv, hD,
        fun_iteratedFDeriv_add_apply (contDiff_infty.1 hA₁ n).contDiffAt
          (contDiff_infty.1 hA₂ n).contDiffAt]
      refine (norm_add_le _ _).trans ((add_le_add I₁ I₂).trans (le_of_eq ?_))
      simp_rw [← mul_add, mul_assoc]
      congr 1
      exact (Finset.sum_choose_succ_mul
        (fun i j => ‖iteratedFDeriv ℝ i a x‖ * ‖iteratedFDeriv ℝ j b x‖) n).symm
  -- Step 10: specialize to `B = lsmul`, `c = 1`
  have h := aux n ℝ (Covector (Euclid P) k) (Covector (Euclid P) k)
    (ContinuousLinearMap.lsmul ℝ ℝ) 1 f g zero_le_one
    (fun t v => by
      rw [ContinuousLinearMap.lsmul_apply, norm_smul, one_mul]) hf hg
  simpa only [ContinuousLinearMap.lsmul_apply, one_mul] using h

/-- **Multiplication by a smooth cutoff is continuous on test forms** (the map `M_k` in the closure
step of Simon 7.2.4).  For `ζ ∈ C^∞_c(ℝᴾ)` with `spt ζ ⊆ U`, `ω ↦ ζω` is an `ℝ`-linear map
`𝒟ᵏ(ℝᴾ) → 𝒟ᵏ(U)` taking `ωⱼ → 0` to `ζωⱼ → 0`.  All `ζωⱼ` are supported in the compact set
`spt ζ ⊆ U`; each `Dˡζ` is bounded, each `Dˡωⱼ → 0` uniformly on all of `ℝᴾ` (it vanishes off
a compact set containing every `spt ωⱼ`), and the Leibniz estimate
`‖Dⁱ(ζωⱼ)‖ ≤ ∑ₗ C(i, l) ‖Dˡζ‖ ‖Dⁱ⁻ˡωⱼ‖` gives `Dⁱ(ζωⱼ) → 0` uniformly. -/
theorem Submission.cbrcs_ce_cutoff_multiplier : ∀ (P k : ℕ) (U : Set (Euclid P)) (ζ : Euclid P → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ → tsupport ζ ⊆ U → ∃ M : TestFormOn (univ : Set (Euclid P)) k →ₗ[ℝ] TestFormOn U k, (∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (x : Euclid P), (M ω : DifferentialForm (Euclid P) k) x = ζ x • (ω : DifferentialForm (Euclid P) k) x) ∧ ∀ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) k, TestFormOnConverges ωs 0 → TestFormOnConverges (fun j => M (ωs j)) 0 := by
  intro P k U ζ hζ hζc hζU
  -- Steps 1–2: `ζω` is a test form in `U` and `ω ↦ ζω` is `ℝ`-linear
  obtain ⟨M, hM⟩ : ∃ M : TestFormOn (univ : Set (Euclid P)) k →ₗ[ℝ] TestFormOn U k,
      ∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (x : Euclid P),
        (M ω : DifferentialForm (Euclid P) k) x = ζ x • (ω : DifferentialForm (Euclid P) k) x :=
    ⟨{ toFun := fun ω => ⟨fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x,
          ⟨⟨hζ.smul ω.property.1.1, hζc.smul_right⟩, (tsupport_smul_subset_left _ _).trans hζU⟩⟩
       map_add' := fun ω η => Subtype.ext <| funext fun x => smul_add _ _ _
       map_smul' := fun c ω => Subtype.ext <| funext fun x => smul_comm (ζ x) c _ }, fun _ _ => rfl⟩
  refine ⟨M, hM, fun ωs hωs => ?_⟩
  have hMfun : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, (M ω : DifferentialForm (Euclid P) k) =
      fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x :=
    fun ω => funext (hM ω)
  -- Step 3: a compact set `K'` carries all `spt ωⱼ`, and `Dˡωⱼ → 0` uniformly on `K'`
  obtain ⟨K', -, -, hK', -, hconv⟩ := hωs
  -- Step 4: every `Dˡζ` is bounded by some `B l ≥ 0`
  have hBex : ∀ l : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ l ζ x‖ ≤ B := by
    intro l
    obtain ⟨B, hB⟩ := (hζ.continuous_iteratedFDeriv (m := l) (by exact_mod_cast le_top)
      ).bounded_above_of_compact_support (hζc.iteratedFDeriv l)
    exact ⟨max B 0, le_max_right _ _, fun x => (hB x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  -- Step 5: eventually `‖Dˡωⱼ(x)‖ < δ` for all `x ∈ ℝᴾ` (`Dˡωⱼ` vanishes off `spt ωⱼ ⊆ K'`)
  have hsmall : ∀ l : ℕ, ∀ δ > 0, ∀ᶠ j in atTop, ∀ x,
      ‖iteratedFDeriv ℝ l (ωs j : DifferentialForm (Euclid P) k) x‖ < δ := by
    intro l δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconv l) δ hδ] with j hj x
    by_cases hx : x ∈ K'
    · simpa using hj x hx
    · rw [notMem_support.1 fun h => hx (hK' j (support_iteratedFDeriv_subset l h)), norm_zero]
      exact hδ
  -- Step 3 (cont.): the compact set `spt ζ ⊆ U` contains every `spt (ζωⱼ)` and `spt 0 = ∅`
  refine ⟨tsupport ζ, hζc, hζU, fun j => ?_, by simp, fun i => ?_⟩
  · rw [hMfun]
    exact tsupport_smul_subset_left _ _
  -- Step 6: the Leibniz estimate gives `‖Dⁱ(ζωⱼ)(x)‖ < ε` for all large `j`
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  set C : ℝ := ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * B l with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (hB0 l)
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hev : ∀ᶠ j in atTop, ∀ l ∈ Finset.range (i + 1), ∀ x,
      ‖iteratedFDeriv ℝ (i - l) (ωs j : DifferentialForm (Euclid P) k) x‖ < ε / (C + 1) :=
    (eventually_all_finset _).2 fun l _ => hsmall (i - l) _ hδ
  filter_upwards [hev] with j hj x _
  have h0 : ((0 : TestFormOn U k) : DifferentialForm (Euclid P) k) = 0 := rfl
  rw [h0, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left, hMfun]
  calc ‖iteratedFDeriv ℝ i (fun y => ζ y • (ωs j : DifferentialForm (Euclid P) k) y) x‖
      ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l ζ x‖ *
          ‖iteratedFDeriv ℝ (i - l) (ωs j : DifferentialForm (Euclid P) k) x‖ :=
        Submission.cbrcs_ce_leibniz_smul_bound P k i ζ _ x hζ (ωs j).property.1.1
    _ ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * B l * (ε / (C + 1)) :=
        Finset.sum_le_sum fun l hl => mul_le_mul
          (mul_le_mul_of_nonneg_left (hB l x) (Nat.cast_nonneg _)) (hj l hl x).le
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 l))
    _ = C * (ε / (C + 1)) := by rw [hC, Finset.sum_mul]
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
        nlinarith
/-- **The Euclidean coefficient norm is a continuous seminorm dominated by the operator norm**
(Simon Ch. 6, 1.15 and 2.4; used by the smooth approximation of test forms behind the mass of
`τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})`
for strictly increasing `I : Fin n → Fin P` and `c_I α = 0` otherwise.  Then
`covectorEuclideanNorm α = ‖v α‖` for the coefficient vector
`v α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)`, which is linear in `α`; this gives the
triangle inequality and homogeneity.  `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖` gives the bound with
`C = √(card (Fin n → Fin P))`, and then the norm is `C`-Lipschitz, hence continuous. -/
theorem Submission.rsd_mw_tfa_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
  intro P n
  classical
  -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
    if StrictMono I then α (fun i => e (I i)) else 0
  let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
    WithLp.toLp 2 (fun I => c I α)
  have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [v, c, e, hI]
  -- Step 2: `v` is additive and `ℝ`-homogeneous
  have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
    intro α α'
    simp only [v, ← WithLp.toLp_add]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
    intro t α
    simp only [v, ← WithLp.toLp_smul]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
  have h1 : ∀ α α' : Covector (Euclid P) n,
      covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
    intro α α'
    rw [hN, hN, hN, hadd]
    exact norm_add_le _ _
  -- Step 4: (ii), homogeneity of the Euclidean norm
  have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
  -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
  have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
    intro I α
    by_cases hI : StrictMono I
    · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
    · simp [c, hI]
  -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
  have h3 : ∀ α : Covector (Euclid P) n,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
    intro α
    have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
      Finset.sum_le_sum fun I _ => by
        simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
    rw [hN, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
  have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
      (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
    intro α α'
    have ha : covectorEuclideanNorm α ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
      simpa only [sub_add_cancel] using h1 (α - α') α'
    have hb : covectorEuclideanNorm α' ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
      have h := h1 (α' - α) α
      rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
    have hC := h3 (α - α')
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    constructor <;> linarith
  exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
    (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩
/-- **A triple in `U` carried by a compact `K ⊆ U` is a triple in `ℝᴾ`** (Simon Ch. 6, 3.1; used
to extend a cut-off current from `U` to `ℝᴾ`).  Keep `M`, `θ`, `ξ` and every field of `R` that
does not mention the domain; `M ⊆ ℝᴾ` is trivial.  For compact `K' ⊆ ℝᴾ`, `M ∩ K' ⊆ M ∩ K`
because `M ⊆ K`, so `∫_{M ∩ K'} θ dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞`, the last bound being local
integrability of `θ` in `U` on the compact set `K ⊆ U`. -/
theorem Submission.cbrcs_ce_imrep_lift_univ : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → R.carrier ⊆ K → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = R.carrier ∧ R'.mult = R.mult ∧ R'.orient = R.orient := by
  intro P n U K R hK hKU hRK
  -- Steps 1–3: the same data; only `locallyIntegrable_mult` involves the domain
  refine ⟨{ carrier := R.carrier
            mult := R.mult
            orient := R.orient
            measurableSet_carrier := R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := R.rectifiable
            measurable_mult := R.measurable_mult
            mult_pos := R.mult_pos
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := R.aestronglyMeasurable_orient
            orients := R.orients }, rfl, rfl, rfl⟩
  -- Step 4: `∫_{M ∩ K'} θ ≤ ∫_{M ∩ K} θ < ∞`, as `M ∩ K' ⊆ M ∩ K`
  intro K' _ _
  have hsub : R.carrier ∩ K' ⊆ R.carrier ∩ K := fun x hx => ⟨hx.1, hRK hx.1⟩
  exact ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) (lintegral_mono_set hsub)
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion

/-- **Extension of a current from `U` to `ℝᴾ` by a smooth cutoff** (Simon 6.2.1–6.2.5, 6.2.11;
used in the closure step of 7.2.4).  Fix `ζ ∈ C^∞_c(U)` with `0 ≤ ζ ≤ 1` and `ζ = 1` on an open
`N ⊇ K`, and put `E X(ω) = X(ζω)`; `ω ↦ ζω` is sequentially continuous from `𝒟^{m+1}(ℝᴾ)` to
`𝒟^{m+1}(U)`, so `E X ∈ 𝒟_{m+1}(ℝᴾ)`.  (i) `ζω = ω` when `spt ω ⊆ K`.  (ii) holds pointwise.
(iii) `|ζω| ≤ |ω|`, so `ζω` is admissible for `M(X)` whenever `ω` is admissible for `M(E X)`.
(iv) `spt ζω ⊆ spt ω`, so `E X` kills forms supported away from `K`; and `ζ dη − d(ζη)` vanishes
on `N ⊇ K`, so `∂(E X)(η) = X(ζ dη) = X(d(ζη)) = ∂X(ζη)`.  (v) A triple carried by `K` is a
triple in `ℝᴾ`, and it represents `E X` because `ζ = 1` on its carrier. -/
theorem Submission.cbrcs_cutoff_extension : ∀ (P m : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ K → E X (testFormOnInclusion (subset_univ U) (m + 1) ω) = X ω) ∧ (∀ (Xs : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)), WeaklyConvergesOn Xs X → WeaklyConvergesOn (fun j => E (Xs j)) (E X)) ∧ (∀ X : GeometricCurrentOn U (m + 1), (E X).mass ≤ X.mass) ∧ (∀ X : GeometricCurrentOn U (m + 1), (∀ ω : TestFormOn U (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → X ω = 0) → (E X).support ⊆ K ∧ (E X).boundary.mass ≤ X.boundary.mass) ∧ (∀ (X : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)), R.Represents X → R.carrier ⊆ K → IsIntegerMultiplicity (E X)) := by
  intro P m U K hU hK hKU
  -- Step 1: a cutoff `ζ ∈ C^∞_c(U)` with `0 ≤ ζ ≤ 1` and `ζ = 1` on an open `N ⊇ K`
  obtain ⟨ζ, N, hζ, hζc, hζU, hζ01, hNo, hKN, hζN⟩ :=
    Submission.cbrcs_ce_smooth_cutoff P U K hU hK hKU
  -- Steps 2 and 4: `ω ↦ ζω` in degrees `m + 1` and `m`, continuous in degree `m + 1`
  obtain ⟨M₁, hM₁, hM₁c⟩ := Submission.cbrcs_ce_cutoff_multiplier P (m + 1) U ζ hζ hζc hζU
  obtain ⟨M₀, hM₀, -⟩ := Submission.cbrcs_ce_cutoff_multiplier P m U ζ hζ hζc hζU
  -- Step 3: `|ζ(x) α| = ζ(x) |α| ≤ 1` whenever `|α| ≤ 1`
  have hnorm : ∀ {k : ℕ} (x : Euclid P) (α : Covector (Euclid P) k),
      covectorEuclideanNorm α ≤ 1 → covectorEuclideanNorm (ζ x • α) ≤ 1 := by
    intro k x α hα
    rw [(Submission.rsd_mw_tfa_norm_props P k).2.1, abs_of_nonneg (hζ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg α) (hζ01 x).2).trans hα
  -- Step 5: `E X(ω) = X(ζω)`, a current in `ℝᴾ` because `M₁` is sequentially continuous
  obtain ⟨E, hE⟩ : ∃ E : GeometricCurrentOn U (m + 1) →
      GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      ∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)),
        E X ω = X (M₁ ω) :=
    ⟨fun X => ⟨X.toCurrent ∘ₗ M₁, fun ωs h => X.continuous' _ (hM₁c ωs h)⟩, fun _ _ => rfl⟩
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 6: (i), `ζω = ω` when `spt ω ⊆ K`
    intro X ω hωK
    rw [hE]
    congr 1
    refine Subtype.ext (funext fun x => ?_)
    rw [hM₁, testFormOnInclusion_coe]
    by_cases hx : x ∈ K
    · rw [hζN x (hKN hx), one_smul]
    · rw [image_eq_zero_of_notMem_tsupport fun h => hx (hωK h), smul_zero]
  · -- Step 7: (ii), `E Xⱼ(ω) = Xⱼ(ζω) → X(ζω) = E X(ω)`
    intro Xs X h ω
    simp only [hE]
    exact h (M₁ ω)
  · -- Step 8: (iii), `ζω` is admissible for `M(X)` when `ω` is admissible for `M(E X)`
    intro X
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (E X ω) ≤ X.massOn U
    rw [hE]
    exact X.le_massOn ⟨(M₁ ω).property.2, fun x => by rw [hM₁]; exact hnorm x _ (hω.2 x)⟩
  · intro X hvan
    -- `spt ζω ⊆ spt ω`
    have hspt : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
        tsupport (M₁ ω : DifferentialForm (Euclid P) (m + 1)) ⊆
          tsupport (ω : DifferentialForm (Euclid P) (m + 1)) := by
      intro ω
      rw [show (M₁ ω : DifferentialForm (Euclid P) (m + 1)) =
        fun x => ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x from funext (hM₁ ω)]
      exact tsupport_smul_subset_right _ _
    refine ⟨(Submission.rsd_cmr_support_subset_of_vanish P (m + 1) univ K (E X) isOpen_univ hK
      (subset_univ K) fun ω hω => ?_).1, ?_⟩
    · -- Step 9: (iv), `E X` kills every form supported away from `K`, so `spt (E X) ⊆ K`
      rw [hE]
      exact hvan (M₁ ω) (Set.disjoint_of_subset_left (hspt ω) hω)
    · -- Step 10: (iv), `∂(E X)(η) = ∂X(ζη)` with `ζη` admissible for `M(∂X)`
      refine sSup_le ?_
      rintro r ⟨η, hη, rfl⟩
      show ENNReal.ofReal ((E X).boundary η) ≤ X.boundary.massOn U
      -- `δ = ζ dη − d(ζη)` vanishes on `N`, where `ζη = η` near each point
      have hδ : ∀ y ∈ N, ((M₁ (exteriorDerivativeTestOn univ m η) -
          exteriorDerivativeTestOn U m (M₀ η) : TestFormOn U (m + 1)) :
            DifferentialForm (Euclid P) (m + 1)) y = 0 := by
        intro y hy
        have hev : (M₀ η : DifferentialForm (Euclid P) m) =ᶠ[𝓝 y]
            (η : DifferentialForm (Euclid P) m) := by
          filter_upwards [hNo.mem_nhds hy] with z hz
          rw [hM₀, hζN z hz, one_smul]
        rw [Submodule.coe_sub, Pi.sub_apply, hM₁, hζN y hy, one_smul, sub_eq_zero]
        exact hev.extDeriv_eq.symm
      -- so `spt δ ⊆ ℝᴾ \ N` misses `K`, and `X(ζ dη) = X(d(ζη))`
      have hX : X (M₁ (exteriorDerivativeTestOn univ m η)) =
          X (exteriorDerivativeTestOn U m (M₀ η)) := by
        rw [← sub_eq_zero, ← map_sub]
        exact hvan _ (Set.disjoint_of_subset_left
          (closure_minimal (fun y hy hyN => hy (hδ y hyN)) hNo.isClosed_compl)
          hKN.disjoint_compl_left)
      rw [GeometricCurrentOn.boundary_apply, hE, hX]
      exact X.boundary.le_massOn
        ⟨(M₀ η).property.2, fun x => by rw [hM₀]; exact hnorm x _ (hη.2 x)⟩
  · -- Step 11: (v), the triple lifted to `ℝᴾ` represents `E X`, as `ζ = 1` on its carrier
    intro X R hR hRK
    obtain ⟨R', hc, hm, ho⟩ := Submission.cbrcs_ce_imrep_lift_univ P (m + 1) U K R hK hKU hRK
    refine ⟨R', fun ω => ?_⟩
    rw [hE, hR]
    unfold IMRep.action
    rw [hc, hm, ho]
    refine setIntegral_congr_fun R.measurableSet_carrier fun x hx => ?_
    rw [hM₁, hζN x (hKN (hRK hx)), one_smul]
/-- **Mass localization for a current vanishing away from a compact set** (Simon 7.2.4, proof,
step 4(a)).  Let `C ⊆ V` with `C` compact and `V` open, and let `X ∈ 𝒟ₖ(U)` kill every
`ω ∈ 𝒟ᵏ(U)` with `spt ω ∩ C = ∅`.  Then `M_G(X) ≤ M_V(X)` for every `G`.  Choose a smooth
`χ : ℝᴾ → [0, 1]` with `χ = 1` on an open `N ⊇ C` and `spt χ ⊆ V`.  For `ω` admissible
for `M_G`, `(1 − χ)ω` vanishes on `N`, so `X(ω) = X(χω)`, and `χω` is admissible for `M_V`
because `|χω| = χ|ω| ≤ 1`. -/
theorem Submission.lcmp_massOn_le_of_vanish_off_compact : ∀ (P k : ℕ) (U V C : Set (Euclid P)) (X : GeometricCurrentOn U k), IsCompact C → IsOpen V → C ⊆ V → (∀ ω : TestFormOn U k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) C → X ω = 0) → ∀ G : Set (Euclid P), X.massOn G ≤ X.massOn V := by
  intro P k U V C X hC hV hCV hvan G
  -- Step 4: `|cα| = |c| |α|` for the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
        ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) =
        c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        ring
      · simp
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  -- Step 1: if `C = ∅` then `X = 0`, so `M_G(X) = 0`
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · refine sSup_le ?_
    rintro r ⟨ω, -, rfl⟩
    show ENNReal.ofReal (X ω) ≤ X.massOn V
    rw [hvan ω (disjoint_empty _), ENNReal.ofReal_zero]
    exact zero_le
  -- Step 2: `C ⊆ V' = {dist(·, C) < δ/2}` with `closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hV'o : IsOpen (thickening (δ / 2) C) := isOpen_thickening
  -- Step 3: `χ = τ(2g/a)`, where `{g ≠ 0} = V'`, `a = min_C g > 0`, `τ` the smooth transition
  obtain ⟨g, hgsupp, hgsmooth, hgrange⟩ := hV'o.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hgnn : ∀ x, 0 ≤ g x := fun x => (hgrange ⟨x, rfl⟩).1
  have hgpos : ∀ x ∈ C, 0 < g x := by
    intro x hx
    have hxs : x ∈ support g := by
      rw [hgsupp]
      exact self_subset_thickening (half_pos hδ) C hx
    exact lt_of_le_of_ne (hgnn x) (Ne.symm hxs)
  obtain ⟨x₀, hx₀C, hx₀min⟩ := hC.exists_isMinOn hCne hgsmooth.continuous.continuousOn
  set a := g x₀
  have ha : 0 < a := hgpos x₀ hx₀C
  set χ : Euclid P → ℝ := fun x => Real.smoothTransition (2 * g x / a)
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul hgsmooth).div_const a)
  -- `χ = 1` on the open set `N = {g > a/2} ⊇ C`
  set N : Set (Euclid P) := {x | a / 2 < g x}
  have hNo : IsOpen N := isOpen_lt continuous_const hgsmooth.continuous
  have hCN : C ⊆ N := fun x hx => by
    have h1 : a ≤ g x := hx₀min hx
    show a / 2 < g x
    linarith
  have hχN : ∀ x ∈ N, χ x = 1 := fun x hx => by
    apply Real.smoothTransition.one_of_one_le
    have hx' : a / 2 < g x := hx
    rw [le_div_iff₀ ha]
    linarith
  -- `χ = 0` where `g = 0`, so `spt χ ⊆ closure V' ⊆ {dist(·, C) ≤ δ/2} ⊆ V`
  have hχsupp : support χ ⊆ thickening (δ / 2) C := by
    intro x hx
    by_contra h
    rw [← hgsupp, mem_support, not_not] at h
    apply hx
    show Real.smoothTransition (2 * g x / a) = 0
    rw [h, mul_zero, zero_div]
    exact Real.smoothTransition.zero_of_nonpos le_rfl
  have hclχ : tsupport χ ⊆ cthickening (δ / 2) C :=
    (closure_mono hχsupp).trans (closure_thickening_subset_cthickening _ _)
  have htχ : tsupport χ ⊆ V :=
    hclχ.trans ((cthickening_mono (half_le_self hδ.le) C).trans hδV)
  -- Step 5: for `ω` admissible for `M_G`, `ω₁ = χω ∈ 𝒟ᵏ(U)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ X.massOn V
  have hωt : IsTestForm (ω : DifferentialForm (Euclid P) k) := ω.property.1
  obtain ⟨ω₁f, hω₁f⟩ : ∃ g : DifferentialForm (Euclid P) k,
      g = fun x => χ x • (ω : DifferentialForm (Euclid P) k) x := ⟨_, rfl⟩
  have hω₁smooth : IsSmoothForm ω₁f := by
    rw [hω₁f]
    exact hχsmooth.smul hωt.1
  have hω₁supp : tsupport ω₁f ⊆ tsupport (ω : DifferentialForm (Euclid P) k) := by
    rw [hω₁f]
    exact tsupport_smul_subset_right _ _
  have hω₁suppχ : tsupport ω₁f ⊆ tsupport χ := by
    rw [hω₁f]
    exact tsupport_smul_subset_left _ _
  have hω₁cpt : HasCompactSupport ω₁f :=
    IsCompact.of_isClosed_subset hωt.2 (isClosed_tsupport _) hω₁supp
  let ω₁ : TestFormOn U k := ⟨ω₁f, ⟨hω₁smooth, hω₁cpt⟩, hω₁supp.trans ω.property.2⟩
  -- Step 6: `ω₂ = ω − ω₁` vanishes on `N ⊇ C`, so `spt ω₂ ∩ C = ∅` and `X(ω₂) = 0`
  have hω₂van : X (ω - ω₁) = 0 := by
    apply hvan
    rw [Set.disjoint_left]
    intro x hx hxC
    have hzero : ∀ y ∈ N, ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y = 0 := by
      intro y hy
      have hco : ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) y =
          (ω : DifferentialForm (Euclid P) k) y - ω₁f y := rfl
      rw [hco, hω₁f]
      beta_reduce
      rw [hχN y hy, one_smul, sub_self]
    have hxN : x ∈ N := hCN hxC
    have hnot : x ∉ tsupport ((ω - ω₁ : TestFormOn U k) : DifferentialForm (Euclid P) k) := by
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hNo.mem_nhds hxN] with y hy
      exact hzero y hy
    exact hnot hx
  have hsplit : X ω = X ω₁ := by
    have : X (ω - ω₁) = X ω - X ω₁ := map_sub X.toCurrent ω ω₁
    linarith
  -- Step 5 (cont.): `spt ω₁ ⊆ spt χ ⊆ V` and `|ω₁(x)| = χ(x) |ω(x)| ≤ 1`
  have hadm : ω₁ ∈ massAdmissibleOn U k V := by
    refine ⟨hω₁suppχ.trans htχ, fun x => ?_⟩
    have hco : (ω₁ : DifferentialForm (Euclid P) k) x =
        χ x • (ω : DifferentialForm (Euclid P) k) x := by
      show ω₁f x = _
      rw [hω₁f]
    rw [hco, hsmul]
    have h0 : 0 ≤ χ x := Real.smoothTransition.nonneg _
    have h1 : χ x ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_of_nonneg h0]
    have h2 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
    have h3 := hω.2 x
    nlinarith
  -- Step 7: `ofReal X(ω) = ofReal X(ω₁) ≤ M_V(X)`; take the supremum over `ω`
  rw [hsplit]
  exact X.le_massOn hadm
/-- **Triangle inequality for local mass** (Simon 6.2.5).  If `|c| ≤ 1` and
`Z(ω) = X(ω) + c Y(ω)` for every `ω ∈ 𝒟ᵏ(U)` with `spt ω ⊆ G`, then
`M_G(Z) ≤ M_G(X) + M_G(Y)`.  For `ω` admissible for `M_G`, `−ω` is admissible too, so
`|Y(ω)| ≤ M_G(Y)`; since `c Y(ω) ≤ |Y(ω)|`, `Z(ω) ≤ X(ω) + |Y(ω)| ≤ M_G(X) + M_G(Y)`.  Taking the
supremum over admissible `ω` gives the claim (`c = ±1`: sum and difference). -/
theorem Submission.lcmp_massOn_le_add_of_eval_eq : ∀ (P k : ℕ) (U G : Set (Euclid P)) (X Y Z : GeometricCurrentOn U k) (c : ℝ), |c| ≤ 1 → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ G → Z ω = X ω + c * Y ω) → Z.massOn G ≤ X.massOn G + Y.massOn G := by
  intro P k U G X Y Z c hc hZ
  -- Step 4: `M_G(Z)` is a supremum, so bound each admissible value `ofReal (Z ω)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- Step 1: `−ω` is admissible (same support, same Euclidean coefficient norm)
  have hneg : -ω ∈ massAdmissibleOn U k G := by
    refine ⟨?_, fun x => ?_⟩
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) =
          -(ω : DifferentialForm (Euclid P) k) := rfl
      rw [hco, tsupport_neg]
      exact hω.1
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
          -((ω : DifferentialForm (Euclid P) k) x) := rfl
      rw [hco, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 2: `ofReal (X ω) ≤ M_G(X)` and, as `Y(−ω) = −Y(ω)`, `ofReal |Y(ω)| ≤ M_G(Y)`
  have hXle : ENNReal.ofReal (X ω) ≤ X.massOn G := X.le_massOn hω
  have hYle : ENNReal.ofReal (Y ω) ≤ Y.massOn G := Y.le_massOn hω
  have hYle' : ENNReal.ofReal (Y (-ω)) ≤ Y.massOn G := Y.le_massOn hneg
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hYle'
  have habs : ENNReal.ofReal |Y ω| ≤ Y.massOn G := by
    rcases abs_cases (Y ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hYle
    · rw [h]; exact hYle'
  -- Step 3: `c Y(ω) ≤ |c| |Y(ω)| ≤ |Y(ω)|`; `ofReal` is monotone and subadditive
  have hcy : c * Y ω ≤ |Y ω| :=
    calc c * Y ω ≤ |c * Y ω| := le_abs_self _
      _ = |c| * |Y ω| := abs_mul _ _
      _ ≤ 1 * |Y ω| := by gcongr
      _ = |Y ω| := one_mul _
  show ENNReal.ofReal (Z ω) ≤ X.massOn G + Y.massOn G
  calc ENNReal.ofReal (Z ω) = ENNReal.ofReal (X ω + c * Y ω) := by rw [hZ ω hω.1]
    _ ≤ ENNReal.ofReal (X ω + |Y ω|) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (X ω) + ENNReal.ofReal |Y ω| := ENNReal.ofReal_add_le
    _ ≤ X.massOn G + Y.massOn G := add_le_add hXle habs
/-- **Restriction of an integer multiplicity representation** (Simon Ch. 6, 3.1).  For
`R = (M, θ, ξ)` with weight `μ_R = θ Hⁿ⌞M`: (a) `μ_R ≪ Hⁿ⌞M`; (b) `ξ` is `μ_R`-a.e. strongly
measurable; (c) for Borel `E` and `R' = (M ∩ E, θ, ξ)`, `μ_{R'} = μ_R⌞E` and
`R'(ω) = ∫_E ⟨ω, ξ⟩ dμ_R` for every `n`-form `ω`. -/
theorem Submission.lcmp_imRep_measure_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), R.measure ≪ μHE[n].restrict R.carrier ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ (E : Set (Euclid P)) (R' : IMRep U n), MeasurableSet E → R'.carrier = R.carrier ∩ E → R'.mult = R.mult → R'.orient = R.orient → R'.measure = R.measure.restrict E ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x in E, R.orient x (ω x) ∂R.measure := by
  intro P n U R
  -- (a) a measure with a density is absolutely continuous; (b) so `ξ` is `μ_R`-measurable
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  refine ⟨hac, R.aestronglyMeasurable_orient.mono_ac hac, ?_⟩
  intro E R' hE hc hm ho
  -- (c), weights: `((Hⁿ⌞M).withDensity θ)⌞E = (Hⁿ⌞(E ∩ M)).withDensity θ = μ_{R'}`
  have hmeasEq : R'.measure = R.measure.restrict E := by
    unfold IMRep.measure
    rw [restrict_withDensity hE, Measure.restrict_restrict hE, hc, hm, inter_comm]
  refine ⟨hmeasEq, fun ω => ?_⟩
  -- (c), actions: `∫ h d(λ.withDensity θ) = ∫ θ h dλ` for the Borel density `θ : ℝᴾ → [0, ∞)`
  have hmult : (fun x => (R'.mult x : ℝ≥0∞)) = fun x => (((R'.mult x : NNReal)) : ℝ≥0∞) := by
    funext x
    simp
  have hmeas : Measurable fun x => ((R'.mult x : ℕ) : NNReal) :=
    (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R'.measurable_mult
  rw [← hmeasEq]
  unfold IMRep.action IMRep.measure
  rw [hmult, integral_withDensity_eq_integral_smul hmeas]
  congr 1
  funext x
  rw [ho, NNReal.smul_def, smul_eq_mul]
  norm_cast
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
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
/-- **Good radius** (Simon 7.2.4, choice of the slicing level; the factor-2 averaging of Ch. 2,
6.7(1)).  If `ρ < ρ'`, `μ(B̄_{ρ'}(y)) < ∞`, `∫ g dL¹ ≤ I` and `p` holds `L¹`-a.e., then some
`t ∈ (ρ, ρ')` has `p t`, `μ(∂B_t(y)) = 0` and `g t ≤ (2 / (ρ' - ρ)) I`: the levels failing `p` and
the (countably many) levels whose sphere charges the finite measure `μ⌞B̄_{ρ'}(y)` are `L¹`-null,
and by Markov's inequality the levels with `g t > (2 / (ρ' - ρ)) I` have `L¹`-measure at most
`(ρ' - ρ) / 2 < L¹((ρ, ρ'))`. -/
theorem Submission.dor_lmb_glc_good_radius : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (ρ ρ' : ℝ) (g : ℝ → ℝ≥0∞) (I : ℝ≥0∞) (p : ℝ → Prop), ρ < ρ' → μ (closedBall y ρ') ≠ ∞ → AEMeasurable g → ∫⁻ t, g t ≤ I → (∀ᵐ t, p t) → ∃ t : ℝ, ρ < t ∧ t < ρ' ∧ p t ∧ μ (sphere y t) = 0 ∧ g t ≤ ENNReal.ofReal (2 / (ρ' - ρ)) * I := by
  intro P μ y ρ ρ' g I p hρ hμ hg hI hp
  have hδ : 0 < ρ' - ρ := sub_pos.mpr hρ
  set c := ENNReal.ofReal (2 / (ρ' - ρ)) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcinv : c⁻¹ = ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rw [hc_def, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  -- `N₁`: the exceptional set of `p` is Lebesgue-null
  have hN₁ : volume {t : ℝ | ¬ p t} = 0 := ae_iff.mp hp
  -- `N₂`: only countably many spheres charge the finite measure `μ⌞B̄_{ρ'}(y)`
  have hfin : IsFiniteMeasure (μ.restrict (closedBall y ρ')) := isFiniteMeasure_restrict.mpr hμ
  have hcount : {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun s => isClosed_sphere.measurableSet)
      (fun s s' hss' => Set.disjoint_left.mpr fun x hx hx' =>
        hss' ((mem_sphere.mp hx).symm.trans (mem_sphere.mp hx')))
  have hN₂ : volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} = 0 :=
    hcount.measure_zero volume
  -- `N₃`: Markov's inequality gives `L¹(N₃) ≤ (ρ' - ρ) / 2`
  have hN₃ : volume {t : ℝ | c * I < g t} ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rcases eq_or_ne I 0 with h0 | h0
    · have hzero : ∫⁻ t, g t = 0 := le_antisymm (hI.trans h0.le) zero_le
      have hae : g =ᵐ[volume] 0 := (lintegral_eq_zero_iff' hg).mp hzero
      have hnull : volume {t : ℝ | c * I < g t} = 0 := by
        refine measure_mono_null (fun t ht => ?_) (ae_iff.mp hae)
        simp only [Set.mem_ofPred_eq, h0, mul_zero] at ht ⊢
        exact ht.ne'
      rw [hnull]
      exact zero_le
    rcases eq_or_ne I ∞ with htop | htop
    · have hempty : {t : ℝ | c * I < g t} = ∅ := by
        ext t
        simp [htop, ENNReal.mul_top hc0]
      rw [hempty, measure_empty]
      exact zero_le
    have hε0 : c * I ≠ 0 := mul_ne_zero hc0 h0
    have hεtop : c * I ≠ ∞ := ENNReal.mul_ne_top hctop htop
    calc volume {t : ℝ | c * I < g t} ≤ volume {t : ℝ | c * I ≤ g t} :=
          measure_mono fun t (ht : c * I < g t) => show c * I ≤ g t from ht.le
      _ ≤ (∫⁻ t, g t) / (c * I) := meas_ge_le_lintegral_div hg hε0 hεtop
      _ ≤ I / (c * I) := ENNReal.div_le_div_right hI _
      _ = c⁻¹ := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_assoc,
          ENNReal.inv_mul_cancel h0 htop, mul_one]
      _ = ENNReal.ofReal ((ρ' - ρ) / 2) := hcinv
  -- covering: if no good `t` existed, then `(ρ, ρ') ⊆ N₁ ∪ N₂ ∪ N₃`
  by_contra hcon
  have hcover : Ioo ρ ρ' ⊆ {t : ℝ | ¬ p t} ∪
      {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪ {t : ℝ | c * I < g t} := by
    intro t ht
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, nonpos_iff_eq_zero]
      at hnot
    obtain ⟨⟨hpt, hνt⟩, hgt⟩ := hnot
    have hμt : μ (sphere y t) = 0 := by
      rwa [Measure.restrict_apply isClosed_sphere.measurableSet, Set.inter_eq_left.mpr
        (sphere_subset_closedBall.trans (closedBall_subset_closedBall ht.2.le))] at hνt
    exact hcon ⟨t, ht.1, ht.2, hpt, hμt, hgt⟩
  have hle : ENNReal.ofReal (ρ' - ρ) ≤ ENNReal.ofReal ((ρ' - ρ) / 2) :=
    calc ENNReal.ofReal (ρ' - ρ) = volume (Ioo ρ ρ') := Real.volume_Ioo.symm
      _ ≤ volume ({t : ℝ | ¬ p t} ∪ {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪
          {t : ℝ | c * I < g t}) := measure_mono hcover
      _ ≤ volume {t : ℝ | ¬ p t} + volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} +
          volume {t : ℝ | c * I < g t} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
        rw [hN₁, hN₂, zero_add, zero_add]
        exact hN₃
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  linarith

/-- **Localization at a point** (Simon Ch. 6, Remark 8.3(1), with the slicing of 4.5(1), (2) and
the averaging of Ch. 2, 6.7(2)).  Given the representation (REP), mass (MR), integer multiplicity
(IMC), slicing (SL) and convergence (TOOLS) facts as hypotheses: if `Tⱼ ∈ 𝒟_{d+1}(U)` are integer
multiplicity with `supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for `W ⊂⊂ U`, `Tⱼ ⇀ T` and `x₀ ∈ U`, then there
are `r > 0` with `B̄_r(x₀) ⊆ U` and a subsequence `j'` such that `Sⱼ := T_{j'}⌞B_r(x₀)` are integer
multiplicity, carried by and vanishing off `B̄_r(x₀)`, with `supⱼ (M(Sⱼ) + M(∂Sⱼ)) < ∞`, and
`Sⱼ ⇀ A`, where `A = T` on forms supported in `B_r(x₀)`.  The radius `r` is a slicing level of
`dist(·, x₀)` where the limit of the weights does not charge `∂B_r(x₀)` and the slice defects
`M(∂(Tⱼ⌞B_r) − (∂Tⱼ)⌞B_r)` have a finite `liminf`; the mass bounds use the sublevel-set integral
formula, vanishing off the compact sphere and the mass triangle inequality. -/
theorem Submission.cbrcs_localize_at_point : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ((∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop)) → ∀ (d P : ℕ) (U : Set (Euclid P)) (Ts : ℕ → GeometricCurrentOn U (d + 1)) (T : GeometricCurrentOn U (d + 1)) (x₀ : Euclid P), IsOpen U → (∀ j, IsIntegerMultiplicity (Ts j)) → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) → WeaklyConvergesOn Ts T → x₀ ∈ U → ∃ (r : ℝ) (Ss : ℕ → GeometricCurrentOn U (d + 1)) (Rs : ℕ → IMRep U (d + 1)) (A : GeometricCurrentOn U (d + 1)), 0 < r ∧ closedBall x₀ r ⊆ U ∧ (∀ j, (Rs j).Represents (Ss j) ∧ (Rs j).carrier ⊆ closedBall x₀ r) ∧ (∀ (j : ℕ) (ω : TestFormOn U (d + 1)), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (d + 1))) (closedBall x₀ r) → Ss j ω = 0) ∧ ⨆ j, ((Ss j).mass + (Ss j).boundary.mass) < ∞ ∧ WeaklyConvergesOn Ss A ∧ ∀ ω : TestFormOn U (d + 1), tsupport (ω : DifferentialForm (Euclid P) (d + 1)) ⊆ ball x₀ r → A ω = T ω := by
  have hVOM := Submission.lcmp_massOn_le_of_vanish_off_compact
  have hTRI := Submission.lcmp_massOn_le_add_of_eval_eq
  have hIR := Submission.lcmp_imRep_measure_restrict
  have hICF := Submission.rsd_imrep_compact_measure_ne_top
  have hIAI := Submission.dor_ims_action_eq_integral
  have hGR := Submission.dor_lmb_glc_good_radius
  have hMSI : (∀ (P k : ℕ) (U s : Set (Euclid P)) (X : GeometricCurrentOn U k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x in s, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → X.mass ≤ μ s) := by
    intro P k U s X μ ξ hbd hrep
    unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
    show ENNReal.ofReal (X ω) ≤ μ s
    rw [hrep ω]
    have hae : ∀ᵐ x ∂(μ.restrict s), ‖ξ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ≤ 1 := by
      filter_upwards [ae_restrict_of_ae hbd] with x hx
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.2 ((hx _).trans (hω x))
    calc ENNReal.ofReal (∫ x in s, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ)
        ≤ ‖∫ x in s, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in s, ‖ξ x ((ω : DifferentialForm (Euclid P) k) x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in s, 1 ∂μ := lintegral_mono_ae hae
      _ = μ s := by rw [setLIntegral_const, one_mul]
  intro hREP hMR hIMC hSL hTOOLS d P U Ts T x₀ hU hIM hbd hconv hx₀
  obtain ⟨_, hIMCb, _, hIMCd⟩ := hIMC
  obtain ⟨hT1, hT2, hMM⟩ := hTOOLS
  -- the slicing function
  set f : Euclid P → ℝ := fun x => dist x x₀ with hf_def
  have hf_cont : Continuous f := continuous_id.dist continuous_const
  have hf_lip : LipschitzWith 1 f := LipschitzWith.dist_left x₀
  -- Step 1: r₀ and G
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hr₀ : 0 < ε / 2 := half_pos hε
  have hcb₀ : closedBall x₀ (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  set r₀ := ε / 2 with hr₀_def
  set G : Set (Euclid P) := ball x₀ r₀ with hG_def
  have hGo : IsOpen G := isOpen_ball
  have hGcc : CompactlyContained G U :=
    ⟨(isCompact_closedBall x₀ r₀).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
     closure_ball_subset_closedBall.trans hcb₀⟩
  have hΛ := hbd G hGo hGcc
  set Λ := ⨆ j, ((Ts j).massOn G + boundaryMassOn (Ts j) G) with hΛ_def
  have hTjG : ∀ j, (Ts j).massOn G ≤ Λ := fun j =>
    le_self_add.trans (le_iSup (fun j => (Ts j).massOn G + boundaryMassOn (Ts j) G) j)
  have hbTjG : ∀ j, (Ts j).boundary.massOn G ≤ Λ := fun j =>
    (le_add_self : (Ts j).boundary.massOn G ≤ (Ts j).massOn G + (Ts j).boundary.massOn G).trans
      (le_iSup (fun j => (Ts j).massOn G + boundaryMassOn (Ts j) G) j)
  -- Step 2: locally finite masses
  have hlocT : ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞ := by
    intro W hW hWU
    have h1 := hconv.massOn_le_liminf W
    have h2 : liminf (fun j => (Ts j).massOn W) atTop ≤
        ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) :=
      (liminf_le_limsup).trans (limsup_le_iSup.trans (iSup_mono fun j => le_self_add))
    exact lt_of_le_of_lt (h1.trans h2) (hbd W hW hWU)
  have hlocbT : ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.boundary.massOn W < ∞ := by
    intro W hW hWU
    have h1 := (hconv.boundary).massOn_le_liminf W
    have h2 : liminf (fun j => (Ts j).boundary.massOn W) atTop ≤
        ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) :=
      (liminf_le_limsup).trans (limsup_le_iSup.trans (iSup_mono fun j =>
        (le_add_self : (Ts j).boundary.massOn W ≤ (Ts j).massOn W + (Ts j).boundary.massOn W)))
    exact lt_of_le_of_lt (h1.trans h2) (hbd W hW hWU)
  have hlocbTj : ∀ j, ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U →
      (Ts j).boundary.massOn W < ∞ := by
    intro j W hW hWU
    exact lt_of_le_of_lt ((le_add_self : (Ts j).boundary.massOn W ≤ (Ts j).massOn W + (Ts j).boundary.massOn W).trans
      (le_iSup (fun j => (Ts j).massOn W + boundaryMassOn (Ts j) W) j)) (hbd W hW hWU)
  -- Step 3: representations
  choose μ' ξ' _ hμ'K hμ'W hξ'meas hξ'bd hξ'rep _ using
    fun j => hREP P d U (Ts j).boundary hU (hlocbTj j)
  obtain ⟨μT, ξT, -, hμTK, -, hξTmeas, hξTbd, hξTrep, -⟩ := hREP P (d + 1) U T hU hlocT
  obtain ⟨μbT, ξbT, -, hμbTK, -, hξbTmeas, hξbTbd, hξbTrep, -⟩ := hREP P d U T.boundary hU hlocbT
  choose R hR using hIM
  have hRK : ∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → (R j).measure K < ∞ :=
    fun j K hK hKU => lt_top_iff_ne_top.2 (hICF P (d + 1) U (R j) K hK hKU).2
  have hRmeas : ∀ j, AEStronglyMeasurable (R j).orient (R j).measure :=
    fun j => (hIR P (d + 1) U (R j)).2.1
  have hRbd : ∀ j, ∀ᵐ x ∂(R j).measure, ∀ α : Covector (Euclid P) (d + 1),
      |(R j).orient x α| ≤ covectorEuclideanNorm α :=
    fun j => (hIR P (d + 1) U (R j)).1.ae_le (hIMCd P (d + 1) U (R j))
  have hRrep : ∀ j, ∀ ω : TestFormOn U (d + 1), Ts j ω =
      ∫ x, (R j).orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(R j).measure :=
    fun j ω => (hR j ω).trans (hIAI P (d + 1) U (R j) ω).2
  have hRW : ∀ j, ∀ W : Set (Euclid P), IsOpen W → (Ts j).massOn W = (R j).measure W :=
    fun j W hW => hMR P (d + 1) U (Ts j) (R j) hU (hR j) W hW
  -- Step 4: uniform bounds on compact sets
  have hsupK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, (R j).measure K < ∞ := by
    intro K hK hKU
    obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    refine lt_of_le_of_lt ?_ (hbd W hWo ⟨hWc, hWU⟩)
    refine iSup_mono fun j => ?_
    calc (R j).measure K ≤ (R j).measure W := measure_mono hKW
      _ = (Ts j).massOn W := (hRW j W hWo).symm
      _ ≤ _ := le_self_add
  -- Step 5: measure compactness
  obtain ⟨φ, μ, hφ, -, hμK, -, hμlimsup, -⟩ := hT1 P U (fun j => (R j).measure) hU hsupK
  -- Step 6: slicing
  choose A B hA hB hAB hZ _ using fun j =>
    hSL P d U (Ts (φ j)) (R (φ j)).measure (μ' (φ j)) (R (φ j)).orient (ξ' (φ j)) f 1 hU
      (hRK (φ j)) (hμ'K (φ j)) (hRmeas (φ j)) (hξ'meas (φ j)) (hRbd (φ j))
      (Filter.Eventually.of_forall (hξ'bd (φ j))) (hRrep (φ j)) (hξ'rep (φ j)) hf_lip
  obtain ⟨AT, BT, hAT, -, -, -, -⟩ := hSL P d U T μT μbT ξT ξbT f 1 hU hμTK hμbTK hξTmeas hξbTmeas
    (Filter.Eventually.of_forall hξTbd) (Filter.Eventually.of_forall hξbTbd) hξTrep hξbTrep hf_lip
  -- Step 7: measurable majorant
  set z : ℕ → ℝ → ℝ≥0∞ := fun j t => ((A j t).boundary - B j t).massOn G with hz_def
  have hfinG : ∀ j, (R (φ j)).measure (G ∩ {x | 0 < f x ∧ f x < r₀}) < ∞ := by
    intro j
    refine lt_of_le_of_lt (measure_mono inter_subset_left) ?_
    rw [← hRW (φ j) G hGo]
    exact lt_of_le_of_lt (hTjG (φ j)) hΛ
  obtain ⟨g, hgm, hgae, hgint⟩ := hMM P (fun j => (R (φ j)).measure) f G 0 r₀ 1 z hf_cont hfinG
    (fun j t _ => hZ j G t hGo)
  have hgint' : ∫⁻ t in Ioo 0 r₀, g t ≤ Λ := by
    refine hgint.trans ?_
    rw [ENNReal.coe_one, one_mul]
    refine (liminf_le_limsup).trans (limsup_le_iSup.trans (iSup_le fun j => ?_))
    calc (R (φ j)).measure (G ∩ {x | 0 < f x ∧ f x < r₀}) ≤ (R (φ j)).measure G :=
          measure_mono inter_subset_left
      _ = (Ts (φ j)).massOn G := (hRW (φ j) G hGo).symm
      _ ≤ Λ := hTjG (φ j)
  -- Step 8: good radius
  have hμcb : μ (closedBall x₀ r₀) ≠ ∞ := (hμK _ (isCompact_closedBall x₀ r₀) hcb₀).ne
  obtain ⟨r, hr0, hrr₀, hpr, hsph, hgr⟩ := hGR P μ x₀ 0 r₀ ((Ioo 0 r₀).indicator g) Λ
    (fun t => t ∈ Ioo 0 r₀ → liminf (fun j => z j t) atTop ≤ g t) hr₀ hμcb
    ((hgm.indicator measurableSet_Ioo).aemeasurable)
    (by rw [lintegral_indicator measurableSet_Ioo]; exact hgint') hgae
  have hrI : r ∈ Ioo 0 r₀ := ⟨hr0, hrr₀⟩
  have hgr' : g r < ∞ := by
    rw [indicator_of_mem hrI] at hgr
    exact lt_of_le_of_lt hgr (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΛ)
  set C : NNReal := (g r).toNNReal + 1 with hC_def
  have hlim : liminf (fun j => z j r) atTop < (C : ℝ≥0∞) := by
    calc liminf (fun j => z j r) atTop ≤ g r := hpr hrI
      _ < g r + 1 := ENNReal.lt_add_right hgr'.ne one_ne_zero
      _ = (C : ℝ≥0∞) := by rw [hC_def, ENNReal.coe_add, ENNReal.coe_toNNReal hgr'.ne, ENNReal.coe_one]
  obtain ⟨ψ, hψ, hψC⟩ := extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hlim)
  -- Step 9: the localized currents
  have hball_meas : MeasurableSet (ball x₀ r) := measurableSet_ball
  choose S R' hR'rep hR'car hR'mult hR'or using
    fun j => hIMCb P (d + 1) U (R (φ (ψ j))) (ball x₀ r) hU hball_meas
  have hSval : ∀ j, ∀ ω : TestFormOn U (d + 1), S j ω = ∫ x in ball x₀ r,
      (R (φ (ψ j))).orient x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂(R (φ (ψ j))).measure := by
    intro j ω
    rw [hR'rep j ω]
    exact ((hIR P (d + 1) U (R (φ (ψ j)))).2.2 (ball x₀ r) (R' j) hball_meas (hR'car j) (hR'mult j)
      (hR'or j)).2 _
  have hSA : ∀ j, S j = A (ψ j) r := by
    intro j
    ext ω
    rw [hSval j ω, hA (ψ j) r ω]
    rfl
  have hcarr : ∀ j, (R' j).carrier ⊆ closedBall x₀ r := by
    intro j
    rw [hR'car j]
    exact inter_subset_right.trans ball_subset_closedBall
  have hvan : ∀ (j : ℕ) (ω : TestFormOn U (d + 1)),
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) (d + 1))) (closedBall x₀ r) → S j ω = 0 := by
    intro j ω hdisj
    rw [hSval j ω]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport (ω : DifferentialForm (Euclid P) (d + 1)) :=
      fun h => hdisj.ne_of_mem h (ball_subset_closedBall hx) rfl
    rw [image_eq_zero_of_notMem_tsupport hx', map_zero]
  have hSmass : ∀ j, (S j).mass ≤ Λ := by
    intro j
    calc (S j).mass ≤ (R (φ (ψ j))).measure (ball x₀ r) :=
          hMSI P (d + 1) U (ball x₀ r) (S j) (R (φ (ψ j))).measure (R (φ (ψ j))).orient
            (hRbd _) (hSval j)
      _ ≤ (R (φ (ψ j))).measure G := measure_mono (ball_subset_ball hrr₀.le)
      _ = (Ts (φ (ψ j))).massOn G := (hRW _ G hGo).symm
      _ ≤ Λ := hTjG _
  have hsphG : sphere x₀ r ⊆ G := sphere_subset_ball hrr₀
  have hbmass : ∀ j, (S j).boundary.mass ≤ (C : ℝ≥0∞) + Λ := by
    intro j
    set Zd := (A (ψ j) r).boundary - B (ψ j) r with hZd_def
    have hZdvan : ∀ η : TestFormOn U d,
        Disjoint (tsupport (η : DifferentialForm (Euclid P) d)) (sphere x₀ r) → Zd η = 0 := by
      intro η hη
      change (A (ψ j) r).boundary η - B (ψ j) r η = 0
      rw [hAB (ψ j) r η hη, sub_self]
    have hZd : Zd.mass ≤ (C : ℝ≥0∞) :=
      calc Zd.mass = Zd.massOn U := rfl
        _ ≤ Zd.massOn G := hVOM P d U G (sphere x₀ r) Zd (isCompact_sphere x₀ r) hGo hsphG hZdvan U
        _ = z (ψ j) r := rfl
        _ ≤ (C : ℝ≥0∞) := (hψC j).le
    have hBm : (B (ψ j) r).mass ≤ Λ :=
      calc (B (ψ j) r).mass ≤ μ' (φ (ψ j)) (ball x₀ r) :=
            hMSI P d U (ball x₀ r) (B (ψ j) r) (μ' (φ (ψ j))) (ξ' (φ (ψ j)))
              (Filter.Eventually.of_forall (hξ'bd _)) (hB (ψ j) r)
        _ ≤ μ' (φ (ψ j)) G := measure_mono (ball_subset_ball hrr₀.le)
        _ = (Ts (φ (ψ j))).boundary.massOn G := (hμ'W _ G hGo).symm
        _ ≤ Λ := hbTjG _
    have htri : (S j).boundary.massOn U ≤ Zd.massOn U + (B (ψ j) r).massOn U := by
      refine hTRI P d U U Zd (B (ψ j) r) (S j).boundary 1 (by simp) fun η _ => ?_
      rw [hSA j]
      change (A (ψ j) r).boundary η = ((A (ψ j) r).boundary η - B (ψ j) r η) + 1 * B (ψ j) r η
      ring
    calc (S j).boundary.mass = (S j).boundary.massOn U := rfl
      _ ≤ Zd.massOn U + (B (ψ j) r).massOn U := htri
      _ = Zd.mass + (B (ψ j) r).mass := rfl
      _ ≤ (C : ℝ≥0∞) + Λ := add_le_add hZd hBm
  have hsup : ⨆ j, ((S j).mass + (S j).boundary.mass) < ∞ := by
    refine lt_of_le_of_lt (iSup_le fun j => add_le_add (hSmass j) (hbmass j)) ?_
    exact ENNReal.add_lt_top.2 ⟨hΛ, ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, hΛ⟩⟩
  -- Step 10: convergence
  have hconv' : WeaklyConvergesOn (fun j => Ts (φ (ψ j))) T :=
    fun ω => (hconv ω).comp ((hφ.comp hψ).tendsto_atTop)
  have hlimsup' : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      limsup (fun j => (R (φ (ψ j))).measure K) atTop ≤ μ K := by
    intro K hK hKU
    refine le_trans ?_ (hμlimsup K hK hKU)
    have h1 : limsup (fun j => (R (φ (ψ j))).measure K) atTop =
        limsup (fun j => (R (φ j)).measure K) (map ψ atTop) :=
      limsup_comp (fun j => (R (φ j)).measure K) ψ atTop
    rw [h1]
    exact limsup_le_limsup_of_le hψ.tendsto_atTop (by isBoundedDefault) (by isBoundedDefault)
  have hSconv : WeaklyConvergesOn S (AT r) := by
    intro ω
    have h := hT2 P (d + 1) U (fun j => Ts (φ (ψ j))) T (fun j => (R (φ (ψ j))).measure)
      (fun j => (R (φ (ψ j))).orient) μT μ ξT f r hU hf_cont hconv' (fun j => hRK _)
      (fun j => hRmeas _) (fun j => hRbd _) (fun j => hRrep _) hμTK hξTmeas
      (Filter.Eventually.of_forall hξTbd) hξTrep hμK hlimsup' hsph ω
    rw [hAT r ω]
    convert h using 2 with j
    exact hSval j ω
  -- Step 11: agreement
  have hagree : ∀ ω : TestFormOn U (d + 1),
      tsupport (ω : DifferentialForm (Euclid P) (d + 1)) ⊆ ball x₀ r → AT r ω = T ω := by
    intro ω hω
    rw [hAT r ω, hξTrep ω]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hx' : x ∉ tsupport (ω : DifferentialForm (Euclid P) (d + 1)) := fun h => hx (hω h)
    rw [image_eq_zero_of_notMem_tsupport hx', map_zero]
  exact ⟨r, S, R', AT r, hr0, (closedBall_subset_closedBall hrr₀.le).trans hcb₀,
    fun j => ⟨hR'rep j, hcarr j⟩, hvan, hsup, hSconv, hagree⟩
/-- An open `U ⊆ ℝᴾ` is exhausted by the compact sets `Kᵢ = B̄(0, i) \ thickening((i + 1)⁻¹, Uᶜ)`
(the exhaustion in the proof of Simon 1.4.16): `Kᵢ ⊆ U`, since a point of `Uᶜ` lies in every
positive thickening of `Uᶜ`; a compact `C ⊆ U` has a margin `δ > 0` with `thickening δ C ⊆ U` and
a radius `R` with `C ⊆ B̄(0, R)`, so `C ⊆ Kₘ` once `R ≤ m` and `(m + 1)⁻¹ < δ`. -/
theorem Submission.cbr_ct_vs_compact_exhaustion : ∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i := by
  intro P U hU
  refine ⟨fun i => closedBall (0 : Euclid P) i \ thickening ((i : ℝ) + 1)⁻¹ Uᶜ,
    fun i => (isCompact_closedBall _ _).diff isOpen_thickening, fun i x hx => ?_,
    fun C hC hCU => ?_⟩
  · by_contra hxU
    exact hx.2 (self_subset_thickening (by positivity) _ hxU)
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Euclid P)
    obtain ⟨m, hm⟩ := exists_nat_ge (max R δ⁻¹)
    have hmδ : ((m : ℝ) + 1)⁻¹ < δ := inv_lt_of_inv_lt₀ hδ (by linarith [le_max_right R δ⁻¹])
    refine ⟨m, fun x hx => ⟨closedBall_subset_closedBall ((le_max_left R δ⁻¹).trans hm) (hR hx),
      fun hxt => ?_⟩⟩
    -- a point `y ∉ U` within `(m + 1)⁻¹ < δ` of `x ∈ C` would lie in `thickening δ C ⊆ U`
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hxt
    exact hy (hδU (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
/-- **Simon 1.4.16, one compact piece** (the Alaoglu step of the proof, corrected to a genuine
subsequence).  If `K ⊆ ℝᴾ` is compact and `supⱼ μⱼ(K) < ∞`, there is a strictly increasing `θ`
such that `∫ f dμ_{θ(j)}` converges for every continuous `f` with `tsupport f ⊆ K`.  As `f`
vanishes off `K`, `∫ f dμⱼ = ∫_K f dμⱼ`.  The step functions `g (n, L) x = L[m]` (`m` the first
index with `|x - dₘ| < 1/(n+1)`, `(dₘ)` dense in `ℝᴾ`, `L` a list of rationals) form a countable
family that is uniformly dense on `K` for such `f`.  Sequential compactness of a countable product
of compact intervals gives one subsequence along which every `∫_K g dμⱼ` converges, and a `3ε`
argument makes `∫_K f dμ_{θ(j)}` Cauchy. -/
theorem Submission.cbr_ct_vs_compact_piece_subseq : ∀ (P : ℕ) (K : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsCompact K → ⨆ j, μs j K < ∞ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (θ j))) atTop (𝓝 c) := by
  classical
  intro P K μs hK hM
  -- `M = supⱼ μⱼ(K)` as a real number
  set M : ℝ := (⨆ j, μs j K).toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hμK : ∀ j, μs j K ≤ ⨆ j, μs j K := fun j => le_iSup (fun j => μs j K) j
  have hμKfin : ∀ j, μs j K < ∞ := fun j => lt_of_le_of_lt (hμK j) hM
  have hμKM : ∀ j, (μs j).real K ≤ M := fun j => ENNReal.toReal_mono hM.ne (hμK j)
  -- a dense sequence `d` in `ℝᴾ`: every `x` is within `1/(n+1)` of some `d m`
  set d : ℕ → Euclid P := TopologicalSpace.denseSeq (Euclid P)
  have hr : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  have hcov : ∀ (n : ℕ) (x : Euclid P), ∃ m, dist x (d m) < 1 / ((n : ℝ) + 1) :=
    fun n x => (TopologicalSpace.denseRange_denseSeq (Euclid P)).exists_dist_lt x (hr n)
  -- the countable test family `g (n, L) x = L[m]`, `m` the first index with
  -- `dist x (d m) < 1/(n+1)`; it is measurable and bounded by `B (n, L) = ∑ |L[i]|`
  let g : ℕ × List ℚ → Euclid P → ℝ := fun k x =>
    ((k.2.getD (Nat.find (hcov k.1 x)) 0 : ℚ) : ℝ)
  have hgm : ∀ k, Measurable (g k) := fun k =>
    Measurable.find (f := fun m _ => ((k.2.getD m 0 : ℚ) : ℝ)) (fun _ => measurable_const)
      (fun _ => measurableSet_ball) (hcov k.1)
  let B : ℕ × List ℚ → ℝ := fun k => (k.2.map (fun q : ℚ => |(q : ℝ)|)).sum
  have hgB : ∀ k x, |g k x| ≤ B k := by
    have key : ∀ (L : List ℚ) (m : ℕ),
        |((L.getD m 0 : ℚ) : ℝ)| ≤ (L.map (fun q : ℚ => |(q : ℝ)|)).sum := by
      intro L
      induction L with
      | nil => intro m; simp
      | cons a L ih =>
        intro m
        have hs : 0 ≤ (L.map (fun q : ℚ => |(q : ℝ)|)).sum := List.sum_nonneg (by simp)
        cases m with
        | zero =>
          simp only [List.getD_cons_zero, List.map_cons, List.sum_cons]
          linarith
        | succ m =>
          simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
          linarith [ih m, abs_nonneg (a : ℝ)]
    exact fun k x => key k.2 _
  -- every admissible `f` is uniformly approximated on `K` by the test family
  have happrox : ∀ f : Euclid P → ℝ, Continuous f → tsupport f ⊆ K →
      ∀ ε > 0, ∃ k, ∀ x ∈ K, |f x - g k x| ≤ ε := by
    intro f hf hfK ε hε
    have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
      (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun m => ball (d m) (1 / ((n : ℝ) + 1)))
      (fun _ => isOpen_ball) (fun x _ => mem_iUnion.mpr (hcov n x))
    choose q hq using fun m => Rat.denseRange_cast.exists_dist_lt (f (d m)) (half_pos hε)
    refine ⟨(n, (List.range (t.sup id + 1)).map q), fun x hx => ?_⟩
    obtain ⟨m, hmt, hxm⟩ := mem_iUnion₂.mp (ht hx)
    have hlt : Nat.find (hcov n x) < t.sup id + 1 :=
      Nat.lt_succ_of_le ((Nat.find_min' (hcov n x) hxm).trans (Finset.le_sup (f := id) hmt))
    have h1 := hfδ ((Nat.find_spec (hcov n x)).trans hn)
    have h2 := hq (Nat.find (hcov n x))
    rw [Real.dist_eq] at h1 h2
    have hg : g (n, (List.range (t.sup id + 1)).map q) x = q (Nat.find (hcov n x)) := by
      simp only [g, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
        Option.map_some, Option.getD_some]
    rw [hg]
    linarith [abs_sub_le (f x) (f (d (Nat.find (hcov n x)))) (q (Nat.find (hcov n x)) : ℝ)]
  -- the test integrals `v j k = ∫_K g k dμⱼ` satisfy `|v j k| ≤ B k * M`
  have hgi : ∀ j k, IntegrableOn (g k) K (μs j) := fun j k =>
    Measure.integrableOn_of_bounded (hμKfin j).ne (hgm k).aestronglyMeasurable
      (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hgB k x))
  let v : ℕ → ℕ × List ℚ → ℝ := fun j k => ∫ x in K, g k x ∂(μs j)
  have hvB : ∀ j k, |v j k| ≤ B k * M := by
    intro j k
    rw [← Real.norm_eq_abs]
    calc ‖∫ x in K, g k x ∂(μs j)‖ ≤ B k * (μs j).real K :=
          norm_setIntegral_le_of_norm_le_const (hμKfin j)
            (fun x _ => (Real.norm_eq_abs _).trans_le (hgB k x))
      _ ≤ B k * M := mul_le_mul_of_nonneg_left (hμKM j) ((abs_nonneg _).trans (hgB k 0))
  -- diagonal selection: `(v j)ⱼ` lies in the compact `∏ₖ [-B k M, B k M]`, which is
  -- first countable since `ℕ × List ℚ` is countable
  obtain ⟨a, -, θ, hθ, hlim⟩ :=
    (isCompact_univ_pi fun k : ℕ × List ℚ =>
      isCompact_Icc (a := -(B k * M)) (b := B k * M)).tendsto_subseq
      (x := v) fun j => Set.mem_univ_pi.mpr fun k => abs_le.mp (hvB j k)
  have hconv : ∀ k, Tendsto (fun j => v (θ j) k) atTop (𝓝 (a k)) := tendsto_pi_nhds.mp hlim
  refine ⟨θ, hθ, fun f hf hfK => ?_⟩
  -- `f` vanishes off `K`, so `∫ f dμⱼ = ∫_K f dμⱼ`; and `f` is bounded
  have hf0 : ∀ x ∉ K, f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfK h)
  have hfK' : ∀ j, ∫ x, f x ∂(μs j) = ∫ x in K, f x ∂(μs j) := fun j =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero hf0).symm
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support
    (hK.of_isClosed_subset (isClosed_tsupport f) hfK)
  have hfi : ∀ j, IntegrableOn f K (μs j) := fun j =>
    Measure.integrableOn_of_bounded (hμKfin j).ne hf.aestronglyMeasurable (ae_of_all _ hC)
  -- `∫ f dμⱼ` is `η M`-close to a test integral, uniformly in `j`
  have hclose : ∀ η > 0, ∃ k, ∀ j, dist (∫ x, f x ∂(μs j)) (v j k) ≤ η * M := by
    intro η hη
    obtain ⟨k, hk⟩ := happrox f hf hfK η hη
    refine ⟨k, fun j => ?_⟩
    rw [hfK' j, dist_eq_norm, ← integral_sub (hfi j) (hgi j k)]
    calc ‖∫ x in K, (f x - g k x) ∂(μs j)‖ ≤ η * (μs j).real K :=
          norm_setIntegral_le_of_norm_le_const (hμKfin j)
            (fun x hx => (Real.norm_eq_abs _).trans_le (hk x hx))
      _ ≤ η * M := mul_le_mul_of_nonneg_left (hμKM j) hη.le
  -- hence `(∫ f dμ_{θ j})ⱼ` is Cauchy, so it converges
  have hcauchy : CauchySeq (fun j => ∫ x, f x ∂(μs (θ j))) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := hclose (ε / (3 * (M + 1))) (by positivity)
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hconv k).cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hk (θ m)
    have h2 := hk (θ n)
    have h3 := hN m hm n hn
    have hη : ε / (3 * (M + 1)) * M ≤ ε / 3 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc dist (∫ x, f x ∂(μs (θ m))) (∫ x, f x ∂(μs (θ n)))
        ≤ dist (∫ x, f x ∂(μs (θ m))) (v (θ m) k) + dist (v (θ m) k) (v (θ n) k) +
            dist (v (θ n) k) (∫ x, f x ∂(μs (θ n))) := dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm (v (θ n) k)]; linarith
  exact cauchySeq_tendsto_of_complete hcauchy
/-- **Diagonal subsequence** (Simon Ch. 1, proof of 4.16, chapter-01.txt lines 1767–1768: "By
choosing the subsequences successively and taking a diagonal sequence, we then get a subsequence
`μ_{k'}` …").  If every strictly increasing `ψ` has a strictly increasing refinement `ψ ∘ θ` along
which `s i` converges for all `i ∈ F m`, then one strictly increasing `φ` makes `s i ∘ φ` converge
for every `m` and every `i ∈ F m`.  Successive refinements `ψ₀ = Θ 0 id`,
`ψ_{m+1} = ψ_m ∘ Θ (m + 1) ψ_m` give the diagonal `φ j = ψ_j j`, whose tail
`φ (m + k) = ψ_m (τ_k (m + k))` is a subsequence of `ψ_m`. -/
theorem Submission.cbr_ct_vs_diagonal_subseq : ∀ (ι : Type) (F : ℕ → Set ι) (s : ι → ℕ → ℝ), (∀ (m : ℕ) (ψ : ℕ → ℕ), StrictMono ψ → ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (ψ (θ j))) atTop (𝓝 c)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℕ, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i (φ j)) atTop (𝓝 c) := by
  intro ι F s h
  -- Step 2: choice `Θ m ψ` of a strictly increasing refinement of `ψ` convergent on `F m`
  choose Θ hΘ hΘconv using h
  -- Step 3: `ψ₀ = Θ 0 id`, `ψ_{m+1} = ψ_m ∘ Θ (m + 1) ψ_m`, carried with `StrictMono`
  let ψ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun m =>
    Nat.rec ⟨Θ 0 id strictMono_id, hΘ 0 id strictMono_id⟩
      (fun m p => ⟨p.1 ∘ Θ (m + 1) p.1 p.2, p.2.comp (hΘ (m + 1) p.1 p.2)⟩) m
  have hgood : ∀ m, ∀ i ∈ F m, ∃ c : ℝ, Tendsto (fun j => s i ((ψ m).1 j)) atTop (𝓝 c) := by
    intro m
    cases m with
    | zero => exact hΘconv 0 id strictMono_id
    | succ m => exact hΘconv (m + 1) (ψ m).1 (ψ m).2
  -- Step 4: `ψ_{m+k} = ψ_m ∘ τ` with `τ` strictly increasing
  have hfac : ∀ m k, ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ n, (ψ (m + k)).1 n = (ψ m).1 (τ n) := by
    intro m k
    induction k with
    | zero => exact ⟨id, strictMono_id, fun n => rfl⟩
    | succ k ih =>
      obtain ⟨τ, hτ, hτeq⟩ := ih
      exact ⟨τ ∘ Θ (m + k + 1) (ψ (m + k)).1 (ψ (m + k)).2, hτ.comp (hΘ _ _ _),
        fun n => hτeq (Θ (m + k + 1) (ψ (m + k)).1 (ψ (m + k)).2 n)⟩
  -- Step 5: the diagonal `φ j = ψ_j j`; `ψ_{j+1} (j + 1) = ψ_j (Θ _ _ _ (j + 1)) ≥ ψ_j (j + 1)`
  let φ : ℕ → ℕ := fun j => (ψ j).1 j
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun j =>
    ((ψ j).2 (Nat.lt_add_one j)).trans_le
      ((ψ j).2.monotone (hΘ (j + 1) (ψ j).1 (ψ j).2).le_apply)
  refine ⟨φ, hφ, fun m i hi => ?_⟩
  -- Step 6: `φ (m + k) = ψ_m (σ k)` with `σ k = τ_k (m + k)` strictly increasing
  choose τ hτ hτeq using hfac m
  have hφτ : ∀ k, φ (m + k) = (ψ m).1 (τ k (m + k)) := fun k => hτeq k (m + k)
  have hσ : StrictMono fun k => τ k (m + k) := strictMono_nat_of_lt_succ fun k => by
    have h1 : φ (m + k) < φ (m + (k + 1)) := hφ (Nat.lt_add_one (m + k))
    rw [hφτ, hφτ] at h1
    exact (ψ m).2.lt_iff_lt.mp h1
  -- Step 7: compose with `σ → ∞` and undo the index shift by `m`
  obtain ⟨c, hc⟩ := hgood m i hi
  refine ⟨c, (tendsto_add_atTop_iff_nat m).mp ((hc.comp hσ.tendsto_atTop).congr fun k => ?_)⟩
  show s i ((ψ m).1 (τ k (m + k))) = s i (φ (k + m))
  rw [add_comm k m, hφτ]

/-- **Vague selection on an open set** (Simon Ch. 1, Theorem 4.16 and its proof, chapter-01.txt
lines 1750–1778, for `X = U` open in `ℝᴾ`).  If `supⱼ μⱼ(K) < ∞` for every compact `K ⊆ U`, one
strictly increasing `φ` makes `∫ f dμ_{φ(j)}` converge for every continuous `f` with compact
support in `U`.  Exhaust `U` by compact `Kₘ ⊆ U`; the one-piece selection (the Alaoglu step,
corrected to a genuine subsequence) refines any strictly increasing `ψ` on `Kₘ`, because
`supⱼ μ_{ψ(j)}(Kₘ) ≤ supⱼ μⱼ(Kₘ) < ∞`, and the diagonal argument yields `φ`.  The compact
`tsupport f ⊆ U` lies in some `Kₘ`. -/
theorem Submission.cbr_vague_convergent_subseq : ∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 c) := by
  intro P U μs hU hμ
  -- Step 1: compact `Kₘ ⊆ U` such that every compact subset of `U` lies in some `Kₘ`
  obtain ⟨K, hK, hKU, hKC⟩ := Submission.cbr_ct_vs_compact_exhaustion P U hU
  -- Steps 2–6: diagonal subsequence for `F m = {f | f continuous, tsupport f ⊆ Kₘ}` and
  -- `s f j = ∫ f dμⱼ`; Claim A refines `ψ` on `Kₘ`, as `supⱼ μ_{ψ(j)}(Kₘ) ≤ supⱼ μⱼ(Kₘ) < ∞`
  obtain ⟨φ, hφ, hconv⟩ := Submission.cbr_ct_vs_diagonal_subseq (Euclid P → ℝ)
    (fun m => {f | Continuous f ∧ tsupport f ⊆ K m}) (fun f j => ∫ x, f x ∂(μs j))
    fun m ψ _ => by
      obtain ⟨θ, hθ, hθc⟩ := Submission.cbr_ct_vs_compact_piece_subseq P (K m)
        (fun j => μs (ψ j)) (hK m)
        ((iSup_comp_le (fun j => μs j (K m)) ψ).trans_lt (hμ (K m) (hK m) (hKU m)))
      exact ⟨θ, hθ, fun f hf => hθc f hf.1 hf.2⟩
  -- Step 7: the compact `tsupport f ⊆ U` lies in some `Kₘ`
  refine ⟨φ, hφ, fun f hf hfc hfU => ?_⟩
  obtain ⟨m, hm⟩ := hKC (tsupport f) hfc.isCompact hfU
  exact hconv m f ⟨hf, hm⟩
/-- A continuous function `f` with compact support in `U` is `ν`-integrable for every measure `ν`
finite on compact subsets of `U` (Simon Ch. 1, 4.16: `∫ f dμ` is finite for `f ∈ K(X)`).
`S = spt f` is a compact subset of `U`, so `ν(S) < ∞` and `ν⌞S` is a finite measure; `f` is
`ν⌞S`-integrable, and since `f` vanishes off `S` it is `ν`-integrable. -/
theorem Submission.cbr_vl_integrable_of_tsupport_subset : ∀ (P : ℕ) (U : Set (Euclid P)) (ν : Measure (Euclid P)) (f : Euclid P → ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K < ∞) → Continuous f → HasCompactSupport f → tsupport f ⊆ U → Integrable f ν := by
  intro P U ν f hν hf hcf hU
  -- Step 1: `S = tsupport f` is a compact subset of `U`, so `ν(S) < ∞`.
  have hS : ν (tsupport f) < ∞ := hν _ hcf hU
  -- Step 2: `ν⌞S` has total mass `ν(S) < ∞`.
  have : IsFiniteMeasure (ν.restrict (tsupport f)) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  -- Steps 3–4: `f` is `ν⌞S`-integrable and vanishes off `S`, hence is `ν`-integrable.
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    (hf.integrable_of_hasCompactSupport hcf)
/-- **Simon 1.4.12 on `U`** (Riesz representation, as invoked in the proof of 1.4.16): a positive
linear functional `Λ` on the continuous functions with compact support in the open set `U ⊆ ℝᴾ`
is `f ↦ ∫ f dμ` for a measure `μ` on `ℝᴾ` with `μ(ℝᴾ \ U) = 0` that is finite on compact subsets
of `U`.  Mathlib's `RealRMK.rieszMeasure` on the locally compact subtype `U`, applied to
`g ↦ Λ(ĝ)` (`ĝ` the extension of `g` by zero), is pushed forward to `ℝᴾ`. -/
theorem Submission.cbr_vl_riesz_measure_on_open : ∀ (P : ℕ) (U : Set (Euclid P)) (Λ : (Euclid P → ℝ) → ℝ), IsOpen U → (∀ f g : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Continuous g → HasCompactSupport g → tsupport g ⊆ U → Λ (f + g) = Λ f + Λ g) → (∀ (c : ℝ) (f : Euclid P → ℝ), Continuous f → HasCompactSupport f → tsupport f ⊆ U → Λ (c • f) = c * Λ f) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → (∀ x, 0 ≤ f x) → 0 ≤ Λ f) → ∃ μ : Measure (Euclid P), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∫ x, f x ∂μ = Λ f := by
  intro P U Λ hU hadd hsmul hpos
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  -- the extension `ĝ = Subtype.val.extend g 0` of `g : U → ℝ` by zero
  have hext_val : ∀ (g : U → ℝ) (y : U), Subtype.val.extend g (0 : Euclid P → ℝ) y = g y :=
    fun g y => Subtype.val_injective.extend_apply g 0 y
  have hext_out : ∀ (g : U → ℝ) (x : Euclid P), x ∉ U →
      Subtype.val.extend g (0 : Euclid P → ℝ) x = 0 := by
    intro g x hx
    have hx' : ¬∃ y : U, (y : Euclid P) = x := by
      rintro ⟨y, rfl⟩
      exact hx y.2
    rw [extend_apply' g (0 : Euclid P → ℝ) x hx']
    rfl
  -- `ĝ` is continuous with compact support in `U` for `g ∈ C_c(U, ℝ)`
  have hext : ∀ g : CompactlySupportedContinuousMap U ℝ,
      Continuous (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ)) ∧
        HasCompactSupport (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ)) ∧
        tsupport (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ)) ⊆ U := fun g =>
    ⟨HasCompactSupport.continuous_extend_zero hU g.continuous g.hasCompactSupport,
      g.hasCompactSupport.extend_zero continuous_subtype_val,
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)⟩
  -- `Λ_U(g) = Λ(ĝ)` is a positive linear functional on `C_c(U, ℝ)`
  let L : CompactlySupportedContinuousMap U ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun g => Λ (Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ))
      map_add' := fun g₁ g₂ => by
        have h := extend_add (Subtype.val : U → Euclid P) (g₁ : U → ℝ) g₂ (0 : Euclid P → ℝ) 0
        rw [add_zero] at h
        simp only [CompactlySupportedContinuousMap.coe_add]
        rw [h]
        exact hadd _ _ (hext g₁).1 (hext g₁).2.1 (hext g₁).2.2 (hext g₂).1 (hext g₂).2.1
          (hext g₂).2.2
      map_smul' := fun c g => by
        have h := extend_smul c (Subtype.val : U → Euclid P) (g : U → ℝ) (0 : Euclid P → ℝ)
        rw [smul_zero] at h
        simp only [CompactlySupportedContinuousMap.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [h]
        exact hsmul c _ (hext g).1 (hext g).2.1 (hext g).2.2 }
  let ΛU := PositiveLinearMap.mk₀ L fun g hg => by
    refine hpos _ (hext g).1 (hext g).2.1 (hext g).2.2 fun x => ?_
    by_cases hx : x ∈ U
    · rw [show x = ((⟨x, hx⟩ : U) : Euclid P) from rfl, hext_val]
      exact hg ⟨x, hx⟩
    · rw [hext_out _ x hx]
  -- the Riesz measure of `Λ_U` on `U`, pushed forward to `ℝᴾ`
  have hme : MeasurableEmbedding (Subtype.val : U → Euclid P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have hcpt : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IsCompact ((Subtype.val : U → Euclid P) ⁻¹' K) := by
    intro K hK hKU
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr hKU]
    exact hK
  refine ⟨(RealRMK.rieszMeasure ΛU).map Subtype.val, ?_, fun K hK hKU => ?_,
    fun f hf hfc hfU => ?_⟩
  · rw [hme.map_apply, Subtype.preimage_coe_compl, measure_empty]
  · rw [hme.map_apply]
    exact (hcpt K hK hKU).measure_lt_top
  · -- `f = ĝ` for `g = f ∘ Subtype.val ∈ C_c(U, ℝ)`
    let g : CompactlySupportedContinuousMap U ℝ :=
      ⟨⟨f ∘ Subtype.val, hf.comp continuous_subtype_val⟩,
        IsCompact.of_isClosed_subset (hcpt _ hfc hfU) (isClosed_tsupport _)
          (tsupport_comp_subset_preimage f continuous_subtype_val)⟩
    have hfg : Subtype.val.extend (g : U → ℝ) (0 : Euclid P → ℝ) = f := by
      funext x
      by_cases hx : x ∈ U
      · rw [show x = ((⟨x, hx⟩ : U) : Euclid P) from rfl, hext_val]
        rfl
      · rw [hext_out _ x hx, image_eq_zero_of_notMem_tsupport fun h => hx (hfU h)]
    rw [hme.integral_map]
    calc ∫ y, f y ∂RealRMK.rieszMeasure ΛU = ∫ y, g y ∂RealRMK.rieszMeasure ΛU := rfl
      _ = ΛU g := RealRMK.integral_rieszMeasure ΛU g
      _ = Λ f := congrArg Λ hfg

/-- **Simon 1.4.16, last step** (the vague limit is a Radon measure on `U`): if every `ν_j` is
finite on compact subsets of the open set `U ⊆ ℝᴾ` and `∫ f dν_j` converges for every continuous
`f` with compact support in `U`, then `Λ(f) = lim_j ∫ f dν_j` is additive, homogeneous and
non-negative on these `f` (such `f` are `ν_j`-integrable; uniqueness of limits), so Simon 1.4.12
on `U` gives `μ` with `μ(ℝᴾ \ U) = 0`, finite on compact subsets of `U`, and
`∫ f dμ = Λ(f) = lim_j ∫ f dν_j`. -/
theorem Submission.cbr_vague_limit_measure : ∀ (P : ℕ) (U : Set (Euclid P)) (νs : ℕ → Measure (Euclid P)), IsOpen U → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → νs j K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ c : ℝ, Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 c)) → ∃ μ : Measure (Euclid P), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  intro P U νs hU hν hlim
  -- the limit functional `Λ(f) = lim_j ∫ f dν_j`
  let Λ : (Euclid P → ℝ) → ℝ := fun f => limUnder atTop fun j => ∫ x, f x ∂(νs j)
  have hΛ : ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (Λ f)) :=
    fun f hf hfc hfU => tendsto_nhds_limUnder (hlim f hf hfc hfU)
  -- such `f` are `ν_j`-integrable, so `∫ · dν_j` is linear on them
  have hint : ∀ (j : ℕ) (f : Euclid P → ℝ), Continuous f → HasCompactSupport f →
      tsupport f ⊆ U → Integrable f (νs j) :=
    fun j f => Submission.cbr_vl_integrable_of_tsupport_subset P U (νs j) f (hν j)
  -- `Λ` is additive, homogeneous and non-negative, so it is integration against some `μ`
  obtain ⟨μ, hμU, hμK, hμΛ⟩ := Submission.cbr_vl_riesz_measure_on_open P U Λ hU
    (fun f g hf hfc hfU hg hgc hgU => by
      refine tendsto_nhds_unique (hΛ _ (hf.add hg) (hfc.add hgc)
        ((tsupport_add f g).trans (union_subset hfU hgU))) ?_
      refine ((hΛ f hf hfc hfU).add (hΛ g hg hgc hgU)).congr fun j => ?_
      exact (integral_add (hint j f hf hfc hfU) (hint j g hg hgc hgU)).symm)
    (fun c f hf hfc hfU => by
      have hcf : support (c • f) ⊆ support f := support_const_smul_subset c f
      refine tendsto_nhds_unique (hΛ _ (hf.const_smul c) (hfc.mono hcf)
        ((closure_mono hcf).trans hfU)) ?_
      refine ((hΛ f hf hfc hfU).const_mul c).congr fun j => ?_
      exact (integral_smul c f).symm)
    (fun f hf hfc hfU hf0 => ge_of_tendsto' (hΛ f hf hfc hfU) fun j => integral_nonneg hf0)
  refine ⟨μ, hμU, hμK, fun f hf hfc hfU => ?_⟩
  rw [hμΛ f hf hfc hfU]
  exact hΛ f hf hfc hfU
/-- **Portmanteau inequalities for vague convergence on an open set** (Evans–Gariepy §1.9).
Simon does not state this separately: it is the converse of the "standard approximation
argument" ending the proof of 7.2.4, and its compact-set half is the `ε`-neighbourhood argument
giving (13) there (chapter-07.txt lines 264–288).  Let `U` be open and `νⱼ`, `μ` finite on compact
subsets of `U`.  If `∫ f dνⱼ → ∫ f dμ` for every continuous `f` with compact support in `U`, then
`limsup νⱼ(K) ≤ μ(K)` for compact `K ⊆ U` and `μ(G) ≤ liminf νⱼ(G)` for open `G ⊆ U`.  Urysohn
cut-offs `1_K ≤ h ≤ 1_{thickening r K}` give `limsup νⱼ(K) ≤ μ(cthickening r K) → μ(K)` as
`r ↓ 0`; cut-offs `1_C ≤ h` with `tsupport h ⊆ G` give `μ(C) ≤ liminf νⱼ(G)` for compact
`C ⊆ G`, and `G` is exhausted by increasing compact sets. -/
theorem Submission.cbr_vague_portmanteau : ∀ (P : ℕ) (U : Set (Euclid P)) (νs : ℕ → Measure (Euclid P)) (μ : Measure (Euclid P)), IsOpen U → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → νs j K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(νs j)) atTop (𝓝 (∫ x, f x ∂μ))) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => νs j K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => νs j G) atTop) := by
  intro P U νs μ hU hνs hμ hconv
  -- Step 1: cut-off functions.  For compact `C` and `r > 0`, Urysohn's lemma gives a continuous
  -- `h` with compact support, `0 ≤ h ≤ 1`, `h = 1` on `C` and `h = 0` off `thickening r C`;
  -- hence `tsupport h ⊆ cthickening r C`
  have hcut : ∀ (C : Set (Euclid P)) (r : ℝ), IsCompact C → 0 < r →
      ∃ h : Euclid P → ℝ, Continuous h ∧ HasCompactSupport h ∧ (∀ x, 0 ≤ h x) ∧
        (∀ x ∈ C, h x = 1) ∧ (∀ x, h x ≤ 1) ∧ (∀ x, x ∉ thickening r C → h x = 0) ∧
        tsupport h ⊆ cthickening r C := by
    intro C r hC hr
    obtain ⟨h, h1, h0, hcs, h01⟩ := exists_continuous_one_zero_of_isCompact hC
      isOpen_thickening.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (self_subset_thickening hr C))
    refine ⟨h, h.continuous, hcs, fun x => (h01 x).1, fun x hx => h1 hx, fun x => (h01 x).2,
      fun x hx => h0 hx, (closure_mono fun x hx => ?_).trans
        (closure_thickening_subset_cthickening r C)⟩
    by_contra hxr
    exact hx (h0 hxr)
  -- Step 0: such an `h` is `ρ`-integrable whenever `ρ(tsupport h) < ∞`; then
  -- `ρ(B) ≤ ofReal (∫ h dρ)` if `h = 1` on `B` (`Integrable.measure_le_integral`), and in any
  -- case `ofReal (∫ h dρ) ≤ ρ(V)` if `h ≤ 1` and `h = 0` off `V` (`integral_le_measure`)
  have hint : ∀ (ρ : Measure (Euclid P)) (h : Euclid P → ℝ), Continuous h → HasCompactSupport h →
      ρ (tsupport h) < ∞ → Integrable h ρ := fun ρ h hc hcs hρ =>
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport h)).mp
      (hc.continuousOn.integrableOn_of_subset_isCompact hcs (isClosed_tsupport h).measurableSet
        subset_rfl hρ.ne)
  -- Step 2: compact sets.  Choose `δ > 0` with `cthickening δ K ⊆ U`; for `0 < r ≤ δ`,
  -- `limsup νⱼ(K) ≤ lim ofReal (∫ h dνⱼ) = ofReal (∫ h dμ) ≤ μ(cthickening r K)`, and
  -- `μ(cthickening r K) → μ(K)` as `r → 0` because `μ(cthickening δ K) < ∞`
  have hK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      limsup (fun j => νs j K) atTop ≤ μ K := by
    intro K hKc hKU
    obtain ⟨δ, hδ, hδU⟩ := hKc.exists_cthickening_subset_open hU hKU
    have hr : ∀ r, 0 < r → r ≤ δ → limsup (fun j => νs j K) atTop ≤ μ (cthickening r K) := by
      intro r hr hrδ
      obtain ⟨h, hc, hcs, h0, h1, hle1, hout, hts⟩ := hcut K r hKc hr
      have htsU : tsupport h ⊆ U := hts.trans ((cthickening_mono hrδ K).trans hδU)
      calc limsup (fun j => νs j K) atTop
          ≤ limsup (fun j => ENNReal.ofReal (∫ x, h x ∂(νs j))) atTop :=
            limsup_le_limsup (Eventually.of_forall fun j =>
              (hint (νs j) h hc hcs (hνs j _ hcs htsU)).measure_le_integral
                (Eventually.of_forall h0) fun x hx => (h1 x hx).ge)
        _ = ENNReal.ofReal (∫ x, h x ∂μ) :=
            ((ENNReal.continuous_ofReal.tendsto _).comp (hconv h hc hcs htsU)).limsup_eq
        _ ≤ μ (cthickening r K) := integral_le_measure (fun x _ => hle1 x)
            fun x hx => (hout x fun hx' => hx (thickening_subset_cthickening r K hx')).le
    have hlim := tendsto_measure_cthickening_of_isClosed
      ⟨δ, hδ, (hμ _ hKc.cthickening hδU).ne⟩ hKc.isClosed
    refine ge_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)) ?_
    filter_upwards [Ioc_mem_nhdsGT hδ] with r hr' using hr r hr'.1 hr'.2
  -- Step 3: compact subsets `C` of open `G ⊆ U`.  With `h = 1` on `C` and `tsupport h ⊆ G`,
  -- `μ(C) ≤ ofReal (∫ h dμ) = lim ofReal (∫ h dνⱼ) ≤ liminf νⱼ(G)`
  have hCG : ∀ G : Set (Euclid P), IsOpen G → G ⊆ U → ∀ C : Set (Euclid P), IsCompact C →
      C ⊆ G → μ C ≤ liminf (fun j => νs j G) atTop := by
    intro G hG hGU C hCc hCG
    obtain ⟨δ, hδ, hδG⟩ := hCc.exists_cthickening_subset_open hG hCG
    obtain ⟨h, hc, hcs, h0, h1, hle1, -, hts⟩ := hcut C δ hCc hδ
    have htsG : tsupport h ⊆ G := hts.trans hδG
    calc μ C ≤ ENNReal.ofReal (∫ x, h x ∂μ) :=
          (hint μ h hc hcs (hμ _ hcs (htsG.trans hGU))).measure_le_integral
            (Eventually.of_forall h0) fun x hx => (h1 x hx).ge
      _ = liminf (fun j => ENNReal.ofReal (∫ x, h x ∂(νs j))) atTop :=
          (((ENNReal.continuous_ofReal.tendsto _).comp
            (hconv h hc hcs (htsG.trans hGU))).liminf_eq).symm
      _ ≤ liminf (fun j => νs j G) atTop :=
          liminf_le_liminf (Eventually.of_forall fun j => integral_le_measure (fun x _ => hle1 x)
            fun x hx => (image_eq_zero_of_notMem_tsupport fun hx' => hx (htsG hx')).le)
  -- Step 4: open sets.  `G = ⋃ₙ Fₙ` with `Fₙ` closed and increasing, so `G` is exhausted by the
  -- increasing compact sets `Fₙ ∩ closedBall 0 n ⊆ G`; continuity from below and Step 3
  refine ⟨hK, fun G hG hGU => ?_⟩
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hCm : Monotone fun n : ℕ => F n ∩ closedBall (0 : Euclid P) n := fun m n hmn =>
    inter_subset_inter (hFm hmn) (closedBall_subset_closedBall (Nat.cast_le.mpr hmn))
  calc μ G ≤ μ (⋃ n : ℕ, F n ∩ closedBall (0 : Euclid P) n) := measure_mono fun x hx => by
        rw [← hFU] at hx
        obtain ⟨m, hm⟩ := mem_iUnion.mp hx
        obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
        exact mem_iUnion.mpr ⟨max m k, hFm (le_max_left m k) hm,
          mem_closedBall_zero_iff.mpr (hk.trans (Nat.cast_le.mpr (le_max_right m k)))⟩
    _ = ⨆ n : ℕ, μ (F n ∩ closedBall (0 : Euclid P) n) := hCm.measure_iUnion
    _ ≤ liminf (fun j => νs j G) atTop := iSup_le fun n =>
        hCG G hG hGU _ ((isCompact_closedBall 0 n).inter_left (hFc n))
          (inter_subset_left.trans (hFG n))
/-- A test form has bounded Euclidean coefficient norm: for `ω ∈ 𝒟ᵏ(U)` there is `M ≥ 0` with
`|ω(x)| ≤ M` for every `x` (Simon (6.1.15), `|ω|_U < ∞`).  The coefficient norm `|ω(x)|` is
continuous, as a square root of a finite sum of squares of evaluations of `ω(x)`, and vanishes
off `spt ω`, so it is continuous with compact support, hence bounded. -/
theorem Submission.cbr_rlim_coeffNorm_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ M : ℝ, 0 ≤ M ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M := by
  intro P k U ω
  obtain ⟨w, ⟨hws, hwcs⟩, -⟩ := ω
  change ∃ M : ℝ, 0 ≤ M ∧ ∀ x, covectorEuclideanNorm (w x) ≤ M
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  -- and vanishes off `spt w`, so it has compact support
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  -- hence it is bounded by some `M`, and by `max M 0`
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  exact ⟨max M 0, le_max_right _ _,
    fun x => ((Real.le_norm_self _).trans (hM x)).trans (le_max_left _ _)⟩
/-- **Smooth one-sided cut-off of a test form** (the `C^∞` version of the Lipschitz cut-off
`γ_ε ∘ f` in the proof of Simon 6.4.5(2)): for continuous `f`, `t` and `ε > 0` there is `χ` with
`0 ≤ χ ≤ 1`, `χ = 1` on `{f ≤ t - ε}` and `χ = 0` on `{f ≥ t}` such that `χ ω` is again a test
form in `U`.  The smooth Urysohn lemma for the closed set `{f ≤ t - ε}` inside the open set
`{f < t}` gives `χ`, and `χ ω` is smooth with `tsupport (χ ω) ⊆ tsupport ω ⊆ U` compact. -/
theorem Submission.cbr_rlim_smooth_cutoff : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k) (f : Euclid P → ℝ) (t ε : ℝ), Continuous f → 0 < ε → ∃ (χ : Euclid P → ℝ) (η : TestFormOn U k), (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, f x ≤ t - ε → χ x = 1) ∧ (∀ x, t ≤ f x → χ x = 0) := by
  intro P k U ω f t ε hf hε
  -- steps 1-2: a `C^∞` Urysohn function for the closed `{f ≤ t - ε}` inside the open `{f < t}`
  have hsub : {x | f x ≤ t - ε} ⊆ {x | f x < t} := fun x (hx : f x ≤ t - ε) =>
    show f x < t by linarith
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_lt hf continuous_const) (isClosed_le hf continuous_const) hsub
  -- step 3: `χ • ω` is smooth, compactly supported, with `tsupport (χ • ω) ⊆ tsupport ω ⊆ U`
  obtain ⟨⟨hω, hωc⟩, hωU⟩ := ω.2
  have hv : χ • (ω : DifferentialForm (Euclid P) k) ∈ testFormOnSubmodule U k :=
    ⟨⟨hχ.smul hω, hωc.smul_left⟩, (tsupport_smul_subset_right χ _).trans hωU⟩
  -- steps 4-5: `0 ≤ χ ≤ 1` from `range χ ⊆ [0, 1]`, and `χ = 1` exactly on `{f ≤ t - ε}`
  refine ⟨χ, ⟨_, hv⟩, fun x => rfl, fun x => hχr (mem_range_self x), fun x hx => (hχ1 x).1 hx,
    fun x hx => notMem_support.1 fun hx' => ?_⟩
  -- step 6: `t ≤ f x` puts `x` outside `support χ = {f < t}`
  rw [hχs] at hx'
  exact (not_lt.2 hx) hx'
/-- Cut-off error estimate for an admissible pair `(μ, ξ)` (`|ξ(x)(α)| ≤ |α|_E` for `μ`-a.e. `x`):
if `|ω|_E ≤ M`, `η = χ ω` with `0 ≤ χ ≤ 1`, `χ = 1` on `{f ≤ t − ε}` and `χ = 0` on `{f ≥ t}` (as
for the cut-off `γ_ε ∘ f` in the proof of Simon Ch. 6, 4.5(2)), then `∫_{f<t} ξ(ω) dμ` and
`∫ ξ(η) dμ` differ by at most `M μ(spt ω ∩ {t − ε < f < t})`.  Both integrands are bounded by
`M 1_{spt ω}`, and `1_{f<t} ξ(ω) − ξ(η) = (1_{f<t} − χ) ξ(ω)` vanishes off
`spt ω ∩ {t − ε < f < t}`. -/
theorem Submission.cbr_rlim_cutoff_error_le : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (ω η : TestFormOn U k) (χ f : Euclid P → ℝ) (t ε M : ℝ), Continuous f → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M) → (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x, f x ≤ t - ε → χ x = 1) → (∀ x, t ≤ f x → χ x = 0) → |(∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) - ∫ x, ξ x ((η : DifferentialForm (Euclid P) k) x) ∂μ| ≤ M * (μ (tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t})).toReal := by
  intro P k U μ ξ ω η χ f t ε M hf hμ hξm hξ hωM hη hχ hχ1 hχ0
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  have hηs := η.2.1.1
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  set v : DifferentialForm (Euclid P) k := (η : DifferentialForm (Euclid P) k)
  set C := tsupport w
  set S := {x | f x < t}
  set B := {x | t - ε < f x ∧ f x < t}
  -- Step 1: `M ≥ 0`.
  have hM : 0 ≤ M := (covectorEuclideanNorm_nonneg _).trans (hωM 0)
  -- Step 2: measurability and finiteness.
  have hCm : MeasurableSet C := (isClosed_tsupport w).measurableSet
  have hSm : MeasurableSet S := measurableSet_lt hf.measurable measurable_const
  have hBm : MeasurableSet B :=
    (measurableSet_lt measurable_const hf.measurable).inter
      (measurableSet_lt hf.measurable measurable_const)
  have hCf : μ C < ∞ := hμ C hωc hωU
  have hCBf : μ (C ∩ B) < ∞ := (measure_mono inter_subset_left).trans_lt hCf
  -- Step 3: `g = ξ(w)` and `h = ξ(v)` are a.e. strongly measurable.
  have hgm : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξm
      (ContDiff.continuous hωs).aestronglyMeasurable
  have hhm : AEStronglyMeasurable (fun x => ξ x (v x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξm
      (ContDiff.continuous hηs).aestronglyMeasurable
  -- Step 4: `|g| ≤ M` a.e., `g = 0` off `C`, so `g` is integrable.
  have hg0 : ∀ x, x ∉ C → ξ x (w x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, map_zero]
  have hgM : ∀ᵐ x ∂μ, |ξ x (w x)| ≤ M := by
    filter_upwards [hξ] with x hx
    exact (hx _).trans (hωM x)
  have hCi : Integrable (C.indicator fun _ => M) μ :=
    (integrable_indicator_iff hCm).2 (integrableOn_const hCf.ne)
  have hgi : Integrable (fun x => ξ x (w x)) μ := by
    refine hCi.mono' hgm ?_
    filter_upwards [hgM] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs]
      exact hx
    · rw [indicator_of_notMem hxC, hg0 x hxC, norm_zero]
  -- Step 5: `h = χ g`, so `h` is integrable.
  have hhg : ∀ x, ξ x (v x) = χ x * ξ x (w x) := fun x => by
    rw [hη x, map_smul, smul_eq_mul]
  have hhi : Integrable (fun x => ξ x (v x)) μ := by
    refine hgi.mono hhm (Eventually.of_forall fun x => ?_)
    rw [hhg x, norm_mul, Real.norm_eq_abs (χ x), abs_of_nonneg (hχ x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x).2
  -- Step 6: rewrite the difference as one integral.
  rw [← integral_indicator hSm, ← integral_sub (hgi.indicator hSm) hhi]
  -- Step 7: pointwise bound by `M 1_{C ∩ B}`.
  have hbd : ∀ᵐ x ∂μ, ‖S.indicator (fun x => ξ x (w x)) x - ξ x (v x)‖ ≤
      (C ∩ B).indicator (fun _ => M) x := by
    filter_upwards [hgM] with x hx
    have hnn : 0 ≤ (C ∩ B).indicator (fun _ => M) x := indicator_nonneg (fun _ _ => hM) x
    rw [hhg x]
    by_cases hxS : f x < t
    · rw [indicator_of_mem (show x ∈ S from hxS)]
      by_cases hxε : f x ≤ t - ε
      · rw [hχ1 x hxε, one_mul, sub_self, norm_zero]
        exact hnn
      · by_cases hxC : x ∈ C
        · rw [indicator_of_mem (show x ∈ C ∩ B from ⟨hxC, not_le.1 hxε, hxS⟩)]
          rw [← one_sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.2 (hχ x).2)]
          exact (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self 1 (hχ x).1)).trans hx
        · rw [hg0 x hxC, mul_zero, sub_zero, norm_zero]
          exact hnn
    · rw [indicator_of_notMem (show x ∉ S from hxS), hχ0 x (not_lt.1 hxS), zero_mul, sub_zero,
        norm_zero]
      exact hnn
  -- Step 8: integrate the majorant.
  have hmi : Integrable ((C ∩ B).indicator fun _ => M) μ :=
    (integrable_indicator_iff (hCm.inter hBm)).2 (integrableOn_const hCBf.ne)
  calc |∫ x, S.indicator (fun x => ξ x (w x)) x - ξ x (v x) ∂μ|
      = ‖∫ x, S.indicator (fun x => ξ x (w x)) x - ξ x (v x) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, (C ∩ B).indicator (fun _ => M) x ∂μ := norm_integral_le_of_norm_le hmi hbd
    _ = M * (μ (C ∩ B)).toReal := by
      rw [integral_indicator_const M (hCm.inter hBm), smul_eq_mul, measureReal_def, mul_comm]
/-- A thin level band of small measure: if `C` is measurable with `μ(C), ν(C) < ∞`, `f` is
continuous, `μ{f = t} = 0` and `δ > 0`, then some `ε > 0` has `μ(C ∩ {t − ε ≤ f ≤ t}) < δ` and
`ν(C ∩ {t − ε < f < t}) < δ`.  The closed bands of width `1/(n+1)` decrease into the `μ`-null set
`{f = t}` and the open ones decrease to `∅`, so by continuity from above both measures tend
to `0`. -/
theorem Submission.cbr_rlim_thin_band : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (C : Set (Euclid P)) (f : Euclid P → ℝ) (t δ : ℝ), MeasurableSet C → μ C < ∞ → ν C < ∞ → Continuous f → μ {x | f x = t} = 0 → 0 < δ → ∃ ε : ℝ, 0 < ε ∧ μ (C ∩ {x | t - ε ≤ f x ∧ f x ≤ t}) < ENNReal.ofReal δ ∧ ν (C ∩ {x | t - ε < f x ∧ f x < t}) < ENNReal.ofReal δ := by
  intro P μ ν C f t δ hC hμC hνC hf hμt hδ
  have hfm : Measurable f := hf.measurable
  -- the widths `1 / (n + 1)` decrease, so the closed and the open bands decrease in `n`
  have hr : Antitone fun n : ℕ => 1 / ((n : ℝ) + 1) := fun _ _ h => Nat.one_div_le_one_div h
  have hAm : Antitone fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t} :=
    fun _ _ h x hx => ⟨hx.1, (sub_le_sub_left (hr h) t).trans hx.2.1, hx.2.2⟩
  have hBm : Antitone fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t} :=
    fun _ _ h x hx => ⟨hx.1, (sub_le_sub_left (hr h) t).trans_lt hx.2.1, hx.2.2⟩
  -- the closed bands shrink into the `μ`-null level set `{f = t}`
  have hA0 : μ (⋂ n : ℕ, C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t}) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hμt
    rw [mem_iInter] at hx
    refine le_antisymm (hx 0).2.2 (le_of_not_gt fun hlt => ?_)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    linarith [(hx n).2.1]
  -- the open bands shrink to the empty set
  have hB0 : ν (⋂ n : ℕ, C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t}) = 0 := by
    refine measure_mono_null (fun x hx => ?_) measure_empty
    rw [mem_iInter] at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hx 0).2.2)
    exact absurd (hx n).2.1 (by linarith)
  -- continuity from above (the first bands have finite measure): eventually both band
  -- measures are below `δ`
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have hA := (tendsto_measure_iInter_atTop
    (s := fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t})
    (fun _ => (hC.inter ((measurableSet_le measurable_const hfm).inter
      (measurableSet_le hfm measurable_const))).nullMeasurableSet) hAm
    ⟨0, ((measure_mono inter_subset_left).trans_lt hμC).ne⟩).eventually_lt_const
    (hA0.trans_lt hδ')
  have hB := (tendsto_measure_iInter_atTop
    (s := fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t})
    (fun _ => (hC.inter ((measurableSet_lt measurable_const hfm).inter
      (measurableSet_lt hfm measurable_const))).nullMeasurableSet) hBm
    ⟨0, ((measure_mono inter_subset_left).trans_lt hνC).ne⟩).eventually_lt_const
    (hB0.trans_lt hδ')
  obtain ⟨N, hN⟩ := (hA.and hB).exists
  exact ⟨1 / ((N : ℝ) + 1), Nat.one_div_pos_of_nat, hN.1, hN.2⟩
/-- **Restriction to a sublevel set passes to weak limits** (the step of Simon Ch. 6, Remark
8.3(1), `T_j ⌞ {f < t} ⇀ T ⌞ {f < t}`, justified there "by an argument like that in 6.7(2) of
Ch. 2"): if `X_j ⇀ X` are represented by admissible pairs `(μ_j, ξ_j)`, `(μ_X, ξ_X)`, the
`μ_j` are dominated in the limit by `μ` on compact subsets of `U`, and `μ{f = t} = 0`, then
`∫_{f<t} ξ_j(ω) dμ_j → ∫_{f<t} ξ_X(ω) dμ_X` for every test form `ω`.  This is an `ε/3`
argument: with `|ω|_E ≤ M`, a thin band `{t − ε ≤ f ≤ t}` of `μ`- and `μ_X`-measure `< δ` on
`spt ω`, and the smooth cut-off `η = χ ω`, both restricted integrals are within `M δ` of
`X_j(η)` resp. `X(η)` (eventually in `j`, by the `limsup` bound on the compact band), and
`X_j(η) → X(η)`. -/
theorem Submission.cbr_sublevel_restriction_tendsto : ∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX)) := by
  intro P k U Xs X μs ξs μX μ ξX f t _ hf hconv hμs hξsm hξs hXs hμX hξXm hξX hX hμ hlim hμt ω
  obtain ⟨-, hωc⟩ := ω.2.1
  have hωU := ω.2.2
  -- step 1: `|ω|_E ≤ M` everywhere
  obtain ⟨M, hM, hωM⟩ := Submission.cbr_rlim_coeffNorm_bound P k U ω
  rw [Metric.tendsto_nhds]
  intro e he
  -- step 6: a band of width `ε` with `μ`- and `μ_X`-measure `< δ` on `spt ω`
  have hδ : 0 < e / (3 * (M + 1)) := div_pos he (by positivity)
  have hMδ : M * (e / (3 * (M + 1))) ≤ e / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨ε, hε, hband, hbandX⟩ := Submission.cbr_rlim_thin_band P μ μX
    (tsupport (ω : DifferentialForm (Euclid P) k)) f t (e / (3 * (M + 1)))
    (isClosed_tsupport _).measurableSet (hμ _ hωc hωU) (hμX _ hωc hωU) hf hμt hδ
  -- steps 3-4: the cut-off test form `η = χ ω`
  obtain ⟨χ, η, hη, hχ, hχ1, hχ0⟩ := Submission.cbr_rlim_smooth_cutoff P k U ω f t ε hf hε
  -- step 7: the closed band is a compact subset of `U`, so eventually `μ_j(band) < δ`
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε ≤ f x ∧ f x ≤ t}) :=
    IsCompact.inter_right hωc ((isClosed_le continuous_const hf).inter
      (isClosed_le hf continuous_const))
  have hev := eventually_lt_of_limsup_lt
    ((hlim _ hKc (inter_subset_left.trans hωU)).trans_lt hband)
  filter_upwards [hev, (hconv η).eventually (Metric.ball_mem_nhds (X η) (by positivity : 0 < e / 3))]
    with j hj hjη
  -- step 5: the cut-off errors for `(μ_j, ξ_j)` and `(μ_X, ξ_X)`, each at most `M δ ≤ e / 3`
  have hej := Submission.cbr_rlim_cutoff_error_le P k U (μs j) (ξs j) ω η χ f t ε M hf (hμs j)
    (hξsm j) (hξs j) hωM hη hχ hχ1 hχ0
  have heX := Submission.cbr_rlim_cutoff_error_le P k U μX ξX ω η χ f t ε M hf hμX hξXm hξX hωM
    hη hχ hχ1 hχ0
  have hsub : tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t} ⊆
      tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε ≤ f x ∧ f x ≤ t} :=
    fun x hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hbj : M * (μs j (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε < f x ∧ f x < t})).toReal ≤ e / 3 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal
      ((measure_mono hsub).trans_lt hj)).le hM).trans hMδ
  have hbX : M * (μX (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε < f x ∧ f x < t})).toReal ≤ e / 3 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hbandX).le hM).trans hMδ
  have h1 := abs_le.1 (hej.trans hbj)
  have h3 := abs_le.1 (heX.trans hbX)
  have h2 := abs_lt.1 (show |Xs j η - X η| < e / 3 from Metric.mem_ball.1 hjη)
  rw [hXs j η, hX η] at h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
/-- **Strip masses of an arbitrary set** (Simon Ch. 6, remark before 4.10: `M_W(T⌞{f < t})` is
increasing in `t`).  Put `F(s) = μ(G ∩ {a < f < min(s, b)})`, finite by hypothesis.  Then `F` is
nondecreasing, `F(b) − F(a) = μ(G ∩ {a < f < b})`, and `μ(G ∩ {t − h < f < t}) ≤ F(t) − F(t − h)`
because the strip `{t − h < f < t}` is open, hence measurable, and splits the possibly
non-measurable `G ∩ {a < f < t}` into `G ∩ {t − h < f < t}` and a superset of
`G ∩ {a < f < t − h}`. -/
theorem Submission.cbr_smm_strip_distribution_function : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ), Continuous f → μ (G ∩ {x | a < f x ∧ f x < b}) < ∞ → ∃ F : ℝ → ℝ, Monotone F ∧ ENNReal.ofReal (F b - F a) = μ (G ∩ {x | a < f x ∧ f x < b}) ∧ ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a), μ (G ∩ {x | t - h < f x ∧ f x < t}) ≤ ENNReal.ofReal (F t - F (t - h)) := by
  intro P μ f G a b hf hfin
  -- `G ∩ {a < f < s}` increases with `s` and has finite measure for `s ≤ b`
  have hmono : ∀ {s s' : ℝ}, s ≤ s' →
      G ∩ {x | a < f x ∧ f x < s} ⊆ G ∩ {x | a < f x ∧ f x < s'} :=
    fun hss' x hx => ⟨hx.1, hx.2.1, hx.2.2.trans_le hss'⟩
  have hfin' : ∀ {s : ℝ}, s ≤ b → μ (G ∩ {x | a < f x ∧ f x < s}) ≠ ∞ :=
    fun hs => ((measure_mono (hmono hs)).trans_lt hfin).ne
  refine ⟨fun s => (μ (G ∩ {x | a < f x ∧ f x < min s b})).toReal, ?_, ?_, ?_⟩
  · intro s s' hss'
    exact ENNReal.toReal_mono (hfin' (min_le_right _ _))
      (measure_mono (hmono (min_le_min_right b hss')))
  · simp only [min_self]
    rcases le_or_gt b a with hba | hab
    · -- `b ≤ a`: both sides vanish
      have hempty : G ∩ {x | a < f x ∧ f x < b} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => (hx.2.1.trans hx.2.2).not_ge hba
      rw [min_eq_right hba, sub_self, ENNReal.ofReal_zero, hempty, measure_empty]
    · -- `a < b`: `F a = μ ∅ = 0`
      have hempty : G ∩ {x | a < f x ∧ f x < a} = ∅ :=
        eq_empty_of_forall_notMem fun x hx => (hx.2.1.trans hx.2.2).false
      rw [min_eq_left hab.le, hempty, measure_empty, ENNReal.toReal_zero, sub_zero,
        ENNReal.ofReal_toReal hfin.ne]
  · rintro t ⟨-, htb⟩ h ⟨hh0, hht⟩
    have hst : t - h ≤ b := by linarith
    simp only [min_eq_left htb.le, min_eq_left hst]
    -- the strip `{t - h < f < t}` is open, hence measurable; split `G ∩ {a < f < t}` along it
    have hS : MeasurableSet {x | t - h < f x ∧ f x < t} :=
      ((isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)).measurableSet
    have hinter : G ∩ {x | a < f x ∧ f x < t} ∩ {x | t - h < f x ∧ f x < t} =
        G ∩ {x | t - h < f x ∧ f x < t} :=
      Subset.antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx =>
        ⟨⟨hx.1, by linarith [hx.2.1], hx.2.2⟩, hx.2⟩
    have hdiff : G ∩ {x | a < f x ∧ f x < t - h} ⊆
        (G ∩ {x | a < f x ∧ f x < t}) \ {x | t - h < f x ∧ f x < t} :=
      fun x hx => ⟨hmono (by linarith) hx, fun hx' => hx.2.2.not_gt hx'.1⟩
    have key : μ (G ∩ {x | t - h < f x ∧ f x < t}) + μ (G ∩ {x | a < f x ∧ f x < t - h}) ≤
        μ (G ∩ {x | a < f x ∧ f x < t}) := by
      rw [← measure_inter_add_sdiff (G ∩ {x | a < f x ∧ f x < t}) hS, hinter]
      exact add_le_add le_rfl (measure_mono hdiff)
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin' htb.le),
      ENNReal.ofReal_toReal (hfin' hst)]
    exact ENNReal.le_sub_of_add_le_right (hfin' hst) key
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cbr_smm_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)
/-- **Left slopes at a point of differentiability** (Simon Ch. 6, 4.9 and (2) in the proof of
8.2).  If `F : ℝ → ℝ` is differentiable at `t`, then
`liminf_{h → 0+} ofReal (h⁻¹) * ofReal (F(t) - F(t - h)) ≤ ofReal (F′(t))`.  The left difference
quotients `h⁻¹ (F(t) - F(t - h))` tend to `F′(t)` as `h ↓ 0`; for `h > 0` the product above is
`ofReal` of the quotient, so it tends to `ofReal (F′(t))`, and along `𝓝[>] 0` the liminf of a
convergent function is its limit.  Monotonicity of `F` is not needed. -/
theorem Submission.cbr_smm_liminf_left_slope_le_deriv : ∀ (F : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ F t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h))) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv F t) := by
  intro F t hF
  -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
  have hlim : Tendsto (fun h : ℝ => h⁻¹ * (F t - F (t - h))) (𝓝[>] 0) (𝓝 (deriv F t)) := by
    refine (hF.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
    simp only [Function.comp_apply, smul_eq_mul]
    rw [← sub_eq_add_neg, inv_neg]
    ring
  -- for `h > 0`, `ofReal h⁻¹ * ofReal (F t - F (t - h)) = ofReal (h⁻¹ * (F t - F (t - h)))`
  have hlim' : Tendsto (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (deriv F t))) := by
    refine (ENNReal.tendsto_ofReal hlim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact ENNReal.ofReal_mul (inv_nonneg.2 hh.le)
  exact hlim'.liminf_eq.le

/-- **Fatou majorant from left difference quotients** (Simon Ch. 6, 4.9–4.10, integrated over a
sequence as in Remark 8.3(1)): if the `F_j` are nondecreasing and
`Z_j(t) ≤ L · liminf_{h↓0} h⁻¹ (F_j(t) − F_j(t − h))` on `(a, b)`, then `g = L · liminf_j F_j′`
is measurable, `liminf_j Z_j ≤ g` a.e. on `(a, b)`, and
`∫⁻_{(a,b)} g ≤ L · liminf_j (F_j(b) − F_j(a))`.  Wherever every `F_j` is differentiable (a.e.,
by Lebesgue's theorem) the left difference quotient tends to `F_j′`; the integral bound is
Fatou's lemma plus `∫⁻_{(a,b)} F_j′ ≤ F_j(b) − F_j(a)`. -/
theorem Submission.cbr_smm_monotone_majorant : ∀ (F : ℕ → ℝ → ℝ) (Z : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (L : NNReal), (∀ j, Monotone (F j)) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F j t - F j (t - h))) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (F j b - F j a)) atTop := by
  intro F Z a b L hF hZ
  -- the densities `d_j = F_j′` and `g = L · liminf_j d_j` are measurable
  have hd : ∀ j, Measurable fun t => ENNReal.ofReal (deriv (F j) t) :=
    fun j => (measurable_deriv (F j)).ennreal_ofReal
  have hlim : Measurable fun t => liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop :=
    Measurable.liminf hd
  refine ⟨fun t => (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop,
    hlim.const_mul _, ?_, ?_⟩
  · -- a.e. every `F_j` is differentiable, and there `Z_j ≤ L · d_j`
    have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), ∀ j, DifferentiableAt ℝ (F j) t :=
      ae_all_iff.2 fun j => (hF j).ae_differentiableAt
    filter_upwards [hdiff] with t ht htab
    have hle : ∀ j, Z j t ≤ (L : ℝ≥0∞) * ENNReal.ofReal (deriv (F j) t) := fun j =>
      (hZ j t htab).trans
        (by gcongr; exact Submission.cbr_smm_liminf_left_slope_le_deriv (F j) t (ht j))
    calc liminf (fun j => Z j t) atTop
        ≤ liminf (fun j => (L : ℝ≥0∞) * ENNReal.ofReal (deriv (F j) t)) atTop :=
          liminf_le_liminf (Eventually.of_forall hle)
      _ = (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop :=
          ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top
  · -- Fatou's lemma, then `∫⁻_{(a,b)} F_j′ ≤ F_j(b) − F_j(a)` for each `j`
    calc ∫⁻ t in Ioo a b, (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop
        = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b, liminf (fun j => ENNReal.ofReal (deriv (F j) t)) atTop :=
          lintegral_const_mul _ hlim
      _ ≤ (L : ℝ≥0∞) * liminf (fun j => ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv (F j) t)) atTop := by
          gcongr
          exact lintegral_liminf_le hd
      _ ≤ (L : ℝ≥0∞) * liminf (fun j => ENNReal.ofReal (F j b - F j a)) atTop := by
          gcongr
          exact liminf_le_liminf (Eventually.of_forall fun j =>
            Submission.cbr_smm_lintegral_ofReal_deriv_le (F j) a b (hF j))

/-- **Measurable majorant for slice masses** (Simon Ch. 6, 4.9–4.10 and the sentence between
them, in the sequence form used for Remark 8.3(1)).  For each `j` let `F_j` be the distribution
function of the strip masses of `G` (`cbr_smm_strip_distribution_function`): `F_j` is monotone,
`F_j(b) − F_j(a) = μ_j(G ∩ {a < f < b})` and `μ_j(G ∩ {t − h < f < t}) ≤ F_j(t) − F_j(t − h)` for
`0 < h < t − a`, i.e. eventually as `h ↓ 0`.  So the bound on `Z_j` passes to the left difference
quotients of `F_j`, and `cbr_smm_monotone_majorant` gives `g`. -/
theorem Submission.cbr_slice_mass_majorant : ∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop := by
  intro P μs f G a b L Z hf hfin hZ
  -- the distribution functions `F_j` of the strip masses
  choose F hFmono hFab hFstrip using fun j =>
    Submission.cbr_smm_strip_distribution_function P (μs j) f G a b hf (hfin j)
  -- for `0 < h < t − a` (a neighbourhood of `0⁺`) the strip mass is at most `F_j(t) − F_j(t − h)`
  have hZF : ∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) *
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F j t - F j (t - h))) (𝓝[>] 0) := by
    intro j t ht
    refine (hZ j t ht).trans (mul_le_mul_right (liminf_le_liminf ?_) _)
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact mul_le_mul_right (hFstrip j t ht h hh) _
  obtain ⟨g, hg, hgae, hgint⟩ := Submission.cbr_smm_monotone_majorant F Z a b L hFmono hZF
  -- `F_j(b) − F_j(a) = μ_j(G ∩ {a < f < b})`
  refine ⟨g, hg, hgae, hgint.trans_eq ?_⟩
  simp only [hFab]

/-- **Measure convergence tools** for the closure theorem (Simon Ch. 6, 8.2–8.3, as used for
7.2.4).  (T1) Compactness of Radon measures on an open `U ⊆ ℝᴾ` (Simon Ch. 1, 4.16) together with
the semicontinuity inequalities `limsup μ_{φ j}(K) ≤ μ(K)` (`K ⊆ U` compact) and
`μ(G) ≤ liminf μ_{φ j}(G)` (`G ⊆ U` open); (T2) convergence of the restricted actions
`∫_{f<t} ξⱼ(ω) dμⱼ → ∫_{f<t} ξ_X(ω) dμ_X` when `Xⱼ ⇀ X` and `μ{f = t} = 0`; (MM) a measurable
majorant `g` of `liminfⱼ Zⱼ` for slice masses `Zⱼ(t) ≤ L · liminf_{h↓0} h⁻¹ μⱼ(G ∩ {t − h < f < t})`
with `∫_{(a,b)} g ≤ L · liminfⱼ μⱼ(G ∩ {a < f < b})`.  For (T1) pass to a subsequence along which
every `∫ f dμ_{φ j}`, `f ∈ C_c(U)`, converges, represent the limit functional by a measure carried
by `U` (Riesz–Markov–Kakutani), and obtain both inequalities by Urysohn approximation. -/
theorem Submission.cbr_measure_convergence_tools : (∀ (P : ℕ) (U : Set (Euclid P)) (μs : ℕ → Measure (Euclid P)), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ⨆ j, μs j K < ∞) → ∃ (φ : ℕ → ℕ) (μ : Measure (Euclid P)), StrictMono φ ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → Tendsto (fun j => ∫ x, f x ∂(μs (φ j))) atTop (𝓝 (∫ x, f x ∂μ))) ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs (φ j) K) atTop ≤ μ K) ∧ (∀ G : Set (Euclid P), IsOpen G → G ⊆ U → μ G ≤ liminf (fun j => μs (φ j) G) atTop)) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX))) ∧ (∀ (P : ℕ) (μs : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (G : Set (Euclid P)) (a b : ℝ) (L : NNReal) (Z : ℕ → ℝ → ℝ≥0∞), Continuous f → (∀ j, μs j (G ∩ {x | a < f x ∧ f x < b}) < ∞) → (∀ (j : ℕ) (t : ℝ), t ∈ Ioo a b → Z j t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μs j (G ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => Z j t) atTop ≤ g t) ∧ ∫⁻ t in Ioo a b, g t ≤ (L : ℝ≥0∞) * liminf (fun j => μs j (G ∩ {x | a < f x ∧ f x < b})) atTop) := by
  refine ⟨?_, Submission.cbr_sublevel_restriction_tendsto, Submission.cbr_slice_mass_majorant⟩
  intro P U μs hU hbound
  -- a subsequence along which `∫ f dμ_{φ j}` converges for every `f ∈ C_c(U)`
  obtain ⟨φ, hφ, hconv⟩ := Submission.cbr_vague_convergent_subseq P U μs hU hbound
  -- the subsequence is finite on compact subsets of `U`
  have hfin : ∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μs (φ j) K < ∞ :=
    fun j K hK hKU => (le_iSup (fun i => μs i K) (φ j)).trans_lt (hbound K hK hKU)
  -- the limit functional is integration against a measure `μ` carried by `U`
  obtain ⟨μ, hμU, hμK, hμconv⟩ :=
    Submission.cbr_vague_limit_measure P U (fun j => μs (φ j)) hU hfin hconv
  -- upper semicontinuity on compact sets, lower semicontinuity on open sets
  obtain ⟨hlimsup, hliminf⟩ :=
    Submission.cbr_vague_portmanteau P U (fun j => μs (φ j)) μ hU hfin hμK hμconv
  exact ⟨φ, μ, hφ, hμU, hμK, hμconv, hlimsup, hliminf⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
