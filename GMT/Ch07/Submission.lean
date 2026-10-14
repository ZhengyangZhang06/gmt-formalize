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

/-- **Simon, proof of A.4** (the rescaled secants): if `S ∩ B_σ(0)` is infinite for some `σ < 1`,
there are `x` with `|x| < 1`, scales `λ_k ↓ 0` with `λ_k < 1` and `|x| ≤ 1 − λ_k`, and points
`z_k → z` with `|z_k| = |z| = 1/2` and `x + λ_k z_k ∈ S`.  Distinct points of `S ∩ B_σ(0)`
subconverge to some `x ∈ B̄_σ(0)`; a tail `q_k ∈ S \ {x}` still tends to `x`, so the scales
`λ = 2|q − x| > 0` tend to `0` and are made strictly decreasing and `≤ (1 − |x|)/2` along
inductively chosen indices; the secants `(q − x)/λ` lie on the compact sphere `|w| = 1/2`, so a
further subsequence converges. -/
theorem Submission.adr_secant_rescaling_of_infinite : ∀ (P : ℕ) (S : Set (Euclid P)) (σ : ℝ), σ < 1 → (S ∩ ball (0 : Euclid P) σ).Infinite → ∃ (x : Euclid P) (lams : ℕ → ℝ) (zs : ℕ → Euclid P) (z : Euclid P), ‖x‖ < 1 ∧ (∀ k, 0 < lams k) ∧ StrictAnti lams ∧ Tendsto lams atTop (𝓝 0) ∧ (∀ k, lams k < 1) ∧ (∀ k, ‖x‖ ≤ 1 - lams k) ∧ (∀ k, x + lams k • zs k ∈ S) ∧ (∀ k, ‖zs k‖ = 1 / 2) ∧ Tendsto zs atTop (𝓝 z) ∧ ‖z‖ = 1 / 2 := by
  intro P S σ hσ hinf
  -- pairwise distinct points `p k ∈ S ∩ B_σ(0)`
  let e := Set.Infinite.natEmbedding _ hinf
  let p : ℕ → Euclid P := fun k => (e k : Euclid P)
  have hp : Injective p := Subtype.val_injective.comp e.injective
  -- a subsequence `p ∘ m` converges to some `x ∈ B̄_σ(0)`, so `|x| ≤ σ < 1`
  obtain ⟨x, hxσ, m, hm, hpx⟩ := (isCompact_closedBall (0 : Euclid P) σ).tendsto_subseq
    fun k => ball_subset_closedBall (e k).2.2
  have hx : ‖x‖ < 1 := (mem_closedBall_zero_iff.mp hxσ).trans_lt hσ
  -- by injectivity at most one `p (m j)` equals `x`, so a tail `q k = p (m (k + j₁))` avoids `x`
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, ∀ j ≥ j₁, p (m j) ≠ x := by
    by_cases h : ∃ j₀, p (m j₀) = x
    · obtain ⟨j₀, hj₀⟩ := h
      exact ⟨j₀ + 1, fun j hj hjx => (hm (Nat.lt_of_succ_le hj)).ne' (hp (hjx.trans hj₀.symm))⟩
    · push Not at h
      exact ⟨0, fun j _ => h j⟩
  let q : ℕ → Euclid P := fun k => p (m (k + j₁))
  have hqS : ∀ k, q k ∈ S := fun k => (e (m (k + j₁))).2.1
  have hqx : ∀ k, ‖q k - x‖ ≠ 0 := fun k =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hj₁ _ (Nat.le_add_left _ _)))
  have hq : Tendsto q atTop (𝓝 x) := hpx.comp (tendsto_add_atTop_nat j₁)
  -- the scales `a k = 2|q k − x|` are positive and tend to `0`
  let a : ℕ → ℝ := fun k => 2 * ‖q k - x‖
  have ha : ∀ k, 0 < a k := fun k => mul_pos two_pos ((norm_nonneg _).lt_of_ne' (hqx k))
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp hq).const_mul 2
    rwa [mul_zero] at h
  -- indices `ks j` with `a (ks 0) ≤ (1 − |x|)/2` along which `a` strictly decreases
  obtain ⟨k₀, hk₀⟩ := (ha0.eventually (ge_mem_nhds (half_pos (sub_pos.mpr hx)))).exists
  have hnext : ∀ k, ∃ k', k < k' ∧ a k' < a k := fun k =>
    ((eventually_gt_atTop k).and (ha0.eventually (gt_mem_nhds (ha k)))).exists
  choose nxt hnxt using hnext
  let ks : ℕ → ℕ := fun j => Nat.rec (motive := fun _ => ℕ) k₀ (fun _ kj => nxt kj) j
  have hks : StrictMono ks := strictMono_nat_of_lt_succ fun j => (hnxt (ks j)).1
  have haks : StrictAnti (a ∘ ks) := strictAnti_nat_of_succ_lt fun j => (hnxt (ks j)).2
  have haks_le : ∀ j, a (ks j) ≤ (1 - ‖x‖) / 2 := fun j =>
    (haks.antitone (Nat.zero_le j)).trans hk₀
  -- the rescaled secants `w j = (q (ks j) − x)/a (ks j)` lie on the sphere `|w| = 1/2`
  let w : ℕ → Euclid P := fun j => (a (ks j))⁻¹ • (q (ks j) - x)
  have hw : ∀ j, ‖w j‖ = 1 / 2 := fun j => by
    change ‖(2 * ‖q (ks j) - x‖)⁻¹ • (q (ks j) - x)‖ = 1 / 2
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (ha _).le, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hqx _), mul_one, one_div]
  obtain ⟨z, hz, ψ, hψ, hwz⟩ := (isCompact_sphere (0 : Euclid P) (1 / 2)).tendsto_subseq
    fun j => mem_sphere_zero_iff_norm.mpr (hw j)
  refine ⟨x, fun i => a (ks (ψ i)), fun i => w (ψ i), z, hx, fun i => ha _,
    haks.comp_strictMono hψ, ha0.comp (hks.comp hψ).tendsto_atTop, fun i => ?_, fun i => ?_,
    fun i => ?_, fun i => hw _, hwz, mem_sphere_zero_iff_norm.mp hz⟩
  · linarith [haks_le (ψ i), norm_nonneg x]
  · linarith [haks_le (ψ i)]
  · change x + a (ks (ψ i)) • (a (ks (ψ i)))⁻¹ • (q (ks (ψ i)) - x) ∈ S
    rw [smul_inv_smul₀ (ha _).ne', add_sub_cancel]
    exact hqS _
/-- **Radial segment** (Simon, proof of A.4: `H¹(sing ψ ∩ B_1(0)) > 0`).  If `S` contains the
radial segment `{t z : 0 < t ≤ 1}`, where `z ≠ 0` and `|z| < 1`, then `μH[1](S ∩ B_1(0)) > 0`:
the closed segment `[z / 2, z]` lies in `S ∩ B_1(0)`, its endpoints differ, and its
`μH[1]`-measure is the distance between them (`hausdorffMeasure_segment`). -/
theorem Submission.adr_radial_segment_hausdorff_pos : ∀ (P : ℕ) (S : Set (Euclid P)) (z : Euclid P), z ≠ 0 → ‖z‖ < 1 → (∀ t : ℝ, 0 < t → t ≤ 1 → t • z ∈ S) → 0 < μH[1] (S ∩ ball (0 : Euclid P) 1) := by
  intro P S z hz hz1 hS
  -- a point `α • (z / 2) + β • z` of `[z / 2, z]` is `t • z` with `t = α / 2 + β ∈ (0, 1]`, so it
  -- lies in `S`, and `|t z| ≤ |z| < 1`
  have hsub : segment ℝ ((1 / 2 : ℝ) • z) z ⊆ S ∩ ball (0 : Euclid P) 1 := by
    rintro w ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hw : α • (1 / 2 : ℝ) • z + β • z = (α / 2 + β) • z := by
      rw [smul_smul, ← add_smul, mul_one_div]
    have ht0 : 0 < α / 2 + β := by linarith
    have ht1 : α / 2 + β ≤ 1 := by linarith
    rw [hw]
    refine ⟨hS _ ht0 ht1, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht0.le]
    calc (α / 2 + β) * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 1 := by rwa [one_mul]
  -- `z / 2 ≠ z`, since otherwise `(1 / 2 - 1) • z = 0` forces `z = 0`
  have hne : (1 / 2 : ℝ) • z ≠ z := by
    intro h
    have h' : ((1 / 2 : ℝ) - 1) • z = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact hz ((smul_eq_zero.mp h').resolve_left (by norm_num))
  calc (0 : ℝ≥0∞) < edist ((1 / 2 : ℝ) • z) z := edist_pos.mpr hne
    _ = μH[1] (segment ℝ ((1 / 2 : ℝ) • z) z) := (hausdorffMeasure_segment _ _).symm
    _ ≤ μH[1] (S ∩ ball (0 : Euclid P) 1) := measure_mono hsub
/-- **Lemma T** (Simon, proof of A.4: limits of singular points are singular).  Let `F` satisfy
A.3c (`sing φ` closed) and A.3(3) (upper semicontinuity of `sing` under weak convergence).  If
`φ_k ∈ F` converge weakly to `ψ ∈ F`, `z_k ∈ B_1(0) ∩ sing φ_k` and `z_k → z`, then `z ∈ sing ψ`:
A.3(3) with `ε / 2` puts each `z_k` with `k` large within `ε / 2` of `sing ψ`, so `z` lies within
`ε` of `sing ψ` for every `ε > 0`, and `sing ψ` is closed. -/
theorem Submission.adr_sing_mem_of_tendsto : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ ψ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) → ∀ (zs : ℕ → Euclid P) (z : Euclid P), (∀ k, zs k ∈ ball (0 : Euclid P) 1 ∩ sing (φs k)) → Tendsto zs atTop (𝓝 z) → z ∈ sing ψ := by
  intro P n Q F sing hclosed husc ψ hψ φs hφs hweak zs z hzs hz
  rw [← (hclosed ψ hψ).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  -- A.3(3) with `ε / 2` puts `z_k` within `ε / 2` of `sing ψ` for `k ≥ k₀`
  obtain ⟨k₀, hk₀⟩ := husc ψ hψ φs hφs hweak (ε / 2) (half_pos hε)
  -- `z_k → z` puts `z_k` within `ε / 2` of `z` for `k ≥ k₁`
  obtain ⟨k₁, hk₁⟩ := Metric.tendsto_atTop.mp hz (ε / 2) (half_pos hε)
  obtain ⟨v, hv, hzv⟩ := hk₀ (max k₀ k₁) (le_max_left _ _) (hzs (max k₀ k₁))
  have hz' : dist z (zs (max k₀ k₁)) < ε / 2 := by
    rw [dist_comm]
    exact hk₁ (max k₀ k₁) (le_max_right _ _)
  exact ⟨v, hv, (dist_triangle z (zs (max k₀ k₁)) v).trans_lt
    ((add_lt_add hz' hzv).trans_eq (add_halves ε))⟩
/-- **Simon, proof of A.4** (the uses of A.3(2)): a closed `S ⊆ ℝᴾ` with `{x : y + λx ∈ S} = S`
whenever `y ∈ L`, `0 < λ < 1`, `|y| ≤ 1 − λ` satisfies `y + λz ∈ S ⇔ z ∈ S` for all `y ∈ L`,
`λ > 0`, and contains `L` if it is nonempty.  The admissible maps `z ↦ y + λz` give every
dilation `z ↦ cz` (`c > 1` by inverting `c⁻¹`), hence every short translation `z ↦ a + z`,
`|a| ≤ 1/2` (composing `z ↦ a + z/2` with `z ↦ 2z`), hence every translation along `L`
(conjugating a short one by a dilation); letting `λ ↓ 0` in `y + λz ∈ S` gives `y ∈ S̄ = S`. -/
theorem Submission.adr_affine_invariant_closed_set : ∀ (P : ℕ) (S : Set (Euclid P)) (L : Submodule ℝ (Euclid P)), IsClosed S → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => y + lam • x) ⁻¹' S = S) → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ z, y + lam • z ∈ S ↔ z ∈ S) ∧ (S.Nonempty → (L : Set (Euclid P)) ⊆ S) := by
  intro P S L hS hinv
  -- the hypothesis, pointwise
  have hG : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam →
      ∀ z, y + lam • z ∈ S ↔ z ∈ S := fun y hy lam h0 h1 hy' z =>
    Set.ext_iff.mp (hinv y hy lam h0 h1 hy') z
  -- every dilation `z ↦ c z`, `c > 0`
  have hD : ∀ c : ℝ, 0 < c → ∀ z : Euclid P, c • z ∈ S ↔ z ∈ S := by
    have hD0 : ∀ c : ℝ, 0 < c → c < 1 → ∀ z : Euclid P, c • z ∈ S ↔ z ∈ S := by
      intro c hc hc1 z
      have h := hG 0 L.zero_mem c hc hc1 (by rw [norm_zero]; linarith) z
      rwa [zero_add] at h
    intro c hc z
    rcases lt_trichotomy c 1 with hc1 | rfl | hc1
    · exact hD0 c hc hc1 z
    · rw [one_smul]
    · have h := hD0 c⁻¹ (inv_pos.mpr hc) (inv_lt_one_of_one_lt₀ hc1) (c • z)
      rw [inv_smul_smul₀ hc.ne'] at h
      exact h.symm
  -- short translations `z ↦ a + z`, `a ∈ L`, `‖a‖ ≤ 1/2`
  have hT0 : ∀ a ∈ L, ‖a‖ ≤ 1 / 2 → ∀ z : Euclid P, a + z ∈ S ↔ z ∈ S := by
    intro a ha ha' z
    have h := hG a ha (1 / 2) (by norm_num) (by norm_num) (by linarith) ((2 : ℝ) • z)
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h
    exact h.trans (hD 2 two_pos z)
  -- every translation along `L`: a short one conjugated by a dilation
  have hT : ∀ y ∈ L, ∀ z : Euclid P, y + z ∈ S ↔ z ∈ S := by
    intro y hy z
    have hc : (0 : ℝ) < (2 * ‖y‖ + 1)⁻¹ := by positivity
    have hcy : ‖(2 * ‖y‖ + 1)⁻¹ • y‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_of_nonneg hc.le, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      linarith
    rw [← hD _ hc (y + z), smul_add, hT0 _ (L.smul_mem _ hy) hcy, hD _ hc z]
  -- part (i)
  have hi : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ z, y + lam • z ∈ S ↔ z ∈ S :=
    fun y hy lam hlam z => (hT y hy (lam • z)).trans (hD lam hlam z)
  refine ⟨hi, ?_⟩
  -- part (ii): let `λ ↓ 0` in `y + λ z ∈ S`
  rintro ⟨z, hz⟩ y hy
  have hcont : Continuous fun lam : ℝ => y + lam • z := by fun_prop
  have hlim : Tendsto (fun lam : ℝ => y + lam • z) (𝓝[>] 0) (𝓝 y) :=
    (hcont.tendsto' 0 y (by simp)).mono_left nhdsWithin_le_nhds
  exact hS.mem_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun lam hlam => (hi y hy lam hlam z).mpr hz)
/-- **Simon, Remark A.5** (invariance forces a plane indicator).  If `ψ ∈ L¹_loc(μH[n])` on `ℝᴾ`
satisfies `ψ(y + λx) = ψ(x)` for all `y ∈ L`, `λ > 0`, where `dim L ≥ n`, then
`ψ = ψ(0) 1_{L'}` for an `n`-dimensional subspace `L'` (taken inside `L`).  Off `L'`, at `x ∉ L'`,
`ψ ≡ ψ(x)` on the image of a small closed ball around `(0, 1)` under the injective linear map
`L' × ℝ → ℝᴾ`, `(y, t) ↦ y + t x`; this compact piece of the `(n + 1)`-plane `L' + ℝx` has positive
`μH[n + 1]` measure, hence infinite `μH[n]` measure, so local integrability forces `ψ(x) = 0`. -/
theorem Submission.adr_invariant_eq_indicator : ∀ (P n Q : ℕ) (ψ : Euclid P → Euclid Q) (L : Submodule ℝ (Euclid P)), LocallyIntegrable ψ μH[(n : ℝ)] → n ≤ Module.finrank ℝ L → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → ∃ L' : Submodule ℝ (Euclid P), Module.finrank ℝ L' = n ∧ ψ = Set.indicator (L' : Set (Euclid P)) (fun _ => ψ 0) := by
  intro P n Q ψ L hψ hn hinv
  -- an `n`-dimensional subspace `L' ≤ L`
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hn
  have hb : LinearIndependent ℝ (L.subtype ∘ f) := hf.map' L.subtype L.ker_subtype
  obtain ⟨L', hL'⟩ : ∃ L' : Submodule ℝ (Euclid P), L' = Submodule.span ℝ (range (L.subtype ∘ f)) :=
    ⟨_, rfl⟩
  have hL'L : L' ≤ L := by
    rw [hL', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  have hL'rank : Module.finrank ℝ L' = n := by
    rw [hL', finrank_span_eq_card hb, Fintype.card_fin]
  refine ⟨L', hL'rank, ?_⟩
  funext v
  by_cases hv : v ∈ L'
  · rw [Set.indicator_of_mem hv]
    simpa using hinv v (hL'L hv) 1 one_pos 0
  · rw [Set.indicator_of_notMem hv]
    -- the injective linear map `g (y, t) = y + t • v` on `L' × ℝ`
    let g : (L' × ℝ) →ₗ[ℝ] Euclid P :=
      L'.subtype.coprod (LinearMap.toSpanSingleton ℝ (Euclid P) v)
    have hg : ∀ p : L' × ℝ, g p = (p.1 : Euclid P) + p.2 • v := fun p => rfl
    have hker : LinearMap.ker g = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨y, t⟩ h
      rw [hg] at h
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero, ZeroMemClass.coe_eq_zero] at h
        simp [h]
      · exfalso
        apply hv
        have h' : t • v = -(y : Euclid P) := eq_neg_of_add_eq_zero_right h
        have : v = t⁻¹ • -(y : Euclid P) := by rw [← h', inv_smul_smul₀ ht]
        rw [this]
        exact L'.smul_mem _ (L'.neg_mem y.2)
    obtain ⟨K, -, hK⟩ := g.exists_antilipschitzWith hker
    have hgc : Continuous g := g.continuous_of_finiteDimensional
    -- local integrability at `v`
    obtain ⟨s, hs, hint⟩ := hψ v
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
    have hg0 : g ((0 : L'), (1 : ℝ)) = v := by simp [hg]
    have hT : g ⁻¹' ball v r ∩ {p : L' × ℝ | 0 < p.2} ∈ 𝓝 ((0 : L'), (1 : ℝ)) := by
      refine Filter.inter_mem ?_ ?_
      · apply hgc.continuousAt.preimage_mem_nhds
        rw [hg0]
        exact ball_mem_nhds v hr
      · exact (isOpen_lt continuous_const continuous_snd).mem_nhds (by simp)
    obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
    have hUT : closedBall ((0 : L'), (1 : ℝ)) (ε / 2) ⊆ g ⁻¹' ball v r ∩ {p : L' × ℝ | 0 < p.2} :=
      (closedBall_subset_ball (by linarith)).trans hεT
    have hSc : IsCompact (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) :=
      (isCompact_closedBall _ _).image hgc
    have hSs : g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2) ⊆ s := by
      rintro _ ⟨p, hp, rfl⟩
      exact hrs (hUT hp).1
    have hSψ : EqOn ψ (fun _ => ψ v) (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) := by
      rintro _ ⟨p, hp, rfl⟩
      show ψ (g p) = ψ v
      rw [hg]
      exact hinv p.1 (hL'L p.1.2) p.2 (hUT hp).2 v
    -- the `(n + 1)`-dimensional piece has infinite `μH[n]` measure
    have hU_pos : 0 < μH[(Module.finrank ℝ (L' × ℝ) : ℝ)] (closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) :=
      Metric.measure_closedBall_pos _ _ (by linarith)
    have hrank : (Module.finrank ℝ (L' × ℝ) : ℝ) = (n : ℝ) + 1 := by
      rw [Module.finrank_prod, Module.finrank_self, hL'rank]
      push_cast
      ring
    rw [hrank] at hU_pos
    have hS_pos : μH[(n : ℝ) + 1] (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) ≠ 0 := by
      intro h0
      have := hK.le_hausdorffMeasure_image (d := (n : ℝ) + 1) (by positivity)
        (closedBall ((0 : L'), (1 : ℝ)) (ε / 2))
      rw [h0, mul_zero] at this
      exact hU_pos.ne' (nonpos_iff_eq_zero.mp this)
    have hS_top : μH[(n : ℝ)] (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) = ∞ :=
      (Measure.hausdorffMeasure_zero_or_top (lt_add_one (n : ℝ)) _).resolve_left hS_pos
    -- a nonzero constant is not integrable on a set of infinite measure
    have h1 : IntegrableOn (fun _ => ψ v) (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) μH[(n : ℝ)] :=
      (hint.mono_set hSs).congr_fun hSψ hSc.isClosed.measurableSet
    rw [integrableOn_const_iff] at h1
    rcases h1 with h1 | h1
    · simpa using h1
    · rw [hS_top] at h1
      exact absurd h1 (lt_irrefl _)
/-- **Affine change of variables for `μH[n]`-integrals** (Simon's rescalings
`φ_{x,λ}(z) = φ(x + λz)`, Appendix A).  For `c > 0` the map `x ↦ c • x` pushes `μH[n]` forward to
`c⁻ⁿ μH[n]` (Hausdorff scaling law) and `μH[n]` is translation invariant, so
`∫ h(y + c x) dμH[n](x) = c⁻ⁿ ∫ h dμH[n]` for every `h`; both sides vanish when `h` is not
integrable. -/
theorem Submission.adr_hausdorff_integral_comp_affine : ∀ (P n Q : ℕ) (h : Euclid P → Euclid Q) (y : Euclid P) (c : ℝ), 0 < c → ∫ x, h (y + c • x) ∂μH[(n : ℝ)] = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)] := by
  intro P n Q h y c hc
  -- `x ↦ c • x` is a homeomorphism, hence a measurable embedding
  have hemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- push-forward of `μH[n]` under `x ↦ c • x` (the homothety with centre `0` and ratio `c`)
  have hmap : Measure.map (fun x : Euclid P => c • x) μH[(n : ℝ)] =
      ‖c‖₊⁻¹ ^ (n : ℝ) • μH[(n : ℝ)] := by
    have := map_homothety_hausdorffMeasure (Nat.cast_nonneg n) (0 : Euclid P) hc.ne'
    convert this using 2
    funext x
    simp [AffineMap.homothety_apply]
  calc ∫ x, h (y + c • x) ∂μH[(n : ℝ)]
      = ∫ w, h (y + w) ∂(Measure.map (fun x : Euclid P => c • x) μH[(n : ℝ)]) :=
        (hemb.integral_map (fun w => h (y + w))).symm
    _ = (‖c‖₊⁻¹ ^ (n : ℝ)) • ∫ w, h (y + w) ∂μH[(n : ℝ)] := by
        rw [hmap, integral_smul_nnreal_measure]
    _ = (‖c‖₊⁻¹ ^ (n : ℝ)) • ∫ w, h w ∂μH[(n : ℝ)] := by
        rw [integral_add_left_eq_self]
    _ = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)] := by
        rw [NNReal.smul_def]
        congr 1
        simp [Real.norm_of_nonneg hc.le, inv_pow]
/-- **Uniform bound for weakly bounded sequences** (Simon, Appendix A: needed tacitly by the weak
limits `ψ_{y,1} = lim φ_{y+x,λⱼ}` in the proof of A.4, p. 228).  The bounded continuous functions
vanishing off the compact set `K` form a closed subspace `X` of `Euclid P →ᵇ ℝ`, hence a Banach
space.  On it, `Λₖ u = ∫ u • gₖ dμ` are continuous linear maps (`‖Λₖ u‖ ≤ (∫_K ‖gₖ‖ dμ) ‖u‖`),
pointwise bounded by hypothesis, so the uniform boundedness principle, proved here from the Baire
category theorem, gives `‖Λₖ‖ ≤ M` for all `k`. -/
theorem Submission.adr_uniform_bound_of_weak_bounded : ∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∃ C, ∀ k, ‖∫ x, f x • gs k x ∂μ‖ ≤ C) → IsCompact K → ∃ M, ∀ (k : ℕ) (h : Euclid P → ℝ) (C : ℝ), Continuous h → (∀ x ∉ K, h x = 0) → (∀ x, |h x| ≤ C) → ‖∫ x, h x • gs k x ∂μ‖ ≤ M * C := by
  intro P Q μ gs K hloc hbdd hK
  -- the subspace `X` of bounded continuous functions vanishing off `K`
  let X : Submodule ℝ (BoundedContinuousFunction (Euclid P) ℝ) :=
    { carrier := {u | ∀ x ∉ K, u x = 0}
      add_mem' := fun {u v} hu hv x hx => by simp [hu x hx, hv x hx]
      zero_mem' := fun x _ => rfl
      smul_mem' := fun c u hu x hx => by simp [hu x hx] }
  -- `X` is closed, hence complete
  have hXclosed : IsClosed (X : Set (BoundedContinuousFunction (Euclid P) ℝ)) := by
    change IsClosed {u : BoundedContinuousFunction (Euclid P) ℝ | ∀ x ∉ K, u x = 0}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe)
        continuous_const
  let _ : SeminormedAddCommGroup X := Submodule.seminormedAddCommGroup X
  let _ : NormedSpace ℝ X := Submodule.normedSpace X
  have : CompleteSpace X := hXclosed.completeSpace_coe
  -- every `u ∈ X` has compact support, so `u • gₖ` is integrable
  have hcs : ∀ u : X,
      HasCompactSupport ((u : BoundedContinuousFunction (Euclid P) ℝ) : Euclid P → ℝ) :=
    fun u => HasCompactSupport.intro hK u.2
  have hint : ∀ k (u : X),
      Integrable (fun x => (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x) μ :=
    fun k u => (hloc k).integrable_smul_left_of_hasCompactSupport
      (u : BoundedContinuousFunction (Euclid P) ℝ).continuous (hcs u)
  -- `‖Λₖ u‖ ≤ (∫_K ‖gₖ‖ dμ) ‖u‖`
  have hbound : ∀ k (u : X), ‖∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ‖ ≤
      (∫ x in K, ‖gs k x‖ ∂μ) * ‖u‖ := by
    intro k u
    have hgK : IntegrableOn (gs k) K μ := (hloc k).integrableOn_isCompact hK
    calc ‖∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ‖
        ≤ ∫ x, ‖(u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = ∫ x in K, ‖(u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x‖ ∂μ := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
          simp [u.2 x hx]
      _ ≤ ∫ x in K, ‖u‖ * ‖gs k x‖ ∂μ := by
          refine setIntegral_mono_on (hint k u).norm.integrableOn
            (hgK.norm.const_mul _) hK.measurableSet fun x _ => ?_
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right
            (BoundedContinuousFunction.norm_coe_le_norm
              (u : BoundedContinuousFunction (Euclid P) ℝ) x)
            (norm_nonneg _)
      _ = (∫ x in K, ‖gs k x‖ ∂μ) * ‖u‖ := by
          rw [integral_const_mul, mul_comm]
  -- the continuous linear maps `Λₖ : X → ℝ^Q`
  let L : ℕ → X →ₗ[ℝ] Euclid Q := fun k =>
    { toFun := fun u => ∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ
      map_add' := fun u v => by
        simp only [Submodule.coe_add, BoundedContinuousFunction.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint k u) (hint k v)
      map_smul' := fun c u => by
        simp only [SetLike.val_smul, BoundedContinuousFunction.coe_smul, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact integral_smul c _ }
  let Λ : ℕ → X →L[ℝ] Euclid Q := fun k =>
    LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := X) (F := Euclid Q) (L k)
      (∫ x in K, ‖gs k x‖ ∂μ) (hbound k)
  -- pointwise boundedness: the hypothesis applied to `u ∈ X`
  have hpt : ∀ u : X, ∃ C, ∀ k, ‖Λ k u‖ ≤ C := fun u => by
    obtain ⟨C, hC⟩ := hbdd _ (u : BoundedContinuousFunction (Euclid P) ℝ).continuous (hcs u)
    exact ⟨C, fun k => hC k⟩
  -- uniform boundedness principle (Banach–Steinhaus) from the Baire category theorem
  obtain ⟨M', hM'⟩ : ∃ M', ∀ k, ‖Λ k‖ ≤ M' := by
    let e : ℕ → Set X := fun n => ⋂ k : ℕ, {u : X | ‖Λ k u‖ ≤ n}
    have hc : ∀ n, IsClosed (e n) := fun n =>
      isClosed_iInter fun k => isClosed_le (Λ k).continuous.norm continuous_const
    have hU : ⋃ n, e n = univ := by
      refine eq_univ_of_forall fun u => ?_
      obtain ⟨C, hC⟩ := hpt u
      obtain ⟨m, hm⟩ := exists_nat_ge C
      exact mem_iUnion.2 ⟨m, mem_iInter.2 fun k => (hC k).trans hm⟩
    obtain ⟨m, u₀, hu₀⟩ := nonempty_interior_of_iUnion_of_closed hc hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u₀ hu₀
    have hm : ∀ v ∈ Metric.ball u₀ ε, ∀ k, ‖Λ k v‖ ≤ m := fun v hv k =>
      mem_iInter.1 (interior_subset (hball hv)) k
    refine ⟨(m + m : ℝ) / (ε / 2), fun k =>
      ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hε (by positivity) (by norm_num)
        fun v hv1 _ => ?_⟩
    have hv1' : ε / 2 ≤ ‖v‖ := by simpa using hv1
    calc ‖Λ k v‖ = ‖Λ k (v + u₀) - Λ k u₀‖ := by rw [map_add, add_sub_cancel_right]
      _ ≤ ‖Λ k (v + u₀)‖ + ‖Λ k u₀‖ := norm_sub_le _ _
      _ ≤ m + m := add_le_add
          (hm _ (by rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]) k)
          (hm _ (Metric.mem_ball_self hε) k)
      _ ≤ (m + m : ℝ) / (ε / 2) * ‖v‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hv1' (by positivity)
  -- conclusion with `M = max M' 0`: a continuous `h` vanishing off `K` with `|h| ≤ C` is an
  -- element of `X` of norm `≤ C`
  refine ⟨max M' 0, fun k h C hcont hK0 hC => ?_⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  let hb : BoundedContinuousFunction (Euclid P) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨h, hcont⟩ (2 * C) (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      calc |h x - h y| ≤ |h x| + |h y| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC x, hC y])
  have hbX : hb ∈ X := fun x hx => hK0 x hx
  have hnorm : ‖(⟨hb, hbX⟩ : X)‖ ≤ C := by
    change ‖hb‖ ≤ C
    exact (BoundedContinuousFunction.norm_le hC0).2 fun x => by simpa [hb] using hC x
  calc ‖∫ x, h x • gs k x ∂μ‖ = ‖Λ k ⟨hb, hbX⟩‖ := rfl
    _ ≤ M' * ‖(⟨hb, hbX⟩ : X)‖ := (Λ k).le_of_opNorm_le (hM' k) _
    _ ≤ max M' 0 * C := mul_le_mul (le_max_left _ _) hnorm (norm_nonneg _) (le_max_right _ _)

/-- **Weak convergence against moving test functions** (Simon, Appendix A: "all limits in the
weak sense", the limits `ψ_{y,1} = lim φ_{y+x,λⱼ}` in the proof of A.4, p. 228).  If
`∫ f • gₖ dμ → ∫ f • g dμ` for every continuous compactly supported `f`, and continuous `hₖ → h`
uniformly, with `h` and eventually every `hₖ` vanishing off a fixed compact `K`, then
`∫ hₖ • gₖ dμ → ∫ h • g dμ`: by `Submission.adr_uniform_bound_of_weak_bounded`,
`‖∫ (hₖ - h) • gₖ dμ‖ ≤ M ‖hₖ - h‖_∞ → 0`, and `∫ h • gₖ dμ → ∫ h • g dμ` by hypothesis. -/
theorem Submission.adr_weak_tendsto_of_tendstoUniformly : ∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μ) atTop (𝓝 (∫ x, f x • g x ∂μ))) → IsCompact K → (∀ k, Continuous (hs k)) → Continuous h → (∀ᶠ k in atTop, ∀ x ∉ K, hs k x = 0) → (∀ x ∉ K, h x = 0) → TendstoUniformly hs h atTop → Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ) atTop (𝓝 (∫ x, h x • g x ∂μ)) := by
  intro P Q μ gs g hs h K hloc hweak hK hcont hc hsK hK0 hunif
  -- convergent sequences are bounded, so the uniform bound applies on `K`
  obtain ⟨M, hM⟩ := Submission.adr_uniform_bound_of_weak_bounded P Q μ gs K hloc
    (fun f hf hfc => by
      obtain ⟨C, hC⟩ :=
        isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hweak f hf hfc))
      exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩) hK
  -- `h` vanishes off the compact `K`, so it is an admissible test function
  have hhc : HasCompactSupport h := HasCompactSupport.intro hK hK0
  -- `∫ hₖ • gₖ dμ - ∫ h • gₖ dμ = ∫ (hₖ - h) • gₖ dμ → 0`
  have hdiff : Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ - ∫ x, h x • gs k x ∂μ) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hδ : 0 < ε / (2 * (|M| + 1)) := by positivity
    filter_upwards [hsK, Metric.tendstoUniformly_iff.1 hunif _ hδ] with k hk0 hk1
    rw [dist_zero_right, ← integral_sub
      ((hloc k).integrable_smul_left_of_hasCompactSupport (hcont k) (HasCompactSupport.intro hK hk0))
      ((hloc k).integrable_smul_left_of_hasCompactSupport hc hhc)]
    simp_rw [← sub_smul]
    calc ‖∫ x, (hs k x - h x) • gs k x ∂μ‖ ≤ M * (ε / (2 * (|M| + 1))) :=
          hM k (fun x => hs k x - h x) _ ((hcont k).sub hc)
            (fun x hx => by simp [hk0 x hx, hK0 x hx])
            (fun x => by simpa [Real.dist_eq, abs_sub_comm] using (hk1 x).le)
      _ ≤ |M| * (ε / (2 * (|M| + 1))) := mul_le_mul_of_nonneg_right (le_abs_self M) hδ.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [mul_nonneg (abs_nonneg M) hε.le]
  simpa using hdiff.add (hweak h hc hhc)
/-- **Rescaled translates converge uniformly** (Simon, Appendix A, the weak limits
`ψ = lim φ_{x+λⱼβx,λⱼ}`; step 3 of the proof of `adr_weak_tendsto_comp_affine`).  If `f` is
continuous with compact support and `c_k → 1`, then `f(c_k⁻¹(w − y)) → f(w − y)` uniformly in `w`,
and `f(· − y)` and, for large `k`, `f(c_k⁻¹(· − y))` vanish off one compact ball `K = B̄_{2R}(y)`,
where `R ≥ 1` and `f = 0` off `B̄_R(0)`.  No sign of `c_k` is assumed: eventually `1/2 < c_k < 2`. -/
theorem Submission.adr_rescaled_translate_tendstoUniformly : ∀ (P : ℕ) (f : Euclid P → ℝ) (y : Euclid P) (mus : ℕ → ℝ), Continuous f → HasCompactSupport f → Tendsto mus atTop (𝓝 1) → ∃ K : Set (Euclid P), IsCompact K ∧ (∀ w ∉ K, f (w - y) = 0) ∧ (∀ᶠ k in atTop, ∀ w ∉ K, f ((mus k)⁻¹ • (w - y)) = 0) ∧ TendstoUniformly (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) atTop := by
  intro P f y mus hf hfc hmus
  -- step 1: `tsupport f ⊆ B̄_{R₀}(0)`; with `R := max R₀ 1 ≥ 1`, `f x = 0` whenever `‖x‖ > R`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hzero : ∀ x : Euclid P, R < ‖x‖ → f x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
    have h := hR₀ hxs
    rw [mem_closedBall_zero_iff] at h
    linarith [le_max_left R₀ 1]
  have h2R : 0 < 2 * R := by linarith
  -- step 2: `K := B̄_{2R}(y)`; `f (w - y) = 0` off `K`
  have hK : ∀ w ∉ closedBall y (2 * R), f (w - y) = 0 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    exact hzero _ (by linarith)
  -- step 3: eventually `1 / 2 < c_k < 2`, so `‖c_k⁻¹ (w - y)‖ > 2R / 2 = R` and
  -- `f (c_k⁻¹ (w - y)) = 0` off `K`
  have hKk : ∀ᶠ k in atTop, ∀ w ∉ closedBall y (2 * R), f ((mus k)⁻¹ • (w - y)) = 0 := by
    filter_upwards [hmus (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))] with k hk w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    have hpos : 0 < mus k := by linarith [hk.1]
    apply hzero
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith [hk.2]
  refine ⟨closedBall y (2 * R), isCompact_closedBall y (2 * R), hK, hKk, ?_⟩
  -- step 4: `f` is uniformly continuous; on `K` the argument moves by
  -- `|1 - c_k⁻¹| ‖w - y‖ ≤ |c_k⁻¹ - 1| 2R → 0`, and off `K` both values vanish
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf) ε hε
  have hinv : Tendsto (fun k => (mus k)⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hmus.inv₀ one_ne_zero
  filter_upwards [hKk, Metric.tendsto_nhds.mp hinv (δ / (2 * R)) (div_pos hδ h2R)]
    with k hk hk' w
  show dist (f (w - y)) (f ((mus k)⁻¹ • (w - y))) < ε
  by_cases hw : w ∈ closedBall y (2 * R)
  · apply hfδ
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [Real.dist_eq, abs_sub_comm] at hk'
    have hsub : (w - y) - (mus k)⁻¹ • (w - y) = (1 - (mus k)⁻¹) • (w - y) := by
      rw [sub_smul, one_smul]
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |1 - (mus k)⁻¹| * ‖w - y‖ ≤ |1 - (mus k)⁻¹| * (2 * R) :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ < δ / (2 * R) * (2 * R) := mul_lt_mul_of_pos_right hk' h2R
      _ = δ := div_mul_cancel₀ δ h2R.ne'
  · rw [hK w hw, hk w hw, dist_self]
    exact hε

/-- **Simon, proof of A.4 (chapter-A.txt lines 125–133): weak limits of rescalings.**  If
`gₖ ⇀ g` in the weak sense of Appendix A (lines 13–15: tested against `C⁰_c(ℝᴾ)`), each `gₖ`
locally `μH[n]`-integrable, and `cₖ > 0`, `cₖ → 1`, then `gₖ(y + cₖ ·) ⇀ g(y + ·)`.  The change of
variables `w = y + cₖ x` (`adr_hausdorff_integral_comp_affine`) gives
`∫ f(x) gₖ(y + cₖ x) dμ = (cₖⁿ)⁻¹ ∫ fₖ gₖ dμ` with `fₖ = f(cₖ⁻¹ • (· - y))`.  The `fₖ` converge
uniformly to `f(· - y)` with supports eventually in a fixed compact set
(`adr_rescaled_translate_tendstoUniformly`), so the Banach–Steinhaus bound behind
`adr_weak_tendsto_of_tendstoUniformly` gives `∫ fₖ gₖ dμ → ∫ f(· - y) g dμ`. -/
theorem Submission.adr_weak_tendsto_comp_affine : ∀ (P n Q : ℕ) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (y : Euclid P) (mus : ℕ → ℝ), (∀ k, LocallyIntegrable (gs k) μH[(n : ℝ)]) → (∀ k, 0 < mus k) → Tendsto mus atTop (𝓝 1) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g x ∂μH[(n : ℝ)]))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g (y + x) ∂μH[(n : ℝ)])) := by
  intro P n Q gs g y mus hloc hpos hmus hweak f hf hfc
  -- `fₖ = f (cₖ⁻¹ • (· - y)) → f (· - y)` uniformly, all eventually vanishing off a compact `K`
  obtain ⟨K, hK, h0, hk0, hunif⟩ :=
    Submission.adr_rescaled_translate_tendstoUniformly P f y mus hf hfc hmus
  -- change of variables `w = y + cₖ • x`, and `w = y + x` in the limit
  have hL : ∀ k, ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)] =
      ((mus k) ^ n)⁻¹ • ∫ w, f ((mus k)⁻¹ • (w - y)) • gs k w ∂μH[(n : ℝ)] := by
    intro k
    rw [← Submission.adr_hausdorff_integral_comp_affine P n Q
      (fun w => f ((mus k)⁻¹ • (w - y)) • gs k w) y (mus k) (hpos k)]
    simp only [add_sub_cancel_left, inv_smul_smul₀ (hpos k).ne']
  have hR : ∫ x, f x • g (y + x) ∂μH[(n : ℝ)] = ∫ w, f (w - y) • g w ∂μH[(n : ℝ)] := by
    simpa only [one_smul, add_sub_cancel_left, one_pow, inv_one] using
      Submission.adr_hausdorff_integral_comp_affine P n Q (fun w => f (w - y) • g w) y 1 one_pos
  -- weak convergence against the moving test functions `fₖ`
  have hmain := Submission.adr_weak_tendsto_of_tendstoUniformly P Q μH[(n : ℝ)] gs g
    (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) K hloc hweak hK
    (fun k => by fun_prop) (by fun_prop) hk0 h0 hunif
  -- the Jacobian factors `(cₖⁿ)⁻¹ → 1`
  have hc : Tendsto (fun k => ((mus k) ^ n)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, inv_one] using (hmus.pow n).inv₀ (pow_ne_zero n one_ne_zero)
  have hlim := hc.smul hmain
  rw [one_smul] at hlim
  rw [hR]
  exact hlim.congr fun k => (hL k).symm

/-- **Simon, proof of A.4, Lemma I** (chapter-A.txt lines 125–134: `ψ_{y,1} = ψ` for `y ∈ S` and
`ψ_{βx,1} = ψ` for `β ∈ ℝ`).  If `φ ∈ F` is invariant under the subspace `S` and its blow-ups
`φ_{x,λₖ} ∈ F` converge weakly to a homogeneous `ψ ∈ F`, then `ψ` is invariant under `S + ℝx`.
Weak limits in `F` are unique (fundamental lemma and (H0)), every translate `ψ(w + ·)` lies in `F`
((A.1) with `θ = 1/(2 + |w|)` and homogeneity), and `ψ(w + ·) = ψ` as soon as
`φ_{x,λₖ}(w + ·) = φ_{x,λₖ}(cₖ ·)` for large `k`, with `cₖ > 0`, `cₖ → 1`
(`adr_weak_tendsto_comp_affine` twice).  This holds for `w ∈ S` with `cₖ = 1`, and for `w = βx`
with `cₖ = 1/(1 + βλₖ)` by the homogeneity of `φ`. -/
theorem Submission.adr_tangent_invariance : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → ∀ φ ∈ F, ∀ S : Submodule ℝ (Euclid P), (∀ y ∈ S, ∀ lam : ℝ, 0 < lam → ∀ x, φ (y + lam • x) = φ x) → ∀ (x : Euclid P) (lams : ℕ → ℝ) (ψ : Euclid P → Euclid Q), (∀ k, 0 < lams k) → Tendsto lams atTop (𝓝 0) → (∀ k, (fun z => φ (x + lams k • z)) ∈ F) → ψ ∈ F → (∀ lam : ℝ, 0 < lam → ∀ z, ψ (lam • z) = ψ z) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z, f z • φ (x + lams k • z) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ z, f z • ψ z ∂μH[(n : ℝ)]))) → ∀ y ∈ S ⊔ Submodule.span ℝ {x}, ∀ lam : ℝ, 0 < lam → ∀ z, ψ (y + lam • z) = ψ z := by
  intro P n Q F H0 H1 A1 φ hφ S hS x lams ψ hlams_pos hlams hFk hψ hψhom hconv
  -- weak limits in `F` are unique
  have uniq : ∀ g ∈ F, (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f →
      ∫ z, f z • g z ∂μH[(n : ℝ)] = ∫ z, f z • ψ z ∂μH[(n : ℝ)]) → g = ψ := by
    intro g hg hint
    exact H0 g hg ψ hψ (ae_eq_of_integral_contDiff_smul_eq (H1 g hg) (H1 ψ hψ)
      fun f hf hfs => hint f hf.continuous hfs)
  -- every translate `ψ (w + ·) = ψ (θ • w + θ • ·)`, `θ = 1 / (2 + ‖w‖)`, lies in `F` by (A.1)
  have transl : ∀ w : Euclid P, (fun z => ψ (w + z)) ∈ F := by
    intro w
    have h2 : 0 < 2 + ‖w‖ := by positivity
    set θ : ℝ := 1 / (2 + ‖w‖) with hθ
    have hθpos : 0 < θ := by positivity
    have hθlt : θ < 1 := by
      rw [hθ, div_lt_one h2]
      linarith [norm_nonneg w]
    have hθw : ‖θ • w‖ ≤ 1 - θ := by
      rw [norm_smul, Real.norm_of_nonneg hθpos.le, hθ, div_mul_eq_mul_div, one_mul,
        div_le_iff₀ h2, sub_mul, div_mul_cancel₀ _ h2.ne']
      linarith
    convert A1 ψ hψ (θ • w) θ hθpos hθlt hθw using 1
    funext z
    rw [← smul_add, hψhom θ hθpos]
  -- if `φ (x + λₖ • (w + ·)) = φ (x + λₖ • (cₖ • ·))` for large `k`, `cₖ → 1`, then `ψ (w + ·) = ψ`
  have key : ∀ (w : Euclid P) (c : ℕ → ℝ), (∀ k, 0 < c k) → Tendsto c atTop (𝓝 1) →
      (∀ᶠ k in atTop, ∀ z, φ (x + lams k • (w + z)) = φ (x + lams k • (c k • z))) →
      ∀ z, ψ (w + z) = ψ z := by
    intro w c hcpos hc hev
    have hloc : ∀ k, LocallyIntegrable (fun z => φ (x + lams k • z)) μH[(n : ℝ)] :=
      fun k => H1 _ (hFk k)
    have hint : ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f →
        ∫ z, f z • ψ (w + z) ∂μH[(n : ℝ)] = ∫ z, f z • ψ z ∂μH[(n : ℝ)] := by
      intro f hf hfs
      have h1 := Submission.adr_weak_tendsto_comp_affine P n Q (fun k z => φ (x + lams k • z)) ψ
        w (fun _ => 1) hloc (fun _ => one_pos) tendsto_const_nhds hconv f hf hfs
      have h2 := Submission.adr_weak_tendsto_comp_affine P n Q (fun k z => φ (x + lams k • z)) ψ
        0 c hloc hcpos hc hconv f hf hfs
      simp only [one_smul, zero_add] at h1 h2
      refine tendsto_nhds_unique (h1.congr' ?_) h2
      filter_upwards [hev] with k hk
      simp only [hk]
    exact congrFun (uniq _ (transl w) hint)
  -- translations in `S`: `φ (x + λₖ • (s + z)) = φ (λₖ • s + 1 • (x + λₖ • z))`
  have hSinv : ∀ s ∈ S, ∀ z, ψ (s + z) = ψ z := by
    intro s hs
    refine key s (fun _ => 1) (fun _ => one_pos) tendsto_const_nhds
      (Eventually.of_forall fun k z => ?_)
    have := hS (lams k • s) (S.smul_mem _ hs) 1 one_pos (x + lams k • z)
    rw [one_smul] at this ⊢
    rw [← this]
    congr 1
    module
  -- translations along `x`: `φ (x + λₖ • (β • x + z)) = φ (aₖ • (x + λₖ • (aₖ⁻¹ • z)))`,
  -- `aₖ = 1 + β λₖ > 0` for large `k`
  have hxinv : ∀ β : ℝ, ∀ z, ψ (β • x + z) = ψ z := by
    intro β
    have ha : Tendsto (fun k => 1 + β * lams k) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hlams.const_mul β)
    have hev : ∀ᶠ k in atTop, 0 < 1 + β * lams k := ha.eventually (eventually_gt_nhds one_pos)
    let c : ℕ → ℝ := fun k => if 0 < 1 + β * lams k then (1 + β * lams k)⁻¹ else 1
    have hc : ∀ᶠ k in atTop, c k = (1 + β * lams k)⁻¹ := by
      filter_upwards [hev] with k hk
      simp only [c, hk, ite_true]
    refine key (β • x) c (fun k => ?_) ?_ ?_
    · by_cases h : 0 < 1 + β * lams k
      · simp only [c, h, ite_true]
        positivity
      · simp only [c, h, ite_false]
        exact one_pos
    · refine (tendsto_congr' hc).2 ?_
      simpa using ha.inv₀ one_ne_zero
    · filter_upwards [hev, hc] with k hk hck z
      rw [hck]
      have := hS 0 S.zero_mem (1 + β * lams k) hk (x + lams k • ((1 + β * lams k)⁻¹ • z))
      rw [zero_add] at this
      rw [← this]
      congr 1
      rw [smul_add (1 + β * lams k), smul_comm (1 + β * lams k) (lams k),
        smul_inv_smul₀ hk.ne']
      module
  intro y hy lam hlam z
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp ht
  rw [add_assoc, hSinv s hs, hxinv β, hψhom lam hlam]
/-- **Simon A.4** (proof of (1), the radii `λₖ ↓ 0`): if every `δ > 0` admits some `ρ ∈ (0, δ)`
with `Q ρ`, then there are `ρₖ ∈ (0, δ₀)` with `Q ρₖ`, strictly decreasing to `0`.  Choose
`g(δ) ∈ (0, δ)` with `Q (g δ)` for each `δ > 0` and set `ρ₀ = g(δ₀)`,
`ρₖ₊₁ = g(min ρₖ (1/(k+1)))`; then `0 < ρₖ₊₁ < min ρₖ (1/(k+1))`. -/
theorem Submission.adr_exists_strictAnti_radii : ∀ (Q : ℝ → Prop) (δ₀ : ℝ), 0 < δ₀ → (∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q ρ) → ∃ ρs : ℕ → ℝ, (∀ k, 0 < ρs k) ∧ (∀ k, ρs k < δ₀) ∧ StrictAnti ρs ∧ Tendsto ρs atTop (𝓝 0) ∧ ∀ k, Q (ρs k) := by
  intro Q δ₀ hδ₀ hQ
  -- `g δ ∈ (0, δ)` with `Q (g δ)` for every `δ > 0`
  choose! g hg0 hgδ hgQ using hQ
  -- `ρ₀ = g δ₀`, `ρₖ₊₁ = g (min ρₖ (1/(k+1)))`
  let ρs : ℕ → ℝ := fun k =>
    Nat.rec (motive := fun _ => ℝ) (g δ₀) (fun k ρ => g (min ρ (1 / ((k : ℝ) + 1)))) k
  have hsucc : ∀ k, ρs (k + 1) = g (min (ρs k) (1 / ((k : ℝ) + 1))) := fun _ => rfl
  have hpos : ∀ k, 0 < ρs k := by
    intro k
    induction k with
    | zero => exact hg0 δ₀ hδ₀
    | succ k ih =>
      rw [hsucc]
      exact hg0 _ (lt_min ih Nat.one_div_pos_of_nat)
  have hmin : ∀ k, 0 < min (ρs k) (1 / ((k : ℝ) + 1)) := fun k =>
    lt_min (hpos k) Nat.one_div_pos_of_nat
  have hlt : ∀ k, ρs (k + 1) < min (ρs k) (1 / ((k : ℝ) + 1)) := fun k => by
    rw [hsucc]
    exact hgδ _ (hmin k)
  have hanti : StrictAnti ρs :=
    strictAnti_nat_of_succ_lt fun k => (hlt k).trans_le (min_le_left _ _)
  refine ⟨ρs, hpos, fun k => (hanti.antitone k.zero_le).trans_lt (hgδ δ₀ hδ₀), hanti, ?_, ?_⟩
  · -- squeeze `0 < ρₖ₊₁ < 1/(k+1)`
    refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (hpos (k + 1)).le)
      fun k => ((hlt k).trans_le (min_le_right _ _)).le)
  · intro k
    cases k with
    | zero => exact hgQ δ₀ hδ₀
    | succ k =>
      rw [hsucc]
      exact hgQ _ (hmin k)
/-- **An `H^ℓ`-null set has open covers of arbitrarily small `ℓ`-dimensional cost**: the open
balls covering `sing ψ` with `∑ⱼ ω_ℓ ρⱼ^ℓ < ε` in the proof of Simon A.4 (chapter-A.txt
lines 88–97), with thickenings in place of balls.  The scale-`1` term of `hausdorffMeasure_apply`
gives a cover `E ⊆ ⋃ₙ tₙ` with `diam tₙ ≤ 1` and `∑ₙ c(tₙ) < ε / 2`, where `c(t) = (diam t)^ℓ`
for `t ≠ ∅` and `c(∅) = 0`.  With slack `δₙ > 0`, `∑ₙ δₙ < ε / 2`, each `tₙ` is replaced by its
open `rₙ`-thickening, `rₙ > 0` so small that `(diam tₙ + 2rₙ)^ℓ < (diam tₙ)^ℓ + δₙ`. -/
theorem Submission.adr_null_open_cover : ∀ (P : ℕ) (ℓ : ℝ) (E : Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → μH[ℓ] E = 0 → 0 < ε → ∃ U : ℕ → Set (Euclid P), (∀ j, IsOpen (U j)) ∧ E ⊆ ⋃ j, U j ∧ ∑' j, Metric.ediam (U j) ^ ℓ < ε := by
  intro P ℓ E ε hℓ hE hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- the scale-`1` term of the formula for `μH[ℓ] E = 0` gives a cheap cover `t`
  obtain ⟨t, hEt, ht1, ht⟩ : ∃ t : ℕ → Set (Euclid P), E ⊆ ⋃ n, t n ∧
      (∀ n, ediam (t n) ≤ 1) ∧ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ < ε / 2 := by
    have h1 : (⨅ (t : ℕ → Set (Euclid P)) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ 1),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) < ε / 2 := by
      refine lt_of_le_of_lt ?_ hε2
      rw [← hE, Measure.hausdorffMeasure_apply]
      exact le_iSup₂_of_le (1 : ℝ≥0∞) one_pos le_rfl
    simpa only [iInf_lt_iff, exists_prop] using h1
  -- slack `δₙ > 0` with `∑ₙ δₙ < ε / 2`
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε2.ne' ℕ
  -- radii `rₙ > 0` with `(diam tₙ + 2rₙ)^ℓ < (diam tₙ)^ℓ + δₙ`, by continuity at `0`
  have hr : ∀ n, ∃ r : NNReal, 0 < r ∧
      (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ < ediam (t n) ^ ℓ + δ n := by
    intro n
    have hcont : Continuous fun r : NNReal => (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ := by
      fun_prop (disch := norm_num)
    have hfin : ediam (t n) ^ ℓ ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hℓ.le ((ht1 n).trans_lt ENNReal.one_lt_top).ne
    have hev : ∀ᶠ r : NNReal in 𝓝 0,
        (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ < ediam (t n) ^ ℓ + δ n :=
      (isOpen_lt hcont continuous_const).mem_nhds
        (by simpa using ENNReal.lt_add_right hfin (hδ n).ne')
    exact (Filter.Eventually.and self_mem_nhdsWithin
      (hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ r : NNReal in 𝓝[>] 0, 0 < r ∧ _).exists
  choose r hr0 hr using hr
  -- `Uₙ` is the open `rₙ`-thickening of `tₙ`; `diam Uₙ ≤ diam tₙ + 2rₙ`
  refine ⟨fun n => thickening (r n) (t n), fun n => isOpen_thickening, ?_, ?_⟩
  · exact hEt.trans (iUnion_mono fun n => self_subset_thickening (NNReal.coe_pos.mpr (hr0 n)) _)
  calc ∑' n, ediam (thickening (r n) (t n)) ^ ℓ
      ≤ ∑' n, ((⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) + δ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rcases (t n).eq_empty_or_nonempty with h | h
        · simp [h, ENNReal.zero_rpow_of_pos hℓ]
        · rw [iSup_pos h]
          exact (ENNReal.rpow_le_rpow (ediam_thickening_le (r n)) hℓ.le).trans (hr n).le
    _ = ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) + ∑' n, δ n := ENNReal.tsum_add
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add ht hδsum
    _ = ε := ENNReal.add_halves ε

/-- **A small-cost cover of a null closed set eventually covers nearby sets in `B_{1/2}(0)`**:
Simon's "`K ≡ B̄₁(0) \ ∪ⱼ B_{ρⱼ}(xⱼ)` is a compact set with positive distance from `sing ψ`.
Hence by assumption A.3(3) we have `sing φ_{x,λₖ'} ∩ B₁(0) ⊆ ∪ⱼ B_{ρⱼ}(xⱼ)` for all sufficiently
large `k`" in the proof of A.4 (chapter-A.txt lines 97–101), for `S ∩ B̄_{1/2}(0)` only.
`adr_null_open_cover` covers the null set `E = S ∩ B̄_{1/2}(0)` by open `Uⱼ`.  The compact
`K = B̄_{1/2}(0) \ ⋃ⱼ Uⱼ` misses the closed `S`, so some thickening `thickening η K` misses `S`;
the hypothesis at this `η` puts `B_{1/2}(0) ∩ Tₖ` (`k ≥ k₀`) within `η` of `S`, hence off `K`. -/
theorem Submission.adr_eventually_subset_small_cover : ∀ (P : ℕ) (ℓ : ℝ) (S : Set (Euclid P)) (Ts : ℕ → Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → IsClosed S → μH[ℓ] (S ∩ ball (0 : Euclid P) 1) = 0 → 0 < ε → (∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ Ts k ⊆ {x | ∃ z ∈ S, dist x z < η}) → ∃ (U : ℕ → Set (Euclid P)) (k₀ : ℕ), ∑' j, Metric.ediam (U j) ^ ℓ < ε ∧ ∀ k ≥ k₀, ball (0 : Euclid P) (1 / 2) ∩ Ts k ⊆ ⋃ j, U j := by
  intro P ℓ S Ts ε hℓ hS hS1 hε hT
  -- `E = S ∩ B̄_{1/2}(0) ⊆ S ∩ B₁(0)` is `μH[ℓ]`-null, so it has an open cover of cost `< ε`
  have hE : μH[ℓ] (S ∩ closedBall (0 : Euclid P) (1 / 2)) = 0 :=
    measure_mono_null (inter_subset_inter_right S (closedBall_subset_ball (by norm_num))) hS1
  obtain ⟨U, hUo, hEU, hU⟩ := Submission.adr_null_open_cover P ℓ _ ε hℓ hE hε
  -- `K = B̄_{1/2}(0) \ ⋃ⱼ Uⱼ` is compact and misses the closed set `S`
  have hK : IsCompact (closedBall (0 : Euclid P) (1 / 2) \ ⋃ j, U j) :=
    (isCompact_closedBall _ _).diff (isOpen_iUnion hUo)
  have hKS : closedBall (0 : Euclid P) (1 / 2) \ ⋃ j, U j ⊆ Sᶜ := fun w hw hwS =>
    hw.2 (hEU ⟨hwS, hw.1⟩)
  -- a uniform gap: `thickening η K` misses `S`
  obtain ⟨η, hη, hηK⟩ := hK.exists_thickening_subset_open hS.isOpen_compl hKS
  obtain ⟨k₀, hk₀⟩ := hT η hη
  refine ⟨U, k₀, hU, fun k hk w hw => ?_⟩
  by_contra hwU
  obtain ⟨z, hzS, hwz⟩ := hk₀ k hk ⟨ball_subset_ball (by norm_num) hw.1, hw.2⟩
  exact hηK (mem_thickening_iff.mpr ⟨w, ⟨ball_subset_closedBall hw.1, hwU⟩, by rwa [dist_comm]⟩)
    hzS
/-- **Simon A.4** (proof of (1), the rescaling step, with blow-up scale `λ = 2ρ`): if every cover
`{Cⱼ}` of `A ∩ B_ρ(x)` has `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` and the `Uⱼ` cover every `z` with `|z| < 1/2`
and `x + 2ρz ∈ A`, then `Σⱼ (diam Uⱼ)^ℓ ≥ 2^{−ℓ}/8`.  The sets `Cⱼ = x + 2ρ·Uⱼ` cover
`A ∩ B_ρ(x)` and have `diam Cⱼ = 2ρ diam Uⱼ`, so a smaller sum would give
`ρ^ℓ ≤ 2·2^ℓρ^ℓ Σⱼ (diam Uⱼ)^ℓ < ρ^ℓ/4`. -/
theorem Submission.adr_rescaled_content_lower_bound : ∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)) (x : Euclid P) (ρ : ℝ) (U : ℕ → Set (Euclid P)), 0 < ℓ → 0 < ρ → (∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ) → (∀ z : Euclid P, x + (2 * ρ) • z ∈ A → ‖z‖ < 1 / 2 → z ∈ ⋃ j, U j) → (2 : ℝ≥0∞) ^ (-ℓ) / 8 ≤ ∑' j, Metric.ediam (U j) ^ ℓ := by
  intro P ℓ A x ρ U hℓ hρ hD hU
  have hlam : 0 < 2 * ρ := by positivity
  -- `Cⱼ = g(Uⱼ)` with `g(z) = x + 2ρz` cover `A ∩ B_ρ(x)`: `w = g(z)` for `z = (2ρ)⁻¹(w − x)`,
  -- and `|z| = |w − x|/(2ρ) < 1/2`
  have hcover : A ∩ ball x ρ ⊆ ⋃ j, (fun z => x + (2 * ρ) • z) '' U j := by
    rintro w ⟨hwA, hwB⟩
    have hgz : x + (2 * ρ) • ((2 * ρ)⁻¹ • (w - x)) = w := by
      rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
    have hzn : ‖(2 * ρ)⁻¹ • (w - x)‖ < 1 / 2 := by
      rw [mem_ball, dist_eq_norm] at hwB
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hlam.le, inv_mul_lt_iff₀ hlam]
      linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hU _ (by rw [hgz]; exact hwA) hzn)
    exact mem_iUnion.mpr ⟨j, _, hj, hgz⟩
  -- `diam Cⱼ = 2ρ diam Uⱼ`: `g` is the dilation by `2ρ` followed by a translation
  have hdiam : ∀ j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) =
      ENNReal.ofReal (2 * ρ) * Metric.ediam (U j) := by
    intro j
    rw [show (fun z => x + (2 * ρ) • z) '' U j = (fun y => x + y) '' ((fun z => (2 * ρ) • z) '' U j)
        from (Set.image_image (fun y => x + y) (fun z => (2 * ρ) • z) (U j)).symm,
      (isometry_add_left x).ediam_image, Set.image_smul, ediam_smul₀, ENNReal.smul_def, smul_eq_mul,
      ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hlam.le]
  -- hence `Σⱼ (diam Cⱼ)^ℓ = 2^ℓ ρ^ℓ Σⱼ (diam Uⱼ)^ℓ`
  have hsum : ∑' j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) ^ ℓ =
      2 ^ ℓ * ENNReal.ofReal ρ ^ ℓ * ∑' j, Metric.ediam (U j) ^ ℓ := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hdiam j, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ENNReal.mul_rpow_of_nonneg _ _ hℓ.le, ENNReal.mul_rpow_of_nonneg _ _ hℓ.le]
  have key :
      ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) ^ ℓ :=
    hD _ hcover
  rw [hsum] at key
  -- if `σ < 2^{−ℓ}/8` then `r ≤ 2·2^ℓ r σ < 2·2^ℓ r 2^{−ℓ}/8 = r/4 ≤ r`, where `r = ρ^ℓ ∈ (0, ∞)`
  rw [ENNReal.rpow_neg]
  refine not_lt.mp fun hlt => ?_
  set σ := ∑' j, Metric.ediam (U j) ^ ℓ
  set r := ENNReal.ofReal ρ ^ ℓ
  set t := (2 : ℝ≥0∞) ^ ℓ
  have hr0 : r ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hρ) ENNReal.ofReal_ne_top).ne'
  have hrT : r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hℓ.le ENNReal.ofReal_ne_top
  have ht0 : t ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have htT : t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hℓ.le (by norm_num)
  have hcalc : 2 * t * r * (t⁻¹ / 8) = r / 4 := by
    have h8 : (8 : ℝ≥0∞)⁻¹ = 2⁻¹ * 4⁻¹ := by
      rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
      norm_num
    rw [div_eq_mul_inv, div_eq_mul_inv, h8]
    calc 2 * t * r * (t⁻¹ * (2⁻¹ * 4⁻¹))
        = (2 * 2⁻¹) * (t * t⁻¹) * (r * 4⁻¹) := by ring
      _ = r * 4⁻¹ := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), ENNReal.mul_inv_cancel ht0 htT,
          one_mul, one_mul]
  have hfac0 : 2 * t * r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ht0) hr0
  have hfacT : 2 * t * r ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) htT) hrT
  have hrr : r < r :=
    calc r ≤ 2 * (t * r * σ) := key
      _ = 2 * t * r * σ := by ring
      _ < 2 * t * r * (t⁻¹ / 8) := ENNReal.mul_lt_mul_right hfac0 hfacT hlt
      _ = r / 4 := hcalc
      _ ≤ r := ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by norm_num))
  exact lt_irrefl r hrr
/-- **Simon Ch. 1, 3.26(2)** (cover form, unnormalized): for `ℓ > 0` and `A ⊆ ℝᴾ`, at `μH[ℓ]`-a.e.
`x ∈ A` there are arbitrarily small `ρ` with `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` for every countable cover
`{Cⱼ}` of `A ∩ B_ρ(x)`.  Let `η(E) = inf Σⱼ (diam Cⱼ)^ℓ` over countable covers of `E` (the content
`H^ℓ_∞`).  The exceptional points lie in countably many sets `B ⊆ A` of diameter `< R` with
`2η(A ∩ B_ρ(x)) ≤ ρ^ℓ` for `x ∈ B`, `0 < ρ < R`.  If `C` meets such a `B` at `x`, then
`C ∩ B ⊆ A ∩ B_ρ(x)` for every `ρ > diam(C ∩ B)`, so `2η(C ∩ B) ≤ (diam C)^ℓ`; hence
`η(B) ≤ η(B)/2`, `η(B) = 0`, and `μH[ℓ](B) = 0` because covers of small sum have small diameters.
Measurability and boundedness of `A` are not used. -/
theorem Submission.adr_content_density : ∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)), 0 < ℓ → MeasurableSet A → Bornology.IsBounded A → μH[ℓ] {x | x ∈ A ∧ ¬ ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ ∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ} = 0 := by
  intro P ℓ A hℓ _ _
  -- `η` is the content `H^ℓ_∞`
  set η : OuterMeasure (Euclid P) := OuterMeasure.boundedBy fun C => ediam C ^ ℓ with hη
  -- content-null sets are `μH[ℓ]`-null: a cover with `Σⱼ (diam Cⱼ)^ℓ < min ε r^ℓ` has all
  -- diameters `≤ r`
  have hnull : ∀ B : Set (Euclid P), η B = 0 → μH[ℓ] B = 0 := by
    intro B hB
    refine le_antisymm ?_ bot_le
    rw [Measure.hausdorffMeasure_apply]
    refine iSup₂_le fun r hr => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hlt : η B < min (ε : ℝ≥0∞) (r ^ ℓ) := by
      rw [hB]
      exact lt_min (by exact_mod_cast hε) (ENNReal.rpow_pos_of_nonneg hr hℓ.le)
    rw [hη, OuterMeasure.boundedBy_apply] at hlt
    obtain ⟨t, ht, hsum⟩ : ∃ t : ℕ → Set (Euclid P), B ⊆ ⋃ n, t n ∧
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ < min (ε : ℝ≥0∞) (r ^ ℓ) := by
      simpa only [iInf_lt_iff, exists_prop] using hlt
    refine iInf₂_le_of_le t ht (iInf_le_of_le (fun n => ?_) ?_)
    · rcases (t n).eq_empty_or_nonempty with hn | hn
      · simp [hn]
      · refine ((ENNReal.rpow_lt_rpow_iff hℓ).1 ?_).le
        exact ((le_iSup (fun _ : (t n).Nonempty => ediam (t n) ^ ℓ) hn).trans
          (ENNReal.le_tsum (f := fun k => ⨆ _ : (t k).Nonempty, ediam (t k) ^ ℓ) n)).trans_lt
          (hsum.trans_le (min_le_right _ _))
    · rw [zero_add]
      exact (hsum.trans_le (min_le_left _ _)).le
  -- the contraction `η(B) ≤ η(B)/2` on a set `B ⊆ A` of diameter `< R`
  have hcontr : ∀ (R : ℝ) (B : Set (Euclid P)), 0 < R → B ⊆ A → ediam B < ENNReal.ofReal R →
      (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < R → 2 * η (A ∩ ball x ρ) ≤ ENNReal.ofReal ρ ^ ℓ) →
      η B = 0 := by
    intro R B hR hBA hBR hball
    have hkey : ∀ C : Set (Euclid P), 2 * η (C ∩ B) ≤ ediam C ^ ℓ := by
      intro C
      rcases (C ∩ B).eq_empty_or_nonempty with hCB | ⟨x, hxC, hxB⟩
      · rw [hCB, measure_empty, mul_zero]
        exact bot_le
      have hDR : ediam (C ∩ B) < ENNReal.ofReal R :=
        (ediam_mono inter_subset_right).trans_lt hBR
      have hd : ENNReal.ofReal (ediam (C ∩ B)).toReal = ediam (C ∩ B) :=
        ENNReal.ofReal_toReal hDR.ne_top
      have hdR : (ediam (C ∩ B)).toReal < R := by
        rwa [← hd, ENNReal.ofReal_lt_ofReal_iff hR] at hDR
      have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ ^ ℓ) (𝓝[>] (ediam (C ∩ B)).toReal)
          (𝓝 (ENNReal.ofReal (ediam (C ∩ B)).toReal ^ ℓ)) :=
        ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto _).mono_left
          nhdsWithin_le_nhds
      -- `C ∩ B ⊆ A ∩ B_ρ(x)` for `diam(C ∩ B) < ρ < R`; let `ρ ↓ diam(C ∩ B)`
      calc 2 * η (C ∩ B) ≤ ENNReal.ofReal (ediam (C ∩ B)).toReal ^ ℓ := by
            refine ge_of_tendsto hlim ?_
            filter_upwards [Ioo_mem_nhdsGT hdR] with ρ hρ
            have hρ0 : 0 < ρ := ENNReal.toReal_nonneg.trans_lt hρ.1
            have hsub : C ∩ B ⊆ A ∩ ball x ρ := by
              intro y hy
              refine ⟨hBA hy.2, ?_⟩
              have hyx : edist y x ≤ ediam (C ∩ B) := edist_le_ediam_of_mem hy ⟨hxC, hxB⟩
              rw [edist_dist, ← hd, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at hyx
              exact mem_ball.2 (hyx.trans_lt hρ.1)
            calc 2 * η (C ∩ B) ≤ 2 * η (A ∩ ball x ρ) := by gcongr
              _ ≤ ENNReal.ofReal ρ ^ ℓ := hball x hxB ρ hρ0 hρ.2
        _ = ediam (C ∩ B) ^ ℓ := by rw [hd]
        _ ≤ ediam C ^ ℓ := ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) hℓ.le
    have hle : OuterMeasure.restrict B η ≤ (2 : ℝ≥0∞)⁻¹ • η := by
      have h2 : (2 : ℝ≥0∞)⁻¹ • η =
          OuterMeasure.boundedBy ((2 : ℝ≥0∞)⁻¹ • fun C : Set (Euclid P) => ediam C ^ ℓ) :=
        OuterMeasure.smul_boundedBy (ENNReal.inv_ne_top.2 two_ne_zero)
      rw [h2]
      refine OuterMeasure.le_boundedBy.2 fun C => ?_
      rw [OuterMeasure.restrict_apply, Pi.smul_apply, smul_eq_mul,
        ← ENNReal.mul_le_iff_le_inv two_ne_zero ENNReal.ofNat_ne_top]
      exact hkey C
    have hBB : η B ≤ (2 : ℝ≥0∞)⁻¹ * η B := by
      simpa only [OuterMeasure.restrict_apply, inter_self, smul_apply, smul_eq_mul] using hle B
    have hfin : η B ≠ ∞ :=
      ((OuterMeasure.boundedBy_le B).trans_lt (ENNReal.rpow_lt_top_of_nonneg hℓ.le
        (hBR.trans ENNReal.ofReal_lt_top).ne)).ne
    rw [← ENNReal.mul_le_iff_le_inv two_ne_zero ENNReal.ofNat_ne_top, two_mul] at hBB
    exact nonpos_iff_eq_zero.1
      ((ENNReal.add_le_add_iff_left hfin).1 (hBB.trans_eq (add_zero _).symm))
  -- the exceptional set lies in the sets `N m ∩ B(u j, 1/(4(m + 1)))`, `u` dense
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Euclid P)
  let N : ℕ → Set (Euclid P) := fun m => {x | x ∈ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (m + 1) →
    2 * η (A ∩ ball x ρ) ≤ ENNReal.ofReal ρ ^ ℓ}
  refine measure_mono_null (t := ⋃ m : ℕ, ⋃ j : ℕ,
    N m ∩ eball (u j) (ENNReal.ofReal (1 / (4 * (m + 1))))) ?_ ?_
  · rintro x ⟨hxA, hx⟩
    push Not at hx
    obtain ⟨δ, hδ, hδx⟩ := hx
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨j, hj⟩ := hu.exists_dist_lt x (show (0 : ℝ) < 1 / (4 * (m + 1)) by positivity)
    refine mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨j, ⟨hxA, fun ρ hρ hρm => ?_⟩, ?_⟩⟩
    · obtain ⟨C, hC, hCsum⟩ := hδx ρ hρ (hρm.trans hm)
      calc 2 * η (A ∩ ball x ρ) ≤ 2 * ∑' j, ediam (C j) ^ ℓ := by
            gcongr
            exact (measure_mono hC).trans ((measure_iUnion_le C).trans
              (ENNReal.tsum_le_tsum fun j => OuterMeasure.boundedBy_le _))
        _ ≤ ENNReal.ofReal ρ ^ ℓ := hCsum.le
    · rw [mem_eball, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hj
  · refine measure_iUnion_null fun m => measure_iUnion_null fun j => hnull _ ?_
    refine hcontr (1 / (m + 1)) _ (by positivity) (fun x hx => hx.1.1) ?_ (fun x hx => hx.1.2)
    calc ediam (N m ∩ eball (u j) (ENNReal.ofReal (1 / (4 * (m + 1)))))
        ≤ ediam (eball (u j) (ENNReal.ofReal (1 / (4 * (m + 1))))) :=
          ediam_mono inter_subset_right
      _ ≤ 2 * ENNReal.ofReal (1 / (4 * (m + 1))) := ediam_eball_le
      _ < ENNReal.ofReal (1 / (m + 1)) := by
        rw [two_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        field_simp
        linarith

/-- **Simon A.4**, proof of (1) (chapter-A.txt lines 58–112): for `μH[ℓ]`-a.e.
`x ∈ A = sing φ ∩ B₁(0)` some blow-up `φ_{x,λₖ} ⇀ ψ ∈ F` has `ψ` homogeneous of degree zero and
`μH[ℓ](sing ψ ∩ B₁(0)) > 0`.  `A` is closed ∩ open (A.3c), so by `adr_content_density` it
suffices to treat `x ∈ A` with the cover inequality `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` at arbitrarily
small `ρ`.  `adr_exists_strictAnti_radii` gives such `ρₖ ↓ 0` with `ρₖ < (1 − |x|)/4`, and A.2 for
the scales `2ρₖ` gives `sub` and `ψ` with `φ_{x,λₖ} ⇀ ψ`, `λₖ = 2ρ_{sub(k)}`.  If
`μH[ℓ](sing ψ ∩ B₁(0)) = 0`, then A.1 and A.3(3) feed `adr_eventually_subset_small_cover`:
`B_{1/2}(0) ∩ sing φ_{x,λₖ} ⊆ ⋃ⱼ Uⱼ` for `k ≥ k₀`, with `Σⱼ (diam Uⱼ)^ℓ < 2^{−ℓ}/8`.  By A.3(2)
this is hypothesis (ii) of `adr_rescaled_content_lower_bound` at `ρ = ρ_{sub(k₀)}`, whose
conclusion `Σⱼ (diam Uⱼ)^ℓ ≥ 2^{−ℓ}/8` is a contradiction. -/
theorem Submission.adr_tangent_keeps_measure : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ ℓ : ℝ, 0 < ℓ → ∀ φ ∈ F, μH[ℓ] {x | x ∈ sing φ ∩ ball (0 : Euclid P) 1 ∧ ¬ ∃ (lams : ℕ → ℝ) (ψ : Euclid P → Euclid Q), (∀ k, 0 < lams k) ∧ (∀ k, lams k < 1) ∧ (∀ k, ‖x‖ ≤ 1 - lams k) ∧ Tendsto lams atTop (𝓝 0) ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z, f z • φ (x + lams k • z) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ z, f z • ψ z ∂μH[(n : ℝ)]))) ∧ (∀ lam : ℝ, 0 < lam → ∀ z, ψ (lam • z) = ψ z) ∧ 0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1)} = 0 := by
  intro P n Q F sing hF hblow hclosed hsing hconv ℓ hℓ φ hφ
  set A := sing φ ∩ ball (0 : Euclid P) 1
  -- off a `μH[ℓ]`-null set, `x ∈ A` has the cover inequality at arbitrarily small radii
  refine measure_mono_null ?_ (Submission.adr_content_density P ℓ A hℓ
    ((hclosed φ hφ).measurableSet.inter measurableSet_ball) (isBounded_ball.subset inter_subset_right))
  rintro x ⟨hxA, hx⟩
  refine ⟨hxA, fun hD => hx ?_⟩
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hxA.2
  -- radii `ρₖ ↓ 0`, `ρₖ < (1 − |x|)/4`, each with the cover inequality
  obtain ⟨ρs, hρ0, hρlt, hρanti, hρlim, hρD⟩ :=
    Submission.adr_exists_strictAnti_radii _ ((1 - ‖x‖) / 4) (by linarith) hD
  -- A.2 at `y = x` for the scales `2ρₖ`; the blow-up scales are `λₖ = 2ρ_{sub(k)}`
  have h2lim : Tendsto (fun k => 2 * ρs k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hρlim.const_mul 2
  obtain ⟨sub, ψ, hsub, hψF, hψ, hψhom⟩ := hblow φ hφ x hx1 (fun k => 2 * ρs k)
    (fun k => mul_pos two_pos (hρ0 k))
    (fun a b hab => by
      show 2 * ρs b < 2 * ρs a
      linarith [hρanti hab])
    h2lim
  have hlam0 : ∀ k, 0 < 2 * ρs (sub k) := fun k => mul_pos two_pos (hρ0 (sub k))
  have hlam1 : ∀ k, 2 * ρs (sub k) < 1 := fun k => by
    linarith [hρlt (sub k), norm_nonneg x]
  have hlamx : ∀ k, ‖x‖ ≤ 1 - 2 * ρs (sub k) := fun k => by
    linarith [hρlt (sub k)]
  have hlamlim : Tendsto (fun k => 2 * ρs (sub k)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (hρlim.comp hsub.tendsto_atTop).const_mul 2
  refine ⟨fun k => 2 * ρs (sub k), ψ, hlam0, hlam1, hlamx, hlamlim, hψF, hψ, hψhom, ?_⟩
  -- if `μH[ℓ](sing ψ ∩ B₁(0)) = 0`, a cheap cover of `sing ψ` contradicts the cover inequality
  refine pos_iff_ne_zero.2 fun hψ0 => ?_
  have hε : (0 : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (-ℓ) / 8 :=
    ENNReal.div_pos (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne' (by norm_num)
  obtain ⟨U, k₀, hU, hUcov⟩ := Submission.adr_eventually_subset_small_cover P ℓ (sing ψ)
    (fun k => sing fun z => φ (x + (2 * ρs (sub k)) • z)) ((2 : ℝ≥0∞) ^ (-ℓ) / 8) hℓ
    (hclosed ψ hψF) hψ0 hε
    (hconv ψ hψF (fun k z => φ (x + (2 * ρs (sub k)) • z))
      (fun k => hF φ hφ x (2 * ρs (sub k)) (hlam0 k) (hlam1 k) (hlamx k)) hψ)
  -- by A.3(2), `x + λ_{k₀} z ∈ A` with `|z| < 1/2` puts `z` in `B_{1/2}(0) ∩ sing φ_{x,λ_{k₀}}`
  have hcov : ∀ z : Euclid P, x + (2 * ρs (sub k₀)) • z ∈ A → ‖z‖ < 1 / 2 → z ∈ ⋃ j, U j := by
    intro z hzA hz
    refine hUcov k₀ le_rfl ⟨mem_ball_zero_iff.mpr hz, ?_⟩
    show z ∈ sing fun w => φ (x + (2 * ρs (sub k₀)) • w)
    rw [hsing φ hφ x (2 * ρs (sub k₀)) (hlam0 k₀) (hlam1 k₀) (hlamx k₀)]
    exact hzA.1
  exact absurd hU (not_lt.2 (Submission.adr_rescaled_content_lower_bound P ℓ A x (ρs (sub k₀)) U
    hℓ (hρ0 _) (hρD _) hcov))

/-- **Simon, proof of Theorem A.4: the induction on the invariance dimension** (step 7 of the
dimension reduction argument).  If every `L`-invariant `ψ ∈ F` with `sing ψ ≠ ∅` has `dim L ≤ d`,
then `μH[d + α](sing φ ∩ B₁(0)) = 0` for every `φ ∈ F` and `α > 0`.  Otherwise, with `ℓ = d + α`,
induction on `j ≤ d + 1` produces `ψⱼ ∈ F`, invariant under a subspace `Sⱼ` of dimension `≥ j`, with
`μH[ℓ](sing ψⱼ ∩ B₁(0)) > 0`: `adr_tangent_keeps_measure` gives a homogeneous (`{0}`-invariant)
`ψ₀`, and in the step `dim Sⱼ ≤ d < ℓ` makes `Sⱼ` `μH[ℓ]`-null, so a good point `x ∉ Sⱼ` of
`adr_tangent_keeps_measure` exists, whose tangent function is `(Sⱼ + ℝx)`-invariant by
`adr_tangent_invariance`.  Then `ψ_{d+1}` contradicts the bound on `d`. -/
theorem Submission.adr_dimension_bound : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ d : ℕ, (∀ ψ ∈ F, ∀ L : Submodule ℝ (Euclid P), (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → (sing ψ).Nonempty → Module.finrank ℝ L ≤ d) → ∀ φ ∈ F, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] (sing φ ∩ ball (0 : Euclid P) 1) = 0 := by
  intro P n Q F sing hF0 hF1 hA1 hA2 hA3c hA32 hA33 d hd φ hφ α hα
  suffices h : ∀ ℓ : ℝ, (d : ℝ) < ℓ → μH[ℓ] (sing φ ∩ ball (0 : Euclid P) 1) = 0 from
    h _ (lt_add_of_pos_right _ hα)
  intro ℓ hdℓ
  have hℓ : 0 < ℓ := (Nat.cast_nonneg d).trans_lt hdℓ
  -- Step 1: a linear subspace of dimension `≤ d` is `μH[ℓ]`-null
  have hnull : ∀ S : Submodule ℝ (Euclid P), Module.finrank ℝ S ≤ d →
      μH[ℓ] (S : Set (Euclid P)) = 0 := by
    intro S hS
    have hSℓ : (Module.finrank ℝ S : ℝ) < ℓ := lt_of_le_of_lt (by exact_mod_cast hS) hdℓ
    -- `μH[dim S]` is an additive Haar measure on `S`, finite on balls, so `μH[ℓ]` vanishes there
    have hball : ∀ r : ℕ, μH[ℓ] (closedBall (0 : S) r) = 0 := fun r =>
      (Measure.hausdorffMeasure_zero_or_top hSℓ _).resolve_right
        (isCompact_closedBall (0 : S) r).measure_lt_top.ne
    have huniv : μH[ℓ] (univ : Set S) = 0 := by
      refine measure_mono_null (fun y _ => ?_) (measure_iUnion_null hball)
      obtain ⟨r, hr⟩ := exists_nat_ge ‖y‖
      exact mem_iUnion.mpr ⟨r, mem_closedBall_zero_iff.mpr hr⟩
    -- transport along the isometric inclusion `S → ℝᴾ`
    calc μH[ℓ] (S : Set (Euclid P)) = μH[ℓ] (S.subtypeₗᵢ '' univ) := by simp
      _ = μH[ℓ] (univ : Set S) := S.subtypeₗᵢ.isometry.hausdorffMeasure_image (Or.inl hℓ.le) _
      _ = 0 := huniv
  -- a set of positive measure has a point off a null set `N` with a property `p` failing only on
  -- a null set
  have hgood : ∀ (A N : Set (Euclid P)) (p : Euclid P → Prop), 0 < μH[ℓ] A →
      μH[ℓ] {x | x ∈ A ∧ ¬ p x} = 0 → μH[ℓ] N = 0 → ∃ x ∈ A, x ∉ N ∧ p x := by
    intro A N p hA hbad hN
    by_contra hcon
    refine hA.ne' (measure_mono_null (fun x hx => ?_) (measure_union_null hbad hN))
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, fun h => hcon ⟨x, hx, hxN, h⟩⟩
  have hne : ∀ ψ : Euclid P → Euclid Q, 0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1) →
      (sing ψ).Nonempty := fun ψ h => (nonempty_of_measure_ne_zero h.ne').left
  by_contra h0
  have hpos : 0 < μH[ℓ] (sing φ ∩ ball (0 : Euclid P) 1) := pos_iff_ne_zero.mpr h0
  -- Step 2: the claim `C(j)`, with `dim Sⱼ ≥ j`
  have key : ∀ j : ℕ, ∃ ψ ∈ F, ∃ S : Submodule ℝ (Euclid P), j ≤ Module.finrank ℝ S ∧
      (∀ y ∈ S, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧
      0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1) := by
    intro j
    induction j with
    | zero =>
      -- Step 3: a homogeneous tangent function of positive measure; homogeneity is
      -- `{0}`-invariance
      obtain ⟨x, -, -, lams, ψ, -, -, -, -, hψF, -, hψhom, hψpos⟩ :=
        hgood _ ∅ _ hpos (Submission.adr_tangent_keeps_measure P n Q F sing hA1 hA2 hA3c hA32 hA33
          ℓ hℓ φ hφ) measure_empty
      refine ⟨ψ, hψF, ⊥, Nat.zero_le _, fun y hy lam hlam z => ?_, hψpos⟩
      rw [(Submodule.mem_bot ℝ).mp hy, zero_add]
      exact hψhom lam hlam z
    | succ j ih =>
      -- Step 4: blow up `ψⱼ` at a good point `x ∉ Sⱼ`
      obtain ⟨ψ, hψF, S, hjS, hSinv, hψpos⟩ := ih
      have hSd : Module.finrank ℝ S ≤ d := hd ψ hψF S hSinv (hne ψ hψpos)
      obtain ⟨x, -, hxS, lams, ψ', hlam0, hlam1, hlamx, hlim, hψ'F, hconv, hψ'hom, hψ'pos⟩ :=
        hgood _ _ _ hψpos (Submission.adr_tangent_keeps_measure P n Q F sing hA1 hA2 hA3c hA32
          hA33 ℓ hℓ ψ hψF) (hnull S hSd)
      refine ⟨ψ', hψ'F, S ⊔ Submodule.span ℝ {x}, ?_,
        Submission.adr_tangent_invariance P n Q F hF0 hF1 hA1 ψ hψF S hSinv x lams ψ' hlam0 hlim
          (fun k => hA1 ψ hψF x (lams k) (hlam0 k) (hlam1 k) (hlamx k)) hψ'F hψ'hom hconv,
        hψ'pos⟩
      rw [Submodule.finrank_sup_span_singleton hxS]
      omega
  -- Step 5: `C(d + 1)` contradicts the bound on `d`
  obtain ⟨ψ, hψF, S, hS, hSinv, hψpos⟩ := key (d + 1)
  have := hd ψ hψF S hSinv (hne ψ hψpos)
  omega

/-- **Simon, proof of A.4 (p. 228), `sing ψ = T`.**  Let `d` bound `dim L` for every subspace `L`
such that some `ψ ∈ F` with `sing ψ ≠ ∅` satisfies `ψ(y + λx) = ψ(x)` for `y ∈ L`, `λ > 0`.  If
`φ ∈ F` with `sing φ ≠ ∅` is invariant in this sense under a `d`-dimensional `L`, then
`sing φ = L`: `L ⊆ sing φ` by A.3(2), and a singular point outside `L`, rescaled to `x` with
`‖x‖ = 1/2`, would give by A.2 a tangent function at `x` that is singular at `0` (A.3(3)) and
invariant under the `(d + 1)`-dimensional `L + ℝx`. -/
theorem Submission.adr_extremal_sing_eq : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ d : ℕ, (∀ ψ ∈ F, ∀ L : Submodule ℝ (Euclid P), (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → (sing ψ).Nonempty → Module.finrank ℝ L ≤ d) → ∀ φ ∈ F, ∀ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, φ (y + lam • x) = φ x) → (sing φ).Nonempty → sing φ = (L : Set (Euclid P)) := by
  intro P n Q F sing hH0 hH1 hA1 hA2 hclosed hA32 hA33 d hd φ hφ L hLdim hLinv hne
  -- Lemma S: `y + λ ·` (`y ∈ L`, `λ > 0`) preserves `sing φ`, and `L ⊆ sing φ`
  have hpre : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam →
      (fun x => y + lam • x) ⁻¹' sing φ = sing φ := by
    intro y hy lam hlam hlam1 hy1
    rw [← hA32 φ hφ y lam hlam hlam1 hy1, funext fun x => hLinv y hy lam hlam x]
  obtain ⟨hinv, hLsub⟩ :=
    Submission.adr_affine_invariant_closed_set P (sing φ) L (hclosed φ hφ) hpre
  refine Set.Subset.antisymm (fun z hz => ?_) (hLsub hne)
  by_contra hzL
  -- rescale a singular point `z ∉ L` to `x ∈ sing φ ∖ L` with `‖x‖ = 1/2`
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => hzL (h ▸ L.zero_mem)
  set c : ℝ := 1 / (2 * ‖z‖) with hc
  have hc0 : 0 < c := by positivity
  set x : Euclid P := c • z with hx
  have hxs : x ∈ sing φ := by simpa using (hinv 0 L.zero_mem c hc0 z).2 hz
  have hxn : ‖x‖ = 1 / 2 := by
    rw [hx, norm_smul, Real.norm_of_nonneg hc0.le, hc]
    field_simp
  have hxL : x ∉ L := fun h => hzL <| by
    simpa [hx, smul_smul, inv_mul_cancel₀ hc0.ne'] using L.smul_mem c⁻¹ h
  -- A.2 at `x` along `Λ k = (1/2)/(k + 2) ≤ 1/4`: a homogeneous tangent function `ψ`
  set Λ : ℕ → ℝ := fun k => (1 / 2) / ((k : ℝ) + 2) with hΛ
  have hΛpos : ∀ k, 0 < Λ k := fun k => by positivity
  have hΛanti : StrictAnti Λ := fun a b hab =>
    div_lt_div_of_pos_left (by norm_num) (by positivity)
      (by simpa using (Nat.cast_lt.2 hab : (a : ℝ) < b))
  have hΛlim : Tendsto Λ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hΛle : ∀ k, Λ k ≤ 1 / 4 := fun k => by
    rw [hΛ, div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨sub, ψ, hsub, hψ, hconv, hhom⟩ :=
    hA2 φ hφ x (by rw [hxn]; norm_num) Λ hΛpos hΛanti hΛlim
  have hk : ∀ k, 0 < Λ (sub k) ∧ Λ (sub k) < 1 ∧ ‖x‖ ≤ 1 - Λ (sub k) := fun k =>
    ⟨hΛpos _, by linarith [hΛle (sub k)], by linarith [hΛle (sub k)]⟩
  have hφk : ∀ k, (fun z => φ (x + Λ (sub k) • z)) ∈ F := fun k =>
    hA1 φ hφ x _ (hk k).1 (hk k).2.1 (hk k).2.2
  -- Lemma T: `0 ∈ sing ψ`, since `0 ∈ B₁(0) ∩ sing φ_{x,λ_k}` by A.3(2)
  have hψs : (0 : Euclid P) ∈ sing ψ :=
    Submission.adr_sing_mem_of_tendsto P n Q F sing hclosed hA33 ψ hψ
      (fun k z => φ (x + Λ (sub k) • z)) hφk hconv (fun _ => 0) 0
      (fun k => ⟨mem_ball_self one_pos, by
        rw [hA32 φ hφ x _ (hk k).1 (hk k).2.1 (hk k).2.2, Set.mem_preimage, smul_zero, add_zero]
        exact hxs⟩)
      tendsto_const_nhds
  -- Lemma I: `ψ` is invariant under `L + ℝx`, of dimension `d + 1`, contradicting the bound `d`
  have hdim := hd ψ hψ (L ⊔ Submodule.span ℝ {x})
    (Submission.adr_tangent_invariance P n Q F hH0 hH1 hA1 φ hφ L hLinv x (fun k => Λ (sub k)) ψ
      (fun k => (hk k).1) (hΛlim.comp hsub.tendsto_atTop) hφk hψ hhom hconv) ⟨0, hψs⟩
  rw [Submodule.finrank_sup_span_singleton hxL, hLdim] at hdim
  omega

/-- **Simon A.4, last claim (p. 228).**  If `sing φ ∩ B₁(0)` is `μH[1]`-null for every `φ ∈ F`
(the case `d = 0`), then `sing φ ∩ B_σ(0)` is finite for `σ < 1`.  Otherwise
`adr_secant_rescaling_of_infinite` gives `x`, `|x| < 1`, admissible scales `λₖ ↓ 0` and points
`zₖ → z`, `|zₖ| = |z| = 1/2`, with `x + λₖzₖ ∈ sing φ`.  A.2 gives a homogeneous `ψ ∈ F` with
`φ_{x,λₖ'} ⇀ ψ`; by A.1 and A.3(2), `zₖ' ∈ B₁(0) ∩ sing φ_{x,λₖ'}`, so `z ∈ sing ψ`
(`adr_sing_mem_of_tendsto`).  Homogeneity and A.3(2) make the closed set `sing ψ` invariant
under the dilations `w ↦ λw` (`adr_affine_invariant_closed_set` with `L = {0}`), so it contains
the segment `(0, z]` and `μH[1](sing ψ ∩ B₁(0)) > 0` (`adr_radial_segment_hausdorff_pos`),
contradicting the hypothesis for `ψ`. -/
theorem Submission.adr_finite_of_dim_zero : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → (∀ φ ∈ F, μH[1] (sing φ ∩ ball (0 : Euclid P) 1) = 0) → ∀ φ ∈ F, ∀ σ : ℝ, σ < 1 → (sing φ ∩ ball (0 : Euclid P) σ).Finite := by
  intro P n Q F sing hA1 hA2 hclosed hA32 hA33 hnull φ hφ σ hσ
  refine Set.not_infinite.1 fun hinf => ?_
  -- an accumulation point `x` of `sing φ`, admissible scales and rescaled singular points
  obtain ⟨x, lams, zs, z, hx, hpos, hanti, hlim, hlt, hle, hmem, hzs, hzlim, hz⟩ :=
    Submission.adr_secant_rescaling_of_infinite P (sing φ) σ hσ hinf
  -- A.2: a homogeneous tangent function `ψ` of `φ` at `x`
  obtain ⟨sub, ψ, hsub, hψ, hconv, hhom⟩ := hA2 φ hφ x hx lams hpos hanti hlim
  -- A.1 and A.3(2): `zₖ'` is a singular point of the blow-up `φ_{x,λₖ'}` in `B₁(0)`
  have hzsing : ∀ k, zs (sub k) ∈ ball (0 : Euclid P) 1 ∩
      sing (fun w => φ (x + lams (sub k) • w)) := fun k =>
    ⟨by rw [mem_ball_zero_iff, hzs]; norm_num, by
      rw [hA32 φ hφ x (lams (sub k)) (hpos _) (hlt _) (hle _)]
      exact hmem (sub k)⟩
  -- Lemma T: `z ∈ sing ψ`
  have hzψ : z ∈ sing ψ :=
    Submission.adr_sing_mem_of_tendsto P n Q F sing hclosed hA33 ψ hψ
      (fun k w => φ (x + lams (sub k) • w))
      (fun k => hA1 φ hφ x (lams (sub k)) (hpos _) (hlt _) (hle _)) hconv
      (fun k => zs (sub k)) z hzsing (hzlim.comp hsub.tendsto_atTop)
  -- Lemma S with `L = {0}`: `t • w ∈ sing ψ ↔ w ∈ sing ψ` for `t > 0`
  have hray := (Submission.adr_affine_invariant_closed_set P (sing ψ) ⊥ (hclosed ψ hψ)
    fun y hy lam hlam hlam1 hy1 => by
      obtain rfl := (Submodule.mem_bot ℝ).1 hy
      have hdil : (fun w => ψ (0 + lam • w)) = ψ := funext fun w => by
        rw [zero_add]
        exact hhom lam hlam w
      have h := hA32 ψ hψ 0 lam hlam hlam1 hy1
      rw [hdil] at h
      exact h.symm).1 0 (Submodule.zero_mem ⊥)
  -- the segment `(0, z]` lies in `sing ψ`, so `sing ψ ∩ B₁(0)` is not `μH[1]`-null
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hseg := Submission.adr_radial_segment_hausdorff_pos P (sing ψ) z hz0
    (by rw [hz]; norm_num) fun t ht _ => by simpa using (hray t ht z).2 hzψ
  exact hseg.ne' (hnull ψ hψ)

/-- **Simon A.4 (Theorem, pp. 226–228)**, with the additional hypothesis (H0) that members of `F`
agreeing `μH[n]`-a.e. are equal.  Let `d` be the largest dimension of a subspace `L` such that some
`ψ ∈ F` with `sing ψ ≠ ∅` satisfies `ψ(y + λx) = ψ(x)` for all `y ∈ L`, `λ > 0`.  A tangent
function at a singular point in `B₁(0)` (A.2, A.3(2), A.3(3)) shows that `L = {0}` qualifies, and
Remark A.5 with A.3(1) gives `d ≤ n − 1`.  The dimension bound, `sing ψ = L` for an extremal `ψ`
and finiteness when `d = 0` are `adr_dimension_bound`, `adr_extremal_sing_eq` and
`adr_finite_of_dim_zero`. -/
theorem Submission.abstract_dimension_reduction : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (L : Submodule ℝ (Euclid P)) (c : Euclid Q), Module.finrank ℝ L = n → φ = Set.indicator (L : Set (Euclid P)) (fun _ => c) → sing φ = ∅) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → (∀ φ ∈ F, ball (0 : Euclid P) 1 ∩ sing φ = ∅) ∨ ∃ d : ℕ, d + 1 ≤ n ∧ (∀ φ ∈ F, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] (sing φ ∩ ball (0 : Euclid P) 1) = 0) ∧ (∃ ψ ∈ F, ∃ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d ∧ sing ψ = (L : Set (Euclid P)) ∧ ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧ (d = 0 → ∀ φ ∈ F, ∀ σ : ℝ, σ < 1 → (sing φ ∩ ball (0 : Euclid P) σ).Finite) := by
  intro P n Q F sing hH0 hH1 hA1 hA2 hclosed hplane hA32 hA33
  by_cases hI : ∀ φ ∈ F, ball (0 : Euclid P) 1 ∩ sing φ = ∅
  · exact Or.inl hI
  refine Or.inr ?_
  obtain ⟨φ₀, hφ₀, x₀, hx₀, hx₀s⟩ : ∃ φ ∈ F, (ball (0 : Euclid P) 1 ∩ sing φ).Nonempty := by
    by_contra h
    exact hI fun φ hφ => Set.not_nonempty_iff_eq_empty.1 fun hne => h ⟨φ, hφ, hne⟩
  -- `D`: dimensions of subspaces leaving invariant a member of `F` with nonempty singular set
  obtain ⟨D, hD⟩ : ∃ D : Set ℕ, ∀ m, m ∈ D ↔ ∃ ψ ∈ F, ∃ L : Submodule ℝ (Euclid P),
      (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧ (sing ψ).Nonempty ∧
        Module.finrank ℝ L = m :=
    ⟨_, fun _ => Iff.rfl⟩
  -- Remark A.5 and A.3(1): `D` lies below `n`
  have hDlt : ∀ m ∈ D, m < n := by
    intro m hm
    obtain ⟨ψ, hψ, L, hinv, hne, rfl⟩ := (hD m).1 hm
    by_contra hle
    obtain ⟨L', hL', hψL'⟩ :=
      Submission.adr_invariant_eq_indicator P n Q ψ L (hH1 ψ hψ) (not_lt.1 hle) hinv
    exact hne.ne_empty (hplane ψ hψ L' (ψ 0) hL' hψL')
  -- A.2, A.3(2) and Lemma T: a homogeneous tangent function at `x₀` is singular at `0`
  have hD0 : 0 ∈ D := by
    have hx₀n : ‖x₀‖ < 1 := mem_ball_zero_iff.1 hx₀
    have hr : 0 < 1 - ‖x₀‖ := sub_pos.2 hx₀n
    set lams : ℕ → ℝ := fun k => (1 - ‖x₀‖) / ((k : ℝ) + 2)
    have hpos : ∀ k, 0 < lams k := fun k => div_pos hr (by positivity)
    have hsmall : ∀ k, lams k < 1 - ‖x₀‖ := fun k =>
      div_lt_self hr (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hanti : StrictAnti lams := fun a b hab =>
      div_lt_div_of_pos_left hr (by positivity) (by linarith [(Nat.cast_lt.2 hab : (a : ℝ) < b)])
    have hlim : Tendsto lams atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    obtain ⟨sub, ψ, -, hψ, hconv, hhom⟩ := hA2 φ₀ hφ₀ x₀ hx₀n lams hpos hanti hlim
    have hk : ∀ k, 0 < lams (sub k) ∧ lams (sub k) < 1 ∧ ‖x₀‖ ≤ 1 - lams (sub k) := fun k =>
      ⟨hpos _, by linarith [hsmall (sub k), norm_nonneg x₀], by linarith [hsmall (sub k)]⟩
    have hsing0 : (0 : Euclid P) ∈ sing ψ :=
      Submission.adr_sing_mem_of_tendsto P n Q F sing hclosed hA33 ψ hψ
        (fun k x => φ₀ (x₀ + lams (sub k) • x))
        (fun k => hA1 φ₀ hφ₀ x₀ _ (hk k).1 (hk k).2.1 (hk k).2.2) hconv (fun _ => 0) 0
        (fun k => ⟨mem_ball_self one_pos, by
          rw [hA32 φ₀ hφ₀ x₀ _ (hk k).1 (hk k).2.1 (hk k).2.2, Set.mem_preimage, smul_zero,
            add_zero]
          exact hx₀s⟩)
        tendsto_const_nhds
    refine (hD 0).2 ⟨ψ, hψ, ⊥, fun y hy lam hlam x => ?_, ⟨0, hsing0⟩, finrank_bot ℝ (Euclid P)⟩
    rw [(Submodule.mem_bot ℝ).1 hy, zero_add]
    exact hhom lam hlam x
  -- `d := max D`
  obtain ⟨d, hdD, hdmax⟩ : ∃ d ∈ D, ∀ m ∈ D, m ≤ d :=
    have hbdd : BddAbove D := ⟨n, fun m hm => (hDlt m hm).le⟩
    ⟨sSup D, Nat.sSup_mem ⟨0, hD0⟩ hbdd, fun m hm => le_csSup hbdd hm⟩
  have hd : ∀ ψ ∈ F, ∀ L : Submodule ℝ (Euclid P),
      (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → (sing ψ).Nonempty →
        Module.finrank ℝ L ≤ d :=
    fun ψ hψ L hinv hne => hdmax _ ((hD _).2 ⟨ψ, hψ, L, hinv, hne, rfl⟩)
  have hdim := Submission.adr_dimension_bound P n Q F sing hH0 hH1 hA1 hA2 hclosed hA32 hA33 d hd
  obtain ⟨ψ, hψ, L, hinv, hne, hL⟩ := (hD d).1 hdD
  refine ⟨d, hDlt d hdD, hdim, ⟨ψ, hψ, L, hL, ?_, hinv⟩, fun hd0 => ?_⟩
  · exact Submission.adr_extremal_sing_eq P n Q F sing hH0 hH1 hA1 hA2 hclosed hA32 hA33 d hd
      ψ hψ L hL hinv hne
  · subst hd0
    refine Submission.adr_finite_of_dim_zero P n Q F sing hA1 hA2 hclosed hA32 hA33
      fun φ hφ => ?_
    have h1 := hdim φ hφ 1 one_pos
    rwa [Nat.cast_zero, zero_add] at h1

/-- **Simon 7.3.3**, step 1 of the class reduction (Remark 3.4, proof of 3.3(2)): for any measure
`μ` on `ℝᴾ` the upper density `limsup_{ρ↓0} μ(B_ρ(x))/(ωₙρⁿ)` is Borel in `x`.  `x ↦ μ(B_ρ(x))`
is lower semicontinuous by continuity from below on the balls `B_{ρ−1/(m+1)}(x) ↑ B_ρ(x)`;
dividing by `ωₙρⁿ ≠ 0` and taking suprema over `ρ ∈ (0, 1/(m+1))` keeps lower semicontinuity,
and the `limsup` along `𝓝[>] 0` is the infimum over `m ∈ ℕ` of these suprema. -/
theorem Submission.idtp_fons_cr_density_measurable : ∀ (P n : ℕ) (μ : Measure (Euclid P)), Measurable (fun x : Euclid P => (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) := by
  intro P n μ
  -- `x ↦ μ(B_ρ(x))` is lower semicontinuous: `B_ρ(x)` is the increasing union of the balls
  -- `B_{ρ - 1/(m+1)}(x)`, each contained in `B_ρ(x')` for `|x' - x| < 1/(m+1)`
  have hball : ∀ ρ : ℝ, LowerSemicontinuous fun x : Euclid P => μ (ball x ρ) := by
    intro ρ x t ht
    have hU : ⋃ m : ℕ, ball x (ρ - 1 / ((m : ℝ) + 1)) = ball x ρ := by
      ext z
      simp only [mem_iUnion, mem_ball]
      constructor
      · rintro ⟨m, hm⟩
        linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := m)]
      · intro hz
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
        exact ⟨m, by linarith⟩
    have hmono : Monotone fun m : ℕ => ball x (ρ - 1 / ((m : ℝ) + 1)) := fun a b hab =>
      ball_subset_ball (sub_le_sub_left (Nat.one_div_le_one_div hab) ρ)
    have ht' : t < μ (⋃ m : ℕ, ball x (ρ - 1 / ((m : ℝ) + 1))) := by
      rw [hU]
      exact ht
    obtain ⟨m, hm⟩ := ((tendsto_measure_iUnion_atTop (μ := μ) hmono).eventually
      (lt_mem_nhds ht')).exists
    filter_upwards [ball_mem_nhds x (Nat.one_div_pos_of_nat (α := ℝ) (n := m))] with x' hx'
    refine hm.trans_le (measure_mono (ball_subset_ball' ?_))
    rw [mem_ball, dist_comm] at hx'
    linarith
  -- dividing by `ωₙρⁿ ≠ 0` preserves lower semicontinuity
  have hω : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hg : ∀ ρ : ℝ, 0 < ρ → LowerSemicontinuous fun x : Euclid P =>
      μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := fun ρ hρ =>
    (ENNReal.continuous_div_const _ (mul_ne_zero hω (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne')
      ).comp_lowerSemicontinuous (hball ρ) fun a b hab => ENNReal.div_le_div_right hab _
  -- the `limsup` along `𝓝[>] 0` is the countable infimum over the basis `(0, 1/(m+1))`
  have hbasis := nhdsWithin_hasBasis (nhds_basis_ball_inv_nat_succ (x := (0 : ℝ))) (Ioi 0)
  simp_rw [hbasis.limsup_eq_iInf_iSup]
  exact Measurable.ennreal_toReal (Measurable.iInf fun m => Measurable.iInf fun _ =>
    (lowerSemicontinuous_biSup fun ρ hρ => hg ρ hρ.2).measurable)
/-- **Simon 7.3.3, proof of 3.3(2)**, rescaling (chapter-07.txt lines 512–583, with Remark 3.4,
lines 380–398): for `t > 0` let `μ^{y,t} = t⁻ⁿ (η_{y,t})_# μ`.  As
`η_{y,t}⁻¹(B_ρ(w)) = B_{tρ}(y + tw)`, `μ^{y,t}(B_ρ(w)) = t⁻ⁿ μ(B_{tρ}(y + tw))`, so the density
ratio of `μ^{y,t}` at `(w, ρ)` is that of `μ` at `(y + tw, tρ)`; since `ρ ↦ tρ` maps `𝓝[>] 0`
onto itself the upper densities agree, and since `t⁻ⁿ ≠ 0` every ball about `w` has positive
`μ^{y,t}`-measure iff every ball about `y + tw` has positive `μ`-measure. -/
theorem Submission.idtp_fons_cr_density_rescale : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (t : ℝ), 0 < t → (∀ w : Euclid P, limsup (fun ρ : ℝ => (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => μ (ball (y + t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)) ∧ ∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (y + t • w) ε) ≠ 0 := by
  intro P n μ y t ht
  -- `η_{y,t}⁻¹(B_ρ(w)) = B_{tρ}(y + tw)`, so `μ^{y,t}(B_ρ(w)) = t⁻ⁿ μ(B_{tρ}(y + tw))`
  have hball : ∀ (w : Euclid P) (ρ : ℝ), (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t))
      (ball w ρ) = ENNReal.ofReal (t⁻¹ ^ n) * μ (ball (y + t • w) (t * ρ)) := by
    intro w ρ
    have hmeas : Measurable (dilation y t) :=
      (continuous_const.add (dilationCLM P t).continuous).measurable
    have hpre : dilation y t ⁻¹' ball w ρ = ball (y + t • w) (t * ρ) := by
      ext z
      have hz : dilation y t z - w = t⁻¹ • (z - (y + t • w)) := by
        change -(t⁻¹ • y) + t⁻¹ • z - w = _
        rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
        abel
      rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hz, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht]
    rw [Measure.smul_apply, Measure.map_apply hmeas measurableSet_ball, hpre, smul_eq_mul]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · -- the density ratio of `μ^{y,t}` at `(w, ρ)` is that of `μ` at `(y + tw, tρ)`
    set H : ℝ → ℝ≥0∞ := fun r => μ (ball (y + t • w) r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))
    have hk0 : ENNReal.ofReal (t ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht n)).ne'
    have hfun : (fun ρ : ℝ => (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) = H ∘ (t * ·) := by
      funext ρ
      rw [comp_apply, hball]
      simp only [H, mul_pow, ENNReal.ofReal_mul (pow_nonneg ht.le n), inv_pow,
        ENNReal.ofReal_inv_of_pos (pow_pos ht n), div_eq_mul_inv]
      rw [mul_left_comm (unitBallVolume n), ENNReal.mul_inv (Or.inl hk0) (Or.inl ENNReal.ofReal_ne_top)]
      ring
    -- `ρ ↦ tρ` maps `𝓝[>] 0` onto itself
    have hmap : map (t * ·) (𝓝[>] (0 : ℝ)) = 𝓝[>] 0 := by
      conv_lhs => rw [← comap_mulLeft_nhdsGT_zero ht]
      exact map_comap_of_surjective (mul_left_surjective₀ ht.ne') _
    rw [hfun, limsup_comp, hmap]
  · -- `t⁻ⁿ ≠ 0` and `ε ↦ tε` is a bijection of `(0, ∞)`
    have hc : ENNReal.ofReal (t⁻¹ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 ht) n)).ne'
    simp only [hball, ne_eq, mul_eq_zero, hc, false_or]
    constructor
    · intro h δ hδ
      have := h (δ / t) (div_pos hδ ht)
      rwa [mul_div_cancel₀ δ ht.ne'] at this
    · intro h ε hε
      exact h (t * ε) (mul_pos ht hε)
/-- **Normalization** (Simon 7.3.3, proof of 3.3(2); Remark 3.4): `μHE[n] = a • μH[n]` with
`a = addHaarScalarFactor(volume, μH[n]) ≠ 0` depending only on `n`, so `c = a⁻¹`.  If
`μ = μHE[n]⌞g` is finite on compact sets, then `∫⁻_K g dμH[n] = a⁻¹ μ(K) < ∞` for compact `K`,
so `g • e` is locally `μH[n]`-integrable, and
`∫ f (g • e) dμH[n] = (∫ f g dμH[n]) • e = (a⁻¹ ∫ f g dμHE[n]) • e = (a⁻¹ ∫ f dμ) • e`. -/
theorem Submission.idtp_fons_cr_density_normalization : ∀ (P n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (Q : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (e : Euclid Q), Measurable g → (∀ x, 0 ≤ g x) → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (g x)) → LocallyIntegrable (fun x => g x • e) μH[(n : ℝ)] ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x • (g x • e) ∂μH[(n : ℝ)] = (c * ∫ x, f x ∂μ) • e := by
  intro P n
  -- `μHE[n] = a • μH[n]`, where `a ≠ 0` depends only on `n`
  obtain ⟨a, ha0, hE⟩ : ∃ a : NNReal, a ≠ 0 ∧
      (μHE[n] : Measure (Euclid P)) = a • μH[(n : ℝ)] :=
    ⟨_, Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n,
      Measure.euclideanHausdorffMeasure_def n⟩
  refine ⟨(a : ℝ)⁻¹, inv_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha0)), ?_⟩
  intro Q μ g e hg hg0 hμK hμ
  -- `μ = a • μH[n]⌞g`
  have hμ' : μ = (a : ℝ≥0∞) • (μH[(n : ℝ)] : Measure (Euclid P)).withDensity
      (fun x => ENNReal.ofReal (g x)) := by
    rw [hμ, hE, ← withDensity_smul_measure]
    rfl
  refine ⟨?_, fun f hf hfc => ?_⟩
  · -- local integrability: `∫⁻_K g dμH[n] = a⁻¹ μ(K) < ∞` for compact `K`
    rw [locallyIntegrable_iff]
    intro K hK
    refine Integrable.smul_const ⟨hg.aestronglyMeasurable, ?_⟩ e
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0), ← withDensity_apply _ hK.measurableSet]
    have hK' := hμK K hK
    rw [hμ', Measure.smul_apply, smul_eq_mul] at hK'
    exact ENNReal.lt_top_of_mul_ne_top_right hK' (by exact_mod_cast ha0)
  · -- pull out `e`, then pass from `μH[n]` to `μHE[n] = a • μH[n]` and to `μ = μHE[n]⌞g`
    have h1 : ∀ x, f x • (g x • e) = (f x * g x) • e := fun x => smul_smul _ _ _
    simp_rw [h1]
    rw [integral_smul_const]
    congr 1
    have h2 : ∫ x, f x ∂μ = (a : ℝ) * ∫ x, f x * g x ∂μH[(n : ℝ)] := by
      rw [hμ, hE, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top), integral_smul_nnreal_measure,
        NNReal.smul_def, smul_eq_mul]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul, mul_comm]
    rw [h2, ← mul_assoc, inv_mul_cancel₀ (NNReal.coe_ne_zero.2 ha0), one_mul]
/-- **Support semicontinuity** (Simon 7.3.3, proof of 3.3(2); Remark 3.4).  Let `μₖ → μ`
vaguely, let the domains `Dₖ` exhaust the open set `U`, and let `μₖ(B_ρ(z)) ≥ e^{−Λρ} ωₙ ρⁿ` for
`z ∈ spt μₖ` whenever `B̄_ρ(z) ⊆ Dₖ`.  If `yₖ ∈ spt μₖ` and `yₖ → y ∈ U`, then `y ∈ spt μ`.  With
`B_{r₀}(y) ⊆ U` and `r = min(ε, r₀)/4`, the bump `f = max(0, 4 − |x − y|/r)` is `≥ 1` on
`B_r(yₖ)` for large `k`, so `∫ f dμₖ ≥ μₖ(B_r(yₖ)) ≥ e^{−Λr} ωₙ rⁿ > 0`; hence `∫ f dμ > 0`, which
is impossible if `μ(B_ε(y)) = 0`, as `f = 0` off `B_{4r}(y) ⊆ B_ε(y)`. -/
theorem Submission.idtp_fons_cr_support_limit : ∀ (P n : ℕ) (Λ : ℝ) (μ : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (U : Set (Euclid P)) (Ds : ℕ → Set (Euclid P)) (ys : ℕ → Euclid P) (y : Euclid P), (∀ (k : ℕ) (K : Set (Euclid P)), IsCompact K → μs k K ≠ ∞) → IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∀ᶠ k in atTop, K ⊆ Ds k) → (∀ (k : ℕ) (z : Euclid P) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ Ds k → (∀ ε : ℝ, 0 < ε → μs k (ball z ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(Λ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ μs k (ball z ρ)) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x ∂(μs k)) atTop (𝓝 (∫ x, f x ∂μ))) → (∀ (k : ℕ) (ε : ℝ), 0 < ε → μs k (ball (ys k) ε) ≠ 0) → Tendsto ys atTop (𝓝 y) → y ∈ U → ∀ ε : ℝ, 0 < ε → μ (ball y ε) ≠ 0 := by
  intro P n Λ μ μs U Ds ys y hfin hU hexh hlow hvague hys hy hyU ε hε hμ0
  -- `B_{r₀}(y) ⊆ U`; work at the radius `r = min(ε, r₀)/4`
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hU y hyU
  set r : ℝ := min ε r₀ / 4 with hr_def
  have hr : 0 < r := div_pos (lt_min hε hr₀) four_pos
  have h4r : 4 * r ≤ ε := by rw [hr_def]; linarith [min_le_left ε r₀]
  have h2r : 2 * r < r₀ := by rw [hr_def]; linarith [min_le_right ε r₀]
  -- eventually the compact `B̄_{2r}(y) ⊆ U` lies in `Ds k`, and `|yₖ − y| < r`
  have hK : ∀ᶠ k in atTop, closedBall y (2 * r) ⊆ Ds k :=
    hexh _ (isCompact_closedBall y (2 * r)) ((closedBall_subset_ball h2r).trans hr₀U)
  have hyk : ∀ᶠ k in atTop, ys k ∈ ball y r := hy.eventually (ball_mem_nhds y hr)
  -- the bump `f = max(0, 4 − |x − y|/r)`: `f ≥ 1` on `B_{2r}(y)`, `f = 0` off `B_{4r}(y)`
  set f : Euclid P → ℝ := fun x => max 0 (4 - dist x y / r)
  have hfc : Continuous f :=
    continuous_const.max (continuous_const.sub ((continuous_id.dist continuous_const).div_const r))
  have hf0 : ∀ x, 0 ≤ f x := fun x => le_max_left _ _
  have hfsupp : ∀ x, f x ≠ 0 → dist x y < 4 * r := by
    intro x hx
    by_contra h
    refine hx (max_eq_left ?_)
    have : 4 ≤ dist x y / r := (le_div_iff₀ hr).2 (by linarith [not_lt.1 h])
    linarith
  have hfcs : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall y (4 * r)) fun x hx => by
      by_contra h
      exact hx (mem_closedBall.2 (hfsupp x h).le)
  -- `m = e^{−Λr} ωₙ rⁿ ∈ (0, ∞)`
  set m : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(Λ * r))) *
    (unitBallVolume n * ENNReal.ofReal (r ^ n))
  have hω : unitBallVolume n = volume (ball (0 : Euclid n) 1) := rfl
  have hm0 : m ≠ 0 :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (ENNReal.mul_pos (hω ▸ measure_ball_pos _ _ one_pos).ne'
        (ENNReal.ofReal_pos.2 (pow_pos hr n)).ne').ne').ne'
  have hmtop : m ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (hω ▸ measure_ball_lt_top.ne) ENNReal.ofReal_ne_top)
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
  -- for large `k`: `∫ f dμₖ ≥ μₖ(B_r(yₖ)) ≥ m`
  have hlarge : ∀ᶠ k in atTop, m.toReal ≤ ∫ x, f x ∂(μs k) := by
    filter_upwards [hK, hyk] with k hk hdk
    rw [mem_ball] at hdk
    have : IsFiniteMeasureOnCompacts (μs k) := ⟨fun K hK => (hfin k K hK).lt_top⟩
    have hmk : m ≤ μs k (ball (ys k) r) :=
      hlow k (ys k) r hr ((closedBall_subset_closedBall' (by linarith)).trans hk) (hys k)
    have hind : (ball (ys k) r).indicator (1 : Euclid P → ℝ) ≤ f := by
      intro x
      by_cases hx : x ∈ ball (ys k) r
      · rw [indicator_of_mem hx, Pi.one_apply]
        have hdx : dist x y < 2 * r := by
          linarith [dist_triangle x (ys k) y, mem_ball.1 hx]
        have : dist x y / r < 2 := (div_lt_iff₀ hr).2 (by linarith)
        exact le_max_of_le_right (by linarith)
      · rw [indicator_of_notMem hx]
        exact hf0 x
    calc m.toReal ≤ (μs k (ball (ys k) r)).toReal :=
          ENNReal.toReal_mono measure_ball_lt_top.ne hmk
      _ = ∫ x, (ball (ys k) r).indicator 1 x ∂(μs k) := by
          rw [integral_indicator_one measurableSet_ball, measureReal_def]
      _ ≤ ∫ x, f x ∂(μs k) :=
          integral_mono_of_nonneg (ae_of_all _ (indicator_nonneg fun _ _ => zero_le_one))
            (hfc.integrable_of_hasCompactSupport hfcs) (ae_of_all _ hind)
  -- in the limit `∫ f dμ ≥ m > 0`, yet `f = 0` `μ`-a.e. because `μ(B_ε(y)) = 0`
  have hlim : m.toReal ≤ ∫ x, f x ∂μ := ge_of_tendsto (hvague f hfc hfcs) hlarge
  have hzero : ∫ x, f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ0] with x hx
    by_contra h
    exact hx (mem_ball.2 ((hfsupp x h).trans_le h4r))
  linarith
/-- **Simon 7.3.3, proof of 3.3(2)** (with A.3): for closed `S`, open `D` and `β > 0`, the set of
points of `S ∩ D` that are not `β`-flat, together with `ℝᴾ ∖ D`, is closed.  Here `w` is `β`-flat
if `B_ρ(w) ⊆ D` and `sup_{y ∈ S ∩ B_ρ(w)} |q(y − w)| ≤ s < βρ` for some `ρ > 0`, some
`n`-dimensional `Q` and `q = id − p_Q` (the quantity `h(spt S, L, ρ, x)` of (3)).  Off `S` the open
set `D ∖ S` misses this set; at a flat `w ∈ S` (so `s ≥ 0`) every `w'` with
`t = |w' − w| < (βρ − s)/(1 + β)` is flat with witnesses `(ρ − t, Q, s + t)`, since `q` is linear
and `|q(v)| ≤ |v|`. -/
theorem Submission.idtp_fons_cr_nonflat_closed : ∀ (P n : ℕ) (β : ℝ) (S Dset : Set (Euclid P)), 0 < β → IsClosed S → IsOpen Dset → IsClosed (((S ∩ Dset) \ {w | ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Dset ∧ ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧ ∀ y ∈ S, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s}) ∪ Dsetᶜ) := by
  intro P n β S Dset hβ hS hD
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro w hw
  -- a point off the set lies in `D`, and is either off `S` or `β`-flat
  have hwD : w ∈ Dset := by_contra fun h => hw (Or.inr h)
  by_cases hwS : w ∈ S
  · obtain ⟨ρ, hρ, hball, Q, hQ, s, hs, hflat⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ball w ρ ⊆ Dset ∧
        ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ ∃ s : ℝ, s < β * ρ ∧
          ∀ y ∈ S, y ∈ ball w ρ → ‖(y - w) - Q.starProjection (y - w)‖ ≤ s :=
      by_contra fun h => hw (Or.inl ⟨⟨hwS, hwD⟩, h⟩)
    -- `y = w` gives `s ≥ 0`
    have hs0 : 0 ≤ s := (norm_nonneg _).trans (hflat w hwS (mem_ball_self hρ))
    refine ⟨(β * ρ - s) / (1 + β), div_pos (by linarith) (by linarith), fun w' hw' => ?_⟩
    have ht : (1 + β) * dist w' w < β * ρ - s := by
      rw [mem_ball, lt_div_iff₀ (by linarith)] at hw'
      linarith
    have ht0 : 0 ≤ dist w' w := dist_nonneg
    have htρ : dist w' w < ρ := by nlinarith
    -- `B_{ρ − t}(w') ⊆ B_ρ(w) ⊆ D`
    have hsub : ball w' (ρ - dist w' w) ⊆ ball w ρ := fun z hz => by
      rw [mem_ball] at hz ⊢
      linarith [dist_triangle z w' w]
    rintro (⟨-, hnR⟩ | hnD)
    · refine hnR ⟨ρ - dist w' w, by linarith, hsub.trans hball, Q, hQ, s + dist w' w,
        by linarith, fun y hy hyb => ?_⟩
      -- `q(y − w') = q(y − w) + q(w − w')` and `|q(w − w')| ≤ |w − w'|`
      have hlin : (y - w') - Q.starProjection (y - w') =
          ((y - w) - Q.starProjection (y - w)) + ((w - w') - Q.starProjection (w - w')) := by
        rw [show y - w' = (y - w) + (w - w') by abel, map_add]
        abel
      have hq : ‖(w - w') - Q.starProjection (w - w')‖ ≤ dist w' w := by
        rw [← Submodule.starProjection_orthogonal_val, dist_comm, dist_eq_norm]
        exact Submodule.norm_starProjection_apply_le _ _
      rw [hlin]
      exact (norm_add_le _ _).trans (add_le_add (hflat y hy (hsub hyb)) hq)
    · exact hnD (hball (mem_ball.2 htρ))
  · -- off `S`: the open set `D ∖ S` misses the set
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (hD.inter hS.isOpen_compl) w ⟨hwD, hwS⟩
    refine ⟨ε, hε, fun w' hw' => ?_⟩
    obtain ⟨hw'D, hw'S⟩ := hεsub hw'
    rintro (⟨⟨hw'S', -⟩, -⟩ | hnD)
    · exact hw'S hw'S'
    · exact hnD hw'D

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
