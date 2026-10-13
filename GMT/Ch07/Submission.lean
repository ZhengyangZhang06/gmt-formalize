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

/-- **`Hᵐ` of a ball in an `m`-dimensional subspace** (Simon Ch. 3, Remark 1.5(3): `Hᵐ` on an
`m`-plane is `m`-dimensional Lebesgue measure): if `Q ⊆ ℝᴺ` is a linear subspace with
`dim Q = m` and `s > 0`, then `Hᵐ(Q ∩ B_s(0)) = ωₘsᵐ`.  An orthonormal basis of `Q` gives a
linear isometry `ι : ℝᵐ → ℝᴺ` with `ι(B_s(0)) = Q ∩ B_s(0)`; `μHE[m]` is preserved by isometries
and equals `volume` on `ℝᵐ`, where `volume (B_s(0)) = sᵐωₘ`. -/
theorem Submission.codim1_rdo_dg_ftd_plane_ball_measure : ∀ (N m : ℕ) (Q : Submodule ℝ (Euclid N)), Module.finrank ℝ Q = m → ∀ s : ℝ, 0 < s → μHE[m] ((Q : Set (Euclid N)) ∩ ball 0 s) = unitBallVolume m * ENNReal.ofReal (s ^ m) := by
  intro N m Q hm s hs
  -- Step 1: the coordinates of an orthonormal basis of `Q` indexed by `Fin m` give
  -- `e : Q ≃ₗᵢ ℝᵐ`, and `ι = e⁻¹` followed by `Q ↪ ℝᴺ` is a linear isometry with values in `Q`
  let e : Q ≃ₗᵢ[ℝ] Euclid m := ((stdOrthonormalBasis ℝ Q).reindex (finCongr hm)).repr
  let ι : Euclid m →ₗᵢ[ℝ] Euclid N := Q.subtypeₗᵢ.comp e.symm.toLinearIsometry
  have hι : ∀ a, ι a = (e.symm a : Euclid N) := fun a => rfl
  -- Step 2: `ι(B_s(0)) = Q ∩ B_s(0)`
  have himage : ι '' ball 0 s = (Q : Set (Euclid N)) ∩ ball 0 s := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨by rw [hι]; exact (e.symm a).2, ?_⟩
      rw [mem_ball_zero_iff] at ha ⊢
      rwa [LinearIsometry.norm_map]
    · rintro ⟨hz, hzs⟩
      refine ⟨e ⟨z, hz⟩, ?_, by rw [hι, LinearIsometryEquiv.symm_apply_apply]⟩
      rw [mem_ball_zero_iff] at hzs ⊢
      rwa [LinearIsometryEquiv.norm_map]
  -- Steps 3–5: isometry invariance of `μHE[m]`, `μHE[m] = volume` on `ℝᵐ`, Haar scaling of balls
  rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_ball_of_pos (volume : Measure (Euclid m)) 0 hs, finrank_euclideanSpace_fin,
    unitBallVolume]
  -- Step 6: commute the product
  exact mul_comm _ _
/-- **Markov bound for rescaled measures** (the measure-theoretic half of the flat-tangent
density estimate): if `f ≥ 0` is continuous with compact support, `f ≥ 1` on `A`,
`μ(B̄_{r₀}(y)) < ∞`, and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → L < L'` as `r ↓ 0`, then
`μ{z : r⁻¹(z − y) ∈ A} ≤ L' rᵐ` for all small `r > 0`.  Once `r R' < r₀`, where `f = 0` off
`B̄_{R'}(0)`, the rescaled integrand is bounded and vanishes off `B̄_{r₀}(y)`, hence integrable,
and Markov's inequality at level `1` bounds the (possibly non-measurable) set by its integral. -/
theorem Submission.codim1_rdo_dg_ftd_test_upper_bound : ∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → Continuous f → HasCompactSupport f → (∀ w, 0 ≤ f w) → (∀ w ∈ A, 1 ≤ f w) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L < L' → ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {z | r⁻¹ • (z - y) ∈ A} ≤ ENNReal.ofReal (L' * r ^ m) := by
  intro N m μ y f A L L' ⟨r₀, hr₀, hfin⟩ hf hfc hf0 hA hlim hLL'
  -- a radius `R' > 0` outside of which `f` vanishes, and a bound `‖f‖ ≤ C`
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R', hR'pos, hzero⟩ : ∃ R' : ℝ, 0 < R' ∧ ∀ w : Euclid N, R' < ‖w‖ → f w = 0 := by
    refine ⟨max R 1, lt_max_of_lt_right one_pos, fun w hw => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hws => ?_
    have hwR := hR hws
    rw [mem_closedBall, dist_zero_right] at hwR
    linarith [le_max_left R 1]
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  -- eventually `r < r₀ / R'` and the rescaled integral is `< L'`
  filter_upwards [hlim (Iio_mem_nhds hLL'), Ioo_mem_nhdsGT (div_pos hr₀ hR'pos)] with r hrL hr
  have hr0 : 0 < r := hr.1
  have hrR : r * R' < r₀ := (lt_div_iff₀ hR'pos).mp hr.2
  -- `z ↦ f (r⁻¹ • (z - y))` is continuous, bounded, and vanishes off `closedBall y r₀`
  have hgc : Continuous fun z => f (r⁻¹ • (z - y)) :=
    hf.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
  have hgint : Integrable (fun z => f (r⁻¹ • (z - y))) μ := by
    have hball : IntegrableOn (fun z => f (r⁻¹ • (z - y))) (closedBall y r₀) μ :=
      Measure.integrableOn_of_bounded (M := C) hfin hgc.aestronglyMeasurable
        (Eventually.of_forall fun z => hC _)
    refine integrableOn_univ.mp (hball.of_forall_sdiff_eq_zero MeasurableSet.univ fun z hz => ?_)
    have hz' : r₀ < ‖z - y‖ := by
      have hz2 := hz.2
      rwa [mem_closedBall, dist_eq_norm, not_le] at hz2
    apply hzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0, lt_inv_mul_iff₀ hr0]
    linarith
  -- Markov's inequality at level `1`
  have hmarkov : μ {z | r⁻¹ • (z - y) ∈ A} ≤ ENNReal.ofReal (∫ z, f (r⁻¹ • (z - y)) ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall fun z => hf0 _)]
    calc μ {z | r⁻¹ • (z - y) ∈ A}
        ≤ μ {z | 1 ≤ ENNReal.ofReal (f (r⁻¹ • (z - y)))} :=
          measure_mono fun z hz => ENNReal.one_le_ofReal.mpr (hA _ hz)
      _ = 1 * μ {z | 1 ≤ ENNReal.ofReal (f (r⁻¹ • (z - y)))} := (one_mul _).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ :=
          mul_meas_ge_le_lintegral₀ hgc.measurable.ennreal_ofReal.aemeasurable 1
  refine hmarkov.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint := (inv_mul_lt_iff₀ (pow_pos hr0 m)).mp hrL
  rw [mul_comm L']
  exact hint.le
/-- **Lower bound for rescaled measures from a test function** (the lower half of the
flat-tangent density estimate): if `f` is continuous, `0 ≤ f ≤ 1`, `f = 0` off `A`, and
`r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → L > L'` as `r ↓ 0`, then `L' rᵐ ≤ μ{z : r⁻¹(z − y) ∈ A}` for all
small `r > 0`.  The rescaled integrand is dominated by the indicator of the (possibly
non-measurable) set, and a non-integrable integrand has Bochner integral `0`. -/
theorem Submission.codim1_rdo_dg_ftd_test_lower_bound : ∀ (N m : ℕ) (μ : Measure (Euclid N)) (y : Euclid N) (f : Euclid N → ℝ) (A : Set (Euclid N)) (L L' : ℝ), Continuous f → (∀ w, 0 ≤ f w) → (∀ w, f w ≤ 1) → (∀ w, w ∉ A → f w = 0) → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) → L' < L → ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (L' * r ^ m) ≤ μ {z | r⁻¹ • (z - y) ∈ A} := by
  intro N m μ y f A L L' hf hf0 hf1 hfA hlim hLL'
  -- eventually `r > 0` and the rescaled integral exceeds `L'`
  filter_upwards [hlim (Ioi_mem_nhds hLL'), self_mem_nhdsWithin] with r hrL hr
  have hint : L' * r ^ m < ∫ z, f (r⁻¹ • (z - y)) ∂μ :=
    (lt_inv_mul_iff₀' (pow_pos hr m)).mp hrL
  -- `ofReal (∫ g) ≤ ∫⁻ ofReal g`: equality if `g` is integrable, otherwise `∫ g = 0`
  have hlint : ENNReal.ofReal (∫ z, f (r⁻¹ • (z - y)) ∂μ) ≤
      ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ := by
    by_cases hg : Integrable (fun z => f (r⁻¹ • (z - y))) μ
    · exact (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall fun z => hf0 _)).le
    · rw [integral_undef hg, ENNReal.ofReal_zero]
      exact zero_le
  -- `ofReal g ≤ 1_{S_r}` pointwise, and `∫⁻ 1_{S_r} dμ ≤ μ S_r` for any set `S_r`
  have hind : ∫⁻ z, ENNReal.ofReal (f (r⁻¹ • (z - y))) ∂μ ≤
      ∫⁻ z, {z | r⁻¹ • (z - y) ∈ A}.indicator 1 z ∂μ := by
    refine lintegral_mono fun z => ?_
    show ENNReal.ofReal (f (r⁻¹ • (z - y))) ≤ {z | r⁻¹ • (z - y) ∈ A}.indicator 1 z
    by_cases hz : r⁻¹ • (z - y) ∈ A
    · rw [indicator_of_mem (show z ∈ {z | r⁻¹ • (z - y) ∈ A} from hz), Pi.one_apply]
      exact ENNReal.ofReal_le_one.mpr (hf1 _)
    · rw [hfA _ hz, ENNReal.ofReal_zero]
      exact zero_le
  exact (ENNReal.ofReal_le_ofReal hint.le).trans
    (hlint.trans (hind.trans (lintegral_indicator_one_le _)))

/-- **Ball densities of a measure with a flat tangent measure** (Simon Ch. 3, Remark 1.5(3),
first assertion, for `μ` in place of `Hⁿ⌞M`): if `P = v^⊥` (`‖v‖ = 1`), `μ(B̄_{r₀}(y)) < ∞`
and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → ∫_P f dHᵐ` as `r ↓ 0` for every continuous compactly
supported `f`, then `μ(B̄_r(y))/(ωₘrᵐ) → 1` and `μ(B_r(y))/(ωₘrᵐ) → 1`.  Since
`Hᵐ(P ∩ B_s(0)) = ωₘsᵐ`, the radial cutoffs `f₊ = 1` on `B̄₁(0)`, `= 0` off `B_{1+ε}(0)`, and
`f₋ = 1` on `B̄_{1−ε}(0)`, `= 0` off `B₁(0)`, have `∫_P f₊ ≤ ωₘ(1 + ε)ᵐ` and
`∫_P f₋ ≥ ωₘ(1 − ε)ᵐ`; the Markov-type bounds for rescaled measures then give
`ωₘcrᵐ ≤ μ(B_r(y)) ≤ μ(B̄_r(y)) ≤ ωₘCrᵐ` for small `r > 0`, for any `c < 1 < C`. -/
theorem Submission.codim1_rdo_dg_ftd_ball_density : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → Tendsto (fun r : ℝ => μ (closedBall y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) ∧ Tendsto (fun r : ℝ => μ (ball y r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 1) := by
  intro m μ y v _hm hv hr₀ hlim
  -- Step 0(a): `P = v^⊥` is an `m`-dimensional subspace of `ℝ^{m+1}`
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hv
    exact zero_ne_one hv
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hPdim : Module.finrank ℝ (Submodule.span ℝ {v})ᗮ = m :=
    Submodule.finrank_orthogonal_span_singleton hv0
  -- Step 0(b): `ωₘ = ofReal ω` with `ω > 0`
  have hω0 : unitBallVolume m ≠ 0 := by
    rw [unitBallVolume]
    exact (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume m ≠ ∞ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top.ne
  obtain ⟨ω, hωpos, hωeq⟩ : ∃ ω : ℝ, 0 < ω ∧ unitBallVolume m = ENNReal.ofReal ω :=
    ⟨(unitBallVolume m).toReal, ENNReal.toReal_pos hω0 hωtop, (ENNReal.ofReal_toReal hωtop).symm⟩
  -- Step 0(c): `ν = Hᵐ⌞P` gives `B_s(0)` the measure `ω sᵐ`
  set ν : Measure (Euclid (m + 1)) :=
    μHE[m].restrict ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))) with hν
  have hνball : ∀ s : ℝ, 0 < s → ν (ball 0 s) = ENNReal.ofReal (ω * s ^ m) := by
    intro s hs
    rw [hν, Measure.restrict_apply measurableSet_ball, inter_comm,
      Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m _ hPdim s hs, hωeq,
      ENNReal.ofReal_mul hωpos.le]
  have hνint : ∀ s : ℝ, 0 < s →
      Integrable ((ball (0 : Euclid (m + 1)) s).indicator fun _ => (1 : ℝ)) ν := by
    intro s hs
    have hfin : ν (ball 0 s) ≠ ∞ := by
      rw [hνball s hs]
      exact ENNReal.ofReal_ne_top
    exact (integrableOn_const hfin).integrable_indicator measurableSet_ball
  have hνind : ∀ s : ℝ, 0 < s →
      ∫ w, (ball (0 : Euclid (m + 1)) s).indicator (fun _ => (1 : ℝ)) w ∂ν = ω * s ^ m := by
    intro s hs
    rw [integral_indicator_const _ measurableSet_ball, measureReal_def, hνball s hs,
      ENNReal.toReal_ofReal (mul_pos hωpos (pow_pos hs m)).le, smul_eq_mul, mul_one]
  -- Step 1: comparison of `I(g) = ∫_P g dHᵐ` with plane balls
  have hle_ind : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), (∀ w, g w ≤ 1) →
      (∀ w, b ≤ ‖w‖ → g w = 0) →
      ∀ w, g w ≤ (ball (0 : Euclid (m + 1)) b).indicator (fun _ => (1 : ℝ)) w := by
    intro b g hg1 hgb w
    by_cases hw : w ∈ ball (0 : Euclid (m + 1)) b
    · rw [indicator_of_mem hw]
      exact hg1 w
    · rw [indicator_of_notMem hw, hgb w (not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h))]
  have hgint : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < b → Continuous g → (∀ w, 0 ≤ g w) →
      (∀ w, g w ≤ 1) → (∀ w, b ≤ ‖w‖ → g w = 0) → Integrable g ν := by
    intro b g hb hg hg0 hg1 hgb
    refine (hνint b hb).mono' hg.aestronglyMeasurable (Eventually.of_forall fun w => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 w)]
    exact hle_ind b g hg1 hgb w
  -- (U) `I(g) ≤ ω bᵐ` if `0 ≤ g ≤ 1` vanishes off `B_b(0)`
  have hplane_le : ∀ (b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < b → Continuous g →
      (∀ w, 0 ≤ g w) → (∀ w, g w ≤ 1) → (∀ w, b ≤ ‖w‖ → g w = 0) →
      ∫ w, g w ∂ν ≤ ω * b ^ m := fun b g hb hg hg0 hg1 hgb =>
    (integral_mono (hgint b g hb hg hg0 hg1 hgb) (hνint b hb) (hle_ind b g hg1 hgb)).trans_eq
      (hνind b hb)
  -- (L) `ω aᵐ ≤ I(g)` if moreover `g ≥ 1` on `B_a(0)`
  have hplane_ge : ∀ (a b : ℝ) (g : Euclid (m + 1) → ℝ), 0 < a → 0 < b → Continuous g →
      (∀ w, 0 ≤ g w) → (∀ w, g w ≤ 1) → (∀ w, ‖w‖ < a → 1 ≤ g w) →
      (∀ w, b ≤ ‖w‖ → g w = 0) → ω * a ^ m ≤ ∫ w, g w ∂ν := by
    intro a b g ha hb hg hg0 hg1 hga hgb
    refine (hνind a ha).symm.trans_le
      (integral_mono (hνint a ha) (hgint b g hb hg hg0 hg1 hgb) fun w => ?_)
    by_cases hw : w ∈ ball (0 : Euclid (m + 1)) a
    · rw [indicator_of_mem hw]
      exact hga w (mem_ball_zero_iff.mp hw)
    · rw [indicator_of_notMem hw]
      exact hg0 w
  -- Step 2: the radial cutoff `g_{a,b} = min 1 (max 0 ((b − ‖w‖)/(b − a)))`
  have hcut : ∀ a b : ℝ, a < b → ∃ g : Euclid (m + 1) → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ w, 0 ≤ g w) ∧ (∀ w, g w ≤ 1) ∧ (∀ w, ‖w‖ ≤ a → g w = 1) ∧
      (∀ w, b ≤ ‖w‖ → g w = 0) := by
    intro a b hab
    have hba : 0 < b - a := sub_pos.mpr hab
    have hzero : ∀ w : Euclid (m + 1), b ≤ ‖w‖ → min 1 (max 0 ((b - ‖w‖) / (b - a))) = 0 := by
      intro w hw
      rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hba.le),
        min_eq_right zero_le_one]
    refine ⟨fun w => min 1 (max 0 ((b - ‖w‖) / (b - a))), by fun_prop, ?_,
      fun w => le_min zero_le_one (le_max_left _ _), fun w => min_le_left _ _, fun w hw => ?_,
      hzero⟩
    · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) b)
        fun w hw => hzero w ?_
      rw [mem_closedBall_zero_iff, not_le] at hw
      exact hw.le
    · have h1 : 1 ≤ (b - ‖w‖) / (b - a) := by
        rw [le_div_iff₀ hba]
        linarith
      show min 1 (max 0 ((b - ‖w‖) / (b - a))) = 1
      rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1]
  -- Step 3: `{z : r⁻¹(z − y) ∈ B̄₁(0)} = B̄_r(y)` and `{z : r⁻¹(z − y) ∈ B₁(0)} = B_r(y)`
  have hset_closed : ∀ r : ℝ, 0 < r →
      {z | r⁻¹ • (z - y) ∈ closedBall (0 : Euclid (m + 1)) 1} = closedBall y r := by
    intro r hr
    ext z
    change r⁻¹ • (z - y) ∈ closedBall (0 : Euclid (m + 1)) 1 ↔ z ∈ closedBall y r
    rw [mem_closedBall_zero_iff, mem_closedBall_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_le_iff₀ hr, mul_one]
  have hset_open : ∀ r : ℝ, 0 < r →
      {z | r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) 1} = ball y r := by
    intro r hr
    ext z
    change r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) 1 ↔ z ∈ ball y r
    rw [mem_ball_zero_iff, mem_ball_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
  -- Step 4: for `C > 1`, eventually `μ(B̄_r(y)) ≤ ω C rᵐ` (test with `f₊ = g_{1,1+ε}`)
  have hupper : ∀ C : ℝ, 1 < C →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall y r) ≤ ENNReal.ofReal (ω * C * r ^ m) := by
    intro C hC
    have hcont : Continuous fun t : ℝ => (1 + t) ^ m := by fun_prop
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 + t) ^ m < C :=
      ((hcont.tendsto' 0 1 (by simp)).eventually (gt_mem_nhds hC)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨ε, hεC, hε⟩ := (hev.and self_mem_nhdsWithin).exists
    have hε0 : (0 : ℝ) < ε := hε
    obtain ⟨g, hgc, hgcs, hg0, hg1, hgone, hgzero⟩ :=
      hcut 1 (1 + ε) (lt_add_of_pos_right 1 hε0)
    have hI : ∫ w, g w ∂ν < ω * C :=
      (hplane_le (1 + ε) g (by linarith) hgc hg0 hg1 hgzero).trans_lt
        (mul_lt_mul_of_pos_left hεC hωpos)
    filter_upwards [Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y g
      (closedBall 0 1) _ (ω * C) hr₀ hgc hgcs hg0
      (fun w hw => (hgone w (mem_closedBall_zero_iff.mp hw)).ge) (hlim g hgc hgcs) hI,
      self_mem_nhdsWithin] with r hr hrpos
    rwa [hset_closed r hrpos] at hr
  -- Step 5: for `c < 1`, eventually `ω c rᵐ ≤ μ(B_r(y))` (test with `f₋ = g_{1−ε,1}`)
  have hlower : ∀ c : ℝ, c < 1 →
      ∀ᶠ r in 𝓝[>] (0 : ℝ), ENNReal.ofReal (ω * c * r ^ m) ≤ μ (ball y r) := by
    intro c hc
    have hcont : Continuous fun t : ℝ => (1 - t) ^ m := by fun_prop
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), c < (1 - t) ^ m :=
      ((hcont.tendsto' 0 1 (by simp)).eventually (lt_mem_nhds hc)).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨ε, hεc, hε⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
    have hε0 : (0 : ℝ) < ε := hε.1
    have hε1 : ε < 1 := hε.2
    obtain ⟨g, hgc, hgcs, hg0, hg1, hgone, hgzero⟩ := hcut (1 - ε) 1 (by linarith)
    have hI : ω * c < ∫ w, g w ∂ν :=
      (mul_lt_mul_of_pos_left hεc hωpos).trans_le
        (hplane_ge (1 - ε) 1 g (by linarith) one_pos hgc hg0 hg1
          (fun w hw => (hgone w hw.le).ge) hgzero)
    filter_upwards [Submission.codim1_rdo_dg_ftd_test_lower_bound (m + 1) m μ y g
      (ball 0 1) _ (ω * c) hgc hg0 hg1
      (fun w hw => hgzero w (not_lt.mp fun h => hw (mem_ball_zero_iff.mpr h)))
      (hlim g hgc hgcs) hI, self_mem_nhdsWithin] with r hr hrpos
    rwa [hset_open r hrpos] at hr
  -- Step 6: `ofReal (ω c rᵐ) / (ωₘ rᵐ) = ofReal c`
  have hratio : ∀ c : ℝ, 0 ≤ c → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (ω * c * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) =
        ENNReal.ofReal c := by
    intro c hc r hr
    have hden0 : unitBallVolume m * ENNReal.ofReal (r ^ m) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.mpr (pow_pos hr m)).ne'
    have hdentop : unitBallVolume m * ENNReal.ofReal (r ^ m) ≠ ∞ :=
      ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    rw [show ω * c * r ^ m = c * (ω * r ^ m) by ring, ENNReal.ofReal_mul hc,
      ENNReal.ofReal_mul hωpos.le, ← hωeq, ENNReal.mul_div_cancel_right hden0 hdentop]
  -- Step 7: squeeze between `B_r(y)` and `B̄_r(y)` in the order topology of `[0, ∞]`
  have hsqueeze : ∀ F : ℝ → Set (Euclid (m + 1)), (∀ r, ball y r ⊆ F r) →
      (∀ r, F r ⊆ closedBall y r) →
      Tendsto (fun r : ℝ => μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0)
        (𝓝 1) := by
    intro F hF1 hF2
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨c, hc0, hac, hc1⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
      filter_upwards [hlower c (ENNReal.ofReal_lt_one.mp hc1), self_mem_nhdsWithin]
        with r hr hrpos
      calc a < ENNReal.ofReal c := hac
        _ = ENNReal.ofReal (ω * c * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
          (hratio c hc0 r hrpos).symm
        _ ≤ μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
          ENNReal.div_le_div_right (hr.trans (measure_mono (hF1 r))) _
    · obtain ⟨C, hC0, h1C, hCb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
      filter_upwards [hupper C (ENNReal.one_lt_ofReal.mp h1C), self_mem_nhdsWithin]
        with r hr hrpos
      calc μ (F r) / (unitBallVolume m * ENNReal.ofReal (r ^ m))
          ≤ ENNReal.ofReal (ω * C * r ^ m) / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
            ENNReal.div_le_div_right ((measure_mono (hF2 r)).trans hr) _
        _ = ENNReal.ofReal C := hratio C hC0 r hrpos
        _ < b := hCb
  exact ⟨hsqueeze (closedBall y) (fun _ => ball_subset_closedBall) (fun _ => subset_rfl),
    hsqueeze (ball y) (fun _ => subset_rfl) (fun _ => ball_subset_closedBall)⟩

/-- **The double cone around the normal has density zero** (Simon Ch. 3, Remark 1.5(3), second
assertion): if `‖v‖ = 1`, `P = v^⊥`, `μ(B̄_{r₀}(y)) < ∞` and `r⁻ᵐ ∫ f(r⁻¹(z − y)) dμ(z) → ∫_P f dHᵐ`
as `r ↓ 0` for every continuous compactly supported `f`, then for every `α > 0`
`μ({z : α‖z − y‖ ≤ |⟨z − y, v⟩|} ∩ B̄_r(y)) / rᵐ → 0` (`m ≥ 1`).  With
`K = {w : α‖w‖ ≤ |⟨w, v⟩|} ∩ B̄₁(0)`, the test function `g = (1 − dist(·, K)/θ)⁺` is `1` on `K` and
vanishes at points of `P` outside `B_{θ(1+1/α)}(0)`, so `∫_P g dHᵐ ≤ ωₘ(θ(1 + 1/α))ᵐ`; the Markov
bound then gives `μ(cone ∩ B̄_r(y)) ≤ (ωₘ(θ(1 + 1/α))ᵐ + θ) rᵐ` for small `r`, and `θ ↓ 0`. -/
theorem Submission.codim1_rdo_dg_ftd_cone_density : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (y v : Euclid (m + 1)), 1 ≤ m → ‖v‖ = 1 → (∃ r₀ : ℝ, 0 < r₀ ∧ μ (closedBall y r₀) ≠ ∞) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), f z ∂μHE[m]))) → ∀ α : ℝ, 0 < α → Tendsto (fun r : ℝ => μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r) / ENNReal.ofReal (r ^ m)) (𝓝[>] 0) (𝓝 0) := by
  intro m μ y v hm hv hfin hconv α hα
  -- Step 0: `P = v^⊥` is a closed `m`-dimensional subspace, and `(Hᵐ⌞P)(B_s(0)) = ωₘ sᵐ`
  set P : Submodule ℝ (Euclid (m + 1)) := (Submodule.span ℝ {v})ᗮ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hv
    exact zero_ne_one hv
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hPdim : Module.finrank ℝ P = m := Submodule.finrank_orthogonal_span_singleton hv0
  have hPmeas : MeasurableSet (P : Set (Euclid (m + 1))) :=
    P.closed_of_finiteDimensional.measurableSet
  have hωfin : unitBallVolume m ≠ ∞ := measure_ball_lt_top.ne
  set ω : ℝ := (unitBallVolume m).toReal
  have hω0 : 0 ≤ ω := ENNReal.toReal_nonneg
  have hωeq : unitBallVolume m = ENNReal.ofReal ω := (ENNReal.ofReal_toReal hωfin).symm
  have hball : ∀ s : ℝ, 0 < s →
      μHE[m].restrict (P : Set (Euclid (m + 1))) (ball 0 s) = ENNReal.ofReal (ω * s ^ m) := by
    intro s hs
    rw [Measure.restrict_apply measurableSet_ball, inter_comm,
      Submission.codim1_rdo_dg_ftd_plane_ball_measure (m + 1) m P hPdim s hs, hωeq,
      ← ENNReal.ofReal_mul hω0]
  -- Step 8: it suffices to bound the ratio eventually by each `ε ∈ (0, ∞)`
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact Eventually.of_forall fun r => hεtop ▸ le_top
  have ht : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  -- since `m ≥ 1`, `ωₘ(θ(1 + α⁻¹))ᵐ + θ → 0` as `θ → 0`; pick `θ > 0` with this `< ε`
  have hφ : Tendsto (fun θ : ℝ => ω * (θ * (1 + α⁻¹)) ^ m + θ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun θ : ℝ => ω * (θ * (1 + α⁻¹)) ^ m + θ := by fun_prop
    have h0 := hc.tendsto 0
    rw [zero_mul, zero_pow (by omega), mul_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  obtain ⟨θ, hθt, hθmem⟩ := ((hφ.eventually (gt_mem_nhds ht)).and self_mem_nhdsWithin).exists
  have hθ : 0 < θ := hθmem
  set ρ : ℝ := θ * (1 + α⁻¹) with hρ
  have hρpos : 0 < ρ := mul_pos hθ (add_pos one_pos (inv_pos.mpr hα))
  -- Step 1: the cone `K` in the closed unit ball contains `0`
  set K : Set (Euclid (m + 1)) := {w | α * ‖w‖ ≤ |inner ℝ w v|} ∩ closedBall 0 1
  have hKne : K.Nonempty := ⟨0, by simp [K]⟩
  -- Step 2: `g = (1 − dist(·, K)/θ)⁺` is continuous, `0 ≤ g ≤ 1`, `g = 1` on `K`, and `g(w) ≠ 0`
  -- forces `dist(w, k) < θ` for some `k ∈ K`
  set g : Euclid (m + 1) → ℝ := fun w => max 0 (1 - infDist w K / θ)
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const θ))
  have hg0 : ∀ w, 0 ≤ g w := fun w => le_max_left _ _
  have hg1 : ∀ w, g w ≤ 1 := fun w =>
    max_le zero_le_one (by linarith [div_nonneg (infDist_nonneg (x := w) (s := K)) hθ.le])
  have hgK : ∀ w ∈ K, 1 ≤ g w := fun w hw =>
    le_max_of_le_right (by rw [infDist_zero_of_mem hw, zero_div, sub_zero])
  have hgne : ∀ w, g w ≠ 0 → ∃ k ∈ K, dist w k < θ := by
    intro w hw
    rw [← infDist_lt_iff hKne]
    by_contra hcon
    have h1 : 1 ≤ infDist w K / θ := by
      rw [le_div_iff₀ hθ, one_mul]
      exact not_lt.mp hcon
    exact hw (max_eq_left (by linarith))
  -- Step 3: `g` vanishes outside `B̄_{1+θ}(0)`, so it has compact support
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) (1 + θ))
      fun w hw => ?_
    by_contra hne
    obtain ⟨k, hk, hwk⟩ := hgne w hne
    rw [dist_eq_norm] at hwk
    have hk1 : ‖k‖ ≤ 1 := mem_closedBall_zero_iff.mp hk.2
    apply hw
    rw [mem_closedBall_zero_iff]
    calc ‖w‖ = ‖(w - k) + k‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - k‖ + ‖k‖ := norm_add_le _ _
      _ ≤ 1 + θ := by linarith
  -- Step 4: on `P`, `g(w) ≠ 0` forces `‖w‖ < ρ = θ(1 + α⁻¹)` (Cauchy–Schwarz, `⟨w, v⟩ = 0`)
  have hgP : ∀ w ∈ P, ρ ≤ ‖w‖ → g w = 0 := by
    intro w hwP hwρ
    by_contra hne
    obtain ⟨k, hk, hwk⟩ := hgne w hne
    rw [dist_eq_norm] at hwk
    have hwv : inner ℝ w v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hwP
    have hαk : α * ‖k‖ < θ :=
      calc α * ‖k‖ ≤ |inner ℝ k v| := hk.1
        _ = |inner ℝ (k - w) v| := by rw [inner_sub_left, hwv, sub_zero]
        _ ≤ ‖k - w‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ = ‖w - k‖ := by rw [hv, mul_one, norm_sub_rev]
        _ < θ := hwk
    have hkθ : ‖k‖ < θ * α⁻¹ := by
      rw [← div_eq_mul_inv, lt_div_iff₀ hα]
      linarith
    have hwρ' : ‖w‖ < ρ :=
      calc ‖w‖ = ‖(w - k) + k‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - k‖ + ‖k‖ := norm_add_le _ _
        _ < θ + θ * α⁻¹ := add_lt_add hwk hkθ
        _ = ρ := by rw [hρ]; ring
    linarith
  -- Step 5: `∫_P g dHᵐ ≤ ∫_P 1_{B_ρ(0)} dHᵐ = ωₘ ρᵐ`
  have hIg : ∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m] ≤ ω * ρ ^ m := by
    have hint : Integrable ((ball (0 : Euclid (m + 1)) ρ).indicator (1 : Euclid (m + 1) → ℝ))
        (μHE[m].restrict (P : Set (Euclid (m + 1)))) := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact integrableOn_const (by rw [hball ρ hρpos]; exact ENNReal.ofReal_ne_top)
    calc ∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m]
        ≤ ∫ z in (P : Set (Euclid (m + 1))),
            (ball (0 : Euclid (m + 1)) ρ).indicator 1 z ∂μHE[m] := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w => hg0 w) hint ?_
          rw [EventuallyLE, ae_restrict_iff' hPmeas]
          refine Eventually.of_forall fun w hwP => ?_
          by_cases hwb : w ∈ ball (0 : Euclid (m + 1)) ρ
          · rw [indicator_of_mem hwb, Pi.one_apply]
            exact hg1 w
          · rw [indicator_of_notMem hwb, hgP w hwP (by rwa [mem_ball_zero_iff, not_lt] at hwb)]
      _ = ω * ρ ^ m := by
          rw [integral_indicator_one measurableSet_ball, measureReal_def, hball ρ hρpos,
            ENNReal.toReal_ofReal (mul_nonneg hω0 (pow_nonneg hρpos.le m))]
  -- Step 6: the Markov bound for `g` and `K`, with `L' = ωₘ ρᵐ + θ`
  have hev := Submission.codim1_rdo_dg_ftd_test_upper_bound (m + 1) m μ y g K
    (∫ z in (P : Set (Euclid (m + 1))), g z ∂μHE[m]) (ω * ρ ^ m + θ) hfin hgc hgcs hg0 hgK
    (hconv g hgc hgcs) (by linarith)
  -- Steps 7–8: the cone in `B̄_r(y)` rescales into `K`, so the ratio is eventually `≤ ε`
  filter_upwards [hev, self_mem_nhdsWithin] with r hr hrmem
  have hr0 : 0 < r := hrmem
  have hincl : {z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r ⊆
      {z | r⁻¹ • (z - y) ∈ K} := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨?_, ?_⟩
    · show α * ‖r⁻¹ • (z - y)‖ ≤ |inner ℝ (r⁻¹ • (z - y)) v|
      rw [norm_smul, real_inner_smul_left, abs_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      calc α * (r⁻¹ * ‖z - y‖) = r⁻¹ * (α * ‖z - y‖) := by ring
        _ ≤ r⁻¹ * |inner ℝ (z - y) v| := mul_le_mul_of_nonneg_left hz1 (inv_nonneg.mpr hr0.le)
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0,
        inv_mul_le_iff₀ hr0, mul_one]
      rwa [mem_closedBall, dist_eq_norm] at hz2
  refine ENNReal.div_le_of_le_mul ?_
  calc μ ({z | α * ‖z - y‖ ≤ |inner ℝ (z - y) v|} ∩ closedBall y r)
      ≤ μ {z | r⁻¹ • (z - y) ∈ K} := measure_mono hincl
    _ ≤ ENNReal.ofReal ((ω * ρ ^ m + θ) * r ^ m) := hr
    _ ≤ ENNReal.ofReal (ε.toReal * r ^ m) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hθt.le (pow_nonneg hr0.le m))
    _ = ε * ENNReal.ofReal (r ^ m) := by
        rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hεtop]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
