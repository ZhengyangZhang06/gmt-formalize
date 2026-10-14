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

/-- Directional derivatives of test forms are test forms: if `φ ∈ 𝒟^q(ℝᴾ)` and `v ∈ ℝᴾ`, then
`z ↦ Dφ(z)[v]` is again `C^∞` (`Dφ` is `C^∞`, as `∞ + 1 ≤ ∞`) with compact support
(`spt Dφ ⊆ spt φ`, and evaluation at `v` maps `0` to `0`). -/
theorem Submission.dimred_cs_sos_mt_cs_isTestForm_fderiv_apply : ∀ (P q : ℕ) (φ : DifferentialForm (Euclid P) q) (v : Euclid P), IsTestForm φ → IsTestForm (fun z => fderiv ℝ φ z v) := by
  rintro P q φ v ⟨hs, hc⟩
  refine ⟨?_, ?_⟩
  · -- `Dφ` is `C^∞`, hence so is its evaluation at the constant vector `v`
    exact (hs.fderiv_right (by simp)).clm_apply contDiff_const
  · -- `Dφ` has compact support, and `L ↦ L v` maps `0` to `0`
    exact (hc.fderiv ℝ).comp_left (g := fun L : Euclid P →L[ℝ] Covector (Euclid P) q => L v) rfl
/-- **Splitting the contracted exterior derivative** (Step 1 of the cube Stokes formula in the proof
of Simon 7.3.5, where minimality passes from `[[L]] × S₀` to `S₀`).  Let `g = (g₀, …, g_j)` be
vectors in `ℝᴾ` and let `flatD`, `flat`, `flatF a` contract covectors with `g`, resp. with `g`
without `g_a`: `flatD α v = α(g, v)`, `flat α v = α(g, v)`, `flatF a α v = α(g ∘ a.succAbove, v)`.
If the `n'`-form `ω` is differentiable at `x`, then
`flatD(dω(x)) = Σₐ (−1)ᵃ D[flatF a ∘ ω](x)[g_a] + (−1)^{j+1} d[flat ∘ ω](x)`.
Evaluate at a tuple `w` and put `V = (g, w)`.  As `dω(x)(V) = Σᵢ (−1)ⁱ (Dω(x)[Vᵢ])(V without Vᵢ)`,
`D[flatF a ∘ ω](x) = flatF a ∘ Dω(x)` and `D[flat ∘ ω](x) = flat ∘ Dω(x)`, both sides are
alternating sums of values of `Dω(x)`.  Split the sum over `i < n' + 1` at `j + 1`: the index
`a < j + 1` carries `g_a`, and omitting it leaves `(g ∘ a.succAbove, w)`; the index `j + 1 + l`
carries `w_l`, and omitting it leaves `(g, w without w_l)`, with sign `(−1)^{j+1}(−1)ˡ`. -/
theorem Submission.dimred_cs_sos_mt_cs_flat_extDeriv_split : ∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h : n' = (j + 1) + m) (h₁ : n' + 1 = (j + 1) + (m + 1)) (h₂ : n' = j + (m + 1)) (flatD : Covector (Euclid P) (n' + 1) →L[ℝ] Covector (Euclid P) (m + 1)) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m) (flatF : Fin (j + 1) → Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) (m + 1)) (ω : DifferentialForm (Euclid P) n') (x : Euclid P), DifferentiableAt ℝ ω x → (∀ (α : Covector (Euclid P) (n' + 1)) (v : Fin (m + 1) → Euclid P), flatD α v = α (Fin.append g v ∘ Fin.cast h₁)) → (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → flatD (exteriorDerivative ω x) = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) • fderiv ℝ (fun z => flatF a (ω z)) x (g a) + (-1 : ℝ) ^ (j + 1) • exteriorDerivative (fun z => flat (ω z)) x := by
  intro P j m n' g h h₁ h₂ flatD flat flatF ω x hω hflatD hflat hflatF
  -- Step 1: chain rule, `D[flatF a ∘ ω](x) = flatF a ∘ Dω(x)` and `D[flat ∘ ω](x) = flat ∘ Dω(x)`
  have hβ : ∀ a, fderiv ℝ (fun z => flatF a (ω z)) x = (flatF a).comp (fderiv ℝ ω x) := fun a =>
    ((flatF a).hasFDerivAt.comp x hω.hasFDerivAt).fderiv
  have hγ : fderiv ℝ (fun z => flat (ω z)) x = flat.comp (fderiv ℝ ω x) :=
    (flat.hasFDerivAt.comp x hω.hasFDerivAt).fderiv
  -- Step 5: value formulas for `Fin.append` and `Fin.succAbove`
  have happL : ∀ {p q : ℕ} (u : Fin p → Euclid P) (v : Fin q → Euclid P) (k : Fin (p + q))
      (hk : (k : ℕ) < p), Fin.append u v k = u ⟨k, hk⟩ := fun u v k hk =>
    Fin.append_left u v ⟨k, hk⟩
  have happR : ∀ {p q : ℕ} (u : Fin p → Euclid P) (v : Fin q → Euclid P) (k : Fin (p + q))
      (hk : p ≤ (k : ℕ)), Fin.append u v k = v ⟨k - p, by have := k.isLt; omega⟩ := by
    intro p q u v k hk
    rw [← Fin.append_right u v ⟨k - p, by have := k.isLt; omega⟩]
    congr 1
    ext
    simp only [Fin.val_natAdd]
    omega
  have hsA : ∀ {N : ℕ} (p : Fin (N + 1)) (i : Fin N),
      ((p.succAbove i : Fin (N + 1)) : ℕ) = if (i : ℕ) < p then (i : ℕ) else i + 1 := by
    intro N p i
    rcases Nat.lt_or_ge (i : ℕ) p with hip | hip
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 hip), ite_eq_left hip]
      rfl
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 hip), ite_eq_right (by omega)]
      rfl
  -- Steps 2–4: evaluate at `w`; both sides become alternating sums of values of `Dω(x)`
  ext w
  rw [hflatD]
  simp only [exteriorDerivative, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, hβ, hγ, ContinuousLinearMap.comp_apply, hflatF, hflat]
  -- Step 7: omitting the index of value `a` from `V = (g, w)` leaves `(g ∘ a.succAbove, w)`
  have e2 : ∀ (a : Fin (j + 1)) (i : Fin (n' + 1)), (i : ℕ) = a →
      i.removeNth (Fin.append g w ∘ Fin.cast h₁) =
        Fin.append (g ∘ a.succAbove) w ∘ Fin.cast h₂ := by
    intro a i hi
    funext l
    have ha := a.isLt
    have hs := hsA i l
    rw [hi] at hs
    simp only [Fin.removeNth, Function.comp_apply]
    rcases Nat.lt_or_ge (l : ℕ) j with hlj | hlj
    · have hk1 : (Fin.cast h₂ l : ℕ) < j := by simpa using hlj
      have hk2 : (Fin.cast h₁ (i.succAbove l) : ℕ) < j + 1 := by
        rw [Fin.val_cast, hs]; split_ifs <;> omega
      rw [happL _ _ _ hk1, happL _ _ _ hk2, Function.comp_apply]
      congr 1
      ext
      simp only [Fin.val_cast, hs, hsA]
    · have hla : ¬ (l : ℕ) < a := by omega
      rw [ite_eq_right hla] at hs
      have hk1 : j ≤ (Fin.cast h₂ l : ℕ) := by simpa using hlj
      have hk2 : j + 1 ≤ (Fin.cast h₁ (i.succAbove l) : ℕ) := by
        rw [Fin.val_cast, hs]; omega
      rw [happR _ _ _ hk1, happR _ _ _ hk2]
      congr 1
      ext
      simp only [Fin.val_cast, hs]
      omega
  -- Step 8: omitting the index of value `j + 1 + l` from `V = (g, w)` leaves `(g, w without w_l)`
  have e4 : ∀ (l : Fin (m + 1)) (i : Fin (n' + 1)), (i : ℕ) = j + 1 + l →
      i.removeNth (Fin.append g w ∘ Fin.cast h₁) = Fin.append g (l.removeNth w) ∘ Fin.cast h := by
    intro l i hi
    funext k
    have hs := hsA i k
    rw [hi] at hs
    simp only [Fin.removeNth, Function.comp_apply]
    rcases Nat.lt_or_ge (k : ℕ) (j + 1) with hkj | hkj
    · rw [ite_eq_left (by omega)] at hs
      have hk1 : (Fin.cast h k : ℕ) < j + 1 := by simpa using hkj
      have hk2 : (Fin.cast h₁ (i.succAbove k) : ℕ) < j + 1 := by
        rw [Fin.val_cast, hs]; omega
      rw [happL _ _ _ hk1, happL _ _ _ hk2]
      congr 1
      ext
      simp only [Fin.val_cast, hs]
    · have hk1 : j + 1 ≤ (Fin.cast h k : ℕ) := by simpa using hkj
      have hk2 : j + 1 ≤ (Fin.cast h₁ (i.succAbove k) : ℕ) := by
        rw [Fin.val_cast, hs]; split_ifs <;> omega
      rw [happR _ _ _ hk1, happR _ _ _ hk2]
      congr 1
      ext
      simp only [Fin.val_cast, hs, hsA]
      split_ifs <;> omega
  -- Step 6: reindex along `Fin.cast h₁` and split the sum at `j + 1`
  rw [← Fin.sum_congr' _ h₁.symm, Fin.sum_univ_add (a := j + 1) (b := m + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hi : (((Fin.castAdd (m + 1) a).cast h₁.symm : Fin (n' + 1)) : ℕ) = a := by simp
    rw [e2 a _ hi]
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_left, hi,
      zsmul_eq_mul, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  · -- the sign `(−1)^{(j+1)+l} = (−1)^{j+1}(−1)^l`
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hi : (((Fin.natAdd (j + 1) l).cast h₁.symm : Fin (n' + 1)) : ℕ) = j + 1 + l := by simp
    rw [e4 l _ hi]
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right, hi,
      zsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
/-- **Interior product with a frame; translated test forms.**  (a) For `g = (g₁, …, g_k)` in
`ℝᴾ` and `n' = k + m`, `♭α(v) = α(g₁, …, g_k, v₁, …, v_m)` defines a continuous linear map
`♭ : Λ^{n'} → Λ^m`.  Updating `vⱼ` updates only the entry `natAdd k j` of `(g, v)`, so `♭α` is
multilinear; it is alternating because equal entries of `v` stay at distinct indices; it is
continuous; and `‖♭α‖ ≤ (∏ᵢ ‖gᵢ‖) ‖α‖`, so `α ↦ ♭α` is bounded (`LinearMap.mkContinuous`).
(b) For a continuous linear `Φ : Λᵃ → Λᵇ`, a test `a`-form `ω` and `t ∈ ℝᴾ`, `y ↦ Φ(ω(t + y))`
is smooth and vanishes off the closed set `{y : t + y ∈ spt ω}`, the compact translate
`spt ω − t`; hence it is a test form supported there.  This is the interior product `♭_g` of
the product construction `[[E]] ×_g A` used to split off the spine of a cone. -/
theorem Submission.dimred_cs_sos_mt_interior_product : ∀ P : ℕ, (∀ (k m n' : ℕ) (g : Fin k → Euclid P) (h : n' = k + m), ∃ flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m, ∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) ∧ ∀ (a b : ℕ) (flat : Covector (Euclid P) a →L[ℝ] Covector (Euclid P) b) (ω : DifferentialForm (Euclid P) a) (t : Euclid P), IsTestForm ω → IsTestForm (fun y => flat (ω (t + y))) ∧ tsupport (fun y => flat (ω (t + y))) ⊆ (fun y => t + y) ⁻¹' tsupport ω := by
  intro P
  refine ⟨fun k m n' g h => ?_, fun a b flat ω t hω => ?_⟩
  · -- (a) the interior product with the frame `g`; first identify `n'` with `k + m`
    subst h
    -- the entries `castAdd m i` (from `g`) and `natAdd k j` (from `v`) are distinct
    have hne : ∀ (i : Fin k) (j : Fin m), Fin.castAdd m i ≠ Fin.natAdd k j := by
      intro i j hc
      have hv := congrArg Fin.val hc
      have hi := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    -- updating `v` at `j` updates `Fin.append g v` at `natAdd k j` (for any `DecidableEq`)
    have hupd : ∀ (_ : DecidableEq (Fin m)) (v : Fin m → Euclid P) (j : Fin m) (x : Euclid P),
        Fin.append g (Function.update v j x) =
          Function.update (Fin.append g v) (Fin.natAdd k j) x := by
      intro _ v j x
      funext z
      induction z using Fin.addCases with
      | left i => rw [Fin.append_left, Function.update_of_ne (hne i j), Fin.append_left]
      | right j' =>
        rw [Fin.append_right, Function.update_apply_of_injective _ (Fin.natAdd_injective m k)]
        congr 1
        funext i
        rw [Fin.append_right]
    -- `v ↦ Fin.append g v` is continuous: each entry is a constant `gᵢ` or a projection `vⱼ`
    have hcont : Continuous fun v : Fin m → Euclid P => Fin.append g v := by
      refine continuous_pi fun z => ?_
      induction z using Fin.addCases with
      | left i => simp only [Fin.append_left]; exact continuous_const
      | right j => simp only [Fin.append_right]; exact continuous_apply j
    -- `♭α (v) = α (g, v)` is a continuous alternating map
    let φ : Covector (Euclid P) (k + m) → Covector (Euclid P) m := fun α =>
      { toFun := fun v => α (Fin.append g v)
        map_update_add' := fun v j x y => by
          simp only [hupd _ v j, α.map_update_add]
        map_update_smul' := fun v j c x => by
          simp only [hupd _ v j, α.map_update_smul]
        cont := α.cont.comp hcont
        map_eq_zero_of_eq' := fun v i j hv hij =>
          α.map_eq_zero_of_eq (Fin.append g v) (i := Fin.natAdd k i) (j := Fin.natAdd k j)
            (by rw [Fin.append_right, Fin.append_right]; exact hv)
            ((Fin.natAdd_injective m k).ne hij) }
    have hφ : ∀ α v, φ α v = α (Fin.append g v) := fun α v => rfl
    -- `α ↦ ♭α` is linear
    let L : Covector (Euclid P) (k + m) →ₗ[ℝ] Covector (Euclid P) m :=
      { toFun := φ
        map_add' := fun α β => by
          ext v
          simp only [hφ, ContinuousAlternatingMap.add_apply]
        map_smul' := fun c α => by
          ext v
          simp only [hφ, ContinuousAlternatingMap.smul_apply, RingHom.id_apply] }
    -- and bounded: `|α (g, v)| ≤ ‖α‖ ∏ᵢ ‖gᵢ‖ ∏ⱼ ‖vⱼ‖`, so `‖♭α‖ ≤ (∏ᵢ ‖gᵢ‖) ‖α‖`
    have hbound : ∀ α, ‖L α‖ ≤ (∏ i, ‖g i‖) * ‖α‖ := by
      intro α
      refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
      calc ‖L α v‖ = ‖α (Fin.append g v)‖ := rfl
        _ ≤ ‖α‖ * ∏ z, ‖Fin.append g v z‖ := α.le_opNorm _
        _ = (∏ i, ‖g i‖) * ‖α‖ * ∏ j, ‖v j‖ := by
          rw [Fin.prod_univ_add]
          simp only [Fin.append_left, Fin.append_right]
          ring
    refine ⟨L.mkContinuous (∏ i, ‖g i‖) hbound, fun α v => ?_⟩
    rw [LinearMap.mkContinuous_apply, Fin.cast_refl, Function.comp_id]
    rfl
  · -- (b) off `{y : t + y ∈ spt ω}` the form `ω (t + y)` vanishes, hence so does its image
    have hsub : tsupport (fun y => flat (ω (t + y))) ⊆ (fun y => t + y) ⁻¹' tsupport ω := by
      refine closure_minimal (fun y hy => ?_)
        ((isClosed_tsupport ω).preimage (continuous_const.add continuous_id))
      by_contra hy'
      apply hy
      show flat (ω (t + y)) = 0
      rw [image_eq_zero_of_notMem_tsupport (f := ω) (x := t + y) hy', map_zero]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := hω.1
    -- `{y : t + y ∈ spt ω}` is the compact translate `spt ω − t`
    have hK : IsCompact ((fun y => t + y) ⁻¹' tsupport ω) := by
      have hK' := (Homeomorph.addLeft t).isCompact_preimage.mpr hω.2
      rwa [Homeomorph.coe_addLeft] at hK'
    refine ⟨⟨?_, ?_⟩, hsub⟩
    · exact flat.contDiff.comp (hs.comp (contDiff_const.add contDiff_id))
    · exact hK.of_isClosed_subset (isClosed_tsupport _) hsub

/-- **Boundary on translated forms.**  If `∂Y = X` in `ℝᴾ`, `γ` is a test `m`-form and
`t ∈ ℝᴾ`, then `Y(d(γ(t + ·))) = X(γ(t + ·))`, both sides read by `currentEval`.  The translate
`γₜ = γ(t + ·)` is a test form (`dimred_cs_sos_mt_interior_product` (b) with `Φ = id`), and
translation commutes with `d`: `D(γ(t + ·))(y) = Dγ(t + y)` (`fderiv_comp_add_left`), so
`dγₜ = (dγ)(t + ·)`.  Hence both arguments are test forms supported in `ℝᴾ`, `currentEval`
evaluates the currents on them, and `Y(dγₜ) = ∂Y(γₜ) = X(γₜ)`. -/
theorem Submission.dimred_cs_sos_mt_cs_translate_boundary_eval : ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (γ : DifferentialForm (Euclid P) m) (t : Euclid P), Y.boundary = X → IsTestForm γ → currentEval Y (fun y => exteriorDerivative γ (t + y)) = currentEval X (fun y => γ (t + y)) := by
  intro P m X Y γ t hYX hγ
  subst hYX
  -- the translate `γₜ = γ(t + ·)` is a test form (interior product (b) with `Φ = id`)
  have hγt : IsTestForm (fun y => γ (t + y)) :=
    ((Submission.dimred_cs_sos_mt_interior_product P).2 m m
      (ContinuousLinearMap.id ℝ (Covector (Euclid P) m)) γ t hγ).1
  -- translation commutes with `d`, since `D(γ(t + ·))(y) = Dγ(t + y)`
  have hd : exteriorDerivative (fun y => γ (t + y)) = fun y => exteriorDerivative γ (t + y) := by
    funext y
    show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => γ (t + y)) y) =
      ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ γ (t + y))
    rw [fderiv_comp_add_left]
  -- both forms are test forms supported in `ℝᴾ`, so `currentEval` evaluates on them
  have hmem : IsTestForm (fun y => γ (t + y)) ∧ tsupport (fun y => γ (t + y)) ⊆ univ :=
    ⟨hγt, subset_univ _⟩
  have hdmem : IsTestForm (fun y => exteriorDerivative γ (t + y)) ∧
      tsupport (fun y => exteriorDerivative γ (t + y)) ⊆ univ :=
    ⟨hd ▸ exteriorDerivative_isTestForm hγt, subset_univ _⟩
  -- unfold `currentEval`; `∂Y(γₜ) = Y(dγₜ)` and `dγₜ = (dγ)(t + ·)` as test forms
  rw [currentEval, currentEval, dite_eq_left hdmem, dite_eq_left hmem,
    GeometricCurrentOn.boundary_apply]
  exact congrArg Y (Subtype.ext hd.symm)

/-- **Slice identity for one translate.**  Write `β_a = ♭_{g ∘ a.succAbove} ω`, `γ = ♭_g ω` and
`δ_a = D_{g_a} β_a`.  At every point `t + y` the contraction of `dω` with the frame splits as
`♭_g dω = Σ_a (−1)^a δ_a + (−1)^{j+1} dγ` (`flat_extDeriv_split`).  Every translated form here
is a test form (interior product (b), `isTestForm_fderiv_apply`, `exteriorDerivative_isTestForm`),
so `Y` evaluates the splitting linearly, and the last term is
`Y(dγ(t + ·)) = ∂Y(γ(t + ·)) = X(γ(t + ·))` (`translate_boundary_eval`). -/
theorem Submission.dimred_cs_sos_mt_cs_slice_identity : ∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h : n' = (j + 1) + m) (h₁ : n' + 1 = (j + 1) + (m + 1)) (h₂ : n' = j + (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (flatD : Covector (Euclid P) (n' + 1) →L[ℝ] Covector (Euclid P) (m + 1)) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m) (flatF : Fin (j + 1) → Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) n') (t : Euclid P), Y.boundary = X → (∀ (α : Covector (Euclid P) (n' + 1)) (v : Fin (m + 1) → Euclid P), flatD α v = α (Fin.append g v ∘ Fin.cast h₁)) → (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → currentEval Y (fun y => flatD (exteriorDerivative (ω : DifferentialForm (Euclid P) n') (t + y))) = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) * currentEval Y (fun y => fderiv ℝ (fun z => flatF a ((ω : DifferentialForm (Euclid P) n') z)) (t + y) (g a)) + (-1 : ℝ) ^ (j + 1) * currentEval X (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) := by
  intro P j m n' g h h₁ h₂ X Y flatD flat flatF ω t hYX hD hflat hF
  -- `currentEval` is the current itself on test forms (every support lies in `univ`)
  have hev : ∀ (k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (φ : DifferentialForm (Euclid P) k) (hφ : IsTestForm φ ∧ tsupport φ ⊆ univ),
      currentEval T φ = T ⟨φ, hφ⟩ := by
    intro k T φ hφ
    rw [currentEval, dite_eq_left hφ]
  -- work with the underlying form `w` of `ω`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n') := ω.property.1
  generalize (ω : DifferentialForm (Euclid P) n') = w at hω ⊢
  -- `β_a = flatF a ∘ w` and `γ = flat ∘ w` are test forms (interior product (b), translate by `0`)
  have hβ : ∀ a : Fin (j + 1), IsTestForm (fun z => flatF a (w z)) := fun a => by
    simpa only [zero_add] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 n' (m + 1) (flatF a) w 0 hω).1
  have hγ : IsTestForm (fun z => flat (w z)) := by
    simpa only [zero_add] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 n' m flat w 0 hω).1
  -- the translates `♭_g dw (t + ·)`, `δ_a (t + ·)` and `dγ (t + ·)` are test forms
  have hFt : IsTestForm (fun y => flatD (exteriorDerivative w (t + y))) :=
    ((Submission.dimred_cs_sos_mt_interior_product P).2 (n' + 1) (m + 1) flatD _ t
      (exteriorDerivative_isTestForm hω)).1
  have hAt : ∀ a : Fin (j + 1),
      IsTestForm (fun y => fderiv ℝ (fun z => flatF a (w z)) (t + y) (g a)) := fun a => by
    simpa only [ContinuousLinearMap.id_apply] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 (m + 1) (m + 1)
        (ContinuousLinearMap.id ℝ _) _ t
        (Submission.dimred_cs_sos_mt_cs_isTestForm_fderiv_apply P (m + 1) _ (g a) (hβ a))).1
  have hDt : IsTestForm (fun y => exteriorDerivative (fun z => flat (w z)) (t + y)) := by
    simpa only [ContinuousLinearMap.id_apply] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 (m + 1) (m + 1)
        (ContinuousLinearMap.id ℝ _) _ t (exteriorDerivative_isTestForm hγ)).1
  -- the pointwise splitting at `t + y`, read as an identity of test forms in `ℝᴾ`
  have hsplit : (⟨fun y => flatD (exteriorDerivative w (t + y)), hFt, subset_univ _⟩ :
        TestFormOn (univ : Set (Euclid P)) (m + 1)) =
      ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) •
        (⟨fun y => fderiv ℝ (fun z => flatF a (w z)) (t + y) (g a), hAt a, subset_univ _⟩ :
          TestFormOn (univ : Set (Euclid P)) (m + 1)) +
      (-1 : ℝ) ^ (j + 1) •
        (⟨fun y => exteriorDerivative (fun z => flat (w z)) (t + y), hDt, subset_univ _⟩ :
          TestFormOn (univ : Set (Euclid P)) (m + 1)) := by
    refine Subtype.ext (funext fun y => ?_)
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.add_apply, Pi.smul_apply]
    exact Submission.dimred_cs_sos_mt_cs_flat_extDeriv_split P j m n' g h h₁ h₂ flatD flat flatF
      w (t + y) ((hω.1.differentiable (by simp)).differentiableAt) hD hflat hF
  -- the boundary term: `Y(dγ(t + ·)) = X(γ(t + ·))`
  have hbd : currentEval Y (fun y => exteriorDerivative (fun z => flat (w z)) (t + y)) =
      currentEval X (fun y => flat (w (t + y))) :=
    Submission.dimred_cs_sos_mt_cs_translate_boundary_eval P m X Y _ t hYX hγ
  have hA : ∀ a : Fin (j + 1),
      currentEval Y (fun y => fderiv ℝ (fun z => flatF a (w z)) (t + y) (g a)) =
        Y ⟨_, hAt a, subset_univ _⟩ := fun a => hev _ Y _ ⟨hAt a, subset_univ _⟩
  -- linearity of `Y`
  rw [← hbd, hev _ Y _ ⟨hFt, subset_univ _⟩, hev _ Y _ ⟨hDt, subset_univ _⟩, hsplit]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hA]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
