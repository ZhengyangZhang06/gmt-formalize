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

/-- **Jacobi's trace identity for column replacement** (parent fact (F3) of the divergence form
of the mass representation).  Let `M = (u j k)_{k,j}` be the matrix with columns `u j`.
Replacing column `i` by `A (u i)` and summing the determinants over `i` gives `tr(A) · det M`.
With `B` the matrix of `A` in the standard basis `e` of `ℝⁿ`, column `i` of `B M` is `A (u i)`,
so by Cramer's rule the `i`-th determinant is `(adj M · B M)_{i,i}`; then
`tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr B = det M · tr A`. -/
theorem Submission.cmr_df_det_update_sum_trace : ∀ (n : ℕ) (A : Euclid n →ₗ[ℝ] Euclid n) (u : Fin n → Euclid n), ∑ i : Fin n, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) = LinearMap.trace ℝ (Euclid n) A * Matrix.det (Matrix.of fun k j => u j k) := by
  intro n A u
  -- the standard basis `e` of `ℝⁿ`, the matrix `M` with columns `u j`, the matrix `B` of `A`
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => u j k
  let B := LinearMap.toMatrix e e A
  -- Step 1: `A (u i) k = (B M)_{k,i}`, from `B *ᵥ e.repr x = e.repr (A x)` and `e.repr x = x`
  have hA : ∀ i k, A (u i) k = (B * M) k i := by
    intro i k
    have := congrFun (LinearMap.toMatrix_mulVec_repr e e A (u i)) k
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, e, B, M] using this.symm
  -- Step 2: the `i`-th summand is `det (M.updateCol i (B M)_{·,i}) = (adj M · B M)_{i,i}` (Cramer)
  have hcol : ∀ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
      (M.adjugate * (B * M)) i i := by
    intro i
    have h1 : (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
        M.updateCol i (fun k => (B * M) k i) := by
      ext k j
      by_cases hj : j = i
      · subst hj
        simp [hA]
      · simp [hj, M]
    rw [h1, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  -- Step 3: `tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr A`
  calc ∑ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k)
      = Matrix.trace (M.adjugate * (B * M)) := by
        simp only [hcol, Matrix.trace, Matrix.diag_apply]
    _ = Matrix.trace (B * (M * M.adjugate)) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = LinearMap.trace ℝ (Euclid n) A * M.det := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
          LinearMap.trace_eq_matrix_trace ℝ e A, mul_comm]

/-- **Coordinate form of `Σᵢ (-1)ⁱ θ(L wᵢ, w₀, …, ŵᵢ, …, w_m) = tr(A) θ(w)`** (the trace step of
the divergence-form computation behind the mass representation in Simon 7.2.4).  Let `θ` be the
`(m+1)`-covector `θ(v) = det (v j (I k))_{k,j}` on `ℝᴾ`, let `A` be linear on `ℝ^{m+1}`, and let
`L : ℝᴾ → ℝᴾ` satisfy `(L v)(I k) = (A (p v))_k` with `p v = (v (I k))_k`.  Moving `L wᵢ` from
the front to slot `i` costs `(-1)ⁱ`, so the `i`-th term is `θ(w)` with `wᵢ` replaced by `L wᵢ`.
In the coordinates `uⱼ = p wⱼ` it is the determinant of `u` with its `i`-th column replaced by
`A uᵢ`.  Jacobi's identity `Submission.cmr_df_det_update_sum_trace` sums these determinants to
`tr(A) det u`, and `det u = θ(w)`. -/
theorem Submission.cmr_df_cons_sum_trace : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (L : Euclid P → Euclid P), (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → (∀ (v : Euclid P) (k : Fin (m + 1)), L v (I k) = A (WithLp.toLp 2 (fun k' => v (I k'))) k) → ∀ w : Fin (m + 1) → Euclid P, ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons (L (w i)) (i.removeNth w)) = LinearMap.trace ℝ (Euclid (m + 1)) A * θ w := by
  intro P m I θ A L hθ hL w
  -- Step 1: sign rule, `(-1)ⁱ θ(x, w₀, …, ŵᵢ, …, w_m) = θ(w with wᵢ replaced by x)`
  have h1 : ∀ (i : Fin (m + 1)) (x : Euclid P),
      (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons x (i.removeNth w)) = θ (Function.update w i x) := by
    intro i x
    rw [← Fin.insertNth_removeNth, ContinuousAlternatingMap.map_insertNth, zsmul_eq_mul]
    push_cast
    rfl
  -- the coordinate columns `uⱼ = p wⱼ ∈ ℝ^{m+1}`
  let u : Fin (m + 1) → Euclid (m + 1) := fun j => WithLp.toLp 2 (fun k => w j (I k))
  -- Step 2: the `i`-th term is `det u` with its `i`-th column replaced by `A uᵢ`, entrywise
  have h2 : ∀ i : Fin (m + 1), θ (Function.update w i (L (w i))) =
      Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) := by
    intro i
    rw [hθ]
    congr 1
    ext k j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, u]
    · simp [Function.update_of_ne hj, u]
  -- Step 4: `det u = θ(w)`
  have h4 : Matrix.det (Matrix.of fun k j => u j k) = θ w := (hθ w).symm
  -- Step 3: Jacobi's identity
  simp_rw [h1, h2]
  rw [Submission.cmr_df_det_update_sum_trace (m + 1) A u, h4]
/-- **Exterior derivative of a function times a contracted covector** (used for the divergence
form in the mass-representation step of Simon 7.2.4).  If `b : ℝᴾ → ℝ` and `G : ℝᴾ → ℝᴾ` are
differentiable at `x` and `θ` is a fixed `(m+1)`-covector, then `η(y) = b(y) θ(G(y), ·)` has
`dη(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ (Db(x)wᵢ · θ(G(x), ŵᵢ) + b(x) · θ(DG(x)wᵢ, ŵᵢ))`, where `ŵᵢ` is
`(w₀, …, w_m)` with `wᵢ` removed: each term of the alternating sum differentiates
`y ↦ b(y) θ(G(y), ŵᵢ)` by the product and chain rules. -/
theorem Submission.cmr_df_extDeriv_smul_curryLeft : ∀ (P m : ℕ) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ) (G : Euclid P → Euclid P) (x : Euclid P), DifferentiableAt ℝ b x → DifferentiableAt ℝ G x → ∀ w : Fin (m + 1) → Euclid P, exteriorDerivative (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w))) := by
  intro P m θ b G x hb hG w
  have hc : DifferentiableAt ℝ (fun y => ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    (ContinuousAlternatingMap.curryLeft θ).differentiableAt.comp x hG
  have hη : DifferentiableAt ℝ (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    hb.smul hc
  rw [exteriorDerivative_apply hη w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_continuousAlternatingMap_apply_const_apply hη, fderiv_fun_smul hb hc,
    fderiv_fun_comp x (ContinuousAlternatingMap.curryLeft θ).differentiableAt hG,
    ContinuousLinearMap.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    smul_eq_mul, zsmul_eq_mul]
  simp only [Matrix.vecCons]
  push_cast
  ring
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

/-- **Divergence form of `b · (div g) ∘ p_I` against `θ = dx^I`** (the projection step
`p_I^#((div g) dy) = d(p_I^#γ)` of the mass representation used for Simon 7.2.4).  Let
`p_I x = (x_{I k})_k`, `ι y = ∑ₖ y_k e_{I k}` and `G = ι ∘ g ∘ p_I`, so that
`(DG(x) v)_{I k} = (Dg(p_I x)(p_I v))_k`.  Put `η = b • θ.curryLeft ∘ G` and
`ζ = dη − (b · tr Dg ∘ p_I) • θ`.  The formula for `dη` (`cmr_df_extDeriv_smul_curryLeft`) and
Jacobi's trace identity in coordinates (`cmr_df_cons_sum_trace`) give
`ζ(x)(w) = ∑ᵢ (−1)ⁱ Db(x)(wᵢ) θ(G x, w without wᵢ)`.  Hence `‖η‖ ≤ sup|b| ‖θ‖ ‖ι‖` and
`‖ζ‖ ≤ (m + 1) sup‖Db‖ ‖θ‖ ‖ι‖`, both forms vanish off `tsupport b`, and part (iii) of
`rsd_mw_tfa_norm_props` turns these operator-norm bounds into a coefficient-norm bound `K`
that does not depend on `g`. -/
theorem Submission.cmr_coordinate_divergence_form : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ), StrictMono I → (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → ∃ K : ℝ, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → (∀ y, ‖g y‖ ≤ 1) → ∃ (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)), IsTestForm η ∧ IsTestForm ζ ∧ tsupport η ⊆ tsupport b ∧ tsupport ζ ⊆ tsupport b ∧ (∀ x, covectorEuclideanNorm (η x) ≤ K) ∧ (∀ x, covectorEuclideanNorm (ζ x) ≤ K) ∧ ∀ x, exteriorDerivative η x = (b x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ + ζ x := by
  intro P m I θ b hI hθ hb hbc
  -- the coordinate projection `p = p_I` and the coordinate embedding `ι`, `(ι y)_{I k} = y_k`
  let p : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun k => x (I k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : Euclid (m + 1) →L[ℝ] Euclid P := LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun j => ∑ k, if I k = j then y k else 0)
      map_add' := fun y z => by
        ext j
        simp only [PiLp.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      map_smul' := fun c y => by
        ext j
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp }
  have hι : ∀ y k, ι y (I k) = y k := by
    intro y k
    change (∑ k', if I k' = I k then y k' else 0) = y k
    simp [hI.injective.eq_iff]
  -- the constant `K`: (F1) from `rsd_mw_tfa_norm_props` (iii), `β₀ = sup |b|`, `β₁ = sup ‖Db‖`
  obtain ⟨Cm, hCm0, hCm⟩ := (Submission.rsd_mw_tfa_norm_props P m).2.2.1
  obtain ⟨Cn, hCn0, hCn⟩ := (Submission.rsd_mw_tfa_norm_props P (m + 1)).2.2.1
  obtain ⟨β₀, hβ₀⟩ := hb.continuous.bounded_above_of_compact_support hbc
  obtain ⟨β₁, hβ₁⟩ :=
    (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support (hbc.fderiv ℝ)
  have hβ₀0 : 0 ≤ β₀ := (norm_nonneg _).trans (hβ₀ 0)
  have hβ₁0 : 0 ≤ β₁ := (norm_nonneg _).trans (hβ₁ 0)
  refine ⟨Cm * (β₀ * (‖θ‖ * ‖ι‖)) + Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))), ?_⟩
  intro g hg hg1
  -- the vector field `G = ι ∘ g ∘ p`: smooth, `‖G‖ ≤ ‖ι‖`, `DG(x) = ι ∘ Dg(p x) ∘ p`
  obtain ⟨G, hG⟩ : ∃ G : Euclid P → Euclid P, G = fun x => ι (g (p x)) := ⟨_, rfl⟩
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := hG ▸ ι.contDiff.comp (hg.comp p.contDiff)
  have hGb : ∀ x, ‖G x‖ ≤ ‖ι‖ := by
    intro x
    rw [hG]
    calc ‖ι (g (p x))‖ ≤ ‖ι‖ * ‖g (p x)‖ := ι.le_opNorm _
      _ ≤ ‖ι‖ * 1 := mul_le_mul_of_nonneg_left (hg1 _) (norm_nonneg _)
      _ = ‖ι‖ := mul_one _
  have hDG : ∀ x v, fderiv ℝ G x v = ι (fderiv ℝ g (p x) (p v)) := by
    intro x v
    have hgd : DifferentiableAt ℝ g (p x) := hg.differentiable (by simp) _
    have h : HasFDerivAt G (ι.comp ((fderiv ℝ g (p x)).comp p)) x := by
      rw [hG]
      exact ι.hasFDerivAt.comp x (hgd.hasFDerivAt.comp x p.hasFDerivAt)
    rw [h.fderiv]
    rfl
  -- `(DG(x) v)_{I k} = (Dg(p x)(p v))_k`, the hypothesis of `cmr_df_cons_sum_trace`
  have hL : ∀ x (v : Euclid P) (k : Fin (m + 1)), fderiv ℝ G x v (I k) =
      (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap
        (WithLp.toLp 2 (fun k' => v (I k'))) k := by
    intro x v k
    rw [hDG, hι]
    rfl
  -- the forms `η = b • θ.curryLeft ∘ G` and `ζ = dη − (b · tr Dg ∘ p) • θ`
  obtain ⟨η, hη⟩ : ∃ η : DifferentialForm (Euclid P) m,
      η = fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : DifferentialForm (Euclid P) (m + 1),
      ζ = fun x => exteriorDerivative η x - (b x * LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ := ⟨_, rfl⟩
  -- Step 1: `η` is a test form with `tsupport η ⊆ tsupport b`
  have hηs : tsupport η ⊆ tsupport b := by
    rw [hη]
    exact tsupport_smul_subset_left b _
  have hηT : IsTestForm η := by
    refine ⟨?_, hbc.mono' ((subset_tsupport η).trans hηs)⟩
    rw [hη]
    exact hb.smul ((ContinuousAlternatingMap.curryLeft θ).contDiff.comp hGs)
  -- Steps 2-4: `dη(x)(w) = Z_x(w) + b(x) S_x(w)` and `S_x(w) = tr Dg(p x) · θ(w)`,
  -- so `ζ(x)(w) = Z_x(w) = ∑ᵢ (−1)ⁱ Db(x)(wᵢ) θ(G x, w without wᵢ)`
  have hζZ : ∀ x (w : Fin (m + 1) → Euclid P), ζ x w = ∑ i : Fin (m + 1),
      (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w))) := by
    intro x w
    have hbx : DifferentiableAt ℝ b x := hb.differentiable (by simp) x
    have hGx : DifferentiableAt ℝ G x := hGs.differentiable (by simp) x
    have h1 := Submission.cmr_df_extDeriv_smul_curryLeft P m θ b G x hbx hGx w
    have h2 := Submission.cmr_df_cons_sum_trace P m I θ
      (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap (fderiv ℝ G x) hθ (hL x) w
    have h3 : ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i))
          (i.removeNth w))) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w))) + b x * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
          θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hζ]
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [hη, h1, h3, h2]
    ring
  -- Step 4: `ζ` is a test form with `tsupport ζ ⊆ tsupport b`
  have hζsupp : support ζ ⊆ tsupport b := by
    intro x hx
    by_contra hxb
    have hbx : b x = 0 := image_eq_zero_of_notMem_tsupport hxb
    have hdη : exteriorDerivative η x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hxb (hηs (tsupport_exteriorDerivative_subset η h))
    exact hx (by rw [hζ]; simp [hbx, hdη])
  have hζs : tsupport ζ ⊆ tsupport b := closure_minimal hζsupp (isClosed_tsupport b)
  have hζT : IsTestForm ζ := by
    refine ⟨?_, hbc.mono' hζsupp⟩
    let tr : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid (m + 1)) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have htr : ContDiff ℝ (⊤ : ℕ∞) fun x : Euclid P => LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap :=
      tr.contDiff.comp ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp p.contDiff)
    rw [hζ]
    exact (exteriorDerivative_isTestForm hηT).1.sub ((hb.mul htr).smul contDiff_const)
  -- Step 5: operator-norm bounds, independent of `g`
  have hη_op : ∀ x, ‖η x‖ ≤ β₀ * (‖θ‖ * ‖ι‖) := by
    intro x
    rw [hη, norm_smul]
    refine mul_le_mul (hβ₀ x) ?_ (norm_nonneg _) hβ₀0
    calc ‖ContinuousAlternatingMap.curryLeft θ (G x)‖
        ≤ ‖ContinuousAlternatingMap.curryLeft θ‖ * ‖G x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖θ‖ * ‖ι‖ := by
        rw [ContinuousAlternatingMap.norm_curryLeft]
        exact mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _)
  have hζ_op : ∀ x, ‖ζ x‖ ≤ ((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖)) := by
    intro x
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [hζZ x w]
    have hterm : ∀ i : Fin (m + 1), ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w)))‖ ≤ β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ := by
      intro i
      have h1 : ‖fderiv ℝ b x (w i)‖ ≤ β₁ * ‖w i‖ :=
        ((fderiv ℝ b x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hβ₁ x) (norm_nonneg _))
      have h2 : ‖θ (Fin.cons (G x) (i.removeNth w))‖ ≤
          ‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖ := by
        calc ‖θ (Fin.cons (G x) (i.removeNth w))‖
            ≤ ‖θ‖ * ∏ j : Fin (m + 1),
                ‖(Fin.cons (G x) (i.removeNth w) : Fin (m + 1) → Euclid P) j‖ :=
              θ.le_opNorm _
          _ = ‖θ‖ * (‖G x‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by
              rw [Fin.prod_univ_succ]
              simp [Fin.removeNth_apply]
          _ ≤ ‖θ‖ * (‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by
              gcongr
              exact hGb x
          _ = ‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖ := by ring
      calc ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)))‖
          = ‖fderiv ℝ b x (w i)‖ * ‖θ (Fin.cons (G x) (i.removeNth w))‖ := by
            simp [norm_mul]
        _ ≤ (β₁ * ‖w i‖) * (‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = β₁ * (‖θ‖ * ‖ι‖) * (‖w i‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by ring
        _ = β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ := by
            rw [Fin.prod_univ_succAbove (fun j => ‖w j‖) i]
    calc ‖∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
          θ (Fin.cons (G x) (i.removeNth w)))‖
        ≤ ∑ i : Fin (m + 1), ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
          θ (Fin.cons (G x) (i.removeNth w)))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (m + 1), β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖)) * ∏ j, ‖w j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  -- Steps 5-6: coefficient-norm bounds by (F1), and the identity, by definition of `ζ`
  have hK1 : 0 ≤ Cm * (β₀ * (‖θ‖ * ‖ι‖)) := by positivity
  have hK2 : 0 ≤ Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))) := by positivity
  refine ⟨η, ζ, hηT, hζT, hηs, hζs, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · calc covectorEuclideanNorm (η x) ≤ Cm * ‖η x‖ := hCm _
      _ ≤ Cm * (β₀ * (‖θ‖ * ‖ι‖)) := mul_le_mul_of_nonneg_left (hη_op x) hCm0
      _ ≤ _ := le_add_of_nonneg_right hK2
  · calc covectorEuclideanNorm (ζ x) ≤ Cn * ‖ζ x‖ := hCn _
      _ ≤ Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))) := mul_le_mul_of_nonneg_left (hζ_op x) hCn0
      _ ≤ _ := le_add_of_nonneg_left hK1
  · rw [hζ]
    exact (add_sub_cancel _ _).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
