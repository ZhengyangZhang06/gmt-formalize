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

/-- **Discrete growth** (Simon Ch. 3, 4.3, (10), integrated in discrete steps).  If `V > 0` on
`(0, ρ₁)` and `V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ+δ) − V(ρ))` whenever `ρ, δ > 0`, `ρ + δ < ρ₁`, then
`(ρ/(2K(m+1)))^{m+1} ≤ V(ρ)` for `0 < ρ < ρ₁`.  With `W = V^{1/(m+1)}` and the Bernoulli bound
`xⁿ(x + n(y − x)) ≤ x yⁿ` (`x, y ≥ 0`), one step of length `δ` gives
`δw ≤ (W(r+δ) − W(r))(K(m+1)w + mδ)` for `0 ≤ w ≤ W(r)`.  Summing `N` such steps with
`δ = ρ/(2N)` from `ρ/2`, `w = W(ρ/2)` and `N > mρ²/(4K²(m+1)²W(ρ/2)²)` gives
`W(ρ) ≥ ρ/(2K(m+1))`. -/
theorem Submission.codim1_rdo_dg_vdl_discrete_growth : ∀ (m : ℕ) (K ρ₁ : ℝ) (V : ℝ → ℝ), 0 < K → (∀ r : ℝ, 0 < r → r < ρ₁ → 0 < V r) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → V ρ ^ ((m : ℝ) / (m + 1)) ≤ K / δ * (V (ρ + δ) - V ρ)) → ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ V ρ := by
  intro m K ρ₁ V hK hV hdiff ρ hρ hρ₁
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hKm : 0 < K * (m + 1) := by positivity
  -- Bernoulli's inequality `xⁿ (x + n (y − x)) ≤ x yⁿ` for `x, y ≥ 0`
  have bern : ∀ n : ℕ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ n * (x + n * (y - x)) ≤ x * y ^ n := by
    intro n
    induction n with
    | zero => intro x y _ _; simp
    | succ n ih =>
      intro x y hx hy
      have h1 := mul_le_mul_of_nonneg_left (ih x y hx hy) hy
      have h2 : 0 ≤ x ^ n * (n * (y - x) ^ 2) :=
        mul_nonneg (pow_nonneg hx n) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (y - x)))
      rw [pow_succ, pow_succ]
      push_cast
      linarith
  -- Step 2: `W = V^{1/(m+1)}`, so `W > 0`, `W^{m+1} = V` and `W^m = V^{m/(m+1)}`
  obtain ⟨W, hWpos, hWpow, hWpowm⟩ : ∃ W : ℝ → ℝ, (∀ r, 0 < r → r < ρ₁ → 0 < W r) ∧
      (∀ r, 0 < r → r < ρ₁ → W r ^ (m + 1) = V r) ∧
      (∀ r, 0 < r → r < ρ₁ → W r ^ m = V r ^ ((m : ℝ) / (m + 1))) := by
    refine ⟨fun r => V r ^ ((1 : ℝ) / (m + 1)), fun r h1 h2 => Real.rpow_pos_of_pos (hV r h1 h2) _,
      fun r h1 h2 => ?_, fun r h1 h2 => ?_⟩
    · show (V r ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = V r
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hV r h1 h2).le, Nat.cast_add_one,
        one_div_mul_cancel hm1, Real.rpow_one]
    · show (V r ^ ((1 : ℝ) / (m + 1))) ^ m = V r ^ ((m : ℝ) / (m + 1))
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hV r h1 h2).le, one_div_mul_eq_div]
  -- Step 3, algebra: `δ bᵐ ≤ K (a^{m+1} − b^{m+1})` and `0 ≤ w ≤ b` give
  -- `δ w ≤ (a − b) (K (m+1) w + m δ)`
  have alg : ∀ a b δ w : ℝ, 0 < a → 0 < b → 0 < δ → 0 ≤ w → w ≤ b →
      δ * b ^ m ≤ K * (a ^ (m + 1) - b ^ (m + 1)) →
      δ * w ≤ (a - b) * (K * (m + 1) * w + m * δ) := by
    intro a b δ w ha hb hδ hw0 hwb hd
    rw [pow_succ, pow_succ] at hd
    have hP : 0 < a ^ m := pow_pos ha m
    have hQ : 0 < b ^ m := pow_pos hb m
    have hB1 := bern (m + 1) a b ha.le hb.le
    rw [pow_succ, pow_succ] at hB1
    push_cast at hB1
    have hB0 := bern m a b ha.le hb.le
    -- `a^{m+1} − b^{m+1} ≤ (m+1) aᵐ (a − b)`
    have h1 : a ^ m * a - b ^ m * b ≤ (m + 1) * a ^ m * (a - b) := by
      have h : a * (a ^ m * a - b ^ m * b) ≤ a * ((m + 1) * a ^ m * (a - b)) := by linarith
      exact le_of_mul_le_mul_left h ha
    have h2 : δ * b ^ m ≤ K * (m + 1) * a ^ m * (a - b) := by
      have := mul_le_mul_of_nonneg_left h1 hK.le
      linarith
    have hab : 0 ≤ a - b := by
      by_contra hcon
      have : K * (m + 1) * a ^ m * (a - b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hKm.le hP.le) (not_le.mp hcon).le
      have : 0 < δ * b ^ m := mul_pos hδ hQ
      linarith
    -- `δ (a − m (a − b)) ≤ K (m+1) a (a − b)`
    have h3 : δ * (a + m * (b - a)) ≤ K * (m + 1) * a * (a - b) := by
      have e1 := mul_le_mul_of_nonneg_left hB0 hδ.le
      have e2 := mul_le_mul_of_nonneg_left h2 ha.le
      have h4 : a ^ m * (δ * (a + m * (b - a))) ≤ a ^ m * (K * (m + 1) * a * (a - b)) := by
        linarith
      exact le_of_mul_le_mul_left h4 hP
    have h5 : a * (δ * w) ≤ a * ((a - b) * (K * (m + 1) * w + m * δ)) := by
      have e1 := mul_le_mul_of_nonneg_left h3 hw0
      have e2 : 0 ≤ (a - b) * m * δ * (a - w) :=
        mul_nonneg (mul_nonneg (mul_nonneg hab hm0) hδ.le) (by linarith)
      linarith
    exact le_of_mul_le_mul_left h5 ha
  -- Step 3: one step of length `δ`
  have step : ∀ r δ w : ℝ, 0 < r → 0 < δ → r + δ < ρ₁ → 0 ≤ w → w ≤ W r →
      δ * w ≤ (W (r + δ) - W r) * (K * (m + 1) * w + m * δ) := by
    intro r δ w hr hδ hrδ hw0 hwb
    have hr1 : r < ρ₁ := by linarith
    have hrδ0 : 0 < r + δ := by linarith
    have hd := hdiff r δ hr hδ hrδ
    rw [← hWpowm r hr hr1, ← hWpow r hr hr1, ← hWpow (r + δ) hrδ0 hrδ] at hd
    refine alg _ _ δ w (hWpos _ hrδ0 hrδ) (hWpos r hr hr1) hδ hw0 hwb ?_
    have hδne : δ ≠ 0 := hδ.ne'
    calc δ * W r ^ m ≤ δ * (K / δ * (W (r + δ) ^ (m + 1) - W r ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left hd hδ.le
      _ = K * (W (r + δ) ^ (m + 1) - W r ^ (m + 1)) := by field_simp
  -- Step 4′: `N` steps of length `δ = ρ/(2N)` from `ρ/2`
  have hρ2 : 0 < ρ / 2 := by linarith
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ = W (ρ / 2) := ⟨_, rfl⟩
  have hw₀pos : 0 < w₀ := by rw [hw₀]; exact hWpos _ hρ2 (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) * ρ ^ 2 / (4 * (K * (m + 1)) ^ 2 * w₀ ^ 2))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ρ / (2 * N) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hNδ : (N : ℝ) * δ = ρ / 2 := by
    rw [hδ]
    field_simp
  have ind : ∀ j : ℕ, j ≤ N →
      (j : ℝ) * δ * w₀ ≤ (K * (m + 1) * w₀ + m * δ) * (W (ρ / 2 + j * δ) - w₀) := by
    intro j
    induction j with
    | zero => intro _; simp [hw₀]
    | succ j ih =>
      intro hj
      have ih' := ih (Nat.le_of_succ_le hj)
      have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      have hr : 0 < ρ / 2 + j * δ := by positivity
      have hrδ : ρ / 2 + j * δ + δ < ρ₁ := by
        have := mul_le_mul_of_nonneg_right hjN hδpos.le
        linarith
      have hcoef : 0 < K * (m + 1) * w₀ + m * δ := by positivity
      have hwb : w₀ ≤ W (ρ / 2 + j * δ) := by
        by_contra hcon
        have h1 : (K * (m + 1) * w₀ + m * δ) * (W (ρ / 2 + j * δ) - w₀) < 0 :=
          mul_neg_of_pos_of_neg hcoef (by linarith [not_le.mp hcon])
        have h2 : 0 ≤ (j : ℝ) * δ * w₀ := by positivity
        linarith
      have hs := step (ρ / 2 + j * δ) δ w₀ hr hδpos hrδ hw₀pos.le hwb
      have heq : ρ / 2 + ((j + 1 : ℕ) : ℝ) * δ = ρ / 2 + j * δ + δ := by push_cast; ring
      rw [heq]
      push_cast
      linarith
  have hfin := ind N le_rfl
  have hρN : ρ / 2 + (N : ℝ) * δ = ρ := by rw [hNδ]; ring
  rw [hρN, hNδ] at hfin
  -- `N` is large: `m δ ρ < 2 (K (m+1))² w₀²`
  have hmδ : (m : ℝ) * δ * ρ < 2 * (K * (m + 1)) ^ 2 * w₀ ^ 2 := by
    have h1 : (m : ℝ) * ρ ^ 2 < N * (4 * (K * (m + 1)) ^ 2 * w₀ ^ 2) := by
      rwa [div_lt_iff₀ (by positivity)] at hN
    have h2 : (2 * N) * ((m : ℝ) * δ * ρ) = m * ρ ^ 2 := by
      have : (2 * N) * ((m : ℝ) * δ * ρ) = 2 * m * ρ * (N * δ) := by ring
      rw [this, hNδ]; ring
    have h3 : (2 * N) * ((m : ℝ) * δ * ρ) < (2 * N) * (2 * (K * (m + 1)) ^ 2 * w₀ ^ 2) := by
      rw [h2]; linarith
    exact lt_of_mul_lt_mul_left h3 (by positivity)
  -- Steps 4′(c) and 6: `ρ/(2K(m+1)) ≤ W(ρ)`, so `(ρ/(2K(m+1)))^{m+1} ≤ W(ρ)^{m+1} = V(ρ)`
  have hA : ρ / (2 * K * (m + 1)) ≤ W ρ := by
    rw [div_le_iff₀ (by positivity)]
    by_contra hcon
    have hcoef : 0 < K * (m + 1) * w₀ + m * δ := by positivity
    have e1 := mul_lt_mul_of_pos_left (not_le.mp hcon) hcoef
    have e2 := mul_le_mul_of_nonneg_left hfin hKm.le
    have e3 : 0 ≤ K * (m + 1) * m * δ * w₀ := by positivity
    linarith
  calc (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ W ρ ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) hA (m + 1)
    _ = V ρ := hWpow ρ hρ hρ₁
/-- **Annular cut-off** (step 3 of the lower volume-density bound in De Giorgi's theorem, Simon
Ch. 3, 4.3, proof of (10)–(11)).  There is `C₀ > 0` such that for all `ρ, δ > 0` some `C¹`
function `ζ` on `ℝᴾ` has compact support in `B̄_{ρ+δ}(y)`, `0 ≤ ζ ≤ 1`, `ζ = 1` on `B̄_ρ(y)`,
`‖Dζ‖ ≤ C₀/δ`, and `Dζ = 0` off the open annulus `B_{ρ+δ}(y) \ B̄_ρ(y)`.  Take `C₀ = 3/2` and
`ζ(z) = h((‖z − y‖ − ρ)/δ)` with `h(t) = 1 − ∫₀ᵗ 6 max(0, s(1 − s)) ds` (`= 1 − 3t² + 2t³` on
`[0, 1]`): `h` is `C¹`, `1` on `(−∞, 0]`, `0` on `[1, ∞)`, `h' = 0` there and `|h'| ≤ 3/2`.  Then
`ζ` is constant near `y`, `h ∘ u` with `u` smooth away from `y`, and `(3/(2δ))`-Lipschitz by the
reverse triangle inequality. -/
theorem Submission.codim1_rdo_dg_vdl_annular_cutoff : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ C₀ / δ) ∧ ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
  -- Step 1: the profile `h(t) = 1 − ∫₀ᵗ g`, `g(s) = 6 max(0, s(1 − s))`
  obtain ⟨h, hh_C1, hh_flat, hh_bounds, hh_one, hh_zero, hh_lip⟩ : ∃ h : ℝ → ℝ,
      ContDiff ℝ 1 h ∧ (∀ t, t ≤ 0 ∨ 1 ≤ t → HasDerivAt h 0 t) ∧ (∀ t, 0 ≤ h t ∧ h t ≤ 1) ∧
      (∀ t, t ≤ 0 → h t = 1) ∧ (∀ t, 1 ≤ t → h t = 0) ∧
      ∀ a b, ‖h b - h a‖ ≤ 3 / 2 * ‖b - a‖ := by
    set g : ℝ → ℝ := fun s => 6 * max 0 (s * (1 - s)) with hg_eq
    have hg_cont : Continuous g := by fun_prop
    have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hg_cont.intervalIntegrable a b
    have hg_nonneg : ∀ s, 0 ≤ g s := fun s => mul_nonneg (by norm_num) (le_max_left _ _)
    have hg_le : ∀ s, g s ≤ 3 / 2 := fun s => by
      have h : max 0 (s * (1 - s)) ≤ 1 / 4 :=
        max_le (by norm_num) (by nlinarith [sq_nonneg (s - 1 / 2)])
      simp only [hg_eq]
      linarith
    have hg_left : ∀ s, s ≤ 0 → g s = 0 := fun s hs => by
      simp only [hg_eq]
      rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg hs (by linarith)), mul_zero]
    have hg_right : ∀ s, 1 ≤ s → g s = 0 := fun s hs => by
      simp only [hg_eq]
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)), mul_zero]
    -- `∫₀¹ g = 1`: on `[0, 1]`, `g(s) = 6s(1 − s)` is the derivative of `3s² − 2s³`
    have hg_one : ∫ s in (0 : ℝ)..1, g s = 1 := by
      have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 * s ^ 2 - 2 * s ^ 3)
          (6 * (s * (1 - s))) s := fun s => by
        convert ((hasDerivAt_pow 2 s).const_mul 3).sub ((hasDerivAt_pow 3 s).const_mul 2) using 1
        norm_num
        ring
      rw [intervalIntegral.integral_congr (g := fun s => 6 * (s * (1 - s))) ?_,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
          ((by fun_prop : Continuous fun s : ℝ => 6 * (s * (1 - s))).intervalIntegrable _ _)]
      · norm_num
      · intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        simp only [hg_eq]
        rw [max_eq_right (mul_nonneg hs.1 (by linarith [hs.2]))]
    -- the primitive `F(t) = ∫₀ᵗ g`, with `F' = g`
    set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hF_eq
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
      (hg_cont.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hF_left : ∀ t, t ≤ 0 → F t = 0 := fun t ht => by
      simp only [hF_eq]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_ge ht] at hs
        exact hg_left s hs.2
    have hF_right : ∀ t, 1 ≤ t → F t = 1 := fun t ht => by
      simp only [hF_eq]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int 0 1) (hg_int 1 t), hg_one]
      have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro s hs
          rw [uIcc_of_le ht] at hs
          exact hg_right s hs.1
      rw [h, add_zero]
    have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ 1 := fun t => by
      rcases le_total t 0 with ht | ht
      · rw [hF_left t ht]
        exact ⟨le_rfl, zero_le_one⟩
      rcases le_total 1 t with ht' | ht'
      · rw [hF_right t ht']
        exact ⟨zero_le_one, le_rfl⟩
      refine ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u, ?_⟩
      rw [← hg_one]
      exact intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg)
        (hg_int _ _)
    -- `h = 1 − F`, with `h' = −g`
    have hh_deriv : ∀ t, HasDerivAt (fun t => 1 - F t) (-g t) t := fun t =>
      (hF_deriv t).const_sub 1
    refine ⟨fun t => 1 - F t, ?_, fun t ht => ?_, fun t => ?_, fun t ht => ?_, fun t ht => ?_,
      fun a b => ?_⟩
    · rw [contDiff_one_iff_deriv]
      refine ⟨fun t => (hh_deriv t).differentiableAt, ?_⟩
      rw [show deriv (fun t => 1 - F t) = fun t => -g t from funext fun t => (hh_deriv t).deriv]
      exact hg_cont.neg
    · have hg0 : g t = 0 := ht.elim (hg_left t) (hg_right t)
      simpa [hg0] using hh_deriv t
    · obtain ⟨h₀, h₁⟩ := hF_bounds t
      exact ⟨by linarith, by linarith⟩
    · simp only [hF_left t ht, sub_zero]
    · simp only [hF_right t ht, sub_self]
    · refine convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hh_deriv t).hasDerivWithinAt) (fun t _ => ?_) (mem_univ a) (mem_univ b)
      rw [norm_neg, Real.norm_of_nonneg (hg_nonneg t)]
      exact hg_le t
  -- Step 2: `C₀ = 3/2` and `ζ(z) = h(u(z))`, `u(z) = (‖z − y‖ − ρ)/δ`
  refine ⟨3 / 2, by norm_num, fun P y ρ δ hρ hδ => ?_⟩
  -- Step 3: `ζ ≡ 1` on `B_ρ(y)`, a neighbourhood of `y`
  have hζ_near : (fun z : Euclid P => h ((‖z - y‖ - ρ) / δ)) =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds y hρ] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hh_one _ ((div_le_iff₀ hδ).2 (by linarith))
  -- `u` is smooth away from `y`
  have hu : ∀ z : Euclid P, z ≠ y → ContDiffAt ℝ 1 (fun w : Euclid P => (‖w - y‖ - ρ) / δ) z :=
    fun z hz => (((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hz)).sub
      contDiffAt_const).div_const δ
  -- Step 4: `ζ = 0` off `B_{ρ+δ}(y)`, so `tsupport ζ ⊆ closure B_{ρ+δ}(y) ⊆ B̄_{ρ+δ}(y)`
  have htsupp : tsupport (fun z : Euclid P => h ((‖z - y‖ - ρ) / δ)) ⊆ closedBall y (ρ + δ) := by
    refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro z hz
    by_contra hzb
    apply hz
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hzb
    exact hh_zero _ ((le_div_iff₀ hδ).2 (by linarith))
  refine ⟨fun z => h ((‖z - y‖ - ρ) / δ), ?_,
    (isCompact_closedBall y (ρ + δ)).of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp,
    fun z => hh_bounds _, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  -- Step 5: `ζ` is `C¹` — constant near `y`, and `h ∘ u` with `u` smooth away from `y`
  · rw [contDiff_iff_contDiffAt]
    intro z
    rcases eq_or_ne z y with rfl | hz
    · exact contDiffAt_const.congr_of_eventuallyEq hζ_near
    · exact hh_C1.contDiffAt.comp z (hu z hz)
  -- Step 3: `ζ = 1` on `B̄_ρ(y)`
  · rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hh_one _ ((div_le_iff₀ hδ).2 (by linarith))
  -- Step 6: `ζ` is `(3/(2δ))`-Lipschitz (reverse triangle inequality), so `‖Dζ(z)‖ ≤ 3/(2δ)`
  · refine norm_fderiv_le_of_lip' ℝ (by positivity) (Eventually.of_forall fun w => ?_)
    calc ‖h ((‖w - y‖ - ρ) / δ) - h ((‖z - y‖ - ρ) / δ)‖
        ≤ 3 / 2 * ‖(‖w - y‖ - ρ) / δ - (‖z - y‖ - ρ) / δ‖ := hh_lip _ _
      _ = 3 / 2 / δ * |‖w - y‖ - ‖z - y‖| := by
          rw [Real.norm_eq_abs, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ]
          ring
      _ ≤ 3 / 2 / δ * ‖(w - y) - (z - y)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = 3 / 2 / δ * ‖w - z‖ := by rw [sub_sub_sub_cancel_right]
  -- Step 7: `Dζ(z) = 0` off the open annulus
  · rcases eq_or_ne z y with rfl | hzy
    · rw [hζ_near.fderiv_eq, fderiv_const_apply]
    · -- `u(z) ≤ 0` or `u(z) ≥ 1`, where `h' = 0`; chain rule
      have hu_out : (‖z - y‖ - ρ) / δ ≤ 0 ∨ 1 ≤ (‖z - y‖ - ρ) / δ := by
        rcases le_or_gt ‖z - y‖ ρ with h₁ | h₁
        · exact Or.inl ((div_le_iff₀ hδ).2 (by linarith))
        · refine Or.inr ((le_div_iff₀ hδ).2 ?_)
          have h₂ : z ∉ ball y (ρ + δ) := fun hb => hz ⟨hb, by
            rw [Metric.mem_closedBall, dist_eq_norm, not_le]
            exact h₁⟩
          rw [Metric.mem_ball, dist_eq_norm, not_lt] at h₂
          linarith
      have hD := (hh_flat _ hu_out).comp_hasFDerivAt z
        ((hu z hzy).differentiableAt one_ne_zero).hasFDerivAt
      rw [zero_smul] at hD
      exact hD.fderiv

/-- **Finite-difference form of De Giorgi's volume estimate** (Simon Ch. 3, 4.3, the first
displays of (10); used for 7.5.8).  Let `G ⊆ ℝ^{m+1}` (`m ≥ 1`) be Borel and
`V(r) = L^{m+1}(G ∩ B̄_r(y))`.  Suppose `(∫_G ζ^{(m+1)/m})^{m/(m+1)} ≤ c (∫ ζ dμ + ∫_G |Dζ|)`
for every `C¹` function `ζ ≥ 0` with compact support in `D ⊇ B̄_{ρ₁}(y)` (`μ(B̄_{ρ₁}(y)) < ∞`), and
`δ μ(B̄_ρ(y)) ≤ C₁ L^{m+1}(G ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` whenever `ρ, δ > 0`, `ρ + δ < ρ₁`.  Then
`V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ+δ) − V(ρ))` for such `ρ, δ`, with `K = 2c(C₁ + C₀)`, `C₀` the constant
of `Submission.codim1_rdo_dg_vdl_annular_cutoff`.  Test the Sobolev inequality with that cut-off
`ζ` for the radii `ρ` and `η = δ/2`: the left side is at least `V(ρ)^{m/(m+1)}`, since `ζ = 1` on
`B̄_ρ(y)`; `∫ ζ dμ ≤ μ(B̄_{ρ+η}(y)) ≤ (C₁/η) L^{m+1}(G ∩ A₂)`, `A₂ = B_{ρ+δ}(y) \ B̄_{ρ+η}(y)`, by
the second hypothesis at radius `ρ + η`; and `∫_G |Dζ| ≤ (C₀/η) L^{m+1}(G ∩ A₁)`,
`A₁ = B_{ρ+η}(y) \ B̄_ρ(y)`.  The sets `G ∩ B̄_ρ(y)`, `G ∩ A₁` and `G ∩ A₂` are disjoint subsets of
`G ∩ B̄_{ρ+δ}(y)`. -/
theorem Submission.codim1_rdo_dg_vdl_finite_difference : ∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ K : ℝ, 0 < K ∧ ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤ K / δ * ((volume (G ∩ closedBall y (ρ + δ))).toReal - (volume (G ∩ closedBall y ρ)).toReal) := by
  intro m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ hS hA
  obtain ⟨C₀, hC₀, hcut⟩ := Submission.codim1_rdo_dg_vdl_annular_cutoff
  refine ⟨2 * c * (C₁ + C₀), mul_pos (mul_pos two_pos hc) (by linarith), ?_⟩
  intro ρ δ hρ hδ hρδ
  -- Step 0: the exponents, the half width `η = δ/2` and the two annuli `A₁`, `A₂`.
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hp : (0 : ℝ) < (m + 1 : ℝ) / m := div_pos (by positivity) hm0
  have hq : (0 : ℝ) ≤ (m : ℝ) / (m + 1) := by positivity
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = δ / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; exact half_pos hδ
  set A₁ := ball y (ρ + η) \ closedBall y ρ
  set A₂ := ball y (ρ + δ) \ closedBall y (ρ + η)
  have hA₁m : MeasurableSet A₁ := measurableSet_ball.diff measurableSet_closedBall
  have hA₂m : MeasurableSet A₂ := measurableSet_ball.diff measurableSet_closedBall
  have hA₁fin : volume A₁ ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hA₂fin : volume A₂ ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hGA₁fin : volume (G ∩ A₁) ≠ ∞ := ne_top_of_le_ne_top hA₁fin (measure_mono inter_subset_right)
  have hGA₂fin : volume (G ∩ A₂) ≠ ∞ := ne_top_of_le_ne_top hA₂fin (measure_mono inter_subset_right)
  have hGB : ∀ r : ℝ, volume (G ∩ closedBall y r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right)
  -- `∫_G 𝟙_s a dL^{m+1} = a L^{m+1}(G ∩ s)`
  have hind : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → ∀ a : ℝ,
      ∫ z in G, s.indicator (fun _ => a) z = a * (volume (G ∩ s)).toReal := by
    intro s hs a
    rw [integral_indicator_const a hs, measureReal_restrict_apply hs, smul_eq_mul, mul_comm,
      inter_comm s G, measureReal_def]
  -- Step 1: the cut-off `ζ` for the radii `ρ` and `η`; it is admissible in the Sobolev inequality.
  obtain ⟨ζ, hζC, hζc, hζsupp, hζ01, hζ1, hζgrad, hζzero⟩ := hcut (m + 1) y ρ η hρ hη
  have hsub : closedBall y (ρ + η) ⊆ closedBall y ρ₁ := closedBall_subset_closedBall (by linarith)
  have hSob := hS ζ hζC hζc (hζsupp.trans (hsub.trans hD)) fun z => (hζ01 z).1
  -- Step 2: `V(ρ) ≤ ∫_G ζ^{(m+1)/m}`, as `ζ^{(m+1)/m} ≥ 𝟙_{B̄_ρ}`.
  have hleft : (volume (G ∩ closedBall y ρ)).toReal ≤ ∫ z in G, ζ z ^ ((m + 1 : ℝ) / m) := by
    have hcont : Continuous fun z => ζ z ^ ((m + 1 : ℝ) / m) :=
      hζC.continuous.rpow_const fun _ => Or.inr hp.le
    have hcpt : HasCompactSupport fun z => ζ z ^ ((m + 1 : ℝ) / m) :=
      hζc.comp_left (g := fun t : ℝ => t ^ ((m + 1 : ℝ) / m)) (Real.zero_rpow hp.ne')
    have hint : Integrable (fun z => ζ z ^ ((m + 1 : ℝ) / m)) (volume.restrict G) :=
      (hcont.integrable_of_hasCompactSupport hcpt).integrableOn
    calc (volume (G ∩ closedBall y ρ)).toReal
        = ∫ z in G, (closedBall y ρ).indicator (fun _ => (1 : ℝ)) z := by
          rw [hind _ measurableSet_closedBall, one_mul]
      _ ≤ ∫ z in G, ζ z ^ ((m + 1 : ℝ) / m) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) hint
            (Eventually.of_forall fun z => ?_)
          · exact indicator_nonneg (fun _ _ => zero_le_one) z
          · dsimp only
            by_cases hz : z ∈ closedBall y ρ
            · rw [indicator_of_mem hz, hζ1 z hz, Real.one_rpow]
            · rw [indicator_of_notMem hz]
              exact Real.rpow_nonneg (hζ01 z).1 _
  -- Step 3: `η ∫ ζ dμ ≤ η μ(B̄_{ρ+η}) ≤ C₁ L^{m+1}(G ∩ A₂)`, by the annular bound at `ρ + η`.
  have hμfin : μ (closedBall y (ρ + η)) ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono hsub)
  have hIμ : ∫ z, ζ z ∂μ ≤ (μ (closedBall y (ρ + η))).toReal := by
    have hint : Integrable ((closedBall y (ρ + η)).indicator fun _ => (1 : ℝ)) μ :=
      (integrableOn_const hμfin).integrable_indicator measurableSet_closedBall
    calc ∫ z, ζ z ∂μ ≤ ∫ z, (closedBall y (ρ + η)).indicator (fun _ => (1 : ℝ)) z ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => (hζ01 z).1) hint
            (Eventually.of_forall fun z => ?_)
          by_cases hz : z ∈ closedBall y (ρ + η)
          · rw [indicator_of_mem hz]
            exact (hζ01 z).2
          · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport fun h => hz (hζsupp h)]
      _ = (μ (closedBall y (ρ + η))).toReal := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
            measureReal_def]
  have hAη : ENNReal.ofReal η * μ (closedBall y (ρ + η)) ≤
      ENNReal.ofReal C₁ * volume (G ∩ A₂) := by
    have h := hA (ρ + η) η (by linarith) hη (by linarith)
    rwa [show ρ + η + η = ρ + δ by linarith] at h
  have hμterm : η * ∫ z, ζ z ∂μ ≤ C₁ * (volume (G ∩ A₂)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGA₂fin) hAη
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le,
      ENNReal.toReal_ofReal hC₁] at h
    exact (mul_le_mul_of_nonneg_left hIμ hη.le).trans h
  -- Step 4: `η ∫_G |Dζ| ≤ C₀ L^{m+1}(G ∩ A₁)`, as `|Dζ| ≤ (C₀/η) 𝟙_{A₁}`.
  have hgrad : ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ C₀ / η * (volume (G ∩ A₁)).toReal := by
    have hint : Integrable (A₁.indicator fun _ => C₀ / η) (volume.restrict G) :=
      ((integrableOn_const hA₁fin).integrable_indicator hA₁m).integrableOn
    calc ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ ∫ z in G, A₁.indicator (fun _ => C₀ / η) z := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
            (Eventually.of_forall fun z => ?_)
          dsimp only
          by_cases hz : z ∈ A₁
          · rw [indicator_of_mem hz]
            exact hζgrad z
          · rw [indicator_of_notMem hz, hζzero z hz, norm_zero]
      _ = C₀ / η * (volume (G ∩ A₁)).toReal := hind A₁ hA₁m _
  have hgradterm : η * ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ C₀ * (volume (G ∩ A₁)).toReal := by
    calc η * ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ η * (C₀ / η * (volume (G ∩ A₁)).toReal) :=
          mul_le_mul_of_nonneg_left hgrad hη.le
      _ = C₀ * (volume (G ∩ A₁)).toReal := by field_simp
  -- Step 5: `G ∩ B̄_ρ`, `G ∩ A₁`, `G ∩ A₂` are disjoint subsets of `G ∩ B̄_{ρ+δ}`.
  have hpieces : (volume (G ∩ closedBall y ρ)).toReal + (volume (G ∩ A₁)).toReal +
      (volume (G ∩ A₂)).toReal ≤ (volume (G ∩ closedBall y (ρ + δ))).toReal := by
    have hd₁ : Disjoint (G ∩ closedBall y ρ) (G ∩ A₁) := by
      rw [Set.disjoint_left]
      rintro z ⟨-, hz⟩ ⟨-, -, hz'⟩
      exact hz' hz
    have hd₂ : Disjoint (G ∩ closedBall y ρ ∪ G ∩ A₁) (G ∩ A₂) := by
      rw [Set.disjoint_left]
      rintro z hz ⟨-, -, hz'⟩
      apply hz'
      rcases hz with ⟨-, hz⟩ | ⟨-, hz, -⟩
      · exact closedBall_subset_closedBall (by linarith) hz
      · exact ball_subset_closedBall hz
    have hsub' : G ∩ closedBall y ρ ∪ G ∩ A₁ ∪ G ∩ A₂ ⊆ G ∩ closedBall y (ρ + δ) := by
      rintro z ((⟨hzG, hz⟩ | ⟨hzG, hz, -⟩) | ⟨hzG, hz, -⟩)
      · exact ⟨hzG, closedBall_subset_closedBall (by linarith) hz⟩
      · exact ⟨hzG, closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)⟩
      · exact ⟨hzG, ball_subset_closedBall hz⟩
    have hle : volume (G ∩ closedBall y ρ) + volume (G ∩ A₁) + volume (G ∩ A₂) ≤
        volume (G ∩ closedBall y (ρ + δ)) := by
      rw [← measure_union hd₁ (hG.inter hA₁m), ← measure_union hd₂ (hG.inter hA₂m)]
      exact measure_mono hsub'
    rw [← ENNReal.toReal_add (hGB ρ) hGA₁fin,
      ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hGB ρ, hGA₁fin⟩) hGA₂fin]
    exact ENNReal.toReal_mono (hGB (ρ + δ)) hle
  -- Step 6: combine, with `δ = 2η` and `K = 2c(C₁ + C₀)`.
  have ha₁ : 0 ≤ (volume (G ∩ A₁)).toReal := ENNReal.toReal_nonneg
  have ha₂ : 0 ≤ (volume (G ∩ A₂)).toReal := ENNReal.toReal_nonneg
  have hlhs : (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤
      c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖) :=
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hleft hq).trans hSob
  have hann : C₁ * (volume (G ∩ A₂)).toReal + C₀ * (volume (G ∩ A₁)).toReal ≤
      (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
        (volume (G ∩ closedBall y ρ)).toReal) := by
    nlinarith [mul_nonneg hC₁ ha₁, mul_nonneg hC₀.le ha₂]
  have key : η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤
      c * (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
        (volume (G ∩ closedBall y ρ)).toReal) := by
    calc η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1))
        ≤ η * (c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) :=
          mul_le_mul_of_nonneg_left hlhs hη.le
      _ = c * (η * ∫ z, ζ z ∂μ + η * ∫ z in G, ‖fderiv ℝ ζ z‖) := by ring
      _ ≤ c * (C₁ * (volume (G ∩ A₂)).toReal + C₀ * (volume (G ∩ A₁)).toReal) :=
          mul_le_mul_of_nonneg_left (add_le_add hμterm hgradterm) hc.le
      _ ≤ c * ((C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
            (volume (G ∩ closedBall y ρ)).toReal)) :=
          mul_le_mul_of_nonneg_left hann hc.le
      _ = c * (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
            (volume (G ∩ closedBall y ρ)).toReal) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  have hδη : (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) * δ =
      2 * (η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1))) := by
    rw [hη_def]
    ring
  rw [hδη]
  linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
