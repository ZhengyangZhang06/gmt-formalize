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

/-- Lower density of `Hⁿ⌞M` at an approximate tangent point (Simon Ch. 3, Definition 1.4 and
Remark 1.5(3)): if `Q` is an approximate tangent space of `M` at `x` (`dim Q = n ≥ 1`), then
`c ωₙ tⁿ ≤ Hⁿ(M ∩ B_t(x))` for every `c < 1` and all small `t > 0`.  For `0 < c < 1` fix `ε > 0`
with `c (1 + ε)ⁿ < 1`.  The cutoff `ψ = max(0, min(1, (1 + ε − |y|)/ε))` satisfies
`1_{B₁(0)} ≤ ψ ≤ 1_{B_{1+ε}(0)}`, so `∫_Q ψ dHⁿ ≥ Hⁿ(Q ∩ B₁(0)) = ωₙ`.  The blow-up integrals
`∫_{η_{x,r}(M)} ψ dHⁿ` tend to `∫_Q ψ dHⁿ` and are at most `r⁻ⁿ Hⁿ(M ∩ B_{r(1+ε)}(x))` by
scaling; taking `t = r(1 + ε)` gives the bound. -/
theorem Submission.dorag_dbs_approxTangent_lower_density : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → HasApproximateTangentSpaceAt n M x Q → ∀ c : ℝ, c < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ μHE[n] (M ∩ closedBall x t) := by
  intro P n M x Q hn hQ c hc
  by_cases hc0 : c ≤ 0
  · filter_upwards with t
    simp [ENNReal.ofReal_of_nonpos hc0]
  push Not at hc0
  obtain ⟨hfin, hconv⟩ := hQ
  -- the unit-ball volume
  have hω0 : unitBallVolume n ≠ 0 := by
    unfold unitBallVolume
    exact (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := by
    unfold unitBallVolume
    exact measure_ball_lt_top.ne
  have hωr : 0 < (unitBallVolume n).toReal := ENNReal.toReal_pos hω0 hωtop
  -- Step 5(a): the plane ball has measure ω_n
  have hQball : (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 1) = unitBallVolume n := by
    have : Nontrivial Q := Module.nontrivial_of_finrank_pos (hfin.symm ▸ hn)
    have hrange : Set.range (Q.subtypeₗᵢ : Q → Euclid P) = (Q : Set (Euclid P)) := by
      ext y; simp
    rw [← hrange, ← Q.subtypeₗᵢ.isometry.map_euclideanHausdorffMeasure,
      Measure.map_apply Q.subtypeₗᵢ.continuous.measurable measurableSet_closedBall]
    have hpre : (Q.subtypeₗᵢ : Q → Euclid P) ⁻¹' closedBall (0 : Euclid P) 1 =
        closedBall (0 : Q) 1 := by
      ext y; simp [mem_closedBall, dist_eq_norm]
    have hvol : (μHE[n] : Measure Q) = volume := by
      rw [← hfin]; exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [hpre, hvol, Measure.addHaar_closedBall_eq_addHaar_ball]
    rw [← hfin]
    unfold unitBallVolume
    let e := (stdOrthonormalBasis ℝ Q).repr
    have hmp : MeasurePreserving e volume volume := e.measurePreserving
    rw [← hmp.measure_preimage measurableSet_ball.nullMeasurableSet]
    congr 1
    ext y
    simp [e, mem_ball, dist_eq_norm]
  -- choice of ε
  have hεlim : Tendsto (fun ε : ℝ => c * (1 + ε) ^ n) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_const_nhds
    simpa only [id_eq, add_zero, one_pow, mul_one] using
      ((hone.add (tendsto_id.mono_left inf_le_left :
        Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0))).pow n).const_mul c
  obtain ⟨ε, hεc, hε⟩ :=
    ((hεlim.eventually (gt_mem_nhds hc)).and self_mem_nhdsWithin).exists
  have hε0 : 0 < ε := hε
  have hA : 0 < 1 + ε := by linarith
  -- the cutoff ψ
  let ψf : Euclid P → ℝ := fun y => max 0 (min 1 ((1 + ε - ‖y‖) / ε))
  have hψcont : Continuous ψf := by
    apply continuous_const.max
    apply continuous_const.min
    exact (continuous_const.sub continuous_norm).div_const ε
  have hψ0 : ∀ y, y ∉ closedBall (0 : Euclid P) (1 + ε) → ψf y = 0 := by
    intro y hy
    have hy' : 1 + ε < ‖y‖ := by simpa [mem_closedBall, dist_eq_norm] using hy
    have hneg : (1 + ε - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε0
    simp only [ψf]
    exact max_eq_left ((min_le_right _ _).trans hneg.le)
  have hψsupp : HasCompactSupport ψf :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) (1 + ε)) hψ0
  let ψ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    { toFun := ψf, continuous_toFun := hψcont, hasCompactSupport' := hψsupp }
  have hψapp : ∀ y, ψ y = ψf y := fun _ => rfl
  have hψ01 : ∀ y, 0 ≤ ψf y ∧ ψf y ≤ 1 := by
    intro y
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hψ1 : ∀ y ∈ closedBall (0 : Euclid P) 1, ψf y = 1 := by
    intro y hy
    have hy' : ‖y‖ ≤ 1 := by simpa [mem_closedBall, dist_eq_norm] using hy
    have h1 : 1 ≤ (1 + ε - ‖y‖) / ε := by
      rw [le_div_iff₀ hε0]; linarith
    simp only [ψf]
    rw [min_eq_left h1]
    exact max_eq_right zero_le_one
  -- Step 5: the plane integral is at least ω_n
  have hplane : (unitBallVolume n).toReal ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hfin
    have hint : Integrable ψ (μHE[n].restrict (Q : Set (Euclid P))) :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hle := setIntegral_le_integral (s := closedBall (0 : Euclid P) 1) hint
      (Eventually.of_forall (fun y => (hψ01 y).1))
    have heq : ∫ y in closedBall (0 : Euclid P) 1, ψ y ∂(μHE[n].restrict (Q : Set (Euclid P))) =
        (unitBallVolume n).toReal := by
      have hcongr : ∫ y in closedBall (0 : Euclid P) 1, ψ y ∂(μHE[n].restrict (Q : Set (Euclid P))) =
          ∫ _ in closedBall (0 : Euclid P) 1, (1 : ℝ) ∂(μHE[n].restrict (Q : Set (Euclid P))) :=
        setIntegral_congr_fun measurableSet_closedBall (fun y hy => by rw [hψapp]; exact hψ1 y hy)
      rw [hcongr]
      simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
        Measure.restrict_apply_univ, hQball]
    rw [heq] at hle
    exact hle
  -- Step 6: eventually the blow-up integrals exceed c (1+ε)^n ω_n
  have hgap : c * (1 + ε) ^ n * (unitBallVolume n).toReal <
      ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have : c * (1 + ε) ^ n * (unitBallVolume n).toReal < (unitBallVolume n).toReal := by
      nlinarith
    linarith
  have hev := (hconv ψ).eventually (lt_mem_nhds hgap)
  -- Step 8: scaling of the blow-up
  have hscale : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) =
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] S := by
    intro r hr S
    have hshift : Isometry (fun y : Euclid P => y - x) := by
      apply Isometry.of_dist_eq
      intro a b
      simp only [dist_eq_norm]
      congr 1
      abel
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        AffineMap.homothety (0 : Euclid P) r⁻¹ '' ((fun y : Euclid P => y - x) '' S) := by
      rw [← image_comp]
      congr 1
      funext y
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Euclid P) (inv_ne_zero hr.ne'),
      hshift.euclideanHausdorffMeasure_image]
    simp only [ENNReal.smul_def, ENNReal.coe_pow, smul_eq_mul]
    congr 2
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hinter : ∀ r : ℝ, 0 < r → ∀ S : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (closedBall x (r * (1 + ε)) ∩ S) =
        closedBall (0 : Euclid P) (1 + ε) ∩ (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) := by
    intro r hr S
    have hmem : ∀ y : Euclid P, Poincare.SimonGMT.Chapter03.blowUpMap x r y ∈
        closedBall (0 : Euclid P) (1 + ε) ↔ y ∈ closedBall x (r * (1 + ε)) := by
      intro y
      simp only [mem_closedBall, dist_eq_norm, sub_zero, Poincare.SimonGMT.Chapter03.blowUpMap,
        norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr).le]
      rw [← div_eq_inv_mul, div_le_iff₀ hr, mul_comm r (1 + ε)]
    ext y
    constructor
    · rintro ⟨z, ⟨hzB, hzS⟩, rfl⟩
      exact ⟨(hmem z).mpr hzB, mem_image_of_mem _ hzS⟩
    · rintro ⟨hyB, z, hzS, rfl⟩
      exact ⟨z, ⟨(hmem z).mp hyB, hzS⟩, rfl⟩
  -- Step 7: upper bound for the blow-up integrals
  have hup : ∀ r : ℝ, 0 < r → μHE[n] (M ∩ closedBall x (r * (1 + ε))) ≠ ∞ →
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]) ≤
        (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x (r * (1 + ε)))).toReal := by
    intro r hr hfinM
    have hνB : (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        (closedBall (0 : Euclid P) (1 + ε)) =
          ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * (1 + ε))) := by
      rw [Measure.restrict_apply measurableSet_closedBall, ← hinter r hr M, hscale r hr,
        inter_comm]
    have hνfin : (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        (closedBall (0 : Euclid P) (1 + ε)) < ∞ := by
      rw [hνB]
      exact ENNReal.mul_lt_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top hfinM.lt_top
    have hnorm := norm_setIntegral_le_of_norm_le_const_ae (f := fun y => ψ y) hνfin
      (Eventually.of_forall (fun y => show ‖ψ y‖ ≤ 1 by
        rw [hψapp, Real.norm_of_nonneg (hψ01 y).1]
        exact (hψ01 y).2))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hψapp]; exact hψ0 y hy),
      one_mul] at hnorm
    calc (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n])
        ≤ ‖∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]‖ := le_abs_self _
      _ ≤ _ := hnorm
      _ = (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x (r * (1 + ε)))).toReal := by
        rw [measureReal_def, hνB, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal (inv_pos.mpr hr).le]
  -- Step 9: conclusion with r = t / (1 + ε)
  have hrA : Tendsto (fun t : ℝ => t / (1 + ε)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, id_eq] using
        (tendsto_id.mono_left inf_le_left : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).div_const (1 + ε)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos ht hA
  filter_upwards [hrA.eventually hev, self_mem_nhdsWithin] with t ht htpos
  have htpos' : 0 < t := htpos
  have hr : 0 < t / (1 + ε) := div_pos htpos' hA
  have hrA' : t / (1 + ε) * (1 + ε) = t := div_mul_cancel₀ _ hA.ne'
  by_cases hH : μHE[n] (M ∩ closedBall x t) = ∞
  · rw [hH]; exact le_top
  have hb := hup (t / (1 + ε)) hr (by rwa [hrA'])
  rw [hrA'] at hb
  have h1 : c * (1 + ε) ^ n * (unitBallVolume n).toReal <
      ((t / (1 + ε))⁻¹) ^ n * (μHE[n] (M ∩ closedBall x t)).toReal := lt_of_lt_of_le ht hb
  have hrn : 0 < (t / (1 + ε)) ^ n := pow_pos hr n
  have h2 : ((t / (1 + ε))⁻¹) ^ n * (t / (1 + ε)) ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  have h3 : (1 + ε) ^ n * (t / (1 + ε)) ^ n = t ^ n := by
    rw [← mul_pow, mul_comm, hrA']
  have hreal : c * (unitBallVolume n).toReal * t ^ n ≤ (μHE[n] (M ∩ closedBall x t)).toReal := by
    have h4 := mul_lt_mul_of_pos_right h1 hrn
    calc c * (unitBallVolume n).toReal * t ^ n
        = c * (1 + ε) ^ n * (unitBallVolume n).toReal * (t / (1 + ε)) ^ n := by
          rw [← h3]; ring
      _ ≤ ((t / (1 + ε))⁻¹) ^ n * (μHE[n] (M ∩ closedBall x t)).toReal * (t / (1 + ε)) ^ n :=
          h4.le
      _ = (μHE[n] (M ∩ closedBall x t)).toReal := by
          rw [mul_right_comm, h2, one_mul]
  calc ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n)
      = ENNReal.ofReal (c * (unitBallVolume n).toReal * t ^ n) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hc0.le,
          ENNReal.ofReal_toReal hωtop]
    _ ≤ ENNReal.ofReal (μHE[n] (M ∩ closedBall x t)).toReal := ENNReal.ofReal_le_ofReal hreal
    _ = μHE[n] (M ∩ closedBall x t) := ENNReal.ofReal_toReal hH
/-- **Localized Besicovitch density theorem** (Simon Ch. 1, 3.16 with Remark 3.7(2)): if `ν` is
finite on compact subsets of the open set `W` and `s` is measurable, then `ν⌞s`-a.e. `x ∈ W` has
`a · ν(B_t(x)) ≤ ν(s ∩ B_t(x))` for every `a < 1` and all small `t > 0`.  `W` is covered by
countably many open balls `B̆_{rᵢ}(i)` with `B_{2rᵢ}(i) ⊆ W` compact; on each, Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div` for the finite measure `ν⌞B_{2rᵢ}(i)` gives
`ν(s ∩ B_t(x)) / ν(B_t(x)) → 1` for `ν⌞s`-a.e. `x ∈ B̆_{rᵢ}(i)`, and the countable union
(`ae_ball_iff`) gives the claim. -/
theorem Submission.dorag_dbs_localized_density_point : ∀ (P : ℕ) (W s : Set (Euclid P)) (ν : Measure (Euclid P)), IsOpen W → MeasurableSet s → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → ν K ≠ ∞) → ∀ᵐ x ∂ν.restrict s, x ∈ W → ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t) := by
  intro P W s ν hW hs hfin
  -- radii: closedBall x (2 r) ⊆ W
  have hr : ∀ x : W, ∃ r : ℝ, 0 < r ∧ closedBall (x : Euclid P) (2 * r) ⊆ W := by
    intro x
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x x.2
    exact ⟨ε / 3, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  choose r hr0 hrW using hr
  -- countable subcover of W by the balls ball x (r x)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : W => ball (x : Euclid P) (r x)) (fun _ => isOpen_ball)
  have hcover : ∀ x ∈ W, ∃ i ∈ T, x ∈ ball (i : Euclid P) (r i) := by
    intro x hx
    have hmem : x ∈ ⋃ i : W, ball (i : Euclid P) (r i) :=
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr0 _)⟩
    rw [← hTU] at hmem
    simpa only [mem_iUnion, exists_prop] using hmem
  -- the local statement on each ball
  have hloc : ∀ i : W, ∀ᵐ x ∂ν.restrict s, x ∈ ball (i : Euclid P) (r i) →
      ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t) := by
    intro i
    have hKm : MeasurableSet (closedBall (i : Euclid P) (2 * r i)) := measurableSet_closedBall
    have hKfin : ν (closedBall (i : Euclid P) (2 * r i)) ≠ ∞ :=
      hfin _ (isCompact_closedBall _ _) (hrW i)
    have : IsFiniteMeasure (ν.restrict (closedBall (i : Euclid P) (2 * r i))) :=
      isFiniteMeasure_restrict.mpr hKfin
    have hB := Besicovitch.ae_tendsto_measure_inter_div
      (ν.restrict (closedBall (i : Euclid P) (2 * r i))) s
    have heq : (ν.restrict (closedBall (i : Euclid P) (2 * r i))).restrict s =
        (ν.restrict s).restrict (closedBall (i : Euclid P) (2 * r i)) := by
      rw [Measure.restrict_restrict hs, Measure.restrict_restrict hKm, inter_comm]
    rw [heq, ae_restrict_iff' hKm] at hB
    filter_upwards [hB] with x hx hxV a ha
    have hxd : dist x i < r i := mem_ball.mp hxV
    have hxK : x ∈ closedBall (i : Euclid P) (2 * r i) := by
      rw [mem_closedBall]; linarith [hr0 i]
    have hlim := hx hxK
    by_cases ha0 : a ≤ 0
    · filter_upwards with t
      simp [ENNReal.ofReal_of_nonpos ha0]
    have hlt : ENNReal.ofReal a < 1 := ENNReal.ofReal_lt_one.mpr ha
    have ht0 : (0 : ℝ) < r i - dist x i := by linarith
    filter_upwards [hlim.eventually (lt_mem_nhds hlt), Ioo_mem_nhdsGT ht0] with t ht hti
    have hBK : closedBall x t ⊆ closedBall (i : Euclid P) (2 * r i) := by
      intro p hp
      rw [mem_closedBall] at hp ⊢
      calc dist p i ≤ dist p x + dist x i := dist_triangle _ _ _
        _ ≤ 2 * r i := by linarith [hti.2, hr0 i]
    rw [Measure.restrict_apply' hKm, Measure.restrict_apply' hKm,
      inter_eq_left.mpr hBK, inter_eq_left.mpr (inter_subset_right.trans hBK)] at ht
    by_cases hB0 : ν (closedBall x t) = 0
    · simp [hB0]
    have hBtop : ν (closedBall x t) ≠ ∞ := ne_top_of_le_ne_top hKfin (measure_mono hBK)
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp ht).le
  -- countably many balls
  have hall : ∀ᵐ x ∂ν.restrict s, ∀ i ∈ T, x ∈ ball (i : Euclid P) (r i) →
      ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t) :=
    (ae_ball_iff hTc).mpr (fun i _ => hloc i)
  filter_upwards [hall] with x hx hxW
  obtain ⟨i, hiT, hxi⟩ := hcover x hxW
  exact hx i hiT hxi

/-- Simon Ch. 3, Remark 1.5(3) with the density theorem of Ch. 1, 3.16: for `μ = θHⁿ⌞M` and an
open `W ⊆ U`, at `Hⁿ⌞M`-a.e. `x ∈ W` every `c < θ(x)` has `cωₙtⁿ ≤ μ(B_t(x))` for small `t > 0`.
With `m = θ(x)` and `M_m = {θ = m} ∩ M`, the density theorem on `M_m` and the approximate tangent
plane at `x` give `μ(B_t(x)) ≥ m Hⁿ(M_m ∩ B_t(x)) ≥ m a Hⁿ(M ∩ B_t(x)) ≥ m a² ωₙtⁿ`, and
`a = (1 + c/m)/2 < 1` has `c ≤ m a²`. -/
theorem Submission.dorag_dbs_lower_density_ge_mult : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n), 0 < n → IsOpen W → W ⊆ U → ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ W → ∀ c : ℝ, c < R.mult x → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ R.measure (closedBall x t) := by
  intro P n U W R hn hW hWU
  have hM := R.measurableSet_carrier
  -- Step 1: `Hⁿ⌞M` is finite on compact `K ⊆ W`, as `θ ≥ 1` on `M` and `θ` is locally integrable
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ W →
      (μHE[n].restrict R.carrier) K ≠ ∞ := by
    intro K hK hKW
    rw [Measure.restrict_apply' hM]
    have h := R.locallyIntegrable_mult K hK (hKW.trans hWU)
    refine ne_top_of_le_ne_top h ?_
    calc μHE[n] (K ∩ R.carrier) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
          rw [setLIntegral_const, one_mul, inter_comm]
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_mono' (hM.inter hK.measurableSet)
          intro x hx
          have := R.mult_pos x hx.1
          exact_mod_cast this
  -- Step 2: the density theorem on each level set `M_m = {y ∈ M | θ(y) = m}`, for all `m` at once
  have hs : ∀ m : ℕ, MeasurableSet {y | y ∈ R.carrier ∧ R.mult y = m} := fun m =>
    hM.inter (R.measurable_mult (measurableSet_singleton m))
  have hlev : ∀ m : ℕ, ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      x ∈ {y | y ∈ R.carrier ∧ R.mult y = m} → x ∈ W → ∀ a : ℝ, a < 1 →
        ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal a * (μHE[n].restrict R.carrier) (closedBall x t) ≤
          (μHE[n].restrict R.carrier) ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t) := by
    intro m
    have := Submission.dorag_dbs_localized_density_point P W {y | y ∈ R.carrier ∧ R.mult y = m}
      (μHE[n].restrict R.carrier) hW (hs m) hfin
    rwa [ae_restrict_iff' (hs m)] at this
  have hlev' := ae_all_iff.mpr hlev
  -- Steps 3–4: a.e. `x` lies in `M` and has an approximate tangent plane `Q`
  have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R.carrier := ae_restrict_mem hM
  filter_upwards [hlev', R.orients, hmem] with x hlevx htanx hxM hxW c hc
  obtain ⟨Q, hQ, -⟩ := htanx
  -- Step 5: with `m = θ(x) ≥ 1` and `0 < c < m`, `a = (1 + c/m)/2 < 1` satisfies `c ≤ m a²`
  have hm1 : 1 ≤ R.mult x := R.mult_pos x hxM
  have hm0 : (0 : ℝ) < R.mult x := by exact_mod_cast hm1
  by_cases hc0 : c ≤ 0
  · filter_upwards with t
    simp [ENNReal.ofReal_of_nonpos hc0]
  push Not at hc0
  set m := R.mult x
  have hq0 : 0 < c / m := div_pos hc0 hm0
  have hq1 : c / m < 1 := (div_lt_one hm0).mpr hc
  set a := (1 + c / m) / 2 with ha_def
  have ha1 : a < 1 := by linarith
  have ha0 : 0 < a := by linarith
  have haq : c / m ≤ a * a := by nlinarith
  have hcm : c ≤ m * (a * a) := by
    have := (div_le_iff₀ hm0).mp haq
    linarith
  -- Step 6: `μ(B_t(x)) ≥ m Hⁿ(M_m ∩ B_t(x)) ≥ m a Hⁿ(M ∩ B_t(x)) ≥ m a² ωₙtⁿ ≥ c ωₙtⁿ`
  have hA := Submission.dorag_dbs_approxTangent_lower_density P n R.carrier x Q hn hQ a ha1
  have hB := hlevx m ⟨hxM, rfl⟩ hxW a ha1
  filter_upwards [hA, hB] with t hAt hBt
  rw [Measure.restrict_apply measurableSet_closedBall,
    Measure.restrict_apply ((hs m).inter measurableSet_closedBall)] at hBt
  have hset : {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t ∩ R.carrier =
      {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t := by
    ext y; constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, h.1.1⟩
  rw [hset] at hBt
  have hmeas : (m : ℝ≥0∞) * μHE[n] ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t) ≤
      R.measure (closedBall x t) := by
    unfold IMRep.measure
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall]
    calc (m : ℝ≥0∞) * μHE[n] ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t)
        = ∫⁻ _ in {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t, (m : ℝ≥0∞) ∂μHE[n] := by
          rw [setLIntegral_const, mul_comm]
      _ = ∫⁻ y in {y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t,
            (R.mult y : ℝ≥0∞) ∂μHE[n] := by
          apply setLIntegral_congr_fun ((hs m).inter measurableSet_closedBall)
          intro y hy
          exact (congrArg (fun k : ℕ => (k : ℝ≥0∞)) hy.1.2).symm
      _ ≤ ∫⁻ y in closedBall x t ∩ R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[n] := by
          apply lintegral_mono_set
          intro y hy
          exact ⟨hy.2, hy.1.1⟩
  have hinter : μHE[n] (closedBall x t ∩ R.carrier) = μHE[n] (R.carrier ∩ closedBall x t) := by
    rw [inter_comm]
  rw [hinter] at hBt
  calc ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n)
      ≤ ENNReal.ofReal (m * (a * a)) * unitBallVolume n * ENNReal.ofReal (t ^ n) := by
        gcongr
    _ = (m : ℝ≥0∞) * (ENNReal.ofReal a * (ENNReal.ofReal a * unitBallVolume n *
          ENNReal.ofReal (t ^ n))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul ha0.le,
          ENNReal.ofReal_natCast]
        ring
    _ ≤ (m : ℝ≥0∞) * (ENNReal.ofReal a * μHE[n] (R.carrier ∩ closedBall x t)) := by
        gcongr
    _ ≤ (m : ℝ≥0∞) * μHE[n] ({y | y ∈ R.carrier ∧ R.mult y = m} ∩ closedBall x t) := by
        gcongr
    _ ≤ R.measure (closedBall x t) := hmeas

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
